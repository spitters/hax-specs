//! AES-128 and AES-256 block cipher (FIPS 197).
//!
//! Straightforward S-box-table AES (no T-tables), written in a
//! hax-extraction-friendly style:
//!   * fixed-size `[u8; N]` arrays only (no `Vec`),
//!   * bounded `for i in 0..N` loops (no `while`, no `?`),
//!   * `wrapping_*` / xor arithmetic only.
//!
//! The `AesCipher` trait (AES-128, single 16-byte key) is implemented by
//! [`RealAes`]; AES-256 is exposed as a free function for the AES-256-GCM
//! path of `realgcm`.

use crate::aes::AesCipher;
use crate::types::{AesBlock, AesKey};

/// AES forward S-box (FIPS 197, Figure 7).
const SBOX: [u8; 256] = [
    0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
    0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
    0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
    0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
    0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
    0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
    0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
    0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
    0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
    0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
    0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
    0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
    0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
    0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
    0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
    0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16,
];

/// Round constants (Rcon), MSB only, for key expansion.
const RCON: [u8; 10] = [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36];

/// S-box lookup.
fn sub_byte(x: u8) -> u8 {
    SBOX[x as usize]
}

/// `xtime`: multiply by x (0x02) in GF(2^8) with the AES polynomial.
fn xtime(b: u8) -> u8 {
    let hi: u8 = b >> 7;
    let shifted: u8 = b << 1;
    // 0x1b reduction iff the high bit was set.
    shifted ^ (hi.wrapping_mul(0x1b))
}

/// GF(2^8) multiply, used by MixColumns.
fn gmul(a: u8, b: u8) -> u8 {
    // We only need multiplication by 1,2,3 for MixColumns, expressed via xtime.
    let mut acc: u8 = 0;
    let mut aa: u8 = a;
    let mut bb: u8 = b;
    for _ in 0..8 {
        let lsb: u8 = bb & 1;
        // add aa if lsb set
        acc ^= aa.wrapping_mul(lsb);
        aa = xtime(aa);
        bb >>= 1;
    }
    acc
}

// ---------------------------------------------------------------------------
// AES round transformations (state is column-major 16 bytes, FIPS 197 layout:
// state[r + 4*c], i.e. byte order is column 0 first).
// ---------------------------------------------------------------------------

fn sub_bytes(state: &mut AesBlock) {
    for i in 0..16 {
        state[i] = sub_byte(state[i]);
    }
}

fn shift_rows(state: &mut AesBlock) {
    let mut out: AesBlock = [0u8; 16];
    // state index = row + 4*col. Row r is rotated left by r.
    for r in 0..4 {
        for c in 0..4 {
            let src_col: usize = (c + r) % 4;
            out[r + 4 * c] = state[r + 4 * src_col];
        }
    }
    for i in 0..16 {
        state[i] = out[i];
    }
}

fn mix_columns(state: &mut AesBlock) {
    let mut out: AesBlock = [0u8; 16];
    for c in 0..4 {
        let s0: u8 = state[4 * c];
        let s1: u8 = state[4 * c + 1];
        let s2: u8 = state[4 * c + 2];
        let s3: u8 = state[4 * c + 3];
        out[4 * c] = gmul(s0, 2) ^ gmul(s1, 3) ^ s2 ^ s3;
        out[4 * c + 1] = s0 ^ gmul(s1, 2) ^ gmul(s2, 3) ^ s3;
        out[4 * c + 2] = s0 ^ s1 ^ gmul(s2, 2) ^ gmul(s3, 3);
        out[4 * c + 3] = gmul(s0, 3) ^ s1 ^ s2 ^ gmul(s3, 2);
    }
    for i in 0..16 {
        state[i] = out[i];
    }
}

fn add_round_key(state: &mut AesBlock, rk: &AesBlock) {
    for i in 0..16 {
        state[i] ^= rk[i];
    }
}

// ---------------------------------------------------------------------------
// AES-128: 11 round keys (176 bytes).
// ---------------------------------------------------------------------------

/// Expand a 16-byte AES-128 key into 11 round keys (176 bytes).
pub fn key_expansion_128(key: &AesKey) -> [u8; 176] {
    let mut w: [u8; 176] = [0u8; 176];
    for i in 0..16 {
        w[i] = key[i];
    }
    // Each subsequent 4-byte word.
    for i in 4..44 {
        let mut t0: u8 = w[4 * (i - 1)];
        let mut t1: u8 = w[4 * (i - 1) + 1];
        let mut t2: u8 = w[4 * (i - 1) + 2];
        let mut t3: u8 = w[4 * (i - 1) + 3];
        if i % 4 == 0 {
            // RotWord
            let r0: u8 = t1;
            let r1: u8 = t2;
            let r2: u8 = t3;
            let r3: u8 = t0;
            // SubWord
            t0 = sub_byte(r0) ^ RCON[i / 4 - 1];
            t1 = sub_byte(r1);
            t2 = sub_byte(r2);
            t3 = sub_byte(r3);
        }
        w[4 * i] = w[4 * (i - 4)] ^ t0;
        w[4 * i + 1] = w[4 * (i - 4) + 1] ^ t1;
        w[4 * i + 2] = w[4 * (i - 4) + 2] ^ t2;
        w[4 * i + 3] = w[4 * (i - 4) + 3] ^ t3;
    }
    w
}

fn round_key_128(schedule: &[u8; 176], round: usize) -> AesBlock {
    let mut rk: AesBlock = [0u8; 16];
    for i in 0..16 {
        rk[i] = schedule[round * 16 + i];
    }
    rk
}

/// Encrypt one 16-byte block under AES-128.
pub fn aes128_encrypt_block(key: &AesKey, block: &AesBlock) -> AesBlock {
    let schedule: [u8; 176] = key_expansion_128(key);
    let mut state: AesBlock = *block;

    let rk0: AesBlock = round_key_128(&schedule, 0);
    add_round_key(&mut state, &rk0);

    for round in 1..10 {
        sub_bytes(&mut state);
        shift_rows(&mut state);
        mix_columns(&mut state);
        let rk: AesBlock = round_key_128(&schedule, round);
        add_round_key(&mut state, &rk);
    }

    // Final round (no MixColumns).
    sub_bytes(&mut state);
    shift_rows(&mut state);
    let rk10: AesBlock = round_key_128(&schedule, 10);
    add_round_key(&mut state, &rk10);

    state
}

// ---------------------------------------------------------------------------
// AES-256: 15 round keys (240 bytes), 32-byte key.
// ---------------------------------------------------------------------------

/// Expand a 32-byte AES-256 key into 15 round keys (240 bytes).
pub fn key_expansion_256(key: &[u8; 32]) -> [u8; 240] {
    let mut w: [u8; 240] = [0u8; 240];
    for i in 0..32 {
        w[i] = key[i];
    }
    // Nk = 8 words; total words Nb*(Nr+1) = 4*15 = 60.
    for i in 8..60 {
        let mut t0: u8 = w[4 * (i - 1)];
        let mut t1: u8 = w[4 * (i - 1) + 1];
        let mut t2: u8 = w[4 * (i - 1) + 2];
        let mut t3: u8 = w[4 * (i - 1) + 3];
        if i % 8 == 0 {
            // RotWord + SubWord + Rcon
            let r0: u8 = t1;
            let r1: u8 = t2;
            let r2: u8 = t3;
            let r3: u8 = t0;
            t0 = sub_byte(r0) ^ RCON[i / 8 - 1];
            t1 = sub_byte(r1);
            t2 = sub_byte(r2);
            t3 = sub_byte(r3);
        } else if i % 8 == 4 {
            // SubWord only (AES-256 extra step)
            t0 = sub_byte(t0);
            t1 = sub_byte(t1);
            t2 = sub_byte(t2);
            t3 = sub_byte(t3);
        }
        w[4 * i] = w[4 * (i - 8)] ^ t0;
        w[4 * i + 1] = w[4 * (i - 8) + 1] ^ t1;
        w[4 * i + 2] = w[4 * (i - 8) + 2] ^ t2;
        w[4 * i + 3] = w[4 * (i - 8) + 3] ^ t3;
    }
    w
}

fn round_key_256(schedule: &[u8; 240], round: usize) -> AesBlock {
    let mut rk: AesBlock = [0u8; 16];
    for i in 0..16 {
        rk[i] = schedule[round * 16 + i];
    }
    rk
}

/// Encrypt one 16-byte block under AES-256.
pub fn aes256_encrypt_block(key: &[u8; 32], block: &AesBlock) -> AesBlock {
    let schedule: [u8; 240] = key_expansion_256(key);
    let mut state: AesBlock = *block;

    let rk0: AesBlock = round_key_256(&schedule, 0);
    add_round_key(&mut state, &rk0);

    for round in 1..14 {
        sub_bytes(&mut state);
        shift_rows(&mut state);
        mix_columns(&mut state);
        let rk: AesBlock = round_key_256(&schedule, round);
        add_round_key(&mut state, &rk);
    }

    sub_bytes(&mut state);
    shift_rows(&mut state);
    let rk14: AesBlock = round_key_256(&schedule, 14);
    add_round_key(&mut state, &rk14);

    state
}

/// Concrete AES-128 cipher implementing the [`AesCipher`] trait.
///
/// Performs the full FIPS 197 AES-128 round function.
#[derive(Copy, Clone)]
pub struct RealAes;

impl AesCipher for RealAes {
    fn aes128_encrypt_block(self, key: &AesKey, block: &AesBlock) -> AesBlock {
        aes128_encrypt_block(key, block)
    }
}
