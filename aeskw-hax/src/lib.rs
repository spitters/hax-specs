// Copyright (c) 2026 CatCrypt Contributors. MIT license.
//! AES Key Wrap (NIST SP 800-38F / RFC 3394): Hax-extractable implementation.
//!
//! AES Key Wrap provides confidentiality and integrity protection for
//! cryptographic keys using a Key Encryption Key (KEK).
//!
//! Construction (RFC 3394, Section 2.2.1 — Wrap):
//!
//! ```text
//! 1. Initialize A = IV (default: A6A6A6A6A6A6A6A6)
//! 2. For j = 0..5, for i = 1..n:
//!    B = AES(A || R[i]), A = MSB(64,B) XOR t, R[i] = LSB(64,B)
//!    where t = n*j + i
//! 3. Output C = A || R[1] || ... || R[n]
//! ```
//!
//! Construction (RFC 3394, Section 2.2.2 — Unwrap):
//!
//! ```text
//! 1. Initialize A = C[0], R[i] = C[i] for i = 1..n
//! 2. For j = 5..0, for i = n..1:
//!    B = AES^{-1}((A XOR t) || R[i]), A = MSB(64,B), R[i] = LSB(64,B)
//!    where t = n*j + i
//! 3. Verify A == IV, output R[1] || ... || R[n]
//! ```
//!
//! All loops are bounded `for i in 0..N`, all arithmetic is wrapping,
//! all buffers are fixed-size arrays. The Lean extraction of this module
//! produced by `cargo hax into lean` is checked in under `proofs/lean/`.

#![no_std]
// The index-loop style is kept for hax extraction; these lints suggest slice
// methods (`copy_from_slice`, iterators) instead.
#![allow(clippy::manual_memcpy, clippy::needless_range_loop)]

// =========================================================================
// AES-128 specification (FIPS 197)
// =========================================================================

/// AES S-box lookup table (FIPS 197, Figure 7).
pub static AES_SBOX: [u8; 256] = [
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

/// AES inverse S-box lookup table (FIPS 197, Figure 14).
pub static AES_INV_SBOX: [u8; 256] = [
    0x52, 0x09, 0x6a, 0xd5, 0x30, 0x36, 0xa5, 0x38, 0xbf, 0x40, 0xa3, 0x9e, 0x81, 0xf3, 0xd7, 0xfb,
    0x7c, 0xe3, 0x39, 0x82, 0x9b, 0x2f, 0xff, 0x87, 0x34, 0x8e, 0x43, 0x44, 0xc4, 0xde, 0xe9, 0xcb,
    0x54, 0x7b, 0x94, 0x32, 0xa6, 0xc2, 0x23, 0x3d, 0xee, 0x4c, 0x95, 0x0b, 0x42, 0xfa, 0xc3, 0x4e,
    0x08, 0x2e, 0xa1, 0x66, 0x28, 0xd9, 0x24, 0xb2, 0x76, 0x5b, 0xa2, 0x49, 0x6d, 0x8b, 0xd1, 0x25,
    0x72, 0xf8, 0xf6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xd4, 0xa4, 0x5c, 0xcc, 0x5d, 0x65, 0xb6, 0x92,
    0x6c, 0x70, 0x48, 0x50, 0xfd, 0xed, 0xb9, 0xda, 0x5e, 0x15, 0x46, 0x57, 0xa7, 0x8d, 0x9d, 0x84,
    0x90, 0xd8, 0xab, 0x00, 0x8c, 0xbc, 0xd3, 0x0a, 0xf7, 0xe4, 0x58, 0x05, 0xb8, 0xb3, 0x45, 0x06,
    0xd0, 0x2c, 0x1e, 0x8f, 0xca, 0x3f, 0x0f, 0x02, 0xc1, 0xaf, 0xbd, 0x03, 0x01, 0x13, 0x8a, 0x6b,
    0x3a, 0x91, 0x11, 0x41, 0x4f, 0x67, 0xdc, 0xea, 0x97, 0xf2, 0xcf, 0xce, 0xf0, 0xb4, 0xe6, 0x73,
    0x96, 0xac, 0x74, 0x22, 0xe7, 0xad, 0x35, 0x85, 0xe2, 0xf9, 0x37, 0xe8, 0x1c, 0x75, 0xdf, 0x6e,
    0x47, 0xf1, 0x1a, 0x71, 0x1d, 0x29, 0xc5, 0x89, 0x6f, 0xb7, 0x62, 0x0e, 0xaa, 0x18, 0xbe, 0x1b,
    0xfc, 0x56, 0x3e, 0x4b, 0xc6, 0xd2, 0x79, 0x20, 0x9a, 0xdb, 0xc0, 0xfe, 0x78, 0xcd, 0x5a, 0xf4,
    0x1f, 0xdd, 0xa8, 0x33, 0x88, 0x07, 0xc7, 0x31, 0xb1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xec, 0x5f,
    0x60, 0x51, 0x7f, 0xa9, 0x19, 0xb5, 0x4a, 0x0d, 0x2d, 0xe5, 0x7a, 0x9f, 0x93, 0xc9, 0x9c, 0xef,
    0xa0, 0xe0, 0x3b, 0x4d, 0xae, 0x2a, 0xf5, 0xb0, 0xc8, 0xeb, 0xbb, 0x3c, 0x83, 0x53, 0x99, 0x61,
    0x17, 0x2b, 0x04, 0x7e, 0xba, 0x77, 0xd6, 0x26, 0xe1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0c, 0x7d,
];

/// AES round constants (FIPS 197, Section 5.2).
static RCON: [u8; 10] = [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36];

/// A 128-bit block (16 bytes).
pub type Block = [u8; 16];

/// AES-128 key: 16 bytes.
pub type AesKey = [u8; 16];

/// AES-128 round keys: 11 x 16 bytes (initial + 10 rounds).
pub type RoundKeys = [[u8; 16]; 11];

/// A 64-bit half-block (8 bytes), used in Key Wrap.
pub type HalfBlock = [u8; 8];

/// Maximum number of 64-bit key data blocks for Key Wrap.
/// Supports wrapping keys up to 512 bits (8 x 64 bits).
pub const MAX_BLOCKS: usize = 8;

/// Default Initial Value for AES Key Wrap (RFC 3394, Section 2.2.3.1).
pub const DEFAULT_IV: HalfBlock = [0xA6, 0xA6, 0xA6, 0xA6, 0xA6, 0xA6, 0xA6, 0xA6];

// =========================================================================
// Block operations
// =========================================================================

/// XOR two 128-bit blocks.
#[inline]
pub fn xor_block(a: &Block, b: &Block) -> Block {
    let mut result: Block = [0u8; 16];
    for i in 0..16 {
        result[i] = a[i] ^ b[i];
    }
    result
}

/// XOR two 64-bit half-blocks.
#[inline]
pub fn xor_half(a: &HalfBlock, b: &HalfBlock) -> HalfBlock {
    let mut result: HalfBlock = [0u8; 8];
    for i in 0..8 {
        result[i] = a[i] ^ b[i];
    }
    result
}

/// Concatenate two 64-bit half-blocks into a 128-bit block.
#[inline]
pub fn concat_halves(left: &HalfBlock, right: &HalfBlock) -> Block {
    let mut result: Block = [0u8; 16];
    for i in 0..8 {
        result[i] = left[i];
    }
    for i in 0..8 {
        result[8 + i] = right[i];
    }
    result
}

/// Extract the most significant 64 bits (first 8 bytes) of a 128-bit block.
#[inline]
pub fn msb64(block: &Block) -> HalfBlock {
    let mut result: HalfBlock = [0u8; 8];
    for i in 0..8 {
        result[i] = block[i];
    }
    result
}

/// Extract the least significant 64 bits (last 8 bytes) of a 128-bit block.
#[inline]
pub fn lsb64(block: &Block) -> HalfBlock {
    let mut result: HalfBlock = [0u8; 8];
    for i in 0..8 {
        result[i] = block[8 + i];
    }
    result
}

/// Encode a u64 value as big-endian 8-byte array.
#[inline]
pub fn u64_to_be_bytes(val: u64) -> HalfBlock {
    let mut result: HalfBlock = [0u8; 8];
    result[0] = (val >> 56) as u8;
    result[1] = (val >> 48) as u8;
    result[2] = (val >> 40) as u8;
    result[3] = (val >> 32) as u8;
    result[4] = (val >> 24) as u8;
    result[5] = (val >> 16) as u8;
    result[6] = (val >> 8) as u8;
    result[7] = val as u8;
    result
}

// =========================================================================
// AES-128 key expansion (FIPS 197, Section 5.2)
// =========================================================================

/// Multiply by 2 in GF(2^8) with irreducible polynomial x^8 + x^4 + x^3 + x + 1.
#[inline]
fn gf_mul2(x: u8) -> u8 {
    let shifted = (x as u16) << 1;
    let reduced = if x & 0x80 != 0 { shifted ^ 0x1b } else { shifted };
    reduced as u8
}

/// Multiply by 3 in GF(2^8): 3*x = 2*x XOR x.
#[inline]
fn gf_mul3(x: u8) -> u8 {
    gf_mul2(x) ^ x
}

/// Multiply by 9 in GF(2^8): 9*x = 8*x XOR x.
#[inline]
fn gf_mul9(x: u8) -> u8 {
    gf_mul2(gf_mul2(gf_mul2(x))) ^ x
}

/// Multiply by 11 in GF(2^8): 11*x = 8*x XOR 2*x XOR x.
#[inline]
fn gf_mul11(x: u8) -> u8 {
    gf_mul2(gf_mul2(gf_mul2(x))) ^ gf_mul2(x) ^ x
}

/// Multiply by 13 in GF(2^8): 13*x = 8*x XOR 4*x XOR x.
#[inline]
fn gf_mul13(x: u8) -> u8 {
    gf_mul2(gf_mul2(gf_mul2(x))) ^ gf_mul2(gf_mul2(x)) ^ x
}

/// Multiply by 14 in GF(2^8): 14*x = 8*x XOR 4*x XOR 2*x.
#[inline]
fn gf_mul14(x: u8) -> u8 {
    gf_mul2(gf_mul2(gf_mul2(x))) ^ gf_mul2(gf_mul2(x)) ^ gf_mul2(x)
}

/// AES SubBytes on a single word (4 bytes).
#[inline]
fn sub_word(w: [u8; 4]) -> [u8; 4] {
    [AES_SBOX[w[0] as usize], AES_SBOX[w[1] as usize],
     AES_SBOX[w[2] as usize], AES_SBOX[w[3] as usize]]
}

/// AES RotWord: rotate 4 bytes left by 1.
#[inline]
fn rot_word(w: [u8; 4]) -> [u8; 4] {
    [w[1], w[2], w[3], w[0]]
}

/// AES-128 key expansion: produce 11 round keys from 16-byte key.
pub fn aes128_key_expansion(key: &AesKey) -> RoundKeys {
    let mut rk: RoundKeys = [[0u8; 16]; 11];

    // Copy initial key into first round key
    for i in 0..16 {
        rk[0][i] = key[i];
    }

    // Expand: for each subsequent word W[i] (i = 4..43)
    for round in 1..11 {
        let prev_last: [u8; 4] = [
            rk[round - 1][12], rk[round - 1][13],
            rk[round - 1][14], rk[round - 1][15],
        ];

        let rotated = rot_word(prev_last);
        let subbed = sub_word(rotated);
        let rcon_byte = RCON[round - 1];

        rk[round][0] = rk[round - 1][0] ^ subbed[0] ^ rcon_byte;
        rk[round][1] = rk[round - 1][1] ^ subbed[1];
        rk[round][2] = rk[round - 1][2] ^ subbed[2];
        rk[round][3] = rk[round - 1][3] ^ subbed[3];

        for j in 1..4 {
            let base = j * 4;
            for b in 0..4 {
                rk[round][base + b] = rk[round - 1][base + b] ^ rk[round][base - 4 + b];
            }
        }
    }

    rk
}

// =========================================================================
// AES-128 single-block encryption (FIPS 197)
// =========================================================================

/// AES SubBytes: apply S-box to all 16 bytes.
fn aes_sub_bytes(state: &mut Block) {
    for i in 0..16 {
        state[i] = AES_SBOX[state[i] as usize];
    }
}

/// AES ShiftRows: cyclic left shift of rows.
fn aes_shift_rows(state: &mut Block) {
    // Row 1: shift left by 1
    let t = state[1];
    state[1] = state[5]; state[5] = state[9]; state[9] = state[13]; state[13] = t;
    // Row 2: shift left by 2
    let t0 = state[2]; let t1 = state[6];
    state[2] = state[10]; state[6] = state[14]; state[10] = t0; state[14] = t1;
    // Row 3: shift left by 3 (= right by 1)
    let t = state[15];
    state[15] = state[11]; state[11] = state[7]; state[7] = state[3]; state[3] = t;
}

/// AES MixColumns: mix each column using GF(2^8) multiplication.
fn aes_mix_columns(state: &mut Block) {
    for col in 0..4 {
        let base = col * 4;
        let s0 = state[base];
        let s1 = state[base + 1];
        let s2 = state[base + 2];
        let s3 = state[base + 3];

        state[base]     = gf_mul2(s0) ^ gf_mul3(s1) ^ s2 ^ s3;
        state[base + 1] = s0 ^ gf_mul2(s1) ^ gf_mul3(s2) ^ s3;
        state[base + 2] = s0 ^ s1 ^ gf_mul2(s2) ^ gf_mul3(s3);
        state[base + 3] = gf_mul3(s0) ^ s1 ^ s2 ^ gf_mul2(s3);
    }
}

/// AES AddRoundKey: XOR state with round key.
fn aes_add_round_key(state: &mut Block, rk: &Block) {
    for i in 0..16 {
        state[i] ^= rk[i];
    }
}

/// AES-128 encrypt a single 16-byte block.
///
/// Performs 10 rounds: initial AddRoundKey, 9 full rounds, 1 final round
/// (no MixColumns).
pub fn aes128_encrypt(key: &AesKey, plaintext: &Block) -> Block {
    let rk = aes128_key_expansion(key);
    let mut state = *plaintext;

    // Initial round key addition
    aes_add_round_key(&mut state, &rk[0]);

    // Rounds 1-9: SubBytes + ShiftRows + MixColumns + AddRoundKey
    for round in 1..10 {
        aes_sub_bytes(&mut state);
        aes_shift_rows(&mut state);
        aes_mix_columns(&mut state);
        aes_add_round_key(&mut state, &rk[round]);
    }

    // Round 10: SubBytes + ShiftRows + AddRoundKey (no MixColumns)
    aes_sub_bytes(&mut state);
    aes_shift_rows(&mut state);
    aes_add_round_key(&mut state, &rk[10]);

    state
}

// =========================================================================
// AES-128 single-block decryption (FIPS 197)
// =========================================================================

/// AES InvSubBytes: apply inverse S-box to all 16 bytes.
fn aes_inv_sub_bytes(state: &mut Block) {
    for i in 0..16 {
        state[i] = AES_INV_SBOX[state[i] as usize];
    }
}

/// AES InvShiftRows: cyclic right shift of rows.
fn aes_inv_shift_rows(state: &mut Block) {
    // Row 1: shift right by 1
    let t = state[13];
    state[13] = state[9]; state[9] = state[5]; state[5] = state[1]; state[1] = t;
    // Row 2: shift right by 2
    let t0 = state[2]; let t1 = state[6];
    state[2] = state[10]; state[6] = state[14]; state[10] = t0; state[14] = t1;
    // Row 3: shift right by 3 (= left by 1)
    let t = state[3];
    state[3] = state[7]; state[7] = state[11]; state[11] = state[15]; state[15] = t;
}

/// AES InvMixColumns: inverse mix each column using GF(2^8) multiplication.
///
/// Uses the inverse MDS matrix: [14, 11, 13, 9] rotated per row.
fn aes_inv_mix_columns(state: &mut Block) {
    for col in 0..4 {
        let base = col * 4;
        let s0 = state[base];
        let s1 = state[base + 1];
        let s2 = state[base + 2];
        let s3 = state[base + 3];

        state[base]     = gf_mul14(s0) ^ gf_mul11(s1) ^ gf_mul13(s2) ^ gf_mul9(s3);
        state[base + 1] = gf_mul9(s0) ^ gf_mul14(s1) ^ gf_mul11(s2) ^ gf_mul13(s3);
        state[base + 2] = gf_mul13(s0) ^ gf_mul9(s1) ^ gf_mul14(s2) ^ gf_mul11(s3);
        state[base + 3] = gf_mul11(s0) ^ gf_mul13(s1) ^ gf_mul9(s2) ^ gf_mul14(s3);
    }
}

/// AES-128 decrypt a single 16-byte block.
///
/// Performs 10 inverse rounds: initial AddRoundKey (round 10),
/// 9 full inverse rounds, 1 final inverse round (no InvMixColumns).
pub fn aes128_decrypt(key: &AesKey, ciphertext: &Block) -> Block {
    let rk = aes128_key_expansion(key);
    let mut state = *ciphertext;

    // Initial round key addition (last round key)
    aes_add_round_key(&mut state, &rk[10]);

    // Rounds 9-1: InvShiftRows + InvSubBytes + AddRoundKey + InvMixColumns
    for round in (1..10).rev() {
        aes_inv_shift_rows(&mut state);
        aes_inv_sub_bytes(&mut state);
        aes_add_round_key(&mut state, &rk[round]);
        aes_inv_mix_columns(&mut state);
    }

    // Round 0: InvShiftRows + InvSubBytes + AddRoundKey (no InvMixColumns)
    aes_inv_shift_rows(&mut state);
    aes_inv_sub_bytes(&mut state);
    aes_add_round_key(&mut state, &rk[0]);

    state
}

// =========================================================================
// AES Key Wrap (RFC 3394, Section 2.2.1)
// =========================================================================

/// AES Key Wrap: wrap key data using a KEK.
///
/// Implements RFC 3394, Section 2.2.1 (Index-based wrapping).
///
/// # Arguments
/// * `kek` - 16-byte Key Encryption Key (AES-128)
/// * `key_data` - plaintext key data as 64-bit blocks
/// * `n` - number of 64-bit key data blocks (must be >= 2, <= MAX_BLOCKS)
///
/// # Returns
/// Wrapped key: (n+1) 64-bit blocks = `A || R[1] || ... || R[n]`.
/// Returns `(A, R)` where A is the 8-byte integrity check value and
/// R is the array of n wrapped 64-bit blocks.
pub fn aes_wrap(
    kek: &AesKey,
    key_data: &[HalfBlock; MAX_BLOCKS],
    n: usize,
) -> (HalfBlock, [HalfBlock; MAX_BLOCKS]) {
    // 1. Initialize variables
    let mut a: HalfBlock = DEFAULT_IV;
    let mut r: [HalfBlock; MAX_BLOCKS] = [[0u8; 8]; MAX_BLOCKS];

    // Set R[i] = P[i] for i = 0..n-1 (0-indexed)
    for i in 0..MAX_BLOCKS {
        if i < n {
            r[i] = key_data[i];
        }
    }

    // 2. Calculate intermediate values
    // For j = 0 to 5
    //   For i = 1 to n (1-indexed in RFC; 0-indexed here as i-1)
    //     B = AES(K, A || R[i])
    //     A = MSB(64, B) XOR t  where t = n*j + i
    //     R[i] = LSB(64, B)
    for j in 0..6u64 {
        for i in 0..MAX_BLOCKS {
            if i < n {
                let t: u64 = (n as u64) * j + (i as u64) + 1;
                let input = concat_halves(&a, &r[i]);
                let b = aes128_encrypt(kek, &input);
                let t_bytes = u64_to_be_bytes(t);
                a = xor_half(&msb64(&b), &t_bytes);
                r[i] = lsb64(&b);
            }
        }
    }

    (a, r)
}

/// AES Key Unwrap: unwrap key data using a KEK.
///
/// Implements RFC 3394, Section 2.2.2 (Index-based unwrapping).
///
/// # Arguments
/// * `kek` - 16-byte Key Encryption Key (AES-128)
/// * `a_in` - 8-byte integrity check value (first 64 bits of wrapped key)
/// * `cipher_data` - wrapped key data as 64-bit blocks
/// * `n` - number of 64-bit key data blocks (must be >= 2, <= MAX_BLOCKS)
///
/// # Returns
/// `Some(plaintext_blocks)` if the integrity check passes (A == default IV),
/// `None` if the integrity check fails.
pub fn aes_unwrap(
    kek: &AesKey,
    a_in: &HalfBlock,
    cipher_data: &[HalfBlock; MAX_BLOCKS],
    n: usize,
) -> Option<[HalfBlock; MAX_BLOCKS]> {
    // 1. Initialize variables
    let mut a: HalfBlock = *a_in;
    let mut r: [HalfBlock; MAX_BLOCKS] = [[0u8; 8]; MAX_BLOCKS];

    // Set R[i] = C[i] for i = 0..n-1
    for i in 0..MAX_BLOCKS {
        if i < n {
            r[i] = cipher_data[i];
        }
    }

    // 2. Calculate intermediate values
    // For j = 5 downto 0
    //   For i = n downto 1 (1-indexed in RFC; 0-indexed here as i-1)
    //     B = AES^{-1}(K, (A XOR t) || R[i])  where t = n*j + i
    //     A = MSB(64, B)
    //     R[i] = LSB(64, B)
    for jj in 0..6u64 {
        let j = 5 - jj;
        for ii in 0..MAX_BLOCKS {
            if ii < n {
                let i = n - 1 - ii; // iterate from n-1 down to 0 (0-indexed)
                let t: u64 = (n as u64) * j + (i as u64) + 1;
                let t_bytes = u64_to_be_bytes(t);
                let a_xor_t = xor_half(&a, &t_bytes);
                let input = concat_halves(&a_xor_t, &r[i]);
                let b = aes128_decrypt(kek, &input);
                a = msb64(&b);
                r[i] = lsb64(&b);
            }
        }
    }

    // 3. Output results — verify integrity check value
    if iv_check(&a) {
        Some(r)
    } else {
        None
    }
}

/// Check if the integrity check value matches the default IV.
#[inline]
pub fn iv_check(a: &HalfBlock) -> bool {
    let mut ok = true;
    for i in 0..8 {
        if a[i] != DEFAULT_IV[i] {
            ok = false;
        }
    }
    ok
}

// =========================================================================
// Convenience functions
// =========================================================================

/// Wrap a 128-bit key (16 bytes = 2 x 64-bit blocks).
///
/// # Returns
/// 24-byte wrapped key (3 x 64-bit blocks).
pub fn aes_wrap_128(kek: &AesKey, key_data: &[u8; 16]) -> [u8; 24] {
    let mut blocks: [HalfBlock; MAX_BLOCKS] = [[0u8; 8]; MAX_BLOCKS];
    for i in 0..8 {
        blocks[0][i] = key_data[i];
    }
    for i in 0..8 {
        blocks[1][i] = key_data[8 + i];
    }

    let (a, r) = aes_wrap(kek, &blocks, 2);

    let mut result = [0u8; 24];
    for i in 0..8 {
        result[i] = a[i];
    }
    for i in 0..8 {
        result[8 + i] = r[0][i];
    }
    for i in 0..8 {
        result[16 + i] = r[1][i];
    }
    result
}

/// Unwrap a 128-bit key (16 bytes) from 24-byte wrapped key.
///
/// # Returns
/// `Some([u8; 16])` if integrity check passes, `None` otherwise.
pub fn aes_unwrap_128(kek: &AesKey, wrapped: &[u8; 24]) -> Option<[u8; 16]> {
    let mut a: HalfBlock = [0u8; 8];
    for i in 0..8 {
        a[i] = wrapped[i];
    }

    let mut cipher_data: [HalfBlock; MAX_BLOCKS] = [[0u8; 8]; MAX_BLOCKS];
    for i in 0..8 {
        cipher_data[0][i] = wrapped[8 + i];
    }
    for i in 0..8 {
        cipher_data[1][i] = wrapped[16 + i];
    }

    match aes_unwrap(kek, &a, &cipher_data, 2) {
        Some(r) => {
            let mut result = [0u8; 16];
            for i in 0..8 {
                result[i] = r[0][i];
            }
            for i in 0..8 {
                result[8 + i] = r[1][i];
            }
            Some(result)
        }
        None => None,
    }
}

/// Wrap a 256-bit key (32 bytes = 4 x 64-bit blocks).
///
/// # Returns
/// 40-byte wrapped key (5 x 64-bit blocks).
pub fn aes_wrap_256(kek: &AesKey, key_data: &[u8; 32]) -> [u8; 40] {
    let mut blocks: [HalfBlock; MAX_BLOCKS] = [[0u8; 8]; MAX_BLOCKS];
    for b in 0..4 {
        for i in 0..8 {
            blocks[b][i] = key_data[b * 8 + i];
        }
    }

    let (a, r) = aes_wrap(kek, &blocks, 4);

    let mut result = [0u8; 40];
    for i in 0..8 {
        result[i] = a[i];
    }
    for b in 0..4 {
        for i in 0..8 {
            result[8 + b * 8 + i] = r[b][i];
        }
    }
    result
}

/// Unwrap a 256-bit key (32 bytes) from 40-byte wrapped key.
///
/// # Returns
/// `Some([u8; 32])` if integrity check passes, `None` otherwise.
pub fn aes_unwrap_256(kek: &AesKey, wrapped: &[u8; 40]) -> Option<[u8; 32]> {
    let mut a: HalfBlock = [0u8; 8];
    for i in 0..8 {
        a[i] = wrapped[i];
    }

    let mut cipher_data: [HalfBlock; MAX_BLOCKS] = [[0u8; 8]; MAX_BLOCKS];
    for b in 0..4 {
        for i in 0..8 {
            cipher_data[b][i] = wrapped[8 + b * 8 + i];
        }
    }

    match aes_unwrap(kek, &a, &cipher_data, 4) {
        Some(r) => {
            let mut result = [0u8; 32];
            for b in 0..4 {
                for i in 0..8 {
                    result[b * 8 + i] = r[b][i];
                }
            }
            Some(result)
        }
        None => None,
    }
}

// =========================================================================
// Kani harnesses
// =========================================================================

#[cfg(kani)]
mod kani_harnesses {
    use super::*;

    /// XOR self is zero.
    #[kani::proof]
    fn xor_self_is_zero() {
        let a: [u8; 8] = kani::any();
        let result = xor_half(&a, &a);
        for i in 0..8 {
            assert_eq!(result[i], 0);
        }
    }

    /// XOR with zero is identity.
    #[kani::proof]
    fn xor_zero_identity() {
        let a: [u8; 8] = kani::any();
        let zero: HalfBlock = [0u8; 8];
        let result = xor_half(&a, &zero);
        for i in 0..8 {
            assert_eq!(result[i], a[i]);
        }
    }

    /// IV check accepts the default IV.
    #[kani::proof]
    fn iv_check_accepts_default() {
        assert!(iv_check(&DEFAULT_IV));
    }

    /// IV check rejects non-default values.
    #[kani::proof]
    fn iv_check_rejects_modified() {
        let mut bad_iv = DEFAULT_IV;
        let idx: usize = kani::any();
        kani::assume(idx < 8);
        let delta: u8 = kani::any();
        kani::assume(delta != 0);
        bad_iv[idx] ^= delta;
        assert!(!iv_check(&bad_iv));
    }

    /// concat_halves then msb64/lsb64 round-trips.
    #[kani::proof]
    fn concat_split_roundtrip() {
        let left: HalfBlock = kani::any();
        let right: HalfBlock = kani::any();
        let block = concat_halves(&left, &right);
        let got_left = msb64(&block);
        let got_right = lsb64(&block);
        for i in 0..8 {
            assert_eq!(got_left[i], left[i]);
            assert_eq!(got_right[i], right[i]);
        }
    }

    /// S-box is a permutation: injective on full u8 range.
    #[kani::proof]
    fn sbox_injective() {
        let a: u8 = kani::any();
        let b: u8 = kani::any();
        kani::assume(a != b);
        assert_ne!(AES_SBOX[a as usize], AES_SBOX[b as usize],
            "S-box must be injective (permutation)");
    }

    /// Inverse S-box is a permutation: injective on full u8 range.
    #[kani::proof]
    fn inv_sbox_injective() {
        let a: u8 = kani::any();
        let b: u8 = kani::any();
        kani::assume(a != b);
        assert_ne!(AES_INV_SBOX[a as usize], AES_INV_SBOX[b as usize],
            "Inverse S-box must be injective (permutation)");
    }

    /// S-box and inverse S-box are inverses.
    #[kani::proof]
    fn sbox_inv_sbox_roundtrip() {
        let x: u8 = kani::any();
        assert_eq!(AES_INV_SBOX[AES_SBOX[x as usize] as usize], x);
        assert_eq!(AES_SBOX[AES_INV_SBOX[x as usize] as usize], x);
    }
}

// =========================================================================
// Unit tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // FIPS 197 Appendix B test vector: AES-128 encrypt
    #[test]
    fn test_aes128_fips197_appendix_b() {
        let key: AesKey = [
            0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6,
            0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c,
        ];
        let pt: Block = [
            0x32, 0x43, 0xf6, 0xa8, 0x88, 0x5a, 0x30, 0x8d,
            0x31, 0x31, 0x98, 0xa2, 0xe0, 0x37, 0x07, 0x34,
        ];
        let expected_ct: Block = [
            0x39, 0x25, 0x84, 0x1d, 0x02, 0xdc, 0x09, 0xfb,
            0xdc, 0x11, 0x85, 0x97, 0x19, 0x6a, 0x0b, 0x32,
        ];
        let ct = aes128_encrypt(&key, &pt);
        assert_eq!(ct, expected_ct, "AES-128 FIPS 197 Appendix B encrypt");
    }

    // AES-128 decrypt: inverse of FIPS 197 Appendix B
    #[test]
    fn test_aes128_decrypt_fips197() {
        let key: AesKey = [
            0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6,
            0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c,
        ];
        let ct: Block = [
            0x39, 0x25, 0x84, 0x1d, 0x02, 0xdc, 0x09, 0xfb,
            0xdc, 0x11, 0x85, 0x97, 0x19, 0x6a, 0x0b, 0x32,
        ];
        let expected_pt: Block = [
            0x32, 0x43, 0xf6, 0xa8, 0x88, 0x5a, 0x30, 0x8d,
            0x31, 0x31, 0x98, 0xa2, 0xe0, 0x37, 0x07, 0x34,
        ];
        let pt = aes128_decrypt(&key, &ct);
        assert_eq!(pt, expected_pt, "AES-128 FIPS 197 Appendix B decrypt");
    }

    // AES-128 encrypt then decrypt roundtrip
    #[test]
    fn test_aes128_encrypt_decrypt_roundtrip() {
        let key: AesKey = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
            0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
        ];
        let pt: Block = [
            0xde, 0xad, 0xbe, 0xef, 0xca, 0xfe, 0xba, 0xbe,
            0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef,
        ];
        let ct = aes128_encrypt(&key, &pt);
        let recovered = aes128_decrypt(&key, &ct);
        assert_eq!(recovered, pt, "AES-128 encrypt/decrypt roundtrip");
    }

    // RFC 3394 Section 4.1: 128-bit KEK, 128-bit key data
    #[test]
    fn test_wrap_rfc3394_4_1() {
        let kek: AesKey = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
            0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F,
        ];
        let key_data: [u8; 16] = [
            0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
            0x88, 0x99, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF,
        ];
        let expected_wrapped: [u8; 24] = [
            0x1F, 0xA6, 0x8B, 0x0A, 0x81, 0x12, 0xB4, 0x47,
            0xAE, 0xF3, 0x4B, 0xD8, 0xFB, 0x5A, 0x7B, 0x82,
            0x9D, 0x3E, 0x86, 0x23, 0x71, 0xD2, 0xCF, 0xE5,
        ];

        let wrapped = aes_wrap_128(&kek, &key_data);
        assert_eq!(wrapped, expected_wrapped, "RFC 3394 Section 4.1 wrap");
    }

    // RFC 3394 Section 4.1: unwrap
    #[test]
    fn test_unwrap_rfc3394_4_1() {
        let kek: AesKey = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
            0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F,
        ];
        let wrapped: [u8; 24] = [
            0x1F, 0xA6, 0x8B, 0x0A, 0x81, 0x12, 0xB4, 0x47,
            0xAE, 0xF3, 0x4B, 0xD8, 0xFB, 0x5A, 0x7B, 0x82,
            0x9D, 0x3E, 0x86, 0x23, 0x71, 0xD2, 0xCF, 0xE5,
        ];
        let expected_key_data: [u8; 16] = [
            0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
            0x88, 0x99, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF,
        ];

        let result = aes_unwrap_128(&kek, &wrapped);
        assert!(result.is_some(), "RFC 3394 Section 4.1 unwrap should succeed");
        assert_eq!(result.unwrap(), expected_key_data, "RFC 3394 Section 4.1 unwrap data");
    }

    // Wrap/unwrap roundtrip for 128-bit key
    #[test]
    fn test_wrap_unwrap_roundtrip_128() {
        let kek: AesKey = [
            0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6,
            0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c,
        ];
        let key_data: [u8; 16] = [
            0xde, 0xad, 0xbe, 0xef, 0xca, 0xfe, 0xba, 0xbe,
            0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef,
        ];

        let wrapped = aes_wrap_128(&kek, &key_data);
        let unwrapped = aes_unwrap_128(&kek, &wrapped);
        assert!(unwrapped.is_some(), "Roundtrip unwrap should succeed");
        assert_eq!(unwrapped.unwrap(), key_data, "Roundtrip 128-bit key data");
    }

    // Wrap/unwrap roundtrip for 256-bit key
    #[test]
    fn test_wrap_unwrap_roundtrip_256() {
        let kek: AesKey = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
            0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
        ];
        let key_data: [u8; 32] = [
            0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
            0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff,
            0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54, 0x32, 0x10,
            0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef,
        ];

        let wrapped = aes_wrap_256(&kek, &key_data);
        let unwrapped = aes_unwrap_256(&kek, &wrapped);
        assert!(unwrapped.is_some(), "Roundtrip unwrap 256 should succeed");
        assert_eq!(unwrapped.unwrap(), key_data, "Roundtrip 256-bit key data");
    }

    // Tampered wrapped key should fail integrity check
    #[test]
    fn test_unwrap_tampered_fails() {
        let kek: AesKey = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
            0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F,
        ];
        let key_data: [u8; 16] = [
            0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
            0x88, 0x99, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF,
        ];

        let mut wrapped = aes_wrap_128(&kek, &key_data);
        // Tamper with a byte
        wrapped[12] ^= 0x01;
        let result = aes_unwrap_128(&kek, &wrapped);
        assert!(result.is_none(), "Tampered wrapped key should fail integrity check");
    }

    // Wrong KEK should fail integrity check
    #[test]
    fn test_unwrap_wrong_kek_fails() {
        let kek: AesKey = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
            0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F,
        ];
        let wrong_kek: AesKey = [
            0xFF, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
            0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F,
        ];
        let key_data: [u8; 16] = [
            0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
            0x88, 0x99, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF,
        ];

        let wrapped = aes_wrap_128(&kek, &key_data);
        let result = aes_unwrap_128(&wrong_kek, &wrapped);
        assert!(result.is_none(), "Wrong KEK should fail integrity check");
    }

    // IV check tests
    #[test]
    fn test_iv_check_valid() {
        assert!(iv_check(&DEFAULT_IV), "Default IV should pass");
    }

    #[test]
    fn test_iv_check_invalid() {
        let bad_iv: HalfBlock = [0xA6, 0xA6, 0xA6, 0xA6, 0xA6, 0xA6, 0xA6, 0x00];
        assert!(!iv_check(&bad_iv), "Modified IV should fail");
    }

    // Half-block operations
    #[test]
    fn test_concat_split() {
        let left: HalfBlock = [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08];
        let right: HalfBlock = [0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10];
        let block = concat_halves(&left, &right);
        assert_eq!(msb64(&block), left, "MSB should match left");
        assert_eq!(lsb64(&block), right, "LSB should match right");
    }

    // u64 encoding
    #[test]
    fn test_u64_to_be_bytes() {
        let val: u64 = 0x0102030405060708;
        let bytes = u64_to_be_bytes(val);
        assert_eq!(bytes, [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08]);
    }

    #[test]
    fn test_u64_to_be_bytes_one() {
        let bytes = u64_to_be_bytes(1);
        assert_eq!(bytes, [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01]);
    }

    // S-box spot checks
    #[test]
    fn test_sbox_known_values() {
        assert_eq!(AES_SBOX[0x00], 0x63);
        assert_eq!(AES_SBOX[0x01], 0x7c);
        assert_eq!(AES_SBOX[0x53], 0xed);
        assert_eq!(AES_SBOX[0xff], 0x16);
    }

    // Inverse S-box spot checks
    #[test]
    fn test_inv_sbox_known_values() {
        assert_eq!(AES_INV_SBOX[0x63], 0x00);
        assert_eq!(AES_INV_SBOX[0x7c], 0x01);
        assert_eq!(AES_INV_SBOX[0xed], 0x53);
        assert_eq!(AES_INV_SBOX[0x16], 0xff);
    }

    // S-box / inverse S-box roundtrip
    #[test]
    fn test_sbox_inv_roundtrip() {
        for i in 0..256 {
            let x = i as u8;
            assert_eq!(AES_INV_SBOX[AES_SBOX[x as usize] as usize], x,
                "S-box -> InvS-box roundtrip failed for {}", x);
            assert_eq!(AES_SBOX[AES_INV_SBOX[x as usize] as usize], x,
                "InvS-box -> S-box roundtrip failed for {}", x);
        }
    }

    // GF(2^8) tests
    #[test]
    fn test_gf_mul2_known() {
        assert_eq!(gf_mul2(0x57), 0xae);
        assert_eq!(gf_mul2(0x00), 0x00);
        assert_eq!(gf_mul2(0x01), 0x02);
        assert_eq!(gf_mul2(0x80), 0x1b);
    }

    // Wrap with generic interface using 3 blocks (192-bit key data)
    #[test]
    fn test_wrap_unwrap_roundtrip_192() {
        let kek: AesKey = [
            0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6,
            0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c,
        ];
        let mut key_data: [HalfBlock; MAX_BLOCKS] = [[0u8; 8]; MAX_BLOCKS];
        key_data[0] = [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08];
        key_data[1] = [0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10];
        key_data[2] = [0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18];

        let (a, r) = aes_wrap(&kek, &key_data, 3);
        let result = aes_unwrap(&kek, &a, &r, 3);
        assert!(result.is_some(), "192-bit roundtrip should succeed");
        let unwrapped = result.unwrap();
        for i in 0..3 {
            assert_eq!(unwrapped[i], key_data[i], "192-bit block {} mismatch", i);
        }
    }
}
