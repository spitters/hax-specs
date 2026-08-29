// Copyright (c) 2026 CatCrypt Contributors. MIT license.
//! XTS-AES-128 (IEEE Std 1619-2018): hax-extractable implementation.
//!
//! XTS (XEX-based Tweaked-codebook mode with ciphertext Stealing) is a
//! tweakable block cipher mode designed for disk/storage encryption.
//!
//! Construction (per data unit / sector):
//!   1. Encrypt the tweak (sector number) with Key2: T = AES_K2(tweak)
//!   2. For each 16-byte block j:
//!      a. PP = plaintext_j XOR T
//!      b. CC = AES_K1(PP)
//!      c. ciphertext_j = CC XOR T
//!      d. T = T * alpha in GF(2^128) (little-endian)
//!
//! Data units are sequences of whole 16-byte blocks (at most `MAX_BLOCKS`);
//! ciphertext stealing for a partial final block (IEEE Std 1619-2018,
//! Section 5.3.1) is not implemented.
//!
//! All loops are bounded `for i in 0..N`, all arithmetic is wrapping,
//! all buffers are fixed-size arrays.

#![no_std]
// The index-loop, fixed-array style is what hax extracts; these lints ask for
// iterator and slice forms that it does not.
#![allow(clippy::needless_range_loop, clippy::manual_memcpy)]

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

/// Zero block constant.
pub const ZERO_BLOCK: Block = [0u8; 16];

/// Maximum number of 16-byte blocks per sector (32 blocks = 512 bytes).
pub const MAX_BLOCKS: usize = 32;

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

    aes_add_round_key(&mut state, &rk[0]);

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
/// Performs 10 inverse rounds: initial AddRoundKey(10), 9 full inverse rounds,
/// 1 final inverse round.
pub fn aes128_decrypt(key: &AesKey, ciphertext: &Block) -> Block {
    let rk = aes128_key_expansion(key);
    let mut state = *ciphertext;

    // Initial round key addition with last round key
    aes_add_round_key(&mut state, &rk[10]);

    // Rounds 9 down to 1: InvShiftRows + InvSubBytes + AddRoundKey + InvMixColumns
    for round in (1..10).rev() {
        aes_inv_shift_rows(&mut state);
        aes_inv_sub_bytes(&mut state);
        aes_add_round_key(&mut state, &rk[round]);
        aes_inv_mix_columns(&mut state);
    }

    // Final round: InvShiftRows + InvSubBytes + AddRoundKey (no InvMixColumns)
    aes_inv_shift_rows(&mut state);
    aes_inv_sub_bytes(&mut state);
    aes_add_round_key(&mut state, &rk[0]);

    state
}

// =========================================================================
// GF(2^128) multiplication by alpha (IEEE Std 1619-2018, Section 5.2)
// =========================================================================

/// Multiply a tweak value by alpha in GF(2^128) with polynomial
/// x^128 + x^7 + x^2 + x + 1.
///
/// XTS uses little-endian bit ordering:
/// - The tweak is treated as a 128-bit little-endian integer
/// - Multiplication by alpha = left shift of the LE integer
/// - Byte 0 is least significant, byte 15 is most significant
/// - If bit 127 (`byte[15]` bit 7) was set, XOR 0x87 into `byte[0]`
///
/// Concretely:
/// ```text
/// carry_out = (tweak[15] >> 7) & 1
/// for i in (1..16).rev(): result[i] = (tweak[i] << 1) | (tweak[i-1] >> 7)
/// result[0] = (tweak[0] << 1) ^ (carry_out * 0x87)
/// ```
pub fn gf128_mul_alpha(tweak: &Block) -> Block {
    let mut result: Block = [0u8; 16];
    let carry_out = (tweak[15] >> 7) & 1;

    // Shift left as a little-endian 128-bit integer:
    // MSB of byte[i-1] becomes LSB of byte[i]
    for i in (1..16).rev() {
        result[i] = (tweak[i] << 1) | (tweak[i - 1] >> 7);
    }
    result[0] = (tweak[0] << 1) ^ (carry_out.wrapping_mul(0x87));

    result
}

// =========================================================================
// XTS-AES encryption/decryption (IEEE Std 1619-2018, Section 5.3)
// =========================================================================

/// Encrypt a single 16-byte block using XTS-AES.
///
/// # Arguments
/// * `key1` - AES key for data encryption
/// * `key2` - AES key for tweak encryption
/// * `tweak_input` - 16-byte tweak (typically sector number in LE)
/// * `block_index` - block index within the data unit (for alpha multiplication)
/// * `plaintext` - 16-byte plaintext block
///
/// # Returns
/// 16-byte ciphertext block
///
/// Algorithm:
///   T = AES_K2(tweak_input) then multiply by alpha `block_index` times
///   PP = plaintext XOR T
///   CC = AES_K1(PP)
///   ciphertext = CC XOR T
pub fn xts_encrypt_block(
    key1: &AesKey,
    key2: &AesKey,
    tweak_input: &Block,
    block_index: usize,
    plaintext: &Block,
) -> Block {
    // Encrypt tweak with key2
    let mut tweak = aes128_encrypt(key2, tweak_input);

    // Multiply by alpha block_index times
    for i in 0..MAX_BLOCKS {
        if i >= block_index {
            break;
        }
        tweak = gf128_mul_alpha(&tweak);
    }

    // PP = plaintext XOR T
    let pp = xor_block(plaintext, &tweak);

    // CC = AES_K1(PP)
    let cc = aes128_encrypt(key1, &pp);

    // ciphertext = CC XOR T
    xor_block(&cc, &tweak)
}

/// Decrypt a single 16-byte block using XTS-AES.
///
/// # Arguments
/// * `key1` - AES key for data encryption/decryption
/// * `key2` - AES key for tweak encryption
/// * `tweak_input` - 16-byte tweak (typically sector number in LE)
/// * `block_index` - block index within the data unit (for alpha multiplication)
/// * `ciphertext` - 16-byte ciphertext block
///
/// # Returns
/// 16-byte plaintext block
///
/// Algorithm:
///   T = AES_K2(tweak_input) then multiply by alpha `block_index` times
///   CC = ciphertext XOR T
///   PP = AES_K1_decrypt(CC)
///   plaintext = PP XOR T
pub fn xts_decrypt_block(
    key1: &AesKey,
    key2: &AesKey,
    tweak_input: &Block,
    block_index: usize,
    ciphertext: &Block,
) -> Block {
    // Encrypt tweak with key2
    let mut tweak = aes128_encrypt(key2, tweak_input);

    // Multiply by alpha block_index times
    for i in 0..MAX_BLOCKS {
        if i >= block_index {
            break;
        }
        tweak = gf128_mul_alpha(&tweak);
    }

    // CC = ciphertext XOR T
    let cc = xor_block(ciphertext, &tweak);

    // PP = AES_K1_decrypt(CC)
    let pp = aes128_decrypt(key1, &cc);

    // plaintext = PP XOR T
    xor_block(&pp, &tweak)
}

/// Encrypt a full sector (sequence of 16-byte blocks) using XTS-AES.
///
/// # Arguments
/// * `key1` - AES key for data encryption
/// * `key2` - AES key for tweak encryption
/// * `tweak_input` - 16-byte tweak (sector number encoded as LE 128-bit)
/// * `data_blocks` - array of plaintext blocks (up to MAX_BLOCKS)
/// * `num_blocks` - number of blocks to encrypt (1..=MAX_BLOCKS)
///
/// # Returns
/// Array of encrypted blocks (same size as input)
pub fn xts_encrypt_sector(
    key1: &AesKey,
    key2: &AesKey,
    tweak_input: &Block,
    data_blocks: &[[u8; 16]; MAX_BLOCKS],
    num_blocks: usize,
) -> [[u8; 16]; MAX_BLOCKS] {
    let mut result: [[u8; 16]; MAX_BLOCKS] = [[0u8; 16]; MAX_BLOCKS];

    // Encrypt tweak with key2 once
    let mut tweak = aes128_encrypt(key2, tweak_input);

    for i in 0..MAX_BLOCKS {
        if i >= num_blocks {
            break;
        }

        // PP = plaintext XOR T
        let pp = xor_block(&data_blocks[i], &tweak);

        // CC = AES_K1(PP)
        let cc = aes128_encrypt(key1, &pp);

        // ciphertext = CC XOR T
        result[i] = xor_block(&cc, &tweak);

        // Advance tweak: T = T * alpha
        tweak = gf128_mul_alpha(&tweak);
    }

    result
}

/// Decrypt a full sector (sequence of 16-byte blocks) using XTS-AES.
///
/// # Arguments
/// * `key1` - AES key for data decryption
/// * `key2` - AES key for tweak encryption
/// * `tweak_input` - 16-byte tweak (sector number encoded as LE 128-bit)
/// * `data_blocks` - array of ciphertext blocks (up to MAX_BLOCKS)
/// * `num_blocks` - number of blocks to decrypt (1..=MAX_BLOCKS)
///
/// # Returns
/// Array of decrypted blocks (same size as input)
pub fn xts_decrypt_sector(
    key1: &AesKey,
    key2: &AesKey,
    tweak_input: &Block,
    data_blocks: &[[u8; 16]; MAX_BLOCKS],
    num_blocks: usize,
) -> [[u8; 16]; MAX_BLOCKS] {
    let mut result: [[u8; 16]; MAX_BLOCKS] = [[0u8; 16]; MAX_BLOCKS];

    // Encrypt tweak with key2 once
    let mut tweak = aes128_encrypt(key2, tweak_input);

    for i in 0..MAX_BLOCKS {
        if i >= num_blocks {
            break;
        }

        // CC = ciphertext XOR T
        let cc = xor_block(&data_blocks[i], &tweak);

        // PP = AES_K1_decrypt(CC)
        let pp = aes128_decrypt(key1, &cc);

        // plaintext = PP XOR T
        result[i] = xor_block(&pp, &tweak);

        // Advance tweak: T = T * alpha
        tweak = gf128_mul_alpha(&tweak);
    }

    result
}

/// Convenience: encode a 64-bit sector number as a 16-byte LE tweak block.
///
/// The sector number is placed in the first 8 bytes in little-endian order;
/// the remaining 8 bytes are zero.
pub fn sector_number_to_tweak(sector_number: u64) -> Block {
    let mut tweak: Block = [0u8; 16];
    let bytes = sector_number.to_le_bytes();
    for i in 0..8 {
        tweak[i] = bytes[i];
    }
    tweak
}

// =========================================================================
// Kani harnesses
// =========================================================================

#[cfg(kani)]
mod kani_harnesses {
    use super::*;

    /// gf128_mul_alpha(0) should produce 0.
    #[kani::proof]
    fn gf128_mul_alpha_zero_is_zero() {
        let zero = ZERO_BLOCK;
        let result = gf128_mul_alpha(&zero);
        for i in 0..16 {
            assert_eq!(result[i], 0);
        }
    }

    /// gf128_mul_alpha is deterministic: same input always produces same output.
    #[kani::proof]
    fn gf128_mul_alpha_deterministic() {
        let input: [u8; 16] = kani::any();
        let r1 = gf128_mul_alpha(&input);
        let r2 = gf128_mul_alpha(&input);
        for i in 0..16 {
            assert_eq!(r1[i], r2[i]);
        }
    }

    /// XOR self is zero.
    #[kani::proof]
    fn xor_self_is_zero() {
        let a: [u8; 16] = kani::any();
        let result = xor_block(&a, &a);
        for i in 0..16 {
            assert_eq!(result[i], 0);
        }
    }

    /// XOR with zero is identity.
    #[kani::proof]
    fn xor_zero_identity() {
        let a: [u8; 16] = kani::any();
        let result = xor_block(&a, &ZERO_BLOCK);
        for i in 0..16 {
            assert_eq!(result[i], a[i]);
        }
    }

    /// GF(2^8) mul2(0) = 0.
    #[kani::proof]
    fn gf_mul2_zero() {
        assert_eq!(gf_mul2(0), 0);
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

    /// Inverse S-box is the inverse of S-box.
    #[kani::proof]
    fn sbox_inv_sbox_roundtrip() {
        let a: u8 = kani::any();
        assert_eq!(AES_INV_SBOX[AES_SBOX[a as usize] as usize], a,
            "InvSBox(SBox(x)) must equal x");
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
        assert_eq!(ct, expected_ct, "AES-128 FIPS 197 Appendix B");
    }

    // AES-128 encrypt/decrypt roundtrip
    #[test]
    fn test_aes128_encrypt_decrypt_roundtrip() {
        let key: AesKey = [
            0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6,
            0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c,
        ];
        let pt: Block = [
            0x32, 0x43, 0xf6, 0xa8, 0x88, 0x5a, 0x30, 0x8d,
            0x31, 0x31, 0x98, 0xa2, 0xe0, 0x37, 0x07, 0x34,
        ];
        let ct = aes128_encrypt(&key, &pt);
        let recovered = aes128_decrypt(&key, &ct);
        assert_eq!(recovered, pt, "AES-128 decrypt(encrypt(pt)) = pt");
    }

    // AES-128 decrypt known vector
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
        assert_eq!(pt, expected_pt, "AES-128 FIPS 197 decrypt");
    }

    // gf128_mul_alpha properties
    #[test]
    fn test_gf128_mul_alpha_zero() {
        let result = gf128_mul_alpha(&ZERO_BLOCK);
        assert_eq!(result, ZERO_BLOCK, "gf128_mul_alpha(0) should be 0");
    }

    #[test]
    fn test_gf128_mul_alpha_one() {
        // alpha * 1 (LE: byte[0]=0x01, rest 0) should give 0x02 in byte[0]
        let mut input: Block = [0u8; 16];
        input[0] = 0x01;
        let result = gf128_mul_alpha(&input);
        assert_eq!(result[0], 0x02, "alpha * 1 = 2 in LE");
        for i in 1..16 {
            assert_eq!(result[i], 0x00);
        }
    }

    #[test]
    fn test_gf128_mul_alpha_carry() {
        // When bit 127 (byte[15] bit 7) is set, should XOR 0x87 into byte[0]
        let mut input: Block = [0u8; 16];
        input[15] = 0x80; // bit 127 set
        let result = gf128_mul_alpha(&input);
        // Left shift: 0x80 << 1 = 0x00 with carry, so byte[15] = 0
        // XOR 0x87 into byte[0]
        assert_eq!(result[0], 0x87, "carry should XOR 0x87 into byte 0");
        for i in 1..16 {
            assert_eq!(result[i], 0x00);
        }
    }

    #[test]
    fn test_gf128_mul_alpha_byte_carry() {
        // byte[0] = 0x80 should carry into byte[1]
        let mut input: Block = [0u8; 16];
        input[0] = 0x80;
        let result = gf128_mul_alpha(&input);
        assert_eq!(result[0], 0x00, "byte 0: 0x80 << 1 = 0x00");
        assert_eq!(result[1], 0x01, "byte 1: carry from byte 0");
    }

    // Sector number encoding
    #[test]
    fn test_sector_number_to_tweak() {
        let tweak = sector_number_to_tweak(0);
        assert_eq!(tweak, ZERO_BLOCK);

        let tweak = sector_number_to_tweak(1);
        let mut expected: Block = [0u8; 16];
        expected[0] = 0x01;
        assert_eq!(tweak, expected);

        let tweak = sector_number_to_tweak(0x0102030405060708);
        assert_eq!(tweak[0], 0x08); // LE
        assert_eq!(tweak[7], 0x01);
    }

    // IEEE 1619 Vector 1: all zeros
    #[test]
    fn test_xts_ieee1619_vector1() {
        let key1: AesKey = [0u8; 16];
        let key2: AesKey = [0u8; 16];
        let tweak = sector_number_to_tweak(0);
        let pt: [[u8; 16]; MAX_BLOCKS] = [[0u8; 16]; MAX_BLOCKS];

        let ct = xts_encrypt_sector(&key1, &key2, &tweak, &pt, 2);

        let expected_ct0: Block = [
            0x91, 0x7c, 0xf6, 0x9e, 0xbd, 0x68, 0xb2, 0xec,
            0x9b, 0x9f, 0xe9, 0xa3, 0xea, 0xdd, 0xa6, 0x92,
        ];
        let expected_ct1: Block = [
            0xcd, 0x43, 0xd2, 0xf5, 0x95, 0x98, 0xed, 0x85,
            0x8c, 0x02, 0xc2, 0x65, 0x2f, 0xbf, 0x92, 0x2e,
        ];
        assert_eq!(ct[0], expected_ct0, "IEEE 1619 Vector 1, block 0");
        assert_eq!(ct[1], expected_ct1, "IEEE 1619 Vector 1, block 1");
    }

    // XTS encrypt/decrypt roundtrip
    #[test]
    fn test_xts_encrypt_decrypt_roundtrip() {
        let key1: AesKey = [
            0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6,
            0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c,
        ];
        let key2: AesKey = [
            0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef,
            0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54, 0x32, 0x10,
        ];
        let tweak = sector_number_to_tweak(42);

        let mut pt: [[u8; 16]; MAX_BLOCKS] = [[0u8; 16]; MAX_BLOCKS];
        for i in 0..4 {
            for j in 0..16 {
                pt[i][j] = ((i * 16 + j) & 0xff) as u8;
            }
        }

        let ct = xts_encrypt_sector(&key1, &key2, &tweak, &pt, 4);
        let recovered = xts_decrypt_sector(&key1, &key2, &tweak, &ct, 4);

        for i in 0..4 {
            assert_eq!(recovered[i], pt[i], "roundtrip block {}", i);
        }
    }

    // XTS single block encrypt/decrypt roundtrip
    #[test]
    fn test_xts_block_roundtrip() {
        let key1: AesKey = [0x11u8; 16];
        let key2: AesKey = [0x22u8; 16];
        let tweak: Block = [0x33, 0x33, 0x33, 0x33, 0x33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
        let pt: Block = [0x44u8; 16];

        let ct = xts_encrypt_block(&key1, &key2, &tweak, 0, &pt);
        let recovered = xts_decrypt_block(&key1, &key2, &tweak, 0, &ct);
        assert_eq!(recovered, pt, "single block roundtrip");
    }

    // S-box / inverse S-box roundtrip
    #[test]
    fn test_sbox_inv_sbox_roundtrip() {
        for i in 0..256 {
            let x = i as u8;
            assert_eq!(AES_INV_SBOX[AES_SBOX[x as usize] as usize], x,
                "InvSBox(SBox({})) != {}", x, x);
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

    // S-box spot checks
    #[test]
    fn test_sbox_known_values() {
        assert_eq!(AES_SBOX[0x00], 0x63);
        assert_eq!(AES_SBOX[0x01], 0x7c);
        assert_eq!(AES_SBOX[0x53], 0xed);
        assert_eq!(AES_SBOX[0xff], 0x16);
    }

    // XOR block properties
    #[test]
    fn test_xor_involution() {
        let a: Block = [
            0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc, 0xde, 0xf0,
            0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88,
        ];
        let b: Block = [
            0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54, 0x32, 0x10,
            0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
        ];
        let c = xor_block(&a, &b);
        let recovered = xor_block(&c, &b);
        assert_eq!(recovered, a, "XOR is involutory: (a ^ b) ^ b = a");
    }
}
