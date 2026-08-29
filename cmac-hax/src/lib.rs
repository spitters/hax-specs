// Copyright (c) 2026 CatCrypt Contributors. MIT license.
//! AES-CMAC (NIST SP 800-38B): Hax-extractable implementation.
//!
//! CMAC (Cipher-based MAC) uses AES in CBC-MAC mode with subkey derivation.
//! Also known as OMAC1.
//!
//! Construction:
//!   1. Generate subkeys K1, K2 from AES_K(0^128) via `dbl` in GF(2^128)
//!   2. Process message blocks with CBC-MAC
//!   3. XOR last block with K1 (complete) or K2 (incomplete + padding)
//!
//! All loops are bounded `for i in 0..N`, all arithmetic is wrapping,
//! all buffers are fixed-size arrays.
//!
//! The Lean extraction (`proofs/lean/extraction/Cmac_hax.lean`) is produced by
//! `cargo hax into lean` and consumed by the CatCrypt library.

#![no_std]
// Indexed `for i in 0..N` loops and explicit integer arithmetic are the fragment
// the hax Lean backend extracts; the iterator and `div_ceil` rewrites clippy
// suggests fall outside it.
#![allow(
    clippy::needless_range_loop,
    clippy::manual_memcpy,
    clippy::manual_div_ceil,
    clippy::manual_is_multiple_of
)]

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

/// Maximum message length for bounded iteration: 64 blocks = 1024 bytes.
pub const MAX_BLOCKS: usize = 64;

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
    // W[0..43] as 4-byte words, stored in round key blocks
    let mut rk: RoundKeys = [[0u8; 16]; 11];

    // Copy initial key into first round key
    for i in 0..16 {
        rk[0][i] = key[i];
    }

    // Expand: for each subsequent word W[i] (i = 4..43)
    // W[i] = W[i-4] XOR temp
    // where temp = SubWord(RotWord(W[i-1])) XOR Rcon[i/4] if i%4 == 0
    //              else W[i-1]
    for round in 1..11 {
        // Extract last word of previous round key: W[4*round - 1]
        let prev_last: [u8; 4] = [
            rk[round - 1][12], rk[round - 1][13],
            rk[round - 1][14], rk[round - 1][15],
        ];

        // RotWord + SubWord + Rcon
        let rotated = rot_word(prev_last);
        let subbed = sub_word(rotated);
        let rcon_byte = RCON[round - 1];

        // W[4*round] = W[4*(round-1)] XOR SubWord(RotWord(W[4*round-1])) XOR Rcon
        rk[round][0] = rk[round - 1][0] ^ subbed[0] ^ rcon_byte;
        rk[round][1] = rk[round - 1][1] ^ subbed[1];
        rk[round][2] = rk[round - 1][2] ^ subbed[2];
        rk[round][3] = rk[round - 1][3] ^ subbed[3];

        // W[4*round+j] = W[4*(round-1)+j] XOR W[4*round+j-1] for j=1,2,3
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
    // Row 0: no shift
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
// CMAC subkey generation (SP 800-38B, Section 6.1)
// =========================================================================

/// GF(2^128) constant R_b = 0^120 || 10000111 = 0x00...0087.
/// Used in the `dbl` operation for subkey derivation.
const RB: Block = [
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x87,
];

/// Doubling in GF(2^128): left-shift by 1, XOR with R_b if MSB was 1.
///
/// This is the core operation for CMAC subkey generation.
pub fn dbl(block: &Block) -> Block {
    let msb = block[0] & 0x80; // check MSB
    let mut result: Block = [0u8; 16];

    // Left shift by 1 bit
    for i in 0..15 {
        result[i] = (block[i] << 1) | (block[i + 1] >> 7);
    }
    result[15] = block[15] << 1;

    // Conditional XOR with R_b if MSB was set
    if msb != 0 {
        for i in 0..16 {
            result[i] ^= RB[i];
        }
    }

    result
}

/// CMAC subkey generation (SP 800-38B, Section 6.1).
///
/// 1. L = AES_K(0^128)
/// 2. K1 = dbl(L)
/// 3. K2 = dbl(K1)
///
/// Returns (K1, K2).
pub fn cmac_subkey_gen(key: &AesKey) -> (Block, Block) {
    let l = aes128_encrypt(key, &ZERO_BLOCK);
    let k1 = dbl(&l);
    let k2 = dbl(&k1);
    (k1, k2)
}

// =========================================================================
// CMAC MAC generation (SP 800-38B, Section 6.2)
// =========================================================================

/// CMAC padding: append 1-bit then zeros to fill a block.
///
/// `data` contains `len` bytes (0 <= len < 16). Pads to a full 16-byte block.
fn cmac_pad(data: &[u8; 16], len: usize) -> Block {
    let mut padded: Block = [0u8; 16];
    for i in 0..16 {
        if i < len {
            padded[i] = data[i];
        } else if i == len {
            padded[i] = 0x80;
        }
        // remaining bytes stay 0
    }
    padded
}

/// AES-CMAC computation (SP 800-38B, Section 6.2).
///
/// Computes CMAC-AES-128 over a message of `msg_len` bytes.
/// Message is provided in `blocks` as complete 16-byte blocks;
/// `msg_len` indicates the actual message length in bytes.
///
/// # Arguments
/// * `key` - 16-byte AES-128 key
/// * `blocks` - message split into 16-byte blocks (last may be partial)
/// * `num_blocks` - number of blocks used (0 for empty message)
/// * `msg_len` - total message length in bytes
///
/// # Returns
/// 16-byte CMAC tag
pub fn cmac(key: &AesKey, blocks: &[[u8; 16]; MAX_BLOCKS], num_blocks: usize, msg_len: usize) -> Block {
    let (k1, k2) = cmac_subkey_gen(key);

    if msg_len == 0 {
        // Special case: empty message
        // M_last = K2 XOR pad(empty) = K2 XOR (0x80 || 0^112)
        let empty: [u8; 16] = [0u8; 16];
        let padded = cmac_pad(&empty, 0);
        let m_last = xor_block(&k2, &padded);
        return aes128_encrypt(key, &m_last);
    }

    // Determine if last block is complete
    let last_block_len = if msg_len % 16 == 0 { 16 } else { msg_len % 16 };
    let is_complete = last_block_len == 16;

    // CBC-MAC over first (n-1) blocks
    let mut x: Block = ZERO_BLOCK;
    for i in 0..MAX_BLOCKS {
        if i >= num_blocks {
            break;
        }
        if i < num_blocks - 1 {
            // Process intermediate block: Y = AES_K(X XOR M_i)
            let y = xor_block(&x, &blocks[i]);
            x = aes128_encrypt(key, &y);
        } else {
            // Last block: XOR with K1 or K2
            if is_complete {
                let m_last = xor_block(&blocks[i], &k1);
                let y = xor_block(&x, &m_last);
                x = aes128_encrypt(key, &y);
            } else {
                let padded = cmac_pad(&blocks[i], last_block_len);
                let m_last = xor_block(&padded, &k2);
                let y = xor_block(&x, &m_last);
                x = aes128_encrypt(key, &y);
            }
        }
    }

    x
}

/// Convenience: compute CMAC over a flat byte array (up to MAX_BLOCKS * 16 bytes).
///
/// Splits the message into 16-byte blocks and calls `cmac`.
pub fn cmac_bytes(key: &AesKey, msg: &[u8], msg_len: usize) -> Block {
    let mut blocks: [[u8; 16]; MAX_BLOCKS] = [[0u8; 16]; MAX_BLOCKS];
    let num_blocks = if msg_len == 0 { 0 } else { (msg_len + 15) / 16 };

    for i in 0..MAX_BLOCKS {
        if i >= num_blocks {
            break;
        }
        for j in 0..16 {
            let idx = i * 16 + j;
            if idx < msg_len {
                blocks[i][j] = msg[idx];
            }
        }
    }

    cmac(key, &blocks, num_blocks, msg_len)
}

// =========================================================================
// Kani harnesses
// =========================================================================

#[cfg(kani)]
mod kani_harnesses {
    use super::*;

    /// dbl(0) should produce 0 (left shift of zero is zero, MSB=0 so no XOR).
    #[kani::proof]
    fn dbl_zero_is_zero() {
        let zero = ZERO_BLOCK;
        let result = dbl(&zero);
        for i in 0..16 {
            assert_eq!(result[i], 0);
        }
    }

    /// dbl is deterministic: same input always produces same output.
    #[kani::proof]
    fn dbl_deterministic() {
        let input: [u8; 16] = kani::any();
        let r1 = dbl(&input);
        let r2 = dbl(&input);
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

    // SP 800-38B Section D.1: AES-128 CMAC subkey generation
    #[test]
    fn test_cmac_subkeys_sp800_38b() {
        let key: AesKey = [
            0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6,
            0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c,
        ];
        // L = AES_K(0^128) = 7df76b0c 1ab899b3 3e42f047 b91b546f
        let l = aes128_encrypt(&key, &ZERO_BLOCK);
        let expected_l: Block = [
            0x7d, 0xf7, 0x6b, 0x0c, 0x1a, 0xb8, 0x99, 0xb3,
            0x3e, 0x42, 0xf0, 0x47, 0xb9, 0x1b, 0x54, 0x6f,
        ];
        assert_eq!(l, expected_l, "L = AES_K(0^128)");

        let (k1, k2) = cmac_subkey_gen(&key);

        // K1 = fbeed618 35713366 7c85e08f 7236a8de
        let expected_k1: Block = [
            0xfb, 0xee, 0xd6, 0x18, 0x35, 0x71, 0x33, 0x66,
            0x7c, 0x85, 0xe0, 0x8f, 0x72, 0x36, 0xa8, 0xde,
        ];
        assert_eq!(k1, expected_k1, "K1 = dbl(L)");

        // K2 = f7ddac30 6ae266cc f90bc11e e46d513b
        let expected_k2: Block = [
            0xf7, 0xdd, 0xac, 0x30, 0x6a, 0xe2, 0x66, 0xcc,
            0xf9, 0x0b, 0xc1, 0x1e, 0xe4, 0x6d, 0x51, 0x3b,
        ];
        assert_eq!(k2, expected_k2, "K2 = dbl(K1)");
    }

    // SP 800-38B Section D.1, Example 1: empty message (Mlen = 0)
    #[test]
    fn test_cmac_empty_message() {
        let key: AesKey = [
            0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6,
            0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c,
        ];
        let expected_tag: Block = [
            0xbb, 0x1d, 0x69, 0x29, 0xe9, 0x59, 0x37, 0x28,
            0x7f, 0xa3, 0x7d, 0x12, 0x9b, 0x75, 0x67, 0x46,
        ];
        let blocks: [[u8; 16]; MAX_BLOCKS] = [[0u8; 16]; MAX_BLOCKS];
        let tag = cmac(&key, &blocks, 0, 0);
        assert_eq!(tag, expected_tag, "CMAC empty message (D.1 Example 1)");
    }

    // SP 800-38B Section D.1, Example 2: 16-byte message (1 complete block)
    #[test]
    fn test_cmac_16_bytes() {
        let key: AesKey = [
            0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6,
            0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c,
        ];
        let msg: [u8; 16] = [
            0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96,
            0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a,
        ];
        let expected_tag: Block = [
            0x07, 0x0a, 0x16, 0xb4, 0x6b, 0x4d, 0x41, 0x44,
            0xf7, 0x9b, 0xdd, 0x9d, 0xd0, 0x4a, 0x28, 0x7c,
        ];
        let tag = cmac_bytes(&key, &msg, 16);
        assert_eq!(tag, expected_tag, "CMAC 16-byte message (D.1 Example 2)");
    }

    // SP 800-38B Section D.1, Example 3: 40-byte message (incomplete last block)
    #[test]
    fn test_cmac_40_bytes() {
        let key: AesKey = [
            0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6,
            0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c,
        ];
        let msg: [u8; 40] = [
            0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96,
            0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a,
            0xae, 0x2d, 0x8a, 0x57, 0x1e, 0x03, 0xac, 0x9c,
            0x9e, 0xb7, 0x6f, 0xac, 0x45, 0xaf, 0x8e, 0x51,
            0x30, 0xc8, 0x1c, 0x46, 0xa3, 0x5c, 0xe4, 0x11,
        ];
        let expected_tag: Block = [
            0xdf, 0xa6, 0x67, 0x47, 0xde, 0x9a, 0xe6, 0x30,
            0x30, 0xca, 0x32, 0x61, 0x14, 0x97, 0xc8, 0x27,
        ];
        let tag = cmac_bytes(&key, &msg, 40);
        assert_eq!(tag, expected_tag, "CMAC 40-byte message (D.1 Example 3)");
    }

    // SP 800-38B Section D.1, Example 4: 64-byte message (4 complete blocks)
    #[test]
    fn test_cmac_64_bytes() {
        let key: AesKey = [
            0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6,
            0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c,
        ];
        let msg: [u8; 64] = [
            0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96,
            0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a,
            0xae, 0x2d, 0x8a, 0x57, 0x1e, 0x03, 0xac, 0x9c,
            0x9e, 0xb7, 0x6f, 0xac, 0x45, 0xaf, 0x8e, 0x51,
            0x30, 0xc8, 0x1c, 0x46, 0xa3, 0x5c, 0xe4, 0x11,
            0xe5, 0xfb, 0xc1, 0x19, 0x1a, 0x0a, 0x52, 0xef,
            0xf6, 0x9f, 0x24, 0x45, 0xdf, 0x4f, 0x9b, 0x17,
            0xad, 0x2b, 0x41, 0x7b, 0xe6, 0x6c, 0x37, 0x10,
        ];
        let expected_tag: Block = [
            0x51, 0xf0, 0xbe, 0xbf, 0x7e, 0x3b, 0x9d, 0x92,
            0xfc, 0x49, 0x74, 0x17, 0x79, 0x36, 0x3c, 0xfe,
        ];
        let tag = cmac_bytes(&key, &msg, 64);
        assert_eq!(tag, expected_tag, "CMAC 64-byte message (D.1 Example 4)");
    }

    // dbl properties
    #[test]
    fn test_dbl_zero() {
        let result = dbl(&ZERO_BLOCK);
        assert_eq!(result, ZERO_BLOCK, "dbl(0) should be 0");
    }

    #[test]
    fn test_dbl_msb_set() {
        // When MSB is set, result should include XOR with R_b
        let mut input: Block = [0u8; 16];
        input[0] = 0x80; // MSB set
        let result = dbl(&input);
        // Left shift: 0x80 << 1 = 0x00 (with carry), then XOR with R_b
        // Expected: 0x00...0087
        assert_eq!(result[15], 0x87, "dbl with MSB set should XOR R_b");
        assert_eq!(result[0], 0x00, "dbl with MSB set: byte 0");
    }

    #[test]
    fn test_dbl_no_msb() {
        // When MSB is not set, pure left shift
        let mut input: Block = [0u8; 16];
        input[0] = 0x40; // no MSB
        let result = dbl(&input);
        assert_eq!(result[0], 0x80, "dbl without MSB: simple left shift");
        assert_eq!(result[15], 0x00, "dbl without MSB: no R_b XOR");
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
}
