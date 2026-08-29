// Copyright (c) 2026 CatCrypt Contributors. MIT license.
//! AES-GCM-SIV (RFC 8452): Hax-extractable implementation.
//!
//! AES-GCM-SIV is a nonce-misuse resistant AEAD (Authenticated Encryption
//! with Associated Data) using Synthetic IV construction.
//!
//! All loops are bounded `for i in 0..N`, all arithmetic is wrapping,
//! all buffers are fixed-size arrays.

#![no_std]
// The index-loop style (`for i in 0..N` with explicit indexing, explicit
// `a + b` / `a - b` arithmetic) is the subset that hax extracts; the iterator
// and slice-method rewrites these lints suggest fall outside it.
#![allow(
    clippy::needless_range_loop,
    clippy::manual_memcpy,
    clippy::manual_div_ceil,
    clippy::implicit_saturating_sub,
    clippy::assign_op_pattern
)]

// =========================================================================
// AES-128 specification (FIPS 197)
// =========================================================================

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

static RCON: [u8; 10] = [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36];

pub type Block = [u8; 16];
pub type AesKey = [u8; 16];
pub type RoundKeys = [[u8; 16]; 11];
pub type Nonce = [u8; 12];
pub const ZERO_BLOCK: Block = [0u8; 16];
pub const MAX_BLOCKS: usize = 32;

// =========================================================================
// Block operations
// =========================================================================

#[inline]
pub fn xor_block(a: &Block, b: &Block) -> Block {
    let mut result: Block = [0u8; 16];
    for i in 0..16 { result[i] = a[i] ^ b[i]; }
    result
}

// =========================================================================
// AES-128
// =========================================================================

#[inline]
fn gf_mul2(x: u8) -> u8 {
    let s = (x as u16) << 1;
    (if x & 0x80 != 0 { s ^ 0x1b } else { s }) as u8
}

#[inline]
fn gf_mul3(x: u8) -> u8 { gf_mul2(x) ^ x }

fn sub_word(w: [u8; 4]) -> [u8; 4] {
    [AES_SBOX[w[0] as usize], AES_SBOX[w[1] as usize],
     AES_SBOX[w[2] as usize], AES_SBOX[w[3] as usize]]
}

fn rot_word(w: [u8; 4]) -> [u8; 4] { [w[1], w[2], w[3], w[0]] }

pub fn aes128_key_expansion(key: &AesKey) -> RoundKeys {
    let mut rk: RoundKeys = [[0u8; 16]; 11];
    for i in 0..16 { rk[0][i] = key[i]; }
    for round in 1..11 {
        let prev_last: [u8; 4] = [
            rk[round-1][12], rk[round-1][13], rk[round-1][14], rk[round-1][15],
        ];
        let subbed = sub_word(rot_word(prev_last));
        let rc = RCON[round - 1];
        rk[round][0] = rk[round-1][0] ^ subbed[0] ^ rc;
        rk[round][1] = rk[round-1][1] ^ subbed[1];
        rk[round][2] = rk[round-1][2] ^ subbed[2];
        rk[round][3] = rk[round-1][3] ^ subbed[3];
        for j in 1..4 {
            let base = j * 4;
            for b in 0..4 { rk[round][base+b] = rk[round-1][base+b] ^ rk[round][base-4+b]; }
        }
    }
    rk
}

fn aes_sub_bytes(s: &mut Block) { for i in 0..16 { s[i] = AES_SBOX[s[i] as usize]; } }

fn aes_shift_rows(s: &mut Block) {
    let t = s[1]; s[1]=s[5]; s[5]=s[9]; s[9]=s[13]; s[13]=t;
    let t0=s[2]; let t1=s[6]; s[2]=s[10]; s[6]=s[14]; s[10]=t0; s[14]=t1;
    let t = s[15]; s[15]=s[11]; s[11]=s[7]; s[7]=s[3]; s[3]=t;
}

fn aes_mix_columns(s: &mut Block) {
    for col in 0..4 {
        let b = col*4;
        let (s0,s1,s2,s3) = (s[b],s[b+1],s[b+2],s[b+3]);
        s[b]   = gf_mul2(s0) ^ gf_mul3(s1) ^ s2 ^ s3;
        s[b+1] = s0 ^ gf_mul2(s1) ^ gf_mul3(s2) ^ s3;
        s[b+2] = s0 ^ s1 ^ gf_mul2(s2) ^ gf_mul3(s3);
        s[b+3] = gf_mul3(s0) ^ s1 ^ s2 ^ gf_mul2(s3);
    }
}

fn aes_add_round_key(s: &mut Block, rk: &Block) { for i in 0..16 { s[i] ^= rk[i]; } }

pub fn aes128_encrypt(key: &AesKey, pt: &Block) -> Block {
    let rk = aes128_key_expansion(key);
    let mut s = *pt;
    aes_add_round_key(&mut s, &rk[0]);
    for round in 1..10 {
        aes_sub_bytes(&mut s); aes_shift_rows(&mut s);
        aes_mix_columns(&mut s); aes_add_round_key(&mut s, &rk[round]);
    }
    aes_sub_bytes(&mut s); aes_shift_rows(&mut s); aes_add_round_key(&mut s, &rk[10]);
    s
}

// =========================================================================
// POLYVAL: GF(2^128) with p(x) = x^128 + x^127 + x^126 + x^121 + 1
// =========================================================================
//
// Field elements: LE bit order (bit 0 of byte 0 = x^0).
// dot(H, X) = H * X * x^{-128} mod p(x)  (RFC 8452, Section 3).

#[inline]
pub fn le_u64(bytes: &[u8], offset: usize) -> u64 {
    let mut v: u64 = 0;
    for i in 0..8 { v |= (bytes[offset + i] as u64) << (i * 8); }
    v
}

#[inline]
pub fn put_le_u64(bytes: &mut [u8], offset: usize, v: u64) {
    for i in 0..8 { bytes[offset + i] = ((v >> (i * 8)) & 0xff) as u8; }
}

/// Reduction constant: q(x) = x^127 + x^126 + x^121 + 1 (= p(x) - x^128).
/// As (lo, hi) in LE u64: q_lo = 1, q_hi = 0xc200000000000000.
const Q_LO: u64 = 0x0000000000000001;
const Q_HI: u64 = 0xc200000000000000;

/// Multiply by x in GF(2^128): left shift by 1 with conditional reduction.
#[inline]
fn gf128_mul_x(lo: &mut u64, hi: &mut u64) {
    let msb = (*hi >> 63) & 1;
    *hi = (*hi << 1) | (*lo >> 63);
    *lo = *lo << 1;
    if msb == 1 {
        *lo ^= Q_LO;
        *hi ^= Q_HI;
    }
}

/// Standard field multiplication: H * X mod p(x).
/// Bit-by-bit schoolbook with online reduction.
fn gf128_mul(h: &Block, x: &Block) -> Block {
    let h0 = le_u64(h, 0);
    let h1 = le_u64(h, 8);
    let x0 = le_u64(x, 0);
    let x1 = le_u64(x, 8);

    let mut v_lo = x0;
    let mut v_hi = x1;
    let mut r_lo: u64 = 0;
    let mut r_hi: u64 = 0;

    for i in 0..64 {
        if (h0 >> i) & 1 == 1 { r_lo ^= v_lo; r_hi ^= v_hi; }
        gf128_mul_x(&mut v_lo, &mut v_hi);
    }
    for i in 0..64 {
        if (h1 >> i) & 1 == 1 { r_lo ^= v_lo; r_hi ^= v_hi; }
        gf128_mul_x(&mut v_lo, &mut v_hi);
    }

    let mut result: Block = [0u8; 16];
    put_le_u64(&mut result, 0, r_lo);
    put_le_u64(&mut result, 8, r_hi);
    result
}

/// x^{-128} mod p(x) = x^127 + x^124 + x^121 + x^114 + 1 (RFC 8452, Section 3).
/// As a Block in LE bit order:
///   bit 0 -> byte 0 bit 0
///   bit 114 -> byte 14 bit 2
///   bit 121 -> byte 15 bit 1
///   bit 124 -> byte 15 bit 4
///   bit 127 -> byte 15 bit 7
const XINV128: Block = [
    0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x92,
];

/// POLYVAL dot product: dot(H, X) = H * X * x^{-128} mod p(x).
///
/// Computed as gf128_mul(gf128_mul(H, X), XINV128).
pub fn polyval_mul(h: &Block, x: &Block) -> Block {
    let hx = gf128_mul(h, x);
    gf128_mul(&hx, &XINV128)
}

/// POLYVAL(H, X_1, ..., X_n):
///   S_0 = 0; S_j = dot(S_{j-1} XOR X_j, H); result = S_n
pub fn polyval(h: &Block, blocks: &[Block; MAX_BLOCKS], num_blocks: usize) -> Block {
    let mut s: Block = ZERO_BLOCK;
    for i in 0..MAX_BLOCKS {
        if i >= num_blocks { break; }
        s = xor_block(&s, &blocks[i]);
        s = polyval_mul(h, &s);
    }
    s
}

// =========================================================================
// AES-GCM-SIV Key Derivation (RFC 8452, Section 4)
// =========================================================================

/// Helper for `derive_keys`: AES-encrypts the block `LE32(ctr) || nonce`.
///
/// RFC 8452 Section 4 derives the record keys from four such blocks
/// (counters 0..3). The loop is unrolled in `derive_keys` so that each
/// output key is assigned from a single straight-line sequence, which keeps
/// the mutable state per loop single-variable for extraction.
fn derive_keys_block(key: &AesKey, nonce: &Nonce, ctr: u32) -> Block {
    let mut input: Block = [0u8; 16];
    input[0] = (ctr & 0xff) as u8;
    input[1] = ((ctr >> 8) & 0xff) as u8;
    input[2] = ((ctr >> 16) & 0xff) as u8;
    input[3] = ((ctr >> 24) & 0xff) as u8;
    for j in 0..12 { input[4 + j] = nonce[j]; }
    aes128_encrypt(key, &input)
}

pub fn derive_keys(key: &AesKey, nonce: &Nonce) -> (Block, Block) {
    let mut auth_key: Block = [0u8; 16];
    let mut enc_key: Block = [0u8; 16];

    // ctr 0,1 -> auth_key.
    let enc0 = derive_keys_block(key, nonce, 0);
    for j in 0..8 { auth_key[j] = enc0[j]; }
    let enc1 = derive_keys_block(key, nonce, 1);
    for j in 0..8 { auth_key[8 + j] = enc1[j]; }
    // ctr 2,3 -> enc_key.
    let enc2 = derive_keys_block(key, nonce, 2);
    for j in 0..8 { enc_key[j] = enc2[j]; }
    let enc3 = derive_keys_block(key, nonce, 3);
    for j in 0..8 { enc_key[8 + j] = enc3[j]; }
    (auth_key, enc_key)
}

// =========================================================================
// AES-GCM-SIV CTR mode (RFC 8452, Section 6)
// =========================================================================

fn gcm_siv_ctr_increment(ctr: &mut Block) {
    let mut val = (ctr[0] as u32) | ((ctr[1] as u32) << 8)
        | ((ctr[2] as u32) << 16) | ((ctr[3] as u32) << 24);
    val = val.wrapping_add(1);
    ctr[0] = (val & 0xff) as u8;
    ctr[1] = ((val >> 8) & 0xff) as u8;
    ctr[2] = ((val >> 16) & 0xff) as u8;
    ctr[3] = ((val >> 24) & 0xff) as u8;
}

fn gcm_siv_ctr_crypt(
    enc_key: &AesKey, tag: &Block,
    in_blocks: &[Block; MAX_BLOCKS], out_blocks: &mut [Block; MAX_BLOCKS],
    num_blocks: usize, msg_len: usize,
) {
    let mut ctr = *tag;
    ctr[15] |= 0x80;

    for i in 0..MAX_BLOCKS {
        if i >= num_blocks { break; }
        let keystream = aes128_encrypt(enc_key, &ctr);
        gcm_siv_ctr_increment(&mut ctr);

        let block_start = i * 16;
        let remaining = if msg_len > block_start { msg_len - block_start } else { 0 };
        let bytes_in_block = if remaining > 16 { 16 } else { remaining };

        out_blocks[i] = [0u8; 16];
        for j in 0..16 {
            if j < bytes_in_block {
                out_blocks[i][j] = in_blocks[i][j] ^ keystream[j];
            }
        }
    }
}

// =========================================================================
// AES-GCM-SIV Seal / Open
// =========================================================================

fn build_polyval_input(
    aad: &[Block; MAX_BLOCKS], num_aad_blocks: usize,
    msg: &[Block; MAX_BLOCKS], num_msg_blocks: usize,
    aad_len: usize, msg_len: usize,
    out: &mut [Block; MAX_BLOCKS],
) -> usize {
    let mut idx: usize = 0;
    for i in 0..MAX_BLOCKS {
        if i >= num_aad_blocks { break; }
        out[idx] = aad[i]; idx += 1;
    }
    for i in 0..MAX_BLOCKS {
        if i >= num_msg_blocks { break; }
        out[idx] = msg[i]; idx += 1;
    }
    let aad_bits = (aad_len as u64).wrapping_mul(8);
    let msg_bits = (msg_len as u64).wrapping_mul(8);
    let mut len_block: Block = [0u8; 16];
    put_le_u64(&mut len_block, 0, aad_bits);
    put_le_u64(&mut len_block, 8, msg_bits);
    out[idx] = len_block; idx += 1;
    idx
}

pub fn bytes_to_blocks(data: &[u8], data_len: usize, blocks: &mut [Block; MAX_BLOCKS]) -> usize {
    if data_len == 0 { return 0; }
    let num_blocks = (data_len + 15) / 16;
    for i in 0..MAX_BLOCKS {
        if i >= num_blocks { break; }
        blocks[i] = [0u8; 16];
        for j in 0..16 {
            let idx = i * 16 + j;
            if idx < data_len { blocks[i][j] = data[idx]; }
        }
    }
    num_blocks
}

pub fn blocks_to_bytes(blocks: &[Block; MAX_BLOCKS], byte_len: usize, out: &mut [u8]) {
    for i in 0..byte_len {
        let block_idx = i / 16;
        let byte_idx = i % 16;
        if block_idx < MAX_BLOCKS && i < out.len() { out[i] = blocks[block_idx][byte_idx]; }
    }
}

pub fn aes_gcm_siv_seal(
    key: &AesKey, nonce: &Nonce,
    aad: &[u8], aad_len: usize,
    plaintext: &[u8], pt_len: usize,
) -> ([Block; MAX_BLOCKS], usize, Block) {
    let (auth_key, enc_key) = derive_keys(key, nonce);

    let mut aad_blocks: [Block; MAX_BLOCKS] = [[0u8; 16]; MAX_BLOCKS];
    let num_aad_blocks = bytes_to_blocks(aad, aad_len, &mut aad_blocks);
    let mut pt_blocks: [Block; MAX_BLOCKS] = [[0u8; 16]; MAX_BLOCKS];
    let num_pt_blocks = bytes_to_blocks(plaintext, pt_len, &mut pt_blocks);

    let mut pv_input: [Block; MAX_BLOCKS] = [[0u8; 16]; MAX_BLOCKS];
    let pv_count = build_polyval_input(
        &aad_blocks, num_aad_blocks, &pt_blocks, num_pt_blocks,
        aad_len, pt_len, &mut pv_input,
    );
    let pv_result = polyval(&auth_key, &pv_input, pv_count);

    let mut tag_input = pv_result;
    for i in 0..12 { tag_input[i] ^= nonce[i]; }
    tag_input[15] &= 0x7f;
    let tag = aes128_encrypt(&enc_key, &tag_input);

    let mut ct_blocks: [Block; MAX_BLOCKS] = [[0u8; 16]; MAX_BLOCKS];
    if pt_len > 0 {
        gcm_siv_ctr_crypt(&enc_key, &tag, &pt_blocks, &mut ct_blocks, num_pt_blocks, pt_len);
    }
    (ct_blocks, num_pt_blocks, tag)
}

pub fn aes_gcm_siv_open(
    key: &AesKey, nonce: &Nonce,
    aad: &[u8], aad_len: usize,
    ciphertext: &[u8], ct_len: usize,
    tag: &Block,
) -> Option<([Block; MAX_BLOCKS], usize)> {
    let (auth_key, enc_key) = derive_keys(key, nonce);

    let mut ct_blocks: [Block; MAX_BLOCKS] = [[0u8; 16]; MAX_BLOCKS];
    let num_ct_blocks = bytes_to_blocks(ciphertext, ct_len, &mut ct_blocks);
    let mut pt_blocks: [Block; MAX_BLOCKS] = [[0u8; 16]; MAX_BLOCKS];
    if ct_len > 0 {
        gcm_siv_ctr_crypt(&enc_key, tag, &ct_blocks, &mut pt_blocks, num_ct_blocks, ct_len);
    }

    let mut aad_blocks: [Block; MAX_BLOCKS] = [[0u8; 16]; MAX_BLOCKS];
    let num_aad_blocks = bytes_to_blocks(aad, aad_len, &mut aad_blocks);

    let mut pv_input: [Block; MAX_BLOCKS] = [[0u8; 16]; MAX_BLOCKS];
    let pv_count = build_polyval_input(
        &aad_blocks, num_aad_blocks, &pt_blocks, num_ct_blocks,
        aad_len, ct_len, &mut pv_input,
    );
    let pv_result = polyval(&auth_key, &pv_input, pv_count);

    let mut tag_input = pv_result;
    for i in 0..12 { tag_input[i] ^= nonce[i]; }
    tag_input[15] &= 0x7f;
    let expected_tag = aes128_encrypt(&enc_key, &tag_input);

    let mut diff: u8 = 0;
    for i in 0..16 { diff |= expected_tag[i] ^ tag[i]; }
    if diff != 0 { None } else { Some((pt_blocks, num_ct_blocks)) }
}

// =========================================================================
// Kani harnesses
// =========================================================================

#[cfg(kani)]
mod kani_harnesses {
    use super::*;

    #[kani::proof]
    fn xor_self_is_zero() {
        let a: Block = kani::any();
        let r = xor_block(&a, &a);
        for i in 0..16 { assert_eq!(r[i], 0); }
    }

    #[kani::proof]
    fn polyval_single_zero() {
        let h: Block = kani::any();
        let mut blocks: [Block; MAX_BLOCKS] = [[0u8; 16]; MAX_BLOCKS];
        blocks[0] = ZERO_BLOCK;
        let r = polyval(&h, &blocks, 1);
        for i in 0..16 { assert_eq!(r[i], 0); }
    }
}

// =========================================================================
// Unit tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_aes128_fips197() {
        let key: AesKey = [0x2b,0x7e,0x15,0x16,0x28,0xae,0xd2,0xa6,
                           0xab,0xf7,0x15,0x88,0x09,0xcf,0x4f,0x3c];
        let pt: Block = [0x32,0x43,0xf6,0xa8,0x88,0x5a,0x30,0x8d,
                         0x31,0x31,0x98,0xa2,0xe0,0x37,0x07,0x34];
        let expected: Block = [0x39,0x25,0x84,0x1d,0x02,0xdc,0x09,0xfb,
                               0xdc,0x11,0x85,0x97,0x19,0x6a,0x0b,0x32];
        assert_eq!(aes128_encrypt(&key, &pt), expected);
    }

    #[test]
    fn test_xor_self_is_zero() {
        let a: Block = [0x12,0x34,0x56,0x78,0x9a,0xbc,0xde,0xf0,
                        0x11,0x22,0x33,0x44,0x55,0x66,0x77,0x88];
        assert_eq!(xor_block(&a, &a), ZERO_BLOCK);
    }

    #[test]
    fn test_polyval_mul_by_zero() {
        let h: Block = [0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,
                        0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f,0x10];
        assert_eq!(polyval_mul(&h, &ZERO_BLOCK), ZERO_BLOCK);
    }

    #[test]
    fn test_polyval_appendix_a() {
        let h: Block = [0x25,0x62,0x93,0x47,0x58,0x92,0x42,0x76,
                        0x1d,0x31,0xf8,0x26,0xba,0x4b,0x75,0x7b];
        let x1: Block = [0x4f,0x4f,0x95,0x66,0x8c,0x83,0xdf,0xb6,
                         0x40,0x17,0x62,0xbb,0x2d,0x01,0xa2,0x62];
        let x2: Block = [0xd1,0xa2,0x4d,0xdd,0x27,0x21,0xd0,0x06,
                         0xbb,0xe4,0x5f,0x20,0xd3,0xc9,0xf3,0x62];
        let expected: Block = [0xf7,0xa3,0xb4,0x7b,0x84,0x61,0x19,0xfa,
                               0xe5,0xb7,0x86,0x6c,0xf5,0xe5,0xb7,0x7e];
        let mut blocks: [Block; MAX_BLOCKS] = [[0u8; 16]; MAX_BLOCKS];
        blocks[0] = x1; blocks[1] = x2;
        assert_eq!(polyval(&h, &blocks, 2), expected, "POLYVAL Appendix A");
    }

    #[test]
    fn test_rfc8452_c1_empty() {
        let key: AesKey = [0x01,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
        let nonce: Nonce = [0x03,0,0,0,0,0,0,0,0,0,0,0];
        let expected_tag: Block = [0xdc,0x20,0xe2,0xd8,0x3f,0x25,0x70,0x5b,
                                   0xb4,0x9e,0x43,0x9e,0xca,0x56,0xde,0x25];
        let (_ct, n, tag) = aes_gcm_siv_seal(&key, &nonce, &[], 0, &[], 0);
        assert_eq!(n, 0);
        assert_eq!(tag, expected_tag, "C.1 tag");
        assert!(aes_gcm_siv_open(&key, &nonce, &[], 0, &[], 0, &tag).is_some());
    }

    #[test]
    fn test_rfc8452_c2_8bytes() {
        let key: AesKey = [0x01,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
        let nonce: Nonce = [0x03,0,0,0,0,0,0,0,0,0,0,0];
        let pt: [u8; 8] = [0x01,0,0,0,0,0,0,0];
        let exp_ct: [u8; 8] = [0xb5,0xd8,0x39,0x33,0x0a,0xc7,0xb7,0x86];
        let exp_tag: Block = [0x57,0x87,0x82,0xff,0xf6,0x01,0x3b,0x81,
                              0x5b,0x28,0x7c,0x22,0x49,0x3a,0x36,0x4c];
        let (ct_blocks, _, tag) = aes_gcm_siv_seal(&key, &nonce, &[], 0, &pt, 8);
        assert_eq!(tag, exp_tag, "C.2 tag");
        let mut ct: [u8; 8] = [0; 8];
        blocks_to_bytes(&ct_blocks, 8, &mut ct);
        assert_eq!(ct, exp_ct, "C.2 ciphertext");
        let r = aes_gcm_siv_open(&key, &nonce, &[], 0, &exp_ct, 8, &tag);
        assert!(r.is_some());
        if let Some((pb, _)) = r {
            let mut rec: [u8; 8] = [0; 8];
            blocks_to_bytes(&pb, 8, &mut rec);
            assert_eq!(rec, pt);
        }
    }

    #[test]
    fn test_rfc8452_c3_12bytes() {
        let key: AesKey = [0x01,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
        let nonce: Nonce = [0x03,0,0,0,0,0,0,0,0,0,0,0];
        let pt: [u8; 12] = [0x01,0,0,0,0,0,0,0,0,0,0,0];
        let exp_ct: [u8; 12] = [0x73,0x23,0xea,0x61,0xd0,0x59,0x32,0x26,
                                 0x00,0x47,0xd9,0x42];
        let exp_tag: Block = [0xa4,0x97,0x8d,0xb3,0x57,0x39,0x1a,0x0b,
                              0xc4,0xfd,0xec,0x8b,0x0d,0x10,0x66,0x39];
        let (ct_blocks, _, tag) = aes_gcm_siv_seal(&key, &nonce, &[], 0, &pt, 12);
        assert_eq!(tag, exp_tag, "C.3 tag");
        let mut ct: [u8; 12] = [0; 12];
        blocks_to_bytes(&ct_blocks, 12, &mut ct);
        assert_eq!(ct, exp_ct, "C.3 ciphertext");
        assert!(aes_gcm_siv_open(&key, &nonce, &[], 0, &exp_ct, 12, &tag).is_some());
    }

    #[test]
    fn test_seal_open_roundtrip() {
        let key: AesKey = [0x42; 16];
        let nonce: Nonce = [1,2,3,4,5,6,7,8,9,10,11,12];
        let pt: [u8; 16] = [0xde,0xad,0xbe,0xef,0xca,0xfe,0xba,0xbe,
                             0x01,0x23,0x45,0x67,0x89,0xab,0xcd,0xef];
        let aad: [u8; 4] = [1,2,3,4];
        let (ct_blocks, _, tag) = aes_gcm_siv_seal(&key, &nonce, &aad, 4, &pt, 16);
        let mut ct: [u8; 16] = [0; 16];
        blocks_to_bytes(&ct_blocks, 16, &mut ct);
        let r = aes_gcm_siv_open(&key, &nonce, &aad, 4, &ct, 16, &tag);
        assert!(r.is_some());
        if let Some((pb, _)) = r {
            let mut rec: [u8; 16] = [0; 16];
            blocks_to_bytes(&pb, 16, &mut rec);
            assert_eq!(rec, pt);
        }
    }

    #[test]
    fn test_open_wrong_tag_fails() {
        let key: AesKey = [0x42; 16];
        let nonce: Nonce = [1,2,3,4,5,6,7,8,9,10,11,12];
        let pt: [u8; 8] = [1,2,3,4,5,6,7,8];
        let (ct_blocks, _, tag) = aes_gcm_siv_seal(&key, &nonce, &[], 0, &pt, 8);
        let mut ct: [u8; 8] = [0; 8];
        blocks_to_bytes(&ct_blocks, 8, &mut ct);
        let mut bad_tag = tag;
        bad_tag[0] ^= 0xff;
        assert!(aes_gcm_siv_open(&key, &nonce, &[], 0, &ct, 8, &bad_tag).is_none());
    }

    #[test]
    fn test_le_u64_roundtrip() {
        let mut buf: [u8; 16] = [0; 16];
        put_le_u64(&mut buf, 0, 0x0807060504030201);
        assert_eq!(buf[0], 0x01);
        assert_eq!(buf[7], 0x08);
        assert_eq!(le_u64(&buf, 0), 0x0807060504030201);
    }
}
