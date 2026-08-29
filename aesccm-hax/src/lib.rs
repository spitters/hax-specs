// Copyright (c) 2026 CatCrypt Contributors. MIT license.
//! AES-CCM (NIST SP 800-38C): Hax-extractable implementation.
//!
//! CCM (Counter with CBC-MAC) combines AES-CTR encryption with AES-CBC-MAC
//! authentication into an authenticated encryption with associated data (AEAD)
//! scheme.
//!
//! Construction:
//!   1. Format B0 block from flags, nonce, and message length
//!   2. Compute CBC-MAC T over B0 || formatted AAD || padded payload
//!   3. Encrypt payload with AES-CTR (counter blocks A1, A2, ...)
//!   4. Encrypt tag T with AES-CTR (counter block A0) to produce U
//!
//! All loops are bounded `for i in 0..N`, all arithmetic is wrapping,
//! all buffers are fixed-size arrays.
//!
//! The `proofs/lean/extraction` directory holds the hax Lean extraction of
//! this module.

#![no_std]
// The index-loop, fixed-array style is what hax extracts; these lints ask for
// iterator and slice forms that it does not.
#![allow(
    clippy::needless_range_loop,
    clippy::manual_memcpy,
    clippy::manual_div_ceil,
    clippy::too_many_arguments
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

/// Maximum message length for bounded iteration: 256 bytes.
pub const MAX_MSG: usize = 256;

/// Maximum AAD length for bounded iteration: 256 bytes.
pub const MAX_AAD: usize = 256;

/// Maximum number of CBC-MAC input blocks: B0(1) + AAD_hdr(2+256)/16 + MSG(256)/16 = 35.
/// Use 40 for safety margin.
const MAX_CBC_BLOCKS: usize = 40;

/// Maximum number of CTR blocks: ceil(256/16) + 1 = 17 for A0..A16.
const MAX_CTR_BLOCKS: usize = 18;

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
///
/// Produces the 44-word expanded key of FIPS 197, Section 5.2, laid out as 11 round keys.
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
///
/// This is the only block-cipher call CCM makes; the CBC-MAC and CTR layers are built on it.
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
// CCM B0 block formatting (SP 800-38C, Section A.2)
// =========================================================================

/// Format the B0 block for CCM.
///
/// B0 = Flags || Nonce || Q
///
/// Flags = 64*Adata || 8*((t-2)/2) || (q-1)
/// where:
///   - Adata = 1 if there is associated data, 0 otherwise
///   - t = tag length in bytes (must be even, 4..16)
///   - q = 15 - nonce_len = number of bytes for message length encoding
///   - Q = message length encoded in q bytes (big-endian)
///
/// `nonce_len` must be 7..13.
pub fn format_b0(
    nonce: &[u8; 13],
    nonce_len: usize,
    msg_len: usize,
    tag_len: usize,
    has_aad: usize,
) -> Block {
    let mut b0: Block = [0u8; 16];

    // q = 15 - nonce_len (number of octets for encoding message length)
    let q = 15 - nonce_len;

    // Flags byte
    let adata_flag: u8 = if has_aad != 0 { 0x40 } else { 0x00 };
    let t_field: u8 = (((tag_len - 2) / 2) as u8) << 3;
    let q_field: u8 = (q - 1) as u8;
    b0[0] = adata_flag | t_field | q_field;

    // Nonce: bytes 1..(1+nonce_len)
    for i in 0..13 {
        if i < nonce_len {
            b0[1 + i] = nonce[i];
        }
    }

    // Q: message length in big-endian, occupying bytes (1+nonce_len)..16
    // i.e., last q bytes of B0
    let mut len_val = msg_len;
    for i in 0..q {
        b0[15 - i] = (len_val & 0xff) as u8;
        len_val >>= 8;
    }

    b0
}

/// Format a counter block Ai for CCM-CTR mode.
///
/// Ai = Flags || Nonce || Counter
///
/// Flags = (q-1)  (lower 3 bits only)
/// Counter is q bytes, big-endian.
pub fn format_ctr_block(
    nonce: &[u8; 13],
    nonce_len: usize,
    counter: usize,
) -> Block {
    let mut ai: Block = [0u8; 16];
    let q = 15 - nonce_len;

    // Flags: just (q-1) in the lower 3 bits
    ai[0] = (q - 1) as u8;

    // Nonce
    for i in 0..13 {
        if i < nonce_len {
            ai[1 + i] = nonce[i];
        }
    }

    // Counter in big-endian, last q bytes
    let mut ctr_val = counter;
    for i in 0..q {
        ai[15 - i] = (ctr_val & 0xff) as u8;
        ctr_val >>= 8;
    }

    ai
}

/// Increment the counter portion of a CTR block.
///
/// The counter occupies the last `q` bytes (big-endian).
/// q = 15 - nonce_len.
pub fn ctr_increment(block: &mut Block, nonce_len: usize) {
    let q = 15 - nonce_len;
    // Increment big-endian counter in last q bytes
    let mut carry: u16 = 1;
    for i in 0..q {
        let pos = 15 - i;
        let sum = (block[pos] as u16).wrapping_add(carry);
        block[pos] = sum as u8;
        carry = sum >> 8;
    }
}

// =========================================================================
// CCM CBC-MAC computation (SP 800-38C, Section 6.1 / A.2)
// =========================================================================

/// Format AAD length header.
///
/// If 0 < a < 2^16 - 2^8: encode as 2 bytes.
/// (We only support a <= MAX_AAD = 256 which fits in 2 bytes.)
///
/// Returns the header bytes and number of header bytes used.
fn format_aad_header(aad_len: usize) -> ([u8; 6], usize) {
    let mut hdr = [0u8; 6];
    // For 0 < a < 0xFF00, use 2-byte encoding
    hdr[0] = ((aad_len >> 8) & 0xff) as u8;
    hdr[1] = (aad_len & 0xff) as u8;
    (hdr, 2)
}

/// Compute CBC-MAC tag T for CCM.
///
/// Input to CBC-MAC is: B0 || [AAD header || AAD || pad] || [payload || pad]
///
/// Each segment is padded to a multiple of 16 bytes.
///
/// Returns the full 16-byte CBC-MAC tag T (before truncation/encryption).
pub fn ccm_cbc_mac(
    key: &AesKey,
    nonce: &[u8; 13],
    nonce_len: usize,
    plaintext: &[u8; MAX_MSG],
    pt_len: usize,
    aad: &[u8; MAX_AAD],
    aad_len: usize,
    tag_len: usize,
) -> Block {
    // Assemble all CBC-MAC input blocks into a flat buffer
    let mut cbc_input: [[u8; 16]; MAX_CBC_BLOCKS] = [[0u8; 16]; MAX_CBC_BLOCKS];
    // --- B0 block ---
    let b0 = format_b0(nonce, nonce_len, pt_len, tag_len, if aad_len > 0 { 1 } else { 0 });
    cbc_input[0] = b0;
    let mut block_count: usize = 1;
    let mut buf: [u8; 16] = [0u8; 16];
    let mut buf_pos: usize = 0;

    // --- AAD encoding (if any) ---
    if aad_len > 0 {
        // Format AAD header (2-byte encoding for aad_len < 0xFF00)
        let (aad_hdr, hdr_len) = format_aad_header(aad_len);

        // Fill buf with header + AAD data, emitting blocks as they fill
        // Write header bytes
        for i in 0..6 {
            if i < hdr_len {
                buf[buf_pos] = aad_hdr[i];
                buf_pos += 1;
                if buf_pos == 16 {
                    cbc_input[block_count] = buf;
                    block_count += 1;
                    buf = [0u8; 16];
                    buf_pos = 0;
                }
            }
        }

        // Write AAD data
        for i in 0..MAX_AAD {
            if i < aad_len {
                buf[buf_pos] = aad[i];
                buf_pos += 1;
                if buf_pos == 16 {
                    cbc_input[block_count] = buf;
                    block_count += 1;
                    buf = [0u8; 16];
                    buf_pos = 0;
                }
            }
        }

        // Pad remaining AAD block (if partial)
        if buf_pos > 0 {
            // buf is already zero-padded from initialization
            cbc_input[block_count] = buf;
            block_count += 1;
        }
    }

    // --- Payload blocks ---
    if pt_len > 0 {
        buf = [0u8; 16];
        buf_pos = 0;

        for i in 0..MAX_MSG {
            if i < pt_len {
                buf[buf_pos] = plaintext[i];
                buf_pos += 1;
                if buf_pos == 16 {
                    cbc_input[block_count] = buf;
                    block_count += 1;
                    buf = [0u8; 16];
                    buf_pos = 0;
                }
            }
        }

        // Pad remaining payload block (if partial)
        if buf_pos > 0 {
            cbc_input[block_count] = buf;
            block_count += 1;
        }
    }

    // --- CBC-MAC computation ---
    let mut x: Block = ZERO_BLOCK;
    for i in 0..MAX_CBC_BLOCKS {
        if i >= block_count {
            break;
        }
        let y = xor_block(&x, &cbc_input[i]);
        x = aes128_encrypt(key, &y);
    }

    x
}

// =========================================================================
// CCM encryption (SP 800-38C, Section 6.1)
// =========================================================================

/// CCM-AES-128 authenticated encryption.
///
/// # Arguments
/// * `key` - 16-byte AES-128 key
/// * `nonce` - Nonce stored in a 13-byte array (only first `nonce_len` bytes used)
/// * `nonce_len` - Actual nonce length (7..13)
/// * `plaintext` - Plaintext in a MAX_MSG-byte array
/// * `pt_len` - Actual plaintext length in bytes
/// * `aad` - Associated data in a MAX_AAD-byte array
/// * `aad_len` - Actual AAD length in bytes
/// * `tag_len` - Tag length in bytes (4, 6, 8, 10, 12, 14, or 16)
///
/// # Returns
/// `(ciphertext, tag)` where:
/// * `ciphertext` is a MAX_MSG-byte array (first `pt_len` bytes valid)
/// * `tag` is a 16-byte array (first `tag_len` bytes valid)
pub fn ccm_encrypt(
    key: &AesKey,
    nonce: &[u8; 13],
    nonce_len: usize,
    plaintext: &[u8; MAX_MSG],
    pt_len: usize,
    aad: &[u8; MAX_AAD],
    aad_len: usize,
    tag_len: usize,
) -> ([u8; MAX_MSG], [u8; 16]) {
    // Step 1: Compute CBC-MAC tag T
    let t = ccm_cbc_mac(key, nonce, nonce_len, plaintext, pt_len, aad, aad_len, tag_len);

    // Step 2: CTR encryption
    // A0 is used to encrypt the tag
    let a0 = format_ctr_block(nonce, nonce_len, 0);
    let s0 = aes128_encrypt(key, &a0);

    // Encrypt tag: U = T XOR first tag_len bytes of S0
    let mut tag: Block = [0u8; 16];
    for i in 0..16 {
        if i < tag_len {
            tag[i] = t[i] ^ s0[i];
        }
    }

    // Encrypt plaintext: C_i = P_i XOR S_i where S_i = AES_K(A_i)
    let mut ciphertext: [u8; MAX_MSG] = [0u8; MAX_MSG];
    let num_pt_blocks = if pt_len == 0 { 0 } else { (pt_len + 15) / 16 };

    for blk in 0..MAX_CTR_BLOCKS {
        if blk >= num_pt_blocks {
            break;
        }
        let ai = format_ctr_block(nonce, nonce_len, blk + 1);
        let si = aes128_encrypt(key, &ai);

        for j in 0..16 {
            let idx = blk * 16 + j;
            if idx < pt_len {
                ciphertext[idx] = plaintext[idx] ^ si[j];
            }
        }
    }

    (ciphertext, tag)
}

/// CCM-AES-128 authenticated decryption.
///
/// # Arguments
/// * `key` - 16-byte AES-128 key
/// * `nonce` - Nonce stored in a 13-byte array (only first `nonce_len` bytes used)
/// * `nonce_len` - Actual nonce length (7..13)
/// * `ciphertext` - Ciphertext in a MAX_MSG-byte array
/// * `ct_len` - Actual ciphertext length in bytes
/// * `aad` - Associated data in a MAX_AAD-byte array
/// * `aad_len` - Actual AAD length in bytes
/// * `received_tag` - Received authentication tag (16-byte array, first `tag_len` bytes used)
/// * `tag_len` - Tag length in bytes (4, 6, 8, 10, 12, 14, or 16)
///
/// # Returns
/// `Some(plaintext)` if authentication succeeds, `None` if tag verification fails.
/// The plaintext is a MAX_MSG-byte array (first `ct_len` bytes valid).
pub fn ccm_decrypt(
    key: &AesKey,
    nonce: &[u8; 13],
    nonce_len: usize,
    ciphertext: &[u8; MAX_MSG],
    ct_len: usize,
    aad: &[u8; MAX_AAD],
    aad_len: usize,
    received_tag: &[u8; 16],
    tag_len: usize,
) -> Option<[u8; MAX_MSG]> {
    // Step 1: Decrypt ciphertext using CTR mode to recover plaintext
    let mut plaintext: [u8; MAX_MSG] = [0u8; MAX_MSG];
    let num_ct_blocks = if ct_len == 0 { 0 } else { (ct_len + 15) / 16 };

    for blk in 0..MAX_CTR_BLOCKS {
        if blk >= num_ct_blocks {
            break;
        }
        let ai = format_ctr_block(nonce, nonce_len, blk + 1);
        let si = aes128_encrypt(key, &ai);

        for j in 0..16 {
            let idx = blk * 16 + j;
            if idx < ct_len {
                plaintext[idx] = ciphertext[idx] ^ si[j];
            }
        }
    }

    // Step 2: Recompute CBC-MAC over the recovered plaintext
    let t = ccm_cbc_mac(key, nonce, nonce_len, &plaintext, ct_len, aad, aad_len, tag_len);

    // Step 3: Encrypt the recomputed tag with A0
    let a0 = format_ctr_block(nonce, nonce_len, 0);
    let s0 = aes128_encrypt(key, &a0);

    let mut expected_tag: Block = [0u8; 16];
    for i in 0..16 {
        if i < tag_len {
            expected_tag[i] = t[i] ^ s0[i];
        }
    }

    // Step 4: Compare tags (constant-time-ish for hax compatibility)
    let mut diff: u8 = 0;
    for i in 0..16 {
        if i < tag_len {
            diff |= received_tag[i] ^ expected_tag[i];
        }
    }

    if diff == 0 {
        Some(plaintext)
    } else {
        None
    }
}

// =========================================================================
// Kani harnesses
// =========================================================================

#[cfg(kani)]
mod kani_harnesses {
    use super::*;

    /// CTR increment wraps correctly: incrementing 0 gives 1.
    #[kani::proof]
    fn ctr_increment_zero_gives_one() {
        let mut block: Block = [0u8; 16];
        // nonce_len=13 means q=2, counter in last 2 bytes
        block[0] = 0x01; // flags = q-1 = 1
        ctr_increment(&mut block, 13);
        assert_eq!(block[15], 1);
        assert_eq!(block[14], 0);
    }

    /// CTR increment wraps on overflow of last byte.
    #[kani::proof]
    fn ctr_increment_carry() {
        let mut block: Block = [0u8; 16];
        block[0] = 0x01;
        block[15] = 0xff;
        ctr_increment(&mut block, 13);
        assert_eq!(block[15], 0x00);
        assert_eq!(block[14], 0x01);
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

    // B0 formatting test
    #[test]
    fn test_format_b0() {
        // RFC 3610 Packet Vector #1:
        // nonce = 00 00 00 03 02 01 00 A0 A1 A2 A3 A4 A5 (13 bytes)
        // msg_len = 23, tag_len = 8, has_aad = true
        // Flags = 0x40 | ((8-2)/2 << 3) | (2-1) = 0x40 | 0x18 | 0x01 = 0x59
        let nonce: [u8; 13] = [0x00, 0x00, 0x00, 0x03, 0x02, 0x01, 0x00,
                                0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5];
        let b0 = format_b0(&nonce, 13, 23, 8, 1);
        assert_eq!(b0[0], 0x59, "B0 flags byte");
        // Nonce in bytes 1..14
        assert_eq!(b0[1], 0x00);
        assert_eq!(b0[7], 0x00);
        assert_eq!(b0[8], 0xA0);
        assert_eq!(b0[13], 0xA5);
        // Q = 23 in last 2 bytes (q=2)
        assert_eq!(b0[14], 0x00);
        assert_eq!(b0[15], 0x17); // 23 = 0x17
    }

    // CTR block formatting test
    #[test]
    fn test_format_ctr_block() {
        let nonce: [u8; 13] = [0x00, 0x00, 0x00, 0x03, 0x02, 0x01, 0x00,
                                0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5];
        // A0: counter = 0
        let a0 = format_ctr_block(&nonce, 13, 0);
        assert_eq!(a0[0], 0x01, "A0 flags = q-1 = 1");
        assert_eq!(a0[14], 0x00);
        assert_eq!(a0[15], 0x00);

        // A1: counter = 1
        let a1 = format_ctr_block(&nonce, 13, 1);
        assert_eq!(a1[0], 0x01);
        assert_eq!(a1[14], 0x00);
        assert_eq!(a1[15], 0x01);
    }

    // CTR increment test
    #[test]
    fn test_ctr_increment() {
        let nonce: [u8; 13] = [0x00; 13];
        let mut a = format_ctr_block(&nonce, 13, 0);
        ctr_increment(&mut a, 13);
        assert_eq!(a[15], 0x01, "increment 0 -> 1");
        assert_eq!(a[14], 0x00);

        // Test carry
        let mut a2 = format_ctr_block(&nonce, 13, 0xff);
        ctr_increment(&mut a2, 13);
        assert_eq!(a2[15], 0x00, "increment 0xff -> carry");
        assert_eq!(a2[14], 0x01, "carry into byte 14");
    }

    // RFC 3610 Packet Vector #1 — full encrypt/decrypt round-trip
    #[test]
    fn test_ccm_rfc3610_vector1() {
        let key: AesKey = [
            0xC0, 0xC1, 0xC2, 0xC3, 0xC4, 0xC5, 0xC6, 0xC7,
            0xC8, 0xC9, 0xCA, 0xCB, 0xCC, 0xCD, 0xCE, 0xCF,
        ];
        let nonce: [u8; 13] = [
            0x00, 0x00, 0x00, 0x03, 0x02, 0x01, 0x00,
            0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5,
        ];
        let pt_data: [u8; 23] = [
            0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F,
            0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
            0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E,
        ];
        let aad_data: [u8; 8] = [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07];

        let mut plaintext = [0u8; MAX_MSG];
        for i in 0..23 { plaintext[i] = pt_data[i]; }
        let mut aad = [0u8; MAX_AAD];
        for i in 0..8 { aad[i] = aad_data[i]; }

        let (ct, tag) = ccm_encrypt(&key, &nonce, 13, &plaintext, 23, &aad, 8, 8);

        // Expected ciphertext (23 bytes) + tag (8 bytes) from RFC 3610
        let expected_ct: [u8; 23] = [
            0x58, 0x8C, 0x97, 0x9A, 0x61, 0xC6, 0x63, 0xD2,
            0xF0, 0x66, 0xD0, 0xC2, 0xC0, 0xF9, 0x89, 0x80,
            0x6D, 0x5F, 0x6B, 0x61, 0xDA, 0xC3, 0x84,
        ];
        let expected_tag: [u8; 8] = [
            0x17, 0xE8, 0xD1, 0x2C, 0xFD, 0xF9, 0x26, 0xE0,
        ];

        for i in 0..23 {
            assert_eq!(ct[i], expected_ct[i], "ciphertext byte {} mismatch", i);
        }
        for i in 0..8 {
            assert_eq!(tag[i], expected_tag[i], "tag byte {} mismatch", i);
        }

        // Round-trip: decrypt should recover plaintext
        let mut recv_tag = [0u8; 16];
        for i in 0..8 { recv_tag[i] = tag[i]; }
        let result = ccm_decrypt(&key, &nonce, 13, &ct, 23, &aad, 8, &recv_tag, 8);
        assert!(result.is_some(), "decryption should succeed");
        let recovered = result.unwrap();
        for i in 0..23 {
            assert_eq!(recovered[i], pt_data[i], "recovered plaintext byte {} mismatch", i);
        }
    }

    // Test that modified ciphertext fails authentication
    #[test]
    fn test_ccm_tamper_detection() {
        let key: AesKey = [
            0xC0, 0xC1, 0xC2, 0xC3, 0xC4, 0xC5, 0xC6, 0xC7,
            0xC8, 0xC9, 0xCA, 0xCB, 0xCC, 0xCD, 0xCE, 0xCF,
        ];
        let nonce: [u8; 13] = [
            0x00, 0x00, 0x00, 0x03, 0x02, 0x01, 0x00,
            0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5,
        ];
        let mut plaintext = [0u8; MAX_MSG];
        plaintext[0] = 0x08; plaintext[1] = 0x09;
        let mut aad = [0u8; MAX_AAD];
        aad[0] = 0x00; aad[1] = 0x01;

        let (mut ct, tag) = ccm_encrypt(&key, &nonce, 13, &plaintext, 2, &aad, 2, 8);

        // Tamper with ciphertext
        ct[0] ^= 0x01;

        let mut recv_tag = [0u8; 16];
        for i in 0..8 { recv_tag[i] = tag[i]; }
        let result = ccm_decrypt(&key, &nonce, 13, &ct, 2, &aad, 2, &recv_tag, 8);
        assert!(result.is_none(), "tampered ciphertext should fail authentication");
    }

    // Test empty plaintext (AAD-only authentication)
    #[test]
    fn test_ccm_empty_plaintext() {
        let key: AesKey = [0x01u8; 16];
        let nonce: [u8; 13] = [0x02u8; 13];
        let plaintext = [0u8; MAX_MSG];
        let mut aad = [0u8; MAX_AAD];
        for i in 0..8 { aad[i] = i as u8; }

        let (ct, tag) = ccm_encrypt(&key, &nonce, 13, &plaintext, 0, &aad, 8, 8);

        // All ciphertext bytes should be zero (no plaintext)
        for i in 0..MAX_MSG {
            assert_eq!(ct[i], 0, "no ciphertext for empty plaintext");
        }

        // Round-trip
        let mut recv_tag = [0u8; 16];
        for i in 0..8 { recv_tag[i] = tag[i]; }
        let result = ccm_decrypt(&key, &nonce, 13, &ct, 0, &aad, 8, &recv_tag, 8);
        assert!(result.is_some(), "empty plaintext decrypt should succeed");
    }

    // Test with no AAD
    #[test]
    fn test_ccm_no_aad() {
        let key: AesKey = [0x03u8; 16];
        let nonce: [u8; 13] = [0x04u8; 13];
        let mut plaintext = [0u8; MAX_MSG];
        for i in 0..16 { plaintext[i] = (i as u8).wrapping_mul(3); }
        let aad = [0u8; MAX_AAD];

        let (ct, tag) = ccm_encrypt(&key, &nonce, 13, &plaintext, 16, &aad, 0, 8);

        let mut recv_tag = [0u8; 16];
        for i in 0..8 { recv_tag[i] = tag[i]; }
        let result = ccm_decrypt(&key, &nonce, 13, &ct, 16, &aad, 0, &recv_tag, 8);
        assert!(result.is_some(), "no-AAD decrypt should succeed");
        let recovered = result.unwrap();
        for i in 0..16 {
            assert_eq!(recovered[i], plaintext[i], "recovered byte {}", i);
        }
    }

    // S-box spot checks
    #[test]
    fn test_sbox_known_values() {
        assert_eq!(AES_SBOX[0x00], 0x63);
        assert_eq!(AES_SBOX[0x01], 0x7c);
        assert_eq!(AES_SBOX[0x53], 0xed);
        assert_eq!(AES_SBOX[0xff], 0x16);
    }

    // GF(2^8) tests
    #[test]
    fn test_gf_mul2_known() {
        assert_eq!(gf_mul2(0x57), 0xae);
        assert_eq!(gf_mul2(0x00), 0x00);
        assert_eq!(gf_mul2(0x01), 0x02);
        assert_eq!(gf_mul2(0x80), 0x1b);
    }
}
