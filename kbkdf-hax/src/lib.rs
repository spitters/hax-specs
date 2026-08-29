// Copyright (c) 2026 CatCrypt Contributors. MIT license.
//! KBKDF in Counter Mode (NIST SP 800-108 Rev. 1, Section 4.1) with
//! HMAC-SHA-256 as the PRF, in a hax-extractable Rust subset.
//!
//! The KDF in Counter Mode is
//!
//! ```text
//!   n = ceil(L / h)  where h = 256 (HMAC-SHA-256 output bits)
//!   For i = 1..n:
//!     K(i) = PRF(K_IN, [i]_r || FixedInputData)
//!   K_OUT = K(1) || K(2) || ... || K(n), truncated to L/8 bytes
//! ```
//!
//! with the counter `[i]_r` placed before the fixed input data and encoded
//! as a big-endian 32-bit integer (r = 32). `kbkdf_counter_hmac256_fixed`
//! takes the fixed input data as an opaque byte string, the form the NIST
//! CAVP KDFCTR vectors use. `kbkdf_counter_hmac256` assembles the fixed
//! input data in the layout SP 800-108 Rev. 1, Section 4, recommends:
//!
//! ```text
//!   FixedInputData = Label || 0x00 || Context || [L]_4
//! ```
//!
//! where Label identifies the purpose of the derived key, 0x00 separates
//! it from the application-specific Context, and `[L]_4` is the big-endian
//! 32-bit encoding of the output length L in bits.
//!
//! All loops are bounded `for i in 0..N`, all arithmetic is wrapping,
//! all buffers are fixed-size arrays.
//!
//! The crate has no dependencies and is `no_std`. The SHA-256 (FIPS 180-4)
//! and HMAC (RFC 2104) primitives are included so that the extracted code is
//! self-contained. The Lean extraction produced by hax is committed under
//! `proofs/lean/extraction/`.

#![no_std]
// Index loops and nested bounds checks are kept in the form the hax frontend
// extracts; slice copies and short-circuit conditions are avoided on purpose.
#![allow(
    clippy::manual_memcpy,
    clippy::needless_range_loop,
    clippy::collapsible_if,
    clippy::new_without_default,
    clippy::manual_div_ceil
)]

// =========================================================================
// SHA-256 (FIPS 180-4)
// =========================================================================

/// SHA-256 initial hash values (FIPS 180-4, Section 5.3.3).
static SHA256_H0: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

/// SHA-256 round constants (FIPS 180-4, Section 4.2.2).
static SHA256_K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
    0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
    0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
    0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
    0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
    0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

/// SHA-256 block size in bytes.
pub const SHA256_BLOCK_SIZE: usize = 64;

/// SHA-256 digest size in bytes.
pub const SHA256_DIGEST_SIZE: usize = 32;

/// Maximum message length for SHA-256/HMAC: 256 bytes (for hax bounded iteration).
pub const MAX_MSG_LEN: usize = 256;

/// SHA-256 state.
#[derive(Clone, Copy)]
pub struct Sha256State {
    pub h: [u32; 8],
    pub buf: [u8; 64],
    pub buf_len: usize,
    pub total_len: u64,
}

impl Sha256State {
    /// Initialize SHA-256 state.
    pub fn new() -> Self {
        Sha256State {
            h: SHA256_H0,
            buf: [0u8; 64],
            buf_len: 0,
            total_len: 0,
        }
    }
}

#[inline]
fn ch(x: u32, y: u32, z: u32) -> u32 { (x & y) ^ ((!x) & z) }
#[inline]
fn maj(x: u32, y: u32, z: u32) -> u32 { (x & y) ^ (x & z) ^ (y & z) }
#[inline]
fn sigma0(x: u32) -> u32 { x.rotate_right(2) ^ x.rotate_right(13) ^ x.rotate_right(22) }
#[inline]
fn sigma1(x: u32) -> u32 { x.rotate_right(6) ^ x.rotate_right(11) ^ x.rotate_right(25) }
#[inline]
fn lsigma0(x: u32) -> u32 { x.rotate_right(7) ^ x.rotate_right(18) ^ (x >> 3) }
#[inline]
fn lsigma1(x: u32) -> u32 { x.rotate_right(17) ^ x.rotate_right(19) ^ (x >> 10) }

/// Process a single 64-byte block (SHA-256 compression function).
fn sha256_compress(state: &mut [u32; 8], block: &[u8; 64]) {
    // Parse block into 16 u32 words (big-endian)
    let mut w: [u32; 64] = [0u32; 64];
    for i in 0..16 {
        w[i] = (block[i*4] as u32) << 24
             | (block[i*4+1] as u32) << 16
             | (block[i*4+2] as u32) << 8
             | (block[i*4+3] as u32);
    }

    // Extend to 64 words
    for i in 16..64 {
        w[i] = lsigma1(w[i-2])
            .wrapping_add(w[i-7])
            .wrapping_add(lsigma0(w[i-15]))
            .wrapping_add(w[i-16]);
    }

    // Working variables
    let mut a = state[0];
    let mut b = state[1];
    let mut c = state[2];
    let mut d = state[3];
    let mut e = state[4];
    let mut f = state[5];
    let mut g = state[6];
    let mut h = state[7];

    // 64 rounds
    for i in 0..64 {
        let t1 = h.wrapping_add(sigma1(e))
                  .wrapping_add(ch(e, f, g))
                  .wrapping_add(SHA256_K[i])
                  .wrapping_add(w[i]);
        let t2 = sigma0(a).wrapping_add(maj(a, b, c));
        h = g; g = f; f = e;
        e = d.wrapping_add(t1);
        d = c; c = b; b = a;
        a = t1.wrapping_add(t2);
    }

    state[0] = state[0].wrapping_add(a);
    state[1] = state[1].wrapping_add(b);
    state[2] = state[2].wrapping_add(c);
    state[3] = state[3].wrapping_add(d);
    state[4] = state[4].wrapping_add(e);
    state[5] = state[5].wrapping_add(f);
    state[6] = state[6].wrapping_add(g);
    state[7] = state[7].wrapping_add(h);
}

/// Update SHA-256 state with data.
pub fn sha256_update(mut state: Sha256State, data: &[u8], data_len: usize) -> Sha256State {
    let mut processed: usize = 0;
    for _iter in 0..((MAX_MSG_LEN + SHA256_BLOCK_SIZE * 2) / SHA256_BLOCK_SIZE + 2) {
        if processed >= data_len { break; }

        // Fill buffer
        let remaining = data_len - processed;
        let space = SHA256_BLOCK_SIZE - state.buf_len;
        let to_copy = if remaining < space { remaining } else { space };

        for i in 0..to_copy {
            if processed + i < data_len {
                state.buf[state.buf_len + i] = data[processed + i];
            }
        }
        state.buf_len += to_copy;
        processed += to_copy;
        state.total_len = state.total_len.wrapping_add(to_copy as u64);

        if state.buf_len == SHA256_BLOCK_SIZE {
            let block = state.buf;
            sha256_compress(&mut state.h, &block);
            state.buf_len = 0;
            state.buf = [0u8; 64];
        }
    }
    state
}

/// Finalize SHA-256 and produce 32-byte digest.
pub fn sha256_finalize(mut state: Sha256State) -> [u8; 32] {
    let bit_len = state.total_len.wrapping_mul(8);

    // Append 0x80
    state.buf[state.buf_len] = 0x80;
    state.buf_len += 1;

    // If not enough space for length (8 bytes), process current block and start new one
    if state.buf_len > 56 {
        for i in state.buf_len..64 { state.buf[i] = 0; }
        let block = state.buf;
        sha256_compress(&mut state.h, &block);
        state.buf = [0u8; 64];
        state.buf_len = 0;
    }

    // Zero-pad up to byte 56
    for i in state.buf_len..56 { state.buf[i] = 0; }

    // Append bit length as big-endian u64
    state.buf[56] = (bit_len >> 56) as u8;
    state.buf[57] = (bit_len >> 48) as u8;
    state.buf[58] = (bit_len >> 40) as u8;
    state.buf[59] = (bit_len >> 32) as u8;
    state.buf[60] = (bit_len >> 24) as u8;
    state.buf[61] = (bit_len >> 16) as u8;
    state.buf[62] = (bit_len >> 8) as u8;
    state.buf[63] = bit_len as u8;

    let block = state.buf;
    sha256_compress(&mut state.h, &block);

    // Serialize hash as big-endian bytes
    let mut digest: [u8; 32] = [0u8; 32];
    for i in 0..8 {
        digest[i*4]     = (state.h[i] >> 24) as u8;
        digest[i*4 + 1] = (state.h[i] >> 16) as u8;
        digest[i*4 + 2] = (state.h[i] >> 8) as u8;
        digest[i*4 + 3] = state.h[i] as u8;
    }
    digest
}

/// SHA-256 one-shot: hash `data[0..data_len]`.
pub fn sha256(data: &[u8], data_len: usize) -> [u8; 32] {
    let state = Sha256State::new();
    let state = sha256_update(state, data, data_len);
    sha256_finalize(state)
}

// =========================================================================
// HMAC-SHA-256 (RFC 2104)
// =========================================================================

/// HMAC key: up to 64 bytes (SHA-256 block size). Keys longer than 64 bytes
/// are first hashed to 32 bytes.
pub type HmacKey = [u8; SHA256_BLOCK_SIZE];

/// HMAC tag: 32 bytes (SHA-256 output).
pub type HmacTag = [u8; SHA256_DIGEST_SIZE];

/// Prepare HMAC key: if key > block_size, hash it; then zero-pad to block_size.
pub fn hmac_prepare_key(key: &[u8], key_len: usize) -> HmacKey {
    let mut k_prime: HmacKey = [0u8; SHA256_BLOCK_SIZE];

    if key_len > SHA256_BLOCK_SIZE {
        // Hash the key
        let hashed = sha256(key, key_len);
        for i in 0..SHA256_DIGEST_SIZE {
            k_prime[i] = hashed[i];
        }
    } else {
        for i in 0..SHA256_BLOCK_SIZE {
            if i < key_len {
                k_prime[i] = key[i];
            }
        }
    }

    k_prime
}

/// HMAC-SHA-256 computation.
///
/// HMAC(K, M) = H((K' XOR opad) || H((K' XOR ipad) || M))
///
/// where ipad = 0x36 * 64, opad = 0x5c * 64.
pub fn hmac_sha256(key: &[u8], key_len: usize, msg: &[u8], msg_len: usize) -> HmacTag {
    let k_prime = hmac_prepare_key(key, key_len);

    // Inner hash: H((K' XOR ipad) || M)
    let mut ipad_key: [u8; SHA256_BLOCK_SIZE] = [0u8; SHA256_BLOCK_SIZE];
    for i in 0..SHA256_BLOCK_SIZE {
        ipad_key[i] = k_prime[i] ^ 0x36;
    }

    let inner_state = Sha256State::new();
    let inner_state = sha256_update(inner_state, &ipad_key, SHA256_BLOCK_SIZE);
    let inner_state = sha256_update(inner_state, msg, msg_len);
    let inner_hash = sha256_finalize(inner_state);

    // Outer hash: H((K' XOR opad) || inner_hash)
    let mut opad_key: [u8; SHA256_BLOCK_SIZE] = [0u8; SHA256_BLOCK_SIZE];
    for i in 0..SHA256_BLOCK_SIZE {
        opad_key[i] = k_prime[i] ^ 0x5c;
    }

    let outer_state = Sha256State::new();
    let outer_state = sha256_update(outer_state, &opad_key, SHA256_BLOCK_SIZE);
    let outer_state = sha256_update(outer_state, &inner_hash, SHA256_DIGEST_SIZE);
    sha256_finalize(outer_state)
}

// =========================================================================
// KBKDF Counter Mode (NIST SP 800-108 Rev. 1, Section 4.1)
// =========================================================================

/// Maximum derived key length in bytes (2 HMAC-SHA-256 blocks = 64 bytes = 512 bits).
pub const MAX_DK_LEN: usize = 64;

/// Maximum number of HMAC blocks (ceil(MAX_DK_LEN / SHA256_DIGEST_SIZE)).
pub const MAX_BLOCKS: usize = 2;

/// Maximum label length in bytes.
pub const MAX_LABEL_LEN: usize = 32;

/// Maximum context length in bytes.
pub const MAX_CONTEXT_LEN: usize = 64;

/// Counter length in bytes (r = 32 bits).
pub const COUNTER_LEN: usize = 4;

/// Maximum fixed input data length in bytes:
///   MAX_LABEL_LEN + 1 (separator) + MAX_CONTEXT_LEN + 4 (L encoding)
///   = 32 + 1 + 64 + 4 = 101
pub const MAX_FIXED_LEN: usize = MAX_LABEL_LEN + 1 + MAX_CONTEXT_LEN + 4;

/// Maximum PRF input buffer size: COUNTER_LEN + MAX_FIXED_LEN = 105.
pub const MAX_PRF_INPUT_LEN: usize = COUNTER_LEN + MAX_FIXED_LEN;

/// Key derivation key: 32 bytes (for HMAC-SHA-256).
pub type KbkdfKey = [u8; SHA256_DIGEST_SIZE];

/// Derived key output buffer: MAX_DK_LEN bytes.
pub type DerivedKey = [u8; MAX_DK_LEN];

/// KBKDF in Counter Mode with HMAC-SHA-256 as PRF over opaque fixed input
/// data (SP 800-108 Rev. 1, Section 4.1), counter before the fixed input
/// data, r = 32.
///
/// # Arguments
/// * `ki` - Key derivation key (32 bytes)
/// * `fixed` - Fixed input data (up to MAX_FIXED_LEN bytes)
/// * `fixed_len` - Actual length of the fixed input data
/// * `output_bits` - Desired output length L in bits (a multiple of 8,
///   at most MAX_DK_LEN * 8 = 512)
///
/// # Returns
/// Fixed-size array of MAX_DK_LEN bytes; only the first `output_bits / 8` bytes
/// are meaningful, the rest are zero.
///
/// # Algorithm
/// ```text
/// n = ceil(output_bits / 256)
/// For i = 1..n:
///   K(i) = HMAC-SHA-256(KI, [i]_4 || FixedInputData)
/// K_OUT = K(1) || K(2) || ... || K(n), truncated to output_bits/8 bytes
/// ```
pub fn kbkdf_counter_hmac256_fixed(
    ki: &KbkdfKey,
    fixed: &[u8],
    fixed_len: usize,
    output_bits: u32,
) -> DerivedKey {
    // Number of output bytes
    let output_bytes = (output_bits / 8) as usize;

    // Number of HMAC blocks needed: ceil(output_bits / 256)
    let n = if output_bits == 0 {
        0usize
    } else {
        ((output_bits as usize) + 255) / 256
    };

    let mut dk: DerivedKey = [0u8; MAX_DK_LEN];

    // PRF input buffer: [i]_4 || FixedInputData. The counter occupies
    // positions 0..4 and is filled per iteration; the rest is constant.
    let mut prf_input: [u8; MAX_PRF_INPUT_LEN] = [0u8; MAX_PRF_INPUT_LEN];
    for i in 0..MAX_FIXED_LEN {
        if i < fixed_len {
            prf_input[COUNTER_LEN + i] = fixed[i];
        }
    }
    let prf_len: usize = COUNTER_LEN + fixed_len;

    // Iterate over blocks
    for block_idx in 0..MAX_BLOCKS {
        if block_idx >= n {
            break;
        }

        // Counter i = block_idx + 1 (1-based), big-endian 32-bit
        let counter = (block_idx as u32).wrapping_add(1);
        prf_input[0] = (counter >> 24) as u8;
        prf_input[1] = (counter >> 16) as u8;
        prf_input[2] = (counter >> 8) as u8;
        prf_input[3] = counter as u8;

        // K(i) = HMAC-SHA-256(KI, prf_input[0..prf_len])
        let block_mac = hmac_sha256(ki, SHA256_DIGEST_SIZE, &prf_input, prf_len);

        // Copy into output buffer
        let offset = block_idx * SHA256_DIGEST_SIZE;
        for j in 0..SHA256_DIGEST_SIZE {
            if offset + j < output_bytes {
                dk[offset + j] = block_mac[j];
            }
        }
    }

    dk
}

/// KBKDF in Counter Mode with HMAC-SHA-256 as PRF and the fixed input data
/// `Label || 0x00 || Context || [L]_4` (SP 800-108 Rev. 1, Section 4).
///
/// # Arguments
/// * `ki` - Key derivation key (32 bytes)
/// * `label` - Label byte string (up to MAX_LABEL_LEN bytes)
/// * `label_len` - Actual length of label
/// * `context` - Context byte string (up to MAX_CONTEXT_LEN bytes)
/// * `context_len` - Actual length of context
/// * `output_bits` - Desired output length L in bits (a multiple of 8,
///   at most MAX_DK_LEN * 8 = 512)
///
/// # Returns
/// Fixed-size array of MAX_DK_LEN bytes; only the first `output_bits / 8` bytes
/// are meaningful, the rest are zero.
///
/// # Algorithm
/// ```text
/// n = ceil(output_bits / 256)
/// For i = 1..n:
///   K(i) = HMAC-SHA-256(KI, [i]_4 || Label || 0x00 || Context || [L]_4)
/// K_OUT = K(1) || K(2) || ... || K(n), truncated to output_bits/8 bytes
/// ```
pub fn kbkdf_counter_hmac256(
    ki: &KbkdfKey,
    label: &[u8],
    label_len: usize,
    context: &[u8],
    context_len: usize,
    output_bits: u32,
) -> DerivedKey {
    // Build fixed input data: label || 0x00 || context || [L]_4
    let mut fixed: [u8; MAX_FIXED_LEN] = [0u8; MAX_FIXED_LEN];
    let mut fixed_len: usize = 0;

    // Append label
    for i in 0..MAX_LABEL_LEN {
        if i < label_len {
            fixed[fixed_len + i] = label[i];
        }
    }
    fixed_len += label_len;

    // Append separator 0x00
    fixed[fixed_len] = 0x00;
    fixed_len += 1;

    // Append context
    for i in 0..MAX_CONTEXT_LEN {
        if i < context_len {
            fixed[fixed_len + i] = context[i];
        }
    }
    fixed_len += context_len;

    // Append [L]_4 = big-endian 32-bit encoding of output_bits
    fixed[fixed_len]     = (output_bits >> 24) as u8;
    fixed[fixed_len + 1] = (output_bits >> 16) as u8;
    fixed[fixed_len + 2] = (output_bits >> 8) as u8;
    fixed[fixed_len + 3] = output_bits as u8;
    fixed_len += 4;

    kbkdf_counter_hmac256_fixed(ki, &fixed, fixed_len, output_bits)
}

// =========================================================================
// Kani harnesses
// =========================================================================

#[cfg(kani)]
mod kani_harnesses {
    use super::*;

    #[kani::proof]
    fn ipad_opad_disjoint() {
        // ipad XOR opad = 0x36 XOR 0x5c = 0x6a (never zero)
        let x: u8 = 0x36 ^ 0x5c;
        assert_eq!(x, 0x6a);
        assert_ne!(x, 0);
    }

    #[kani::proof]
    fn sha256_initial_state_nonzero() {
        let s = Sha256State::new();
        assert_ne!(s.h[0], 0);
    }

    #[kani::proof]
    fn counter_encoding_one() {
        // Counter 1 encodes as [0x00, 0x00, 0x00, 0x01]
        let counter: u32 = 1;
        assert_eq!((counter >> 24) as u8, 0x00);
        assert_eq!((counter >> 16) as u8, 0x00);
        assert_eq!((counter >> 8) as u8, 0x00);
        assert_eq!(counter as u8, 0x01);
    }
}

// =========================================================================
// Unit tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // ----- SHA-256 tests -----

    #[test]
    fn test_sha256_empty() {
        let digest = sha256(&[], 0);
        let expected: [u8; 32] = [
            0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14,
            0x9a, 0xfb, 0xf4, 0xc8, 0x99, 0x6f, 0xb9, 0x24,
            0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c,
            0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55,
        ];
        assert_eq!(digest, expected, "SHA-256 of empty string");
    }

    #[test]
    fn test_sha256_abc() {
        let msg = b"abc";
        let digest = sha256(msg, 3);
        let expected: [u8; 32] = [
            0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea,
            0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
            0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c,
            0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad,
        ];
        assert_eq!(digest, expected, "SHA-256 of 'abc'");
    }

    // ----- HMAC-SHA-256 tests (RFC 4231) -----

    #[test]
    fn test_hmac_rfc4231_case1() {
        let key: [u8; 20] = [0x0b; 20];
        let msg = b"Hi There";
        let tag = hmac_sha256(&key, 20, msg, 8);
        let expected: [u8; 32] = [
            0xb0, 0x34, 0x4c, 0x61, 0xd8, 0xdb, 0x38, 0x53,
            0x5c, 0xa8, 0xaf, 0xce, 0xaf, 0x0b, 0xf1, 0x2b,
            0x88, 0x1d, 0xc2, 0x00, 0xc9, 0x83, 0x3d, 0xa7,
            0x26, 0xe9, 0x37, 0x6c, 0x2e, 0x32, 0xcf, 0xf7,
        ];
        assert_eq!(tag, expected, "HMAC RFC 4231 Test Case 1");
    }

    #[test]
    fn test_hmac_rfc4231_case2() {
        let key = b"Jefe";
        let msg = b"what do ya want for nothing?";
        let tag = hmac_sha256(key, 4, msg, 28);
        let expected: [u8; 32] = [
            0x5b, 0xdc, 0xc1, 0x46, 0xbf, 0x60, 0x75, 0x4e,
            0x6a, 0x04, 0x24, 0x26, 0x08, 0x95, 0x75, 0xc7,
            0x5a, 0x00, 0x3f, 0x08, 0x9d, 0x27, 0x39, 0x83,
            0x9d, 0xec, 0x58, 0xb9, 0x64, 0xec, 0x38, 0x43,
        ];
        assert_eq!(tag, expected, "HMAC RFC 4231 Test Case 2");
    }

    // ----- KBKDF Counter Mode tests -----

    #[test]
    fn test_kbkdf_single_block() {
        // KI = 0x00112233...ccddeeff00112233...ccddeeff (32 bytes)
        let ki: KbkdfKey = [
            0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
            0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff,
            0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
            0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff,
        ];
        let label = b"test";
        let context = b"context";

        // L = 256 bits (1 block)
        // PRF input: [0x00,0x00,0x00,0x01] || "test" || 0x00 || "context" || [0x00,0x00,0x01,0x00]
        let dk = kbkdf_counter_hmac256(&ki, label, 4, context, 7, 256);

        // Expected: HMAC-SHA-256(KI, 0x000000017465737400636f6e7465787400000100)
        let expected: [u8; 32] = [
            0x35, 0xd7, 0xdd, 0xab, 0x05, 0x44, 0xe7, 0x5e,
            0x19, 0xf9, 0xea, 0x7a, 0xca, 0xe0, 0x68, 0x39,
            0x02, 0xbd, 0x8c, 0x5e, 0xa9, 0x0c, 0xaf, 0xe8,
            0x8f, 0x71, 0x44, 0xc6, 0x20, 0xdf, 0x74, 0x03,
        ];
        for i in 0..32 {
            assert_eq!(dk[i], expected[i], "KBKDF single block mismatch at byte {}", i);
        }
    }

    #[test]
    fn test_kbkdf_two_blocks() {
        // Same KI
        let ki: KbkdfKey = [
            0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
            0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff,
            0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
            0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff,
        ];
        let label = b"test";
        let context = b"context";

        // L = 512 bits (2 blocks = 64 bytes)
        let dk = kbkdf_counter_hmac256(&ki, label, 4, context, 7, 512);

        // Block 1: HMAC-SHA-256(KI, [0x00000001] || "test" || 0x00 || "context" || [0x00000200])
        let expected_block1: [u8; 32] = [
            0x62, 0x05, 0x73, 0xa5, 0x89, 0x8e, 0xe1, 0xaa,
            0x7a, 0x85, 0xbc, 0x8d, 0xf4, 0x1d, 0x14, 0x15,
            0x7d, 0x50, 0x40, 0x26, 0xdf, 0xab, 0xac, 0x5b,
            0xba, 0x5a, 0xb1, 0x54, 0x97, 0xd2, 0xa4, 0x12,
        ];
        // Block 2: HMAC-SHA-256(KI, [0x00000002] || "test" || 0x00 || "context" || [0x00000200])
        let expected_block2: [u8; 32] = [
            0x99, 0xa5, 0xd0, 0xa3, 0x27, 0x4f, 0xbe, 0xb3,
            0x27, 0x15, 0x2c, 0xea, 0x16, 0x87, 0x36, 0xb1,
            0x11, 0xc2, 0xf7, 0x59, 0x49, 0x00, 0xbc, 0xff,
            0xd5, 0x6b, 0xd0, 0x5e, 0x4f, 0xeb, 0xa6, 0x56,
        ];

        for i in 0..32 {
            assert_eq!(dk[i], expected_block1[i],
                "KBKDF 2-block: block 1 mismatch at byte {}", i);
        }
        for i in 0..32 {
            assert_eq!(dk[32 + i], expected_block2[i],
                "KBKDF 2-block: block 2 mismatch at byte {}", i);
        }
    }

    #[test]
    fn test_kbkdf_zero_output() {
        // L = 0 should produce all zeros
        let ki: KbkdfKey = [0xab; 32];
        let dk = kbkdf_counter_hmac256(&ki, b"lbl", 3, b"ctx", 3, 0);
        for i in 0..MAX_DK_LEN {
            assert_eq!(dk[i], 0, "KBKDF zero output should be all zeros");
        }
    }

    #[test]
    fn test_kbkdf_different_keys_differ() {
        let ki1: KbkdfKey = [0x01; 32];
        let ki2: KbkdfKey = [0x02; 32];
        let label = b"same";
        let context = b"same";

        let dk1 = kbkdf_counter_hmac256(&ki1, label, 4, context, 4, 256);
        let dk2 = kbkdf_counter_hmac256(&ki2, label, 4, context, 4, 256);

        let mut differ = false;
        for i in 0..32 {
            if dk1[i] != dk2[i] {
                differ = true;
            }
        }
        assert!(differ, "Different keys should produce different derived keys");
    }

    #[test]
    fn test_kbkdf_different_labels_differ() {
        let ki: KbkdfKey = [0x42; 32];
        let context = b"ctx";

        let dk1 = kbkdf_counter_hmac256(&ki, b"label1", 6, context, 3, 256);
        let dk2 = kbkdf_counter_hmac256(&ki, b"label2", 6, context, 3, 256);

        let mut differ = false;
        for i in 0..32 {
            if dk1[i] != dk2[i] {
                differ = true;
            }
        }
        assert!(differ, "Different labels should produce different derived keys");
    }

    #[test]
    fn test_kbkdf_different_contexts_differ() {
        let ki: KbkdfKey = [0x42; 32];
        let label = b"lbl";

        let dk1 = kbkdf_counter_hmac256(&ki, label, 3, b"context1", 8, 256);
        let dk2 = kbkdf_counter_hmac256(&ki, label, 3, b"context2", 8, 256);

        let mut differ = false;
        for i in 0..32 {
            if dk1[i] != dk2[i] {
                differ = true;
            }
        }
        assert!(differ, "Different contexts should produce different derived keys");
    }

    #[test]
    fn test_kbkdf_deterministic() {
        let ki: KbkdfKey = [0x55; 32];
        let dk1 = kbkdf_counter_hmac256(&ki, b"det", 3, b"test", 4, 512);
        let dk2 = kbkdf_counter_hmac256(&ki, b"det", 3, b"test", 4, 512);
        assert_eq!(dk1, dk2, "KBKDF must be deterministic");
    }
}
