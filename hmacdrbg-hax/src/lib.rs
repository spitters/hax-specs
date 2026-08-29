// Copyright (c) 2026 CatCrypt Contributors. MIT license.
//! HMAC_DRBG with SHA-256 (NIST SP 800-90A Rev. 1, Section 10.1.2) in a
//! hax-extractable Rust subset.
//!
//! HMAC_DRBG is a deterministic random bit generator based on HMAC.
//! This implementation uses HMAC-SHA-256 as the underlying primitive.
//!
//! State: (V, Key) where V and Key are both 32 bytes.
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
    clippy::new_without_default
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

/// Maximum message length for SHA-256 bounded iteration: 512 bytes.
/// HMAC-DRBG builds messages up to V || 0x01 || seed_material, which
/// can be 32 + 1 + (entropy + nonce + perso). We set this generously.
pub const MAX_MSG_LEN: usize = 512;

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
// HMAC-DRBG (SP 800-90A Rev. 1, Section 10.1.2)
// =========================================================================

/// Maximum output size per generate call (bytes).
/// Must be a multiple of SHA256_DIGEST_SIZE for simplicity.
pub const MAX_OUTPUT: usize = 128;

/// Maximum seed material length: entropy(32) + nonce(16) + personalization(up to 64).
pub const MAX_SEED_MATERIAL: usize = 128;

/// Maximum number of HMAC blocks generated in a single generate call.
/// MAX_OUTPUT / SHA256_DIGEST_SIZE = 128 / 32 = 4.
const MAX_GEN_BLOCKS: usize = MAX_OUTPUT / SHA256_DIGEST_SIZE;

/// Maximum HMAC input for update: V(32) + 1 + seed_material(MAX_SEED_MATERIAL).
const MAX_HMAC_INPUT: usize = SHA256_DIGEST_SIZE + 1 + MAX_SEED_MATERIAL;

/// HMAC-DRBG internal state (SP 800-90A Rev. 1, Section 10.1.2).
///
/// For HMAC-SHA-256:
///   - Key: 32 bytes
///   - V: 32 bytes
#[derive(Clone, Copy)]
pub struct HmacDrbgState {
    pub key: [u8; SHA256_DIGEST_SIZE],
    pub v: [u8; SHA256_DIGEST_SIZE],
}

/// HMAC-DRBG Update function (SP 800-90A Rev. 1, Section 10.1.2.2).
///
/// Update(K, V, provided_data):
///   K = HMAC(K, V || 0x00 || provided_data)
///   V = HMAC(K, V)
///   if provided_data is not empty:
///     K = HMAC(K, V || 0x01 || provided_data)
///     V = HMAC(K, V)
pub fn hmac_drbg_update(state: &HmacDrbgState, provided_data: &[u8], provided_data_len: usize) -> HmacDrbgState {
    // Build message: V || 0x00 || provided_data
    let mut msg: [u8; MAX_HMAC_INPUT] = [0u8; MAX_HMAC_INPUT];
    for i in 0..SHA256_DIGEST_SIZE {
        msg[i] = state.v[i];
    }
    msg[SHA256_DIGEST_SIZE] = 0x00;
    for i in 0..MAX_SEED_MATERIAL {
        if i < provided_data_len {
            msg[SHA256_DIGEST_SIZE + 1 + i] = provided_data[i];
        }
    }
    let msg_len = SHA256_DIGEST_SIZE + 1 + provided_data_len;

    // K = HMAC(K, V || 0x00 || provided_data)
    let new_key = hmac_sha256(&state.key, SHA256_DIGEST_SIZE, &msg, msg_len);
    // V = HMAC(K, V)
    let new_v = hmac_sha256(&new_key, SHA256_DIGEST_SIZE, &state.v, SHA256_DIGEST_SIZE);

    if provided_data_len == 0 {
        return HmacDrbgState { key: new_key, v: new_v };
    }

    // provided_data is not empty: second round
    // Build message: V || 0x01 || provided_data
    let mut msg2: [u8; MAX_HMAC_INPUT] = [0u8; MAX_HMAC_INPUT];
    for i in 0..SHA256_DIGEST_SIZE {
        msg2[i] = new_v[i];
    }
    msg2[SHA256_DIGEST_SIZE] = 0x01;
    for i in 0..MAX_SEED_MATERIAL {
        if i < provided_data_len {
            msg2[SHA256_DIGEST_SIZE + 1 + i] = provided_data[i];
        }
    }
    let msg2_len = SHA256_DIGEST_SIZE + 1 + provided_data_len;

    // K = HMAC(K, V || 0x01 || provided_data)
    let new_key2 = hmac_sha256(&new_key, SHA256_DIGEST_SIZE, &msg2, msg2_len);
    // V = HMAC(K, V)
    let new_v2 = hmac_sha256(&new_key2, SHA256_DIGEST_SIZE, &new_v, SHA256_DIGEST_SIZE);

    HmacDrbgState { key: new_key2, v: new_v2 }
}

/// HMAC-DRBG Instantiate function (SP 800-90A Rev. 1, Section 10.1.2.3).
///
/// Instantiate(entropy, nonce, personalization):
///   K = 0x00 * 32
///   V = 0x01 * 32
///   seed_material = entropy || nonce || personalization
///   (K, V) = Update(seed_material, K, V)
pub fn hmac_drbg_instantiate(
    entropy: &[u8], entropy_len: usize,
    nonce: &[u8], nonce_len: usize,
    personalization: &[u8], personalization_len: usize,
) -> HmacDrbgState {
    let mut key = [0x00u8; SHA256_DIGEST_SIZE];
    let mut v = [0x01u8; SHA256_DIGEST_SIZE];
    for i in 0..SHA256_DIGEST_SIZE { key[i] = 0x00; }
    for i in 0..SHA256_DIGEST_SIZE { v[i] = 0x01; }

    // Build seed_material = entropy || nonce || personalization
    let mut seed_material: [u8; MAX_SEED_MATERIAL] = [0u8; MAX_SEED_MATERIAL];
    let mut offset: usize = 0;

    for i in 0..MAX_SEED_MATERIAL {
        if i < entropy_len {
            seed_material[offset + i] = entropy[i];
        }
    }
    offset += entropy_len;

    for i in 0..MAX_SEED_MATERIAL {
        if i < nonce_len {
            if offset + i < MAX_SEED_MATERIAL {
                seed_material[offset + i] = nonce[i];
            }
        }
    }
    offset += nonce_len;

    for i in 0..MAX_SEED_MATERIAL {
        if i < personalization_len {
            if offset + i < MAX_SEED_MATERIAL {
                seed_material[offset + i] = personalization[i];
            }
        }
    }
    offset += personalization_len;

    let seed_len = offset;

    let initial_state = HmacDrbgState { key, v };
    hmac_drbg_update(&initial_state, &seed_material, seed_len)
}

/// HMAC-DRBG Generate function (SP 800-90A Rev. 1, Section 10.1.2.5).
///
/// Generate(state, requested_bytes, additional_input):
///   if additional_input is not empty:
///     (K, V) = Update(additional_input)
///   temp = empty
///   while len(temp) < requested_bytes:
///     V = HMAC(K, V)
///     temp = temp || V
///   (K, V) = Update(additional_input)
///   return temp[0..requested_bytes]
///
/// `num_bytes` must be <= MAX_OUTPUT.
pub fn hmac_drbg_generate(
    state: &HmacDrbgState,
    num_bytes: usize,
    additional_input: &[u8],
    additional_input_len: usize,
) -> (HmacDrbgState, [u8; MAX_OUTPUT]) {
    // If additional_input is provided, update state first
    let working_state = if additional_input_len > 0 {
        hmac_drbg_update(state, additional_input, additional_input_len)
    } else {
        *state
    };

    let mut output: [u8; MAX_OUTPUT] = [0u8; MAX_OUTPUT];
    let mut current_v = working_state.v;
    let mut generated: usize = 0;

    // Generate blocks: bounded loop over max possible blocks
    for _block in 0..MAX_GEN_BLOCKS {
        if generated >= num_bytes {
            break;
        }
        // V = HMAC(K, V)
        current_v = hmac_sha256(&working_state.key, SHA256_DIGEST_SIZE, &current_v, SHA256_DIGEST_SIZE);

        // Copy V to output
        for i in 0..SHA256_DIGEST_SIZE {
            if generated + i < num_bytes && generated + i < MAX_OUTPUT {
                output[generated + i] = current_v[i];
            }
        }
        generated += SHA256_DIGEST_SIZE;
    }

    // Update state with additional_input (may be empty)
    let updated_state = HmacDrbgState { key: working_state.key, v: current_v };
    let final_state = hmac_drbg_update(&updated_state, additional_input, additional_input_len);

    (final_state, output)
}

/// HMAC-DRBG Reseed function (SP 800-90A Rev. 1, Section 10.1.2.4).
///
/// Reseed(state, entropy, additional_input):
///   seed_material = entropy || additional_input
///   (K, V) = Update(seed_material, K, V)
pub fn hmac_drbg_reseed(
    state: &HmacDrbgState,
    entropy: &[u8], entropy_len: usize,
    additional: &[u8], additional_len: usize,
) -> HmacDrbgState {
    // Build seed_material = entropy || additional
    let mut seed_material: [u8; MAX_SEED_MATERIAL] = [0u8; MAX_SEED_MATERIAL];

    for i in 0..MAX_SEED_MATERIAL {
        if i < entropy_len {
            seed_material[i] = entropy[i];
        }
    }
    for i in 0..MAX_SEED_MATERIAL {
        if i < additional_len {
            if entropy_len + i < MAX_SEED_MATERIAL {
                seed_material[entropy_len + i] = additional[i];
            }
        }
    }

    let seed_len = entropy_len + additional_len;
    hmac_drbg_update(state, &seed_material, seed_len)
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
    fn instantiate_deterministic() {
        // Same inputs should produce same state
        let entropy = [0x42u8; 32];
        let nonce = [0x13u8; 16];
        let s1 = hmac_drbg_instantiate(&entropy, 32, &nonce, 16, &[], 0);
        let s2 = hmac_drbg_instantiate(&entropy, 32, &nonce, 16, &[], 0);
        assert_eq!(s1.key, s2.key);
        assert_eq!(s1.v, s2.v);
    }
}

// =========================================================================
// Unit tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // NIST SHA-256 test: empty string
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

    // NIST SHA-256 test: "abc"
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

    // RFC 4231 Test Case 1: HMAC-SHA-256
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

    // Test instantiate produces non-zero state
    #[test]
    fn test_instantiate_nonzero() {
        let entropy = [0x42u8; 32];
        let nonce = [0x13u8; 16];
        let state = hmac_drbg_instantiate(&entropy, 32, &nonce, 16, &[], 0);
        // Key and V should not be the initial values after update
        assert_ne!(state.key, [0x00u8; 32], "Key should be updated from initial");
        assert_ne!(state.v, [0x01u8; 32], "V should be updated from initial");
    }

    // Test that update with empty data only does one round
    #[test]
    fn test_update_empty_data() {
        let state = HmacDrbgState {
            key: [0x00u8; 32],
            v: [0x01u8; 32],
        };
        let new_state = hmac_drbg_update(&state, &[], 0);
        // After update with empty data:
        // K = HMAC(0x00*32, 0x01*32 || 0x00)
        // V = HMAC(K, 0x01*32)
        // Should be deterministic
        let new_state2 = hmac_drbg_update(&state, &[], 0);
        assert_eq!(new_state.key, new_state2.key);
        assert_eq!(new_state.v, new_state2.v);
    }

    // Test generate produces output and updates state
    #[test]
    fn test_generate_produces_output() {
        let entropy = [0xabu8; 32];
        let nonce = [0xcdu8; 16];
        let state = hmac_drbg_instantiate(&entropy, 32, &nonce, 16, &[], 0);
        let (new_state, output) = hmac_drbg_generate(&state, 32, &[], 0);
        // Output should not be all zeros
        let mut all_zero = true;
        for i in 0..32 {
            if output[i] != 0 { all_zero = false; }
        }
        assert!(!all_zero, "Generate output should not be all zeros");
        // State should be updated
        assert_ne!(new_state.key, state.key, "Key should change after generate");
    }

    // Test reseed changes state
    #[test]
    fn test_reseed_changes_state() {
        let entropy = [0x11u8; 32];
        let nonce = [0x22u8; 16];
        let state = hmac_drbg_instantiate(&entropy, 32, &nonce, 16, &[], 0);

        let new_entropy = [0x33u8; 32];
        let reseeded = hmac_drbg_reseed(&state, &new_entropy, 32, &[], 0);
        assert_ne!(reseeded.key, state.key, "Reseed should change key");
        assert_ne!(reseeded.v, state.v, "Reseed should change V");
    }

    // Test deterministic: same inputs produce same outputs
    #[test]
    fn test_deterministic() {
        let entropy = [0xffu8; 32];
        let nonce = [0xeeu8; 16];

        let state1 = hmac_drbg_instantiate(&entropy, 32, &nonce, 16, &[], 0);
        let (_, output1) = hmac_drbg_generate(&state1, 64, &[], 0);

        let state2 = hmac_drbg_instantiate(&entropy, 32, &nonce, 16, &[], 0);
        let (_, output2) = hmac_drbg_generate(&state2, 64, &[], 0);

        for i in 0..64 {
            assert_eq!(output1[i], output2[i], "Output should be deterministic at byte {}", i);
        }
    }

    // NIST CAVP test vector: SHA-256, no prediction resistance, no reseed
    // Count = 0
    #[test]
    fn test_nist_cavp_count0() {
        let entropy: [u8; 32] = [
            0xca, 0x85, 0x19, 0x11, 0x34, 0x93, 0x84, 0xbf,
            0xfe, 0x89, 0xde, 0x1c, 0xbd, 0xc4, 0x6e, 0x68,
            0x31, 0xe4, 0x4d, 0x34, 0xa4, 0xfb, 0x93, 0x5e,
            0xe2, 0x85, 0xdd, 0x14, 0xb7, 0x1a, 0x74, 0x88,
        ];
        let nonce: [u8; 16] = [
            0x65, 0x9b, 0xa9, 0x6c, 0x60, 0x1d, 0xc6, 0x9f,
            0xc9, 0x02, 0x94, 0x08, 0x05, 0xec, 0x0c, 0xa8,
        ];

        // Instantiate
        let state = hmac_drbg_instantiate(&entropy, 32, &nonce, 16, &[], 0);

        // First generate (128 bytes, output discarded)
        let (state2, _) = hmac_drbg_generate(&state, 128, &[], 0);

        // Second generate (128 bytes, output checked)
        let (_, output) = hmac_drbg_generate(&state2, 128, &[], 0);

        let expected: [u8; 128] = [
            0xe5, 0x28, 0xe9, 0xab, 0xf2, 0xde, 0xce, 0x54,
            0xd4, 0x7c, 0x7e, 0x75, 0xe5, 0xfe, 0x30, 0x21,
            0x49, 0xf8, 0x17, 0xea, 0x9f, 0xb4, 0xbe, 0xe6,
            0xf4, 0x19, 0x96, 0x97, 0xd0, 0x4d, 0x5b, 0x89,
            0xd5, 0x4f, 0xbb, 0x97, 0x8a, 0x15, 0xb5, 0xc4,
            0x43, 0xc9, 0xec, 0x21, 0x03, 0x6d, 0x24, 0x60,
            0xb6, 0xf7, 0x3e, 0xba, 0xd0, 0xdc, 0x2a, 0xba,
            0x6e, 0x62, 0x4a, 0xbf, 0x07, 0x74, 0x5b, 0xc1,
            0x07, 0x69, 0x4b, 0xb7, 0x54, 0x7b, 0xb0, 0x99,
            0x5f, 0x70, 0xde, 0x25, 0xd6, 0xb2, 0x9e, 0x2d,
            0x30, 0x11, 0xbb, 0x19, 0xd2, 0x76, 0x76, 0xc0,
            0x71, 0x62, 0xc8, 0xb5, 0xcc, 0xde, 0x06, 0x68,
            0x96, 0x1d, 0xf8, 0x68, 0x03, 0x48, 0x2c, 0xb3,
            0x7e, 0xd6, 0xd5, 0xc0, 0xbb, 0x8d, 0x50, 0xcf,
            0x1f, 0x50, 0xd4, 0x76, 0xaa, 0x04, 0x58, 0xbd,
            0xab, 0xa8, 0x06, 0xf4, 0x8b, 0xe9, 0xdc, 0xb8,
        ];

        for i in 0..128 {
            assert_eq!(output[i], expected[i],
                "NIST CAVP mismatch at byte {} (got 0x{:02x}, expected 0x{:02x})",
                i, output[i], expected[i]);
        }
    }
}
