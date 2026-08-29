use crate::aes::AesCipher;
use crate::counter::{gctr_one_block, inc32, make_j0, xor_blocks};
use crate::types::{AesBlock, AesKey, GcmNonce, GcmState, GcmTag};

/// Trait abstracting GCM cryptographic primitives.
///
/// Extends `AesCipher` with GHASH multiplication in GF(2^128).
/// The trait lets the field multiplication be treated as an opaque
/// primitive by an extraction backend; [`crate::realgcm::RealGcm`]
/// implements it with [`crate::ghash_impl::ghash_mul`].
pub trait GcmCrypto: Copy + AesCipher {
    /// Multiply two elements in GF(2^128) for GHASH.
    ///
    /// Uses the GCM polynomial x^128 + x^7 + x^2 + x + 1.
    fn ghash_multiply(self, h: &GcmState, x: &GcmState) -> GcmState;
}

/// Zero block constant.
pub fn zero_block() -> AesBlock {
    [0u8; 16]
}

/// Encode a u64 as 8 big-endian bytes into a buffer starting at `offset`.
fn encode_u64_be(buf: &mut [u8; 16], offset: usize, value: u64) {
    buf[offset] = ((value >> 56) & 0xFF) as u8;
    buf[offset + 1] = ((value >> 48) & 0xFF) as u8;
    buf[offset + 2] = ((value >> 40) & 0xFF) as u8;
    buf[offset + 3] = ((value >> 32) & 0xFF) as u8;
    buf[offset + 4] = ((value >> 24) & 0xFF) as u8;
    buf[offset + 5] = ((value >> 16) & 0xFF) as u8;
    buf[offset + 6] = ((value >> 8) & 0xFF) as u8;
    buf[offset + 7] = (value & 0xFF) as u8;
}

/// Build the length block for GHASH: [len(A) in bits || len(C) in bits].
///
/// Per NIST SP 800-38D Section 6.4, the final GHASH input is the
/// concatenation of the bit lengths of AAD and ciphertext, each
/// encoded as a 64-bit big-endian integer.
pub fn make_len_block(aad_bytes: u64, ct_bytes: u64) -> AesBlock {
    let mut block: AesBlock = [0u8; 16];
    let aad_bits: u64 = aad_bytes * 8;
    let ct_bits: u64 = ct_bytes * 8;
    encode_u64_be(&mut block, 0, aad_bits);
    encode_u64_be(&mut block, 8, ct_bits);
    block
}

/// Extract a 16-byte block from a 64-byte array at the given block index.
fn extract_block(data: &[u8; 64], block_idx: usize) -> AesBlock {
    let mut block: AesBlock = [0u8; 16];
    let offset: usize = block_idx * 16;
    for i in 0..16 {
        block[i] = data[offset + i];
    }
    block
}

/// Write a 16-byte block into a 64-byte array at the given block index.
fn write_block(data: &mut [u8; 64], block_idx: usize, block: &AesBlock) {
    let offset: usize = block_idx * 16;
    for i in 0..16 {
        data[offset + i] = block[i];
    }
}

/// Perform one GHASH step: state = (state XOR block) * H.
pub fn ghash_step<C: GcmCrypto>(
    crypto: C,
    h: &GcmState,
    state: &GcmState,
    block: &AesBlock,
) -> GcmState {
    let xored: GcmState = xor_blocks(state, block);
    crypto.ghash_multiply(h, &xored)
}

/// Compute GHASH over AAD (1 block), ciphertext (4 blocks), and length block.
///
/// GHASH_H(A, C) processes:
///   1. AAD block
///   2. Ciphertext blocks (4 blocks = 64 bytes)
///   3. Length block [len(A) || len(C)] in bits
pub fn ghash_compute<C: GcmCrypto>(
    crypto: C,
    h: &GcmState,
    aad: &AesBlock,
    ciphertext: &[u8; 64],
) -> GcmState {
    let zero: GcmState = zero_block();

    // Step 1: Process AAD (1 block of 16 bytes).
    let state: GcmState = ghash_step(crypto, h, &zero, aad);

    // Step 2: Process ciphertext blocks (4 blocks).
    let ct_block_0: AesBlock = extract_block(ciphertext, 0);
    let state: GcmState = ghash_step(crypto, h, &state, &ct_block_0);

    let ct_block_1: AesBlock = extract_block(ciphertext, 1);
    let state: GcmState = ghash_step(crypto, h, &state, &ct_block_1);

    let ct_block_2: AesBlock = extract_block(ciphertext, 2);
    let state: GcmState = ghash_step(crypto, h, &state, &ct_block_2);

    let ct_block_3: AesBlock = extract_block(ciphertext, 3);
    let state: GcmState = ghash_step(crypto, h, &state, &ct_block_3);

    // Step 3: Process length block.
    // AAD = 16 bytes = 128 bits, ciphertext = 64 bytes = 512 bits.
    let len_block: AesBlock = make_len_block(16, 64);
    let state: GcmState = ghash_step(crypto, h, &state, &len_block);

    state
}

/// Encrypt 4 blocks (64 bytes) using AES-128-GCM.
///
/// Implements NIST SP 800-38D Section 7.1 (GCM-AE_K):
///   1. H = AES_K(0^128)
///   2. J0 = nonce || 0x00000001
///   3. For i in 0..3: C_i = P_i XOR AES_K(inc32^{i+1}(J0))
///   4. T = GHASH_H(A, C) XOR AES_K(J0)
///
/// # Arguments
/// * `crypto` - Cryptographic primitives (AES + GHASH)
/// * `key` - AES-128 key
/// * `nonce` - 96-bit nonce
/// * `aad` - Additional authenticated data (one 16-byte block)
/// * `plaintext` - 64 bytes of plaintext (4 AES blocks)
///
/// # Returns
/// Tuple of (ciphertext, authentication tag).
pub fn gcm_encrypt<C: GcmCrypto>(
    crypto: C,
    key: &AesKey,
    nonce: &GcmNonce,
    aad: &AesBlock,
    plaintext: &[u8; 64],
) -> ([u8; 64], GcmTag) {
    // Step 1: Compute hash key H = AES_K(0^128).
    let zero: AesBlock = zero_block();
    let h: GcmState = crypto.aes128_encrypt_block(key, &zero);

    // Step 2: Construct initial counter J0 = nonce || 0x00000001.
    let j0: AesBlock = make_j0(nonce);

    // Step 3: Encrypt plaintext in counter mode.
    // Counter starts at inc32(J0) = J0 + 1, so counter value 2.
    let mut ciphertext: [u8; 64] = [0u8; 64];

    let mut counter: AesBlock = inc32(&j0); // counter = 2
    let pt_block_0: AesBlock = extract_block(plaintext, 0);
    let ct_block_0: AesBlock = gctr_one_block(crypto, key, &counter, &pt_block_0);
    write_block(&mut ciphertext, 0, &ct_block_0);

    counter = inc32(&counter); // counter = 3
    let pt_block_1: AesBlock = extract_block(plaintext, 1);
    let ct_block_1: AesBlock = gctr_one_block(crypto, key, &counter, &pt_block_1);
    write_block(&mut ciphertext, 1, &ct_block_1);

    counter = inc32(&counter); // counter = 4
    let pt_block_2: AesBlock = extract_block(plaintext, 2);
    let ct_block_2: AesBlock = gctr_one_block(crypto, key, &counter, &pt_block_2);
    write_block(&mut ciphertext, 2, &ct_block_2);

    counter = inc32(&counter); // counter = 5
    let pt_block_3: AesBlock = extract_block(plaintext, 3);
    let ct_block_3: AesBlock = gctr_one_block(crypto, key, &counter, &pt_block_3);
    write_block(&mut ciphertext, 3, &ct_block_3);

    // Step 4: Compute GHASH over AAD and ciphertext.
    let ghash_result: GcmState = ghash_compute(crypto, &h, aad, &ciphertext);

    // Step 5: Compute tag = GHASH_result XOR AES_K(J0).
    let tag: GcmTag = gctr_one_block(crypto, key, &j0, &ghash_result);

    (ciphertext, tag)
}

/// Compare two 16-byte tags in constant time.
///
/// Returns `true` if and only if all bytes are equal.
pub fn tags_equal(a: &GcmTag, b: &GcmTag) -> bool {
    let mut acc: u8 = 0;
    for i in 0..16 {
        acc |= a[i] ^ b[i];
    }
    acc == 0
}

/// Decrypt 4 blocks (64 bytes) using AES-128-GCM.
///
/// Implements NIST SP 800-38D Section 7.2 (GCM-AD_K):
///   1. H = AES_K(0^128)
///   2. J0 = nonce || 0x00000001
///   3. Recompute tag from AAD and ciphertext
///   4. Verify tag; if mismatch return None
///   5. For i in 0..3: P_i = C_i XOR AES_K(inc32^{i+1}(J0))
///
/// # Arguments
/// * `crypto` - Cryptographic primitives (AES + GHASH)
/// * `key` - AES-128 key
/// * `nonce` - 96-bit nonce
/// * `aad` - Additional authenticated data (one 16-byte block)
/// * `ciphertext` - 64 bytes of ciphertext (4 AES blocks)
/// * `tag` - Authentication tag to verify
///
/// # Returns
/// `Some(plaintext)` if tag verification succeeds, `None` otherwise.
pub fn gcm_decrypt<C: GcmCrypto>(
    crypto: C,
    key: &AesKey,
    nonce: &GcmNonce,
    aad: &AesBlock,
    ciphertext: &[u8; 64],
    tag: &GcmTag,
) -> Option<[u8; 64]> {
    // Step 1: Compute hash key H = AES_K(0^128).
    let zero: AesBlock = zero_block();
    let h: GcmState = crypto.aes128_encrypt_block(key, &zero);

    // Step 2: Construct initial counter J0 = nonce || 0x00000001.
    let j0: AesBlock = make_j0(nonce);

    // Step 3: Compute GHASH over AAD and ciphertext.
    let ghash_result: GcmState = ghash_compute(crypto, &h, aad, ciphertext);

    // Step 4: Compute expected tag = GHASH_result XOR AES_K(J0).
    let expected_tag: GcmTag = gctr_one_block(crypto, key, &j0, &ghash_result);

    // Step 5: Verify tag.
    if !tags_equal(tag, &expected_tag) {
        return None;
    }

    // Step 6: Decrypt ciphertext in counter mode.
    let mut plaintext: [u8; 64] = [0u8; 64];

    let mut counter: AesBlock = inc32(&j0); // counter = 2
    let ct_block_0: AesBlock = extract_block(ciphertext, 0);
    let pt_block_0: AesBlock = gctr_one_block(crypto, key, &counter, &ct_block_0);
    write_block(&mut plaintext, 0, &pt_block_0);

    counter = inc32(&counter); // counter = 3
    let ct_block_1: AesBlock = extract_block(ciphertext, 1);
    let pt_block_1: AesBlock = gctr_one_block(crypto, key, &counter, &ct_block_1);
    write_block(&mut plaintext, 1, &pt_block_1);

    counter = inc32(&counter); // counter = 4
    let ct_block_2: AesBlock = extract_block(ciphertext, 2);
    let pt_block_2: AesBlock = gctr_one_block(crypto, key, &counter, &ct_block_2);
    write_block(&mut plaintext, 2, &pt_block_2);

    counter = inc32(&counter); // counter = 5
    let ct_block_3: AesBlock = extract_block(ciphertext, 3);
    let pt_block_3: AesBlock = gctr_one_block(crypto, key, &counter, &ct_block_3);
    write_block(&mut plaintext, 3, &pt_block_3);

    Some(plaintext)
}
