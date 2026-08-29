//! Cross-validation: aesccm-hax vs RustCrypto `ccm` crate.
//!
//! Verifies that our hax-compatible AES-CCM implementation produces
//! identical ciphertext and tags to the reference `ccm` crate for
//! various message lengths, AAD lengths, and tag sizes.

#![allow(clippy::needless_range_loop, clippy::manual_memcpy)]

use ccm::aead::generic_array::GenericArray;
use ccm::aead::{Aead, KeyInit, Payload};
use ccm::consts::{U8, U13};
use aes::Aes128;

/// Type alias for AES-128-CCM with 8-byte tag and 13-byte nonce.
type Aes128Ccm = ccm::Ccm<Aes128, U8, U13>;

/// Compute CCM encrypt using the reference `ccm` crate.
/// Returns (ciphertext, tag) separately.
fn reference_ccm_encrypt(key: &[u8; 16], nonce: &[u8; 13], plaintext: &[u8], aad: &[u8]) -> (Vec<u8>, Vec<u8>) {
    let cipher = Aes128Ccm::new(GenericArray::from_slice(key));
    let nonce_ga = GenericArray::from_slice(nonce);
    let payload = Payload { msg: plaintext, aad };
    let result = cipher.encrypt(nonce_ga, payload).expect("encryption failed");

    // The ccm crate returns ciphertext || tag appended
    let ct_len = plaintext.len();
    let ct = result[..ct_len].to_vec();
    let tag = result[ct_len..].to_vec();
    (ct, tag)
}

/// Compute CCM encrypt using our hax-compatible implementation.
fn our_ccm_encrypt(key: &[u8; 16], nonce: &[u8; 13], plaintext: &[u8], aad: &[u8]) -> (Vec<u8>, Vec<u8>) {
    let mut pt_buf = [0u8; aesccm_hax::MAX_MSG];
    for i in 0..plaintext.len() {
        pt_buf[i] = plaintext[i];
    }
    let mut aad_buf = [0u8; aesccm_hax::MAX_AAD];
    for i in 0..aad.len() {
        aad_buf[i] = aad[i];
    }

    let (ct, tag) = aesccm_hax::ccm_encrypt(key, nonce, 13, &pt_buf, plaintext.len(), &aad_buf, aad.len(), 8);

    let ct_vec = ct[..plaintext.len()].to_vec();
    let tag_vec = tag[..8].to_vec();
    (ct_vec, tag_vec)
}

// ============================================================
// Cross-check tests
// ============================================================

const TEST_KEY: [u8; 16] = [
    0xC0, 0xC1, 0xC2, 0xC3, 0xC4, 0xC5, 0xC6, 0xC7,
    0xC8, 0xC9, 0xCA, 0xCB, 0xCC, 0xCD, 0xCE, 0xCF,
];

const TEST_NONCE: [u8; 13] = [
    0x00, 0x00, 0x00, 0x03, 0x02, 0x01, 0x00,
    0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5,
];

#[test]
fn crosscheck_1_byte_msg() {
    let msg = [0x42u8];
    let aad = [0x00u8, 0x01, 0x02, 0x03];
    let (ref_ct, ref_tag) = reference_ccm_encrypt(&TEST_KEY, &TEST_NONCE, &msg, &aad);
    let (our_ct, our_tag) = our_ccm_encrypt(&TEST_KEY, &TEST_NONCE, &msg, &aad);
    assert_eq!(our_ct, ref_ct, "1-byte msg: ciphertext mismatch");
    assert_eq!(our_tag, ref_tag, "1-byte msg: tag mismatch");
}

#[test]
fn crosscheck_16_byte_msg() {
    let msg: [u8; 16] = [
        0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F,
        0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
    ];
    let aad: [u8; 8] = [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07];
    let (ref_ct, ref_tag) = reference_ccm_encrypt(&TEST_KEY, &TEST_NONCE, &msg, &aad);
    let (our_ct, our_tag) = our_ccm_encrypt(&TEST_KEY, &TEST_NONCE, &msg, &aad);
    assert_eq!(our_ct, ref_ct, "16-byte msg: ciphertext mismatch");
    assert_eq!(our_tag, ref_tag, "16-byte msg: tag mismatch");
}

#[test]
fn crosscheck_23_byte_msg() {
    let msg: [u8; 23] = [
        0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F,
        0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
        0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E,
    ];
    let aad: [u8; 8] = [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07];
    let (ref_ct, ref_tag) = reference_ccm_encrypt(&TEST_KEY, &TEST_NONCE, &msg, &aad);
    let (our_ct, our_tag) = our_ccm_encrypt(&TEST_KEY, &TEST_NONCE, &msg, &aad);
    assert_eq!(our_ct, ref_ct, "23-byte msg: ciphertext mismatch");
    assert_eq!(our_tag, ref_tag, "23-byte msg: tag mismatch");
}

#[test]
fn crosscheck_48_byte_msg() {
    let msg: [u8; 48] = [0xAB; 48];
    let aad: [u8; 16] = [
        0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80,
        0x90, 0xA0, 0xB0, 0xC0, 0xD0, 0xE0, 0xF0, 0x00,
    ];
    let (ref_ct, ref_tag) = reference_ccm_encrypt(&TEST_KEY, &TEST_NONCE, &msg, &aad);
    let (our_ct, our_tag) = our_ccm_encrypt(&TEST_KEY, &TEST_NONCE, &msg, &aad);
    assert_eq!(our_ct, ref_ct, "48-byte msg: ciphertext mismatch");
    assert_eq!(our_tag, ref_tag, "48-byte msg: tag mismatch");
}

#[test]
fn crosscheck_no_aad() {
    let msg: [u8; 32] = [
        0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
        0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10,
        0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18,
        0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F, 0x20,
    ];
    let aad: [u8; 0] = [];
    let (ref_ct, ref_tag) = reference_ccm_encrypt(&TEST_KEY, &TEST_NONCE, &msg, &aad);
    let (our_ct, our_tag) = our_ccm_encrypt(&TEST_KEY, &TEST_NONCE, &msg, &aad);
    assert_eq!(our_ct, ref_ct, "no-AAD 32-byte msg: ciphertext mismatch");
    assert_eq!(our_tag, ref_tag, "no-AAD 32-byte msg: tag mismatch");
}

#[test]
fn crosscheck_empty_plaintext_with_aad() {
    let msg: [u8; 0] = [];
    let aad: [u8; 12] = [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
                          0x08, 0x09, 0x0A, 0x0B];
    let (ref_ct, ref_tag) = reference_ccm_encrypt(&TEST_KEY, &TEST_NONCE, &msg, &aad);
    let (our_ct, our_tag) = our_ccm_encrypt(&TEST_KEY, &TEST_NONCE, &msg, &aad);
    assert_eq!(our_ct, ref_ct, "empty pt with AAD: ciphertext mismatch");
    assert_eq!(our_tag, ref_tag, "empty pt with AAD: tag mismatch");
}

// ============================================================
// Cross-check with alternative key
// ============================================================

#[test]
fn crosscheck_alt_key_33_bytes() {
    let key: [u8; 16] = [
        0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
        0x88, 0x99, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF,
    ];
    let nonce: [u8; 13] = [
        0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16,
        0x17, 0x18, 0x19, 0x1A, 0x1B, 0x1C,
    ];
    let msg: [u8; 33] = [0x55; 33];
    let aad: [u8; 20] = [0xAA; 20];
    let (ref_ct, ref_tag) = reference_ccm_encrypt(&key, &nonce, &msg, &aad);
    let (our_ct, our_tag) = our_ccm_encrypt(&key, &nonce, &msg, &aad);
    assert_eq!(our_ct, ref_ct, "alt key 33-byte: ciphertext mismatch");
    assert_eq!(our_tag, ref_tag, "alt key 33-byte: tag mismatch");
}

#[test]
fn crosscheck_all_zeros() {
    let key: [u8; 16] = [0x00; 16];
    let nonce: [u8; 13] = [0x00; 13];
    let msg: [u8; 1] = [0x00];
    let aad: [u8; 1] = [0x00];
    let (ref_ct, ref_tag) = reference_ccm_encrypt(&key, &nonce, &msg, &aad);
    let (our_ct, our_tag) = our_ccm_encrypt(&key, &nonce, &msg, &aad);
    assert_eq!(our_ct, ref_ct, "all zeros: ciphertext mismatch");
    assert_eq!(our_tag, ref_tag, "all zeros: tag mismatch");
}

#[test]
fn crosscheck_all_ff() {
    let key: [u8; 16] = [0xFF; 16];
    let nonce: [u8; 13] = [0xFF; 13];
    let msg: [u8; 64] = [0xFF; 64];
    let aad: [u8; 32] = [0xFF; 32];
    let (ref_ct, ref_tag) = reference_ccm_encrypt(&key, &nonce, &msg, &aad);
    let (our_ct, our_tag) = our_ccm_encrypt(&key, &nonce, &msg, &aad);
    assert_eq!(our_ct, ref_ct, "all 0xFF: ciphertext mismatch");
    assert_eq!(our_tag, ref_tag, "all 0xFF: tag mismatch");
}
