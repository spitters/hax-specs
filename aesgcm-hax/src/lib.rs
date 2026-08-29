// Copyright (c) 2026 CatCrypt Contributors. MIT license.
//! AES-GCM (NIST SP 800-38D, *Recommendation for Block Cipher Modes of
//! Operation: Galois/Counter Mode (GCM) and GMAC*) as a hax-extractable
//! Rust specification, with AES-128 and AES-256 (FIPS 197) and GHASH over
//! GF(2^128) implemented in the crate.
//!
//! Module map:
//!   * [`types`] — fixed-size key, block, nonce, tag and state aliases;
//!   * [`aes`] — the `AesCipher` trait; [`aes_impl`] — FIPS 197 AES-128/256;
//!   * [`ghash_impl`] — GHASH multiplication (SP 800-38D, Section 6.3);
//!   * [`counter`] — `inc32`, `J0` construction (Section 7.1), block XOR;
//!   * [`gcm`] — fixed-shape GCM (64-byte plaintext, one AAD block) over
//!     the traits; [`realgcm`] — the concrete backend and a
//!     variable-length GCM core for AES-128 and AES-256.
//!
//! Only 96-bit IVs are supported. The crate is `no_std`, has no
//! dependencies, and uses bounded `for` loops and fixed-size arrays.
#![no_std]
// The index-loop, fixed-array style is what hax extracts; these lints ask for
// iterator and slice forms that it does not.
#![allow(clippy::needless_range_loop, clippy::manual_memcpy)]

pub mod aes;
pub mod aes_impl;
pub mod counter;
pub mod gcm;
pub mod ghash_impl;
pub mod realgcm;
pub mod types;

#[cfg(test)]
mod tests {
    use crate::counter::{inc32, make_j0, xor_blocks};
    use crate::gcm::{gcm_decrypt, gcm_encrypt};
    use crate::realgcm::RealGcm;
    use crate::types::{AesBlock, AesKey, GcmNonce};

    #[test]
    fn test_inc32() {
        // Counter block: nonce(12 bytes) || 0x00000001
        let block: AesBlock = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x00, 0x00,
            0x00, 0x01,
        ];
        let result = inc32(&block);
        // Should increment to 0x00000002.
        assert_eq!(result[12], 0x00);
        assert_eq!(result[13], 0x00);
        assert_eq!(result[14], 0x00);
        assert_eq!(result[15], 0x02);
        // Nonce portion unchanged.
        for i in 0..12 {
            assert_eq!(result[i], block[i]);
        }
    }

    #[test]
    fn test_inc32_carry() {
        // Counter at 0x000000FF should carry to 0x00000100.
        let block: AesBlock = [
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0xFF,
        ];
        let result = inc32(&block);
        assert_eq!(result[12], 0x00);
        assert_eq!(result[13], 0x00);
        assert_eq!(result[14], 0x01);
        assert_eq!(result[15], 0x00);
    }

    #[test]
    fn test_inc32_wrap() {
        // Counter at 0xFFFFFFFF should wrap to 0x00000000.
        let block: AesBlock = [
            0xAA, 0xBB, 0xCC, 0xDD, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF,
            0xFF, 0xFF,
        ];
        let result = inc32(&block);
        assert_eq!(result[12], 0x00);
        assert_eq!(result[13], 0x00);
        assert_eq!(result[14], 0x00);
        assert_eq!(result[15], 0x00);
        // First 12 bytes unchanged.
        assert_eq!(result[0], 0xAA);
        assert_eq!(result[1], 0xBB);
        assert_eq!(result[2], 0xCC);
        assert_eq!(result[3], 0xDD);
    }

    #[test]
    fn test_make_j0() {
        let nonce: GcmNonce = [
            0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c,
        ];
        let j0 = make_j0(&nonce);
        // First 12 bytes should be the nonce.
        for i in 0..12 {
            assert_eq!(j0[i], nonce[i]);
        }
        // Last 4 bytes should be 0x00000001.
        assert_eq!(j0[12], 0x00);
        assert_eq!(j0[13], 0x00);
        assert_eq!(j0[14], 0x00);
        assert_eq!(j0[15], 0x01);
    }

    #[test]
    fn test_xor_blocks() {
        let a: AesBlock = [
            0xFF, 0x00, 0xAA, 0x55, 0x01, 0x02, 0x03, 0x04, 0x10, 0x20, 0x30, 0x40, 0x50, 0x60,
            0x70, 0x80,
        ];
        let b: AesBlock = [
            0x0F, 0xF0, 0x55, 0xAA, 0x10, 0x20, 0x30, 0x40, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06,
            0x07, 0x08,
        ];
        let result = xor_blocks(&a, &b);
        assert_eq!(result[0], 0xF0);
        assert_eq!(result[1], 0xF0);
        assert_eq!(result[2], 0xFF);
        assert_eq!(result[3], 0xFF);
        assert_eq!(result[4], 0x11);
        assert_eq!(result[5], 0x22);
        assert_eq!(result[6], 0x33);
        assert_eq!(result[7], 0x44);
        assert_eq!(result[8], 0x11);
        assert_eq!(result[9], 0x22);
        assert_eq!(result[10], 0x33);
        assert_eq!(result[11], 0x44);
        assert_eq!(result[12], 0x55);
        assert_eq!(result[13], 0x66);
        assert_eq!(result[14], 0x77);
        assert_eq!(result[15], 0x88);
    }

    #[test]
    fn test_xor_self_is_zero() {
        let a: AesBlock = [
            0x12, 0x34, 0x56, 0x78, 0x9A, 0xBC, 0xDE, 0xF0, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66,
            0x77, 0x88,
        ];
        let result = xor_blocks(&a, &a);
        for i in 0..16 {
            assert_eq!(result[i], 0x00);
        }
    }

    #[test]
    fn test_encrypt_decrypt_roundtrip() {
        let crypto = RealGcm;
        let key: AesKey = [
            0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E,
            0x0F, 0x10,
        ];
        let nonce: GcmNonce = [
            0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5, 0xA6, 0xA7, 0xA8, 0xA9, 0xAA, 0xAB,
        ];
        let aad: AesBlock = [
            0xB0, 0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7, 0xB8, 0xB9, 0xBA, 0xBB, 0xBC, 0xBD,
            0xBE, 0xBF,
        ];
        let plaintext: [u8; 64] = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D,
            0x0E, 0x0F, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1A, 0x1B,
            0x1C, 0x1D, 0x1E, 0x1F, 0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28, 0x29,
            0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, 0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37,
            0x38, 0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F,
        ];

        let (ciphertext, tag) = gcm_encrypt(crypto, &key, &nonce, &aad, &plaintext);

        // Ciphertext should differ from plaintext (with overwhelming probability).
        let mut differs = false;
        for i in 0..64 {
            if ciphertext[i] != plaintext[i] {
                differs = true;
            }
        }
        assert!(differs, "ciphertext should differ from plaintext");

        // Decrypt should recover original plaintext.
        let decrypted = gcm_decrypt(crypto, &key, &nonce, &aad, &ciphertext, &tag);
        assert!(decrypted.is_some(), "decryption should succeed");
        let recovered = decrypted.unwrap();
        for i in 0..64 {
            assert_eq!(recovered[i], plaintext[i]);
        }
    }

    #[test]
    fn test_tampered_ciphertext_fails() {
        let crypto = RealGcm;
        let key: AesKey = [
            0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E,
            0x0F, 0x10,
        ];
        let nonce: GcmNonce = [
            0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5, 0xA6, 0xA7, 0xA8, 0xA9, 0xAA, 0xAB,
        ];
        let aad: AesBlock = [0u8; 16];
        let plaintext: [u8; 64] = [0x42u8; 64];

        let (mut ciphertext, tag) = gcm_encrypt(crypto, &key, &nonce, &aad, &plaintext);

        // Tamper with ciphertext.
        ciphertext[0] ^= 0x01;

        // Decryption should fail (tag mismatch).
        let result = gcm_decrypt(crypto, &key, &nonce, &aad, &ciphertext, &tag);
        assert!(result.is_none(), "tampered ciphertext should fail verification");
    }

    #[test]
    fn test_tampered_tag_fails() {
        let crypto = RealGcm;
        let key: AesKey = [
            0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E,
            0x0F, 0x10,
        ];
        let nonce: GcmNonce = [
            0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5, 0xA6, 0xA7, 0xA8, 0xA9, 0xAA, 0xAB,
        ];
        let aad: AesBlock = [0u8; 16];
        let plaintext: [u8; 64] = [0x42u8; 64];

        let (ciphertext, mut tag) = gcm_encrypt(crypto, &key, &nonce, &aad, &plaintext);

        // Tamper with tag.
        tag[0] ^= 0x01;

        // Decryption should fail.
        let result = gcm_decrypt(crypto, &key, &nonce, &aad, &ciphertext, &tag);
        assert!(result.is_none(), "tampered tag should fail verification");
    }

    #[test]
    fn test_wrong_aad_fails() {
        let crypto = RealGcm;
        let key: AesKey = [
            0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E,
            0x0F, 0x10,
        ];
        let nonce: GcmNonce = [
            0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5, 0xA6, 0xA7, 0xA8, 0xA9, 0xAA, 0xAB,
        ];
        let aad: AesBlock = [0xFFu8; 16];
        let plaintext: [u8; 64] = [0x42u8; 64];

        let (ciphertext, tag) = gcm_encrypt(crypto, &key, &nonce, &aad, &plaintext);

        // Use different AAD for decryption.
        let wrong_aad: AesBlock = [0x00u8; 16];
        let result = gcm_decrypt(crypto, &key, &nonce, &wrong_aad, &ciphertext, &tag);
        assert!(result.is_none(), "wrong AAD should fail verification");
    }
}
