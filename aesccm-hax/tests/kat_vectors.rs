//! Known Answer Tests for AES-CCM (SP 800-38C).
//!
//! Test vectors from RFC 3610, Section 8 (Packet Vectors #1-#4).
//! These validate the public API against known-good outputs.

#![allow(clippy::needless_range_loop, clippy::manual_memcpy)]

use aesccm_hax::*;

// ============================================================
// RFC 3610 common key for vectors #1-#4
// Key = C0 C1 C2 C3 C4 C5 C6 C7 C8 C9 CA CB CC CD CE CF
// ============================================================

const RFC3610_KEY: AesKey = [
    0xC0, 0xC1, 0xC2, 0xC3, 0xC4, 0xC5, 0xC6, 0xC7,
    0xC8, 0xC9, 0xCA, 0xCB, 0xCC, 0xCD, 0xCE, 0xCF,
];

/// Helper: pack a byte slice into a MAX_MSG array.
fn pack_msg(data: &[u8]) -> [u8; MAX_MSG] {
    let mut buf = [0u8; MAX_MSG];
    for i in 0..data.len() {
        buf[i] = data[i];
    }
    buf
}

/// Helper: pack a byte slice into a MAX_AAD array.
fn pack_aad(data: &[u8]) -> [u8; MAX_AAD] {
    let mut buf = [0u8; MAX_AAD];
    for i in 0..data.len() {
        buf[i] = data[i];
    }
    buf
}

// ============================================================
// RFC 3610, Packet Vector #1
// Nonce = 00 00 00 03 02 01 00 A0 A1 A2 A3 A4 A5
// AAD = 00 01 02 03 04 05 06 07 (8 bytes)
// Plaintext = 08 09 0A ... 1E (23 bytes)
// Tag length = 8
// ============================================================

#[test]
fn kat_rfc3610_vector1() {
    let nonce: [u8; 13] = [
        0x00, 0x00, 0x00, 0x03, 0x02, 0x01, 0x00,
        0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5,
    ];
    let pt_bytes: [u8; 23] = [
        0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F,
        0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
        0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E,
    ];
    let aad_bytes: [u8; 8] = [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07];

    // Expected output: ciphertext(23) || tag(8)
    let expected_ct: [u8; 23] = [
        0x58, 0x8C, 0x97, 0x9A, 0x61, 0xC6, 0x63, 0xD2,
        0xF0, 0x66, 0xD0, 0xC2, 0xC0, 0xF9, 0x89, 0x80,
        0x6D, 0x5F, 0x6B, 0x61, 0xDA, 0xC3, 0x84,
    ];
    let expected_tag: [u8; 8] = [
        0x17, 0xE8, 0xD1, 0x2C, 0xFD, 0xF9, 0x26, 0xE0,
    ];

    let plaintext = pack_msg(&pt_bytes);
    let aad = pack_aad(&aad_bytes);

    let (ct, tag) = ccm_encrypt(&RFC3610_KEY, &nonce, 13, &plaintext, 23, &aad, 8, 8);

    for i in 0..23 {
        assert_eq!(ct[i], expected_ct[i], "V1 ciphertext byte {}", i);
    }
    for i in 0..8 {
        assert_eq!(tag[i], expected_tag[i], "V1 tag byte {}", i);
    }

    // Decrypt round-trip
    let mut recv_tag = [0u8; 16];
    for i in 0..8 { recv_tag[i] = tag[i]; }
    let result = ccm_decrypt(&RFC3610_KEY, &nonce, 13, &ct, 23, &aad, 8, &recv_tag, 8);
    assert!(result.is_some(), "V1 decrypt should succeed");
    let recovered = result.unwrap();
    for i in 0..23 {
        assert_eq!(recovered[i], pt_bytes[i], "V1 recovered byte {}", i);
    }
}

// ============================================================
// RFC 3610, Packet Vector #2
// Nonce = 00 00 00 04 03 02 01 A0 A1 A2 A3 A4 A5
// AAD = 00 01 02 03 04 05 06 07 (8 bytes)
// Plaintext = 08 09 0A ... 1F (24 bytes)
// Tag length = 8
// ============================================================

#[test]
fn kat_rfc3610_vector2() {
    let nonce: [u8; 13] = [
        0x00, 0x00, 0x00, 0x04, 0x03, 0x02, 0x01,
        0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5,
    ];
    let pt_bytes: [u8; 24] = [
        0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F,
        0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
        0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F,
    ];
    let aad_bytes: [u8; 8] = [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07];

    let expected_ct: [u8; 24] = [
        0x72, 0xC9, 0x1A, 0x36, 0xE1, 0x35, 0xF8, 0xCF,
        0x29, 0x1C, 0xA8, 0x94, 0x08, 0x5C, 0x87, 0xE3,
        0xCC, 0x15, 0xC4, 0x39, 0xC9, 0xE4, 0x3A, 0x3B,
    ];
    let expected_tag: [u8; 8] = [
        0xA0, 0x91, 0xD5, 0x6E, 0x10, 0x40, 0x09, 0x16,
    ];

    let plaintext = pack_msg(&pt_bytes);
    let aad = pack_aad(&aad_bytes);

    let (ct, tag) = ccm_encrypt(&RFC3610_KEY, &nonce, 13, &plaintext, 24, &aad, 8, 8);

    for i in 0..24 {
        assert_eq!(ct[i], expected_ct[i], "V2 ciphertext byte {}", i);
    }
    for i in 0..8 {
        assert_eq!(tag[i], expected_tag[i], "V2 tag byte {}", i);
    }

    // Decrypt round-trip
    let mut recv_tag = [0u8; 16];
    for i in 0..8 { recv_tag[i] = tag[i]; }
    let result = ccm_decrypt(&RFC3610_KEY, &nonce, 13, &ct, 24, &aad, 8, &recv_tag, 8);
    assert!(result.is_some(), "V2 decrypt should succeed");
    let recovered = result.unwrap();
    for i in 0..24 {
        assert_eq!(recovered[i], pt_bytes[i], "V2 recovered byte {}", i);
    }
}

// ============================================================
// RFC 3610, Packet Vector #3
// Nonce = 00 00 00 05 04 03 02 A0 A1 A2 A3 A4 A5
// AAD = 00 01 02 03 04 05 06 07 (8 bytes)
// Plaintext = 08 09 0A ... 20 (25 bytes)
// Tag length = 8
// ============================================================

#[test]
fn kat_rfc3610_vector3() {
    let nonce: [u8; 13] = [
        0x00, 0x00, 0x00, 0x05, 0x04, 0x03, 0x02,
        0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5,
    ];
    let pt_bytes: [u8; 25] = [
        0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F,
        0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
        0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F,
        0x20,
    ];
    let aad_bytes: [u8; 8] = [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07];

    let expected_ct: [u8; 25] = [
        0x51, 0xB1, 0xE5, 0xF4, 0x4A, 0x19, 0x7D, 0x1D,
        0xA4, 0x6B, 0x0F, 0x8E, 0x2D, 0x28, 0x2A, 0xE8,
        0x71, 0xE8, 0x38, 0xBB, 0x64, 0xDA, 0x85, 0x96,
        0x57,
    ];
    let expected_tag: [u8; 8] = [
        0x4A, 0xDA, 0xA7, 0x6F, 0xBD, 0x9F, 0xB0, 0xC5,
    ];

    let plaintext = pack_msg(&pt_bytes);
    let aad = pack_aad(&aad_bytes);

    let (ct, tag) = ccm_encrypt(&RFC3610_KEY, &nonce, 13, &plaintext, 25, &aad, 8, 8);

    for i in 0..25 {
        assert_eq!(ct[i], expected_ct[i], "V3 ciphertext byte {}", i);
    }
    for i in 0..8 {
        assert_eq!(tag[i], expected_tag[i], "V3 tag byte {}", i);
    }

    // Decrypt round-trip
    let mut recv_tag = [0u8; 16];
    for i in 0..8 { recv_tag[i] = tag[i]; }
    let result = ccm_decrypt(&RFC3610_KEY, &nonce, 13, &ct, 25, &aad, 8, &recv_tag, 8);
    assert!(result.is_some(), "V3 decrypt should succeed");
    let recovered = result.unwrap();
    for i in 0..25 {
        assert_eq!(recovered[i], pt_bytes[i], "V3 recovered byte {}", i);
    }
}

// ============================================================
// RFC 3610, Packet Vector #4
// Nonce = 00 00 00 06 05 04 03 A0 A1 A2 A3 A4 A5
// AAD = 00 01 02 03 04 05 06 07 08 09 0A 0B (12 bytes)
// Plaintext = 0C 0D 0E ... 1E (19 bytes)
// Tag length = 8
// ============================================================

#[test]
fn kat_rfc3610_vector4() {
    let nonce: [u8; 13] = [
        0x00, 0x00, 0x00, 0x06, 0x05, 0x04, 0x03,
        0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5,
    ];
    let pt_bytes: [u8; 19] = [
        0x0C, 0x0D, 0x0E, 0x0F, 0x10, 0x11, 0x12, 0x13,
        0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1A, 0x1B,
        0x1C, 0x1D, 0x1E,
    ];
    let aad_bytes: [u8; 12] = [
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
        0x08, 0x09, 0x0A, 0x0B,
    ];

    let expected_ct: [u8; 19] = [
        0xA2, 0x8C, 0x68, 0x65, 0x93, 0x9A, 0x9A, 0x79,
        0xFA, 0xAA, 0x5C, 0x4C, 0x2A, 0x9D, 0x4A, 0x91,
        0xCD, 0xAC, 0x8C,
    ];
    let expected_tag: [u8; 8] = [
        0x96, 0xC8, 0x61, 0xB9, 0xC9, 0xE6, 0x1E, 0xF1,
    ];

    let plaintext = pack_msg(&pt_bytes);
    let aad = pack_aad(&aad_bytes);

    let (ct, tag) = ccm_encrypt(&RFC3610_KEY, &nonce, 13, &plaintext, 19, &aad, 12, 8);

    for i in 0..19 {
        assert_eq!(ct[i], expected_ct[i], "V4 ciphertext byte {}", i);
    }
    for i in 0..8 {
        assert_eq!(tag[i], expected_tag[i], "V4 tag byte {}", i);
    }

    // Decrypt round-trip
    let mut recv_tag = [0u8; 16];
    for i in 0..8 { recv_tag[i] = tag[i]; }
    let result = ccm_decrypt(&RFC3610_KEY, &nonce, 13, &ct, 19, &aad, 12, &recv_tag, 8);
    assert!(result.is_some(), "V4 decrypt should succeed");
    let recovered = result.unwrap();
    for i in 0..19 {
        assert_eq!(recovered[i], pt_bytes[i], "V4 recovered byte {}", i);
    }
}

// ============================================================
// Additional: tamper detection across all vectors
// ============================================================

#[test]
fn kat_rfc3610_vector1_tamper() {
    let nonce: [u8; 13] = [
        0x00, 0x00, 0x00, 0x03, 0x02, 0x01, 0x00,
        0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5,
    ];
    let pt_bytes: [u8; 23] = [
        0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F,
        0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
        0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E,
    ];
    let aad_bytes: [u8; 8] = [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07];

    let plaintext = pack_msg(&pt_bytes);
    let aad = pack_aad(&aad_bytes);

    let (mut ct, tag) = ccm_encrypt(&RFC3610_KEY, &nonce, 13, &plaintext, 23, &aad, 8, 8);

    // Flip one bit in ciphertext
    ct[10] ^= 0x01;

    let mut recv_tag = [0u8; 16];
    for i in 0..8 { recv_tag[i] = tag[i]; }
    let result = ccm_decrypt(&RFC3610_KEY, &nonce, 13, &ct, 23, &aad, 8, &recv_tag, 8);
    assert!(result.is_none(), "V1 tampered ciphertext should fail");
}
