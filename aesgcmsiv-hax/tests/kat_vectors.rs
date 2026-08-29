//! Known Answer Tests for AES-GCM-SIV (RFC 8452).
//!
//! Test vectors from RFC 8452, Appendix C.1 (AEAD_AES_128_GCM_SIV),
//! https://www.rfc-editor.org/rfc/rfc8452.txt, transcribed verbatim.

use aesgcmsiv_hax::*;

// ============================================================
// RFC 8452 Appendix C: AES-128 GCM-SIV
// ============================================================

const TEST_KEY: AesKey = [
    0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
];

const TEST_NONCE: Nonce = [
    0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00,
];

// ============================================================
// Test Case 1: Empty plaintext, empty AAD
// ============================================================

#[test]
fn kat_c1_empty() {
    let expected_tag: Block = [
        0xdc, 0x20, 0xe2, 0xd8, 0x3f, 0x25, 0x70, 0x5b,
        0xb4, 0x9e, 0x43, 0x9e, 0xca, 0x56, 0xde, 0x25,
    ];

    let (_, num_ct_blocks, tag) = aes_gcm_siv_seal(
        &TEST_KEY, &TEST_NONCE, &[], 0, &[], 0,
    );
    assert_eq!(num_ct_blocks, 0, "empty plaintext");
    assert_eq!(tag, expected_tag, "C.1 tag");

    // Verify open
    let result = aes_gcm_siv_open(&TEST_KEY, &TEST_NONCE, &[], 0, &[], 0, &tag);
    assert!(result.is_some(), "C.1 open should succeed");
}

// ============================================================
// Test Case 2: 8-byte plaintext, empty AAD
// ============================================================

#[test]
fn kat_c2_8bytes() {
    let pt: [u8; 8] = [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
    let expected_ct: [u8; 8] = [0xb5, 0xd8, 0x39, 0x33, 0x0a, 0xc7, 0xb7, 0x86];
    let expected_tag: Block = [
        0x57, 0x87, 0x82, 0xff, 0xf6, 0x01, 0x3b, 0x81,
        0x5b, 0x28, 0x7c, 0x22, 0x49, 0x3a, 0x36, 0x4c,
    ];

    let (ct_blocks, _, tag) = aes_gcm_siv_seal(
        &TEST_KEY, &TEST_NONCE, &[], 0, &pt, 8,
    );
    assert_eq!(tag, expected_tag, "C.2 tag");

    let mut ct_bytes: [u8; 8] = [0u8; 8];
    blocks_to_bytes(&ct_blocks, 8, &mut ct_bytes);
    assert_eq!(ct_bytes, expected_ct, "C.2 ciphertext");

    // Verify open
    let result = aes_gcm_siv_open(&TEST_KEY, &TEST_NONCE, &[], 0, &expected_ct, 8, &tag);
    assert!(result.is_some(), "C.2 open should succeed");
    if let Some((pt_blocks, _)) = result {
        let mut recovered: [u8; 8] = [0u8; 8];
        blocks_to_bytes(&pt_blocks, 8, &mut recovered);
        assert_eq!(recovered, pt, "C.2 plaintext recovery");
    }
}

// ============================================================
// Test Case 3: 12-byte plaintext, empty AAD
// ============================================================

#[test]
fn kat_c3_12bytes() {
    let pt: [u8; 12] = [
        0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00,
    ];
    let expected_ct: [u8; 12] = [
        0x73, 0x23, 0xea, 0x61, 0xd0, 0x59, 0x32, 0x26,
        0x00, 0x47, 0xd9, 0x42,
    ];
    let expected_tag: Block = [
        0xa4, 0x97, 0x8d, 0xb3, 0x57, 0x39, 0x1a, 0x0b,
        0xc4, 0xfd, 0xec, 0x8b, 0x0d, 0x10, 0x66, 0x39,
    ];

    let (ct_blocks, _, tag) = aes_gcm_siv_seal(
        &TEST_KEY, &TEST_NONCE, &[], 0, &pt, 12,
    );
    assert_eq!(tag, expected_tag, "C.3 tag");

    let mut ct_bytes: [u8; 12] = [0u8; 12];
    blocks_to_bytes(&ct_blocks, 12, &mut ct_bytes);
    assert_eq!(ct_bytes, expected_ct, "C.3 ciphertext");

    // Verify open
    let result = aes_gcm_siv_open(&TEST_KEY, &TEST_NONCE, &[], 0, &expected_ct, 12, &tag);
    assert!(result.is_some(), "C.3 open should succeed");
    if let Some((pt_blocks, _)) = result {
        let mut recovered: [u8; 12] = [0u8; 12];
        blocks_to_bytes(&pt_blocks, 12, &mut recovered);
        assert_eq!(recovered, pt, "C.3 plaintext recovery");
    }
}

// ============================================================
// Roundtrip tests
// ============================================================

#[test]
fn kat_roundtrip_empty() {
    let key: AesKey = [0xff; 16];
    let nonce: Nonce = [0xaa; 12];

    let (_, _, tag) = aes_gcm_siv_seal(&key, &nonce, &[], 0, &[], 0);
    let result = aes_gcm_siv_open(&key, &nonce, &[], 0, &[], 0, &tag);
    assert!(result.is_some(), "roundtrip empty should succeed");
}

#[test]
fn kat_roundtrip_with_aad() {
    let key: AesKey = [0x42; 16];
    let nonce: Nonce = [0x01, 0x02, 0x03, 0x04, 0x05, 0x06,
                        0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c];
    let aad: [u8; 8] = [0xfe, 0xed, 0xfa, 0xce, 0xde, 0xad, 0xbe, 0xef];
    let pt: [u8; 16] = [0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
                         0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff];

    let (ct_blocks, _, tag) = aes_gcm_siv_seal(&key, &nonce, &aad, 8, &pt, 16);

    let mut ct_bytes: [u8; 16] = [0u8; 16];
    blocks_to_bytes(&ct_blocks, 16, &mut ct_bytes);

    let result = aes_gcm_siv_open(&key, &nonce, &aad, 8, &ct_bytes, 16, &tag);
    assert!(result.is_some(), "roundtrip with AAD should succeed");
    if let Some((pt_blocks, _)) = result {
        let mut recovered: [u8; 16] = [0u8; 16];
        blocks_to_bytes(&pt_blocks, 16, &mut recovered);
        assert_eq!(recovered, pt, "roundtrip plaintext");
    }
}

#[test]
fn kat_roundtrip_multi_block() {
    let key: AesKey = [0x55; 16];
    let nonce: Nonce = [0x11; 12];
    let pt: [u8; 48] = [
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
        0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
        0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
        0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f,
        0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27,
        0x28, 0x29, 0x2a, 0x2b, 0x2c, 0x2d, 0x2e, 0x2f,
    ];

    let (ct_blocks, _, tag) = aes_gcm_siv_seal(&key, &nonce, &[], 0, &pt, 48);

    let mut ct_bytes: [u8; 48] = [0u8; 48];
    blocks_to_bytes(&ct_blocks, 48, &mut ct_bytes);

    let result = aes_gcm_siv_open(&key, &nonce, &[], 0, &ct_bytes, 48, &tag);
    assert!(result.is_some(), "multi-block roundtrip should succeed");
    if let Some((pt_blocks, _)) = result {
        let mut recovered: [u8; 48] = [0u8; 48];
        blocks_to_bytes(&pt_blocks, 48, &mut recovered);
        assert_eq!(recovered, pt, "multi-block roundtrip plaintext");
    }
}

// ============================================================
// Tag verification failure
// ============================================================

#[test]
fn kat_tampered_ciphertext_fails() {
    let key: AesKey = [0x42; 16];
    let nonce: Nonce = [0x01; 12];
    let pt: [u8; 8] = [0xaa; 8];

    let (ct_blocks, _, tag) = aes_gcm_siv_seal(&key, &nonce, &[], 0, &pt, 8);

    let mut ct_bytes: [u8; 8] = [0u8; 8];
    blocks_to_bytes(&ct_blocks, 8, &mut ct_bytes);

    // Tamper with ciphertext
    ct_bytes[0] ^= 0x01;

    let result = aes_gcm_siv_open(&key, &nonce, &[], 0, &ct_bytes, 8, &tag);
    assert!(result.is_none(), "tampered ciphertext should fail verification");
}

#[test]
fn kat_wrong_key_fails() {
    let key: AesKey = [0x42; 16];
    let wrong_key: AesKey = [0x43; 16];
    let nonce: Nonce = [0x01; 12];
    let pt: [u8; 8] = [0xbb; 8];

    let (ct_blocks, _, tag) = aes_gcm_siv_seal(&key, &nonce, &[], 0, &pt, 8);

    let mut ct_bytes: [u8; 8] = [0u8; 8];
    blocks_to_bytes(&ct_blocks, 8, &mut ct_bytes);

    let result = aes_gcm_siv_open(&wrong_key, &nonce, &[], 0, &ct_bytes, 8, &tag);
    assert!(result.is_none(), "wrong key should fail verification");
}

// ============================================================
// POLYVAL tests
// ============================================================

#[test]
fn kat_polyval_zero_blocks() {
    let h: Block = [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
                    0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10];
    let blocks: [Block; MAX_BLOCKS] = [[0u8; 16]; MAX_BLOCKS];
    let result = polyval(&h, &blocks, 0);
    assert_eq!(result, ZERO_BLOCK, "POLYVAL with 0 blocks should be 0");
}

// ============================================================
// AES-128 encrypt known answer test
// ============================================================

#[test]
fn kat_aes128() {
    let key: AesKey = [
        0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6,
        0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c,
    ];
    let pt: Block = [
        0x32, 0x43, 0xf6, 0xa8, 0x88, 0x5a, 0x30, 0x8d,
        0x31, 0x31, 0x98, 0xa2, 0xe0, 0x37, 0x07, 0x34,
    ];
    let expected: Block = [
        0x39, 0x25, 0x84, 0x1d, 0x02, 0xdc, 0x09, 0xfb,
        0xdc, 0x11, 0x85, 0x97, 0x19, 0x6a, 0x0b, 0x32,
    ];
    assert_eq!(aes128_encrypt(&key, &pt), expected);
}

// ============================================================
// Further RFC 8452 Appendix C.1 cases (same key and nonce)
// ============================================================

/// Record authentication key and record encryption key printed for every
/// case of Appendix C.1 (they depend only on key and nonce).
#[test]
fn kat_derive_keys() {
    let expected_auth: Block = [
        0xd9, 0xb3, 0x60, 0x27, 0x96, 0x94, 0x94, 0x1a,
        0xc5, 0xdb, 0xc6, 0x98, 0x7a, 0xda, 0x73, 0x77,
    ];
    let expected_enc: Block = [
        0x40, 0x04, 0xa0, 0xdc, 0xd8, 0x62, 0xf2, 0xa5,
        0x73, 0x60, 0x21, 0x9d, 0x2d, 0x44, 0xef, 0x6c,
    ];
    let (auth_key, enc_key) = derive_keys(&TEST_KEY, &TEST_NONCE);
    assert_eq!(auth_key, expected_auth, "record authentication key");
    assert_eq!(enc_key, expected_enc, "record encryption key");
}

/// Seals `pt` with `aad` under the shared key/nonce and checks ciphertext
/// and tag, then opens the reference ciphertext and checks the plaintext.
fn check_case<const P: usize, const A: usize>(
    pt: &[u8; P], aad: &[u8; A], expected_ct: &[u8; P], expected_tag: &Block, label: &str,
) {
    let (ct_blocks, _, tag) = aes_gcm_siv_seal(&TEST_KEY, &TEST_NONCE, aad, A, pt, P);
    assert_eq!(&tag, expected_tag, "{label} tag");
    let mut ct_bytes: [u8; P] = [0u8; P];
    blocks_to_bytes(&ct_blocks, P, &mut ct_bytes);
    assert_eq!(&ct_bytes, expected_ct, "{label} ciphertext");

    let result = aes_gcm_siv_open(&TEST_KEY, &TEST_NONCE, aad, A, expected_ct, P, expected_tag);
    let (pt_blocks, n) = result.unwrap_or_else(|| panic!("{label} open should succeed"));
    assert_eq!(n, P.div_ceil(16), "{label} block count");
    let mut recovered: [u8; P] = [0u8; P];
    blocks_to_bytes(&pt_blocks, P, &mut recovered);
    assert_eq!(&recovered, pt, "{label} plaintext recovery");
}

/// Plaintext `01 00.. | 02 00.. | ...`: block i (from 1) is `i` followed by zeros.
fn counting_blocks<const N: usize>() -> [u8; N] {
    let mut pt = [0u8; N];
    let mut i = 0;
    while i < N {
        pt[i] = (i / 16 + 1) as u8;
        i += 16;
    }
    pt
}

#[test]
fn kat_c4_16bytes() {
    let pt: [u8; 16] = counting_blocks();
    let expected_ct: [u8; 16] = [
        0x74, 0x3f, 0x7c, 0x80, 0x77, 0xab, 0x25, 0xf8,
        0x62, 0x4e, 0x2e, 0x94, 0x85, 0x79, 0xcf, 0x77,
    ];
    let expected_tag: Block = [
        0x30, 0x3a, 0xaf, 0x90, 0xf6, 0xfe, 0x21, 0x19,
        0x9c, 0x60, 0x68, 0x57, 0x74, 0x37, 0xa0, 0xc4,
    ];
    check_case(&pt, &[], &expected_ct, &expected_tag, "C.1 case 4");
}

#[test]
fn kat_c5_32bytes() {
    let pt: [u8; 32] = counting_blocks();
    let expected_ct: [u8; 32] = [
        0x84, 0xe0, 0x7e, 0x62, 0xba, 0x83, 0xa6, 0x58,
        0x54, 0x17, 0x24, 0x5d, 0x7e, 0xc4, 0x13, 0xa9,
        0xfe, 0x42, 0x7d, 0x63, 0x15, 0xc0, 0x9b, 0x57,
        0xce, 0x45, 0xf2, 0xe3, 0x93, 0x6a, 0x94, 0x45,
    ];
    let expected_tag: Block = [
        0x1a, 0x8e, 0x45, 0xdc, 0xd4, 0x57, 0x8c, 0x66,
        0x7c, 0xd8, 0x68, 0x47, 0xbf, 0x61, 0x55, 0xff,
    ];
    check_case(&pt, &[], &expected_ct, &expected_tag, "C.1 case 5");
}

#[test]
fn kat_c6_48bytes() {
    let pt: [u8; 48] = counting_blocks();
    let expected_ct: [u8; 48] = [
        0x3f, 0xd2, 0x4c, 0xe1, 0xf5, 0xa6, 0x7b, 0x75,
        0xbf, 0x23, 0x51, 0xf1, 0x81, 0xa4, 0x75, 0xc7,
        0xb8, 0x00, 0xa5, 0xb4, 0xd3, 0xdc, 0xf7, 0x01,
        0x06, 0xb1, 0xee, 0xa8, 0x2f, 0xa1, 0xd6, 0x4d,
        0xf4, 0x2b, 0xf7, 0x22, 0x61, 0x22, 0xfa, 0x92,
        0xe1, 0x7a, 0x40, 0xee, 0xaa, 0xc1, 0x20, 0x1b,
    ];
    let expected_tag: Block = [
        0x5e, 0x6e, 0x31, 0x1d, 0xbf, 0x39, 0x5d, 0x35,
        0xb0, 0xfe, 0x39, 0xc2, 0x71, 0x43, 0x88, 0xf8,
    ];
    check_case(&pt, &[], &expected_ct, &expected_tag, "C.1 case 6");
}

#[test]
fn kat_c7_64bytes() {
    let pt: [u8; 64] = counting_blocks();
    let expected_ct: [u8; 64] = [
        0x24, 0x33, 0x66, 0x8f, 0x10, 0x58, 0x19, 0x0f,
        0x6d, 0x43, 0xe3, 0x60, 0xf4, 0xf3, 0x5c, 0xd8,
        0xe4, 0x75, 0x12, 0x7c, 0xfc, 0xa7, 0x02, 0x8e,
        0xa8, 0xab, 0x5c, 0x20, 0xf7, 0xab, 0x2a, 0xf0,
        0x25, 0x16, 0xa2, 0xbd, 0xcb, 0xc0, 0x8d, 0x52,
        0x1b, 0xe3, 0x7f, 0xf2, 0x8c, 0x15, 0x2b, 0xba,
        0x36, 0x69, 0x7f, 0x25, 0xb4, 0xcd, 0x16, 0x9c,
        0x65, 0x90, 0xd1, 0xdd, 0x39, 0x56, 0x6d, 0x3f,
    ];
    let expected_tag: Block = [
        0x8a, 0x26, 0x3d, 0xd3, 0x17, 0xaa, 0x88, 0xd5,
        0x6b, 0xdf, 0x39, 0x36, 0xdb, 0xa7, 0x5b, 0xb8,
    ];
    check_case(&pt, &[], &expected_ct, &expected_tag, "C.1 case 7");
}

/// Case 7 also prints the POLYVAL result over the padded input
/// (four plaintext blocks and the length block).
#[test]
fn kat_c7_polyval() {
    let (auth_key, _) = derive_keys(&TEST_KEY, &TEST_NONCE);
    let mut blocks: [Block; MAX_BLOCKS] = [[0u8; 16]; MAX_BLOCKS];
    for (i, b) in blocks.iter_mut().enumerate().take(4) { b[0] = (i + 1) as u8; }
    blocks[4] = [
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    ];
    let expected: Block = [
        0x1e, 0x39, 0xb6, 0xd3, 0x34, 0x4d, 0x34, 0x8f,
        0x60, 0x44, 0xf8, 0x99, 0x35, 0xd1, 0xcf, 0x78,
    ];
    assert_eq!(polyval(&auth_key, &blocks, 5), expected, "C.1 case 7 POLYVAL result");
}

#[test]
fn kat_c8_8bytes_aad1() {
    let pt: [u8; 8] = [0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
    let aad: [u8; 1] = [0x01];
    let expected_ct: [u8; 8] = [0x1e, 0x6d, 0xab, 0xa3, 0x56, 0x69, 0xf4, 0x27];
    let expected_tag: Block = [
        0x3b, 0x0a, 0x1a, 0x25, 0x60, 0x96, 0x9c, 0xdf,
        0x79, 0x0d, 0x99, 0x75, 0x9a, 0xbd, 0x15, 0x08,
    ];
    check_case(&pt, &aad, &expected_ct, &expected_tag, "C.1 case 8");
}

#[test]
fn kat_c9_12bytes_aad1() {
    let pt: [u8; 12] = [
        0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00,
    ];
    let aad: [u8; 1] = [0x01];
    let expected_ct: [u8; 12] = [
        0x29, 0x6c, 0x78, 0x89, 0xfd, 0x99, 0xf4, 0x19,
        0x17, 0xf4, 0x46, 0x20,
    ];
    let expected_tag: Block = [
        0x08, 0x29, 0x9c, 0x51, 0x02, 0x74, 0x5a, 0xaa,
        0x3a, 0x0c, 0x46, 0x9f, 0xad, 0x9e, 0x07, 0x5a,
    ];
    check_case(&pt, &aad, &expected_ct, &expected_tag, "C.1 case 9");
}

#[test]
fn kat_c10_16bytes_aad1() {
    let pt: [u8; 16] = [
        0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    ];
    let aad: [u8; 1] = [0x01];
    let expected_ct: [u8; 16] = [
        0xe2, 0xb0, 0xc5, 0xda, 0x79, 0xa9, 0x01, 0xc1,
        0x74, 0x5f, 0x70, 0x05, 0x25, 0xcb, 0x33, 0x5b,
    ];
    let expected_tag: Block = [
        0x8f, 0x89, 0x36, 0xec, 0x03, 0x9e, 0x4e, 0x4b,
        0xb9, 0x7e, 0xbd, 0x8c, 0x44, 0x57, 0x44, 0x1f,
    ];
    check_case(&pt, &aad, &expected_ct, &expected_tag, "C.1 case 10");
}

#[test]
fn kat_c14_4bytes_aad12() {
    let pt: [u8; 4] = [0x02, 0x00, 0x00, 0x00];
    let aad: [u8; 12] = [
        0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00,
    ];
    let expected_ct: [u8; 4] = [0xa8, 0xfe, 0x3e, 0x87];
    let expected_tag: Block = [
        0x07, 0xeb, 0x1f, 0x84, 0xfb, 0x28, 0xf8, 0xcb,
        0x73, 0xde, 0x8e, 0x99, 0xe2, 0xf4, 0x8a, 0x14,
    ];
    check_case(&pt, &aad, &expected_ct, &expected_tag, "C.1 case 14");
}

/// Case 14 prints the POLYVAL input (padded AAD block, padded plaintext
/// block, length block) and its result.
#[test]
fn kat_c14_polyval() {
    let (auth_key, _) = derive_keys(&TEST_KEY, &TEST_NONCE);
    let mut blocks: [Block; MAX_BLOCKS] = [[0u8; 16]; MAX_BLOCKS];
    blocks[0][0] = 0x01;
    blocks[1][0] = 0x02;
    blocks[2] = [
        0x60, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    ];
    let expected: Block = [
        0xf6, 0xce, 0x9d, 0x3d, 0xcd, 0x68, 0xa2, 0xfd,
        0x60, 0x3c, 0x7e, 0xcc, 0x18, 0xfb, 0x99, 0x18,
    ];
    assert_eq!(polyval(&auth_key, &blocks, 3), expected, "C.1 case 14 POLYVAL result");
}
