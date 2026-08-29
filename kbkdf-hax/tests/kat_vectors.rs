//! Self-consistency tests for KBKDF in Counter Mode (NIST SP 800-108 Rev. 1,
//! Section 4.1) with HMAC-SHA-256 as the PRF, through the public API.
//!
//! The expected KBKDF outputs here are computed from the specification with
//! the crate's own HMAC; the published NIST CAVP vectors are in
//! `tests/cavp_kdfctr.rs`. The SHA-256 and HMAC checks at the end use the
//! FIPS 180-4 and RFC 4231 literals.

use kbkdf_hax::*;

// ============================================================
// Test key (32 bytes)
// ============================================================

const TEST_KI: KbkdfKey = [
    0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
    0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff,
    0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
    0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff,
];

// ============================================================
// KAT 1: Single block (L = 256 bits)
// ============================================================
//
// PRF input = [0x00,0x00,0x00,0x01] || "test" || [0x00] || "context" || [0x00,0x00,0x01,0x00]
//           = 0x000000017465737400636f6e7465787400000100
// Expected  = HMAC-SHA-256(TEST_KI, PRF input)
//           = 35d7ddab0544e75e19f9ea7acae0683902bd8c5ea90cafe88f7144c620df7403

#[test]
fn kat_kbkdf_single_block() {
    let dk = kbkdf_counter_hmac256(&TEST_KI, b"test", 4, b"context", 7, 256);

    let expected: [u8; 32] = [
        0x35, 0xd7, 0xdd, 0xab, 0x05, 0x44, 0xe7, 0x5e,
        0x19, 0xf9, 0xea, 0x7a, 0xca, 0xe0, 0x68, 0x39,
        0x02, 0xbd, 0x8c, 0x5e, 0xa9, 0x0c, 0xaf, 0xe8,
        0x8f, 0x71, 0x44, 0xc6, 0x20, 0xdf, 0x74, 0x03,
    ];

    for i in 0..32 {
        assert_eq!(dk[i], expected[i], "KAT single block mismatch at byte {}", i);
    }
    // Remaining bytes should be zero (unused)
    assert_eq!(dk[32..MAX_DK_LEN], [0u8; MAX_DK_LEN - 32],
        "KAT single block: unused bytes should be zero");
}

// ============================================================
// KAT 2: Two blocks (L = 512 bits = 64 bytes)
// ============================================================
//
// Block 1 PRF input = [0x00000001] || "test" || [0x00] || "context" || [0x00000200]
// Block 2 PRF input = [0x00000002] || "test" || [0x00] || "context" || [0x00000200]

#[test]
fn kat_kbkdf_two_blocks() {
    let dk = kbkdf_counter_hmac256(&TEST_KI, b"test", 4, b"context", 7, 512);

    let expected: [u8; 64] = [
        // Block 1
        0x62, 0x05, 0x73, 0xa5, 0x89, 0x8e, 0xe1, 0xaa,
        0x7a, 0x85, 0xbc, 0x8d, 0xf4, 0x1d, 0x14, 0x15,
        0x7d, 0x50, 0x40, 0x26, 0xdf, 0xab, 0xac, 0x5b,
        0xba, 0x5a, 0xb1, 0x54, 0x97, 0xd2, 0xa4, 0x12,
        // Block 2
        0x99, 0xa5, 0xd0, 0xa3, 0x27, 0x4f, 0xbe, 0xb3,
        0x27, 0x15, 0x2c, 0xea, 0x16, 0x87, 0x36, 0xb1,
        0x11, 0xc2, 0xf7, 0x59, 0x49, 0x00, 0xbc, 0xff,
        0xd5, 0x6b, 0xd0, 0x5e, 0x4f, 0xeb, 0xa6, 0x56,
    ];

    for i in 0..64 {
        assert_eq!(dk[i], expected[i], "KAT two blocks mismatch at byte {}", i);
    }
}

// ============================================================
// KAT 3: Verify PRF input construction
// ============================================================
//
// Manually verify that the HMAC input for single-block derivation is correct
// by computing HMAC-SHA-256 directly and comparing.

#[test]
fn kat_kbkdf_manual_hmac_check() {
    // Build PRF input manually: [0x00000001] || "test" || 0x00 || "context" || [0x00000100]
    let prf_input: [u8; 20] = [
        0x00, 0x00, 0x00, 0x01,             // counter = 1
        0x74, 0x65, 0x73, 0x74,             // "test"
        0x00,                               // separator
        0x63, 0x6f, 0x6e, 0x74, 0x65, 0x78, 0x74, // "context"
        0x00, 0x00, 0x01, 0x00,             // L = 256
    ];

    // Direct HMAC computation
    let direct_hmac = hmac_sha256(&TEST_KI, 32, &prf_input, 20);

    // KBKDF output
    let dk = kbkdf_counter_hmac256(&TEST_KI, b"test", 4, b"context", 7, 256);

    for i in 0..32 {
        assert_eq!(dk[i], direct_hmac[i],
            "KBKDF output must match direct HMAC at byte {}", i);
    }
}

// ============================================================
// KAT 4: Empty label and context
// ============================================================

#[test]
fn kat_kbkdf_empty_label_context() {
    let dk = kbkdf_counter_hmac256(&TEST_KI, b"", 0, b"", 0, 256);

    // PRF input: [0x00000001] || "" || 0x00 || "" || [0x00000100]
    // = [0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00]
    let prf_input: [u8; 9] = [
        0x00, 0x00, 0x00, 0x01,  // counter
        0x00,                    // separator (empty label then 0x00)
        0x00, 0x00, 0x01, 0x00,  // L = 256
    ];
    let expected = hmac_sha256(&TEST_KI, 32, &prf_input, 9);

    for i in 0..32 {
        assert_eq!(dk[i], expected[i],
            "KBKDF empty label/context mismatch at byte {}", i);
    }
}

// ============================================================
// KAT 5: Determinism
// ============================================================

#[test]
fn kat_kbkdf_deterministic() {
    let dk1 = kbkdf_counter_hmac256(&TEST_KI, b"det", 3, b"test", 4, 512);
    let dk2 = kbkdf_counter_hmac256(&TEST_KI, b"det", 3, b"test", 4, 512);
    assert_eq!(dk1, dk2, "KBKDF must be deterministic");
}

// ============================================================
// KAT 6: Different L values produce different results
// ============================================================

#[test]
fn kat_kbkdf_different_l_values() {
    // L=256 and L=512 should produce different first 32 bytes because
    // the L encoding is part of the PRF input
    let dk_256 = kbkdf_counter_hmac256(&TEST_KI, b"test", 4, b"ctx", 3, 256);
    let dk_512 = kbkdf_counter_hmac256(&TEST_KI, b"test", 4, b"ctx", 3, 512);

    let mut differ = false;
    for i in 0..32 {
        if dk_256[i] != dk_512[i] {
            differ = true;
        }
    }
    assert!(differ, "Different L values should produce different derived keys");
}

// ============================================================
// SHA-256 and HMAC integration tests (sanity)
// ============================================================

#[test]
fn kat_sha256_empty() {
    let digest = sha256(&[], 0);
    let expected: [u8; 32] = [
        0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14,
        0x9a, 0xfb, 0xf4, 0xc8, 0x99, 0x6f, 0xb9, 0x24,
        0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c,
        0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55,
    ];
    assert_eq!(digest, expected);
}

#[test]
fn kat_hmac_rfc4231_case1() {
    let key: [u8; 20] = [0x0b; 20];
    let msg = b"Hi There";
    let tag = hmac_sha256(&key, 20, msg, 8);
    let expected: [u8; 32] = [
        0xb0, 0x34, 0x4c, 0x61, 0xd8, 0xdb, 0x38, 0x53,
        0x5c, 0xa8, 0xaf, 0xce, 0xaf, 0x0b, 0xf1, 0x2b,
        0x88, 0x1d, 0xc2, 0x00, 0xc9, 0x83, 0x3d, 0xa7,
        0x26, 0xe9, 0x37, 0x6c, 0x2e, 0x32, 0xcf, 0xf7,
    ];
    assert_eq!(tag, expected);
}
