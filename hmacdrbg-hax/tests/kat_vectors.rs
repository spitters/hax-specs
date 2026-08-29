//! Known Answer Tests for HMAC_DRBG with SHA-256 (SP 800-90A Rev. 1).
//!
//! Test vectors from NIST CAVP HMAC_DRBG with SHA-256,
//! no prediction resistance, no reseed.
//! These serve as integration tests validating the public API independently.

use hmacdrbg_hax::*;

// ============================================================
// NIST CAVP: HMAC_DRBG SHA-256, no prediction resistance
// Count = 0
// ============================================================

#[test]
fn kat_nist_cavp_sha256_count0() {
    // EntropyInput = ca851911349384bffe89de1cbdc46e6831e44d34a4fb935ee285dd14b71a7488
    let entropy: [u8; 32] = [
        0xca, 0x85, 0x19, 0x11, 0x34, 0x93, 0x84, 0xbf,
        0xfe, 0x89, 0xde, 0x1c, 0xbd, 0xc4, 0x6e, 0x68,
        0x31, 0xe4, 0x4d, 0x34, 0xa4, 0xfb, 0x93, 0x5e,
        0xe2, 0x85, 0xdd, 0x14, 0xb7, 0x1a, 0x74, 0x88,
    ];

    // Nonce = 659ba96c601dc69fc902940805ec0ca8
    let nonce: [u8; 16] = [
        0x65, 0x9b, 0xa9, 0x6c, 0x60, 0x1d, 0xc6, 0x9f,
        0xc9, 0x02, 0x94, 0x08, 0x05, 0xec, 0x0c, 0xa8,
    ];

    // PersonalizationString = (empty)

    // Instantiate
    let state = hmac_drbg_instantiate(&entropy, 32, &nonce, 16, &[], 0);

    // First generate call: 128 bytes, no additional input, output discarded
    let (state2, _first_output) = hmac_drbg_generate(&state, 128, &[], 0);

    // Second generate call: 128 bytes, no additional input
    let (_, second_output) = hmac_drbg_generate(&state2, 128, &[], 0);

    // ReturnedBits (from second call) =
    // e528e9abf2dece54d47c7e75e5fe302149f817ea9fb4bee6f4199697d04d5b89
    // d54fbb978a15b5c443c9ec21036d2460b6f73ebad0dc2aba6e624abf07745bc1
    // 07694bb7547bb0995f70de25d6b29e2d3011bb19d27676c07162c8b5ccde0668
    // 961df86803482cb37ed6d5c0bb8d50cf1f50d476aa0458bdaba806f48be9dcb8
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
        assert_eq!(second_output[i], expected[i],
            "NIST CAVP Count=0 mismatch at byte {} (got 0x{:02x}, expected 0x{:02x})",
            i, second_output[i], expected[i]);
    }
}

// ============================================================
// Instantiate: verify deterministic behavior
// ============================================================

#[test]
fn kat_instantiate_deterministic() {
    let entropy = [0x42u8; 32];
    let nonce = [0x13u8; 16];

    let s1 = hmac_drbg_instantiate(&entropy, 32, &nonce, 16, &[], 0);
    let s2 = hmac_drbg_instantiate(&entropy, 32, &nonce, 16, &[], 0);

    assert_eq!(s1.key, s2.key, "Instantiate must be deterministic (key)");
    assert_eq!(s1.v, s2.v, "Instantiate must be deterministic (V)");
}

// ============================================================
// Generate: verify deterministic output
// ============================================================

#[test]
fn kat_generate_deterministic() {
    let entropy = [0xaau8; 32];
    let nonce = [0xbbu8; 16];

    let state = hmac_drbg_instantiate(&entropy, 32, &nonce, 16, &[], 0);

    let (_, out1) = hmac_drbg_generate(&state, 64, &[], 0);
    let (_, out2) = hmac_drbg_generate(&state, 64, &[], 0);

    for i in 0..64 {
        assert_eq!(out1[i], out2[i],
            "Generate must be deterministic at byte {}", i);
    }
}

// ============================================================
// Reseed: verify state changes
// ============================================================

#[test]
fn kat_reseed_changes_output() {
    let entropy = [0x11u8; 32];
    let nonce = [0x22u8; 16];

    let state = hmac_drbg_instantiate(&entropy, 32, &nonce, 16, &[], 0);

    // Generate without reseed
    let (_, out_no_reseed) = hmac_drbg_generate(&state, 32, &[], 0);

    // Reseed then generate
    let new_entropy = [0x33u8; 32];
    let reseeded = hmac_drbg_reseed(&state, &new_entropy, 32, &[], 0);
    let (_, out_reseeded) = hmac_drbg_generate(&reseeded, 32, &[], 0);

    // Outputs should differ
    let mut same = true;
    for i in 0..32 {
        if out_no_reseed[i] != out_reseeded[i] { same = false; }
    }
    assert!(!same, "Reseed should change the output");
}

// ============================================================
// Update: verify with and without provided_data differ
// ============================================================

#[test]
fn kat_update_with_data_differs() {
    let state = HmacDrbgState {
        key: [0x00u8; SHA256_DIGEST_SIZE],
        v: [0x01u8; SHA256_DIGEST_SIZE],
    };

    let empty_update = hmac_drbg_update(&state, &[], 0);
    let data = [0xffu8; 32];
    let data_update = hmac_drbg_update(&state, &data, 32);

    assert_ne!(empty_update.key, data_update.key,
        "Update with data should differ from update without data");
    assert_ne!(empty_update.v, data_update.v,
        "Update with data should produce different V");
}
