//! Cross-validation: cmac-hax vs RustCrypto `cmac` crate.
//!
//! Verifies that our hax-compatible AES-CMAC implementation produces
//! identical tags to the reference `cmac` crate for various message lengths.

use cmac::Mac;
use aes::Aes128;

/// Compute CMAC using the reference `cmac` crate.
fn reference_cmac(key: &[u8; 16], msg: &[u8]) -> [u8; 16] {
    type CmacAes128 = cmac::Cmac<Aes128>;
    let mut mac = CmacAes128::new_from_slice(key).expect("valid key length");
    mac.update(msg);
    let result = mac.finalize();
    let bytes = result.into_bytes();
    let mut out = [0u8; 16];
    out.copy_from_slice(&bytes);
    out
}

/// Compute CMAC using our hax-compatible implementation.
fn our_cmac(key: &[u8; 16], msg: &[u8]) -> [u8; 16] {
    cmac_hax::cmac_bytes(key, msg, msg.len())
}

// ============================================================
// Cross-check: SP 800-38B test key, various lengths
// ============================================================

const TEST_KEY: [u8; 16] = [
    0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6,
    0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c,
];

#[test]
fn crosscheck_empty() {
    let ref_tag = reference_cmac(&TEST_KEY, &[]);
    let our_tag = our_cmac(&TEST_KEY, &[]);
    assert_eq!(our_tag, ref_tag, "empty message mismatch");
}

#[test]
fn crosscheck_1_byte() {
    let msg = [0x42u8];
    let ref_tag = reference_cmac(&TEST_KEY, &msg);
    let our_tag = our_cmac(&TEST_KEY, &msg);
    assert_eq!(our_tag, ref_tag, "1-byte message mismatch");
}

#[test]
fn crosscheck_15_bytes() {
    let msg: [u8; 15] = [
        0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
        0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
    ];
    let ref_tag = reference_cmac(&TEST_KEY, &msg);
    let our_tag = our_cmac(&TEST_KEY, &msg);
    assert_eq!(our_tag, ref_tag, "15-byte message mismatch");
}

#[test]
fn crosscheck_16_bytes() {
    let msg: [u8; 16] = [
        0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96,
        0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a,
    ];
    let ref_tag = reference_cmac(&TEST_KEY, &msg);
    let our_tag = our_cmac(&TEST_KEY, &msg);
    assert_eq!(our_tag, ref_tag, "16-byte message mismatch");
}

#[test]
fn crosscheck_17_bytes() {
    let msg: [u8; 17] = [
        0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96,
        0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a,
        0xae,
    ];
    let ref_tag = reference_cmac(&TEST_KEY, &msg);
    let our_tag = our_cmac(&TEST_KEY, &msg);
    assert_eq!(our_tag, ref_tag, "17-byte message mismatch");
}

#[test]
fn crosscheck_32_bytes() {
    let msg: [u8; 32] = [
        0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96,
        0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a,
        0xae, 0x2d, 0x8a, 0x57, 0x1e, 0x03, 0xac, 0x9c,
        0x9e, 0xb7, 0x6f, 0xac, 0x45, 0xaf, 0x8e, 0x51,
    ];
    let ref_tag = reference_cmac(&TEST_KEY, &msg);
    let our_tag = our_cmac(&TEST_KEY, &msg);
    assert_eq!(our_tag, ref_tag, "32-byte message mismatch");
}

#[test]
fn crosscheck_40_bytes() {
    let msg: [u8; 40] = [
        0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96,
        0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a,
        0xae, 0x2d, 0x8a, 0x57, 0x1e, 0x03, 0xac, 0x9c,
        0x9e, 0xb7, 0x6f, 0xac, 0x45, 0xaf, 0x8e, 0x51,
        0x30, 0xc8, 0x1c, 0x46, 0xa3, 0x5c, 0xe4, 0x11,
    ];
    let ref_tag = reference_cmac(&TEST_KEY, &msg);
    let our_tag = our_cmac(&TEST_KEY, &msg);
    assert_eq!(our_tag, ref_tag, "40-byte message mismatch");
}

#[test]
fn crosscheck_64_bytes() {
    let msg: [u8; 64] = [
        0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96,
        0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a,
        0xae, 0x2d, 0x8a, 0x57, 0x1e, 0x03, 0xac, 0x9c,
        0x9e, 0xb7, 0x6f, 0xac, 0x45, 0xaf, 0x8e, 0x51,
        0x30, 0xc8, 0x1c, 0x46, 0xa3, 0x5c, 0xe4, 0x11,
        0xe5, 0xfb, 0xc1, 0x19, 0x1a, 0x0a, 0x52, 0xef,
        0xf6, 0x9f, 0x24, 0x45, 0xdf, 0x4f, 0x9b, 0x17,
        0xad, 0x2b, 0x41, 0x7b, 0xe6, 0x6c, 0x37, 0x10,
    ];
    let ref_tag = reference_cmac(&TEST_KEY, &msg);
    let our_tag = our_cmac(&TEST_KEY, &msg);
    assert_eq!(our_tag, ref_tag, "64-byte message mismatch");
}

// ============================================================
// Cross-check: different key
// ============================================================

#[test]
fn crosscheck_alt_key_empty() {
    let key: [u8; 16] = [0xffu8; 16];
    let ref_tag = reference_cmac(&key, &[]);
    let our_tag = our_cmac(&key, &[]);
    assert_eq!(our_tag, ref_tag, "alt key empty message mismatch");
}

#[test]
fn crosscheck_alt_key_48_bytes() {
    let key: [u8; 16] = [
        0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77,
        0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff,
    ];
    let msg: [u8; 48] = [0xab; 48];
    let ref_tag = reference_cmac(&key, &msg);
    let our_tag = our_cmac(&key, &msg);
    assert_eq!(our_tag, ref_tag, "alt key 48-byte message mismatch");
}
