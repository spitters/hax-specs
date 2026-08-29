//! Differential tests against the RustCrypto `aes-kw` crate.
//!
//! `aes-kw` is a dev-dependency only; nothing from it is linked into the
//! library. Inputs are fixed literals, so the tests are deterministic.

use aeskw_hax::*;
use aes_kw::KekAes128;
use hex_literal::hex;

const KEKS: [AesKey; 3] = [
    hex!("000102030405060708090A0B0C0D0E0F"),
    hex!("2b7e151628aed2a6abf7158809cf4f3c"),
    hex!("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF"),
];

const DATA_128: [[u8; 16]; 3] = [
    hex!("00112233445566778899AABBCCDDEEFF"),
    hex!("deadbeefcafebabe0123456789abcdef"),
    [0u8; 16],
];

const DATA_256: [[u8; 32]; 2] = [
    hex!("00112233445566778899aabbccddeefffedcba98765432100123456789abcdef"),
    [0xFFu8; 32],
];

#[test]
fn cross_check_wrap_unwrap_128() {
    for kek in KEKS.iter() {
        let oracle = KekAes128::from(*kek);
        for data in DATA_128.iter() {
            let ours = aes_wrap_128(kek, data);
            let mut theirs = [0u8; 24];
            oracle.wrap(data, &mut theirs).expect("aes-kw wrap");
            assert_eq!(ours, theirs, "wrap_128 disagrees with aes-kw");

            let mut recovered = [0u8; 16];
            oracle.unwrap(&ours, &mut recovered).expect("aes-kw unwrap");
            assert_eq!(recovered, *data, "aes-kw cannot unwrap our ciphertext");
            assert_eq!(aes_unwrap_128(kek, &theirs), Some(*data), "unwrap_128 rejects aes-kw ciphertext");
        }
    }
}

#[test]
fn cross_check_wrap_unwrap_256() {
    for kek in KEKS.iter() {
        let oracle = KekAes128::from(*kek);
        for data in DATA_256.iter() {
            let ours = aes_wrap_256(kek, data);
            let mut theirs = [0u8; 40];
            oracle.wrap(data, &mut theirs).expect("aes-kw wrap");
            assert_eq!(ours, theirs, "wrap_256 disagrees with aes-kw");

            let mut recovered = [0u8; 32];
            oracle.unwrap(&ours, &mut recovered).expect("aes-kw unwrap");
            assert_eq!(recovered, *data, "aes-kw cannot unwrap our ciphertext");
            assert_eq!(aes_unwrap_256(kek, &theirs), Some(*data), "unwrap_256 rejects aes-kw ciphertext");
        }
    }
}

#[test]
fn cross_check_tampered_rejected_by_both() {
    let kek = KEKS[0];
    let oracle = KekAes128::from(kek);
    let mut wrapped = aes_wrap_128(&kek, &DATA_128[0]);
    wrapped[7] ^= 0x80;
    let mut out = [0u8; 16];
    assert!(oracle.unwrap(&wrapped, &mut out).is_err());
    assert!(aes_unwrap_128(&kek, &wrapped).is_none());
}
