//! Cross-validation of `kmac128` / `kmac256` against the RustCrypto `sha3`
//! crate.
//!
//! `sha3` exposes cSHAKE128 / cSHAKE256 but not KMAC, so the oracle assembles
//! KMAC from cSHAKE following SP 800-185 Section 4.3.1: it feeds
//! `bytepad(encode_string(K), rate) || X || right_encode(L)` to cSHAKE with
//! function name "KMAC" and customization string S. The encoding helpers used
//! by the oracle are written independently of the ones in `src/lib.rs`.

use sha3::digest::{ExtendableOutput, Update, XofReader};
use sha3::{CShake128, CShake128Core, CShake256, CShake256Core};

/// left_encode(x) per SP 800-185 Section 2.3.1.
fn left_encode(x: u64) -> Vec<u8> {
    let be = x.to_be_bytes();
    let n = be.iter().position(|&b| b != 0).map_or(7, |p| p.min(7));
    let mut v = vec![(8 - n) as u8];
    v.extend_from_slice(&be[n..]);
    v
}

/// right_encode(x) per SP 800-185 Section 2.3.1.
fn right_encode(x: u64) -> Vec<u8> {
    let be = x.to_be_bytes();
    let n = be.iter().position(|&b| b != 0).map_or(7, |p| p.min(7));
    let mut v = be[n..].to_vec();
    v.push((8 - n) as u8);
    v
}

/// bytepad(encode_string(K), w) per SP 800-185 Sections 2.3.2 and 2.3.3.
fn bytepad_encoded_key(key: &[u8], w: usize) -> Vec<u8> {
    let mut v = left_encode(w as u64);
    v.extend_from_slice(&left_encode(8 * key.len() as u64));
    v.extend_from_slice(key);
    while !v.len().is_multiple_of(w) {
        v.push(0);
    }
    v
}

/// KMAC128 via `sha3::CShake128`.
fn reference_kmac128(key: &[u8], data: &[u8], custom: &[u8], out_len: usize) -> Vec<u8> {
    let mut h = CShake128::from_core(CShake128Core::new_with_function_name(b"KMAC", custom));
    h.update(&bytepad_encoded_key(key, 168));
    h.update(data);
    h.update(&right_encode(8 * out_len as u64));
    let mut out = vec![0u8; out_len];
    h.finalize_xof().read(&mut out);
    out
}

/// KMAC256 via `sha3::CShake256`.
fn reference_kmac256(key: &[u8], data: &[u8], custom: &[u8], out_len: usize) -> Vec<u8> {
    let mut h = CShake256::from_core(CShake256Core::new_with_function_name(b"KMAC", custom));
    h.update(&bytepad_encoded_key(key, 136));
    h.update(data);
    h.update(&right_encode(8 * out_len as u64));
    let mut out = vec![0u8; out_len];
    h.finalize_xof().read(&mut out);
    out
}

/// Deterministic byte pattern of length `n`.
fn pattern(n: usize, seed: u8) -> Vec<u8> {
    (0..n).map(|i| seed.wrapping_add((i as u8).wrapping_mul(31))).collect()
}

const KEY_LENS: [usize; 4] = [4, 32, 64, 200];
const DATA_LENS: [usize; 9] = [0, 1, 4, 31, 32, 135, 136, 168, 500];
const CUSTOM: [&[u8]; 3] = [b"", b"My Tagged Application", b"customization string longer than thirty-two bytes, for a multi-byte left_encode"];
const OUT_LENS: [usize; 4] = [16, 32, 64, 200];

#[test]
fn crosscheck_kmac128() {
    for &kl in &KEY_LENS {
        let key = pattern(kl, 0x40);
        for &dl in &DATA_LENS {
            let data = pattern(dl, 0x11);
            for custom in CUSTOM {
                for &ol in &OUT_LENS {
                    let mut ours = vec![0u8; ol];
                    kmac_hax::kmac128(&key, &data, &mut ours, custom);
                    let theirs = reference_kmac128(&key, &data, custom, ol);
                    assert_eq!(
                        ours, theirs,
                        "kmac128 mismatch: key {kl} B, data {dl} B, custom {} B, out {ol} B",
                        custom.len()
                    );
                }
            }
        }
    }
}

#[test]
fn crosscheck_kmac256() {
    for &kl in &KEY_LENS {
        let key = pattern(kl, 0x40);
        for &dl in &DATA_LENS {
            let data = pattern(dl, 0x11);
            for custom in CUSTOM {
                for &ol in &OUT_LENS {
                    let mut ours = vec![0u8; ol];
                    kmac_hax::kmac256(&key, &data, &mut ours, custom);
                    let theirs = reference_kmac256(&key, &data, custom, ol);
                    assert_eq!(
                        ours, theirs,
                        "kmac256 mismatch: key {kl} B, data {dl} B, custom {} B, out {ol} B",
                        custom.len()
                    );
                }
            }
        }
    }
}

#[test]
fn crosscheck_sha3_256_and_shake256() {
    use sha3::Digest;
    for &dl in &DATA_LENS {
        let data = pattern(dl, 0x77);
        let theirs = sha3::Sha3_256::digest(&data);
        assert_eq!(kmac_hax::keccak::sha3_256(&data).to_vec(), theirs.to_vec(), "sha3-256 at {dl} B");

        let mut ours = vec![0u8; 300];
        kmac_hax::keccak::shake256(&data, &mut ours);
        let mut h = sha3::Shake256::default();
        h.update(&data);
        let mut theirs = vec![0u8; 300];
        h.finalize_xof().read(&mut theirs);
        assert_eq!(ours, theirs, "shake256 at {dl} B");
    }
}
