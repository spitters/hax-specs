//! NIST CAVP DRBGVS known-answer tests for CTR_DRBG with AES-128, no
//! derivation function.
//!
//! Every vector is COUNT = 0 of an `[AES-128 no df]` group of `CTR_DRBG.rsp`
//! in the NIST CAVP DRBG test vector archive
//! (<https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/drbg/drbgtestvectors.zip>,
//! CAVS 14.3), directories `drbgvectors_no_reseed`, `drbgvectors_pr_false`
//! and `drbgvectors_pr_true`. The files were read byte-for-byte from the
//! mirror <https://github.com/coruus/nist-testvectors> (path
//! `csrc.nist.gov/groups/STM/cavp/documents/drbg/drbgtestvectors/`), and the
//! `no_reseed` 0/0 vector agrees with the copy of that vector in
//! `tests/kat_vectors.rs`. Each file holds four `[AES-128 no df]` groups per
//! (PersonalizationStringLen, AdditionalInputLen) pair; the vectors below are
//! from the first group of each pair. All groups use EntropyInputLen = 256,
//! NonceLen = 0 and ReturnedBitsLen = 512, which match this crate's fixed
//! 32-byte seed material and 4-block output.
//!
//! The DRBGVS call sequence (SP 800-90A Rev. 1, Section 9) is:
//!
//! - no_reseed: Instantiate; Generate(AdditionalInput[0]) discarded;
//!   Generate(AdditionalInput[1]) compared with ReturnedBits.
//! - pr_false: Instantiate; Reseed(EntropyInputReseed, AdditionalInputReseed);
//!   Generate(AdditionalInput[0]) discarded; Generate(AdditionalInput[1])
//!   compared with ReturnedBits.
//! - pr_true: Instantiate; for each of the two Generate calls, Reseed
//!   (EntropyInputPR, AdditionalInput) followed by Generate with empty
//!   additional input (SP 800-90A Rev. 1, Section 9.3.1, step 7); the second
//!   output is compared with ReturnedBits.
//!
//! An empty PersonalizationString or AdditionalInput is the all-zero
//! 32-byte array, which is how SP 800-90A Rev. 1, Section 10.2.1.3.1 pads
//! inputs shorter than seedlen when no derivation function is used.

// The hax-extractable loop form indexes arrays with a bounded `for i in 0..N`.
#![allow(clippy::needless_range_loop, clippy::manual_memcpy)]

use ctrdrbg_hax::*;

/// Decode a hex string into `N` bytes; the empty string decodes to zeros.
fn hex<const N: usize>(s: &str) -> [u8; N] {
    let mut out = [0u8; N];
    let b = s.as_bytes();
    assert!(b.len() == 2 * N || b.is_empty(), "hex length {}", b.len());
    for i in 0..b.len() / 2 {
        let nibble = |c: u8| (c as char).to_digit(16).expect("hex digit") as u8;
        out[i] = (nibble(b[2 * i]) << 4) | nibble(b[2 * i + 1]);
    }
    out
}

/// Concatenate the first four output blocks of a Generate call.
fn returned_bits(out: &[[u8; 16]; MAX_GEN_BLOCKS]) -> [u8; 64] {
    let mut r = [0u8; 64];
    for block in 0..4 {
        for i in 0..16 {
            r[block * 16 + i] = out[block][i];
        }
    }
    r
}

/// no_reseed: Instantiate, Generate, Generate.
fn run_no_reseed(entropy: &str, perso: &str, add0: &str, add1: &str) -> [u8; 64] {
    let st = ctr_drbg_instantiate(hex(entropy), hex(perso));
    let (st, _) = ctr_drbg_generate(st, 4, hex(add0));
    let (_, out) = ctr_drbg_generate(st, 4, hex(add1));
    returned_bits(&out)
}

/// pr_false: Instantiate, Reseed, Generate, Generate.
fn run_pr_false(
    entropy: &str, perso: &str, entropy_reseed: &str, add_reseed: &str, add0: &str, add1: &str,
) -> [u8; 64] {
    let st = ctr_drbg_instantiate(hex(entropy), hex(perso));
    let st = ctr_drbg_reseed(st, hex(entropy_reseed), hex(add_reseed));
    let (st, _) = ctr_drbg_generate(st, 4, hex(add0));
    let (_, out) = ctr_drbg_generate(st, 4, hex(add1));
    returned_bits(&out)
}

/// pr_true: Instantiate, (Reseed, Generate) twice.
fn run_pr_true(
    entropy: &str, perso: &str, add0: &str, pr0: &str, add1: &str, pr1: &str,
) -> [u8; 64] {
    let st = ctr_drbg_instantiate(hex(entropy), hex(perso));
    let st = ctr_drbg_reseed(st, hex(pr0), hex(add0));
    let (st, _) = ctr_drbg_generate(st, 4, hex(""));
    let st = ctr_drbg_reseed(st, hex(pr1), hex(add1));
    let (_, out) = ctr_drbg_generate(st, 4, hex(""));
    returned_bits(&out)
}

// ---------------------------------------------------------------------------
// drbgvectors_no_reseed/CTR_DRBG.rsp
// ---------------------------------------------------------------------------

#[test]
fn cavp_no_reseed_perso0_add0() {
    let got = run_no_reseed(
        "ce50f33da5d4c1d3d4004eb35244b7f2cd7f2e5076fbf6780a7ff634b249a5fc",
        "",
        "",
        "",
    );
    assert_eq!(got, hex::<64>("6545c0529d372443b392ceb3ae3a99a30f963eaf313280f1d1a1e87f9db373d361e75d18018266499cccd64d9bbb8de0185f213383080faddec46bae1f784e5a"));
}

#[test]
fn cavp_no_reseed_perso0_add256() {
    let got = run_no_reseed(
        "6bd4f2ae649fc99350951ff0c5d460c1a9214154e7384975ee54b34b7cae0704",
        "",
        "ecd4893b979ac92db1894ae3724518a2f78cf2dbe2f6bbc6fda596df87c7a4ae",
        "b23e9188687c88768b26738862c4791fa52f92502e1f94bf66af017c4228a0dc",
    );
    assert_eq!(got, hex::<64>("5b2bf7a5c60d8ab6591110cbd61cd387b02de19784f496d1a109123d8b3562a5de2dd6d5d1aef957a6c4f371cecd93c15799d82e34d6a0dba7e915a27d8e65f3"));
}

#[test]
fn cavp_no_reseed_perso256_add0() {
    let got = run_no_reseed(
        "cee23de86a69c7ef57f6e1e12bd16e35e51624226fa19597bf93ec476a44b0f2",
        "a2ef16f226ea324f23abd59d5e3c660561c25e73638fe21c87566e86a9e04c3e",
        "",
        "",
    );
    assert_eq!(got, hex::<64>("2a76d71b329f449c98dc08fff1d205a2fbd9e4ade120c7611c225c984eac8531288dd3049f3dc3bb3671501ab8fbf9ad49c86cce307653bd8caf29cb0cf07764"));
}

#[test]
fn cavp_no_reseed_perso256_add256() {
    let got = run_no_reseed(
        "50b96542a1f2b8b05074051fe8fb0e45adbbd5560e3594e12d485fe1bfcb741f",
        "820c3030f97b3ead81a93b88b871937278fd3d711d2085d9280cba394673b17e",
        "1f1632058806d6d8e231288f3b15a3c324e90ccef4891bd595f09c3e80e27469",
        "5cadc8bfd86d2a5d44f921f64c7d153001b9bdd7caa6618639b948ebfad5cb8a",
    );
    assert_eq!(got, hex::<64>("02b76a66f103e98d450e25e09c35337747d987471d2b3d81e03be24c7e985417a32acd72bc0a6eddd9871410dacb921c659249b4e2b368c4ac8580fb5db559bc"));
}

// ---------------------------------------------------------------------------
// drbgvectors_pr_false/CTR_DRBG.rsp
// ---------------------------------------------------------------------------

#[test]
fn cavp_pr_false_perso0_add0() {
    let got = run_pr_false(
        "ed1e7f21ef66ea5d8e2a85b9337245445b71d6393a4eecb0e63c193d0f72f9a9",
        "",
        "303fb519f0a4e17d6df0b6426aa0ecb2a36079bd48be47ad2a8dbfe48da3efad",
        "",
        "",
        "",
    );
    assert_eq!(got, hex::<64>("f80111d08e874672f32f42997133a5210f7a9375e22cea70587f9cfafebe0f6a6aa2eb68e7dd9164536d53fa020fcab20f54caddfab7d6d91e5ffec1dfd8deaa"));
}

#[test]
fn cavp_pr_false_perso0_add256() {
    let got = run_pr_false(
        "6bc709aa4c975b0eccb922ce2110fa9b572403f9013dfd10f06a88d54d380002",
        "",
        "cf1af84eddd5bef666ea42bea6067a23e52742e24661f944ba2514fe052abf31",
        "a46988bad49b78c613c94e06a53b080bf6d20b7385bf4c782ad7cd145ddc9053",
        "139d6f72bf1d0ec5bfdd245e013f5cdac85e3eca716196018b92133c00a07436",
        "240f1a5af7fc2e4d32ace635acba5947f3564ecbfd7516c479c0adda20747f26",
    );
    assert_eq!(got, hex::<64>("e727268a546c0c891cf53a70a92820ee9bbf728ad52f30625b2e28f0f6c906f60ffd02f7d81623295950c04b63a48634eb41a5b4d649bdabff335ac3200690b0"));
}

#[test]
fn cavp_pr_false_perso256_add0() {
    let got = run_pr_false(
        "34cbc2b217f3d907fa2ad6a0d7a813b0fda1e17fbeed94b0e0a0abfbec947146",
        "e8fa4c5de825791e68180f2ba107e829c48299cb01be939cd0be76da120a91f2",
        "8326f8e9cfbd02eb076bbb9819d96a02386f80bf913c8e4a80361d82cafad52e",
        "",
        "",
        "",
    );
    assert_eq!(got, hex::<64>("52f5e718bf48d99e498775c00378e545799bb2059aef0b74be573d8283f02b5293917913bc8f26fc23760a1c86c3f5c844857419868eafeb17c9248227d026b8"));
}

#[test]
fn cavp_pr_false_perso256_add256() {
    let got = run_pr_false(
        "289e5c8283cbd7dbe707255cb3cf2907d8a5ce5b347314966f9b2bebb1a1e200",
        "7f7b59f23510b976fe155d047525c94e2dacb30d77ac8b09281544dd815d5293",
        "98c522028f36fc6b85a8f3c003efd4b130dd90180ec81cf7c67d4c53d10f0022",
        "f7a0378328d939f0f8521e39409d7175d87319c7597a9050414f7adc392a328d",
        "19c286f5b36194d1cc62c0188140bc9d61d2a9c5d88bb5aebc224bfb04dfca83",
        "820650c3201d347f5b20d3d25d1c8c7bef4d9f66a5a04c7dd9d669e95182a0c4",
    );
    assert_eq!(got, hex::<64>("79a79d44edada58e3fc12a4e36ae900eeace290265f01262f40f2958a70dcbd4d4185f708c088ede7ff8c8375f44f4012f2512d38328a5df171a17029d90f185"));
}

// ---------------------------------------------------------------------------
// drbgvectors_pr_true/CTR_DRBG.rsp
// ---------------------------------------------------------------------------

#[test]
fn cavp_pr_true_perso0_add0() {
    let got = run_pr_true(
        "f1893be2bc86c80d6422f3d586c0a8ce9bad6486f23123f02ba01403384b83fe",
        "",
        "",
        "79dde8e1502818df744e1afe8e5ecb3b8d19365182c7957260d1794e54912620",
        "",
        "cf684fd0eebba77901efcbe3cc5297ba9f04367fd54fe6af9463ad2ebcfedbf4",
    );
    assert_eq!(got, hex::<64>("fdb97f0eb27279b8d885f2462e8968dc4c9266f81167359d89df4c327642eae1b3131f90d64c1b5a0e71950284fc3fd026201094e8ab3f3760184d7184c90a34"));
}

#[test]
fn cavp_pr_true_perso0_add256() {
    let got = run_pr_true(
        "4d85ec7a58763c383548e70758c6db91f99b1466baa7d4f20ba1f8a44ec4d1f3",
        "",
        "dd4f1c82473fe4cc56128152001547ff7234eadea5e94f0d64b0c08d24788570",
        "3a9e8e7aebfed99f34b16294c1da973bd706afba105d78cb132e4d3aee221cc1",
        "e90046b7fcd9d86434c312b959795fbfbe666dda2b16a7b14cb0cc1d84895273",
        "e37f193e5f1356368aec70a0de2c330c3cf9af26c6aee46b9f114f6276ed38b4",
    );
    assert_eq!(got, hex::<64>("173a535a1ce52e3ca2b68fb2c24880a4dc2837174ce3df1c1f445f43013384a0570ec8d5197b2d00fef3cb3556086bd82fb6075562f3adae4dca39008bcd7397"));
}

#[test]
fn cavp_pr_true_perso256_add0() {
    let got = run_pr_true(
        "528ccd2d6c143800a34ad33e7f153cfaceaa2411abbaf4bfcfe9796898d0ece6",
        "07ca7a007b53f014d7f10461d6c97b5c8b0c502d3461d583f99efec69f121cd2",
        "",
        "478fd1eaa7ed293294d370979b0f0f1948d5a3161b12eeebf2cf6bd1bf059adf",
        "",
        "036bf1173977b323f60c6f0f603d9c50835b2afca8347dfb24e8f66604444951",
    );
    assert_eq!(got, hex::<64>("bba1ef50b4bad288897f02ac2706ee1e01488dcbe9b3d8a637921f5e788faed3b23db63d590ceaa7607a2179192bea9aeaa85d048e7e108fee666dc646af5f0e"));
}

#[test]
fn cavp_pr_true_perso256_add256() {
    let got = run_pr_true(
        "f623911bb7efe5f6c4e969799724b317d6aa2107a356ab6a05143eee99e675b3",
        "19733edbc20bedc0bc269c4837a1a471377cfeb6cd60039e4944b31af73bc4c0",
        "0591feffa77de223d6fb1a91579f766c4c09f3e9540d14fd2ee98894f7a80053",
        "60a809d63f6d5efeb4335b819e1d0a06b7be668765ca72f5404992a0e90b7a70",
        "c5f7b282a516a2f831d668ca4448662c92907cbbfa9b90c3745ea2e79b28ec6d",
        "530e7a6dfa6339aaa6661bc4fb13ff1f351c79e9d3415e2d0d570b8f9907c8b4",
    );
    assert_eq!(got, hex::<64>("e108b1bd65928d8097190c106321e9fcb3b930ef3b74421ed8e70802d3f06ebe7338948cbf08ab91cdf71dd398ddc4752b6d3dbc265fe836588783fbddd509fb"));
}
