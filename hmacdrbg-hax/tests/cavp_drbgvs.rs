//! NIST CAVP DRBGVS known-answer tests for HMAC_DRBG with SHA-256.
//!
//! Every vector is COUNT = 0 of a `[SHA-256]` group of `HMAC_DRBG.rsp` in
//! the NIST CAVP DRBG test vector archive
//! (<https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/drbg/drbgtestvectors.zip>,
//! CAVS 14.3), copied verbatim from the `drbgvectors_no_reseed`,
//! `drbgvectors_pr_false` and `drbgvectors_pr_true` directories. All groups
//! use EntropyInputLen = 256, NonceLen = 128 and ReturnedBitsLen = 1024.
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

use hex_literal::hex;
use hmacdrbg_hax::*;

/// no_reseed: Instantiate, Generate, Generate.
fn run_no_reseed(
    entropy: &[u8], nonce: &[u8], personalization: &[u8],
    add0: &[u8], add1: &[u8],
) -> [u8; MAX_OUTPUT] {
    let st = hmac_drbg_instantiate(
        entropy, entropy.len(), nonce, nonce.len(), personalization, personalization.len());
    let (st, _) = hmac_drbg_generate(&st, MAX_OUTPUT, add0, add0.len());
    let (_, out) = hmac_drbg_generate(&st, MAX_OUTPUT, add1, add1.len());
    out
}

/// pr_false: Instantiate, Reseed, Generate, Generate.
fn run_pr_false(
    entropy: &[u8], nonce: &[u8], personalization: &[u8],
    entropy_reseed: &[u8], add_reseed: &[u8],
    add0: &[u8], add1: &[u8],
) -> [u8; MAX_OUTPUT] {
    let st = hmac_drbg_instantiate(
        entropy, entropy.len(), nonce, nonce.len(), personalization, personalization.len());
    let st = hmac_drbg_reseed(&st, entropy_reseed, entropy_reseed.len(), add_reseed, add_reseed.len());
    let (st, _) = hmac_drbg_generate(&st, MAX_OUTPUT, add0, add0.len());
    let (_, out) = hmac_drbg_generate(&st, MAX_OUTPUT, add1, add1.len());
    out
}

/// pr_true: Instantiate, then twice (Reseed with the additional input, Generate).
fn run_pr_true(
    entropy: &[u8], nonce: &[u8], personalization: &[u8],
    add0: &[u8], entropy_pr0: &[u8],
    add1: &[u8], entropy_pr1: &[u8],
) -> [u8; MAX_OUTPUT] {
    let st = hmac_drbg_instantiate(
        entropy, entropy.len(), nonce, nonce.len(), personalization, personalization.len());
    let st = hmac_drbg_reseed(&st, entropy_pr0, entropy_pr0.len(), add0, add0.len());
    let (st, _) = hmac_drbg_generate(&st, MAX_OUTPUT, &[], 0);
    let st = hmac_drbg_reseed(&st, entropy_pr1, entropy_pr1.len(), add1, add1.len());
    let (_, out) = hmac_drbg_generate(&st, MAX_OUTPUT, &[], 0);
    out
}

// drbgvectors_no_reseed/HMAC_DRBG.rsp
// [SHA-256] [PersonalizationStringLen = 0] [AdditionalInputLen = 0] COUNT = 0
#[test]
fn no_reseed_ps0_ai0_count0() {
    let out = run_no_reseed(
        &hex!("ca851911349384bffe89de1cbdc46e6831e44d34a4fb935ee285dd14b71a7488"),
        &hex!("659ba96c601dc69fc902940805ec0ca8"),
        &[], &[], &[]);
    assert_eq!(out, hex!(
        "e528e9abf2dece54d47c7e75e5fe302149f817ea9fb4bee6f4199697d04d5b89d54fbb978a15b5c443c9ec21036d2460b6f73ebad0dc2aba6e624abf07745bc107694bb7547bb0995f70de25d6b29e2d3011bb19d27676c07162c8b5ccde0668961df86803482cb37ed6d5c0bb8d50cf1f50d476aa0458bdaba806f48be9dcb8"));
}

// drbgvectors_no_reseed/HMAC_DRBG.rsp
// [SHA-256] [PersonalizationStringLen = 0] [AdditionalInputLen = 256] COUNT = 0
#[test]
fn no_reseed_ps0_ai256_count0() {
    let out = run_no_reseed(
        &hex!("d3cc4d1acf3dde0c4bd2290d262337042dc632948223d3a2eaab87da44295fbd"),
        &hex!("0109b0e729f457328aa18569a9224921"),
        &[],
        &hex!("3c311848183c9a212a26f27f8c6647e40375e466a0857cc39c4e47575d53f1f6"),
        &hex!("fcb9abd19ccfbccef88c9c39bfb3dd7b1c12266c9808992e305bc3cff566e4e4"));
    assert_eq!(out, hex!(
        "9c7b758b212cd0fcecd5daa489821712e3cdea4467b560ef5ddc24ab47749a1f1ffdbbb118f4e62fcfca3371b8fbfc5b0646b83e06bfbbab5fac30ea09ea2bc76f1ea568c9be0444b2cc90517b20ca825f2d0eccd88e7175538b85d90ab390183ca6395535d34473af6b5a5b88f5a59ee7561573337ea819da0dcc3573a22974"));
}

// drbgvectors_no_reseed/HMAC_DRBG.rsp
// [SHA-256] [PersonalizationStringLen = 256] [AdditionalInputLen = 256] COUNT = 0
#[test]
fn no_reseed_ps256_ai256_count0() {
    let out = run_no_reseed(
        &hex!("5d3286bc53a258a53ba781e2c4dcd79a790e43bbe0e89fb3eed39086be34174b"),
        &hex!("c5422294b7318952ace7055ab7570abf"),
        &hex!("2dba094d008e150d51c4135bb2f03dcde9cbf3468a12908a1b025c120c985b9d"),
        &hex!("793a7ef8f6f0482beac542bb785c10f8b7b406a4de92667ab168ecc2cf7573c6"),
        &hex!("2238cdb4e23d629fe0c2a83dd8d5144ce1a6229ef41dabe2a99ff722e510b530"));
    assert_eq!(out, hex!(
        "d04678198ae7e1aeb435b45291458ffde0891560748b43330eaf866b5a6385e74c6fa5a5a44bdb284d436e98d244018d6acedcdfa2e9f499d8089e4db86ae89a6ab2d19cb705e2f048f97fb597f04106a1fa6a1416ad3d859118e079a0c319eb95686f4cbcce3b5101c7a0b010ef029c4ef6d06cdfac97efb9773891688c37cf"));
}

// drbgvectors_pr_false/HMAC_DRBG.rsp
// [SHA-256] [PersonalizationStringLen = 0] [AdditionalInputLen = 0] COUNT = 0
#[test]
fn pr_false_ps0_ai0_count0() {
    let out = run_pr_false(
        &hex!("06032cd5eed33f39265f49ecb142c511da9aff2af71203bffaf34a9ca5bd9c0d"),
        &hex!("0e66f71edc43e42a45ad3c6fc6cdc4df"),
        &[],
        &hex!("01920a4e669ed3a85ae8a33b35a74ad7fb2a6bb4cf395ce00334a9c9a5a5d552"),
        &[], &[], &[]);
    assert_eq!(out, hex!(
        "76fc79fe9b50beccc991a11b5635783a83536add03c157fb30645e611c2898bb2b1bc215000209208cd506cb28da2a51bdb03826aaf2bd2335d576d519160842e7158ad0949d1a9ec3e66ea1b1a064b005de914eac2e9d4f2d72a8616a80225422918250ff66a41bd2f864a6a38cc5b6499dc43f7f2bd09e1e0f8f5885935124"));
}

// drbgvectors_pr_false/HMAC_DRBG.rsp
// [SHA-256] [PersonalizationStringLen = 0] [AdditionalInputLen = 256] COUNT = 0
#[test]
fn pr_false_ps0_ai256_count0() {
    let out = run_pr_false(
        &hex!("05ac9fc4c62a02e3f90840da5616218c6de5743d66b8e0fbf833759c5928b53d"),
        &hex!("2b89a17904922ed8f017a63044848545"),
        &[],
        &hex!("2791126b8b52ee1fd9392a0a13e0083bed4186dc649b739607ac70ec8dcecf9b"),
        &hex!("43bac13bae715092cf7eb280a2e10a962faf7233c41412f69bc74a35a584e54c"),
        &hex!("3f2fed4b68d506ecefa21f3f5bb907beb0f17dbc30f6ffbba5e5861408c53a1e"),
        &hex!("529030df50f410985fde068df82b935ec23d839cb4b269414c0ede6cffea5b68"));
    assert_eq!(out, hex!(
        "02ddff5173da2fcffa10215b030d660d61179e61ecc22609b1151a75f1cbcbb4363c3a89299b4b63aca5e581e73c860491010aa35de3337cc6c09ebec8c91a6287586f3a74d9694b462d2720ea2e11bbd02af33adefb4a16e6b370fa0effd57d607547bdcfbb7831f54de7073ad2a7da987a0016a82fa958779a168674b56524"));
}

// drbgvectors_pr_false/HMAC_DRBG.rsp
// [SHA-256] [PersonalizationStringLen = 256] [AdditionalInputLen = 256] COUNT = 0
#[test]
fn pr_false_ps256_ai256_count0() {
    let out = run_pr_false(
        &hex!("cdb0d9117cc6dbc9ef9dcb06a97579841d72dc18b2d46a1cb61e314012bdf416"),
        &hex!("d0c0d01d156016d0eb6b7e9c7c3c8da8"),
        &hex!("6f0fb9eab3f9ea7ab0a719bfa879bf0aaed683307fda0c6d73ce018b6e34faaa"),
        &hex!("8ec6f7d5a8e2e88f43986f70b86e050d07c84b931bcf18e601c5a3eee3064c82"),
        &hex!("1ab4ca9014fa98a55938316de8ba5a68c629b0741bdd058c4d70c91cda5099b3"),
        &hex!("16e2d0721b58d839a122852abd3bf2c942a31c84d82fca74211871880d7162ff"),
        &hex!("53686f042a7b087d5d2eca0d2a96de131f275ed7151189f7ca52deaa78b79fb2"));
    assert_eq!(out, hex!(
        "dda04a2ca7b8147af1548f5d086591ca4fd951a345ce52b3cd49d47e84aa31a183e31fbc42a1ff1d95afec7143c8008c97bc2a9c091df0a763848391f68cb4a366ad89857ac725a53b303ddea767be8dc5f605b1b95f6d24c9f06be65a973a089320b3cc42569dcfd4b92b62a993785b0301b3fc452445656fce22664827b88f"));
}

// drbgvectors_pr_true/HMAC_DRBG.rsp
// [SHA-256] [PersonalizationStringLen = 0] [AdditionalInputLen = 0] COUNT = 0
#[test]
fn pr_true_ps0_ai0_count0() {
    let out = run_pr_true(
        &hex!("9969e54b4703ff31785b879a7e5c0eae0d3e309559e9fe96b0676d49d591ea4d"),
        &hex!("07d20d46d064757d3023cac2376127ab"),
        &[],
        &[],
        &hex!("c60f2999100f738c10f74792676a3fc4a262d13721798046e29a295181569f54"),
        &[],
        &hex!("c11d4524c9071bd3096015fcf7bc24a607f22fa065c937658a2a77a8699089f4"));
    assert_eq!(out, hex!(
        "abc015856094803a938dffd20da94843870ef935b82cfec17706b8f551b8385044235dd44b599f94b39be78dd476e0cf11309c995a7334e0a78b37bc9586235086fa3b637ba91cf8fb65efa22a589c137531aa7b2d4e2607aac27292b01c698e6e01ae679eb87c01a89c7422d4372d6d754ababb4bf896fcb1cd09d692d0283f"));
}

// drbgvectors_pr_true/HMAC_DRBG.rsp
// [SHA-256] [PersonalizationStringLen = 0] [AdditionalInputLen = 256] COUNT = 0
#[test]
fn pr_true_ps0_ai256_count0() {
    let out = run_pr_true(
        &hex!("2cad88b2b6a06e703de46185ccb2ddcf5e0ee030995ebdf95cc4fbc38441f17f"),
        &hex!("32310770e04172c0cf91f6590cce44a4"),
        &[],
        &hex!("ef6da5e6530e0d621749ab192e06327e995c3ac0c3963ab8c8cd2df2839ab5df"),
        &hex!("448bfbc5ce9e3b9da3e9642daecd994dfe373e75253e8eb585141224eca7ad7b"),
        &hex!("44278b31ed853f0a510bd14650ac4b4971d8b426799a43511d016be68dedbb8d"),
        &hex!("afb57f69799c0b892b3015990e133698d543aa87829ace868e4a5e9525d62357"));
    assert_eq!(out, hex!(
        "4c7dfbe509dc5a3ac26998723c6a44cad20b197fc86117c778d1568ab828923862885e97198f77a1cb45113f5d78726a0f120aec94afc45f57c8dcc1cb092b343480012858ef5bc559f57023442209326ec4a54d91ca3a77dfdf9e75f117cef50e6fd2dc9af6ddce8e6515b4a97357a97b6cd274f68a042fa41bbd7b7261b034"));
}

// drbgvectors_pr_true/HMAC_DRBG.rsp
// [SHA-256] [PersonalizationStringLen = 256] [AdditionalInputLen = 256] COUNT = 0
#[test]
fn pr_true_ps256_ai256_count0() {
    let out = run_pr_true(
        &hex!("4294671d493dc085b5184607d7de2ff2b6aceb734a1b026f6cfee7c5a90f03da"),
        &hex!("d071544e599235d5eb38b64b551d2a6e"),
        &hex!("63bc769ae1d95a98bde870e4db7776297041d37c8a5c688d4e024b78d83f4d78"),
        &hex!("28848becd3f47696f124f4b14853a456156f69be583a7d4682cff8d44b39e1d3"),
        &hex!("db9b4790b62336fbb9a684b82947065393eeef8f57bd2477141ad17e776dac34"),
        &hex!("8bfce0b7132661c3cd78175d83926f643e36f7608eec2c5dac3ddcbacc8c2182"),
        &hex!("4a9abe80f6f522f29878bedf8245b27940a76471006fb4a4110beb4decb6c341"));
    assert_eq!(out, hex!(
        "e580dc969194b2b18a97478aef9d1a72390aff14562747bf080d741527a6655ce7fc135325b457483a9f9c70f91165a811cf4524b50d51199a0df3bd60d12abac27d0bf6618e6b114e05420352e23f3603dfe8a225dc19b3d1fff1dc245dc6b1df24c741744bec3f9437dbbf222df84881a457a589e7815ef132f686b760f012"));
}
