//! NIST CAVP DRBGVS known-answer tests for Hash_DRBG with SHA-256.
//!
//! Every vector is COUNT = 0 of a `[SHA-256]` group of `Hash_DRBG.rsp` in
//! the NIST CAVP DRBG test vector archive
//! (<https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/drbg/drbgtestvectors.zip>,
//! CAVS 14.3), copied verbatim from the `drbgvectors_no_reseed`,
//! `drbgvectors_pr_false` and `drbgvectors_pr_true` directories, read from
//! the byte-identical mirror
//! <https://github.com/coruus/nist-testvectors> (path
//! `csrc.nist.gov/groups/STM/cavp/documents/drbg/drbgtestvectors/`). All
//! groups use EntropyInputLen = 256, NonceLen = 128 and ReturnedBitsLen =
//! 1024.
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
//! The crate's functions take fixed-size buffers with an explicit length, so
//! each input is copied into a zero-padded buffer of the crate's maximum size.

use hashdrbg_hax::*;
use hex_literal::hex;

fn pad<const N: usize>(src: &[u8]) -> [u8; N] {
    let mut out = [0u8; N];
    out[..src.len()].copy_from_slice(src);
    out
}

fn instantiate(entropy: &[u8], nonce: &[u8], personalization: &[u8]) -> HashDrbgState {
    hash_drbg_instantiate(
        &pad::<SEEDLEN>(entropy), entropy.len(),
        &pad::<OUTLEN>(nonce), nonce.len(),
        &pad::<MAX_PERSONALIZATION_LEN>(personalization), personalization.len())
}

fn reseed(st: &HashDrbgState, entropy: &[u8], additional: &[u8]) -> HashDrbgState {
    hash_drbg_reseed(
        st,
        &pad::<SEEDLEN>(entropy), entropy.len(),
        &pad::<MAX_ADDITIONAL_INPUT_LEN>(additional), additional.len())
}

fn generate(st: &HashDrbgState, additional: &[u8]) -> ([u8; MAX_OUTPUT], HashDrbgState) {
    hash_drbg_generate(
        st, MAX_OUTPUT,
        &pad::<MAX_ADDITIONAL_INPUT_LEN>(additional), additional.len())
}

/// no_reseed: Instantiate, Generate, Generate.
fn run_no_reseed(
    entropy: &[u8], nonce: &[u8], personalization: &[u8],
    add0: &[u8], add1: &[u8],
) -> [u8; MAX_OUTPUT] {
    let st = instantiate(entropy, nonce, personalization);
    let (_, st) = generate(&st, add0);
    let (out, _) = generate(&st, add1);
    out
}

/// pr_false: Instantiate, Reseed, Generate, Generate.
fn run_pr_false(
    entropy: &[u8], nonce: &[u8], personalization: &[u8],
    entropy_reseed: &[u8], add_reseed: &[u8],
    add0: &[u8], add1: &[u8],
) -> [u8; MAX_OUTPUT] {
    let st = instantiate(entropy, nonce, personalization);
    let st = reseed(&st, entropy_reseed, add_reseed);
    let (_, st) = generate(&st, add0);
    let (out, _) = generate(&st, add1);
    out
}

/// pr_true: Instantiate, then twice (Reseed with the additional input, Generate).
fn run_pr_true(
    entropy: &[u8], nonce: &[u8], personalization: &[u8],
    add0: &[u8], entropy_pr0: &[u8],
    add1: &[u8], entropy_pr1: &[u8],
) -> [u8; MAX_OUTPUT] {
    let st = instantiate(entropy, nonce, personalization);
    let st = reseed(&st, entropy_pr0, add0);
    let (_, st) = generate(&st, &[]);
    let st = reseed(&st, entropy_pr1, add1);
    let (out, _) = generate(&st, &[]);
    out
}

// drbgvectors_no_reseed/Hash_DRBG.rsp
// [SHA-256] [PersonalizationStringLen = 0] [AdditionalInputLen = 0] COUNT = 0
#[test]
fn no_reseed_ps0_ai0_count0() {
    let out = run_no_reseed(
        &hex!("a65ad0f345db4e0effe875c3a2e71f42c7129d620ff5c119a9ef55f05185e0fb"),
        &hex!("8581f9317517276e06e9607ddbcbcc2e"),
        &[], &[], &[]);
    assert_eq!(out, hex!(
        "d3e160c35b99f340b2628264d1751060e0045da383ff57a57d73a673d2b8d80daaf6a6c35a91bb4579d73fd0c8fed111b0391306828adfed528f018121b3febdc343e797b87dbb63db1333ded9d1ece177cfa6b71fe8ab1da46624ed6415e51ccde2c7ca86e283990eeaeb91120415528b2295910281b02dd431f4c9f70427df"));
}

// drbgvectors_no_reseed/Hash_DRBG.rsp
// [SHA-256] [PersonalizationStringLen = 0] [AdditionalInputLen = 256] COUNT = 0
#[test]
fn no_reseed_ps0_ai256_count0() {
    let out = run_no_reseed(
        &hex!("9b6d88373841458da926cc51f83922d363f0f80f90a2f5505c04033824ef7385"),
        &hex!("82b21ff47bb5e1b33288b22f3856886b"),
        &[],
        &hex!("45d21d94ae1ea460857b50b5b240d943d42160e4c12377e0f817b79e92530bc1"),
        &hex!("ea432e31cc94c20d66fb13d1ef42a5f62b024134fc635aa1279a6179204731ca"));
    assert_eq!(out, hex!(
        "3d23d0fc03936766a1e1330393e8ff6211149f3d0758db038da1c833ca8e5265c2a9ff6c8e0836904c5fcd3e61b1c77d613dc6bdaf6437573a618e3e75e455338a7f9a41300da8fd2da408cf095ff7eae1686d60ce9c2f547d0515da91600201c8374b7af8a5f49a6381aaca394c65d451341a0ae1546cd57e0d9167a6b5397d"));
}

// drbgvectors_no_reseed/Hash_DRBG.rsp
// [SHA-256] [PersonalizationStringLen = 256] [AdditionalInputLen = 0] COUNT = 0
#[test]
fn no_reseed_ps256_ai0_count0() {
    let out = run_no_reseed(
        &hex!("dfeabab904bfe93a37bb5b1ea4a696f881ab5ab4be87ffbf2d4e8cdfaabb37fd"),
        &hex!("a2d458b475053a0346b57fc518849ba1"),
        &hex!("d15d5d9a4a3a41877b4ea98dbda5079ee393f6ab24105dbd70f5bf145772b15c"),
        &[], &[]);
    assert_eq!(out, hex!(
        "86d8c63ed4a8a19f3429b4dd57ede5ca573e861712e631400645ceee763c37cf950bdcc4d9c886ead3f0f1bf46a63bf22bd2eb39b2dac61d2e8c8f29e26045b3db56b2265adc8152d4f736c09ee90364a1e265eb5e77b0c5988c8fa52717fd33b6da760e78f2a7c27065227c47ac2134b95b7dadbf96e4ea2dad78ef200e174b"));
}

// drbgvectors_no_reseed/Hash_DRBG.rsp
// [SHA-256] [PersonalizationStringLen = 256] [AdditionalInputLen = 256] COUNT = 0
#[test]
fn no_reseed_ps256_ai256_count0() {
    let out = run_no_reseed(
        &hex!("68c43a008fe46a823d260a9d7fa388fb9e401f0197e7e758a744b4babb3f4651"),
        &hex!("eb6825777856331884aaf3751b3e4006"),
        &hex!("23ce0d32cbf2d26467f0d62acff1a3acbaa6d2746dc3ee7aa9d32c880788afc8"),
        &hex!("a31b9f13b58d4fa2f8d8ac42b62a207ff647339a146bd8b268b33d4aff57adbd"),
        &hex!("d34fc6504eca4b568193c75357b0d3821a48c77ff80d6dbd21c6cf045ff489cf"));
    assert_eq!(out, hex!(
        "abb4ecbacd4e8fa943c7221aed433861c3b203232657ec4c417d021f905d911db1058ff1e11e272232482ec96bae7cb4efc135502dbe41724077077f6de79b713670c385d04644e1281c3e582e0016255abbe5f8c06d0de57160559f0c08f7fb5be3563c649966190f8d3261364447537de2c7371c6e8c308933d27145bf90ab"));
}

// drbgvectors_pr_false/Hash_DRBG.rsp
// [SHA-256] [PersonalizationStringLen = 0] [AdditionalInputLen = 0] COUNT = 0
#[test]
fn pr_false_ps0_ai0_count0() {
    let out = run_pr_false(
        &hex!("63363377e41e86468deb0ab4a8ed683f6a134e47e014c700454e81e95358a569"),
        &hex!("808aa38f2a72a62359915a9f8a04ca68"),
        &[],
        &hex!("e62b8a8ee8f141b6980566e3bfe3c04903dad4ac2cdf9f2280010a6739bc83d3"),
        &[], &[], &[]);
    assert_eq!(out, hex!(
        "04eec63bb231df2c630a1afbe724949d005a587851e1aa795e477347c8b056621c18bddcdd8d99fc5fc2b92053d8cfacfb0bb8831205fad1ddd6c071318a6018f03b73f5ede4d4d071f9de03fd7aea105d9299b8af99aa075bdb4db9aa28c18d174b56ee2a014d098896ff2282c955a81969e069fa8ce007a180183a07dfae17"));
}

// drbgvectors_pr_false/Hash_DRBG.rsp
// [SHA-256] [PersonalizationStringLen = 0] [AdditionalInputLen = 256] COUNT = 0
#[test]
fn pr_false_ps0_ai256_count0() {
    let out = run_pr_false(
        &hex!("9cfb7ad03be487a3b42be06e9ae44f283c2b1458cec801da2ae6532fcb56cc4c"),
        &hex!("a20765538e8db31295747ec922c13a69"),
        &[],
        &hex!("96bc8014f90ebdf690db0e171b59cc46c75e2e9b8e1dc699c65c03ceb2f4d7dc"),
        &hex!("6fea0894052dab3c44d503950c7c72bd7b87de87cb81d3bb51c32a62f742286d"),
        &hex!("d3467c78563b74c13db7af36c2a964820f2a9b1b167474906508fdac9b2049a6"),
        &hex!("5840a11cc9ebf77b963854726a826370ffdb2fc2b3d8479e1df5dcfa3dddd10b"));
    assert_eq!(out, hex!(
        "71c1154a2a7a3552413970bf698aa02f14f8ea95e861f801f463be27868b1b14b1b4babd9eba5915a6414ab1104c8979b1918f3094925aeab0d07d2037e613b63cbd4f79d9f95c84b47ed9b77230a57515c211f48f4af6f5edb2c308b33905db308cf88f552c8912c49b34e66c026e67b302ca65b187928a1aba9a49edbfe190"));
}

// drbgvectors_pr_false/Hash_DRBG.rsp
// [SHA-256] [PersonalizationStringLen = 256] [AdditionalInputLen = 0] COUNT = 0
#[test]
fn pr_false_ps256_ai0_count0() {
    let out = run_pr_false(
        &hex!("b87bb4de5c148d964fc0cb612d69295671780b4270fe32bf389b6f49488efe13"),
        &hex!("27eb37a0c695c4ee3c9b70b7f6b33492"),
        &hex!("52321406ac8a9c266b1f8d811bb871269e5824b59a0234f01d358193523bbb7c"),
        &hex!("7638267f534c4e6ee22cc6ca6ed824fd5d3d387c00b89dd791eb5ac9766385b8"),
        &[], &[], &[]);
    assert_eq!(out, hex!(
        "de01c061651bab3cef2fc4ea89a56b6e86e74b2e9fd11ed671c97c813778a06a2c1f41b41e754a5257750c6bde9601da9d67d8d9564f4a8538b92516a2dacc496dee257b85393f2a01ad59aa3257f1b6da9566e3706d2d6d4a26e511b0c64d7dc223acb24827178afa43ca8d5a66f983d6929dc61564c4c14fc32d85765a23f7"));
}

// drbgvectors_pr_false/Hash_DRBG.rsp
// [SHA-256] [PersonalizationStringLen = 256] [AdditionalInputLen = 256] COUNT = 0
#[test]
fn pr_false_ps256_ai256_count0() {
    let out = run_pr_false(
        &hex!("6c623aea73bc8a59e28c6cd9c7c7ec8ca2e75190bd5dcae5978cf0c199c23f4f"),
        &hex!("e55db067a0ed537e66886b7cda02f772"),
        &hex!("1e59d798810083d1ff848e90b25c9927e3dfb55a0888b0339566a9f9ca7542dc"),
        &hex!("9ab40164744c7d00c78b4196f6f917ec33d70030a0812cd4606c5a25387568a9"),
        &hex!("4e8bead7cbba7a7bc9ae1e1617222c4139661347599950e7225d1e2faa5d57f5"),
        &hex!("dcb22a5d9f149858636f3ede2253e419816fb7b1103194451ed6a573a8fe6271"),
        &hex!("8f9d5c78cdabc32e71ac3b3c49239caddf96053250f4fd92056efbd0be487d36"));
    assert_eq!(out, hex!(
        "6e98a3b1f686f6ffa79355c9d8a5ab7f93312159d52659a2298315f10007c71adabc0b5ccb4164c0949fbdb221b43acdb62bed3099596f2d7bd5d0048173dd2360a543b234ab61a441ddb9299af84ca45c6e618fd521366dbf509d4ec06174da924361d642b107e5564ac1b32340dd2f3158bf4c00bcb4dcf12c6d67af4b74ee"));
}

// drbgvectors_pr_true/Hash_DRBG.rsp
// [SHA-256] [PersonalizationStringLen = 0] [AdditionalInputLen = 0] COUNT = 0
#[test]
fn pr_true_ps0_ai0_count0() {
    let out = run_pr_true(
        &hex!("4a4e743f877ea6e94e545a56ccb5a1f99efc7eb1e8191929152a56d41dc92425"),
        &hex!("33b7ab9356acf7da03d3d6773b61f8d9"),
        &[],
        &[],
        &hex!("2e148f9269d00a162e897a91f3aca46fed1e2adbab4f848218f288650dab8b1e"),
        &[],
        &hex!("2566475353ec8ced47d03b76fca779d0668c95136cf7866259d9e3b7e0d1f74f"));
    assert_eq!(out, hex!(
        "924b74d6ba3d56dffc0de00711e3010ccbdb730718743f0cc0631931434b0ffc4ad6d5ef96fd81f16e51a10206f674987d1b52f0cf15d294c98bc4a877f4716c0ff2c2484d3f057eafd09154874aa2a213a2641da1a3d7be6988616b6bb483cd9213ed750858ce85811b8f708dcfd607b383eda845c87f60084db7a0500643b1"));
}

// drbgvectors_pr_true/Hash_DRBG.rsp
// [SHA-256] [PersonalizationStringLen = 0] [AdditionalInputLen = 256] COUNT = 0
#[test]
fn pr_true_ps0_ai256_count0() {
    let out = run_pr_true(
        &hex!("e6cb69220ef01bb23f8879a508be049ec7e8dacb898e2ddb75cef6bcc5a84a3f"),
        &hex!("4429e3d890f2b6ef9a36f21286e9c885"),
        &[],
        &hex!("46f518eabcf170eae6ab571432269e874dff27a66f2c2f792a695b4f68678e3c"),
        &hex!("aaecb8f54221c7176e2dd941625bf84eb79e9c53c8d1a5569a33dcb4c198e627"),
        &hex!("0aabce2b5bafc3314db0605d85b80edf9561a0e2e8d4e408d53f551cea6a558b"),
        &hex!("c72ef4489b151dbd6e8214887d3ddc48043e21a4ede40fe6f1ecbcd5f5641be5"));
    assert_eq!(out, hex!(
        "8a5b386266528ee2d5e197f636748ea878508a1a0b805473f44cc60f8bddfc57387dc958ac51b3fabf077b8939d21c9424a663c5b0873c7977ca2ce447699a9e39e1ba5e51c6619127e9f18bb6abc2d1831d95bf34f4f81da6c79eda485944b4f7043e4639f6bc8855c1c017cbed40e3bca2eac4c45ebfc69f7a8189e76f51c7"));
}

// drbgvectors_pr_true/Hash_DRBG.rsp
// [SHA-256] [PersonalizationStringLen = 256] [AdditionalInputLen = 0] COUNT = 0
#[test]
fn pr_true_ps256_ai0_count0() {
    let out = run_pr_true(
        &hex!("5314e6405ceb2b26b4034502aea394850570650ab622c41090d0c15414a5a7e0"),
        &hex!("1ac01cf36c44bf789e53a0d6456d12ce"),
        &hex!("8f09e95ad10aa3c2d3f8468e70ecfa373a3461de7a5002bd837d35a607dcfc30"),
        &[],
        &hex!("7dac9bba1000dde15e3d9099e1d7824b54d8e6241be478435aad647539c72d58"),
        &[],
        &hex!("722ed3424e3b586ddea0d37b6318ecd549667086b5e63e35ff85a734c4666b31"));
    assert_eq!(out, hex!(
        "c90b12cba054c272e05686ce79b48fbab4059db8311f9b39ad7e5e4f72b586354cceeb3adec29508396aeeb66cba471f208f28f49306c9501e1fcf221b1a05ded54a64cef14b617f9fb476a370984308f62ab586b11b58b5a95aadca1de8c92c1ed9ae5894fe7ed4ccd9887d666382cbcf7535c78e5cecbb0b1b97b43f59b97d"));
}

// drbgvectors_pr_true/Hash_DRBG.rsp
// [SHA-256] [PersonalizationStringLen = 256] [AdditionalInputLen = 256] COUNT = 0
#[test]
fn pr_true_ps256_ai256_count0() {
    let out = run_pr_true(
        &hex!("29e1a42709b7e84dbe50788fbad8cb609c127eec3262636a513fd9059fb8bae4"),
        &hex!("f3a521f28dffbd97574c405b69b636ad"),
        &hex!("c99a1147d8db401f4fcf763867296758e26404a30a4a9fa496a717f21f5d749b"),
        &hex!("17254ea392aead0dc94992d867813497d3fd6dc7669667150afe6c28a2b89946"),
        &hex!("d5266c01e10d72dd7e8a3bf717cccb8f643ca233314e3e74f106f46b090e5c73"),
        &hex!("157dde59ceb2c662c8665fbe623ec75873fd0c5ccce79a9f5b7098ec8ed77b67"),
        &hex!("c7e5f03d26bdf9553338e64ba64ce5b5751b04f9c69992221495f2227b9799d0"));
    assert_eq!(out, hex!(
        "e304de9ffd885cf917ead78f05939b8cf54709fc2d0c799a98b543486337204477b1060bceae2a22f7ff42b6cb4b4bc0610ae2b67558a7c54b65e45bb9f1a86981b74705b48cdbf7d8decf87868267bd948e9394aa4357f8dbbf30612a0eb5b131884c220e442d36778e8d74091d8a27c070fe690469e07f3aabeef7c629bfab"));
}
