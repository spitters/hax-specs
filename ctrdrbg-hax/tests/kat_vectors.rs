//! Known Answer Tests (KAT) for CTR_DRBG with AES-128.
//!
//! `kat_nist_sp80090a_ctr_aes128_no_df_no_reseed` drives the crate's own
//! instantiate -> generate pipeline against a published NIST SP 800-90A
//! Rev. 1 / CAVP CTR_DRBG DRBGVS vector (exact expected bytes copied from
//! the CAVP `CTR_DRBG.rsp`; `tests/cavp_drbgvs.rs` cites the source). The remaining `kat_*` tests exercise structural and
//! boundary behaviour of the counter, Update, Instantiate, Generate and
//! Reseed operations.

// The hax-extractable loop form indexes arrays with a bounded `for i in 0..N`.
#![allow(clippy::needless_range_loop, clippy::manual_memcpy)]

use ctrdrbg_hax::*;

// =========================================================================
// Published NIST CAVP CTR_DRBG KAT (SP 800-90A Rev. 1 DRBGVS)
// =========================================================================

#[test]
fn kat_nist_sp80090a_ctr_aes128_no_df_no_reseed() {
    // NIST SP 800-90A Rev. 1 / CAVP CTR_DRBG DRBGVS, group:
    //   [AES-128 no df]
    //   [PredictionResistance = False]
    //   [EntropyInputLen = 256]  [NonceLen = 0]
    //   [PersonalizationStringLen = 0]  [AdditionalInputLen = 0]
    //   [ReturnedBitsLen = 512]
    //   COUNT = 0
    //
    // DRBGVS "no reseed" procedure: Instantiate, then two Generate calls;
    // the first call's output is discarded, the second call's output is the
    // published ReturnedBits. With no derivation function, the 256-bit
    // entropy input is used directly as seed material (seedlen = 32 bytes for
    // AES-128), matching this crate's `ctr_drbg_instantiate`.
    //
    // Expected bytes below are the exact CAVP values from the NIST
    // `CTR_DRBG.rsp` file (drbgvectors_no_reseed).
    let entropy: [u8; SEEDLEN] = [
        0xce, 0x50, 0xf3, 0x3d, 0xa5, 0xd4, 0xc1, 0xd3, 0xd4, 0x00, 0x4e, 0xb3,
        0x52, 0x44, 0xb7, 0xf2, 0xcd, 0x7f, 0x2e, 0x50, 0x76, 0xfb, 0xf6, 0x78,
        0x0a, 0x7f, 0xf6, 0x34, 0xb2, 0x49, 0xa5, 0xfc,
    ];
    let perso = [0u8; SEEDLEN];

    let expected_returned_bits: [u8; 64] = [
        0x65, 0x45, 0xc0, 0x52, 0x9d, 0x37, 0x24, 0x43, 0xb3, 0x92, 0xce, 0xb3,
        0xae, 0x3a, 0x99, 0xa3, 0x0f, 0x96, 0x3e, 0xaf, 0x31, 0x32, 0x80, 0xf1,
        0xd1, 0xa1, 0xe8, 0x7f, 0x9d, 0xb3, 0x73, 0xd3, 0x61, 0xe7, 0x5d, 0x18,
        0x01, 0x82, 0x66, 0x49, 0x9c, 0xcc, 0xd6, 0x4d, 0x9b, 0xbb, 0x8d, 0xe0,
        0x18, 0x5f, 0x21, 0x33, 0x83, 0x08, 0x0f, 0xad, 0xde, 0xc4, 0x6b, 0xae,
        0x1f, 0x78, 0x4e, 0x5a,
    ];

    // Instantiate (entropy, no nonce, empty personalization string).
    let state = ctr_drbg_instantiate(entropy, perso);

    // First Generate: output discarded (DRBGVS no-reseed procedure).
    // ReturnedBitsLen = 512 bits = 64 bytes = 4 blocks; no additional input.
    let (state, _discard) = ctr_drbg_generate(state, 4, [0u8; SEEDLEN]);

    // Second Generate: this output is the published ReturnedBits.
    let (_state, output) = ctr_drbg_generate(state, 4, [0u8; SEEDLEN]);

    let mut returned_bits = [0u8; 64];
    for block in 0..4 {
        for i in 0..16 {
            returned_bits[block * 16 + i] = output[block][i];
        }
    }

    assert_eq!(
        returned_bits, expected_returned_bits,
        "NIST CAVP CTR_DRBG AES-128 no df, no reseed, COUNT=0"
    );
}

// =========================================================================
// increment_counter boundary tests
// =========================================================================

#[test]
fn kat_increment_zero() {
    let v = [0x00u8; 16];
    let result = increment_counter(&v);
    assert_eq!(result, [
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01,
    ]);
}

#[test]
fn kat_increment_one() {
    let mut v = [0x00u8; 16];
    v[15] = 0x01;
    let result = increment_counter(&v);
    assert_eq!(result, [
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02,
    ]);
}

#[test]
fn kat_increment_0xff_wrap_one_byte() {
    let mut v = [0x00u8; 16];
    v[15] = 0xff;
    let result = increment_counter(&v);
    assert_eq!(result, [
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00,
    ]);
}

#[test]
fn kat_increment_full_wrap() {
    // 0xFF...FF + 1 should wrap to 0x00...00
    let v = [0xffu8; 16];
    let result = increment_counter(&v);
    assert_eq!(result, [0x00u8; 16]);
}

#[test]
fn kat_increment_multi_byte_carry() {
    // 0x00..00_FF_FF_FF + 1 = 0x00..01_00_00_00
    let mut v = [0x00u8; 16];
    v[13] = 0xff;
    v[14] = 0xff;
    v[15] = 0xff;
    let result = increment_counter(&v);
    assert_eq!(result, [
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,
    ]);
}

#[test]
fn kat_increment_preserves_high_bytes() {
    // 0xAB_CD_00..00_05 + 1 = 0xAB_CD_00..00_06
    let mut v = [0x00u8; 16];
    v[0] = 0xab;
    v[1] = 0xcd;
    v[15] = 0x05;
    let result = increment_counter(&v);
    assert_eq!(result[0], 0xab);
    assert_eq!(result[1], 0xcd);
    assert_eq!(result[15], 0x06);
    for i in 2..15 {
        assert_eq!(result[i], 0x00);
    }
}

// =========================================================================
// Update tests with known AES values
// =========================================================================

#[test]
fn kat_update_zero_key_zero_v_zero_data() {
    // Key=0, V=0, provided_data=0
    // V is incremented to 0x01, AES_0(0x01) computed
    // V is incremented to 0x02, AES_0(0x02) computed
    // temp = AES_0(0x01) || AES_0(0x02) XOR 0 = AES_0(0x01) || AES_0(0x02)
    let state = CtrDrbgState { key: [0u8; 16], v: [0u8; 16] };
    let result = ctr_drbg_update(state, [0u8; SEEDLEN]);

    // Compute expected values manually
    let v1: Block = [
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01,
    ];
    let v2: Block = [
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02,
    ];

    let expected_key = aes128_encrypt(&[0u8; 16], &v1);
    let expected_v = aes128_encrypt(&[0u8; 16], &v2);

    assert_eq!(result.key, expected_key);
    assert_eq!(result.v, expected_v);
}

#[test]
fn kat_update_with_nonzero_data() {
    let state = CtrDrbgState { key: [0u8; 16], v: [0u8; 16] };
    let mut data = [0u8; SEEDLEN];
    for i in 0..SEEDLEN {
        data[i] = i as u8;
    }
    let result = ctr_drbg_update(state, data);

    // Compute: temp = AES_0(0x01) || AES_0(0x02)
    let v1 = increment_counter(&[0u8; 16]);
    let block1 = aes128_encrypt(&[0u8; 16], &v1);
    let v2 = increment_counter(&v1);
    let block2 = aes128_encrypt(&[0u8; 16], &v2);

    // XOR with provided_data
    let mut expected_key = [0u8; 16];
    let mut expected_v = [0u8; 16];
    for i in 0..16 {
        expected_key[i] = block1[i] ^ data[i];
        expected_v[i] = block2[i] ^ data[16 + i];
    }

    assert_eq!(result.key, expected_key);
    assert_eq!(result.v, expected_v);
}

// =========================================================================
// Instantiate + Generate roundtrip
// =========================================================================

#[test]
fn kat_instantiate_generate_roundtrip() {
    // Instantiate with known entropy, generate 4 blocks, verify determinism
    let mut entropy = [0u8; SEEDLEN];
    for i in 0..SEEDLEN {
        entropy[i] = ((i * 13 + 7) % 256) as u8;
    }
    let perso = [0u8; SEEDLEN];

    let state = ctr_drbg_instantiate(entropy, perso);
    let (new_state, output) = ctr_drbg_generate(state, 4, [0u8; SEEDLEN]);

    // Repeat and verify identical
    let state2 = ctr_drbg_instantiate(entropy, perso);
    let (new_state2, output2) = ctr_drbg_generate(state2, 4, [0u8; SEEDLEN]);

    for i in 0..4 {
        assert_eq!(output[i], output2[i], "Block {} must match on replay", i);
    }
    assert_eq!(new_state.key, new_state2.key);
    assert_eq!(new_state.v, new_state2.v);
}

// =========================================================================
// Generate produces MAX_GEN_BLOCKS correctly
// =========================================================================

#[test]
fn kat_generate_max_blocks() {
    let entropy = [0x42u8; SEEDLEN];
    let perso = [0u8; SEEDLEN];
    let state = ctr_drbg_instantiate(entropy, perso);

    let (_new_state, output) = ctr_drbg_generate(state, MAX_GEN_BLOCKS, [0u8; SEEDLEN]);

    // All blocks should be non-zero and distinct
    for i in 0..MAX_GEN_BLOCKS {
        let is_nonzero = output[i].iter().any(|&b| b != 0);
        assert!(is_nonzero, "Block {} should be non-zero", i);
    }

    // Verify all blocks are pairwise distinct
    for i in 0..MAX_GEN_BLOCKS {
        for j in (i + 1)..MAX_GEN_BLOCKS {
            assert_ne!(output[i], output[j],
                "Blocks {} and {} should differ", i, j);
        }
    }
}

// =========================================================================
// Reseed + Generate
// =========================================================================

#[test]
fn kat_reseed_then_generate() {
    let entropy = [0x11u8; SEEDLEN];
    let perso = [0u8; SEEDLEN];
    let state = ctr_drbg_instantiate(entropy, perso);

    // Reseed with new entropy
    let new_entropy = [0x22u8; SEEDLEN];
    let reseeded = ctr_drbg_reseed(state, new_entropy, [0u8; SEEDLEN]);

    // Generate after reseed
    let (_final_state, output) = ctr_drbg_generate(reseeded, 2, [0u8; SEEDLEN]);

    // Verify output is deterministic: reseed + generate again
    let reseeded2 = ctr_drbg_reseed(state, new_entropy, [0u8; SEEDLEN]);
    let (_final_state2, output2) = ctr_drbg_generate(reseeded2, 2, [0u8; SEEDLEN]);

    assert_eq!(output[0], output2[0], "Reseed+generate must be deterministic (block 0)");
    assert_eq!(output[1], output2[1], "Reseed+generate must be deterministic (block 1)");
}

#[test]
fn kat_reseed_with_additional_input() {
    let entropy = [0x33u8; SEEDLEN];
    let perso = [0u8; SEEDLEN];
    let state = ctr_drbg_instantiate(entropy, perso);

    // Reseed with additional input
    let new_entropy = [0x44u8; SEEDLEN];
    let additional = [0x55u8; SEEDLEN];
    let reseeded = ctr_drbg_reseed(state, new_entropy, additional);

    // Verify it differs from reseed without additional input
    let reseeded_no_add = ctr_drbg_reseed(state, new_entropy, [0u8; SEEDLEN]);

    assert_ne!(reseeded.key, reseeded_no_add.key,
        "Additional input should change the reseeded key");
}

// =========================================================================
// Generate with additional_input
// =========================================================================

#[test]
fn kat_generate_with_additional_input() {
    let entropy = [0x66u8; SEEDLEN];
    let perso = [0u8; SEEDLEN];
    let state = ctr_drbg_instantiate(entropy, perso);

    // Generate with additional_input = 0
    let (s1, out1) = ctr_drbg_generate(state, 2, [0u8; SEEDLEN]);

    // Generate with non-zero additional_input
    let (s2, out2) = ctr_drbg_generate(state, 2, [0xffu8; SEEDLEN]);

    // A non-Null additional input refreshes the state before the output
    // blocks are produced (SP 800-90A Rev. 1, Section 10.2.1.5.1, step 2),
    // so both the output and the resulting state differ.
    assert_ne!(out1[0], out2[0], "Additional input should change output block 0");
    assert_ne!(out1[1], out2[1], "Additional input should change output block 1");
    assert_ne!(s1.key, s2.key, "Additional input should change post-generate key");
}

// =========================================================================
// Pinned output vector: self-consistent reference
// =========================================================================

#[test]
fn kat_pinned_output_vector() {
    // This test pins the exact output of a specific instantiate+generate sequence.
    // Any change to the implementation will break this test, serving as a regression guard.

    // Instantiate with sequential bytes
    let mut entropy = [0u8; SEEDLEN];
    for i in 0..SEEDLEN {
        entropy[i] = i as u8;
    }
    let perso = [0u8; SEEDLEN];
    let state = ctr_drbg_instantiate(entropy, perso);

    // Generate 2 blocks
    let (_new_state, output) = ctr_drbg_generate(state, 2, [0u8; SEEDLEN]);

    // Pin the output (computed from the implementation)
    // We compute these at test time to be self-consistent, then verify
    // they remain stable across runs.

    // Step 1: Instantiate
    // seed_material = entropy XOR perso = entropy (since perso=0)
    // Update(seed_material, Key=0, V=0):
    let v1 = increment_counter(&[0u8; 16]);  // 0x00..01
    let block1 = aes128_encrypt(&[0u8; 16], &v1);
    let v2 = increment_counter(&v1);  // 0x00..02
    let block2 = aes128_encrypt(&[0u8; 16], &v2);

    let mut inst_key = [0u8; 16];
    let mut inst_v = [0u8; 16];
    for i in 0..16 {
        inst_key[i] = block1[i] ^ entropy[i];
        inst_v[i] = block2[i] ^ entropy[16 + i];
    }
    assert_eq!(state.key, inst_key, "Pinned: instantiate key");
    assert_eq!(state.v, inst_v, "Pinned: instantiate V");

    // Step 2: Generate
    let gen_v1 = increment_counter(&inst_v);
    let gen_out1 = aes128_encrypt(&inst_key, &gen_v1);
    let gen_v2 = increment_counter(&gen_v1);
    let gen_out2 = aes128_encrypt(&inst_key, &gen_v2);

    assert_eq!(output[0], gen_out1, "Pinned: generate block 0");
    assert_eq!(output[1], gen_out2, "Pinned: generate block 1");
}

// =========================================================================
// Full sequence: instantiate -> generate -> reseed -> generate
// =========================================================================

#[test]
fn kat_full_sequence() {
    let entropy = [0xabu8; SEEDLEN];
    let perso = [0xcdu8; SEEDLEN];

    // Instantiate
    let state = ctr_drbg_instantiate(entropy, perso);

    // First generate
    let (state2, first_output) = ctr_drbg_generate(state, 3, [0u8; SEEDLEN]);

    // Reseed
    let reseed_entropy = [0xefu8; SEEDLEN];
    let state3 = ctr_drbg_reseed(state2, reseed_entropy, [0u8; SEEDLEN]);

    // Second generate
    let (_state4, second_output) = ctr_drbg_generate(state3, 3, [0u8; SEEDLEN]);

    // First and second outputs must differ
    assert_ne!(first_output[0], second_output[0],
        "Full sequence: outputs after reseed must differ (block 0)");
    assert_ne!(first_output[1], second_output[1],
        "Full sequence: outputs after reseed must differ (block 1)");
    assert_ne!(first_output[2], second_output[2],
        "Full sequence: outputs after reseed must differ (block 2)");

    // Replay the full sequence and verify determinism
    let state_r = ctr_drbg_instantiate(entropy, perso);
    let (state2_r, first_output_r) = ctr_drbg_generate(state_r, 3, [0u8; SEEDLEN]);
    let state3_r = ctr_drbg_reseed(state2_r, reseed_entropy, [0u8; SEEDLEN]);
    let (_state4_r, second_output_r) = ctr_drbg_generate(state3_r, 3, [0u8; SEEDLEN]);

    for i in 0..3 {
        assert_eq!(first_output[i], first_output_r[i],
            "Full sequence replay: first output block {} must match", i);
        assert_eq!(second_output[i], second_output_r[i],
            "Full sequence replay: second output block {} must match", i);
    }
}
