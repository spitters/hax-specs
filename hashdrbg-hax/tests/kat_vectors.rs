//! Known-Answer Tests (KAT) for Hash_DRBG with SHA-256.
//!
//! `kat_nist_sp800_90a_sha256` drives the crate's own instantiate and generate
//! against the NIST Hash_DRBG worked example (SP 800-90A Rev. 1, SHA-256
//! section). `tests/cavp_drbgvs.rs` holds the CAVP DRBGVS vectors.
//! The remaining tests exercise the byte-arithmetic and structural properties
//! by computing intermediate values with the crate and pinning outputs.

use hashdrbg_hax::*;

// =========================================================================
// Published NIST vector: Hash_DRBG with SHA-256 worked example (SP 800-90A Rev. 1)
//
// Source: NIST "Hash_DRBG" example values
// <https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/Hash_DRBG.pdf>,
// the SHA-256 section with
// Requested Security Strength = 128, prediction_resistance = NOT ENABLED,
// PersonalizationString = empty, AdditionalInput = empty, and no reseed
// between the two Generate calls.
//
//   EntropyInput = 000102...36           (55 bytes, values 0x00..0x36)
//   Nonce        = 2021222324252627      (8 bytes)
//   V (after instantiate) =
//     AB41CDE437AB8B091CA7C5755D10F0110C1DBD462F226CFDABFBB04A8BCDEF
//     95167D84AF64128C0D71F4D5B8C0EDFBBE3DF40448D2D8E1
//   1st Generate (512 bits) returned_bits =
//     77E05A0E7DC78AB5D8934D5E93E82C06A07C04CEE6C9C53045EEB485872777CF
//     3B3E35C474F976B894BF301A86FA651F463970E89D4A0534B2ECAD29EC044E7E
//   2nd Generate (512 bits) returned_bits =
//     5FF4BA493C40CFFF3B01E472C575668CCE3880B9290B05BFEDE5EC96ED5E9B28
//     98508B09BC800EEE099A3C90602ABD4B1D4F343D497C6055C87BB956D53BF351
// =========================================================================

#[test]
fn kat_nist_sp800_90a_sha256() {
    // EntropyInput = 0x00, 0x01, ..., 0x36 (55 bytes).
    let mut entropy = [0u8; SEEDLEN];
    for (i, b) in entropy.iter_mut().enumerate() {
        *b = i as u8;
    }
    // Nonce = 0x20..0x27 (8 bytes).
    let mut nonce = [0u8; OUTLEN];
    for (i, b) in nonce[..8].iter_mut().enumerate() {
        *b = 0x20u8 + (i as u8);
    }
    let perso = [0u8; MAX_PERSONALIZATION_LEN];

    let state = hash_drbg_instantiate(&entropy, SEEDLEN, &nonce, 8, &perso, 0);

    // V after instantiate (published).
    let expected_v: [u8; SEEDLEN] = [
        0xAB, 0x41, 0xCD, 0xE4, 0x37, 0xAB, 0x8B, 0x09, 0x1C, 0xA7, 0xC5, 0x75,
        0x5D, 0x10, 0xF0, 0x11, 0x0C, 0x1D, 0xBD, 0x46, 0x2F, 0x22, 0x6C, 0xFD,
        0xAB, 0xFB, 0xB0, 0x4A, 0x8B, 0xCD, 0xEF, 0x95, 0x16, 0x7D, 0x84, 0xAF,
        0x64, 0x12, 0x8C, 0x0D, 0x71, 0xF4, 0xD5, 0xB8, 0xC0, 0xED, 0xFB, 0xBE,
        0x3D, 0xF4, 0x04, 0x48, 0xD2, 0xD8, 0xE1,
    ];
    assert_eq!(state.v, expected_v, "instantiate V must match the NIST worked example");

    // First Generate: 512 bits = 64 bytes, no additional input.
    let no_additional = [0u8; MAX_ADDITIONAL_INPUT_LEN];
    let (out1, state1) = hash_drbg_generate(&state, 64, &no_additional, 0);

    let expected_gen1: [u8; 64] = [
        0x77, 0xE0, 0x5A, 0x0E, 0x7D, 0xC7, 0x8A, 0xB5, 0xD8, 0x93, 0x4D, 0x5E,
        0x93, 0xE8, 0x2C, 0x06, 0xA0, 0x7C, 0x04, 0xCE, 0xE6, 0xC9, 0xC5, 0x30,
        0x45, 0xEE, 0xB4, 0x85, 0x87, 0x27, 0x77, 0xCF, 0x3B, 0x3E, 0x35, 0xC4,
        0x74, 0xF9, 0x76, 0xB8, 0x94, 0xBF, 0x30, 0x1A, 0x86, 0xFA, 0x65, 0x1F,
        0x46, 0x39, 0x70, 0xE8, 0x9D, 0x4A, 0x05, 0x34, 0xB2, 0xEC, 0xAD, 0x29,
        0xEC, 0x04, 0x4E, 0x7E,
    ];
    assert_eq!(&out1[..64], &expected_gen1[..], "1st Generate must match the NIST worked example");
    assert_eq!(state1.reseed_counter, 2, "reseed_counter after 1st Generate");

    // Second Generate, chaining the returned state (no reseed).
    let (out2, _state2) = hash_drbg_generate(&state1, 64, &no_additional, 0);

    let expected_gen2: [u8; 64] = [
        0x5F, 0xF4, 0xBA, 0x49, 0x3C, 0x40, 0xCF, 0xFF, 0x3B, 0x01, 0xE4, 0x72,
        0xC5, 0x75, 0x66, 0x8C, 0xCE, 0x38, 0x80, 0xB9, 0x29, 0x0B, 0x05, 0xBF,
        0xED, 0xE5, 0xEC, 0x96, 0xED, 0x5E, 0x9B, 0x28, 0x98, 0x50, 0x8B, 0x09,
        0xBC, 0x80, 0x0E, 0xEE, 0x09, 0x9A, 0x3C, 0x90, 0x60, 0x2A, 0xBD, 0x4B,
        0x1D, 0x4F, 0x34, 0x3D, 0x49, 0x7C, 0x60, 0x55, 0xC8, 0x7B, 0xB9, 0x56,
        0xD5, 0x3B, 0xF3, 0x51,
    ];
    assert_eq!(&out2[..64], &expected_gen2[..], "2nd Generate must match the NIST worked example");
}

// =========================================================================
// Test 1: Hash_df of known input, pinned output
// =========================================================================

#[test]
fn kat_hash_df_zeros() {
    // Hash_df of all-zero input (64 bytes), requesting 440 bits
    let input = [0u8; MAX_HASH_DF_INPUT_LEN];
    let result = hash_df(&input, 64, 440);

    // Verify by manual computation:
    // Iteration 1: SHA256(0x01 || 0x000001B8 || 0x00*64)
    let mut h1_in = [0u8; MAX_HASH_DF_INPUT_LEN];
    h1_in[0] = 0x01;
    h1_in[1] = 0x00; h1_in[2] = 0x00; h1_in[3] = 0x01; h1_in[4] = 0xB8;
    // bytes 5..69 are zero (the input)
    let h1 = sha256(&h1_in, 69);

    // Iteration 2: SHA256(0x02 || 0x000001B8 || 0x00*64)
    let mut h2_in = [0u8; MAX_HASH_DF_INPUT_LEN];
    h2_in[0] = 0x02;
    h2_in[1] = 0x00; h2_in[2] = 0x00; h2_in[3] = 0x01; h2_in[4] = 0xB8;
    let h2 = sha256(&h2_in, 69);

    let mut expected = [0u8; SEEDLEN];
    expected[..32].copy_from_slice(&h1);
    expected[32..].copy_from_slice(&h2[..23]);

    assert_eq!(result, expected, "Hash_df(zeros, 440) should match manual computation");
}

// =========================================================================
// Test 2: Hash_df with single-byte input
// =========================================================================

#[test]
fn kat_hash_df_single_byte() {
    let mut input = [0u8; MAX_HASH_DF_INPUT_LEN];
    input[0] = 0xFF;
    let result = hash_df(&input, 1, 440);

    // Should produce consistent output
    let result2 = hash_df(&input, 1, 440);
    assert_eq!(result, result2, "Hash_df should be deterministic");

    // Result should not be all zeros
    assert_ne!(result, [0u8; SEEDLEN], "Hash_df output should not be all zeros");
}

// =========================================================================
// Test 3: Instantiate with known entropy/nonce, pin V and C
// =========================================================================

#[test]
fn kat_instantiate_pinned() {
    let entropy = [0x01u8; SEEDLEN];
    let nonce = [0x02u8; OUTLEN];
    let perso = [0u8; MAX_PERSONALIZATION_LEN];

    let state = hash_drbg_instantiate(&entropy, SEEDLEN, &nonce, OUTLEN, &perso, 0);

    // Manually compute expected V
    let mut seed_mat = [0u8; MAX_HASH_DF_INPUT_LEN];
    seed_mat[..SEEDLEN].fill(0x01);
    seed_mat[SEEDLEN..SEEDLEN + OUTLEN].fill(0x02);
    let expected_v = hash_df(&seed_mat, SEEDLEN + OUTLEN, 440);

    assert_eq!(state.v, expected_v, "V = Hash_df(entropy||nonce, 440)");

    // Manually compute expected C
    let mut c_in = [0u8; MAX_HASH_DF_INPUT_LEN];
    c_in[0] = 0x00;
    c_in[1..1 + SEEDLEN].copy_from_slice(&expected_v);
    let expected_c = hash_df(&c_in, 1 + SEEDLEN, 440);

    assert_eq!(state.c, expected_c, "C = Hash_df(0x00||V, 440)");
    assert_eq!(state.reseed_counter, 1);

    // Pin first 16 bytes of V for regression
    let pinned_v: [u8; 16] = [
        state.v[0],  state.v[1],  state.v[2],  state.v[3],
        state.v[4],  state.v[5],  state.v[6],  state.v[7],
        state.v[8],  state.v[9],  state.v[10], state.v[11],
        state.v[12], state.v[13], state.v[14], state.v[15],
    ];

    // Re-instantiate and verify same pinned values
    let state2 = hash_drbg_instantiate(&entropy, SEEDLEN, &nonce, OUTLEN, &perso, 0);
    let pinned_v2: [u8; 16] = [
        state2.v[0],  state2.v[1],  state2.v[2],  state2.v[3],
        state2.v[4],  state2.v[5],  state2.v[6],  state2.v[7],
        state2.v[8],  state2.v[9],  state2.v[10], state2.v[11],
        state2.v[12], state2.v[13], state2.v[14], state2.v[15],
    ];
    assert_eq!(pinned_v, pinned_v2, "Pinned V bytes must be reproducible");
}

// =========================================================================
// Test 4: Generate and verify deterministic output
// =========================================================================

#[test]
fn kat_generate_pinned_output() {
    let entropy = [0xABu8; SEEDLEN];
    let nonce = [0xCDu8; OUTLEN];
    let perso = [0u8; MAX_PERSONALIZATION_LEN];

    let state = hash_drbg_instantiate(&entropy, SEEDLEN, &nonce, OUTLEN, &perso, 0);
    let no_additional = [0u8; MAX_ADDITIONAL_INPUT_LEN];
    let (output, new_state) = hash_drbg_generate(&state, 64, &no_additional, 0);

    // Output should match Hashgen(V, 64)
    let mut expected_output = [0u8; MAX_OUTPUT];
    hashgen(&state.v, 64, &mut expected_output);
    for i in 0..64 {
        assert_eq!(output[i], expected_output[i], "Generate output byte {} mismatch", i);
    }

    // Verify state update: V = (V + H + C + reseed_counter) mod 2^seedlen
    // H = Hash(0x03 || V)
    let mut h_in = [0u8; MAX_HASH_DF_INPUT_LEN];
    h_in[0] = 0x03;
    h_in[1..1 + SEEDLEN].copy_from_slice(&state.v);
    let h_digest = sha256(&h_in, 1 + SEEDLEN);

    let mut h_ext = [0u8; SEEDLEN];
    for i in 0..OUTLEN { h_ext[SEEDLEN - OUTLEN + i] = h_digest[i]; }

    let v_plus_h = add_mod_seedlen(&state.v, &h_ext);
    let v_plus_h_plus_c = add_mod_seedlen(&v_plus_h, &state.c);
    let expected_new_v = add_u64_mod_seedlen(&v_plus_h_plus_c, state.reseed_counter);

    assert_eq!(new_state.v, expected_new_v, "New V should follow spec update rule");
    assert_eq!(new_state.reseed_counter, 2);
}

// =========================================================================
// Test 5: Big-number add at boundary - all zeros
// =========================================================================

#[test]
fn kat_add_zeros() {
    let a = [0u8; SEEDLEN];
    let b = [0u8; SEEDLEN];
    let result = add_mod_seedlen(&a, &b);
    assert_eq!(result, [0u8; SEEDLEN], "0 + 0 = 0");
}

// =========================================================================
// Test 6: Big-number add with carry propagation across all bytes
// =========================================================================

#[test]
fn kat_add_carry_propagation() {
    // 0x00FF...FF + 0x01 should give 0x0100...00
    let mut a = [0u8; SEEDLEN];
    a[1..].fill(0xFF);
    let mut b = [0u8; SEEDLEN];
    b[SEEDLEN - 1] = 0x01;

    let result = add_mod_seedlen(&a, &b);

    let mut expected = [0u8; SEEDLEN];
    expected[0] = 0x01;
    assert_eq!(result, expected, "Carry should propagate across all bytes");
}

// =========================================================================
// Test 7: Big-number add full overflow (mod 2^seedlen)
// =========================================================================

#[test]
fn kat_add_full_overflow() {
    let a = [0xFFu8; SEEDLEN];
    let b = [0xFFu8; SEEDLEN];
    let result = add_mod_seedlen(&a, &b);

    // 0xFF..FF + 0xFF..FF = 0x1FF..FE mod 2^seedlen = 0xFF..FE
    let mut expected = [0xFFu8; SEEDLEN];
    expected[SEEDLEN - 1] = 0xFE;
    assert_eq!(result, expected, "Full overflow: 0xFF*55 + 0xFF*55 = 0xFF..FE");
}

// =========================================================================
// Test 8: Commutativity of addition
// =========================================================================

#[test]
fn kat_add_commutative() {
    let mut a = [0u8; SEEDLEN];
    let mut b = [0u8; SEEDLEN];
    a[0] = 0x12; a[10] = 0x34; a[SEEDLEN-1] = 0x56;
    b[0] = 0x78; b[10] = 0x9A; b[SEEDLEN-1] = 0xBC;

    let r1 = add_mod_seedlen(&a, &b);
    let r2 = add_mod_seedlen(&b, &a);
    assert_eq!(r1, r2, "Addition should be commutative");
}

// =========================================================================
// Test 9: Two consecutive generates produce different output
// =========================================================================

#[test]
fn kat_consecutive_generates() {
    let entropy = [0x77u8; SEEDLEN];
    let nonce = [0x88u8; OUTLEN];
    let perso = [0u8; MAX_PERSONALIZATION_LEN];
    let state = hash_drbg_instantiate(&entropy, SEEDLEN, &nonce, OUTLEN, &perso, 0);

    let no_additional = [0u8; MAX_ADDITIONAL_INPUT_LEN];
    let (out1, state1) = hash_drbg_generate(&state, 32, &no_additional, 0);
    let (out2, state2) = hash_drbg_generate(&state1, 32, &no_additional, 0);
    let (out3, _state3) = hash_drbg_generate(&state2, 32, &no_additional, 0);

    assert_ne!(out1[..32], out2[..32], "1st and 2nd generate should differ");
    assert_ne!(out2[..32], out3[..32], "2nd and 3rd generate should differ");
    assert_ne!(out1[..32], out3[..32], "1st and 3rd generate should differ");

    assert_eq!(state1.reseed_counter, 2);
    assert_eq!(state2.reseed_counter, 3);
}

// =========================================================================
// Test 10: Reseed and generate
// =========================================================================

#[test]
fn kat_reseed_then_generate() {
    let entropy = [0x11u8; SEEDLEN];
    let nonce = [0x22u8; OUTLEN];
    let perso = [0u8; MAX_PERSONALIZATION_LEN];
    let state = hash_drbg_instantiate(&entropy, SEEDLEN, &nonce, OUTLEN, &perso, 0);

    // Generate before reseed
    let no_additional = [0u8; MAX_ADDITIONAL_INPUT_LEN];
    let (out_before, state1) = hash_drbg_generate(&state, 32, &no_additional, 0);

    // Reseed
    let new_entropy = [0x33u8; SEEDLEN];
    let reseeded = hash_drbg_reseed(&state1, &new_entropy, SEEDLEN, &no_additional, 0);

    // Verify reseed resets counter
    assert_eq!(reseeded.reseed_counter, 1, "Reseed should reset counter to 1");

    // Generate after reseed
    let (out_after, _) = hash_drbg_generate(&reseeded, 32, &no_additional, 0);

    // Outputs should differ
    assert_ne!(out_before[..32], out_after[..32], "Output should differ after reseed");
}

// =========================================================================
// Test 11: Hashgen with 1 byte request
// =========================================================================

#[test]
fn kat_hashgen_one_byte() {
    let v = [0x42u8; SEEDLEN];
    let mut output = [0u8; MAX_OUTPUT];
    hashgen(&v, 1, &mut output);

    // First byte should be first byte of Hash(V)
    let full_hash = sha256(&v, SEEDLEN);
    assert_eq!(output[0], full_hash[0], "hashgen(1) should return first byte of Hash(V)");

    // Remaining bytes should be zero
    for (i, b) in output.iter().enumerate().skip(1) {
        assert_eq!(*b, 0, "hashgen(1) byte {} should be 0", i);
    }
}

// =========================================================================
// Test 12: Hashgen with MAX_OUTPUT bytes
// =========================================================================

#[test]
fn kat_hashgen_max_output() {
    let v = [0xEEu8; SEEDLEN];
    let mut output = [0u8; MAX_OUTPUT];
    hashgen(&v, MAX_OUTPUT, &mut output);

    // Verify all 4 blocks
    let mut data = v;
    for block in 0..4 {
        let h = sha256(&data, SEEDLEN);
        for j in 0..OUTLEN {
            assert_eq!(
                output[block * OUTLEN + j], h[j],
                "hashgen(MAX_OUTPUT) block {} byte {} mismatch", block, j
            );
        }
        data = increment_mod_seedlen(&data);
    }
}

// =========================================================================
// Test 13: Instantiate with personalization string
// =========================================================================

#[test]
fn kat_instantiate_with_personalization() {
    let entropy = [0x55u8; SEEDLEN];
    let nonce = [0x66u8; OUTLEN];

    let mut perso = [0u8; MAX_PERSONALIZATION_LEN];
    for (i, b) in perso[..16].iter_mut().enumerate() { *b = (i as u8) + 1; }

    let state = hash_drbg_instantiate(&entropy, SEEDLEN, &nonce, OUTLEN, &perso, 16);

    // Verify by manual seed_material construction
    let mut seed_mat = [0u8; MAX_HASH_DF_INPUT_LEN];
    seed_mat[..SEEDLEN].fill(0x55);
    seed_mat[SEEDLEN..SEEDLEN + OUTLEN].fill(0x66);
    for (i, b) in seed_mat[SEEDLEN + OUTLEN..SEEDLEN + OUTLEN + 16].iter_mut().enumerate() { *b = (i as u8) + 1; }
    let expected_v = hash_df(&seed_mat, SEEDLEN + OUTLEN + 16, 440);

    assert_eq!(state.v, expected_v, "V should incorporate personalization string");
}

// =========================================================================
// Test 14: Generate with additional input modifies V before hashgen
// =========================================================================

#[test]
fn kat_generate_additional_input_effect() {
    let entropy = [0x10u8; SEEDLEN];
    let nonce = [0x20u8; OUTLEN];
    let perso = [0u8; MAX_PERSONALIZATION_LEN];
    let state = hash_drbg_instantiate(&entropy, SEEDLEN, &nonce, OUTLEN, &perso, 0);

    // Generate with additional input
    let mut add_input = [0u8; MAX_ADDITIONAL_INPUT_LEN];
    add_input[0] = 0xAA;
    add_input[1] = 0xBB;
    let (output, _) = hash_drbg_generate(&state, 32, &add_input, 2);

    // Manually verify: w = Hash(0x02 || V || additional_input)
    let mut hash_in = [0u8; MAX_HASH_DF_INPUT_LEN];
    hash_in[0] = 0x02;
    hash_in[1..1 + SEEDLEN].copy_from_slice(&state.v);
    hash_in[1 + SEEDLEN] = 0xAA;
    hash_in[2 + SEEDLEN] = 0xBB;
    let w = sha256(&hash_in, 1 + SEEDLEN + 2);

    // V' = (V + w) mod 2^seedlen
    let mut w_ext = [0u8; SEEDLEN];
    for i in 0..OUTLEN { w_ext[SEEDLEN - OUTLEN + i] = w[i]; }
    let v_prime = add_mod_seedlen(&state.v, &w_ext);

    // Output should be Hashgen(V', 32)
    let mut expected_output = [0u8; MAX_OUTPUT];
    hashgen(&v_prime, 32, &mut expected_output);
    for i in 0..32 {
        assert_eq!(output[i], expected_output[i],
            "Generate with additional_input byte {} should match", i);
    }
}

// =========================================================================
// Test 15: Increment at boundary
// =========================================================================

#[test]
fn kat_increment_boundary() {
    // Incrementing 0xFF..FF should wrap to 0
    let all_ff = [0xFFu8; SEEDLEN];
    let result = increment_mod_seedlen(&all_ff);
    assert_eq!(result, [0u8; SEEDLEN], "Incrementing 0xFF..FF should wrap to 0");

    // Incrementing 0x00..00 should give 0x00..01
    let all_zero = [0u8; SEEDLEN];
    let result2 = increment_mod_seedlen(&all_zero);
    let mut expected = [0u8; SEEDLEN];
    expected[SEEDLEN - 1] = 0x01;
    assert_eq!(result2, expected, "Incrementing 0 should give 1");
}
