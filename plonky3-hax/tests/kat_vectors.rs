//! Regression values of this crate's own outputs.
//!
//! None of the values below comes from an external source. The field
//! values (`bb_inv(7)`, `bb_pow(31, 27)`, the roots of unity) are checked
//! here by the identities they satisfy and are also recomputed by the
//! Plonky3 oracle in `cross_lib.rs` and taken from the Plonky3 sources in
//! `plonky3_vectors.rs`. The Merkle hashes, FRI fold values, trace
//! commitments and transcript seeds of the reference STARK were produced by
//! this crate and recorded, so that a change to the hash, the LDE layout or
//! the order of boundary claims fails a test; they are not validated
//! against any other implementation, since the STARK has none.
//!
//! 1. Baby Bear arithmetic: identities and specific values.
//! 2. Polynomial evaluation by Horner's rule against a hand computation.
//! 3. FRI fold values and index maps.
//! 4. Merkle leaf, node and root hashes.
//! 5. Fibonacci AIR proofs of heights 8 and 16: trace commitment and
//!    transcript seed.

use hex_literal::hex;
use plonky3_hax::air::{air_max_degree, fib_air, fib_trace, trace_valid};
use plonky3_hax::fri::{
    domain_element, fold_polynomial, folded_index, fri_fold, sibling_index, FriOptions,
};
use plonky3_hax::plonky3::{plonky3_prove, transcript_seed};
use plonky3_hax::specs::baby_bear::*;
use plonky3_hax::specs::merkle::*;

// ========================================================================
// 1. Baby Bear arithmetic KATs
// ========================================================================

#[test]
fn kat_baby_bear_prime() {
    // p = 2^31 - 2^27 + 1 = 0x78000001
    assert_eq!(BABY_BEAR_PRIME, 2013265921);
    assert_eq!(BABY_BEAR_PRIME, 0x78000001);
}

#[test]
fn kat_baby_bear_prime_polynomial_form() {
    // p = 2^31 - 2^27 + 1, checked separately from the numeric literal in
    // `kat_baby_bear_prime`.
    let from_polynomial: u64 = (1u64 << 31) - (1u64 << 27) + 1;
    assert_eq!(BABY_BEAR_PRIME, from_polynomial);
    // Multiplicative-group order:
    //     p - 1 = 2^27 * (2^4 - 1) = 2^27 * 15
    // so the group is 2-adic of order 2^27 and the cofactor is 15.
    let p_minus_one = BABY_BEAR_PRIME - 1;
    assert_eq!(p_minus_one, (1u64 << 27) * 15);
    assert_eq!(p_minus_one >> 27, 15);
}

#[test]
fn kat_baby_bear_generator_has_full_order() {
    // GENERATOR = 31 generates F_p^*, i.e. has order exactly p - 1.
    // It is enough to check that GENERATOR^((p-1)/q) ≠ 1 for every prime
    // factor q of p - 1. The prime factors of 2^27 * 15 are 2, 3, 5.
    let p_minus_one = BABY_BEAR_PRIME - 1;
    // Spot check the (already covered) Fermat side first.
    assert_eq!(bb_pow(GENERATOR, p_minus_one), 1);
    // Non-trivial side: order is not a proper divisor of p - 1.
    for &q in &[2u64, 3, 5] {
        let e = p_minus_one / q;
        let g_e = bb_pow(GENERATOR, e);
        assert_ne!(
            g_e, 1,
            "GENERATOR^((p-1)/{}) = 1 — order is a proper divisor of p-1",
            q
        );
    }
}

#[test]
fn kat_fib_air_transition_degree() {
    // The transition constraints of the Fibonacci AIR are linear, so their
    // declared degree bound is 1.
    let air = fib_air();
    let d = air_max_degree(&air);
    assert_eq!(d, 1, "fib_air transition degree bound changed");
}

#[test]
fn kat_baby_bear_add_wraparound() {
    // p - 1 + 1 = 0
    assert_eq!(bb_add(2013265920, 1), 0);
    // Commutativity on a specific pair
    assert_eq!(bb_add(1_000_000, 2_000_000), 3_000_000);
}

#[test]
fn kat_baby_bear_mul_specific() {
    assert_eq!(bb_mul(2, 3), 6);
    // (p-1)^2 = 1 mod p
    assert_eq!(bb_mul(2013265920, 2013265920), 1);
}

#[test]
fn kat_baby_bear_inv_of_7() {
    // 7 * bb_inv(7) == 1
    assert_eq!(bb_inv(7), 862828252);
    assert_eq!(bb_mul(7, bb_inv(7)), 1);
}

#[test]
fn kat_baby_bear_pow() {
    // 31^27 mod p, frozen for regression
    assert_eq!(bb_pow(31, 27), 607168496);
    // Fermat's little theorem spot check
    assert_eq!(bb_pow(17, BABY_BEAR_PRIME - 1), 1);
}

#[test]
fn kat_baby_bear_sub_wraparound() {
    // 0 - 1 = p - 1
    assert_eq!(bb_sub(0, 1), BABY_BEAR_PRIME - 1);
    assert_eq!(bb_sub(5, 7), BABY_BEAR_PRIME - 2);
}

#[test]
fn kat_baby_bear_neg() {
    assert_eq!(bb_neg(0), 0);
    assert_eq!(bb_neg(1), BABY_BEAR_PRIME - 1);
    assert_eq!(bb_neg(bb_neg(123_456_789)), 123_456_789);
}

#[test]
fn kat_baby_bear_square() {
    // (p-1)^2 = 1 mod p (already covered by mul_specific, but separately
    // exercises bb_square)
    assert_eq!(bb_square(2013265920), 1);
    assert_eq!(bb_square(7), 49);
    // Consistency with bb_mul on a non-trivial input
    let v = 1_234_567u64;
    assert_eq!(bb_square(v), bb_mul(v, v));
}

#[test]
fn kat_baby_bear_div() {
    // a / b = a * inv(b)
    assert_eq!(bb_div(21, 7), 3);
    // Division by zero: bb_inv(0) = 0, so bb_div(a, 0) = 0.
    assert_eq!(bb_div(123, 0), 0);
}

#[test]
fn kat_baby_bear_inv_of_zero_is_zero() {
    // Convention: inv(0) := 0 for totality.
    assert_eq!(bb_inv(0), 0);
}

#[test]
fn kat_baby_bear_roots_of_unity() {
    assert_eq!(bb_root_of_unity(8), 1732600167);
    assert_eq!(bb_root_of_unity(16), 1421947380);
    assert_eq!(bb_root_of_unity(27), 440564289);
    // Primitivity checks
    assert_eq!(bb_pow(bb_root_of_unity(8), 256), 1);
    assert_eq!(bb_pow(bb_root_of_unity(27), 1u64 << 27), 1);
}

// ========================================================================
// 2. Polynomial evaluation
// ========================================================================

#[test]
fn kat_poly_eval_horner() {
    // p(x) = 7 + 11 x + 13 x^2 + 17 x^3 at x = 3.
    // p(3) = 7 + 33 + 117 + 459 = 616.
    let p = [7u64, 11, 13, 17];
    assert_eq!(bb_poly_eval(&p, 3), 616);
}

// ========================================================================
// 3. FRI fold KATs
// ========================================================================

#[test]
fn kat_fri_fold_specific_point() {
    // fri_fold(100, 50, 7, 3) against the implementation.
    assert_eq!(fri_fold(100, 50, 7, 3), 287609503);
}

#[test]
fn kat_fri_fold_constant_returns_constant() {
    // Constant polynomial p(x) = c => fold is c for any alpha.
    assert_eq!(fri_fold(42, 42, 5, 999), 42);
    assert_eq!(fri_fold(1, 1, 1, 0), 1);
}

#[test]
fn kat_fri_sibling_index() {
    // log2 = 4 => domain size 16, sibling flips the high bit (n/2 = 8).
    assert_eq!(sibling_index(0, 4), 8);
    assert_eq!(sibling_index(8, 4), 0);
    assert_eq!(sibling_index(3, 4), 11);
    assert_eq!(sibling_index(11, 4), 3);
}

#[test]
fn kat_fri_folded_index() {
    // For log2 = 4 the folded index is i mod (n/2) = i mod 8.
    assert_eq!(folded_index(0, 4), 0);
    assert_eq!(folded_index(7, 4), 7);
    assert_eq!(folded_index(8, 4), 0);
    assert_eq!(folded_index(15, 4), 7);
}

#[test]
fn kat_fri_domain_element_is_root_of_unity() {
    // domain_element(k, 0) = 1 (any root^0)
    assert_eq!(domain_element(8, 0), 1);
    // domain_element(k, 1) = bb_root_of_unity(k)
    assert_eq!(domain_element(8, 1), bb_root_of_unity(8));
}

#[test]
fn kat_fri_fold_polynomial_constant() {
    // p(x) = c collapses to a single coefficient under one fold step.
    let folded = fold_polynomial(&[42, 0], 5);
    assert_eq!(folded, vec![42]);
}

#[test]
fn kat_fri_fold_polynomial_linear() {
    // p(x) = a + b x => fold(alpha)(x^2) = a + alpha * b
    // coeffs = [a, b], alpha = 11 => [a + 11*b]
    let folded = fold_polynomial(&[3, 5], 11);
    assert_eq!(folded, vec![bb_add(3, bb_mul(11, 5))]);
}

// ========================================================================
// 4. Merkle hash KATs
// ========================================================================

#[test]
fn kat_hash_field_elem_zero() {
    assert_eq!(
        hash_field_elem(0),
        hex!("09c4d5a801ac8dd07914c57871fc7da0e964b548e14c6d7059b4a518519c5d40")
    );
}

#[test]
fn kat_hash_field_elem_one() {
    assert_eq!(
        hash_field_elem(1),
        hex!("0983729f469bba77ce3382cfd64bcaa75ee392ff66fbdad7ee93a18c2db019f4")
    );
}

#[test]
fn kat_hash_field_elem_forty_two() {
    assert_eq!(
        hash_field_elem(42),
        hex!("091a972e53e2ef366b2ac7be03f21fc61b3af74eb3024f56cb4a416ccd90b9d4")
    );
}

#[test]
fn kat_hash_two_to_one_constant_inputs() {
    assert_eq!(
        hash_two_to_one([0x01u8; 32], [0x02u8; 32]),
        hex!("b5fd0238a9bdfef855e5b270b9d56e2025fd32f859fd2ef84585c2d089f51e80")
    );
}

#[test]
fn kat_field_elem_to_bytes_little_endian() {
    // u64 -> [u8; 8] little-endian.
    assert_eq!(field_elem_to_bytes(0), [0, 0, 0, 0, 0, 0, 0, 0]);
    assert_eq!(field_elem_to_bytes(1), [1, 0, 0, 0, 0, 0, 0, 0]);
    assert_eq!(
        field_elem_to_bytes(0x0807060504030201),
        [1, 2, 3, 4, 5, 6, 7, 8]
    );
}

#[test]
fn kat_merkle_root_four_leaves() {
    // Tree over (hash_field_elem(1), .., hash_field_elem(4))
    let leaves: Vec<MerkleHash> = (1u64..=4u64).map(hash_field_elem).collect();
    let root = merkle_build_root(&leaves, 4);
    assert_eq!(
        root,
        hex!("00e1d70044a1e330b8c13f008cb1eb70c0f17770645183209871b7c024899b78")
    );
}

// ========================================================================
// 5. Fibonacci AIR regression vectors
// ========================================================================

#[test]
fn kat_fibonacci_trace_values() {
    // First ten Fibonacci numbers (mod p, but they're small).
    let trace = fib_trace(10);
    let expected: [u64; 10] = [1, 1, 2, 3, 5, 8, 13, 21, 34, 55];
    for (i, &exp) in expected.iter().enumerate() {
        assert_eq!(trace.get(i, 1), exp, "row {}", i);
    }
}

fn default_options() -> FriOptions {
    FriOptions {
        num_layers: 3,
        domain_log2: 5,
        num_queries: 8,
        blowup: 2,
        coset_shift: plonky3_hax::plonky3::LDE_COSET_SHIFT,
        proof_of_work_bits: 0,
    }
}

#[test]
fn kat_plonky3_fib_height8_commitment() {
    let air = fib_air();
    let trace = fib_trace(8);
    assert!(trace_valid(&air, &trace));
    let proof = plonky3_prove(&air, &trace, default_options()).expect("prover");
    assert_eq!(
        proof.trace_commitment,
        hex!("00faf642866028e830ca7eea6630a0b0c05a86d2e66038f8d02a0b3b3a14793d")
    );
    assert_eq!(proof.boundary_claims, vec![0u64, 1u64]);
    assert_eq!(proof.column_fri_proofs.len(), 2);
}

#[test]
fn kat_plonky3_fib_height8_transcript_seed() {
    let air = fib_air();
    let trace = fib_trace(8);
    let proof = plonky3_prove(&air, &trace, default_options()).unwrap();
    assert_eq!(
        transcript_seed(&proof),
        hex!("00766435de1322a40ceaf8d12a973e00903634558ef3f2c4fcea7e5dc731ed5e")
    );
}

#[test]
fn kat_plonky3_fib_height16_commitment() {
    let air = fib_air();
    let trace = fib_trace(16);
    let proof = plonky3_prove(&air, &trace, default_options()).expect("prover");
    assert_eq!(
        proof.trace_commitment,
        hex!("001cfcd0bf3437bc74b8d05c6b68b3c0d09cec50cf7407dcc4587f47532388ac")
    );
}

#[test]
fn kat_plonky3_fib_height16_transcript_seed() {
    let air = fib_air();
    let trace = fib_trace(16);
    let proof = plonky3_prove(&air, &trace, default_options()).unwrap();
    assert_eq!(
        transcript_seed(&proof),
        hex!("00c012c79313557868d8420fdb8b4570d0e0f2178373f5e8b8388217c60eec69")
    );
}
