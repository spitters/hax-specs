//! Integration tests for the plonky3-hax crate.
//!
//! These tests exercise the real API across modules:
//! 1. Baby Bear field axioms (associativity, distributivity, inverses).
//! 2. Root-of-unity properties at various orders.
//! 3. Merkle tree build/verify round-trips.
//! 4. FRI folding consistency between coefficient-form and query-form folding.
//! 5. End-to-end Plonky3 prove/verify on the Fibonacci AIR.

use plonky3_hax::air::{fib_air, fib_trace, trace_valid};
use plonky3_hax::fri::{
    domain_element, fold_polynomial, fri_fold, FriOptions,
};
use plonky3_hax::plonky3::{plonky3_prove, plonky3_verify, transcript_seed};
use plonky3_hax::specs::baby_bear::*;
use plonky3_hax::specs::merkle::*;

// ========================================================================
// Baby Bear field arithmetic
// ========================================================================

#[test]
fn test_baby_bear_prime_formula() {
    let computed: u64 = (1u64 << 31) - (1u64 << 27) + 1;
    assert_eq!(BABY_BEAR_PRIME, 2013265921);
    assert_eq!(BABY_BEAR_PRIME, computed);
}

#[test]
fn test_baby_bear_field_axioms() {
    let vals: [u64; 5] = [0, 1, 42, 0xDEADBEEF & ((1 << 31) - 1), BABY_BEAR_PRIME - 1];

    // Identities.
    for &a in vals.iter() {
        assert_eq!(bb_add(a, 0), a);
        assert_eq!(bb_add(0, a), a);
        assert_eq!(bb_mul(a, 1), a);
        assert_eq!(bb_mul(1, a), a);
    }

    // Additive inverses.
    for &a in vals.iter() {
        assert_eq!(bb_add(a, bb_neg(a)), 0);
    }

    // Multiplicative inverses (nonzero).
    for &a in vals.iter().skip(1) {
        assert_eq!(bb_mul(a, bb_inv(a)), 1);
    }

    // Distributivity.
    let a: u64 = 123;
    let b: u64 = 456;
    let c: u64 = 789;
    assert_eq!(
        bb_mul(a, bb_add(b, c)),
        bb_add(bb_mul(a, b), bb_mul(a, c))
    );

    // Associativity of +.
    assert_eq!(bb_add(bb_add(a, b), c), bb_add(a, bb_add(b, c)));
    // Associativity of *.
    assert_eq!(bb_mul(bb_mul(a, b), c), bb_mul(a, bb_mul(b, c)));
}

#[test]
fn test_baby_bear_roots_of_unity_orders() {
    // For each k in 1..=20, omega^(2^k) = 1 and omega^(2^(k-1)) = -1.
    let mut k: u32 = 1;
    while k <= 20 {
        let omega = bb_root_of_unity(k);
        let order: u64 = 1u64 << k;
        assert_eq!(bb_pow(omega, order), 1, "order mismatch at k={}", k);
        assert_eq!(
            bb_pow(omega, order >> 1),
            BABY_BEAR_PRIME - 1,
            "non-primitive at k={}",
            k
        );
        k += 1;
    }
}

// ========================================================================
// Merkle tree
// ========================================================================

#[test]
fn test_merkle_roundtrip_16_leaves() {
    let num_leaves: usize = 16;
    let mut leaf_hashes: Vec<MerkleHash> = Vec::new();
    let mut i: usize = 0;
    while i < num_leaves {
        leaf_hashes.push(hash_field_elem((i as u64 + 1) * 1337));
        i += 1;
    }
    let mut idx: usize = 0;
    while idx < num_leaves {
        let (root, path) = merkle_build_and_prove(&leaf_hashes, num_leaves, idx);
        assert!(merkle_verify_path(root, leaf_hashes[idx], idx as u64, &path));
        idx += 1;
    }
}

// ========================================================================
// FRI folding consistency
// ========================================================================

#[test]
fn test_fri_folding_consistency_multiple_polynomials() {
    let polys = [
        vec![1u64, 2, 3, 4],
        vec![42u64],
        vec![1u64, 0, 1, 0, 1, 0, 1, 0],
        vec![100u64, 200, 300, 400, 500, 600, 700, 800],
    ];
    let alpha: u64 = 0xDEADBEEF;
    let domain_log2 = 5u32;

    for coeffs in polys.iter() {
        let folded_coeffs = fold_polynomial(coeffs, alpha);
        let mut idx: u64 = 0;
        while idx < 8 {
            let x = domain_element(domain_log2, idx);
            let neg_x = bb_neg(x);
            let eval_pos = bb_poly_eval(coeffs, x);
            let eval_neg = bb_poly_eval(coeffs, neg_x);
            let folded_eval = fri_fold(eval_pos, eval_neg, x, alpha);
            let x_sq = bb_square(x);
            let direct = bb_poly_eval(&folded_coeffs, x_sq);
            assert_eq!(
                folded_eval, direct,
                "poly={:?}, idx={}",
                coeffs, idx
            );
            idx += 1;
        }
    }
}

// ========================================================================
// End-to-end Plonky3 proof on Fibonacci AIR
// ========================================================================

fn default_options() -> FriOptions {
    FriOptions {
        num_layers: 3,
        domain_log2: 5,
        num_queries: 16,
        blowup: 2,
        coset_shift: plonky3_hax::plonky3::LDE_COSET_SHIFT,
        proof_of_work_bits: 0,
    }
}

#[test]
fn test_plonky3_fibonacci_proof_accepts() {
    let air = fib_air();
    let trace = fib_trace(16);
    assert!(trace_valid(&air, &trace));
    let proof = plonky3_prove(&air, &trace, default_options()).expect("prover failed");
    let alphas: Vec<Vec<u64>> = vec![vec![], vec![]];
    assert!(plonky3_verify(&air, &proof, &alphas, default_options()));
}

#[test]
fn test_plonky3_fibonacci_proof_different_lengths() {
    for &h in &[2usize, 4, 8, 16, 32] {
        let air = fib_air();
        let trace = fib_trace(h);
        let proof = plonky3_prove(&air, &trace, default_options())
            .unwrap_or_else(|| panic!("prover failed at height {}", h));
        let alphas: Vec<Vec<u64>> = vec![vec![], vec![]];
        assert!(
            plonky3_verify(&air, &proof, &alphas, default_options()),
            "verify failed at height {}",
            h
        );
    }
}

#[test]
fn test_plonky3_rejects_corrupted_trace() {
    let air = fib_air();
    let mut trace = fib_trace(16);
    trace.set(3, 1, bb_add(trace.get(3, 1), 7));
    assert!(plonky3_prove(&air, &trace, default_options()).is_none());
}

#[test]
fn test_plonky3_transcript_seed_reflects_proof() {
    let air = fib_air();
    let trace = fib_trace(16);
    let proof = plonky3_prove(&air, &trace, default_options()).unwrap();
    let seed_a = transcript_seed(&proof);

    // Second proof over the same trace is byte-identical (prover is
    // deterministic), so the transcript seed matches.
    let proof2 = plonky3_prove(&air, &trace, default_options()).unwrap();
    assert_eq!(seed_a, transcript_seed(&proof2));
}
