//! Property-based equivalence tests for plonky3-hax.
//!
//! Random-input checks that exercise:
//!
//! 1. **Baby Bear field axioms.** Additive/multiplicative commutativity,
//!    associativity, distributivity, identity, inverses — over fresh
//!    `u64` samples reduced into `[0, p)`.
//! 2. **FRI fold/evaluate consistency.** For random polynomial coefficient
//!    vectors and random challenges, the FRI verifier formula
//!    `fri_fold(p(x), p(-x), x, alpha)` equals `p'(x²)` where `p'` is
//!    `fold_polynomial(p, alpha)`. This is the load-bearing algebraic
//!    identity behind FRI soundness.
//! 3. **Roots of unity.** For random `k ∈ [1, 20]`, the computed
//!    `bb_root_of_unity(k)` has order exactly `2^k`.
//! 4. **Merkle tree correctness.** For random leaf sets, any leaf verifies
//!    against the computed root, and tampering breaks verification.
//! 5. **Plonky3 prover integrity.** For random Fibonacci trace heights,
//!    the prover produces a proof the verifier accepts; tampering any
//!    transition cell causes prover-side rejection.
//!
//! These tests are deliberately independent of Kani harnesses: proptest
//! explores concrete random values across many cases, whereas Kani
//! explores symbolic values over bounded unwinds.

use plonky3_hax::air::{fib_air, fib_trace, trace_valid};
use plonky3_hax::fri::{domain_element, fold_polynomial, fri_fold};
use plonky3_hax::plonky3::{plonky3_prove, plonky3_verify, Plonky3Proof};
use plonky3_hax::specs::baby_bear::*;
use plonky3_hax::specs::merkle::*;
use plonky3_hax::fri::FriOptions;
use proptest::prelude::*;

/// A Baby Bear field element in canonical form.
fn bb_element() -> impl Strategy<Value = u64> {
    (0u64..BABY_BEAR_PRIME).boxed()
}

/// A polynomial of up to `max_deg + 1` Baby Bear coefficients.
fn bb_polynomial(max_deg: usize) -> impl Strategy<Value = Vec<u64>> {
    prop::collection::vec(bb_element(), 1..=max_deg + 1)
}

// ========================================================================
// 1. Field axioms over random values
// ========================================================================

proptest! {
    #[test]
    fn prop_bb_add_commutative(a in bb_element(), b in bb_element()) {
        prop_assert_eq!(bb_add(a, b), bb_add(b, a));
    }

    #[test]
    fn prop_bb_mul_commutative(a in bb_element(), b in bb_element()) {
        prop_assert_eq!(bb_mul(a, b), bb_mul(b, a));
    }

    #[test]
    fn prop_bb_add_associative(
        a in bb_element(), b in bb_element(), c in bb_element()
    ) {
        prop_assert_eq!(bb_add(bb_add(a, b), c), bb_add(a, bb_add(b, c)));
    }

    #[test]
    fn prop_bb_mul_associative(
        a in bb_element(), b in bb_element(), c in bb_element()
    ) {
        prop_assert_eq!(bb_mul(bb_mul(a, b), c), bb_mul(a, bb_mul(b, c)));
    }

    #[test]
    fn prop_bb_distributive(
        a in bb_element(), b in bb_element(), c in bb_element()
    ) {
        prop_assert_eq!(
            bb_mul(a, bb_add(b, c)),
            bb_add(bb_mul(a, b), bb_mul(a, c))
        );
    }

    #[test]
    fn prop_bb_add_identity(a in bb_element()) {
        prop_assert_eq!(bb_add(a, 0), a);
    }

    #[test]
    fn prop_bb_mul_identity(a in bb_element()) {
        prop_assert_eq!(bb_mul(a, 1), a);
    }

    #[test]
    fn prop_bb_add_inverse(a in bb_element()) {
        prop_assert_eq!(bb_add(a, bb_neg(a)), 0);
    }

    #[test]
    fn prop_bb_mul_inverse(a in 1u64..BABY_BEAR_PRIME) {
        // Nonzero elements have multiplicative inverses.
        prop_assert_eq!(bb_mul(a, bb_inv(a)), 1);
    }

    #[test]
    fn prop_bb_sub_add_cancel(a in bb_element(), b in bb_element()) {
        prop_assert_eq!(bb_sub(bb_add(a, b), b), a);
    }
}

// ========================================================================
// 2. FRI fold/evaluate consistency
// ========================================================================

proptest! {
    #[test]
    fn prop_fri_fold_matches_folded_polynomial(
        coeffs in bb_polynomial(8),
        alpha in bb_element(),
        idx in 0u64..16,
    ) {
        // Use a domain of size 2^5 = 32 so idx is always valid.
        let domain_log2 = 5u32;
        let folded_coeffs = fold_polynomial(&coeffs, alpha);

        let x = domain_element(domain_log2, idx);
        prop_assume!(x != 0);
        let neg_x = bb_neg(x);

        let eval_pos = bb_poly_eval(&coeffs, x);
        let eval_neg = bb_poly_eval(&coeffs, neg_x);

        let via_fold = fri_fold(eval_pos, eval_neg, x, alpha);
        let direct = bb_poly_eval(&folded_coeffs, bb_square(x));

        prop_assert_eq!(via_fold, direct);
    }

    #[test]
    fn prop_fri_fold_constant_polynomial(
        c in bb_element(), x in 1u64..BABY_BEAR_PRIME, alpha in bb_element()
    ) {
        // Folding a constant gives the constant back.
        prop_assert_eq!(fri_fold(c, c, x, alpha), c);
    }
}

// ========================================================================
// 3. Roots of unity have the claimed order
// ========================================================================

proptest! {
    #[test]
    fn prop_root_of_unity_has_correct_order(k in 1u32..=20u32) {
        let omega = bb_root_of_unity(k);
        let order: u64 = 1u64 << k;
        prop_assert_eq!(bb_pow(omega, order), 1);
        prop_assert_eq!(bb_pow(omega, order >> 1), BABY_BEAR_PRIME - 1);
    }
}

// ========================================================================
// 4. Merkle tree correctness
// ========================================================================

proptest! {
    #[test]
    fn prop_merkle_roundtrip(
        leaves in prop::collection::vec(bb_element(), 2..=8),
        idx in 0usize..8,
    ) {
        // Round up leaf count to a power of two.
        let mut n = 1usize;
        while n < leaves.len() { n <<= 1; }
        let mut padded: Vec<MerkleHash> = leaves.iter()
            .map(|&v| hash_field_elem(v))
            .collect();
        while padded.len() < n {
            padded.push([0u8; HASH_SIZE]);
        }
        let idx_mod = idx % n;
        let (root, path) = merkle_build_and_prove(&padded, n, idx_mod);
        prop_assert!(merkle_verify_path(root, padded[idx_mod], idx_mod as u64, &path));
    }

    #[test]
    fn prop_merkle_wrong_leaf_rejected(
        leaves in prop::collection::vec(bb_element(), 4..=8),
        idx in 0usize..8,
        wrong in bb_element(),
    ) {
        let mut n = 1usize;
        while n < leaves.len() { n <<= 1; }
        let mut padded: Vec<MerkleHash> = leaves.iter()
            .map(|&v| hash_field_elem(v))
            .collect();
        while padded.len() < n {
            padded.push([0u8; HASH_SIZE]);
        }
        let idx_mod = idx % n;
        prop_assume!(leaves[idx_mod % leaves.len()] != wrong);
        let (root, path) = merkle_build_and_prove(&padded, n, idx_mod);
        // Substituting a different leaf must cause verification failure
        // (except with the negligible-probability event that the two
        // leaf hashes collide, which we treat as a bug if it triggers).
        let wrong_leaf = hash_field_elem(wrong);
        if wrong_leaf != padded[idx_mod] {
            prop_assert!(!merkle_verify_path(root, wrong_leaf, idx_mod as u64, &path));
        }
    }
}

// ========================================================================
// 5. Plonky3 prover/verifier on Fibonacci AIR
// ========================================================================

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

proptest! {
    // Plonky3 traces have power-of-two height (the FFT-based LDE needs
    // this). The proptests pick `log_h ∈ {1, 2, 3, 4, 5}` and use
    // `height = 1 << log_h`.

    #[test]
    fn prop_fib_prove_verify_roundtrip(log_h in 1u32..=5u32) {
        let height = 1usize << log_h;
        let air = fib_air();
        let trace = fib_trace(height);
        prop_assert!(trace_valid(&air, &trace));

        let proof: Plonky3Proof =
            plonky3_prove(&air, &trace, default_options())
                .expect("prover rejected a valid trace");
        let alphas: Vec<Vec<u64>> = vec![vec![], vec![]];
        prop_assert!(plonky3_verify(&air, &proof, &alphas, default_options()));
    }

    #[test]
    fn prop_fib_tampered_trace_rejected(
        log_h in 2u32..=4u32,
        row_offset in 1usize..4,
        tamper in 1u64..BABY_BEAR_PRIME,
    ) {
        let height = 1usize << log_h;
        let air = fib_air();
        let mut trace = fib_trace(height);
        let row = row_offset.min(trace.height - 1);
        trace.set(row, 1, bb_add(trace.get(row, 1), tamper));
        // Any nonzero tamper breaks the Fibonacci transition, so the
        // prover must reject.
        prop_assert!(plonky3_prove(&air, &trace, default_options()).is_none());
    }

    #[test]
    fn prop_fib_boundary_claim_binding(
        log_h in 2u32..=4u32,
        col in 0usize..=1,
        tamper in 1u64..BABY_BEAR_PRIME,
    ) {
        let height = 1usize << log_h;
        let air = fib_air();
        let trace = fib_trace(height);
        let mut proof = plonky3_prove(&air, &trace, default_options())
            .expect("prover");
        // Flip a boundary claim.
        proof.boundary_claims[col] = bb_add(proof.boundary_claims[col], tamper);
        let alphas: Vec<Vec<u64>> = vec![vec![], vec![]];
        prop_assert!(!plonky3_verify(&air, &proof, &alphas, default_options()));
    }
}
