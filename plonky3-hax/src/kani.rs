//! Kani harnesses for plonky3-hax, compiled only under `cfg(kani)`.
//!
//! The harnesses check:
//!
//! 1. absence of panics and arithmetic overflow for the field operations and
//!    for the FRI, Merkle and hash functions, on symbolic canonical inputs,
//!    with bounded exponents or fixed small domain sizes where marked;
//! 2. with the `kani-equiv` feature, equality of `specs::baby_bear` with the
//!    Montgomery-form field of `p3-baby-bear` 0.5 on symbolic canonical
//!    inputs;
//! 3. index identities (`sibling_index`, `folded_index`) and Merkle
//!    round-trips at fixed small sizes, and one prove/verify round-trip of
//!    the Fibonacci AIR.
//!
//! Algebraic identities of the field (commutativity, distributivity,
//! inverses) are not checked here.

#[cfg(kani)]
mod kani_harnesses {
    use crate::air::*;
    use crate::fri::*;
    use crate::specs::baby_bear::*;
    use crate::specs::merkle::*;

    // Any u64 value reduced into canonical [0, p) form. Kani explores the
    // full non-symbolic range of u64, so we constrain to the field.
    fn bb_any() -> u64 {
        let v: u64 = kani::any();
        kani::assume(v < BABY_BEAR_PRIME);
        v
    }

    // =========================================================
    // 1. Panic-freedom for Baby Bear arithmetic
    // =========================================================

    #[kani::proof]
    fn bb_add_panic_free() {
        let a = bb_any();
        let b = bb_any();
        let _ = bb_add(a, b);
    }

    #[kani::proof]
    fn bb_sub_panic_free() {
        let a = bb_any();
        let b = bb_any();
        let _ = bb_sub(a, b);
    }

    #[kani::proof]
    fn bb_neg_panic_free() {
        let a = bb_any();
        let _ = bb_neg(a);
    }

    #[kani::proof]
    fn bb_mul_panic_free() {
        let a = bb_any();
        let b = bb_any();
        let _ = bb_mul(a, b);
    }

    #[kani::proof]
    fn bb_square_panic_free() {
        let a = bb_any();
        let _ = bb_square(a);
    }

    #[kani::proof]
    #[kani::unwind(68)]
    fn bb_pow_panic_free_small_exp() {
        let base = bb_any();
        let exp: u64 = kani::any();
        // Bound the exponent bitwidth to keep the proof tractable.
        kani::assume(exp <= 0xFF);
        let _ = bb_pow(base, exp);
    }

    #[kani::proof]
    #[kani::unwind(68)]
    fn bb_inv_panic_free() {
        let a = bb_any();
        let _ = bb_inv(a);
    }

    #[kani::proof]
    #[kani::unwind(68)]
    fn bb_div_panic_free() {
        let a = bb_any();
        let b = bb_any();
        let _ = bb_div(a, b);
    }

    #[kani::proof]
    #[kani::unwind(68)]
    fn bb_root_of_unity_panic_free() {
        let k: u32 = kani::any();
        kani::assume(k <= 27);
        let _ = bb_root_of_unity(k);
    }

    #[kani::proof]
    fn bb_poly_eval_panic_free_small() {
        let c0 = bb_any();
        let c1 = bb_any();
        let c2 = bb_any();
        let x = bb_any();
        let coeffs = [c0, c1, c2];
        let _ = bb_poly_eval(&coeffs, x);
    }

    // =========================================================
    // 2. Panic-freedom for FRI / Merkle / hash primitives
    // =========================================================

    #[kani::proof]
    #[kani::unwind(68)]
    fn fri_fold_panic_free() {
        let pos = bb_any();
        let neg = bb_any();
        let x = bb_any();
        kani::assume(x != 0);
        let alpha = bb_any();
        let _ = fri_fold(pos, neg, x, alpha);
    }

    #[kani::proof]
    fn folded_index_panic_free() {
        let log2: u32 = 4;
        let n: u64 = 1u64 << log2;
        let i: u64 = kani::any();
        kani::assume(i < n);
        let _ = folded_index(i, log2);
    }

    #[kani::proof]
    #[kani::unwind(68)]
    fn domain_element_panic_free() {
        let log2: u32 = 4;
        let n: u64 = 1u64 << log2;
        let i: u64 = kani::any();
        kani::assume(i < n);
        let _ = domain_element(log2, i);
    }

    #[kani::proof]
    fn hash_field_elem_panic_free() {
        let v = bb_any();
        let _ = hash_field_elem(v);
    }

    #[kani::proof]
    fn hash_two_to_one_panic_free() {
        let l: MerkleHash = kani::any();
        let r: MerkleHash = kani::any();
        let _ = hash_two_to_one(l, r);
    }

    #[kani::proof]
    fn hash_leaf_panic_free() {
        let b: [u8; 8] = kani::any();
        let _ = hash_leaf(b);
    }

    #[kani::proof]
    fn field_elem_to_bytes_panic_free() {
        let v = bb_any();
        let _ = field_elem_to_bytes(v);
    }

    // =========================================================
    // 3. Structural sanity (cheap, fixed-size)
    // =========================================================

    #[kani::proof]
    fn sibling_index_involution() {
        let log2: u32 = 4;
        let n: u64 = 1u64 << log2;
        let i: u64 = kani::any();
        kani::assume(i < n);
        assert_eq!(sibling_index(sibling_index(i, log2), log2), i);
    }

    #[kani::proof]
    fn sibling_index_is_in_domain() {
        let log2: u32 = 4;
        let n: u64 = 1u64 << log2;
        let i: u64 = kani::any();
        kani::assume(i < n);
        let s = sibling_index(i, log2);
        assert!(s < n);
    }

    // Bit-twiddling equivalences: ADD-AND-MASK form vs algebraic
    // characterizations. Cheap (small symbolic-bit count) and exactly
    // the kind of thing CBMC excels at.

    #[kani::proof]
    fn equiv_sibling_index_xor() {
        // sibling_index(i, log2) = (i + n/2) & (n-1)  [the impl]
        //                        = i XOR (n/2)        [the algebraic spec]
        // for any i < n. Proves the two characterizations agree.
        let log2: u32 = 4;
        let n: u64 = 1u64 << log2;
        let half: u64 = 1u64 << (log2 - 1);
        let i: u64 = kani::any();
        kani::assume(i < n);
        assert_eq!(sibling_index(i, log2), i ^ half);
    }

    #[kani::proof]
    fn equiv_folded_index_branchless() {
        // folded_index(i, log2) = i & (n/2 - 1)             [the impl]
        //                       = if i < n/2 { i } else { i - n/2 }  [algebraic]
        // The branched form is the natural cosetting view; the masked form
        // is the optimized branchless one. Proves they match.
        let log2: u32 = 4;
        let n: u64 = 1u64 << log2;
        let half: u64 = 1u64 << (log2 - 1);
        let i: u64 = kani::any();
        kani::assume(i < n);
        let branched = if i < half { i } else { i - half };
        assert_eq!(folded_index(i, log2), branched);
    }

    #[kani::proof]
    fn folded_index_within_half() {
        let log2: u32 = 4;
        let n: u64 = 1u64 << log2;
        let half: u64 = 1u64 << (log2 - 1);
        let i: u64 = kani::any();
        kani::assume(i < n);
        let f = folded_index(i, log2);
        assert!(f < half);
    }

    #[kani::proof]
    #[kani::unwind(33)]
    fn merkle_single_leaf_verifies() {
        let v = bb_any();
        let leaf = hash_field_elem(v);
        let path = MerklePath {
            siblings: [[0u8; HASH_SIZE]; MAX_MERKLE_DEPTH],
            depth: 0,
        };
        assert!(merkle_verify_path(leaf, leaf, 0, &path));
    }

    #[kani::proof]
    #[kani::unwind(33)]
    fn merkle_two_leaf_roundtrip() {
        let v0 = bb_any();
        let v1 = bb_any();
        let leaf0 = hash_field_elem(v0);
        let leaf1 = hash_field_elem(v1);
        let root = hash_two_to_one(leaf0, leaf1);

        let mut path0 = MerklePath {
            siblings: [[0u8; HASH_SIZE]; MAX_MERKLE_DEPTH],
            depth: 1,
        };
        path0.siblings[0] = leaf1;
        assert!(merkle_verify_path(root, leaf0, 0, &path0));
    }

    // =========================================================
    // 4. Plonky3 protocol roundtrip (Fibonacci AIR, fixed height)
    // =========================================================

    #[kani::proof]
    #[kani::unwind(34)]
    fn plonky3_fibonacci_prove_verify_roundtrip_h4() {
        let air = fib_air();
        let trace = fib_trace(4);
        let opts = FriOptions {
            num_layers: 2,
            domain_log2: 3,
            num_queries: 4,
            blowup: 2,
            coset_shift: crate::plonky3::LDE_COSET_SHIFT,
            proof_of_work_bits: 0,
        };
        let proof = crate::plonky3::plonky3_prove(&air, &trace, opts)
            .expect("prover must accept a valid Fibonacci trace");
        let alphas: [Vec<u64>; 0] = [];
        assert!(crate::plonky3::plonky3_verify(
            &air, &proof, &[vec![], vec![]], opts
        ));
        let _ = alphas;
    }

    // =========================================================
    // 5. Equivalence with the Montgomery-form field of `p3-baby-bear`.
    //
    //    Each harness lifts canonical `u64` representatives into the
    //    upstream `BabyBear` type, runs the operation, projects back with
    //    `as_canonical_u32`, and asserts equality with `specs::baby_bear`.
    //    The module is gated behind the `kani-equiv` feature, so that a
    //    plain build does not depend on the Plonky3 crates.
    // =========================================================

    #[cfg(feature = "kani-equiv")]
    mod equiv {
        use super::bb_any;
        use crate::specs::baby_bear::*;
        use p3_baby_bear::BabyBear;
        use p3_field::{Field, PrimeCharacteristicRing, PrimeField32};

        fn lift(v: u64) -> BabyBear {
            BabyBear::new(v as u32)
        }

        fn project(x: BabyBear) -> u64 {
            x.as_canonical_u32() as u64
        }

        #[kani::proof]
        fn equiv_bb_add() {
            let a = bb_any();
            let b = bb_any();
            let ours = bb_add(a, b);
            let theirs = project(lift(a) + lift(b));
            assert_eq!(ours, theirs);
        }

        #[kani::proof]
        fn equiv_bb_sub() {
            let a = bb_any();
            let b = bb_any();
            let ours = bb_sub(a, b);
            let theirs = project(lift(a) - lift(b));
            assert_eq!(ours, theirs);
        }

        #[kani::proof]
        fn equiv_bb_neg() {
            let a = bb_any();
            let ours = bb_neg(a);
            let theirs = project(-lift(a));
            assert_eq!(ours, theirs);
        }

        #[kani::proof]
        fn equiv_bb_mul() {
            let a = bb_any();
            let b = bb_any();
            let ours = bb_mul(a, b);
            let theirs = project(lift(a) * lift(b));
            assert_eq!(ours, theirs);
        }

        #[kani::proof]
        fn equiv_bb_square() {
            let a = bb_any();
            let ours = bb_square(a);
            let theirs = project(lift(a) * lift(a));
            assert_eq!(ours, theirs);
        }

        #[kani::proof]
        #[kani::unwind(68)]
        fn equiv_bb_pow_small() {
            // Reference (ours): square-and-multiply on canonical u64 reps.
            // Upstream: Montgomery-form exp_u64. Bounded exponent for
            // tractability.
            let base = bb_any();
            let exp: u64 = kani::any();
            kani::assume(exp <= 0xFF);
            let ours = bb_pow(base, exp);
            let theirs = project(lift(base).exp_u64(exp));
            assert_eq!(ours, theirs);
        }

        #[kani::proof]
        #[kani::unwind(68)]
        fn equiv_bb_inv() {
            // Fermat-style inverse on canonical u64 vs upstream extended-
            // Euclidean inverse. Expensive: bb_inv internally calls
            // bb_pow with exponent p - 2 ≈ 2^31, so kani must unwind the
            // square-and-multiply loop fully (64 iterations).
            let a = bb_any();
            kani::assume(a != 0);
            let ours = bb_inv(a);
            let theirs = project(lift(a).try_inverse().expect("nonzero has inverse"));
            assert_eq!(ours, theirs);
        }

        #[kani::proof]
        fn equiv_bb_poly_eval_horner_vs_monomial_sum() {
            // Horner-form polynomial evaluation (ours) vs explicit
            // sum-of-monomials computed in the upstream field type
            // (theirs). Fixed 3-coefficient polynomial keeps the proof
            // tractable.
            let c0 = bb_any();
            let c1 = bb_any();
            let c2 = bb_any();
            let x = bb_any();
            let ours = bb_poly_eval(&[c0, c1, c2], x);
            let xb = lift(x);
            let theirs = project(lift(c0) + lift(c1) * xb + lift(c2) * xb * xb);
            assert_eq!(ours, theirs);
        }
    }
}
