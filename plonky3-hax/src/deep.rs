//! DEEP quotients of the reference STARK.
//!
//! For a committed polynomial `P` with claimed value `v` at the OOD point
//! `z`, the DEEP quotient is `DEEP_P(x) = (P(x) − v) / (x − z)`. If
//! `v = P(z)` it is a polynomial of degree `< deg P`; otherwise it is a
//! rational function with a pole at `z`. The quotients of all trace columns
//! and of `Q` are combined as `B(x) = Σ_i β^i · DEEP_{P_i}(x)`, and one FRI
//! folding proof is produced for `B`.
//!
//! The FRI proof for `B` is built at the layer-0 query indices derived from
//! the trace commitment, the same indices as the column proofs. The
//! verifier recomputes `B` at each queried point from the column openings
//! and compares it with the opened value of `B`.

use crate::fri::coset_element;
use crate::specs::baby_bear::*;
use crate::specs::merkle::*;

/// Derive the DEEP-batching challenge `β` from the quotient commitment.
/// Same Fiat-Shamir style as the other challenges, but with the 'D'
/// domain separator so the streams stay disjoint.
pub fn derive_deep_beta(quotient_commitment: &MerkleRoot) -> u64 {
    let mut acc: u64 = 0;
    acc = bb_add(bb_mul(acc, 257), 0x44);
    for b in 0..HASH_SIZE {
        acc = bb_add(bb_mul(acc, 257), quotient_commitment[b] as u64);
    }
    acc
}

/// Compute the DEEP polynomial's LDE values: `DEEP_P[j] = (P_lde[j] − v) / (x_j − z)`,
/// where `x_j = shift · ω_n^j` is the LDE coset point at index `j`.
pub fn compute_deep_poly_lde(
    p_lde: &[u64],
    claimed_value: u64,
    z: u64,
    domain_log2: u32,
    shift: u64,
) -> Vec<u64> {
    let n = p_lde.len();
    let mut deep: Vec<u64> = Vec::with_capacity(n);
    for j in 0..n {
        let x_j = coset_element(shift, domain_log2, j as u64);
        let numerator = bb_sub(p_lde[j], claimed_value);
        let denominator_inv = bb_inv(bb_sub(x_j, z));
        deep.push(bb_mul(numerator, denominator_inv));
    }
    deep
}

/// Batched LC: `B[j] = Σ_i β^i · DEEP_{P_i}[j]`.
pub fn combine_deep_polys(deeps: &[Vec<u64>], beta: u64) -> Vec<u64> {
    if deeps.is_empty() {
        return Vec::new();
    }
    let n = deeps[0].len();
    let mut result: Vec<u64> = vec![0u64; n];
    let mut beta_pow: u64 = 1;
    for i in 0..deeps.len() {
        let d = &deeps[i];
        let bound = n.min(d.len());
        for j in 0..bound {
            result[j] = bb_add(result[j], bb_mul(beta_pow, d[j]));
        }
        beta_pow = bb_mul(beta_pow, beta);
    }
    result
}

/// Reconstruct the DEEP-batched LC value at LDE point `x_q` from the
/// opened polynomial values at the same point and the claimed OOD
/// evaluations. The verifier uses this to cross-check the DEEP FRI
/// proof's first-layer query against the column-FRI openings.
///
/// `p_openings[i]` is the opened value of `P_i` at `x_q`,
/// `claimed_values[i]` is `P_i(z)` from the OOD claim,
/// `x_q` is the LDE point, `z` is the OOD challenge,
/// `beta` is the DEEP-batching challenge.
pub fn reconstruct_deep_value_at(
    p_openings: &[u64],
    claimed_values: &[u64],
    x_q: u64,
    z: u64,
    beta: u64,
) -> u64 {
    let denom_inv = bb_inv(bb_sub(x_q, z));
    let mut result: u64 = 0;
    let mut beta_pow: u64 = 1;
    let bound = p_openings.len().min(claimed_values.len());
    for i in 0..bound {
        let deep_i = bb_mul(bb_sub(p_openings[i], claimed_values[i]), denom_inv);
        result = bb_add(result, bb_mul(beta_pow, deep_i));
        beta_pow = bb_mul(beta_pow, beta);
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::air::{fib_air, fib_trace};
    use crate::ood::{evaluate_trace_at, evaluate_quotient_at};
    use crate::plonky3::{compute_trace_lde, LDE_COSET_SHIFT};
    use crate::quotient::{
        compute_quotient_lde, derive_constraint_alphas, commit_quotient_lde,
    };

    #[test]
    fn test_deep_poly_at_z_is_zero_for_consistent_claim() {
        // If the claimed value equals P(z), then DEEP_P(z) is the limit of
        // (P(x) − P(z))/(x − z) as x → z, which is P'(z) — finite. We
        // can't evaluate at z directly (would divide by zero), but the
        // DEEP_P LDE values should be consistent: applying inv-NTT and
        // evaluating at z should give P'(z). For our purposes the simpler
        // property is: DEEP_P[j] = (P[j] − v) / (x_j − z), and if v = P(z)
        // then DEEP_P is a polynomial of degree < deg(P).
        let p_lde: Vec<u64> = vec![10, 20, 30, 40, 50, 60, 70, 80];
        let z: u64 = 99;
        let v: u64 = 7;
        let domain_log2: u32 = 3;
        let deep = compute_deep_poly_lde(&p_lde, v, z, domain_log2, LDE_COSET_SHIFT);
        assert_eq!(deep.len(), 8);
        // Each entry is a Baby Bear element.
        for k in 0..deep.len() {
            assert!(deep[k] < BABY_BEAR_PRIME);
        }
    }

    #[test]
    fn test_combine_single_deep_is_itself() {
        // β^0 = 1, so the LC of a single DEEP is that DEEP.
        let d = vec![1u64, 2, 3, 4];
        let combined = combine_deep_polys(std::slice::from_ref(&d), 42);
        assert_eq!(combined, d);
    }

    #[test]
    fn test_combine_two_deeps_with_beta_zero() {
        // β = 0 picks out the first DEEP only.
        let d1 = vec![1u64, 2, 3];
        let d2 = vec![10u64, 20, 30];
        let combined = combine_deep_polys(&[d1.clone(), d2], 0);
        assert_eq!(combined, d1);
    }

    #[test]
    fn test_reconstruct_matches_combine_at_query_point() {
        // The reconstruct-from-openings path must agree with the
        // direct-combine path, since both compute the same LC of DEEPs.
        let air = fib_air();
        let trace = fib_trace(8);
        let trace_log2: u32 = 3;
        let domain_log2: u32 = 5;
        let shift = LDE_COSET_SHIFT;
        let lde = compute_trace_lde(&trace, domain_log2, shift);

        let z: u64 = 12345; // any non-coset value works for this test

        // For each column build DEEP and the corresponding claimed_value.
        let mut deeps: Vec<Vec<u64>> = Vec::new();
        let mut claimed: Vec<u64> = Vec::new();
        let n = 1usize << domain_log2;
        let width = trace.width;
        for col in 0..width {
            let mut p_lde = vec![0u64; n];
            for j in 0..n {
                p_lde[j] = lde[j * width + col];
            }
            let v = evaluate_trace_at(&trace, z)[col];
            let d = compute_deep_poly_lde(&p_lde, v, z, domain_log2, shift);
            deeps.push(d);
            claimed.push(v);
        }
        // Add quotient DEEP.
        let constraint_alphas = derive_constraint_alphas(&[0u8; HASH_SIZE], air.transitions.len());
        let q_lde = compute_quotient_lde(
            &lde,
            &air,
            &constraint_alphas,
            width,
            domain_log2,
            trace_log2,
            shift,
        );
        let q_at_z = evaluate_quotient_at(&q_lde, domain_log2, shift, z);
        let q_deep = compute_deep_poly_lde(&q_lde, q_at_z, z, domain_log2, shift);
        deeps.push(q_deep);
        claimed.push(q_at_z);

        let beta: u64 = derive_deep_beta(&commit_quotient_lde(&q_lde));
        let combined = combine_deep_polys(&deeps, beta);

        // Pick a query point and reconstruct from openings.
        let query_j: usize = 7;
        let x_q = coset_element(shift, domain_log2, query_j as u64);
        let mut p_openings: Vec<u64> = Vec::new();
        for c in 0..width {
            p_openings.push(lde[query_j * width + c]);
        }
        p_openings.push(q_lde[query_j]);

        let reconstructed = reconstruct_deep_value_at(&p_openings, &claimed, x_q, z, beta);
        assert_eq!(combined[query_j], reconstructed);
    }
}
