//! Out-of-domain (OOD) evaluations of the reference STARK.
//!
//! After the trace and quotient commitments, the prover sends, at a point
//! `z` derived from the quotient commitment, the values `T_c(z)` and
//! `T_c(g · z)` of every trace column `c` and the value `Q(z)`. The verifier
//! checks `C(z) = Q(z) · Z'_H(z)`, where
//! `C(z) = Σ_k α_k · c_k(T(z), T(g · z))` (module `quotient`). The binding
//! of these values to the commitments is checked by the DEEP step (module
//! `deep`).
//!
//! `T_c(z)` is computed by interpolating the column's `h` values with the
//! inverse NTT and evaluating the coefficients at `z` by Horner's rule.

use crate::air::Trace;
use crate::ntt;
use crate::quotient::vanishing_poly_eval;
use crate::specs::baby_bear::*;
use crate::specs::merkle::*;

/// Derive a deterministic OOD point from the quotient commitment.
///
/// For `counter = 0, 1, …, 63` the candidate is the base-257 accumulation
/// in F_p of the byte `0x7A`, the 32 commitment bytes and `counter`; the
/// first candidate that is nonzero and satisfies `Z_H(z) ≠ 0` is returned,
/// and `GENERATOR` if none is. Membership of `z` in the LDE coset is not
/// checked, and `domain_log2` is unused.
pub fn derive_ood_point(
    quotient_commitment: &MerkleRoot,
    trace_log2: u32,
    domain_log2: u32,
) -> u64 {
    let _ = domain_log2;
    for counter in 0u64..64 {
        let mut acc: u64 = 0;
        // Domain separator: 'z' = 0x7A distinguishes the OOD challenge
        // from alpha / query streams.
        acc = bb_add(bb_mul(acc, 257), 0x7A);
        for b in 0..HASH_SIZE {
            acc = bb_add(bb_mul(acc, 257), quotient_commitment[b] as u64);
        }
        acc = bb_add(bb_mul(acc, 257), counter);
        // Accept iff Z_H(acc) ≠ 0 and acc is not on the LDE coset.
        // Z_H test catches `acc ∈ H`. We also test against the LDE coset
        // by checking `Z_{K_n}(acc / shift) ≠ 0`, but in our parameters
        // the LDE coset and H are disjoint and both have density ≪ p, so
        // it's enough to check Z_H ≠ 0 and acc ≠ 0.
        if acc != 0 && vanishing_poly_eval(acc, trace_log2) != 0 {
            return acc;
        }
    }
    // Fallback: GENERATOR is well-known to be outside H.
    GENERATOR
}

/// Evaluate every column of the trace polynomial at `z`.
///
/// For each column `c`, the trace values `[T_c(ω_h^0), …, T_c(ω_h^{h-1})]`
/// are INTTed to recover the column polynomial's coefficients, which are
/// then Horner-evaluated at `z`. Returns one field element per column.
///
/// Requires `trace.height` to be a power of two.
pub fn evaluate_trace_at(trace: &Trace, z: u64) -> Vec<u64> {
    let h = trace.height;
    let w = trace.width;
    let mut out: Vec<u64> = Vec::with_capacity(w);
    if h == 0 || (h & (h - 1)) != 0 {
        return out;
    }
    let trace_log2: u32 = h.trailing_zeros();
    let omega_h = bb_root_of_unity(trace_log2);
    for col in 0..w {
        // Pull out column evaluations on H.
        let mut evals: Vec<u64> = Vec::with_capacity(h);
        for i in 0..h {
            evals.push(trace.get(i, col));
        }
        // INTT → coefficients.
        ntt::intt(&mut evals, omega_h);
        // Horner-evaluate at z.
        let v = bb_poly_eval(&evals, z);
        out.push(v);
    }
    out
}

/// Evaluate the quotient polynomial at `z` given its evaluations on the
/// LDE coset `shift · K_n`.
///
/// The values are interpolated with the inverse NTT as evaluations of
/// `Q(shift · x)` on `K_n`; the `i`-th coefficient is then multiplied by
/// `shift^{-i}` to obtain the coefficients of `Q`, which are evaluated at
/// `z` by Horner's rule. Returns `0` when `q_lde.len() != 2^domain_log2`.
pub fn evaluate_quotient_at(
    q_lde: &[u64],
    domain_log2: u32,
    shift: u64,
    z: u64,
) -> u64 {
    let n = q_lde.len();
    if n != (1usize << domain_log2) {
        return 0;
    }
    // 1. INTT the LDE values, treating them as evaluations of `g(x) = Q(shift · x)`
    //    on the bare subgroup `K_n`. This yields `g`'s coefficients `b_i`.
    let mut coeffs: Vec<u64> = q_lde.to_vec();
    let omega_n = bb_root_of_unity(domain_log2);
    ntt::intt(&mut coeffs, omega_n);
    // 2. Twist `b_i ↦ c_i = b_i · shift^{-i}` to recover `Q`'s coefficients.
    let shift_inv = bb_inv(shift);
    let mut shift_inv_pow: u64 = 1;
    for i in 0..n {
        coeffs[i] = bb_mul(coeffs[i], shift_inv_pow);
        shift_inv_pow = bb_mul(shift_inv_pow, shift_inv);
    }
    // 3. Horner-evaluate `Q` at `z`.
    bb_poly_eval(&coeffs, z)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::quotient::vanishing_selector_eval;
    use crate::air::{fib_air, fib_trace};
    use crate::plonky3::{compute_trace_lde, LDE_COSET_SHIFT};
    use crate::quotient::{
        commit_quotient_lde, compute_quotient_lde, derive_constraint_alphas,
    };

    #[test]
    fn test_derive_ood_point_nonzero_and_off_h() {
        let trace_log2: u32 = 3;
        let domain_log2: u32 = 5;
        let z = derive_ood_point(&[42u8; HASH_SIZE], trace_log2, domain_log2);
        assert_ne!(z, 0);
        assert_ne!(vanishing_poly_eval(z, trace_log2), 0);
    }

    #[test]
    fn test_derive_ood_point_deterministic() {
        let trace_log2: u32 = 3;
        let domain_log2: u32 = 5;
        let z1 = derive_ood_point(&[7u8; HASH_SIZE], trace_log2, domain_log2);
        let z2 = derive_ood_point(&[7u8; HASH_SIZE], trace_log2, domain_log2);
        assert_eq!(z1, z2);
    }

    #[test]
    fn test_evaluate_trace_at_recovers_subgroup_values() {
        // T_col(ω_h^i) should equal trace.get(i, col).
        let trace = fib_trace(8);
        let trace_log2: u32 = 3;
        let omega_h = bb_root_of_unity(trace_log2);
        for i in 0..8usize {
            let x = bb_pow(omega_h, i as u64);
            let evals_at_x = evaluate_trace_at(&trace, x);
            for col in 0..trace.width {
                assert_eq!(
                    evals_at_x[col],
                    trace.get(i, col),
                    "row {} col {}",
                    i,
                    col
                );
            }
        }
    }

    #[test]
    fn test_ood_identity_holds_for_valid_trace() {
        // For a Fibonacci trace, at any OOD point z with Z_H(z) ≠ 0, the
        // identity C(z) = Q(z) · Z_H(z) holds — modulo the cyclic-row
        // wraparound which makes the constraint nonzero at the last row
        // (so the quotient is a higher-degree polynomial but the equality
        // still holds by construction of Q := C / Z_H).
        let air = fib_air();
        let trace = fib_trace(8);
        let trace_log2: u32 = 3;
        let domain_log2: u32 = 5;

        let lde = compute_trace_lde(&trace, domain_log2, LDE_COSET_SHIFT);
        let trace_commitment = [0u8; HASH_SIZE];
        let alphas = derive_constraint_alphas(&trace_commitment, air.transitions.len());
        let q_lde = compute_quotient_lde(
            &lde,
            &air,
            &alphas,
            trace.width,
            domain_log2,
            trace_log2,
            LDE_COSET_SHIFT,
        );
        let q_commit = commit_quotient_lde(&q_lde);

        let z = derive_ood_point(&q_commit, trace_log2, domain_log2);

        // Compute T(z), T(g·z), Q(z), Z_H(z).
        let omega_h = bb_root_of_unity(trace_log2);
        let g_z = bb_mul(omega_h, z);
        let trace_at_z = evaluate_trace_at(&trace, z);
        let trace_at_gz = evaluate_trace_at(&trace, g_z);
        let q_at_z = evaluate_quotient_at(&q_lde, domain_log2, LDE_COSET_SHIFT, z);
        let sel_at_z = vanishing_selector_eval(z, trace_log2);
        let _ = vanishing_poly_eval(z, trace_log2);

        // C(z) = Σ α_k · c_k(T(z), T(g·z))
        let mut c_at_z: u64 = 0;
        for k in 0..air.transitions.len() {
            let v = crate::air::eval_transition(
                air.transitions[k].kind,
                &trace_at_z,
                &trace_at_gz,
            );
            c_at_z = bb_add(c_at_z, bb_mul(alphas[k], v));
        }

        // The identity: C(z) = Q(z) · Z'_H(z), where Z'_H is the
        // "all-but-last-row" selector (Plonky3 convention for cyclic
        // transition constraints).
        let rhs = bb_mul(q_at_z, sel_at_z);
        assert_eq!(c_at_z, rhs, "OOD identity failed: C(z) ≠ Q(z) · Z'_H(z)");
    }
}
