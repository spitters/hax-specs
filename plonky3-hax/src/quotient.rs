//! Quotient polynomial of the reference STARK.
//!
//! Let `T` be the trace polynomial of degree `< h = trace.height` and
//! `c_k(T(x), T(g·x))` the transition constraints, with `g = ω_h`. For a
//! valid trace the combination `C = Σ_k α_k · c_k` vanishes on the rows
//! `ω_h^0, …, ω_h^{h-2}` of the trace subgroup `H`, so it is divisible by
//! the selector `Z'_H(x) = (x^h − 1) / (x − ω_h^{h-1})`, and the quotient
//! `Q = C / Z'_H` is a polynomial. Dividing by `Z'_H` is the same as
//! multiplying the constraints by Plonky3's `is_transition` selector
//! `x − ω_h^{h-1}` and dividing by `Z_H(x) = x^h − 1`.
//!
//! The prover evaluates `Q` on the LDE coset `shift · K_n` and commits to
//! the values; the verifier checks `C(z) = Q(z) · Z'_H(z)` at the
//! out-of-domain point `z` (module `ood`).
//!
//! - `vanishing_poly_eval`: `Z_H(x) = x^h − 1`.
//! - `vanishing_selector_eval`: `Z'_H(x)`.
//! - `derive_constraint_alphas`: the challenges `α_k`, computed from the
//!   trace commitment bytes.
//! - `compute_constraint_lde_value`: `C` at one LDE coset point.
//! - `compute_quotient_lde`: `Q` at every LDE coset point.
//! - `commit_quotient_lde`: the Merkle root over those values.
//!
//! Boundary constraints are not part of `C`; the verifier compares the
//! prover's boundary claims with the AIR directly.

use crate::air::AirSpec;
use crate::specs::baby_bear::*;
use crate::specs::merkle::*;

/// Vanishing polynomial `Z_H(x) = x^h − 1`, where `h = 2^trace_log2`.
/// Zero exactly on the trace subgroup `H = {ω_h^0, …, ω_h^{h-1}}`.
pub fn vanishing_poly_eval(x: u64, trace_log2: u32) -> u64 {
    let h: u64 = 1u64 << trace_log2;
    bb_sub(bb_pow(x, h), 1)
}

/// Inverse of the vanishing polynomial, defined only when `x ∉ H`. The
/// caller is responsible for that precondition; on `H`, `Z_H` is zero
/// and `bb_inv` returns 0 (the canonical "undefined" sentinel).
pub fn vanishing_poly_inv(x: u64, trace_log2: u32) -> u64 {
    bb_inv(vanishing_poly_eval(x, trace_log2))
}

/// "All-but-last-row" selector
/// `Z'_H(x) = Z_H(x) / (x − ω_h^{h-1})`, which is zero exactly on the
/// rows `0 .. h-2` and nonzero at row `h-1`.
///
/// Plonky3's quotient uses this selector instead of the full `Z_H`
/// because for cyclic AIRs (like Fibonacci) the transition constraint
/// is only required to vanish on the first `h-1` rows; the wraparound
/// at row `h-1` is not required, and dividing by `Z_H` would force
/// the prover to satisfy a stricter condition than the AIR demands.
///
/// Computed without polynomial long-division:
/// `Z'_H(x) = (x^h − 1) / (x − ω_h^{h-1})`.
/// At `x ∉ H`, `Z_H(x) ≠ 0` and `(x − ω_h^{h-1}) ≠ 0`, so the division
/// is well-defined in the field.
pub fn vanishing_selector_eval(x: u64, trace_log2: u32) -> u64 {
    let omega_h = bb_root_of_unity(trace_log2);
    let h: u64 = 1u64 << trace_log2;
    // ω_h^{h-1} = ω_h^{-1} (since ω_h has order h).
    let omega_last = bb_pow(omega_h, h - 1);
    bb_mul(
        vanishing_poly_eval(x, trace_log2),
        bb_inv(bb_sub(x, omega_last)),
    )
}

/// Inverse of `vanishing_selector_eval`, defined when `x ∉ {ω_h^0, …, ω_h^{h-2}}`.
pub fn vanishing_selector_inv(x: u64, trace_log2: u32) -> u64 {
    bb_inv(vanishing_selector_eval(x, trace_log2))
}

/// Derive `num_constraints` deterministic random challenges for the
/// constraint LC, mixed from the trace commitment bytes. Same hash-style
/// derivation as `derive_fri_alphas`, but with a distinct domain
/// separator (`"C"` byte before each constraint index) so the FRI and
/// quotient challenge streams don't collide.
pub fn derive_constraint_alphas(
    trace_commitment: &MerkleRoot,
    num_constraints: usize,
) -> Vec<u64> {
    let mut result: Vec<u64> = Vec::with_capacity(num_constraints);
    for k in 0..num_constraints {
        let mut acc: u64 = 0;
        // Domain separator: 'C' = 0x43 distinguishes from FRI's no-prefix
        // alphas and the query-index byte stream.
        acc = bb_add(bb_mul(acc, 257), 0x43);
        for b in 0..HASH_SIZE {
            let v = trace_commitment[b] as u64;
            acc = bb_add(bb_mul(acc, 257), v);
        }
        acc = bb_add(bb_mul(acc, 257), k as u64);
        result.push(acc);
    }
    result
}

/// Helper: read row `j` of the LDE as a `Vec<u64>` of length `width`.
fn lde_row(lde: &[u64], j: usize, width: usize) -> Vec<u64> {
    let mut r: Vec<u64> = Vec::with_capacity(width);
    for c in 0..width {
        r.push(lde[j * width + c]);
    }
    r
}

/// Evaluate the linear combination of AIR transition constraints at LDE
/// row `j`. The "next row" for transition purposes is row `j + n/h`
/// (mod n), since the trace shift `g = ω_h` corresponds to a stride of
/// `n/h` in the LDE indexing.
pub fn compute_constraint_lde_value(
    lde: &[u64],
    j: usize,
    air: &AirSpec,
    alphas: &[u64],
    width: usize,
    n: usize,
    n_over_h: usize,
) -> u64 {
    let cur = lde_row(lde, j, width);
    let next = lde_row(lde, (j + n_over_h) % n, width);
    let mut acc: u64 = 0;
    let limit = air.transitions.len().min(alphas.len());
    for k in 0..limit {
        let c = &air.transitions[k];
        let v = crate::air::eval_transition(c.kind, &cur, &next);
        acc = bb_add(acc, bb_mul(alphas[k], v));
    }
    acc
}

/// Compute the quotient polynomial's evaluations on the LDE coset
/// `shift · K_n`: for each `j` in `[0, n)` the value
/// `Q(x_j) = C(x_j) / Z'_H(x_j)`, where `x_j = shift · ω_n^j` and `C` is
/// the `α`-combination of the AIR transition constraints. When `shift` is
/// not in the 2-adic subgroup, `Z'_H(x_j) ≠ 0` for every `j`.
///
/// Returns an empty `Vec` if preconditions fail (trace_log2 > domain_log2,
/// width mismatch, n not the LDE size).
pub fn compute_quotient_lde(
    lde: &[u64],
    air: &AirSpec,
    alphas: &[u64],
    width: usize,
    domain_log2: u32,
    trace_log2: u32,
    shift: u64,
) -> Vec<u64> {
    if trace_log2 > domain_log2 || width != air.num_columns {
        return Vec::new();
    }
    let n: usize = 1usize << domain_log2;
    let h: usize = 1usize << trace_log2;
    if lde.len() != n * width {
        return Vec::new();
    }
    if n % h != 0 {
        return Vec::new();
    }
    let n_over_h = n / h;
    let mut q: Vec<u64> = Vec::with_capacity(n);
    let omega_n = bb_root_of_unity(domain_log2);
    for j in 0..n {
        // x_j = shift · ω_n^j
        let x_j = bb_mul(shift, bb_pow(omega_n, j as u64));
        let c_j = compute_constraint_lde_value(lde, j, air, alphas, width, n, n_over_h);
        // Divide by the all-but-last-row selector, not by Z_H itself,
        // so the cyclic transition constraint at row h-1 is allowed to
        // be nonzero (Plonky3 convention).
        let inv = vanishing_selector_inv(x_j, trace_log2);
        q.push(bb_mul(c_j, inv));
    }
    q
}

/// Merkle-commit the quotient LDE values, leaf-hashing each `u64`.
pub fn commit_quotient_lde(q_lde: &[u64]) -> MerkleRoot {
    let n = q_lde.len();
    if n == 0 {
        return [0u8; HASH_SIZE];
    }
    let mut leaves: Vec<MerkleHash> = Vec::with_capacity(n);
    for i in 0..n {
        leaves.push(hash_field_elem(q_lde[i]));
    }
    merkle_build_root(&leaves, n)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::air::{fib_air, fib_trace};
    use crate::plonky3::{compute_trace_lde, LDE_COSET_SHIFT};

    #[test]
    fn test_vanishing_poly_zero_on_trace_subgroup() {
        // Z_H(ω_h^i) = ω_h^{ih} − 1 = 1 − 1 = 0 for any i, h.
        let trace_log2: u32 = 3; // h = 8
        let omega_h = bb_root_of_unity(trace_log2);
        for i in 0u64..8 {
            let x = bb_pow(omega_h, i);
            assert_eq!(vanishing_poly_eval(x, trace_log2), 0);
        }
    }

    #[test]
    fn test_vanishing_poly_nonzero_on_coset() {
        // For shift = GENERATOR ∉ H, Z_H(shift · ω_n^j) ≠ 0 for any j.
        let trace_log2: u32 = 3;
        let domain_log2: u32 = 5; // blowup ×4
        let omega_n = bb_root_of_unity(domain_log2);
        for j in 0u64..32 {
            let x = bb_mul(LDE_COSET_SHIFT, bb_pow(omega_n, j));
            assert_ne!(
                vanishing_poly_eval(x, trace_log2),
                0,
                "Z_H(shift·ω^{}) unexpectedly zero",
                j
            );
        }
    }

    #[test]
    fn test_quotient_lde_nonempty_for_fibonacci() {
        // For a valid Fibonacci trace of height 8 with domain 32:
        //   compute_quotient_lde returns n = 32 values, all nonzero
        //   (the cyclic constraint fails at the last row, so the
        //   quotient is a higher-degree polynomial but well-defined on
        //   shift · K since Z_H is nonzero there).
        let air = fib_air();
        let trace = fib_trace(8);
        let trace_log2: u32 = 3;
        let domain_log2: u32 = 5;
        let lde = compute_trace_lde(&trace, domain_log2, LDE_COSET_SHIFT);
        assert!(!lde.is_empty());

        let trace_commitment = [0u8; HASH_SIZE];
        let alphas = derive_constraint_alphas(&trace_commitment, air.transitions.len());

        let q = compute_quotient_lde(
            &lde,
            &air,
            &alphas,
            trace.width,
            domain_log2,
            trace_log2,
            LDE_COSET_SHIFT,
        );
        assert_eq!(q.len(), 1usize << domain_log2);
    }

    #[test]
    fn test_quotient_commit_is_deterministic() {
        let air = fib_air();
        let trace = fib_trace(8);
        let trace_log2: u32 = 3;
        let domain_log2: u32 = 5;
        let lde = compute_trace_lde(&trace, domain_log2, LDE_COSET_SHIFT);
        let alphas = derive_constraint_alphas(&[0u8; HASH_SIZE], air.transitions.len());
        let q = compute_quotient_lde(
            &lde,
            &air,
            &alphas,
            trace.width,
            domain_log2,
            trace_log2,
            LDE_COSET_SHIFT,
        );
        let root1 = commit_quotient_lde(&q);
        let root2 = commit_quotient_lde(&q);
        assert_eq!(root1, root2);
    }
}
