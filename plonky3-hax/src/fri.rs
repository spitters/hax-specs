//! FRI-style folding over the Baby Bear field, for the reference STARK.
//!
//! A folding round maps a polynomial `p` to `p'`, where
//! `p(x) = p_even(x^2) + x · p_odd(x^2)` and
//! `p'(y) = p_even(y) + alpha · p_odd(y)`; on evaluations,
//! `p'(x^2) = (p(x) + p(-x))/2 + alpha · (p(x) - p(-x))/(2x)`.
//!
//! A proof holds, for each round, a Merkle root over the evaluations and,
//! for each query index, the openings at `x` and `-x` with their
//! authentication paths, followed by the coefficients of the final
//! polynomial. The verifier checks the paths, the sibling indices, the
//! folding relation between consecutive rounds, the final round against the
//! remainder polynomial, and that the remainder coefficients above degree
//! `MAX_REMAINDER_DEGREE` are zero. This is a simplification of the FRI
//! protocol of Ben-Sasson, Bentov, Horesh and Riabzev (ICALP 2018); it has
//! no degree correction and follows no published parameter set.

use crate::specs::baby_bear::*;
use crate::specs::merkle::*;

/// Maximum number of FRI layers (folding rounds).
///
/// Baby Bear admits 2^27 roots of unity, so tree depth <= 27.
pub const MAX_FRI_LAYERS: usize = 27;

/// Maximum number of query positions per round.
pub const MAX_FRI_QUERIES: usize = 64;

/// Maximum remainder-polynomial degree (the final layer is checked directly).
pub const MAX_REMAINDER_DEGREE: usize = 16;

/// FRI protocol options.
#[derive(Clone, Copy)]
pub struct FriOptions {
    /// Number of folding rounds.
    pub num_layers: usize,
    /// Log2 of the initial evaluation domain size.
    pub domain_log2: u32,
    /// Number of query positions to check.
    pub num_queries: usize,
    /// Blowup factor: the polynomial of degree d is evaluated on a domain
    /// of size `d * blowup`. Typical values are 2, 4, 8.
    pub blowup: usize,
    /// Initial coset shift for the FRI evaluation domain. The verifier
    /// treats layer-0 query points as `coset_shift · ω^i` rather than
    /// `ω^i`; the shift then squares with each fold (since y = x²).
    /// Set to `1` for FRI on the bare subgroup.
    pub coset_shift: u64,
    /// Proof-of-Work soundness amplification: number of leading zero
    /// bits the prover must produce in `hash(transcript_seed, nonce)`.
    /// Set to `0` to disable.
    pub proof_of_work_bits: u32,
}

/// A single query response for one FRI layer.
///
/// The prover supplies: the evaluation at the queried point, the evaluation
/// at its sibling (negation), and Merkle authentication paths for both.
pub struct FriLayerQuery {
    pub eval_pos: u64,
    pub eval_neg: u64,
    pub path_pos: MerklePath,
    pub path_neg: MerklePath,
    pub index_pos: u64,
    pub index_neg: u64,
}

/// A complete FRI layer: Merkle root plus per-query responses.
pub struct FriLayer {
    pub commitment: MerkleRoot,
    pub queries: Vec<FriLayerQuery>,
}

/// The remainder polynomial, sent explicitly after all folding rounds.
pub struct FriRemainder {
    /// Coefficients with `coeffs[i]` the coefficient of `x^i`.
    pub coeffs: Vec<u64>,
}

/// A complete FRI proof.
pub struct FriProof {
    pub layers: Vec<FriLayer>,
    pub remainder: FriRemainder,
}

/// Compute the FRI fold at one query.
///
/// Given `eval_pos = p(x)`, `eval_neg = p(-x)`, the query point `x`, and
/// the verifier challenge `alpha`, returns `p'(x^2)`.
pub fn fri_fold(eval_pos: u64, eval_neg: u64, x: u64, alpha: u64) -> u64 {
    let sum = bb_add(eval_pos, eval_neg);
    let diff = bb_sub(eval_pos, eval_neg);

    let two: u64 = 2;
    let inv_two = bb_inv(two);
    let two_x = bb_mul(two, x);
    let inv_two_x = bb_inv(two_x);

    let p_even = bb_mul(sum, inv_two);
    let p_odd = bb_mul(diff, inv_two_x);

    bb_add(p_even, bb_mul(alpha, p_odd))
}

/// Compute the domain element at a given index.
///
/// The domain is `{omega^0, omega^1, ..., omega^(n-1)}`, where
/// `omega = bb_root_of_unity(domain_log2)`.
pub fn domain_element(domain_log2: u32, index: u64) -> u64 {
    let omega = bb_root_of_unity(domain_log2);
    bb_pow(omega, index)
}

/// Coset variant of [`domain_element`]: returns the `index`-th element
/// of the coset `shift · K`, where `K` is the 2-adic subgroup of order
/// `2^domain_log2`. Equal to `shift * domain_element(domain_log2, index)`.
pub fn coset_element(shift: u64, domain_log2: u32, index: u64) -> u64 {
    crate::specs::baby_bear::bb_mul(shift, domain_element(domain_log2, index))
}

/// Given an index in a domain of size 2^k, return the index of its negation.
///
/// Since omega^(n/2) = -1 in a primitive 2^k-th root domain, the sibling
/// of i is `(i + n/2) mod n`.
pub fn sibling_index(index: u64, domain_log2: u32) -> u64 {
    let n = 1u64 << domain_log2;
    let half_n = n >> 1;
    (index + half_n) & (n - 1)
}

/// Compute the folded-domain index for `index`.
///
/// When folding x -> x^2, in a domain with generator omega indices i and
/// i + n/2 both map to the same element in the squared domain.
pub fn folded_index(index: u64, domain_log2: u32) -> u64 {
    let half_n = 1u64 << (domain_log2 - 1);
    index & (half_n - 1)
}

/// Fold a polynomial's coefficients with challenge alpha.
///
/// `p'(y) = p_even(y) + alpha * p_odd(y)` in coefficient form.
pub fn fold_polynomial(coeffs: &[u64], alpha: u64) -> Vec<u64> {
    let n = coeffs.len();
    let half = n.div_ceil(2);
    let mut result: Vec<u64> = vec![0u64; half];

    for i in 0..half {
        let even_coeff = coeffs[2 * i];
        let odd_coeff = if 2 * i + 1 < n { coeffs[2 * i + 1] } else { 0 };
        result[i] = bb_add(even_coeff, bb_mul(alpha, odd_coeff));
    }

    result
}

/// Verify one FRI layer transition.
///
/// For each query, checks:
/// 1. Merkle path for p(x) is valid under the layer commitment.
/// 2. Merkle path for p(-x) is valid under the layer commitment.
/// 3. `index_neg` is the sibling of `index_pos` in the domain.
/// 4. The folded value matches the corresponding next-layer claimed evaluation.
pub fn fri_verify_layer(
    layer: &FriLayer,
    next_eval_at_query: &[u64],
    alpha: u64,
    domain_log2: u32,
    shift: u64,
) -> bool {
    let num_queries = layer.queries.len();
    for i in 0..num_queries {
        let query = &layer.queries[i];

        // 1. Merkle path for p(x)
        let leaf_pos = hash_field_elem(query.eval_pos);
        if !merkle_verify_path(layer.commitment, leaf_pos, query.index_pos, &query.path_pos) {
            return false;
        }

        // 2. Merkle path for p(-x)
        let leaf_neg = hash_field_elem(query.eval_neg);
        if !merkle_verify_path(layer.commitment, leaf_neg, query.index_neg, &query.path_neg) {
            return false;
        }

        // 3. Sibling index check
        let expected_neg = sibling_index(query.index_pos, domain_log2);
        if query.index_neg != expected_neg {
            return false;
        }

        // 4. Folding relation vs. next layer. The query point is on the
        //    coset `shift · K`, so x = shift · ω^index_pos.
        let x = coset_element(shift, domain_log2, query.index_pos);
        let folded = fri_fold(query.eval_pos, query.eval_neg, x, alpha);

        if i < next_eval_at_query.len() && folded != next_eval_at_query[i] {
            return false;
        }
    }

    true
}

/// Verify a complete FRI proof.
///
/// Walks the layers, checks each transition, and verifies the final layer
/// against the remainder polynomial. Returns true iff all checks pass.
pub fn fri_verify(proof: &FriProof, alphas: &[u64], options: FriOptions) -> bool {
    let num_layers = proof.layers.len();

    if num_layers != options.num_layers {
        return false;
    }
    if alphas.len() < num_layers {
        return false;
    }
    if num_layers == 0 {
        return false;
    }

    let mut current_domain_log2 = options.domain_log2;
    let mut current_shift = options.coset_shift;

    for layer_idx in 0..num_layers {
        let layer = &proof.layers[layer_idx];
        let alpha = alphas[layer_idx];

        let num_queries = layer.queries.len();
        if num_queries != options.num_queries {
            return false;
        }

        let next_domain_log2 = current_domain_log2 - 1;
        let mut next_evals: Vec<u64> = Vec::new();

        if layer_idx + 1 < num_layers {
            let next_layer = &proof.layers[layer_idx + 1];
            for q in 0..num_queries {
                if q < next_layer.queries.len() {
                    next_evals.push(next_layer.queries[q].eval_pos);
                }
            }
        } else {
            // Final layer: check against the remainder polynomial.
            // After this fold the LDE lives on `current_shift^2 · K_{n/2}`,
            // so the remainder is evaluated at that coset. The index
            // mapping is `folded_index` (pair i with i + n/2 — its
            // sibling — to the same next-layer index), not `i >> 1`
            // (which would pair adjacent i's).
            let next_shift = bb_mul(current_shift, current_shift);
            for q in 0..num_queries {
                let x_index = folded_index(layer.queries[q].index_pos, current_domain_log2);
                let x_squared = coset_element(next_shift, next_domain_log2, x_index);
                let remainder_eval = bb_poly_eval(&proof.remainder.coeffs, x_squared);
                next_evals.push(remainder_eval);
            }
        }

        if !fri_verify_layer(layer, &next_evals, alpha, current_domain_log2, current_shift) {
            return false;
        }

        current_domain_log2 = next_domain_log2;
        current_shift = bb_mul(current_shift, current_shift);
    }

    // Remainder degree bound
    let max_remainder_deg = MAX_REMAINDER_DEGREE;
    if proof.remainder.coeffs.len() > max_remainder_deg + 1 {
        for k in (max_remainder_deg + 1)..proof.remainder.coeffs.len() {
            if proof.remainder.coeffs[k] != 0 {
                return false;
            }
        }
    }

    true
}

/// Evaluate a polynomial on a domain and build the Merkle commitment.
/// Used by the prover / tests.
pub fn commit_polynomial(
    coeffs: &[u64],
    domain_log2: u32,
) -> (Vec<u64>, Vec<MerkleHash>, MerkleRoot) {
    let n = 1usize << domain_log2;
    let omega = bb_root_of_unity(domain_log2);

    let mut evals: Vec<u64> = vec![0u64; n];
    let mut hashes: Vec<MerkleHash> = vec![[0u8; HASH_SIZE]; n];
    let mut point = ONE;
    for i in 0..n {
        evals[i] = bb_poly_eval(coeffs, point);
        hashes[i] = hash_field_elem(evals[i]);
        point = bb_mul(point, omega);
    }

    let root = merkle_build_root(&hashes, n);
    (evals, hashes, root)
}

/// Build a real FRI proof for one column's LDE evaluations.
///
/// `column_lde` is the size-`n` vector of evaluations of the column's
/// polynomial on the coset `options.coset_shift · K_n`, where
/// `n = 2^options.domain_log2`.
///
/// `alphas[i]` is the verifier challenge for fold `i`; the slice must
/// have at least `options.num_layers` entries.
///
/// `query_indices` are the verifier's chosen layer-0 query positions
/// in `[0, n)`; the slice length must equal `options.num_queries`.
///
/// Returns `None` if any dimension precondition is violated.
pub fn fri_prove_column(
    column_lde: &[u64],
    options: FriOptions,
    alphas: &[u64],
    query_indices: &[u64],
) -> Option<FriProof> {
    let n = column_lde.len();
    if n != (1usize << options.domain_log2) {
        return None;
    }
    if alphas.len() < options.num_layers {
        return None;
    }
    if query_indices.len() != options.num_queries {
        return None;
    }
    if options.num_layers == 0 {
        return None;
    }
    if options.num_layers as u32 > options.domain_log2 {
        return None;
    }

    let mut current_evals: Vec<u64> = column_lde.to_vec();
    let mut current_log2: u32 = options.domain_log2;
    let mut current_shift: u64 = options.coset_shift;
    let mut current_query_indices: Vec<u64> = query_indices.to_vec();
    let mut layers: Vec<FriLayer> = Vec::with_capacity(options.num_layers);

    for layer_idx in 0..options.num_layers {
        let m = current_evals.len();

        // Merkle-commit the layer.
        let mut leaves: Vec<MerkleHash> = Vec::with_capacity(m);
        for i in 0..m {
            leaves.push(hash_field_elem(current_evals[i]));
        }
        let commitment = merkle_build_root(&leaves, m);

        // Build openings at every queried position.
        let mut queries: Vec<FriLayerQuery> = Vec::with_capacity(options.num_queries);
        for q in 0..options.num_queries {
            let i_pos = current_query_indices[q];
            let i_neg = sibling_index(i_pos, current_log2);
            let (_, path_pos) = merkle_build_and_prove(&leaves, m, i_pos as usize);
            let (_, path_neg) = merkle_build_and_prove(&leaves, m, i_neg as usize);
            queries.push(FriLayerQuery {
                eval_pos: current_evals[i_pos as usize],
                eval_neg: current_evals[i_neg as usize],
                path_pos,
                path_neg,
                index_pos: i_pos,
                index_neg: i_neg,
            });
        }

        layers.push(FriLayer { commitment, queries });

        // Fold to the next layer.
        let alpha = alphas[layer_idx];
        let next_size = m / 2;
        let mut next_evals: Vec<u64> = vec![0u64; next_size];
        for i in 0..next_size {
            let x = coset_element(current_shift, current_log2, i as u64);
            next_evals[i] = fri_fold(
                current_evals[i],
                current_evals[i + next_size],
                x,
                alpha,
            );
        }

        let mut next_query_indices: Vec<u64> = Vec::with_capacity(options.num_queries);
        for q in 0..options.num_queries {
            next_query_indices.push(folded_index(current_query_indices[q], current_log2));
        }

        current_evals = next_evals;
        current_log2 -= 1;
        current_shift = bb_mul(current_shift, current_shift);
        current_query_indices = next_query_indices;
    }

    // Extract the remainder polynomial's coefficients from the final
    // folded LDE evaluations. The final LDE sits on `current_shift · K`
    // with `K` of order `2^current_log2`, so:
    //   intt with ω_{K} → coefficients of P(current_shift · x)
    //   untwist coeffs by `current_shift^{-i}` → coefficients of P(x)
    let remaining_size = current_evals.len();
    let mut coeffs = current_evals;
    if remaining_size > 1 {
        let omega = bb_root_of_unity(current_log2);
        crate::ntt::intt(&mut coeffs, omega);
        if current_shift != 1 {
            let shift_inv = bb_inv(current_shift);
            let mut shift_inv_pow: u64 = 1;
            for i in 0..remaining_size {
                coeffs[i] = bb_mul(coeffs[i], shift_inv_pow);
                shift_inv_pow = bb_mul(shift_inv_pow, shift_inv);
            }
        }
    }

    Some(FriProof {
        layers,
        remainder: FriRemainder { coeffs },
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fri_fold_constant_polynomial() {
        // p(x) = c => p(x) = p(-x) = c, folded = c
        let c: u64 = 42;
        let x: u64 = 7;
        let alpha: u64 = 999;
        assert_eq!(fri_fold(c, c, x, alpha), c);
    }

    #[test]
    fn test_fri_fold_linear_polynomial() {
        // p(x) = a + b*x
        let a: u64 = 10;
        let b: u64 = 20;
        let x: u64 = 5;
        let alpha: u64 = 3;

        let eval_pos = bb_add(a, bb_mul(b, x));
        let eval_neg = bb_sub(a, bb_mul(b, x));

        // p'(y) = a + alpha * b
        let expected = bb_add(a, bb_mul(alpha, b));
        assert_eq!(fri_fold(eval_pos, eval_neg, x, alpha), expected);
    }

    #[test]
    fn test_fri_fold_quadratic_polynomial() {
        // p(x) = 1 + 2x + 3x^2, p_even(y) = 1 + 3y, p_odd(y) = 2
        // p'(y) = 1 + 3y + alpha*2
        let x: u64 = 7;
        let alpha: u64 = 5;

        let eval_pos = bb_add(bb_add(1, bb_mul(2, x)), bb_mul(3, bb_square(x)));
        let neg_x = bb_neg(x);
        let eval_neg = bb_add(bb_add(1, bb_mul(2, neg_x)), bb_mul(3, bb_square(neg_x)));

        let x_sq = bb_square(x);
        let expected = bb_add(bb_add(1, bb_mul(3, x_sq)), bb_mul(alpha, 2));

        assert_eq!(fri_fold(eval_pos, eval_neg, x, alpha), expected);
    }

    #[test]
    fn test_fold_polynomial_coefficients() {
        // p(x) = 1 + 2x + 3x^2 + 4x^3, alpha = 5
        // p'(y) = (1 + 5*2) + (3 + 5*4)*y = [11, 23]
        let coeffs = vec![1u64, 2, 3, 4];
        let alpha: u64 = 5;
        let folded = fold_polynomial(&coeffs, alpha);
        assert_eq!(folded.len(), 2);
        assert_eq!(folded[0], bb_add(1, bb_mul(alpha, 2)));
        assert_eq!(folded[1], bb_add(3, bb_mul(alpha, 4)));
    }

    #[test]
    fn test_sibling_index() {
        assert_eq!(sibling_index(0, 3), 4);
        assert_eq!(sibling_index(1, 3), 5);
        assert_eq!(sibling_index(4, 3), 0);
        assert_eq!(sibling_index(7, 3), 3);
    }

    #[test]
    fn test_folded_index() {
        assert_eq!(folded_index(0, 3), 0);
        assert_eq!(folded_index(4, 3), 0);
        assert_eq!(folded_index(1, 3), 1);
        assert_eq!(folded_index(5, 3), 1);
    }

    #[test]
    fn test_domain_element_roots() {
        let log2 = 3u32;
        let n = 1u64 << log2;
        let omega = bb_root_of_unity(log2);
        assert_eq!(domain_element(log2, 0), 1);
        assert_eq!(domain_element(log2, 1), omega);
        assert_eq!(domain_element(log2, n), 1);
        assert_eq!(domain_element(log2, n / 2), BABY_BEAR_PRIME - 1);
    }

    #[test]
    fn test_fri_folding_consistency() {
        // p(x) = 5 + 3x + 7x^2 + 2x^3
        let coeffs = vec![5u64, 3, 7, 2];
        let alpha: u64 = 11;
        let folded_coeffs = fold_polynomial(&coeffs, alpha);

        let domain_log2 = 4u32;
        let idx: u64 = 3;
        let x = domain_element(domain_log2, idx);
        let neg_x = bb_neg(x);

        let eval_pos = bb_poly_eval(&coeffs, x);
        let eval_neg = bb_poly_eval(&coeffs, neg_x);

        let folded_eval = fri_fold(eval_pos, eval_neg, x, alpha);
        let x_sq = bb_square(x);
        let direct_eval = bb_poly_eval(&folded_coeffs, x_sq);

        assert_eq!(folded_eval, direct_eval);
    }

    #[test]
    fn test_fri_folding_multiple_points() {
        let coeffs = vec![1u64, 2, 3, 4, 5, 6, 7, 8];
        let alpha: u64 = 42;
        let folded_coeffs = fold_polynomial(&coeffs, alpha);

        let domain_log2 = 4u32;
        for idx in 0u64..8 {
            let x = domain_element(domain_log2, idx);
            let neg_x = bb_neg(x);
            let eval_pos = bb_poly_eval(&coeffs, x);
            let eval_neg = bb_poly_eval(&coeffs, neg_x);
            let folded_eval = fri_fold(eval_pos, eval_neg, x, alpha);
            let x_sq = bb_square(x);
            let direct_eval = bb_poly_eval(&folded_coeffs, x_sq);
            assert_eq!(
                folded_eval, direct_eval,
                "Mismatch at idx={}: folded={}, direct={}",
                idx, folded_eval, direct_eval
            );
        }
    }
}
