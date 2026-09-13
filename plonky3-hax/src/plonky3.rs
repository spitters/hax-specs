//! Prover and verifier of the reference STARK.
//!
//! `plonky3_prove` rejects a trace that violates the AIR, and otherwise:
//!
//! 1. computes the low-degree extension (LDE) of every trace column on the
//!    coset `LDE_COSET_SHIFT · K_n` and commits to the row-wise combination
//!    of the columns with a Merkle tree;
//! 2. produces one FRI folding proof per column, with challenges and query
//!    indices computed from the trace commitment;
//! 3. computes the quotient polynomial on the same coset, commits to it and
//!    produces its FRI folding proof;
//! 4. evaluates the trace columns and the quotient at the out-of-domain
//!    point `z`;
//! 5. searches a proof-of-work nonce when `proof_of_work_bits > 0`;
//! 6. produces the FRI folding proof of the batched DEEP quotient.
//!
//! All challenges are computed deterministically from commitment bytes by
//! base-257 accumulation in F_p, and the Merkle hash is the
//! non-cryptographic function of `specs::merkle`. The construction follows
//! the structure of a STARK; it is not Plonky3's prover, and its proofs are
//! not interoperable with Plonky3.

use crate::air::{trace_valid, AirSpec, Trace};
use crate::fri::{fri_prove_column, fri_verify, FriOptions, FriProof};
use crate::specs::baby_bear::*;
use crate::specs::merkle::*;

/// A proof of the reference STARK.
pub struct Plonky3Proof {
    /// Merkle commitment to the LDE of all trace columns, row-interleaved.
    pub trace_commitment: MerkleRoot,
    /// Merkle commitment to the quotient polynomial's LDE evaluations
    /// (alpha-LC of AIR transition constraints, divided by `Z'_H`).
    pub quotient_commitment: MerkleRoot,
    /// FRI proofs, one per trace column.
    pub column_fri_proofs: Vec<FriProof>,
    /// FRI proof for the quotient column.
    pub quotient_fri_proof: FriProof,
    /// Boundary values claimed by the prover, in the same order as
    /// `air.boundaries`. The verifier re-checks these against the AIR spec.
    pub boundary_claims: Vec<u64>,
    /// log2 of the trace subgroup size used by the prover. The verifier
    /// uses this to recompute `Z'_H` at the OOD point.
    pub trace_log2: u32,
    /// Trace polynomial evaluations at the OOD point `z`, one per column.
    pub ood_trace_evals: Vec<u64>,
    /// Trace polynomial evaluations at `g · z`, one per column.
    pub ood_trace_next_evals: Vec<u64>,
    /// Quotient polynomial evaluation at the OOD point `z`.
    pub ood_quotient_eval: u64,
    /// Proof-of-Work nonce. The verifier checks
    /// `hash_two_to_one(quotient_commitment, nonce_to_hash(nonce))`
    /// has at least `options.proof_of_work_bits` leading zero bits.
    pub pow_nonce: u64,
    /// Batched DEEP-FRI proof binding OOD evaluations to commitments.
    /// `B(x) = Σ_i β^i · (P_i(x) − P_i(z)) / (x − z)` is a polynomial of
    /// degree `< max_i deg(P_i)` iff the claimed OOD values are
    /// consistent with the committed polynomials. The verifier runs FRI
    /// on B; if the claim is false, B has a pole at z and FRI rejects.
    pub deep_fri_proof: FriProof,
}

/// Derive `num_layers` field-element FRI challenges per column from the
/// trace commitment. Pure function of the commitment bytes, so prover
/// and verifier produce the same vector.
pub fn derive_fri_alphas(
    trace_commitment: &MerkleRoot,
    num_columns: usize,
    num_layers: usize,
) -> Vec<Vec<u64>> {
    let mut result: Vec<Vec<u64>> = Vec::with_capacity(num_columns);
    for col in 0..num_columns {
        let mut row: Vec<u64> = Vec::with_capacity(num_layers);
        for l in 0..num_layers {
            // Mix in (col, l) so each (column, layer) pair gets a distinct
            // challenge, deterministically derived from the commitment.
            let mut acc: u64 = 0;
            for b in 0..HASH_SIZE {
                let v = trace_commitment[b] as u64;
                acc = bb_add(bb_mul(acc, 257), v);
            }
            acc = bb_add(bb_mul(acc, 257), col as u64);
            acc = bb_add(bb_mul(acc, 257), l as u64);
            row.push(acc);
        }
        result.push(row);
    }
    result
}

/// Derive `num_queries` layer-0 query indices in `[0, n)` from the trace
/// commitment. Same deterministic-from-transcript shape as
/// `derive_fri_alphas`.
pub fn derive_query_indices(
    trace_commitment: &MerkleRoot,
    num_queries: usize,
    n: usize,
) -> Vec<u64> {
    let mut result: Vec<u64> = Vec::with_capacity(num_queries);
    for q in 0..num_queries {
        // 8 bytes per query, rotating through the 32-byte commitment.
        let mut acc: u64 = 0;
        for b in 0..8 {
            let i = (q * 8 + b) % HASH_SIZE;
            acc = (acc << 8) | (trace_commitment[i] as u64);
        }
        result.push(acc % (n as u64));
    }
    result
}

/// The byte-wise XOR of the trace commitment, the layer-0 commitment of every
/// column FRI proof that has layers, and the quotient commitment.
pub fn transcript_seed(proof: &Plonky3Proof) -> [u8; HASH_SIZE] {
    let mut seed = proof.trace_commitment;
    for i in 0..proof.column_fri_proofs.len() {
        let layers = &proof.column_fri_proofs[i].layers;
        if !layers.is_empty() {
            for j in 0..HASH_SIZE {
                seed[j] ^= layers[0].commitment[j];
            }
        }
    }
    for j in 0..HASH_SIZE {
        seed[j] ^= proof.quotient_commitment[j];
    }
    seed
}

/// Build the row-interleaved Low-Degree Extension (LDE) of a trace on
/// the coset `shift · K`, where `K` is the multiplicative subgroup of
/// order `n = 2^domain_log2`.
///
/// Each column of the trace is interpreted as the evaluations of a
/// polynomial `P_col(x)` at the trace subgroup `H = {ω_h^0, ..., ω_h^{h-1}}`
/// where `h = trace.height` and `ω_h` is a primitive `h`-th root of
/// unity. The pipeline is:
///
/// 1. `intt`: recover the coefficients of `P_col` from its evaluations
///    on `H`.
/// 2. Zero-pad the coefficient vector from length `h` up to length `n`.
/// 3. Coset-twist: multiply the `i`-th coefficient by `shift^i`. After
///    this, the coefficient vector represents `P(shift · x)`.
/// 4. `ntt`: evaluate the twisted polynomial on `K`. By construction
///    those values are the evaluations of `P_col` on `shift · K`.
///
/// Use `shift = 1` to evaluate on the subgroup `K` itself (no coset).
/// The conventional Plonky3 choice is `shift = GENERATOR` so that the
/// LDE coset is disjoint from `H`.
///
/// The result contains `n * trace.width` values; the `i`-th block of
/// `trace.width` values is the evaluation of all columns at the `i`-th
/// domain point `shift · ω_n^i`.
///
/// ## Preconditions
///
/// - `trace.height` is a power of two.
/// - `trace.height <= 1 << domain_log2`.
/// - `domain_log2 <= 27` (Baby Bear's two-adicity).
/// - `shift` is nonzero. (Shift = 0 would collapse the entire LDE to 0.)
///
/// Violation of any precondition produces an empty `Vec`; callers should
/// check `compute_trace_lde(...).is_empty()` to detect the rejection.
pub fn compute_trace_lde(trace: &Trace, domain_log2: u32, shift: u64) -> Vec<u64> {
    let h = trace.height;
    let n = 1usize << domain_log2;

    if h == 0 || (h & (h - 1)) != 0 || h > n || domain_log2 > 27 || shift == 0 {
        return Vec::new();
    }
    let trace_log2: u32 = h.trailing_zeros();
    let omega_trace = bb_root_of_unity(trace_log2);
    let omega_n = bb_root_of_unity(domain_log2);

    let mut result = vec![0u64; n * trace.width];
    for col in 0..trace.width {
        // 1. Extract column evaluations on H, then intt → coefficients.
        let mut coeffs = vec![0u64; n];
        for i in 0..h {
            coeffs[i] = trace.get(i, col);
        }
        let (head, _tail) = coeffs.split_at_mut(h);
        crate::ntt::intt(head, omega_trace);
        // 2. Zero-padding already in place.
        // 3. Coset twist: coeffs[i] *= shift^i. Skipped when shift == 1.
        if shift != 1 {
            let mut shift_pow: u64 = 1;
            for i in 0..n {
                coeffs[i] = bb_mul(coeffs[i], shift_pow);
                shift_pow = bb_mul(shift_pow, shift);
            }
        }
        // 4. ntt on the full n-entry coefficient vector → evals on shift·K.
        crate::ntt::ntt(&mut coeffs, omega_n);

        for i in 0..n {
            result[i * trace.width + col] = coeffs[i];
        }
    }
    result
}

/// The conventional Plonky3 LDE coset shift on Baby Bear: the
/// multiplicative `GENERATOR`. Using this shift makes `shift · K`
/// disjoint from any of the trace subgroups (which all sit inside the
/// 2-adic subgroup, while `GENERATOR` does not).
pub const LDE_COSET_SHIFT: u64 = GENERATOR;

/// Commit to the interleaved LDE via a Merkle tree.
pub fn commit_trace_lde(lde: &[u64], width: usize, domain_log2: u32) -> MerkleRoot {
    let n = 1usize << domain_log2;
    let mut leaves: Vec<MerkleHash> = Vec::with_capacity(n);
    for i in 0..n {
        // Hash the `width` elements of this row by folding them together
        // into a single 8-byte value and then calling `hash_field_elem`.
        // For a real prover we'd hash the concatenation directly; this
        // simpler mixing keeps us within the existing leaf-hash primitive.
        let mut mixed: u64 = 0;
        for col in 0..width {
            mixed = bb_add(bb_mul(mixed, 31), lde[i * width + col]);
        }
        leaves.push(hash_field_elem(mixed));
    }
    merkle_build_root(&leaves, n)
}

/// Default zero FRI proof: returned by `batch_fri_prove_columns`
/// when the FRI prover preconditions are violated. The caller then
/// checks `any_failed` and bails out without using the proofs.
fn default_fri_proof() -> FriProof {
    FriProof {
        layers: Vec::new(),
        remainder: crate::fri::FriRemainder { coeffs: Vec::new() },
    }
}

/// Per-column FRI: collects FriProofs and reports a separate
/// `any_failed` flag rather than threading `Option` through the loop
/// body. This keeps the early-return out of every `for` body — there
/// is no `return None` inside any loop in this function. Haxpipe
/// extracts this cleanly because the only CF marker is `cfContinue`
/// (no `cfBreak` nested under `forFoldReturn`).
pub fn batch_fri_prove_columns(
    lde: &[u64],
    width: usize,
    n: usize,
    options: FriOptions,
    column_alphas: &[Vec<u64>],
    query_indices: &[u64],
) -> (Vec<FriProof>, bool) {
    let mut out: Vec<FriProof> = Vec::with_capacity(width);
    let mut any_failed: bool = false;
    for col in 0..width {
        let mut vals = vec![0u64; n];
        for i in 0..n {
            vals[i] = lde[i * width + col];
        }
        let p = fri_prove_column(
            &vals,
            options,
            &column_alphas[col],
            query_indices,
        );
        match p {
            Some(proof) => out.push(proof),
            None => {
                any_failed = true;
                out.push(default_fri_proof());
            }
        }
    }
    (out, any_failed)
}

/// Build a proof that `trace` satisfies `air`.
///
/// `options` gives the FRI parameters; `options.coset_shift` is ignored and
/// `LDE_COSET_SHIFT` is used. All challenges are derived from the
/// commitments.
///
/// Returns `None` if the trace violates the AIR, has the wrong width, has a
/// height that is not a power of two or exceeds `2^options.domain_log2`, or
/// if an FRI or proof-of-work precondition fails.
pub fn plonky3_prove(
    air: &AirSpec,
    trace: &Trace,
    options: FriOptions,
) -> Option<Plonky3Proof> {
    if trace.width != air.num_columns {
        return None;
    }
    if !trace_valid(air, trace) {
        return None;
    }
    // The LDE pipeline requires a power-of-two trace height.
    if trace.height == 0 || (trace.height & (trace.height - 1)) != 0 {
        return None;
    }

    // LDE domain size is fixed by the caller's `options.domain_log2`.
    // The trace must fit and have power-of-two height (already checked).
    let domain_log2: u32 = options.domain_log2;
    let trace_log2: u32 = trace.height.trailing_zeros();
    if trace_log2 > domain_log2 {
        return None;
    }

    // Commit to the trace LDE. Use the conventional Plonky3 coset shift
    // so that the LDE coset shift · K is disjoint from the trace subgroup
    // H, mirroring upstream `coset_lde_batch`.
    let lde = compute_trace_lde(trace, domain_log2, LDE_COSET_SHIFT);
    if lde.is_empty() {
        return None;
    }
    let trace_commitment = commit_trace_lde(&lde, trace.width, domain_log2);

    // Deterministically derive per-column FRI challenges and per-query
    // indices from the trace commitment. The verifier re-derives them
    // the same way and checks consistency.
    let column_alphas = derive_fri_alphas(&trace_commitment, trace.width, options.num_layers);
    let n = 1usize << domain_log2;
    let query_indices = derive_query_indices(&trace_commitment, options.num_queries, n);

    // Stage-D FRI option layout: every column folds the same LDE size so
    // we feed `fri_prove_column` an `options` tuned to that size.
    let column_fri_options = FriOptions {
        num_layers: options.num_layers,
        domain_log2,
        num_queries: options.num_queries,
        blowup: options.blowup,
        coset_shift: LDE_COSET_SHIFT,
        proof_of_work_bits: options.proof_of_work_bits,
    };

    // Per-column FRI proofs. The helper returns `(Vec, bool)` instead of
    // `Option<Vec>`, so that no early return sits inside a `for` body; it
    // pushes an empty proof for a failing column and reports the failure
    // in the flag.
    let (proofs, any_failed) = batch_fri_prove_columns(
        &lde,
        trace.width,
        n,
        column_fri_options,
        &column_alphas,
        &query_indices,
    );
    if any_failed {
        return None;
    }
    let column_fri_proofs: Vec<FriProof> = proofs;

    // Quotient polynomial commitment. Random LC of AIR transition
    // constraints, divided pointwise by Z_H(x) = x^h − 1 on the LDE
    // coset. The verifier checks `C(z) = Q(z) · Z_H(z)` at the OOD
    // point (next step in the protocol).
    let constraint_alphas =
        crate::quotient::derive_constraint_alphas(&trace_commitment, air.transitions.len());
    let quotient_lde = crate::quotient::compute_quotient_lde(
        &lde,
        air,
        &constraint_alphas,
        trace.width,
        domain_log2,
        trace_log2,
        LDE_COSET_SHIFT,
    );
    if quotient_lde.is_empty() {
        return None;
    }
    let quotient_commitment = crate::quotient::commit_quotient_lde(&quotient_lde);
    let quotient_alphas = derive_fri_alphas(&quotient_commitment, 1, options.num_layers);
    let quotient_query_indices =
        derive_query_indices(&quotient_commitment, options.num_queries, n);
    let quotient_fri_proof_opt = fri_prove_column(
        &quotient_lde,
        column_fri_options,
        &quotient_alphas[0],
        &quotient_query_indices,
    );
    let quotient_fri_proof = match quotient_fri_proof_opt {
        Some(p) => p,
        None => return None,
    };

    // Boundary claims follow the same order as the AIR spec.
    let mut boundary_claims: Vec<u64> = Vec::with_capacity(air.boundaries.len());
    for k in 0..air.boundaries.len() {
        let b = &air.boundaries[k];
        boundary_claims.push(trace.get(b.row, b.col));
    }

    // OOD evaluation: derive z from quotient commitment, evaluate trace
    // and quotient at z and g·z, send them in the proof. The verifier
    // re-derives z and checks the AIR identity at z.
    let z = crate::ood::derive_ood_point(&quotient_commitment, trace_log2, domain_log2);
    let omega_h = bb_root_of_unity(trace_log2);
    let g_z = bb_mul(omega_h, z);
    let ood_trace_evals = crate::ood::evaluate_trace_at(trace, z);
    let ood_trace_next_evals = crate::ood::evaluate_trace_at(trace, g_z);
    let ood_quotient_eval =
        crate::ood::evaluate_quotient_at(&quotient_lde, domain_log2, LDE_COSET_SHIFT, z);

    // Proof-of-Work grinding. The PoW seed is the same byte stream that
    // every challenge already mixes — we use the quotient commitment
    // (last committed object before PoW in the Fiat-Shamir order) so
    // the verifier can re-derive it without seeing pow_nonce.
    // Both branches produce an `Option<u64>` and a single `match` does the
    // early return, so that no branch mixes a value with a
    // match-with-return, a shape the Lean translation does not collapse.
    let pow_nonce_opt: Option<u64> = if options.proof_of_work_bits == 0 {
        Some(0u64)
    } else {
        crate::pow::grind_pow_nonce(
            &quotient_commitment,
            options.proof_of_work_bits,
            1u64 << (options.proof_of_work_bits + 8),
        )
    };
    let pow_nonce = match pow_nonce_opt {
        Some(n) => n,
        None => return None,
    };

    // Batched DEEP-FRI: build (P(x) − P(z))/(x − z) for every committed
    // polynomial (each trace column + the quotient), combine via random
    // β, and run a single FRI on the combined polynomial.
    let beta = crate::deep::derive_deep_beta(&quotient_commitment);
    let mut all_deeps: Vec<Vec<u64>> = Vec::with_capacity(trace.width + 1);
    for c in 0..trace.width {
        let mut p_lde = vec![0u64; n];
        for j in 0..n {
            p_lde[j] = lde[j * trace.width + c];
        }
        all_deeps.push(crate::deep::compute_deep_poly_lde(
            &p_lde,
            ood_trace_evals[c],
            z,
            domain_log2,
            LDE_COSET_SHIFT,
        ));
    }
    all_deeps.push(crate::deep::compute_deep_poly_lde(
        &quotient_lde,
        ood_quotient_eval,
        z,
        domain_log2,
        LDE_COSET_SHIFT,
    ));
    let combined_deep = crate::deep::combine_deep_polys(&all_deeps, beta);
    let deep_alphas = derive_fri_alphas(&quotient_commitment, 1, options.num_layers);
    // DEEP FRI uses the same layer-0 query indices as the column FRIs
    // (derived from trace_commitment) so the verifier can cross-check
    // openings without sampling new positions.
    let deep_fri_proof_opt = fri_prove_column(
        &combined_deep,
        column_fri_options,
        &deep_alphas[0],
        &query_indices,
    );
    let deep_fri_proof = match deep_fri_proof_opt {
        Some(p) => p,
        None => return None,
    };

    Some(Plonky3Proof {
        trace_commitment,
        quotient_commitment,
        column_fri_proofs,
        quotient_fri_proof,
        boundary_claims,
        trace_log2,
        ood_trace_evals,
        ood_trace_next_evals,
        ood_quotient_eval,
        pow_nonce,
        deep_fri_proof,
    })
}

/// Verify a Plonky3 proof against an AIR specification.
///
/// Checks, in order:
/// 1. the boundary claims agree with `air.boundaries` in number and value;
/// 2. there is one FRI proof per column, and each passes `fri_verify`;
/// 3. the quotient FRI proof passes `fri_verify`;
/// 4. the OOD identity `C(z) = Q(z) · Z'_H(z)` holds at the re-derived `z`;
/// 5. the proof-of-work nonce, when `options.proof_of_work_bits > 0`;
/// 6. the DEEP FRI proof passes `fri_verify`, and its layer-0 opened values
///    equal the DEEP combination recomputed from the layer-0 openings of the
///    column and quotient proofs.
///
/// The folding challenges of column `col` are `column_fri_alphas[col]` when
/// that vector has at least `options.num_layers` entries, and otherwise
/// those derived from the trace commitment. The verifier does not check
/// that the query indices in the proofs are the derived ones.
pub fn plonky3_verify(
    air: &AirSpec,
    proof: &Plonky3Proof,
    column_fri_alphas: &[Vec<u64>],
    options: FriOptions,
) -> bool {
    // 1. Boundary-claim arity
    if proof.boundary_claims.len() != air.boundaries.len() {
        return false;
    }

    // 2. Boundary values
    for k in 0..air.boundaries.len() {
        if proof.boundary_claims[k] != air.boundaries[k].value {
            return false;
        }
    }

    // 3. Column count
    if proof.column_fri_proofs.len() != air.num_columns {
        return false;
    }

    // 4. Derive challenges deterministically from the trace commitment.
    //    Challenges supplied by the caller take precedence (see below).
    let derived_alphas =
        derive_fri_alphas(&proof.trace_commitment, air.num_columns, options.num_layers);

    // The prover commits to the column LDE on the same coset as the trace
    // LDE; the verifier trusts `options.domain_log2` to match.
    let column_options = FriOptions {
        num_layers: options.num_layers,
        domain_log2: options.domain_log2,
        num_queries: options.num_queries,
        blowup: options.blowup,
        coset_shift: options.coset_shift,
        proof_of_work_bits: options.proof_of_work_bits,
    };

    for col in 0..proof.column_fri_proofs.len() {
        let fri_proof = &proof.column_fri_proofs[col];
        // Caller-supplied challenges are used when they cover all
        // `options.num_layers` layers; otherwise the derived ones.
        let alphas: &[u64] = if col < column_fri_alphas.len()
            && column_fri_alphas[col].len() >= options.num_layers
        {
            &column_fri_alphas[col]
        } else {
            &derived_alphas[col]
        };
        if !fri_verify(fri_proof, alphas, column_options) {
            return false;
        }
    }

    // 5. Quotient FRI: check the FRI proof for the quotient polynomial
    //    against alphas derived from the quotient commitment.
    let quotient_alphas =
        derive_fri_alphas(&proof.quotient_commitment, 1, options.num_layers);
    if !fri_verify(&proof.quotient_fri_proof, &quotient_alphas[0], column_options) {
        return false;
    }

    // 6. OOD identity: C(z) = Q(z) · Z'_H(z).
    //    The prover supplies trace + quotient evaluations at the
    //    Fiat-Shamir-derived OOD point `z`. The verifier re-derives `z`,
    //    re-derives the constraint alphas, and checks the AIR identity.
    //    The consistency of ood_trace_evals with the trace commitment
    //    is checked by the DEEP step (step 8).
    if proof.ood_trace_evals.len() != air.num_columns
        || proof.ood_trace_next_evals.len() != air.num_columns
    {
        return false;
    }
    let z = crate::ood::derive_ood_point(
        &proof.quotient_commitment,
        proof.trace_log2,
        options.domain_log2,
    );
    let constraint_alphas =
        crate::quotient::derive_constraint_alphas(&proof.trace_commitment, air.transitions.len());
    // Compute C(z) = Σ_k α_k · c_k(T(z), T(g·z)).
    let mut c_at_z: u64 = 0;
    let lim = air.transitions.len().min(constraint_alphas.len());
    for k in 0..lim {
        let v = crate::air::eval_transition(
            air.transitions[k].kind,
            &proof.ood_trace_evals,
            &proof.ood_trace_next_evals,
        );
        c_at_z = bb_add(c_at_z, bb_mul(constraint_alphas[k], v));
    }
    let sel_at_z = crate::quotient::vanishing_selector_eval(z, proof.trace_log2);
    let rhs = bb_mul(proof.ood_quotient_eval, sel_at_z);
    if c_at_z != rhs {
        return false;
    }

    // 7. Proof-of-Work check. The PoW seed is the quotient commitment
    //    so the verifier can re-derive it independently of pow_nonce.
    if options.proof_of_work_bits > 0
        && !crate::pow::verify_pow_nonce(
            &proof.quotient_commitment,
            proof.pow_nonce,
            options.proof_of_work_bits,
        )
    {
        return false;
    }

    // 8. DEEP-FRI binding. Run FRI on the batched DEEP polynomial, then
    //    cross-check the FRI's first-layer query openings against a
    //    DEEP value reconstructed from the column-FRI openings at the
    //    same query position. Disagreement means the prover's OOD
    //    claims don't match the committed polynomials.
    let deep_alphas = derive_fri_alphas(&proof.quotient_commitment, 1, options.num_layers);
    if !fri_verify(&proof.deep_fri_proof, &deep_alphas[0], column_options) {
        return false;
    }
    let beta = crate::deep::derive_deep_beta(&proof.quotient_commitment);
    let mut claimed: Vec<u64> = Vec::with_capacity(air.num_columns + 1);
    for c in 0..air.num_columns {
        claimed.push(proof.ood_trace_evals[c]);
    }
    claimed.push(proof.ood_quotient_eval);
    let deep_queries = &proof.deep_fri_proof.layers[0].queries;
    for q in 0..deep_queries.len() {
        let dq = &deep_queries[q];
        let x_q = crate::fri::coset_element(
            options.coset_shift,
            options.domain_log2,
            dq.index_pos,
        );
        let mut p_openings: Vec<u64> = Vec::with_capacity(air.num_columns + 1);
        for c2 in 0..air.num_columns {
            if proof.column_fri_proofs[c2].layers.is_empty()
                || q >= proof.column_fri_proofs[c2].layers[0].queries.len()
            {
                return false;
            }
            p_openings
                .push(proof.column_fri_proofs[c2].layers[0].queries[q].eval_pos);
        }
        if proof.quotient_fri_proof.layers.is_empty()
            || q >= proof.quotient_fri_proof.layers[0].queries.len()
        {
            return false;
        }
        p_openings.push(proof.quotient_fri_proof.layers[0].queries[q].eval_pos);

        let reconstructed =
            crate::deep::reconstruct_deep_value_at(&p_openings, &claimed, x_q, z, beta);
        if dq.eval_pos != reconstructed {
            return false;
        }
    }

    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::air::{fib_air, fib_trace};

    fn default_options() -> FriOptions {
        FriOptions {
            num_layers: 3,
            domain_log2: 4,
            num_queries: 8,
            blowup: 2,
            coset_shift: LDE_COSET_SHIFT,
            proof_of_work_bits: 0,
        }
    }

    #[test]
    fn test_prove_verify_fibonacci_roundtrip() {
        let air = fib_air();
        let trace = fib_trace(16);
        let opts = default_options();

        let proof = plonky3_prove(&air, &trace, opts).expect("prover rejected valid trace");
        let alphas: Vec<Vec<u64>> = vec![vec![], vec![]];
        assert!(plonky3_verify(&air, &proof, &alphas, opts));
    }

    #[test]
    fn test_deep_fri_rejects_tampered_ood_claim() {
        // If the prover tampers with the claimed OOD trace evaluation,
        // the batched DEEP polynomial has a pole at z and the DEEP-FRI
        // cross-check at the queries fails.
        let air = fib_air();
        let trace = fib_trace(16);
        let opts = default_options();
        let proof = plonky3_prove(&air, &trace, opts).expect("prover");
        let alphas: Vec<Vec<u64>> = vec![vec![], vec![]];
        assert!(plonky3_verify(&air, &proof, &alphas, opts));

        let mut bad = Plonky3Proof {
            trace_commitment: proof.trace_commitment,
            quotient_commitment: proof.quotient_commitment,
            column_fri_proofs: proof.column_fri_proofs,
            quotient_fri_proof: proof.quotient_fri_proof,
            boundary_claims: proof.boundary_claims,
            trace_log2: proof.trace_log2,
            ood_trace_evals: proof.ood_trace_evals.clone(),
            ood_trace_next_evals: proof.ood_trace_next_evals,
            ood_quotient_eval: proof.ood_quotient_eval,
            pow_nonce: proof.pow_nonce,
            deep_fri_proof: proof.deep_fri_proof,
        };
        bad.ood_trace_evals[0] = bb_add(bad.ood_trace_evals[0], 1);
        assert!(!plonky3_verify(&air, &bad, &alphas, opts));
    }

    #[test]
    fn test_prove_verify_with_pow_grinding() {
        // Same roundtrip but with PoW enabled (4 bits — small enough that
        // grinding is fast, large enough that the verifier check is
        // non-trivial).
        let air = fib_air();
        let trace = fib_trace(16);
        let mut opts = default_options();
        opts.proof_of_work_bits = 4;
        let proof = plonky3_prove(&air, &trace, opts).expect("prover");
        assert!(plonky3_verify(&air, &proof, &[vec![], vec![]], opts));
        // Tampering with the pow_nonce must invalidate the proof when
        // pow_bits > 0.
        let mut bad = Plonky3Proof {
            trace_commitment: proof.trace_commitment,
            quotient_commitment: proof.quotient_commitment,
            column_fri_proofs: proof.column_fri_proofs,
            quotient_fri_proof: proof.quotient_fri_proof,
            boundary_claims: proof.boundary_claims,
            trace_log2: proof.trace_log2,
            ood_trace_evals: proof.ood_trace_evals,
            ood_trace_next_evals: proof.ood_trace_next_evals,
            ood_quotient_eval: proof.ood_quotient_eval,
            pow_nonce: proof.pow_nonce.wrapping_add(1),
            deep_fri_proof: proof.deep_fri_proof,
        };
        let _ = &mut bad;
        assert!(!plonky3_verify(&air, &bad, &[vec![], vec![]], opts));
    }

    #[test]
    fn test_prove_rejects_invalid_trace() {
        let air = fib_air();
        let mut trace = fib_trace(16);
        // Tamper with transition
        trace.set(7, 1, bb_add(trace.get(7, 1), 1));
        let opts = default_options();
        assert!(plonky3_prove(&air, &trace, opts).is_none());
    }

    #[test]
    fn test_prove_rejects_wrong_width_trace() {
        let air = fib_air();
        let bad = Trace::zeros(3, 16);
        let opts = default_options();
        assert!(plonky3_prove(&air, &bad, opts).is_none());
    }

    #[test]
    fn test_verify_rejects_tampered_boundary_claim() {
        let air = fib_air();
        let trace = fib_trace(16);
        let opts = default_options();

        let mut proof = plonky3_prove(&air, &trace, opts).unwrap();
        // Flip the first boundary claim
        proof.boundary_claims[0] = bb_add(proof.boundary_claims[0], 1);
        let alphas: Vec<Vec<u64>> = vec![vec![], vec![]];
        assert!(!plonky3_verify(&air, &proof, &alphas, opts));
    }

    #[test]
    fn test_verify_rejects_wrong_column_count() {
        let air = fib_air();
        let trace = fib_trace(16);
        let opts = default_options();

        let mut proof = plonky3_prove(&air, &trace, opts).unwrap();
        proof.column_fri_proofs.pop();
        let alphas: Vec<Vec<u64>> = vec![vec![], vec![]];
        assert!(!plonky3_verify(&air, &proof, &alphas, opts));
    }

    #[test]
    fn test_transcript_seed_deterministic() {
        let air = fib_air();
        let trace = fib_trace(16);
        let opts = default_options();
        let proof = plonky3_prove(&air, &trace, opts).unwrap();
        assert_eq!(transcript_seed(&proof), transcript_seed(&proof));
    }

    #[test]
    fn test_transcript_seed_sensitive_to_commitment() {
        let air = fib_air();
        let trace = fib_trace(16);
        let opts = default_options();
        let mut proof = plonky3_prove(&air, &trace, opts).unwrap();
        let seed1 = transcript_seed(&proof);
        proof.trace_commitment[0] ^= 0x01;
        let seed2 = transcript_seed(&proof);
        assert_ne!(seed1, seed2);
    }
}
