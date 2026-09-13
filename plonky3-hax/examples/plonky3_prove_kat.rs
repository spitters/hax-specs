//! Prints the intermediate values of `plonky3_prove` on the Fibonacci AIR
//! (commitments, challenges, OOD point and evaluations, DEEP values,
//! proof-of-work nonces, transcript seed) for trace heights 8 and 16.
//!
//! Run with `cargo run --release --example plonky3_prove_kat`. The trace
//! commitments and transcript seeds printed agree with the regression
//! values in `tests/kat_vectors.rs`. All values are outputs of this crate.

use plonky3_hax::air::{air_max_degree, fib_air, fib_trace};
use plonky3_hax::deep::{combine_deep_polys, compute_deep_poly_lde, derive_deep_beta};
use plonky3_hax::ood::{derive_ood_point, evaluate_quotient_at, evaluate_trace_at};
use plonky3_hax::plonky3::{
    commit_trace_lde, compute_trace_lde, derive_fri_alphas, derive_query_indices,
    plonky3_prove, transcript_seed, LDE_COSET_SHIFT,
};
use plonky3_hax::pow::grind_pow_nonce;
use plonky3_hax::quotient::{
    commit_quotient_lde, compute_quotient_lde, derive_constraint_alphas,
};
use plonky3_hax::specs::baby_bear::bb_root_of_unity;
use plonky3_hax::specs::baby_bear::bb_mul;
use plonky3_hax::fri::FriOptions;

fn hex32(b: &[u8; 32]) -> String {
    b.iter().map(|x| format!("{:02x}", x)).collect()
}

fn dump_phase(height: usize, num_layers: usize, domain_log2: u32, num_queries: usize, blowup: usize) {
    let air = fib_air();
    let trace = fib_trace(height);
    let trace_log2 = (height as u64).trailing_zeros();
    let n: usize = 1usize << domain_log2;

    println!("=== height {height} (trace_log2={trace_log2}, domain_log2={domain_log2}, n={n}) ===");
    println!("air_max_degree (bare) = {}", air_max_degree(&air));
    println!("selector-inclusive quotient degree = {} (bare {} + 1 selector)", air_max_degree(&air) + 1, air_max_degree(&air));
    println!("blowup factor n/h = {}", n / height);

    let lde = compute_trace_lde(&trace, domain_log2, LDE_COSET_SHIFT);
    let trace_commitment = commit_trace_lde(&lde, trace.width, domain_log2);
    println!("trace_commitment = {}", hex32(&trace_commitment));

    let constraint_alphas = derive_constraint_alphas(&trace_commitment, air.transitions.len());
    println!("constraint_alphas = {:?}", constraint_alphas);

    let quotient_lde = compute_quotient_lde(
        &lde, &air, &constraint_alphas, trace.width, domain_log2, trace_log2, LDE_COSET_SHIFT,
    );
    let quotient_commitment = commit_quotient_lde(&quotient_lde);
    println!("quotient_commitment = {}", hex32(&quotient_commitment));

    let z = derive_ood_point(&quotient_commitment, trace_log2, domain_log2);
    let omega_h = bb_root_of_unity(trace_log2);
    let g_z = bb_mul(omega_h, z);
    println!("ood_point z = {z}");
    println!("g_z = {g_z}");
    let ood_trace_evals = evaluate_trace_at(&trace, z);
    let ood_trace_next_evals = evaluate_trace_at(&trace, g_z);
    let ood_quotient_eval = evaluate_quotient_at(&quotient_lde, domain_log2, LDE_COSET_SHIFT, z);
    println!("ood_trace_evals = {:?}", ood_trace_evals);
    println!("ood_trace_next_evals = {:?}", ood_trace_next_evals);
    println!("ood_quotient_eval = {ood_quotient_eval}");

    let beta = derive_deep_beta(&quotient_commitment);
    println!("deep_beta = {beta}");

    let _ = (num_layers, num_queries, blowup);
    // PoW with default 0 bits → nonce 0.
    let nonce = grind_pow_nonce(&quotient_commitment, 0, 16).unwrap_or(0);
    println!("pow_nonce (bits=0) = {nonce}");

    // 4-bit PoW grind on the quotient commitment seed (deterministic).
    let nonce4 = grind_pow_nonce(&quotient_commitment, 4, 4096);
    println!("pow_nonce (bits=4) = {:?}", nonce4);

    // derive_fri_alphas / query_indices for the trace commitment.
    let column_alphas = derive_fri_alphas(&trace_commitment, trace.width, num_layers);
    let query_indices = derive_query_indices(&trace_commitment, num_queries, n);
    println!("column_alphas = {:?}", column_alphas);
    println!("query_indices = {:?}", query_indices);

    // First DEEP poly column 0, first 2 entries.
    let mut p0 = vec![0u64; n];
    for j in 0..n { p0[j] = lde[j * trace.width]; }
    let deep0 = compute_deep_poly_lde(&p0, ood_trace_evals[0], z, domain_log2, LDE_COSET_SHIFT);
    println!("deep_poly_col0[0..4] = {:?}", &deep0[0..4.min(deep0.len())]);
    let combined = combine_deep_polys(std::slice::from_ref(&deep0), beta);
    println!("combined_deep[0..2] = {:?}", &combined[0..2.min(combined.len())]);

    // Full proof transcript seed.
    let opts = FriOptions {
        num_layers, domain_log2, num_queries, blowup,
        coset_shift: LDE_COSET_SHIFT, proof_of_work_bits: 0,
    };
    let proof = plonky3_prove(&air, &trace, opts).expect("prover");
    println!("transcript_seed = {}", hex32(&transcript_seed(&proof)));
    println!("boundary_claims = {:?}", proof.boundary_claims);
    println!();
}

fn main() {
    dump_phase(8, 3, 5, 8, 2);
    dump_phase(16, 3, 5, 8, 2);
}
