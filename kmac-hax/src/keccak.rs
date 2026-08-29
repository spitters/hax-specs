//! FIPS-202 (SHA-3 / SHAKE) — byte-exact pure-Rust Keccak, ported into this
//! crate so the KMAC construction runs over a real sponge with zero external
//! dependencies.
//!
//! This is the Keccak-f\[1600\] permutation plus a generic sponge (variable rate,
//! variable domain-separation byte, arbitrary-length squeeze). cSHAKE / KMAC in
//! `crate` drive this directly.

/// Keccak-f\[1600\] round constants.
const RC: [u64; 24] = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
    0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
    0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
];

/// Rotation offsets, in the ρ/π traversal order.
const ROTC: [u32; 24] = [
    1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14,
    27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44,
];

/// Lane permutation (π), in the ρ/π traversal order.
const PILN: [usize; 24] = [
    10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4,
    15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1,
];

/// The Keccak-f\[1600\] permutation, in place on 25 lanes of 64 bits.
fn keccakf(st: &mut [u64; 25]) {
    let mut bc = [0u64; 5];
    for round in 0..24 {
        // θ
        for i in 0..5 {
            bc[i] = st[i] ^ st[i + 5] ^ st[i + 10] ^ st[i + 15] ^ st[i + 20];
        }
        for i in 0..5 {
            let t = bc[(i + 4) % 5] ^ bc[(i + 1) % 5].rotate_left(1);
            for jj in 0..5 {
                let j = jj * 5;
                st[j + i] ^= t;
            }
        }
        // ρ and π
        let mut t = st[1];
        for i in 0..24 {
            let j = PILN[i];
            let tmp = st[j];
            st[j] = t.rotate_left(ROTC[i]);
            t = tmp;
        }
        // χ
        for jj in 0..5 {
            let j = jj * 5;
            for i in 0..5 {
                bc[i] = st[j + i];
            }
            for i in 0..5 {
                st[j + i] ^= (!bc[(i + 1) % 5]) & bc[(i + 2) % 5];
            }
        }
        // ι
        st[0] ^= RC[round];
    }
}

/// XOR a `rate`-byte block into the state (little-endian lanes). `rate` must be
/// a multiple of 8.
fn xor_block(st: &mut [u64; 25], block: &[u8], rate: usize) {
    let mut i = 0;
    while i < rate / 8 {
        let b = i * 8;
        let lane = (block[b] as u64)
            | ((block[b + 1] as u64) << 8)
            | ((block[b + 2] as u64) << 16)
            | ((block[b + 3] as u64) << 24)
            | ((block[b + 4] as u64) << 32)
            | ((block[b + 5] as u64) << 40)
            | ((block[b + 6] as u64) << 48)
            | ((block[b + 7] as u64) << 56);
        st[i] ^= lane;
        i += 1;
    }
}

/// Extract `out.len()` bytes from the state (little-endian lanes), `out.len() <= rate`.
fn extract(st: &[u64; 25], out: &mut [u8]) {
    for k in 0..out.len() {
        let lane = st[k / 8];
        out[k] = (lane >> (8 * (k % 8))) as u8;
    }
}

/// Generic sponge: absorb `input`, then squeeze `out.len()` bytes.
/// `rate` in bytes; `delim` is the domain-separation/padding byte.
pub fn keccak(rate: usize, delim: u8, input: &[u8], out: &mut [u8]) {
    let mut st = [0u64; 25];
    let mut block = [0u8; 168]; // max rate (SHAKE-128)

    // Absorb full blocks.
    let mut pos = 0;
    while input.len() - pos >= rate {
        xor_block(&mut st, &input[pos..pos + rate], rate);
        keccakf(&mut st);
        pos += rate;
    }

    // Final block with pad10*1 padding.
    let rem = input.len() - pos;
    for i in 0..rate {
        block[i] = 0;
    }
    for i in 0..rem {
        block[i] = input[pos + i];
    }
    block[rem] = delim;
    block[rate - 1] |= 0x80;
    xor_block(&mut st, &block[..rate], rate);
    keccakf(&mut st);

    // Squeeze.
    let mut outpos = 0;
    while outpos < out.len() {
        let n = if out.len() - outpos < rate { out.len() - outpos } else { rate };
        extract(&st, &mut out[outpos..outpos + n]);
        outpos += n;
        if outpos < out.len() {
            keccakf(&mut st);
        }
    }
}

/// SHA3-256 (rate 136, delim 0x06). Used only for the Keccak self-check.
pub fn sha3_256(input: &[u8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    keccak(136, 0x06, input, &mut out);
    out
}

/// SHAKE-256 (rate 136, delim 0x1f), arbitrary output length.
pub fn shake256(input: &[u8], out: &mut [u8]) {
    keccak(136, 0x1f, input, out);
}
