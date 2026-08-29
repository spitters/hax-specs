# kmac-hax

A Rust specification of KMAC128 and KMAC256 (NIST SP 800-185), written in
the fragment of Rust that the [hax](https://github.com/cryspen/hax) toolchain
extracts to Lean. The crate carries its own Keccak-f[1600] sponge (FIPS 202),
so it has no runtime dependencies.

## Standard

- NIST SP 800-185, *SHA-3 Derived Functions: cSHAKE, KMAC, TupleHash and
  ParallelHash* (encoding functions §2.3, cSHAKE §3, KMAC §4).
- FIPS 202, *SHA-3 Standard: Permutation-Based Hash and Extendable-Output
  Functions* (Keccak-f[1600] §3, sponge construction §4, SHA3-256 and
  SHAKE256 §6).

## Layout

| Path | Contents |
|---|---|
| `src/lib.rs` | The SP 800-185 encoding layer over fixed-size buffers (`left_encode`, `right_encode`, `encode_string_32`, `bytepad`, `kmac128_preimage`, `kmac256_preimage`), and the full construction over byte slices (`kmac128`, `kmac256`, with cSHAKE and the encodings as private helpers) |
| `src/keccak.rs` | Keccak-f[1600], the generic sponge `keccak(rate, delim, input, out)`, `sha3_256`, `shake256` |
| `tests/kmac_kat.rs` | Known-answer tests from the SP 800-185 KMAC samples and FIPS 202 digests |
| `tests/kmac_crosscheck.rs` | Byte-for-byte comparison against KMAC assembled from the RustCrypto `sha3` crate's cSHAKE |
| `proofs/lean/extraction/Kmac_hax.lean` | Lean module produced by `cargo hax into lean` |
| `validation.toml` | Manifest naming the vectors and the test files that assert them |

Code shape of the encoding layer: every loop is a bounded `for i in 0..N`,
every buffer is a fixed-size array, and arithmetic is wrapping. The
preimage functions take a 32-byte key and a 64-byte message and return the
three components `bytepad(encode_string(K), rate) || X || right_encode(L)`
that feed cSHAKE. `kmac128` and `kmac256` accept keys, messages,
customization strings and output lengths of any size.

## Public API

```rust
pub fn left_encode(x: usize) -> Encoded9;
pub fn right_encode(x: usize) -> Encoded9;
pub fn encode_string_32(s: &[u8; 32], s_len: usize) -> Encoded41;
pub fn bytepad(x_data: &[u8; 41], x_len: usize, w: usize) -> [u8; 168];
pub fn kmac128_preimage(key: &[u8; 32], data: &[u8; 64], out_bits: usize) -> KmacPreimage;
pub fn kmac256_preimage(key: &[u8; 32], data: &[u8; 64], out_bits: usize) -> KmacPreimage;
pub fn kmac128(key: &[u8], data: &[u8], out: &mut [u8], s: &[u8]);
pub fn kmac256(key: &[u8], data: &[u8], out: &mut [u8], s: &[u8]);
pub fn keccak::keccak(rate: usize, delim: u8, input: &[u8], out: &mut [u8]);
pub fn keccak::sha3_256(input: &[u8]) -> [u8; 32];
pub fn keccak::shake256(input: &[u8], out: &mut [u8]);
```

## Test vectors

`tests/kmac_kat.rs` asserts the six KMAC samples published by NIST alongside
SP 800-185 (`KMAC_samples.pdf`): Samples 1–3 are KMAC128 with L = 256 and
Samples 4–6 are KMAC256 with L = 512, all with key `40 41 … 5F`, data either
`00 01 02 03` or `00 01 … C7`, and customization string either empty or
`"My Tagged Application"`. The sponge is checked first against the FIPS 202
digests SHA3-256("abc") and the first 32 bytes of SHAKE256("").

`tests/kmac_crosscheck.rs` compares `kmac128` and `kmac256` with KMAC
assembled from `sha3::CShake128` and `sha3::CShake256` (RustCrypto `sha3
0.10`) for key lengths 4, 32, 64 and 200 bytes, message lengths 0, 1, 4, 31,
32, 135, 136, 168 and 500 bytes, three customization strings and output
lengths 16, 32, 64 and 200 bytes; `sha3_256` and `shake256` are compared
with `sha3::Sha3_256` and `sha3::Shake256` on the same message lengths.

## Running the tests

```sh
cargo test --release
```

## hax extraction

The Lean module under `proofs/lean/extraction/` is generated from `src/` by
the hax toolchain. To regenerate it, or to produce the frontend JSON:

```sh
cargo hax into lean
cargo hax json
```

`cargo hax json` writes `hax_frontend_export.json`, which is ignored by git.

## License

MIT; see `LICENSE`.
