# aeskw-hax

A pure-Rust specification of AES Key Wrap (NIST SP 800-38F, RFC 3394) with an
AES-128 key-encryption key, written in the restricted Rust subset that
[hax](https://github.com/hacspec/hax) extracts into Lean. The same source is
a runnable reference implementation and the input to the formal extraction.
The crate is `#![no_std]` and has no production dependencies.

## Standards

- NIST SP 800-38F, Section 6.2 — the KW authenticated-encryption mode.
- RFC 3394 — the AES Key Wrap algorithm (Section 2.2.1 wrap, Section 2.2.2
  unwrap, Section 2.2.3.1 default initial value) and its test vectors
  (Section 4).
- FIPS 197 — the AES-128 block cipher used as the underlying permutation.

KWP (RFC 5649 / SP 800-38F Section 6.3) is not implemented.

## Contents

One module, `src/lib.rs`, in these sections:

| Section | Items |
| --- | --- |
| AES-128 (FIPS 197) | `AES_SBOX`, `AES_INV_SBOX`, `aes128_key_expansion`, `aes128_encrypt`, `aes128_decrypt` |
| Block operations | `xor_block`, `xor_half`, `concat_halves`, `msb64`, `lsb64`, `u64_to_be_bytes` |
| Key Wrap (RFC 3394 Section 2.2) | `aes_wrap`, `aes_unwrap`, `iv_check`, `DEFAULT_IV`, `MAX_BLOCKS` |
| Fixed-size wrappers | `aes_wrap_128`, `aes_unwrap_128`, `aes_wrap_256`, `aes_unwrap_256` |
| Kani harnesses (`#[cfg(kani)]`) | S-box bijectivity, XOR identities, IV check, half-block split/concat |

`aes_wrap` and `aes_unwrap` take the key data as an array of `MAX_BLOCKS`
(8) 64-bit half-blocks and a block count `n` with `2 <= n <= 8`, so key data
of 128 to 512 bits can be wrapped. Only the 128-bit KEK is implemented; the
192- and 256-bit KEK variants of RFC 3394 are not.

All loops have static bounds, all arithmetic is wrapping, and all buffers are
fixed-size arrays; these are the constraints of the hax-extractable subset.

## Test vectors and provenance

| Test | Source |
| --- | --- |
| `kat_rfc3394_4_1_wrap`, `kat_rfc3394_4_1_unwrap` | RFC 3394 Section 4.1 (128-bit key data, 128-bit KEK), transcribed from <https://www.rfc-editor.org/rfc/rfc3394.txt> |
| `kat_aes128_fips197` | FIPS 197 Appendix B |

RFC 3394 Sections 4.2 to 4.6 use 192- or 256-bit KEKs and are therefore
outside what this crate implements. The remaining tests in
`tests/kat_vectors.rs` (roundtrips at 128, 192 and 256 bits of key data,
tampered-ciphertext and wrong-KEK rejection, half-block operations) are
self-consistency checks. `validation.toml` records the same provenance in
machine-readable form.

## Cross-check

`tests/cross_check.rs` compares `aes_wrap_128`, `aes_unwrap_128`,
`aes_wrap_256` and `aes_unwrap_256` against RustCrypto's
[`aes-kw`](https://crates.io/crates/aes-kw) on fixed inputs, in both
directions (each side unwraps the other's ciphertext), and checks that both
reject a tampered ciphertext. `aes-kw` is a dev-dependency only.

## Running the tests

```bash
cargo test --release
```

The Kani harnesses run with `cargo kani` when the
[Kani](https://model-checking.github.io/kani/) model checker is installed;
they are compiled only under `cfg(kani)`.

## Hax extraction

`proofs/lean/extraction/Aeskw_hax.lean` is the Lean output of
`cargo hax into lean` for this crate. The intermediate frontend export is
regenerated with

```bash
cargo hax json
```

which writes `hax_frontend_export.json` (several megabytes; ignored by git).

## License

MIT; see `LICENSE`.
