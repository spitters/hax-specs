# aesgcmsiv-hax

A pure-Rust, `no_std` specification of AES-GCM-SIV (RFC 8452) written in the
subset of Rust that the [hax](https://github.com/hacspec/hax) toolchain
extracts to proof assistants. All loops are bounded (`for i in 0..N`), all
arithmetic is explicit or wrapping, and all buffers are fixed-size arrays.
Messages and associated data are bounded by `MAX_BLOCKS = 32` blocks
(512 bytes) each.

The crate is a specification, not an implementation for deployment: the AES
core is a table-based reference, POLYVAL multiplication is bit-serial, and no
effort is made toward constant-time execution or performance.

## Standard

RFC 8452, *AES-GCM-SIV: Nonce Misuse-Resistant Authenticated Encryption*.
Only the AES-128 variant (AEAD_AES_128_GCM_SIV) is specified; keys are
16 bytes, nonces 12 bytes, tags 16 bytes.

## Modules

The crate is a single module, `src/lib.rs`, in these sections:

| Section | Items | Reference |
|---|---|---|
| AES-128 | `AES_SBOX`, `aes128_key_expansion`, `aes128_encrypt` | FIPS 197 |
| POLYVAL | `le_u64`, `put_le_u64`, `polyval_mul`, `polyval` | RFC 8452 Section 3 |
| Key derivation | `derive_keys` | RFC 8452 Section 4 |
| CTR mode | `gcm_siv_ctr_crypt` (private) | RFC 8452 Section 6 |
| AEAD | `bytes_to_blocks`, `blocks_to_bytes`, `aes_gcm_siv_seal`, `aes_gcm_siv_open` | RFC 8452 Section 5 |

`aes_gcm_siv_seal` returns the ciphertext as padded blocks with its block
count and the tag separately; `aes_gcm_siv_open` returns `None` on tag
mismatch. Two Kani harnesses (`xor_self_is_zero`, `polyval_single_zero`) are
gated behind `cfg(kani)`.

## Test vectors

`tests/kat_vectors.rs` and the unit tests in `src/lib.rs` assert the
following literals, transcribed from
<https://www.rfc-editor.org/rfc/rfc8452.txt> and FIPS 197:

- RFC 8452 Appendix C.1 (AEAD_AES_128_GCM_SIV), cases 1–10 and 14:
  ciphertext and tag for each, the record authentication and encryption
  keys, and the POLYVAL results printed for cases 7 and 14.
- RFC 8452 Appendix A, the POLYVAL worked example.
- FIPS 197 Appendix B, the AES-128 block `3243f6a8…` under key `2b7e1516…`.

The remaining tests are self-consistency checks (seal/open roundtrips,
tampered ciphertext and wrong key rejected). `validation.toml` records the
provenance of the vectors in machine-readable form. Appendix C.2
(AEAD_AES_256_GCM_SIV) is not covered because the crate specifies AES-128
only. No third-party implementation is used as a crosscheck; the crate has
no dependencies.

## Running the tests

```
cargo test --release
```

## Hax extraction

`proofs/lean/extraction/Aesgcmsiv_hax.lean` is the Lean 4 output of the hax
Lean backend for this crate. `hax_frontend_export.json` is the hax frontend
export from which backends are run; it is regenerated with

```
cargo hax json
```

and is ignored by `.gitignore` because of its size.

## License

MIT; see `LICENSE`.
