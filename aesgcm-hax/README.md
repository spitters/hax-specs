# aesgcm-hax

AES-GCM (Galois/Counter Mode) written as a hax-extractable Rust
specification, with AES-128 and AES-256 and the GHASH multiplication
implemented in the crate. The crate is `no_std`, has no dependencies, and
uses bounded `for` loops, wrapping arithmetic, and fixed-size arrays, so
that [hax](https://github.com/cryspen/hax) can translate it to a proof
assistant. It is a reference specification: it is not constant-time and is
not tuned for speed.

## Standards

- NIST SP 800-38D, *Recommendation for Block Cipher Modes of Operation:
  Galois/Counter Mode (GCM) and GMAC* (GHASH in Section 6.3, the length
  block in Section 6.4, `J0` and `inc32` in Section 7.1).
- FIPS 197 for the AES-128 and AES-256 block ciphers.

Supported parameters: 16-byte (AES-128) or 32-byte (AES-256) key; 96-bit
IV only; 128-bit tag. The fixed-shape interface in `gcm` takes a 64-byte
plaintext and one 16-byte block of associated data; the variable-length
interface in `realgcm` takes byte slices of any length.

## Modules

| Module | Items |
|---|---|
| `types` | `AesKey`, `AesBlock`, `GcmNonce`, `GcmTag`, `GcmState` (fixed-size aliases) |
| `aes` | `AesCipher` trait (one AES-128 block encryption) |
| `aes_impl` | `key_expansion_128`, `aes128_encrypt_block`, `key_expansion_256`, `aes256_encrypt_block`, `RealAes` (FIPS 197) |
| `ghash_impl` | `ghash_mul`, `ghash_multiply` (GF(2^128) multiplication, SP 800-38D Section 6.3) |
| `counter` | `xor_blocks`, `make_j0`, `inc32`, `gctr_one_block` (Section 7.1) |
| `gcm` | `GcmCrypto` trait, `make_len_block`, `ghash_step`, `ghash_compute`, `gcm_encrypt`, `gcm_decrypt`, `tags_equal` (fixed-shape GCM over the traits) |
| `realgcm` | `RealGcm` (the concrete backend), `AesVariant`, `gcm_encrypt_var`, `gcm_decrypt_var` (variable-length GCM for AES-128 and AES-256) |

`gcm_decrypt` returns `None`, and `gcm_decrypt_var` returns `false` without
writing the plaintext, when the tag does not verify. The `AesCipher` and
`GcmCrypto` traits let an extraction backend treat the block cipher and the
field multiplication as opaque primitives; `RealGcm` implements both with
the functions of this crate.

## Test vectors and their provenance

| File | Source | Coverage |
|---|---|---|
| `tests/kat_vectors.rs` | FIPS 197, Appendix C.1 and C.3 | one AES-128 block, one AES-256 block |
| `tests/kat_vectors.rs` | NIST CAVP GCMVS `gcmEncryptExtIV128.rsp`, `gcmEncryptExtIV256.rsp` (CAVS 14.0, 2012-08-31), Count 0 | 96-bit IV, 128-bit tag; PT 128 and 256 bits, AAD 0 and 128 bits |
| `tests/cavp_decrypt_vectors.rs` | NIST CAVP GCMVS `gcmDecrypt128.rsp`, `gcmDecrypt256.rsp` (CAVS 14.0, 2012-08-31), Count 0 to 6 | 96-bit IV, 128-bit PT, AAD and tag; ten accepted and four `FAIL` (rejected-tag) vectors |
| `tests/kat_vectors.rs` | RustCrypto `aes-gcm` 0.10.3 | AES-128 and AES-256, payloads of 0, 1, 16 and 60 bytes with and without associated data, and the fixed-shape `gcm_encrypt` |
| `src/lib.rs` (unit tests) | SP 800-38D Section 7.1 | `inc32` carry and wrap, `J0`, block XOR, round trip, tamper rejection |

The CAVP response files are the GCMVS sample vectors published by NIST
(`csrc.nist.gov/groups/STM/cavp/documents/mac/gcmtestvectors/`), copied
verbatim. Each encrypt vector test computes `(CT, Tag)` with
`gcm_encrypt_var`, compares both with the response file byte for byte, and
checks that `gcm_decrypt_var` recovers the plaintext. Each decrypt vector
test feeds `(Key, IV, CT, AAD, Tag)` to `gcm_decrypt_var` and asserts the
expected plaintext, or rejection with the output buffer untouched for a
`FAIL` vector.

The cross-check compares `ciphertext || tag` from `gcm_encrypt_var` with
the RustCrypto `aes-gcm` crate, an independent implementation, on inputs
the CAVP samples do not cover: the empty message, a one-byte message, and a
60-byte message with a partial final block. `aes-gcm` is a dev-dependency only.

`validation.toml` records the vector sources for each test file.

## Running the tests

```
cargo test --release
cargo clippy --all-targets
cargo doc --no-deps
```

## hax extraction

`proofs/lean/extraction/Aesgcm_hax.lean` is the Lean output of the hax
Lean backend for this crate. To regenerate the frontend export and the
extraction with a hax toolchain installed:

```
cargo hax json
cargo hax into lean
```

`hax_frontend_export.json` is the intermediate produced by the first
command; it is ignored by git.

## License

MIT; see `LICENSE`.
