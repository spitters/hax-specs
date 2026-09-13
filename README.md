# hax-specs

Rust specifications of cryptographic primitives and protocols written in the
subset of Rust that the [hax](https://github.com/cryspen/hax) toolchain
extracts to proof assistants. Each crate is a runnable reference
implementation of one standard, carrying the known-answer tests printed in
that standard and, where an independent implementation exists, a byte-level
cross-check against it as a dev-dependency.

The crates are the sources from which the Lean models used in the
[CatCrypt](https://github.com/spitters) security proofs are extracted. A crate
is added here once its tests, cross-checks and documentation stand on their
own; the standard it implements and the provenance of its vectors are stated
in its README and in `validation.toml`.

## Crates

| Crate | Standard | Vectors | Cross-check |
| --- | --- | --- | --- |
| [`aesccm-hax`](aesccm-hax) | AES-CCM, NIST SP 800-38C / RFC 3610 | RFC 3610 §8 Packet Vectors 1–24 | RustCrypto `ccm` |
| [`aesgcm-hax`](aesgcm-hax) | AES-GCM, NIST SP 800-38D (AES-128/256, 96-bit IV) | NIST CAVP GCMVS encrypt and decrypt files, FIPS 197 Appendix C | RustCrypto `aes-gcm` |
| [`aesgcmsiv-hax`](aesgcmsiv-hax) | AES-GCM-SIV, RFC 8452 (AES-128) | RFC 8452 Appendix C.1 | — |
| [`aeskw-hax`](aeskw-hax) | AES Key Wrap, NIST SP 800-38F / RFC 3394 (AES-128 KEK) | RFC 3394 §4.1 | RustCrypto `aes-kw` |
| [`cmac-hax`](cmac-hax) | AES-CMAC, NIST SP 800-38B (AES-128) | SP 800-38B Appendix D.1 | RustCrypto `cmac` |
| [`ctrdrbg-hax`](ctrdrbg-hax) | CTR_DRBG with AES-128 (no derivation function), NIST SP 800-90A Rev. 1 | NIST CAVP DRBGVS (no_reseed, pr_false, pr_true) | — |
| [`hashdrbg-hax`](hashdrbg-hax) | Hash_DRBG with SHA-256, NIST SP 800-90A Rev. 1 | NIST CAVP DRBGVS (no_reseed, pr_false, pr_true), NIST worked example | — |
| [`hmacdrbg-hax`](hmacdrbg-hax) | HMAC_DRBG with SHA-256, NIST SP 800-90A Rev. 1 | NIST CAVP DRBGVS | — |
| [`kbkdf-hax`](kbkdf-hax) | KBKDF counter mode with HMAC-SHA256, NIST SP 800-108 Rev. 1 | NIST CAVP KDFCTR_gen (HMAC_SHA256, counter before fixed data, 32-bit counter) | — |
| [`kmac-hax`](kmac-hax) | KMAC128/256 over cSHAKE, NIST SP 800-185 / FIPS 202 | SP 800-185 samples 1–6, FIPS 202 digests | RustCrypto `sha3` (cSHAKE) |
| [`plonky3-hax`](plonky3-hax) | Plonky3 Baby Bear field (p = 2^31 − 2^27 + 1) and Poseidon2 width 16 (`default_babybear_poseidon2_16`), with a reference STARK that follows no published specification | Plonky3 `p3-baby-bear` 0.5.2 test `test_default_babybear_poseidon2_width_16` (recorded by Plonky3) | Polygon `p3-baby-bear`, `p3-poseidon2` 0.5 |
| [`xtsaes-hax`](xtsaes-hax) | XTS-AES-128, IEEE Std 1619-2018 (whole blocks) | IEEE 1619 Annex B Vectors 1–4, FIPS 197 Appendix C.1 | RustCrypto `xts-mode` |

The pure specifications of the libcrux primitives (hashes, HMAC, HKDF, AES,
GCM, ChaCha20-Poly1305, X25519, Ed25519, P-256, ECDSA) live in the separate
crate [`libcrux-specs-hax`](https://github.com/spitters/libcrux-specs-hax).

## Layout of a crate

| Path | Contents |
| --- | --- |
| `src/lib.rs` | The specification, in the hax-extractable fragment: bounded `for` loops, fixed-size arrays, no heap allocation (the reference STARK of `plonky3-hax` uses `Vec`; its field and permutation modules follow the rule) |
| `tests/` | Known-answer tests and cross-checks |
| `validation.toml` | The standard, the vector provenance and the test files that assert them |
| `proofs/lean/extraction/` | The Lean module produced by `cargo hax into lean` |
| `README.md` | Standard, API, vectors, cross-check |

## Building and testing

```sh
cargo test --release            # every crate
cargo test --release -p cmac-hax
```

The hax frontend export of a crate (`hax_frontend_export.json`, not tracked)
is produced inside the crate directory with `cargo hax json`; the Lean module
with `cargo hax into lean`. Both need the `cargo-hax` frontend from the hax
repository.
CI also runs the syntax-level pre-check `hax-lint src/*.rs` from
[hax-treesitter](https://github.com/spitters/hax-skills) over every crate.

## License

MIT; see [`LICENSE`](LICENSE). Each crate carries the same license.
