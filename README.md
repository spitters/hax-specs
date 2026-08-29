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
| [`aesgcmsiv-hax`](aesgcmsiv-hax) | AES-GCM-SIV, RFC 8452 (AES-128) | RFC 8452 Appendix C.1 | — |
| [`aeskw-hax`](aeskw-hax) | AES Key Wrap, NIST SP 800-38F / RFC 3394 (AES-128 KEK) | RFC 3394 §4.1 | RustCrypto `aes-kw` |
| [`cmac-hax`](cmac-hax) | AES-CMAC, NIST SP 800-38B (AES-128) | SP 800-38B Appendix D.1 | RustCrypto `cmac` |
| [`hmacdrbg-hax`](hmacdrbg-hax) | HMAC_DRBG with SHA-256, NIST SP 800-90A Rev. 1 | NIST CAVP DRBGVS | — |

The pure specifications of the libcrux primitives (hashes, HMAC, HKDF, AES,
GCM, ChaCha20-Poly1305, X25519, Ed25519, P-256, ECDSA) live in the separate
crate [`libcrux-specs-hax`](https://github.com/spitters/libcrux-specs-hax).

## Layout of a crate

| Path | Contents |
| --- | --- |
| `src/lib.rs` | The specification, in the hax-extractable fragment: bounded `for` loops, fixed-size arrays, no heap allocation |
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
