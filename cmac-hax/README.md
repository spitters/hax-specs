# cmac-hax

A `no_std` Rust specification of AES-128 CMAC (NIST SP 800-38B), written in
the fragment of Rust that the [hax](https://github.com/cryspen/hax) toolchain
extracts to Lean. The crate carries its own AES-128 (FIPS 197) block cipher,
so it has no runtime dependencies.

## Standard

- NIST SP 800-38B, *Recommendation for Block Cipher Modes of Operation: The
  CMAC Mode for Authentication* (subkey generation §6.1, MAC generation §6.2).
- FIPS 197, *Advanced Encryption Standard* (key expansion §5.2, the cipher §5.1).

Only AES-128 is implemented; AES-192 and AES-256 keys are not supported.

## Layout

| Path | Contents |
|---|---|
| `src/lib.rs` | The whole specification: AES-128 key expansion and single-block encryption; GF(2^128) doubling `dbl`; `cmac_subkey_gen`; `cmac` over pre-split blocks; `cmac_bytes` over a flat byte slice; Kani harnesses under `#[cfg(kani)]` |
| `tests/kat_vectors.rs` | Known-answer tests from SP 800-38B Appendix D.1 and FIPS 197 Appendix B |
| `tests/cmac_crosscheck.rs` | Byte-for-byte comparison against the RustCrypto `cmac` crate |
| `proofs/lean/extraction/Cmac_hax.lean` | Lean module produced by `cargo hax into lean` |
| `validation.toml` | Manifest naming the vectors and the test files that assert them |

Code shape: every loop is a bounded `for i in 0..N`, every buffer is a
fixed-size array, and there is no heap allocation. Messages are bounded by
`MAX_BLOCKS = 64` blocks (1024 bytes); `cmac_bytes` takes the message slice
together with its length.

## Public API

```rust
pub fn aes128_key_expansion(key: &AesKey) -> RoundKeys;
pub fn aes128_encrypt(key: &AesKey, plaintext: &Block) -> Block;
pub fn dbl(block: &Block) -> Block;
pub fn cmac_subkey_gen(key: &AesKey) -> (Block, Block);
pub fn cmac(key: &AesKey, blocks: &[[u8; 16]; MAX_BLOCKS], num_blocks: usize, msg_len: usize) -> Block;
pub fn cmac_bytes(key: &AesKey, msg: &[u8], msg_len: usize) -> Block;
```

## Test vectors

`tests/kat_vectors.rs` asserts the AES-128 example values of NIST SP 800-38B
Appendix D.1 (key `2b7e1516 28aed2a6 abf71588 09cf4f3c`): the subkeys K1 and
K2, and the tags for messages of 0, 16, 40 and 64 bytes. The same four
AES-128 examples are reproduced in RFC 4493 §4. The AES-128 block cipher is
checked against FIPS 197 Appendix B.

`tests/cmac_crosscheck.rs` compares `cmac_bytes` with `cmac::Cmac<aes::Aes128>`
from RustCrypto (`cmac 0.7`, `aes 0.8`) on the SP 800-38B key and on two
further keys, for message lengths 0, 1, 15, 16, 17, 32, 40, 48 and 64 bytes.

## Running the tests

```sh
cargo test --release
```

The Kani harnesses in `src/lib.rs` run with `cargo kani` when the
[Kani](https://github.com/model-checking/kani) model checker is installed.

## hax extraction

The Lean module under `proofs/lean/extraction/` is generated from `src/lib.rs`
by the hax toolchain. To regenerate it, or to produce the frontend JSON:

```sh
cargo hax into lean
cargo hax json
```

`cargo hax json` writes `hax_frontend_export.json`, which is ignored by git.

## License

MIT; see `LICENSE`.
