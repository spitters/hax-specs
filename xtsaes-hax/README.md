# xtsaes-hax

XTS-AES-128 (IEEE Std 1619-2018) written as a hax-extractable Rust
specification. The crate is `no_std`, has no dependencies, and uses only
bounded `for` loops, wrapping arithmetic, and fixed-size arrays, so that
[hax](https://github.com/cryspen/hax) can translate it to a proof assistant.
It is a reference specification: it is not constant-time and is not tuned
for speed.

## Standards

- IEEE Std 1619-2018, *IEEE Standard for Cryptographic Protection of Data on
  Block-Oriented Storage Devices*: the XTS-AES tweakable block cipher
  (Section 5), the GF(2^128) tweak multiplication by alpha with the
  polynomial x^128 + x^7 + x^2 + x + 1 in little-endian convention
  (Section 5.2), and the test vectors (Annex B). The 2018 edition supersedes
  IEEE Std 1619-2007; the algorithm and the Annex B vectors are unchanged.
- FIPS 197 for the AES-128 block cipher, implemented in the same module.

Supported parameters: two 16-byte keys (Key1 for data, Key2 for the tweak);
a 16-byte tweak, normally the data-unit number in little-endian order
(`sector_number_to_tweak`); data units of 1 to 32 whole 16-byte blocks
(`MAX_BLOCKS`, 512 bytes). Callers pass a fixed-size block array together
with the number of valid blocks. Ciphertext stealing for a partial final
block (Section 5.3.1) is not implemented.

## Modules

The crate is a single module, `src/lib.rs`, in four parts:

| Part | Items |
|---|---|
| AES-128 (FIPS 197) | `AES_SBOX`, `AES_INV_SBOX`, `aes128_key_expansion`, `aes128_encrypt`, `aes128_decrypt`, `xor_block` |
| Tweak arithmetic (IEEE 1619, Section 5.2) | `gf128_mul_alpha`, `sector_number_to_tweak` |
| Single block (IEEE 1619, Section 5.3.1 and 5.4.1) | `xts_encrypt_block`, `xts_decrypt_block` |
| Data unit (IEEE 1619, Section 5.3 and 5.4) | `xts_encrypt_sector`, `xts_decrypt_sector` |

A `#[cfg(kani)]` module holds bounded model-checking harnesses for the XOR,
S-box, and alpha-multiplication helpers; they are compiled only under Kani.

## Test vectors and their provenance

| File | Source | Coverage |
|---|---|---|
| `src/lib.rs` (unit tests) | FIPS 197, Appendix B; IEEE 1619, Annex B, Vector 1 | one AES-128 block; one 32-byte data unit |
| `tests/kat_vectors.rs` | IEEE 1619, Annex B, Vectors 1-4; FIPS 197, Appendix C.1 | 32-byte data units under three key pairs and two tweaks; a 512-byte (32-block) data unit; one AES-128 block |
| `tests/xts_crosscheck.rs` | RustCrypto `xts-mode` 0.5 with `aes` 0.8 | data units of 1 to 32 blocks, four key pairs, five data-unit numbers, all-zero and all-0xFF data |

The Annex B vectors were transcribed from IEEE Std 1619-2007 and are
identical in the 2018 edition. Vectors 1-3 are 32-byte data units; Vector 4
is a 512-byte data unit whose first two and last two blocks are asserted.
Vectors 15-19 (partial final block, ciphertext stealing) are not included
because the crate does not implement ciphertext stealing.

The cross-check compares `xts_encrypt_sector` and `xts_decrypt_sector` with
the RustCrypto `xts-mode` crate, an independent implementation, in both
directions: our ciphertext equals theirs, our decryption of their
ciphertext recovers the plaintext, and their decryption of ours does. A
ciphertext with one flipped bit is checked not to decrypt to the original
block. `xts-mode`, `aes`, and `hex-literal` are dev-dependencies only.

`validation.toml` records the vector sources for each test file.

## Running the tests

```
cargo test --release
cargo clippy --all-targets
cargo doc --no-deps
```

## hax extraction

`proofs/lean/extraction/Xtsaes_hax.lean` is the Lean output of the hax
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
