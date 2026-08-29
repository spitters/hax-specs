# aesccm-hax

AES-128-CCM (Counter with CBC-MAC) written as a hax-extractable Rust
specification. The crate is `no_std`, has no dependencies, and uses only
bounded `for` loops, wrapping arithmetic, and fixed-size arrays, so that
[hax](https://github.com/cryspen/hax) can translate it to a proof assistant.
It is a reference specification: it is not constant-time and is not tuned
for speed.

## Standards

- NIST SP 800-38C, *Recommendation for Block Cipher Modes of Operation: The
  CCM Mode for Authentication and Confidentiality* (block formatting in
  Appendix A: B0, the associated-data length encoding, counter blocks).
- RFC 3610, *Counter with CBC-MAC (CCM)*, whose Section 8 supplies the test
  vectors.
- FIPS 197 for the AES-128 block cipher, implemented in the same module.

Supported parameters: 16-byte key; nonce length 7 to 13 bytes; tag length
4, 6, 8, 10, 12, 14, or 16 bytes; payload and associated data each at most
256 bytes (`MAX_MSG`, `MAX_AAD`). Callers pass fixed-size buffers together
with the number of valid bytes.

## Modules

The crate is a single module, `src/lib.rs`, in four parts:

| Part | Items |
|---|---|
| AES-128 (FIPS 197) | `AES_SBOX`, `aes128_key_expansion`, `aes128_encrypt`, `xor_block` |
| CCM block formatting (SP 800-38C, Appendix A) | `format_b0`, `format_ctr_block`, `ctr_increment` |
| CBC-MAC | `ccm_cbc_mac` |
| AEAD interface | `ccm_encrypt`, `ccm_decrypt` |

`ccm_decrypt` returns `None` when the tag does not verify. A `#[cfg(kani)]`
module holds bounded model-checking harnesses for the AES helpers; they are
compiled only under Kani.

## Test vectors and their provenance

| File | Source | Coverage |
|---|---|---|
| `src/lib.rs` (unit tests) | FIPS 197, Appendix B | one AES-128 block |
| `tests/kat_vectors.rs` | RFC 3610, Section 8, Packet Vectors #1-#4 | 8-byte tags, 8- and 12-byte headers, one key |
| `tests/rfc3610_vectors_5_24.rs` | RFC 3610, Section 8, Packet Vectors #5-#24 | 8- and 10-byte tags, two keys, payloads of 19 to 25 bytes |
| `tests/ccm_crosscheck.rs` | RustCrypto `ccm` 0.5 with `aes` 0.8 | payloads of 0 to 48 bytes, with and without associated data |

The RFC vectors were copied from
<https://www.rfc-editor.org/rfc/rfc3610.txt>. In every vector the nonce is
13 octets; the packet's leading 8 or 12 octets are the cleartext header
(associated data) and the rest is the payload. Each vector test encrypts,
compares header || ciphertext || tag with the RFC output byte for byte,
decrypts, and checks that a flipped ciphertext bit is rejected.

The cross-check compares `ccm_encrypt` with the RustCrypto `ccm` crate,
an independent implementation, on inputs the RFC does not cover: empty
payload, block-aligned lengths, three-block payloads, all-zero and all-0xFF
data. `ccm` and `aes` are dev-dependencies only.

`validation.toml` records the vector sources for each test file.

## Running the tests

```
cargo test --release
cargo clippy
cargo doc --no-deps
```

## hax extraction

`proofs/lean/extraction/Aesccm_hax.lean` is the Lean output of the hax
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
