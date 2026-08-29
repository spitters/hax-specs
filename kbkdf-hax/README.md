# kbkdf-hax

KBKDF in Counter Mode with HMAC-SHA-256 as the PRF, as specified in NIST
SP 800-108 Rev. 1, Section 4.1, written in the restricted Rust subset
accepted by [hax](https://github.com/hacspec/hax). The same source is a
runnable reference implementation and the input to formal extraction. The
crate is `no_std` and has no dependencies; SHA-256 (FIPS 180-4) and HMAC
(RFC 2104) are included so that the extracted code is self-contained.

All loops are bounded (`for i in 0..N` with constant `N`), all buffers are
fixed-size arrays, and all arithmetic is wrapping.

## Contents

The crate is a single module, `src/lib.rs`, in three sections:

| Section | Items                                                                 | Standard                     |
| ------- | --------------------------------------------------------------------- | ---------------------------- |
| SHA-256 | `Sha256State`, `sha256_update`, `sha256_finalize`, `sha256`           | FIPS 180-4                   |
| HMAC    | `hmac_prepare_key`, `hmac_sha256`                                     | RFC 2104                     |
| KBKDF   | `kbkdf_counter_hmac256_fixed`, `kbkdf_counter_hmac256`                | SP 800-108 Rev. 1, §4.1      |

The counter is placed before the fixed input data and encoded as a
big-endian 32-bit integer (r = 32). `kbkdf_counter_hmac256_fixed` takes the
fixed input data as an opaque byte string; `kbkdf_counter_hmac256` assembles
it as `Label || 0x00 || Context || [L]_4`, the layout Section 4 of the
standard recommends, and calls the former.

Limits: messages hashed in one call are at most `MAX_MSG_LEN` (256) bytes;
the fixed input data is at most `MAX_FIXED_LEN` (101) bytes, with a label of
at most `MAX_LABEL_LEN` (32) and a context of at most `MAX_CONTEXT_LEN` (64)
bytes; the derived key is at most `MAX_DK_LEN` (64) bytes, that is
`MAX_BLOCKS` (2) PRF invocations. The key derivation key is 32 bytes.

## Test vectors

`tests/cavp_kdfctr.rs` checks all 40 vectors of the group
`[PRF=HMAC_SHA256] [CTRLOCATION=BEFORE_FIXED] [RLEN=32_BITS]` of
`KDFCTR_gen.rsp` (CAVS 14.4) from the NIST CAVP KBKDF validation system,
<https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/KBKDF800-108/kbkdfvs.zip>,
transcribed from the mirror
<https://github.com/coruus/nist-testvectors> (path
`csrc.nist.gov/groups/STM/cavp/documents/KBKDF800-108/CounterMode/KDFCTR_gen.rsp`).
The group covers L = 128, 160, 256 and 320 bits with a 32-byte KI and 60
bytes of fixed input data; the other groups of the file (other PRFs,
counter after or inside the fixed input data, 8-, 16- and 24-bit counters)
are outside what the crate implements. The vectors drive
`kbkdf_counter_hmac256_fixed`, since the CAVP fixed input data is random and
does not have the `Label || 0x00 || Context || [L]_4` layout.

`tests/kat_vectors.rs` covers `kbkdf_counter_hmac256` with
self-consistency checks (agreement with a direct HMAC of the assembled PRF
input, determinism, sensitivity to key, label, context and L) and checks
the SHA-256 and HMAC layers against the FIPS 180-4 and RFC 4231 literals;
`src/lib.rs` carries unit tests of the same layers. `validation.toml`
records the reference vectors in machine-readable form.

## Running the tests

```bash
cargo test --release
```

## Hax extraction

The Lean extraction is committed at
`proofs/lean/extraction/Kbkdf_hax.lean`. The intermediate hax frontend
export (`hax_frontend_export.json`) is not tracked; regenerate it with

```bash
cargo hax json
```

which requires the `cargo-hax` frontend from the hax repository. The
`#[cfg(kani)]` module holds Kani harnesses and is compiled only under
`cargo kani`.

## License

MIT. See [`LICENSE`](./LICENSE).
