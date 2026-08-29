# hmacdrbg-hax

HMAC_DRBG with SHA-256, as specified in NIST SP 800-90A Rev. 1, Section
10.1.2, written in the restricted Rust subset accepted by
[hax](https://github.com/hacspec/hax). The same source is a runnable
reference implementation and the input to formal extraction. The crate is
`no_std` and has no dependencies; SHA-256 (FIPS 180-4) and HMAC (RFC 2104)
are included so that the extracted code is self-contained.

All loops are bounded (`for i in 0..N` with constant `N`), all buffers are
fixed-size arrays, and all arithmetic is wrapping.

## Contents

The crate is a single module, `src/lib.rs`, in three sections:

| Section    | Items                                                              | Standard                  |
| ---------- | ------------------------------------------------------------------ | ------------------------- |
| SHA-256    | `Sha256State`, `sha256_update`, `sha256_finalize`, `sha256`        | FIPS 180-4                |
| HMAC       | `hmac_prepare_key`, `hmac_sha256`                                  | RFC 2104                  |
| HMAC_DRBG  | `HmacDrbgState`, `hmac_drbg_update`, `hmac_drbg_instantiate`, `hmac_drbg_generate`, `hmac_drbg_reseed` | SP 800-90A Rev. 1, §10.1.2 |

Limits: messages hashed in one call are at most `MAX_MSG_LEN` (512) bytes;
seed material (entropy, nonce and personalization string, or entropy and
additional input on reseed) is at most `MAX_SEED_MATERIAL` (128) bytes; a
single generate call returns at most `MAX_OUTPUT` (128) bytes. Reseed
counters and the reseed interval are not tracked; the caller decides when to
reseed.

## Test vectors

`tests/cavp_drbgvs.rs` checks nine vectors from the NIST CAVP DRBG
validation system (DRBGVS), file `HMAC_DRBG.rsp`, `[SHA-256]` groups,
`COUNT = 0`, from
<https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/drbg/drbgtestvectors.zip>
(CAVS 14.3). Every group uses EntropyInputLen = 256, NonceLen = 128 and
ReturnedBitsLen = 1024.

| Directory                | PersonalizationStringLen / AdditionalInputLen |
| ------------------------ | --------------------------------------------- |
| `drbgvectors_no_reseed`  | 0/0, 0/256, 256/256                           |
| `drbgvectors_pr_false`   | 0/0, 0/256, 256/256                           |
| `drbgvectors_pr_true`    | 0/0, 0/256, 256/256                           |

The `pr_true` vectors are run as a reseed with the additional input followed
by a generate with empty additional input, the sequence SP 800-90A Rev. 1,
Section 9.3.1, step 7 prescribes when prediction resistance is requested.
`tests/kat_vectors.rs` repeats the `no_reseed` 0/0 vector and adds
self-consistency checks (determinism of instantiate and generate; reseed and
additional input change the output). `src/lib.rs` also carries unit tests of
the SHA-256 and HMAC layers. `validation.toml` records the reference
vectors in machine-readable form.

## Running the tests

```bash
cargo test --release
```

## Hax extraction

The Lean extraction is committed at
`proofs/lean/extraction/Hmacdrbg_hax.lean`. The intermediate hax frontend
export (`hax_frontend_export.json`) is not tracked; regenerate it with

```bash
cargo hax json
```

which requires the `cargo-hax` frontend from the hax repository. The
`#[cfg(kani)]` module holds Kani harnesses and is compiled only under
`cargo kani`.

## License

MIT. See [`LICENSE`](./LICENSE).
