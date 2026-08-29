# hashdrbg-hax

Hash_DRBG with SHA-256, as specified in NIST SP 800-90A Rev. 1, Section
10.1.1, written in the restricted Rust subset accepted by
[hax](https://github.com/hacspec/hax). The same source is a runnable
reference implementation and the input to formal extraction. The crate is
`no_std` and has no dependencies; SHA-256 (FIPS 180-4) is included so that
the extracted code is self-contained.

All loops are bounded (`for i in 0..N` with constant `N`), all buffers are
fixed-size arrays, and all arithmetic is wrapping. Variable-length inputs are
passed as a fixed-size buffer together with an explicit length.

## Contents

The crate is a single module, `src/lib.rs`, in four sections:

| Section        | Items                                                                 | Standard                   |
| -------------- | --------------------------------------------------------------------- | -------------------------- |
| SHA-256        | `Sha256State`, `sha256_update`, `sha256_finalize`, `sha256`           | FIPS 180-4                 |
| Byte arithmetic | `add_mod_seedlen`, `add_u64_mod_seedlen`, `increment_mod_seedlen`    | SP 800-90A Rev. 1, §10.1.1 (addition mod 2^seedlen) |
| Hash_df        | `hash_df`                                                             | SP 800-90A Rev. 1, §10.3.1 |
| Hash_DRBG      | `HashDrbgState`, `hash_drbg_instantiate`, `hash_drbg_reseed`, `hashgen`, `hash_drbg_generate` | SP 800-90A Rev. 1, §10.1.1 |

Parameters for SHA-256: `SEEDLEN` = 55 bytes (440 bits), `OUTLEN` = 32
bytes. Limits: the entropy input is at most `SEEDLEN` bytes and the nonce at
most `OUTLEN` bytes; a personalization string or additional input is at most
256 bytes (`MAX_PERSONALIZATION_LEN`, `MAX_ADDITIONAL_INPUT_LEN`); a single
generate call returns at most `MAX_OUTPUT` (128) bytes. The state carries the
`reseed_counter`; the reseed interval is not enforced, the caller decides when
to reseed.

## Test vectors

`tests/cavp_drbgvs.rs` checks twelve vectors from the NIST CAVP DRBG
validation system (DRBGVS), file `Hash_DRBG.rsp`, `[SHA-256]` groups,
`COUNT = 0`, from
<https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/drbg/drbgtestvectors.zip>
(CAVS 14.3), copied verbatim from the byte-identical mirror
<https://github.com/coruus/nist-testvectors>. Every group uses
EntropyInputLen = 256, NonceLen = 128 and ReturnedBitsLen = 1024.

| Directory                | PersonalizationStringLen / AdditionalInputLen |
| ------------------------ | --------------------------------------------- |
| `drbgvectors_no_reseed`  | 0/0, 0/256, 256/0, 256/256                    |
| `drbgvectors_pr_false`   | 0/0, 0/256, 256/0, 256/256                    |
| `drbgvectors_pr_true`    | 0/0, 0/256, 256/0, 256/256                    |

The `pr_true` vectors are run as a reseed with the additional input followed
by a generate with empty additional input, the sequence SP 800-90A Rev. 1,
Section 9.3.1, step 7 prescribes when prediction resistance is requested.

`tests/kat_vectors.rs` checks the NIST Hash_DRBG worked example
(<https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/Hash_DRBG.pdf>,
SHA-256 section, prediction resistance not enabled, no reseed, empty
personalization string and additional input): the value of V after
instantiate and the two chained 512-bit generate outputs. The remaining tests
there are self-consistency checks of the byte arithmetic and of the
instantiate, reseed and generate state transitions against the standard's
formulas. `src/lib.rs` also carries unit tests of the SHA-256 layer and the
byte arithmetic. `validation.toml` records the reference vectors in
machine-readable form.

## Running the tests

```bash
cargo test --release
```

## Hax extraction

The Lean extraction is committed at
`proofs/lean/extraction/Hashdrbg_hax.lean`. The intermediate hax frontend
export (`hax_frontend_export.json`) is not tracked; regenerate it with

```bash
cargo hax json
```

which requires the `cargo-hax` frontend from the hax repository. The
`#[cfg(kani)]` module holds Kani harnesses and is compiled only under
`cargo kani`.

## License

MIT. See [`LICENSE`](./LICENSE).
