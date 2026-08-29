# ctrdrbg-hax

CTR_DRBG with AES-128 and no derivation function, as specified in NIST SP
800-90A Rev. 1, Section 10.2.1, written in the restricted Rust subset
accepted by [hax](https://github.com/hacspec/hax). The same source is a
runnable reference implementation and the input to formal extraction. The
crate is `no_std` and has no dependencies; AES-128 (FIPS 197) is included so
that the extracted code is self-contained.

All loops are bounded (`for i in 0..N` with constant `N`), all buffers are
fixed-size arrays, and all arithmetic is wrapping.

## Contents

The crate is a single module, `src/lib.rs`, in two sections:

| Section  | Items                                                                                              | Standard                   |
| -------- | -------------------------------------------------------------------------------------------------- | -------------------------- |
| AES-128  | `aes128_key_expansion`, `aes128_encrypt`, `xor_block`                                              | FIPS 197                   |
| CTR_DRBG | `CtrDrbgState`, `increment_counter`, `ctr_drbg_update`, `ctr_drbg_instantiate`, `ctr_drbg_generate`, `ctr_drbg_reseed` | SP 800-90A Rev. 1, §10.2.1 |

Parameters are fixed at AES-128 without derivation function: seedlen is
`SEEDLEN` (32) bytes, so entropy input, personalization string and
additional input are each a 32-byte array (an absent input is all zeros, as
Section 10.2.1.3.1 pads inputs shorter than seedlen), and there is no nonce.
A single generate call returns at most `MAX_GEN_BLOCKS` (16) blocks of 16
bytes. Reseed counters and the reseed interval are not tracked; the caller
decides when to reseed.

## Test vectors

`tests/cavp_drbgvs.rs` checks twelve vectors from the NIST CAVP DRBG
validation system (DRBGVS), file `CTR_DRBG.rsp`, `[AES-128 no df]` groups,
`COUNT = 0`, from
<https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/drbg/drbgtestvectors.zip>
(CAVS 14.3), read byte-for-byte from the mirror
<https://github.com/coruus/nist-testvectors>. Every group uses
EntropyInputLen = 256, NonceLen = 0 and ReturnedBitsLen = 512.

| Directory                | PersonalizationStringLen / AdditionalInputLen |
| ------------------------ | --------------------------------------------- |
| `drbgvectors_no_reseed`  | 0/0, 0/256, 256/0, 256/256                    |
| `drbgvectors_pr_false`   | 0/0, 0/256, 256/0, 256/256                    |
| `drbgvectors_pr_true`    | 0/0, 0/256, 256/0, 256/256                    |

The `pr_true` vectors are run as a reseed with the additional input followed
by a generate with empty additional input, the sequence SP 800-90A Rev. 1,
Section 9.3.1, step 7 prescribes when prediction resistance is requested.
`tests/kat_vectors.rs` repeats the `no_reseed` 0/0 vector and adds
self-consistency checks (determinism of instantiate, generate and reseed;
counter carry and wrap; reseed and additional input change the state).
`src/lib.rs` also carries the FIPS 197 Appendix B AES-128 vector and unit
tests of each DRBG operation. There is no cross-check against another
implementation. `validation.toml` records the reference vectors in
machine-readable form.

## Running the tests

```bash
cargo test --release
```

## Hax extraction

The Lean extraction is committed at
`proofs/lean/extraction/Ctrdrbg_hax.lean`. The intermediate hax frontend
export (`hax_frontend_export.json`) is not tracked; regenerate it with

```bash
cargo hax json
```

which requires the `cargo-hax` frontend from the hax repository. The
`#[cfg(kani)]` module holds Kani harnesses and is compiled only under
`cargo kani`.

## License

MIT. See [`LICENSE`](./LICENSE).
