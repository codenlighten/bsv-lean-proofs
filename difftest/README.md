# Differential tests

Tests, not proofs. Each compares what a Lean model returns with what the
modelled source returns when it is compiled and run. None of the sources is
kept in this repository; each script takes their locations as arguments.

| Script | Lean model | Source run | Cases |
|---|---|---|---|
| `run.sh <v1.2.2 header dir> <v1.2.3 header dir>` | `deser123`, `deser122`, `ser` | drivers compiled from the unmodified `int_serialization.h` of bitcoin-sv v1.2.2 and v1.2.3 | 1,180,312 |
| `run_gosdk.sh <go-sdk v1.7.0 copy> <go-sdk 511b58ce checkout>` | `check170`, `checkMaster` | `checkHashTypeEncoding` called from a test dropped into the package | 2 × 4,096 (the whole domain) |
| `node_hashtype.py <verify_script> <script_error.h> <fixture json>` then compare with `readercheck sighashNode` | `nodeVerifyScript` | a compiled bitcoin-sv v1.2.2 `VerifyScript` on `<sig> <pubkey> OP_CHECKSIG` | 2,048 (the whole domain) |
| `merkle_compare.py <merkledump> <merkle_ref>` | `rootLit`, `mutatedLit`, `branchLit` | the reference node's `ComputeMerkleRoot` and `ComputeMerkleBranch`, linked from its built libraries (`merkle_ref.cpp`) | 9,718 |
| `shift_compare.sh <v1.2.3 interpreter.cpp>` | `lshiftLoop`, `rshiftLoop` (via `shiftcheck`) | `LShift` and `RShift` extracted unmodified from the v1.2.3 `interpreter.cpp` and compiled (g++, ASan and UBSan on) | 1,449,305: every 1- and 2-byte string with every count below its bit length, and 200,000 seeded random strings of 3 to 64 bytes |
| `vectors_oracle.py <vectors.json> <verify_script> <script_error.h> expected` | `Bsv.Splice` (the vectors in `vectors/` are generated from it by the `vectors` executable) | a compiled bitcoin-sv v1.2.3 `VerifyScript` | 2,078 |

`merkle_ref.cpp` is compiled against a built bitcoin-sv tree with the include
flags of that build and linked with its `libcommon.a`, `libbitcoinconsensus.a`,
`libutil.a`, `crypto/libcrypto.a`, `secp256k1/src/libsecp256k1.a` and
`univalue/libunivalue.a`, in the usual way for a standalone oracle.

Which node version each comparison ran against. The compiled oracle and
libraries used here are one reference build, which was v1.2.2 until
2026-10-07 17:43 local time and v1.2.3 from then on.

| Comparison | v1.2.2 | v1.2.3 |
|---|---|---|
| script-number reader and encoder (headers) | yes | yes |
| node sighash check | yes (2026-10-07, before the rebuild) | yes (2026-10-08) |
| Merkle root, flag and branch | yes | yes (2026-10-08, relinked) |
| splice vectors | 174 + 80 earlier fixtures only | yes, all 2,078 |

Results (g++ 13.3, Go 1.26 toolchain, x86-64): every comparison identical.

## Random whole scripts (2026-10-08)

`fuzz_scripts.py` generates scripts, `scripteval` (the model in
`BsvLeanProofs/Interp.lean`) judges them, and the compiled v1.2.3 `VerifyScript`
is asked the same question.

| run | generated | judged | mismatches |
|---|---|---|---|
| seeds 101 to 110, 100,000 each | 1,000,000 | 982,990 | 0 |
| seed 20261008 (`vectors/scripts-v1.json`) | 25,000 | 24,571 | 0 |

The rest were set aside as outside the model (hash, signature and active
locktime opcodes; elements over 4,096 bytes). The oracle binary was rebuilt by
its owner during the run: seeds 101 to 104 ran on the earlier build, seeds 105
to 110 and the corpus on the rebuilt one (sha256 8a1ee3e080c02c48…), on which
all four curated vector files were also rechecked, identical. Both builds are
of the v1.2.3 source; what the rebuild changed was not examined.
Self-test: `MUTATE=40` (the model is given a flag word with one bit flipped)
produces mismatches, so the comparison is live.
