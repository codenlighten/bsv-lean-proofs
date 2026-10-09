# Coverage and limits

What this repository models of bitcoin-sv v1.2.3, what kind of evidence stands
behind each part, and what is not covered. "Proved" means a Lean theorem that
passes the kernel replay (`lake env leanchecker`); "tested" means agreement
with compiled reference code on stated inputs, which is evidence and not proof.

## Script

| Part | Files | Proved | Tested against a compiled v1.2.3 node |
|---|---|---|---|
| Number reading and encoding | `ScriptNum`, `RoundTrip`, `MinEncode`, `MinimalUnique` | acceptance condition of the reader, round trip, uniqueness of minimal encodings | 1.18 million inputs against the C++ headers |
| OP_CAT, OP_SPLIT, OP_NUM2BIN, OP_BIN2NUM, OP_SIZE, OP_SUBSTR, OP_LEFT, OP_RIGHT | `Splice`, `SpliceProps`, `Convert` | results on success, error conditions, inverse laws | 6,264 vectors |
| OP_LSHIFTNUM, OP_RSHIFTNUM | `ShiftNum` | results are x·2ⁿ and x/2ⁿ toward zero; the big-integer refusal | 4,560 vectors |
| OP_LSHIFT, OP_RSHIFT | `ByteShift` | result length only; the result is DEFINED arithmetically, and that the source's byte loop computes it is not proved | 1,920 vectors |
| 25 arithmetic and comparison opcodes | `Arith`, `ArithProps` | results of OP_ADD, OP_MUL, OP_DIV, OP_MOD; no 64-bit overflow before Genesis | 20,256 vectors |
| The interpreter loop: decoding, minimal pushes, conditionals, OP_RETURN, stack, alt-stack and bitwise opcodes, limits, final checks | `Interp`, `InterpProps` | only that the loop's fuel is never exhausted, and two truthiness facts | about one million random scripts (see `difftest/README.md`) |

Eras covered: outputs created before Genesis, after Genesis, and after
Chronicle, always spent with Chronicle active. Flag words: the block word and
the relay word in the curated vectors; random subsets of MINIMALDATA,
DISCOURAGE_UPGRADABLE_NOPS, CLEANSTACK, MINIMALIF and P2SH in the random
scripts; transaction versions 1 and 2.

Not modelled in script:

- the hash opcodes and OP_CHECKSIG, OP_CHECKSIGVERIFY, OP_CHECKMULTISIG,
  OP_CHECKMULTISIGVERIFY;
- OP_CHECKLOCKTIMEVERIFY and OP_CHECKSEQUENCEVERIFY where they are active
  (outputs before Genesis);
- pay-to-script-hash evaluation;
- the stack-memory limit, and elements above 4,096 bytes inside whole scripts;
- a non-empty unlocking script (whole scripts are run against an empty one);
- spends validated before Chronicle activation;
- the chunked path of the byte shifts for counts above 2³¹ − 1.

## Signatures

| Part | Files | Proved | Tested |
|---|---|---|---|
| Accepted signature-hash type bytes | `SighashType` | which bytes the node and the Go SDK accept, and where they differed | 2,048 cases on the node, 4,096 on the SDK |
| A strict signature parser of an independent Rust node implementation (not bitcoin-sv's) | `StrictSignature` | each accepted byte string is the one canonical encoding of its (r, s) pair | — |
| Fork-id digest layout | `SighashPreimage` | the preimage determines each of its fields | — |
| Fork-id digest, type ALL | `SighashCommit` | equal digests give equal version, inputs' outpoints and sequence numbers, outputs, lock time, script code and amount, or a named hash collision | — |
| Fork-id digest, other types | `SighashVariants` | what every type fixes; ALL fixes the outputs with or without ANYONECANPAY; SINGLE fixes the output at the signed index; and, with no hash assumption, that NONE reads no output, SINGLE reads only that one (none if out of range), and ANYONECANPAY reads only the signed input | — |

Not covered: SHA-256 itself (the hash is a parameter); the serialization of
outpoints, outputs and the type, which is assumed and not derived from the
source; how the node derives the script code and amount; the original digest
used without the fork-id bit or with the Chronicle bit; ECDSA.

## Merkle trees

| Part | Files | Proved | Tested |
|---|---|---|---|
| Root, branch and mutation flag as the reference computes them | `Merkle*` | equality with the tree definition; correct exactly up to 2³¹ leaves for a 32-bit counter; a branch folds to the root | 9,718 cases |

Not covered: SHA-256 (hashing is a parameter), and block or transaction
parsing.

## How far a result reaches

- Every model was written by reading the v1.2.3 source. A theorem is about the
  model. It is about the node only as far as the model matches the node, and
  the tests are the evidence for that match.
- The compiled reference used for testing was built for x86-64 with g++ 13.3.
  Behaviour that depends on the compiler or target is outside these tests.
- Theorems that use `bv_decide` depend on its native-evaluation axioms; the
  rest use only Lean's standard axioms. `#print axioms` shows which.
