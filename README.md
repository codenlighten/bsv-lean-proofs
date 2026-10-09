# BSV Lean proofs

A reference semantics for parts of the BSV node software (bitcoin-sv v1.2.3),
written in Lean 4, with machine-checked theorems about it and conformance
vectors generated from it.

Authors: Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan.

## What is here

- **Script.** Total definitions of the number reader and encoder, the splice
  and conversion opcodes, the numeric and byte-string shifts, the arithmetic
  and comparison opcodes, and the interpreter loop, for outputs created
  before Genesis, after Genesis and after Chronicle.
- **Signatures.** A model of which signature-hash type bytes the node's checks
  accept, and, for a model of the fork-id signature digest (serialization
  assumed), what it fixes for each signature-hash type, stated as reductions
  to hash collisions.
- **Merkle trees.** A model of the node's constant-space Merkle root, branch and
  mutation computation, proved equal to the tree definition up to the exact
  limit a 32-bit leaf counter allows, and tested against the node's code.
- **Conformance vectors** (`vectors/`): 57,571 rows in the five current files, whose expected verdict is
  what the Lean model returns, in a JSON format a script interpreter can run
  directly. A compiled bitcoin-sv v1.2.3 `VerifyScript` returns the expected
  verdict on every row.
- **Differential tests** (`difftest/`): the harnesses that compare the models
  with compiled reference code, including a random whole-script tester
  (`fuzz_scripts.py`).

[`COVERAGE.md`](COVERAGE.md) states exactly what is modelled, what is proved,
what is only tested and on how many inputs, and what is not covered. Read it
before relying on any part.

## How to read a result

A theorem is about the Lean model. It is about the node only as far as the
model matches the node, and the differential tests are the evidence for that
match: evidence, not proof. Every model was written by reading the v1.2.3
source; file headers say what is modelled, what is proved and what is assumed.

## Building and checking

Lean 4.34.1, core library only (no Mathlib):

```sh
lake build                       # the library and the test executables
lake env leanchecker BsvLeanProofs.ScriptNum BsvLeanProofs.Interp ...   # kernel replay
```

`#print axioms <theorem>` shows what each theorem depends on. Most use only
`propext`, `Classical.choice` and `Quot.sound`; theorems proved with
`bv_decide` also depend on its native-evaluation axioms. `CLEAN_BUILD.log`
records a build and kernel replay of this tree from a fresh checkout.

## Running the vectors

`vectors/README.md` describes the row format. Each row carries a transaction,
a locking script, a flag word and the expected result; a runner calls its
interpreter on these and compares. `difftest/vectors_oracle.py` does this for
a compiled bitcoin-sv `VerifyScript`.

## Licence

Copyright 2026 Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan.

Licensed under the Apache License, Version 2.0; see [`LICENSE`](LICENSE).
