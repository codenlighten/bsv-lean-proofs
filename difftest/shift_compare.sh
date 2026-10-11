#!/usr/bin/env bash
# Differential test: the Lean transcriptions of the byte-shift loops
# (`lshiftLoop`, `rshiftLoop`) against the source's own `LShift` and `RShift`,
# compiled unmodified. A test, not a proof (the proof is in ByteShiftLoop.lean,
# and it covers the Lean text: this checks that the Lean text is the C++).
#
#   difftest/shift_compare.sh <bitcoin-sv v1.2.3 interpreter.cpp>
#
# Needs g++ with C++20 and a built `shiftcheck` (lake build shiftcheck).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(dirname "$here")
work=$(mktemp -d)
# From `make_rshift_mask` up to, not including, `CastToBool`.
awk '/^inline uint8_t make_rshift_mask/{p=1} /^bool CastToBool/{p=0} p' "$1" > "$work/shift_src.inc"
grep -q "static valtype LShift" "$work/shift_src.inc"
grep -q "static valtype RShift" "$work/shift_src.inc"
cp "$here/shift_ref.cpp" "$work/"
cd "$work"
g++ -std=c++20 -O2 -fsanitize=undefined,address -fno-sanitize-recover=all -o shift_ref shift_ref.cpp
python3 "$here/shift_gen.py" in.txt
./shift_ref < in.txt > cpp.out
"$root/.lake/build/bin/shiftcheck" < in.txt > lean.out
if cmp -s cpp.out lean.out; then
  echo "IDENTICAL  LShift and RShift  ($(wc -l < cpp.out) inputs, sanitizers on)"
  rc=0
else
  echo "DIFFERENT"; rc=1
fi
rm -rf "$work"
exit $rc
