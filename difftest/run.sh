#!/usr/bin/env bash
# Differential test: the Lean script-number models against drivers compiled
# from the UNMODIFIED bitcoin-sv headers. A test, not a proof.
#
#   difftest/run.sh <dir with v1.2.2 int_serialization.h> <dir with v1.2.3 int_serialization.h>
#
# The headers are not kept in this repository. v1.2.3:
#   https://raw.githubusercontent.com/bitcoin-sv/bitcoin-sv/v1.2.3/src/script/int_serialization.h
# Needs g++ with C++20 and a built `readercheck` (lake build readercheck).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(dirname "$here")
work=$(mktemp -d)
mkdir -p "$work/v122" "$work/v123"
cp "$1/int_serialization.h" "$work/v122/"
cp "$2/int_serialization.h" "$work/v123/"
cp "$here"/drv123.cpp "$here"/drv122.cpp "$here"/drvser.cpp "$work/"
cd "$work"
san="-fsanitize=undefined,address -fno-sanitize-recover=all"
g++ -std=c++20 -O2 $san -o drv123 drv123.cpp
g++ -std=c++20 -O2 -fsanitize=undefined -fno-sanitize-recover=all -o drv122san drv122.cpp
g++ -std=c++20 -O2 -o drv122 drv122.cpp
g++ -std=c++20 -O2 $san -o drvser drvser.cpp
python3 "$here/gen_inputs.py" "$work"
rc="$root/.lake/build/bin/readercheck"
fail=0
check() { # name, C++ command, Lean mode, input
  if $2 < "$4" > cpp.out && "$rc" "$3" < "$4" > lean.out && cmp -s cpp.out lean.out; then
    echo "IDENTICAL  $1  ($(wc -l < cpp.out) inputs)"
  else
    echo "DIFFERENT  $1"; fail=1
  fi
}
check "1.2.3 reader, 0-12 bytes, sanitizers on"            ./drv123    deser123 in_deser.txt
check "1.2.2 reader, 1-9 bytes, UB sanitizer on"           ./drv122san deser122 in_122_short.txt
check "1.2.2 reader, 10-300 bytes, g++ -O2 (undefined)"    ./drv122    deser122 in_122_wide.txt
check "encoder, int64 values, sanitizers on"               ./drvser    ser      in_ser.txt
rm -rf "$work"
exit $fail
