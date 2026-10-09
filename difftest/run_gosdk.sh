#!/usr/bin/env bash
# Exhaustive comparison of the Lean sighash-type models with the go-sdk code
# as executed: every byte and every setting of the four flags each version
# reads (4096 cases per version). A test, not a proof, but it covers the whole
# domain of the models.
#
#   difftest/run_gosdk.sh <writable copy of go-sdk v1.7.0> <writable checkout of go-sdk at 511b58ce>
#
# The dump tests are dropped into script/interpreter of each tree (they must be
# inside the package: the function is a method on an unexported type) and
# removed afterwards. Needs Go and a built `readercheck`.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(dirname "$here")
rc="$root/.lake/build/bin/readercheck"
work=$(mktemp -d)
fail=0
one() { # tree, dump test, Lean mode, label
  cp "$here/$2" "$1/script/interpreter/zz_hashtype_dump_test.go"
  (cd "$1" && HASHTYPE_OUT="$work/go.txt" GOFLAGS=-mod=mod go test ./script/interpreter/ -run TestDumpHashType -count=1 > /dev/null)
  rm -f "$1/script/interpreter/zz_hashtype_dump_test.go"
  "$rc" "$3" > "$work/lean.txt"
  if cmp -s "$work/go.txt" "$work/lean.txt"; then
    echo "IDENTICAL  $4  ($(wc -l < "$work/go.txt") cases)"
  else
    echo "DIFFERENT  $4"; fail=1
  fi
}
one "$1" hashtype_dump_v170_test.go.txt   sighash170    "go-sdk v1.7.0 checkHashTypeEncoding"
one "$2" hashtype_dump_master_test.go.txt sighashMaster "go-sdk 511b58ce checkHashTypeEncoding"
rm -rf "$work"
exit $fail
