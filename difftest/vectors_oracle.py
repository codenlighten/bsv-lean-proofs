#!/usr/bin/env python3
"""Runs conformance vectors through a compiled bitcoin-sv VerifyScript oracle
and compares its verdict with the model's. A test, not a proof.

  vectors_oracle.py <vectors.json> <verify_script binary> <script_error.h> [field]

`field` is the expectation to compare with: `expected_1_2_2` (default, for a
v1.2.2 oracle) or `expected` (for a v1.2.3 oracle).
"""
import collections, json, re, subprocess, sys
vec, binary, errh = sys.argv[1:4]
field = sys.argv[4] if len(sys.argv) > 4 else 'expected_1_2_2'
src = open(errh).read()
body = src[src.index('typedef enum ScriptError_t'):src.index('} ScriptError;')]
enum, i = {}, 0
for n, val in re.findall(r'\b(SCRIPT_ERR_[A-Z0-9_]+)\b(?:\s*=\s*(\d+))?\s*,', body):
    if val: i = int(val)
    enum[i] = n.replace('SCRIPT_ERR_', ''); i += 1
cases = json.load(open(vec))['cases']
bad, by = 0, collections.Counter()
for c in cases:
    out = subprocess.run([binary, c['txHex'], '0', str(c['amount']), c['scriptPubKey'], hex(c['flags'])],
                         capture_output=True, text=True, check=True).stdout.split()
    got = enum[int(out[1])]
    by[(c['opcode'], got == c[field])] += 1
    if got != c[field]:
        bad += 1
        if bad <= 25:
            print(f"MISMATCH {c['id']}: model {c[field]}, oracle {got}  [{c['covers']}]", file=sys.stderr)
ops = sorted({k[0] for k in by})
for o in ops:
    print(f"  {o}: {by[(o, True)]} agree, {by[(o, False)]} differ")
print(f'{"IDENTICAL" if bad == 0 else "DIFFERENT"}  {len(cases)} vectors against the oracle, field {field}: {bad} mismatches')
sys.exit(1 if bad else 0)
