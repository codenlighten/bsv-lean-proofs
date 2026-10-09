#!/usr/bin/env python3
"""Compares the proved Lean Merkle model with the reference node's own
ComputeMerkleRoot / ComputeMerkleBranch. A test, not a proof.

  merkle_compare.py <merkledump binary> <merkle_ref binary>

The Lean side prints expressions over leaf symbols; this script evaluates them
with double SHA-256 (the leaf for symbol k is k in four little-endian bytes,
then 28 zero bytes) and compares root, mutation flag and every branch entry
with what the C++ printed.
"""
import hashlib, itertools, subprocess, sys
lean, ref = sys.argv[1:3]

def cases():
    for n in range(1, 201):
        syms = ' '.join(map(str, range(n)))
        positions = range(n) if n <= 64 else sorted({0, 1, n // 2, n - 2, n - 1})
        for p in positions:
            yield f'{p}|{syms}'
        yield f'{n}|{syms}'          # just outside the list
        yield f'{n + 7}|{syms}'
    for n in range(1, 8):            # repeats, for the mutation flag
        for t in itertools.product('012', repeat=n):
            yield f'0|{" ".join(t)}'
            yield f'{n - 1}|{" ".join(t)}'

def leaf(k):
    return int(k).to_bytes(4, 'little') + bytes(28)

def dsha(b):
    return hashlib.sha256(hashlib.sha256(b).digest()).digest()

def ev(s, memo={}):
    """Evaluate one expression; returns (bytes, rest of string)."""
    s = s.lstrip()
    if s[0] == 'L':
        j = 1
        while j < len(s) and s[j].isdigit():
            j += 1
        return leaf(s[1:j]), s[j:]
    assert s[:2] == '(N'
    a, rest = ev(s[2:])
    b, rest = ev(rest)
    rest = rest.lstrip()
    assert rest[0] == ')'
    return dsha(a + b), rest[1:]

def full(s):
    v, rest = ev(s)
    assert rest.strip() == ''
    return v.hex()

inp = '\n'.join(cases()) + '\n'
lo = subprocess.run([lean], input=inp, capture_output=True, text=True, check=True).stdout.split('\n')[:-1]
ro = subprocess.run([ref], input=inp, capture_output=True, text=True, check=True).stdout.split('\n')[:-1]
lines = inp.split('\n')[:-1]
assert len(lo) == len(ro) == len(lines)
sys.setrecursionlimit(100000)
bad = flagged = entries = 0
for c, l, r in zip(lines, lo, ro):
    lr, lm, lb = l.split('|')
    rr, rm, rb = r.split('|')
    got = '|'.join([full(lr) if lr != '-' else '-', lm, ';'.join(full(e) for e in lb.split(';') if e)])
    flagged += lm == '1'
    entries += len([e for e in lb.split(';') if e])
    if got != r:
        bad += 1
        if bad <= 5:
            print('MISMATCH', c[:60], file=sys.stderr)
print(f'{"IDENTICAL" if bad == 0 else "DIFFERENT"}  literal Merkle model vs reference ComputeMerkleRoot/Branch '
      f'({len(lines)} cases, {entries} branch entries, {flagged} flagged, {bad} mismatches)')
sys.exit(1 if bad else 0)
