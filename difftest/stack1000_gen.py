#!/usr/bin/env python3
"""Writes vectors/stack1000-v1.json: scripts of n x OP_1 (n = 999..1002), plain
and with n/2 of them moved to the alt stack, each judged by the model
(`scripteval`) before and after Genesis. The two eras of a script differ only in
flag bit 19. Usage: stack1000_gen.py <scripteval binary> <scripts-v1.json> <out>"""
import hashlib, json, subprocess, sys

exe, src, out = sys.argv[1:4]
tx = json.load(open(src))['cases'][2]
BEFORE = 1402863
rows = []
for kind in ('main', 'split'):
    for n in (999, 1000, 1001, 1002):
        s = '51' * n + ('6b' * (n // 2) if kind == 'split' else '')
        for era, fl in (('before-genesis', BEFORE), ('after-genesis', BEFORE | 1 << 19)):
            rows.append(dict(id=f'stack1000-{kind}-{n}-{era}', kind=kind, count=n,
                             txHex=tx['txHex'], amount=tx['amount'], scriptPubKey=s,
                             flags=fl, utxo=era, version=1))
inp = ''.join(f"{r['version']} {r['flags']:x} {r['scriptPubKey']}\n" for r in rows)
res = subprocess.run([exe], input=inp, capture_output=True, text=True, check=True).stdout.split('\n')
for r, o in zip(rows, res):
    r['expected'] = o.strip()
canon = json.dumps(rows, sort_keys=True, separators=(',', ':')).encode()
src_note = ("bsv-lean-proofs, STACK_SIZE boundary pairs judged by BsvLeanProofs.Interp "
            "(model of bitcoin-sv v1.2.3); expected = the model's verdict; flags are "
            "script_flags.h bit numbers, after-genesis = before-genesis | bit 19")
with open(out, 'w') as f:
    f.write('{"source": %s,\n "version": 1,\n "rows": %d,\n "rows_sha256": "%s",\n "cases": [\n' %
            (json.dumps(src_note), len(rows), hashlib.sha256(canon).hexdigest()))
    f.write(',\n'.join('  ' + json.dumps(r) for r in rows))
    f.write('\n ]}\n')
print(out, len(rows))
