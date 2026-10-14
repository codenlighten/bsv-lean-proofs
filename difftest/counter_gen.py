#!/usr/bin/env python3
"""Writes vectors/counter2of3-v1.json: the 32-byte alt-stack 2-of-3 counter
(`BsvLeanProofs/ThresholdCounter.lean`) behind a prefix that pushes the three slots, for
every choice of slot content (its own constant, OP_0, another slot's constant, a
different 4-byte string) in each slot, before and after Genesis. Judged by the model
(`scripteval`). Usage: counter_gen.py <scripteval binary> <scripts-v1.json> <out>"""
import hashlib, itertools, json, subprocess, sys

exe, src, out = sys.argv[1:4]
tx = json.load(open(src))['cases'][2]
K = {1: '63316331', 2: '63326332', 3: '63336333'}
COUNTER = ('006b04' + K[3] + '876c936b04' + K[2] + '876c936b04' + K[1] + '876c936b6c52a2')
assert len(COUNTER) == 64
BEFORE = 1402863
def slot(i, kind):
    if kind == 'own': return '04' + K[i]
    if kind == 'empty': return '00'
    if kind == 'cross': return '04' + K[i % 3 + 1]
    return '0464646464'  # 'other'
rows = []
for kinds in itertools.product(('own', 'empty', 'cross', 'other'), repeat=3):
    # slot 1 is pushed first, slot 3 last (on top)
    script = ''.join(slot(i + 1, k) for i, k in enumerate(kinds)) + COUNTER
    n = sum(k == 'own' for k in kinds)
    for era, fl in (('before-genesis', BEFORE), ('after-genesis', BEFORE | 1 << 19)):
        rows.append(dict(id='counter2of3-' + '-'.join(kinds) + '-' + era, opcode='counter2of3',
                         covers='slots ' + ','.join(kinds) + f'; {n} of 3 equal their own constant',
                         slots=list(kinds), matching=n, txHex=tx['txHex'], amount=tx['amount'],
                         scriptPubKey=script, flags=fl, utxo=era, version=1))
inp = ''.join(f"{r['version']} {r['flags']:x} {r['scriptPubKey']}\n" for r in rows)
res = subprocess.run([exe], input=inp, capture_output=True, text=True, check=True).stdout.split('\n')
for r, o in zip(rows, res):
    r['expected'] = o.strip()
canon = json.dumps(rows, sort_keys=True, separators=(',', ':')).encode()
note = ("bsv-lean-proofs, the alt-stack 2-of-3 counter judged by BsvLeanProofs.Interp (model of "
        "bitcoin-sv v1.2.3); expected = the model's verdict; a slot is its own constant (own), "
        "OP_0 (empty), the next slot's constant (cross) or another 4-byte string (other)")
with open(out, 'w') as f:
    f.write('{"source": %s,\n "version": 1,\n "rows": %d,\n "rows_sha256": "%s",\n "cases": [\n' %
            (json.dumps(note), len(rows), hashlib.sha256(canon).hexdigest()))
    f.write(',\n'.join('  ' + json.dumps(r) for r in rows))
    f.write('\n ]}\n')
print(out, len(rows))
