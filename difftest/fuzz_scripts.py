#!/usr/bin/env python3
"""Differential test of the interpreter model (BsvLeanProofs/Interp.lean)
against a compiled bitcoin-sv VerifyScript, on random whole scripts.

  fuzz_scripts.py <count> <seed> <verify_script binary> <script_error.h> [corpus.json]

Each case is a locking script run against an empty unlocking script, under a
flag word and a transaction version. The model's verdict comes from
`.lake/build/bin/scripteval`; cases it reports OUT_OF_MODEL are set aside and
counted. With a fifth argument, the judged cases are written as vectors.
A test, not a proof. The generator is not trusted: the model judges whatever
it produces.
"""
import collections, hashlib, json, os, random, re, subprocess, sys
from concurrent.futures import ThreadPoolExecutor

count, seed, binary, errh = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
corpus = sys.argv[5] if len(sys.argv) > 5 else None
here = os.path.dirname(os.path.abspath(__file__))
rng = random.Random(seed)
# self-test of the tester: MUTATE=<hex mask> gives the model a different flag word, which must show up
MUTATE = int(os.environ.get('MUTATE', '0'), 16)

TX = ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0000000000ffffffff"
      "01905f0100000000001976a914925d4028880bd0c9d68fbc7fc7dfee976698629c88ac00000000")
def tx(version): return f"{version:02x}000000" + "01" + TX
AMOUNT = 100000

BASE = 0x3d462f                      # the block word, output after Chronicle
ERAS = {'after-chronicle': 0, 'after-genesis': 0x200000, 'before-genesis': 0x280000}
OPTIONAL = [6, 7, 8, 13]             # MINIMALDATA, DISCOURAGE_UPGRADABLE_NOPS, CLEANSTACK, MINIMALIF

def num(n):
    if n == 0: return b''
    a, out = abs(n), bytearray()
    while a: out.append(a & 0xff); a >>= 8
    if out[-1] & 0x80: out.append(0x80 if n < 0 else 0)
    elif n < 0: out[-1] |= 0x80
    return bytes(out)

def push(d, sloppy=False):
    n = len(d)
    if not sloppy:
        if n == 0: return b'\x00'
        if n == 1 and 1 <= d[0] <= 16: return bytes([0x50 + d[0]])
        if d == b'\x81': return b'\x4f'
    if n < 0x4c and not (sloppy and rng.random() < 0.5): return bytes([n]) + d
    if n <= 0xff and not (sloppy and rng.random() < 0.5): return b'\x4c' + bytes([n]) + d
    if n <= 0xffff and not (sloppy and rng.random() < 0.5): return b'\x4d' + n.to_bytes(2, 'little') + d
    return b'\x4e' + n.to_bytes(4, 'little') + d

BOUNDARY = [0, 1, -1, 2, 3, 7, 8, 16, 17, 127, 128, 255, 256, 520, 521, 0x7fff, 0x8000,
            2**31 - 1, -(2**31 - 1), 2**31, -(2**31), 2**32, 2**39, 2**63 - 1, -(2**63), 2**63, 2**64, 2**70 + 5]
def element():
    r = rng.random()
    if r < 0.30: return num(rng.choice(BOUNDARY))
    if r < 0.50: return num(rng.randint(-20, 20))
    if r < 0.58: return rng.choice([b'\x80', b'\x00', b'\x01\x00', b'\x00\x80', b'\x05\x00\x00',
                                    b'\x09' + b'\x00' * 8, b'\xff' * 9, b'\x01' + b'\x00' * 9 + b'\x80',
                                    b'\x01\x00\x00\x00', b'\x02\x00\x00\x00'])
    if r < 0.62: return bytes(rng.choice([519, 520, 521, 600]))
    return bytes(rng.randrange(256) for _ in range(rng.choice([1, 1, 2, 3, 4, 5, 8, 9, 10, 20, 33])))

STACK = [0x6b, 0x6c, 0x6d, 0x6e, 0x6f, 0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79, 0x7a, 0x7b, 0x7c, 0x7d]
SPLICE = [0x7e, 0x7f, 0x80, 0x81, 0x82, 0xb3, 0xb4, 0xb5]
BITS = [0x83, 0x84, 0x85, 0x86, 0x87, 0x88, 0x98, 0x99]
ARITH = list(range(0x8b, 0x98)) + list(range(0x9a, 0xa6)) + [0xb6, 0xb7]
MISC = [0x61, 0x62, 0x69, 0x6a, 0xb0, 0xb1, 0xb2, 0xb8, 0xb9, 0xab, 0x4f, 0x4f, 0x61, 0x69]
RARE = [0x50, 0x89, 0x8a, 0x65, 0x66, 0x62]
def opcode():
    r = rng.random()
    if r < 0.30: return rng.choice(STACK)
    if r < 0.50: return rng.choice(SPLICE)
    if r < 0.62: return rng.choice(BITS)
    if r < 0.90: return rng.choice(ARITH)
    if r < 0.975: return rng.choice(MISC)
    if r < 0.992: return rng.choice(RARE)
    return rng.randrange(0xa6, 0x100)

# (elements needed, net change) for a stack-aware choice; unknown opcodes: (0, 0)
NEED = {0x6b: (1, -1), 0x6c: (9, 1), 0x6d: (2, -2), 0x6e: (2, 2), 0x6f: (3, 3), 0x70: (4, 2), 0x71: (6, 0),
        0x72: (4, 0), 0x73: (1, 0), 0x74: (0, 1), 0x75: (1, -1), 0x76: (1, 1), 0x77: (2, -1), 0x78: (2, 1),
        0x79: (2, 0), 0x7a: (2, -1), 0x7b: (3, 0), 0x7c: (2, 0), 0x7d: (2, 1), 0x7e: (2, -1), 0x7f: (2, 0),
        0x80: (2, -1), 0x81: (1, 0), 0x82: (1, 1), 0xb3: (3, -2), 0xb4: (2, -1), 0xb5: (2, -1), 0x83: (1, 0),
        0x84: (2, -1), 0x85: (2, -1), 0x86: (2, -1), 0x87: (2, -1), 0x88: (2, -2), 0x98: (2, -1), 0x99: (2, -1),
        0xa5: (3, -2), 0xb6: (2, -1), 0xb7: (2, -1), 0x69: (1, -1), 0x9d: (2, -2)}
for o in range(0x8b, 0x93): NEED[o] = (1, 0)
for o in list(range(0x93, 0x98)) + [0x9a, 0x9b, 0x9c, 0x9e, 0x9f, 0xa0, 0xa1, 0xa2, 0xa3, 0xa4]: NEED[o] = (2, -1)

def small_index(depth):
    return num(rng.choice([0, 0, 1, 1, 2, 3, max(depth - 1, 0), depth, -1]))

def block(depth, length, d):
    """d: the generator's estimate of the stack depth (a guide, not a guarantee)."""
    out = b''
    for _ in range(length):
        r = rng.random()
        if r < 0.36 or (d < 2 and r < 0.6):
            out += push(element(), sloppy=rng.random() < 0.03); d += 1
        elif r < 0.90:
            for _ in range(8):
                o = opcode()
                if NEED.get(o, (0, 0))[0] <= d or rng.random() < 0.06: break
            if o in (0x79, 0x7a, 0x7f, 0xb4, 0xb5, 0x98, 0x99, 0xb6, 0xb7, 0x80) and rng.random() < 0.6:
                out += push(small_index(d)); d += 1        # a plausible count on top
            out += bytes([o]); d = max(d + NEED.get(o, (0, 0))[1], 0)
        elif r < 0.97 and depth < 3:
            if rng.random() < 0.8: out += push(rng.choice([b'', b'\x01', b'\x01', b'\x02', b'\x80', b'\x01\x00\x00\x00', b'\x02\x00\x00\x00']))
            else: d = max(d - 1, 0)
            out += bytes([rng.choice([0x63, 0x63, 0x64, 0x65, 0x66])]) + block(depth + 1, rng.randint(0, 4), d)
            for _ in range(rng.choice([0, 1, 1, 2])): out += b'\x67' + block(depth + 1, rng.randint(0, 3), d)
            if rng.random() < 0.95: out += b'\x68'
        elif r < 0.99: out += bytes([rng.choice([0x63, 0x64, 0x67, 0x68])])
        elif rng.random() < 0.3: out += bytes(rng.randrange(256) for _ in range(rng.randint(1, 3)))
    return out

def script():
    r = rng.random()
    if r < 0.01: return bytes([0x61]) * rng.choice([499, 500, 501]) + b'\x51'
    if r < 0.02: return b'\x51' * rng.choice([999, 1000, 1001, 1002])
    if r < 0.03: return (b'\x00' * rng.choice([9998, 9999, 10000]) + b'\x51')[:rng.choice([9999, 10000, 10001])]
    s = block(0, rng.randint(1, 24), 0)
    if rng.random() < 0.6: s += rng.choice([b'\x51', b'\x74', b'\x51', b'\x75\x51', b'\x74\x91\x91'])
    return s

cases = []
for i in range(count):
    era = rng.choice(list(ERAS))
    flags = BASE - ERAS[era]
    for b in OPTIONAL:
        if rng.random() < 0.5: flags |= 1 << b
    if rng.random() < 0.15: flags &= ~1                       # P2SH off
    if rng.random() < 0.01: flags = (flags | 1 << 21) & ~(1 << 19)   # an invalid era pair
    cases.append({'id': f'script-{seed}-{i}', 'version': rng.choice([1, 1, 2]), 'flags': flags,
                  'utxo': era, 'scriptPubKey': script().hex()})

model = subprocess.run([os.path.join(here, '..', '.lake', 'build', 'bin', 'scripteval')],
                       input=''.join(f"{c['version']} {c['flags'] ^ MUTATE:x} {c['scriptPubKey']}\n" for c in cases),
                       capture_output=True, text=True, check=True).stdout.split('\n')
src = open(errh).read()
body = src[src.index('typedef enum ScriptError_t'):src.index('} ScriptError;')]
enum, k = {}, 0
for n, val in re.findall(r'\b(SCRIPT_ERR_[A-Z0-9_]+)\b(?:\s*=\s*(\d+))?\s*,', body):
    if val: k = int(val)
    enum[k] = n.replace('SCRIPT_ERR_', ''); k += 1

def oracle(c):
    r = subprocess.run([binary, tx(c['version']), '0', str(AMOUNT), c['scriptPubKey'], hex(c['flags'])],
                       capture_output=True, text=True)
    if r.returncode != 0 or len(r.stdout.split()) < 2: return f'ORACLE_FAILED({r.returncode})'
    return enum[int(r.stdout.split()[1])]
with ThreadPoolExecutor(max_workers=int(os.environ.get('JOBS', '4'))) as ex:
    node = list(ex.map(oracle, cases))

by, bad, judged = collections.Counter(), [], []
for c, m, n in zip(cases, model, node):
    if m == 'OUT_OF_MODEL': by['(set aside: out of model)'] += 1; continue
    by[m] += 1
    c['expected'] = m; c['txHex'] = tx(c['version']); c['amount'] = AMOUNT
    judged.append(c)
    if m != n: bad.append((c, m, n))
for kname, v in sorted(by.items(), key=lambda kv: -kv[1]): print(f'  {v:8d}  {kname}')
for c, m, n in bad[:30]:
    print(f"MISMATCH {c['id']} v{c['version']} {c['flags']:#x} {c['utxo']}: model {m}, node {n}: {c['scriptPubKey'][:200]}")
print(f"{'IDENTICAL' if not bad else 'DIFFERENT'}  {len(judged)} judged of {count} generated (seed {seed}): {len(bad)} mismatches")
if corpus and not bad:
    rows = [{k2: c[k2] for k2 in ('id', 'txHex', 'amount', 'scriptPubKey', 'flags', 'utxo', 'version', 'expected')} for c in judged]
    h = hashlib.sha256(json.dumps(rows, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    tmp = corpus + '.tmp'
    with open(tmp, 'w') as f:
        json.dump({'source': 'bsv-lean-proofs, random scripts judged by BsvLeanProofs.Interp (model of bitcoin-sv v1.2.3); '
                             'expected = the model\'s verdict', 'version': 1, 'seed': seed, 'rows': len(rows),
                   'rows_sha256': h, 'cases': rows}, f, separators=(',', ':'))
    os.replace(tmp, corpus)
sys.exit(1 if bad else 0)
