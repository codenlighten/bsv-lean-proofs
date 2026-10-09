#!/usr/bin/env python3
"""Inputs for the differential test of the script-number models. Deterministic."""
import random, sys
out = sys.argv[1]
rng = random.Random(20261007)
L = ['']
L += ['%02x' % a for a in range(256)]
L += ['%02x%02x' % (a, b) for a in range(256) for b in range(256)]
for _ in range(300000):
    L.append(bytes(rng.randrange(256) for _ in range(rng.randrange(0, 13))).hex())
edge = [0x00, 0x01, 0x7f, 0x80, 0x81, 0xff]
for n in (7, 8, 9, 10):
    for _ in range(40000):
        b = bytearray(rng.choice(edge + [rng.randrange(256)] * 2) if rng.random() < 0.5
                      else rng.randrange(256) for _ in range(n))
        b[-1] = rng.choice(edge + [rng.randrange(256)])
        b[-2] = rng.choice(edge + [rng.randrange(256)])
        if rng.random() < 0.3:
            for k in range(n - 2):
                b[k] = 0
        L.append(bytes(b).hex())
open(out + '/in_deser.txt', 'w').write('\n'.join(L) + '\n')
short = [l for l in L if l != '' and len(l) <= 18]
open(out + '/in_122_short.txt', 'w').write('\n'.join(short) + '\n')
rng = random.Random(7)
wide = [bytes(rng.randrange(256) for _ in range(rng.randrange(10, 301))).hex() for _ in range(100000)]
open(out + '/in_122_wide.txt', 'w').write('\n'.join(wide) + '\n')
vals = {0, -2**63, 2**63 - 1}
for k in range(64):
    for d in (-2, -1, 0, 1, 2):
        for s in (1, -1):
            v = s * ((1 << k) + d)
            if -2**63 <= v < 2**63:
                vals.add(v)
for _ in range(200000):
    bits = rng.randrange(1, 65)
    v = rng.getrandbits(bits) - (1 << (bits - 1))
    if -2**63 <= v < 2**63:
        vals.add(v)
open(out + '/in_ser.txt', 'w').write('\n'.join(map(str, sorted(vals))) + '\n')
