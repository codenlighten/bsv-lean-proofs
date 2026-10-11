#!/usr/bin/env python3
"""Inputs for shift_compare.sh: every 1- and 2-byte string with every count
below its bit length, then seeded random strings of 3 to 64 bytes with random
counts below the bit length (the only counts for which the opcode runs the
loop) and at the edges 0, 7, 8, 8L-1."""
import random, sys
out = open(sys.argv[1], "w")
for v in range(256):
    for n in range(8):
        out.write(f"{v:02x} {n}\n")
for v in range(65536):
    for n in range(16):
        out.write(f"{v:04x} {n}\n")
rng = random.Random(20261010)
for _ in range(200000):
    L = rng.randint(3, 64)
    x = bytes(rng.randrange(256) for _ in range(L))
    if rng.random() < 0.2:
        x = bytes(rng.choice([0, 255, 1, 128, 127]) for _ in range(L))
    bits = 8 * L
    for n in {rng.randrange(bits), rng.choice([0, 7, 8, 9, bits - 1, bits - 8, bits - 9]) % bits}:
        out.write(f"{x.hex()} {n}\n")
