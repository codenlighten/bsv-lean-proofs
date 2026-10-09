#!/usr/bin/env python3
"""Runs a compiled bitcoin-sv VerifyScript oracle on <sig> <pubkey> OP_CHECKSIG
for every sighash-type byte and every setting of STRICTENC, SIGHASH_FORKID and
CHRONICLE, and prints the hash-type verdict in the format of
`readercheck sighashNode`.

  node_hashtype.py <verify_script binary> <script_error.h> <fixture json with a txHex>

The signature is DER-valid (r = 1, s = 1) and does not verify, so a script that
gets past the hash-type check ends with some later error; any error other than
the four hash-type ones is printed as "accept" (of the hash type).
"""
import json, re, subprocess, sys
binary, errh, fixture = sys.argv[1:4]
src = open(errh).read()
body = src[src.index('typedef enum ScriptError_t'):src.index('} ScriptError;')]
enum, i = {}, 0
for n, val in re.findall(r'\b(SCRIPT_ERR_[A-Z0-9_]+)\b(?:\s*=\s*(\d+))?\s*,', body):
    if val: i = int(val)
    enum[i] = n; i += 1
name = {'SCRIPT_ERR_SIG_HASHTYPE': 'ErrInvalidSigHashType', 'SCRIPT_ERR_ILLEGAL_FORKID': 'ErrIllegalForkID',
        'SCRIPT_ERR_ILLEGAL_CHRONICLE': 'ErrIllegalChronicle', 'SCRIPT_ERR_MUST_USE_FORKID': 'ErrMustUseForkID'}
d = json.load(open(fixture))
tx = (d['cases'] if isinstance(d, dict) else d)[0]['txHex']
pub = bytes.fromhex('0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798')
other = {}
for strict in (0, 1):
    for forkid in (0, 1):
        for chron in (0, 1):
            flags = (strict << 1) | (forkid << 16) | (chron << 20)
            for b in range(256):
                sig = bytes.fromhex('3006020101020101') + bytes([b])
                spk = bytes([len(sig)]) + sig + bytes([len(pub)]) + pub + b'\xac'
                out = subprocess.run([binary, tx, '0', '100000', spk.hex(), hex(flags)],
                                     capture_output=True, text=True, check=True).stdout.split()
                e = enum[int(out[1])]
                if e not in name: other[e] = other.get(e, 0) + 1
                print(('true' if strict else 'false'), ('true' if forkid else 'false'),
                      ('true' if chron else 'false'), '%02x' % b, name.get(e, 'accept'))
print('other verdicts counted as accept:', other, file=sys.stderr)
