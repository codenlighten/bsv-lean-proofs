#!/usr/bin/env bash
# Regenerates the vector files from the models. Each file is written under a
# temporary name and renamed into place, so a reader never sees a partial file.
# A `rows_sha256` field is added to the header: the SHA-256 of the `cases`
# array serialized with sorted keys and no spaces. It changes exactly when a
# row changes.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(dirname "$here")
gen="$root/.lake/build/bin/vectors"
one() { # mode, file
  tmp=$(mktemp "$here/.tmp.XXXXXX")
  "$gen" $1 > "$tmp.raw"
  python3 - "$tmp.raw" "$tmp" <<'PY'
import hashlib, json, sys
d = json.load(open(sys.argv[1]))
canon = json.dumps(d['cases'], sort_keys=True, separators=(',', ':')).encode()
out = {'source': d['source'], 'version': d.get('version', 1), 'rows': len(d['cases']),
       'rows_sha256': hashlib.sha256(canon).hexdigest(), 'cases': d['cases']}
with open(sys.argv[2], 'w') as f:
    f.write('{"source": %s,\n "version": %d,\n "rows": %d,\n "rows_sha256": "%s",\n "cases": [\n' %
            (json.dumps(out['source']), out['version'], out['rows'], out['rows_sha256']))
    f.write(',\n'.join('  ' + json.dumps(c) for c in out['cases']))
    f.write('\n ]}\n')
PY
  rm -f "$tmp.raw"
  mv "$tmp" "$here/$2"
  python3 -c "import json,sys; d=json.load(open(sys.argv[1])); print(sys.argv[2], d['rows'], d['rows_sha256'][:16])" "$here/$2" "$2"
}
if [ $# -eq 2 ]; then one "$1" "$2"; exit 0; fi
one ""        splice-v2.json
one shift     shiftnum-v1.json
one byteshift byteshift-v1.json
one arith     arith-v1.json
