# IP records

| Date | Covers | Type | Record hash | Signer | Tag |
|---|---|---|---|---|---|
| 2026-10-09 | The public release at commit `7d1ef28` | software, hash-only | [`b9188055c6e7a1fad02f59beddce7622628ab72207ae35d78fd8b24896c9fa84`](https://iptrust.org/v/b9188055c6e7a1fad02f59beddce7622628ab72207ae35d78fd8b24896c9fa84) | Gregory J. Ward (authors: Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan) | `ip-2026-10-09` |
| 2026-10-11 | The repository at commit `8ec16a3`: byte-shift loop equivalence proof, interpreter step lemmas, boundary vectors | software, hash-only | [`d456c0ed11b78cfc692bb4bb2f5f8d06e3e7e0ac2ee2b3a685b0dc1e58bcce6a`](https://iptrust.org/v/d456c0ed11b78cfc692bb4bb2f5f8d06e3e7e0ac2ee2b3a685b0dc1e58bcce6a) | Gregory J. Ward (authors: Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan) | `ip-2026-10-11` |

A record is evidence that the committed content existed by the time of its anchor and
that the signer made the statement; it does not create or register any right.

The evidence package (`.iptrust/v2/<recordHash>/`, with `opening.json` and
`manifest.json`) is committed in this repository (the content it commits to is already public). Verification needs it:

```
git worktree add /tmp/at-tag-bsv-lean-proofs-public ip-2026-10-11
cp -r .iptrust /tmp/at-tag-bsv-lean-proofs-public/
(cd /tmp/at-tag-bsv-lean-proofs-public && iptrust2 verify d456c0ed11b78cfc692bb4bb2f5f8d06e3e7e0ac2ee2b3a685b0dc1e58bcce6a --fetch-headers)
git worktree remove --force /tmp/at-tag-bsv-lean-proofs-public
```

Expect `verdict: valid` and `content: matched` once both chains have anchored.
