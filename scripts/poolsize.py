#!/usr/bin/env python3
"""Report proof sizes exactly as lean-pool's quality checker measures them.

Their rule (python/lean_pool/quality.py): for `theorem`/`lemma` only, take the block from the
declaration to the next one, start at the first line containing `:=`, strip comments, and count
non-blank lines; the limit is 200.
"""
import re
import subprocess

SRC = ".pool-quality.py"
src = open(SRC, encoding="utf-8").read()
ns = {"re": re}
exec(re.search(r"^DECLARATION_PREFIX = \(.*?\)\n", src, re.S | re.M).group(0), ns)
for fn in ("_strip_lean_comments", "_non_comment_code_lines"):
    exec(re.search(rf"^def {fn}\(.*?(?=\n\n\ndef |\n\n\n@|\Z)", src, re.S | re.M).group(0), ns)

strip, ncl, PREFIX = ns["_strip_lean_comments"], ns["_non_comment_code_lines"], ns["DECLARATION_PREFIX"]
pat = re.compile(rf"^\s*{PREFIX}(?:theorem|lemma)\b")

files = subprocess.check_output(["git", "ls-files", "Jacobian/*.lean"], text=True).split()
viol = []
for f in files:
    original = open(f, encoding="utf-8").read().splitlines()
    starts = [(i, l) for i, l in enumerate(strip("\n".join(original)).splitlines(), start=1)
              if pat.match(l)]
    for idx, (sl, _) in enumerate(starts):
        el = starts[idx + 1][0] if idx + 1 < len(starts) else len(original) + 1
        block = original[sl - 1:el - 1]
        try:
            bs = next(o for o, l in enumerate(block) if ":=" in l)
        except StopIteration:
            continue
        n = ncl("\n".join(block[bs:]))
        if n > 200:
            viol.append((n, f, sl))
viol.sort(reverse=True)
print(f"over the pool's 200-line proof cap: {len(viol)}")
for n, f, sl in viol:
    print(f"  {n:4}  (need -{n - 200:3})  {f}:{sl}")
