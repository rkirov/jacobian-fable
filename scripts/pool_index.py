#!/usr/bin/env python3
"""Regenerate a lean-pool checkout's `LeanPool.lean` index, the way `lake exe mk_all` does.

The pool's index imports every module under `LeanPool/`, sorted by module name, so it can be
rebuilt without a Lean toolchain — which is what lets `scripts/make_pool_pr.py`'s payload be
assembled and checked offline. `lake exe mk_all --check` inside the pool is the authority; this
reproduces it byte-for-byte (verified against the pool's committed index before adding anything).

    python3 scripts/pool_index.py <pool-checkout>
"""
import os
import sys

root = sys.argv[1] if len(sys.argv) > 1 else "."
lib = os.path.join(root, "LeanPool")

modules = sorted(
    os.path.relpath(os.path.join(dirpath, name), root)[:-len(".lean")].replace(os.sep, ".")
    for dirpath, _, files in os.walk(lib)
    for name in files
    if name.endswith(".lean")
)

index = os.path.join(root, "LeanPool.lean")
open(index, "w", encoding="utf-8").write("".join(f"import {m}\n" for m in modules))
print(f"{index}: {len(modules)} modules")
