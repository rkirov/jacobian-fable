#!/usr/bin/env python3
"""Generate the lean-pool content PR payload for this library.

lean-pool (github.com/Vilin97/lean-pool) takes a project as `LeanPool/<Project>/**` with the
module prefix rewritten, plus one card in `LeanPool/projects.yml`. This script emits both into
an output directory, so assembling the PR is a copy plus `lake exe mk_all`.

    python3 scripts/make_pool_pr.py                 # writes to build/pool-pr/
    python3 scripts/make_pool_pr.py --check         # exits 1 if a previous run is stale

Layout produced:

    <out>/LeanPool/JacobianDiffgeo.lean        (root module: this repo's Jacobian.lean)
    <out>/LeanPool/JacobianDiffgeo/**.lean     (the library, `Jacobian.*` -> `LeanPool.JacobianDiffgeo.*`)
    <out>/projects.yml.fragment                (the card to splice into LeanPool/projects.yml)

The rewrite is the same mechanical one the lean-eval overlay uses (`scripts/make_submission.py`):
only `import Jacobian…` lines change, since the library never mentions its own module names
anywhere else.
"""
import os
import re
import shutil
import sys

PROJECT = "JacobianDiffgeo"
OUT = "build/pool-pr"
CHECK = "--check" in sys.argv
dst_root = "/tmp/jacobian_pool_pr_check" if CHECK else OUT

import_re = re.compile(r"^import Jacobian(?=[.\s])", re.M)


def rewrite(text: str) -> str:
    return import_re.sub(f"import LeanPool.{PROJECT}", text)


shutil.rmtree(dst_root, ignore_errors=True)
lib = os.path.join(dst_root, "LeanPool", PROJECT)
os.makedirs(lib, exist_ok=True)

count = 0
for root, _, files in os.walk("Jacobian"):
    for name in files:
        if not name.endswith(".lean"):
            continue
        src = os.path.join(root, name)
        dst = os.path.join(lib, os.path.relpath(src, "Jacobian"))
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        with open(src, encoding="utf-8") as fh:
            open(dst, "w", encoding="utf-8").write(rewrite(fh.read()))
        count += 1

with open("Jacobian.lean", encoding="utf-8") as fh:
    open(os.path.join(dst_root, "LeanPool", f"{PROJECT}.lean"), "w", encoding="utf-8").write(
        rewrite(fh.read())
    )

CARD = """  - slug: jacobian-diffgeo
    title: The Jacobian of a Compact Riemann Surface
    summary: >-
      Constructs the Jacobian of a compact Riemann surface as the period-lattice
      quotient of the dual of holomorphic 1-forms, and proves the surrounding
      theory it needs: the genus as the dimension of the space of holomorphic
      1-forms, discreteness and full rank 2g of the period lattice, the
      Abel-Jacobi map with Abel's theorem in the form of its injectivity on
      degree-zero divisor classes, functoriality (pushforward, pullback, degree,
      and the projection formula), Riemann-Roch, Serre duality via Laurent
      tails, the residue theorem, the Dolbeault-Cech comparison, and finite
      dimensionality of the first cohomology by a Schwartz/Montel argument. The
      headline no-hack guard is that the genus vanishes exactly when the surface
      is homeomorphic to the sphere.
    branch: complex analysis and geometry
    entry_module: LeanPool.JacobianDiffgeo
    authors:
      - Rado Kirov
    source:
      title: >-
        Jacobians of compact Riemann surfaces (AI challenge)
      authors:
        - Kevin Buzzard
      url: "https://gist.github.com/kbuzzard/778bc714030b3e974ab5f4038783d1a9"
      github_repo: rkirov/jacobian-fable
    license: Apache-2.0
    status: verified
    provenance: AI
    main_declarations:
      - JacobianChallenge.genus_eq_zero_iff_homeo
      - JacobianChallenge.Jacobian.ofCurve_inj
      - JacobianChallenge.Jacobian.pushforward_pullback
    main_results:
      - declaration: JacobianChallenge.genus_eq_zero_iff_homeo
        informal: >-
          A compact connected Riemann surface has genus zero if and only if it
          is homeomorphic to the 2-sphere.
      - declaration: JacobianChallenge.Jacobian.ofCurve_inj
        informal: >-
          The Abel-Jacobi map of a compact Riemann surface of positive genus is
          injective: two points with the same image coincide.
      - declaration: JacobianChallenge.Jacobian.pushforward_pullback
        informal: >-
          For a non-constant holomorphic map between compact Riemann surfaces,
          the pushforward composed with the pullback on Jacobians is
          multiplication by the degree of the map.
    tags:
      - riemann-surfaces
      - complex-geometry
      - abel-jacobi
      - riemann-roch
      - serre-duality
    msc:
      - "14H40"
      - "30F30"
      - "32G20"
"""
open(os.path.join(dst_root, "projects.yml.fragment"), "w", encoding="utf-8").write(CARD)

if CHECK:
    if not os.path.isdir(OUT):
        print(f"{OUT} does not exist; run without --check first")
        sys.exit(1)
    same = True
    for root, _, files in os.walk(dst_root):
        for name in files:
            a = os.path.join(root, name)
            b = os.path.join(OUT, os.path.relpath(a, dst_root))
            if not os.path.exists(b) or open(a, "rb").read() != open(b, "rb").read():
                print("stale:", os.path.relpath(a, dst_root))
                same = False
    sys.exit(0 if same else 1)

print(f"wrote {dst_root}: {count} library files + root module + projects.yml fragment")
print(f"PR assembly: copy {dst_root}/LeanPool/** into the pool checkout, splice")
print(f"{dst_root}/projects.yml.fragment into LeanPool/projects.yml, then run `lake exe mk_all`.")
