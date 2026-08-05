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

# The pool's entry module has a fixed shape (`python/lean_pool/quality.py::_write_project_card`):
# the four-line header, then the imports, then the generated project card — and the card has to
# match `projects.yml` exactly or their card check rejects the PR. Everything else in this repo's
# `Jacobian.lean` (the prose comments) is dropped, since it would sit between the header and the
# imports and push the card out of that shape.
with open("Jacobian.lean", encoding="utf-8") as fh:
    root_src = rewrite(fh.read()).split("\n")
header = "\n".join(root_src[: root_src.index("-/") + 1])
imports = "\n".join(line for line in root_src if line.startswith("import "))

# Rendered exactly as `_project_card` renders it, from the same values as the YAML card below.
TITLE = "The Jacobian of a Compact Riemann Surface"
SOURCE_URL = "https://gist.github.com/kbuzzard/778bc714030b3e974ab5f4038783d1a9"
AUTHORS = ["Rado Kirov"]
STATUS = "verified"
# One headline declaration, not all three: the card is a Lean file, so a `Main declarations:` line
# listing three `JacobianChallenge.…` names would be 157 columns and the pool's build — which runs
# mathlib's `style.longLine` linter and fails on any warning — would reject it. The other two stay
# in `main_results`, which is prose and wraps.
MAIN_DECLARATIONS = ["JacobianChallenge.genus_eq_zero_iff_homeo"]
TAGS = ["riemann-surfaces", "complex-geometry", "abel-jacobi", "riemann-roch", "serre-duality"]
MSC = ["14H40", "30F30", "32G20"]

LEAN_CARD = "\n".join([
    "/-!",
    f"# {TITLE}",
    "",
    f"Source: url:{SOURCE_URL}",
    f"Authors: {', '.join(AUTHORS)}",
    f"Status: {STATUS}",
    "Main declarations: " + ", ".join(f"`{name}`" for name in MAIN_DECLARATIONS),
    f"Tags: {', '.join(TAGS)}",
    f"MSC: {', '.join(MSC)}",
    "-/",
])

open(os.path.join(dst_root, "LeanPool", f"{PROJECT}.lean"), "w", encoding="utf-8").write(
    f"{header}\n\n{imports}\n\n{LEAN_CARD}\n"
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
# The Lean card and the YAML card are two renderings of one project; a drift between them is
# exactly what the pool's card check rejects, so assert they agree before writing either.
for _value in [TITLE, SOURCE_URL, STATUS, *AUTHORS, *MAIN_DECLARATIONS, *TAGS, *MSC]:
    assert _value in CARD, f"card field not in projects.yml fragment: {_value}"
assert CARD.count("      - JacobianChallenge.") == len(MAIN_DECLARATIONS)

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
