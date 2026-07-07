#!/usr/bin/env python3
"""Generate the lean-eval leaderboard submission overlay for jacobian_challenge_diffgeo.

Layout (the lean-eval submission pipeline overlays ONLY Submission.lean + Submission/**
onto its pristine problem workspace):

  submission/jacobian_challenge_diffgeo/
    lakefile.toml        (name = problem id; content otherwise unused by the CI)
    Submission.lean      (the comparator-PASSED shim, verbatim)
    Submission/**        (the whole Jacobian library, module prefix rewritten
                          Jacobian.* -> Submission.*; root module -> Submission/Root.lean;
                          Submission/Helpers.lean retargeted to Submission.Challenge)

Adapted from github.com/rkirov/jacobian-claude scripts/make_submission.py.
Run from the repo root: python3 scripts/make_submission.py
Staleness check (exits 1 if the committed copy differs): --check
"""
import os, re, shutil, sys, filecmp

CHECK = '--check' in sys.argv
REAL = 'submission/jacobian_challenge_diffgeo'
DST = '/tmp/jacobian_submission_check' if CHECK else REAL
shutil.rmtree(DST, ignore_errors=True)
os.makedirs(f'{DST}/Submission', exist_ok=True)

imp = re.compile(r'^import Jacobian(?=[.\s])', re.M)

def rewrite(text):
    return imp.sub('import Submission', text)

n = 0
for root, _, files in os.walk('Jacobian'):
    for f in files:
        if not f.endswith('.lean'):
            continue
        src = os.path.join(root, f)
        dst = os.path.join(DST, 'Submission', os.path.relpath(src, 'Jacobian'))
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        with open(src) as fh:
            open(dst, 'w').write(rewrite(fh.read()))
        n += 1

# the root library module becomes Submission/Root.lean
open(f'{DST}/Submission/Root.lean', 'w').write(rewrite(open('Jacobian.lean').read()))

# Helpers: same role as in the comparator workspace, retargeted to the rewritten library
open(f'{DST}/Submission/Helpers.lean', 'w').write(
    "/- Bridge from the shim to the full development (rewritten module prefix). -/\n"
    "import Submission.Root\n")

# Submission.lean = the comparator-PASSED shim, verbatim (imports Mathlib + Submission.Helpers)
shutil.copyfile('comparator/Submission.lean', f'{DST}/Submission.lean')

open(f'{DST}/lakefile.toml', 'w').write(
    'name = "jacobian_challenge_diffgeo"\n'
    'defaultTargets = ["Submission"]\n\n'
    '[[lean_lib]]\nname = "Submission"\n')

if CHECK:
    if not os.path.isdir(REAL):
        print('STALE: no committed submission workspace found')
        sys.exit(1)
    cmp = filecmp.dircmp(REAL, DST)
    def stale(c):
        return bool(c.left_only or c.right_only or c.diff_files or any(
            stale(sub) for sub in c.subdirs.values()))
    if stale(cmp):
        print('STALE: committed submission differs from fresh generation — rerun '
              'python3 scripts/make_submission.py')
        sys.exit(1)
    print('submission workspace is up to date')
else:
    print(f'wrote {DST}: {n} library files + Root/Helpers/Submission.lean/lakefile')
