# Submission: Jacobian-diffgeo

Solution to Kevin Buzzard's **Jacobians** AI challenge, v0.4
(https://gist.github.com/kbuzzard/778bc714030b3e974ab5f4038783d1a9).

## Claim

Every declaration of the challenge file is provided, with **zero `sorry`s** and no axioms beyond
`propext`, `Classical.choice`, `Quot.sound`. No `axiom`, `native_decide`, `unsafe`, or
`@[implemented_by]` anywhere in the development. All definitions are mathematically meaningful
(no vacuous carriers: `Jacobian X` is honestly `ℂ^g/Λ` with Λ proved discrete of rank `2g`;
`genus` is honestly `dim Ω¹(X)`; the no-hack guards `genus_eq_zero_iff_homeo` and `ofCurve_inj`
are proved as stated).

## Toolchain

- `leanprover/lean4:v4.32.2`
- mathlib pinned at `905b95818eb32af7874a58b427f50c1711a5e96c` (mathlib tag `v4.32.2`)

The gist header requires `v4.30.0-rc2` / mathlib `548398201a64f3a5127d90d83945278cfe38cac4`; the
development was forward-ported off that pin (statements unchanged, only mathlib API drift fixed).

## How to verify

```bash
lake exe cache get          # mathlib oleans
lake build                  # whole development: ~3,300 jobs, zero errors, zero sorries
lake env lean GistAcceptance.lean
```

`GistAcceptance.lean` is the acceptance artifact: it restates all 24 gist items **verbatim**
(the gist's exact statements, in the gist's own variable blocks) and proves each by the
providing declaration, then runs `#print axioms` on the six main items. If it compiles, the
challenge API exists at the claimed names with the claimed signatures and the claimed axioms.

Additional sweeps:

```bash
grep -rn -w sorry   Jacobian/ --include='*.lean'    # empty
grep -rnE '^\s*axiom |native_decide' Jacobian/ --include='*.lean'   # empty
```

## lean-eval submission (`jacobian_challenge_diffgeo`)

Upstream target: `leanprover/lean-eval`, problem workspace `generated/jacobian_challenge_diffgeo`.
Checked against upstream on 2026-08-03:

- upstream pins `leanprover/lean4:v4.32.2` + mathlib `905b95818eb32af7874a58b427f50c1711a5e96c`
  — **identical to this repo's pin**, so the submission builds on the same mathlib we build on;
- upstream `Challenge.lean` and `config.json` are byte-identical to `comparator/Challenge.lean`
  and `comparator/config.json` (the trusted statement is unchanged: 24 holes, permitted axioms
  `propext`, `Quot.sound`, `Classical.choice`);
- upstream `Solution.lean` gained `noncomputable` on its shim `def`s/`instance`s; the verbatim
  copy in `comparator/` was refreshed to match.

What gets submitted is the overlay in `submission/jacobian_challenge_diffgeo/` — `Submission.lean`
(the comparator shim) plus `Submission/**` (this library with its module prefix rewritten
`Jacobian.* → Submission.*`). Regenerate and check it with:

```bash
python3 scripts/make_submission.py            # regenerate from the library + shim
python3 scripts/make_submission.py --check    # exits 1 if the committed copy is stale (CI gate)
```

The equivalent-of-upstream check is `./verify.sh`: it builds the replica workspace in
`comparator/` (which path-requires this library, so the real build is what gets checked) and runs
the real `leanprover/comparator` through lean-eval's own `WorkspaceTest` harness, which forces
`enable_nanoda := true`. Tool revisions mirror lean-eval's `.github/workflows/ci.yml`:

| tool | pin | note |
| --- | --- | --- |
| comparator | `71b52ec2` | upstream builds it with its own toolchain (v4.30.0-rc2) |
| lean4export | `4e791520` (tag v4.32.0) | workspace `lean-toolchain` copied over it, as upstream does |
| nanoda | `68d5ca9` (robsimmons/nanoda_lib) | independent kernel replay, required for every problem |
| landrun | `v0.1.14` release binary | sandbox |

`verify.sh` defaults to building comparator with the *workspace* toolchain, so a dev box needs
only one Lean install; set `COMPARATOR_OWN_TOOLCHAIN=1` for upstream's exact recipe. The
`comparator` GitHub workflow runs `verify.sh` with that variable set on every push to
`lean-eval`.

**Status**: the comparator run on the v4.32.2 pin has *not* been completed on the development
machine (it ran out of disk partway through, after the workspace built); CI is the intended
runner for it. The comparator PASS recorded earlier in this repo was on the previous
v4.32.0-rc1 / mathlib `360da6fa` pin.

## Where each gist item lives

The gist declarations exist at their exact gist names (root level / `Jacobian` namespace).
`Jacobian/Challenge.lean` is the assembly point; its module docstring carries the item-by-item
provenance map, and its `GistCheck` section re-witnesses every item. Highlights:

| Gist | Location |
|---|---|
| `genus` | `Jacobian/Forms/Genus.lean` |
| `genus_eq_zero_iff_homeo` | `Jacobian/GenusSphereHeadline/Basic.lean` |
| `Jacobian` + 7 instances | `Jacobian/JacobianConstruction/Basic.lean` (instances unconditional after `Jacobian/CechCount/Final.lean`) |
| `Jacobian.ofCurve`, `ofCurve_self`, `ofCurve_contMDiff` | `Jacobian/JacobianConstruction/OfCurve.lean` |
| `Jacobian.ofCurve_inj` | `Jacobian/CechCount/Final.lean` |
| `Jacobian.pushforward`/`pullback`, 4 functoriality laws, `pushforward_pullback` | `Jacobian/JacFunctorial/` + `Jacobian/Challenge.lean` |
| `ContMDiff.degree` | `Jacobian/ProperDegree/ChallengeDegree.lean` |

## Documented deviations (cosmetic, 2)

1. **Universes.** The functorial declarations (`pushforward`/`pullback`/laws) state their
   surfaces in one shared `universe u` instead of the gist's independent `Type*`s: with
   independent universes the `ULift`/quotient defeq problem sends the elaborator into a
   deterministic timeout (documented in `Jacobian/JacFunctorial.lean`). Statements are otherwise
   verbatim; all same-universe uses (including everything in `Type`) elaborate identically.
2. **`ofCurve_contMDiff`** carries one extra *instance-implicit* argument
   (`[DiscreteTopology (RS.periodSubgroup X).topologicalClosure]`) which is discharged by a
   global instance — invisible at every use site; the gist-shaped statement elaborates verbatim
   (witnessed in `GistAcceptance.lean`).

## Provenance / clean-room statement

Built from scratch over the pinned mathlib following the mathematical roadmap in
`clean_room_blueprint.md`, consulting only the reference texts (Forster GTM 81, Miranda GSM 5,
Griffiths–Harris) and the pinned mathlib source. No existing solutions were consulted, on disk
or online. Design documents for every unit are in `docs/design/`; the full build journal is
`docs/build-log.md`; a post-mortem is in `RETRO.md`.

46,692 lines of Lean, 212 files, 32 units. See `README.md` for the architecture overview.
