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
