import Jacobian.PlanarStokes.Compat
import Jacobian.PlanarStokes.CompactSupport
import Jacobian.PlanarStokes.AnnulusResidue

/-!
# planar-stokes-atoms: compact-support planar Stokes for `∂̄` and the smeared residue theorem (`RS`)

Purely planar (mathlib-only, plus `Jacobian.Dbar.Wirtinger`/`Jacobian.ResidueCalculus`; no
manifold imports). API summary (see `docs/design/planar-stokes.md`):

* **Compat**: `RS.wirtingerDbar_mul` (Leibniz rule for `∂̄`, not in `Jacobian/Dbar/Wirtinger.lean`)
  and its holomorphic-factor/off-support specializations; `RS.ContDiffOn.contDiff_of_
  hasCompactSupport` (glue a `ContDiffOn` compactly-supported-in-`U` function to a global
  `ContDiff`); the `ℂ`-rectangle ↔ iterated-real-integral bridge
  (`RS.integral_eq_intervalIntegral_of_tsupport_subset_reProdIm`).
* **Atom 1** (`CompactSupport.lean`): `RS.integral_wirtingerDbar_eq_zero` — the `∂̄` of a
  compactly-supported `C¹` function integrates to `0` over all of `ℂ`; and its holomorphic-
  multiplier corollary `RS.integral_wirtingerDbar_mul_eq_zero_of_differentiableOn` (Atom 1b, the
  "no pole in this chart" case).
* **Atom 1′** (`AnnulusResidue.lean`): `RS.circleIntegral_sub_circleIntegral_eq_two_mul_I_mul_
  integral_wirtingerDbar` — the annulus Stokes identity (exp-substitution), general, no meromorphy.
* **Atom 2** (`AnnulusResidue.lean`, the smeared residue theorem):
  `RS.integral_wirtingerDbar_mul_eq_neg_pi_mul_resAt` — `∫∫ (∂̄g)·f = -π·g(p)·resAt f p`, for `g`
  compactly supported and **locally constant near the puncture `p`** (this hypothesis is load-
  bearing — the fully general smeared-residue formula for merely-continuous `g` and a pole of
  order `≥ 2` is false, see the design's §D4/§8.1 Fourier-resonance analysis; residue-theorem's
  `ContDiffBump`-built partitions of unity satisfy it for free). Cross-checked independently on
  `f = (·-p)⁻¹` (`RS.integral_wirtingerDbar_mul_inv_sub_eq`, proved via `RS.cauchyPompeiu`, not via
  Atom 2) — both routes agree on the `-π` constant.

Routing: residue-theorem consumes Atoms 1b/2 one chart at a time (PoU pieces), plus
`ResidueCalculus.resAt_comp_mul_deriv` (not from this unit) for chart-independence of `Res_p(ω)`
prior to summing; no "change of variables for the area integral" atom is designed or built here
(every integral here lives in one fixed chart, see §10). abel-weak-solutions is expected to need
only Atom 1/1b (a compact-support Green's-identity check, no poles) — see the design's §11 and the
build-log entry for this unit for the current read on its refinement needs.
-/
