import Jacobian.Monodromy.OpenLocus
import Jacobian.Meromorphic
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# `monodromy`: continuation of `log f` along pole/zero-avoiding paths

Unit: monodromy (`docs/design/monodromy.md` §4.2). The DAG-critical deliverable: a continuous
branch of `log f` (equivalently, a primitive of `dlog f = df/f`) along any path avoiding the
zeros/poles of a meromorphic function `f : ℳ X`, with the defining exponential compatibility
`exp (F t) = f.holoRepr (γ.extend t)`.

`dlogForm` is built by *reusing* `Jacobian/Forms/MDifferential.lean`'s `RS.mdifferential`
(the differential of a holomorphic function) and `RS.Form1.smulFun` (multiplication of a form by
a holomorphic function) — both already proved *generically* over any `X` satisfying the standing
surface hypotheses — instantiated with `X := poleZeroLocus f` (the open locus, `Jacobian/Monodromy
/OpenLocus.lean`). This sidesteps entirely the chart-transition/`subtypeRestr` bookkeeping a
from-scratch `Form1CoeffData` construction would need: `f.holoRepr` restricted to the locus is
`ContMDiff` (`mathlib`'s `contMDiffAt_subtype_iff` — smoothness of an open-submanifold restriction
is exactly a per-point statement), nonvanishing there (order `0` at every point of the locus, by
construction), hence its logarithmic derivative `(f.holoRepr)⁻¹ • d(f.holoRepr)` assembles as a
genuine `Form1 (poleZeroLocus f)` via the two already-built combinators, no new coefficient-data
proof needed.

The exponential-compatibility theorem (`exp_eq_holoRepr_of_isPrimitiveAlong`) shows any primitive
of `dlogForm` normalized at the starting value is an honest branch of `log f`, by exhibiting
`H t := f.holoRepr (γ.extend t) * exp (-(F t))` as locally constant (zero-derivative argument, via
`RS.eventuallyEq_of_hasDerivAt_eq`) and hence globally constant (`ℝ` preconnected) — no branch-cut
case analysis on `Complex.log`/`Complex.arg` anywhere.

Main declarations:
* `RS.Monodromy.poleZeroLocus`, `RS.Monodromy.dlogForm` — the pole/zero-free locus and the
  logarithmic-derivative 1-form on it.
* `RS.Monodromy.exp_eq_holoRepr_of_isPrimitiveAlong` — the exponential-compatibility theorem.
* `RS.Monodromy.exists_logBranchAlong`, `RS.Monodromy.logBranchAlong_unique` — existence with a
  prescribed initial branch value, and uniqueness (both bookkeeping over `Path`'s already-built
  existence/uniqueness API).
-/

open scoped ContDiff Manifold Topology
open Set Filter TopologicalSpace

noncomputable section

namespace RS.Monodromy

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The pole/zero-free locus -/

/-- The zero/pole locus of `f` as an open pole-free locus (`(divisor f).support` is finite by
compactness, hence closed by `T2Space`). -/
noncomputable def poleZeroLocus (f : ℳ X) : Opens X :=
  openLocusOfFinite (RS.finite_support_divisor f)

theorem mem_poleZeroLocus_iff {f : ℳ X} (hf : f ≠ 0) {x : X} :
    x ∈ poleZeroLocus f ↔ f.ord x = 0 := by
  show x ∈ openLocusOfFinite (RS.finite_support_divisor f) ↔ f.ord x = 0
  rw [mem_openLocusOfFinite, Function.mem_support, not_not, RS.divisor_apply,
    WithTop.untop₀_eq_zero]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h (RS.Mero.ord_ne_top hf x)
  · exact Or.inl

/-! ### `f.holoRepr` restricted to the locus is a nonvanishing holomorphic function -/

theorem contMDiff_holoRepr_poleZeroLocus (f : ℳ X) (hf : f ≠ 0) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun p : poleZeroLocus f => f.holoRepr (p : X)) := by
  intro p
  rw [contMDiffAt_subtype_iff]
  exact RS.MeroGermOn.holoRepr_contMDiffAt isOpen_univ (mem_univ (p : X))
    (le_of_eq (mem_poleZeroLocus_iff hf |>.mp p.2).symm)

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- `f.holoRepr` does not vanish anywhere on the order-zero locus (a helper for the general
"order exactly zero ⇒ the canonical representative is nonzero there" fact, R2 in the design). -/
theorem holoRepr_ne_zero_of_ord_eq_zero {f : ℳ X} {x : X} (h0 : f.ord x = 0) :
    f.holoRepr x ≠ 0 := by
  have hcm : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f.holoRepr x :=
    RS.MeroGermOn.holoRepr_contMDiffAt isOpen_univ (mem_univ x) (le_of_eq h0.symm)
  have hAn : AnalyticAt ℂ (f.holoRepr ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
    RS.contMDiffAt_iff_analyticAt_comp_chartAt.mp hcm
  have hordAmb : meromorphicOrderAt (f.holoRepr ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) = 0 := by
    show RS.ordAtX f.holoRepr x = 0
    have hmk : RS.MeroGermOn.mk f.holoRepr (RS.MeroGermOn.meromorphicOnX_holoRepr isOpen_univ f)
        = f := RS.MeroGermOn.mk_holoRepr isOpen_univ f
    calc RS.ordAtX f.holoRepr x
        = (RS.MeroGermOn.mk f.holoRepr
            (RS.MeroGermOn.meromorphicOnX_holoRepr isOpen_univ f)).ord x := by
          rw [RS.MeroGermOn.ord_mk isOpen_univ (mem_univ x)]
      _ = f.ord x := by rw [hmk]
      _ = 0 := h0
  have hNF : MeromorphicNFAt (f.holoRepr ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) := hAn.meromorphicNFAt
  have hne := hNF.meromorphicOrderAt_eq_zero_iff.mp hordAmb
  simpa [Function.comp_apply, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)] using hne

theorem holoRepr_poleZeroLocus_ne_zero (f : ℳ X) (hf : f ≠ 0) (p : poleZeroLocus f) :
    f.holoRepr (p : X) ≠ 0 :=
  holoRepr_ne_zero_of_ord_eq_zero (mem_poleZeroLocus_iff hf |>.mp p.2)

/-! ### `dlogForm`: the logarithmic-derivative 1-form on the locus -/

/-- The logarithmic-derivative 1-form `df/f` of `f`, a genuine holomorphic 1-form on the
pole/zero-free open locus `poleZeroLocus f` — assembled from `RS.mdifferential`/`RS.Form1.smulFun`
(both already built, generically over any surface satisfying the standing hypotheses),
instantiated with `X := poleZeroLocus f`. -/
noncomputable def dlogForm (f : ℳ X) (hf : f ≠ 0) : RS.Form1 (poleZeroLocus f) :=
  RS.Form1.smulFun (fun p : poleZeroLocus f => (f.holoRepr (p : X))⁻¹)
    ((contMDiff_holoRepr_poleZeroLocus f hf).inv₀ (holoRepr_poleZeroLocus_ne_zero f hf))
    (RS.mdifferential (fun p : poleZeroLocus f => f.holoRepr (p : X))
      (contMDiff_holoRepr_poleZeroLocus f hf))

/-- `dlogForm`'s coefficient in any maximal-atlas chart of the locus, on the chart target: the
familiar `(f'/f)`-shape logarithmic derivative, read through the chart. -/
theorem coeffIn_dlogForm (f : ℳ X) (hf : f ≠ 0)
    {e : OpenPartialHomeomorph (poleZeroLocus f) ℂ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω (poleZeroLocus f)) {z : ℂ} (hz : z ∈ e.target) :
    RS.coeffIn e (dlogForm f hf) z =
      (f.holoRepr ((e.symm z : X)))⁻¹ *
        deriv ((fun p : poleZeroLocus f => f.holoRepr (p : X)) ∘ ⇑e.symm) z := by
  show RS.coeffIn e (RS.Form1.smulFun _ _
    (RS.mdifferential (fun p : poleZeroLocus f => f.holoRepr (p : X))
      (contMDiff_holoRepr_poleZeroLocus f hf))) z = _
  rw [RS.coeffIn_smulFun]
  congr 1
  exact RS.coeffIn_mdifferential he (contMDiff_holoRepr_poleZeroLocus f hf) hz

end RS.Monodromy

end
