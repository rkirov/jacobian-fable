# Design: paths-and-integrals (`Jacobian/Path/`)

Owner unit of **CC6** (frozen in `docs/design/core-choices.md`). Defines the integral of a
holomorphic 1-form along a *continuous* path via primitives-along-the-path (Forster 10.9's
definition, done by chain continuation instead of the universal cover), proves homotopy
invariance (rel-endpoint and free-loop), the interval-integral bridge for C¹ pieces, periods,
and the perturb-a-loop-off-a-finite-set lemma. References: Forster §10 (book 68–81 = PDF 74–87;
esp. 10.1–10.5, 10.9–10.11). No measure theory on `X`; the only integration is planar.

**Spike status (compiled truth).** `scratch_paths.lean` (60 lines) compiles clean at the pin
(`lake env lean scratch_paths.lean`, exit 0, one unused-variable warning). Verified by *proof*
(not just `#check`):

1. **Mathlib HAS the disk primitive.** `Mathlib/Analysis/Complex/HasPrimitives.lean` (at the
   pin, 313 lines, Jauslin–Kontorovich–Nash): `Complex.IsExactOn f U := ∃ g, ∀ z ∈ U,
   HasDerivAt g (f z) z`, **`DifferentiableOn.isExactOn_ball : DifferentiableOn ℂ f (ball c r) →
   IsExactOn f (ball c r)`** (Morera/wedge-integral proof), and
   `Complex.IsExactOn.with_val_at (x₀) (y) : ∃ g, g x₀ = y ∧ ∀ x ∈ s, HasDerivAt g (f x) x`.
   The spike derives, in 2 lines, the exact atom we need:
   `AnalyticOnNhd ℂ f U → ball c r ⊆ U → ∃ g, g z₀ = w ∧ ∀ z ∈ ball c r, HasDerivAt g (f z) z`.
   **No power-series construction needed.** (CC6's "check mathlib for an existing
   disk-primitive" resolves YES.)
2. **Local uniqueness of primitives** compiles: two functions with `∀ᶠ z in 𝓝 z₀, HasDerivAt · (d z) z`
   and equal value at `z₀` agree on a neighborhood — via `Metric.eventually_nhds_iff_ball`,
   `Convex.is_const_of_fderivWithin_eq_zero` (`MeanValue.lean:558`),
   `fderivWithin_of_isOpen`, `HasFDerivAt.fderiv`, closing with `linear_combination`.
3. `Set.Countable.isPathConnected_compl_of_one_lt_rank` applies to `ℂ` with
   `rank_real_complex` + `norm_num` (spiked as a term proof).
4. Elaborated: `exists_monotone_Icc_subset_open_cover_unitInterval` and `_prod_self`
   (`Topology/UnitInterval.lean:481/:487` — the 1D subdivision AND the 2D grid Lebesgue lemma
   both exist!), `Path.Homotopy.transAssoc`, `Path.Homotopy.reflTransSymm`,
   `Path.Homotopic.hcomp`, `Path.truncate`, `Path.Homotopy.reparam`,
   `intervalIntegral.integral_eq_sub_of_hasDeriv_right`, `HasDerivAt.comp_hasDerivWithinAt`,
   `nhdsWithin_union`, `IsLocallyConstant.apply_eq_of_isPreconnected`,
   `Set.Countable.dense_compl`, `segment_inter_eq_endpoint_of_linearIndependent_of_ne`,
   `IsPreconnected.prod`.

**Path type decision (CC6 realization).** Use mathlib's `Path x y` (continuous, on
`I = unitInterval`) as the base type, and mathlib's `Path.Homotopy` / `Path.Homotopic` /
`Path.Homotopic.Quotient` for homotopy. *No smoothness anywhere*: the primitive-along-path
definition needs only continuity. Convention pin (verified in
`Topology/Homotopy/Path.lean`): for `F : Path.Homotopy p₀ p₁`, the **first** coordinate is the
deformation parameter — `F.eval 0 = p₀`, `F.eval 1 = p₁`, `F.source : F (t, 0) = x₀`,
`F.target : F (t, 1) = x₁`. Piecewise-C¹ appears only in the (optional-input) bridge lemma,
as an explicit `HasDerivWithinAt` hypothesis on `e ∘ γ.extend` — never as a class on paths.

Standing variables (every file except `Planar.lean`):

```lean
open scoped ContDiff Manifold unitInterval
open IsManifold Metric Set
namespace RS
variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
```

**No `T2Space`, `CompactSpace`, or `ConnectedSpace` anywhere in this unit** (compactness of
`[0,1]`/`[0,1]²` does all the work). Forms are named `η`, `θ` (`ω` is the smoothness exponent).

---

## 1. File plan

```
Jacobian/Path.lean               -- unit root: imports all, API docstring
Jacobian/Path/Planar.lean        -- pure-ℂ atoms; NO manifold imports (reused by dbar, monodromy,
                                 --   abel-weak, residue-calculus)
Jacobian/Path/LocalPrimitive.lean-- IsPrimitiveAlongMap (generic), rechart, uniqueness, glue, comp
Jacobian/Path/Chain.lean         -- ChartChain: subdivision + chart-ball data along a path
Jacobian/Path/Continuation.lean  -- existence, IsPrimitiveAlong, pathIntegral, path algebra, linearity
Jacobian/Path/Bridge.lean        -- interval-integral bridge (C¹, one chart), ∫ d f = Δf
Jacobian/Path/HomotopySquare.lean-- primitive along a square, homotopy invariance (rel + free)
Jacobian/Path/Periods.lean       -- period, periodVector, descent to Homotopic.Quotient
Jacobian/Path/Perturb.lean       -- loop perturbation off a finite set
```

Import skeleton:
- `Planar`: `Mathlib.Analysis.Complex.HasPrimitives`, `Mathlib.Analysis.Calculus.MeanValue`,
  `Mathlib.Analysis.Normed.Module.Connected`, `Mathlib.LinearAlgebra.Complex.FiniteDimensional`,
  `Mathlib.Topology.Homotopy.Path`, `Mathlib.Analysis.Convex.Segment` (for the
  segment-intersection lemma; already transitive).
- `LocalPrimitive`: `Jacobian.Forms.Coeffs`, `Jacobian.Path.Planar`,
  `Mathlib.Topology.LocallyConstant.Basic`.
- `Chain`: `Mathlib.Topology.UnitInterval` (subdivision lemmas), `Jacobian.Forms.Coeffs`.
- `Continuation`: the above + `Mathlib.Topology.Order.ProjIcc`.
- `Bridge`: + `Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`,
  `Jacobian.Forms.MDifferential`.
- `HomotopySquare`: + nothing new (grid lemma is in `Topology.UnitInterval`).
- `Perturb`: + `Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic` (groupoid-law homotopies).

---

## 2. The central definition

### 2.1 `IsPrimitiveAlongMap` (`LocalPrimitive.lean`)

One generic predicate serves paths (`α := ℝ`, `K := γ.extend`, `s := univ`), homotopy squares
(`α := ℝ × ℝ`, `K :=` clamped homotopy, `s := Icc 0 1 ×ˢ Icc 0 1` then upgraded to `univ`),
and restrictions to subintervals/edges (via `comp`):

```lean
variable {α : Type*} [TopologicalSpace α]

/-- `F` is a primitive of the 1-form `η` along the map `K` on `s`: near every `a ∈ s`
(within `s`), `F` factors as `g ∘ e ∘ K` for a chart `e` at `K a` and a planar local
primitive `g` of the chart coefficient of `η`. -/
def IsPrimitiveAlongMap (K : α → X) (η : Form1 X) (F : α → ℂ) (s : Set α) : Prop :=
  ∀ a ∈ s, ∃ e : OpenPartialHomeomorph X ℂ, e ∈ maximalAtlas 𝓘(ℂ) ω X ∧ K a ∈ e.source ∧
    ∃ g : ℂ → ℂ, (∀ᶠ z in 𝓝 (e (K a)), HasDerivAt g (coeffIn e η z) z) ∧
      ∀ᶠ b in 𝓝[s] a, K b ∈ e.source ∧ F b = g (e (K b))
```

Design notes.
- `𝓝[s] a` (not `𝓝 a`) makes restriction/gluing/edge-extraction compositional; for `a ∈ s`
  members of `𝓝[s] a` contain `a`, so `F a = g (e (K a))` holds *at* the point — used freely.
- The chart is existentially quantified per-point from the **maximal atlas** (matches
  `coeffIn_trans`/`analyticOnNhd_coeffIn` hypotheses in `docs/design/holomorphic-forms.md`).
- `g` is a primitive only *near the image point* — existence on a ball is always available
  (`Form1.analyticOnNhd_coeffIn` + the spiked planar atom), and the germ-level statement is
  what the uniqueness/gluing arguments actually consume.

### 2.2 Core lemma kit (all in `LocalPrimitive.lean`)

```lean
theorem IsPrimitiveAlongMap.mono (h : IsPrimitiveAlongMap K η F s) (hst : t ⊆ s) :
    IsPrimitiveAlongMap K η F t
theorem IsPrimitiveAlongMap.add_const (h : IsPrimitiveAlongMap K η F s) (c : ℂ) :
    IsPrimitiveAlongMap K η (fun a => F a + c) s          -- replace g by g + c
theorem IsPrimitiveAlongMap.congr (h : …) (hFF' : ∀ a ∈ s, F a = F' a) : …  -- also a K-congr twin
theorem IsPrimitiveAlongMap.continuousOn (h : …) (hK : ContinuousOn K s) : ContinuousOn F s

/-- Composition / restriction along a continuous map of parameter spaces. -/
theorem IsPrimitiveAlongMap.comp {β : Type*} [TopologicalSpace β]
    (h : IsPrimitiveAlongMap K η F s) {φ : β → α} {t : Set β}
    (hφ : ContinuousOn φ t) (hm : MapsTo φ t s) :
    IsPrimitiveAlongMap (K ∘ φ) η (F ∘ φ) t
  -- ContinuousWithinAt.tendsto_nhdsWithin transports the two ∀ᶠ's.
```

**Rechart** (the workhorse; used by uniqueness, glue, linearity, bridge):

```lean
/-- The chart in the local-primitive data can be re-chosen to be any maximal-atlas chart
containing the image point. -/
theorem IsPrimitiveAlongMap.rechart (h : IsPrimitiveAlongMap K η F s) (ha : a ∈ s)
    (hK : ContinuousWithinAt K s a)
    {e' : OpenPartialHomeomorph X ℂ} (he' : e' ∈ maximalAtlas 𝓘(ℂ) ω X)
    (hKa : K a ∈ e'.source) :
    ∃ g' : ℂ → ℂ, (∀ᶠ z in 𝓝 (e' (K a)), HasDerivAt g' (coeffIn e' η z) z) ∧
      ∀ᶠ b in 𝓝[s] a, K b ∈ e'.source ∧ F b = g' (e' (K b))
```

*Proof plan.* Let `(e, g)` be the given data, `p := K a`, `τ := ↑e ∘ ↑e'.symm` (the transition
`e'`-coords → `e`-coords). Set `g' := g ∘ τ`. (i) `τ` is analytic near `z' := e' p` with
`HasDerivAt τ (deriv τ z) z` there — from transition-map analyticity on the open overlap image
(`StructureGroupoid.compatible_of_mem_maximalAtlas he' he` +
`contDiffOn_omega_iff_analyticOn`; this helper is requested from holomorphic-forms /
local-multiplicity, see §8, with a 15-line local `Compat` fallback). (ii) chain rule:
`HasDerivAt g' (deriv g (τ z) * deriv τ z) z = HasDerivAt g' (coeffIn e η (τ z) * deriv τ z) z`,
and `coeffIn_trans he he'` says exactly
`coeffIn e' η z = deriv (↑e ∘ ↑e'.symm) z * coeffIn e η (e (e'.symm z))` — match up to `mul_comm`.
(iii) the eventual factorization: eventually in `𝓝[s] a`, `K b ∈ e.source ∩ e'.source` (data +
continuity of `K` within `s` + openness), and there
`g' (e' (K b)) = g (e (e'.symm (e' (K b)))) = g (e (K b)) = F b` by `e'.left_inv`. ∎

**Uniqueness up to a constant** — the subtle point the blueprint warns about. Chart overlaps
need NOT be connected; we never compare primitives on overlaps, only **along the parameter
space** (per CC6/task): the set where `F₁ - F₂` is locally constant is everything, and `s`
preconnected finishes.

```lean
theorem IsPrimitiveAlongMap.sub_eq_sub (hs : IsPreconnected s) (hK : ContinuousOn K s)
    (h₁ : IsPrimitiveAlongMap K η F₁ s) (h₂ : IsPrimitiveAlongMap K η F₂ s)
    (ha : a ∈ s) (hb : b ∈ s) : F₁ b - F₂ b = F₁ a - F₂ a
```

*Proof plan.* Fix `c ∈ s`. Take `h₁`'s data `(e₁, g₁)` at `c`; `rechart` `h₂`'s data into `e₁`,
getting `g₂'`. Both `g₁` and `g₂'` are `∀ᶠ`-primitives of `coeffIn e₁ η` at `z₀ := e₁ (K c)`;
by the spiked planar lemma (`eventuallyEq_of_hasDerivAt_eq` below, applied to
`g₂' + (g₁ z₀ - g₂' z₀)`), `g₁ - g₂'` is *constant near `z₀`*. Hence eventually in `𝓝[s] c`:
`F₁ b - F₂ b = g₁ (e₁ (K b)) - g₂' (e₁ (K b)) = g₁ z₀ - g₂' z₀ = F₁ c - F₂ c` (the middle step
needs `e₁ (K b)` eventually in the constancy ball: continuity of `K` within `s`). So
`D := F₁ - F₂` restricted to the subtype `↥s` satisfies `∀ x, ∀ᶠ y in 𝓝 x, D y = D x`, i.e.
`IsLocallyConstant D` by `IsLocallyConstant.iff_eventually_eq`
(subtype `𝓝` = comap of `𝓝[s]`: `nhds_subtype_eq_comap` plumbing, ~10 lines); conclude with
`IsLocallyConstant.apply_eq_of_preconnectedSpace` under `Subtype.preconnectedSpace hs`. ∎

**Glue** (the junction argument, factored ONCE; used by 1D existence, `trans`, and the 2D grid):

```lean
theorem IsPrimitiveAlongMap.glue [∀ a, Decidable (a ∈ s₁)]
    (hK : ContinuousOn K (s₁ ∪ s₂))
    (h₁ : IsPrimitiveAlongMap K η F₁ s₁) (h₂ : IsPrimitiveAlongMap K η F₂ s₂)
    (hL : IsPreconnected (s₁ ∩ s₂)) {a₀ : α} (ha₀ : a₀ ∈ s₁ ∩ s₂) (hval : F₁ a₀ = F₂ a₀)
    (hcov : ∀ a ∈ s₁ ∪ s₂, s₁ ∈ 𝓝[s₁ ∪ s₂] a ∨ s₂ ∈ 𝓝[s₁ ∪ s₂] a ∨ a ∈ s₁ ∩ s₂) :
    IsPrimitiveAlongMap K η (Set.piecewise s₁ F₁ F₂) (s₁ ∪ s₂)
```

*Proof plan.* First, `F₁ = F₂` on all of `s₁ ∩ s₂`: `sub_eq_sub` on `s₁ ∩ s₂` (both are
primitives there by `mono`; `hL`; `hval`). So `piecewise` is unambiguous on the overlap. At
`a` with `s₁ ∈ 𝓝[s₁∪s₂] a` (resp. `s₂`): use `h₁`'s (resp. `h₂`'s) data; the eventual claim
upgrades from `𝓝[s₁] a` to `𝓝[s₁∪s₂] a` because `𝓝[s₁∪s₂] a ⊓ 𝓟 s₁ ≤ 𝓝[s₁] a` and `s₁` is
eventually true. At `a ∈ s₁ ∩ s₂` (junction): take `h₁`-data `(e, g₁)` at `a`, `rechart`
`h₂`-data to `e` getting `g₂'`; both are `∀ᶠ`-primitives of `coeffIn e η` at `e (K a)` and
`g₁ (e (K a)) = F₁ a = F₂ a = g₂' (e (K a))`, so `g₁ =ᶠ[𝓝 (e (K a))] g₂'`
(`eventuallyEq_of_hasDerivAt_eq`). Split `𝓝[s₁∪s₂] a = 𝓝[s₁] a ⊔ 𝓝[s₂] a` (`nhdsWithin_union`);
on the `s₁` side `piecewise = F₁ = g₁ ∘ e ∘ K` eventually, on the `s₂` side
`piecewise = F₂ = g₂' ∘ e ∘ K = g₁ ∘ e ∘ K` eventually (the last step by the eventual equality
of `g₁, g₂'` + continuity of `K`). So `(e, g₁)` is data at `a` for the union. ∎

`hcov` dischargers (tiny private lemmas): for adjacent real intervals
`s₁ = Icc l c, s₂ = Icc c r` (`Icc_union_Icc_eq_Icc`, one-sided `Icc_mem_nhdsWithin_*`), and
for products `Icc ×ˢ Icc` split along one coordinate.

### 2.3 Planar atoms (`Planar.lean`, no manifold imports)

```lean
/-- Primitive with prescribed value on a ball inside a domain of analyticity. [spiked verbatim] -/
theorem exists_hasDerivAt_ball {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U)
    {c z₀ w : ℂ} {r : ℝ} (hb : ball c r ⊆ U) (hz₀ : z₀ ∈ ball c r) :
    ∃ g : ℂ → ℂ, g z₀ = w ∧ ∀ z ∈ ball c r, HasDerivAt g (f z) z

/-- Two local primitives of the same function with equal value agree nearby. [spiked verbatim] -/
theorem eventuallyEq_of_hasDerivAt_eq {f g d : ℂ → ℂ} {z₀ : ℂ}
    (hf : ∀ᶠ z in 𝓝 z₀, HasDerivAt f (d z) z) (hg : ∀ᶠ z in 𝓝 z₀, HasDerivAt g (d z) z)
    (h : f z₀ = g z₀) : f =ᶠ[𝓝 z₀] g

/-- An open convex planar set minus a countable set is path-connected. -/
theorem Convex.isPathConnected_diff_countable {s : Set ℂ} (hs : Convex ℝ s) (ho : IsOpen s)
    (hne : s.Nonempty) {T : Set ℂ} (hT : T.Countable) : IsPathConnected (s \ T)

/-- Any two paths with the same endpoints inside a convex planar set are homotopic
rel endpoints, through the set. -/
theorem exists_homotopy_range_subset_of_convex {a b : ℂ} {s : Set ℂ} (hs : Convex ℝ s)
    {p q : Path a b} (hp : range ⇑p ⊆ s) (hq : range ⇑q ⊆ s) :
    ∃ H : p.Homotopy q, ∀ z, H z ∈ s
```

*`isPathConnected_diff_countable` proof plan* (adaptation of
`Set.Countable.isPathConnected_compl_of_one_lt_rank`, whose proof was read at the pin): WLOG
`a ≠ b ∈ s \ T`. Midpoint `m := (a+b)/2 ∈ s`; `x := (b-a)/2 ≠ 0`; pick `y` with
`![x, y]` ℝ-linearly independent (`exists_linearIndependent_pair_of_one_lt_rank`,
`rank_real_complex`). Choose `ε > 0` with `ball m ε ⊆ s` (`ho`). For
`t ∈ Ioo (-ε/‖y‖) (ε/‖y‖)`, `z t := m + t • y ∈ s`. The two exceptional sets
`{t | ([a -[ℝ] z t] ∩ T).Nonempty}` and `{t | ([b -[ℝ] z t] ∩ T).Nonempty}` are countable —
by `countable_setOf_nonempty_of_disjoint`, since distinct `t`'s give segments meeting only at
the common endpoint (`segment_inter_eq_endpoint_of_linearIndependent_of_ne`; for the `a`-family
apply it with the independent pair `![-x, y]` as mathlib's proof does, via `.units_smul`).
`Ioo` is uncountable (`Cardinal.not_countable_real`-style; or: its complement-in-itself of a
countable set is nonempty by measure/cardinality — use `Set.Countable.dense_compl ℝ` on the
countable union restricted to the interval: `(A ∪ B).dense_compl` gives a point in
`Ioo ∩ (A ∪ B)ᶜ` since `Ioo` is open nonempty). Then `a → z t → b` along two segments inside
`s` (convexity) avoiding `T`; also both segment endpoints avoid `T`. `JoinedIn.trans` of two
`JoinedIn.of_segment_subset`. ~80 lines.

*`exists_homotopy_range_subset_of_convex` plan*: the affine homotopy
`H (τ, u) := (1 - τ) • p u + τ • q u` as an explicit `ContinuousMap.HomotopyRel` (structure
fields: `toFun`/`map_zero_left`/`map_one_left`/`prop'`; continuity by `fun_prop`/`Continuous.smul`;
membership by `hs hp hq`; rel-`{0,1}` since `p 0 = q 0`, `p 1 = q 1`). ~25 lines.

`Planar.lean` is the "clean standalone planar file" for reuse: **dbar-solvability,
residue-calculus, monodromy, abel-weak should import `Jacobian.Path.Planar` (or
`Mathlib.Analysis.Complex.HasPrimitives` directly) for disk primitives** — do not re-prove.

---

## 3. Chains, existence, `pathIntegral` (`Chain.lean`, `Continuation.lean`)

### 3.1 `ChartChain`

```lean
/-- A subdivision of `[0,1]` with chart-and-ball data adapted to `γ`. -/
structure ChartChain (γ : Path x y) where
  n : ℕ
  t : ℕ → ℝ
  ht0 : t 0 = 0
  ht1 : ∀ k, n ≤ k → t k = 1
  mono : Monotone t
  e : ℕ → OpenPartialHomeomorph X ℂ
  he : ∀ k, e k ∈ maximalAtlas 𝓘(ℂ) ω X
  c : ℕ → ℂ
  r : ℕ → ℝ
  hr : ∀ k, 0 < r k
  ball_subset : ∀ k, ball (c k) (r k) ⊆ (e k).target
  maps : ∀ k, ∀ u ∈ Icc (t k) (t (k + 1)),
    γ.extend u ∈ (e k).source ∧ e k (γ.extend u) ∈ ball (c k) (r k)

theorem exists_chartChain (γ : Path x y) : Nonempty (ChartChain γ)
```

*Proof plan.* For each `τ : I`, let `eτ := chartAt ℂ (γ τ)` (∈ atlas ⊆ maximal atlas via
`subset_maximalAtlas (chart_mem_atlas …)`), pick `rτ > 0` with
`ball (eτ (γ τ)) rτ ⊆ eτ.target` (target open). `Oτ := γ ⁻¹' (eτ.source ∩ eτ ⁻¹' ball …)` is
open in `I` and contains `τ`; apply `exists_monotone_Icc_subset_open_cover_unitInterval`
(ι := I, spiked) to get `t : ℕ → I` with `t 0 = 0`, monotone, `∃ n, ∀ m ≥ n, t m = 1`, and each
`Icc (t k) (t (k+1))` inside some `O_{i k}` (choice). Coerce `t` to ℝ; `γ.extend u = γ ⟨u, _⟩`
on `[0,1]` (`Path.extend_extends`) converts subtype membership to the `maps` field. ~120 lines
of routine plumbing. (This structure is deliberately export-grade: `Perturb.lean` consumes it,
and the monodromy unit (21) can reuse it for chain continuation.)

### 3.2 Existence and definition of the integral

```lean
def IsPrimitiveAlong (γ : Path x y) (η : Form1 X) (F : ℝ → ℂ) : Prop :=
  IsPrimitiveAlongMap γ.extend η F Set.univ

theorem exists_isPrimitiveAlong (γ : Path x y) (η : Form1 X) :
    ∃ F : ℝ → ℂ, IsPrimitiveAlong γ η F ∧ F 0 = 0

noncomputable def pathIntegral (γ : Path x y) (η : Form1 X) : ℂ :=
  (exists_isPrimitiveAlong γ η).choose 1

theorem IsPrimitiveAlong.pathIntegral_eq {F} (hF : IsPrimitiveAlong γ η F) :
    pathIntegral γ η = F 1 - F 0
```

*Existence proof plan.* Take `C : ChartChain γ`. By induction on `k ≤ C.n` build
`F_k : ℝ → ℂ` with `IsPrimitiveAlongMap γ.extend η F_k (Icc 0 (C.t k))` and `F_k 0 = 0`.
- Base `k = 0`: `Icc 0 0 = {0}`; data at `0`: chart `C.e 0`, primitive `g` on the ball through
  `exists_hasDerivAt_ball` with value pinned so `g (e (γ 0)) = 0`; `F₀ := fun _ => 0`; the
  `∀ᶠ` in `𝓝[{0}] 0` is evaluation at `0` only.
- Step: the piece `G := fun u => g_k (C.e k (γ.extend u))` with `g_k` from
  `exists_hasDerivAt_ball` (on `ball (C.c k) (C.r k) ⊆ target`, coefficient analytic there by
  `Form1.analyticOnNhd_coeffIn (C.he k)`) is `IsPrimitiveAlongMap` on `s₂ := Icc (C.t k) (C.t (k+1))`
  *with the same `(e, g)` at every point* — the `maps` field puts the whole piece inside
  chart+ball. Shift by `add_const` so it matches `F_k` at `C.t k`; `glue` along
  `s₁ ∩ s₂ = {C.t k}` (singleton: preconnected; `hval` by the shift; `hcov` by the interval
  helper; degenerate steps `t k = t (k+1)` are harmless). `Icc_union_Icc_eq_Icc` re-types the
  union.
- At `k = C.n`: `F` on `Icc 0 1`. Upgrade to `univ`: `F ∘ clamp` with
  `clamp := fun u => max 0 (min u 1)` via `comp` (`γ.extend ∘ clamp = γ.extend` — pointwise
  from `extend_of_le_zero`, `extend_of_one_le`, `extend_extends`; `MapsTo clamp univ (Icc 0 1)`).
  `F (clamp 0) = F 0 = 0`. ∎

*Well-definedness* (`pathIntegral_eq`): two primitives along `γ` differ by a constant on
`univ` (`sub_eq_sub`, `isPreconnected_univ`, `γ.continuous_extend.continuousOn`). ∎

### 3.3 Path algebra — all via `comp` with clamped reparametrizations

Every invariance is a 3-to-10-liner from `comp` + `sub_eq_sub`, because the definition is
germ-level (this is the payoff of the continuation definition; reparametrization invariance is
"free" as the task predicted, and needs **no monotonicity** of the reparametrization):

```lean
@[simp] theorem pathIntegral_refl (x : X) (η : Form1 X) : pathIntegral (Path.refl x) η = 0
@[simp] theorem pathIntegral_symm (γ : Path x y) (η) :
    pathIntegral γ.symm η = -pathIntegral γ η
  -- F ∘ (fun u => 1 - u); Path.extend_symm_apply holds for ALL real u.
theorem pathIntegral_trans (γ : Path x y) (γ' : Path y z) (η) :
    pathIntegral (γ.trans γ') η = pathIntegral γ η + pathIntegral γ' η
  -- With H a primitive along γ.trans γ': H ∘ (fun u => clamp u / 2) is a primitive along γ
  -- ((γ.trans γ').extend (clamp u / 2) = γ.extend u via extend_trans_of_le_half), and
  -- H ∘ (fun u => (1 + clamp u) / 2) one along γ' (extend_trans_of_half_le). Telescope.
theorem pathIntegral_reparam (γ : Path x y) {f : I → I} (hf : Continuous f)
    (h₀ : f 0 = 0) (h₁ : f 1 = 1) (η) :
    pathIntegral (γ.reparam f hf h₀ h₁) η = pathIntegral γ η
  -- F ∘ (fun u => ↑(f (projIcc 0 1 zero_le_one u))); continuous_projIcc.
@[simp] theorem pathIntegral_cast {x' y'} (γ : Path x y) (hx : x' = x) (hy : y' = y) (η) :
    pathIntegral (γ.cast hx hy) η = pathIntegral γ η
```

ℂ-linearity in `η` (rechart both data to a common chart, add the planar primitives):

```lean
theorem pathIntegral_add (γ) (η θ) : pathIntegral γ (η + θ) = pathIntegral γ η + pathIntegral γ θ
theorem pathIntegral_smul (γ) (c : ℂ) (η) : pathIntegral γ (c • η) = c * pathIntegral γ η
@[simp] theorem pathIntegral_zero_form (γ) : pathIntegral γ (0 : Form1 X) = 0
noncomputable def pathIntegralₗ (γ : Path x y) : Form1 X →ₗ[ℂ] ℂ   -- bundling the above
```

(Proof of `add`: given primitives `F, G` with data `(e₁,g₁)`, `(e₂,g₂)` at `a`, rechart the
second to `e₁`; `g₁ + g₂'` is a local primitive of `coeffIn e₁ (η + θ)` by `coeffIn_add`;
`F + G` matches. `smul` likewise with `coeffIn_smul`.)

---

## 4. The bridge to honest integrals (`Bridge.lean`)

Ownership decision: **this unit proves the abstract single-chart C¹ bridge as an
interval integral**; `circleIntegral`/`curveIntegral` specializations (e.g. for `circleMap`)
belong to **residue-calculus / planar-stokes-atoms**, which own the planar contour calculus.
For piecewise-C¹ paths, consumers subdivide with `Path.truncate`-style decompositions or apply
the bridge per piece and add via `pathIntegral_trans`. (Mathlib's
`MeasureTheory/Integral/CurveIntegral/Basic.lean` was checked: `curveIntegral` is
`∫ t in 0..1, ω (γ.extend t) (derivWithin γ.extend I t)` for planar 1-forms `E → E →L F`; our
interval-integral form composes with it trivially if ever needed, but nothing downstream
consumes `curveIntegral` directly, so we do not export that wrapper.)

```lean
/-- On a path contained in a single chart, `pathIntegral` is the classical integral
`∫ coeff · (chart∘γ)'`. -/
theorem pathIntegral_eq_intervalIntegral {γ : Path x y} {η : Form1 X}
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ maximalAtlas 𝓘(ℂ) ω X)
    (hγ : range ⇑γ ⊆ e.source) {u' : ℝ → ℂ}
    (hu : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt (fun s => e (γ.extend s)) (u' t) (Icc 0 1) t)
    (hu' : ContinuousOn u' (Icc 0 1)) :
    pathIntegral γ η = ∫ t in (0:ℝ)..1, coeffIn e η (e (γ.extend t)) * u' t
```

*Proof plan.* Let `F` be the chosen primitive along `γ`, so LHS `= F 1 - F 0`. Claim:
`∀ t ∈ Icc 0 1, HasDerivWithinAt F (coeffIn e η (e (γ.extend t)) * u' t) (Icc 0 1) t`. At `t`:
`rechart` the data into `e` (possible since `γ.extend t ∈ e.source` by `hγ` +
`extend_range`), giving `g` with `HasDerivAt g (coeffIn e η ·)` near `e (γ.extend t)` and
`F = g ∘ (e ∘ γ.extend)` eventually near `t` (here `s = univ`, so plain `𝓝 t`). Chain rule
`HasDerivAt.comp_hasDerivWithinAt` on `g` and `hu t`, then
`HasDerivWithinAt.congr_of_eventuallyEq` (values agree at `t`). FTC-2:
`intervalIntegral.integral_eq_sub_of_hasDeriv_right` with (i) `ContinuousOn F (Icc 0 1)` from
`IsPrimitiveAlongMap.continuousOn`, (ii) interior derivative from the claim via
`HasDerivWithinAt.mono_of_mem_nhdsWithin` (`Icc 0 1 ∈ 𝓝[>] t` for `t ∈ Ioo 0 1`), (iii)
integrand `IntervalIntegrable` since it is continuous on `Icc 0 1`
(`coeffIn` analytic⇒continuous on target ∘ continuous, times `hu'`;
`ContinuousOn.intervalIntegrable`). ∎ (~60 lines.)

```lean
/-- FTC along a path: `∫_γ df = f(end) − f(start)` (Forster 10.2, continuous-path version). -/
theorem pathIntegral_mdifferential {f : X → ℂ} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (γ : Path x y) : pathIntegral γ (mdifferential f hf) = f y - f x
```

*Proof plan.* `F := f ∘ γ.extend` is a primitive along `γ`: at `t`, chart
`e := chartAt ℂ (γ.extend t)`, `g := f ∘ ↑e.symm`; `g` is analytic near `e (γ.extend t)`
(holomorphic-forms' `contMDiffAt_iff_analyticAt_comp` applied to `hf` at the point — stated for
`chartAt`-charts, which is why we pick `e := chartAt`), and `deriv g = coeffIn e (mdifferential f)`
on the target by `coeffIn_mdifferential` (+ `AnalyticAt.hasDerivAt`-style upgrade
`AnalyticAt.differentiableAt.hasDerivAt`, congr on the open target). `F u = g (e (γ.extend u))`
near `t` by `e.left_inv`. Then `pathIntegral_eq` gives `F 1 - F 0 = f y - f x`. ∎
(Feeds monodromy and sphere-topology; no `Surface` import needed.)

---

## 5. Homotopy invariance (`HomotopySquare.lean`) — the grid argument

Route decision: **hand-rolled grid** (Forster 10.10's content, but done as "a primitive along
the homotopy square exists", which subsumes both (a) rel-endpoints and (b) free-loop versions
and is precisely what mathlib's 2D Lebesgue lemma
`exists_monotone_Icc_subset_open_cover_unitInterval_prod_self` supports). Mathlib's
covering-space monodromy (`Topology/Homotopy/Lifting.lean`) is NOT used: it would require
building the primitive covering space first (that is the monodromy unit's later device, and
overkill here).

### 5.1 The square theorem

```lean
/-- A primitive of `η` along a continuous square `H : C(I × I, X)` exists. -/
theorem exists_primitive_along_square (H : C(I × I, X)) (η : Form1 X) :
    ∃ F : ℝ × ℝ → ℂ,
      IsPrimitiveAlongMap (fun p => H (projIcc 0 1 zero_le_one p.1, projIcc 0 1 zero_le_one p.2))
        η F Set.univ
```

*Proof plan.* Write `K : ℝ × ℝ → X` for the clamped map, `Q c d := Icc 0 c ×ˢ Icc 0 d ⊆ ℝ²`.
1. **Grid.** As in `exists_chartChain` but on `I × I`: cover by preimages of chart-balls;
   `exists_monotone_Icc_subset_open_cover_unitInterval_prod_self` gives ONE monotone
   `t : ℕ → I` (with `t 0 = 0`, stabilizing at `1` from index `m`) such that every grid cell
   `Icc (t j) (t (j+1)) ×ˢ Icc (t k) (t (k+1))` maps into a single chart-ball `(e j k, B j k)`.
   Coerce to ℝ.
2. **Cell primitive.** On cell `(j, k)`: `G := g ∘ e j k ∘ K` with `g` from
   `exists_hasDerivAt_ball` is `IsPrimitiveAlongMap … (cell)` with constant data (as in 1D).
3. **Row (strip) assembly** — inner induction on `k`: primitives on
   `Icc (t j) (t (j+1)) ×ˢ Icc 0 (t k)` glued with the next cell along
   `L = Icc (t j) (t (j+1)) ×ˢ {t k}` — a segment: `IsPreconnected` by
   `isPreconnected_Icc.prod isPreconnected_singleton` (`IsPreconnected.prod` verified). `hval`
   by `add_const`-normalizing at one corner; `hcov` by the product-interval helper (split in
   the second coordinate).
4. **Stacking strips** — outer induction on `j`: primitive on `Q (t j) 1` glued with the
   strip along `L' = {t j} ×ˢ Icc 0 1` (again `IsPreconnected.prod`), same normalize-and-glue.
5. At `j = m`: primitive on `Q 1 1`. Upgrade to `univ` by `comp` with the componentwise clamp
   (`K ∘ clamp² = K` pointwise). ∎ (~250 lines; the only genuinely new content vs 1D is the
   product `hcov`/`IsPreconnected` bookkeeping — `glue` itself is reused verbatim.)

### 5.2 Consequences

```lean
theorem pathIntegral_congr_homotopic {γ₀ γ₁ : Path x y} (h : γ₀.Homotopic γ₁) (η : Form1 X) :
    pathIntegral γ₀ η = pathIntegral γ₁ η
```

*Proof.* `H := h.some` (a `Path.Homotopy`, i.e. `HomotopyRel … {0,1}`); `F` from §5.1 along
`H.toContinuousMap`. Restrict to the four edges by `comp` with the affine maps
`u ↦ (0, u), (1, u), (u, 0), (u, 1)` (clamped): the bottom/top restrictions are primitives
along `γ₀.extend`, `γ₁.extend` (using `H.eval 0 = γ₀` etc. and, on the edges,
`Path.Homotopy.source/target`), so `pathIntegral γᵢ η = F(i,1) − F(i,0)`; the side
restrictions are primitives along `Path.refl x` and `Path.refl y` (rel-endpoint property
`HomotopyRel.eq_fst/eq_snd`), hence constant: `F(1,0) = F(0,0)`, `F(1,1) = F(0,1)`
(uniqueness against the constant primitive, or directly `sub_eq_sub` with `F₂ := const`).
Combine. ∎

```lean
/-- Descent of the integral to homotopy classes (consumed by π₁-flavoured statements). -/
noncomputable def pathIntegralQ (η : Form1 X) (q : Path.Homotopic.Quotient x y) : ℂ :=
  Quotient.liftOn q (pathIntegral · η) fun _ _ h => pathIntegral_congr_homotopic h η
@[simp] theorem pathIntegralQ_mk (γ : Path x y) (η) : pathIntegralQ η ⟦γ⟧ = pathIntegral γ η
theorem pathIntegralQ_trans (p : …Quotient x y) (q : …Quotient y z) (η) :
    pathIntegralQ η (p.trans q) = pathIntegralQ η p + pathIntegralQ η q   -- Quotient.ind₂

/-- Free homotopy of loops (moving basepoint) preserves periods. -/
theorem pathIntegral_congr_freeHomotopic {x₀ x₁ : X} {γ₀ : Path x₀ x₀} {γ₁ : Path x₁ x₁}
    (H : ContinuousMap.Homotopy γ₀.toContinuousMap γ₁.toContinuousMap)
    (hloop : ∀ s : I, H (s, 0) = H (s, 1)) (η : Form1 X) :
    pathIntegral γ₀ η = pathIntegral γ₁ η
  -- Same square; now the two side edges are BOTH primitives along the basepoint track
  -- σ := fun s => H (s, 0) (well-defined as a Path (H(0,0)) (H(1,0)) via hloop for the right
  -- edge), so F(1,0)−F(0,0) = ∫σ = F(1,1)−F(0,1); rearrange.

theorem pathIntegral_eq_of_simplyConnected [SimplyConnectedSpace X] (γ₀ γ₁ : Path x y) (η) :
    pathIntegral γ₀ η = pathIntegral γ₁ η   -- simply_connected_iff_paths_homotopic
theorem period_eq_zero_of_homotopic_refl {γ : Path x x} (h : γ.Homotopic (.refl x)) (η) :
    pathIntegral γ η = 0
```

The last two feed **sphere-topology** (backward headline: on simply-connected `X` all periods
vanish; the exactness/genus-0 conclusion is the monodromy unit's job, unit 21 — NOT here).

---

## 6. Periods (`Periods.lean`)

Carrier decision (CC9 alignment): the clean carrier is **based loops `Path x x`**, with descent
to `Path.Homotopic.Quotient x x` available via `pathIntegralQ`. We do NOT define the period
subgroup here — CC9's `AddSubgroup (Fin (genus X) → ℂ)` is owned by jacobian-construction;
we export exactly the ingredients its `AddSubgroup.closure (Set.range (periodVector b))`
recipe needs, plus the loop-algebra lemmas that make the range ℤ-span-friendly:

```lean
/-- The period of a 1-form along a loop. -/
noncomputable abbrev period (γ : Path x x) (η : Form1 X) : ℂ := pathIntegral γ η

theorem period_trans (γ γ' : Path x x) (η) : period (γ.trans γ') η = period γ η + period γ' η
theorem period_symm (γ : Path x x) (η) : period γ.symm η = -period γ η
@[simp] theorem period_refl (η) : period (Path.refl x) η = 0
theorem period_congr_homotopic {γ γ' : Path x x} (h : γ.Homotopic γ') (η) : …
/-- Conjugation invariance: periods are basepoint-independent along a connecting path. -/
theorem period_conj (σ : Path x' x) (γ : Path x x) (η) :
    period ((σ.trans γ).trans σ.symm) η = period γ η   -- pure trans/symm algebra

/-- Period vector w.r.t. a basis of `Form1 X` (CC9 feed). -/
noncomputable def periodVector {n : ℕ} (b : Basis (Fin n) ℂ (Form1 X)) (γ : Path x x) :
    Fin n → ℂ := fun i => period γ (b i)
theorem periodVector_trans / periodVector_symm / periodVector_refl  -- Pi.add/neg/zero shapes
```

jacobian-construction then defines (their file, spelled here for coordination):
`periodSubgroup b x₀ : AddSubgroup (Fin g → ℂ) := AddSubgroup.closure
(Set.range fun γ : Path x₀ x₀ => periodVector b γ)` — `AddSubgroup.closure` IS the ℤ-span;
`periodVector_trans/symm/refl` show the range is already closed under `+`/`-`/`0` when they
need `closure = range`-type facts, and `period_conj` + `pathIntegral_trans` give
basepoint-independence and the `ofCurve` well-definedness argument of CC9 (path-difference
= loop ⇒ difference of `ofCurve` integrals lies in the subgroup — **no homotopy invariance
needed for that**, only `trans`/`symm`; homotopy invariance is exported anyway for
period-lattice-rank and monodromy). If they prefer a `Submodule ℤ`, `AddSubgroup.toIntSubmodule`
bridges.

---

## 7. Perturbing a loop off a finite set (`Perturb.lean`)

Blueprint ⚠ heeded: we perturb **breakpoint values** (the `γ (t k)`), not the loop pointwise;
each replacement arc is chosen inside one chart ball. The final statement quantifies only over
the homotopy class — that is all Abel needs, since (i) periods only depend on the class (§5),
and (ii) any *re*-subdivision of the output loop automatically has breakpoints off `S` because
the whole loop avoids `S`.

```lean
theorem exists_homotopic_avoiding {a b : X} (γ : Path a b) {S : Set X} (hS : S.Finite)
    (ha : a ∉ S) (hb : b ∉ S) :
    ∃ γ' : Path a b, γ.Homotopic γ' ∧ Disjoint (Set.range ⇑γ') S

/-- Loop version (the blueprint's deliverable). -/
theorem Loop.exists_homotopic_avoiding (γ : Path x₀ x₀) {S : Set X} (hS : S.Finite)
    (hx₀ : x₀ ∉ S) : ∃ γ' : Path x₀ x₀, γ.Homotopic γ' ∧ Disjoint (Set.range ⇑γ') S
```

*Proof plan* (strong induction on `ChartChain` length; all homotopy algebra done in
`Path.Homotopic.Quotient` where `trans` is associative etc. via the verified
`Path.Homotopy.transAssoc/reflTransSymm/transRefl/reflTrans` +
`Path.Homotopic.trans_symm/symm_trans` from `AlgebraicTopology/FundamentalGroupoid/Basic.lean`):

0. **Truncation decomposition** (new lemma, `Perturb.lean`-local):
   ```lean
   theorem Path.homotopic_truncate_trans (γ : Path a b) {c : ℝ} (h₀ : 0 ≤ c) (h₁ : c ≤ 1) :
       (((γ.truncate 0 c).cast (by simp [γ.extend_zero, min_eq_left h₀]) rfl).trans
         ((γ.truncate c 1).cast rfl (by simp [γ.extend_one, min_eq_left h₁]))).Homotopic γ
   ```
   Proof: the LHS equals `γ.reparam ρ` for the explicit
   `ρ u := if (u:ℝ) ≤ 1/2 then min (2*u) c else min (max (2*u - 1) c) 1` (check by `Path.ext` +
   `Path.trans_apply` + the `truncate` formula `γ.extend (min (max s t₀) t₁)`, read from the
   pin); then `Path.Homotopy.reparam`. (~50 lines; flagged risk R4.)
1. **Base case** (chain length 1, whole path in one chart-ball `(e, B)`): endpoints
   `a, b ∉ S`. Planar: `p := (e∘γ)`-path from `e a` to `e b` inside `B`;
   `T := e '' (S ∩ e.source)` finite; `e a, e b ∈ B \ T`;
   `Convex.isPathConnected_diff_countable` (ball, finite ⊆ countable) gives a planar
   `q : Path (e a) (e b)` with range ⊆ `B \ T`; `exists_homotopy_range_subset_of_convex`
   homotopes `p ~ q` inside `B` (the homotopy MAY cross `T` — harmless). Transport through
   `e.symm`: `γ' := q.map' (e.symm-continuity on B ⊆ target)`, and the homotopy transports as
   an explicit `HomotopyRel` with `toFun := ↑e.symm ∘ H`, continuity via
   `ContinuousOn.comp_continuous` (range of `H` ⊆ `B ⊆ e.target`), and `e.symm ∘ e ∘ γ = γ` on
   the source. `range γ' ∩ S = ∅` since `z ∈ B \ T ⇒ e.symm z ∉ S`.
2. **Inductive step** (chain of length `n+1`): let `c := t 1`, `m := γ.extend c`. The point `m`
   lies in `W₀ ∩ W₁` (both adjacent chart-ball preimages, by the two `maps` fields at the
   shared endpoint). Pick a *new breakpoint*: inside the open `e₁ '' (W₀ ∩ W₁ ∩ (e₁).source)`
   choose a small ball `B' ∋ e₁ m`, then `b₁' ∈ B' \ (T₁ ∪ {junk})` nonempty by
   `Set.Countable.dense_compl ℝ` (finite ⇒ countable ⇒ complement dense ⇒ meets the open ball);
   set `b₁ := e₁.symm b₁' ∉ S`, and connecting arc `σ : Path m b₁ := (segment in B').map' e₁.symm`
   — note `σ`'s range ⊆ `W₀ ∩ W₁` by construction (convexity of `B'` inside the image of the
   *intersection*; this sidesteps "chart overlaps need not be connected").
3. Decompose `⟦γ⟧ = ⟦head₀⟧ ≫ ⟦tail₀⟧` by step 0 at `c`; insert `σ`:
   `⟦γ⟧ = ⟦head₀.trans σ⟧ ≫ ⟦σ.symm.trans tail₀⟧` (groupoid cancellation in the quotient).
   `head := head₀.trans σ : Path a b₁` lies in `W₀` (piece-0 `maps` + σ ⊆ W₀), a single-chart
   path with endpoints off `S` ⇒ base case gives avoiding `head'`.
   `tail := σ.symm.trans tail₀ : Path b₁ b`: build its `ChartChain` of length `n` explicitly —
   `tail₀ = γ.truncate c 1` keeps γ's original clock (constant `= m` on `[0, c]`), so `tail`'s
   pieces are `[0, (1+t 2)/2] ⊆ W₁` (σ.symm then the constant stretch then `γ[[t 1, t 2]]`)
   and `[(1+t k)/2, (1+t (k+1))/2] ⊆ W_k` for `k ≥ 2` (breakpoint arithmetic via
   `Path.trans_apply` + the truncate formula; flagged risk R4). Induction hypothesis on `tail`
   gives avoiding `tail'`. Then `γ' := head'.trans tail'`; ranges union avoids `S`
   (`Path.trans_range`); homotopy classes compose. ∎

Helper worth exporting (used above; also generally useful):
```lean
theorem nonempty_open_diff_finite {U : Set X} (hU : IsOpen U) (hne : U.Nonempty)
    {S : Set X} (hS : S.Finite) : (U \ S).Nonempty
  -- through a chart: open nonempty ⊆ ℂ minus countable is nonempty via Set.Countable.dense_compl.
```

---

## 8. Requests to other units

Filed in `docs/requests/holomorphic-forms.md` (created by this design):
1. **Transition-analyticity helper** (needed by `rechart`): export
   `AnalyticOnNhd ℂ (↑e' ∘ ↑e.symm) (e '' (e.source ∩ e'.source))` for
   `e, e' ∈ maximalAtlas 𝓘(ℂ) ω X` (they derive exactly this inside
   `analyticOnNhd_coeffIn`/`coeffIn_trans`; local-multiplicity independently offers
   `analyticAt_transition`). Non-blocking: 15-line `Compat` fallback via
   `StructureGroupoid.compatible_of_mem_maximalAtlas` + `contDiffOn_omega_iff_analyticOn`.
2. Confirmation that `coeffIn_trans` lands with the orientation
   `coeffIn e' η z = deriv (↑e ∘ ↑e'.symm) z * coeffIn e η (e (e'.symm z))` (this design's
   `rechart` and linearity proofs are keyed to it), and that
   `Form1.analyticOnNhd_coeffIn`, `coeffIn_add/smul`, `coeffIn_mdifferential`,
   `contMDiffAt_iff_analyticAt_comp` are exported as per their design doc §2.

No requests to surfaces-and-charts: this unit deliberately avoids `Jacobian.Surface` imports
(the `chartAt`-chart trick in §4 removes the only candidate dependency), matching the
blueprint edge "paths-and-integrals builds on holomorphic-forms".

---

## 9. Verified mathlib names (all grepped/spiked at pin `5483982…`)

| Fact | Name / location |
|---|---|
| Disk primitive (Morera) | `DifferentiableOn.isExactOn_ball`, `Complex.IsExactOn`, `Complex.IsExactOn.with_val_at` — `Analysis/Complex/HasPrimitives.lean:290/:115/:118` (spiked) |
| Analytic ⇒ differentiable | `AnalyticOnNhd.differentiableOn` — `Analysis/Calculus/FDeriv/Analytic.lean:176` |
| Zero-derivative ⇒ constant on convex | `Convex.is_const_of_fderivWithin_eq_zero` — `MeanValue.lean:558` (spiked); helpers `fderivWithin_of_isOpen`, `HasFDerivAt.fderiv` |
| 1D Lebesgue subdivision | `exists_monotone_Icc_subset_open_cover_unitInterval` — `Topology/UnitInterval.lean:481` |
| 2D grid subdivision | `exists_monotone_Icc_subset_open_cover_unitInterval_prod_self` — `:487` (spiked) |
| Path core | `Path`, `refl/symm/trans/cast/reparam/truncate/map'/extend` — `Topology/Path.lean` (`extend_symm_apply :250` for all real `t`; `extend_trans_of_le_half :309`, `_of_half_le :315`; `trans_range :328`; `truncate :544`) |
| Homotopy | `Path.Homotopy` (= `HomotopyRel … {0,1}`), `.eval/source/target`, `Homotopy.reparam :189`, `Homotopic`, `.hcomp :274`, `Homotopic.Quotient` — `Topology/Homotopy/Path.lean`; `HomotopyRel.eq_fst/eq_snd` — `Homotopy/Basic.lean` |
| Groupoid-law homotopies | `Path.Homotopy.reflTransSymm/reflSymmTrans/transRefl/reflTrans/transAssoc`, `Path.Homotopic.trans_symm/symm_trans` — `AlgebraicTopology/FundamentalGroupoid/Basic.lean:62-217` (spiked) |
| ℂ-minus-countable path-conn | `Set.Countable.isPathConnected_compl_of_one_lt_rank` — `Analysis/Normed/Module/Connected.lean:44` + `rank_real_complex` — `LinearAlgebra/Complex/FiniteDimensional.lean:35` (spiked); proof-adaptation ingredients `segment_inter_eq_endpoint_of_linearIndependent_of_ne` (`Convex/Segment.lean:320`, public), `exists_linearIndependent_pair_of_one_lt_rank` (`Dimension/RankNullity.lean:143`), `countable_setOf_nonempty_of_disjoint` (`Data/Set/Countable.lean:310`), `Set.Countable.dense_compl` (`Topology/Algebra/Module/Cardinality.lean:131`) |
| Locally-constant machinery | `IsLocallyConstant.iff_eventually_eq :77`, `.apply_eq_of_isPreconnected :128`, `.apply_eq_of_preconnectedSpace :137` — `Topology/LocallyConstant/Basic.lean`; `Subtype.preconnectedSpace` — `Connected/Basic.lean:726`; `IsPreconnected.prod :426` |
| Filter plumbing | `nhdsWithin_union` — `Topology/NhdsWithin.lean:206`; `Icc_union_Icc_eq_Icc` — `Order/Interval/Set/LinearOrder.lean`; `continuous_projIcc` — `Topology/Order/ProjIcc.lean:33` |
| FTC / chain rule | `intervalIntegral.integral_eq_sub_of_hasDeriv_right` — `FundThmCalculus.lean:1129`; `HasDerivAt.comp_hasDerivWithinAt` — `Deriv/Comp.lean:281` (both spiked) |
| Chart transport | `ContinuousOn.comp_continuous` — `Topology/ContinuousOn.lean:523`; charts are `OpenPartialHomeomorph` (open source/target) |
| NOT in mathlib (we build) | homotopy-invariant line integrals on manifolds (inventory §17), any `Path`-`truncate`-vs-`trans` homotopy lemma, convex-minus-countable path-connectivity, ball-relative homotopy of paths |

---

## 10. Risks & fallbacks

- **R1 (glue-lemma filter bookkeeping).** The `𝓝[s]`-eventual manipulation in
  `glue`/`rechart` is the concentrated technical debt (~150 lines). Mitigation: `nhdsWithin`
  API is mature (`nhdsWithin_union`, `mem_nhdsWithin`, `eventually_nhdsWithin_iff`); the spike
  proved the planar cores so only filter transport remains. Fallback: specialize `glue` to the
  two concrete shapes used (adjacent real intervals; product strips) instead of the abstract
  `hcov` form.
- **R2 (holomorphic-forms slippage).** We consume `coeffIn`, `coeffIn_trans` (orientation
  pinned in §8), `analyticOnNhd_coeffIn`, `coeffIn_add/smul`, `coeffIn_mdifferential`,
  `contMDiffAt_iff_analyticAt_comp`. If their landed forms drift, only
  `LocalPrimitive.lean`/`Bridge.lean` proofs adjust; the export surface here is stable.
  Transition-analyticity has a local `Compat` fallback (§8).
- **R3 (square-grid induction size).** The double induction is mechanical but long. Mitigation:
  strips reuse the 1D induction *shape*; all gluing is the same lemma. Fallback if the product
  `hcov` helpers get ugly: do the whole square induction with `s`-sets in `ℝ²` only (already
  the plan) and prove the three needed `hcov` instances as bare `Icc`-arithmetic lemmas.
- **R4 (Perturb truncate/trans arithmetic).** `homotopic_truncate_trans` (step 0) and the
  tail-chain reindexing (step 3) involve explicit piecewise-parameter computation with
  `Path.trans_apply` case splits. Sized at ~120 lines combined; fallback: replace the
  `ChartChain`-length induction by induction on `n` with the subdivision *carried as
  hypothesis* on the ORIGINAL γ (avoid rebuilding chains for `tail` by consuming the original
  chain's later pieces re-clocked — the truncate-keeps-the-clock trick in §7 exists precisely
  to make that reindexing affine). Worst case this theorem slips without blocking anything
  else in this unit (only Abel, much later, consumes it).
- **R5 (junk off-target).** `coeffIn` is junk off `e.target`; every ball in this design is
  kept `⊆ e.target` by construction (`ChartChain.ball_subset`, `exists_hasDerivAt_ball`
  hypotheses). Invariant: never state `HasDerivAt g (coeffIn e η z) z` except under
  `z ∈ ball ⊆ e.target`.
- **R6 (degenerate subdivisions).** `t k = t (k+1)` cells/pieces: all constructions handle
  singletons (`Icc c c = {c}`, glue with `L = s₂`); no positivity side conditions anywhere.

## 11. Downstream consumption map

- **jacobian-construction (CC9):** `pathIntegral`, `pathIntegralₗ`, `pathIntegral_trans/symm`,
  `period`, `periodVector` (+ its `trans/symm/refl` lemmas), `period_conj`,
  `pathIntegral_congr_homotopic`. Recipe for `periodSubgroup` in §6.
- **monodromy (unit 21):** `IsPrimitiveAlongMap` + `rechart`/`sub_eq_sub`/`glue`/`comp`,
  `ChartChain`, `exists_primitive_along_square`, `pathIntegral_mdifferential`,
  `pathIntegral_eq_of_simplyConnected`. (The monodromy theorem itself — global primitives on
  simply-connected surfaces — is NOT here.)
- **sphere-topology:** `period_eq_zero_of_homotopic_refl`, `pathIntegral_eq_of_simplyConnected`,
  `pathIntegral_mdifferential`.
- **abel-weak-solutions / abel:** `Loop.exists_homotopic_avoiding`, `exists_homotopic_avoiding`,
  `ChartChain`, `pathIntegral_eq_intervalIntegral` (bridge), `Planar.lean` atoms.
- **projective-line:** `pathIntegral` API generically (genus-0 facts); nothing bespoke.
- **residue-calculus / planar-stokes-atoms:** `Jacobian.Path.Planar` (disk primitives — do not
  re-prove; also `Mathlib.Analysis.Complex.HasPrimitives` directly); they own
  `circleIntegral`-shaped specializations of the bridge.
- **dbar-solvability:** `Planar.lean`'s `exists_hasDerivAt_ball` (holomorphic-primitive atom);
  its ∂̄-specific machinery is its own.

## 12. What this unit does NOT do

Monodromy theorem / global primitives on simply-connected surfaces (unit 21); Abel machinery;
residues and any `circleIntegral` computation; integration of 2-forms / Stokes (planar-stokes);
smooth or piecewise-C¹ path *classes* (C¹ enters only as a hypothesis of the bridge lemma);
the period subgroup/lattice as a def (CC9, jacobian-construction); `π₁` group structure beyond
`Path.Homotopic.Quotient` descent.
