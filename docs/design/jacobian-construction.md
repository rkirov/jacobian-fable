# Design: jacobian-construction (`Jacobian/JacobianConstruction/`)

Owner unit of **CC9** (frozen in `docs/design/core-choices.md`). Blueprint entry:
`clean_room_blueprint.md` §jacobian-construction. Builds the `Jacobian X` TYPE and its
group/topology/manifold **scaffolding**; the *full-rank* facts (discreteness and rank `2g` of the
period lattice) are period-lattice-rank's theorem, much later. References: Forster §20–21
(page map `docs/refs/forster-map.md`); G–H Ch. 2 for the picture only (not for the route — see
blueprint routing warning: no Hodge theory).

**Verdict up front** (details below): the T2 route is **CONFIRMED** —
`Jacobian X := V ⧸ (periodSubgroup).topologicalClosure` gives `T2Space` for **every** genus,
including `g = 0`, with no discreteness input at all. `CompactSpace`/`ChartedSpace`/`IsManifold`/
`LieAddGroup` are built once, generically, over an **abstract torus layer**
`Torus (V) (L : AddSubgroup V)`, and instantiated at `L := (periodSubgroup).topologicalClosure`
only once period-lattice-rank supplies `[DiscreteTopology L]` (and, for compactness,
`[IsZLattice ℝ L.toIntSubmodule]`). A genuinely new finding, not addressed by any other unit's
design doc: the challenge's `def Jacobian (X : Type u) [...] : Type u := sorry` is
**universe-polymorphic in `X`**, but every natural construction (`Fin g → ℂ` quotients) lives in
`Type 0`; this forces a `ULift` shell around the whole construction (§7). The spike
(`scratch_jac.lean`, 4 examples, compiles clean) exercises the T2 closure trick, the `→ₜ+`
substrate, and the `ZLattice` compactness trick.

---

## 0. Standing setup

```lean
open scoped ContDiff Manifold Pointwise
open Set Filter Topology

namespace RS
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
```

Consumed from upstream (design docs are the interface contract; see `docs/mathlib-inventory.md`
§7–8 for the mathlib side):

- **holomorphic-forms**: `RS.Form1 X` (`AddCommGroup`, `Module ℂ`), `genus X := Module.finrank ℂ
  (Form1 X)`, `FiniteDimensional ℂ (Form1 X)` (compact `X`), `coeffIn`, `Form1.analyticOnNhd_coeffIn`.
- **paths-and-integrals**: `Path x y` (mathlib), `pathIntegral`, `pathIntegral_trans/symm/refl`,
  `pathIntegral_add/smul`, `period`, `periodVector {n} (b : Basis (Fin n) ℂ (Form1 X)) (γ : Path
  x x) : Fin n → ℂ`, `periodVector_trans/symm/refl`, `IsPrimitiveAlongMap` + `rechart` +
  `pathIntegral_eq_intervalIntegral` (chart-local formula, consumed by `ofCurve_contMDiff`).
- **surfaces-and-charts**: `contMDiffAt_iff_analyticAt_of_mem_source`,
  `contMDiffOn_iff_analyticOnNhd_of_subset_source` (Bridges); `chartedSpaceOfFamily`,
  `isManifold_of_family` (ChartedSpaceKit — **hardcoded to codomain `ℂ`**, see §4.2 for why we
  need a generalized local copy).
- **mathlib**: `QuotientAddGroup` (topology, `T2`/`T3`, group/ring instances),
  `Subgroup.topologicalClosure`/`AddSubgroup.topologicalClosure`, `ZLattice`/`ZSpan`
  (`docs/mathlib-inventory.md` §7), `ContinuousAddMonoidHom` (`→ₜ+`), `ULift` algebra/topology
  transport instances (all free), `LieAddGroup`/`ContMDiffAdd` (`docs/mathlib-inventory.md` §8).

**mapping-degree dependency (blueprint edge) — not actually consumed.** The blueprint lists
`mapping-degree` as a dependency of this unit; nothing in the design below needs its API
(`fiberMultSum`, `FiberStack`, covering-map machinery). `ofCurve_contMDiff` is proved from paths'
chart-local primitive formula alone (§8), and path-connectedness of `X` (needed for `ofCurve` to
be total) comes from `ChartedSpace.locPathConnectedSpace` + `ConnectedSpace X`, not from any
degree/covering argument. Flagging this as a blueprint-DAG inaccuracy for the orchestrator; not
blocking (an unused "builds on" edge costs nothing).

---

## 1. File plan

```
Jacobian/JacobianConstruction/ChartedSpaceKitV.lean  -- generalized chartedSpaceOfFamily/isManifold_of_family
                                                      --   over an arbitrary NormedSpace ℂ codomain
                                                      --   (Compat copy of Surface's kit; request filed)
Jacobian/JacobianConstruction/Torus.lean              -- THE abstract layer: V ⧸ L for L : AddSubgroup V
                                                      --   free instances (§3), ChartedSpace/IsManifold
                                                      --   (§4, needs [DiscreteTopology L]), LieAddGroup
                                                      --   (§5, same hyp), CompactSpace (§6, needs IsZLattice),
                                                      --   inducedHom / →ₜ+ substrate (§9)
Jacobian/JacobianConstruction/Periods.lean            -- basis, periodVector, periodSubgroup Λ
Jacobian/JacobianConstruction/ULift.lean              -- generic "transport ChartedSpace/IsManifold/
                                                      --   LieAddGroup along a homeomorphism/ContinuousAddEquiv"
                                                      --   toolkit (§7), + its ULift instantiation
Jacobian/JacobianConstruction/Basic.lean              -- Jac₀ X := V ⧸ Λ.topologicalClosure (Type 0);
                                                      --   Jacobian X := ULift.{u} (Jac₀ X) (Type u);
                                                      --   ALL challenge instances assembled; LEDGER
Jacobian/JacobianConstruction/OfCurve.lean            -- ofCurve, well-definedness, ofCurve_self,
                                                      --   ofCurve_contMDiff (§8)
Jacobian/JacobianConstruction/Functorial.lean         -- pushforward/pullback SUBSTRATE only (§9),
                                                      --   wrapped through the ULift shell
Jacobian/JacobianConstruction.lean                    -- unit root, API docstring
```

Dependency order: `ChartedSpaceKitV` and `Torus` are foundation (no `X`); `Periods` depends on
holomorphic-forms + paths-and-integrals only (no `Torus`); `ULift` depends on `Torus`; `Basic`
depends on `Periods` + `Torus` + `ULift`; `OfCurve` and `Functorial` depend on `Basic`.

---

## 2. The ULift sharp point (universe polymorphism)

The challenge (`docs/Jacobian_challenge.lean:58-62`):

```lean
universe u in
def Jacobian (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Type u := sorry
```

`u` is a **bound universe parameter** of the definition — the body must have type `Type u` for
*every* instantiation of `u`, not just `u := 0`. But `Fin (genus X) → ℂ` and any quotient of it
live in `Type 0` (`ℂ`, `Fin n` are `Type 0` regardless of `X`'s universe). Writing
`def Jacobian (X : Type u) [...] : Type u := (Fin (genus X) → ℂ) ⧸ L` **does not typecheck** for
generic `u` — this is not a corner case, it fails outright. No other unit's design doc addresses
this (checked: no `ULift`/`universe` discussion anywhere in `docs/` or `Jacobian/`). Resolution:

```lean
/-- The Type-0 core: the torus itself, before the universe shell. -/
def Jac₀ (X : Type*) [...] : Type := (Fin (genus X) → ℂ) ⧸ (periodSubgroup X).topologicalClosure

/-- The challenge's `Jacobian`, universe-matched to `X` via `ULift`. -/
def Jacobian (X : Type u) [...] : Type u := ULift.{u} (Jac₀ X)
```

All the interesting mathematics (§3–§9) is developed entirely on `Jac₀ X` (`Type 0`, no universe
friction, matches the ambient `ZLattice`/`QuotientAddGroup` literature exactly). §7 builds a
one-time, reusable "transport `ChartedSpace`/`IsManifold`/`LieAddGroup` along a homeomorphism"
toolkit and instantiates it at `Homeomorph.ulift : ULift Jac₀ X ≃ₜ Jac₀ X` to move every instance
across the shell. `AddCommGroup`/`TopologicalSpace`/`T2Space`/`CompactSpace` transport across
`ULift` **for free** (mathlib has generic instances for all of these on `ULift`, verified below);
only the *manifold-specific* classes need the custom transport, because mathlib has no
`ChartedSpace`/`IsManifold` transport-along-equiv lemma at all (checked: `grep -rn ULift
Mathlib/Geometry/Manifold/` hits only `Bordism.lean`, unrelated).

Verified free `ULift` instances (source-read, pinned commit):
`ULift.topologicalSpace` (`Topology/Constructions.lean:69`), `ULift.instT2Space`
(`Topology/Separation/Hausdorff.lean:377`), `ULift.compactSpace`
(`Topology/Compactness/Compact.lean:1060`), `ULift.commGroup`/`AddCommGroup`
(`Algebra/Group/ULift.lean:108`, `@[to_additive]`), `instance : IsTopologicalGroup (ULift G)`
(`Topology/Algebra/Group/Basic.lean:461`, additive counterpart from `to_additive`),
`Homeomorph.ulift : ULift X ≃ₜ X`, `AddEquiv.ulift : ULift R ≃+ R`
(`Algebra/Group/ULift.lean:74`, `@[to_additive]`), and — most useful of all —
`ContinuousLinearEquiv.ulift : ULift M₁ ≃L[R₁] M₁` (`Topology/Algebra/Module/Equiv.lean:694`,
built from `continuous_uliftDown`/`continuous_uliftUp`,
`Topology/Constructions.lean:1325`/`:1329`). We do **not** need the linear-equiv version (we only
`ULift` the *finished quotient*, not the ambient `V`), but its existence is reassuring evidence
this is exactly the idiom mathlib expects here.

**Risk.** This is genuinely new custom work (~100–150 lines: `ChartedSpace.transport`,
`IsManifold.transport`, `LieAddGroup`-level transport, each instantiated at `Homeomorph.ulift`/
`ContinuousAddEquiv.ulift`). Low *mathematical* risk (conjugating an atlas by a fixed
homeomorphism reuses the exact same transition-map analyticity proof, since `f.symm.trans f =
refl` collapses the "new" transitions to the old ones — see §7). Medium *engineering* risk (first
time this pattern is built in the project). Fallback: if the generic transport lemma proves
fiddly, specialize it to exactly the one homeomorphism we need (`Homeomorph.ulift`) rather than
an abstract `M' ≃ₜ M`; the mathematical content is identical either way.

---

## 3. The T2 crux — CONFIRMED, spiked

**Route** (matches the task's RECOMMENDED route, confirmed workable): define

```lean
def Jac₀ (X) [...] : Type := (Fin (genus X) → ℂ) ⧸ (periodSubgroup X).topologicalClosure
```

`AddSubgroup.topologicalClosure` (`Topology/Algebra/Group/Basic.lean:673`, `to_additive` of
`Subgroup.topologicalClosure`) is an actual `AddSubgroup` (not just a `Set`), with
`isClosed_topologicalClosure : IsClosed (↑L.topologicalClosure)` and
`le_topologicalClosure : L ≤ L.topologicalClosure` (so periods ⊆ closure, needed for `ofCurve`
well-definedness, §8). Then, **for every genus, including `g = 0`**:

- `AddCommGroup (Jac₀ X)`: `QuotientAddGroup`'s generic instance for an abelian ambient group
  (`Quotient.commGroup`/additive, `GroupTheory/QuotientGroup/Defs.lean:151`) — no `Normal`
  hypothesis needed to *supply*, since `V := Fin g → ℂ` is abelian and
  `Subgroup.normal_of_isMulCommutative` (`Algebra/Group/Subgroup/Defs.lean:631`, priority 100,
  `to_additive`) makes every subgroup normal automatically by instance search.
- `TopologicalSpace (Jac₀ X)`: `QuotientAddGroup.instTopologicalSpace`.
- `T2Space (Jac₀ X)`: via the **T3 chain** `QuotientAddGroup.instT3Space [N.Normal] [IsClosed N] :
  T3Space (G⧸N)` (`Topology/Algebra/Group/Quotient.lean`, needs `[IsTopologicalGroup G]`, true for
  any normed space) → `T3Space.t25Space` → `T25Space.t2Space`
  (`Topology/Separation/Regular.lean:416`/`:371`). **One catch, found by the spike**: `IsClosed
  (L.topologicalClosure : Set V)` is a **theorem**
  (`Subgroup.isClosed_topologicalClosure`), not registered as an instance, so plain
  `infer_instance` for `T2Space (V ⧸ L.topologicalClosure)` **fails** until you add one `haveI`
  line:
  ```lean
  haveI : IsClosed (L.topologicalClosure : Set V) := L.isClosed_topologicalClosure
  ```
  after which `infer_instance` closes `T2Space` (spiked, `scratch_jac.lean` items 1–2).

This settles the crux exactly as hoped: **no discreteness, no full rank, no input from
period-lattice-rank at all** is needed for `AddCommGroup`/`TopologicalSpace`/`T2Space`. They are
available from the moment `periodSubgroup` exists (§Periods below), for every `X` including
`genus X = 0` (where `Fin 0 → ℂ` is the zero module, `periodSubgroup` is the trivial subgroup,
closure of `{0}` is `{0}`, and `Jac₀ X` is a one-point space — trivially `T2`).

**`ofCurve` well-definedness is unaffected**, per the task's check: periods live in
`periodSubgroup X ≤ (periodSubgroup X).topologicalClosure`
(`AddSubgroup.le_topologicalClosure`), so the path-choice-difference argument (§8) goes through
unchanged whether we quotient by `Λ` or by `closure Λ` — we only ever need "the difference lies in
*some* subgroup containing the periods," and closure trivially contains them.

---

## 4. Abstract torus layer — `ChartedSpace`/`IsManifold` (`Torus.lean`, §1 of it)

Fix `V : Type` (always instantiated at `Fin n → ℂ`), `[NormedAddCommGroup V] [NormedSpace ℂ V]
[FiniteDimensional ℂ V]`, `L : AddSubgroup V`, `[DiscreteTopology L]`.

### 4.1 Uniform injectivity radius

```lean
theorem exists_uniform_injRadius (L : AddSubgroup V) [DiscreteTopology L] :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ℓ ∈ L, ℓ ≠ 0 → 2 * ρ ≤ ‖ℓ‖
```

*Proof.* `DiscreteTopology L` gives `IsOpen ({0} : Set L)` via
`discreteTopology_iff_isOpen_singleton_zero`
(additive of `Topology/Algebra/Group/Basic.lean:139`); unfold subspace topology to get `U` open in
`V` with `U ∩ (L : Set V) = {0}`; shrink to a ball `ball 0 r ⊆ U`; conclude `ball 0 r ∩ (L:Set V) =
{0}`, i.e. every nonzero `ℓ ∈ L` has `‖ℓ‖ ≥ r`; set `ρ := r/2`. ~15 lines.

```lean
theorem mk_injOn_ball (L : AddSubgroup V) [DiscreteTopology L] {x : V} :
    Set.InjOn (QuotientAddGroup.mk (s := L)) (Metric.ball x ρ)
```

*Proof.* If `z₁ z₂ ∈ ball x ρ` and `mk z₁ = mk z₂` (i.e. `z₁ - z₂ ∈ L`,
`QuotientAddGroup.eq_iff_sub_mem`), then `‖z₁ - z₂‖ ≤ ‖z₁-x‖+‖x-z₂‖ < 2ρ`; by §4.1's
contrapositive, `z₁ - z₂ = 0`. ~8 lines.

### 4.2 The chart family (centered charts)

**Design choice, load-bearing everywhere downstream (§5, §8, §9): charts are CENTERED at a
representative**, not merely "some local section of `mk`." For `x : V`:

```lean
/-- The chart at representative `x`: `mk(x + w) ↦ w`, for `w` in the uniform injectivity ball. -/
noncomputable def centeredChart (L : AddSubgroup V) [DiscreteTopology L] (x : V) :
    OpenPartialHomeomorph (V ⧸ L) V where
  toFun q := (mk_injOn_ball L (x := x)).... -- the unique w ∈ ball 0 ρ with mk (x+w) = q, junk 0 else
  invFun w := QuotientAddGroup.mk (x + w)
  source := QuotientAddGroup.mk '' Metric.ball x ρ
  target := Metric.ball 0 ρ
  ...
```

Built as: `invFun w := mk (x+w)` is a continuous injection `ball 0 ρ → V⧸L` (injective by §4.1
translated: `mk(x+w₁)=mk(x+w₂) → w₁-w₂ ∈ L`, `‖w₁-w₂‖<2ρ ⟹ w₁=w₂`); it is an open map onto its
image (composition of the translation `w ↦ x+w`, a homeomorphism of `V`, with the globally open
map `mk` — `QuotientAddGroup.isOpenMap_coe`, `Topology/Algebra/Group/Quotient.lean`); hence
(injective + continuous + open onto image) it is an open embedding, and
`toFun := invFun`'s inverse on the image is exactly `centeredChart`. (Standard "injective +
continuous + open map ⇒ open embedding onto image" fact; if no one-line mathlib lemma matches
exactly, ~15 lines by hand: continuity of the inverse from openness of `invFun`, membership from
`OpenPartialHomeomorph.mk` fields.)

```lean
noncomputable def chartAt' (L : AddSubgroup V) [DiscreteTopology L] (q : V ⧸ L) :
    OpenPartialHomeomorph (V ⧸ L) V :=
  centeredChart L (Function.surjInv QuotientAddGroup.mk_surjective q)

instance chartedSpace (L : AddSubgroup V) [DiscreteTopology L] : ChartedSpace V (V ⧸ L) :=
  chartedSpaceOfFamily' (centeredChart L) (fun q => Function.surjInv mk_surjective q)
    (fun q => ⟨0, Metric.mem_ball_self hρ, by simp [centeredChart, Function.surjInv_eq]⟩)
```

using `chartedSpaceOfFamily'` — the **generalized** copy of Surface's kit (§4.2.1). Membership
`q ∈ (chartAt' q).source`: with `x := surjInv mk_surjective q`, `mk x = q`
(`Function.surjInv_eq`), and `x = x + 0 ∈ ball x ρ` trivially, so `q = mk(x+0) ∈ mk '' ball x ρ =
source`. **No continuity of the section is needed** — this is exactly why
`chartedSpaceOfFamily`'s signature (`∀ z, z ∈ (c (idx z)).source`, no continuity hypothesis on
`idx`) is the right tool; a `Classical.choice`-level section suffices.

#### 4.2.1 `ChartedSpaceKitV.lean` — the generalization request

Surface's `Jacobian/Surface/ChartedSpaceKit.lean` hardcodes the chart codomain to literal `ℂ`:
`chartedSpaceOfFamily (c : ι → OpenPartialHomeomorph Z ℂ) ...`. Nothing in its ~65-line proof is
`ℂ`-specific except the scalar field of `AnalyticOnNhd`; we need codomain `V := Fin n → ℂ`. We add
a **local, textually-identical generalization** (`{E : Type*} [NormedAddCommGroup E] [NormedSpace
ℂ E]` in place of the hardcoded `ℂ`) in `ChartedSpaceKitV.lean`, and file a non-blocking request in
`docs/requests/surfaces-and-charts.md` to generalize their file instead (whichever lands, the two
are `rfl`-compatible since the proofs are identical).

### 4.3 `IsManifold` — transitions are translations

```lean
theorem isManifold_torus (L : AddSubgroup V) [DiscreteTopology L] :
    @IsManifold ℂ _ V _ _ V _ 𝓘(ℂ, V) ω (V ⧸ L) _ (chartedSpace L)
```

*Proof plan.* Apply the generalized `isManifold_of_family'`: need, for all `x x' : V`,
`AnalyticOnNhd ℂ ((centeredChart L x).symm ≫ₕ centeredChart L x') (...)`. Key local computation:
for `w` in the overlap (i.e. `mk(x+w) ∈ source of chart at x'`), there is (by §4.1's uniqueness)
a **unique** `ℓ ∈ L` with `x + w - x' - ℓ ∈ ball 0 ρ`, and the transition value there is
`τ(w) = x + w - x' - ℓ`. As `w` ranges over a small enough neighborhood, `ℓ` is
**locally constant** (it is pinned down by which "sheet" `w` lands in, and jumps only where
`x+w-x'` crosses a lattice coset boundary at distance `≥ 2ρ` away — i.e. never, locally). Hence
`τ` agrees, near any point of the overlap, with the **entire** map `w ↦ w + (x - x' - ℓ)` for a
fixed constant `ℓ` — `AnalyticAt` by `analyticAt_id.add analyticAt_const`; conclude `AnalyticOnNhd`
pointwise. ~40 lines (the "ℓ is locally constant" step is the same shape as
holomorphic-forms'/paths-and-integrals' recurring "eventual agreement on an open set" arguments —
no new proof technique, just bookkeeping).

**This is the payoff of centered charts**: the transition is *literally* `identity + constant`,
not merely "an analytic function" — trivial to certify, and reused verbatim by §5 (`LieAddGroup`)
and §8 (`ofCurve_contMDiff`).

---

## 5. `LieAddGroup` — addition/negation are identity in charts

```lean
instance lieAddGroup (L : AddSubgroup V) [DiscreteTopology L] :
    @LieAddGroup ℂ _ V _ _ V _ 𝓘(ℂ, V) ω (V ⧸ L) _ (chartedSpace L) _ (isManifold_torus L) := ...
```

Needs `ContMDiffAdd` (`contMDiff_add : ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,V)) 𝓘(ℂ,V) ω (fun p => p.1+p.2)`)
and `contMDiff_neg`. Both proved via `contMDiff_iff_contMDiffAt` + the **identical computation** as
§4.3's transitions:

- **Addition**, at `(q₁,q₂)` with representatives `x := surjInv mk_surjective q₁`, `y := surjInv
  mk_surjective q₂`: in the charts `centeredChart L x`, `centeredChart L y` (domain), `centeredChart
  L (x+y)` (codomain, representative `x+y` for the sum point), the composite is, for `(a,b)` near
  `(0,0)`: `writtenInExtChartAt(...)((a,b)) = centeredChart L (x+y) (mk(x+a) + mk(y+b)) =
  centeredChart L (x+y) (mk((x+y)+(a+b))) = a+b` (valid once `‖a+b‖ < ρ`, true near `(0,0)`).
  So the chart composite **equals** `fun (a,b) => a+b` near the point — entire
  (`contDiff_fst.add contDiff_snd` / `AnalyticAt.add`), hence `ContMDiffAt`.
- **Negation**, at `q` with representative `x`, in charts `centeredChart L x` (domain),
  `centeredChart L (-x)` (codomain): composite is `a ↦ centeredChart L (-x) (mk(-(x+a))) =
  centeredChart L (-x) (mk((-x)+(-a))) = -a` near `0` — entire.

~60 lines total (mostly `ContMDiffAt.congr_of_eventuallyEq` bookkeeping to go from "the composite
equals an entire map near the point" to `ContMDiffAt`, the same move used throughout
holomorphic-forms/paths-and-integrals). No new mathematics beyond §4.3.

---

## 6. `CompactSpace` — the `ZLattice` periodicity trick (spiked)

Needs the FULL hypothesis: `L : Submodule ℤ V` (via `AddSubgroup.toIntSubmodule : AddSubgroup V ≃o
Submodule ℤ V`, `Algebra/Module/Submodule/Lattice.lean:415`), `[DiscreteTopology L]`,
`[IsZLattice ℝ L]` (needs `[NormedSpace ℝ V]` too — automatic on `Fin n → ℂ` via `ℂ`'s standard
real-normed-space structure and `Pi`).

```lean
instance compactSpace {L : Submodule ℤ V} [DiscreteTopology L] [IsZLattice ℝ L] :
    CompactSpace (V ⧸ L.toAddSubgroup)
```

*Proof (spiked, `scratch_jac.lean` item 4).* Apply
`IsZLattice.isCompact_range_of_periodic L (mk : V → V⧸L.toAddSubgroup) continuous_mk hper`
(`Algebra/Module/ZLattice/Basic.lean:791` — "if `f` is periodic w.r.t. a ℤ-lattice, `range f` is
compact," proved via `(Free.chooseBasis).ofZLatticeBasis.parallelepiped.isCompact.image`; we do
**not** need to hand-roll the fundamental-domain-closure argument the mathlib-inventory flags as
absent — this lemma already packages it). Periodicity `hper : ∀ z w, w ∈ L.toAddSubgroup → mk (z +
w) = mk z` is `QuotientAddGroup.eq_iff_sub_mem` (`(z+w)-z = w ∈ L.toAddSubgroup` by
`add_sub_cancel_left`/`neg_mem`). Since `mk` is surjective (`QuotientAddGroup.mk_surjective`),
`range mk = univ`, so `IsCompact (univ : Set (V⧸L.toAddSubgroup))`, i.e. `CompactSpace` via
`isCompact_univ_iff`. **All four lemma names verified present at the pin and the whole argument
compiles** (spike item 4, ~10 lines).

This is considerably shorter than the "closure of a fundamental domain is compact, and `mk` maps
it onto the quotient" route the mathlib-inventory's own note suggested (`ZSpan.fundamentalDomain`
+ `ZSpan.exist_unique_vadd_mem_fundamentalDomain`) — `isCompact_range_of_periodic` already does
exactly that internally (via `parallelepiped`, not `fundamentalDomain`, but the same idea), so we
get it as a two-line citation instead of a from-scratch fundamental-domain argument. Recorded as
the **PRIMARY route**; the fundamental-domain route (`ZSpan.fundamentalDomain`,
`ZSpan.exist_unique_vadd_mem_fundamentalDomain`, `ZSpan.quotientEquiv`) is the documented fallback
if `isCompact_range_of_periodic`'s exact hypotheses (`FiniteDimensional ℝ E`, no `ProperSpace`
needed — check at build time) don't unify cleanly with our `V`.

---

## 7. `ULift` transport toolkit (`ULift.lean`)

Generic, reusable (candidate for upstreaming to Surface's ChartedSpaceKit or core mathlib — no
existing mathlib lemma does this, confirmed by grep):

```lean
/-- Transport a `ChartedSpace` structure backward along a homeomorphism. -/
def ChartedSpace.ofHomeomorph {M' M H} [TopologicalSpace M'] [TopologicalSpace M]
    [TopologicalSpace H] [ChartedSpace H M] (f : M' ≃ₜ M) : ChartedSpace H M' where
  atlas := (f.toOpenPartialHomeomorph.trans ·) '' atlas H M
  chartAt m' := f.toOpenPartialHomeomorph.trans (chartAt H (f m'))
  mem_chart_source m' := by simpa using mem_chart_source (f m')
  chart_mem_atlas m' := ⟨_, chart_mem_atlas (f m'), rfl⟩

theorem isManifold_ofHomeomorph {M' M H E 𝕜} [...] [ChartedSpace H M] [IsManifold I n M]
    (f : M' ≃ₜ M) :
    @IsManifold 𝕜 _ E _ _ H _ I n M' _ (ChartedSpace.ofHomeomorph f)
```

*Proof of the manifold transport.* Every chart of the new atlas is `f.toOpenPartialHomeomorph.trans
e` for `e ∈ atlas H M`. For two such, `(f.trans e).symm ≫ₕ (f.trans e') = e.symm ≫ₕ (f.symm.trans
f) ≫ₕ e' = e.symm ≫ₕ e'` (`f.symm.trans f = refl` from `Homeomorph.self_trans_symm`-style
identities — the SAME transition maps as the original atlas). So membership in `contDiffGroupoid
n I` transfers verbatim from `[IsManifold I n M]`. ~25 lines.

For `LieAddGroup`: when `f` is *also* an `AddEquiv` (true of `Homeomorph.ulift`/`AddEquiv.ulift`
sharing the same underlying `Equiv.ulift`), the group operations conjugate the same way: in the
transported charts, `(+)` on `M'` reads, via `f`, as exactly `(+)` on `M` (since `f` is additive),
so `ContMDiffAdd`/`contMDiff_neg` transfer by the identical congruence argument as §5. ~30 lines.

**Instantiation at `Homeomorph.ulift : ULift (Jac₀ X) ≃ₜ Jac₀ X`:**

```lean
instance : ChartedSpace (Fin (genus X) → ℂ) (ULift (Jac₀ X)) :=
  ChartedSpace.ofHomeomorph Homeomorph.ulift
instance : IsManifold 𝓘(ℂ, Fin (genus X) → ℂ) ω (ULift (Jac₀ X)) := isManifold_ofHomeomorph ...
instance : LieAddGroup 𝓘(ℂ, Fin (genus X) → ℂ) ω (ULift (Jac₀ X)) := ...
```

`AddCommGroup`/`TopologicalSpace`/`T2Space`/`CompactSpace (ULift (Jac₀ X))` need **no** custom
work (§2's free `ULift` instances apply directly, given the corresponding instance on `Jac₀ X`).

---

## 8. `ofCurve` (`OfCurve.lean`)

### 8.1 Path-connectedness of `X` (small gap, filled here)

Needed so "any path `P₀ → x`" exists. **No unit currently provides this** (checked: absent from
every design doc). Two-line derivation, filed as a request to surfaces-and-charts (§Requests) with
a local `Compat` copy here:

```lean
instance : LocPathConnectedSpace X := ChartedSpace.locPathConnectedSpace (H := ℂ)
  -- needs LocPathConnectedSpace ℂ, from LocallyConvexSpace.toLocPathConnectedSpace
  -- (`Topology/Algebra/Module/LocallyConvex.lean:103`), automatic for ℂ.
instance : PathConnectedSpace X := .of_locPathConnectedSpace
  -- `Topology/Connected/LocPathConnected.lean:102`, needs [ConnectedSpace X] (standing hyp).
```

`ChartedSpace.locPathConnectedSpace [LocPathConnectedSpace H] : LocPathConnectedSpace M`
(`Geometry/Manifold/ChartedSpace.lean:268`) is a **theorem**, not an instance — apply it explicitly.

### 8.2 Definition and well-definedness

```lean
noncomputable def basis (X) [...] : Basis (Fin (genus X)) ℂ (Form1 X) := Module.finBasis ℂ (Form1 X)
  -- Module.finBasis needs [Module.Finite ℂ (Form1 X)] (= FiniteDimensional, holomorphic-forms)
  -- and [Module.Free ℂ (Form1 X)] (automatic: `Module.Free.of_divisionRing`, every vector space
  -- over a field is free). `Fin (Module.finrank ℂ (Form1 X)) = Fin (genus X)` by defn of genus.

noncomputable def ofCurve (P₀ : X) (x : X) : Jacobian X :=
  ULift.up (QuotientAddGroup.mk (fun i => pathIntegral (PathConnectedSpace.joined P₀ x).somePath
    (basis X i)))

theorem ofCurve_eq_of_path (P₀ x : X) (σ : Path P₀ x) :
    ofCurve P₀ x = ULift.up (QuotientAddGroup.mk (fun i => pathIntegral σ (basis X i)))
```

*Proof of `ofCurve_eq_of_path`.* Let `σ₀ := (PathConnectedSpace.joined P₀ x).somePath`. The loop
`σ.trans σ₀.symm : Path P₀ P₀` has, for each `i`, `period (σ.trans σ₀.symm) (basis X i) =
pathIntegral σ (basis X i) - pathIntegral σ₀ (basis X i)` (`pathIntegral_trans` +
`pathIntegral_symm`). Its `periodVector` therefore equals the *difference* of the two candidate
vectors, and lies in `Set.range (periodVector (σ := ·))`, hence in `periodSubgroup X ≤
(periodSubgroup X).topologicalClosure` (`AddSubgroup.subset_closure`/`le_topologicalClosure`). So
the two vectors agree mod `(periodSubgroup X).topologicalClosure`
(`QuotientAddGroup.eq_iff_sub_mem`), i.e. their images under `mk` agree. **No homotopy invariance
needed** — only `trans`/`symm` algebra (matches paths-and-integrals §6's remark verbatim). ~15
lines.

```lean
@[simp] theorem ofCurve_self (P₀ : X) : ofCurve P₀ P₀ = 0 :=
  by rw [ofCurve_eq_of_path P₀ P₀ (Path.refl P₀)]; simp [pathIntegral_refl]
```

### 8.3 `ofCurve_contMDiff` — THIS UNIT owns it

**Decision** (per the task's prompt to decide): yes, jacobian-construction proves this, consuming
only paths-and-integrals' chart-local primitive machinery + holomorphic-forms' `coeffIn`
analyticity + this unit's own centered-chart construction (§4.2). No new unit needed.

*Proof plan.* Fix `x₀ : X`. `ContMDiffAt` is local, so work near `x₀`. Let `e := chartAt ℂ x₀`,
pick `r > 0` with `ball (e x₀) r ⊆ e.target`. By `Form1.analyticOnNhd_coeffIn`, `coeffIn e (basis X
i)` is analytic on `e.target ⊇ ball (e x₀) r`; by the spiked planar atom
(`exists_hasDerivAt_ball`, paths-and-integrals §2.3, re-exported), get for each `i` a **holomorphic
primitive** `g_i : ℂ → ℂ` on `ball (e x₀) r` with `g_i (e x₀) = 0` and `HasDerivAt g_i (coeffIn e
(basis X i) z) z` there — `g_i` is itself `AnalyticAt` (holomorphic primitives of holomorphic
functions are holomorphic; `HasDerivAt` at every point of an open set upgrades to
`DifferentiableOn` upgrades to `AnalyticOnNhd`). Build the straight-segment path `τ_z : Path x₀ z`
for `z` in the chart ball (planar segment `t ↦ e x₀ + t•(e z - e x₀)`, mapped back through
`e.symm`; this is the same "planar path pulled through a chart" device paths-and-integrals uses
internally for `ChartChain`'s base case — reuse, don't re-derive). Since the *entire* path `τ_z`
lies in the single chart+ball `(e, ball (e x₀) r)`, `IsPrimitiveAlongMap` with data `(e, g_i)`
witnesses a primitive along `τ_z` for `basis X i`, so (`IsPrimitiveAlong.pathIntegral_eq`)
`pathIntegral τ_z (basis X i) = g_i (e z) - g_i (e x₀) = g_i (e z)`.

Let `v₀ := fun i => pathIntegral σ₀ (basis X i)` for a *fixed* chosen path `σ₀ : P₀ → x₀`. By
`ofCurve_eq_of_path` applied to `σ₀.trans τ_z` (a path `P₀ → z`) and `pathIntegral_trans`:
`ofCurve P₀ z = ULift.up (mk (v₀ + fun i => g_i (e z)))` for all `z` in the chart ball. Now use the
**same representative-point bookkeeping as §4.3/§5**: `v₀` is a fixed vector in `V := Fin (genus X)
→ ℂ`; the Jacobian's own chart at `ULift.up (mk v₀)` (representative `v₀`, via `centeredChart
(periodSubgroup X).topologicalClosure v₀`, transported through `ULift`) reads
`centeredChart(...) (mk (v₀ + w)) = w` for `w` near `0`. So, writing the composite
`writtenInExtChartAt` of `ofCurve P₀` at `x₀` in charts `(e, jacChart)`: for `z` near `x₀` (so `e z`
near `e x₀` and `g(e z) := (g_1(e z),...,g_g(e z))` near `g(e x₀) = 0`),
`jacChart (ofCurve P₀ z) = jacChart (mk (v₀ + g(e z))) = g (e z)`. This is **exactly** the analytic
map `z ↦ (g_1(e z),...,g_g(e z))` composed with the *already-analytic* `g_i`'s — i.e. the
`extChartAt`-composite is literally `g ∘ id` (no further composition with `e` needed on the
inside, since we phrased it in terms of `e z` directly) — `AnalyticAt` by
`AnalyticAt.prod`/componentwise. Conclude `ContMDiffAt` via `contMDiffAt_iff_analyticAt_of_mem_source`-style
bridge (`Bridges.lean` pattern, two-chart version). ~90 lines total (the write-up above is the
whole content; the Lean is mostly `EventuallyEq`/congr bookkeeping identical in shape to
holomorphic-forms' `Form1.ofCoeffs` smoothness proof and paths-and-integrals' `pathIntegral_mdifferential`).

**Not this unit's job**: `ofCurve_inj` (abel-theorem, per blueprint — needs Abel's theorem, g ≥
1). Recorded in the ledger (§10).

---

## 9. `pushforward`/`pullback` substrate (`Functorial.lean`)

### 9.1 The `→ₜ+` type — verified

`Jacobian X →ₜ+ Jacobian Y` is `ContinuousAddMonoidHom (Jacobian X) (Jacobian Y)`
(`Topology/Algebra/ContinuousMonoidHom.lean:45/:74`, `infixr:25 " →ₜ+ " =>
ContinuousAddMonoidHom`), a structure `extends A →+ B, C(A, B)` — needs only `[AddMonoid A]
[AddMonoid B] [TopologicalSpace A] [TopologicalSpace B]`, **not** `ContinuousLinearMap`
(`assert_not_exists ContinuousLinearMap` at the top of the file — deliberately group-only, no
ℂ-linearity tracked at this type). ℂ-linearity/holomorphicity of the induced map is a separate
`ContMDiff` statement we prove alongside, not part of the `→ₜ+` bundle itself.

### 9.2 Abstract substrate (`Torus.lean`)

```lean
noncomputable def inducedHom {V V'} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup V'] [NormedSpace ℂ V'] [FiniteDimensional ℂ V] [FiniteDimensional ℂ V']
    (L : AddSubgroup V) (L' : AddSubgroup V') (T : V →ₗ[ℂ] V')
    (hT : L ≤ L'.comap T.toAddMonoidHom) : (V ⧸ L) →ₜ+ (V' ⧸ L') :=
  { QuotientAddGroup.map L L' T.toAddMonoidHom hT with
    continuous_toFun := by
      rw [(QuotientAddGroup.isQuotientMap_mk (N := L)).continuous_iff]
      have : (QuotientAddGroup.map L L' T.toAddMonoidHom hT) ∘ QuotientAddGroup.mk =
          QuotientAddGroup.mk ∘ T := funext fun x => QuotientAddGroup.map_mk L L' T.toAddMonoidHom hT x
      rw [this]
      exact QuotientAddGroup.continuous_mk.comp T.continuous_of_finiteDimensional }
```

**Spiked verbatim, compiles** (`scratch_jac.lean` item 3). Key names: `QuotientAddGroup.map`
(`GroupTheory/QuotientGroup/Defs.lean:302`, needs `L' ≤ ... ` phrased as `L ≤ L'.comap f`, and
`[L'.Normal]` — free by commutativity as in §3), `QuotientAddGroup.map_mk` (`@[simp]`, literally
`rfl` — `T̄ ∘ mk = mk' ∘ T` definitionally), `IsQuotientMap.continuous_iff`
(`Topology/Maps/Basic.lean:341`), `QuotientAddGroup.isQuotientMap_mk`/`continuous_mk`
(`Topology/Algebra/Group/Quotient.lean`), `LinearMap.continuous_of_finiteDimensional` (used
throughout mathlib's own measure-theory files, confirmed present).

### 9.3 `ContMDiff` of the induced map (abstract layer, under `[DiscreteTopology L] [DiscreteTopology L']`)

```lean
theorem contMDiff_inducedHom {L L'} [DiscreteTopology L] [DiscreteTopology L'] (T hT) :
    ContMDiff 𝓘(ℂ, V) 𝓘(ℂ, V') ω (inducedHom L L' T hT)
```

*Proof plan.* Same representative-point technique as §4.3/§5/§8.3: at `q = mk x`, in the centered
chart at `x` (domain) and the centered chart at `T x` (codomain, valid since `T` is continuous, so
for small enough sub-ball `T (ball x ρ) ⊆ ball (T x) ρ'`), the composite is, for `w` near `0`:
`centeredChart(T x)(mk(T(x+w))) = centeredChart(Tx)(mk(Tx + Tw)) = T w` (using `T`'s linearity: `T
(x+w) = Tx + Tw`). So the chart composite is **literally `T` itself** (restricted) — entire, since
`T` is ℂ-linear between finite-dim spaces. ~30 lines, same shape as the previous three proofs; by
this point in the file it is genuinely a one-paragraph repeat of an established pattern.

### 9.4 Wrapping through the `ULift` shell (`Functorial.lean`)

```lean
noncomputable def Jacobian.inducedHom {X Y} [...] {T : (Fin (genus X) → ℂ) →ₗ[ℂ] (Fin (genus Y) → ℂ)}
    (hT : periodSubgroup X ≤ (periodSubgroup Y).topologicalClosure.comap T.toAddMonoidHom) :
    Jacobian X →ₜ+ Jacobian Y := ...
  -- compose ULift.up/down (as →ₜ+, via `ContinuousAddEquiv.ulift`-level wrapping, §7) with
  -- `RS.Torus.inducedHom` at `L := (periodSubgroup X).topologicalClosure`,
  -- `L' := (periodSubgroup Y).topologicalClosure`.
```

**Out of scope for this unit** (flagged, not silently dropped): constructing the *specific* `T`
for a given holomorphic `f : X → Y` (via pullback-of-forms `f^* : Form1 Y →ₗ[ℂ] Form1 X`,
transposed through the two bases into a map on `Fin (genus X) → ℂ → Fin (genus Y) → ℂ`), proving
`hT` for that `T` (via naturality of periods under post-composition with `f` — a short argument
once `f^*` exists, using `pathIntegral`'s definition and homotopy invariance, but genuinely needs
the pullback-of-forms operation which does **not** yet exist in any design doc), and the
functoriality lemmas `pushforward_id_apply`/`pushforward_comp_apply`/`pushforward_pullback`. **No
blueprint unit explicitly owns this** (checked: `pushforward`/`pullback`/`ContMDiff.degree`/
`pushforward_pullback` do not appear anywhere in `clean_room_blueprint.md`'s 30 unit descriptions
— only in the challenge file itself). Flagging this as a genuine **blueprint gap** for the
orchestrator: some unit (a new one, or an addendum to abel-theorem/period-lattice-rank/final
assembly) must own "pullback of holomorphic 1-forms along a holomorphic map" and the
period-naturality lemma that turns it into the `T`/`hT` this unit's `inducedHom` substrate
consumes.

---

## 10. Instance-availability ledger

| Instance | Constructible now (this unit, no upstream input) | Needs from period-lattice-rank |
|---|---|---|
| `AddCommGroup (Jacobian X)` | **yes** (§3, §7 ULift-free) | — |
| `TopologicalSpace (Jacobian X)` | **yes** | — |
| `T2Space (Jacobian X)` | **yes**, via `closure Λ`, every genus incl. `g=0` (§3, spiked) | — (period-lattice-rank later shows `closure Λ = Λ`, upgrading this from "T2 of a closure quotient" to "T2 of the honest lattice quotient," same type, no re-proof needed downstream) |
| `ofCurve`, `ofCurve_self`, `ofCurve_contMDiff` | **yes** (§8) | — |
| `ChartedSpace (Fin g → ℂ) (Jacobian X)` | abstract layer ready (§4, §7); needs `[DiscreteTopology (closure Λ)]` | **yes** — discreteness is period-lattice-rank's headline ("discreteness via the local Jacobi map") |
| `IsManifold 𝓘(ℂ,Fin g→ℂ) ω (Jacobian X)` | abstract layer ready (§4.3, §7) | same as above (discreteness only, not full rank) |
| `LieAddGroup 𝓘(ℂ,Fin g→ℂ) ω (Jacobian X)` | abstract layer ready (§5, §7) | same as above (discreteness only) |
| `CompactSpace (Jacobian X)` | abstract layer ready (§6, §7) | **yes** — needs *full rank* (`IsZLattice ℝ (closure Λ)`), period-lattice-rank's nondegeneracy + real-basis result |
| `ofCurve_inj` | **no** — needs Abel's theorem (`g ≥ 1`) | abel-theorem unit, not period-lattice-rank |
| `pushforward`/`pullback` (the actual maps, for real `f`) | substrate only (§9.2–9.3); the specific `T`/`hT` for a holomorphic `f` is **not built anywhere yet** (blueprint gap, §9.4) | — |
| `ContMDiff.degree`, `pushforward_pullback` | **no** | proper-map-degree / final assembly |

Practical upshot: `ChartedSpace`/`IsManifold`/`LieAddGroup` need only `DiscreteTopology`, a
strictly weaker fact than the full `IsZLattice` (which `CompactSpace` needs), but
period-lattice-rank's design (per blueprint) proves both together, so in practice all four unlock
at the same time. The abstract layer exposes the finer typeclass distinction anyway (§4 takes
`[DiscreteTopology L]`, §6 additionally takes `[IsZLattice ℝ L]`), so if period-lattice-rank
lands discreteness first and full rank later, three of the four instances can be wired up early.

---

## 11. Verified mathlib names (all read at the pin `548398201a64f3a5127d90d83945278cfe38cac4`, several spiked)

| Fact | Name / location |
|---|---|
| Topological closure of a subgroup, IS a subgroup | `Subgroup.topologicalClosure`/`AddSubgroup.topologicalClosure` — `Topology/Algebra/Group/Basic.lean:673` |
| `IsClosed`/`le`/`isClosed` facts about it | `Subgroup.topologicalClosure_coe/:679`, `le_topologicalClosure:684`, `isClosed_topologicalClosure:688` (a **theorem**, not instance — spiked gotcha) |
| Normal subgroup for free (abelian ambient) | `Subgroup.normal_of_isMulCommutative` (`to_additive`) — `Algebra/Group/Subgroup/Defs.lean:631`, priority 100 |
| T3 chain for a quotient by a closed normal subgroup | `QuotientGroup.instT3Space` (`to_additive`) — `Topology/Algebra/Group/Quotient.lean` |
| T3 → T2.5 → T2 | `T3Space.t25Space` / `T25Space.t2Space` — `Topology/Separation/Regular.lean:416`/`:371` |
| Quotient `AddCommGroup` for free (abelian ambient, no Normal needed) | `Quotient.commGroup` (`to_additive`) — `GroupTheory/QuotientGroup/Defs.lean:151` |
| `mk`/`map`/continuity substrate | `QuotientAddGroup.mk`, `.map` (`GroupTheory/QuotientGroup/Defs.lean:302`), `.map_mk` (`:310`, `@[simp]`, `rfl`), `.mk_surjective`, `.eq_iff_sub_mem`, `.continuous_mk`/`.isQuotientMap_mk` (`Topology/Algebra/Group/Quotient.lean`), `.isOpenMap_coe` |
| Generic continuous-quotient-lift | `IsQuotientMap.continuous_iff` — `Topology/Maps/Basic.lean:341` |
| `→ₜ+` type | `ContinuousAddMonoidHom`, `infixr " →ₜ+ "` — `Topology/Algebra/ContinuousMonoidHom.lean:45/:74`; `assert_not_exists ContinuousLinearMap` (deliberately group-only) |
| Linear map continuity (finite dim) | `LinearMap.continuous_of_finiteDimensional` |
| `AddSubgroup ↔ Submodule ℤ` | `AddSubgroup.toIntSubmodule : AddSubgroup M ≃o Submodule ℤ M` — `Algebra/Module/Submodule/Lattice.lean:415` |
| `IsZLattice`, rank, basis | `IsZLattice` class (`span_top`) — `Algebra/Module/ZLattice/Basic.lean:435`; `ZLattice.rank:525`; `Module.Basis.ofZLatticeBasis:612`; `IsZLattice.basis:686` |
| **Compactness of the quotient (THE trick)** | `IsZLattice.isCompact_range_of_periodic` — `Algebra/Module/ZLattice/Basic.lean:791` (periodic continuous map ⇒ compact range; spiked with `f := mk`) |
| Fundamental-domain fallback route | `ZSpan.fundamentalDomain:92`, `.exist_unique_vadd_mem_fundamentalDomain:261`, `.quotientEquiv:271` (bare `Equiv`, not `≃ₜ`) |
| Path-connectedness of `X` | `ChartedSpace.locPathConnectedSpace` (theorem, not instance) — `Geometry/Manifold/ChartedSpace.lean:268`; `LocallyConvexSpace.toLocPathConnectedSpace` — `Topology/Algebra/Module/LocallyConvex.lean:103`; `PathConnectedSpace.of_locPathConnectedSpace` — `Topology/Connected/LocPathConnected.lean:102` |
| `Module.finBasis` | `LinearAlgebra/Dimension/Free.lean:286`, needs `[Module.Finite]`+`[Module.Free]`; the latter free via `Module.Free.of_divisionRing` — `LinearAlgebra/Basis/VectorSpace.lean:154` |
| `finrank ℝ ℂ = 2` | `Complex.finrank_real_complex` — `LinearAlgebra/Complex/FiniteDimensional.lean:31` |
| `LieAddGroup`/`ContMDiffAdd` class shape | `Geometry/Manifold/Algebra/LieGroup.lean:62/:73`, `Monoid.lean:51/:65` — parametrized by `n : ℕ∞ω`; `instNormedSpaceLieAddGroup` (a normed space is its own Lie group) — `LieGroup.lean:197` |
| `ULift` free instances | `ULift.topologicalSpace` (`Topology/Constructions.lean:69`), `ULift.instT2Space` (`Separation/Hausdorff.lean:377`), `ULift.compactSpace` (`Compactness/Compact.lean:1060`), `ULift.commGroup`/add (`Algebra/Group/ULift.lean:108`), `IsTopologicalGroup (ULift G)` (`Algebra/Group/Basic.lean:461`), `Homeomorph.ulift`, `AddEquiv.ulift` (`:74`), `ContinuousLinearEquiv.ulift` (`Topology/Algebra/Module/Equiv.lean:694`) |
| **ABSENT** (confirmed, we build) | `ChartedSpace`/`IsManifold` transport along a `Homeomorph`/`ULift` (checked: no hits under `Geometry/Manifold/` except unrelated `Bordism.lean`); generalized `chartedSpaceOfFamily` for non-`ℂ` codomain (Surface's is hardcoded); pullback-of-holomorphic-1-forms operation (needed for the *real* `pushforward`/`pullback`, not this unit's job, §9.4) |

---

## 12. Risks & fallbacks

- **R1 (ULift transport, §2, §7).** New pattern, ~100–150 lines, not yet spiked beyond confirming
  every ingredient name exists. Mathematical content is airtight (conjugate-by-fixed-homeomorphism
  transition-map argument); engineering risk is the usual `OpenPartialHomeomorph.trans`/`source`
  bookkeeping (same flavor as surfaces-and-charts' own risk #2 for its IFT). Fallback: specialize
  the generic `ChartedSpace.ofHomeomorph`/`isManifold_ofHomeomorph` to the one concrete
  homeomorphism we need (`Homeomorph.ulift`) instead of an abstract `M' ≃ₜ M` — saves nothing
  mathematically but may reduce elaboration friction from universe-polymorphic `E, H, I` variables.
- **R2 (centered-chart construction, §4.2).** The "injective + continuous + open map ⇒ open
  embedding onto image" step may not have a single matching mathlib lemma (not confirmed by name,
  only by general topology reasoning). Fallback: build the `OpenPartialHomeomorph` by the raw
  6-field constructor directly from `mk_injOn_ball` + `QuotientAddGroup.isOpenMap_coe`, ~15 extra
  lines, no new ideas.
- **R3 (`ChartedSpaceKitV.lean` duplication, §4.2.1).** A textual near-duplicate of Surface's
  ChartedSpaceKit. Low risk (mechanical), but two copies must be kept `rfl`-compatible if both
  land; request filed to `docs/requests/surfaces-and-charts.md` to generalize theirs instead
  (preferred long-term, non-blocking now).
- **R4 (§9.4 blueprint gap).** The actual `pushforward`/`pullback` maps (not just the substrate)
  have no owning unit in the 30-unit blueprint DAG. Not this unit's problem to solve, but
  **reported here** so the orchestrator can assign it (natural candidates: a small addendum to
  abel-theorem, since it already builds period-naturality machinery for Abel's two-point argument,
  or to a not-yet-named "final assembly" step). Until assigned, `Jacobian.pushforward`/`pullback`
  in `Jacobian/Challenge.lean` stay `sorry` even after this unit is otherwise complete — expected
  and acceptable (this unit's own files have zero sorries; the challenge-level wrapper is a
  separate concern).
- **R5 (genus-0 degeneration).** By design, nothing above special-cases `g = 0`
  (`Fin 0 → ℂ` is the zero module, `V ⧸ {0}` is a one-point space, every instance holds
  vacuously/trivially through the *same* generic proofs). Verify this explicitly with `example` at
  build time (`genus X = 0 → Subsingleton (Jacobian X)` as a sanity check), but no separate code
  path is planned or needed.

---

## 13. Downstream consumption map

- **meromorphic-and-divisors, meromorphic-trace**: nothing (no blueprint edge; confirmed no
  mention of `Jacobian` in their design scope).
- **abel-theorem**: `ofCurve`, `ofCurve_eq_of_path` (any-path recipe), `ofCurve_self`, the
  `periodSubgroup`/`Λ` definition and `AddSubgroup.closure`/`subset_closure` facts, and — per R4 —
  is the most natural home for the *actual* `pushforward`/`pullback` construction (it already
  needs period-naturality-under-composition for the two-point Abel argument).
- **period-lattice-rank**: consumes `Torus.chartedSpace`/`isManifold_torus`/`lieAddGroup`/
  `compactSpace` (the abstract layer, §4–§6) and instantiates them at `L :=
  (periodSubgroup X).topologicalClosure` once it proves `[DiscreteTopology L]` and
  `[IsZLattice ℝ L.toIntSubmodule]`; also needs to show `closure Λ = Λ` (via discreteness ⇒ closed,
  a standard "discrete subgroup of a Hausdorff topological group is closed" fact — not built here,
  flagged as period-lattice-rank's own small lemma).
- **final assembly (`Jacobian/Challenge.lean`)**: everything in this unit's root API, per the
  ledger (§10); `genus_eq_zero_iff_homeo`, `ofCurve_inj`, `ContMDiff.degree`,
  `pushforward_pullback` are NOT here.

## 14. What this unit does NOT do

Full-rank/discreteness of the period lattice (period-lattice-rank); `ofCurve_inj` (abel-theorem);
the genus-0 headline; `ContMDiff.degree`, `pushforward_pullback`, and the construction of the
*actual* linear map underlying `pushforward`/`pullback` for a real holomorphic `f` (blueprint gap,
R4); any mapping-degree machinery (unused despite the blueprint edge, §0).

---

## 15. Spike report (`scratch_jac.lean`, 44 lines, kept at project root)

Gated per protocol (`pgrep -cx lean` was `0` before running). Compiles clean,
`lake env lean scratch_jac.lean`, ~6.6s wall, exit 0. Four items, all load-bearing for this design:

1. `T2Space (V ⧸ L.topologicalClosure)` for a bare `AddSubgroup L` (no discreteness) — compiles
   **only** after adding `haveI : IsClosed (L.topologicalClosure : Set V) :=
   L.isClosed_topologicalClosure` (plain `infer_instance` fails without it — real gotcha, recorded
   in §3/§11).
2. `AddCommGroup`/`TopologicalSpace (V ⧸ L.topologicalClosure)` — free, `infer_instance`.
3. `inducedHom`: a `ℂ`-linear `T : V →ₗ[ℂ] V'` with `L ≤ L'.comap T.toAddMonoidHom` produces a
   genuine `(V⧸L) →ₜ+ (V'⧸L')`, continuity via `IsQuotientMap.continuous_iff` +
   `QuotientAddGroup.map_mk` (`rfl`) + `LinearMap.continuous_of_finiteDimensional` — compiles
   exactly as designed in §9.2, no adjustments needed.
4. `CompactSpace (V ⧸ L.toAddSubgroup)` for `[DiscreteTopology L] [IsZLattice ℝ L]`, via
   `IsZLattice.isCompact_range_of_periodic` + periodicity (`QuotientAddGroup.eq_iff_sub_mem`) +
   surjectivity (`QuotientAddGroup.mk_surjective`) — compiles exactly as designed in §6.

Not spiked (out of budget for one gated spike; proof plans only, §4/§5/§7/§8): the centered-chart
`ChartedSpace`/`IsManifold`/`LieAddGroup` construction, the `ULift` transport toolkit, and
`ofCurve_contMDiff`. These are the highest-*engineering*-risk items (R1, R2) though the
mathematical content is fully worked out above and cross-checked against the exact shape of
proofs already compiling elsewhere in the project (holomorphic-forms' section-smoothness proofs,
paths-and-integrals' `rechart`/congr idioms).

---

## 16. Requests to other units

Filed in `docs/requests/surfaces-and-charts.md`:

1. **Generalize `chartedSpaceOfFamily`/`isManifold_of_family`** (`Jacobian/Surface/
   ChartedSpaceKit.lean`) from hardcoded codomain `ℂ` to an arbitrary `{E : Type*}
   [NormedAddCommGroup E] [NormedSpace ℂ E]`. Non-blocking: we carry a local, textually-identical
   copy in `Jacobian/JacobianConstruction/ChartedSpaceKitV.lean` either way.
2. **`LocPathConnectedSpace X` / `PathConnectedSpace X` instances** for any Riemann surface (`§8.1`
   — two-line derivation from `ChartedSpace.locPathConnectedSpace` + `ConnectedSpace X`). Generic,
   likely wanted by other units too (sphere-topology, mapping-degree); we carry a local `Compat`
   copy regardless.
3. **Confirmation of exports** consumed unchanged from their design doc: `contMDiffAt_iff_analyticAt_of_mem_source`,
   `contMDiffOn_iff_analyticOnNhd_of_subset_source` (Bridges — used in `ofCurve_contMDiff`'s final
   step).

Filed in `docs/requests/holomorphic-forms.md` (append): confirmation that `Module.finrank ℂ
(Form1 X)` (i.e. `genus X`) stays exactly `Module.finrank ℂ (RS.Form1 X)` with no wrapper, since
`Module.finBasis ℂ (Form1 X) : Basis (Fin (Module.finrank ℂ (Form1 X))) ℂ (Form1 X)` must be
*definitionally* `Basis (Fin (genus X)) ℂ (Form1 X)` for `basis X` (§8.2) to typecheck against the
challenge's `Fin (genus X) → ℂ` without a `finCongr`/cast.
