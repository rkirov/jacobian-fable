# Design: finiteness-and-chi (`Jacobian/Finiteness/`)

Blueprint unit **finiteness-and-chi** — the load-bearing analytic unit. Delivers:

1. **`FiniteDimensional ℂ (H1 (0 : Divisor X))`** by the Schwartz compact-perturbation
   argument (Forster §14, re-architected for sup-norm Banach spaces — §0 explains the
   re-architecture and why it is *leaner* than a literal transcription);
2. **all-`D` finiteness** `FiniteDimensional ℂ (H1 D)` and `FiniteDimensional ℂ (LinSys D)`
   via cech's six-term skyscraper fragment (decision D2: NOT by twisted norms);
3. the **χ ledger**: `h1 D`, `chi D := l D − h1 D`, `chi D = chi 0 + deg D`, monotonicity,
   and the Riemann-inequality seed `chi 0 + deg D ≤ l D` that canonical-forms consumes.

References: Forster §14 read IN FULL (book 109–118 = PDF 115–124; 14.1–14.7 the analytic
core, 14.8–14.10 assembly, 14.12 the consumer pattern), §16 for the χ bookkeeping (book
126–131 = PDF 132–137, esp. 16.7–16.9). Miranda Ch. VI was consulted and is NOT used here:
Miranda develops finiteness through the tail model that *presupposes* this unit downstream;
Forster §14 is the only self-contained route.

Substrates (AUTHORITATIVE): `docs/design/cech-cohomology.md` (FinCover, cochains, `Z1/B1`,
`H1Cover`, `resZ1/resH1`, colimit `H1`, `toH1`, six-term fragment — Covers/Cochains BUILT,
names verified at source, rest in flight), `docs/design/dolbeault-comparison.md` §0.1 (our
TRUE interface: `exists_trade`, `resH1_surjective_of_isGood`, `toH1_surjective_of_isGood`,
`h1CoverEquiv`; §0.2 records the all-`D` assembly recipe we implement),
`Jacobian/Meromorphic/` (BUILT, verified at source: `MeroGermOn`, `mk/restrict`, `ord`,
`evalAt`, `holoRepr`, `LinSysOn`, `LinSys D`, `l D`, `linSys_zero_eq_span_one`, `l_zero`),
`Jacobian/Forms/Montel.lean` (BUILT: `montelFamily`, `isCompact_closure_montelFamily`,
`norm_deriv_le_of_bounded`, `norm_sub_le_of_bounded_of_cthickening_subset`),
`Jacobian/Surface/Bridges.lean` (BUILT: `contMDiffOn_iff_analyticOnNhd_of_subset_source`
and the ContMDiff↔planar-analytic kit).

---

## 0. The re-architecture (read first): Forster §14 audited, and the leaner proof shape

Forster's proof structure (verbatim audit of PDF 115–124):

- **14.1–14.2**: `L²`-norms on planar holomorphic functions; `‖f‖_{D_r} ≤ (πr)^{-1/2}
  ‖f‖_{L²(D)}`; hence `L²(D, 𝒪)` is a **Hilbert** space.
- **14.3**: for `D' ⋐ D` and any `ε > 0` there is a **closed finite-codimensional** subspace
  `A ⊆ L²(D, 𝒪)` with `‖f‖_{L²(D')} ≤ ε‖f‖_{L²(D)}` on `A` (functions vanishing to high
  order at finitely many centers; Taylor/Pythagoras decay). *No Montel here.*
- **14.4–14.5**: `L²`-cochain norms over a fixed chart family; `Z¹_{L²}` closed.
- **14.6**: for same-index shrinkings `𝔚 ⋐ 𝔙 ⋐ 𝔘 ⋐ 𝔘*`: every `ξ ∈ Z¹_{L²}(𝔙)` trades to
  `ζ ∈ Z¹_{L²}(𝔘)`, `η ∈ C⁰_{L²}(𝔚)` with `ζ = ξ + δη` on `𝔚` and
  `max(‖ζ‖, ‖η‖) ≤ C‖ξ‖`. Part (a) qualitative = dolbeault's `exists_trade`; part (b) =
  **Banach open mapping** applied to the projection `π : L → Z¹_{L²}(𝔙)` off the closed
  subspace `L = {(ζ, ξ, η) : ζ = ξ + δη on 𝔚}` of the product Hilbert space.
- **14.7** (Schwartz iteration): finite-dim `S ⊆ Z¹(𝔘)` with: every `ξ ∈ Z¹(𝔘)` satisfies
  `σ = ξ + δη` on `𝔚` for some `σ ∈ S`. Proof: `ε := 1/2C`, `A` from 14.5/14.3,
  `S := A^⊥` (**orthogonal complement — Hilbert-specific!**), geometric iteration.
- **14.9–14.10**: Leray + disk vanishing identify cover-level `H¹` with `H¹(X)`; compact
  case: `dim H¹(X, 𝒪) < ∞`.

**Two deliberate deviations, justified:**

**(D-a) Sup norms on `⋐`-shrunk pairs, not `L²`.** Chosen because: (i) the sup norm of a
germ over `S ⊆ X` is **chart-independent** (`sup_{x∈S} ‖evalAt φ x‖`) — Forster's `L²` norms
depend on the fixed chart images and need change-of-variable bookkeeping we'd have to build;
(ii) completeness = "uniform limits of holomorphic are holomorphic" =
`TendstoLocallyUniformlyOn.differentiableOn`, already in mathlib and already imported by our
BUILT Montel file — `L²`-completeness would need 14.2's mean-value estimate plus planar
measure theory (Fubini on chart images, none of it staged); (iii) Montel/Arzelà is BUILT for
sup norms on `C(K, ℂ)`; (iv) the only Hilbert-specific step Forster uses (orthogonal
complement in 14.7) is eliminated by (D-b). Carrier: bounded-holomorphic functions on open
`S ⊆ X` as a **closed submodule of `↥S →ᵇ ℂ`** (`BoundedContinuousFunction`), Banach for free.

**(D-b) The endgame is the abstract Schwartz cospan lemma, not Forster's 14.3/14.7.**
Forster's 14.3 (finite-codim ε-contraction subspace) + 14.7 (iteration with orthogonal
decompositions) exist to prove exactly this statement, which is the classical
L. Schwartz perturbation lemma specialized:

> `u, v : E →L F` between Banach spaces, `u` **surjective**, `v` **compact** ⇒ there is a
> finite-dimensional `S ⊆ F` with `F = range (u − v) + S`.

(We do NOT need the second half of Schwartz's theorem — closedness of `range (u − v)` —
because we only ever take *dimensions* of quotients of `range (u − v)`, never its topology.)
With `E := L` (Forster's 14.6(b) subspace), `u := π` (the projection, surjective by the
qualitative trade), `v := (ζ, ξ, η) ↦ ζ|_𝔙` (restriction `Z¹(𝔘) → Z¹(𝔙)`, **compact by
Montel — the blueprint's "compact operator = restriction between nested covers", verbatim**),
one computes `range (u − v) = {θ ∈ Z¹(𝔙) : θ|_𝔚 ∈ range δ_𝔚}` — exactly the cocycles that
die in `H¹(𝔚)`. So `Z¹(𝔙) = S + (classes dying in H¹(𝔚))`, and since bounded `𝔙`-cocycles
hit every `H¹(𝔚)`-class (one more qualitative trade), `H¹(𝔚)` is spanned by the image of the
finite-dimensional `S`. Done — **no 14.3, no ε-contraction subspaces, no orthogonal/closed
complements, no quotient norms, no Riesz theorem.** The proof of the cospan lemma itself is
a geometric-series iteration identical in texture to mathlib's own proof of
`ContinuousLinearMap.exists_preimage_norm_le` (read at the pin; we mirror its idioms:
`Function.iterate`, `Summable.of_norm`, `summable_geometric_of_lt_one`, telescoping,
`tendsto_nhds_unique`). Forster's open-mapping step 14.6(b) survives as the FIRST LINE of
the lemma's proof: `u.exists_preimage_norm_le hu`.

Net effect: mathlib functional analysis consumed = Banach OMT (`exists_preimage_norm_le`) +
`IsCompactOperator` basics + `finite_cover_balls_of_compact` + fin-dim span/closedness.
All verified present at the pin (§1). The inventory's warning "Schwartz lemma does NOT exist
in mathlib" is resolved by *proving it* (`schwartz_finite_cospan`, §6.2) — 80±20 lines,
zero manifold content, buildable today.

**Divisor scope of the analytic core: `D = 0` only** (decision D2, §2). Matches Forster
(§14 is for `𝒪` only) and dolbeault's §0.2 audit; all-`D` is six-term bookkeeping (§7).

---

## 1. Verified mathlib facts (file:line at pin `5483982…`; ★ = compiled in spike §11)

### 1.1 Banach open mapping — `Analysis/Normed/Operator/Banach.lean`

- ★ `ContinuousLinearMap.exists_preimage_norm_le (f : E →SL[σ] F) (surj : Surjective f) :
  ∃ C > 0, ∀ y, ∃ x, f x = y ∧ ‖x‖ ≤ C * ‖y‖` (`:162`) — requires `[CompleteSpace E]`
  (`:155`) and `[CompleteSpace F]` (`:81`). This IS 14.6(b)'s open-mapping input.
  (`ContinuousLinearMap.isOpenMap` (`:229`) exists too; we only need the preimage form.)

### 1.2 Compact operators — `Analysis/Normed/Operator/Compact/Basic.lean`

- `IsCompactOperator f := ∃ K, IsCompact K ∧ f ⁻¹' K ∈ 𝓝 0` (`:69`).
- ★ `isCompactOperator_iff_isCompact_closure_image_closedBall (f) (hr : 0 < r) :
  IsCompactOperator f ↔ IsCompact (closure (f '' Metric.closedBall 0 r))` (`:194`;
  needs `[ContinuousConstSMul] [T2Space]` on the codomain — satisfied by normed spaces).
- ★ `IsCompactOperator.comp_clm (hf) (g : M₁ →SL M₂) : IsCompactOperator (f ∘ g)` (`:274`);
  `IsCompactOperator.clm_comp (hf) (g : M₂ →SL M₃) : IsCompactOperator (g ∘ f)` (`:288`).

### 1.3 Finite-dimensionality plumbing

- ★ `finite_cover_balls_of_compact (hs : IsCompact s) (he : 0 < e) :
  ∃ t ⊆ s, t.Finite ∧ s ⊆ ⋃ x ∈ t, Metric.ball x e` (`Topology/MetricSpace/Pseudo/Basic.lean:265`).
- ★ `FiniteDimensional.span_of_finite K (hA : A.Finite) : FiniteDimensional K (span K A)`
  (`LinearAlgebra/FiniteDimensional/Defs.lean:203`).
- ★ `Submodule.closed_of_finiteDimensional (s) [FiniteDimensional 𝕜 s] : IsClosed (s : Set E)`
  (`Analysis/Normed/Module/FiniteDimension.lean:414` usage; complete field).
- ★ `Module.Finite.of_surjective (f : M →ₛₗ P) (hf : Surjective f)` (`RingTheory/Finiteness/Basic.lean:252`);
  `Module.Finite.equiv (e : M ≃ₗ N)` (`:313`).
- ★ `Module.Finite.of_submodule_quotient (N : Submodule R M) [Module.Finite R N]
  [Module.Finite R (M ⧸ N)] : Module.Finite R M` (`RingTheory/Finiteness/Finsupp.lean:130`)
  — **the extension lemma** for both all-`D` steps. (`FiniteDimensional` is
  `Module.Finite`, so these apply verbatim.)
- ★ `LinearMap.quotKerEquivRange : (M ⧸ ker f) ≃ₗ[R] range f` (`LinearAlgebra/Isomorphisms.lean:39`).
- `LinearMap.finrank_range_add_finrank_ker [FiniteDimensional K V] (f : V →ₗ V₂)`
  (`LinearAlgebra/FiniteDimensional/Lemmas.lean:173`) — rank-nullity for the χ ledger.
- `LinearMap.finrank_le_finrank_of_surjective` (`Dimension/StrongRankCondition.lean:558`).
- NOT USED (recorded for fallback F2 only): `FiniteDimensional.of_isCompact_closedBall₀`
  (Riesz, `Normed/Module/FiniteDimension.lean:457`), `Submodule.Quotient.normedAddCommGroup
  [IsClosed S]` + `Submodule.Quotient.normedSpace` (`Normed/Group/Quotient.lean:429/:462`),
  `LinearMap.continuous_of_finiteDimensional`. No Fredholm API exists or is needed.

### 1.4 Function-space carrier

- `BoundedContinuousFunction` (`α →ᵇ β`): `Topology/ContinuousMap/Bounded/Basic.lean`;
  `instCompleteSpace [CompleteSpace β]` (`:303`);
  `tendsto_iff_tendstoUniformly` (`:236`); `ofNormedAddCommGroup (f : α → β) (Hf :
  Continuous f) (C) (H : ∀ x, ‖f x‖ ≤ C) : α →ᵇ β` (`Bounded/Normed.lean:118`);
  norm and `norm_coe_le_norm` in `Bounded/Normed.lean`.
- ★ Submodule norm instances: `Submodule.seminormedAddCommGroup`/`normedAddCommGroup`
  (`Analysis/Normed/Group/Submodule.lean:21/:42`); `Pi` normed group/space instances
  (`Analysis/Normed/Group/Constructions.lean`; `Pi.normedSpace`); `Prod` likewise.
- ★ `IsClosed.completeSpace_coe` (closed subset of complete is complete);
  `ContinuousLinearMap.isClosed_ker [T1Space M₂]` (`Topology/Algebra/Module/LinearMap.lean:659`);
  `Submodule.subtypeL` (`:1245`).
- `Subtype.isCompact_iff : IsCompact s ↔ IsCompact ((↑) '' s)`
  (`Topology/Compactness/Compact.lean:997`).
- Uniform limits: `TendstoLocallyUniformlyOn.differentiableOn`,
  `TendstoUniformlyOn.tendstoLocallyUniformlyOn` (`Analysis/Complex/LocallyUniformLimit.lean`
  — already imported by `Jacobian/Forms/Montel.lean`); `DifferentiableOn.analyticOnNhd`.
- `IsCompact.exists_bound_of_continuousOn`; `IsCompact.exists_cthickening_subset_open`
  (used in Montel.lean `:91`); `exists_compact_subset` (the `GoodCover.nonempty` pattern,
  `Jacobian/Forms/Finiteness.lean:81`).

### 1.5 Project substrates consumed (exact statements)

- **Montel (BUILT, `Jacobian/Forms/Montel.lean`)**:
  ```
  montelFamily (Ω K : Set ℂ) (C : ℝ) : Set C(K, ℂ)
    -- {f | ∃ g, DifferentiableOn ℂ g Ω ∧ (∀ z ∈ Ω, ‖g z‖ ≤ C) ∧ ∀ z : K, f z = g z}
  isCompact_closure_montelFamily (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (C) :
    IsCompact (closure (montelFamily Ω K C))
  ```
  — the compactness input for `res : Z_U →L Z_V` (§6.3). Also available (not needed on the
  primary path, used by fallback F2): `norm_sub_le_of_bounded_of_cthickening_subset`,
  `norm_deriv_le_of_bounded`.
- **mero (BUILT, verified)**: `MeroGermOn X U`, `mk`, `mk_eq_mk`, `restrict`(AlgHom) +
  presheaf laws, `ord`, `evalAt`, `evalAt_mk_of_contMDiffAt` (`OrderEval.lean:157`),
  `holoRepr` (`:225`), `holoRepr_contMDiffOn` (`:289`), `mk_holoRepr`;
  `LinSysOn D U : Submodule ℂ (MeroGermOn X U)` (`LinearSystem.lean:222`),
  `mem_linSysOn_iff_of_isOpen` (`:240`), `restrict_mem_linSysOn` (`:245`), `linSys_mono`;
  `LinSys D` (`:52`), `l D := finrank ℂ (LinSys D)` (`:98`),
  `linSys_zero_eq_span_one [CompactSpace X] [ConnectedSpace X]` (`:139`), `l_zero` (`:163`)
  — **Liouville is already BUILT**; `Divisor X`, `degree` + algebra.
- **Surface (BUILT)**: `RS.contMDiffOn_iff_analyticOnNhd_of_subset_source` and the
  ContMDiff↔`AnalyticAt` chart bridges (`Surface/Bridges.lean`) — the two chart-crossing
  lemmas (§6.1 closedness, §6.3 Montel transport) reduce to these.
- **cech (Covers/Cochains BUILT — verified at source; rest per frozen design §4)**:
  `FinCover Ω` (`Covers.lean:34`), `IsRefIdx` (`:53`), preorder (`:55`), `IsChartDisk`
  (`:97`), `IsGood` (`:102`), `exists_good_refinement_closure` (`:206`); `C0/C1`, `d0`
  (`Cochains.lean:94`), `Z1` (`:189`), `B1` (`:192`), `H1Cover`, `H1Cover.mk` (`:207`),
  `H1Cover.mk_eq_zero_iff` (`:211`), `congrSet`; in flight: `resZ1/resH1`, `H1 D`, `toH1`,
  `toH1_resH1`, `exists_rep`, `toH1_injective`, `H1Incl`, `Window`, `finrank_window`,
  `windowMap`/`windowConnect` + the six-term fragment (`exact_inclusion_windowMap`,
  `exact_windowMap_windowConnect`, `exact_windowConnect_H1Incl`, `H1Incl_surjective`).
- **dolbeault (design frozen; `Leray.lean` in flight)** — our gate, §0.1 of their doc:
  ```
  exists_trade (h𝒰 : 𝒰.IsGood) (τ) (hτ : IsRefIdx 𝒰 𝒱 τ) (D) (f : Z1 D 𝒱) :
    ∃ (F : Z1 D 𝒰) (g : C0 D 𝒱), (resZ1 D τ hτ F : C1 D 𝒱) = (f : C1 D 𝒱) + d0 D 𝒱 g
  toH1_surjective_of_isGood / resH1_surjective_of_isGood / h1CoverEquiv
  ```

---

## 2. Design decisions

### D1 — Norm setting: intrinsic sup norms on `⋐`-shrunk same-index cover chains

Carrier (§4.1): `BddHoloOn (S : Opens X) : Submodule ℂ (↥(S : Set X) →ᵇ ℂ)` — bounded
continuous functions on the open subtype that agree on `S` with some `ContMDiffOn 𝓘(ℂ) ω`
function. Norm = sup over `S`, chart-free. Closed (uniform limits, §6.1) hence Banach.
The `⋐` relation is packaged once in the four-level `ShrinkChain` (D3). Justification vs
`L²`: §0 (D-a). Cochain spaces are finite `Pi`s of these; `Z`-spaces are pointwise-condition
closed submodules. No hand-rolled norms anywhere.

### D2 — Analytic core at `D = 0` ONLY; all-`D` by the six-term fragment

Sup norms of meromorphic cochains are infinite near poles; a twisted norm layer (weights
`z^{D}`, coherent local equations across overlaps) would be real analytic plumbing for zero
gain. Forster never twists §14 either. All-`D` finiteness is pure fin-dim bookkeeping from
`D = 0` + cech's fragment (recipe recorded by dolbeault §0.2, implemented here §7):
`D' := D ⊔ 0`; `H1Incl_surjective (0 ≤ D')` caps `h1 D'`; exactness at `H1 D` +
`finrank_window` caps `h1 D`. CONFIRMED: the trade/Leray exports ARE all-`D`, but we
deliberately consume them at `D = 0` only.

### D3 — Four-level same-index chain `W ⋐ V ⋐ U ⋐ U*`, `U*` good

`ShrinkChain X` (§4.2): `n`, centers `c : Fin n → X`, `Ustar U V W : Fin n → Opens X`,
per-index closure inclusions, `Ustar i` a chart disk of the chart at `c i`, `W` covers `X`.
Same index set = Forster's 14.4–14.6 setup; all cech refinement maps between the four
induced `FinCover ⊤`s use `τ = id` (their `IsRefIdx` is `W i ≤ V i ≤ U i ≤ Ustar i`), so
zero `τ`-plumbing enters the norm layer. Roles: `U*` = germ home of traded cocycles (good ⇒
`exists_trade` applies); `U` = first bounded level (`closure(U-pair) ⊆ U*-pair`); `V` = the
Banach middle level (Montel `res_UV` compact; its cocycles surject onto `H¹(𝔚)`); `W` =
coboundary level (`η` bounded since `closure(W i) ⊆ V i`). Existence by the
`Forms/Finiteness.lean GoodCover.nonempty` pattern (iterated `exists_compact_subset` is not
enough — `U*` must be a chart *disk*, so we use nested chart-ball pullbacks, §6.4); we do
NOT reuse cech's `exists_good_refinement_closure` (it changes the index set).

### D4 — Compactness packaged as `IsCompactOperator`; concrete everywhere else

The ONLY operator-theoretic notion used is `IsCompactOperator` for the level restriction
`res_UV`, because (i) its API at the pin is sufficient and verified (§1.2), (ii) the
abstract lemma consumes exactly `IsCompactOperator v` and nothing else. Everything else
(nets, series, spans) is concrete-sequential, mirroring mathlib's own OMT proof. Forster's
proof-shape (iteration) is kept but relocated into the one abstract lemma
`schwartz_finite_cospan` with no cochain content, so the analytic file is reusable and
spike-testable in isolation.

### D5 — The Čech/Banach interface is germ↔function bridges, localized in one file

All germ-vs-function traffic goes through three named maps (§4.1): `toGerm` (bounded holo
function ⇒ `LinSysOn 0` germ), `restrictGerm` (germ on `S` ⇒ bounded holo function on
`S' ⋐ S` via `holoRepr`), and their `d0/δ`-naturality lemmas. The Banach files never touch
`MeroGermOn` internals; the cochain files never touch `→ᵇ` internals. Pointwise reasoning
uses mero's `evalAt` rigidity exactly as dolbeault §6.2 does (`repr_cocycle` pattern).

### D6 — Instance hygiene

```lean
open scoped ContDiff Manifold Topology BoundedContinuousFunction
open Set Filter TopologicalSpace Metric
variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
```
`[T2Space X] [CompactSpace X]` from the chain onward (closures/compactness/PoU-fed trade);
`[ConnectedSpace X]` ONLY in `Chi.lean` where `l_zero` (Liouville) enters. `Schwartz.lean`
carries no manifold variables at all. Namespace `RS`; norm-layer names in `RS.Finiteness`.
Targeted imports; the heavy mathlib imports (`Banach`, `Compact.Basic`) enter only
`Schwartz.lean`/`CompactRestrict.lean`.

### D7 — What we do NOT do (owners)

`dim H¹(𝒪) = g` — cech-h1-genus. Serre pairing — serre-duality-cech/tails. The tail model —
laurent-tails. `H^{0,1}` transfer — dolbeault already has `finiteDimensional_H01` keyed on
our instance. Nonconstant-function extraction from `l D ≥ 2` — canonical-forms (we export
the dimension inequality, they own the function surgery, Forster 14.12/16.11 pattern).

---

## 3. File plan (dependency order; estimated sizes; build gates)

```
Jacobian/Finiteness.lean                  -- root: imports + API docstring            (~30)
Jacobian/Finiteness/Schwartz.lean         -- schwartz_finite_cospan + consumer form
                                          --   finiteDimensional_of_cospan; pure
                                          --   Banach, ZERO project deps  [NOW]       (~240)
Jacobian/Finiteness/BddHolo.lean          -- BddHoloOn, closed/complete, restrictCLM,
                                          --   evalCLM, toGerm/restrictGerm bridges
                                          --   [needs mero+Surface: NOW]              (~430)
Jacobian/Finiteness/CompactRestrict.lean  -- Montel transport: IsCompactOperator of
                                          --   BddHoloOn-restriction [Montel: NOW]    (~260)
Jacobian/Finiteness/Chain.lean            -- ShrinkChain, existence, toCover lemmas,
                                          --   NC0/NC1/NZ1, δ CLM, level res CLMs,
                                          --   the space L and π [cech Covers: NOW]   (~420)
Jacobian/Finiteness/TradeBounded.lean     -- germify/degermify cocycles, π surjective,
                                          --   classMap χ, χ surjective, ker lemma
                                          --   [GATE: cech Colimit + dolbeault Leray] (~400)
Jacobian/Finiteness/H1Finite.lean         -- finiteDimensional_H1_zero; all-D
                                          --   [GATE: + cech Skyscraper]              (~220)
Jacobian/Finiteness/Chi.lean              -- FiniteDimensional (LinSys D), h1, chi,
                                          --   ledger + Riemann seed [same gate]      (~360)
```
Four of seven content files are buildable before the gates land — start there.
Import spine: mathlib `Analysis.Normed.Operator.Banach`, `Analysis.Normed.Operator.Compact.Basic`,
`Analysis.Normed.Module.FiniteDimension`, `RingTheory.Finiteness.Finsupp`,
`Topology.ContinuousMap.Bounded.Normed`, `Analysis.Complex.LocallyUniformLimit`; project
`Jacobian.Meromorphic`, `Jacobian.Forms.Montel`, `Jacobian.Surface`, `Jacobian.Cech`,
`Jacobian.DolbeaultComparison` (Leray only — see their D1: `Leray.lean` has no comparison deps).

---

## 4. Exports — exact signatures

### 4.1 `BddHolo.lean` (namespace `RS.Finiteness`)

```lean
/-- Bounded-holomorphic elements: BCF on the open subtype agreeing with a holomorphic
function on `S`. -/
noncomputable def BddHoloOn (S : Opens X) : Submodule ℂ (↥(S : Set X) →ᵇ ℂ) where
  carrier := {f | ∃ g : X → ℂ, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω g ↑S ∧ ∀ z : ↥(S : Set X), f z = g z}
  ...

theorem isClosed_bddHoloOn (S : Opens X) : IsClosed (BddHoloOn S : Set (↥(S:Set X) →ᵇ ℂ))
instance (S : Opens X) : CompleteSpace (BddHoloOn S)      -- IsClosed.completeSpace_coe

/-- Restriction, norm ≤ 1. -/
noncomputable def restrictCLM {S' S : Opens X} (h : S' ≤ S) : BddHoloOn S →L[ℂ] BddHoloOn S'
@[simp] theorem restrictCLM_apply_coe (h) (f) (z : ↥(S' : Set X)) : ...= f ⟨z, h z.2⟩
theorem norm_restrictCLM_apply_le (h) (f) : ‖restrictCLM h f‖ ≤ ‖f‖

/-- Germification (lands in `LinSysOn 0`). -/
noncomputable def toGerm (S : Opens X) : BddHoloOn S →ₗ[ℂ] MeroGermOn X ↑S
theorem toGerm_mem_linSysOn (f) : toGerm S f ∈ LinSysOn (0 : Divisor X) ↑S
theorem evalAt_toGerm (f) {x : X} (hx : x ∈ S) : (toGerm S f).evalAt x = f ⟨x, hx⟩
theorem toGerm_restrict_comm (h : S' ≤ S) (f) :
    toGerm S' (restrictCLM h f) = MeroGermOn.restrict h (toGerm S f)

/-- De-germification onto a compactly-contained smaller open (uses `holoRepr`;
`[T2Space X] [CompactSpace X]`). -/
noncomputable def restrictGerm {S' S : Opens X} (hc : closure (S' : Set X) ⊆ (S : Set X))
    (φ : LinSysOn (0 : Divisor X) ↑S) : BddHoloOn S'
@[simp] theorem restrictGerm_apply (hc) (φ) (z) : (restrictGerm hc φ : _ →ᵇ ℂ) z
    = MeroGermOn.holoRepr (φ : MeroGermOn X ↑S) z
theorem toGerm_restrictGerm (hc) (φ) :
    toGerm S' (restrictGerm hc φ) = MeroGermOn.restrict (le_of_closure hc) ↑φ
theorem restrictGerm_toGerm (hc) (f : BddHoloOn S) :
    restrictGerm hc ⟨toGerm S f, toGerm_mem_linSysOn f⟩ = restrictCLM (le_of_closure hc) f
```

### 4.2 `Chain.lean` (namespace `RS.Finiteness`; `[T2Space X] [CompactSpace X]`)

```lean
/-- Forster's `𝔚 ⋐ 𝔙 ⋐ 𝔘 ⋐ 𝔘*` with `𝔘*` chart disks; same index set. -/
structure ShrinkChain (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] where
  n : ℕ
  c : Fin n → X
  Ustar U V W : Fin n → Opens X
  isChartDisk_Ustar : ∀ i, IsChartDisk (Ustar i)
  Ustar_subset_source : ∀ i, (Ustar i : Set X) ⊆ (chartAt ℂ (c i)).source
  closure_U_subset : ∀ i, closure (U i : Set X) ⊆ (Ustar i : Set X)
  closure_V_subset : ∀ i, closure (V i : Set X) ⊆ (U i : Set X)
  closure_W_subset : ∀ i, closure (W i : Set X) ⊆ (V i : Set X)
  covers_W : ∀ x : X, ∃ i, x ∈ W i

theorem ShrinkChain.nonempty [T2Space X] [CompactSpace X] : Nonempty (ShrinkChain X)

-- the four FinCovers (⊤ : Opens X) + refinement facts, all τ = id:
def ShrinkChain.coverStar / coverU / coverV / coverW (T : ShrinkChain X) : FinCover ⊤
theorem ShrinkChain.good_star : T.coverStar.IsGood
theorem ShrinkChain.ref_star_V : IsRefIdx T.coverStar T.coverV id   -- and _star_W, _V_W, …

-- Banach cochain layer at a level P ∈ {U, V, W} (P : Fin T.n → Opens X abbreviated):
noncomputable def NC0 (T) (P) : Type _ := Π i : Fin T.n, BddHoloOn (P i)
noncomputable def NC1 (T) (P) : Type _ := Π p : Fin T.n × Fin T.n, BddHoloOn (P p.1 ⊓ P p.2)
-- instances NormedAddCommGroup/NormedSpace ℂ/CompleteSpace: Pi of subtypes (spiked ★)

/-- Bounded cocycles: the pointwise triple condition (no NC2 needed). -/
noncomputable def NZ1 (T) (P) : Submodule ℂ (NC1 T P) :=
  { carrier := {f | ∀ i j k, ∀ x (h : x ∈ P i ⊓ P j ⊓ P k),
      f (j,k) ⟨x,…⟩ - f (i,k) ⟨x,…⟩ + f (i,j) ⟨x,…⟩ = 0}, … }
theorem isClosed_NZ1 … ; instance : CompleteSpace (NZ1 T P)

noncomputable def deltaCLM (T) (P) : NC0 T P →L[ℂ] NC1 T P     -- (η_j − η_i)|pair, ‖·‖ ≤ 2
noncomputable def resNC1 (T) {P P'} (h : ∀ i, P' i ≤ P i) : NC1 T P →L[ℂ] NC1 T P'
noncomputable def resZ (T) (h) : NZ1 T P →L[ℂ] NZ1 T P'        -- restriction of resNC1

/-- Forster's `L ⊆ Z¹(𝔘) × Z¹(𝔙) × C⁰(𝔚)` (14.6(b)). -/
noncomputable def tradeSpace (T : ShrinkChain X) : Submodule ℂ
    (NZ1 T T.U × NZ1 T T.V × NC0 T T.W) :=
  LinearMap.ker (tradeDefect T)   -- tradeDefect := res_UW ∘ pr₁ − res_VW ∘ pr₂ − δ_W ∘ pr₃
instance : CompleteSpace (tradeSpace T)                         -- isClosed_ker (★)
noncomputable def tradePi (T) : tradeSpace T →L[ℂ] NZ1 T T.V    -- π = pr₂ ∘ subtypeL
noncomputable def tradeCompact (T) : tradeSpace T →L[ℂ] NZ1 T T.V  -- v = res_UV ∘ pr₁ ∘ subtypeL
```

### 4.3 `Schwartz.lean` (namespace `RS`; pure Banach, no manifolds)

```lean
/-- **The Schwartz cospan lemma**: a compact perturbation of a surjective continuous linear
map between Banach spaces has finite-codimensional range (span form; no closedness). -/
theorem schwartz_finite_cospan {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (u v : E →L[ℂ] F) (hu : Function.Surjective u) (hv : IsCompactOperator v) :
    ∃ S : Submodule ℂ F, FiniteDimensional ℂ S ∧ ∀ f : F, ∃ e : E, f - (u e - v e) ∈ S

/-- Consumer form: any linear target killed by `u − v` and hit by `F` is fin-dim. -/
theorem finiteDimensional_of_cospan {E F P : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    [AddCommGroup P] [Module ℂ P] (u v : E →L[ℂ] F) (hu : Function.Surjective u)
    (hv : IsCompactOperator v) (χ : F →ₗ[ℂ] P) (hker : ∀ e, χ (u e - v e) = 0)
    (hχ : Function.Surjective χ) : FiniteDimensional ℂ P

/-- Extension helper (both all-`D` steps). -/
theorem FiniteDimensional.of_linearMap_ker_range {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] (f : M →ₗ[ℂ] N) [FiniteDimensional ℂ (LinearMap.ker f)]
    [FiniteDimensional ℂ N] : FiniteDimensional ℂ M
```

### 4.4 `CompactRestrict.lean`

```lean
/-- Montel: restriction across a compact inclusion inside one chart is compact. -/
theorem isCompactOperator_restrictCLM {S' S : Opens X} {x₀ : X}
    (hsrc : (S : Set X) ⊆ (chartAt ℂ x₀).source) (hc : closure (S' : Set X) ⊆ (S : Set X))
    [T2Space X] [CompactSpace X] :
    IsCompactOperator (restrictCLM (le_of_closure hc) : BddHoloOn S → BddHoloOn S')
/-- Assembled to cocycle level along a chain. -/
theorem isCompactOperator_resZ_UV (T : ShrinkChain X) : IsCompactOperator (resZ T T.res_U_V)
theorem isCompactOperator_tradeCompact (T) : IsCompactOperator (tradeCompact T)  -- comp_clm
```

### 4.5 `TradeBounded.lean` (`[T2Space X] [CompactSpace X]`; `D = 0` throughout)

```lean
/-- Bounded cocycle ⇒ germ cocycle on the level cover. -/
noncomputable def toGermZ1 (T) (P) (hP : level-to-cover glue) : NZ1 T P →ₗ[ℂ] Z1 0 (T.coverOf P)
/-- Traded germ cocycle ⇒ bounded cocycle one level down. -/
noncomputable def boundZ1 … : Z1 0 T.coverStar →ₗ[ℂ] NZ1 T T.U   -- via restrictGerm; also Star→V

/-- 14.6(a) upgraded to the Banach layer: the trade projection is onto. -/
theorem tradePi_surjective (T : ShrinkChain X) : Function.Surjective (tradePi T)

/-- The Čech class map and its two properties (Schwartz consumer inputs). -/
noncomputable def classMap (T) : NZ1 T T.V →ₗ[ℂ] H1Cover (0 : Divisor X) T.coverW
theorem classMap_tradeDiff_eq_zero (T) (x : tradeSpace T) :
    classMap T (tradePi T x - tradeCompact T x) = 0
theorem classMap_surjective (T) : Function.Surjective (classMap T)
```

### 4.6 `H1Finite.lean`

```lean
theorem finiteDimensional_h1Cover_W (T : ShrinkChain X) [T2Space X] [CompactSpace X] :
    FiniteDimensional ℂ (H1Cover (0 : Divisor X) T.coverW)
instance finiteDimensional_H1_zero [T2Space X] [CompactSpace X] :
    FiniteDimensional ℂ (H1 (0 : Divisor X))
instance finiteDimensional_H1 [T2Space X] [CompactSpace X] (D : Divisor X) :
    FiniteDimensional ℂ (H1 D)
```

### 4.7 `Chi.lean` (`[T2Space X] [CompactSpace X]`, `[ConnectedSpace X]` where flagged)

```lean
instance finiteDimensional_linSys [ConnectedSpace X] (D : Divisor X) :
    FiniteDimensional ℂ (LinSys D)
noncomputable def h1 (D : Divisor X) : ℕ := Module.finrank ℂ (H1 D)
noncomputable def chi [ConnectedSpace X] (D : Divisor X) : ℤ := (l D : ℤ) - (h1 D : ℤ)

theorem l_mono (h : D ≤ D') : l D ≤ l D'
theorem l_le_l_add_degree (h : D ≤ D') : l D' ≤ l D + ((D' - D).degree).toNat
theorem h1_le_of_le (h : D ≤ D') : h1 D' ≤ h1 D
theorem h1_le_h1_add_degree (h : D ≤ D') : h1 D ≤ h1 D' + ((D' - D).degree).toNat
theorem chi_of_le (h : D ≤ D') : chi D' = chi D + (D' - D).degree      -- the ledger step
theorem chi_single_add (P : X) : chi (D + .single P 1) = chi D + 1     -- convenience form
theorem chi_eq_chi_zero_add_degree (D) : chi D = chi 0 + D.degree      -- sup-trick, §8
/-- Riemann-inequality seed (canonical-forms' workhorse): `χ(0) + deg D ≤ l(D)`. -/
theorem chi_zero_add_degree_le_l (D) : chi 0 + D.degree ≤ (l D : ℤ)
theorem exists_ne_zero_mem_linSys (h : 0 < chi 0 + D.degree) : ∃ f ∈ LinSys D, f ≠ 0
theorem l_pos_of_chi_pos … ; theorem one_le_l_zero …                    -- small corollaries
```

---

## 5. Proof plan A — the norm-bounded trade (Forster 14.6(b) as `tradePi_surjective` + OMT)

This is where the open-mapping step lives. 14.6(b) is never a standalone statement: the
Banach geometry (closed `L`, product completeness) is `Chain.lean`; surjectivity of `π` is
proved here from the *qualitative* trade; the norm constant is then extracted inside
`schwartz_finite_cospan` by `exists_preimage_norm_le`. Detailed plan:

1. **Setup.** `T : ShrinkChain X`. Banach spaces `Z_U := NZ1 T T.U`, `Z_V := NZ1 T T.V`,
   `C_W := NC0 T T.W`; `H := Z_U × Z_V × C_W` — `Prod` normed/complete instances.
   `tradeDefect : H →L NC1 T T.W := res_UW ∘L pr₁ − res_VW ∘L pr₂ − δ_W ∘L pr₃` where
   `res_UW/res_VW` are `resZ`-then-`subtypeL` composites and each `resNC1` is a
   `LinearMap.mkContinuous` with bound 1 (componentwise `restrictCLM`, sup over subset).
   `L := ker tradeDefect`; `IsClosed` by `ContinuousLinearMap.isClosed_ker` (★);
   `CompleteSpace ↥L` by `IsClosed.completeSpace_coe` (★). `π := pr₂ ∘L L.subtypeL`.
2. **Membership unfolding lemma.** `mem_tradeSpace_iff : x ∈ L ↔ ∀ p : Fin n × Fin n,
   ∀ z ∈ W p.1 ⊓ W p.2, (x.1 (p) as fn) z = (x.2.1 p) z + ((x.2.2 p.2) z − (x.2.2 p.1) z)`
   — pointwise form used by both directions below (BCF `ext` + `Pi.ext` + `Prod.ext`).
3. **Germify** `ξ ∈ Z_V`: `c := toGermZ1 T V ξ ∈ Z1 0 T.coverV`. Components
   `MeroGermOn.mk (extendZero (ξ p))`; meromorphy: `ContMDiffOn ω` on the open pair-set
   (carrier witness `g`) ⇒ `MeromorphicOnX` via mero's chart layer; membership in
   `LinSysOn 0` by `mem_linSysOn_iff_of_isOpen` (analytic ⇒ `0 ≤ ord`). Cocycle: `d1`
   components are sums of `restrict (mk …)`; rewrite with `restrict_mk`/`mk`-additivity;
   `mk … = 0` because the pointwise triple identity holds at EVERY point of the open
   triple-meet (NZ1's defining condition) — `mk_eq_mk`/`mk_eq_zero` with everywhere-on-`U`
   agreement (no density argument needed).
4. **Trade** (the dolbeault export, the ONLY analytic import of this file):
   `exists_trade T.good_star (τ := id) T.ref_star_V 0 c` gives `F : Z1 0 T.coverStar`,
   `g : C0 0 T.coverV` with `resZ1 0 id _ F = c + d0 0 T.coverV g` in `Z1 0 T.coverV`.
5. **De-germify with bounds.** `ζ := boundZ1 F ∈ Z_U`: components
   `restrictGerm (closure_pair_subset T i j) (F-component)` — `holoRepr` of the `(i,j)`-germ
   is `ContMDiffOn ω` on `Ustar i ⊓ Ustar j` (mero `holoRepr_contMDiffOn`; `LinSysOn 0` ⇒
   `0 ≤ ord` everywhere there), continuous on the compact
   `closure (U i ⊓ U j) ⊆ closure (U i) ∩ closure (U j) ⊆ Ustar-pair`, bounded by
   `IsCompact.exists_bound_of_continuousOn`, packaged by
   `BoundedContinuousFunction.ofNormedAddCommGroup`. NZ1-condition: pointwise via
   `evalAt`-rigidity from `F`'s germ cocycle (dolbeault §6.2 `repr_cocycle` pattern:
   `evalAt_restrict` + `evalAt_add` with `0 ≤ ord` side conditions discharged by a local
   simp lemma `LinSysOn.ord_nonneg`). Similarly `η ∈ C_W`: components
   `restrictGerm (T.closure_W_subset i) (g i)` — `g i` lives on `V i ⊇ closure (W i)`.
6. **The `L`-membership.** Restrict step 4's germ identity to each `W`-pair and evaluate:
   for `z ∈ W i ⊓ W j`, `holoRepr F (i,j) z = ξ (i,j) z + (holoRepr g j z − holoRepr g i z)`
   — apply `evalAt` at `z` to both sides of the germ equation (linear, `evalAt_restrict`),
   rewrite the three summands with `evalAt_toGerm` (for `ξ`) and
   `evalAt`-of-`holoRepr`-roundtrip (`mk_holoRepr` + `evalAt_mk_of_contMDiffAt`). This is
   exactly `mem_tradeSpace_iff`'s condition for `(ζ, ξ, η)`. Hence
   `x := ⟨(ζ, ξ, η), …⟩ : L` and `π x = ξ`. ∎ (`tradePi_surjective`)
7. **Where 14.6(b)'s constant appears.** Inside `schwartz_finite_cospan (u := tradePi T)`:
   its first step is `(tradePi T).exists_preimage_norm_le tradePi_surjective`, giving
   `C > 0` with: every `ξ` has `x ∈ L`, `π x = ξ`, `‖x‖ ≤ C‖ξ‖`, i.e. **precisely
   Forster's `max(‖ζ‖_{𝔘}, ‖η‖_{𝔚}) ≤ C‖ξ‖_{𝔙}`** (Prod norm = max). We never restate it.
8. **Kernel lemma** (`classMap_tradeDiff_eq_zero`): for `x = (ζ, ξ, η) ∈ L`,
   `π x − v x = ξ − res_UV ζ ∈ Z_V`; its `W`-restriction is `−δ_W η` (step 2 identity,
   rearranged — function level). Apply `toGermZ1` and `d0`-naturality
   (`toGermZ1 ∘ δ_W = d0 ∘ toGermC0`, componentwise `restrict_mk`+`mk`-sub): the germ
   cocycle of `res_VW (π x − v x)` lies in `B1 0 T.coverW`, so `H1Cover.mk … = 0` by
   `H1Cover.mk_eq_zero_iff`. (`classMap := H1Cover.mk ∘ₗ toGermZ1 ∘ₗ res_VW`.)
9. **`classMap_surjective`**: given a class, `H1Cover.mk_surjective` lifts it to
   `c ∈ Z1 0 T.coverW`; trade `c` (again `exists_trade`, now against `T.coverW`, `τ = id`,
   `hτ : IsRefIdx T.coverStar T.coverW id`): `resZ1 F = c + d0 g`. Then
   `ξ_F := boundZ1' F ∈ Z_V` (same construction as step 5, landing at level `V`:
   `closure (V-pair) ⊆ U-pair ⊆ Ustar-pair`), and
   `classMap ξ_F = H1Cover.mk (toGermZ1 (res_VW ξ_F)) = H1Cover.mk (resZ1 F |_W)`
   (bridge roundtrip `toGerm_restrictGerm` + restriction coherence)
   `= H1Cover.mk (c + d0 g) = H1Cover.mk c` (`mk_eq_zero_iff` on the `B1` part). ∎

Risk note: steps 3, 5, 6, 9 are `evalAt/mk/restrict` grind of the exact texture dolbeault
§5–6 budgets for; the mitigations are identical (state every identity at an explicit `W`,
one simp set `[restrict_mk, evalAt_restrict, map_add, map_sub]`, the `LinSysOn.ord_nonneg`
side-condition lemma).

## 6. Proof plan B — the Schwartz endgame

### 6.1 `schwartz_finite_cospan` (Schwartz.lean; the make-or-break, fully planned)

Hypotheses: `u v : E →L[ℂ] F` Banach, `hu : Surjective u`, `hv : IsCompactOperator v`.

1. `obtain ⟨C₀, hC₀, hpre⟩ := u.exists_preimage_norm_le hu`; set `C := max C₀ 1`
   (`hC : 0 < C`, `hC1 : 1 ≤ C`; `hpre` upgrades monotonically).
2. `have hK : IsCompact (closure (v '' closedBall 0 C)) :=
   (isCompactOperator_iff_isCompact_closure_image_closedBall v hC).mp hv`.
3. `obtain ⟨t, hts, htf, htcov⟩ := finite_cover_balls_of_compact hK (by norm_num : (0:ℝ) < 2⁻¹)`
   — `t ⊆ closure (…)`, `t.Finite`, `closure (…) ⊆ ⋃ y ∈ t, ball y 2⁻¹`.
4. `S := Submodule.span ℂ t`; `FiniteDimensional ℂ S := FiniteDimensional.span_of_finite ℂ htf`.
   `R`-bound: `obtain ⟨R, hR⟩ : ∃ R, ∀ y ∈ t, ‖y‖ ≤ R` from `htf` (finite image of `norm`
   is bounded above: `Set.Finite.bddAbove (htf.image _)`).
5. **Single-step lemma** (`private`, stated for this `C t R`):
   `step : ∀ f : F, ∃ (e : E) (s : F), s ∈ S ∧ ‖e‖ ≤ C * ‖f‖ ∧ ‖s‖ ≤ R * ‖f‖ ∧
   ‖f - ((u e - v e) + s)‖ ≤ 2⁻¹ * ‖f‖`.
   Proof: `f = 0`: `⟨0, 0, zero_mem, by simp …⟩`. Else `hf0 : ‖f‖ ≠ 0`:
   `obtain ⟨e, hue, hee⟩ := hpre f`. Normalize `w := ‖f‖⁻¹ • e`:
   `‖w‖ ≤ C` (`norm_smul`, `inv_mul_le_iff`), so
   `v w ∈ v '' closedBall 0 C ⊆ closure … ⊆ ⋃ …` (`subset_closure` then `htcov`):
   `obtain ⟨y, hyt, hy⟩ : ∃ y ∈ t, v w ∈ ball y 2⁻¹`. Set `s := ‖f‖ • y ∈ S`
   (`Submodule.smul_mem`, `Submodule.subset_span hyt`). Compute
   `f - ((u e - v e) + s) = v e - s = ‖f‖ • (v w - y)`
   (`hue` kills `f - u e`; `v e = ‖f‖ • v w` by `map_smul` + `smul_inv_smul₀`).
   Norms: `‖‖f‖ • (v w - y)‖ = ‖f‖ * ‖v w - y‖ ≤ ‖f‖ * 2⁻¹` (`mem_ball` + `dist_eq_norm`,
   commute); `‖s‖ = ‖f‖ * ‖y‖ ≤ R * ‖f‖` (`hR y hyt`); `‖e‖ ≤ C * ‖f‖` is `hee`. ∎
6. `choose e s hsS he hs hrem using step` — three functions `e s : F → E/F` plus bounds;
   `next : F → F := fun f => f - ((u (e f) - v (e f)) + s f)`.
7. Fix `f`. `f_k := next^[k] f`. Decay: `hdecay : ∀ k, ‖f_k‖ ≤ 2⁻¹ ^ k * ‖f‖` by induction
   (`iterate_succ_apply'`, `hrem`, `pow_succ`; mirror `hnle` in mathlib's OMT proof).
8. Summability: `hsum_e : Summable fun k => e (f_k)` — norms `≤ C * (2⁻¹ ^ k * ‖f‖)`
   (`he` + `hdecay`), `Summable.of_norm` + `(summable_geometric_of_lt_one … ).mul_left`
   (idioms verbatim from `exists_preimage_norm_le`'s proof). `a := ∑' k, e (f_k)`.
   Likewise `hsum_s : Summable fun k => s (f_k)`; `σ := ∑' k, s (f_k)`.
9. `σ ∈ S`: partial sums `∑ k ∈ range m, s (f_k) ∈ S` (submodule); `S` closed
   (`Submodule.closed_of_finiteDimensional`); `σ` is the limit of partial sums
   (`hsum_s.hasSum.tendsto_sum_nat`); `IsClosed.mem_of_tendsto` (+ `eventually_of_forall`).
10. Telescope: `htel : ∀ m, ∑ k ∈ range m, ((u (e (f_k)) - v (e (f_k))) + s (f_k))
    = f - f_m` by induction on `m` (`sum_range_succ`, definition of `next`,
    `iterate_succ_apply'`; mirror `fsumeq`).
11. Limits: LHS of `htel` tends to `(u a - v a) + σ`:
    `((u - v).continuous.tendsto _).comp hsum_e.hasSum.tendsto_sum_nat` summed with
    `hsum_s.hasSum.tendsto_sum_nat` via `Tendsto.add`; rewrite
    `∑ (u∘e - v∘e) = u (∑ e) - v (∑ e)` by `map_sum` inside the partial sums FIRST
    (so the limit statement is about images of partial sums — same maneuver as `L₁` in
    the OMT proof). RHS tends to `f - 0`: `hdecay` + `squeeze_zero` +
    `tendsto_pow_atTop_nhds_zero_of_lt_one` (norm_num side goals), `Tendsto.const_sub`.
12. `tendsto_nhds_unique`: `f - (u a - v a) = σ ∈ S`. Provide `⟨S, ‹findim›, fun f => ⟨a f, …⟩⟩`. ∎

Line budget: ~110 incl. the step lemma; every mathlib name above verified at pin (§1) or
lifted from the OMT proof read at source.

### 6.2 `finiteDimensional_of_cospan` (consumer wrapper)

`obtain ⟨S, hS, hspan⟩ := schwartz_finite_cospan u v hu hv`. Claim `range χ = ⊤` is spanned
by `χ '' S`: for `p : P`, `hχ` lifts to `f`, `hspan f` gives `e` with `f − (u e − v e) ∈ S`;
`χ f = χ (f − (u e − v e))` (`hker`, `map_sub`) `∈ Submodule.map χ S`. So
`⊤ ≤ Submodule.map χ S`; `Module.Finite (Submodule.map χ S)` from `hS`
(`Module.Finite.map` / image of fin-dim — if the exact name differs, compose
`S.equivMapOfInjective`-free route: `Module.Finite.of_surjective (χ.comp S.subtype)
(surjective_onto_map)`); conclude `Module.Finite ℂ P` via `Submodule.topEquiv` transfer
(`Module.Finite.equiv`). ~25 lines.

### 6.3 Montel compactness of the restriction (`CompactRestrict.lean`)

`isCompactOperator_restrictCLM` (the design centerpiece #1, single-chart version):
`S' ⋐ S ⊆ source (chartAt ℂ x₀)`, `e := chartAt ℂ x₀`, `Ω := e '' S` (open:
`OpenPartialHomeomorph.isOpen_image_of_subset_source`, the `Forms/Finiteness.lean` `isOpen_O`
pattern), `K := e '' closure S'` (compact: continuous image; `⊆ Ω` by `hc`).
1. `Φ : BddHoloOn S → C(K, ℂ)`, `f ↦ ⟨fun z : K => f-as-function (e.symm z), …⟩`
   (continuity: carrier witness `g` is `ContMDiffOn ω ⊆ ContinuousOn` on `S ⊇ closure S'`,
   composed with `e.symm`'s `ContinuousOn`; membership bookkeeping via
   `e.symm_image_image`-style rewrites on `closure S' ⊆ source`).
2. `hmontel : Φ '' (closedBall 0 r ∩ BddHoloOn S) ⊆ montelFamily Ω K r`: witness
   `g' := g ∘ e.symm` with `DifferentiableOn ℂ g' Ω` — from the carrier's
   `ContMDiffOn 𝓘(ℂ) ω g S` via Surface `contMDiffOn_iff_analyticOnNhd_of_subset_source`
   then `AnalyticOnNhd.differentiableOn`; bound `∀ z ∈ Ω, ‖g' z‖ ≤ r` from BCF
   `norm_coe_le_norm` (values of `g` on `S` are values of `f`); agreement on `K` by
   construction. Hence `closure (Φ '' ball) ⊆ closure (montelFamily Ω K r)` compact
   (`isCompact_closure_montelFamily hΩ hK hKΩ r` — **the BUILT Montel theorem, quoted
   §1.5**), so `IsCompact (closure (Φ '' ball))` (`IsCompact.closure_of_subset` /
   closed-subset-of-compact).
3. `Ψ : C(K, ℂ) →L (↥(S' : Set X) →ᵇ ℂ)`: `(Ψ h) z := h ⟨e z, mem_K⟩` (for `z ∈ S'`,
   `e z ∈ e '' S' ⊆ e '' closure S' = K`); linear, `‖Ψ h‖ ≤ ‖h‖` (`mkContinuous`).
   `Ψ ∘ Φ = val ∘ restrictCLM` pointwise (roundtrip `e.symm (e z) = z` on source).
4. Conclude `IsCompactOperator (restrictCLM …)`: the compact set
   `K₀ := (val)⁻¹ (closure (Ψ '' closure (Φ '' ball)))`-style transfer into the subtype —
   `Ψ` continuous image of the step-2 compact is compact; it contains
   `val '' (restrictCLM '' ball)`; `BddHoloOn S'` is closed, so the trace on the subtype is
   compact (`Subtype.isCompact_iff`, image = that compact set ∩ submodule); then
   `IsCompactOperator` via `isCompactOperator_iff_isCompact_closure_image_closedBall`
   applied in the subtype (closure-in-subtype = trace of ambient closure on a closed set).
   (~35 lines of plumbing; flagged in risks R3.)
5. Cocycle level: `resZ T h = (component-wise restrictCLM)` restricted to `NZ1`;
   `IsCompactOperator` for a finite `Pi` of compacts: image of ball ⊆ product of compacta;
   `isCompact_pi'`/`IsCompact.pi` (finite index) + closed-subset; then restrict to the
   closed submodule `NZ1` as in step 4. Finally
   `tradeCompact = (resZ …) ∘L pr₁ ∘L subtypeL`: `IsCompactOperator.comp_clm` twice. ∎

Note: `montelFamily`'s pair `(i,j)` chart is the chart of `c i` — fixed once in
`ShrinkChain`; no chart transitions ever occur in this file (the target of `Ψ` is X-side).

### 6.4 Chain existence (`Chain.lean`), and 6.5 assembly (`H1Finite.lean`)

`ShrinkChain.nonempty`: per `x : X`, `e := chartAt ℂ x`; `e '' source`-interior radius
`r_x > 0` with `closedBall (e x) r_x ⊆ e.target ∩ e '' source`-side conditions (cech §6.3
`exists_chartDisk_basis` pattern); define the four pullbacks
`P_x(ρ) := e.symm '' ball (e x) ρ` for `ρ = r, r/2, r/4, r/8`; each is open
(`isOpen_image_of_subset_source` on `e.symm`… standard: `= e ⁻¹' ball ∩ source`), is a chart
disk for `ρ = r`, and `closure (P_x(ρ/2)) ⊆ e.symm '' closedBall (e x) (ρ/2) ⊆ P_x(ρ)`
(compact image closed in T2 — cech §6.3 verbatim). `covers_W`: finite subcover of
`{P_x(r_x/8)}` by `isCompact_univ.elim_finite_subcover`; reindex by `Finset.equivFin`
(the `GoodCover.nonempty` packaging, read at source). ~120 lines.

Assembly (`finiteDimensional_h1Cover_W`):
`finiteDimensional_of_cospan (tradePi T) (tradeCompact T) (tradePi_surjective T)
(isCompactOperator_tradeCompact T) (classMap T) (classMap_tradeDiff_eq_zero T)
(classMap_surjective T)`. Then `finiteDimensional_H1_zero`:
`T := (ShrinkChain.nonempty).some`; `toH1 0 T.coverW` is surjective onto `H1 0` — from
dolbeault `toH1_surjective_of_isGood T.good_star` (Leray at `coverStar`) plus
`toH1_resH1` along `IsRefIdx coverStar coverW id`: `range (toH1 coverStar) ⊆
range (toH1 coverW)`; so `H1 0 = range (toH1 coverW)` and
`Module.Finite.of_surjective (toH1 0 T.coverW) …` finishes. ~40 lines.

---

## 7. All-`D` finiteness (`H1Finite.lean`; decision D2 — the CONFIRMED route)

For arbitrary `D`, set `D' := D ⊔ 0` (`h₀ : 0 ≤ D'`, `h : D ≤ D'` — lattice facts on
`Divisor X` = `locallyFinsuppWithin`, mathlib lattice instances per mero).
1. `FiniteDimensional ℂ (H1 D')`: cech `H1Incl_surjective h₀ : Surjective (H1Incl h₀ :
   H1 0 →ₗ H1 D')` + `Module.Finite.of_surjective` + the §6.5 instance.
2. `FiniteDimensional ℂ (H1 D)`: apply `FiniteDimensional.of_linearMap_ker_range` to
   `f := H1Incl h : H1 D →ₗ H1 D'`. Its ker: `exact_windowConnect_H1Incl h` gives
   `ker (H1Incl h) = range (windowConnect h)` (`Function.Exact` ↔ `ker = range`:
   `LinearMap.exact_iff`); `range (windowConnect h)` is fin-dim
   (`Module.Finite.of_surjective` from `Window D D'`, fin-dim by cech's instance,
   onto its range); transfer along the `ker = range` equality. Codomain fin-dim by step 1.
   The helper's proof: `M ⧸ ker f ≃ₗ range f` (`LinearMap.quotKerEquivRange`), `range f`
   fin-dim (submodule of fin-dim), `Module.Finite.equiv`, then
   `Module.Finite.of_submodule_quotient (ker f)`. (Helper spiked ★.)

Why not direct all-`D` norms (the task's suggested default): the twisted cochain spaces do
NOT "have the same shape" at the norm level — sup norms blow up at poles, so the carrier
would need divisor-weighted norms with coherent local equations `z_P^{D(P)}` across chart
overlaps: a new analytic layer strictly larger than the six-term bookkeeping above, which is
5 lemmas of finite linear algebra on ALREADY-DELIVERED cech exports. Dolbeault's §0.2 audit
reached the same conclusion; we implement their recorded recipe verbatim.

## 8. χ ledger (`Chi.lean`)

Base data: `l 0 = 1` (mero `l_zero`, BUILT, `[CompactSpace] [ConnectedSpace]`);
`FiniteDimensional ℂ (LinSys 0)` from `linSys_zero_eq_span_one` +
`FiniteDimensional.span_of_finite` (singleton).

1. `finiteDimensional_linSys D`: `D' := D ⊔ 0`; `LinSys D ≤ LinSys D'` (`linSys_mono`), so
   it suffices for `D'`: apply `FiniteDimensional.of_linearMap_ker_range` to
   `windowMap (h₀ : 0 ≤ D') : LinSys D' →ₗ Window 0 D'` — ker = range of the inclusion
   `LinSys 0 → LinSys D'` (cech `exact_inclusion_windowMap` + `inclusion_injective` ⇒ ker
   ≅ `LinSys 0` fin-dim), codomain `Window 0 D'` fin-dim (cech instance). Submodule of
   fin-dim is fin-dim closes `LinSys D`.
2. **Ledger step** `chi_of_le (h : D ≤ D')`: with all six terms fin-dim, four rank-nullity
   applications on the fragment `0 → L(D) →ⁱ L(D') →^β Window →^δ H1 D →^ι H1 D' → 0`
   (Forster 16.9(b)'s computation, our Window replacing his `ℂ`):
   `l D' = finrank (ker β) + finrank (range β)` and `ker β = range i ≅ L(D)`;
   `finrank (Window D D') = finrank (ker δ) + finrank (range δ)`, `ker δ = range β`;
   `h1 D = finrank (ker ι) + finrank (range ι)`, `ker ι = range δ`;
   `h1 D' = finrank (range ι)` (`H1Incl_surjective h`). Alternating sum + cech
   `finrank_window h : finrank = ((D' − D).degree).toNat` + `Int.toNat_of_nonneg`
   (`degree` monotone/nonneg on `0 ≤ D' − D`; if mero lacks `degree_nonneg`/`degree_sub`,
   file a request and prove in a marked Compat section — 5 lines from `degree` additivity)
   give `chi D' = chi D + (D' − D).degree`. Each rank-nullity instance:
   `LinearMap.finrank_range_add_finrank_ker` + `Submodule.finrank_eq` transfers along the
   `ker = range` equalities (`LinearMap.exact_iff`).
3. `chi_eq_chi_zero_add_degree` — **no induction**: `D' := D ⊔ 0`;
   `chi D' = chi D + (D' − D).degree` (step 2 at `D ≤ D'`) and
   `chi D' = chi 0 + D'.degree` (step 2 at `0 ≤ D'`); subtract, `degree` is additive
   (`map_sub`-style mero lemma): `chi D = chi 0 + D.degree`. `chi_single_add` is the
   specialization `D' := D + single P 1` (needs `degree_single : degree (single P 1) = 1`
   — mero/cech; else Compat).
4. Monotonicity: `l_mono` — `Submodule.finrank_mono` on `linSys_mono` (fin-dim ambient);
   `l_le_l_add_degree` — rank-nullity on `windowMap h` bounding
   `finrank (range) ≤ finrank Window`; `h1_le_of_le` —
   `LinearMap.finrank_le_finrank_of_surjective` on `H1Incl_surjective h`;
   `h1_le_h1_add_degree` — rank-nullity on `ι` + `finrank (ker ι) = finrank (range δ) ≤
   finrank Window`.
5. Riemann seed: `chi_zero_add_degree_le_l D`: `chi D = l D − h1 D ≤ l D` (h1 ≥ 0), rewrite
   by step 3. `exists_ne_zero_mem_linSys`: `0 < chi 0 + deg D ≤ l D` ⇒
   `0 < finrank (LinSys D)` ⇒ `Nontrivial (LinSys D)` (`Module.finrank_pos_iff` needs the
   §8.1 instance) ⇒ element ≠ 0.

## 9. Montel reuse ledger (exact statements consumed from `Jacobian/Forms/Montel.lean`)

- `RS.isCompact_closure_montelFamily (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (C) :
  IsCompact (closure (montelFamily Ω K C))` — §6.3 step 2 (the compact-operator input).
- `RS.montelFamily Ω K C` membership shape `⟨g, hg_diff, hg_bd, hg_agree⟩` — §6.3 step 2
  produces exactly this witness triple from the `BddHoloOn` carrier + Surface bridge.
- `RS.norm_sub_le_of_bounded_of_cthickening_subset`, `RS.norm_deriv_le_of_bounded` — NOT on
  the primary path; consumed only by fallback F2 (ε-net contraction subspace).

## 10. Risks & fallbacks (ranked)

**R1 (MED-HIGH, schedule not math): in-flight upstream drift** — we consume ~25 cech names
(Refinement/Colimit/Window/Skyscraper not yet built) and 2 dolbeault names
(`exists_trade`, `toH1_surjective_of_isGood`; `Leray.lean` not yet built). Mitigation:
(i) `TradeBounded.lean` opens with a 15-line adapter section (`abbrev`/`@[simp]`
restatements) — drift costs one edit; (ii) files 2–5 have no gate; (iii) all consumer-facing
statements are phrased against `H1Cover`/`toH1`, surviving cech's documented colimit
fallback (`H1 := H1Cover 𝒰₀`) with body-only changes. If dolbeault's `exists_trade` shape
drifts (e.g. coboundary sign or `resZ1` coercion), only §5 steps 4/9 change.

**R2 (MED): BCF/submodule/Pi instance stack friction** — norms on `Π p, ↥(BddHoloOn …)`,
`CompleteSpace` propagation, `IsCompactOperator` into subtypes. Mitigation: the spike (§11)
compiled the ker-CLM + `completeSpace_coe` + product + Pi-of-submodules stack. Fallback:
replace Pi-of-subtypes by ONE submodule of the Pi of ambient BCF spaces
(`NC1 := {f : Π p, ↥(pair p) →ᵇ ℂ // ∀ p, f p ∈ BddHoloOn …}` as a `Submodule` of the Pi)
— single subtype layer, all instances by `inferInstance` + one `IsClosed` (finite
intersection of closed component conditions).

**R3 (MED): chart-transport grind in `BddHolo.lean`/`CompactRestrict.lean`** (closedness of
holomorphy under uniform limits; `Φ/Ψ` set bookkeeping on `e''`-images; subtype-compactness
transfer §6.3.4). The lemmas all exist (§1.4/1.5); the risk is volume. Mitigation: both
files are gate-free — start them first, they absorb schedule slack; keep the two
chart-crossing proofs self-contained so nothing else touches charts. No mathematical
fallback needed.

**R4 (LOW-MED): germ-bridge naturality volume** (§5 steps 3/5/6/9) — mero API is BUILT and
already exercised in this pattern by dolbeault's design; the one genuinely new lemma is
`toGerm`-vs-`d0` naturality. Mitigation: the D5 policy (all germ traffic through 3 named
maps) keeps it to ~6 lemmas.

**F1 (fallback for `IsCompactOperator` API pain):** restate `schwartz_finite_cospan` with
hypothesis `IsCompact (closure (v '' closedBall 0 1))` (what the proof actually uses after
step 2) and produce that directly from Montel — bypasses the `IsCompactOperator` iff-lemma
and the subtype transfer §6.3.4 entirely (compactness then only ever lives in the ambient
BCF space).

**F2 (fallback if the abstract cospan lemma stalls — NOT expected):** Forster's literal
14.3+14.7: ε-contraction subspace `A := ⋂ ker (evaluation at δ-net points)` with the
Lipschitz estimate `norm_sub_le_of_bounded_of_cthickening_subset` (BUILT) giving
`‖f‖_{V} ≤ (2δ/δ₀)‖f‖_U` on `A`; then the quotient-norm iteration with
`Submodule.Quotient.normedAddCommGroup [IsClosed A]` (verified present `:429`) and a
continuous finite-dim section (`LinearMap.continuous_of_finiteDimensional`). Strictly more
plumbing (documented here so nobody re-derives the ordering-of-constants trap: choose the
net AFTER the OMT constant, projection bound enters the geometric ratio).

**F3 (χ-ledger gaps):** if mero lacks `degree_sub`/`degree_nonneg`/`degree_single`, prove in
a marked Compat section from `degree`'s definition (finite-support sum) and file
`docs/requests/meromorphic-and-divisors.md`; if cech's `finrank_window` lands with a
different `toNat` orientation, the ledger only needs the `0 ≤ D' − D` case where both agree.

## 11. Spike record (run per protocol; results — honest)

`scratch_finiteness.lean` (project root, 57 lines), gated
(`while [ "$(pgrep -cx lean)" -ge 3 ]; do sleep 30; done; lake env lean scratch_finiteness.lean`):
**SUCCESS, exit 0, zero sorries, no warnings** (~40 s wall, cold imports). Verified by
compilation (★ items in §1):
1. `u.exists_preimage_norm_le hu` — exact invocation at `E →L[ℂ] F`, both `CompleteSpace`.
2. `(isCompactOperator_iff_isCompact_closure_image_closedBall v one_pos).mp hv` and the
   composition chain `(hv.clm_comp g).comp_clm w` — the exact §6.3.5 usage.
3. `finite_cover_balls_of_compact hK (by norm_num : (0:ℝ) < 2⁻¹)`;
   `FiniteDimensional.span_of_finite ℂ htf`; `Submodule.closed_of_finiteDimensional`.
4. The full `tradeSpace` Banach stack: `L := LinearMap.ker (T : (E × F × G) →L[ℂ] G)`,
   `IsClosed` via `ContinuousLinearMap.isClosed_ker`, `CompleteSpace ↥L` via
   `IsClosed.completeSpace_coe`, `π := (fst ∘L snd-juggling) ∘L L.subtypeL` — with the
   nested-`Prod` projection composite written explicitly.
5. `FiniteDimensional.of_linearMap_ker_range` helper proved in 6 lines exactly as §7:
   `quotKerEquivRange` + `Module.Finite.equiv` + `Module.Finite.of_submodule_quotient`
   (instance-argument juggling: provide `Module.Finite ℂ (M ⧸ ker f)` by `haveI` before
   the final call).
6. Pi-of-submodules instances: for `p : Fin 3 → Submodule ℂ (α →ᵇ ℂ)`,
   `NormedAddCommGroup (Π i, ↥(p i))` and `NormedSpace ℂ (Π i, ↥(p i))` resolve by
   `inferInstance`; `CompleteSpace (Π i, ↥(p i))` resolves after
   `haveI := fun i => (hp i).completeSpace_coe`.
Notes for the builder: import list used —
`Analysis.Normed.Operator.Banach`, `Analysis.Normed.Operator.Compact.Basic`,
`Analysis.Normed.Module.FiniteDimension`, `RingTheory.Finiteness.Finsupp`,
`LinearAlgebra.Isomorphisms`, `Topology.ContinuousMap.Bounded.Normed`,
`Data.Complex.Basic`. Keep `scratch_finiteness.lean` as reference.

## 12. Downstream consumption map

- **canonical-forms** (direct dependent): `chi_zero_add_degree_le_l` +
  `exists_ne_zero_mem_linSys` (their "χ(D) → ∞ forces L(D) ≠ 0" — Forster 16.11 pattern
  runs on divisors `n • single P 1` with `degree` linear); `finiteDimensional_linSys`;
  `l_mono`. They own nonconstant-function extraction (`l D ≥ 2` vs constants via `l_zero`).
- **riemann-roch**: `chi_eq_chi_zero_add_degree` (their RR is this plus tail-Serre's
  `h1 D = l (K − D)` and cech-h1-genus's `h1 0 = g` rewriting `chi 0 = 1 − g`); the
  `h1`/`chi` definitions (frozen here: `chi D = l D − h1 D : ℤ`).
- **laurent-tails**: `finiteDimensional_H1 D` (tail-space finiteness transfers through
  their `H¹(D) ≅ T[D]/im α`), `h1`, `h1_le_of_le`, the fragment-side dimension counts.
- **cech-h1-genus**: `finiteDimensional_H1 0`, `h1`, ledger monotonicity.
- **dolbeault-comparison**: `finiteDimensional_H1_zero` discharges the hypothesis of their
  `finiteDimensional_H01`.
- **serre-duality-cech**: `finiteDimensional_H1 D` (pairing nondegeneracy is dimension
  counting).
- Nobody consumes `BddHoloOn`/`ShrinkChain`/`schwartz_finite_cospan` downstream — the whole
  norm layer is internal; only §4.6/§4.7 names are public API. (Exception: `Schwartz.lean`
  is project-generic Banach material; if another unit ever needs it, it can move up.)

## 13. Conventions / CC conformance

- CC8 consumed as frozen (all statements via `H1Cover`/`toH1`/fragment names). CC3's
  `l D` reused verbatim (no re-definition; `chi` is the first definition of χ in the
  project — recorded here as the frozen shape `(l D : ℤ) − (h1 D : ℤ)`).
- No `axiom`, no vacuous instances; the `FiniteDimensional` instances are honest theorems.
  `sorry`-free bar per CONVENTIONS; root file registers in `Jacobian.lean`;
  `scripts/check.sh Jacobian/Finiteness` gates DONE; ≤1 lake job; targeted imports only
  (NO `import Mathlib`).
- Deviations flagged for orchestrator: (i) sup-norm/BCF carrier instead of Forster's `L²`
  (§0 D-a — strictly less mathlib-missing machinery); (ii) the Schwartz endgame is the
  abstract cospan lemma, replacing Forster 14.3/14.5/14.7 and eliminating Hilbert-specific
  steps (§0 D-b); (iii) all-`D` via the fragment, not twisted norms (D2, matches both
  Forster's own architecture and dolbeault's §0.2 note). None of these change any exported
  statement shape.
