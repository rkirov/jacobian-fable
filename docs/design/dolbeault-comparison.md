# Design: dolbeault-comparison (`Jacobian/DolbeaultComparison/`)

Blueprint unit **dolbeault-comparison** — the PDE-free bridge (routing decision #3). Delivers:

1. **Leray's theorem** (Forster 12.8) for good covers: `toH1_surjective_of_isGood` — the
   interface the cech design recorded in its `Colimit.lean` docstring and assigned to us —
   plus the cover-level corollaries `resH1_surjective_of_isGood` and
   `h1CoverEquiv : H1Cover D 𝒰 ≃ₗ[ℂ] H1 D` for good `𝒰`;
2. the **cocycle-trade lemma** (qualitative Forster 14.6(a)) at the `Z1`-level — the exact
   surjectivity input to finiteness-and-chi's Schwartz argument;
3. the **Dolbeault comparison** `H¹(X, 𝒪) ≅ H^{0,1}(X)` (Forster 15.14(a)) at `D = 0`:
   `H01 X := Form01 X ⧸ range dbar`, the Čech→Dolbeault map by PoU splitting, injectivity
   (CR bridge), surjectivity (chart-disk ∂̄-solvability + ML gluing), packaged as
   `dolbeaultEquiv : H1 (0 : Divisor X) ≃ₗ[ℂ] H01 X`, with the finiteness-transfer corollary.

NO Weyl lemma, NO elliptic regularity, NO harmonic theory anywhere (blueprint ⚠ honored: the
only PDE consumed is dbar-solvability's disk lemma, already built into its disk-acyclicity
deliverable and `exists_dbar_solution_chart_ball`).

References: Forster §12 (Leray 12.8 proof read at book 101–102 = PDF 107–108; 12.6 at
PDF 107), §14 (finiteness consumption audit, book 109–118 = PDF 115–124, esp. 14.6–14.10 =
PDF 118–121), §15 (Dolbeault 15.13–15.14 = PDF 130–131). Substrates (AUTHORITATIVE designs,
quoted verbatim in §4/§6): `docs/design/cech-cohomology.md` §4, `docs/design/dbar-solvability.md`
§4, `docs/design/meromorphic-and-divisors.md` (unit BUILT — names verified against source),
`Jacobian/Surface/RealSmooth.lean` (BUILT — `RS.exists_smoothPartitionOfUnity` verified at
source, quoted in §1.3).

---

## 0. Routing findings (read first — the "make-or-break" audit)

### 0.1 The TRUE minimal interface consumed by finiteness-and-chi

Forster §14 was re-read line by line (PDF 115–124). **The finiteness proof never uses the
comparison isomorphism `H¹ ≅ H^{0,1}`, and never mentions `H^{0,1}` at all.** Its structure:

- **Lemma 14.6(a)** (qualitative): for nested cover families `𝔚 ≪ 𝔘` (members chart disks),
  every `ξ ∈ Z¹(𝔚, 𝒪)` can be traded: `∃ ζ ∈ Z¹(𝔘, 𝒪), ∃ η ∈ C⁰(𝔚, 𝒪), ζ|𝔚 = ξ + δη`.
  Forster proves this by PoU-splitting + disk-∂̄. **The L²-norm bound in 14.6(b) is NOT an
  analytic input**: it follows from part (a) by the open mapping theorem on the closed
  subspace `L = {(ζ, ξ, η) : ζ = ξ + δη}` — that Banach-space step belongs to
  finiteness-and-chi, not to us.
- **14.7** (Schwartz iteration) and **14.9/14.10** (Leray 12.8 + disk vanishing 13.4 to
  identify cover-level `H¹` with `H¹(X)`).

Moreover, on our colimit `H1` the qualitative 14.6(a) is a **corollary of Leray surjectivity
plus cech's `toH1_injective`** (proof: `c ∈ H1Cover D 𝒲`; `toH1 𝒲 c ∈ H1 D = range (toH1 𝒰)`
by Leray for good `𝒰`; `toH1 𝒲 (resH1 c') = toH1 𝒰 c' = toH1 𝒲 c` and `toH1 𝒲` injective ⇒
`resH1 c' = c`; unfold `H1Cover`-classes to get the `Z1`-level trade). We nevertheless prove
the trade *constructively first* (it IS the Leray engine, §6.1) and derive Leray from it, so
both exports are available and neither depends on the comparison files.

**Therefore the TRUE minimal interface finiteness-and-chi consumes from this unit is:**

```
exists_trade                      -- Z1-level Forster 14.6(a), Schwartz surjectivity input
resH1_surjective_of_isGood        -- same statement at H1Cover level
toH1_surjective_of_isGood         -- Leray (the interface cech recorded for us)
h1CoverEquiv                      -- H1Cover D 𝒰 ≃ₗ[ℂ] H1 D for good 𝒰 (dim transfer)
```

None of these mention `Form01`/`dbar`/`H01`. They live in `Leray.lean`, which imports the
cech + dbar(DiskAcyclic) + mero units but NOT our comparison files. **Build `Leray.lean`
first; finiteness-and-chi is unblocked the moment it compiles**, independent of the
comparison. The comparison `H1 0 ≃ H01 X` is the blueprint's named deliverable and the
finiteness-transfer bridge TO `H^{0,1}` for any later consumer; it is built after.

### 0.2 D-twisting decision: comparison at `D = 0` ONLY

- Forster proves 14.6–14.10 for `𝒪` only; `H¹(𝒪_D)`-finiteness for all `D` follows from
  `dim H¹(0) < ∞` plus cech's six-term fragment, with NO further input from us:
  for arbitrary `D`, set `D' := D ⊔ 0`; then `dim H1 D' ≤ dim H1 0` (cech
  `H1Incl_surjective` for `0 ≤ D'`), and by exactness at `H1 D`
  (`exact_windowConnect_H1Incl` + `finrank_window`)
  `dim H1 D ≤ dim (Window D D') + dim H1 D' < ∞`. This assembly belongs to
  finiteness-and-chi; we record it here so nobody asks for a twisted comparison.
- A `D`-twisted `H^{0,1}` is also *impossible to reach by the smooth-splitting route*
  (cochains with poles cannot be PoU-split smoothly), confirming the scope.
- **`Leray.lean` IS stated for arbitrary `D`** — its proof is sheaf-axiom generic and dbar's
  disk acyclicity is already divisor-twisted (`subsingleton_h1Cover_of_isChartDisk … D`).
  This matches the cech-recorded signature `toH1_surjective_of_isGood … (D)` exactly — no
  drift.
- Nothing downstream needs an `Ω`-sheaf (1-form) Dolbeault comparison: Serre duality is
  routed through Miranda tails (routing decision #1), and the residue functional's
  integration atom is residue-theorem/serre-duality-cech business. Explicit non-goal.

### 0.3 "Existence of Leray covers" gap check

cech owns and exports: `exists_good_refinement` (good covers cofinal, `[CompactSpace X]`),
`exists_good_refinement_closure` (nested compact-closure good refinement — the
finiteness-and-chi shrinking input), `exists_rep_good`. **No gap remains**; we add only the
3-line convenience `exists_goodCover : ∃ 𝒰 : FinCover (⊤ : Opens X), 𝒰.IsGood`
(= `exists_good_refinement` applied to `FinCover.single ⊤`) used by our surjectivity proof.

---

## 1. Verified mathlib facts (file:line at the pin; §9 spike compiled the starred ones)

### 1.1 Maximal atlas & restricted charts (`Geometry/Manifold/HasGroupoid.lean`, `IsManifold/Basic.lean`)

- `IsManifold.maximalAtlas I n M := (contDiffGroupoid n I).maximalAtlas M`
  (`IsManifold/Basic.lean:876`), `IsManifold.chart_mem_maximalAtlas` (`:886`),
  `mem_maximalAtlas_iff` (`:879`, `rfl`).
- `instance : ClosedUnderRestriction (contDiffGroupoid n I)` (`IsManifold/Basic.lean:765`,
  any `n : ℕ∞ω` incl. `ω`).
- ★ `restr_mem_maximalAtlas [ClosedUnderRestriction G] (he : e ∈ G.maximalAtlas M)
  (hs : IsOpen s) : e.restr s ∈ G.maximalAtlas M` (`HasGroupoid.lean:185`) — fires as
  `restr_mem_maximalAtlas _ (IsManifold.chart_mem_maximalAtlas x) hs` at `𝓘(ℂ) ω` (spiked).
- ★ `OpenPartialHomeomorph.restr_source' (s) (hs : IsOpen s) : (e.restr s).source =
  e.source ∩ s` (`Topology/OpenPartialHomeomorph/IsImage.lean:248`).

### 1.2 Partition of unity (`Geometry/Manifold/PartitionOfUnity.lean`)

- `SmoothPartitionOfUnity ι I M s` (`:122`): `toFun : ι → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯`, `nonneg`
  (`:147`), `sum_eq_one (hx : x ∈ s) : ∑ᶠ i, f i x = 1` (`:150`), `IsSubordinate f U :=
  ∀ i, tsupport (f i) ⊆ U i` (`:270`).
- `SmoothPartitionOfUnity.contMDiff_smul (hg : ∀ x ∈ tsupport (f i), ContMDiffAt … g x)`
  (`:181`) — global version; our splitting needs the `On`-variant, hand-assembled from ★
  `ContMDiffAt.smul` (`Geometry/Manifold/Algebra/SMul.lean:128`; the
  `ContMDiffSMul 𝓘(ℝ) 𝓘(ℝ,ℂ) ∞ ℝ ℂ` instance resolves — spiked at model `𝓘(ℝ, ℂ)`) and ★
  `ContMDiffAt.congr_of_eventuallyEq` with `contMDiffAt_const` (extension-by-zero, spiked).
- ★ `finsum_eq_sum_of_fintype` (to_additive of `finprod_eq_prod_of_fintype`,
  `Algebra/BigOperators/Finprod.lean:438`) — collapses `∑ᶠ` to `∑` over `Fin n` (spiked).
- ★ Subordination vanishing: `x ∉ U i → p i x = 0` via `subset_tsupport` (spiked shape).

### 1.3 Project substrates (BUILT units, verified at source)

- `Jacobian/Surface/RealSmooth.lean:118–123`:
  `RS.exists_smoothPartitionOfUnity [T2Space X] [CompactSpace X] {ι} (U : ι → Set X)
  (ho : ∀ i, IsOpen (U i)) (hU : univ ⊆ ⋃ i, U i) :
  ∃ p : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) X univ, p.IsSubordinate U`; also
  `contMDiffOn_real_of_holomorphicOn` (`:112`, holomorphic ⇒ real-smooth on opens).
- `Jacobian/Meromorphic/` (all verified at source): `MeroGermOn.ord_mk` (`OrderEval.lean:50`),
  `ord_restrict` (`:54`), `ord_add/mul/neg` (`:70/:84/:91`), `evalAt_add/smul/mul` (`:168–207`),
  `evalAt_restrict` (`:208`), `evalAt_mk_of_contMDiffAt` (`:157`) — **the pointwise
  `holoRepr∘mk` bridge**, `holoRepr` (`:225`), `holoRepr_contMDiffOn` (`:289`), `mk_holoRepr`;
  `LinSysOn (D) (U : Set X) : Submodule ℂ (MeroGermOn X U)` (`LinearSystem.lean:222`),
  `mem_linSysOn_iff_of_isOpen` (`:240`), `restrict_mem_linSysOn` (`:245`);
  `MeroGermOn.exists_glue` (`Gluing.lean:23`), `glue_unique` (`:57`).

### 1.4 In-flight substrate signatures (quoted from AUTHORITATIVE designs; drift risk §8)

From `docs/design/cech-cohomology.md` §4 (quoted verbatim, used as frozen):
`FinCover Ω` (fields `n, U, le_base, covers`), `IsRefIdx`, `chosenRefIdx/‑_spec`,
`FinCover.meet`, `le_meet_left/right`, `IsChartDisk`, `FinCover.IsGood`,
`exists_good_refinement`, `FinCover.single`; `LinSysOn.restrictL`, `restrictL_apply_coe`,
`MeroGermOn.congrSet`, `C0/C1 D 𝒰`, `d0/d1` (+ `d0_apply/d1_apply`), `Z1/B1`, `Z1.rel_res`,
`H1Cover`, `H1Cover.mk(_eq_zero_iff/_surjective)`, `subsingleton_h1Cover_iff`,
`resC0/resC1/resZ1/resH1(_mk)`, `resH1_indep/_id/_comp`, `resH1'`, `resH1'_eq_resH1`,
`H1 D`, `toH1`, `toH1_resH1'/toH1_resH1`, `exists_rep(_good/_refined)`, `toH1_injective`,
`H1.lift(_toH1)`, `H1.induction_on`.
From `docs/design/dbar-solvability.md` §4: `Form01 X` (fields `coeffAt, coeffAt_zero_off,
contDiffOn_coeffAt, compat`), `Form01.ext`, module instances, `coeffAt_add/smul/zero`,
`Form01CoeffData` (fields `chart, mem_maximalAtlas, exists_mem, coeff, contDiffOn, compat`),
`Form01.ofCoeffs`, `Form01.coeffAt_ofCoeffs`; `SmoothC X`, `dbar`, `coeffAt_dbar`,
`IsDbarAt/IsDbarOn`, `isDbarOn_iff_eqOn_coeff`, `isDbarOn_dbar`,
`contMDiffOn_omega_of_isDbarOn_zero`, `contMDiffOn_omega_sub_of_isDbarOn`,
`exists_dbar_solution_chart_ball`, `subsingleton_h1Cover_of_isChartDisk` (+ `…_zero_…` for
`D = 0` without `[T2Space][CompactSpace]`); `wirtingerDbar`, `wirtingerDbar_add/sub/const_mul`,
`wirtingerDbar_eq_zero_of_differentiableAt`, `wirtingerDbar_comp_differentiableAt`,
`contDiffOn_wirtingerDbar`.

---

## 2. Design decisions

### D1 — Two independent halves; Leray first, comparison second

`Leray.lean` (+ its corollaries) uses NO `Form01`, no PoU, no ∂̄-solving — only cech
machinery, mero gluing, and dbar's `subsingleton_h1Cover_of_isChartDisk` as a black box.
It is the finiteness-and-chi unblocker (§0.1) and is written/compiled first. The comparison
files (`GlueForm01`, `Splitting`, `Comparison`) never feed `Leray.lean`; they consume it
(surjectivity uses `exists_goodCover`; the colimit map uses `exists_rep_good` from cech only).

### D2 — The trade lemma is proved by the Leray engine, not by PoU+∂̄

Forster proves 14.6(a) with PoU + disk-∂̄ and 12.8 with member-splitting; on our colimit the
two statements are equivalent (§0.1). We implement the **member-splitting proof once**
(§6.1) and export both statements from it. Rationale: the member-splitting proof works for
all `D` (matching cech's recorded Leray signature), stays germ-valued throughout (no
smooth-function detour, no PoU on `Z1 D` which is impossible for `D ≠ 0`), and its gluing
pattern is the same `exists_glue/glue_unique` discipline cech's 12.4 proof uses — one
skill, two theorems. The PoU+∂̄ computation still exists in this unit, but only where it is
irreplaceable: the comparison map (§6.3).

### D3 — `H01 X` is the naked quotient of dbar's types; no new form theory

```lean
noncomputable def H01 (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : Type _ :=
  Form01 X ⧸ LinearMap.range (dbar (X := X))
```
exactly as dbar's consumption map anticipates ("define `H^{0,1} := Form01 X ⧸
LinearMap.range dbar`"). Instances by `inferInstance` (quotient of a module). No relative
`H^{0,1}`, no `(1,0)` forms, no 2-forms, no twisted variants (§0.2). `Form01`-level facts
we need beyond dbar's exports are exactly two, both provable from dbar's `compat`/`ext`
fields and kept in a marked Compat section (§4.2): `Form01.ext_center` and the glue
constructor `DbarGlueData.form`.

### D4 — One gluing atom (`DbarGlueData`) serves the whole comparison

The reusable "Mittag-Leffler gluing" of the blueprint: local smooth functions with
holomorphic discrepancies on a chart-subordinate cover determine a UNIQUE global `Form01`
solving `∂̄u_i = ω` on each piece. Both directions of the comparison and every
well-definedness lemma reduce to `DbarGlueData.form_unique` (uniqueness via
`Form01.ext_center`) — this is what makes the comparison file short: instead of comparing
PoU choices, splittings, and covers pairwise, every candidate form is compared to THE
glued form of its local-solution data. (§6.2–§6.4.)

### D5 — PoU splitting: signs frozen against cech's `d0`

cech convention: `(d0 g)_{ij} = g_j − g_i` (restricted), cocycle `f_{jk} − f_{ik} + f_{ij} = 0`.
The correct splitting is
```
g_i := ∑ k, ψ_k • repr f (k, i)        -- component (k, i), NOT (i, k)!
```
(`repr f p := holoRepr (f p)`, extended by junk-0 off the pair-meet; `ψ` a PoU subordinate
to the cover). Then on `U i ⊓ U j`:
`g_j − g_i = ∑ₖ ψ_k • (repr f (k,j) − repr f (k,i)) = ∑ₖ ψ_k • repr f (i,j) = repr f (i,j)`,
using the cocycle at the triple `(k, i, j)`: `f_{ij} − f_{kj} + f_{ki} = 0` ⇒
`f_{kj} − f_{ki} = f_{ij}` pointwise (via `evalAt` rigidity), and `ψ_k x = 0` for `x ∉ U k`
(subordination) makes the identity hold term-by-term everywhere on `U i ⊓ U j`. The task
hint's `g_i := ∑ ψ_k f_ik` has the wrong sign for cech's conventions — frozen HERE so the
builder does not re-derive it. Forster 12.6 (PDF 107) uses the mirror convention
(`c_ij = f_i − f_j`); do not copy his signs.

### D6 — Instance hygiene, namespaces, imports

`variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]`
throughout; `[T2Space X] [CompactSpace X]` added exactly where used (Leray/trade: both,
inherited from dbar's twist + PoU/`exists_good_refinement`; `GlueForm01.lean`: neither;
`Splitting/Comparison`: both). `[ConnectedSpace X]` nowhere. Everything in `namespace RS`;
Leray internals in `namespace RS.Cech` (they are cech-vocabulary lemmas), comparison
internals in `RS.Dolb`. Imports: project `Jacobian.Cech`, `Jacobian.Dbar`,
`Jacobian.Meromorphic`, `Jacobian.Surface` roots (or the specific files if roots drag);
mathlib additions beyond the substrates' own: none (spike imports
`Geometry.Manifold.PartitionOfUnity` and `Geometry.Manifold.Algebra.SMul` — both already in
Surface/Dbar's cone).

---

## 3. File plan (dependency order; estimated sizes)

```
Jacobian/DolbeaultComparison.lean            -- root: imports + 5–15 line API docstring  (~30)
Jacobian/DolbeaultComparison/Leray.lean      -- inducedCover, member splitting, exists_trade,
                                             --   resH1_surjective, toH1_surjective_of_isGood,
                                             --   h1CoverEquiv, exists_goodCover          (~620)
Jacobian/DolbeaultComparison/GlueForm01.lean -- Form01.ext_center [Compat], DbarGlueData,
                                             --   form / isDbarOn_form / form_unique      (~340)
Jacobian/DolbeaultComparison/Splitting.lean  -- repr + pointwise cocycle, smul-extension
                                             --   lemma, SmoothSplitting, exists_,
                                             --   dolbForm + independence lemmas          (~380)
Jacobian/DolbeaultComparison/Comparison.lean -- H01, toDolb, cechToH01, injective,
                                             --   surjective, dolbeaultEquiv, findim      (~450)
```
`Leray.lean` depends on cech (Covers/Cochains/Refinement/Colimit), dbar (DiskAcyclic), mero
(Gluing) — nothing of ours. `GlueForm01 → Splitting → Comparison`; `Comparison` also imports
`Leray` (for `exists_goodCover`; `exists_rep_good` comes from cech). Gate: `Leray.lean` is
DONE-able as soon as cech's `Covers/Cochains/Refinement/Colimit` and dbar's `DiskAcyclic`
land; the comparison files additionally need dbar's `Form01/Operator`.

---

## 4. Exports — exact signatures

Standing variables as in D6; `D : Divisor X`; `𝒰 𝒱 𝒲 : FinCover (⊤ : Opens X)`.

### 4.1 `Leray.lean` (namespace `RS.Cech`)

```lean
/-- The induced cover of a member: `(V ⊓ 𝒱.U α)_α : FinCover V` for `V ≤ ⊤`. -/
def FinCover.induced (𝒱 : FinCover (⊤ : Opens X)) (V : Opens X) : FinCover V
    -- n := 𝒱.n, U := fun α => V ⊓ 𝒱.U α, le_base := inf_le_left, covers from 𝒱.covers
@[simp] theorem induced_n / induced_U

theorem exists_goodCover [T2Space X] [CompactSpace X] :
    ∃ 𝒰 : FinCover (⊤ : Opens X), 𝒰.IsGood

/-- Forster 14.6(a), qualitative (all `D`): cocycles on any refinement of a good cover are,
up to coboundary, restrictions of cocycles on the good cover. THE Schwartz surjectivity
input for finiteness-and-chi. -/
theorem exists_trade [T2Space X] [CompactSpace X] (h𝒰 : 𝒰.IsGood)
    (τ : Fin 𝒱.n → Fin 𝒰.n) (hτ : IsRefIdx 𝒰 𝒱 τ) (D : Divisor X) (f : Z1 D 𝒱) :
    ∃ (F : Z1 D 𝒰) (g : C0 D 𝒱),
      (resZ1 D τ hτ F : C1 D 𝒱) = (f : C1 D 𝒱) + d0 D 𝒱 g

theorem resH1_surjective_of_isGood [T2Space X] [CompactSpace X] (h𝒰 : 𝒰.IsGood)
    (τ : Fin 𝒱.n → Fin 𝒰.n) (hτ : IsRefIdx 𝒰 𝒱 τ) (D : Divisor X) :
    Function.Surjective (resH1 D τ hτ)

/-- LERAY (Forster 12.8 surjectivity half; injectivity is cech's `toH1_injective`).
Discharges the interface recorded in cech's Colimit.lean. -/
theorem toH1_surjective_of_isGood [T2Space X] [CompactSpace X] (h𝒰 : 𝒰.IsGood)
    (D : Divisor X) : Function.Surjective (toH1 D 𝒰)

/-- Cover-level H¹ computes the colimit on good covers — finiteness transfers dimensions
through this. -/
noncomputable def h1CoverEquiv [T2Space X] [CompactSpace X] (h𝒰 : 𝒰.IsGood) (D : Divisor X) :
    H1Cover D 𝒰 ≃ₗ[ℂ] H1 D          -- LinearEquiv.ofBijective (toH1 D 𝒰)
@[simp] theorem h1CoverEquiv_apply (c) : h1CoverEquiv h𝒰 D c = toH1 D 𝒰 c
```

### 4.2 `GlueForm01.lean` (namespace `RS`; no T2/Compact)

```lean
/-- Compat (candidate for upstreaming to dbar): a `Form01` is determined by its
center-coefficients. From the `compat` field applied at `(p, x)` and `Form01.ext`. -/
theorem Form01.ext_center {ω η : Form01 X}
    (h : ∀ x : X, ω.coeffAt x (chartAt ℂ x x) = η.coeffAt x (chartAt ℂ x x)) : ω = η

/-- Local ∂̄-data: smooth local functions, chart-subordinate cover, holomorphic
discrepancies. The single gluing atom of the comparison (D4). -/
structure DbarGlueData (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] where
  n : ℕ
  V : Fin n → Opens X
  covers : ∀ x : X, ∃ i, x ∈ V i
  center : Fin n → X
  subChart : ∀ i, (V i : Set X) ⊆ (chartAt ℂ (center i)).source
  u : Fin n → X → ℂ
  smoothOn : ∀ i, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (u i) (V i)
  holoSub : ∀ i j, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (u i - u j) ↑(V i ⊓ V j)

/-- The glued global (0,1)-form: `ω|V i = ∂̄(u i)`. -/
noncomputable def DbarGlueData.form (d : DbarGlueData X) : Form01 X
theorem DbarGlueData.isDbarOn_form (d : DbarGlueData X) (i) : IsDbarOn (d.u i) d.form (d.V i)
/-- Uniqueness — every well-definedness question of the comparison reduces to this. -/
theorem DbarGlueData.form_unique (d : DbarGlueData X) {ω : Form01 X}
    (h : ∀ i, IsDbarOn (d.u i) ω (d.V i)) : ω = d.form
```

### 4.3 `Splitting.lean` (namespace `RS.Dolb`; `[T2Space X] [CompactSpace X]` from `exists_smoothSplitting` on)

```lean
/-- Pointwise holomorphic representatives of a `D = 0` cocycle. -/
noncomputable def Z1.repr (f : Z1 (0 : Divisor X) 𝒰) (p : Fin 𝒰.n × Fin 𝒰.n) : X → ℂ
    -- := MeroGermOn.holoRepr (f.1 p)
theorem Z1.repr_contMDiffOn (f) (p) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (Z1.repr f p) ↑(𝒰.U p.1 ⊓ 𝒰.U p.2)
/-- Pointwise cocycle identity (via `evalAt` rigidity; same pattern as dbar DiskAcyclic §7.4(a)3). -/
theorem Z1.repr_cocycle (f) {a b c : Fin 𝒰.n} {x : X} (hx : x ∈ 𝒰.U a ⊓ 𝒰.U b ⊓ 𝒰.U c) :
    Z1.repr f (b, c) x - Z1.repr f (a, c) x + Z1.repr f (a, b) x = 0
theorem Z1.repr_add / Z1.repr_smul   -- pointwise ON the pair-meet (evalAt_add/smul)

/-- Extension-by-zero workhorse: `ψ` smooth with `tsupport ψ ⊆ W`, `F` smooth on `W ⊓ U`
⇒ `fun x => ψ x • F x` is smooth on `U` (values off `W ⊓ U` are junk-irrelevant:
the statement fixes the function `fun x => ψ x • F x` with `F` total-but-junk). -/
theorem contMDiffOn_smul_of_tsupport_subset {ψ : X → ℝ} {F : X → ℂ} {W U : Opens X}
    (hψ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ ψ) (hsupp : tsupport ψ ⊆ W)
    (hF : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ F ↑(W ⊓ U))
    (hz : ∀ x ∈ U, x ∉ W → ψ x = 0)     -- from hsupp; kept for direct use
    : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun x => ψ x • F x) U

/-- A smooth splitting of a cocycle (Forster 12.6 output). -/
structure SmoothSplitting (𝒰 : FinCover (⊤ : Opens X)) (f : Z1 (0 : Divisor X) 𝒰) where
  g : Fin 𝒰.n → X → ℂ
  smoothOn : ∀ i, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (g i) ↑(𝒰.U i)
  split : ∀ i j, ∀ x ∈ 𝒰.U i ⊓ 𝒰.U j, Z1.repr f (i, j) x = g j x - g i x

theorem exists_smoothSplitting [T2Space X] [CompactSpace X] (f : Z1 0 𝒰) :
    Nonempty (SmoothSplitting 𝒰 f)      -- D5 formula; PoU from RS.exists_smoothPartitionOfUnity

/-- The glue data of a splitting on a GOOD cover, and its form. -/
noncomputable def SmoothSplitting.glueData (h𝒰 : 𝒰.IsGood) (s : SmoothSplitting 𝒰 f) :
    DbarGlueData X                       -- V := 𝒰.U, u := s.g; holoSub from split + repr
noncomputable def dolbForm (h𝒰 : 𝒰.IsGood) (f : Z1 0 𝒰) : Form01 X
    -- := ((exists_smoothSplitting f).some.glueData h𝒰).form

/-- Independence of the splitting, at the range-dbar level. -/
theorem sub_mem_range_dbar_of_splittings (h𝒰) {f} (s s' : SmoothSplitting 𝒰 f) :
    (s.glueData h𝒰).form - (s'.glueData h𝒰).form ∈ LinearMap.range (dbar (X := X))
theorem dolbForm_add_sub_mem / dolbForm_smul_sub_mem   -- ≡-mod-range linearity
theorem dolbForm_mem_range_of_mem_B1 (h𝒰) {f : Z1 0 𝒰} (hf : (f : C1 0 𝒰) ∈ B1 0 𝒰) :
    dolbForm h𝒰 f ∈ LinearMap.range (dbar (X := X))
/-- Refinement compatibility mod range (good-to-good). -/
theorem dolbForm_res_sub_mem (h𝒰 : 𝒰.IsGood) (h𝒱 : 𝒱.IsGood) (τ) (hτ : IsRefIdx 𝒰 𝒱 τ)
    (f : Z1 0 𝒰) : dolbForm h𝒱 (resZ1 0 τ hτ f) - dolbForm h𝒰 f ∈ LinearMap.range dbar
```

### 4.4 `Comparison.lean` (namespace `RS`; `[T2Space X] [CompactSpace X]` where noted)

```lean
noncomputable def H01 (X) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    Type _ := Form01 X ⧸ LinearMap.range (dbar (X := X))
noncomputable instance : AddCommGroup (H01 X) / Module ℂ (H01 X)
noncomputable def H01.mk : Form01 X →ₗ[ℂ] H01 X          -- (range dbar).mkQ
theorem H01.mk_surjective : Function.Surjective (H01.mk (X := X))
theorem H01.mk_eq_zero_iff {ω} : H01.mk ω = 0 ↔ ∃ u : SmoothC X, dbar u = ω
theorem H01.mk_eq_mk_iff {ω η} : H01.mk ω = H01.mk η ↔ ∃ u, dbar u = ω - η

/-- Cover-level Čech→Dolbeault map on a good cover (Forster 15.14(a) forward map). -/
noncomputable def toDolb [T2Space X] [CompactSpace X] (h𝒰 : 𝒰.IsGood) :
    H1Cover (0 : Divisor X) 𝒰 →ₗ[ℂ] H01 X
@[simp] theorem toDolb_mk (h𝒰) (f : Z1 0 𝒰) :
    toDolb h𝒰 (H1Cover.mk 0 𝒰 f) = H01.mk (RS.Dolb.dolbForm h𝒰 f)
theorem toDolb_res (h𝒰 h𝒱 τ hτ) : (toDolb h𝒱) ∘ₗ (resH1 0 τ hτ) = toDolb h𝒰

/-- THE comparison map on the colimit. -/
noncomputable def cechToH01 [T2Space X] [CompactSpace X] : H1 (0 : Divisor X) →ₗ[ℂ] H01 X
@[simp] theorem cechToH01_toH1 [T2Space X] [CompactSpace X] (h𝒰 : 𝒰.IsGood) (c) :
    cechToH01 (toH1 0 𝒰 c) = toDolb h𝒰 c

theorem cechToH01_injective [T2Space X] [CompactSpace X] :
    Function.Injective (cechToH01 (X := X))
theorem cechToH01_surjective [T2Space X] [CompactSpace X] :
    Function.Surjective (cechToH01 (X := X))

/-- DOLBEAULT (Forster 15.14(a), PDE-free): `H¹(X, 𝒪) ≃ H^{0,1}_∂̄(X)`. -/
noncomputable def dolbeaultEquiv [T2Space X] [CompactSpace X] :
    H1 (0 : Divisor X) ≃ₗ[ℂ] H01 X
/-- The blueprint's stated purpose: Čech finiteness transfers to `H^{0,1}`. -/
theorem finiteDimensional_H01 [T2Space X] [CompactSpace X]
    [FiniteDimensional ℂ (H1 (0 : Divisor X))] : FiniteDimensional ℂ (H01 X)
/-- Global ∂̄-solvability criterion (free corollary, for any later consumer): solvable iff
the Čech class of the Leray cocycle of local solutions vanishes. -/
theorem exists_dbar_eq_iff [T2Space X] [CompactSpace X] {ω : Form01 X} {ξ : H1 (0 : Divisor X)}
    (hξ : cechToH01 ξ = H01.mk ω) : (∃ u : SmoothC X, dbar u = ω) ↔ ξ = 0
```

---

## 5. Leray & trade — proof plan (`Leray.lean`; Forster 12.8 transcription, PDF 107–108)

Fix good `𝒰` (members `U i`, chart disks), arbitrary `𝒱` (members `V α`), `τ`, `hτ`,
`f ∈ Z1 D 𝒱`. All germ manipulations follow cech's D6 policy: pointwise `ord`, the
`restrictL` simp set, `congrSet` only where flagged.

1. **Induced cover + induced cocycle.** `𝒱ᵢ := 𝒱.induced (𝒰.U i) : FinCover (𝒰.U i)`.
   `fⁱ ∈ C1 D 𝒱ᵢ`: component `(α,β) := restrictL` of `f (α,β)` along
   `(Uᵢ ⊓ Vα) ⊓ (Uᵢ ⊓ Vβ) ≤ Vα ⊓ Vβ` (`inf_le_of_right_le`-algebra; ONE lattice lemma,
   reused). `fⁱ ∈ Z1 D 𝒱ᵢ`: componentwise, `d1`-components of `fⁱ` are restrictions of
   `d1 f`-components (by `restrictL_restrictL`), hence `0`.
2. **Member splitting (the analytic input, dbar-owned).**
   `subsingleton_h1Cover_of_isChartDisk (h𝒰 i) D 𝒱ᵢ` + cech's `subsingleton_h1Cover_iff`
   give `Z1 D 𝒱ᵢ ≤ B1 D 𝒱ᵢ`: obtain `gⁱ ∈ C0 D 𝒱ᵢ` with `d0 gⁱ = fⁱ`, i.e. restricted to
   the pair-meets `gⁱ_β − gⁱ_α = f_{αβ}`.
3. **Cross-glue.** For fixed `(i,j)`, the family
   `α ↦ (restrict gʲ_α − restrict gⁱ_α) ∈ LinSysOn D ↑(Uᵢ ⊓ Uⱼ ⊓ Vα)` (restrictions along
   the two obvious `≤`'s; membership by `restrict_mem_linSysOn` + submodule closure) is
   compatible on overlaps: the difference of the `(α)`- and `(β)`-pieces restricted to
   `Uᵢ ⊓ Uⱼ ⊓ Vα ⊓ Vβ` equals `(gʲ_α − gʲ_β) − (gⁱ_α − gⁱ_β) = (−f_{αβ}) − (−f_{αβ}) = 0`
   (step-2 identities restricted; pure `restrictL` algebra). `MeroGermOn.exists_glue` over
   `fun α => ↑(Uᵢ ⊓ Uⱼ ⊓ Vα)`; the union is `↑(Uᵢ ⊓ Uⱼ)` (𝒱 covers `⊤`) — transport by
   `MeroGermOn.congrSet` (flagged use #1). Get `F_{ij} ∈ LinSysOn D ↑(Uᵢ ⊓ Uⱼ)` (pointwise
   `ord` via `ord_restrict` at a covering `Vα` per point) with
   `restrict F_{ij} = gʲ_α − gⁱ_α` on each `Uᵢ ⊓ Uⱼ ⊓ Vα`.
4. **`F ∈ Z1 D 𝒰`.** Each `d1`-component restricted to `Uᵢ ⊓ Uⱼ ⊓ Uₖ ⊓ Vα` telescopes to 0
   by step-3's glue property; the sets over `α` cover `Uᵢ ⊓ Uⱼ ⊓ Uₖ`, so `glue_unique`
   (uniqueness half, against the zero germ) kills the component (flagged `congrSet` use #2,
   same union transport).
5. **Comparison on `𝒱`.** `h ∈ C0 D 𝒱`: `h_α := restrictL (le_inf (hτ α) le_rfl) g^{τα}_α`
   (note `Vα ≤ U_{τα} ⊓ Vα` via `le_inf` — NO congrSet needed). On `Vα ⊓ Vβ` (≤ all relevant
   sets): step-3 glue at index `α` gives `(resC1 F)_{αβ} = g^{τβ}_α − g^{τα}_α`; step-2 at
   `i := τβ` gives `f_{αβ} = g^{τβ}_β − g^{τβ}_α`; summing,
   `(resC1 F)_{αβ} + f_{αβ} = g^{τβ}_β − g^{τα}_α = (d0 h)_{αβ}`.
   **FROZEN CONCLUSION: `resC1 F + f = d0 h`, exported with `F' := −F, g := −h` as
   `resZ1 F' = f + d0 (−h)`** — signs verified twice (against Forster PDF 108, whose mirror
   convention `f_i − f_j` explains his cleaner-looking `F − f = δh`).
6. **`resH1_surjective_of_isGood`**: step 5 says `resZ1 F' − f ∈ B1`, so
   `H1Cover.mk (resZ1 F') = H1Cover.mk f` (`H1Cover.mk_eq_zero_iff` on the difference);
   `resH1_mk` finishes. **`toH1_surjective_of_isGood`**: given `ξ`, `exists_rep` gives
   `(𝒲, c)`; push to `𝒱 := 𝒰.meet 𝒲` (`le_meet_right` + `toH1_resH1'`), trade back along
   `le_meet_left`'s index map, push with `toH1_resH1`. **`h1CoverEquiv`** :=
   `LinearEquiv.ofBijective ⟨toH1_injective, toH1_surjective_of_isGood⟩`.
7. **`exists_trade`** is step 5 re-packaged (no H1Cover in the statement).

Grind risk: steps 3–5 are `restrictL`-heavy (same texture as cech's 12.4 proof §6.7). The
mitigation is identical: cech's `Z1.rel_res`-style "state every identity at an explicit
lower bound `W`" discipline + their simp set. Budget: the largest share of this unit.

## 6. Comparison — proof plans

### 6.1 `Form01.ext_center` and `DbarGlueData.form` (GlueForm01.lean)

- `ext_center`: for `z ∈ (chartAt ℂ x).target`, `p := (chartAt ℂ x).symm z ∈ (chartAt ℂ x).source
  ∩ (chartAt ℂ p).source`; dbar's `compat` field applied to the pair `(p, x)` at `z` writes
  `coeffAt x z = conj (deriv τ) * coeffAt p (chartAt ℂ p p)` — the center-value hypothesis
  transports it; `Form01.ext` closes. (Membership `z ∈ chartAt ℂ x '' (source_p ∩ source_x)`
  is direct.)
- `form`: `Form01CoeffData` with `ι := Fin n`, `chart i := (chartAt ℂ (d.center i)).restr
  (d.V i)` — in the maximal atlas by **`restr_mem_maximalAtlas` + `chart_mem_maximalAtlas`**
  (§1.1, spiked ★), sources `= source ∩ V i = V i` (`restr_source'` + `subChart`), covering
  by `d.covers`; `coeff i := wirtingerDbar (d.u i ∘ (chart i).symm)`. `contDiffOn` on targets:
  CC7 chart transport of `smoothOn` (`contMDiffAt_real_iff_contDiffAt` pointwise) then
  `contDiffOn_wirtingerDbar`. `compat`: on overlaps write
  `u j ∘ symm = ((u j − u i) ∘ symm) + (u i ∘ symm)`; the first summand's `wirtingerDbar`
  vanishes (`holoSub` → planar `DifferentiableAt` via Surface `Bridges` →
  `wirtingerDbar_eq_zero_of_differentiableAt`), the second transforms by the (0,1) chain rule
  `wirtingerDbar_comp_differentiableAt` with the analytic transition (`Forms.Analyticity.analyticAt_trans`)
  — exactly the `Form01CoeffData.compat` shape. Then `form := Form01.ofCoeffs`.
- `isDbarOn_form`: at `x ∈ V i`, unfold `IsDbarAt` at the center; `Form01.coeffAt_ofCoeffs`
  (data index `i`, `hx : x ∈ (chart i).source`) + the same chain rule reduce both sides to
  the planar `wirtingerDbar` of `u i` in the data chart. Mechanical.
- `form_unique`: `ext_center`; at `x` pick `i` with `x ∈ V i` (`covers`); both center
  coefficients equal `wirtingerDbar (u i ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)` by the two
  `IsDbarOn` hypotheses (`isDbarOn_form` for one side). ∎

### 6.2 Smooth splitting (Splitting.lean)

`repr_cocycle`: `d1 f = 0` at `(a,b,c)`; apply `evalAt` at `x` with `evalAt_restrict` +
`evalAt_add` (side conditions `0 ≤ ord` from `LinSysOn 0`-membership) — dbar DiskAcyclic
§7.4(a) step 3 is the identical computation on a disk; ours is cover-generic.
`exists_smoothSplitting`: PoU `p` subordinate to `fun i => ↑(𝒰.U i)`
(`RS.exists_smoothPartitionOfUnity`, needs `[T2Space X] [CompactSpace X]`); set
`g i := fun x => ∑ k, p k x • Z1.repr f (k, i) x` (Finset.sum). Smoothness on `U i`:
term-wise `contMDiffOn_smul_of_tsupport_subset` (★-spiked atoms: `ContMDiffAt.smul`,
eventual-zero congruence; `repr` is smooth on the OPEN pair-meet by `repr_contMDiffOn` +
`contMDiffOn_real_of_holomorphicOn`); `split` identity per D5 (frozen signs), with
`finsum_eq_sum_of_fintype` + `p.sum_eq_one` (★) and subordination vanishing (★).
`glueData`: `center/subChart` from unpacking `IsChartDisk (𝒰.U i)` (`chartAt ℂ x₀`-based
by definition — cech D4 formula); `holoSub i j = −repr f (i,j)` on the meet (from `split`),
holomorphic by `repr_contMDiffOn`, negated.

### 6.3 Independence lemmas (Splitting.lean) — everything via `form_unique`

- **Two splittings `s, s'` of the same `f`:** `w := s.g i − s'.g i` agrees across `i` on
  overlaps (both differences equal `repr f (i,j)`), so it defines a global function `w`;
  smooth (locality; covers); `w ∈ SmoothC X`. Claim `form(s) − form(s') = dbar ⟨w⟩`:
  by `form_unique` applied to the data `(u := s.g)` and candidate `ω := form(s') + dbar ⟨w⟩`
  — `IsDbarOn (s.g i) (form s' + dbar w) (U i)` unfolds at centers to
  `wirtingerDbar(s.g i) = wirtingerDbar(s'.g i) + wirtingerDbar(w)` in the chart — additivity
  of `wirtingerDbar` at smooth points (`wirtingerDbar_add`; needs `coeffAt_add` of dbar's
  module instance + `coeffAt_dbar`). (This shape needs a 3-line helper `IsDbarOn.add`:
  `IsDbarOn u ω s → IsDbarOn v η s → IsDbarOn (u + v) (ω + η) s` — Compat here, candidate
  request to dbar.)
- **`f ∈ B1` kills the form:** `f = d0 c`, take the CANONICAL splitting
  `g i := holoRepr (c i)` (split identity: `evalAt` rigidity on `d0_apply`; smooth by
  `holoRepr_contMDiffOn` + real-restriction). Its glue data satisfies `IsDbarOn (g i) 0 (U i)`
  (`wirtingerDbar` of holomorphic = 0), so `form = 0` by `form_unique`; independence
  transfers `dolbForm f ∈ range dbar`.
- **Additivity/smul mod range:** sum of splittings splits the sum (`repr_add` pointwise +
  `Z1` submodule structure); `form(s + s') = form s + form s'` by `form_unique` +
  `IsDbarOn.add`; independence upgrades to `dolbForm (f + f') − dolbForm f − dolbForm f' ∈
  range dbar`. Same for `smul`.
- **Good-to-good refinement:** pull a `𝒰`-splitting back along `τ`
  (`g' k := g (τ k)`; split-identity via mero's `evalAt_restrict` on `resC1`-components —
  `repr (resZ1 f) (k,l) = repr f (τk, τl)` pointwise on `V k ⊓ V l`); the pulled-back data's
  form equals `form(s)` ON THE NOSE (`form_unique`: `IsDbarOn (g (τ k)) (form s) (V k)` by
  antitone restriction of `IsDbarOn`); independence gives the mod-range statement.

### 6.4 Assembly (Comparison.lean)

- `toDolb h𝒰`: raw map `Z1 0 𝒰 → H01 X`, `f ↦ H01.mk (dolbForm h𝒰 f)`; additive/homogeneous
  by §6.3 bullets 3 (differences land in `range dbar = ker H01.mk`); kills
  `(B1).comap Z1.subtype` by bullet 2; descend with `Submodule.liftQ` (cech spiked the
  `mapQ/liftQ` shapes). `toDolb_res` from bullet 4 + `resH1_mk`.
- `cechToH01` via cech's **`H1.lift`**: extend `toDolb` to all covers by classical good
  refinement: `goodRef 𝒱 := (exists_good_refinement 𝒱).choose` with chosen `h𝒱 : 𝒱 ≤ goodRef 𝒱`;
  `toDolbAll 𝒱 := toDolb (goodRef 𝒱) ∘ₗ resH1' (h𝒱)`. The `H1.lift` compatibility obligation
  `toDolbAll 𝒱 (resH1' h ξ) = toDolbAll 𝒰 ξ` reduces, by taking a common good refinement `𝒲`
  of `goodRef 𝒰` and `goodRef 𝒱` (`meet` + `exists_good_refinement`) and rewriting both sides
  with `toDolb_res` + cech's `resH1_comp`/`resH1_indep`/`resH1'_eq_resH1`, to the same
  `toDolb 𝒲 ∘ resH1'(𝒰 ≤ 𝒲)` — pure diagram algebra on cech exports (~80 lines).
  `cechToH01_toH1` for good `𝒰` follows from `toDolb_res` + `toH1`-triangles.
- **Injectivity**: `cechToH01 ξ = 0`; `exists_rep_good` + `H1Cover.mk_surjective` write
  `ξ = toH1 𝒰 (mk f)`, so `H01.mk (dolbForm f) = 0`, i.e. `form(s) = dbar u`. Then
  `b i := MeroGermOn.mk (s.g i − u)` on `U i`: holomorphic by
  `contMDiffOn_omega_sub_of_isDbarOn` (`IsDbarOn (s.g i) (form s)` = `isDbarOn_form`;
  `IsDbarOn u (form s)` = `isDbarOn_dbar` rewritten along `dbar u = form s`, restricted);
  membership `LinSysOn 0` via dbar's `mk_mem_linSysOn_zero` (DiskAcyclic helper — if kept
  `private` there, 5-line Compat from `ord_mk` + planar order nonneg, as dbar §7.4(a)5
  documents). `d0 b = f`: componentwise `restrict_mk` + `mk`-of-pointwise-difference +
  `split` + `mk_holoRepr`. Hence `mk f = 0`, `ξ = 0`.
- **Surjectivity**: given `ω`, `exists_goodCover` gives good `𝒰`; per member unpack
  `IsChartDisk` and apply dbar's `exists_dbar_solution_chart_ball` → `h i` smooth on `U i`,
  `IsDbarOn (h i) ω (U i)`. Set `f_{ij} := MeroGermOn.mk (h j − h i)` — holomorphic on the
  meet (`contMDiffOn_omega_sub_of_isDbarOn`), `∈ LinSysOn 0`; cocycle by `mk`-algebra
  (pointwise telescoping) ⇒ `F ∈ Z1 0 𝒰`. The family `(h i)` is itself a `SmoothSplitting`
  of `F` (split-identity: `repr F (i,j) x = evalAt (mk (h j − h i)) x = h j x − h i x` by
  **`evalAt_mk_of_contMDiffAt`** (§1.3, BUILT) — no density argument needed), whose glue
  data's form is `ω` by `form_unique` (`IsDbarOn (h i) ω` is the construction). So
  `cechToH01 (toH1 𝒰 (mk F)) = H01.mk (dolbForm F) = H01.mk ω` by splitting-independence. ∎
- `dolbeaultEquiv := LinearEquiv.ofBijective cechToH01 ⟨inj, surj⟩`;
  `finiteDimensional_H01` := transfer along the (surjective linear) equiv;
  `exists_dbar_eq_iff` is `H01.mk_eq_zero_iff` + `dolbeaultEquiv`-vanishing.

---

## 7. What this unit does NOT do (owners)

- Disk acyclicity, `Form01`, `dbar`, chart-disk solvability — **dbar-solvability** (consumed).
- `H1`, refinement machinery, `toH1_injective`, six-term fragment, good/adapted cover
  existence — **cech-cohomology** (consumed; we DISCHARGE their recorded Leray interface).
- Montel, Schwartz, the χ ledger, `dim H¹ < ∞` — **finiteness-and-chi** (they consume §0.1's
  list; the open-mapping/Banach step of Forster 14.6(b) is THEIRS).
- Tail model, `T[D]`, principal parts — **laurent-tails**.
- Any `H^{0,1}_D` (twisted) or `Ω`-sheaf Dolbeault comparison, de Rham, harmonic forms —
  nobody (routing decisions #1/#3); explicitly out of scope.

## 8. Risks & fallbacks (the 3 most drift-prone interfaces flagged)

1. **cech cochain/colimit shapes (HIGH-visibility drift risk).** We consume ~30 names from
   an in-flight unit (§1.4 quotes the authoritative list). Most exposed: (a) `Z1 D 𝒰` as a
   `Submodule` with `↑`-coercion into `C1` (our `exists_trade` equates coerced elements);
   (b) `resZ1/resH1` argument order `(D τ hτ)`; (c) `H1.lift`'s exact `hg`-shape. Mitigation:
   `Leray.lean` opens with a 20-line "adapter" section of `abbrev`s/`@[simp]` restatements of
   every cech name we touch — drift then costs one adapter edit, not a proof rewrite.
   Fallback if cech's colimit assembly slips to their documented fallback (`H1 := H1Cover 𝒰₀`):
   our Leray surjectivity + trade survive verbatim (they are cover-level); only
   `toH1_surjective`/`h1CoverEquiv`/`cechToH01` change bodies, not statements.
2. **dbar `Form01CoeffData`/`ofCoeffs`/`IsDbarOn` shapes (MED-HIGH).** The glue atom needs
   restricted charts to be acceptable `Form01CoeffData.chart` entries; verified possible at
   the pin (★ `restr_mem_maximalAtlas`), but the `coeffAt_ofCoeffs` side-condition shapes
   (`hz : z ∈ chartAt x '' (… ∩ …)`) may shift during their build. Mitigation: ALL
   `Form01`-construction plumbing is confined to `GlueForm01.lean` (D4); the rest of the
   comparison sees only `DbarGlueData.form/isDbarOn_form/form_unique`. Fallback: if
   `ofCoeffs` fights restricted charts, build `form` as a raw `Form01` structure literal
   (`coeffAt x := wirtingerDbar ((u (choice x)) ∘ (chartAt ℂ x).symm)` with local-constancy
   the same `compat` computation) — ~60 extra lines, no new mathematics; second fallback:
   file a request to dbar for a `Form01.ofLocalSolutions` constructor.
3. **mero `holoRepr`/`evalAt` rigidity side conditions (MED).** Our pointwise steps
   (`repr_cocycle`, `repr_add`, injectivity's `d0 b = f`, surjectivity's `repr F = h j − h i`)
   lean on `evalAt_add/mul/restrict` hypotheses `(hU) (hx) (0 ≤ ord)`. These are BUILT and
   verified (§1.3) — the risk is only bookkeeping volume of discharging `0 ≤ ord` from
   `LinSysOn 0`-membership each time. Mitigation: one local lemma
   `LinSysOn.ord_nonneg (hφ : φ ∈ LinSysOn 0 U) (hx) : 0 ≤ φ.ord x` + a `simp` set.
4. (LOW) `Leray.lean` `congrSet` transports (two flagged uses, §5 steps 3–4). Fallback per
   cech §9.3: state the glue against `Set`-indexed unions directly (mero's native interface).
5. (LOW) PoU sum plumbing (`∑ᶠ` vs `∑`, subordination) — fully spiked ★.

## 9. Spike record (RESULTS — run and honest)

`scratch_dolb.lean` (project root, 45 lines), run gated
(`while [ "$(pgrep -cx lean)" -ge 3 ]; do sleep 30; done; lake env lean scratch_dolb.lean`):
**SUCCESS, exit 0, first try, zero sorries.** Verified by compilation:
1. `(chartAt ℂ x).restr s ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X` via
   `restr_mem_maximalAtlas _ (IsManifold.chart_mem_maximalAtlas x) hs` — the ONE genuinely
   new mathlib usage of this unit (restricted charts for the glue-data);
   `(chartAt ℂ x).restr_source' s hs : (….restr s).source = source ∩ s`.
2. `SmoothPartitionOfUnity (Fin n) 𝓘(ℝ, ℂ) X univ`: `∑ i, p i x = 1` by
   `finsum_eq_sum_of_fintype ▸ p.sum_eq_one`; subordination vanishing off `U i` via
   `subset_tsupport`; `ContMDiffAt.smul` for `ψ : X → ℝ` against `g : X → ℂ` at model
   `𝓘(ℝ, ℂ)` (the `ContMDiffSMul` instance resolves); extension-by-zero via
   `(contMDiffAt_const).congr_of_eventuallyEq`.
Keep `scratch_dolb.lean` as the builder's reference.

## 10. Per-consumer consumption map

- **finiteness-and-chi** (direct dependent — §0.1 is its TRUE minimal interface):
  `exists_trade` (Schwartz surjectivity input, all `D`, only `D = 0` needed),
  `toH1_surjective_of_isGood`, `resH1_surjective_of_isGood`, `h1CoverEquiv` (dimension
  transfer `dim H1 D = dim H1Cover D 𝒰`). Assembly note recorded for them (§0.2): all-`D`
  finiteness = `D = 0` finiteness + cech's fragment (`H1Incl_surjective`,
  `exact_windowConnect_H1Incl`, `finrank_window`); no twisted comparison exists or is needed.
- **cech-cohomology**: receives the owed `toH1_surjective_of_isGood` (their Colimit.lean
  docstring interface — discharged verbatim, same statement, plus `[T2Space X]` which their
  D9 standing hypotheses allow).
- **canonical-forms**: nothing direct (Forster 14.12-style existence arguments run on
  cech `mlClass` + finiteness's `dim H¹ < ∞`).
- **laurent-tails**: `toH1_surjective_of_isGood`/`h1CoverEquiv` available for representing
  colimit classes on good covers if their `T[D] ↠ H¹(D)` surjectivity wants
  adapted-AND-good representatives (note: an adapted refinement of a good cover need not be
  good; if they need simultaneous good∧adapted covers, that is a 30-line cover-existence
  addition to cech's `Covers.lean` — flagged, not built here). The comparison itself: NOT
  needed by the tail route.
- **serre-duality-cech**: `exists_rep_good` + `h1CoverEquiv` for pairing well-definedness;
  `H01`/`dolbeaultEquiv` available but NOT promised as their route (Miranda tails is the
  frozen routing).
- **Nobody consumes** `H^{0,1}` twisted variants or an `Ω`-comparison (§0.2, §7).

## 11. CC conformance / conventions

- CC8 consumed as frozen by the cech design (colimit `H1`, `toH1`-phrased statements — our
  exports keep all consumer statements `toH1`/`H1Cover`-phrased, surviving cech's documented
  colimit fallback). CC7 consumed via Surface's PoU + real/holomorphic bridges; no new
  `IsManifold` instances, no bundles, no competing module instances (blueprint diamond ⚠
  honored — `H01` is a quotient of dbar's hand-rolled types).
- The blueprint ⚠ (no Weyl/elliptic regularity) is discharged structurally: this design
  contains no Sobolev spaces, no distributions, no regularity theorem — the only PDE fact
  ever invoked is dbar's `exists_dbar_solution_chart_ball`/disk acyclicity.
- `sorry`-free bar per CONVENTIONS; unit root registers in `Jacobian.lean`;
  `scripts/check.sh Jacobian/DolbeaultComparison` gates DONE; ≤1 lake job; targeted imports.
- Naming: `RS` namespace; Čech-side lemmas in `RS.Cech` (they are theorems ABOUT cech's
  types and should read as such downstream); mathlib-style names throughout.
- Deviation to flag for the orchestrator: the blueprint sentence "Mittag-Leffler gluing"
  is realized as `DbarGlueData` (comparison side) and `exists_trade` (Čech side); the
  blueprint's implied "finiteness consumes the comparison" is corrected by the §0.1 audit —
  finiteness consumes only the Čech-side Leray/trade exports. This SHRINKS the critical
  path; nothing downstream loses an interface.
