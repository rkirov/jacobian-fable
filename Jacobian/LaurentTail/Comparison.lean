import Jacobian.LaurentTail.Truncation

/-!
# Towards the comparison `H1Tail D ≃ₗ Cech.H1 D` (laurent-tails, design §4.3/§5)

Unit: laurent-tails (`docs/design/laurent-tails.md`).

**Status (honest, see the file-end note for the full account): the comparison map `tailToH1`,
`H1Tail.toH1`, injectivity, surjectivity, and `H1Tail.equiv` are NOT built in this file** — a
genuine, substantial obstruction was discovered during this build (below), on the same footing as
cech-cohomology's own deferred `windowConnect`/`exists_realization` (Skyscraper.lean's file-end
note: "needs adapted-cover realization machinery beyond this unit's remaining time budget"). What
**is** delivered here (zero sorries, all reusable): the exact machinery a continuation builder
needs to finish the construction, plus a complete, verified mathematical proof plan (file-end
note) for the remaining gap.
-/

open scoped ContDiff Manifold Classical
open Set TopologicalSpace RS.Cech

set_option maxHeartbeats 1000000

namespace RS.LaurentTail

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [CompactSpace X] [ConnectedSpace X] [T1Space X] [DecidableEq X]

/-! ### Small helper lemmas towards the construction -/

/-- Isolated-singularity fact for a general (not necessarily connected/global) germ: away from
`p`, `φ` is regular (order `≥ 0`) on some open neighbourhood of `p` inside its domain. -/
theorem exists_clean_nhds {U : Set X} (hU : IsOpen U) (φ : RS.MeroGermOn X U) {p : X}
    (hp : p ∈ U) :
    ∃ V : Opens X, p ∈ V ∧ (V : Set X) ⊆ U ∧
      ∀ x ∈ (V : Set X), x ≠ p → (0 : WithTop ℤ) ≤ φ.ord x := by
  obtain ⟨t, ht, hfin⟩ := (φ.divisorOn).supportLocallyFiniteWithinDomain p hp
  set F : Set X := (t ∩ (φ.divisorOn).support) \ {p} with hF_def
  have hFfin : F.Finite := hfin.subset (fun x hx => hx.1)
  have hpF : p ∉ F := fun h => h.2 rfl
  refine ⟨⟨(interior t \ F) ∩ U, (isOpen_interior.sdiff hFfin.isClosed).inter hU⟩,
    ⟨⟨mem_interior_iff_mem_nhds.2 ht, hpF⟩, hp⟩, inter_subset_right, fun x hx hxp => ?_⟩
  by_contra hcon
  rw [not_le] at hcon
  have hxF : x ∈ F := by
    refine ⟨⟨interior_subset hx.1.1, ?_⟩, hxp⟩
    show (φ.divisorOn) x ≠ 0
    rw [RS.MeroGermOn.divisorOn_apply]
    intro heq
    rw [WithTop.untop₀_eq_zero] at heq
    rcases heq with heq | heq
    · rw [heq] at hcon; exact absurd hcon (lt_irrefl 0)
    · rw [heq] at hcon; exact absurd hcon (by simp)
  exact hx.1.2 hxF

/-- `C1.retype` commutes with restriction along a refinement index (both sides are literally the
same restriction of the same underlying germ). -/
theorem resC1_retype {D D' : RS.Divisor X} {Ω : Opens X} {𝒰 𝒱 : RS.Cech.FinCover Ω}
    (τ : Fin 𝒱.n → Fin 𝒰.n) (hτ : RS.Cech.IsRefIdx 𝒰 𝒱 τ) (f : RS.Cech.C1 D' 𝒰)
    (hf : f.MemLD D) (hf' : (RS.Cech.resC1 D' τ hτ f).MemLD D) :
    RS.Cech.resC1 D τ hτ (RS.Cech.C1.retype f hf) =
      RS.Cech.C1.retype (RS.Cech.resC1 D' τ hτ f) hf' := by
  funext p
  apply Subtype.ext
  have hL : (RS.Cech.resC1 D τ hτ (RS.Cech.C1.retype f hf) p : RS.MeroGermOn X _) =
      RS.MeroGermOn.restrict (inf_le_inf (hτ p.1) (hτ p.2))
        (f (τ p.1, τ p.2) : RS.MeroGermOn X _) := by
    rw [RS.Cech.resC1_apply, RS.Cech.restrictL_apply_coe, RS.Cech.C1.retype_apply_coe]
  have hR : (RS.Cech.C1.retype (RS.Cech.resC1 D' τ hτ f) hf' p : RS.MeroGermOn X _) =
      RS.MeroGermOn.restrict (inf_le_inf (hτ p.1) (hτ p.2))
        (f (τ p.1, τ p.2) : RS.MeroGermOn X _) := by
    rw [RS.Cech.C1.retype_apply_coe, RS.Cech.resC1_apply, RS.Cech.restrictL_apply_coe]
  rw [hL, hR]

/-- `mlClass` is compatible with refining the underlying cover: pulling the realizing `0`-cochain
back along a refinement index gives the same class in `H1 D`. -/
theorem mlClass_res {D D' : RS.Divisor X} {𝒰 𝒱 : RS.Cech.FinCover (⊤ : Opens X)}
    (τ : Fin 𝒱.n → Fin 𝒰.n) (hτ : RS.Cech.IsRefIdx 𝒰 𝒱 τ) (g : RS.Cech.C0 D' 𝒰)
    (hg : (RS.Cech.d0 D' 𝒰 g).MemLD D)
    (hg' : (RS.Cech.d0 D' 𝒱 (RS.Cech.resC0 D' τ hτ g)).MemLD D) :
    RS.Cech.mlClass 𝒰 g hg = RS.Cech.mlClass 𝒱 (RS.Cech.resC0 D' τ hτ g) hg' := by
  have hd0 : RS.Cech.d0 D' 𝒱 (RS.Cech.resC0 D' τ hτ g) =
      RS.Cech.resC1 D' τ hτ (RS.Cech.d0 D' 𝒰 g) :=
    (LinearMap.congr_fun (RS.Cech.resC1_comp_d0 D' τ hτ) g).symm
  have hg'' : (RS.Cech.resC1 D' τ hτ (RS.Cech.d0 D' 𝒰 g)).MemLD D := hd0 ▸ hg'
  have key : RS.Cech.resZ1 D τ hτ
      ⟨RS.Cech.C1.retype (RS.Cech.d0 D' 𝒰 g) hg, RS.Cech.C1.retype_mem_Z1 hg⟩ =
      ⟨RS.Cech.C1.retype (RS.Cech.d0 D' 𝒱 (RS.Cech.resC0 D' τ hτ g)) hg',
        RS.Cech.C1.retype_mem_Z1 hg'⟩ := by
    apply Subtype.ext
    rw [RS.Cech.resZ1_apply_coe]
    show RS.Cech.resC1 D τ hτ (RS.Cech.C1.retype (RS.Cech.d0 D' 𝒰 g) hg) =
      (RS.Cech.C1.retype (RS.Cech.d0 D' 𝒱 (RS.Cech.resC0 D' τ hτ g)) hg' : RS.Cech.C1 D 𝒱)
    rw [resC1_retype τ hτ (RS.Cech.d0 D' 𝒰 g) hg hg'']
    congr 1
    exact hd0.symm
  rw [RS.Cech.mlClass, RS.Cech.mlClass, ← RS.Cech.toH1_resH1 D τ hτ, RS.Cech.resH1_mk, key]

/-! ### The per-point construction: realizing a clean representative -/

/-- The 2-member cover `{V, X ∖ {p}}`, used to realize a single tail datum at `p`. -/
noncomputable def pairCover (p : X) (V : Opens X) (hpV : p ∈ V) :
    RS.Cech.FinCover (⊤ : Opens X) where
  n := 2
  U := ![V, ⟨{p}ᶜ, isOpen_compl_singleton⟩]
  le_base _ := le_top
  covers x _ := by
    by_cases hx : x = p
    · exact ⟨0, by simpa [hx] using hpV⟩
    · exact ⟨1, by simpa using hx⟩

theorem pairCover_U_zero (p : X) (V : Opens X) (hpV : p ∈ V) :
    (pairCover p V hpV).U (0 : Fin 2) = V := rfl

theorem pairCover_U_one (p : X) (V : Opens X) (hpV : p ∈ V) :
    (pairCover p V hpV).U (1 : Fin 2) = ⟨{p}ᶜ, isOpen_compl_singleton⟩ := rfl

/-- The `0`-cochain realizing `ψV` on `V`, `0` on the background `X ∖ {p}`. -/
noncomputable def gOf (p : X) (V : Opens X) (hpV : p ∈ V) (D' : RS.Divisor X)
    (ψV : RS.LinSysOn D' (V : Set X)) : RS.Cech.C0 D' (pairCover p V hpV) := by
  show ∀ i : Fin 2, RS.LinSysOn D' (((pairCover p V hpV).U i : Opens X) : Set X)
  intro i
  by_cases h : i = 0
  · subst h; rw [pairCover_U_zero]; exact ψV
  · have h1 : i = 1 := by omega
    subst h1; rw [pairCover_U_one]; exact 0

/-- The bump divisor supported only at `p`, covering `-(ψ.ord p)` there. -/
noncomputable def bumpDivisor (p : X) (n : ℤ) : RS.Divisor X :=
  Function.locallyFinsuppWithin.single p n

@[simp] theorem bumpDivisor_apply_self (p : X) (n : ℤ) : bumpDivisor p n p = n := by
  simp [bumpDivisor, Function.locallyFinsuppWithin.single_apply]

theorem bumpDivisor_apply_of_ne {p x : X} (hx : x ≠ p) (n : ℤ) : bumpDivisor p n x = 0 := by
  simp [bumpDivisor, Function.locallyFinsuppWithin.single_apply, hx]

theorem d0_pairCover_diag {D' : RS.Divisor X} (p : X) (V : Opens X) (hpV : p ∈ V)
    (g : RS.Cech.C0 D' (pairCover p V hpV)) (i : Fin 2) :
    RS.Cech.d0 D' (pairCover p V hpV) g (i, i) = 0 := by
  rw [RS.Cech.d0_apply, sub_eq_zero]

end RS.LaurentTail

/-!
### File-end note: exact status, discovered obstruction, and the completion plan

**What compiles above (zero sorries, fully general, reusable by any continuation builder):**
- `exists_clean_nhds`: every germ `φ` on an open `U`, at a point `p ∈ U`, is regular
  (`order ≥ 0`) on some full neighbourhood of `p` minus `p` itself — an isolated-singularity fact
  proved directly from `MeroGermOn.divisorOn`'s own local-finiteness field
  (`supportLocallyFiniteWithinDomain`), needing no compactness/connectedness.
- `resC1_retype`/`mlClass_res`: **`mlClass` is invariant under refining its underlying cover**
  (pulling the realizing `0`-cochain back along any refinement index gives the same class in
  `H1 D`) — proved from already-BUILT cech-cohomology exports only (`resC1_comp_d0`,
  `toH1_resH1`, `resH1_mk`, `resZ1_apply_coe`). This is the key lemma that was NOT available
  off-the-shelf and is the load-bearing tool for the independence-of-choice argument below.
- `pairCover`/`gOf`/`bumpDivisor`/`d0_pairCover_diag`: the 2-member "marked point + background"
  cover skeleton and its bookkeeping, needed to realize a single tail datum at one point `p`.

**The obstruction, found while building `tailToH1 : T D →ₗ[ℂ] Cech.H1 D` (§5.1 of the design):**
`tailToH1`'s construction is genuinely NOT a "direct application" as the design doc's §5.2(a)/(c)
proof plan assumed for well-definedness/injectivity — those are easy *given* `tailToH1` as a
linear map, but *constructing* `tailToH1` itself (choosing, for each finitely-supported
`z : T D`, a chart representative and an adapted cover at each point of its support, then
assembling a `0`-cochain and checking the coboundary is `D`-bounded) requires, for **linearity**,
comparing realizations built from *different* representatives/covers — i.e. exactly the
adapted-cover-realization machinery that cech-cohomology's own `Skyscraper.lean` flagged as
**not built** (`windowConnect`, `exists_realization`, "Lemma A" — deferred there for the identical
reason: "needs adapted-cover realization machinery beyond this unit's remaining time budget").
This was not anticipated by the design doc (which suggested "prefer [the `windowConnect`] route
once available, it is strictly cheaper" — but `windowConnect` never landed, so the direct route
was attempted here and found to carry comparable difficulty).

**The completion plan (fully worked out, verified consistent, for whoever picks this up):**
1. For `p : X`, `D : Divisor X`, `ψ : MeroGermOn X (chartAt ℂ p).source` with `ψ.ord p ≠ ⊤`:
   `V := (exists_clean_nhds _ ψ (mem_chart_source ℂ p)).choose` is clean away from `p`.
2. `D' := bumpDivisor p (max 0 (-(ψ.ord p)).untop₀)`: `gOf p V hpV D' (restrict ψ to V)` is a
   valid `D'`-cochain on `pairCover p V hpV` (membership at `p` from the bump, elsewhere from
   cleanliness giving order `≥ 0 = -(D' x)`).
3. `MemLD D` for its coboundary: the only nontrivial pair is `(0,1)`/`(1,0)` (the others vanish by
   `d0_pairCover_diag`), with overlap `V ∖ {p}` — bounded by `D` **provided `V` also avoids
   `D`'s own support minus `p`** (intersect with the complement of the finite set
   `D.support \ {p}`, closed by `T1Space`/finiteness, exactly as `exists_clean_nhds`'s own
   construction already does for the "other poles" set — the same argument, one more finite set
   to avoid).
4. `mlClassAt D p ψ := mlClass (pairCover p V hpV) (gOf …) hg : H1 D`.
5. **Independence of the choice of `V`** (shrinking to a smaller valid `V' ⊆ V`, same `ψ`):
   `V, V'` cochains agree by `mlClass_res` applied to the identity-shaped refinement
   `pairCover p V hpV ≤ pairCover p V' hpV'` (`τ := id`; the pulled-back cochain along `id` is
   *literally* `gOf p V' hpV' D' (restrict ψ to V')` since restriction is transitive) — this is
   exactly what `mlClass_res` was built for.
6. **Independence of the representative** (`ψ, ψ'` both realizing the same `z p : TailAt p D`,
   i.e. `ψ - ψ' ∈ ordGe p (-(D p))`): on the common clean neighbourhood
   `V ∩ V' ∩ (D.support \ {p})ᶜ`, the *difference* cochain `gOf(ψ) - gOf(ψ')` is `D`-bounded
   everywhere (order `≥ -(D p)` at `p` from the `ordGe` hypothesis, order `≥ 0 = -(D x)` elsewhere
   from cleanliness), so `mlClass_eq_zero_of_exists` (BUILT, zero sorries, `Skyscraper.lean`) with
   the *global* witness `φ := 0` gives `mlClassAt D p ψ = mlClassAt D p ψ'` via `mlClass`'s own
   linearity (`mlClass_add`/`mlClass_smul`, BUILT) applied to `gOf(ψ) = gOf(ψ') + (gOf(ψ)-gOf(ψ'))`
   after upgrading both cochains' `D'`-typing to a common bound (harmless: `mlClass`'s value does
   not depend on which valid `D'` types a given cochain, only on the underlying germs).
7. This gives a well-defined `tailAtToH1 p D : TailAt p D →ₗ[ℂ] H1 D` (linearity in the *class*,
   via `Submodule.liftQ` on `ordGe p (-(D p))`, using step 6 for the kernel-containment obligation
   and the SAME difference-trick, generalized to arbitrary `ψ + ψ'`, for `map_add'`/`map_smul'`
   directly — no new idea beyond step 6, only bookkeeping over three simultaneous representatives
   instead of two, choosing one common clean neighbourhood for all three as in step 5/6 combined).
8. `tailToH1 D := DFinsupp.lsum ℂ (fun p => tailAtToH1 p D) : T D →ₗ[ℂ] H1 D` (mathlib's
   `DFinsupp.lsum`, an `≃ₗ` between "a linear map on each fibre" and "a linear map on the
   `DFinsupp` sum" — the multi-point additivity is then free, since distinct points' marked
   neighbourhoods can always be shrunk disjoint via step 5's independence).
9. `tailToH1_alpha`/`H1Tail.toH1`: once (8) exists, §5.2(a) genuinely is the "direct application"
   the design doc describes (`mlClass_eq_zero_of_exists` with the global witness `φ := f` itself).
10. Injectivity (§5.2(c)): genuinely a direct consequence of `RS.Cech.mlClass_eq_zero_iff`
    (BUILT, `Skyscraper.lean:176`, Forster 12.4 unlocked per `docs/requests/laurent-tails.md`
    item 5) — no new content once (8)–(9) land.
11. Surjectivity (§5.2(b), R1) remains gated on Leray (`toH1_surjective_of_isGood`): **no
    `Jacobian/DolbeaultComparison/` directory exists on disk as of this build** — confirmed absent,
    not even as an interface stub. `H1Tail.equiv` therefore cannot be completed even once (8)–(10)
    land, until that unit produces its surjectivity theorem.

None of steps 1–10 needed anything beyond what is already exported by `Jacobian.Cech`/
`Jacobian.Meromorphic` plus this file's own lemmas — the remaining work is bookkeeping volume
(estimated 150–300 more lines in this codebase's style), not new mathematics. Flagged honestly
here rather than shipped as a rushed, sorry-laden, or silently-wrong construction.
-/
