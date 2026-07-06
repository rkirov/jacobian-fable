# Design: laurent-tails (`Jacobian/LaurentTail/`)

Blueprint unit **laurent-tails**. Blueprint text: "Miranda Ch. VI Laurent-tail calculus: tail
spaces `T[D]`, truncation maps, tail finiteness, and the tail form of Riemann–Roch. Strategy:
present `H¹(D)` concretely as Laurent tails modulo global principal parts; RR becomes a dimension
count of truncations. This concrete model is what makes Serre duality provable." **Builds on**
(blueprint edge): canonical-forms, meromorphic-trace. References: Miranda Ch. VI §2 (PDF 190–197,
Def 2.1, Lemma 2.3, Lemma 2.6); §3 opening context (PDF 197–198); CC8
(`docs/design/core-choices.md`); `docs/design/cech-cohomology.md` (the BUILT substrate);
`docs/design/finiteness-and-chi.md` (the χ ledger we bridge to, not duplicate).

**The unit's mandate (CC8, frozen)**: build Miranda's tail spaces `T[D]` and truncation
`α_D : ℳ X → T[D]` from scratch, form `H¹Tail(D) := T[D]/im(α_D)`, and prove the comparison
`H¹Tail(D) ≃ₗ Cech.H1 D` against the **already independently built** Čech `H¹(D)`
(`RS.Cech.H1`, a directed colimit over finite covers — see `docs/design/cech-cohomology.md`).
This is the reverse of Miranda's own book, where `H¹(D)` is *defined* as the tail cokernel; here
`Cech.H1 D` already exists (and is already consumed by `finiteness-and-chi`'s χ ledger), so the
comparison is a genuine theorem, not bookkeeping.

**Practical consequence for scope**: this unit does **not** need to re-derive finiteness,
Riemann–Roch first form, or the six-term dimension count from scratch — `finiteness-and-chi`
already delivers all three at the `Cech.H1` level (Schwartz/Montel, independent of any tail
model). Our job for that material is to **transport it across the comparison into tail
language**, not reprove it. The one genuinely new mathematical content is the comparison itself
(§5).

---

## 0. Note on the blueprint's "Builds on" edge

The blueprint lists `canonical-forms, meromorphic-trace` as this unit's dependencies. Neither is
needed for the **core deliverable** (tail spaces, `α_D`, the comparison, the RR bridge): those
only touch `Jacobian/Cech/`, `Jacobian/Meromorphic/`, `Jacobian/ResidueCalculus/` — all BUILT.
Concretely:
- `canonical-forms` is itself still only a design doc (`docs/design/canonical-forms.md`; no
  `Jacobian/CanonicalForms/` directory on disk at design time) — it supplies the canonical
  divisor `K` and the meromorphic-1-form type `MForm`, both needed only by **serre-duality-tails**
  (the pairing `Res_ω`), not by us. We consume nothing from it.
- `meromorphic-trace` supplies the argument-principle / fibre-trace machinery for `proper-map-degree`;
  nothing here touches trace/degree at all.

Recommendation to the orchestrator: this edge is likely a blueprint-DAG imprecision (laurent-tails
should really build on `cech-cohomology` + `meromorphic-and-divisors` + `residue-calculus` only,
plus `finiteness-and-chi` for the **bridge** file specifically, §7). File plan below is ordered so
that the tail-space/comparison files (§4.1–4.3) have **zero** dependency on `finiteness-and-chi`
or `canonical-forms`; only `RiemannRoch.lean` (§4.4, the bridge) needs `finiteness-and-chi`'s
exports, and can be built/checked independently once that unit's `Chi.lean` lands (currently
gated on `dolbeault-comparison`, per `Jacobian/Finiteness.lean`'s own honest status note).

---

## 1. Verified substrate (BUILT, read at source — exact names)

### 1.1 `Jacobian/Cech/Window.lean` (cech-cohomology, BUILT, zero sorries)

```lean
noncomputable def ordGe (p : X) (m : ℤ) : Submodule ℂ (RS.MeroGermOn X (chartAt ℂ p).source)
theorem mem_ordGe_iff {p m ψ} : ψ ∈ ordGe p m ↔ (m : WithTop ℤ) ≤ ψ.ord p        -- Iff.rfl
noncomputable def tailGerm (p : X) (m : ℤ) : RS.MeroGermOn X (chartAt ℂ p).source
theorem ord_tailGerm_self (p m) : (tailGerm p m).ord p = (m : WithTop ℤ)
noncomputable def leadCoeff (p : X) (m : ℤ) : ordGe p m →ₗ[ℂ] ℂ

noncomputable abbrev WindowAt (p : X) (d d' : ℤ) : Type _ :=
  ordGe p (-d') ⧸ (ordGe p (-d)).comap (ordGe p (-d')).subtype
noncomputable def WindowAt.mk (p d d') : ordGe p (-d') →ₗ[ℂ] WindowAt p d d'
theorem WindowAt.mk_eq_zero_iff {p d d' ψ} :
    WindowAt.mk p d d' ψ = 0 ↔ ((-d : ℤ) : WithTop ℤ) ≤ (ψ : RS.MeroGermOn X _).ord p

noncomputable def diffSupp (D D' : RS.Divisor X) : Finset X                    -- [T2Space][CompactSpace]
noncomputable abbrev Window (D D' : RS.Divisor X) : Type _ := ∀ q : diffSupp D D', WindowAt q (D q) (D' q)
noncomputable def windowMap {D D'} (_h : D ≤ D') : RS.LinSys D' →ₗ[ℂ] Window D D'
theorem windowMap_eq_zero_iff {D D'} (h : D ≤ D') (φ) : windowMap h φ = 0 ↔ (φ : RS.Mero X) ∈ RS.LinSys D
theorem exact_inclusion_windowMap {D D'} (h : D ≤ D') :
    Function.Exact (Submodule.inclusion (RS.linSys_mono h)) (windowMap h)
```

`finrank_windowAt`/`finrank_window` are **not** in this file yet (recorded gap, `θ`-basis proof
deferred to the concurrent continuation builder per the file-end note) — the design doc's §6.8
proof plan is the reference if we need the dimension count ourselves (we mostly don't; see §7).

### 1.2 `Jacobian/Cech/Skyscraper.lean` (BUILT: the atom; INTERFACE: the fragment)

Proved with zero sorries:
```lean
def C1.MemLD (f : C1 D' 𝒰) (D) : Prop
noncomputable def C1.retype (f : C1 D' 𝒰) (hf : f.MemLD D) : C1 D 𝒰
noncomputable def mlClass (𝒰 : FinCover ⊤) (g : C0 D' 𝒰) (hg : (d0 D' 𝒰 g).MemLD D) : H1 D
theorem mlClass_add / mlClass_smul                       -- linearity (same cover)
theorem H1Incl_mlClass (h : D ≤ D') (g hg) : H1Incl D h (mlClass 𝒰 g hg) = 0
theorem mlClass_eq_zero_of_exists (g : C0 D' 𝒰) (hg) (φ : RS.LinSys D')
    (hφ : ∀ i, ∀ x ∈ 𝒰.U i, (-(D x):WithTop ℤ) ≤ ((g i : MeroGermOn X _) -
      MeroGermOn.restrict (𝒰.le_base i) (φ : MeroGermOn X univ)).ord x) :
    mlClass 𝒰 g hg = 0
```
**This is the exact lemma that discharges our comparison's well-definedness (§5.2(a)).**

Recorded as interface (per the file's own docstring: "not proved here"), being added
**concurrently** by another builder per the task brief — we design against these exact
signatures (`docs/design/cech-cohomology.md` §4.7):
```lean
theorem mlClass_eq_zero_iff (g : C0 D' 𝒰) (hg) :
    mlClass 𝒰 g hg = 0 ↔ ∃ φ : LinSys D', ∀ i, ∀ x ∈ 𝒰.U i,
      (-(D x):WithTop ℤ) ≤ ((g i : MeroGermOn X _) - res_{U i} φ).ord x
def Realizes (𝒰) (g : C0 D' 𝒰) (w : Window D D') : Prop
theorem exists_realization (h : D ≤ D') (w : Window D D') :
    ∃ 𝒰 g hg, Realizes h 𝒰 g w ∧ 𝒰.IsAdapted (diffSupp D D')
noncomputable def windowConnect (h : D ≤ D') : Window D D' →ₗ[ℂ] H1 D
theorem exact_windowMap_windowConnect (h : D ≤ D') : Function.Exact (windowMap h) (windowConnect h)
theorem exact_windowConnect_H1Incl (h : D ≤ D') : Function.Exact (windowConnect h) (H1Incl h)
theorem H1Incl_surjective (h : D ≤ D') : Function.Surjective (H1Incl h)
```

### 1.3 `Jacobian/Cech/Colimit.lean` (BUILT; one export DEFERRED)

```lean
noncomputable abbrev H1 (D : RS.Divisor X) : Type _ := Module.DirectLimit (fun 𝒰 => H1Cover D 𝒰) (fun _ _ h => resH1' D h)
noncomputable def toH1 (𝒰) : H1Cover D 𝒰 →ₗ[ℂ] H1 D
theorem exists_rep (ξ : H1 D) : ∃ 𝒰 c, toH1 D 𝒰 c = ξ
theorem exists_rep_good [CompactSpace X] (ξ) : ∃ 𝒰, 𝒰.IsGood ∧ ∃ c, toH1 D 𝒰 c = ξ
noncomputable def H1Incl (h : D ≤ D') : H1 D →ₗ[ℂ] H1 D'
theorem H1Incl_id / H1Incl_comp
```
**Deferred** (Forster 12.4, per `Refinement.lean`'s and `Colimit.lean`'s own file-end notes):
`resH1_injective` / `toH1_injective` / `toH1_eq_zero_iff` are **not exported** in the currently
built files. Being added concurrently (task brief). Our injectivity proof (§5.2(c)) is gated on
this landing — **this is Risk R1**, see §8.

### 1.4 `Jacobian/Cech/Covers.lean` (BUILT)

```lean
structure FinCover (Ω : Opens X) where n : ℕ; U : Fin n → Opens X; le_base; covers
def FinCover.IsAdapted (𝒰) (S : Finset X) : Prop := ∀ p ∈ S, ∃! i, p ∈ 𝒰.U i
theorem exists_adapted_refinement [T1Space X] (𝒰) (S : Finset X) (O : X → Opens X)
    (hO : ∀ p ∈ S, p ∈ O p) : ∃ 𝒱, 𝒰 ≤ 𝒱 ∧ 𝒱.IsAdapted S ∧ ∀ p ∈ S, ∀ k, p ∈ 𝒱.U k → 𝒱.U k ≤ O p
def IsChartDisk (V : Opens X) : Prop
theorem exists_good_refinement [CompactSpace X] (𝒰) : ∃ 𝒱, 𝒰 ≤ 𝒱 ∧ 𝒱.IsGood
```
**Gap we will need**: a combined "good AND adapted" refinement (§5.2(b), §8 R2) — not currently
exported; small enough to build locally (Compat) by adapting `exists_adapted_refinement`'s own
construction (§6.2 of the cech design doc) with `O p` chosen to be a chart-disk ball at each
marked point, composed with `exists_good_refinement` for the "background" members.

### 1.5 `Jacobian/Meromorphic/` (BUILT, zero sorries)

```lean
def RS.MeroGermOn (U : Set X) : Type _                        -- germ classes, CommRing/Algebra ℂ/Module ℂ
abbrev RS.Mero X : Type _ := MeroGermOn X univ; notation "ℳ" => RS.Mero
noncomputable def MeroGermOn.restrict (h : V ⊆ U) : MeroGermOn X U →ₐ[ℂ] MeroGermOn X V
noncomputable def MeroGermOn.ord (φ : MeroGermOn X U) (x : X) : WithTop ℤ
theorem MeroGermOn.ord_restrict / ord_mul / ord_add / ord_zero / ord_one
noncomputable def LinSys (D : Divisor X) : Submodule ℂ (ℳ X)
theorem mem_linSys_iff {φ D} : φ ∈ LinSys D ↔ ∀ x, (-(D x):WithTop ℤ) ≤ φ.ord x
noncomputable abbrev divisor [T1Space X][IsManifold …] (φ : ℳ X) : Divisor X := φ.divisorOn
theorem divisor_apply (φ x) : divisor φ x = (φ.ord x).untop₀
theorem divisor_inv (φ) : divisor φ⁻¹ = -divisor φ
theorem Mero.ord_ne_top [T1Space X][ConnectedSpace X] {φ ≠ 0} (x) : φ.ord x ≠ ⊤
noncomputable def Divisor.degree : Divisor X → ℤ                            -- [T2Space][CompactSpace]
theorem Function.locallyFinsuppWithin.degree_mono / degree_add / degree_neg
```
`Divisor.single` is **not built yet** (flagged as a gap by `canonical-forms`'s own design doc
§1.6 too) — we need it only for illustrative examples/tests, not the core deliverable; if needed,
build locally in a `Compat` section (one-line `Function.locallyFinsuppWithin` literal, as
`canonical-forms`'s design doc already plans to).

### 1.6 `Jacobian/ResidueCalculus/` (BUILT, planar — NOT reused directly)

`RS.PrincipalPartData U` (`U : Set ℂ`), `RS.laurentCoeffAt`, `RS.principalPartAt` are **planar**
(data indexed by points of `ℂ`, values in `ℤ →₀ ℂ`). As the task brief flags, this is the wrong
shape for an `X`-indexed tail space directly. **We do not reuse `PrincipalPartData` as the
carrier.** Instead (§2) we build the `X`-indexed tail space directly from Cech's `ordGe`
(already a germ-quotient at a point `p : X`, chart-relative) — `PrincipalPartData`'s *role*
(Mittag-Leffler datum: finite tail at finitely many points) is played by our `T D` (§2.2), built
the analogous way but over `X` and reusing the manifold-level germ machinery instead of
re-deriving Laurent coefficients from scratch. We do not need `laurentCoeffAt`/`principalPartAt`
at all: Cech's `leadCoeff`/`tailGerm` already supply the coefficient-level API if a builder later
wants an explicit monomial basis of `TailAt p D` (not needed for the comparison itself).

---

## 2. Core definitional decisions

### D1 — `TailAt p D`: a **direct quotient**, no colimit

Miranda's definition (PDF 191, Def 2.1): a Laurent tail divisor is a finite formal sum
`Σ_p r_p(z_p)·p`, `r_p` a Laurent polynomial (finitely many terms, any degrees); `T[D](X)`
requires, whenever `r_p ≠ 0`, that **the top term of `r_p` has degree strictly less than `−D(p)`**
— **no lower bound** on how negative the bottom degree may go. Read literally, the fibre of
`T[D]` at `p` is `colim_{d'→∞} WindowAt p (D p) d'` (Cech's own finite window, growing without
bound). The key observation (verified by the spike, §9): **every** `ψ : MeroGermOn X (chartAt p).source`
has *some* finite order (`ψ.ord p : WithTop ℤ` — is `⊤` only for the identically-zero germ, else
a genuine integer), hence lies in `ordGe p (-d')` for `d'` large enough. So the increasing union
`⋃_{d'} ordGe p (-d')` is the **whole ambient germ space**, and the colimit collapses to a single
quotient:

```lean
noncomputable def TailAt (p : X) (D : RS.Divisor X) : Type _ :=
  RS.MeroGermOn X (chartAt ℂ p).source ⧸ RS.Cech.ordGe p (-(D p))
```

This *is* `Cech.WindowAt p (D p) d'` for the largest possible `d'` — we make this precise via a
canonical map `WindowAt p (D p) d' →ₗ[ℂ] TailAt p D` for every finite `d'` (§4.1), which the
spike (§9) confirms compiles as `Submodule.mapQ` with hypothesis `le_rfl` (the two submodules are
**literally equal**, not just comparable — `WindowAt`'s defining quotient submodule
`(ordGe p (-(D p))).comap (ordGe p (-d')).subtype` restricted to `ordGe p (-d')` is exactly the
image of `ordGe p (-(D p))` in the ambient space, intersected with `ordGe p (-d')`).

Reusing `ordGe` (rather than re-deriving a germ quotient by hand) means `TailAt` inherits
`AddCommGroup`/`Module ℂ` for free (`Submodule.Quotient` instances) and needs **zero** new
germ-level lemmas — every fact we need about `ord`/`evalAt`/`restrict` transports through the
existing `MeroGermOn` API.

### D2 — `T D`: `DFinsupp`, not `Finsupp`

The fibre type `TailAt p D` genuinely depends on `p` (different chart, different `Divisor` value
`D p`), so the finitely-supported product is a **dependent** finsupp:

```lean
noncomputable abbrev T (D : RS.Divisor X) : Type _ := Π₀ p : X, TailAt p D
```
(`abbrev`, not `def` — matching `Cech.C0/C1/Window/H1`'s own convention, D9 of the cech design
doc — a plain `def` breaks instance search for the `DFunLike`/`AddCommGroup`/`Module ℂ` structure;
confirmed by the spike, §9, which hit exactly this failure mode with a plain `def` and fixed it by
switching to `abbrev`). Needs `[DecidableEq X]`; we discharge it the same way `Cech.FinCover`
does — `open scoped Classical` locally, no global instance (avoids any diamond risk on `X`, which
carries no other `DecidableEq` in this project).

Construction of individual elements mirrors `Cech.Window.diffSupp`'s own pattern: given a
`Finset X` witness `S` and a function on `S`, `DFinsupp.mk S x : T D` (junk `0` off `S`); the
spike (§9) confirms `DFinsupp.mk_apply` unfolds as expected.

### D3 — `α_D`: assemble via `DFinsupp.mk` on a Finset witness, prove linearity pointwise

```lean
noncomputable def alphaFinset (D : RS.Divisor X) (f : ℳ X) : Finset X   -- a witness ⊇ the true "bad" locus
noncomputable def alpha (D : RS.Divisor X) (f : ℳ X) : T D :=
  T.mk D (alphaFinset D f) (fun p => TailAt.mk p D (MeroGermOn.restrict (subset_univ _) f))
```
`TailAt.mk p D ψ = 0 ↔ (-(D p):WithTop ℤ) ≤ ψ.ord p` (from `mem_ordGe_iff` + `Submodule.Quotient.mk_eq_zero`),
and `ord_restrict` gives `(restrict f).ord p = f.ord p`, so the "true" nonzero locus of `α_D f` is
exactly `{p | f.ord p < -(D p)}`. This set is finite: outside `Divisor.support D` (finite,
compactness) it reduces to `{p | f.ord p < 0}` = the genuine pole set of `f`, finite by
`finite_setOf_ord_neg` (`Meromorphic/Divisor.lean`, needs `f ≠ 0`, `[ConnectedSpace X]`); the
`f = 0` case is trivial (`α_D 0 = 0`, empty witness). So `alphaFinset D f := (Divisor.support D
∪ {poles of f}).toFinset`-shaped; the precise construction is a case split on `f = 0` mirroring
`Divisor.sub`'s support bound.

**Linearity is proved pointwise, not via Finset bookkeeping**: since `DFinsupp.mk S x` evaluated
at *any* `p` (not just `p ∈ S`) equals the "intended" value `TailAt.mk p D (restrict f)` (this
value actually *is* `0` off the witness `S`, by construction of `S` ⊇ the true nonzero locus), we
get `alpha D (f+g) p = alpha D f p + alpha D g p` for every `p` — pure linearity of
`TailAt.mk p D ∘ restrict` — hence `alpha D (f+g) = alpha D f + alpha D g` by `DFinsupp.ext`,
**regardless of which Finset witnesses were used for each side**. `alphaL D : ℳ X →ₗ[ℂ] T D`
packages this.

### D4 — `windowToT`: the finite skyscraper embeds in the tail space

For `D ≤ D'`, `Cech.Window D D'` is a finite product over `diffSupp D D'` of `WindowAt q (D q) (D' q)`;
composing pointwise with `windowAt_toTailAt` (D1) and `DFinsupp.mk (diffSupp D D')` assembles

```lean
noncomputable def windowToT (D D' : RS.Divisor X) (_h : D ≤ D') : RS.Cech.Window D D' →ₗ[ℂ] T D
```

This is the bridge that lets us **derive** the tail-level six-term sequence from Cech's own
(§7) instead of re-proving it.

### D5 — `mulTailAt`/`mulTail`: the multiplication action (serre-duality-tails' first ask)

For `h : ℳ X`, `h ≠ 0`, multiplication by (the chart-restriction of) `h` sends
`ordGe p (-(D p))`-cosets to `ordGe p (-(D p) + (divisor h) p)`-cosets (`ord_mul` +
`divisor_apply`, `(divisor h) p = (h.ord p).untop₀` when `h.ord p` is the finite order at `p`),
i.e. a linear map `TailAt p D →ₗ[ℂ] TailAt p (D - divisor h)` via `Submodule.mapQ`. Assembling
pointwise over `T D` uses `DFinsupp.mapRange` (mathlib has `DFinsupp.mapRange.addMonoidHom`, no
`mapRange.linearMap` at the pin — checked; the `ℂ`-linearity of the assembled map is proved
separately via `DFinsupp.ext` + the pointwise `smul_apply` simp lemma, not cited from a
nonexistent name). `mulTailAt h⁻¹` inverts it (`divisor_inv`), giving Miranda's isomorphism
`μ_h : T D ≃ₗ T (D - divisor h)`. Support is preserved (`⊆` the original support — multiplying
the zero tail class by anything is still zero), so no new finiteness argument is needed.

---

## 3. File plan (5 files; dependency order)

```
Jacobian/LaurentTail.lean               -- unit root: imports + API docstring          (~30)
Jacobian/LaurentTail/TailSpace.lean     -- TailAt, windowAt_toTailAt, T D, T.mk,
                                        --   mulTailAt/mulTail (D1/D2/D4/D5)            (~280)
Jacobian/LaurentTail/Truncation.lean    -- alpha/alphaL, ker_alphaL_eq_linSys, H1Tail D  (~180)
Jacobian/LaurentTail/Comparison.lean    -- tailToH1, well-defined descent, surjectivity,
                                        --   injectivity (gated), H1Tail.equiv           (~380)
Jacobian/LaurentTail/RiemannRoch.lean   -- bridge to finiteness-and-chi's χ ledger:
                                        --   g0, h1tail, firstFormRR, SES restatement    (~150)
```
Import spine: `Jacobian.Cech` (root — pulls in `Window`/`Skyscraper`/`Colimit`/`Covers`),
`Jacobian.Meromorphic` (root), `Mathlib.Data.DFinsupp.Module`. `RiemannRoch.lean` additionally
imports `Jacobian.Finiteness` (only once that unit's `Chi.lean` exists — currently gated, see §0;
the other three files have **no** dependency on `finiteness-and-chi` and can be built and checked
today with `scripts/check.sh Jacobian/LaurentTail` restricted to those three).
Namespace: `RS.LaurentTail` (mirrors `RS.Cech`/`RS.Finiteness`'s per-unit sub-namespace
convention); `RS` for anything that could plausibly upstream (none expected here).

---

## 4. Exports — exact signatures

### 4.1 `TailSpace.lean`

```lean
namespace RS.LaurentTail
variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

noncomputable def TailAt (p : X) (D : RS.Divisor X) : Type _ :=
  RS.MeroGermOn X (chartAt ℂ p).source ⧸ RS.Cech.ordGe p (-(D p))
noncomputable instance (p D) : AddCommGroup (TailAt p D)
noncomputable instance (p D) : Module ℂ (TailAt p D)
noncomputable def TailAt.mk (p : X) (D) : RS.MeroGermOn X (chartAt ℂ p).source →ₗ[ℂ] TailAt p D
theorem TailAt.mk_eq_zero_iff {p D} (ψ) :
    TailAt.mk p D ψ = 0 ↔ (-(D p) : WithTop ℤ) ≤ ψ.ord p

noncomputable def windowAt_toTailAt (p : X) (D : RS.Divisor X) (d' : ℤ) :
    RS.Cech.WindowAt p (D p) d' →ₗ[ℂ] TailAt p D
theorem windowAt_toTailAt_mk (p D d') (ψ : RS.Cech.ordGe p (-d')) :
    windowAt_toTailAt p D d' (RS.Cech.WindowAt.mk p (D p) d' ψ) = TailAt.mk p D ψ  -- rfl
/-- Every tail class is *represented* by some finite window (the union-of-`ordGe` fact). -/
theorem exists_windowAt_repr (p : X) (D : RS.Divisor X) (z : TailAt p D) :
    ∃ (d' : ℤ) (ψ : RS.Cech.ordGe p (-d')), windowAt_toTailAt p D d' (RS.Cech.WindowAt.mk p (D p) d' ψ) = z

variable [DecidableEq X]   -- via `open scoped Classical` at use sites, not a global instance
noncomputable abbrev T (D : RS.Divisor X) : Type _ := Π₀ p : X, TailAt p D
noncomputable instance : AddCommGroup (T D)
noncomputable instance : Module ℂ (T D)
noncomputable def T.mk (D : RS.Divisor X) (S : Finset X) (x : ∀ p : (S : Set X), TailAt (p : X) D) : T D
theorem T.mk_apply_mem {D S x p} (hp : p ∈ S) : T.mk D S x p = x ⟨p, hp⟩
theorem T.mk_apply_not_mem {D S x p} (hp : p ∉ S) : T.mk D S x p = 0

variable [CompactSpace X]
noncomputable def windowToT (D D' : RS.Divisor X) (h : D ≤ D') : RS.Cech.Window D D' →ₗ[ℂ] T D
theorem windowToT_apply (D D' h) (w) (q : RS.Cech.diffSupp D D') :
    windowToT D D' h w (q : X) = windowAt_toTailAt q D _ (w q)   -- q ∉ diffSupp ⇒ value 0 (Iff.rfl-ish)

variable [ConnectedSpace X] [T1Space X]
noncomputable def mulTailAt (h : ℳ X) (hh : h ≠ 0) (p : X) (D : RS.Divisor X) :
    TailAt p D →ₗ[ℂ] TailAt p (D - RS.divisor h)
noncomputable def mulTail (h : ℳ X) (hh : h ≠ 0) (D : RS.Divisor X) : T D →ₗ[ℂ] T (D - RS.divisor h)
theorem mulTail_mulTail_inv (h hh D) :
    (mulTail h⁻¹ (inv_ne_zero hh) (D - RS.divisor h)).comp (mulTail h hh D) = LinearMap.id  -- via divisor_inv
noncomputable def mulTailEquiv (h : ℳ X) (hh : h ≠ 0) (D) : T D ≃ₗ[ℂ] T (D - RS.divisor h)
end RS.LaurentTail
```

### 4.2 `Truncation.lean`

```lean
variable [T2Space X] [CompactSpace X] [ConnectedSpace X] [T1Space X] [DecidableEq X]

noncomputable def alphaFinset (D : RS.Divisor X) (f : ℳ X) : Finset X
noncomputable def alpha (D : RS.Divisor X) (f : ℳ X) : T D
theorem alpha_apply_eq_zero_iff (D f p) :
    (alpha D f : T D) p = 0 ↔ (-(D p) : WithTop ℤ) ≤ f.ord p
noncomputable def alphaL (D : RS.Divisor X) : ℳ X →ₗ[ℂ] T D
@[simp] theorem alphaL_apply (D f) : alphaL D f = alpha D f
/-- Miranda PDF 192: `L(D) = ker(α_D)`. -/
theorem ker_alphaL_eq_linSys (D : RS.Divisor X) :
    LinearMap.ker (alphaL D) = (RS.LinSys D).comap (Algebra.linearMap ℂ (ℳ X))  -- or direct on ℳ X, see note
noncomputable def H1Tail (D : RS.Divisor X) : Type _ := T D ⧸ LinearMap.range (alphaL D)
noncomputable instance : AddCommGroup (H1Tail D)
noncomputable instance : Module ℂ (H1Tail D)
noncomputable def H1Tail.mk (D) : T D →ₗ[ℂ] H1Tail D
```
Note on `ker_alphaL_eq_linSys`: `alphaL D : ℳ X →ₗ[ℂ] T D` is a map *out of* `ℳ X` itself (not a
comap from a submodule), so the honest statement is simply
`LinearMap.ker (alphaL D) = (RS.LinSys D : Submodule ℂ (ℳ X))` (both sides are submodules of
`ℳ X`) — the `.comap (Algebra.linearMap …)` phrasing above is a slip; drop it, state directly.
Proof: `f ∈ ker (alphaL D) ↔ ∀ p, alpha D f p = 0 ↔ (by `alpha_apply_eq_zero_iff`) ∀ p,
(-(D p):WithTop ℤ) ≤ f.ord p ↔ (mem_linSys_iff) f ∈ LinSys D`.

### 4.3 `Comparison.lean` — the CC8 deliverable

```lean
variable [T2Space X] [CompactSpace X] [ConnectedSpace X] [T1Space X] [DecidableEq X]

/-- The comparison map, tail data ↦ Mittag-Leffler class (built on an adapted-cover
representative of the finite support, via `mlClass`). -/
noncomputable def tailToH1 (D : RS.Divisor X) : T D →ₗ[ℂ] RS.Cech.H1 D

theorem tailToH1_alpha (D : RS.Divisor X) (f : ℳ X) : tailToH1 D (alphaL D f) = 0
  -- (a): `mlClass_eq_zero_of_exists`, BUILT, zero sorries — done directly.

noncomputable def H1Tail.toH1 (D : RS.Divisor X) : H1Tail D →ₗ[ℂ] RS.Cech.H1 D
  -- descends via `tailToH1_alpha` + `LinearMap.range_le_ker_iff`/`Submodule.liftQ`

theorem H1Tail.toH1_surjective (D : RS.Divisor X) : Function.Surjective (H1Tail.toH1 D)
  -- (b): RISK R1, §8 — needs a good+adapted cover + Leray (`toH1_surjective_of_isGood`,
  -- owned by dolbeault-comparison, upstream/non-circular)

theorem H1Tail.toH1_injective (D : RS.Divisor X) : Function.Injective (H1Tail.toH1 D)
  -- (c): RISK R2 (the flagged 12.4 gap), §8 — needs `Cech.mlClass_eq_zero_iff`'s `⇒` half,
  -- i.e. `toH1_injective`

/-- CC8's mandate. -/
noncomputable def H1Tail.equiv (D : RS.Divisor X) : H1Tail D ≃ₗ[ℂ] RS.Cech.H1 D :=
  LinearEquiv.ofBijective (H1Tail.toH1 D) ⟨H1Tail.toH1_injective D, H1Tail.toH1_surjective D⟩
```

### 4.4 `RiemannRoch.lean` — bridge to the χ ledger, not a re-proof

```lean
variable [T2Space X] [CompactSpace X] [ConnectedSpace X] [T1Space X] [DecidableEq X]

/-- Miranda's `H¹(0)`, tail-language alias for finiteness-and-chi's `h1 0`. -/
noncomputable def g0 : ℕ := RS.Finiteness.h1 (0 : RS.Divisor X)

instance H1Tail.finiteDimensional (D) : FiniteDimensional ℂ (H1Tail D) :=
  Module.Finite.equiv (H1Tail.equiv D).symm    -- transported from `RS.Finiteness.finiteDimensional_H1`

noncomputable def h1tail (D : RS.Divisor X) : ℕ := Module.finrank ℂ (H1Tail D)
theorem h1tail_eq_h1 (D) : h1tail D = RS.Finiteness.h1 D :=
  LinearEquiv.finrank_eq (H1Tail.equiv D)

/-- Miranda Theorem 3.1 (Riemann–Roch, First Form), in tail language. Immediate from
`RS.Finiteness.chi_eq_chi_zero_add_degree` + `RS.l_zero` + unfolding `chi`/`h1tail_eq_h1` — no
new analysis. -/
theorem firstFormRR (D : RS.Divisor X) :
    (RS.l D : ℤ) - (h1tail D : ℤ) = D.degree + 1 - (g0 : ℤ)

/-- The tail-level six-term sequence (Miranda's SES, PDF 193, and Lemma 2.3), obtained by
post-composing cech's own six-term fragment with `(H1Tail.equiv D).symm`/`(H1Tail.equiv D').symm`
— NOT re-proved. -/
theorem exact_windowToT_H1Tail_mk (D D' : RS.Divisor X) (h : D ≤ D') :
    Function.Exact (windowToT D D' h) ((H1Tail.equiv D).symm.toLinearMap ∘ₗ RS.Cech.windowConnect h)
theorem exact_H1Tail_mk_incl (D D' : RS.Divisor X) (h : D ≤ D') :
    Function.Exact ((H1Tail.equiv D).symm.toLinearMap ∘ₗ RS.Cech.windowConnect h)
      ((H1Tail.equiv D').symm.toLinearMap ∘ₗ RS.Cech.H1Incl h ∘ₗ (H1Tail.equiv D).toLinearMap)
```
(The exact statement shape of the last two is cosmetic — the content is "conjugate cech's
six-term fragment by the two `H1Tail.equiv`s"; a builder should feel free to restate it as
`Function.Exact` chains through the equivs however reads cleanest, e.g. via `LinearEquiv.exact_iff`
if that or an equivalent exists at the pin, else by unfolding `Function.Exact` and pushing through
`(equiv).symm.injective`.)

---

## 5. Proof plan — the comparison (§4.3), in detail

### 5.1 Construction of `tailToH1`

Given `z : T D` with (finite) support `S`, for each `p ∈ S` pick a representative germ
`ψ_p : MeroGermOn X (chartAt p).source` with `TailAt.mk p D ψ_p = z p` (`Submodule.Quotient`
always has a representative, `Quotient.out`/`Submodule.Quotient.mk_surjective`). Apply
`Cech.exists_adapted_refinement (FinCover.single ⊤) S O` with `O p := chartAt p .source` (or a
smaller chart-disk neighborhood, matching the pattern already used by
`Skyscraper.lean`'s `exists_realization`, §6.9(c) of the cech design doc) to get an adapted cover
`𝒰`. Build `g : C0 D' 𝒰` (for `D'` chosen with `D' p := max (D p) (-(ψ_p.ord p))` at `p ∈ S`,
`D' = D` elsewhere — always possible since `ψ_p.ord p : WithTop ℤ` is either `⊤` or a genuine
finite integer, so *some* finite bound exists) by: on the unique member containing `p ∈ S`, the
restriction of `ψ_p`; `0` elsewhere. `(d0 D' 𝒰 g).MemLD D` holds because off-diagonal pairs not
touching any `p ∈ S` have both sides `0` (`D = D'` there), and pairs touching a single `p ∈ S`
have `D`-bounded difference by construction of `D'`. Set
`tailToH1 D z := mlClass 𝒰 g hg`. Linearity in `z` (`map_add'`/`map_smul'`) is exactly the content
of Skyscraper's own "Lemma A" pattern (§6.9(d) of the cech design doc,
`mlClass_eq_of_realizes`/`windowConnect`'s own linearity proof) — two realizing constructions for
`z` and `z'` agree after a common adapted refinement, so `tailToH1 D (z + z') = tailToH1 D z +
tailToH1 D z'`. **This is genuinely the same argument Skyscraper.lean already carries out for
`windowConnect`**; once that lands (concurrently), `tailToH1` may be a two-line composite
(`tailToH1 D z := windowConnect h (windowFrom z)` for a suitable finite `D'` bounding `z`,
`h : D ≤ D'`, `windowFrom` the inverse-ish reading of `z` into `Window D D'` via
`exists_windowAt_repr`, §4.1) instead of a from-scratch adapted-cover construction — **prefer
that route once `windowConnect` is available**, it is strictly cheaper and reuses proven
linearity/independence-of-realization lemmas verbatim.

### 5.2 (a) Well-definedness on `H1Tail D` (kills `im α_D`)

For `f : ℳ X`, `alpha D f`'s representative construction (§5.1, with `ψ_p := restrict f` to the
chart source at each `p ∈ support`) is *literally* the hypothesis shape of
`mlClass_eq_zero_of_exists` (§1.2, BUILT): the 0-cochain `g` built from restrictions of the single
global function `f` has `g i - restrict φ` (`φ := f` itself) `= 0` everywhere, in particular
`D`-bounded. So `tailToH1 D (alpha D f) = mlClass 𝒰 g hg = 0` by that lemma directly — **zero new
proof content**, a direct application. `H1Tail.toH1` then descends by `Submodule.liftQ`
(`LinearMap.range (alphaL D) ≤ LinearMap.ker (tailToH1 D)`, exactly `tailToH1_alpha`).

### 5.2 (b) Surjectivity — RISK R1 (the harder of the two gaps)

Given `ξ : Cech.H1 D`, by `exists_rep_good` get a **good** cover `𝒰` with `ξ = toH1 D 𝒰 [f]`,
`f ∈ Z1 D 𝒰`. Refine further to be **also adapted** to `Divisor.support D` (the "good + adapted"
combined refinement flagged as a small gap in §1.4) — call the result `𝒱`, `f' := resZ1(f)`.

The remaining content (genuinely nontrivial, and the reason this is flagged as a risk rather than
a direct citation): on `𝒱`, pairs of members neither of which contains a point of
`Divisor.support D` have `f'`-components that are **honestly holomorphic** (order `≥ 0`
everywhere, since `D = 0` there). To read off *tail data only*, we need these "background"
components to not contribute any obstruction beyond what the marked points already carry — i.e.
we need the *local, planar* fact that a holomorphic cochain on the (chart-disk) overlaps of a good
cover, away from the finitely many marked points, is cohomologous (via a **further** refinement
and a coboundary correction) to one supported entirely at the marked points. This is exactly
**Leray's theorem applied on a good cover** (`toH1_surjective_of_isGood`, owned by
`dolbeault-comparison`) — the standard route: since `𝒱` is good, `toH1 D 𝒱` needs no separate
argument (we already have a representative *on* `𝒱`, that's not the issue); the issue is
*isolating the marked-point contribution*. Concretely: define `g' ∈ C0 D 𝒱` by `0` on every
non-marked member and (a suitable restriction of) `f'`'s own local data on the marked member of
each `p ∈ support D`; the difference `f' - d0(g')`'s off-diagonal components not touching any
marked point are then a **pure-`O`** (unbounded-divisor, `D=0`) cocycle *localized away from all
poles*, and its class in `H1Cover 0 𝒱` is the obstruction Leray/disk-acyclicity resolves (this is
literally the content `dolbeault-comparison`'s Leray proof already builds — we do not re-derive
disk acyclicity, we *cite* the surjectivity conclusion it enables). Read off `z : T D` from `g'`'s
marked-member data via `TailAt.mk`; `tailToH1 D z = ξ` follows from `windowConnect_spec`-style
uniqueness (§6.9(d) of the cech design doc) once the realizing data agree.

**This step is genuinely the unit's hardest piece.** It is **not** circular (Leray/dolbeault-
comparison precedes `laurent-tails` in every valid build order: `dolbeault-comparison` →
`finiteness-and-chi` → `canonical-forms` → `laurent-tails` per the blueprint DAG), but it does mean
`Comparison.lean`'s surjectivity proof has a **soft dependency** on `dolbeault-comparison`'s Leray
theorem landing (even though the *file* need not `import` it if the good+adapted-cover
construction is phrased so the actual Leray citation is isolated to one lemma). Fallback if Leray
isn't conveniently citable in this shape: prove the needed "planar splitting on a two-disk overlap"
fact directly and locally (a Runge/partial-fractions argument on the overlap of two disks in one
chart — genuinely elementary complex analysis, no manifold content) as a `Compat` lemma; flag to
the orchestrator either way once attempted.

### 5.2 (c) Injectivity — RISK R2 (the flagged 12.4 dependency)

Given `z : T D` with `tailToH1 D z = 0`, i.e. `mlClass 𝒰 g hg = 0` for the realizing data of
§5.1. By the **`⇒` direction of `mlClass_eq_zero_iff`** (§1.2, recorded interface, gated on
`toH1_injective`/Forster 12.4 — per the cech design doc's own §6.9(b): "`(⇒) toH1_injective` +
`H1Cover.mk_eq_zero_iff`: `retype (d0 g) = d0 h` for some `h ∈ C0 D 𝒰` **on `𝒰` itself**
(injectivity spares us the refinement!)"), we get `φ : LinSys D'` with `g_i - restrict φ`
`D`-bounded everywhere on `𝒰`. This `φ`, restricted to each chart source at `p ∈ support(z)`, is
exactly a global function realizing `z`'s tail data, i.e. `z = alpha D φ` (reading off
`TailAt.mk p D (restrict φ) = TailAt.mk p D ψ_p = z p` from the `D`-bounded-difference hypothesis
+ `TailAt.mk_eq_zero_iff`). So `z ∈ range (alphaL D)`, hence `H1Tail.mk D z = 0`. **This is a
direct, mechanical consequence of `mlClass_eq_zero_iff`'s `⇒` half — zero new mathematical
content once that lemma lands**, matching exactly how the task brief frames this dependency.

**Do not attempt to prove this independently of `toH1_injective`.** If the concurrent builder's
12.4 proof stalls (per the cech design doc's own risk R4, §9 item 4, "`toH1_injective` is not on
the critical path of `dbar-solvability`/`dolbeault-comparison`" — i.e. it may simply not land on
our schedule), ship `Comparison.lean` with `H1Tail.toH1_injective` stated with an explicit
`(hinj : Function.Injective (RS.Cech.toH1 D 𝒰))`-shaped hypothesis (or, more simply, an explicit
`RS.Cech.mlClass_eq_zero_iff`-shaped hypothesis) parametrizing the gap, and `H1Tail.equiv` as a
conditional corollary — this keeps the file `sorry`-free while being honest about the outstanding
dependency (matches `CONVENTIONS.md` rule 3's "no vacuous instances" — a genuine explicit
hypothesis, not a fake one).

---

## 6. Why not re-derive Miranda's Lemma 2.3/2.4/2.5/2.6 at the tail level

Miranda's own route to finite-dimensionality (PDF 194–196) is: (i) Lemma 2.3, a dimension
*difference* formula for `H¹(D₁/D₂)` (his notation for `ker(H1Incl (D₁≤D₂))`) purely from the
truncation-window degree count; (ii) Lemma 2.4/2.5, a uniform bound `deg(A) - dim L(A) ≤ M` for
*all* divisors `A`, via a nonconstant meromorphic function's pole divisor and the finitely-
generated function-field machinery (his Ch. VI §1, Prop 1.17–1.21); (iii) Lemma 2.6, a maximal
divisor `A₀` (attaining the bound of (ii)) has `H¹(A₀) = 0`.

**We do not need any of (i)-(iii).** `finiteness-and-chi` already proves, independently (via
Schwartz + Montel, no tail model, no function-field machinery):
`FiniteDimensional ℂ (Cech.H1 D)` for every `D`, and the **exact** ledger `chi D = chi 0 + D.degree`
(strictly stronger than Miranda's inequality-based route — an equality, not just a bound). Once
the comparison `H1Tail.equiv` (§5) is in hand, **every** tail-level finiteness/dimension fact is a
one-line transport (`Module.Finite.equiv`, `LinearEquiv.finrank_eq`) — §4.4 does exactly this.
The one place Miranda's own machinery genuinely reappears is inside the comparison's *surjectivity*
proof (§5.2(b)), but there it enters as a **cohomological** ("Leray/disk-acyclicity") fact, not a
dimension-counting one — Miranda's Lemma 2.3-2.6 chain is a different, and for us unnecessary,
route to the same destination.

**Explicit recommendation (matches the task brief's steer)**: derive tail-form RR
(§4.4's `firstFormRR`) and tail finiteness (`H1Tail.finiteDimensional`) from the comparison +
`finiteness-and-chi`'s χ ledger. Do **not** reprove Lemma 2.3/2.4/2.5/2.6 independently at the
tail level — it would be redundant work solving a problem `finiteness-and-chi` already solved
more strongly, and (per the circularity check in §5.2(b)) attempting to use Miranda's *own*
finite-dimensionality route to instead *prove* the comparison's surjectivity would be circular
(Miranda's route implicitly presupposes the tail model already computes `H¹`, which is exactly
what we are trying to establish).

---

## 7. What serre-duality-tails (#25) and its neighbors consume

Per the blueprint, **serre-duality-tails** builds on `laurent-tails, proper-map-degree,
residue-theorem, serre-duality-cech`. From us specifically, it needs:
- `T D`, `TailAt p D`, `alphaL D`, `H1Tail D` — the carrier for its residue pairing
  `Res_ω : T[D](X) → ℂ` (Miranda PDF 199, §3) to be built against; the pairing itself is *their*
  construction (needs `canonical-forms`'s `MForm`/`resAt`, which we do not consume).
- `mulTail`/`mulTailEquiv` (§2 D5) — the multiplication-operator compatibility
  `Res_{fω} = Res_ω ∘ μ_f` (Miranda Lemma 3.6-adjacent) needs our `μ_f` on tails literally.
- `H1Tail.equiv`/`H1Tail.toH1` (§4.3) — to transport their pairing's surjectivity/injectivity
  results back and forth between tail language (where the pairing lives, Miranda's route) and
  `Cech.H1 D` (where `finiteness-and-chi`'s dimension counts live) — this is the crux reason CC8
  demands the comparison at all: **without it, serre-duality-tails would have no way to connect
  the two halves of the make-or-break argument** (dimension counts on one side, the concrete
  pairing on the other).
- `firstFormRR`/`g0`/`h1tail_eq_h1` (§4.4) — direct reuse for their own dimension bookkeeping
  (`h¹(D) = l(K−D)`), avoiding re-deriving the χ ledger.

**cech-h1-genus** (#26) and **riemann-roch** (#27) consume serre-duality-tails, not us, directly
— but both ultimately rely on `firstFormRR`/`g0` being correctly bridged (§4.4), since
`riemann-roch`'s second form is literally first-form RR + Serre duality (`h¹(D) = l(K−D)`)
substituted in. Coordinate with `docs/requests/` if either unit needs an export not listed above.

---

## 8. Risks (honest, ranked)

1. **R1 — comparison surjectivity (§5.2(b)), HIGH.** The genuinely hardest mathematical content
   of this unit. Needs either a citable form of `dolbeault-comparison`'s Leray theorem applied on
   a good+adapted cover, or a bespoke local (planar, two-disk) splitting lemma. Not circular
   (Leray precedes us in the DAG) but adds a *soft* dependency beyond the blueprint's literal
   "builds on" edge (§0) — flag to the orchestrator if `dolbeault-comparison` is not far enough
   along when this unit is picked up; the fallback is to ship `H1Tail.toH1_surjective` as an
   explicit hypothesis-parametrized statement (same honesty pattern as R2 below) rather than block.
2. **R2 — comparison injectivity (§5.2(c)), MEDIUM (well-understood gap).** Mechanically reduces
   to `Cech.mlClass_eq_zero_iff`'s `⇒` half (Forster 12.4, `toH1_injective`), explicitly flagged
   by the cech design doc itself as "not on the critical path" and possibly deferred. Zero new
   mathematical content once it lands; ship with an explicit hypothesis if it doesn't (per
   `CONVENTIONS.md` rule 3, an honest parametrized statement, not a vacuous one).
3. **R3 — `DFinsupp` friction, LOW (de-risked by the spike, §9).** The two failure modes hit
   during the spike (needing `abbrev` not `def` for `T D` so `DFunLike`/module instances resolve;
   `DFinsupp.mk`'s `Finset`-witness shape) are now known and documented (§2 D1/D2). No
   `mapRange.linearMap` exists at the pin for `mulTail` (§2 D5) — build the `ℂ`-linearity by hand
   from `mapRange.addMonoidHom` + `DFinsupp.ext`, not by citing a nonexistent lemma.
4. **R4 — "good + adapted" combined cover refinement, LOW-MEDIUM.** Not currently exported by
   `Cech/Covers.lean`; needed for §5.2(b). Small (mirrors `exists_adapted_refinement`'s own
   construction, §6.2 of the cech design doc, with chart-disk `O p` and a good background), but is
   genuine new lattice/topology bookkeeping, not a citation. Consider filing a
   `docs/requests/cech-cohomology.md` ask for this export if the combined lemma is more natural to
   build alongside `exists_good_refinement`/`exists_adapted_refinement` than as a `Compat` copy.
5. **R5 — the blueprint's `canonical-forms`/`meromorphic-trace` "builds on" edge, LOW (scoping
   only).** As discussed in §0, neither is needed for the core deliverable; flag the DAG
   correction to the orchestrator (matches the pattern of similar corrections already filed by
   other units, e.g. `docs/requests/meromorphic-and-divisors.md`'s "DAG correction" entries).

---

## 9. Spike record

`scratch_ltails.lean` (project root, 45 lines), run gated
(`while [ "$(pgrep -cx lean)" -ge 3 ]; do sleep 30; done; lake env lean scratch_ltails.lean`):
**success, ~6 s wall**, after one fix (`T D` needed `abbrev`, not `def` — a plain `def` broke
`DFunLike`/instance resolution for `T.mkOfFinset D S x p`, "function expected" error; matches the
`abbrev`-not-`def` pattern the cech design doc's D9/D2 already documents for `C0/C1/Window`).
Verified by compilation:
1. `TailAt p D` as `MeroGermOn X (chartAt p).source ⧸ ordGe p (-(D p))`, with `AddCommGroup`/
   `Module ℂ` instances via `inferInstanceAs` and `TailAt.mk := Submodule.mkQ _`.
2. `windowAt_toTailAt p D d' := Submodule.mapQ _ _ (ordGe p (-d')).subtype le_rfl : WindowAt p (D p) d' →ₗ[ℂ] TailAt p D`
   compiles, and `windowAt_toTailAt p D d' (WindowAt.mk p (D p) d' ψ) = TailAt.mk p D ψ` holds by
   `rfl` — confirming the two submodules genuinely coincide (D1's claim), not merely comparable.
3. `T D := Π₀ p : X, TailAt p D` as an `abbrev` gets `AddCommGroup`/`Module ℂ` for free, and
   `DFinsupp.mk S x : T D` unfolds via `DFinsupp.mk_apply` + `dif_pos`/`dif_neg` exactly as
   `Cech.Window.diffSupp`'s own pattern predicts.
