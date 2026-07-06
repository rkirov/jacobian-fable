# Design: serre-duality-tails (`Jacobian/TailDuality/`)

Blueprint unit **serre-duality-tails** — the blueprint's **make-or-break** unit and routing
decision #1: "Serre duality through Laurent tails (Miranda VI.3): the multiplication action on
`H¹`-tails, surjectivity, the order downgrade (Miranda Lemma 3.6), and **`h¹(D) = l(K−D)`**.
⚠ Use Miranda's concrete tail duality, **not** Hodge symmetry." **Builds on:** laurent-tails,
proper-map-degree, residue-theorem, serre-duality-cech.

References, read in full from the PDF for this design: Miranda GSM5 Ch. VI §3 = book pp. 185–192
= PDF 197–204 (Thm 3.1 First-Form RR PDF 198; the Residue Map + eq. (3.2) PDF 198–199; Thm 3.3 +
injectivity PDF 200; Lemma 3.4 + proof PDF 201; Lemma 3.6 + `Res_ω∘μ_f = Res_{fω}` + surjectivity
proof PDF 202–203; eq. (3.7)–(3.10) three-genera PDF 203–204); Miranda VI §2 Problems A–C
(the `μ_f`/truncation compatibilities, PDF 196–197). Forster §17.6–17.9 (PDF 142–144) consulted
for orientation only — Miranda's route is frozen and is what is designed below.

**Frozen obligation discharged here** (serre-duality-cech D6, quoted exactly):
```lean
theorem RS.TailDuality.i_neg_eq_h1 [T1Space X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    (D : RS.Divisor X) : RS.i (-D) = RS.Finiteness.h1 D
```

One gated end spike (`scratch_tdual.lean`, project root) compiled clean — §10.

---

## 0. RECONCILIATION FIRST: the three tail-space shapes, and the frozen adapter decision

Three sibling designs each carry a "tail space"; this section reconciles them **now** and freezes
the outcome. The three shapes:

| owner | carrier | status |
|---|---|---|
| serre-duality-cech | `RS.SerrePairing.Tail X := X →₀ (ℤ →₀ ℂ)`; `TailSpace D` = tails with exponents `k < -(D x)`; pairing `pair θ τ` by literal monomial sums | design frozen; `Jacobian/SerrePairing/` **not yet on disk** |
| laurent-tails | `RS.LaurentTail.TailAt p D := MeroGermOn X (chartAt ℂ p).source ⧸ Cech.ordGe p (-(D p))`; `T D := Π₀ p, TailAt p D`; `alphaL`, `H1Tail D := T D ⧸ range (alphaL D)`, comparison `H1Tail.equiv : H1Tail D ≃ₗ Cech.H1 D` | design frozen; `Jacobian/LaurentTail/` **not yet on disk** |
| Miranda (the book) | `T[D](X)` = finite formal sums of Laurent polynomials, top degree `< -D(p)` | the mathematics both model |

### 0.1 The decision (FROZEN): the germ model `T D` is the pairing's domain; the raw model is not needed

**All of Miranda VI.3 is executed on laurent-tails' germ model.** Reasons, in force order:

1. **Multiplication is native to the germ model.** Miranda's whole surjectivity argument runs on
   the multiplication operators `μ_f` (Lemma 3.4's diagram, the `Res_ω∘μ_f = Res_{fω}`
   compatibility, the `μ_{1/f}` inversion step). On germ quotients these are `Submodule.mapQ` of
   ring multiplication (`MeroGermOn` is a `CommRing`/`Algebra ℂ`, BUILT) — a few lines each. On
   the raw `Finsupp` model, `μ_f` is convolution against `f`'s Laurent coefficients — hopeless.
2. **The test vectors exist in the germ model with the exact monomial normalization.** Cech's
   `tailGerm p m := MeroGermOn.mk (fun y => (chartAt ℂ p y - chartAt ℂ p p) ^ m)` (BUILT,
   `Jacobian/Cech/Window.lean:73`, verified at source: it is the **literal monomial**, not just
   some order-`m` germ). So the injectivity/3.6 residue computation is the already-spike-verified
   serre-cech pattern `resAt_zpow_mul` + `laurentCoeffAt_order_ne_zero`, with `tailGerm` in place
   of the raw single tail.
3. **The `≤` direction comes for free from the same map.** The residue map
   `resMap : Ω(-D) →ₗ Dual(H1Tail D)` built here is *injective* by the single-`tailGerm` test
   (needed anyway inside the surjectivity endgame, §6 P6, as `φ₂ ≠ 0`) and *surjective* by
   Miranda 3.4+3.6; `LinearEquiv.ofBijective` + `Subspace.dual_finrank_eq` gives
   `i(-D) = h1tail D = h1 D` in one stroke — **both** inequalities of serre-cech's D6 plan.

**Consequences for serre-duality-cech's exports (reconciliation calls, recorded honestly):**

- `finrank_omegaSpace_le` (their D5) is **not instantiated** by this unit. Instantiating it would
  require an adapter `ofRaw : ↥(SerrePairing.TailSpace D) →ₗ T D` **plus its surjectivity** —
  which is exactly the "every germ class mod `ordGe` is a Laurent polynomial class" lemma, i.e.
  the deferred `finrank_windowAt` θ-basis content (cech's own recorded gap, still open on disk:
  `WindowRank.lean` has `leadCoeff_eq_zero_iff`/`leadCoeff_tailGerm_self_ne_zero` but **no**
  `finrank_windowAt` yet). Nothing else needs that lemma; buying the `≤` direction with it when
  the `≥` machinery yields `≤` for free would be pure extra risk. Their D5/D4 remain correct,
  zero-sorry, self-contained exports; their D6 **statement** is discharged here at the exact
  frozen shape. laurent-tails' own design (§1.6) had already independently declined the raw
  model, so this closes the triangle: **germ model wins; raw model = serre-cech-internal.**
- serre-cech's D4 proof pattern (`resAt_zpow_mul` + `ring`-exponent + `laurentCoeffAt_order_ne_zero`,
  spike-verified by them) is reused as-is in §6 P4 — their spike de-risks our core computation.
- The optional cross-check (build `ofRaw` on single tails only and check `pairT∘ofRaw = pair`) is
  documented in §11 as explicitly **non-load-bearing**; do not build unless idle.

### 0.2 Sign and orientation conventions (FROZEN — the single normative table)

Verified against Miranda's text (PDF 199–202), canonical-forms' `mem_omegaSpace_iff`, laurent-tails'
`TailAt.mk_eq_zero_iff`, serre-cech's `Tail.BoundedBy`. All four agree; freeze:

| object | our form | Miranda |
|---|---|---|
| form space | `θ ∈ MForm.OmegaSpace E ↔ θ = 0 ∨ -E ≤ θ.divisor` | `L⁽¹⁾(E)` |
| Serre pairing domain (forms) | `MForm.OmegaSpace (-D)`, i.e. `divisor θ ≥ D` | `L⁽¹⁾(-D)`, `ord_p ω ≥ D(p)` |
| tail fibre | `TailAt p D = germs ⧸ ordGe p (-(D p))`; class `= 0 ↔ (-(D p) : WithTop ℤ) ≤ ord` — records exponents `k < -D(p)` | `T[D]` top degree `< -D(p)` |
| truncation | `D₁ ≤ D₂` ⟹ `truncT : T D₁ →ₗ T D₂` (coarser quotient; kills exponents in `[-D₂ p, -D₁ p)`); `truncT ∘ alphaL D₁ = alphaL D₂` | `t^{D₁}_{D₂}`, Problem C |
| mult.-into | `f` with `∀p, (D p - E p : ℤ) ≤ f.ord p` ⟹ `mulInto f : T D →ₗ T E`; for `f ∈ LinSys C`: `T (A-C) →ₗ T A` | `t ∘ μ_f` (Lemma 3.4's composite) |
| `H¹` model | `H1Tail D := T D ⧸ range (alphaL D)`; `h1tail D = h1 D` (laurent-tails) | `H¹(D) = T[D]/α_D(ℳ)` |
| pairing on a monomial | `pairT θ _ (singleT p D (tailGerm p m)) = laurentCoeffAt (θ.coeffAt p) (chartAt ℂ p p) (-1-m)` | `Res_p(z^m ω) = c_{-1-m}` |
| test tail at order `k` | exponent `-1-k`; in `T D₁` iff `D₁ p ≤ k`; killed by `truncT` to `D₂` iff `k < D₂ p` | `z^{-k-1}·p` (3.3, 3.6) |
| duality numerics | `i E := finrank Ω(E)`; `i (-D) = l (K - D)` via `i_eq_l_add_canonicalDivisorOf` at `-D` (`-D + K = K - D`) | `dim L⁽¹⁾(-D) = dim L(K-D)` |

---

## 1. Facts relied on (each verified at source [BUILT] or against the frozen design [IN FLIGHT])

### 1.1 BUILT, verified at source during this design

- **Cech** (`Jacobian/Cech/`, zero sorries): `ordGe p m` + `mem_ordGe_iff` (Iff.rfl),
  `tailGerm p m` **= the literal monomial germ** (`Window.lean:73-74`), `ord_tailGerm_self`
  (`:76`). **`toH1_injective` / `toH1_eq_zero_iff` have LANDED** (`Injectivity.lean:247/252`) and
  `mlClass_eq_zero_iff` is proved (`Skyscraper.lean:176`) — laurent-tails' comparison-injectivity
  gate (their R2) is now open. `finrank_windowAt`/`finrank_window` still absent (`WindowRank.lean`
  in progress) — irrelevant to us directly (§0.1), relevant to finiteness' χ ledger gate.
- **Meromorphic** (zero sorries): `MeroGermOn` CommRing/Algebra ℂ, `mk`, `mk_eq_mk`, `exists_rep`,
  `mk_mul` (`GermSpace.lean:115`), `restrict` AlgHom + `restrict_mk` (`:206`),
  `ord` + `ord_apply_mk`/`ord_mk` (`OrderEval.lean:37/47/50`), `ord_mul` (`:84`), `ord_restrict`
  (`:54`), `evalAt_restrict` (`:208`), `holoRepr` + `holoRepr_eventuallyEq_nhdsNE` (`:225/229`),
  `Mero.ord_ne_top` (Field.lean), `instFieldMero`, `LinSys`/`l`/`mem_linSys_iff`/`l_zero`,
  `divisor`/`divisor_apply`/`divisor_mul`/`divisor_inv`, `Divisor` lattice (mathlib
  `locallyFinsuppWithin` ordered group), `Divisor.degree` + additivity.
- **ResidueCalculus** (zero sorries): `resAt`, `resAt_congr` (`Residue.lean:39`), `resAt_fun_add`
  (`:42`), `resAt_const_mul` (`:50`), `resAt_of_order_nonneg` (`:72`), `resAt_zpow_mul` (`:193`),
  `resAt_tail_mul` (`:199`), `laurentCoeffAt_order_ne_zero` (`LaurentCoeff.lean:176`), and — a
  design windfall — **`GermFunctionals.lean`**: `meromorphicGermsAt z₀ : Submodule ℂ (Germ (𝓝[≠] z₀) ℂ)`,
  `laurentCoeffL z₀ k`, **`resL z₀ : meromorphicGermsAt z₀ →ₗ[ℂ] ℂ`** (`:81`), `laurentCoeffL_mk`
  — residue as a *linear functional on planar germs with the congr-quotient already handled*.
  §3 D2 builds `pairAt` on top of this, eliminating most rigidity grind.
- **CanonicalForms, files 1–3 on disk** (`MForm.lean`, `OrdRes.lean`, `Differential.lean`):
  `MForm` + `@[ext] MForm.ext` (`MForm.lean:51`), module structure; `ord`/`resAt` (`OrdRes.lean:32/36`),
  `meromorphicAt_coeffAt` (`:39`), `ord_eq_top_iff` (`:45`), `ord_eq_of_mem_source`/`resAt_eq_of_mem_source`,
  `eventually_ord_eq_top/zero`, `divisor`/`divisor_apply` (`:188/215`); `MForm.smul` +
  **`coeffAt_smul_mero … = h.holoRepr ((chartAt ℂ x).symm z) * θ.coeffAt x z := rfl`**
  (`Differential.lean:175`, unconditional, `rfl` — load-bearing for §6 P2/P3).
- **Mathlib at the pin**: `meromorphicOrderAt_mul` (`Analysis/Meromorphic/Order.lean:429`);
  `Submodule.mapQ/liftQ` + `liftQ_apply/liftQ_mkQ/mapQ_apply` (`LinearAlgebra/Quotient/Basic.lean`);
  `DFinsupp.lsum`(+ `lsum_single`, `lhom_ext`, `mapRange_surjective` iff — `Defs.lean:930`);
  `Module.finrank_prod`, `Subspace.dual_finrank_eq` (unconditional, `Dual/Lemmas.lean:510`),
  `instModuleDualFiniteDimensional`, `LinearMap.finrank_le_finrank_of_injective`,
  `Submodule.exists_mem_ne_zero_of_ne_bot`, `LinearMap.ker_eq_bot` — **all spike-verified, §10**.

### 1.2 IN FLIGHT, consumed at the frozen design shapes

- **laurent-tails** (`docs/design/laurent-tails.md` §4, directory not yet on disk): `TailAt p D`,
  `TailAt.mk` (+ `mk_eq_zero_iff`), `T D` (abbrev `Π₀ p, TailAt p D`), `T.mk`, `alphaL D : ℳ X →ₗ T D`
  (+ `alpha_apply…` lemmas), `H1Tail D := T D ⧸ range (alphaL D)` + `H1Tail.mk`,
  `H1Tail.equiv : H1Tail D ≃ₗ Cech.H1 D`, `H1Tail.finiteDimensional`, `h1tail_eq_h1`.
  We do **not** need their `mulTail`/`mulTailEquiv` (§3 D3 builds the sharper `mulInto` locally);
  we DO need `alphaL`'s pointwise-apply lemma — requested, §11. Their two risks re-assessed
  from disk state: R2 (injectivity) now unblocked (`toH1_injective` landed); R1 (surjectivity /
  Leray) still their hardest piece — our top external risk (§8 R1).
- **canonical-forms files 4–6** (design §4.4–4.5): `OmegaSpace` + `mem_omegaSpace_iff`, `i`,
  `Ω_iso_linSys`/`i_eq_l_add_canonicalDivisorOf`, `canonicalDivisorOf`, `eq_zero_or_forall_ord_ne_top`
  (D5), `exists_ne_zero_mform`, `genus_eq_finrank_omegaSpace_zero`.
- **finiteness-and-chi** (`Chi.lean` not yet on disk; frozen §4.7): `h1`, `chi`,
  `chi_eq_chi_zero_add_degree`, `chi_zero_add_degree_le_l`, `l_mono`, `finiteDimensional_linSys`,
  `finiteDimensional_H1`.
- **residue-theorem** (unit not started; orchestrator addendum: trace route primary): the single
  atom, at the shape already frozen in `docs/requests/residue-theorem.md`:
  ```lean
  theorem sum_resAt_eq_zero [T1Space X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
      (f : RS.ℳ X) (θ : RS.MForm X) :
      ∑ᶠ x, RS.resAt (fun z => f.holoRepr ((chartAt ℂ x).symm z) * θ.coeffAt x z) (chartAt ℂ x x) = 0
  ```
  Note (recorded in the request file, §11): since `coeffAt_smul_mero` is `rfl`, this is literally
  `∑ᶠ x, (f • θ).resAt x = 0`; either this finsum form or a `Finset`-flexible
  `residueTheorem (θ) {S} (hS : PoleSet ⊆ S) : ∑ x ∈ S, θ.resAt x = 0` works for §6 P3 — the
  citation is isolated in ONE lemma (`pairT_alpha`) so shape drift costs one edit.
- **proper-map-degree**: listed in our Builds-on edge; audit result: **no export of theirs is
  consumed by this design** (Miranda VI.3 needs no degree theory; `deg(div f) = 0` never enters —
  divisor degrees enter only through finiteness' χ ledger). Recorded as a DAG note (§11), matching
  the precedent of other units' DAG audits; no blueprint edit filed, the edge is merely unused.

### 1.3 Miranda's text, audited — two formal repairs required (found by reading the proof twice)

1. **Lemma 3.4 needs `φ₁ ≠ 0` and `φ₂ ≠ 0`.** Miranda's proof claims the pair map
   `(f₁,f₂) ↦ φ₁∘t∘μ_{f₁} − φ₂∘t∘μ_{f₂}` on `L(C) × L(C)` is injective if no witness pair
   exists — but a kernel element with `f₂ = 0, f₁ ≠ 0` only yields `φ₁∘t∘μ_{f₁} = 0`, no witness.
   Repair: `t∘μ_{f}` (= our `mulInto f`, `f ≠ 0`) is **surjective** (`μ_f` invertible by field
   division in the germ ring + truncations are quotient maps), so `φᵢ∘(t∘μ_{fᵢ}) = 0 ⟹ φᵢ = 0`;
   with `φ₁, φ₂ ≠ 0` as hypotheses the kernel element has both components nonzero. In the one
   place 3.4 is applied, both functionals are nonzero (`φ_A = φ∘trunc ≠ 0` by truncation
   surjectivity; `Res_{ω₀} ≠ 0` by the injectivity computation). §6 P5.
2. **"for C large" must be an explicit divisor.** Miranda's growth-rate contradiction is made
   explicit (no limits, no eventually): `C := Divisor.single P n` with
   `n := (l A - 3•chi 0 - deg A).toNat + 1` — §6 P5 step 5, arithmetic closed by `omega`
   (spike-verified including the `Int.toNat` step).
   Also: 3.6 and the endgame silently assume `ω ≠ 0` where `ord_p(ω)` is used; the `ω = 0` cases
   are trivial memberships and are handled by explicit case splits (§6 P4/P6).

---

## 2. The mathematical skeleton being formalized (Miranda VI.3, in our notation)

With `θ` for meromorphic 1-forms (`ω` is the smoothness exponent in this codebase — on-disk
canonical-forms files already use `θ`), `Ω(E) := MForm.OmegaSpace E`:

- **Pairing** `pairT θ : T D →ₗ ℂ` for `θ ∈ Ω(-D)`: at each point read the germ in the chart,
  multiply by `θ.coeffAt p`, take `resAt` at the chart center; sum over the (finite) tail support.
  Well-defined on the quotient fibres because `ord ψ ≥ -D p` and `ord θ ≥ D p` force
  `resAt(ψ·θ) = 0` (`resAt_of_order_nonneg`).
- **Descent** (residue theorem): `pairT θ (alphaL D f) = ∑ Res(f·θ) = 0`, so `pairT` descends to
  `resMap : Ω(-D) →ₗ Dual (H1Tail D)` — Miranda's `Res : L⁽¹⁾(-D) → H¹(D)^*`.
- **Injectivity** (Thm 3.3, easy half): `θ ≠ 0` pairs nontrivially against the single monomial
  tail `tailGerm p (-1-k)`, `k := ord_p θ`: the value is the leading Laurent coefficient ≠ 0.
- **Lemma 3.4**: for nonzero functionals `φ₁ φ₂` on `T A` vanishing on `im α_A`, there are
  `0 ≤ C` and nonzero `f₁ f₂ ∈ L(C)` with `φ₁ ∘ mulInto f₁ = φ₂ ∘ mulInto f₂` on `T (A - C)`.
  Proof: otherwise the pair map `L(C)² → Dual(H1Tail (A-C))` is injective for every `C`, giving
  `2·l(C) ≤ h1(A-C)`; χ ledger + Riemann seed make the two sides grow at rates `2n` vs `n` in
  `n = deg C` — contradiction at an explicit `n`.
- **Lemma 3.6 (order downgrade)**: `D₁ ≤ D₂`, `θ ∈ Ω(-D₁)`, `pairT θ` vanishing on
  `ker (truncT : T D₁ → T D₂)` ⟹ `θ ∈ Ω(-D₂)`. Proof: a point `p` with
  `D₁ p ≤ k := ord_p θ < D₂ p` yields the tail `tailGerm p (-1-k)` in the kernel of `truncT`
  pairing to the nonzero leading coefficient — contradiction.
- **Surjectivity endgame** (Thm 3.3, hard half): given `φ : T D →ₗ ℂ` vanishing on `im α_D`,
  pick `θ₀ ≠ 0` (canonical-forms), `K := divisor θ₀`, `A := D ⊓ K` (so `A ≤ D`, `θ₀ ∈ Ω(-A)`);
  apply 3.4 to `φ_A := φ ∘ truncT` and `Res_{θ₀}` to get `C, f₁, f₂`; rewrite the right side by
  the multiplication compatibility as `Res_{f₂•θ₀}`; invert `μ_{f₁}`; set
  `η := (f₂ * f₁⁻¹) • θ₀ ∈ Ω(-(A - C - div f₁))`; 3.6 upgrades `η` into `Ω(-A)` (its functional
  factors through the truncation `T(A-C-div f₁) → T A` by construction), identify `φ_A = Res_η`
  on `T A` (truncation surjective); 3.6 again upgrades `η ∈ Ω(-D)` (now the functional factors
  through `T A → T D` since `φ_A = φ ∘ truncT`), and `φ = Res_η` on `T D`. ∎
- **Numerics**: `resMap` bijective ⟹ `i(-D) = finrank Dual(H1Tail D) = finrank H1Tail D
  = h1tail D = h1 D`; canonical-forms' dictionary turns `i(-D)` into `l(K-D)`; at `D = 0` into
  `h1 0 = l K = i 0 = genus X`.

---

## 3. Core definitional decisions

Namespace `RS.TailDuality`. Standing variables (all files):
```lean
open scoped ContDiff Manifold Classical
open RS RS.LaurentTail
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
```
(`[T1Space X]` is derivable from `T2Space` but is written explicitly on the frozen-shape exports
to match serre-cech's D6 statement verbatim. `DecidableEq X` via `open scoped Classical`,
laurent-tails' own idiom.)

### D1 — `truncT` and `singleT`: the truncation lattice and the test vectors (ours, cheap)

`truncAt p (h : D₁ ≤ D₂) : TailAt p D₁ →ₗ[ℂ] TailAt p D₂ := Submodule.mapQ _ _ LinearMap.id h'`
where `h' : ordGe p (-(D₁ p)) ≤ (ordGe p (-(D₂ p))).comap id` is monotonicity of `ordGe` in the
bound (`mem_ordGe_iff` + `WithTop` coe-mono). `truncT h : T D₁ →ₗ T D₂` assembles by
`DFinsupp.mapRange` (add via `mapRange.addMonoidHom`, `ℂ`-linearity by `DFinsupp.ext` — the exact
laurent-tails D5 recipe; **no** `mapRange.linearMap` at the pin, their finding, re-confirmed).
Surjective: pointwise `mapQ` of `id` over surjective `mkQ` + `DFinsupp.mapRange_surjective`
(mathlib iff, `Defs.lean:930`). `singleT p D ψ := DFinsupp.single p (TailAt.mk p D ψ)`.
Miranda Problem C (`truncT_alpha`) is pointwise `mapQ_apply` + `DFinsupp.ext` against `alphaL`'s
apply lemma (requested, §11).

### D2 — `pairAt`/`pairT`: the residue pairing on the germ model, through `RS.resL`

The pairing is built on residue-calculus's **already-built** germ functional `resL`:

```lean
/-- Chart-read of a manifold germ as a punctured planar germ at the chart center. -/
noncomputable def readAt (p : X) :
    MeroGermOn X (chartAt ℂ p).source →ₗ[ℂ] Filter.Germ (𝓝[≠] (chartAt ℂ p p)) ℂ
-- ψ = mk f ↦ ↑(f ∘ (chartAt ℂ p).symm); well-defined: codiscrete agreement on the source
-- transports to 𝓝[≠]-agreement at the center through the chart (the same bridge ordAtX_congr
-- and MeroGermOn.ord's own liftOn congruence already use, Meromorphic/OrderEval+Predicates).

noncomputable def pairAt (θ : MForm X) (p : X) :
    MeroGermOn X (chartAt ℂ p).source →ₗ[ℂ] ℂ
-- := resL (chartAt ℂ p p) ∘ₗ (codRestrict to meromorphicGermsAt of (readAt p ·) * ↑(θ.coeffAt p))
```

`pairAt` is honestly linear because the *germ* target absorbs all junk-value trouble: `readAt` is
linear on the nose (representative-wise, `mk_eq_mk`), multiplication by the fixed germ
`↑(θ.coeffAt p)` is linear in the germ ring, and `resL` is a built linear functional. **No
`holoRepr` pointwise-additivity is ever needed** (it is false at junk points; the germ route
avoids it — this is why `pairAt` is NOT defined via `holoRepr` directly).

Then, exactly the quotient/assembly pattern spiked in §10:
```lean
noncomputable def pairTailAt (θ) (hθ : θ ∈ MForm.OmegaSpace (-D)) (p) : TailAt p D →ₗ[ℂ] ℂ
-- := Submodule.liftQ (ordGe p (-(D p))) (pairAt θ p) (kills: resAt_of_order_nonneg, see P2)
noncomputable def pairT (θ) (hθ : θ ∈ MForm.OmegaSpace (-D)) : T D →ₗ[ℂ] ℂ
-- := DFinsupp.lsum ℕ (pairTailAt θ hθ)
```
`pairT` values are proof-irrelevant in `hθ`. Miranda's `Res_ω` on `T[D]` ✓.

### D3 — `mulInto`: Miranda's `t ∘ μ_f` as ONE uniform map, linear in `f`, no `f ≠ 0` needed

```lean
noncomputable def mulIntoAt (f : ℳ X) (p : X) {D E : Divisor X}
    (hf : ((D p - E p : ℤ) : WithTop ℤ) ≤ f.ord p) : TailAt p D →ₗ[ℂ] TailAt p E
-- := Submodule.mapQ _ _ (LinearMap.mulLeft ℂ (MeroGermOn.restrict (subset_univ _) f)) …
noncomputable def mulInto (f : ℳ X) {D E : Divisor X}
    (hf : ∀ p, ((D p - E p : ℤ) : WithTop ℤ) ≤ f.ord p) : T D →ₗ[ℂ] T E
noncomputable def nuL (A C : Divisor X) : ↥(LinSys C) →ₗ[ℂ] (T (A - C) →ₗ[ℂ] T A)
-- nuL A C f := mulInto ↑f (bound: (A-C) p - A p = -C p ≤ f.ord p, from mem_linSys_iff)
```
Key properties (all germ-level one-liners after `Quotient`/`DFinsupp` induction):
`mulInto` is **linear in `f`** (`restrict` is an `AlgHom`; `mulLeft` additive in the multiplier)
— this is what makes Lemma 3.4's pair map a genuine `LinearMap` (Miranda's `μ_f` alone, with its
`f`-dependent target `T[D - div f]`, is not linear in `f`; composing with the truncation into the
FIXED target `T A` restores linearity — the design's key packaging trick, and the reason
laurent-tails' `mulTail`/`mulTailEquiv` is not needed here). For `f ≠ 0` it is **surjective**
(`mulLeft (restrict f)` is bijective — inverse `mulLeft (restrict f⁻¹)`, using `restrict` AlgHom +
`Field (ℳ X)`; `mapQ` of surjective ∘ `mkQ` surjective; `DFinsupp.mapRange_surjective`).
Miranda Problem B: `mulInto f hf (alphaL D g) = alphaL E (f * g)` (`restrict_mk`/AlgHom `map_mul`).
The `μ_{1/f}` inversion (endgame step): `nuL A C f (mulInto ↑f⁻¹ hinv τ') = truncT hE τ'` — germ
level `f·(f⁻¹·ψ) = ψ` (field), `mapQ` composition.

### D4 — `resMap`, and the headline through it

```lean
noncomputable def resMap (D : Divisor X) :
    ↥(MForm.OmegaSpace (-D)) →ₗ[ℂ] Module.Dual ℂ (H1Tail D)
-- ⟨θ,hθ⟩ ↦ Submodule.liftQ (range (alphaL D)) (pairT θ hθ) (pairT_alpha); linearity in θ via
-- LinearMap.ext + Quotient.mk-surjectivity reduction (serre-cech P2 step-3 pattern).
noncomputable def resEquiv (D) : ↥(MForm.OmegaSpace (-D)) ≃ₗ[ℂ] Module.Dual ℂ (H1Tail D)
-- := LinearEquiv.ofBijective (resMap D) ⟨resMap_injective D, resMap_surjective D⟩
```
`i_neg_eq_h1` = `LinearEquiv.finrank_eq (resEquiv D)` + `Subspace.dual_finrank_eq` +
`h1tail_eq_h1`. Note this yields Miranda's Thm 3.3 **as stated** (Res is an isomorphism), not
just the dimension equality — the stronger functional-level fact is exported for free.

### D5 — ord bookkeeping for `MForm.smul` (Compat here; request filed to canonical-forms)

```lean
theorem MForm.ord_smul (f : ℳ X) (θ : MForm X) (p : X) : (f • θ).ord p = f.ord p + θ.ord p
```
Proof: `(f•θ).ord p = meromorphicOrderAt (f.holoRepr ∘ (chartAt ℂ p).symm * θ.coeffAt p) center`
(`coeffAt_smul_mero` is `rfl`), split by `meromorphicOrderAt_mul` (mathlib), identify the first
factor's order with `f.ord p` (`ord_apply_mk` + `holoRepr_eventuallyEq_nhdsNE` + chart transport
— the same bridge `readAt` uses). Corollaries actually consumed (stated with explicit nonzero
hypotheses so `untop₀` is faithful, via `Mero.ord_ne_top` and `MForm.ord_eq_top_iff`):
`smul_ne_zero'`, `divisor_smul_mform (hf : f ≠ 0) (hθ : θ ≠ 0) : (f•θ).divisor = divisor f + θ.divisor`,
and the membership movers `smul_mem_omegaSpace` instances used in P5/P6.
⚠ Deliberately NOT relied on: `(f*g)•θ = f•(g•θ)` as an `MForm` **equality** — it is FALSE
pointwise at junk points of `holoRepr` (found during this design; flagged to canonical-forms,
§11, since their planned `smul_smul` module law has the same issue). Everything here needs only
the `=ᶠ[𝓝[≠] center]` version (`smul_smul_coeffAt_eventuallyEq`, D6).

### D6 — `pairT` is `=ᶠ`-robust: the congruence + collapse lemmas

```lean
theorem pairT_congr (hcoeff : ∀ p, θ.coeffAt p =ᶠ[𝓝[≠] (chartAt ℂ p p)] θ'.coeffAt p)
    (hθ) (hθ') : pairT θ hθ = pairT θ' hθ'
theorem smul_smul_coeffAt_eventuallyEq (a b : ℳ X) (θ : MForm X) (p : X) :
    (a • (b • θ)).coeffAt p =ᶠ[𝓝[≠] (chartAt ℂ p p)] ((a * b) • θ).coeffAt p
```
(the latter from `holoRepr(a*b) =ᶠ holoRepr a * holoRepr b` on punctured neighborhoods —
`exists_rep` + `mk_mul` + `holoRepr_eventuallyEq_nhdsNE`, transported through the chart). These
two let the endgame collapse the nested smul produced by applying the multiplication
compatibility twice, without any structure-level `smul_smul`.

---

## 4. File plan (4 content files + root; ≈1000 lines total)

| # | File | Content | Est. | Key imports |
|---|------|---------|------|-------------|
| 1 | `TailDuality/TailOps.lean` | `truncAt/truncT` (+ `_mk`, `_surjective`, `_alpha`, `_singleT`), `singleT` (+ `eq_zero_iff`), `mulIntoAt/mulInto` (+ `_mk`, linearity-in-`f`, `_alpha`, `_surjective`), `nuL` (+ apply/alpha/surjective), inversion lemma, `LinSys.divisor_ge`, `ord_eq_divisor` helpers | ~300 | `Jacobian.LaurentTail`, `Jacobian.Meromorphic` |
| 2 | `TailDuality/Pairing.lean` | `readAt` (+ `_mk`, meromorphy, mult., `tailGerm`-read), `pairAt` (+ `_mk`, `_tailGerm`, kill-`ordGe`), `pairTailAt`, `pairT` (+ `_singleT`, `_zero`), D5 ord kit (`MForm.ord_smul` Compat + movers), D6 congruences, `pairT_trunc`, `pairT_mulInto`, `pairT_alpha` (∑Res=0), `pairAt_tailGerm_order_ne_zero`, `pairT_ne_zero`, `resMap` + `resMap_mk` + `resMap_injective` | ~380 | file 1, `Jacobian.CanonicalForms`, `Jacobian.ResidueCalculus.GermFunctionals`, `Jacobian.ResidueTheorem` (one lemma) |
| 3 | `TailDuality/Counting.lean` | `nuPairDual` (the 3.4 pair map into `Dual (H1Tail (A-C))`), `two_l_le_h1_of_injective`, the explicit-`n` arithmetic, **`exists_mul_functional_eq` (LEMMA 3.4)** | ~220 | files 1–2, `Jacobian.Finiteness` |
| 4 | `TailDuality/Duality.lean` | **`mem_omegaSpace_of_vanishing_ker_trunc` (LEMMA 3.6)**, `exists_pairT_eq` (surjectivity endgame), `resMap_surjective`, `resEquiv`, `i_neg_eq_h1`, `l_sub_eq_h1`, `h1_zero_eq_l_K`, `h1_zero_eq_genus`, `h1_canonical` | ~260 | files 1–3 |
| 5 | `Jacobian/TailDuality.lean` | unit root; 5–15-line API docstring | ~30 | all |

Build waves: file 1 gates only on laurent-tails' `TailSpace.lean`/`Truncation.lean` (their files
2–3 — NOT on their `Comparison.lean`); file 2 additionally on canonical-forms file 6
(`OmegaSpace`) and the residue-theorem atom; file 3 on finiteness' `Chi.lean` and laurent-tails'
`H1Tail.finiteDimensional` (their file 5 → comparison); file 4 on all. So the comparison
(laurent-tails R1) gates files 3–4 only; files 1–2 minus `pairT_alpha` are buildable as soon as
laurent-tails' carrier + canonical-forms' `OmegaSpace` land.

---

## 5. Exports — exact signatures

### 5.1 `TailOps.lean`

```lean
namespace RS.TailDuality
noncomputable def truncAt (p : X) {D₁ D₂ : RS.Divisor X} (h : D₁ ≤ D₂) :
    TailAt p D₁ →ₗ[ℂ] TailAt p D₂
@[simp] theorem truncAt_mk (p) {D₁ D₂} (h) (ψ) :
    truncAt p h (TailAt.mk p D₁ ψ) = TailAt.mk p D₂ ψ
noncomputable def truncT {D₁ D₂ : RS.Divisor X} (h : D₁ ≤ D₂) : T D₁ →ₗ[ℂ] T D₂
theorem truncT_apply {D₁ D₂} (h) (τ) (p) : truncT h τ p = truncAt p h (τ p)
theorem truncT_surjective {D₁ D₂} (h : D₁ ≤ D₂) : Function.Surjective (truncT h)
theorem truncT_alpha {D₁ D₂} (h : D₁ ≤ D₂) (f : ℳ X) : truncT h (alphaL D₁ f) = alphaL D₂ f

noncomputable def singleT (p : X) (D : RS.Divisor X)
    (ψ : RS.MeroGermOn X (chartAt ℂ p).source) : T D
@[simp] theorem singleT_apply_self (p D ψ) : singleT p D ψ p = TailAt.mk p D ψ
theorem singleT_eq_zero_iff (p D ψ) :
    singleT p D ψ = 0 ↔ (-(D p) : WithTop ℤ) ≤ ψ.ord p
@[simp] theorem truncT_singleT {D₁ D₂} (h) (p ψ) :
    truncT h (singleT p D₁ ψ) = singleT p D₂ ψ

noncomputable def mulIntoAt (f : ℳ X) (p : X) {D E : RS.Divisor X}
    (hf : ((D p - E p : ℤ) : WithTop ℤ) ≤ f.ord p) : TailAt p D →ₗ[ℂ] TailAt p E
@[simp] theorem mulIntoAt_mk (f p) {D E} (hf) (ψ) : mulIntoAt f p hf (TailAt.mk p D ψ)
    = TailAt.mk p E (MeroGermOn.restrict (Set.subset_univ _) f * ψ)
noncomputable def mulInto (f : ℳ X) {D E : RS.Divisor X}
    (hf : ∀ p, ((D p - E p : ℤ) : WithTop ℤ) ≤ f.ord p) : T D →ₗ[ℂ] T E
theorem mulInto_apply (f) {D E} (hf) (τ) (p) : mulInto f hf τ p = mulIntoAt f p (hf p) (τ p)
theorem mulInto_add_left (f g) {D E} (hf hg) :
    mulInto (f + g) (bound) = mulInto f hf + mulInto g hg      -- bound via min-order; see P1
theorem mulInto_alpha (f) {D E} (hf) (g : ℳ X) : mulInto f hf (alphaL D g) = alphaL E (f * g)
theorem mulInto_surjective {f : ℳ X} (hf0 : f ≠ 0) {D E} (hf) :
    Function.Surjective (mulInto f hf)

noncomputable def nuL (A C : RS.Divisor X) : ↥(RS.LinSys C) →ₗ[ℂ] (T (A - C) →ₗ[ℂ] T A)
theorem nuL_apply (A C) (f) : nuL A C f = mulInto (f : ℳ X) (nu_bound A C f)
theorem nuL_alpha (A C) (f) (g : ℳ X) : nuL A C f (alphaL (A - C) g) = alphaL A ((f : ℳ X) * g)
theorem nuL_surjective (A C) {f} (hf0 : (f : ℳ X) ≠ 0) : Function.Surjective (nuL A C f)
theorem nuL_mulInto_inv (A C) {f : ↥(RS.LinSys C)} (hf0 : (f : ℳ X) ≠ 0)
    (τ' : T (A - C - RS.divisor (f : ℳ X))) :
    nuL A C f (mulInto (f : ℳ X)⁻¹ (inv_bound …) τ')
      = truncT (sub_divisor_le A C f hf0 : A - C - RS.divisor (f:ℳ X) ≤ A) τ'

theorem LinSys.divisor_ge {C : RS.Divisor X} {f : ℳ X} (hf : f ∈ RS.LinSys C) (hf0 : f ≠ 0) :
    -C ≤ RS.divisor f
theorem Mero.ord_eq_divisor {f : ℳ X} (hf : f ≠ 0) (p : X) :
    f.ord p = ((RS.divisor f p : ℤ) : WithTop ℤ)
```

### 5.2 `Pairing.lean`

```lean
noncomputable def readAt (p : X) :
    RS.MeroGermOn X (chartAt ℂ p).source →ₗ[ℂ] Filter.Germ (𝓝[≠] (chartAt ℂ p p)) ℂ
@[simp] theorem readAt_mk (p) {f : X → ℂ} (hf) :
    readAt p (MeroGermOn.mk f hf) = ↑(f ∘ (chartAt ℂ p).symm)
theorem meromorphicGerm_readAt (p ψ) : (readAt p ψ) ∈ RS.meromorphicGermsAt (chartAt ℂ p p)
theorem readAt_mul (p ψ ψ') : readAt p (ψ * ψ') = readAt p ψ * readAt p ψ'
theorem readAt_tailGerm (p m) : readAt p (RS.Cech.tailGerm p m)
    = ↑(fun z => (z - chartAt ℂ p p) ^ m)     -- germ-level; chart right_inv on 𝓝[≠]

noncomputable def pairAt (θ : MForm X) (p : X) :
    RS.MeroGermOn X (chartAt ℂ p).source →ₗ[ℂ] ℂ
theorem pairAt_mk (θ p) {f} (hf) : pairAt θ p (MeroGermOn.mk f hf)
    = RS.resAt (fun z => f ((chartAt ℂ p).symm z) * θ.coeffAt p z) (chartAt ℂ p p)
theorem pairAt_tailGerm (θ p m) : pairAt θ p (RS.Cech.tailGerm p m)
    = RS.laurentCoeffAt (θ.coeffAt p) (chartAt ℂ p p) (-1 - m)
theorem pairAt_eq_zero_of_mem_ordGe {θ D p} (hθ : θ ∈ MForm.OmegaSpace (-D))
    {ψ} (hψ : ψ ∈ RS.Cech.ordGe p (-(D p))) : pairAt θ p ψ = 0

noncomputable def pairTailAt (θ) (hθ : θ ∈ MForm.OmegaSpace (-D)) (p) : TailAt p D →ₗ[ℂ] ℂ
noncomputable def pairT (θ) (hθ : θ ∈ MForm.OmegaSpace (-D)) : T D →ₗ[ℂ] ℂ
@[simp] theorem pairT_singleT (θ hθ p ψ) : pairT θ hθ (singleT p D ψ) = pairAt θ p ψ
@[simp] theorem pairT_zero (D) : pairT (0 : MForm X) (zero_mem _) = (0 : T D →ₗ[ℂ] ℂ)
theorem pairT_add (θ θ' hθ hθ' h+) : pairT (θ + θ') h+ = pairT θ hθ + pairT θ' hθ'
theorem pairT_smul (c θ hθ hc) : pairT (c • θ) hc = c • pairT θ hθ

-- D5 ord kit (Compat; request filed):
theorem MForm.ord_smul (f : ℳ X) (θ : MForm X) (p : X) : (f • θ).ord p = f.ord p + θ.ord p
theorem divisor_smul_mform {f θ} (hf : f ≠ 0) (hθ : θ ≠ 0) :
    (f • θ).divisor = RS.divisor f + θ.divisor
theorem smul_mem_omegaSpace {f θ} {E F : RS.Divisor X}
    (hf : ∀ p, ((F p : ℤ) : WithTop ℤ) ≤ f.ord p) (hθ : θ ∈ MForm.OmegaSpace (-E)) :
    f • θ ∈ MForm.OmegaSpace (-(E + F))       -- the one general mover; instances in P5/P6

-- D6 congruences:
theorem pairT_congr {θ θ' : MForm X} (h : ∀ p, θ.coeffAt p =ᶠ[𝓝[≠] (chartAt ℂ p p)] θ'.coeffAt p)
    (hθ hθ') : pairT θ hθ = pairT θ' hθ'
theorem smul_smul_coeffAt_eventuallyEq (a b : ℳ X) (θ) (p) :
    (a • (b • θ)).coeffAt p =ᶠ[𝓝[≠] (chartAt ℂ p p)] ((a * b) • θ).coeffAt p

theorem pairT_trunc {D₁ D₂} (h : D₁ ≤ D₂) (θ) (hθ₂ : θ ∈ MForm.OmegaSpace (-D₂)) :
    (pairT θ hθ₂) ∘ₗ truncT h = pairT θ (omegaSpace_anti h hθ₂)
theorem pairT_mulInto {D E} (f : ℳ X) (hf : ∀ p, ((D p - E p : ℤ) : WithTop ℤ) ≤ f.ord p)
    (θ) (hθ : θ ∈ MForm.OmegaSpace (-E)) (hfθ : f • θ ∈ MForm.OmegaSpace (-D)) :
    (pairT θ hθ) ∘ₗ mulInto f hf = pairT (f • θ) hfθ        -- Miranda: Res_ω∘μ_f = Res_{fω}

theorem pairT_alpha (θ) (hθ : θ ∈ MForm.OmegaSpace (-D)) (f : ℳ X) :
    pairT θ hθ (alphaL D f) = 0                              -- ∑Res = 0 enters HERE only
theorem pairT_ne_zero {θ} (hθ0 : θ ≠ 0) (hθ : θ ∈ MForm.OmegaSpace (-D)) :
    pairT θ hθ ≠ 0                                            -- Miranda 3.3, injectivity half

noncomputable def resMap (D : RS.Divisor X) :
    ↥(MForm.OmegaSpace (-D)) →ₗ[ℂ] Module.Dual ℂ (H1Tail D)
theorem resMap_mk (D θ hθ τ) : resMap D ⟨θ, hθ⟩ (H1Tail.mk D τ) = pairT θ hθ τ
theorem resMap_injective (D) : Function.Injective (resMap D)
```

### 5.3 `Counting.lean`

```lean
noncomputable def nuPairDual (A C : RS.Divisor X) (φ₁ φ₂ : T A →ₗ[ℂ] ℂ)
    (hα₁ : ∀ g : ℳ X, φ₁ (alphaL A g) = 0) (hα₂ : ∀ g, φ₂ (alphaL A g) = 0) :
    (↥(RS.LinSys C) × ↥(RS.LinSys C)) →ₗ[ℂ] Module.Dual ℂ (H1Tail (A - C))
theorem nuPairDual_apply (…) (f₁ f₂ τ) :
    nuPairDual A C φ₁ φ₂ hα₁ hα₂ (f₁, f₂) (H1Tail.mk _ τ)
      = φ₁ (nuL A C f₁ τ) - φ₂ (nuL A C f₂ τ)
theorem two_l_le_h1_of_injective (…) (hinj : Function.Injective (nuPairDual A C φ₁ φ₂ hα₁ hα₂)) :
    2 * (RS.l C : ℤ) ≤ (RS.Finiteness.h1 (A - C) : ℤ)

/-- **MIRANDA LEMMA 3.4.** -/
theorem exists_mul_functional_eq (A : RS.Divisor X) (φ₁ φ₂ : T A →ₗ[ℂ] ℂ)
    (hα₁ : ∀ g : ℳ X, φ₁ (alphaL A g) = 0) (hα₂ : ∀ g, φ₂ (alphaL A g) = 0)
    (h₁ : φ₁ ≠ 0) (h₂ : φ₂ ≠ 0) :
    ∃ C : RS.Divisor X, 0 ≤ C ∧ ∃ f₁ f₂ : ↥(RS.LinSys C),
      (f₁ : ℳ X) ≠ 0 ∧ (f₂ : ℳ X) ≠ 0 ∧ φ₁ ∘ₗ nuL A C f₁ = φ₂ ∘ₗ nuL A C f₂
```

### 5.4 `Duality.lean`

```lean
/-- **MIRANDA LEMMA 3.6** (the order downgrade). -/
theorem mem_omegaSpace_of_vanishing_ker_trunc {D₁ D₂ : RS.Divisor X} (h : D₁ ≤ D₂)
    {θ : MForm X} (hθ : θ ∈ MForm.OmegaSpace (-D₁))
    (hker : ∀ τ : T D₁, truncT h τ = 0 → pairT θ hθ τ = 0) :
    θ ∈ MForm.OmegaSpace (-D₂)

/-- **MIRANDA THM 3.3, surjectivity half**, functional form on `T D`. -/
theorem exists_pairT_eq (D : RS.Divisor X) (φ : T D →ₗ[ℂ] ℂ)
    (hα : ∀ f : ℳ X, φ (alphaL D f) = 0) :
    ∃ θ : MForm X, ∃ hθ : θ ∈ MForm.OmegaSpace (-D), pairT θ hθ = φ

theorem resMap_surjective (D) : Function.Surjective (resMap D)
noncomputable def resEquiv (D : RS.Divisor X) :
    ↥(MForm.OmegaSpace (-D)) ≃ₗ[ℂ] Module.Dual ℂ (H1Tail D)

/-- THE frozen obligation (serre-duality-cech D6, exact shape). -/
theorem i_neg_eq_h1 [T1Space X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    (D : RS.Divisor X) : RS.i (-D) = RS.Finiteness.h1 D
/-- Serre duality in the `l(K-D)` shape riemann-roch consumes. -/
theorem l_sub_eq_h1 [T1Space X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    {ω₀ : MForm X} (h₀ : ω₀ ≠ 0) (D : RS.Divisor X) :
    RS.l (RS.canonicalDivisorOf ω₀ - D) = RS.Finiteness.h1 D
theorem h1_zero_eq_l_K (…) {ω₀} (h₀ : ω₀ ≠ 0) :
    RS.Finiteness.h1 (0 : RS.Divisor X) = RS.l (RS.canonicalDivisorOf ω₀)
theorem h1_zero_eq_genus (…) : RS.Finiteness.h1 (0 : RS.Divisor X) = RS.genus X
theorem h1_canonical (…) {ω₀} (h₀ : ω₀ ≠ 0) :
    RS.Finiteness.h1 (RS.canonicalDivisorOf ω₀) = 1
```

---

## 6. Proof plans (the full Miranda 3.4→3.6 decomposition)

### P1. `TailOps.lean` (routine; every proof ≤ ~25 lines)

- `truncAt`: `Submodule.mapQ … LinearMap.id` with `ordGe`-monotonicity (`mem_ordGe_iff` +
  `WithTop.coe_le_coe.mpr (neg_le_neg (h p))`). `truncAt_mk` is `mapQ_apply`.
- `truncT`: `DFinsupp.mapRange`-assembly exactly as laurent-tails D5 prescribes (additive via
  `mapRange.addMonoidHom`, `map_smul'` by `DFinsupp.ext p` + `truncAt`'s own `map_smul`).
  Surjectivity: `DFinsupp.mapRange_surjective … .mpr (fun p => (truncAt p h)-surjective)`,
  pointwise from `Submodule.mkQ_surjective` through the `Quotient.ind` diagram.
- `truncT_alpha`: `DFinsupp.ext p`; both sides at `p` are `TailAt.mk` of the SAME restricted germ
  (laurent-tails' `alpha_apply`, requested §11) — `truncAt_mk` closes.
- `mulIntoAt`: `mapQ` of `LinearMap.mulLeft ℂ (restrict f)`; the comap obligation: for
  `ψ.ord p ≥ -(D p)`: `(restrict f * ψ).ord p = (restrict f).ord p + ψ.ord p` (`ord_mul`,
  `chartAt`-source open + center mem), `(restrict f).ord p = f.ord p` (`ord_restrict`), then
  `WithTop` monotone arithmetic (`add_le_add hf hψ` + cast lemma `(a+b : ℤ) → WithTop`) gives
  `≥ (D p - E p) + (-(D p)) = -(E p)`. ~20 lines with one `WithTop` cast helper.
- linearity in `f` (`mulInto_add_left`, `map_smul` analogue): `DFinsupp.ext` + `Quotient.ind`:
  `restrict (f+g) * ψ = restrict f * ψ + restrict g * ψ` (`AlgHom.map_add` + `add_mul`), then
  `Submodule.Quotient.mk_add`. NOTE the bound hypothesis for `f + g` is taken as a separate
  argument (orders of sums only satisfy `≥ min`; at the `nuL` packaging site all three bounds
  come uniformly from `mem_linSys_iff`, so no min-arithmetic is ever needed — `nuL.map_add'`
  instantiates this lemma with all bounds `-C p ≤ ·.ord p`).
- `mulInto_alpha`: `DFinsupp.ext p`, `mulIntoAt_mk` + `alpha_apply` + `restrict`-AlgHom
  `map_mul`: `restrict f * restrict g = restrict (f*g)`.
- `mulInto_surjective`: pointwise: given target `TailAt.mk p E ψ'`, witness
  `TailAt.mk p D (restrict f⁻¹ * ψ')`; `mulIntoAt_mk` + `mul_assoc`-free computation
  `restrict f * (restrict f⁻¹ * ψ') = (restrict f * restrict f⁻¹) * ψ' = restrict (f * f⁻¹) * ψ'
  = 1 * ψ'` (`map_mul`, `mul_inv_cancel₀ hf0` in `Field (ℳ X)`, `map_one`, `one_mul`); assemble
  by `DFinsupp.mapRange_surjective`.
- `nuL`: `toFun f := mulInto ↑f (fun p => by simpa [Divisor.sub_apply] using (mem_linSys_iff.mp f.2 p))`;
  `map_add'`/`map_smul'` from the `f`-linearity lemmas + `LinearMap.ext` + `DFinsupp.ext`.
- `nuL_mulInto_inv`: `DFinsupp.ext` + `Quotient.ind` + the same field cancellation; the `f⁻¹`
  bound `((A-C-div f) p - (A-C) p : ℤ) = -(divisor f p)` vs `f⁻¹.ord p`: by `Mero.ord_eq_divisor`
  (helper: `f ≠ 0` ⟹ `ord = (divisor f p : WithTop ℤ)` via `Mero.ord_ne_top` + `untop₀`) +
  `divisor_inv` — equality, hence `le_of_eq`.
- `LinSys.divisor_ge`: pointwise `divisor_apply` + `mem_linSys_iff` + `untop₀`-monotone with
  `Mero.ord_ne_top`.

### P2. `Pairing.lean`, construction layer

- `readAt`: define by `liftOn` on the underlying codiscrete germ (the same pattern as
  `MeroGermOn.ord`, `OrderEval.lean:37`): representative `f ↦ ↑(f ∘ (chartAt ℂ p).symm)`.
  Congruence obligation: `f =ᶠ[codiscreteWithin source] g ⟹ f∘e.symm =ᶠ[𝓝[≠] (e p)] g∘e.symm`
  — `eventuallyEq_codiscreteWithin_iff_of_isOpen` gives 𝓝[≠]-agreement at `p` on the `X` side
  (`OrderEval`'s own step), then the chart transport bridge (`Predicates.lean`'s
  `eventually_nhdsNE_comp_chart`-family, already consumed by `ordAtX_congr`) finishes. Linearity:
  `exists_rep` on both arguments + `readAt_mk` + `Germ.coe_add/smul` (`mk` is additive). ~50 lines,
  the file's grindiest definition, but a direct transcription of an existing pattern.
- `readAt_tailGerm`: `readAt_mk` on `tailGerm`'s defining `mk`; the read is
  `(chartAt p (chartAt p |>.symm z) - chartAt p p)^m =ᶠ[𝓝[≠] center] (z - center)^m` by
  `right_inv` on a target-neighborhood (`Germ` equality from `EventuallyEq`).
- `pairAt`: `resL (chartAt ℂ p p) ∘ₗ mulRead` where `mulRead` is `readAt p` post-multiplied by
  the fixed germ `↑(θ.coeffAt p)` and cod-restricted into `meromorphicGermsAt` (membership:
  `meromorphicAt_coeffAt` + the germ's own meromorphy `meromorphicGerm_readAt` +
  `MeromorphicAt.mul` — all at the `Germ.liftOn` level `GermFunctionals` already handles).
  `pairAt_mk` unfolds to `laurentCoeffL_mk`-style computation. `pairAt_tailGerm` =
  `readAt_tailGerm` + `resAt_congr` + **`resAt_zpow_mul`** — the serre-cech-spiked core.
- `pairAt_eq_zero_of_mem_ordGe`: case `θ = 0` (from `mem_omegaSpace_iff` disjunct): coeff `≡ 0`,
  `resL` of the zero germ is 0. Case `-(-D) ≤ θ.divisor`: the product germ's
  `meromorphicOrderAt ≥ (-(D p)) + D p = 0` (`meromorphicOrderAt_mul` + `readAt`-order =
  `ψ.ord p` (defeq through `ord_apply_mk`) + `divisor_apply`/`untop₀` handling of `ord = ⊤`),
  then `resAt_of_order_nonneg`. ~35 lines.
- `pairTailAt` := `Submodule.liftQ` (spike item 3); `pairT` := `DFinsupp.lsum ℕ` (spike item 4;
  ⚠ recorded: `lsum_single`'s semiring argument is EXPLICIT — `DFinsupp.lsum_single ℕ F p m`).
- `pairT_trunc`/`pairT_mulInto`: by `DFinsupp.lhom_ext` (spike item 5) reduce to singles, then
  `Quotient.ind`: both sides on `TailAt.mk p _ ψ` are `pairAt`-values;
  for `pairT_trunc` literally the same value (`liftQ_apply` twice + `truncAt_mk`);
  for `pairT_mulInto`: LHS `= pairAt θ p (restrict f * ψ)`, RHS `= pairAt (f•θ) p ψ`; both are
  `resL` of germs that agree on `𝓝[≠] center`: LHS-germ `= read(restrict f)·read ψ·↑(θ.coeffAt p)`
  (`readAt_mul`), RHS-germ `= read ψ·↑((f•θ).coeffAt p)` with
  `(f•θ).coeffAt p = f.holoRepr∘e.symm · θ.coeffAt p` (**`rfl`**, `coeffAt_smul_mero`) and
  `read (restrict f) = ↑(f.holoRepr ∘ e.symm)`-as-germ (helper `readAt_restrict_global`, via
  `restrict_mk` on a representative + `holoRepr_eventuallyEq_nhdsNE` + chart transport).
  Commutativity of `Germ` multiplication closes. ~45 lines including the helper.
- D5 ord kit: `MForm.ord_smul` per §3 D5 (~30 lines); `divisor_smul_mform` pointwise
  (`divisor_apply` + `untop₀` of a sum of non-`⊤`s, `Mero.ord_ne_top` + `MForm.ord_eq_top_iff`
  through `eq_zero_or_forall_ord_ne_top`); `smul_mem_omegaSpace` from these by
  `mem_omegaSpace_iff` + pointwise lattice arithmetic.
- D6: `pairT_congr` by `lhom_ext` + `Quotient.ind`: `pairAt` values are `resL` of germs equal on
  `𝓝[≠] center` (the coeff `=ᶠ` hypothesis multiplies through). `smul_smul_coeffAt_eventuallyEq`:
  both sides are (by `coeffAt_smul_mero`, `rfl`) `a.holoRepr·b.holoRepr·θ.coeff` vs
  `(a*b).holoRepr·θ.coeff`; `exists_rep a/b` + `mk_mul` + three `holoRepr_eventuallyEq_nhdsNE`
  + chart transport. ~35 lines.

### P3. `pairT_alpha` — the ∑Res=0 well-definedness (the ONLY residue-theorem citation)

1. `f = 0`: `alphaL D 0 = 0`, done. Else `hf0 : f ≠ 0`.
2. Choose the common `Finset`: `S :=` (laurent-tails' `alphaFinset D f`) `∪ (f•θ).PoleSet`-witness
   (or directly the pole/support finsets of `f`, `θ`, `D` — whatever residue-theorem's final
   statement makes cheapest; with the requested finsum form, no finset is needed at all: both
   sides are `∑ᶠ`).
3. Term identification at each `p`: `pairTailAt θ hθ p ((alphaL D f) p) = pairAt θ p (restrict f)`
   (by `alpha_apply` + `liftQ_apply`) `= resAt (f-rep ∘ e.symm · θ.coeffAt p) center`
   (`pairAt_mk` on `restrict_mk` of a representative) `= resAt (f.holoRepr∘e.symm · θ.coeffAt p)
   center` (`resAt_congr` + `holoRepr_eventuallyEq_nhdsNE` + chart transport) — exactly the
   summand of `sum_resAt_eq_zero` (and, via `coeffAt_smul_mero`-`rfl`, `= (f•θ).resAt p`).
4. Both sums have support inside a common finite set, and OFF the tail support the residue
   summand also vanishes (`(alphaL D f) p = 0 ⟹ f.ord p ≥ -(D p)` ⟹ product order
   `≥ -(D p) + D p = 0` ⟹ `resAt = 0` — the same `pairAt_eq_zero_of_mem_ordGe` computation).
   `finsum_eq_sum_of_support_subset`-style bookkeeping (or `DFinsupp.sumAddHom` unfolding of
   `lsum`) matches the two sums term by term; residue-theorem's `= 0` closes. ~40 lines.
   This is the derivation serre-cech's §5 P3 already recorded, transposed to the germ model.

### P4. The test-vector computations (3.3-injectivity and 3.6, shared core)

Shared core lemma (once):
```lean
theorem pairAt_tailGerm_order_ne_zero {θ : MForm X} {p : X} (hne : θ.ord p ≠ ⊤) :
    pairAt θ p (RS.Cech.tailGerm p (-1 - (θ.ord p).untop₀)) ≠ 0
```
Proof: with `k := (θ.ord p).untop₀` and `m := -1-k`, `pairAt_tailGerm` gives the value
`laurentCoeffAt (θ.coeffAt p) center (-1 - (-1 - k)) = laurentCoeffAt … k` (exponent algebra by
`ring`/`omega` on ℤ); `k = (meromorphicOrderAt (θ.coeffAt p) center).untop₀`
(defeq), and `laurentCoeffAt_order_ne_zero (meromorphicAt_coeffAt θ p …) hne` finishes — the
serre-cech spike verbatim (`scratch_serrec.lean`, incl. its recorded `set`-refolding pitfall). ~12 lines.

- **`pairT_ne_zero`** (Miranda 3.3, injectivity): `θ ≠ 0` + `eq_zero_or_forall_ord_ne_top` ⟹
  `∀ p, θ.ord p ≠ ⊤`; `ConnectedSpace ⟹ Nonempty X`, pick `p`; `k := (θ.ord p).untop₀`;
  membership `D p ≤ k` from `hθ` (`mem_omegaSpace_iff` + `divisor_apply`); the witness
  `τ := singleT p D (tailGerm p (-1-k))` satisfies `pairT θ hθ τ = pairAt … ≠ 0`
  (`pairT_singleT` + core lemma). Note `τ ∈ T D` needs NO membership condition (it is a quotient
  class; it happens to be a nonzero class since `-1-k < -(D p)`, but even that is not needed).
  ~20 lines.
- **`mem_omegaSpace_of_vanishing_ker_trunc`** (MIRANDA LEMMA 3.6): `by_cases θ = 0` (then
  `zero_mem`). Else all orders finite; `by_contra`: `mem_omegaSpace_iff` fails ⟹
  `¬(D₂ ≤ θ.divisor)` ⟹ `∃ p, θ.divisor p < D₂ p`; `k := (θ.ord p).untop₀ = θ.divisor p`;
  `hθ` gives `D₁ p ≤ k`. Witness `τ := singleT p D₁ (tailGerm p (-1-k))`:
  `truncT h τ = singleT p D₂ (tailGerm …) = 0` by `truncT_singleT` + `singleT_eq_zero_iff` +
  `ord_tailGerm_self` (`(-(D₂ p) : WithTop ℤ) ≤ -1-k ⟺ k < D₂ p` ✓, integer arithmetic +
  `WithTop` casts by `exact_mod_cast`/`omega`); but `pairT θ hθ τ ≠ 0` (core lemma) contradicts
  `hker τ`. ~35 lines. **This is Miranda's whole 3.6 proof; the "order downgrade" is exactly this
  one computation.**

### P5. `Counting.lean` — MIRANDA LEMMA 3.4 (the counting step; the unit's pivot)

1. **`nuPairDual`.** For fixed data, the underlying function is
   `(f₁,f₂) ↦ Submodule.liftQ (range (alphaL (A-C))) (φ₁ ∘ₗ nuL A C f₁ - φ₂ ∘ₗ nuL A C f₂) hkill`
   where `hkill` : the difference kills `alphaL (A-C) g` — by `nuL_alpha`:
   `φ₁ (alphaL A (f₁·g)) - φ₂ (alphaL A (f₂·g)) = 0 - 0` (`hα₁`, `hα₂`). Linearity in `(f₁,f₂)`:
   `LinearMap.ext` + `Submodule.Quotient.mk_surjective` reduction to representatives, where it is
   `nuL`'s own linearity (P1) — the serre-cech P2-step-3 packaging pattern, budgeted MEDIUM there
   and here. ~50 lines.
2. **`two_l_le_h1_of_injective`** — the spike-verified chain (spike item 1):
   `LinearMap.finrank_le_finrank_of_injective hinj` (codomain `Module.Finite` via
   `instModuleDualFiniteDimensional` from `H1Tail.finiteDimensional (A-C)`, laurent-tails), then
   `Module.finrank_prod`, `Subspace.dual_finrank_eq`, `finrank ↥(LinSys C) = l C` (defn),
   `finrank (H1Tail (A-C)) = h1tail (A-C) = h1 (A-C)` (`h1tail_eq_h1`); `omega`. ~15 lines.
3. **Arithmetic ledger** (all in ℤ; spike item 6): from `chi (A-C) = chi 0 + (A-C).degree`
   (finiteness) and `chi = l - h1` (defn): `h1 (A-C) = l (A-C) - chi 0 - A.degree + C.degree`
   (degree additivity, mero). `l (A-C) ≤ l A` (`l_mono`, `A - C ≤ A` from `0 ≤ C`).
   `chi 0 + C.degree ≤ l C` (`chi_zero_add_degree_le_l`). Combining with step 2's
   `2·l C ≤ h1 (A-C)`: `C.degree ≤ l A - 3·chi 0 - A.degree` — `omega`. ~20 lines.
4. **Not-injective at the explicit `C`.** `P : X` (Nonempty from Connected);
   `n := (l A - 3•chi 0 - A.degree).toNat + 1 : ℕ`; `C := Divisor.single P n`
   (canonical-forms Compat / meromorphic-and-divisors request; `degree_single : degree = n`).
   If `nuPairDual` were injective, steps 2–3 give `(n : ℤ) ≤ l A - 3•chi 0 - A.degree < n`
   (`Int.toNat` handled by `omega`, spike-verified) — contradiction. So not injective;
   `LinearMap.ker_eq_bot` + `Submodule.exists_mem_ne_zero_of_ne_bot` (spike item 2) extract
   `(f₁,f₂) ≠ 0` with `nuPairDual … (f₁,f₂) = 0`. ~25 lines.
5. **Kernel element ⟹ the witness pair.** `nuPairDual (f₁,f₂) = 0` unfolds (via
   `nuPairDual_apply` + `H1Tail.mk`-surjectivity) to `φ₁ ∘ₗ nuL A C f₁ = φ₂ ∘ₗ nuL A C f₂`.
   Nonzeroness of BOTH: if `f₂ = 0` then `nuL A C f₂ = 0` (map_zero), so `φ₁ ∘ nuL f₁ = 0` with
   `f₁ ≠ 0` (pair nonzero) ⟹ `φ₁ = 0` on `range (nuL f₁) = ⊤` (`nuL_surjective`) — contra `h₁`;
   symmetric for `f₁ = 0` (contra `h₂`). This is repair #1 of §1.3. ~20 lines.

Total ~130 lines of proof for Lemma 3.4, no step above 50.

### P6. `Duality.lean` — the surjectivity endgame (Miranda PDF 202–203, transcribed)

`exists_pairT_eq (D) (φ) (hα)`:

0. `by_cases φ = 0`: witness `θ := 0`, `pairT_zero`. Else `hφ : φ ≠ 0`.
1. **Reference form.** `obtain ⟨ω₀, hω₀⟩ := exists_ne_zero_mform` (canonical-forms);
   `K := canonicalDivisorOf ω₀ = ω₀.divisor`; `A := D ⊓ K`;
   `hAD : A ≤ D := inf_le_left`; `hω₀A : ω₀ ∈ Ω(-A)` (`mem_omegaSpace_iff`: `A ≤ K = ω₀.divisor`
   by `inf_le_right`).
2. **The two functionals on `T A`.** `φA := φ ∘ₗ truncT hAD`; vanishing on `im α_A` by
   `truncT_alpha` + `hα`; `φA ≠ 0` (if `φ ∘ₗ truncT = 0`, `truncT_surjective` forces `φ = 0`).
   `φ₂ := pairT ω₀ hω₀A ≠ 0` (`pairT_ne_zero`), vanishing on `im α_A` (`pairT_alpha`).
3. **Lemma 3.4** at `A`: get `C ≥ 0`, `f₁ f₂ ∈ LinSys C` both `≠ 0` with
   `[†] : φA ∘ₗ nuL A C f₁ = pairT ω₀ hω₀A ∘ₗ nuL A C f₂`.
4. **Rewrite the RHS** by `pairT_mulInto` (`f := ↑f₂`, bound from `mem_linSys_iff`; membership
   `f₂•ω₀ ∈ Ω(-(A-C))` by `smul_mem_omegaSpace` at `F := C`, `E := A`, plus `A - C = -( -(A)+C)`
   bookkeeping — pointwise lattice arithmetic): `[†'] : φA ∘ₗ nuL A C f₁ = pairT (↑f₂ • ω₀) h₂m`.
5. **Invert `μ_{f₁}`.** `E₁ := A - C - divisor ↑f₁`; `hE₁A : E₁ ≤ A` (from
   `LinSys.divisor_ge f₁`: `-C ≤ divisor f₁` ⟹ `C + divisor f₁ ≥ 0`). Define
   `η := (↑f₂ * (↑f₁)⁻¹) • ω₀` and `hηE₁ : η ∈ Ω(-E₁)`:
   `divisor η = divisor f₂ - divisor f₁ + K ≥ -C - divisor f₁ + A = E₁` pointwise
   (`divisor_smul_mform` + `divisor_mul`/`divisor_inv`; `η ≠ 0` side conditions from
   `f₁, f₂, ω₀ ≠ 0` via `smul_ne_zero'`/field). Claim
   `[‡] : pairT η hηE₁ = φA ∘ₗ truncT hE₁A`: for every `τ' : T E₁`,
   `φA (truncT hE₁A τ') = φA (nuL A C f₁ (mulInto (↑f₁)⁻¹ hinv τ'))` (`nuL_mulInto_inv`, read
   right-to-left) `= pairT (↑f₂ • ω₀) h₂m (mulInto (↑f₁)⁻¹ hinv τ')` (`[†']`)
   `= pairT ((↑f₁)⁻¹ • (↑f₂ • ω₀)) h' τ'` (`pairT_mulInto` at `f := (↑f₁)⁻¹`, exact bound via
   `Mero.ord_eq_divisor` + `divisor_inv`) `= pairT η hηE₁ τ'` (`pairT_congr` +
   `smul_smul_coeffAt_eventuallyEq` + `mul_comm` in `ℳ X`).
6. **3.6, first application** (`D₁ := E₁`, `D₂ := A`): `[‡]` shows `pairT η hηE₁` vanishes on
   `ker (truncT hE₁A)` (its value factors through `truncT`); conclude `hηA : η ∈ Ω(-A)`.
   Then `[§] : φA = pairT η hηA`: both compositions with the surjective `truncT hE₁A` agree
   (`pairT_trunc` on the left of `[‡]`), cancel surjectivity (`LinearMap.ext` +
   `truncT_surjective`).
7. **3.6, second application** (`D₁ := A`, `D₂ := D`): `pairT η hηA = φA = φ ∘ₗ truncT hAD`
   vanishes on `ker (truncT hAD)`; conclude `hηD : η ∈ Ω(-D)`. Then
   `φ = pairT η hηD`: both compositions with the surjective `truncT hAD` agree
   (`pairT_trunc` turns `pairT η hηD ∘ₗ truncT hAD` into `pairT η hηA = φA`); cancel. Witness
   `⟨η, hηD, …⟩`. ∎

~90 lines structured as: steps 4–5 as one `private` lemma (`exists_eta`), steps 6–7 inline.
Every citation in the chain is a named lemma from §5; no step exceeds ~40 lines.

`resMap_surjective`: given `Λ : Dual (H1Tail D)`, `φ := Λ ∘ₗ (range (alphaL D)).mkQ` kills
`im α` by construction (`mkQ` of members is 0); `exists_pairT_eq` gives `(θ, hθ)`;
`resMap D ⟨θ,hθ⟩ = Λ` since both compose with the surjective `H1Tail.mk` to `pairT θ hθ = φ`
(`resMap_mk` + `LinearMap.ext`). ~15 lines. `resMap_injective`: `resMap ⟨θ,hθ⟩ = 0` ⟹
precomposing with `H1Tail.mk`: `pairT θ hθ = 0` ⟹ `θ = 0` (`pairT_ne_zero` contrapositive) ⟹
`Subtype.ext`. ~10 lines.

### P7. The statement bank (`Duality.lean`, each ≤ 12 lines)

- `i_neg_eq_h1`: `RS.i (-D) = finrank Ω(-D)` (defn) `= finrank (Dual (H1Tail D))`
  (`LinearEquiv.finrank_eq (resEquiv D)`) `= finrank (H1Tail D)` (`Subspace.dual_finrank_eq`)
  `= h1tail D` (defn) `= h1 D` (`h1tail_eq_h1`).
- `l_sub_eq_h1`: `i_eq_l_add_canonicalDivisorOf h₀ (-D)` gives `i (-D) = l (-D + K)`;
  `-D + K = K - D` (`neg_add_eq_sub`/`add_comm` on the divisor group); chain with `i_neg_eq_h1`.
- `h1_zero_eq_l_K` := `l_sub_eq_h1` at `D := 0` + `sub_zero`, symmetrized.
- `h1_zero_eq_genus`: `i_neg_eq_h1` at `D := 0` + `neg_zero` gives `i 0 = h1 0`;
  `genus_eq_finrank_omegaSpace_zero` (canonical-forms D12) identifies `i 0 = genus X`.
- `h1_canonical`: `l_sub_eq_h1` at `D := K` + `sub_self` + `RS.l_zero` (mero, `l 0 = 1`).

---

## 7. Junk-value and convention ledger

- `pairT`'s value on a tail class is computed through `readAt`, which is representative-honest
  (`liftOn` over the codiscrete quotient; junk never enters — the `𝓝[≠]` filter of the germ
  functional `resL` is exactly the locus where all representatives and `holoRepr` agree).
- `pairT θ hθ` carries its membership PROOF, but the value is proof-irrelevant and, for `θ = 0`,
  is honestly `0` — no junk statement can become vacuously true (`pairT_ne_zero` explicitly
  requires `θ ≠ 0`).
- `mulInto` for `f = 0` is the honest zero map (Miranda's `μ_0` does not exist; ours is the
  `t∘μ`-composite which extends linearly by 0 — needed ONLY to make Lemma 3.4's pair map linear;
  every place a genuine `μ_f` is inverted carries `f ≠ 0`).
- The `-1-k` exponent convention and the strict bound `k < -D(p)` are pinned in §0.2 and used in
  exactly two proofs (P4's core lemma and 3.6's kernel membership); both reduce to
  `D p ≤ k ↔ -1-k < -(D p)` over ℤ (same one-liner serre-cech recorded).
- `(f*g)•θ = f•(g•θ)` is NOT assumed at the structure level (false at `holoRepr` junk points,
  §3 D5 ⚠); only the `=ᶠ[𝓝[≠]]` collapse (D6) is used. This keeps every statement honest under
  canonical-forms' current pointwise `MForm.ext`.

---

## 8. Risks, ranked

1. **R1 (HIGH, external, schedule): laurent-tails' comparison** (`H1Tail.equiv`, their R1 —
   Leray-based surjectivity). We consume it via `H1Tail.finiteDimensional` (needed by P5 step 2)
   and `h1tail_eq_h1` (P7) — nothing else. Their R2 gate (`toH1_injective`) has LANDED
   (`Cech/Injectivity.lean:247`), halving the exposure. **Mitigation:** files 1–2 and Lemma 3.6 /
   the endgame's functional-level statements (`exists_pairT_eq`) do NOT need the comparison —
   build order puts them first; if `H1Tail.equiv` arrives hypothesis-parametrized (their
   documented fallback), `i_neg_eq_h1` inherits the same explicit hypothesis and the orchestrator
   is flagged (CONVENTIONS-honest, not vacuous).
2. **R2 (MEDIUM): the residue-theorem atom's timing/shape** (`Jacobian/ResidueTheorem/` not
   started; trace route now primary per its orchestrator addendum; `FormTrace/` currently empty;
   one open sorry in `PlanarStokes/AnnulusResidue.lean` belongs to the fallback route only).
   Consumed in exactly ONE lemma (`pairT_alpha`); the requested `MForm`-level signature is
   recorded in `docs/requests/residue-theorem.md` and re-confirmed (§11). Shape drift costs one
   edit; slippage blocks `pairT_alpha` and hence files 3–4 but nothing in files 1–2.
3. **R3 (MEDIUM): `readAt`'s codiscrete→`𝓝[≠]` chart-transport congruence** (P2). The pattern
   exists (`ordAtX_congr`, `MeroGermOn.ord`'s liftOn), but this is the one genuinely new
   germ-plumbing definition; if the transport lemma shapes fight, fallback: define `readAt`'s
   underlying function via `holoRepr` (canonical, choice-free) and prove `readAt_mk` as a lemma
   via `holoRepr_eventuallyEq_nhdsNE` — linearity then routed through `readAt_mk` on
   `exists_rep`-chosen representatives (strictly more lines, zero new mathematics).
4. **R4 (MEDIUM-LOW): canonical-forms files 4–6 in flight** (`OmegaSpace`/`i`/`Ω_iso_linSys`/
   `exists_ne_zero_mform`/`eq_zero_or_forall_ord_ne_top`/`genus_eq_finrank_omegaSpace_zero`).
   Frozen shapes; files 1–3 of their plan are already on disk matching the design exactly
   (verified §1.1), so drift risk is low. The `MForm.ord_smul` gap is OURS to Compat regardless
   (request filed).
5. **R5 (LOW-MEDIUM): the `nuPairDual` linear-packaging** (P5 step 1) — the known-fiddly
   "family of liftQ's as one LinearMap" pattern; spike item 3 verified the single-`liftQ` core;
   serre-cech's P2 fallback (explicit `mk'` against representatives) applies verbatim if needed.
6. **R6 (LOW): `Divisor.single`/`degree_single` availability** (still absent from
   `Meromorphic/Divisor.lean`, request already filed by canonical-forms; their Compat lands with
   their file 5). Worst case: our own 12-line Compat copy (their recipe, §1.6 of their doc).
7. **R7 (LOW): finiteness' χ ledger gate** (`Chi.lean` not on disk; gated on cech's
   Skyscraper fragment + `finrank_window`, itself in progress at `WindowRank.lean`). Frozen
   shapes `chi_eq_chi_zero_add_degree`/`chi_zero_add_degree_le_l`/`l_mono` consumed as cited;
   blocks file 3 only.

---

## 9. Downstream interfaces (FROZEN)

### 9.1 riemann-roch (thin unit — everything below is ℤ-arithmetic + one function extraction)

**Cites** (all frozen above/upstream): `TailDuality.l_sub_eq_h1`, `TailDuality.h1_zero_eq_genus`,
`TailDuality.h1_zero_eq_l_K`, `TailDuality.h1_canonical`; `Finiteness.chi_eq_chi_zero_add_degree`,
`Finiteness.chi` (defn `= l - h1`), `chi_zero_add_degree_le_l`; `RS.l_zero`;
`canonicalDivisorOf` (+ `canonicalDivisorOf_linearEquiv` if it wants `K`-independence remarks);
`Divisor.degree` additivity; `exists_ne_zero_mform`. **Proves:**
```lean
theorem riemannRoch {ω₀ : MForm X} (h₀ : ω₀ ≠ 0) (D : Divisor X) :
    (RS.l D : ℤ) - (RS.l (RS.canonicalDivisorOf ω₀ - D) : ℤ)
      = D.degree + 1 - (RS.genus X : ℤ)
-- proof: rewrite l(K-D) = h1 D (l_sub_eq_h1); chi D = chi 0 + deg D; chi = l - h1;
--        chi 0 = 1 - h1 0 (l_zero) = 1 - genus (h1_zero_eq_genus); omega.
theorem l_K_eq_genus (h₀) : RS.l (RS.canonicalDivisorOf ω₀) = RS.genus X
-- := h1_zero_eq_l_K ▸ h1_zero_eq_genus
theorem degree_canonicalDivisorOf (h₀) :
    (RS.canonicalDivisorOf ω₀).degree = 2 * (RS.genus X : ℤ) - 2
-- riemannRoch at D := K: l K - l 0 = deg K + 1 - g; l K = g (l_K_eq_genus); l 0 = 1; omega.
theorem riemann_inequality (D) : D.degree + 1 - (RS.genus X : ℤ) ≤ (RS.l D : ℤ)
-- chi_zero_add_degree_le_l + chi 0 = 1 - genus; (duality-free once h1_zero_eq_genus exists).
-- + the genus-0 single-simple-pole consequence (headline feed): from riemann_inequality at
--   D := Divisor.single P 1 with genus = 0: l ≥ 2 > 1 = l 0, extract a nonconstant f with a
--   single simple pole (linSys_zero_eq_span_one for the "nonconstant" part).
```
riemann-roch should NOT re-derive any duality or ledger content; if it finds itself touching
`T D`, `pairT`, or `chi`'s internals, the interface above has failed — flag the orchestrator.

### 9.2 cech-h1-genus (one paragraph, as promised)

Its blueprint mandate "`dim H¹(X,𝒪) = g`" is **exactly our `h1_zero_eq_genus`**
(`RS.Finiteness.h1 (0 : Divisor X) = RS.genus X`, where `RS.Finiteness.h1 0 :=
finrank ℂ (RS.Cech.H1 (0 : Divisor X))` — the honest cohomological statement, and `genus :=
finrank ℂ (Form1 X)` is CC1's analytic genus). The chain behind it: `h1 0 = i 0` (our duality at
`D = 0`) and `i 0 = genus X` (canonical-forms' `genus_eq_finrank_omegaSpace_zero`, i.e. D12's
`holomorphicMFormsEquiv : Form1 X ≃ₗ Ω(0)` — CONFIRMED present in canonical-forms' frozen design,
their §4.5, with the explicit remark that `l(K) = g` becomes "a one-line corollary once
`i 0 = h1 0` lands"; that is Miranda (3.9)+(3.10) with his "topological genus" replaced by our
CC1 genus — no topology needed). cech-h1-genus therefore consumes: `TailDuality.h1_zero_eq_genus`
(restate/re-export at whatever name the challenge API wants), `TailDuality.h1_zero_eq_l_K`, and
optionally packages `l_K_eq_genus` if riemann-roch doesn't. Its blueprint-suggested machinery
(cup-product kill, effective-divisor vanishing comparison) is **unnecessary** on this route —
its builder should treat the unit as an assembly file and report surplus scope to the
orchestrator rather than build Forster §17.4–17.5 material.

### 9.3 Everyone else

- **serre-duality-cech**: obligation D6 discharged at the exact frozen shape; their D5
  (`finrank_omegaSpace_le`) not instantiated (reconciliation §0.1); no action needed from them.
- **laurent-tails**: consumed per §1.2 + requests §11. Their `mulTail`/`mulTailEquiv` is NOT
  a dependency of this unit anymore (D3) — orchestrator may re-prioritize.

---

## 10. Spike report (`scratch_tdual.lean`, project root)

Gated per protocol (`pgrep -cx lean` loop; 0 running), `lake env lean scratch_tdual.lean`:
**compiles clean, exit 0** after two recorded fix rounds. Verified at the pin:

1. **The Lemma 3.4 counting core** (P5 step 2, the design's flagged riskiest API): an injective
   `Ψ : (V × V) →ₗ[ℂ] Module.Dual ℂ H` with `V, H` fin-dim yields `2·finrank V ≤ finrank H`, via
   `LinearMap.finrank_le_finrank_of_injective` (the `Module.Finite` instance on `Dual ℂ H`
   resolves automatically from `instModuleDualFiniteDimensional`), `Module.finrank_prod`,
   `Subspace.dual_finrank_eq` (which is **unconditional** — for infinite-dimensional `H` both
   sides are junk-0, so no finiteness prerequisite beyond what we have; our `H := H1Tail (A-C)`
   is honestly fin-dim via laurent-tails' instance), and `omega`.
2. **Kernel extraction from non-injectivity**: `LinearMap.ker_eq_bot` +
   `Submodule.exists_mem_ne_zero_of_ne_bot` produce the nonzero kernel pair (P5 step 4).
3. **`Submodule.liftQ` descent + `liftQ_apply`** — the `pairTailAt`/`resMap`/`nuPairDual` shape.
4. **`DFinsupp.lsum ℕ` + `lsum_single`** — ⚠ two real findings: (i) the semiring argument of
   `DFinsupp.lsum_single` is **explicit** (`DFinsupp.lsum_single ℕ F p m`; writing
   `DFinsupp.lsum_single F p m` mis-elaborates `F` into the semiring slot); (ii) `DFinsupp.single`
   at abstract fibre types needs decidability instances — discharge with `open scoped Classical`
   (laurent-tails' idiom), NOT with ad-hoc `[DecidableEq (M p)]` arguments.
5. **`DFinsupp.lhom_ext`** — the reduction of `pairT_trunc`/`pairT_mulInto`-style identities to
   single-point checks.
6. **The explicit-`n` arithmetic**: `omega` closes both `B < (B.toNat + 1 : ℤ)` and the full
   3.4 growth-contradiction inequality chain (no `Int.toNat` lemma hunting needed).
7. Import finding (recorded for the builder): pure-linear-algebra files over `ℂ` need
   `Mathlib.Data.Complex.Basic` for the `Field ℂ` instances (the first run failed with
   `Semiring ℂ` synthesis errors); no analysis import required at this layer.

`scratch_tdual.lean` left in the repo root as the builder's reference.

---

## 11. Coordination notes filed

- `docs/requests/laurent-tails.md` (appended, "From serre-duality-tails"): (a) export the
  pointwise apply lemma `alpha_apply (D f p) : alphaL D f p = TailAt.mk p D (restrict … f)`;
  (b) keep `H1Tail D` a transparent `T D ⧸ range (alphaL D)` and export `H1Tail.mk_surjective` +
  `H1Tail.mk_eq_zero_iff`; (c) `TailAt.mk_eq_zero_iff` as `@[simp]`; (d) notice: `mulTail`/
  `mulTailEquiv` no longer consumed by us (D3) — deprioritize freely; (e) their R2 gate
  (`toH1_injective`) has landed on disk — comparison injectivity is unblocked.
- `docs/requests/canonical-forms.md` (created): (a) export `MForm.ord_smul` (+ `divisor`-level
  corollary) — we Compat it meanwhile (D5); (b) confirm `eq_zero_or_forall_ord_ne_top` (their D5)
  and `mem_omegaSpace_iff` land as frozen; (c) ⚠ heads-up for their OneDimensional/module-law
  builder: `smul_smul`/`mul_smul` as a pointwise `MForm` **equality** is falsifiable at
  `holoRepr` junk points (§3 D5) — the `=ᶠ[𝓝[≠]]` version suffices for every currently-known
  consumer (us included); recommend they verify before committing to the structure-level law.
- `docs/requests/residue-theorem.md` (appended): confirmation that serre-duality-tails consumes
  the already-requested `sum_resAt_eq_zero` shape, now in the germ-model reduction (§6 P3), and
  the note that with `coeffAt_smul_mero` being `rfl` the statement is literally
  `∑ᶠ x, (f • θ).resAt x = 0`; a `Finset`-flexible `residueTheorem {S} (hS)` variant is equally
  fine — one adapter lemma isolates the citation either way.
- DAG note to orchestrator: the `proper-map-degree` edge into this unit is unused by this design
  (§1.2) — no blueprint edit proposed, recorded for scheduling freedom.
