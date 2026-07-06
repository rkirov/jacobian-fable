# Design: planar-stokes-atoms (`Jacobian/PlanarStokes/`)

Blueprint unit **planar-stokes-atoms**: "Planar integration atoms: compact-support Stokes in the
plane, annulus residue integrals, holomorphic change of variables for contour integrals... prove
the one honest 2-dimensional Stokes you need on rectangles/disks; everything global reduces to it
via PoU." **Builds on:** dbar-solvability, residue-calculus. **Consumers:** residue-theorem
(primary — "cover X, write the form as sum of locally supported pieces, apply planar Stokes to
each; boundary terms cancel; what survives is `∑Res`"), abel-weak-solutions (lighter use, see §11).

Routing decision #2 (`clean_room_blueprint.md`): the residue **theorem** (`∑Res=0`) is
Stokes-only/genus-agnostic; the residue **functional** of Serre duality is a *different* object
built later (serre-duality-tails, via Miranda's tail pairing) and must NOT be shortcut through
this unit. Concretely: **we build the atoms residue-theorem consumes to prove `∑Res=0`; we do
NOT build any `H¹(Ω)→ℂ` functional, any Serre pairing, or any general Stokes theorem on `X`.**
Everything here is stated for bare `ℂ→ℂ` functions; no manifolds, no forms-on-`X`, no
`Form1`/`Form01` bundle theory (canonical-forms/dbar-solvability own those; residue-theorem is
the one place chart-local coefficients of a 1-form on `X` get plugged into our atoms).

References: Forster §10 (Thm 10.21, book 78–79 = PDF ~86, context only — the theorem itself is
residue-theorem's job); Miranda GSM5 PDF 198–200 (residue map, context for the constant
convention). No new textbook computation is used below beyond what routing decision #3
(`docs/design/dbar-solvability.md` §0) already set up: the polar/Wirtinger algebra is reused
verbatim, never re-derived.

All mathlib names below verified by reading source at the pin
(`.lake/packages/mathlib/Mathlib/...`); the riskiest new algebraic step (the Leibniz rule for
`wirtingerDbar` and its composition with `Complex.exp`) is compiled in the spike (§9).

---

## 0. Mandatory reading, digested

- **`docs/design/dbar-solvability.md`**: owns the Wirtinger API (`Jacobian/Dbar/Wirtinger.lean`,
  BUILT, read in full) — `wirtingerD`, `wirtingerDbar`, `fderiv_apply_eq_wirtinger`, the
  Cauchy–Riemann bridge (`wirtingerDbar_eq_zero_of_differentiableAt`,
  `differentiableAt_iff_wirtingerDbar_eq_zero`), the `(0,1)` chain rule
  (`wirtingerDbar_comp_differentiableAt`), and regularity lemmas
  (`contDiffOn_wirtingerDbar`, `hasCompactSupport_wirtingerDbar`). Dbar's own `CauchyKernel.lean`
  (BUILT) proves `cauchyPompeiu`/13.1 via a **polar-FTC** argument specifically to avoid needing
  any 2-D Stokes (its §0.A explains the DAG reason: planar-stokes-atoms builds ON dbar-solvability,
  so dbar cannot use us). Its design explicitly deliberately avoided 2-D Stokes; **this unit
  supplies the honest 2-D Stokes atoms that dbar-solvability sidestepped and that residue-theorem
  needs.** Dbar's `SolveDisk.lean`/`PlanarPoU.lean`/`Form01.lean`/`Operator.lean`/`DiskAcyclic.lean`
  are designed but **not yet built on disk** (only `Wirtinger.lean`, `CauchyKernel.lean` exist);
  we depend only on the two built files, which is exactly what D10 promises importers
  ("no project imports, mathlib only" for the planar files).
- **`docs/design/residue-calculus.md`** + **BUILT** `Jacobian/ResidueCalculus/` (all 8 files exist
  and compile): `resAt`, `laurentCoeffAt`, `principalPartAt`,
  `MeromorphicAt.exists_principalPart_add_analyticAt` (the germ decomposition we reuse
  verbatim), `resAt_of_analyticAt`, `resAt_zpow_monomial`, and — the load-bearing import —
  **`IntegralBridge.lean`**: `circleIntegral_eq_two_pi_I_mul_resAt` and
  `MeromorphicAt.eventually_circleIntegral_eq_two_pi_I_mul_resAt`. We do not re-derive the
  circle/residue bridge; we consume it as a black box.
- **`docs/mathlib-inventory.md`** divergence-theorem section (§6, re-verified against source,
  see §1 below): mathlib's *only* 2-D Green statements are on **rectangles**
  (`MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le` and kin); no
  annulus/disk Stokes exists. **Key discovery** (not in the inventory, found by reading
  `Analysis/Complex/CauchyIntegral.lean` directly): mathlib *already* packages the rectangle
  divergence theorem, specialized to `ℂ`, as
  `Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable`, whose RHS is *literally*
  `2i·wirtingerDbar`-shaped (`I • f' z 1 - f' z I`, matching our `wirtingerDbar` up to the
  constant `2i` — verified algebraically in §2). **We build our rectangle atom as a thin
  corollary of this existing lemma, not by re-deriving from
  `integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le` ourselves.** Likewise,
  mathlib's own proof of `Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable`
  (annulus deformation for *holomorphic* integrands) goes through the **exponential
  substitution** `w = c + exp ζ` mapping a rectangle `[ln r, ln R] × [0, 2π]` onto the closed
  annulus; we reuse exactly this substitution, but with the rectangle's *non-zero-divergence*
  Wirtinger form instead of the Cauchy–Goursat zero-divergence corollary, to get an area-to-two-
  circles identity for **non-holomorphic** integrands (§7 — the actual new content of this unit).

---

## 1. Verified mathlib facts (file:line at the pin)

### 1.1 Rectangle Stokes for `ℂ → E` (`Analysis/Complex/CauchyIntegral.lean`, namespace `Complex`)

```lean
theorem integral_boundary_rect_of_hasFDerivAt_real_off_countable (f : ℂ → E) (f' : ℂ → ℂ →L[ℝ] E)
    (z w : ℂ) (s : Set ℂ) (hs : s.Countable)
    (Hc : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (Hd : ∀ x ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im) \ s,
      HasFDerivAt f (f' x) x)
    (Hi : IntegrableOn (fun z => I • f' z 1 - f' z I) ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
      I • (∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
      I • ∫ y : ℝ in z.im..w.im, f (re z + y * I) =
      ∫ x : ℝ in z.re..w.re, ∫ y : ℝ in z.im..w.im, I • f' (x + y * I) 1 - f' (x + y * I) I
                                                                             -- (:186–196)
theorem integral_boundary_rect_of_continuousOn_of_hasFDerivAt_real  -- (:231) same, s = ∅ baked in
theorem integral_boundary_rect_of_differentiableOn_real (f : ℂ → E) (z w : ℂ)
    (Hd : DifferentiableOn ℝ f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (Hi : IntegrableOn (fun z => I • fderiv ℝ f z 1 - fderiv ℝ f z I)
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) : (same boundary identity, with `fderiv ℝ f`)  -- (:248)
```

`E`: `[NormedAddCommGroup E] [NormedSpace ℂ E]`; we instantiate `E := ℂ` throughout (trivial
instance). `[[a,b]] = Set.uIcc a b` (unordered — **no `z.re ≤ w.re` hypothesis anywhere**, which
is exactly why we can pick "any big enough rectangle" freely). `s ×ℂ t := Complex.reProdIm s t`
(`Data/Complex/Basic.lean:108`, `= re ⁻¹' s ∩ im ⁻¹' t`, `mem_reProdIm : z ∈ s×ℂt ↔ z.re∈s∧z.im∈t`
`:114`). Integrability side-conditions discharge via
`ContinuousOn.integrableOn_compact [T2Space X] (hs : IsCompact s) (hf : ContinuousOn f s) :
IntegrableOn f s` (`MeasureTheory/Function/LocallyIntegrable.lean:592`) — our integrands are
always continuous on the (compact) rectangle since `g`/`u` are `ContDiffOn ℝ 1`.

### 1.2 The `2i·wirtingerDbar` identity (algebra, no new mathlib lemma — our own one-liner)

For `E = ℂ`, `f' z : ℂ →L[ℝ] ℂ`: `I • f' z 1 - f' z I = I * f' z 1 - f' z I`, and by definition
`wirtingerDbar f z = (f' z 1 + I * f' z I)/2` (`Jacobian/Dbar/Wirtinger.lean:43`), so
`2*I*wirtingerDbar f z = I*(f' z 1 + I*f' z I) = I*f' z 1 + I²*f' z I = I*f' z 1 - f' z I` (using
`I*I = -1`), i.e. **`I • f' z 1 - f' z I = 2*I*wirtingerDbar f z`** exactly — matching mathlib's
own docstring ("the integral of `2i ∂f/∂z̄`"). This is the bridge that turns the rectangle lemma
above into a `wirtingerDbar`-integral identity with zero extra analytic work.

### 1.3 Rectangle divergence theorem (raw form, for context / fallback — `MeasureTheory`, inventory §6)

```lean
theorem MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le
    (f g : ℝ × ℝ → E) (f' g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] E) (a b : ℝ × ℝ) (hle : a ≤ b)
    (s : Set (ℝ × ℝ)) (hs : s.Countable) (Hcf Hcg) (Hdf Hdg) (Hi) :
    (∫ x in Icc a b, f' x (1, 0) + g' x (0, 1)) =
      (((∫ x in a.1..b.1, g (x, b.2)) - ∫ x in a.1..b.1, g (x, a.2)) +
          ∫ y in a.2..b.2, f (b.1, y)) - ∫ y in a.2..b.2, f (a.1, y)
```
(`MeasureTheory/Integral/DivergenceTheorem.lean:428`). We do **not** use this directly — it is
what `Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable` is built from (via
`equivRealProdCLM`), and re-deriving through it ourselves would just reprove §1.1 with extra
steps. Recorded as the documented fallback if §1.1's specific corollary ever proves too rigid.

### 1.4 The `ℂ ↔ ℝ×ℝ` measure bridge (`MeasureTheory/Measure/Lebesgue/Complex.lean`)

```lean
def Complex.measurableEquivRealProd : ℂ ≃ᵐ ℝ × ℝ                              -- :43
theorem Complex.measurableEquivRealProd_apply (a) : … = (a.re, a.im) := rfl    -- :47
theorem Complex.volume_preserving_equiv_real_prod :
    MeasurePreserving Complex.measurableEquivRealProd                          -- :60
```
`Complex.reProdIm s t = re⁻¹' s ∩ im⁻¹' t = measurableEquivRealProd ⁻¹' (s ×ˢ t)` (definitional,
from `mem_reProdIm`/`measurableEquivRealProd_apply`). Bridge machinery for going from a `ℂ`-set
integral over a rectangle to the iterated real integral:
`MeasureTheory.MeasurePreserving.setIntegral_preimage_emb (he_vol) (he_emb :
MeasurableEmbedding e) (g) (s) : ∫ y in e '' s, g y ∂ν = ∫ x in s, g (e x) ∂μ` (used identically
in mathlib's own divergence-theorem proofs, e.g. `DivergenceTheorem.lean:335`),
`MeasureTheory.setIntegral_prod` (`Integral/Prod.lean:549`), and (support restriction)
`MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (h : ∀ x, x ∉ s → f x = 0) :
∫ x in s, f x ∂μ = ∫ x, f x ∂μ` (`Integral/Bochner/Set.lean:470`, exact statement — this is the
one lemma that turns a compactly-supported-in-the-rectangle global `∫ w:ℂ` integral into the
rectangle set-integral mathlib's Fubini machinery wants, and back).

### 1.5 `HasCompactSupport`/`tsupport` API used for the "glue ContDiffOn-on-U to ContDiff-globally" step

`HasCompactSupport f ↔ IsCompact (tsupport f)` (definitional); `tsupport f = closure (support f)`;
points outside `tsupport f` have an open neighborhood on which `f ≡ 0`
(`Function.notMem_tsupport_iff_eventuallyEq`-style / `eventuallyEq_zero_nhds` in the support API,
`Mathlib/Topology/Support.lean`). No such "`ContDiffOn U` + compact support `⊆ U` ⇒ global
`ContDiff`" lemma exists prepackaged (checked: no hits for
`ContDiffOn.*HasCompactSupport`/`HasCompactSupport.*ContDiffOn` under
`Analysis/Calculus/ContDiff/` or `Topology/Support.lean`); we prove the two-line gluing argument
ourselves (§4, `Compat.lean`) — it is exactly the pattern Dbar's own `SolveDisk.lean` §6 Step 1
already uses for `ContDiffBump` cutoffs (`ℂ = B ∪ (closedBall … ᶜ)`, `ContDiffAt` is local).

### 1.6 Misc named facts used in the annulus derivation

`Complex.exp_periodic : Function.Periodic Complex.exp (2*π*I)`
(`Analysis/SpecialFunctions/Trigonometric/Basic.lean:1199`); `Complex.deriv_exp : deriv exp = exp`
(`Analysis/SpecialFunctions/ExpDeriv.lean:105`); `Complex.differentiable_exp`/`differentiableAt_exp`
(`:97/:101`, `𝕜 := ℂ`); `deriv_const_add (c) : deriv (c + f ·) x = deriv f x`
(`Analysis/Calculus/Deriv/Add.lean:159`); `hasDerivAt_circleMap`/`circleMap` API already used by
ResidueCalculus (`MeasureTheory/Integral/CircleIntegral.lean`, `circleIntegral.integral` unfolds
to `∫ θ in 0..2π, deriv (circleMap c R) θ • f (circleMap c R θ)`, matching `circleMap c R θ =
c + R*exp(θ*I)`); `fderiv_fun_mul (hc hd) : fderiv 𝕜 (fun y => c y * d y) x = c x • fderiv 𝕜 d x +
d x • fderiv 𝕜 c x` (`Analysis/Calculus/FDeriv/Mul.lean`, the `fun`-headed variant — **note**:
`fderiv_mul` (no `fun`) is stated for the pointwise-notation product `c * d`, not `fun y => c y *
d y`; the spike (§9) hit this naming trap once, recorded).

---

## 2. Normalization convention (fixed here; downstream must match)

Three constants, all fixed and cross-checked against each other and against ResidueCalculus's
already-frozen `2πi` convention:

1. **Rectangle atom**: `∫(boundary) = 2i · ∫∫ wirtingerDbar` (§1.2, forced by mathlib's existing
   lemma — not a choice).
2. **Annulus atom** (new, §7): `∮_{outer} u - ∮_{inner} u = 2i · ∫∫_{annulus} wirtingerDbar(u)`
   (same constant `2i`, since it specializes the rectangle atom under the exponential
   substitution — the substitution itself contributes no extra constant, verified in §7).
3. **Smeared residue** (Atom 2, §8): `∫∫_ℂ wirtingerDbar(g)·f = -π · g(p) · resAt(f,p)`.

The `-π` in (3) is *not* a free choice — it is forced by (2) plus ResidueCalculus's
`circleIntegral_eq_two_pi_I_mul_resAt : ∮_{C(p,ε)} f = 2πi·resAt f p`: from (2) with
`u := g·f`, outer term `0` (support), `2i·∫∫wirtingerDbar(g)f = -∮_{C(p,ε)} g·f`; the
constant-near-`p` hypothesis makes `∮_{C(p,ε)} g·f = g(p)·∮_{C(p,ε)} f = g(p)·2πi·resAt(f,p)`
*exactly* (not asymptotically); so `2i·∫∫wirtingerDbar(g)f = -2πi·g(p)·resAt(f,p)`, i.e. dividing
by `2i`: `∫∫wirtingerDbar(g)f = -π·g(p)·resAt(f,p)`. **Verified on `f = 1/(z-p)` independently**
via a *second*, unrelated derivation (translating Dbar's `cauchyPompeiu`, §8.4) — both routes
give `-π`, cross-checked.

Sanity/degenerate checks: (a) `f` holomorphic throughout (`resAt = 0`) ⇒ RHS `0`, matching
Atom 1's product corollary; (b) `g ≡ 1` near `p` and elsewhere within a chart with only one pole
⇒ this is exactly the "one term of `∑ᵢ ∫∫ ∂̄ψᵢ · fᵢ`" residue-theorem needs (§11).

---

## 3. File plan

```
Jacobian/PlanarStokes.lean                  -- unit root: imports + 5–15 line API docstring  (~25)
Jacobian/PlanarStokes/Compat.lean           -- wirtingerDbar_mul (Leibniz), the ContDiffOn→
                                             --   ContDiff gluing lemma, the ℂ-rectangle ↔
                                             --   iterated-real-integral bridge               (~180)
Jacobian/PlanarStokes/CompactSupport.lean   -- Atom 1: ∫∫_ℂ wirtingerDbar g = 0, and its
                                             --   holomorphic-multiplier corollary             (~150)
Jacobian/PlanarStokes/AnnulusResidue.lean   -- the annulus identity (exp-substitution, the
                                             --   40+-line heart) + Atom 2 (smeared residue)    (~340)
```
Import spine: `Compat` (mathlib + `Jacobian.Dbar.Wirtinger`) `←` `CompactSupport` `←`
`AnnulusResidue` (which also imports `Jacobian.ResidueCalculus.IntegralBridge` and
`Jacobian.ResidueCalculus.PrincipalPart`/`Residue` for `resAt`/`principalPartAt`). No manifold
imports anywhere; everything `namespace RS`; no project-level `variable` block (mathlib-only
signatures throughout, matching Dbar's D10 hygiene so residue-theorem and abel-weak-solutions can
import us without dragging in the surface stack).

Four files total (root + 3), inside the "2–4 files" budget.

---

## 4. Design decisions

### D1 — Regularity: `ContDiff ℝ 1` / `ContDiffOn ℝ 1`, matching Dbar's `cauchyPompeiu`, not `∞`

Every atom only needs one real derivative (mathlib's rectangle lemma asks for `HasFDerivAt`, no
higher regularity). Dbar's own `cauchyPompeiu (hg : ContDiff ℝ 1 g)` already sets this precedent
(dbar-solvability's D1 uses `∞` only for the *surface* layer/`Form01`, not the planar `CauchyKernel`
layer). Consumers (residue-theorem's PoU pieces) will hold `ContDiffOn ℝ ∞` bump functions, which
trivially satisfy `ContDiffOn ℝ 1` (`ContDiffOn.of_le`), so no information is lost.

### D2 — Hypothesis shape: `ContDiffOn ℝ 1 g U`, `IsOpen U`, `HasCompactSupport g`, `tsupport g ⊆ U`

This is the shape Dbar's own (designed, not yet built) `PlanarPoU.lean`/`exists_smooth_partition_
of_finite_cover` produces (`ContDiffOn ℝ ∞ (ψ i) V` on an open `V`, with a support-in-`W i`
clause) and it is what residue-theorem's PoU pieces will literally hold — so our atoms accept
*this* shape directly rather than forcing callers to first upgrade to a global `ContDiff ℝ 1 g`.
Internally we upgrade once, via the `Compat.lean` gluing lemma (§1.5), because the rectangle
argument (Atom 1) needs `g` defined/differentiable on a rectangle that need not stay inside `U`.

### D3 — `f : ℂ → ℂ` bare functions throughout, matching ResidueCalculus's junk convention

No subtypes, no `MeroGermOn`. `MeromorphicAt f p`, `DifferentiableOn ℂ f (U \ {p})` — exactly the
hypotheses `resAt`/`principalPartAt`/`circleIntegral_eq_two_pi_I_mul_resAt` already use. Junk
off-domain values of `f` never enter any computation because every place `f` is evaluated where
it might be "bad" is multiplied by a factor (`g` or `wirtingerDbar g`) that is identically `0`
there (never merely small) — this is *load-bearing*, not cosmetic: it is what lets Atom 2 be a
genuine (non-improper) Bochner integral even though `f` itself may fail to be locally integrable
at `p` for higher-order poles (§8.1 explains why the naive "just take `g` continuous" version
would NOT converge).

### D4 — Atom 2's hypothesis is "`g` locally CONSTANT near `p`", not merely "`g` continuous at `p`"

This is the central scoping decision of the whole design, so it is stated up front rather than
buried in a proof. A first-principles "smeared residue" theorem for arbitrary smooth compactly
supported `g` and a pole of order `≥ 2` is **not** `-π·g(p)·resAt(f,p)` — it also involves `g`'s
higher Wirtinger-derivatives at `p` paired against `f`'s higher Laurent coefficients (the same
shape as ResidueCalculus's `resAt_analyticAt_mul`, which sums *all* of `h`'s Taylor coefficients
against `f`'s tail, not just `h(p)`). A quick check: the crude Lipschitz bound
`|∮_{C(p,ε)}(g-g(p))f| ≤ 2πε·(Lε)·sup|f|` on the circle is `O(ε^{2-m})` for a pole of order `m`,
which fails to vanish once `m ≥ 2`. We therefore do **not** attempt the fully general statement.
Instead we require `g =ᶠ[nhds p] Function.const ℂ (g p)` (`g` is *identically* equal to the
constant `g p` on some open neighborhood of `p`, not just asymptotically close) — under this
hypothesis every "remainder" term the general case would need to control is **exactly** zero
(not merely small), and the resulting identity is exact, elementary, and holds for *any* pole
order. §11 argues this hypothesis costs nothing in practice: residue-theorem's PoU construction
always has this freedom (cutoffs are built from `ContDiffBump`s, which are ≡ 1 near their center
by construction), so the "coordination point" is a one-line requirement on how residue-theorem
builds its cover, not a mathematical restriction.

### D5 — The annulus identity is proved once, in full generality, with no reference to `resAt`

`Jacobian/PlanarStokes/AnnulusResidue.lean`'s first theorem
(`circleIntegral_sub_circleIntegral_eq_two_mul_I_mul_integral_wirtingerDbar`, §7) is stated for
an arbitrary `ContDiffOn ℝ 1` function on a closed annulus — it says nothing about poles,
residues, or meromorphy. Atom 2 is then a two-paragraph corollary (§8) instantiating it at
`u := g·f`. This factoring keeps the genuinely new 2-D-integration content (§7) separated from the
residue-specific bookkeeping (§8, which is otherwise just algebra reusing ResidueCalculus).

### D6 — No general "region with holes" or manifold-with-corners abstraction

We prove exactly the ONE annulus identity needed (disk minus concentric disk), via one
substitution, reusing one mathlib lemma (§1.1) once. No attempt at a reusable "Stokes on
`rectangle \ compact convex hole`" theorem, no `IsManifoldWithCorners`, nothing in
`Analysis/BoxIntegral`. This matches the blueprint's explicit scope discipline ("NO manifold
Stokes, NO general form theory").

---

## 5. Exports — exact signatures

Throughout: `open Complex`, `Real.pi` written `π`, `starRingEnd ℂ` written `conj`. Standing
implicit variables `g f u : ℂ → ℂ`, `z w c p : ℂ`, `U : Set ℂ`, `r R ε : ℝ`.

### 5.1 `Compat.lean` (namespace `RS`)

```lean
/-- Leibniz rule for the Wirtinger `∂̄` (requested for upstreaming to `Jacobian/Dbar/Wirtinger.lean`
— see `docs/requests/dbar-solvability.md`; proved locally here meanwhile). -/
theorem wirtingerDbar_mul (hg : DifferentiableAt ℝ g z) (hf : DifferentiableAt ℝ f z) :
    wirtingerDbar (fun w => g w * f w) z = wirtingerDbar g z * f z + g z * wirtingerDbar f z

/-- The `f`-holomorphic specialization used everywhere below: the ∂̄ of a product with a
holomorphic factor sees only the other factor's ∂̄. -/
theorem wirtingerDbar_mul_of_differentiableAt (hg : DifferentiableAt ℝ g z)
    (hf : DifferentiableAt ℂ f z) :
    wirtingerDbar (fun w => g w * f w) z = wirtingerDbar g z * f z

/-- `g` vanishes identically on a whole neighborhood of any point outside `tsupport g`, so a
product with an arbitrary (possibly non-differentiable/junk) `f` is still ∂̄-trivial there. -/
theorem wirtingerDbar_mul_eq_zero_of_notMem_tsupport (hz : z ∉ tsupport g) :
    wirtingerDbar (fun w => g w * f w) z = 0

/-- Upgrade a `ContDiffOn` function with compact support strictly inside an open set to a
globally `ContDiff` function (two-piece gluing: locally `g` on `U`, locally `0` on `(tsupport g)ᶜ`,
these two opens cover `ℂ`). -/
theorem ContDiffOn.contDiff_of_hasCompactSupport {n : ℕ∞} (hU : IsOpen U)
    (hg : ContDiffOn ℝ n g U) (hcs : HasCompactSupport g) (hsub : tsupport g ⊆ U) :
    ContDiff ℝ n g

/-- The `ℂ`-rectangle ↔ iterated-real-integral bridge: a function vanishing off an open
rectangle has the same global `ℂ`-integral as its iterated real double integral over (any closed
rectangle containing) that open rectangle. -/
theorem integral_eq_intervalIntegral_of_tsupport_subset_reProdIm {F : ℂ → ℂ} {z w : ℂ}
    (hFc : Continuous F)
    (hsub : tsupport F ⊆ Complex.reProdIm (Set.Ioo z.re w.re) (Set.Ioo z.im w.im)) :
    ∫ ζ : ℂ, F ζ = ∫ x : ℝ in z.re..w.re, ∫ y : ℝ in z.im..w.im, F (x + y * I)
```

### 5.2 `CompactSupport.lean` (namespace `RS`) — Atom 1

```lean
/-- **Atom 1** (compact-support planar Stokes for `∂̄`): the ∂̄ of a compactly-supported `C¹`
function integrates to zero over the whole plane. -/
theorem integral_wirtingerDbar_eq_zero (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U)
    (hcs : HasCompactSupport g) (hsub : tsupport g ⊆ U) :
    ∫ w : ℂ, wirtingerDbar g w = 0

/-- **Atom 1b** (immediate corollary, the "no pole in this chart" case residue-theorem needs for
every PoU piece that does not touch a pole): if `f` is holomorphic throughout `U`, the ∂̄-weighted
integral against `f` also vanishes. -/
theorem integral_wirtingerDbar_mul_eq_zero_of_differentiableOn (hU : IsOpen U)
    (hg : ContDiffOn ℝ 1 g U) (hcs : HasCompactSupport g) (hsub : tsupport g ⊆ U)
    (hf : DifferentiableOn ℂ f U) :
    ∫ w : ℂ, wirtingerDbar g w * f w = 0
```

### 5.3 `AnnulusResidue.lean` (namespace `RS`)

```lean
/-- **Atom 1′** (annulus Stokes, general — no meromorphy, no residue): area-to-boundary identity
for the ∂̄ of an arbitrary `C¹` function on a closed annulus. The genuinely new 2-D computation of
this unit; proved by the exponential substitution `w = c + exp ζ` (§7). -/
theorem circleIntegral_sub_circleIntegral_eq_two_mul_I_mul_integral_wirtingerDbar
    {c : ℂ} {r R : ℝ} (h0 : 0 < r) (hle : r ≤ R)
    (hu : ContDiffOn ℝ 1 u (Metric.closedBall c R \ Metric.ball c r)) :
    (∮ w in C(c, R), u w) - (∮ w in C(c, r), u w) =
      2 * I * ∫ w in (Metric.closedBall c R \ Metric.ball c r), wirtingerDbar u w

/-- **Atom 2** (the smeared residue theorem — the "one honest integration atom" routing decision
#2 budgets for): `g` compactly supported in `U`, locally CONSTANT near the puncture `p` (§D4),
`f` holomorphic on `U \ {p}` and meromorphic at `p`. -/
theorem integral_wirtingerDbar_mul_eq_neg_pi_mul_resAt (hU : IsOpen U) (hpU : p ∈ U)
    (hg : ContDiffOn ℝ 1 g U) (hcs : HasCompactSupport g) (hsub : tsupport g ⊆ U)
    (hconst : g =ᶠ[nhds p] Function.const ℂ (g p))
    (hf : DifferentiableOn ℂ f (U \ {p})) (hfp : MeromorphicAt f p) :
    ∫ w : ℂ, wirtingerDbar g w * f w = -π * g p * resAt f p

/-- Model-case corollary (the verification the task asked for, `f = 1/(z-p)`, kept as a named
sanity lemma / regression test — proved a *second*, independent way in §8.4 by translating
`RS.cauchyPompeiu`). -/
theorem integral_wirtingerDbar_mul_inv_sub_eq (hU : IsOpen U) (hpU : p ∈ U)
    (hg : ContDiffOn ℝ 1 g U) (hcs : HasCompactSupport g) (hsub : tsupport g ⊆ U)
    (hconst : g =ᶠ[nhds p] Function.const ℂ (g p)) :
    ∫ w : ℂ, wirtingerDbar g w * (w - p)⁻¹ = -π * g p
```

**Item 3 (change of variables) — nothing new is designed here.** See §10: after reading
`ResidueCalculus/ChangeOfVariables.lean`'s `resAt_comp_mul_deriv` in full, every planar integral
in this unit lives inside a *single fixed chart* (one copy of `ℂ`), because residue-theorem's PoU
pieces are each supported in one chart of `X` by construction. The only place a *chart change*
could enter is comparing the residue computed in two overlapping charts, and that comparison is
exactly `resAt_comp_mul_deriv` (already built, proved algebraically, no integration). We do not
export any `changeOfVariables`-named lemma from this unit.

---

## 6. Proof plan: Atom 1 (`integral_wirtingerDbar_eq_zero`)

1. **Upgrade to global `ContDiff`.** `hg' : ContDiff ℝ 1 g :=
   ContDiffOn.contDiff_of_hasCompactSupport hU hg hcs hsub` (Compat, §1.5/§4 gluing argument:
   `ContDiffAt ℝ 1 g z` for `z ∈ U` from `hg.contDiffAt (hU.mem_nhds _)`; for `z ∉ U` we have
   `z ∉ tsupport g` (contrapositive of `hsub`), so `g =ᶠ[nhds z] 0` (`notMem_tsupport_iff_
   eventuallyEq`-style), giving `ContDiffAt` via `contDiffAt_congr`/the constant function).
2. **Pick a rectangle strictly containing the support.** `tsupport g` compact ⇒ bounded; choose
   `M` with `tsupport g ⊆ ball 0 M`; set `z := (-M-1) + (-M-1)*I`, `w := (M+1)+(M+1)*I`. Then
   `tsupport g ⊆ Complex.reProdIm (Ioo z.re w.re) (Ioo z.im w.im)` (the open rectangle strictly
   contains the ball).
3. **Apply the rectangle lemma.** `integral_boundary_rect_of_differentiableOn_real g z w
   hg'.differentiableOn.restrictScalars (integrability: continuous on compact, §1.1)` — since
   `g ≡ 0` on all four boundary segments (they lie outside `tsupport g` by step 2), the LHS
   (four boundary integrals) is `0` termwise (`intervalIntegral.integral_eq_zero_of_ae`/directly
   `g (x+z.im*I) = 0` pointwise on the segment, `intervalIntegral` of the zero function is `0`).
   So `0 = ∫x in z.re..w.re, ∫y in z.im..w.im, I•fderiv g (x+yI) 1 - fderiv g(x+yI) I`.
4. **Rewrite the integrand via §1.2**: `= ∫x,∫y, 2*I*wirtingerDbar g (x+yI)`, hence
   `∫x,∫y, wirtingerDbar g (x+yI) = 0` (divide by `2I ≠ 0`, `intervalIntegral.integral_const_mul`
   applied twice / `mul_eq_zero`).
5. **Bridge back to the global integral.** `wirtingerDbar g` is continuous
   (`continuous_wirtingerDbar hg'.of_le`, wait: needs `ContDiff ℝ ∞`? — Dbar's
   `continuous_wirtingerDbar` hypothesis is `ContDiff ℝ ∞ f`; since we only have `ContDiff ℝ 1 g`,
   use instead `contDiffOn_wirtingerDbar`/direct continuity from `ContDiff ℝ 1`:
   `hg'.continuous_fderiv (by norm_num)` gives `Continuous (fderiv ℝ g)`, then `wirtingerDbar g`
   is continuous as `(fun z => (fderiv ℝ g z 1 + I*fderiv ℝ g z I)/2)`, a composition of
   continuous maps — a two-line Compat fact if Dbar's own lemma is `∞`-only; **flagged as a
   risk in §12, R1, with the trivial fallback of proving the `C¹` version locally**) and has
   compact support ⊆ `tsupport g` (`hasCompactSupport_wirtingerDbar hcs`, Dbar, works for any
   `HasCompactSupport g`, regularity-free). By construction `tsupport g ⊆ ball 0 M ⊆` the open
   rectangle, so `Compat.integral_eq_intervalIntegral_of_tsupport_subset_reProdIm` gives
   `∫ ζ:ℂ, wirtingerDbar g ζ = ∫x in z.re..w.re, ∫y in z.im..w.im, wirtingerDbar g (x+yI)`, which
   is `0` by step 4. ∎

`Atom 1b` is immediate: `wirtingerDbar (fun w => g w * f w) w = wirtingerDbar g w * f w`
pointwise on `U` (`wirtingerDbar_mul_of_differentiableAt`, `f` holomorphic ⇒ `ℂ`-differentiable
⇒ `ℝ`-differentiable there) and `= 0` off `tsupport g` regardless of `f`
(`wirtingerDbar_mul_eq_zero_of_notMem_tsupport`); so `fun w => g w * f w` is (after the same
`ContDiffOn.contDiff_of_hasCompactSupport`-style gluing, now needing `f` only on `U`) globally
`ContDiff ℝ 1` with compact support `⊆ tsupport g ⊆ U`; apply Atom 1 to it and rewrite via the
pointwise identity.

---

## 7. Proof plan: the annulus identity (the 40+-line heart, exp-substitution)

Goal: for `u` `ContDiffOn ℝ 1` on the closed annulus `A := closedBall c R \ ball c r`
(`0 < r ≤ R`):
```
(∮ w in C(c,R), u w) - (∮ w in C(c,r), u w) = 2*I * ∫ w in A, wirtingerDbar u w.
```

**Step 1 (the substitution).** `τ(ζ) := c + Complex.exp ζ`. On the rectangle
`Rec := [[log r, log R]] ×ℂ [[0, 2π]]` (`a := Real.log r`, `b := Real.log R`; `Real.exp_log`
gives `Real.exp a = r`, `Real.exp b = R`; `a ≤ b` from `Real.log_le_log` and `r ≤ R`), `τ` maps
`Rec` *onto* `A`: for `ζ = x+yI ∈ Rec`, `‖τ(ζ) - c‖ = ‖exp ζ‖ = Real.exp x ∈ [r,R]`
(`Complex.norm_exp`/`abs_exp_eq_iff` — norm of `exp` is `exp` of the real part, standard). This
mirrors *exactly* the substitution mathlib's own
`circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable` proof performs
(`CauchyIntegral.lean:316–346`, read in full) — we reuse its bookkeeping pattern (`h_maps`,
`hdg := differentiable_exp.const_add c`) verbatim, just for a non-holomorphic `u`.

**Step 2 (the transported function and its ∂̄).** `F(ζ) := u(τ(ζ)) * Complex.exp ζ`. This is the
key new object (mathlib's own proof only needs `u∘τ`, since it only tracks Cauchy–Goursat
vanishing; we additionally carry the extra `exp ζ` factor to make the *area element* come out
flat — this is the one genuinely new idea in the derivation). Compute, using **only already-built
API**: for `hu : DifferentiableAt ℝ u (τ ζ)`,
- `Complex.differentiableAt_exp : DifferentiableAt ℂ exp ζ`, hence `.restrictScalars ℝ` gives
  `DifferentiableAt ℝ exp ζ`; `(differentiableAt_const c).add (that)` gives
  `DifferentiableAt ℝ τ ζ`; `hu.comp ζ (that)` gives `DifferentiableAt ℝ (u∘τ) ζ`;
- `wirtingerDbar_mul (that) (DifferentiableAt ℝ exp ζ, from restrictScalars)`:
  `wirtingerDbar F ζ = wirtingerDbar (u∘τ) ζ * exp ζ + (u∘τ)(ζ) * wirtingerDbar exp ζ`;
- `wirtingerDbar exp ζ = 0` (`wirtingerDbar_eq_zero_of_differentiableAt exp ζ
  Complex.differentiableAt_exp` — Dbar's CR bridge, applied to the *holomorphic* `exp`);
- `wirtingerDbar (u∘τ) ζ = conj(deriv τ ζ) * wirtingerDbar u (τ ζ)`
  (`wirtingerDbar_comp_differentiableAt`, Dbar's `(0,1)` chain rule, `τ` holomorphic);
  `deriv τ ζ = deriv exp ζ = exp ζ` (`deriv_const_add`, `Complex.deriv_exp`).
- **Combining**: `wirtingerDbar F ζ = conj(exp ζ) * wirtingerDbar u (τ ζ) * exp ζ + 0 =
  exp ζ * conj(exp ζ) * wirtingerDbar u (τ ζ) = ‖exp ζ‖² * wirtingerDbar u (τ ζ)`
  (`Complex.mul_conj`/`normSq_eq_conj_mul_self`, `‖exp ζ‖ = Real.exp x`). **This exact identity
  (with `u` replaced by a generic differentiable function) is compiled in the spike, §9,
  `RS.wirtingerDbar_expSubst` — de-risked.**

**Step 3 (apply the rectangle lemma to `F` on `Rec`).** `F` is `ContDiffOn ℝ 1` on `Rec`
(composition/product of `ContDiffOn`s: `u` on `A ⊇ τ(Rec)`, `τ` entire, standard `ContDiffOn.comp`
+ `ContDiffOn.mul`; the integrability side-condition discharges via continuity on the compact
`Rec`, §1.1). `integral_boundary_rect_of_differentiableOn_real F ⟨a,0⟩ ⟨b,2π⟩` gives
```
(∫x in a..b, F(x+0I)) - (∫x in a..b, F(x+2πI)) + I(∫y in 0..2π, F(b+yI)) - I(∫y in 0..2π, F(a+yI))
  = ∫x in a..b, ∫y in 0..2π, 2*I*wirtingerDbar F (x+yI)                          -- (via §1.2)
```

**Step 4 (the `y`-boundary cancels by periodicity).** `F(x+0I) = u(c+exp(x))*exp(x)` and
`F(x+2πI) = u(c+exp(x+2πI))*exp(x+2πI) = u(c+exp(x))*exp(x)` (`Complex.exp_periodic` gives
`exp(x+2πI) = exp(x)`, exactly), so the first two terms are literally equal and cancel:
`(∫x, F(x+0I)) - (∫x, F(x+2πI)) = 0`.

**Step 5 (the `x`-boundary is the two circle integrals).** `I*(∫y in 0..2π, F(b+yI)) =
I*∫y, u(c+exp(b+yI))*exp(b+yI) = I*∫y, u(c+R*exp(yI))*R*exp(yI)` (`exp(b) = R`,
`exp(b+yI)=exp(b)*exp(yI)`) `= ∫y, I*R*exp(yI)*u(circleMap c R y) = ∮_{C(c,R)} u`
(unfold `circleIntegral`/`circleMap`/`hasDerivAt_circleMap` — `deriv (circleMap c R) y =
I*R*exp(yI)` exactly matches the integrand). Likewise `I*∫y, F(a+yI) = ∮_{C(c,r)} u`. So Step 3's
LHS is exactly `(∮_{C(c,R)}u) - (∮_{C(c,r)}u)`.

**Step 6 (the RHS is the flat area integral via one 1-D substitution).** By Step 2,
`2*I*wirtingerDbar F(x+yI) = 2*I*‖exp(x+yI)‖²*wirtingerDbar u(c+exp(x+yI)) =
2*I*(exp x)²*wirtingerDbar u(w)` where `w := c + exp(x)*exp(yI)` is exactly the polar
parametrization of `A` with `ρ := exp(x)`, `θ := y`. Substitute `x ↦ ρ := Real.exp x` in the
OUTER (1-D) interval integral only (`intervalIntegral` change-of-variables for the diffeomorphism
`x ↦ exp x`, standard `intervalIntegral.integral_comp_smul_deriv`-style lemma, or directly via
`Real.exp`'s `HasDerivAt` + FTC-style substitution: `dρ = exp(x) dx`, so `∫x in a..b, φ(exp x) *
exp(x) dx = ∫ρ in r..R, φ(ρ) dρ` for continuous `φ`): with
`φ(ρ) := ∫y in 0..2π, wirtingerDbar u (c+ρ*exp(yI)) dy`, we get
`∫x in a..b, (exp x)*φ(exp x) dx = ∫ρ in r..R, φ(ρ) dρ`, i.e.
```
∫x in a..b, ∫y in 0..2π, 2*I*(exp x)²*wirtingerDbar u(w) dy dx
  = 2*I * ∫ρ in r..R, ∫y in 0..2π, ρ*wirtingerDbar u(c+ρ*exp(yI)) dy dρ.
```
The RHS is *exactly* `2*I*∫_{annulus} wirtingerDbar u dA` in polar coordinates
(`dA = ρ dρ dθ`, `Complex.integral_comp_polarCoord_symm`-style identification of the polar
integral with the set integral over `A`, matching Dbar's own §5 Step 3 polar rewrite verbatim —
same lemma, `Complex.polarCoord`/`Complex.integral_comp_polarCoord_symm`, restricted to the
annular target `Ioc r R ×ˢ Ioo (-π) π` translated to `[0,2π]` by periodicity of the integrand in
`θ`, `intervalIntegral.integral_comp_add_right`/`sub_left`-type shift, harmless).

**Step 7 (assemble).** Steps 4–6 combine Step 3's identity into
`(∮_{C(c,R)}u) - (∮_{C(c,r)}u) = 2*I*∫_{A} wirtingerDbar u`. ∎

*(Word count/line estimate for the Lean proof: steps 1–2 ~15 lines (mostly reused Dbar API calls,
compiled in the spike), step 3 ~5 lines, steps 4–5 ~10 lines of `simp`/`ring`/periodicity, step 6
is the genuinely fiddly one, ~15–20 lines threading the 1-D substitution and the polar
identification — comparable in shape, and reusing the same lemmas, as Dbar's own §5 Steps 3–8,
so the "40+ line" estimate is realistic and the risk is contained: every atom it needs already
exists and is already used successfully once, by Dbar, for a structurally identical polar
computation.)*

---

## 8. Proof plan: Atom 2 (the smeared residue theorem)

### 8.1 Why the naive route fails and the local-constancy hypothesis fixes it (recap of §D4)

If `g` is merely continuous at `p` (not locally constant), the "remainder"
`∮_{C(p,ε)}(g - g(p))f` need not vanish as `ε → 0` once `f` has a pole of order `≥ 2`: writing
`g(p+εe^{iθ}) - g(p) = ε(a\cosθ+b\sinθ) + O(ε²)` and pairing against `f`'s `(w-p)^{-m}` term
(`m ≥ 2`) picks out a *resonant* Fourier mode at `m = 2` that does **not** decay — the correct
general formula needs `g`'s higher Wirtinger-derivatives, which is out of scope (§D4). We
therefore require the STRONG hypothesis `hconst : g =ᶠ[nhds p] Function.const ℂ (g p)`.

### 8.2 Step 1 — for any `ε` small enough, the excised-annulus integral is INDEPENDENT of `ε`

From `hconst`, get `δ > 0` with `g ≡ g p` on `ball p δ` (`Metric.eventually_nhds_iff_ball`).
`wirtingerDbar g ≡ 0` on `ball p δ` (`wirtingerDbar_congr_nhds` + `wirtingerDbar_const`, both
Dbar). Hence `wirtingerDbar g · f ≡ 0` on `ball p δ` too (regardless of `f`'s behavior at/near
`p`, including the pole — `0 * (anything) = 0` pointwise, junk-safe: this is where `D3`'s "no
merely-small, only exactly-zero" design point is load-bearing). So for any `0 < ε < ε' < δ`, the
two regions `closedBall p R \ ball p ε` and `closedBall p R \ ball p ε'` differ only inside
`ball p δ`, where the integrand is `0`; hence (support-restriction,
`setIntegral_eq_integral_of_forall_compl_eq_zero`-style / direct `setIntegral_congr_set`)
```
∫ w in (closedBall p R \ ball p ε), wirtingerDbar g w * f w
  = ∫ w in (closedBall p R \ ball p ε'), wirtingerDbar g w * f w        -- same for all ε,ε' < δ
  = ∫ w : ℂ, wirtingerDbar g w * f w                                    -- letting ε → 0 costs nothing
```
(the last equality: `wirtingerDbar g * f` also vanishes outside `tsupport g`
— `wirtingerDbar_mul_eq_zero_of_notMem_tsupport` — so the global integral already only sees
`tsupport g \ ball p δ ⊆ closedBall p R \ ball p ε` once `R` is chosen `⊇ tsupport g`). **No limit
is actually needed anywhere in this unit** — the "ε → 0" language in the task prompt describes the
*mathematical* content; formally it collapses to picking one convenient `ε`.

### 8.3 Step 2 — evaluate at one convenient `ε`, via the annulus identity + the circle bridge

Pick `ε ∈ (0,δ)` small enough that `ResidueCalculus.MeromorphicAt.eventually_circleIntegral_eq_
two_pi_I_mul_resAt hfp` applies at radius `ε` (an `∀ᶠ R in 𝓝[>]0` statement — take `ε` in that
eventual set) and `R` with `tsupport g ⊆ ball p R`. Apply
`circleIntegral_sub_circleIntegral_eq_two_mul_I_mul_integral_wirtingerDbar` (§7) to
`u := fun w => g w * f w` on `closedBall p R \ ball p ε`:
- `u` is `ContDiffOn ℝ 1` there: on `tsupport(g)ᶜ` (open) it is `≡ 0` (locally, so trivially
  `ContDiffOn`, regardless of `f`); on `U \ {p}` (⊇ the rest of the annulus, since `tsupport g ⊆
  U`) it is a product of `ContDiffOn ℝ 1 g` (given) and `DifferentiableOn ℂ f` (given, hence
  `ℝ`-differentiable there) — `ContDiffOn.mul`. These two opens cover the annulus (same gluing
  argument as `Compat.ContDiffOn.contDiff_of_hasCompactSupport`, §1.5, relativized to the
  annulus instead of all of `ℂ`).
- Outer circle: `∮_{C(p,R)} g·f = 0` (`g ≡ 0` on `sphere p R`, `R` chosen `> ` any point of
  `tsupport g`'s distance to `p`, via `circleIntegral.integral_congr`/direct `EqOn`).
- So: `2*I*∫_{annulus} wirtingerDbar(g·f) = -∮_{C(p,ε)} g·f`.
- On the annulus (`w ≠ p`), `wirtingerDbar(g·f)(w) = wirtingerDbar(g)(w)*f(w)`
  (`wirtingerDbar_mul_of_differentiableAt`, `f` `ℂ`-differentiable at every `w ∈ U\{p}`).
- On `sphere p ε` (`ε < δ`), `g ≡ g p` exactly, so `∮_{C(p,ε)} g·f = g p * ∮_{C(p,ε)} f`
  (`circleIntegral.integral_congr` + `circleIntegral.integral_const_mul`) `= g p * 2πi * resAt f p`
  (`circleIntegral_eq_two_pi_I_mul_resAt`, ResidueCalculus, applicable since `ε` was chosen in
  its eventual-truth set and `f` is `DifferentiableAt ℂ` on `ball p R \ {p} ⊇ closedBall p ε
  \ {p}`, from `hf`).

### 8.4 Step 3 — assemble and divide

`2*I*∫_{closedBall p R \ ball p ε} wirtingerDbar(g)·f = -g p * 2πi * resAt f p`; combine with
§8.2's Step 1 (LHS `= ∫ w:ℂ, wirtingerDbar g w * f w`, since `ε < δ`, `R ⊇ tsupport g`); divide by
`2I`: `∫ w:ℂ, wirtingerDbar g w * f w = -π * g p * resAt f p`. ∎

**Model-case cross-check (`f = (·-p)⁻¹`, the task's requested verification), a *second*,
independent derivation not going through §7 at all:** Dbar's `cauchyPompeiu (hg : ContDiff ℝ 1 h)
(hcs : HasCompactSupport h) (z) : ∫ w:ℂ, cauchyKernel w * wirtingerDbar h (z-w) = h z`, with
`cauchyKernel w = (π*w)⁻¹`. Take `h := g` (upgraded to global `ContDiff` via Compat), `z := p`:
`∫w, (πw)⁻¹ * wirtingerDbar g (p-w) = g p`. Substitute `w ↦ p - w` (`w' := p - w`, a
measure-preserving involution of `ℂ`, `MeasurePreserving.integral_comp`/direct
`Measure.map_sub_left`-type invariance of Lebesgue measure under reflection+translation):
`∫w', (π(p-w'))⁻¹ * wirtingerDbar g (w') = g p`, i.e. `∫w', wirtingerDbar g (w') * (-1)/(π(w'-p))
= g p`, i.e. **`∫ w:ℂ, wirtingerDbar g w * (w-p)⁻¹ = -π * g p`** — matching Atom 2 at
`f = (·-p)⁻¹` (`resAt ((·-p)⁻¹) p = 1`, `ResidueCalculus.resAt_sub_inv`) *exactly*, with **no
local-constancy hypothesis on `g` needed at all** in this special case (consistent: a simple pole
is exactly the borderline order where the crude Lipschitz estimate of §8.1 already works, so the
general-`g` and locally-constant-`g` theorems agree there). This cross-check is recorded as the
named lemma `integral_wirtingerDbar_mul_inv_sub_eq` in §5.3, and is intentionally proved via this
*independent* route (not as a corollary of Atom 2) precisely so it is a genuine regression check
on the `-π` constant.

---

## 9. Spike (gated, compiled)

Ran (after `while [ "$(pgrep -cx lean)" -ge 3 ]; do sleep 30; done`, machine had 1 `lean` process,
under the limit of 3): `lake env lean scratch_stokes.lean`, ~45 lines, mathlib-only (no project
edits outside the scratch file). Content: (1) `wirtingerDbar_mul` (the Leibniz rule, exactly as
specified in §5.1) proved from `fderiv_fun_mul` + Dbar's own `wirtingerDbar_add`-style
`ContinuousLinearMap.add_apply`/`ring` pattern; (2) `wirtingerDbar_expSubst`, the §7 Step 2
algebraic core (`wirtingerDbar (fun w => u (c + exp w) * exp w) ζ = exp ζ * conj(exp ζ) *
wirtingerDbar u (c + exp ζ)`), proved by chaining `wirtingerDbar_mul`,
`wirtingerDbar_comp_differentiableAt` (Dbar's `(0,1)` chain rule), and
`wirtingerDbar_eq_zero_of_differentiableAt` (Dbar's CR bridge) applied to `Complex.exp`.

**Result: compiles clean (zero errors, zero warnings)** after two naming fixes discovered by the
spike (recorded so builders don't re-hit them):
- `fderiv_mul` (no `fun`) is for the pointwise-notation product `c * d`; the `fun w => g w * f w`
  goal needs **`fderiv_fun_mul`** instead.
- `DifferentiableAt.restrictScalars` takes the target field `𝕜` as an **explicit** first
  argument (`hexp.restrictScalars ℝ`, not `hexp.restrictScalars`) — omitting it leaves a
  metavariable and `NontriviallyNormedField 𝕜✝` instance search fails.
- `Complex.deriv_exp : deriv exp = exp` is a bare function equality; use
  `congrFun Complex.deriv_exp ζ` to get the pointwise form, not direct `rw`.

This de-risks exactly the two novel algebraic ingredients of §7 (the Leibniz rule, entirely new;
the exp-substitution's chain-rule combination, the crux of the annulus proof) — the remaining
work in §7 (periodicity cancellation, the 1-D `exp`-substitution, the polar identification) reuses
lemmas already successfully deployed once each, by mathlib's own annulus-deformation proof and by
Dbar's own `cauchyPompeiu` polar computation respectively, so it carries materially lower risk
than the two ingredients actually spiked.

`scratch_stokes.lean` left in the repo root per the workflow (not deleted); a builder may delete
it once the real files land.

---

## 10. Item 3 in detail: why `ResidueCalculus.ChangeOfVariables` already suffices

Read `Jacobian/ResidueCalculus/ChangeOfVariables.lean` in full. Its one export,
`resAt_comp_mul_deriv {φ : ℂ → ℂ} (hφ : AnalyticAt ℂ φ w₀) (hφ' : deriv φ w₀ ≠ 0)
(hφ₀ : φ w₀ = z₀) (hf : MeromorphicAt f z₀) : resAt (fun w => f (φ w) * deriv φ w) w₀ = resAt f z₀`,
is proved *purely algebraically* (Laurent-coefficient bookkeeping, §4.5 of that design, no
integration) and is exactly "the residue of a 1-form's coefficient is chart-invariant." Every
integral in *this* unit (Atoms 1, 1b, 1′, 2) is stated and proved inside one fixed copy of `ℂ` —
there is no point in our proofs where two charts' coordinates are simultaneously in play, because
each PoU piece `ψᵢ·ω` that residue-theorem will feed us is, by construction, supported in a
single chart. Consequently **residue-theorem needs no additional "change of variables for the
area integral" atom from us**: it will (a) use `resAt_comp_mul_deriv` to know that the *residue*
computed from chart `i`'s local coefficient agrees with the residue from any other chart at the
same pole (needed once, to make "`Res_p(ω)`" well-defined before summing), and (b) use our Atoms
1/1b/2, one chart at a time, to get the Stokes cancellation. We flag this explicitly, as the task
requests, rather than silently omitting a file: **nothing is designed or built here for item 3.**

---

## 11. Downstream map

**residue-theorem** (primary consumer). Expected use, reconstructed from its blueprint entry
("cover `X`, write the form as sum of locally-supported pieces, apply planar Stokes to each;
boundary terms cancel; what survives is `∑Res`") and cross-checked against this unit's atoms:
- Build a finite open cover of `X` by chart disks, one per pole plus enough to cover the rest,
  and a subordinate smooth PoU `(ψᵢ)` (via the surface-level `SmoothPartitionOfUnity`
  machinery, `docs/mathlib-inventory.md` §16 / Dbar's `RS.exists_smoothPartitionOfUnity`,
  ALREADY compiled per dbar-solvability's design §1.5) with the **extra, one-line-to-arrange
  property** that at any pole `p` covered by chart `i`, `ψᵢ ≡ 1` on some sub-neighborhood of `p`
  (this is the `hconst` hypothesis of Atom 2 — free to arrange: build `ψᵢ` from a
  `ContDiffBump` centered at `p`, which is `≡ 1` on its `rIn`-ball by construction,
  `ContDiffBump.one_of_mem_closedBall`, exactly the same device Dbar's own `SolveDisk.lean`
  already uses for cutoffs).
- For each `i`, in chart `i`'s coordinate `ℂ`, with `fᵢ` the local coefficient of `ω`: if chart
  `i` contains no pole, `∫∫ wirtingerDbar(ψᵢ)·fᵢ = 0` (**Atom 1b**); if it contains pole `pᵢ`,
  `∫∫ wirtingerDbar(ψᵢ)·fᵢ = -π·ψᵢ(pᵢ)·resAt(fᵢ,pᵢ) = -π·resAt(fᵢ,pᵢ)` (**Atom 2**, `ψᵢ(pᵢ)=1`).
- Sum over `i`: since `∑ᵢ ψᵢ ≡ 1` (PoU) and each summand is chart-local, the LHS sum telescopes
  to (a chart-invariant statement of) `∫∫ wirtingerDbar(∑ᵢψᵢ)·ω`-type reasoning `= 0` because
  `∑ᵢψᵢ = 1` is *constant* — but the actually-summed *identities* above already give the RHS
  directly as `-π·∑_p resAt(f,p)`, matching `0` from the LHS, i.e. `∑_p Res_p(ω) = 0`. (This
  telescoping/global-2-form bookkeeping — matching each chart's `wirtingerDbar(ψᵢ)` against
  `d(1)=0` globally — is residue-theorem's own work; we only guarantee the per-chart identities
  it plugs in.)
- residue-theorem does **not** need any atom beyond 1b and 2 from us, and needs
  `resAt_comp_mul_deriv` from ResidueCalculus (not from us, §10) for the well-definedness of
  `Res_p(ω)` prior to summing.

**abel-weak-solutions** (builds on us per the DAG, "chain decompositions and piecewise-planar
solutions... staying in planar pieces glued by monodromy"). Its blueprint entry does not mention
residues or poles; the likeliest need is **Atom 1** alone (or Atom 1b), used when verifying that
two local primitives built by dbar-solvability's chart-disk solvability agree up to the expected
correction across an overlap — a compact-support Green's-identity check, not a residue
computation. We export Atom 1/1b at the top level (no residue-specific imports needed to use
them, `CompactSupport.lean` only imports `Compat.lean` + Dbar's `Wirtinger.lean`) so
abel-weak-solutions can depend on exactly that file without pulling in ResidueCalculus. If its
designer finds a genuine need for the annulus/residue atoms, that is a scope surprise to flag
back to the orchestrator, not something to silently assume here.

---

## 12. Risks and fallbacks

- **R1 (low): `continuous_wirtingerDbar`/`hasCompactSupport_wirtingerDbar` regularity mismatch.**
  Dbar's exported `continuous_wirtingerDbar` needs `ContDiff ℝ ∞ f`; our atoms use `ContDiff ℝ 1`.
  `hasCompactSupport_wirtingerDbar` is regularity-free (works off `HasCompactSupport` alone) —
  no issue there. For continuity, fallback: prove a local `C¹`-only continuity fact directly
  (`hg'.continuous_fderiv (le_refl 1)` composed with `clm_apply`/`add`/`div_const`, mirroring
  Dbar's own `contDiffOn_wirtingerDbar` proof shape one level down) as a two-line `Compat` lemma;
  trivial, already sketched in §6 Step 5.
- **R2 (low): the 1-D `x ↦ Real.exp x` substitution inside a double interval integral (§7 Step
  6).** Needs threading a change-of-variables through an *outer* interval integral whose
  integrand is itself an inner interval integral (`φ(ρ)` in §7). If the direct
  `intervalIntegral.integral_comp_smul_deriv`-family lemma fights the nested shape, fallback:
  swap to `MeasureTheory.integral_comp_smul_deriv`/`MeasureTheory.integral_image_eq_integral_
  abs_deriv_smul` on the outer variable BEFORE splitting into the iterated form (i.e. do the
  substitution on the rectangle-side `Icc`-integral, §1.3's raw form, before invoking `setIntegral_
  prod`) — strictly more mechanical, same content, longer. Not a mathematical risk, a tactic-
  routing one.
- **R3 (low): the polar identification in §7 Step 6 (annulus vs `Ioc r R ×ˢ Ioo(-π) π` vs
  `[0,2π]`).** Dbar's own `cauchyPompeiu` proof (§5 of its design) already threads
  `Complex.polarCoord.target = Ioi 0 ×ˢ Ioo(-π,π)` against a `[0,2π]`-style circle parametrization
  and resolves the `2π`-vs-`(-π,π)` mismatch via periodicity shifts
  (`intervalIntegral.integral_comp_add_right`-style); we reuse that exact resolution, not a new
  one. Recorded as low-risk because it is precedented, not because it is free.
- **R4 (design risk, mitigated, not a Lean risk): the `hconst` hypothesis in Atom 2 (§D4).** If
  residue-theorem's actual PoU construction turns out NOT to give `ψᵢ ≡ 1` near each pole it
  owns (e.g. if its cover is built by some other means that only guarantees continuity), Atom 2
  as stated will not directly apply, and the fully general (higher-Taylor-coefficient) smeared
  residue formula would need to be designed — a materially larger undertaking (see §D4's Fourier-
  resonance analysis) that this doc explicitly declines to attempt speculatively. **Mitigation**:
  flagged prominently in §11 as a one-line requirement on residue-theorem's cover construction,
  which is achievable with a `ContDiffBump` exactly as PoU constructions already work; if
  residue-theorem's designer finds this unworkable, it is a scope issue to raise with the
  orchestrator, not something to route around silently here.
- **R5 (low): `ContDiffOn.contDiff_of_hasCompactSupport` (Compat gluing lemma, §1.5/§4) is used
  three times (Atom 1's global upgrade, Atom 1b's product upgrade, and — relativized to an
  annulus rather than all of `ℂ` — inside Atom 2's step 2 gluing).** Consider stating a single
  more general "glue two `ContDiffOn`s that agree on nothing but whose supports are disjoint
  opens covering the ambient set" lemma once, parametrized by the ambient set, rather than three
  bespoke instances; a simplification pass, not a correctness risk.

---

## 13. Summary of what is NOT built here (scope discipline, restated)

No manifold Stokes, no differential forms on `X`, no `Form1`/`Form01` consumption (residue-theorem
plugs its own chart coefficients into our bare-`ℂ→ℂ` atoms), no residue **functional** /
Serre pairing (serre-duality-tails' job, via Miranda's tail route, per routing decision #2), no
general "region with holes" Stokes beyond the one disk-minus-disk annulus identity, no change-of-
variables lemma (§10: `ResidueCalculus.ChangeOfVariables` already covers everything needed), no
winding numbers, no contour deformation beyond what mathlib's own annulus lemma already gives
(reused, not re-derived) plus the one new exponential-substitution area identity (§7).
