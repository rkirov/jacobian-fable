# Design: meromorphic-and-divisors (`Jacobian/Meromorphic/`)

Blueprint unit **meromorphic-and-divisors**. Implements **CC2** (divisors) and **CC3**
(meromorphic functions, `ℳ X`, orders, `L(D)`, `holoRepr`) — both frozen in
`docs/design/core-choices.md`. This unit carries the project's central correctness hazard:

> *A `toFun`-junk representation of `L(D)` silently makes `l ≡ 0` and Riemann–Roch **false**.*

Everything here is therefore germ-quotient based (junk-free by construction): `ℳ X` and its
relative versions are quotients by `=ᶠ[Filter.codiscreteWithin U]`, orders and divisors are
defined **on the quotient**, and every "value of a meromorphic function" statement is either a
germ statement or goes through the canonical repaired representative `holoRepr`.

References: Forster §6 (sheaf/germ viewpoint; book 40–44 = PDF 46–50), §2.8–2.10 (Liouville,
constancy; PDF 16–19), §16.1–16.5 (divisors, `O_D`; PDF 132–135), §20 opening (weak solutions
vocabulary; PDF 165); Miranda Ch. V (divisors V.1 = PDF 142, partial order V.1 p.136 = PDF 149,
**L(D)** V.3 p.145 = PDF 158, dimension bound p.151 = PDF 164).

All mathlib names below verified against the pin `548398201a64f3a5127d90d83945278cfe38cac4`
by reading source (`file:line` under `.lake/packages/mathlib/Mathlib/`) and by a compiled spike
(§8). Project files quoted (Surface, LocalMultiplicity) were read on disk as built, not from
their design docs.

---

## 1. Verified mathlib + project facts (the load-bearing list)

### 1.1 `Analysis/Meromorphic/Basic.lean`

- `MeromorphicAt f x := ∃ n : ℕ, AnalyticAt 𝕜 (fun z ↦ (z - x) ^ n • f z) x` (`:36`);
  `AnalyticAt.meromorphicAt` (`:40`); `MeromorphicAt.const` (`:68`), `.add` (`:74`),
  `.smul` (`:88`), `.mul` (`:98`), `.neg` (`:166`), `.sub` (`:177`), `.inv` (`:280`,
  **unconditional**: pointwise `f⁻¹` with `0⁻¹ = 0` is meromorphic), `.inv_iff` (`:305`),
  `.div` (`:310`), `.pow`/`.zpow` (`:315`/`:321`).
- `MeromorphicAt.congr (hf : MeromorphicAt f x) (hfg : f =ᶠ[𝓝[≠] x] g) : MeromorphicAt g x`
  (`:250`) — meromorphy is a `𝓝[≠] x`-germ notion.
- **`MeromorphicAt.comp_analyticAt (hf : MeromorphicAt f (g x)) (hg : AnalyticAt 𝕜 g x) :
  MeromorphicAt (f ∘ g) x`** (`:438`) and **`meromorphicAt_comp_iff_of_deriv_ne_zero
  [CompleteSpace 𝕜] [CharZero 𝕜] (hg : AnalyticAt 𝕜 g x) (hg' : deriv g x ≠ 0) :
  MeromorphicAt (f ∘ g) x ↔ MeromorphicAt f (g x)`** (`:~460`, spiked) — chart invariance of
  `MeromorphicAtX` is mathlib-direct, no new composition lemma needed.
- `MeromorphicOn f U := ∀ x ∈ U, MeromorphicAt f x` (`:473`);
  `MeromorphicOn.congr_codiscreteWithin` (`:504`), `meromorphicOn_congr_codiscreteWithin` (`:522`).

### 1.2 `Analysis/Meromorphic/Order.lean`

- `meromorphicOrderAt (f) (x) : WithTop ℤ` (`:47`), junk `0` when `¬ MeromorphicAt f x`.
- `meromorphicOrderAt_eq_top_iff : … = ⊤ ↔ ∀ᶠ z in 𝓝[≠] x, f z = 0` (`:64`);
  `meromorphicOrderAt_eq_int_iff (hf) : … = n ↔ ∃ g, AnalyticAt 𝕜 g x ∧ g x ≠ 0 ∧
  ∀ᶠ z in 𝓝[≠] x, f z = (z - x) ^ n • g z` (`:94`);
  `meromorphicOrderAt_ne_top_iff` (`:126`), `…_ne_top_iff_eventually_ne_zero` (`:137`).
- **`meromorphicOrderAt_congr (hf₁₂ : f₁ =ᶠ[𝓝[≠] x] f₂) : meromorphicOrderAt f₁ x =
  meromorphicOrderAt f₂ x`** (`:261`) — **no meromorphy hypothesis**; this makes `ord`
  liftable to the quotient against *arbitrary* representatives.
- Limits: `tendsto_nhds_of_meromorphicOrderAt_nonneg (hf) (ho : 0 ≤ …) :
  ∃ c, Tendsto f (𝓝[≠] x) (𝓝 c)` (`:202`, spiked);
  `tendsto_cobounded_iff_meromorphicOrderAt_neg (hf) : Tendsto f (𝓝[≠] x)
  (Bornology.cobounded E) ↔ … < 0` (`:211`);
  `tendsto_nhds_iff_meromorphicOrderAt_nonneg (hf)` (`:220`, spiked);
  `tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero (hf)` (`:231`);
  `tendsto_zero_iff_meromorphicOrderAt_pos (hf)` (`:245`).
- Arithmetic: `meromorphicOrderAt_neg : … f x = … (-f) x` (`:388`);
  `meromorphicOrderAt_smul (hf) (hg) : …(f • g) = …f + …g` (`:407`);
  `meromorphicOrderAt_mul (hf) (hg) : …(f*g) = …f + …g` (`:429`, ⊤-correct);
  `meromorphicOrderAt_prod` (`:~475`);
  **`meromorphicOrderAt_inv : …(f⁻¹) x = -(…f x)`** (`:510`, unconditional; `-⊤ = ⊤` via
  `LinearOrderedAddCommGroupWithTop`);
  `meromorphicOrderAt_add (hf₁ hf₂) : min … ≤ …(f₁+f₂)` (`:563`);
  `meromorphicOrderAt_add_of_ne` (exact min when orders differ, `:638`);
  `meromorphicOrderAt_add_of_top_left/right` (`:544/:555`).
- Composition: `MeromorphicAt.meromorphicOrderAt_comp` (`:809`), **`meromorphicOrderAt_comp_of_
  deriv_ne_zero (hg : AnalyticAt 𝕜 g x) (hg' : deriv g x ≠ 0) [CompleteSpace 𝕜] [CharZero 𝕜] :
  meromorphicOrderAt (f ∘ g) x = meromorphicOrderAt f (g x)`** (`:838`, spiked) — **no
  hypothesis on `f`**, so chart invariance of `ordAtX` is junk-robust.
- `AnalyticAt.meromorphicOrderAt_eq (hf) : meromorphicOrderAt f x =
  (analyticOrderAt f x).map (↑)` (`:279`).
- Codiscrete sets: `MeromorphicOn.analyticAt_mem_codiscreteWithin (hf) :
  {x | AnalyticAt 𝕜 f x} ∈ codiscreteWithin U` (`:755`);
  `MeromorphicOn.codiscrete_setOf_meromorphicOrderAt_eq_zero_or_top` (`:766`).

### 1.3 `Analysis/Meromorphic/IsolatedZeros.lean`

- `MeromorphicAt.frequently_zero_iff_eventuallyEq_zero (hf) :
  (∃ᶠ z in 𝓝[≠] x, f z = 0) ↔ f =ᶠ[𝓝[≠] x] 0` (`:43`).
- `MeromorphicAt.frequently_eq_iff_eventuallyEq (hf hg)` (`:90`).
- `MeromorphicOn.codiscreteWithin_setOf_ne_zero (h₁f : MeromorphicOn f U)
  (h₂f : ∀ u ∈ U, meromorphicOrderAt f u ≠ ⊤) : ∀ᶠ x in codiscreteWithin U, f x ≠ 0` (`:71`).
- `MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin (hf hg)
  (h₁x : x ∈ U) (h₂x : AccPt x (𝓟 U)) (h : f =ᶠ[codiscreteWithin U] g) : f =ᶠ[𝓝[≠] x] g`
  (`:99`) — we will NOT need this (our §2.2 bridge is meromorphy-free for open `U`), but it is
  the fallback for non-open sets.

### 1.4 `Analysis/Meromorphic/NormalForm.lean` (repair machinery)

- `MeromorphicNFAt` (`:47`), `meromorphicNFAt_iff_analyticAt_or` (`:53`),
  **`MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt (hf : MeromorphicNFAt f x) :
  0 ≤ meromorphicOrderAt f x ↔ AnalyticAt ℂ f x`** (`:114`, spiked).
- Pointwise repair `toMeromorphicNFAt : (𝕜 → E) → 𝕜 → (𝕜 → E)` (`:377`) with
  **`MeromorphicAt.eq_nhdsNE_toMeromorphicNFAt (hf) : f =ᶠ[𝓝[≠] x] toMeromorphicNFAt f x`**
  (`:399`, spiked) and `meromorphicNFAt_toMeromorphicNFAt` (`:404`, spiked). Set-version
  `toMeromorphicNFOn` (`:656`) + `meromorphicOrderAt_toMeromorphicNFOn` (`:754`) exists but we
  use the pointwise one (our repair is chart-local).

### 1.5 `Topology/DiscreteSubset.lean` (codiscrete filters)

- `Filter.codiscreteWithin (S : Set X) : Filter X := ⨆ x ∈ S, 𝓝[S \ {x}] x` (`:201`);
  `Filter.codiscrete X := codiscreteWithin univ` (`:~383`).
- `mem_codiscreteWithin : S ∈ codiscreteWithin T ↔ ∀ x ∈ T, Disjoint (𝓝[≠] x) (𝓟 (T \ S))`
  (`:203`); **`mem_codiscreteWithin_iff_forall_mem_nhdsNE :
  S ∈ codiscreteWithin T ↔ ∀ x ∈ T, S ∪ Tᶜ ∈ 𝓝[≠] x`** (`:213`, spiked — the key to §2.2);
  `mem_codiscreteWithin_accPt` (`:217`); `Filter.codiscreteWithin_mono {U₁ ⊆ U} :
  codiscreteWithin U₁ ≤ codiscreteWithin U` (`:227`, `@[gcongr]`) — gives restriction maps;
  `codiscreteWithin_iff_locallyFiniteComplementWithin [T1Space X]` (`:288`);
  `compl_singleton_mem_codiscreteWithin [T1Space X]` (`:309`);
  `compl_finite_mem_codiscreteWithin` (`:320`); `mem_codiscrete` (`:335`), `mem_codiscrete'`
  (`:343`, `↔ IsOpen S ∧ IsDiscrete Sᶜ`); `codiscrete_le_cofinite [T1Space X]` (`:373`);
  `IsCompact.finite_diff_of_mem_codiscreteWithin` (`:~393`).

### 1.6 `Order/Filter/Germ/Basic.lean`

- `Filter.Germ l β := Quotient (germSetoid l β)` where the setoid relation IS
  `EventuallyEq l` (`:74/:79`) — exactly CC3's quotient.
- `Germ.ofFun` (`:112`, with `↑` coercion), **`Germ.coe_eq : (↑f : Germ l β) = ↑g ↔ f =ᶠ[l] g`**
  (`:186`, spiked), `liftOn` (`:~176`), `map`/`map₂`, `inductionOn`/`inductionOn₂`,
  `compTendsto`/`compTendsto'` (`:231/:242`), `coeRingHom : (α → R) →+* Germ l R` (`:~598`).
- Instances: `CommRing` (`:594`), **`Inv (Germ l G) := ⟨map Inv.inv⟩`** (`:456`) with
  `coe_inv` (`:459`, spiked), `Module R (Germ l M)` (`:654`),
  **`Nontrivial (Germ l R)` for `[Nontrivial R] [NeBot l]`** (`:526`).
  **No `Field`, no `Algebra` instance anywhere at the pin** (grepped) — we add `Algebra ℂ`
  (spiked, §8) and prove `Field` for `ℳ X` ourselves.
- `Algebra.ofModule (h₁ : ∀ r x y, r • x * y = r • (x * y)) (h₂ : …) : Algebra R A`
  (`Algebra/Algebra/Defs.lean:235`, spiked on `Germ l ℂ` — **no diamond**: it reuses the
  existing `Module` scalar action).

### 1.7 `Topology/LocallyFinsupp.lean` (CC2 container)

- `Function.locallyFinsuppWithin (U : Set X) Y` (`:48`), `locallyFinsupp X Y :=
  locallyFinsuppWithin univ Y` (`:61`); `FunLike` (`:125`).
- `single (x : X) (y : Y) : locallyFinsupp X Y` `[DecidableEq X]` (`:153`, **univ-domain
  only** — fits `Divisor X`), `single_apply` (`:~168`).
- **`finiteSupport [T2Space X] (D) (hU : IsCompact U) : Set.Finite D.support`** (`:243`, spiked
  through the `deg` definition); `discreteSupport` (`:210`), `closedSupport` (`:229`).
- `AddCommGroup` (`:379`); `LE` with **`le_def : D₁ ≤ D₂ ↔ (D₁ : X → Y) ≤ D₂`** (`:386`,
  spiked), `lt_def` (`:397`), `Lattice` (`:462`) with `max_apply`/`min_apply`,
  `IsOrderedAddMonoid` (`:490`), `posPart_apply`/`negPart_apply`.
- `restrict (D) (h : V ⊆ U)` (`:566`) with `restrict_apply`, `restrictMonoidHom` (`:607`).
- **No degree functional** at the pin (grepped) — we define it (§5.6).
- `MeromorphicOn.divisor` (`Analysis/Meromorphic/Divisor.lean:39`) is planar-only; we reuse its
  *conventions* (`untop₀` with junk 0) but build the surface divisor ourselves.
  `WithTop.untop₀` spelling confirmed there (`:41`, plus `WithTop.untop₀_eq_zero`,
  `WithTop.coe_untop₀_of_ne_top` used in mathlib proofs).

### 1.8 `Geometry/Manifold/Complex.lean` (compact rigidity) and topology

- Setup `[IsManifold I 1 M]`, `I.Boundaryless`: `MDifferentiable.isLocallyConstant
  [CompactSpace M]` (`:157`), `MDifferentiable.apply_eq_of_compactSpace [PreconnectedSpace M]`
  (`:166`), **`MDifferentiable.exists_eq_const_of_compactSpace : ∃ c, f = fun _ => c`**
  (`:172`, spiked with our instance set) — the Liouville/`L(0)` input.
- `Filter.Tendsto.limUnder_eq [NeBot f] : Tendsto g f (𝓝 x) → limUnder f g = x`
  (`Topology/Separation/Hausdorff.lean:291`, spiked) — the `evalAt` uniqueness atom.

### 1.9 Project exports consumed (read from disk, current builds)

- `Jacobian/Surface/Bridges.lean`: `RS.contMDiffAt_iff_analyticAt {f : X → ℂ} :
  ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x ↔ AnalyticAt ℂ (f ∘ (extChartAt 𝓘(ℂ) x).symm)
  (extChartAt 𝓘(ℂ) x x)` (`:81`); `contMDiffAt_iff_analyticAt_of_mem_source` (`:130`);
  `contMDiffOn_iff_analyticOnNhd_of_subset_source` (`:149`).
  (`extChartAt 𝓘(ℂ) x = chartAt ℂ x` at `rfl`-level on our surfaces — CC7, pinned there.)
- `Jacobian/Surface/Identity.lean`: `RS.map_extChartAt_nhdsNE (x) :
  Filter.map (extChartAt 𝓘(ℂ) x) (𝓝[≠] x) = 𝓝[≠] (extChartAt 𝓘(ℂ) x x)` (`:36`);
  `instance RS.nhdsNE_neBot (x : X) : (𝓝[≠] x).NeBot` (`:58`);
  `eventually_eq_or_eventually_ne` (`:81`); `eq_of_frequently_eq` (`:131`),
  `eq_of_eqOn_of_accPt` (`:159`) — the ContMDiff identity theorem (we need the meromorphic
  variant too, proved here, §6.1).
- `Jacobian/LocalMultiplicity/ChartBridge.lean`: `RS.analyticAt_transition (he he' hx hx') :
  AnalyticAt ℂ (e' ∘ e.symm) (e x) ∧ deriv (e' ∘ e.symm) (e x) ≠ 0` (`:153`);
  `RS.map_nhdsNE` (`:200`); `trans_mem_maximalAtlas` (`:184`).
- `Jacobian/LocalMultiplicity/Multiplicity.lean`: `meromorphicOrderAt_chart_sub` /
  `meromorphicOrderAt_chart_of_eq_zero` (`:226/:236`) — the CC4↔CC3 compatibility lemmas; we
  restate the second as `ordAtX`-compatibility (§4.1) once `ordAtX` exists.

---

## 2. Design decisions

### D1 — `ℳ` via a subalgebra of the germ ring (realizes CC3's quotient)

CC3 freezes the *mathematical* choice: `ℳ X` is the quotient of meromorphic functions by
`=ᶠ[Filter.codiscrete X]`. We realize that quotient as a **subalgebra of mathlib's germ ring**,
which is *literally the same quotient* with the subtype/quotient order swapped:

```
CC3 shape:  {f // MeromorphicOnX f} ⧸ (=ᶠ[codiscrete X])
here:       {γ : Filter.Germ (codiscrete X) ℂ // γ has a meromorphic representative}
```

`Filter.Germ l ℂ = Quotient (germSetoid l ℂ)` and the setoid relation *is* `=ᶠ[l]` (§1.6), so
the two types are canonically isomorphic; membership in the subalgebra is
representative-independent because meromorphy on an **open** set is a `𝓝[≠]`-germ property
(bridge D2 + `MeromorphicAt.congr`). Payoff: `CommRing`, `Module ℂ`, `Algebra ℂ`, `Nontrivial`
arrive from mathlib instances (spiked, §8) instead of ~300 lines of `Quotient.map₂`
boilerplate; `Germ.coe_eq` is the `mk_eq_mk` lemma for free. **This is a plumbing choice, not a
re-choice of CC3**: all downstream-visible API (constructors from meromorphic `f`, `=ᶠ`
characterization of equality, `ord`/`divisor`/`L(D)` on classes) matches CC3's spec verbatim.
One new Compat instance is needed and spiked: `Algebra ℂ (Germ l ℂ)` by `Algebra.ofModule`
(diamond-free; upstreamable).

### D2 — The open-set codiscrete ⇄ punctured-neighborhood bridge is *purely topological*

The pivotal fact making every quotient-descent proof easy: for **open** `U` and *arbitrary*
functions (no meromorphy!),

```
f =ᶠ[codiscreteWithin U] g  ↔  ∀ x ∈ U, f =ᶠ[𝓝[≠] x] g.
```

Proof from `mem_codiscreteWithin_iff_forall_mem_nhdsNE` (`S ∈ codiscreteWithin T ↔ ∀ x ∈ T,
S ∪ Tᶜ ∈ 𝓝[≠] x`): (←) `S ⊆ S ∪ Tᶜ`; (→) intersect `S ∪ Uᶜ ∈ 𝓝[≠] x` with `U ∈ 𝓝[≠] x`
(openness). **Both directions compiled in the spike** (§8, item 4). Consequences: `ord`,
`evalAt`, `divisor` descend to germ classes against arbitrary representatives (via
`meromorphicOrderAt_congr` / `Filter.map_congr`, both meromorphy-free), and mathlib's
`AccPt`-hypothesis lemma §1.3 is never needed. All sets in this unit and in Cech are open.

### D3 — Junk-value conventions (fixed once, table)

| object | honest domain | junk value | why safe |
|---|---|---|---|
| `MeromorphicAtX f x` | — | (Prop) | chart composite junk only off-source; germ at `chartAt x x` unaffected |
| `ordAtX f x` | `MeromorphicAtX f x` | `0` (mathlib's) | every consumer guards with meromorphy or works on `ℳ` |
| `MeroGermOn.ord φ x` | `IsOpen U ∧ x ∈ U` | `0` | gate baked into the definition so `Germ.liftOn` is total; off-`U` value never quoted |
| `evalAt φ x` | gate ∧ `0 ≤ ord φ x` | `0` | matches mathlib NF value at poles; statements guarded by `0 ≤ ord` |
| `divisor φ x` | always honest on `ℳ X` | `untop₀ ⊤ = 0` at `φ = 0` or on `≡0` germs | `divisor 0 = 0` is the *intended* value; multiplicativity guarded by `≠ 0` on connected `X` |
| `L(D)` membership | always honest | none | carrier is an `ord` inequality, `⊤ ≥` anything, so `0 ∈ L(D)` by arithmetic, not by fiat |

None of these junk values can make a downstream statement vacuously true: `l(D)` is the finrank
of an honest submodule of the honest field `ℳ X`, and `holoRepr` produces an *actual function*
with a proved `ContMDiffAt`, which is what genus-zero-headline needs.

### D4 — `L(D)` carrier: the `ord` inequality, with CC3's disjunction as a theorem

CC3 writes `L(D) := {f : ℳ X // f = 0 ∨ div f ≥ -D}`. We take as *carrier* the equivalent
junk-free inequality that needs no case split and makes the submodule proof one-line-per-field:

```
φ ∈ L(D)  :↔  ∀ x, ((-(D x) : ℤ) : WithTop ℤ) ≤ φ.ord x
```

For `φ = 0` every `ord` is `⊤` (holds); for `φ ≠ 0` on connected `X` no `ord` is `⊤` and the
condition is literally `-D ≤ divisor φ` under `untop₀`. The frozen disjunction is exported as
`mem_L_iff_eq_zero_or_le_divisor` (`[ConnectedSpace X]`), so CC3's spec is a proved
characterization, not a lost shape. (On a disconnected `X` the disjunction would be *wrong* —
a function vanishing on one component only has `ord = ⊤` there but nonzero divisor elsewhere —
one more reason the inequality is the right carrier.)

### D5 — `evalAt`/`holoRepr` by pointwise `limUnder`, not by gluing repaired charts

`holoRepr` must produce a single function on `X` that is holomorphic wherever `ord ≥ 0`.
Gluing chart-local `toMeromorphicNFOn` repairs would need a coherence argument at chart
overlaps. Instead, define the **canonical value** of a class at a point:

```
evalAt φ x := (if the gate and 0 ≤ ord φ x then limUnder (𝓝[≠] x) f₀ else 0)
```

for any representative `f₀`. This is class-well-defined (D2 + `Filter.map_congr`), the limit
exists by `tendsto_nhds_of_meromorphicOrderAt_nonneg` transported through the chart, and it is
*automatically coherent*: near a point with `ord ≥ 0` the values agree with the single analytic
chart-local extension (uniqueness of limits, `Filter.Tendsto.limUnder_eq`, `[T2Space ℂ]`,
`(𝓝[≠] x).NeBot` from Surface). So `holoRepr φ := fun x => evalAt φ x` is holomorphic at every
`ord ≥ 0` point *with no gluing lemma at all* (§6.5). Bonus (this is the **rigidified normal
form** the blueprint demands for Čech `H⁰ = L(D)`): `evalAt` depends only on the local germ, so
canonical representatives of *compatible germs on different opens agree pointwise*, which makes
the sheaf-gluing proof for `MeroGermOn` elementary (§6.6). Mathlib's `toMeromorphicNFAt` is kept
as the *proof tool* for "`0 ≤ ord` ⇒ analytic extension exists in the chart" (§1.4) and as the
fallback design (R6).

### D6 — Relative layer `MeroGermOn U` from day one; `ℳ X` is its `univ` instance

Čech (CC8) needs germ spaces over `codiscreteWithin U` for open `U`, restriction maps, and
relative `ord`/`L(D)`. Building `ℳ X` separately would duplicate the whole quotient stack. So:
`MeroGermOn X U` is the primitive (a type synonym for the meromorphic-germ subalgebra over
`codiscreteWithin U`), and `ℳ X := MeroGermOn X Set.univ` (an `abbrev`, so all `MeroGermOn`
API and instances apply to `ℳ X` verbatim; `codiscreteWithin univ = codiscrete X` by
definition). `U` stays a plain `Set X`; definitions that need openness carry a classical
`IsOpen U ∧ x ∈ U` gate *inside* (D3) so the types stay hypothesis-free and the simp lemmas
carry `(hU : IsOpen U)`. Global (`ℳ X`) restatements are provided so downstream never sees a
trivial `x ∈ univ`.

### D7 — Divisor container and degree (CC2)

`Divisor X := Function.locallyFinsuppWithin (Set.univ : Set X) ℤ` exactly as frozen; point
divisors are mathlib's `single` (univ-domain, fits). The missing degree functional is added in
the mathlib namespace (Compat, upstreamable) so dot notation works:
`D.degree := ∑ x ∈ (D.finiteSupport isCompact_univ).toFinset, D x` on `[T2Space X]
[CompactSpace X]` (definition compiled in spike; exports §4.6). CC2's name `Divisor.deg` is
realized as `Function.locallyFinsuppWithin.degree` — rename noted here and in the root
docstring. `divisor : ℳ X → Divisor X` (CC3's `div`; renamed to avoid `Div`-notation collision)
is total — `divisor 0 = 0` falls out of `untop₀ ⊤ = 0` with an *empty support*, no case split
(§6.3).

### D8 — Instance hygiene

Standing variables per CONVENTIONS (`RS` namespace):

```lean
open scoped ContDiff Manifold Topology
open Filter Set
variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
```

`[IsManifold 𝓘(ℂ) ω X]` is added only for chart-invariance lemmas and `holoRepr` holomorphy;
`[T2Space X]` for the identity dichotomy, `degree`, `Field`; `[ConnectedSpace X]` for `Field`,
`divisor` multiplicativity, `L(D)` characterizations; `[CompactSpace X]` for `degree`,
`finiteSupport`, `L(0) = ℂ`. Never assume more than needed; `omit` where free.

---

## 3. File plan (build order)

```
Jacobian/Meromorphic.lean               -- unit root: imports all, 5-15 line API docstring
Jacobian/Meromorphic/Predicates.lean    -- MeromorphicAtX/OnX, ordAtX: chart invariance, algebra, limits
Jacobian/Meromorphic/CodiscreteBridge.lean -- D2 bridge; NeBot; codiscrete congr; meromorphic identity dichotomy
Jacobian/Meromorphic/GermSpace.lean     -- Algebra ℂ (Germ l ℂ) [Compat]; meroGermSubalgebra; MeroGermOn; ℳ X; mk; restrict
Jacobian/Meromorphic/OrderEval.lean     -- ord on classes; evalAt; holoRepr (+ContMDiff); gluing
Jacobian/Meromorphic/Field.lean         -- Inv; Field (ℳ X); ord/⊤ classification of 0
Jacobian/Meromorphic/Divisor.lean       -- Divisor X, degree [Compat]; divisor(On); algebra; pole/zero data
Jacobian/Meromorphic/LinearSystem.lean  -- L(D), l(D); LDOn; mono; L(0)=ℂ; vanishing lemmas; mulEquiv
```

Import spine (targeted): `Mathlib.Analysis.Meromorphic.Basic/Order/IsolatedZeros/NormalForm`,
`Mathlib.Topology.DiscreteSubset`, `Mathlib.Order.Filter.Germ.Basic`,
`Mathlib.Topology.LocallyFinsupp`, `Mathlib.Geometry.Manifold.Complex` (LinearSystem only),
plus project `Jacobian.Surface.Bridges`, `Jacobian.Surface.Identity`,
`Jacobian.LocalMultiplicity.ChartBridge`. Dependency chain is linear in the listed order
(`Field` needs `OrderEval`'s `ord_*`; `Divisor` needs `Field`'s nonvanishing classification;
`LinearSystem` needs everything).

---

## 4. Exports — exact signatures

Everything in `namespace RS`. `f g : X → ℂ`, `x : X`, `U V : Set X`, `e : OpenPartialHomeomorph
X ℂ`, `φ ψ : MeroGermOn X U` (or `ℳ X`), `D E : Divisor X`, `c : ℂ`.

### 4.1 `Predicates.lean`

```lean
/-- CC3 (frozen): meromorphy of the standard-chart composite. Junk-robust. -/
def MeromorphicAtX (f : X → ℂ) (x : X) : Prop :=
  MeromorphicAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)

/-- Relative CC3 predicate; the frozen global one is `MeromorphicOnX f Set.univ`. -/
def MeromorphicOnX (f : X → ℂ) (U : Set X) : Prop := ∀ x ∈ U, MeromorphicAtX f x

theorem meromorphicOnX_univ : MeromorphicOnX f univ ↔ ∀ x, MeromorphicAtX f x

-- chart invariance ([IsManifold 𝓘(ℂ) ω X] from here on where charts vary)
theorem meromorphicAtX_iff_of_mem_source
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (hx : x ∈ e.source) :
    MeromorphicAtX f x ↔ MeromorphicAt (f ∘ e.symm) (e x)

-- transfer & closure
theorem ContMDiffAt.meromorphicAtX (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x) : MeromorphicAtX f x
theorem MeromorphicAtX.congr (hf : MeromorphicAtX f x) (h : f =ᶠ[𝓝[≠] x] g) : MeromorphicAtX g x
theorem MeromorphicAtX.add/mul/neg/sub/smul/inv/pow/zpow  -- mirroring §1.1, `.inv` unconditional
theorem meromorphicAtX_const (c : ℂ) : MeromorphicAtX (fun _ => c) x
-- and the same suite on `MeromorphicOnX · U` (pointwise ∀-lifting)

/-- CC3 (frozen): the order at `x`, `WithTop ℤ`-valued, junk `0` off meromorphy. -/
noncomputable def ordAtX (f : X → ℂ) (x : X) : WithTop ℤ :=
  meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)

theorem ordAtX_eq_of_mem_source (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X)
    (hx : x ∈ e.source) : ordAtX f x = meromorphicOrderAt (f ∘ e.symm) (e x)
theorem ordAtX_congr (h : f =ᶠ[𝓝[≠] x] g) : ordAtX f x = ordAtX g x   -- meromorphy-free

-- classification (⊤ = locally-≡0 on the punctured filter; pole = neg; finite value = z^n·unit)
theorem ordAtX_eq_top_iff : ordAtX f x = ⊤ ↔ f =ᶠ[𝓝[≠] x] 0
theorem ordAtX_ne_top_iff (hf : MeromorphicAtX f x) :
    ordAtX f x ≠ ⊤ ↔ ∀ᶠ z in 𝓝[≠] x, f z ≠ 0
theorem MeromorphicAtX.frequently_zero_iff (hf : MeromorphicAtX f x) :
    (∃ᶠ z in 𝓝[≠] x, f z = 0) ↔ f =ᶠ[𝓝[≠] x] 0
theorem ContMDiffAt.ordAtX_nonneg (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x) : 0 ≤ ordAtX f x
theorem tendsto_nhds_iff_ordAtX_nonneg (hf : MeromorphicAtX f x) :
    (∃ c, Tendsto f (𝓝[≠] x) (𝓝 c)) ↔ 0 ≤ ordAtX f x
theorem tendsto_cobounded_iff_ordAtX_neg (hf : MeromorphicAtX f x) :
    Tendsto f (𝓝[≠] x) (Bornology.cobounded ℂ) ↔ ordAtX f x < 0
/-- "analytic ⟺ 0 ≤ ord", stated honestly: analyticity of a REPAIR of `f`, since `f` itself
may carry junk at `x` (careful point flagged in the task: `⊤` means locally-≡0, and `f` need
not be analytic at `x` even when `ord ≥ 0`). -/
theorem exists_contMDiffAt_eventuallyEq_iff_ordAtX_nonneg (hf : MeromorphicAtX f x) :
    (∃ g, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω g x ∧ f =ᶠ[𝓝[≠] x] g) ↔ 0 ≤ ordAtX f x

-- arithmetic (chart composites are literal +,*,⁻¹ of chart composites: `rfl`)
theorem ordAtX_add (hf : MeromorphicAtX f x) (hg : MeromorphicAtX g x) :
    min (ordAtX f x) (ordAtX g x) ≤ ordAtX (f + g) x
theorem ordAtX_add_of_ne (hf hg) (h : ordAtX f x ≠ ordAtX g x) :
    ordAtX (f + g) x = min (ordAtX f x) (ordAtX g x)
theorem ordAtX_mul (hf hg) : ordAtX (f * g) x = ordAtX f x + ordAtX g x
theorem ordAtX_inv : ordAtX f⁻¹ x = -ordAtX f x                     -- unconditional
theorem ordAtX_neg : ordAtX (-f) x = ordAtX f x
theorem ordAtX_smul (hf) (hc : c ≠ 0) : ordAtX (c • f) x = ordAtX f x
theorem ordAtX_const : ordAtX (fun _ => c) x = if c = 0 then ⊤ else 0
theorem ordAtX_zero : ordAtX (0 : X → ℂ) x = ⊤ ; theorem ordAtX_one : ordAtX (1 : X → ℂ) x = 0

-- eventual behavior (feeds divisor local finiteness §6.3)
theorem eventually_ordAtX_eq_zero (hf : MeromorphicAtX f x) (h : ordAtX f x ≠ ⊤) :
    ∀ᶠ y in 𝓝[≠] x, ordAtX f y = 0
theorem eventually_ordAtX_eq_top [T1Space X] (h : ordAtX f x = ⊤) :
    ∀ᶠ y in 𝓝 x, ordAtX f y = ⊤
theorem eventually_meromorphicAtX (hf : MeromorphicAtX f x) : ∀ᶠ y in 𝓝[≠] x, MeromorphicAtX f y

-- CC4 compatibility (restatement of LocalMultiplicity's export in ordAtX vocabulary)
theorem ordAtX_of_contMDiffAt_eq_zero (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x) (h0 : f x = 0) :
    ordAtX f x = (multiplicityENat f x).map (Nat.cast : ℕ → ℤ)
```

### 4.2 `CodiscreteBridge.lean`

```lean
-- D2 (both directions spiked); α arbitrary — used for ℂ and for Prop-valued transports
theorem eventuallyEq_codiscreteWithin_iff_of_isOpen {α : Type*} {f g : X → α}
    (hU : IsOpen U) : f =ᶠ[codiscreteWithin U] g ↔ ∀ x ∈ U, f =ᶠ[𝓝[≠] x] g
theorem eventually_codiscreteWithin_iff_of_isOpen {p : X → Prop} (hU : IsOpen U) :
    (∀ᶠ x in codiscreteWithin U, p x) ↔ ∀ x ∈ U, ∀ᶠ y in 𝓝[≠] x, p y
theorem eventuallyEq_codiscrete_iff {α} {f g : X → α} :
    f =ᶠ[codiscrete X] g ↔ ∀ x, f =ᶠ[𝓝[≠] x] g

theorem codiscreteWithin_neBot (hU : IsOpen U) (hne : U.Nonempty) :
    (codiscreteWithin U).NeBot
instance [Nonempty X] : (codiscrete X).NeBot     -- 𝓝[≠]-NeBot from Surface

theorem MeromorphicOnX.congr_codiscreteWithin (hf : MeromorphicOnX f U) (hU : IsOpen U)
    (h : f =ᶠ[codiscreteWithin U] g) : MeromorphicOnX g U

/-- Meromorphic functions on an open set are chart-analytic off a set codiscrete in it. -/
theorem MeromorphicOnX.analyticAt_codiscreteWithin [IsManifold 𝓘(ℂ) ω X]
    (hf : MeromorphicOnX f U) (hU : IsOpen U) :
    ∀ᶠ y in codiscreteWithin U, AnalyticAt ℂ (f ∘ (chartAt ℂ y).symm) (chartAt ℂ y y)

/-- The meromorphic identity dichotomy on a connected surface (§6.1): a function meromorphic
everywhere is codiscretely zero, or nowhere locally-≡0. -/
theorem MeromorphicOnX.eventuallyEq_zero_or_forall_ordAtX_ne_top
    [T1Space X] [ConnectedSpace X] (hf : MeromorphicOnX f univ) :
    f =ᶠ[codiscrete X] 0 ∨ ∀ x, ordAtX f x ≠ ⊤
theorem MeromorphicOnX.codiscrete_setOf_ne_zero [T1Space X] [ConnectedSpace X]
    (hf : MeromorphicOnX f univ) (h : ¬ f =ᶠ[codiscrete X] 0) :
    ∀ᶠ z in codiscrete X, f z ≠ 0
```

### 4.3 `GermSpace.lean`

```lean
-- Compat (upstreamable; spiked verbatim §8):
noncomputable instance {α : Type*} {l : Filter α} : Algebra ℂ (Filter.Germ l ℂ) :=
  Algebra.ofModule (…smul_mul_assoc…) (…mul_smul_comm…)
@[simp] theorem Filter.Germ.algebraMap_apply {l : Filter α} (c : ℂ) :
    algebraMap ℂ (Germ l ℂ) c = ((fun _ => c : α → ℂ) : Germ l ℂ)

variable (X) in
/-- Germs over `codiscreteWithin U` admitting a meromorphic representative. -/
noncomputable def meroGermSubalgebra (U : Set X) :
    Subalgebra ℂ (Filter.Germ (Filter.codiscreteWithin U) ℂ)
-- carrier {γ | ∃ f, MeromorphicOnX f U ∧ γ = Filter.Germ.ofFun f}; closure via §1.1 + coe_add/mul

variable (X) in
/-- The space of meromorphic germ classes on `U` (CC3 relativized; junk-free). -/
def MeroGermOn (U : Set X) : Type _ := meroGermSubalgebra X U

variable (X) in
/-- CC3 (frozen): the field of meromorphic functions, `ℳ X`. -/
abbrev Mero : Type _ := MeroGermOn X Set.univ
scoped notation "ℳ" => RS.Mero            -- `ℳ X`; fallback plain `Mero X` if parsing fights

instance : CommRing (MeroGermOn X U) ; instance : Algebra ℂ (MeroGermOn X U)
  -- (Module ℂ follows; both `inferInstanceAs` transports along the type synonym)
instance [Nonempty X] : Nontrivial (ℳ X)     -- via Germ.instNontrivial + codiscrete NeBot

namespace MeroGermOn
def mk (f : X → ℂ) (hf : MeromorphicOnX f U) : MeroGermOn X U
theorem mk_eq_mk {hf hg} : mk f hf = mk g hg ↔ f =ᶠ[codiscreteWithin U] g
theorem exists_rep (φ : MeroGermOn X U) : ∃ f hf, mk f hf = φ
@[elab_as_elim] theorem ind {motive : MeroGermOn X U → Prop}
    (h : ∀ f hf, motive (mk f hf)) (φ) : motive φ
@[simp] theorem mk_add / mk_mul / mk_neg / mk_smul / mk_zero / mk_one …  -- op ↔ pointwise op
theorem algebraMap_mk (c : ℂ) : algebraMap ℂ (MeroGermOn X U) c = mk (fun _ => c) …

/-- Restriction to a smaller open set (Čech's structure maps). -/
noncomputable def restrict (h : V ⊆ U) : MeroGermOn X U →ₐ[ℂ] MeroGermOn X V
@[simp] theorem restrict_mk (h : V ⊆ U) {hf} :
    restrict h (mk f hf) = mk f (fun x hx => hf x (h hx))
theorem restrict_restrict / restrict_id  -- (functoriality; presheaf laws for Čech)
end MeroGermOn

theorem algebraMap_injective [Nonempty X] : Function.Injective (algebraMap ℂ (ℳ X))
-- the task's `ℂ →+* ℳ X`: `(algebraMap ℂ (ℳ X)).toRingHom`, injective by the above
```

### 4.4 `OrderEval.lean`

```lean
namespace MeroGermOn
/-- Order of a germ class at a point; junk `0` unless `IsOpen U ∧ x ∈ U` (D3). -/
noncomputable def ord (φ : MeroGermOn X U) (x : X) : WithTop ℤ
@[simp] theorem ord_mk (hU : IsOpen U) (hx : x ∈ U) {hf} : (mk f hf).ord x = ordAtX f x
theorem ord_restrict (h : V ⊆ U) (hV : IsOpen V) (hU : IsOpen U) (hx : x ∈ V) :
    (restrict h φ).ord x = φ.ord x

-- class-level order calculus (each with hypotheses (hU : IsOpen U) (hx : x ∈ U); on ℳ X the
-- global restatements below drop them)
theorem ord_zero : (0 : MeroGermOn X U).ord x = if IsOpen U ∧ x ∈ U then ⊤ else 0
theorem ord_one (hU hx) : (1 : MeroGermOn X U).ord x = 0
theorem ord_add (hU hx) : min (φ.ord x) (ψ.ord x) ≤ (φ + ψ).ord x
theorem ord_add_of_ne (hU hx) (h : φ.ord x ≠ ψ.ord x) : (φ + ψ).ord x = min (φ.ord x) (ψ.ord x)
theorem ord_mul (hU hx) : (φ * ψ).ord x = φ.ord x + ψ.ord x
theorem ord_neg : (-φ).ord x = φ.ord x
theorem ord_smul (hU hx) (hc : c ≠ 0) : (c • φ).ord x = φ.ord x
theorem ord_algebraMap (hU hx) (hc : c ≠ 0) : (algebraMap ℂ _ c).ord x = 0

/-- Canonical value (D5): the limit along `𝓝[≠] x` when `0 ≤ ord`, junk `0` else. -/
noncomputable def evalAt (φ : MeroGermOn X U) (x : X) : ℂ
theorem tendsto_evalAt (hU hx) (h : 0 ≤ φ.ord x) {hf} (hrep : mk f hf = φ) :
    Tendsto f (𝓝[≠] x) (𝓝 (φ.evalAt x))
@[simp] theorem evalAt_of_not_nonneg (h : ¬ 0 ≤ φ.ord x) : φ.evalAt x = 0
theorem evalAt_add (hU hx) (h₁ : 0 ≤ φ.ord x) (h₂ : 0 ≤ ψ.ord x) :
    (φ + ψ).evalAt x = φ.evalAt x + ψ.evalAt x
theorem evalAt_smul (hU hx) (h : 0 ≤ φ.ord x) : (c • φ).evalAt x = c * φ.evalAt x
theorem evalAt_mul (hU hx) (h₁ : 0 ≤ φ.ord x) (h₂ : 0 ≤ ψ.ord x) :
    (φ * ψ).evalAt x = φ.evalAt x * ψ.evalAt x
theorem evalAt_mk_of_contMDiffAt (hU hx) {hf} (hc : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x) :
    (mk f hf).evalAt x = f x                                    -- honest value
theorem evalAt_restrict (h : V ⊆ U) (hV hU) (hx : x ∈ V) :
    (restrict h φ).evalAt x = φ.evalAt x                        -- pointwise rigidity

/-- CC3's `holoRepr` (D5): the canonical repaired representative. -/
noncomputable def holoRepr (φ : MeroGermOn X U) : X → ℂ := fun x => φ.evalAt x

-- [IsManifold 𝓘(ℂ) ω X] [T2Space X] for this block
theorem holoRepr_contMDiffAt (hU : IsOpen U) (hx : x ∈ U) (h : 0 ≤ φ.ord x) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω φ.holoRepr x
theorem holoRepr_contMDiffOn (hU : IsOpen U) (h : ∀ x ∈ U, 0 ≤ φ.ord x) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω φ.holoRepr U
theorem holoRepr_contMDiff (φ : ℳ X) (h : ∀ x, 0 ≤ φ.ord x) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω φ.holoRepr                            -- headline's form
theorem holoRepr_eventuallyEq_nhdsNE (hU hx) {hf} (hrep : mk f hf = φ) :
    φ.holoRepr =ᶠ[𝓝[≠] x] f
theorem meromorphicOnX_holoRepr (hU : IsOpen U) : MeromorphicOnX φ.holoRepr U
theorem mk_holoRepr (hU : IsOpen U) : mk φ.holoRepr (meromorphicOnX_holoRepr hU) = φ
theorem holoRepr_restrict (h : V ⊆ U) (hV hU) : Set.EqOn ((restrict h φ).holoRepr) φ.holoRepr V
theorem continuousAt_holoRepr (hU hx) (h : 0 ≤ φ.ord x) : ContinuousAt φ.holoRepr x
theorem tendsto_holoRepr_cobounded_iff (hU hx) :
    Tendsto φ.holoRepr (𝓝[≠] x) (Bornology.cobounded ℂ) ↔ φ.ord x < 0   -- ℙ¹ pole data

/-- Sheaf gluing over an open cover (the Čech `H⁰` engine; §6.6). -/
theorem exists_glue {ι : Type*} {U : ι → Set X} (hU : ∀ i, IsOpen (U i))
    (φ : ∀ i, MeroGermOn X (U i))
    (hcompat : ∀ i j, restrict inter_subset_left (φ i) = restrict inter_subset_right (φ j)) :
    ∃ Φ : MeroGermOn X (⋃ i, U i), ∀ i, restrict (subset_iUnion U i) Φ = φ i
theorem glue_unique {ι} {U : ι → Set X} (hU : ∀ i, IsOpen (U i))
    {Φ Ψ : MeroGermOn X (⋃ i, U i)}
    (h : ∀ i, restrict (subset_iUnion U i) Φ = restrict (subset_iUnion U i) Ψ) : Φ = Ψ
end MeroGermOn
```

### 4.5 `Field.lean`  (`[T2Space X] [ConnectedSpace X]` where marked)

```lean
noncomputable instance : Inv (MeroGermOn X U)      -- pointwise on germs (Germ.instInv + mem)
@[simp] theorem MeroGermOn.mk_inv {hf} : (mk f hf)⁻¹ = mk f⁻¹ (hf.inv)
theorem MeroGermOn.ord_inv (hU hx) : (φ⁻¹).ord x = -(φ.ord x)

-- classification of the zero class on connected X (from the §4.2 dichotomy):
theorem Mero.ord_ne_top [T2Space X] [ConnectedSpace X] {φ : ℳ X} (h : φ ≠ 0) (x : X) :
    φ.ord x ≠ ⊤
theorem Mero.ord_eq_top_iff [T2Space X] [ConnectedSpace X] {φ : ℳ X} (x : X) :
    φ.ord x = ⊤ ↔ φ = 0

/-- CC3: `ℳ X` is a field on a connected surface. `Inv` is the honest pointwise inverse. -/
noncomputable instance [T2Space X] [ConnectedSpace X] : Field (ℳ X)
-- built from the CommRing with explicit inv; mul_inv_cancel via §6.2; inv_zero pointwise;
-- exists_pair_ne from Nontrivial; nnqsmul/qsmul/ratCast left to structure defaults
```

### 4.6 `Divisor.lean`

```lean
variable (X) in
/-- CC2 (frozen). -/
abbrev Divisor := Function.locallyFinsuppWithin (Set.univ : Set X) ℤ

-- Compat (upstreamable; in namespace Function.locallyFinsuppWithin so `D.degree` works):
/-- Degree of a divisor on a compact space (CC2's `deg`; absent from mathlib at the pin). -/
noncomputable def Function.locallyFinsuppWithin.degree [TopologicalSpace X] [T2Space X]
    [CompactSpace X] {Y : Type*} [AddCommMonoid Y]
    (D : Function.locallyFinsuppWithin (Set.univ : Set X) Y) : Y :=
  ∑ x ∈ (D.finiteSupport isCompact_univ).toFinset, D x
@[simp] theorem degree_zero : (0 : Divisor X).degree = 0
theorem degree_add : (D + E).degree = D.degree + E.degree
theorem degree_neg : (-D).degree = -D.degree
@[simp] theorem degree_single [DecidableEq X] (x : X) (n : ℤ) :
    (Function.locallyFinsupp.single x n).degree = n
theorem degree_mono (h : D ≤ E) : D.degree ≤ E.degree
theorem degree_nonneg_of_nonneg (h : 0 ≤ D) : 0 ≤ D.degree ; theorem degree_pos_of… (0 < D)

namespace MeroGermOn
/-- Relative divisor of a germ class (support automatically inside `U` by the D3 junk). -/
noncomputable def divisorOn (φ : MeroGermOn X U) : Function.locallyFinsuppWithin U ℤ
-- toFun x := (φ.ord x).untop₀ ; local finiteness §6.3
@[simp] theorem divisorOn_apply : φ.divisorOn x = (φ.ord x).untop₀
end MeroGermOn

/-- CC3's `div : ℳ X → Divisor X` (renamed `divisor`; total, `divisor 0 = 0` honestly). -/
noncomputable abbrev divisor (φ : ℳ X) : Divisor X := φ.divisorOn
@[simp] theorem divisor_apply (φ : ℳ X) (x : X) : divisor φ x = (φ.ord x).untop₀
@[simp] theorem divisor_zero : divisor (0 : ℳ X) = 0

-- algebra ([T2Space X] [ConnectedSpace X]):
theorem divisor_mul {φ ψ : ℳ X} (hφ : φ ≠ 0) (hψ : ψ ≠ 0) :
    divisor (φ * ψ) = divisor φ + divisor ψ
theorem divisor_inv (φ : ℳ X) : divisor φ⁻¹ = -divisor φ            -- unconditional
theorem min_divisor_le_divisor_add {φ ψ : ℳ X} (h : φ + ψ ≠ 0) :
    min (divisor φ) (divisor ψ) ≤ divisor (φ + ψ)
theorem divisor_smul {φ : ℳ X} (hc : c ≠ 0) : divisor (c • φ) = divisor φ
theorem divisor_algebraMap (c : ℂ) : divisor (algebraMap ℂ (ℳ X) c) = 0
theorem divisor_eq_zero_of_ord_nonneg …  -- holomorphic classes have effective (≥0) divisor:
theorem divisor_nonneg_iff [T2Space X] [ConnectedSpace X] {φ : ℳ X} (h : φ ≠ 0) :
    0 ≤ divisor φ ↔ ∀ x, 0 ≤ φ.ord x

-- compactness + pole/zero data (projective-line's shopping list):
theorem finite_support_divisor [T2Space X] [CompactSpace X] (φ : ℳ X) :
    (divisor φ).support.Finite                                     -- = finiteSupport
theorem finite_setOf_ord_neg [T2Space X] [CompactSpace X] [ConnectedSpace X]
    {φ : ℳ X} (h : φ ≠ 0) : {x | φ.ord x < 0}.Finite               -- poles
theorem finite_setOf_ord_pos … {x | 0 < φ.ord x}.Finite            -- zeros
theorem eventually_ord_eq_zero [T2Space X] [ConnectedSpace X] {φ : ℳ X} (h : φ ≠ 0) (x : X) :
    ∀ᶠ y in 𝓝[≠] x, φ.ord y = 0                                    -- zeros/poles isolated
```

### 4.7 `LinearSystem.lean`

```lean
variable [T2Space X]

/-- CC3's `L(D)` (carrier per D4; 0 ∈ L(D) by `⊤`-arithmetic, not fiat). -/
noncomputable def LinSys (D : Divisor X) : Submodule ℂ (ℳ X) where
  carrier := {φ | ∀ x, ((-(D x) : ℤ) : WithTop ℤ) ≤ φ.ord x} …
scoped notation "L(" D ")" => RS.LinSys D          -- optional; plain `LinSys D` is primary

theorem mem_linSys_iff {φ : ℳ X} : φ ∈ LinSys D ↔ ∀ x, ((-(D x) : ℤ) : WithTop ℤ) ≤ φ.ord x
/-- CC3's frozen shape, recovered as a characterization on connected X. -/
theorem mem_linSys_iff_eq_zero_or_le_divisor [ConnectedSpace X] {φ : ℳ X} :
    φ ∈ LinSys D ↔ φ = 0 ∨ -D ≤ divisor φ

/-- CC3: `l D`. Finiteness is NOT this unit's business (Čech/finiteness proves
`FiniteDimensional`); until then `finrank` junk-returns 0 on infinite-dimensional spaces —
no lemma here depends on finiteness. -/
noncomputable def l (D : Divisor X) : ℕ := Module.finrank ℂ (LinSys D)

theorem linSys_mono (h : D ≤ E) : LinSys D ≤ LinSys E
theorem one_mem_linSys_iff : (1 : ℳ X) ∈ LinSys D ↔ 0 ≤ D
theorem algebraMap_mem_linSys (h : 0 ≤ D) (c : ℂ) : algebraMap ℂ (ℳ X) c ∈ LinSys D

-- the two vanishing/constancy results provable NOW ([CompactSpace X] [ConnectedSpace X]):
theorem linSys_zero_eq_span_one : LinSys (0 : Divisor X) = Submodule.span ℂ {1}
theorem l_zero : l (0 : Divisor X) = 1                              -- Liouville, honest finrank
theorem linSys_eq_bot_of_nonpos_of_ne_zero (h : D ≤ 0) (hD : D ≠ 0) : LinSys D = ⊥
theorem l_eq_zero_of_nonpos_of_ne_zero (h : D ≤ 0) (hD : D ≠ 0) : l D = 0

/-- `deg D < 0 → L(D) = 0`, CONDITIONAL on `deg ∘ divisor = 0` — that input is owned by
proper-map-degree (blueprint routing: argument-principle/degree, NOT Stokes). This unit ships
the one-line bookkeeping so proper-map-degree/riemann-roch just plug in. -/
theorem linSys_eq_bot_of_degree_neg
    (hdeg : ∀ φ : ℳ X, φ ≠ 0 → (divisor φ).degree = 0)
    (h : D.degree < 0) : LinSys D = ⊥

/-- Multiplication equivalence (linear-equivalence of linear systems; Miranda V.3.11 vocab,
riemann-roch's lattice tool): for `φ ≠ 0`, `ψ ↦ φ • ψ` maps `L(D)` iso `L(D - divisor φ)`. -/
noncomputable def linSysMulEquiv [ConnectedSpace X] {φ : ℳ X} (hφ : φ ≠ 0) (D : Divisor X) :
    LinSys D ≃ₗ[ℂ] LinSys (D - divisor φ)

-- relative version (CC8 Čech cochain spaces):
noncomputable def LinSysOn (D : Divisor X) (U : Set X) : Submodule ℂ (MeroGermOn X U)
-- carrier {φ | ∀ x ∈ U, (-(D x) : WithTop ℤ) ≤ φ.ord x}
theorem restrict_mem_linSysOn (h : V ⊆ U) (hV : IsOpen V) (hU : IsOpen U)
    {φ} (hφ : φ ∈ LinSysOn D U) : MeroGermOn.restrict h φ ∈ LinSysOn D V
theorem mem_linSys_iff_forall_restrict {ι} {U : ι → Set X} (hU : ∀ i, IsOpen (U i))
    (hcov : ⋃ i, U i = univ) {φ : ℳ X} :
    φ ∈ LinSys D ↔ ∀ i, MeroGermOn.restrict (by simp [hcov]) φ ∈ LinSysOn D (U i)
    -- with `exists_glue`, this IS `H⁰(𝔘, O_D) = L(D)` up to Čech bookkeeping
```

---

## 6. Proof plans for the six hardest items

### 6.1 The meromorphic identity dichotomy (feeds Field, divisor, L(D))

Statement: `[T1] [ConnectedSpace X]`, `hf : MeromorphicOnX f univ` ⇒
`f =ᶠ[codiscrete X] 0 ∨ ∀ x, ordAtX f x ≠ ⊤`.

Set `S := {x | f =ᶠ[𝓝[≠] x] 0}` (note `ordAtX f x = ⊤ ↔ x ∈ S` by `ordAtX_eq_top_iff` +
chart transport `map_extChartAt_nhdsNE`).
- **S open**: `x ∈ S` gives open `W ∋ x` with `f = 0` on `W \ {x}`. For `y ∈ W`: if `y = x`
  done; else `W \ {x}` is open ∋ y (T1 for `{x}ᶜ` open), and `f = 0` on `(W \ {x}) \ {y} ∈
  𝓝[≠] y`. So `W ⊆ S`.
- **S closed**: let `x ∈ closure S`. Claim `∃ᶠ z in 𝓝[≠] x, f z = 0`: any punctured
  neighborhood `N` of `x` contains some `y ∈ S` (if `y = x` can't be excluded, use instead:
  every open `V ∋ x` meets `S`; pick `y ∈ V ∩ S`; if `y ≠ x` then since `f ≡ 0` on a punctured
  neighborhood of `y` and `(𝓝[≠] y).NeBot` (Surface instance), `V ∩ {z ≠ x | f z = 0} ≠ ∅`;
  if `y = x` then `x ∈ S` directly). Frequent vanishing + `MeromorphicAtX.frequently_zero_iff`
  (transported `MeromorphicAt.frequently_zero_iff_eventuallyEq_zero` via
  `map_extChartAt_nhdsNE`) gives `x ∈ S`.
- Connectedness: `S` clopen ⇒ `S = ∅` (right disjunct) or `S = univ`; in the latter case
  `∀ x, f =ᶠ[𝓝[≠] x] 0` ⇒ `f =ᶠ[codiscrete X] 0` by the D2 bridge (`U = univ` open).

Corollary (`codiscrete_setOf_ne_zero`): if `¬ f =ᶠ[codiscrete X] 0`, the dichotomy gives
`ordAtX f x ≠ ⊤` everywhere; then `ordAtX_ne_top_iff` gives `∀ x, ∀ᶠ z in 𝓝[≠] x, f z ≠ 0`
(chart-transported), i.e. `{f ≠ 0} ∈ 𝓝[≠] x` for every `x`, i.e. `{f ≠ 0} ∈ codiscrete X`
(D2 again). (Alternative: transport mathlib's `MeromorphicOn.codiscreteWithin_setOf_ne_zero`
chart-by-chart — more gluing; the direct route is shorter.)

### 6.2 `Field (ℳ X)` — the inverse, junk-free

- `Inv (MeroGermOn X U)`: for `⟨γ, hγ⟩`, the inverse germ is `γ⁻¹` (mathlib's pointwise
  `Germ.instInv`, `0⁻¹ = 0` junk is *inside ℂ* and harmless); membership: pick `hγ`'s
  representative `f` (`MeromorphicOnX f U`), then `γ⁻¹ = ofFun f⁻¹` (`Germ.coe_inv`) and
  `MeromorphicOnX f⁻¹ U` since `(f⁻¹) ∘ e.symm = (f ∘ e.symm)⁻¹` is `rfl` (Pi.inv) and
  `MeromorphicAt.inv` is unconditional. **No `if` in the definition**; `inv_zero` holds
  because `(const 0)⁻¹ = const 0` pointwise.
- `mul_inv_cancel` (`φ ≠ 0`, `[T2] [ConnectedSpace X]`): pick representative `f`;
  `φ ≠ 0 ↔ ¬ f =ᶠ[codiscrete X] 0` (`mk_eq_mk` + `mk_zero`). By §6.1's corollary
  `{z | f z ≠ 0} ∈ codiscrete X`. On that set `f z * (f z)⁻¹ = 1` (`mul_inv_cancel₀`), so
  `f * f⁻¹ =ᶠ[codiscrete X] 1`, i.e. `mk f · * mk f⁻¹ · = 1` via `mk_mul`/`mk_eq_mk`.
- Assembly: `Field (ℳ X) := { inferInstanceAs (CommRing (ℳ X)) with inv, mul_inv_cancel,
  inv_zero, exists_pair_ne := Nontrivial…, — nnqsmul/qsmul/nnratCast/ratCast: defaults }`.
  Pattern check against `RatFunc.instField` (`FieldTheory/RatFunc/Basic.lean`) if the
  structure-defaults fight; worst case supply `qsmul := _root_.qsmulRec _` explicitly.
- `ord_inv` on classes: representative + `meromorphicOrderAt_inv` (unconditional) +
  chart-invariance; `-⊤ = ⊤` matches the `φ = 0` case.

### 6.3 `divisorOn` local finiteness (no connectedness, no compactness)

Fields of `Function.locallyFinsuppWithin U ℤ` for `toFun x := (φ.ord x).untop₀`:
- `supportWithinDomain'`: for `x ∉ U` (or `U` not open), `ord = 0` junk ⇒ `untop₀ = 0` ⇒
  `x ∉ support`. (The D3 junk choice `0` is load-bearing here — support control for free.)
- `supportLocallyFiniteWithinDomain'`: fix `z ∈ U`; wlog `IsOpen U` (else `ord ≡ 0` junk and
  the support is empty — `by_cases` once). Pick representative `f`; `MeromorphicAtX f z`.
  Two cases on `ordAtX f z`:
  * `= ⊤`: then `f =ᶠ[𝓝[≠] z] 0`, so `f = 0` on `W \ {z}` with `W ∈ 𝓝 z`, `W ⊆ U` open.
    Every `y ∈ W` has `f =ᶠ[𝓝[≠] y] 0` (T1 as in §6.1) ⇒ `ord φ y = ⊤` ⇒ `untop₀ = 0`.
    Take `t := W`: `t ∩ support = ∅`.
  * `≠ ⊤`: `eventually_ordAtX_eq_zero` (§4.1): `∀ᶠ y in 𝓝[≠] z, ordAtX f y = 0`. Its proof:
    write `n := ord` and use `meromorphicOrderAt_eq_int_iff` in the chart at `z`: on some
    `V \ {chart z}` the chart composite *equals* `(· - chart z) ^ n • g` with `g` analytic,
    `g (chart z) ≠ 0`; shrink `V` so `g ≠ 0` on it. At `w ∈ V \ {chart z}` that function is
    analytic and nonvanishing (equality holds on the OPEN set `V \ {chart z}`, so
    `AnalyticAt`-congr applies), hence `meromorphicOrderAt … w = 0`; convert to `ordAtX f y = 0`
    for `y := chart.symm w` by `ordAtX_eq_of_mem_source` (order read in the chart at `z`,
    membership `y ∈ (chartAt ℂ z).source`). Then take `t := (that punctured nbhd) ∪ {z}` ∈ 𝓝 z:
    `t ∩ support ⊆ {z}`, finite.
- Class-level: `ord` is already quotient-level (§6.4), so `divisorOn` needs no further descent.
- Compactness: `finite_support_divisor := (divisor φ).finiteSupport isCompact_univ`
  (mathlib, spiked). Poles/zeros: `{x | φ.ord x < 0} ⊆ (divisor φ).support` given `φ ≠ 0`
  (connected ⇒ no `⊤` ⇒ `untop₀` faithful) ⇒ finite; same for zeros.

### 6.4 `ord` well-definedness on classes + chart invariance

Two layers.
1. **Chart invariance of `ordAtX`** (`ordAtX_eq_of_mem_source`): let `e` be a maximal-atlas
   chart, `x ∈ e.source`, `c := chartAt ℂ x`. On a neighborhood of `e x`,
   `f ∘ e.symm = (f ∘ c.symm) ∘ (c ∘ e.symm)` up to `=ᶠ[𝓝 (e x)]` (both charts contain `x`;
   sources overlap on an open set; use `OpenPartialHomeomorph` composition lemmas +
   `Filter.EventuallyEq` on the overlap image). `τ := c ∘ e.symm` is analytic with
   `deriv τ (e x) ≠ 0` by `RS.analyticAt_transition` (LocalMultiplicity, on disk). Apply
   `meromorphicOrderAt_comp_of_deriv_ne_zero` (no hypothesis on `f`!) and
   `meromorphicOrderAt_congr` for the `=ᶠ` step. Same skeleton proves
   `meromorphicAtX_iff_of_mem_source` via `meromorphicAt_comp_iff_of_deriv_ne_zero`.
2. **Descent to `MeroGermOn`**: define
   `ord φ x := Germ.liftOn φ.toGerm (fun f => if IsOpen U ∧ x ∈ U then ordAtX f x else 0) h`
   where `h` needs, for ARBITRARY `f =ᶠ[codiscreteWithin U] g` (not necessarily meromorphic):
   if the gate holds, D2 gives `f =ᶠ[𝓝[≠] x] g`; chart transport (`map_extChartAt_nhdsNE`
   applied through `Filter.EventuallyEq.filter_mono`/`eventually_map`) gives
   `f ∘ c.symm =ᶠ[𝓝[≠] (c x)] g ∘ c.symm`; conclude by `meromorphicOrderAt_congr`
   (meromorphy-free). If the gate fails: `0 = 0`. The transport lemma
   `eventuallyEq_nhdsNE_comp_chart : f =ᶠ[𝓝[≠] x] g → f ∘ c.symm =ᶠ[𝓝[≠] (c x)] g ∘ c.symm`
   is proved once in `Predicates.lean` (rewrite `𝓝[≠] (c x) = map c (𝓝[≠] x)`, then
   `eventually_map` + `c.symm (c y) = y` eventually).

### 6.5 `evalAt` / `holoRepr` (D5)

- **Definition/descent**: as in §6.4 with value
  `if (IsOpen U ∧ x ∈ U) ∧ 0 ≤ ordAtX f x then limUnder (𝓝[≠] x) f else 0`; invariance: gates
  agree by §6.4, and inside the gate `limUnder (𝓝[≠] x) f = limUnder (𝓝[≠] x) g` by
  `Filter.map_congr` on `f =ᶠ[𝓝[≠] x] g` (`limUnder l f = Filter.lim (map f l)`).
- **`tendsto_evalAt`**: `0 ≤ ordAtX f x` ⇒ chart composite has `0 ≤ meromorphicOrderAt` ⇒
  `tendsto_nhds_of_meromorphicOrderAt_nonneg` gives `c` with chart-composite → `c` along
  `𝓝[≠] (chart x)`; pull back through `map_extChartAt_nhdsNE` to `Tendsto f (𝓝[≠] x) (𝓝 c)`
  (plus the eventual identity `f = (f ∘ c.symm) ∘ c` near `x`). Then
  `limUnder = c` by `Filter.Tendsto.limUnder_eq` (`(𝓝[≠] x).NeBot` instance). Linearity
  (`evalAt_add/smul/mul`): limits of sums/products + uniqueness; `(φ+ψ).ord ≥ min ≥ 0` ensures
  the gate on the left side.
- **`holoRepr_contMDiffAt`** (the crux): fix `x ∈ U` with `0 ≤ φ.ord x`, representative `f`,
  chart `c := chartAt ℂ x`, `z₀ := c x`, `F := f ∘ c.symm`. `h := toMeromorphicNFAt F z₀` has
  `F =ᶠ[𝓝[≠] z₀] h` (`eq_nhdsNE_toMeromorphicNFAt`), `MeromorphicNFAt h z₀`
  (`meromorphicNFAt_toMeromorphicNFAt`), and `0 ≤ meromorphicOrderAt h z₀`
  (`meromorphicOrderAt_congr`), hence `AnalyticAt ℂ h z₀`
  (`meromorphicOrderAt_nonneg_iff_analyticAt`). Choose an open ball `B ∋ z₀` inside: the
  `=ᶠ`-agreement set of `F` and `h`, `h`'s analyticity set (`AnalyticAt.eventually_analyticAt`),
  and `c.target ∩ c '' (U ∩ c.source)`-side conditions. **Claim: `holoRepr φ = h ∘ c` on
  `c.symm '' B`** — for `y = c.symm w`, `w ∈ B`:
  * `w ≠ z₀`: `F = h` on `B \ {z₀}` (a nbhd of `w` minus at most `z₀` — genuinely a
    *neighborhood* of `w` after removing `z₀`, T1); so `f =ᶠ[𝓝[≠] y]` (analytic function
    `h ∘ c`), `ordAtX f y ≥ 0` (analytic order), gate holds, and
    `Tendsto f (𝓝[≠] y) (𝓝 (h w))` by continuity of `h` at `w` (values of `f` near `y` equal
    `h ∘ c` near `w` off `y` itself); `limUnder_eq` gives `evalAt φ y = h (c y)`.
  * `w = z₀`: `tendsto_evalAt` + the same computation gives `evalAt φ x = h z₀` (limit of `F`
    along `𝓝[≠] z₀` is `h z₀` by `h`'s continuity + agreement off `z₀`).
  Then `ContMDiffAt` at `x` follows from `RS.contMDiffAt_iff_analyticAt` (Surface) since
  `holoRepr φ ∘ c.symm = h` near `z₀` (`AnalyticAt.congr` on the neighborhood `B`).
- **`mk_holoRepr`** (`⟦holoRepr φ⟧ = φ`): `MeromorphicOnX (holoRepr φ) U`: at `x ∈ U` with
  `ord ≥ 0` it is `ContMDiffAt` (above) hence meromorphic; at `ord < 0` (pole) it agrees with
  `f` on `𝓝[≠] x` — because eventually near `x` (punctured) the points `y` have `ordAtX f y = 0`
  and `f` chart-analytic there (`eventually_ordAtX_eq_zero` + its analyticity payload), so
  `evalAt φ y = f y` (honest-value lemma `evalAt_mk_of_contMDiffAt` applied at `y`; the chart
  used there is at `y` but the value claim is chart-free) — then `MeromorphicAtX.congr`.
  Germ equality: `{y ∈ U | holoRepr φ y = f y}` contains the codiscrete-within-`U` set where
  `f` is chart-analytic (`MeromorphicOnX.analyticAt_codiscreteWithin`, §4.2) intersected with
  gate conditions ⇒ `holoRepr φ =ᶠ[codiscreteWithin U] f` ⇒ `mk … = mk f … = φ`.
- **`tendsto_holoRepr_cobounded_iff`**: `holoRepr φ =ᶠ[𝓝[≠] x] f` (previous point, both
  cases) + `tendsto_cobounded_iff_ordAtX_neg`.

### 6.6 The relative layer: restriction and gluing

- `restrict (h : V ⊆ U)`: on germs, `Germ.compTendsto`-style along
  `codiscreteWithin V ≤ codiscreteWithin U` (`codiscreteWithin_mono h`, `@[gcongr]`); concretely
  define by `liftOn`/`ofFun`: `restrict h (mk f hf) := mk f (hf restricted)`, well-defined since
  `=ᶠ[codiscreteWithin U] ⇒ =ᶠ[codiscreteWithin V]` (`EventuallyEq.filter_mono`). Bundle as
  `AlgHom` (all ops commute with `mk`, `restrict_mk` is `rfl`-adjacent). Presheaf laws
  `restrict_restrict`, `restrict_id` by `ind` + `rfl`.
- `ord_restrict` / `evalAt_restrict`: same representative on both sides; the gates agree
  (`x ∈ V ⊆ U`, both open); values are chart-local, identical. **This pointwise rigidity is
  exactly why `holoRepr` glues.**
- `exists_glue`: define `F : X → ℂ` by `F x := (φ (choice i with x ∈ U i)).holoRepr x` for
  `x ∈ ⋃ U i` (junk 0 outside; use `Classical` index choice). Well-defined independent of the
  choice: for `x ∈ U i ∩ U j`, `evalAt (φ i) x = evalAt (restrict … (φ i)) x =
  evalAt (restrict … (φ j)) x = evalAt (φ j) x` by `hcompat` + `evalAt_restrict`. So
  `F = (φ i).holoRepr` **pointwise on `U i`** for every `i`. Then: `MeromorphicOnX F (⋃ U i)`
  (at `x ∈ U i`, `F` agrees with `(φ i).holoRepr` on the open `U i`, which is meromorphic by
  §6.5); `Φ := mk F …`; `restrict … Φ = φ i` since `F =ᶠ[codiscreteWithin (U i)] (φ i).holoRepr`
  — actually *equal on* `U i` — and `mk_holoRepr`. Uniqueness (`glue_unique`): from
  `restrict`-injectivity on covers: representatives agree `=ᶠ[codiscreteWithin (U i)]` for each
  `i`; the union of codiscrete-within-`U i` agreement sets is codiscrete within `⋃ U i` by the
  D2 bridge (pointwise: every `x ∈ ⋃ U i` lies in some `U i`, agreement ∈ `𝓝[≠] x`).

*(The sixth hard item, `L(D)`, is spread over D4/§4.7; its only nontrivial steps are
`linSys_zero_eq_span_one` and `linSysMulEquiv`:)*

### 6.7 `L(0) = ℂ·1`, vanishing lemmas, `linSysMulEquiv`

- `linSys_zero_eq_span_one` (`[T2] [CompactSpace] [ConnectedSpace]`): `⊇` from
  `ord_algebraMap ≥ 0`. `⊆`: `φ ∈ LinSys 0` ⇒ `∀ x, 0 ≤ φ.ord x` ⇒
  `ContMDiff … φ.holoRepr` (§6.5, `U = univ`) ⇒ `MDifferentiable` (`ContMDiff.mdifferentiable
  (le_top)`, `ω`-instance downgrade) ⇒ `∃ c, φ.holoRepr = fun _ => c`
  (`MDifferentiable.exists_eq_const_of_compactSpace`, spiked) ⇒
  `φ = mk (const c) = c • 1 ∈ span {1}` via `mk_holoRepr`. `l_zero`: `finrank_span_singleton`
  with `(1 : ℳ X) ≠ 0` (`Nontrivial`, `[Nonempty X]` from `ConnectedSpace`).
- `linSys_eq_bot_of_nonpos_of_ne_zero`: `φ ∈ LinSys D`, `φ ≠ 0`; `D ≤ 0` ⇒ `0 ≤ -D ≤ ord`
  everywhere ⇒ (as above) `φ = algebraMap c`, `c ≠ 0`; but at `x₀` with `D x₀ < 0`,
  `1 ≤ -(D x₀) ≤ ord φ x₀ = 0` (`ord_algebraMap`, `c ≠ 0`) — contradiction. **No degree theory
  used** (identity theorem/constancy only), as the task requires.
- `linSys_eq_bot_of_degree_neg` (conditional): `φ ≠ 0` in `LinSys D` ⇒ `-D ≤ divisor φ` ⇒
  `degree_mono`: `-D.degree = (-D).degree ≤ (divisor φ).degree = 0` (hypothesis) ⇒
  `0 ≤ D.degree`, contradicting `h`.
- `linSysMulEquiv`: forward map `ψ ↦ ⟨φ * ψ, …⟩`; carrier check pointwise:
  `(φ*ψ).ord x = φ.ord x + ψ.ord x ≥ divisor φ x - D x = -(D x - divisor φ x)` using
  `ord_mul` and `φ.ord x = divisor φ x` (no `⊤`, `Mero.ord_ne_top`; if `ψ.ord x = ⊤` the sum
  is `⊤`, trivial). Inverse map multiplies by `φ⁻¹` (`ord_inv`); `left_inv`/`right_inv` by
  field algebra (`φ⁻¹ * (φ * ψ) = ψ` via `mul_inv_cancel`); linearity: `mul_add`, `mul_smul_comm`
  on the ring `ℳ X`. Degree bookkeeping for later units: with `deg ∘ divisor = 0` this gives
  `l(D)` invariance under linear equivalence — statement left to riemann-roch.

---

## 7. What this unit does NOT do (deferred, with owners)

- **`deg (divisor φ) = 0`** — proper-map-degree (argument principle / degree counting; the
  blueprint explicitly warns off the Stokes route). We ship the conditional consumer lemma
  `linSys_eq_bot_of_degree_neg` (§4.7) so no redesign is needed there.
- **Finiteness of `l(D)`** — cech-cohomology/finiteness-and-chi. Nothing here assumes or fakes
  `FiniteDimensional`.
- **Existence of a nonconstant meromorphic function** — canonical-forms (a consequence of
  finiteness + χ, per blueprint). `ℳ X`'s field structure here does NOT need it.
- **`X → ℙ¹` bridge** — projective-line; its inputs are exported: `holoRepr` +
  `tendsto_holoRepr_cobounded_iff` (pole ⇒ →∞), `continuousAt_holoRepr`,
  `finite_setOf_ord_neg`, `eventually_ord_eq_zero`, and `holoRepr(φ⁻¹) =ᶠ[𝓝[≠]x] (holoRepr φ)⁻¹`
  falls out of `holoRepr_eventuallyEq_nhdsNE` + `mk_inv` at any pole (documented, not a named
  export).
- **Laurent coefficients / principal parts** — laurent-tails (mathlib's
  `meromorphicTrailingCoeffAt`, `Analysis/Meromorphic/TrailingCoefficient.lean:36`, is the
  recommended seed; noted for that designer).
- **Čech complexes/refinements** — cech-cohomology; this unit hands over `MeroGermOn`,
  `restrict`, `ord/evalAt/holoRepr` rigidity, `exists_glue`/`glue_unique`, `LinSysOn`,
  `mem_linSys_iff_forall_restrict` (`H⁰ = L(D)` becomes bookkeeping).

## 8. Spike record

`scratch_merodesign.lean` (project root, gitignored `scratch_*`), **80 lines**, run
`lake env lean scratch_merodesign.lean`: **success, 7.7 s wall** (first attempt modulo three
missing `noncomputable` keywords on `example`s — no name or proof failures). Verified by
compilation:
(1) `Algebra ℂ (Filter.Germ l ℂ)` via `Algebra.ofModule` + `Germ.inductionOn₂` +
`Germ.coe_smul/coe_mul` + `smul_mul_assoc`/`mul_smul_comm` — the exact instance text to reuse;
(2) `Subalgebra ℂ (Germ l ℂ)` subtype inherits `CommRing`/`Algebra ℂ`/`Module ℂ` by
`inferInstance`;
(3) `Germ.coe_eq`, `Germ.coe_inv`, `Germ.liftOn`;
(4) the D2 bridge, both directions, from `mem_codiscreteWithin_iff_forall_mem_nhdsNE`
(proof text in the spike file — reuse verbatim);
(5) `Function.locallyFinsuppWithin.finiteSupport` + `isCompact_univ` + `Set.Finite.toFinset`
degree definition; `le_def`; `Function.locallyFinsupp.single`;
(6) `MeromorphicAt.eq_nhdsNE_toMeromorphicNFAt`, `meromorphicNFAt_toMeromorphicNFAt`,
`MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt`,
`tendsto_nhds_iff_meromorphicOrderAt_nonneg`, `Filter.Tendsto.limUnder_eq`;
(7) `meromorphicAt_comp_iff_of_deriv_ne_zero`, `meromorphicOrderAt_comp_of_deriv_ne_zero`;
(8) `MDifferentiable.exists_eq_const_of_compactSpace` with `[IsManifold 𝓘(ℂ) 1 M]`.

## 9. Risks & fallbacks

1. **`Field` structure assembly** (low-med): default fields (`qsmul`, `ratCast`, …) may demand
   explicit values. Fallback: copy the `RatFunc.instField` pattern; last resort
   `IsField.toField` for the *existence* plus a separate `@[simp] mk_inv` API keeping our
   pointwise `Inv` as the `Inv` instance (define `Inv` first, `Field` with `inv := Inv.inv`).
2. **Type-synonym friction** (`MeroGermOn` as `def`) (low): dot notation works off the head
   constant, but `φ.1`/coercions may need helper `toGerm`. Fallback: make `MeroGermOn` an
   `abbrev` and accept `Subtype`-namespace ergonomics (call lemmas by full name).
3. **Gate-style definitions** (`if IsOpen U ∧ x ∈ U`) (low): classical `Decidable` for the
   `if` via `Classical.dec` — standard `open Classical in` or `if h : _` with
   `Classical.propDecidable`; all simp lemmas conditioned on `(hU) (hx)` so the gate never
   leaks. Fallback: parametrize the relative layer by `TopologicalSpace.Opens X`.
4. **Chart-transport boilerplate** (med): `𝓝[≠]`-transport (`map_extChartAt_nhdsNE`) and the
   `=ᶠ` bookkeeping between `f ∘ c.symm` composites recur in ~10 proofs. Mitigation: prove the
   two transport lemmas (`eventuallyEq_nhdsNE_comp_chart`, `tendsto_comp_chart_iff`) once in
   `Predicates.lean` and never inline them. This is the main grind risk, not a correctness risk.
5. **`holoRepr` neighborhood bookkeeping** (§6.5, med): the "`B` small enough for four
   conditions" step is fiddly (`Metric.nhds_basis_ball` + `Filter.eventually` conjunction).
   Fallback if the pointwise-limit route stalls: chart-local `toMeromorphicNFOn` repair glued
   with `evalAt`-uniqueness only at overlap points (weaker rigidity, same exports) — but the
   spike-verified atoms make the primary route concrete.
6. **`exists_glue` choice bookkeeping** (low-med): the index-choice function is discharged by
   the pointwise well-definedness; if `Classical.choice` plumbing gets ugly, state gluing for
   pairwise covers first (`U V`, the only case Čech's `H⁰` argument strictly needs for
   equalizer form) and iterate.
7. **Performance**: files are small; the only heavy imports are `Analysis.Meromorphic.*` (also
   used by LocalMultiplicity — cache warm). No `Mathlib` monolith imports.
8. **CC-conformance flags** (for the orchestrator, per core-choices' stop-and-report rule —
   these are *realizations*, not re-choices): (a) `ℳ X` as meromorphic-subalgebra-of-`Germ`
   rather than literal `Quotient` of the subtype — same quotient, D1; (b) `L(D)` carrier as
   `ord`-inequality with the frozen disjunction as `mem_linSys_iff_eq_zero_or_le_divisor` — D4;
   (c) renames `div ↦ divisor`, `Divisor.deg ↦ Function.locallyFinsuppWithin.degree`,
   `MeromorphicOnX` relativized (global = `… univ`). All downstream-facing statements keep
   CC2/CC3 semantics exactly.

## 10. Downstream contract map

- **cech-cohomology** (primary): `MeroGermOn U`, `restrict` (AlgHom + presheaf laws),
  `LinSysOn D U`, `restrict_mem_linSysOn`, `ord_restrict`/`evalAt_restrict` (rigidified normal
  form!), `exists_glue`/`glue_unique`, `mem_linSys_iff_forall_restrict` ⇒ `H⁰(𝔘, O_D) ≅ L(D)`
  definitionally-easily (CC8). Germ cochains = tuples in `MeroGermOn (U i ∩ U j)` — the type
  is ready; no new quotient design needed.
- **riemann-roch / laurent-tails**: `LinSys`, `l`, `linSys_mono`, `linSysMulEquiv`, `degree`
  (+ algebra), `divisor` (+ algebra), `l_zero`, vanishing lemmas, the conditional
  `linSys_eq_bot_of_degree_neg`; Laurent-tail truncations build on `ordAtX` +
  `meromorphicOrderAt_eq_int_iff` factorizations exported through `ordAtX_eq_of_mem_source`.
- **genus-zero-headline**: `holoRepr_contMDiff` + `mk_holoRepr` (a germ-only `toFun` is not
  `ContMDiff` — this is precisely the exported repair), pole data
  `tendsto_holoRepr_cobounded_iff`.
- **projective-line**: pole/zero exports listed in §7; `Field (ℳ X)` for `1/f`.
- **proper-map-degree**: `divisor`, `degree`, `finite_setOf_ord_neg/pos`,
  `eventually_ord_eq_zero`; owes us `deg ∘ divisor = 0` (consumed via the conditional lemma).
- **canonical-forms** (later): `ℳ X` field, `divisor_mul/inv`, `ordAtX` calculus; nonconstant
  existence is theirs.
