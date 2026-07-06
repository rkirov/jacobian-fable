# Design: serre-duality-cech (`Jacobian/SerrePairing/`)

Blueprint unit **serre-duality-cech**. Blueprint text: "The Serre pairing at the Čech level: the
**dimension-counting surjectivity core** and the duality bookkeeping consumed by the tail route.
Strategy: this is the interface that the Laurent-tail unit discharges concretely; keep it a clean
dimension statement." **Builds on:** canonical-forms. References: Forster §16–§17 (PDF 132–144);
Miranda Ch. VI §3 (PDF 198–204, Serre Duality Thm 3.3 PDF 200, Lemma 3.4 PDF 201, Lemma 3.6 +
surjectivity PDF 202–203).

One gated end spike (`scratch_serrec.lean`, project root) compiled clean — §8.

---

## 0. Division of labor (read first)

### 0.1 What Forster §17 and Miranda VI.3 actually prove, audited page-by-page

**Forster's route** (17.1–17.9, PDF 138–144): `Res : H¹(X,Ω) → ℂ` is *defined by integration* —
`Res(ξ) := (1/2πi) ∬_X τ` for a representative 2-form `τ` via the isomorphism `H¹(X,Ω) ≅
𝓔^{(2)}(X)/d𝓔^{1,0}(X)` (15.14, itself Dolbeault's theorem). Well-definedness against Mittag-Leffler
presentations (`Res(μ) = Res([δμ])`, Thm 17.3) is proved by an honest Stokes/partition-of-unity
argument (excising disks around the finitely many poles, PDF 139, exactly the shape residue-theorem
builds). The dual pairing `⟨ω,ξ⟩ := Res(ωξ)` (17.5) is then a *composite* of (a) the sheaf-level
multiplication `Ω_{-D} × O_D → Ω` (order-additivity, cheap) with (b) this analytic `Res`. Injectivity
(17.6) is a five-line local computation. **Surjectivity (17.9) is the hard fifteen-page argument**
(17.7 dualizes inclusions, 17.8 dualizes multiplication, Lemma 17.5-bis bounds `dim H⁰(Ω_D) ≥ deg D +
k₀`, and 17.9 itself is a dimension-counting argument on growing divisors `D_n := D − nP`).

**Miranda's route** (VI.3, PDF 186–191) is a *different presentation of the same theorem*, built
around the concrete Laurent-tail space `T[D](X)` instead of the abstract `H¹(X,Ω)`. Her `Res_ω :
T[D](X) → ℂ`, `Res_ω(Σ r_p·p) := Σ_p Res_p(r_p ω)`, is **purely algebraic** — no integration, no
2-form representative, just a finite sum of planar residues (PDF 187, boxed formula). Well-
definedness (that `Res_ω` vanishes on `α_D(ℳ(X))`, i.e. descends to `H¹(D) := T[D](X)/α_D(ℳ(X))`)
reduces to **the residue theorem** `Σ_p Res_p(fω) = 0` applied to the *global* meromorphic form
`fω` (PDF 186, eq. (3.2)) — Stokes-free from her point of view, because the Stokes work was already
spent once, earlier, proving the residue theorem itself (a *different*, already-established fact,
not re-derived here). Injectivity (Thm 3.3's proof, PDF 188) is the SAME five-line local computation
as Forster's, just phrased against a Laurent tail instead of a cohomology class. Surjectivity (Lemma
3.4 + Lemma 3.6 + the final assembly, PDF 189–191) is again the hard part — genuinely isomorphic in
difficulty to Forster's 17.7–17.9, just re-packaged: Lemma 3.4 is her analogue of 17.7/17.8
(functionals on `H¹(D)` for growing `D` "eventually agree after pulling back far enough" — needs
Riemann's inequality on *both* a fixed divisor and a growing positive divisor `C`, an honest
dimension-count in the limit), Lemma 3.6 is the "order downgrade" (if a functional's kernel condition
degrades from `D₁` to `D₂ ≥ D₁`, the witness `ω` was already in the smaller space) that closes the
induction.

**The blueprint's routing decision (⚠ in the residue-theorem entry) is exactly this dichotomy**:
"the residue **theorem** (`ΣRes=0`) is genuinely Stokes-only and genus-agnostic. The residue
**functional** `H¹(Ω)→ℂ` of Serre duality is a *different* object that *does* need an integration
atom — the 'Stokes-free' shortcut to it is circular." Forster's `Res` (17.1) *is* that integration-
needing functional; Miranda's `Res_ω` is not — it is built from the ALREADY-PROVED residue theorem's
*output* (a single equation `Σ Res = 0`), never from ∬. **Route (b) — Miranda's tail-level pairing —
is confirmed as the only route consistent with the blueprint's "no residue functional via
integration" hazard, and is adopted throughout this design.**

### 0.2 The actual division of labor between this unit and #26

Both routes' surjectivity halves are genuinely hard (a multi-lemma dimension-counting induction on
growing divisors) and are **not attempted here** — that is squarely serre-duality-tails' (#26) job,
per the blueprint's own "make-or-break" framing and its `⚠ this is *the* key routing decision`. What
THIS unit owns, matching "keep it a clean dimension statement":

1. **The pairing formula itself** (Miranda's `Res_ω`, §2 D2) — purely algebraic, built from
   already-BUILT residue-calculus atoms (`resAt_tail_mul`), zero new analytic content.
2. **The injectivity core** (Miranda's Thm 3.3 injectivity half / Forster's 17.6) — a five-line
   local computation, fully proved here (§2 D4, §5 P1).
3. **A generic "clean dimension inequality" interface theorem** (§2 D5, §5 P2) that #26
   instantiates: *given* (a) laurent-tails' comparison of our tail space with the actual `H¹(D)`
   and (b) residue-theorem's well-definedness input, the inequality `i(−D) ≤ h¹(D)` (equivalently
   `l(K−D) ≤ h¹(D)`) follows by pure linear algebra, proved here once and for all.
4. **The frozen target statement** #26 must fully discharge (§2 D6) to close Serre duality:
   `i(−D) = h¹(D)`, i.e. `l(K−D) = h¹(D)`.

Items 1–3 are proved with zero sorries in this design's file plan; item 4 is stated, not proved,
here — it is #26's deliverable, recorded so #27 (`riemann-roch`)/#26's own downstream (`cech-h1-
genus`) can freeze their own statements against it now.

---

## 1. Facts relied on (verified against files on disk / design docs)

### 1.1 `docs/design/canonical-forms.md` (design frozen, build IN FLIGHT — not yet on disk;
`Jacobian/CanonicalForms/` does not exist yet at design time, checked)

Exact signatures we consume (their own §9 downstream map names us directly: *"serre-duality-cech
(Builds on: canonical-forms): `MForm.OmegaSpace`/`i D` (D11, ...), `canonicalDivisorOf`/
`canonicalDivisorOf_linearEquiv` (D10, ...), `MLFormData`/`totalRes` (D13, ...)"*):

```lean
structure MForm (X) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] where
  coeffAt : X → ℂ → ℂ
  coeffAt_zero_off : ∀ x, ∀ z ∉ (chartAt ℂ x).target, coeffAt x z = 0
  meromorphicOn_coeffAt : ∀ x, MeromorphicOn (coeffAt x) (chartAt ℂ x).target
  compat : ...
noncomputable def MForm.ord (ω : MForm X) (x : X) : WithTop ℤ
noncomputable def MForm.resAt (ω : MForm X) (x : X) : ℂ
noncomputable def MForm.divisor [T2Space X] [CompactSpace X] (ω : MForm X) : Divisor X
@[simp] theorem MForm.divisor_apply [T2Space X] [CompactSpace X] (ω) (x) :
    ω.divisor x = (ω.ord x).untop₀
theorem MForm.eq_zero_or_forall_ord_ne_top [T1Space X] [ConnectedSpace X] (ω : MForm X) :
    ω = 0 ∨ ∀ x, ω.ord x ≠ ⊤                                                          -- D5

def MForm.OmegaSpace [T2Space X] [CompactSpace X] (D : Divisor X) : Submodule ℂ (MForm X)
theorem mem_omegaSpace_iff [T2Space X] [CompactSpace X] {ω : MForm X} {D : Divisor X} :
    ω ∈ MForm.OmegaSpace D ↔ ω = 0 ∨ -D ≤ ω.divisor
noncomputable def i [T2Space X] [CompactSpace X] (D : Divisor X) : ℕ :=
  Module.finrank ℂ (MForm.OmegaSpace D)

noncomputable abbrev canonicalDivisorOf [T2Space X] [CompactSpace X] (ω₀ : MForm X) : Divisor X
theorem canonicalDivisorOf_linearEquiv [T1Space X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    {ω₀ ω₀' : MForm X} (h₀ : ω₀ ≠ 0) (h₀' : ω₀' ≠ 0) :
    ∃ f : ℳ X, f ≠ 0 ∧ canonicalDivisorOf ω₀' = canonicalDivisorOf ω₀ + divisor f

theorem Ω_iso_linSys [T1Space X] [T2Space X] [CompactSpace X] [ConnectedSpace X] {ω₀ : MForm X}
    (h₀ : ω₀ ≠ 0) (D : Divisor X) : MForm.OmegaSpace D ≃ₗ[ℂ] LinSys (D + canonicalDivisorOf ω₀)
theorem i_eq_l_add_canonicalDivisorOf [...] {ω₀} (h₀) (D) : i D = l (D + canonicalDivisorOf ω₀)
```

`MForm.OmegaSpace D` is Forster's `Ω_D` (order `≥ -D` everywhere); we use it at `D := -D'` for a
fixed divisor `D'` throughout (Forster's `Ω_{-D'}`, Miranda's `L^{(1)}(-D')`), giving `ω.divisor ≥
D'` — **sign convention pinned once here, §2 D4's proof is the one place it is used.**

`MLFormData`/`totalRes` (D13) exist in their design but with **no `AddCommGroup`/`Module ℂ`
instance** (their own doc: "we do not anticipate the pairing statement itself... flagged
non-blocking"). We do **not** reuse `MLFormData` directly (§0.3 below explains why) but build our
own tail type mirroring the *residue-calculus* pattern instead (§1.2) — filed as a coordination
note, not a correction (`docs/requests/laurent-tails.md`).

### 1.2 `Jacobian/ResidueCalculus/` (BUILT, zero sorries — verified at source)

- `RS.resAt (f : ℂ → ℂ) (z₀ : ℂ) : ℂ := laurentCoeffAt f z₀ (-1)` (`Residue.lean:37`).
- `RS.resAt_tail_mul {c : ℤ → ℂ} {s : Finset ℤ} (hg : MeromorphicAt g z₀) : resAt (fun z =>
  (∑ k ∈ s, c k * (z-z₀)^k) * g z) z₀ = ∑ k ∈ s, c k * laurentCoeffAt g z₀ (-1-k)`
  (`Residue.lean:199` — **THE pairing atom**, docstring already flags it "Serre-pairing atom,
  tail form (Miranda VI.3 eq. shape `Σ c_n a_{−1−n}`)").
- `RS.resAt_zpow_mul (hg : MeromorphicAt g z₀) (m : ℤ) : resAt (fun z => (z-z₀)^m * g z) z₀ =
  laurentCoeffAt g z₀ (-1-m)` (`Residue.lean:193`) — the single-term specialization, **spike-
  verified** (§8) as the injectivity witness's computation.
- `RS.resAt_const_mul`, `RS.resAt_fun_add`, `RS.resAt_fun_sum` — the linearity kit (all built),
  used for `pair`'s bilinearity.
- `RS.laurentCoeffAt_order_ne_zero (hf : MeromorphicAt f z₀) (h : meromorphicOrderAt f z₀ ≠ ⊤) :
  laurentCoeffAt f z₀ (meromorphicOrderAt f z₀).untop₀ ≠ 0` (`LaurentCoeff.lean:176`) — **the
  "leading coefficient is nonzero" atom**, spike-verified (§8), the other half of the injectivity
  witness's computation.
- `RS.resAt_of_order_nonneg`/`RS.resAt_of_analyticAt` — vanishing off the pole locus (exports list,
  `Residue.lean:20`) — the atom the *well-definedness* derivation for #26 needs (not proved by us,
  see `docs/requests/residue-theorem.md`).
- `RS.PrincipalPartData`/`mlCoeff`/`ofMeromorphicOn` (`MittagLeffler.lean`, semi-frozen) — the
  planar Mittag-Leffler vocabulary our `Tail X` (§2 D1) mirrors at the `X`-indexed level (dropping
  the planar-`U`-membership condition, since our points already range over all of `X`).

### 1.3 `Jacobian/Cech/` (BUILT, zero sorries where noted — verified at source)

- `RS.Cech.H1 D : Type _ := Module.DirectLimit ...` (`Colimit.lean:64`, **CC8-frozen**: the
  official, definitional `H¹(D)` of the whole project).
- `RS.Cech.toH1`, `RS.Cech.exists_rep`/`exists_rep_good` (`Colimit.lean`).
- `RS.Cech.mlClass (𝒰) (g : C0 D' 𝒰) (hg : (d0 D' 𝒰 g).MemLD D) : H1 D` (`Skyscraper.lean:65`) —
  **the Mittag-Leffler realization atom**, docstring: *"Both the χ connecting map
  (finiteness-and-chi) and laurent-tails' `T[D] → H¹(D)` factor through this."* We do not consume
  it directly (out of our DAG scope, no `Builds on: cech-cohomology` edge for this unit) but it is
  the concrete reason laurent-tails' comparison map (needed by #26, `docs/requests/laurent-tails.md`
  item 3) is a bounded-risk build, not a from-scratch one.
- We do **not** otherwise touch `Jacobian/Cech/` — our `Builds on:` edge is `canonical-forms` only,
  and nothing in this design needs a cover, a cochain, or a cocycle.

### 1.4 `docs/design/finiteness-and-chi.md` (design frozen, `Jacobian/Finiteness/` partially BUILT)

```lean
noncomputable def h1 (D : Divisor X) : ℕ := Module.finrank ℂ (RS.Cech.H1 D)             -- Chi.lean
instance finiteDimensional_H1 [T2Space X] [CompactSpace X] (D) : FiniteDimensional ℂ (RS.Cech.H1 D)
noncomputable def chi [ConnectedSpace X] (D : Divisor X) : ℤ := (l D : ℤ) - (h1 D : ℤ)
```
`h1 D` is a bare `ℕ` (their own §4.7), but its DEFINITION is literally `finrank (H1 D)` — so the
underlying finite-dimensional space `RS.Cech.H1 D` genuinely exists and is what #26's `toH` (§2 D5)
must ultimately target. `FiniteDimensional ℂ (H1 D)` (their `finiteDimensional_H1`, gated on cech's
Skyscraper fragment landing, "frozen shape regardless of gate status" per their own §1.5-style
commitment) is the hypothesis our generic theorem (§2 D5) needs on the target space.

### 1.5 A genuine gap noted, not fixed here: `MLFormData` has no module structure (§0.3)

`docs/design/canonical-forms.md` D13 defines `MLFormData X` as a bare structure (`pts : Finset X`,
`data : ∀ x ∈ pts, PrincipalPartData (chartAt ℂ x).target`) with **no** `AddCommGroup`/`Module ℂ`
instance — adding one is nontrivial precisely because two `MLFormData` values can have *different*
`pts` finsets, so `+` needs a union-and-pad construction canonical-forms did not build (their own
doc flags this content as "non-blocking... no current unit is DAG-required to consume it"). A
genuinely bilinear Serre pairing needs an honest `Module ℂ` structure on its second argument, so we
build our own tail type instead (§2 D1) rather than wait on or extend `MLFormData`. This is filed as
a coordination note (`docs/requests/laurent-tails.md`), not a request to canonical-forms — nothing
currently DAG-requires `MLFormData` itself to gain this structure, and our own `Tail X` (§2 D1) is a
free `Finsupp`-based construction with zero proof debt, so there is no need to block on it.

---

## 2. Core definitional decisions

### D1 — `Tail X`: a free `Finsupp`-of-`Finsupp`s, no hand-rolled submodule proof

```lean
namespace RS.SerrePairing

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

open scoped Classical in
/-- Miranda VI.3's *ambient* Laurent-tail space, before any `D`-bound: at finitely many points of
`X`, an arbitrary finite tail of Laurent coefficients (any integer exponents — see the ⚠ below for
why we do NOT restrict to negative exponents here), read in each point's own `chartAt` (no
compatibility/transition data needed: the pairing (`D2`) never crosses charts, exactly as
`MForm.ord`/`resAt` themselves need none, `canonical-forms.md` D4). -/
def Tail (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Type _ :=
  X →₀ (ℤ →₀ ℂ)

noncomputable instance : AddCommGroup (Tail X) := inferInstanceAs (AddCommGroup (X →₀ (ℤ →₀ ℂ)))
noncomputable instance : Module ℂ (Tail X) := inferInstanceAs (Module ℂ (X →₀ (ℤ →₀ ℂ)))

/-- Miranda's `T[D](X)`: tails whose exponent at each point is bounded by `D` (pole order at
`x` at most `D x`; exponent range is `< -(D x)`, matching her convention exactly — for `D = 0`
this is "only negative exponents", her own base case). -/
def Tail.BoundedBy (τ : Tail X) (D : RS.Divisor X) : Prop :=
  ∀ x ∈ τ.support, ∀ k ∈ (τ x).support, k < -(D x)

def TailSpace (D : RS.Divisor X) : Submodule ℂ (Tail X) where
  carrier := {τ | τ.BoundedBy D}
  zero_mem' := fun x hx => absurd hx (by simp)
  add_mem' {τ σ} hτ hσ x hx k hk := ...     -- via `Finsupp.support_add` twice, §5 P0
  smul_mem' c τ hτ x hx k hk := ...          -- via `Finsupp.support_smul_eq`/`smul_ne_zero`, §5 P0

noncomputable def Tail.single (p : X) (n : ℤ) (c : ℂ) : Tail X :=
  Finsupp.single p (Finsupp.single n c)

theorem Tail.single_boundedBy {p : X} {n : ℤ} {c : ℂ} {D : RS.Divisor X}
    (h : c ≠ 0 → n < -(D p)) : (Tail.single p n c).BoundedBy D

end RS.SerrePairing
```

**⚠ Why `Tail X` must NOT hard-code "negative exponents only"** (a mistake caught and corrected
during this design, not left implicit): if `D x < 0` at some point (`O_D` forces a zero of order
`≥ -D(x) > 0` there), Miranda's bound `k < -(D x)` allows some *non-negative* exponents into
`T[D](X)` too (the "obstruction data" then includes part of the regular Taylor expansion, not just
the pole). Mirroring residue-calculus's `principalPartCarrier` verbatim (which *does* hard-code
`k < 0` globally, correctly, since `PrincipalPartData` is always used at the fixed bound `D = 0`
there) would silently make `TailSpace D` empty-or-wrong for divisors with a negative value anywhere.
`Tail X` therefore imposes **no** exponent condition at all (finite support only, entirely free via
`Finsupp`); `Tail.BoundedBy`/`TailSpace D` is the *only* place any bound enters, parameterized by `D`
as it must be.

### D2 — `pair`: the Serre pairing (Miranda's `Res_ω`), purely algebraic

```lean
variable [T2Space X] [CompactSpace X]   -- for `ω.coeffAt`'s meromorphy at the chart center to make
                                        -- sense uniformly; MForm itself needs none of these, but
                                        -- see D4/D5 where they really bite

noncomputable def pair (ω : MForm X) (τ : Tail X) : ℂ :=
  ∑ᶠ x, RS.resAt (fun z => (∑ k ∈ (τ x).support, τ x k * (z - chartAt ℂ x x) ^ k) * ω.coeffAt x z)
    (chartAt ℂ x x)

/-- The computed form (Miranda's boxed formula, PDF 187): `Σ_p Res_p(r_p ω) = Σ_p Σ_n c_n
a_{-1-n}`. -/
theorem pair_eq_finsum_sum (ω : MForm X) (τ : Tail X) :
    pair ω τ = ∑ᶠ x, ∑ k ∈ (τ x).support, τ x k * laurentCoeffAt (ω.coeffAt x) (chartAt ℂ x x) (-1-k)
    -- pointwise via `resAt_tail_mul`, then `finsum_congr`; §5 P0

theorem pair_add_left (ω ω' : MForm X) (τ : Tail X) : pair (ω+ω') τ = pair ω τ + pair ω' τ
theorem pair_smul_left (c : ℂ) (ω : MForm X) (τ : Tail X) : pair (c•ω) τ = c * pair ω τ
theorem pair_add_right (ω : MForm X) (τ σ : Tail X) : pair ω (τ+σ) = pair ω τ + pair ω σ
theorem pair_smul_right (ω : MForm X) (c : ℂ) (τ : Tail X) : pair ω (c•τ) = c * pair ω τ

theorem pair_single (ω : MForm X) (p : X) (n : ℤ) (c : ℂ) :
    pair ω (Tail.single p n c) = c * laurentCoeffAt (ω.coeffAt p) (chartAt ℂ p p) (-1-n)
```

`pair_add_right`/`pair_smul_right` are genuinely bilinear-algebra bookkeeping (extending each
finsum to the union of the two supports, terms outside a tail's own support contributing `0` — the
one place `Tail X`'s "free `Finsupp`" choice pays for itself: `finsum_add_distrib`/
`finsum_smul_distrib` handle this without any hand-rolled `Finset` gymnastics). `pair_single`
is the atom the injectivity witness (D4) uses directly, **spike-verified in full** (§8): its proof
is `resAt_const_mul` (pull `c` out) then `resAt_zpow_mul` (the single-term case of `resAt_tail_mul`,
with the finsum trivially collapsing to the one point `p` via `finsum_mem_singleton`-style support
reasoning since `Tail.single p n c`'s support is `⊆ {p}`).

### D3 — Miranda's dual pairing lives on `MForm.OmegaSpace (-D) × TailSpace D`

Sign convention pinned once (§1.1): `ω ∈ OmegaSpace (-D) ↔ ω = 0 ∨ D ≤ ω.divisor` is Forster's
`Ω_{-D}`/Miranda's `L^{(1)}(-D)`; pairing it against `τ ∈ TailSpace D` (order bound `-D`, matching
`O_D`) is exactly the order-additivity `ω·(\text{tail}) ` has order `≥ D(x) + (-D(x)-1+1)=` ... i.e.
the classical "multiply a `≥D`-order form by a `<-D`-exponent tail and you may pick up a nonzero
residue" setup — no separate lemma needed here (D2's `pair` is defined for *any* `ω : MForm X`,
`τ : Tail X`; the restriction to `OmegaSpace(-D) × TailSpace D` only matters for D4/D5's theorems,
not for `pair`'s own definition, mirroring how `MForm.resAt` itself is defined divisor-free and only
becomes meaningful once restricted, `canonical-forms.md` D4).

### D4 — The injectivity core (Miranda Thm 3.3's injectivity half / Forster 17.6)

```lean
variable [T1Space X] [ConnectedSpace X]

/-- Miranda's injectivity argument (PDF 188), stripped to its purely local content: a nonzero
`ω ∈ Ω(-D)` pairs nontrivially against SOME `D`-bounded tail — pick the point `p` where `ω` has
order `k := ord_p(ω)` (finite and `≥ D(p)`, since `ω ≠ 0`/`ω ∈ Ω(-D)`), pair against the one-term
tail `(z-z_p)^{-1-k}` there: the residue IS the leading Laurent coefficient, nonzero by definition
of order. "Cheap and local", exactly as the task brief anticipates. -/
theorem exists_tail_pair_ne_zero {D : RS.Divisor X} {ω : MForm X}
    (hω : ω ∈ MForm.OmegaSpace (-D)) (hω0 : ω ≠ 0) :
    ∃ τ : Tail X, τ.BoundedBy D ∧ pair ω τ ≠ 0
```

**This is the entire mathematical content of "the pairing map is injective" prior to any
well-definedness/quotient bookkeeping** — see §5 P1 for why this is *exactly* equivalent to
injectivity of the descended map on `H¹(D)`'s dual, once well-definedness (owned by #26 via
residue-theorem) is separately known.

### D5 — The generic "clean dimension inequality" interface theorem

```lean
/-- The interface #26 (serre-duality-tails) discharges. Given ANY finite-dimensional target `H`
(in practice `RS.Cech.H1 D`) and a surjective linear map `toH` from the `D`-bounded tails (in
practice, laurent-tails' comparison, realized via `RS.Cech.mlClass`) such that `pair ω` vanishes on
`ker toH` for every `ω ∈ Ω(-D)` (in practice, THE residue theorem applied to `f·ω` for `f ∈ ℳ(X)`,
`docs/requests/residue-theorem.md`), the pairing descends to an injective map into `Dual H`, hence
`i(-D) ≤ finrank H`. Pure linear algebra once the two hypotheses are supplied — proved here in
full, zero sorries, no dependency on laurent-tails or residue-theorem's own content. -/
theorem finrank_omegaSpace_le {D : RS.Divisor X} {H : Type*} [AddCommGroup H] [Module ℂ H]
    [FiniteDimensional ℂ H] (toH : ↥(TailSpace D) →ₗ[ℂ] H) (hsurj : Function.Surjective toH)
    (hwd : ∀ ω ∈ MForm.OmegaSpace (-D), ∀ τ : ↥(TailSpace D), toH τ = 0 → pair ω (τ : Tail X) = 0) :
    Module.finrank ℂ (MForm.OmegaSpace (-D)) ≤ Module.finrank ℂ H
```

### D6 — The frozen target for #26 (NOT proved here — the obligation this unit hands off)

```lean
/-- #26's headline deliverable (Miranda Thm 3.3 in full, i.e. Serre Duality). The `≤` direction is
`finrank_omegaSpace_le` (D5) instantiated at `H := RS.Cech.H1 D`; the `≥` direction is Miranda
Lemma 3.4 + Lemma 3.6 (surjectivity), genuinely new labor NOT attempted anywhere in this design. -/
theorem RS.TailDuality.i_neg_eq_h1 [T1Space X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    (D : RS.Divisor X) : RS.i (-D) = RS.Finiteness.h1 D

/-- Immediate corollary via canonical-forms' `i_eq_l_add_canonicalDivisorOf` — the shape
riemann-roch actually wants (blueprint: "combine the tail-form RR `l(D) − h¹(D) = deg D + 1 − g`
with tail Serre duality `h¹(D) = l(K−D)`"). -/
theorem RS.TailDuality.l_sub_eq_h1 [...] {ω₀ : MForm X} (h₀ : ω₀ ≠ 0) (D : RS.Divisor X) :
    RS.l (RS.canonicalDivisorOf ω₀ - D) = RS.Finiteness.h1 D
```

At `D := 0`: `i(0) = h1 0`, and canonical-forms' `genus_eq_finrank_omegaSpace_zero` gives `i(0) =
genus X`, so `h1 0 = genus X` — the exact fact cech-h1-genus needs (`dim H¹(X,𝒪) = g`), assembled
entirely from already-frozen pieces once #26 lands.

---

## 3. File plan

| # | File | Content | Est. | Imports beyond stdlib/mathlib |
|---|------|---------|------|-------------------------------|
| 1 | `SerrePairing/TailSpace.lean` | `Tail X` (D1), `AddCommGroup`/`Module ℂ` (free via `Finsupp`), `Tail.BoundedBy`, `TailSpace D`, `Tail.single`/`single_boundedBy` | ~140 | `Mathlib.Data.Finsupp.Basic`, `Jacobian.Meromorphic` (for `Divisor`) |
| 2 | `SerrePairing/Pairing.lean` | `pair` (D2), `pair_eq_finsum_sum`, bilinearity, `pair_single` | ~180 | file 1, `Jacobian.CanonicalForms` (for `MForm`), `Jacobian.ResidueCalculus.Residue` |
| 3 | `SerrePairing/Duality.lean` | `exists_tail_pair_ne_zero` (D4), `finrank_omegaSpace_le` (D5) | ~160 | files 1–2, `Jacobian.CanonicalForms.LinearSystems` (`OmegaSpace`), `Mathlib.LinearAlgebra.Isomorphisms`, `Mathlib.LinearAlgebra.Dual.Lemmas` |
| 4 | `Jacobian/SerrePairing.lean` | unit root, API docstring, records D6's frozen statement as documentation (not a compiled declaration — genuinely not provable here) | ~40 | all |

Four files, within the 2–4 bound. Build waves: file 1 is fully independent of canonical-forms
(only needs `Divisor`, already BUILT); file 2 is gated on canonical-forms' `MForm`/`resAt`/
`coeffAt` landing (files `MForm.lean`/`OrdRes.lean` per their own plan); file 3 additionally needs
`OmegaSpace`/`mem_omegaSpace_iff`/`MForm.eq_zero_or_forall_ord_ne_top` (their files
`OrdRes.lean`/`LinearSystems.lean`). Nothing here is gated on laurent-tails, residue-theorem, or
cech-cohomology — this whole unit is buildable as soon as canonical-forms' first four files land,
independent of canonical-forms' own `Existence.lean`/χ-gate (§1.1: we never call
`exists_nonconstant_mero`/`exists_ne_zero_mform`, only the *types* `MForm`/`OmegaSpace`).

---

## 4. Exports — exact signatures

Namespace `RS.SerrePairing` throughout (files 1–3); file 4 (root) re-exports + docstring only.
Standing variables:
```lean
open scoped ContDiff Manifold Classical
variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
```
`[T2Space X] [CompactSpace X]` enters at `pair`'s use of `MForm.OmegaSpace`/`i` (their own
hypotheses, canonical-forms.md D11); `[T1Space X] [ConnectedSpace X]` enters at D4/D5 (needs
`MForm.eq_zero_or_forall_ord_ne_top`, canonical-forms.md D5).

### 4.1 `TailSpace.lean`

```lean
def Tail (X) [...] : Type _ := X →₀ (ℤ →₀ ℂ)
noncomputable instance : AddCommGroup (Tail X)
noncomputable instance : Module ℂ (Tail X)
def Tail.BoundedBy (τ : Tail X) (D : RS.Divisor X) : Prop
def TailSpace (D : RS.Divisor X) : Submodule ℂ (Tail X)
@[simp] theorem mem_tailSpace_iff {τ : Tail X} {D} : τ ∈ TailSpace D ↔ τ.BoundedBy D := Iff.rfl
noncomputable def Tail.single (p : X) (n : ℤ) (c : ℂ) : Tail X
@[simp] theorem Tail.single_apply (p n c x) :
    Tail.single p n c x = if x = p then Finsupp.single n c else 0
theorem Tail.single_boundedBy {p n c D} (h : c ≠ 0 → n < -(D p)) : (Tail.single p n c).BoundedBy D
```

### 4.2 `Pairing.lean` (`[T2Space X] [CompactSpace X]`)

```lean
noncomputable def pair (ω : MForm X) (τ : Tail X) : ℂ
theorem pair_eq_finsum_sum (ω) (τ) :
    pair ω τ = ∑ᶠ x, ∑ k ∈ (τ x).support, τ x k * laurentCoeffAt (ω.coeffAt x) (chartAt ℂ x x) (-1-k)
theorem pair_add_left (ω ω' : MForm X) (τ) : pair (ω+ω') τ = pair ω τ + pair ω' τ
theorem pair_smul_left (c : ℂ) (ω) (τ) : pair (c • ω) τ = c * pair ω τ
theorem pair_zero_left (τ) : pair (0 : MForm X) τ = 0
theorem pair_add_right (ω) (τ σ : Tail X) : pair ω (τ + σ) = pair ω τ + pair ω σ
theorem pair_smul_right (ω) (c : ℂ) (τ) : pair ω (c • τ) = c * pair ω τ
theorem pair_zero_right (ω) : pair ω (0 : Tail X) = 0
theorem pair_single (ω) (p n c) :
    pair ω (Tail.single p n c) = c * laurentCoeffAt (ω.coeffAt p) (chartAt ℂ p p) (-1-n)

/-- Packaged as a genuine bilinear map, for D5's construction. -/
noncomputable def pairL : MForm X →ₗ[ℂ] Tail X →ₗ[ℂ] ℂ
```

### 4.3 `Duality.lean` (`[T1Space X] [T2Space X] [CompactSpace X] [ConnectedSpace X]`)

```lean
theorem exists_tail_pair_ne_zero {D : RS.Divisor X} {ω : MForm X}
    (hω : ω ∈ MForm.OmegaSpace (-D)) (hω0 : ω ≠ 0) : ∃ τ : Tail X, τ.BoundedBy D ∧ pair ω τ ≠ 0

theorem finrank_omegaSpace_le {D : RS.Divisor X} {H : Type*} [AddCommGroup H] [Module ℂ H]
    [FiniteDimensional ℂ H] (toH : ↥(TailSpace D) →ₗ[ℂ] H) (hsurj : Function.Surjective toH)
    (hwd : ∀ ω ∈ MForm.OmegaSpace (-D), ∀ τ : ↥(TailSpace D), toH τ = 0 → pair ω (τ : Tail X) = 0) :
    Module.finrank ℂ (MForm.OmegaSpace (-D)) ≤ Module.finrank ℂ H
```

---

## 5. Proof plans

### P0. `TailSpace`'s submodule laws, `pair_eq_finsum_sum`, bilinearity (routine, `Tail.lean`/`Pairing.lean`)

`zero_mem'`: `(0 : Tail X).support = ∅` (`Finsupp.support_zero`), vacuous. `add_mem'`: for `x ∈
(τ+σ).support`, `Finsupp.support_add` gives `x ∈ τ.support ∪ σ.support`; for `k ∈ ((τ+σ) x).support
= (τ x + σ x).support`, `Finsupp.support_add` again gives `k ∈ (τ x).support ∪ (σ x).support`; case
on which side `x`/`k` came from (four cases, two trivial since the hypothesis directly applies, two
using that a `Finsupp` evaluates to `0` off its support so the OTHER side's bound is vacuously fine
too — actually only need the bound on whichever side is nonzero at `(x,k)`, standard). `smul_mem'`
similarly via `Finsupp.support_smul_eq` (for `c ≠ 0`; `c = 0` case trivial, smul is `0`).
`pair_eq_finsum_sum`: `resAt_tail_mul` applied pointwise inside the finsum (`finsum_congr`), no
further work — this IS `resAt_tail_mul`'s conclusion literally, re-packaged. Bilinearity in `ω`:
`resAt_fun_add`/`resAt_const_mul` applied pointwise (`finsum_add_distrib`, both finsums share the
SAME index set `τ`'s support, no extension needed). Bilinearity in `τ`: needs `finsum_add_distrib`
across the two (possibly different) supports of `τ`/`σ` — standard, `resAt` of a function that is
identically the `0`-tail's contribution is `0` (`resAt_congr` + the zero-tail sum being empty).
Estimated 60–90 lines total, all routine `Finsupp`/`finsum` bookkeeping, zero conceptual risk
(spike focus was deliberately elsewhere, on P1's computation, the genuinely new content).

### P1. `exists_tail_pair_ne_zero` (D4, `Duality.lean`) — **spike-verified in full, §8**

1. `[ConnectedSpace X]` gives `Nonempty X` automatically (mathlib: `ConnectedSpace` extends
   `Nonempty`); pick ANY `p : X`.
2. `ω ≠ 0` + `MForm.eq_zero_or_forall_ord_ne_top` (canonical-forms D5) resolves to `∀ x, ω.ord x ≠
   ⊤`; in particular `hp : ω.ord p ≠ ⊤`. Set `k := (ω.ord p).untop₀ : ℤ`.
3. `hω`/`mem_omegaSpace_iff` + `hω0` gives `D ≤ ω.divisor` (the `ω = 0` disjunct is excluded);
   evaluate at `p` and rewrite `ω.divisor p = (ω.ord p).untop₀ = k` (`MForm.divisor_apply`): `D p ≤
   k`.
4. Witness `τ := Tail.single p (-1-k) 1`. `BoundedBy`: need `(1:ℂ) ≠ 0 → -1-k < -(D p)`, i.e. `D p ≤
   k` (integer rearrangement, `omega`) — exactly step 3.
5. `pair ω τ = pair_single = 1 * laurentCoeffAt (ω.coeffAt p) (chartAt ℂ p p) (-1-(-1-k)) =
   laurentCoeffAt (ω.coeffAt p) (chartAt ℂ p p) k` (the exponent algebra `-1-(-1-k)=k` is `ring`).
6. `≠ 0` by `laurentCoeffAt_order_ne_zero (ω.meromorphicOn_coeffAt p (chart-center-in-target)) hp`
   — literally the definition of `k` folds this to exactly the hypothesis's conclusion shape.

Steps 5–6 are the **spike-verified core** (§8): the abstract computation `resAt (fun z => (z-z₀)^
(-1-k) * g z) z₀ = laurentCoeffAt g z₀ k ≠ 0` (for `g` meromorphic, `k` its own order, `hne : order
≠ ⊤`) compiles clean via `resAt_zpow_mul` + `laurentCoeffAt_order_ne_zero` with a single `ring`
rewrite in between — exactly the shape steps 5–6 instantiate at `g := ω.coeffAt p`. Estimated 30–40
lines total (steps 1–4 bookkeeping, ~20; steps 5–6, spike-verified, ~10).

### P2. `finrank_omegaSpace_le` (D5, `Duality.lean`) — pure linear algebra, no new mathematics

1. **Descend `pair ω` through `toH`.** For fixed `ω ∈ OmegaSpace(-D)`, `pair ω` restricted to
   `↥(TailSpace D)` is linear (`pairL ω` restricted, `pair_add_right`/`pair_smul_right`); `hwd ω`
   says it vanishes on `LinearMap.ker toH`, so `Submodule.liftQ (pair ω |_{TailSpace D}) (hwd ω : _)
   : ↥(TailSpace D) ⧸ LinearMap.ker toH →ₗ[ℂ] ℂ` (mathlib `Submodule.liftQ`,
   `LinearAlgebra/Quotient/Basic.lean:129`).
2. **Identify the quotient with `H`.** `toH.quotKerEquivOfSurjective hsurj : (↥(TailSpace D) ⧸
   LinearMap.ker toH) ≃ₗ[ℂ] H` (mathlib, `LinearAlgebra/Isomorphisms.lean:45`, exact name verified
   at the pin). Compose: `Φ ω := (Submodule.liftQ _ (hwd ω)).comp (toH.quotKerEquivOfSurjective
   hsurj).symm.toLinearMap : H →ₗ[ℂ] ℂ`, i.e. `Φ ω ∈ Module.Dual ℂ H`.
3. **`Φ` is linear in `ω`.** Both the `liftQ`/`quotKerEquivOfSurjective` machinery are FIXED
   (independent of `ω`); `Φ (ω+ω')`/`Φ (c•ω)` reduce, after unfolding to their action on an
   arbitrary `h = toH τ`, to `pair (ω+ω') τ = pair ω τ + pair ω' τ`/`pair (c•ω) τ = c * pair ω τ`
   (`pair_add_left`/`pair_smul_left`) — package as `Φ : ↥(MForm.OmegaSpace (-D)) →ₗ[ℂ] Module.Dual ℂ
   H` via `LinearMap.mk'`/an explicit `map_add'`/`map_smul'` proof using `LinearMap.ext` +
   `Submodule.Quotient.mk`-surjectivity to reduce to checking on representatives `toH τ`.
4. **Injectivity.** Suppose `Φ ω = 0` with `ω ≠ 0` (`ω ∈ OmegaSpace(-D)` by assumption on the
   domain). By D4 (`exists_tail_pair_ne_zero`), get `τ₀ : Tail X` with `τ₀.BoundedBy D` (i.e. `τ₀ :
   ↥(TailSpace D)`, coerced) and `pair ω τ₀ ≠ 0`. But `Φ ω (toH τ₀) = pair ω τ₀` (unwinding the
   `liftQ`/equiv composite at the representative `τ₀` — a `Submodule.Quotient.mk`/
   `quotKerEquivOfSurjective_apply_mk` computation, both named lemmas), and `Φ ω = 0` forces this to
   be `0` — contradiction. Hence `ω = 0`; `Φ` is injective.
5. **Finrank.** `LinearMap.finrank_le_finrank_of_injective Φ-injective : finrank ℂ
   ↥(MForm.OmegaSpace (-D)) ≤ finrank ℂ (Module.Dual ℂ H)` (mathlib,
   `LinearAlgebra/Dimension/StrongRankCondition.lean:554`, needs `[FiniteDimensional ℂ (Module.Dual
   ℂ H)]` — automatic from `[FiniteDimensional ℂ H]`, mathlib instance
   `instModuleDualFiniteDimensional`). Then `Subspace.dual_finrank_eq : finrank ℂ (Module.Dual ℂ H) =
   finrank ℂ H` (mathlib, `LinearAlgebra/Dual/Lemmas.lean:510`, exact namespace to double-check at
   build time — stated generally, no extra hypothesis) closes the chain.

Estimated 70–100 lines (steps 1–3 are the bulk, standard "package a family of linear maps as one
linear map into a function space" bookkeeping; steps 4–5 are short, direct citations).

### P3. Well-definedness derivation for #26 (NOT proved in this unit — recorded so #26 doesn't
have to re-derive it; full text in `docs/requests/residue-theorem.md`)

For `f : ℳ X`, `ω ∈ OmegaSpace(-D)`: split `f.holoRepr` at each pole `x` into `D`-truncated tail
(exponents `< -(D x)`) plus `O_D`-regular remainder (exponents `≥ -(D x)`,
`MeromorphicAt.exists_principalPart_add_analyticAt`-style, residue-calculus, BUILT). The regular
part times `ω` has order `≥ -(D x) + D(x) = 0` (analytic; `ω`'s own order is `≥ D(x)` there since
`ω ∈ OmegaSpace(-D)`), hence `resAt = 0` there (`RS.resAt_of_order_nonneg`, BUILT). So `resAt(f.holoRepr
· ω)` at `x` equals `resAt(\text{tail}_x · ω)` — one term of `pair ω (α_D f)` via `resAt_tail_mul`
(D2). Summing over `x` (finite: `f` has finitely many poles on compact `X`; `ω` finitely many
zeros/poles) turns residue-theorem's `Σ_x resAt(f.holoRepr · ω) = 0` (the atom requested,
`docs/requests/residue-theorem.md`) directly into `pair ω (α_D f) = 0` — exactly `finrank_omegaSpace_le`'s
`hwd` hypothesis at `ker toH = range α_D` (once laurent-tails' comparison supplies `toH` with this
kernel, `docs/requests/laurent-tails.md`).

---

## 6. Junk-value and compatibility ledger

- `Tail X := X →₀ (ℤ →₀ ℂ)`: no junk anywhere — `Finsupp` is a genuine, junk-free "finite support"
  type; off-support values are definitionally `0`, exactly the honest empty-tail meaning.
- `pair`'s finsum: supported on `{x | τ x ≠ 0}` (`τ.support`, finite by `Finsupp`); at `x` outside
  this support the summand is `resAt (fun z => 0 * ω.coeffAt x z) (center) = resAt 0 (center) = 0`
  (empty inner `Finset.sum`), so `finsum`'s "junk `0` outside finite support" convention is the
  HONEST value here, not a hack — matches `PrincipalPartData.totalRes`'s own `∑ᶠ` idiom exactly.
- `Tail.BoundedBy`'s strict inequality `k < -(D x)` (not `≤`) is Miranda's own convention (verified
  against the PDF, §0.1/§2 D1), pinned so `D4`'s witness computation (`-1-k < -(D p) ↔ D p ≤ k`)
  lines up exactly with `ω.divisor ≥ D`'s `≥` (non-strict) — a one-off arithmetic fact
  (`D p ≤ k ↔ -1-k < -(D p)` over `ℤ`), not a convention mismatch; recorded in P1 step 4.
- `finrank_omegaSpace_le`'s hypotheses (`toH`, `hsurj`, `hwd`) are genuine PREMISES, not
  discharged here — the theorem is honestly conditional; nothing about its statement is vacuous
  (once #26 supplies a real `toH`, all three hypotheses are independently meaningful and the
  conclusion is the real numeric inequality).

---

## 7. Risks & fallbacks

1. **`quotKerEquivOfSurjective`/`liftQ`/`dual_finrank_eq` exact namespaces** (LOW). All three
   verified present at the pin by direct `grep` of `.lake/packages/mathlib` (§1.2/§5 P2 cite
   `file:line`); only risk is a `Subspace.` vs `Module.` namespace prefix drift, a one-line fix.
2. **`Tail X`'s `BoundedBy`-based `TailSpace D` submodule proof (P0)** (LOW). Routine `Finsupp`
   support-of-sum/support-of-smul bookkeeping, no new mathlib gaps expected; not spike-tested
   (budget went to P1's genuinely novel computation) but structurally identical in shape to
   `principalPartCarrier`'s own already-BUILT, zero-sorry proof (`MittagLeffler.lean:44-71`) minus
   one condition (no exponent bound at the ambient level, §2 D1's ⚠) — a strict simplification of
   an already-working proof, not new territory.
3. **Packaging `Φ` as a genuine `LinearMap ω ↦ Dual H` (P2 step 3)** (LOW-MEDIUM). The
   "linear-map-valued-in-a-function-space" pattern is standard but can be fiddly in Lean
   (`LinearMap.ext` + `Submodule.Quotient.mk`-surjectivity reduction); if `Submodule.liftQ`'s
   naturality-in-the-first-argument lemmas prove awkward to compose, a fallback is to build `Φ` via
   `LinearMap.mk'` directly against the EXPLICIT formula `Φ ω h := pair ω (Function.surjInv hsurj h)`
   and prove well-definedness/linearity by hand from `hwd`, bypassing `liftQ` entirely (more lines,
   zero new mathematical content, strictly more robust to name drift).
4. **The `MLFormData`-vs-`Tail X` divergence** (LOW, by design, not a risk to THIS unit — flagged
   for #26/laurent-tails only, `docs/requests/laurent-tails.md`). We deliberately did not try to
   reuse or extend canonical-forms' `MLFormData`; if a future canonical-forms revision retrofits a
   `Module ℂ` instance onto `MLFormData` matching Miranda's `T[D]` exactly, `Tail X`/`TailSpace D`
   here would become redundant with it — a welcome simplification for #26 to make, not a blocker
   for us (our `pair`/`finrank_omegaSpace_le` would simply get an extra adapter `LinearEquiv` in
   that case, per `docs/requests/laurent-tails.md` item 1).

---

## 8. Spike report (`scratch_serrec.lean`, project root)

Gated per compile discipline (`pgrep -cx lean < 3`, checked immediately before: `0` processes),
`lake env lean scratch_serrec.lean`: **compiles clean, exit 0** (one fix needed, recorded below).

Tested the injectivity witness's computational core (P1 steps 5–6) at the bare `ℂ → ℂ` level
(canonical-forms/`MForm` not yet on disk at design time, so the spike is phrased against a generic
`g : ℂ → ℂ` playing the role of `ω.coeffAt p`, exactly what P1 instantiates):

```lean
example (hg : MeromorphicAt g z₀) (hne : meromorphicOrderAt g z₀ ≠ ⊤) :
    resAt (fun z => (z - z₀) ^ (-1 - (meromorphicOrderAt g z₀).untop₀) * g z) z₀ ≠ 0 := by
  set k := (meromorphicOrderAt g z₀).untop₀ with hk
  have h1 : resAt (fun z => (z - z₀) ^ (-1 - k) * g z) z₀ = laurentCoeffAt g z₀ (-1 - (-1 - k)) :=
    resAt_zpow_mul hg (-1 - k)
  rw [h1]; have h2 : -1 - (-1 - k) = k := by ring
  rw [h2]; exact laurentCoeffAt_order_ne_zero hg hne
```

**One fix needed during the spike**: an initial `rw [h2, ← hk]` attempt (trying to rewrite the goal
back through `hk`'s definition after `set` had already folded it) failed — `set` already replaces
all occurrences, so the goal after `rw [h2]` is *already* `laurentCoeffAt g z₀ k ≠ 0`, exactly
`laurentCoeffAt_order_ne_zero`'s conclusion; the extra `← hk` was redundant and mismatched
direction. Removing it closed the proof immediately. Recorded for the builder: **do not** re-fold
through `set`'s defining equation after the `set` itself has already done the folding.

This confirms P1 steps 5–6 (`pair_single` + the exponent algebra + `laurentCoeffAt_order_ne_zero`)
compile exactly as planned, with the one-off exponent identity `-1-(-1-k)=k` closing by `ring` — the
single riskiest computational step in the whole design, now de-risked.

---

## 9. Downstream map (who consumes what)

- **serre-duality-tails / #26** (`Builds on: laurent-tails, proper-map-degree, residue-theorem,
  serre-duality-cech`): `Tail X`/`TailSpace D`/`pair` (§2 D1–D2, the vocabulary their `T[D]`
  comparison targets), `exists_tail_pair_ne_zero` (D4, reused as-is or cited for its proof shape),
  `finrank_omegaSpace_le` (D5, instantiated at `H := RS.Cech.H1 D` with `toH` from their own
  comparison + `mlClass`, `hwd` from residue-theorem per `docs/requests/residue-theorem.md`) to get
  `i(-D) ≤ h1 D`; they supply the reverse inequality (Miranda Lemma 3.4/3.6, genuinely new labor) to
  close D6's `i(-D) = h1 D`.
- **cech-h1-genus** (`Builds on: serre-duality-tails`): consumes D6's `i(-D)=h1 D` at `D:=0`,
  composed with canonical-forms' `genus_eq_finrank_omegaSpace_zero`, to get `h1 0 = genus X` — see
  §2 D6's remark.
- **riemann-roch** (`Builds on: serre-duality-tails`, indirect): consumes D6's `l_sub_eq_h1` form
  directly, combined with finiteness-and-chi's tail-form RR (`l D − h1 D = deg D + 1 − g`), per the
  blueprint's own stated combination.
- **laurent-tails**: consumes `Tail X`/`TailSpace D`/`pair` as the target vocabulary their own `T[D]`
  should either equal or be adapted to (`docs/requests/laurent-tails.md`).
- **residue-theorem**: no direct consumption (they don't depend on us), but their headline statement
  is requested at the exact `MForm`-level shape #26 needs (`docs/requests/residue-theorem.md`).

---

## 10. Coordination notes filed

- `docs/requests/laurent-tails.md`: our `Tail`/`TailSpace`/`pair` shape, requesting either a direct
  identification or an adapter `LinearEquiv` with their eventual `T[D](X)`, plus a request for the
  truncation map `α_D`'s exact shape (bookkeeping-sensitive for the `-1-k` convention) and a flagged
  risk-reducer (`RS.Cech.mlClass`, already BUILT, looks like their `T[D] → H¹(D)` realization map).
- `docs/requests/residue-theorem.md`: the exact `sum_resAt_eq_zero` statement #26 needs (Forster
  10.21 specialized to `f.holoRepr · ω` for `ω : MForm X`), plus the full well-definedness
  derivation (§5 P3) worked out so #26 doesn't have to re-derive the reduction.
- No blueprint edit filed: the blueprint's `Builds on: canonical-forms` edge for serre-duality-cech
  is confirmed sufficient — nothing in this design needs cech-cohomology, laurent-tails, or
  residue-theorem directly (only canonical-forms' `MForm`/`OmegaSpace`/`i` and residue-calculus's
  already-BUILT atoms, both reachable via canonical-forms' own transitive imports).
