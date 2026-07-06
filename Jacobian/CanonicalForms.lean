import Jacobian.CanonicalForms.MForm
import Jacobian.CanonicalForms.OrdRes
import Jacobian.CanonicalForms.Differential
import Jacobian.CanonicalForms.LinearSystems

/-!
# canonical-forms: meromorphic 1-forms and the canonical divisor `K` (namespace `RS`)

API summary (see `docs/design/canonical-forms.md`). Builds on `residue-calculus` (BUILT) and
`finiteness-and-chi` (IN FLIGHT — see the gate note below).

* **`MForm X`** (`MForm.lean`, D1–D3): a meromorphic 1-form as a `chartAt`-indexed coefficient
  family — the meromorphic analogue of `Form1`'s `coeffIn` API / dbar's `Form01`, with
  `MeromorphicOn` coefficients (mathlib's unconditional generalization of `AnalyticOnNhd`/
  `ContDiffOn`, allowing poles) and the `(1,0)`-transition rule (`deriv τ`, no conjugate).
  `RS.MForm.ext`, `Zero`/`Add`/`Neg`/`Sub`/`SMul ℂ`/`AddCommGroup`/`Module ℂ` (pointwise on
  `coeffAt`). `RS.MFormCoeffData X ι`/`RS.MForm.ofCoeffs` (D3): the arbitrary-covering-chart-family
  constructor (mirrors `Form1CoeffData`/`Form1.ofCoeffs`), with the master transport lemma
  `RS.MFormCoeffData.rawCoeffAt_eq` and `RS.MForm.coeffAt_ofCoeffs`.
* **`ord`/`resAt`/`divisor`** (`OrdRes.lean`, D4/D6): `RS.MForm.ord`/`RS.MForm.resAt`, read via the
  fixed `chartAt` (no invariance proof needed to be well-defined); the "read in any maximal-atlas
  chart" corollaries `RS.MForm.ord_eq_of_mem_source`/`RS.MForm.resAt_eq_of_mem_source` (via
  `meromorphicOrderAt_comp_of_deriv_ne_zero`/`RS.resAt_comp_mul_deriv`); local propagation
  `RS.MForm.eventually_ord_eq_top`/`RS.MForm.eventually_ord_eq_zero` (via the cross-point transport
  `RS.MForm.coeffAt_eventuallyEq_of_mem_source`, built from `compat`); `RS.MForm.divisor`/
  `RS.MForm.degree` (connectedness-free local finiteness, mirrors `MeroGermOn.divisorOn` exactly).
* **`MForm.ofForm1`/`Form1.toMForm`, `MForm.smul`, `MForm.d`/`dlog`** (`Differential.lean`, D7):
  the holomorphic embedding (`RS.MForm.ofForm1`, `RS.Form1.toMForm : Form1 X →ₗ[ℂ] MForm X`,
  `RS.MForm.ofForm1_ord_nonneg`); the `ℳ(X)`-module action `RS.MForm.smul`/`SMul (ℳ X) (MForm X)`
  via the canonical `MeroGermOn.holoRepr`; the differential `RS.MForm.d : ℳ X → MForm X` — the
  unit's riskiest lemma (the `compat`-at-poles case split) is isolated as the reusable
  `RS.deriv_comp_chart_congr` (spike-verified, handles poles via junk-collapse in BOTH directions);
  `RS.MForm.d_const`; `RS.MForm.dlog`.
* **`OmegaSpace`/`i`/`MLFormData`** (`LinearSystems.lean`, D11/D13, partial — see deferral note):
  `RS.MForm.OmegaSpace D`/`RS.mem_omegaSpace_iff`/`RS.MForm.i` (index of speciality), defined
  order-wise (mirrors `LinSys`'s own primary definition) via the new order-arithmetic lemmas
  `RS.MForm.ord_add`/`RS.MForm.ord_smul`; `RS.MLFormData`/`RS.MLFormData.Realizes`/`.totalRes`/
  `.Realizes.resAt_eq` (D13, a thin wrapper around residue-calculus's `PrincipalPartData`).

## Deferrals (documented, not sorried — zero sorries in every file above)

**D5 — `MForm.eq_zero_or_forall_ord_ne_top` (the global zero-dichotomy)**: NOT included. Its proof
plan's step 5 ("`S = univ` ⟹ `θ = 0`") needs upgrading "`θ.ord` is `⊤` at every point's OWN chart
center" to "`θ.coeffAt x` is literally `0` at an ARBITRARY target point `z`" — and this genuinely
does NOT follow from order data alone: `meromorphicOrderAt f z₀ = ⊤` is defined as `f =ᶠ[𝓝[≠]z₀] 0`
(a *punctured* neighborhood statement, verified directly against mathlib's
`meromorphicOrderAt_eq_top_iff`), which places **no constraint whatsoever on `f z₀` itself** — a
raw `MeromorphicAt` representative may carry arbitrary junk at any point of non-negative order,
including `⊤`. Chaining `compat` across multiple charts to try to pin such a value down (attempted
extensively) keeps recursing into a symmetric problem one point over; resolving this rigorously
would need `MForm` to carry (or derive) a canonical, junk-free representative at every point —
analogous to `MeroGermOn.holoRepr`/`evalAt`'s role for `ℳ X` — which is out of scope for the time
budgeted to this lemma. This is a *sharper* version of design's own flagged risk §7 item 2
("chart target preconnected"); the difficulty is not preconnectedness but the junk-value issue
itself, which surfaces even for a single chart. Flagged for the orchestrator / a future pass.

**Cascading from D5** (all correspondingly NOT written, not sorried):
* `Jacobian/CanonicalForms/OneDimensional.lean` (D8, `MForm.exists_unique_smul_of_ne_zero`) — its
  proof plan's step 1 directly invokes D5.
* `MForm.canonicalDivisorOf`/`canonicalDivisorOf_linearEquiv` (D10) — needs D8.
* `Ω_iso_linSys`/`i_eq_l_add_canonicalDivisorOf` (D11's second half) — needs `canonicalDivisorOf`.
* `holomorphicMFormsEquiv`/`genus_eq_finrank_omegaSpace_zero` (D12) — its *backward* direction
  (`OmegaSpace 0 → Form1`) hits the **same** junk-value issue as D5 (needing "`0 ≤ ord` at a chart
  center ⇒ analytic on the whole target", design's own P6 step 3), independently of D8.

**D9 — `Existence.lean` is UNWRITTEN** (not sorried): gated on `Jacobian/Finiteness/`'s
`chi`/`h1`/`chi_zero_add_degree_le_l`/`exists_ne_zero_mem_linSys`, which are **not on disk**
(`Jacobian/Finiteness/` currently has only `BddHolo.lean`/`Chain.lean`/`CompactRestrict.lean`/
`Schwartz.lean` — no `Chi.lean`). Per the task's own gating instructions, left unwritten rather
than stated against a nonexistent import. The companion `Divisor.single` Compat (§1.6) is filed as
an upstream request instead of built locally, since its only consumer (`Existence.lean`) does not
exist yet (`docs/requests/meromorphic-and-divisors.md`, item 6).

**`Differential.lean`'s own scope note**: `MForm.smul`'s module laws (`smul_add`/`add_smul`),
`MForm.d_add`/`d_eq_zero_iff`, `MForm.resAt_dlog` are NOT included — they need genuine pointwise
identities for `MeroGermOn.holoRepr` across `+` (`(f+g).holoRepr = f.holoRepr + g.holoRepr`) that
FAIL exactly at the poles of the summands (`evalAt_add` only holds when *both* summands have
`0 ≤ ord`, `OrderEval.lean:168`) — the additive cousin of the D5 junk-value issue. `MForm.d`/`dlog`
themselves (built directly from `holoRepr`, not from a raw sum) are unaffected and fully proved.

Everything NOT listed above in the export summary is proved in full; zero sorries throughout.
-/
