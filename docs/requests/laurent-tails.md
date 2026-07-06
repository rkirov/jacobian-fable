# Requests: laurent-tails

## From serre-duality-cech (designer, see `docs/design/serre-duality-cech.md`)

Filed at design time (2026-07-06); laurent-tails had no design doc yet when this was written, so
these are forward requests, not corrections to an existing interface.

serre-duality-cech builds, **using only canonical-forms + residue-calculus** (no dependency on
you), a self-contained tail space and pairing:

```lean
namespace RS.SerrePairing
def Tail (X) [...] : Type _ := X →₀ (ℤ →₀ ℂ)                        -- Finsupp of Finsupps, free algebra
def Tail.BoundedBy (τ : Tail X) (D : Divisor X) : Prop :=
  ∀ x ∈ τ.support, ∀ k ∈ (τ x).support, k < -(D x)
def TailSpace (D : Divisor X) : Submodule ℂ (Tail X) := ⟨{τ | τ.BoundedBy D}, ...⟩
noncomputable def pair (ω : MForm X) (τ : Tail X) : ℂ :=
  ∑ᶠ x, RS.resAt (fun z => (∑ k ∈ (τ x).support, τ x k * (z - chartAt ℂ x x) ^ k) * ω.coeffAt x z)
    (chartAt ℂ x x)
end RS.SerrePairing
```

(full definitions/lemmas: `docs/design/serre-duality-cech.md` §2 D1–D3, §4.1–4.2).

**What we need from you**, when your own `T[D]` design lands:

1. **Either** identify your `T[D](X)` directly with our `TailSpace D` (a `LinearEquiv`, ideally
   `rfl`-cheap if your definition happens to match), **or** supply an explicit adapter
   `LinearEquiv`/`LinearMap` between your `T[D](X)` and `↥(TailSpace D)`. We deliberately did not
   try to guess your final shape (CC8 only sketches "⨁_p (principal tails at p bounded by D)");
   our `Tail X := X →₀ (ℤ →₀ ℂ)` is one honest, buildable-today model of that sketch (free
   `AddCommGroup`/`Module ℂ` via `Finsupp`, no hand-rolled submodule proof needed) but you may
   have good reasons (e.g. matching `PrincipalPartData`/`MLFormData` more closely, or needing
   `Finset`-indexed rather than `Finsupp`-indexed points for a `Finset.sum` you already have) to
   land on something only *isomorphic* to it, not defeq. Either is fine — we only consume the
   comparison as an equivalence, never definitional equality.

2. **The truncation map** `α_D : ℳ X → TailSpace D` (or your own `T[D]`, transported): our
   well-definedness argument (`docs/design/serre-duality-cech.md` §5, the derivation feeding
   `docs/requests/residue-theorem.md`) needs `α_D f` to literally be, at each point `x`, the
   negative-Laurent-tail of `f.holoRepr` at `x` truncated to exponents `< -(D x)` — i.e.
   `(α_D f) x = mlCoeff f.holoRepr (chartAt ℂ x).target (chartAt ℂ x x) |>.filter (· < -(D x))`- shaped (matching `RS.PrincipalPartData.mlCoeff`, `Jacobian/ResidueCalculus/MittagLeffler.lean:124`,
   which already extracts exactly this shape planar-locally — you may find it reusable almost
   verbatim, just re-indexed by `X` instead of a planar `Set ℂ`). If your `α_D` differs by even a
   sign/truncation-boundary convention from ours, flag it — the `-1-k` bookkeeping in our
   `pair_single`/injectivity lemma is convention-sensitive and would need a one-line adjustment,
   nothing structural.

3. **The comparison to `H¹(D)`.** CC8/`Jacobian/Cech/Skyscraper.lean`'s already-BUILT `mlClass`
   (docstring: *"Both the χ connecting map (finiteness-and-chi) and laurent-tails' `T[D] → H¹(D)`
   factor through this"*) looks like it is exactly the realization map you need: feed it a
   `C0 D' 𝒰` 0-cochain built by placing each tail's own Laurent series on a small chart-disk cover
   around its point (0 elsewhere) and it hands back an `H1 D` class, given only that the
   coboundary satisfies `MemLD D`. We did not verify this reduction in detail (out of our unit's
   scope) but flag it as a likely order-of-magnitude risk-reducer for your own build.

None of this blocks serre-duality-cech — our `Tail`/`TailSpace`/`pair`/injectivity lemma are fully
self-contained and provable today. It only blocks serre-duality-tails (#26), which needs the
adapter to transport our `finrank_omegaSpace_le` (generic interface theorem, §2 D5) to the actual
`RS.Cech.H1 D`.
