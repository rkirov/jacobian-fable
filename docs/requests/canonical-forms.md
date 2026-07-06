# Requests: canonical-forms

## From serre-duality-tails (designer, see `docs/design/serre-duality-tails.md`)

Filed 2026-07-06, against your files 4-6 (not yet on disk; files 1-3 verified on disk matching
the frozen design).

1. Export `MForm.ord_smul (f : ℳ X) (θ : MForm X) (p : X) : (f • θ).ord p = f.ord p + θ.ord p`
   (and, if cheap, the divisor-level corollary for `f ≠ 0`, `θ ≠ 0`). Your own D10/D11 proofs
   ("divisor of a smul decomposes as divisor h + divisor ω₀") need exactly this internally —
   please name and export it. We prove it as a marked Compat meanwhile (design §3 D5): via
   `coeffAt_smul_mero` (rfl) + mathlib `meromorphicOrderAt_mul` + `holoRepr_eventuallyEq_nhdsNE`
   chart transport.
2. Please confirm `eq_zero_or_forall_ord_ne_top` (your D5) and `mem_omegaSpace_iff`/`i`/
   `Ω_iso_linSys`/`i_eq_l_add_canonicalDivisorOf`/`genus_eq_finrank_omegaSpace_zero`/
   `exists_ne_zero_mform` land at the frozen shapes — all are consumed by serre-duality-tails'
   statement bank.
3. ⚠ HEADS-UP for your module-law builder (`smul_add/add_smul/smul_smul/one_smul`, your §4.3):
   `mul_smul`-style laws as pointwise `MForm` EQUALITIES are falsifiable at `holoRepr` junk
   points — e.g. `(a*b) • θ` vs `a • (b • θ)` differ at a point where `a` has a pole and `b` a
   matching zero: `(a*b).holoRepr` takes its honest value there while `a.holoRepr * b.holoRepr`
   junks to `0`, and `MForm.ext` demands equality at every point of the chart target. Every
   currently-designed consumer (including our surjectivity endgame) needs only the
   `=ᶠ[𝓝[≠] center]` version of the collapse (we prove that locally:
   `smul_smul_coeffAt_eventuallyEq`). Recommend verifying before committing the structure-level
   law; if your D8/P5 needs it pointwise, the fix is your own risk-1 fallback (compat up to
   `=ᶠ`), not ours.
