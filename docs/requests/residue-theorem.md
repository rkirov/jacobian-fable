# Requests: residue-theorem

## From serre-duality-cech (designer, see `docs/design/serre-duality-cech.md`)

Filed at design time (2026-07-06); residue-theorem had no design doc yet when this was written.

serre-duality-cech's pairing `RS.SerrePairing.pair : MForm X → Tail X → ℂ` (Miranda VI.3's
`Res_ω`, purely algebraic, no integration — see `docs/design/serre-duality-cech.md` §2 D2) is
**not** proved well-defined on `H¹(D)` by our unit; that step is explicitly deferred to
serre-duality-tails (#26), which is why the blueprint draws the edge `serre-duality-tails →
residue-theorem` and not `serre-duality-cech → residue-theorem`.

**Exact statement #26 will need from you**, worked out in full at design time so you don't have
to re-derive the reduction (`docs/design/serre-duality-cech.md` §5, "well-definedness proof plan
for #26"):

```lean
theorem sum_resAt_eq_zero [T1Space X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    (f : RS.ℳ X) (ω : RS.MForm X) :
    ∑ᶠ x, RS.resAt (fun z => f.holoRepr ((chartAt ℂ x).symm z) * ω.coeffAt x z) (chartAt ℂ x x) = 0
```

i.e. Forster 10.21 / the blueprint's `∑_p Res_p(h·dg₀) = 0`, specialized to the pair-form
`f.holoRepr · ω` for a GLOBAL meromorphic function `f` and a (possibly meromorphic, not just
holomorphic) 1-form `ω : MForm X` (canonical-forms). If your own headline statement is phrased for
a more general pair-form object (e.g. form-trace-tower's traced forms) rather than literally
`MForm`, a corollary at this exact `MForm`-level signature is what we need — please keep it
exported under a stable name so #26 can cite it directly.

**Why this is exactly what's needed** (the reduction, so you can see the shape is right and so
#26 doesn't have to reprove it): for `D : Divisor X`, `ω ∈ MForm.OmegaSpace (-D)` (i.e.
`ω.divisor ≥ D` pointwise) and `f : ℳ X`, split `f.holoRepr` at each pole `x` of `f` into its
`D`-truncated tail (exponents `< -(D x)`) plus an "`O_D`-regular" remainder (exponents `≥ -(D x)`,
by `MeromorphicAt.exists_principalPart_add_analyticAt`-style decomposition, already built in
`Jacobian/ResidueCalculus/PrincipalPart.lean`). The regular part times `ω` has order `≥ -(D x) +
D(x) = 0` at `x` (analytic, since `ω`'s own order is `≥ D(x)` there), hence contributes `0` to
`resAt` (`RS.resAt_of_order_nonneg`, already built). So `resAt (f.holoRepr · ω)` at each `x` equals
`resAt (tail_x · ω)`, which is exactly one term of `RS.SerrePairing.pair ω (α_D f)`
(`RS.resAt_tail_mul`, already built, `docs/design/serre-duality-cech.md` §2 D2). Summing over `x`
(finite: `f` has finitely many poles on compact `X`, `ω` finitely many zeros/poles) turns your
`sum_resAt_eq_zero` directly into `RS.SerrePairing.pair ω (α_D f) = 0` — the well-definedness
`hwd` hypothesis of `RS.SerrePairing.finrank_omegaSpace_le` (§2 D5), instantiated at
`ker toH = range α_D` once laurent-tails' comparison (`docs/requests/laurent-tails.md`) supplies
`toH`.

Nothing here blocks serre-duality-cech; it is entirely forward-looking for #26.

## From serre-duality-tails (designer, see `docs/design/serre-duality-tails.md`) — confirmation

Filed 2026-07-06. The unit that actually consumes your headline (us) confirms the shape
requested above by serre-duality-cech, with one simplification discovered at design time: since
canonical-forms' `coeffAt_smul_mero` is `rfl` (verified on disk, `Differential.lean:175`), the
requested statement is literally

```lean
theorem sum_resAt_eq_zero … (f : ℳ X) (θ : MForm X) : ∑ᶠ x, (f • θ).resAt x = 0
```

Either this finsum form or the Finset-flexible form
`residueTheorem (θ : MForm X) {S : Finset X} (hS : θ.PoleSet ⊆ ↑S) : ∑ x ∈ S, θ.resAt x = 0`
(your own §2 design shape) works for us — we consume it in exactly ONE lemma
(`RS.TailDuality.pairT_alpha`, design §6 P3), so late shape drift costs one edit. The reduction
recorded by serre-duality-cech (splitting `f` into `D`-tail + regular part) is NOT needed on the
germ model: our term-by-term identification is direct (`resAt_congr` + `holoRepr` rigidity), and
off-tail-support terms vanish by `resAt_of_order_nonneg`. Timing note: this is our risk R2 —
files 3–4 of `Jacobian/TailDuality/` gate on your unit landing (trace route primary per the
orchestrator addendum).
