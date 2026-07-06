# Requests to abel-theorem (#29)

## From period-lattice-rank (design: `docs/design/period-lattice-rank.md` §7) — LOAD-BEARING

Forster 21.4(b) (discreteness of the period lattice) consumes Abel's theorem's **sufficiency
direction for an n-point divisor** (n ≤ g in the application, but nothing is saved by bounding n).
The blueprint blurb for abel-theorem emphasizes the two-point application (`ofCurve_inj`); please
also export the general statement — Forster's 20.7(⇐) proof is uniform in the divisor, so this
should be the natural intermediate anyway. **A two-point-only Abel does not suffice for
period-lattice-rank.**

Statement consumed (any equivalent formulation is fine, see the flexibility notes below):

```lean
-- standing surface variables; P₀ := Classical.arbitrary X (the periodSubgroup basepoint)
theorem abel_sufficiency {n : ℕ} {a x : Fin n → X} (σ : ∀ j, Path (a j) (x j))
    (γ : Path (Classical.arbitrary X) (Classical.arbitrary X))
    (h : ∀ η : Form1 X, ∑ j, pathIntegral (σ j) η = period γ η) :
    ∃ f : ℳ X, f ≠ 0 ∧ RS.divisor f
      = ∑ j, (Function.locallyFinsuppWithin.single (x j) 1
              - Function.locallyFinsuppWithin.single (a j) 1)
```

Flexibility (what period-lattice-rank can cheaply bridge on its side):
1. The hypothesis may quantify over `basis X i` only instead of all `η : Form1 X` (equivalent by
   `pathIntegralₗ` linearity), or be phrased via `periodVector`.
2. The loop `γ` may be based anywhere if you prefer, provided a conjugation lemma is exported
   (`period_conj` exists in paths-and-integrals).
3. Chains: if #29 introduces a 1-chain carrier (list/finsupp of paths), a statement in that
   vocabulary is fine as long as a finite family of `Path (a j) (x j)` plus one based loop can be
   assembled into it and the divisor of the chain is the alternating `single`-sum above.
4. Repeated/coincident points must be allowed: in the application some `x j = a j` may occur
   (their divisor contributions cancel), and the same point is never both an `a`- and `x`-point
   for different `j` (period-lattice-rank arranges pairwise-disjoint chart neighborhoods), but the
   statement should not *require* such disjointness.
5. Conclusion: any junk-free formulation of "`f` is a nonzero meromorphic function with divisor
   exactly `D`" works (e.g. via `RS.divisor f = D` as above, or ord-wise `∀ p, f.ord p = D p`).

Consumed at exactly one site (`PeriodLattice/Discreteness.lean`, Stage C.3). Everything else in
period-lattice-rank is independent of #29, so a late-landing `abel_sufficiency` only blocks the
final discreteness lemma, not the unit's build-out.
