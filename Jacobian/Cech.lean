import Jacobian.Cech.Covers
import Jacobian.Cech.Cochains
import Jacobian.Cech.H0
import Jacobian.Cech.Refinement
import Jacobian.Cech.Colimit
import Jacobian.Cech.Injectivity
import Jacobian.Cech.Window
import Jacobian.Cech.WindowRank
import Jacobian.Cech.Skyscraper
import Jacobian.Cech.SixTerm

/-!
# cech-cohomology (CC8): `H¹(D)` as a directed colimit over finite covers (namespace `RS.Cech`)

API summary (see `docs/design/cech-cohomology.md`):

* **Covers** (`Covers.lean`): `FinCover Ω` (`Fin n`-indexed opens covering `Ω`), the refinement
  `Preorder`/`IsDirectedOrder`, `IsChartDisk`/`FinCover.IsGood` (cofinal good covers,
  `exists_good_refinement(_closure)`), `FinCover.IsAdapted` (`exists_adapted_refinement`).
* **Cochains** (`Cochains.lean`): `LinSysOn.restrictL`, `C0`/`C1`/`C2` (full-product convention),
  `d0`/`d1`, `Z1`/`B1`/`H1Cover` (cover-level Čech `H¹(𝒰,D)`), `MeroGermOn.congrSet` [Compat].
* **`H⁰`** (`H0.lean`): `h0EquivLinSysOn`/`h0Equiv` — `H⁰(𝒰,D) ≃ L(D)` via sheaf gluing.
* **Refinement** (`Refinement.lean`): `resC0`/`resC1`/`resZ1`/`resH1`, the cocycle-relation
  workhorse `Z1.rel_res`, **Forster 12.3** (`resH1_indep`) and the functor laws
  (`resH1_id`/`resH1_comp`) that make `H1Cover` a `DirectedSystem`.
* **Colimit** (`Colimit.lean`): **`H1 D`**, the directed colimit (CC8, frozen), `toH1`,
  `exists_rep(_good/_refined)`, `H1.induction_on`, `H1.lift` (universal property),
  `H1Incl` (`D`-monotone functoriality) with `H1Incl_id`/`H1Incl_comp`.
* **Injectivity** (`Injectivity.lean`): **Forster 12.4** — `resH1_injective` (sheaf-axiom
  gluing argument via `injPatch`/`exists_injGlue`), `toH1_injective`/`toH1_eq_zero_iff`,
  `subsingleton_H1_iff`.
* **Window** (`Window.lean`): `ordGe`/`tailGerm`/`leadCoeff`, `WindowAt`/`Window` (the abstract
  skyscraper data), `windowMap` and its exactness/injectivity against `L(D)`/`L(D')`.
* **WindowRank** (`WindowRank.lean`): the `θ`-basis dimension counts `finrank_windowAt`
  (via an explicit one-step splitting `WindowAt p d d' ≃ₗ WindowAt p d (d'-1) × ℂ`, no
  independence/spanning argument) and `finrank_window`, plus the `FiniteDimensional` instances.
* **Skyscraper** (`Skyscraper.lean`): the Mittag-Leffler atom `mlClass` (`C1.MemLD`/`C1.retype`),
  its linearity and `D`-functoriality, and the vanishing criterion `mlClass_eq_zero_iff`
  (both directions — the `⇒` half uses `toH1_injective`).
* **SixTerm** (`SixTerm.lean`): part (g) of the six-term skyscraper fragment —
  `H1Incl_surjective` (no `H²`, no long exact sequence, no snake lemma), via `memLD_of_isAdapted`
  + the general retype lemmas `C1.retype_mem_Z1'`/`h1CoverIncl_mk_retype`.

**Known gap** (documented in-file, not silently dropped): the connecting map `windowConnect`,
`exists_realization`, Lemma A, and the two exactness statements `exact_windowMap_windowConnect`/
`exact_windowConnect_H1Incl` (design §6.9(c)-(f)) are **not proved in this unit** — see
`Skyscraper.lean`'s file-end note. They need adapted-cover *realization* machinery beyond this
unit's time budget; `H1Incl_surjective` (part (g), the fragment's last arrow) **is** proved, and
does not depend on them. Every other export above (including Forster 12.4 injectivity and the
window dimension counts, both previously deferred) is proved with zero sorries.
-/
