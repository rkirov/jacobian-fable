import Jacobian.Cech.Covers
import Jacobian.Cech.Cochains
import Jacobian.Cech.H0
import Jacobian.Cech.Refinement
import Jacobian.Cech.Colimit
import Jacobian.Cech.Window
import Jacobian.Cech.Skyscraper

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
* **Window** (`Window.lean`): `ordGe`/`tailGerm`/`leadCoeff`, `WindowAt`/`Window` (the abstract
  skyscraper data), `windowMap` and its exactness/injectivity against `L(D)`/`L(D')`.
* **Skyscraper** (`Skyscraper.lean`): the Mittag-Leffler atom `mlClass` (`C1.MemLD`/`C1.retype`),
  its linearity and `D`-functoriality, and the vanishing criterion
  `mlClass_eq_zero_of_exists`.

**Known gaps** (documented in-file, not silently dropped): `resH1_injective`/`toH1_injective`
(Forster 12.4) and `finrank_windowAt`/`finrank_window` (the `θ`-basis dimension count) are not
proved in this unit — see `Refinement.lean`'s and `Window.lean`'s file-end notes. The full
six-term skyscraper exactness (`windowConnect`, `exists_realization`, Lemma A) is recorded as an
interface in `Skyscraper.lean`'s docstring, not proved. Every other export above is proved with
zero sorries.
-/
