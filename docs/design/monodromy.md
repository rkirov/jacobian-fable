# Design: monodromy (`Jacobian/Monodromy/`)

Blueprint unit **monodromy**. Blueprint text: "Global primitives on a simply-connected surface by
**discrete analytic continuation** along chains (no integration): local primitive frames, chain
values, homotopy invariance." Read: Forster §10.4 (PDF 76–77); Miranda Ch. IV §1. ⚠ "Prefer this
discrete route to anything requiring ∫ over paths on `X` as a primitive." Declared **Builds on:**
canonical-forms, sphere-topology.

One gated end spike (`scratch_mono.lean`, project root) compiled clean, 0 sorries — see §7.

---

## 0. Verdict up front

**This is a small unit, and the blueprint's literal ask is already fully discharged elsewhere.**
Forster 10.4/10.5's content — local primitives on disks, chain-of-charts continuation (no
integration), homotopy invariance, and the "simply connected ⇒ global primitive" theorem — is
**completely built** in `Jacobian/Path/{LocalPrimitive,Chain,Continuation,HomotopySquare}.lean`
and `Jacobian/SphereTopology/GlobalPrimitive.lean`. Both unit docstrings say so explicitly and in
detail (quoted in full in §1). There is **no remaining proof obligation** for the blueprint's own
stated content.

What remains is **not** "finish the blueprint's ask" but "notice what its real DAG consumer
(`abel-weak-solutions`) actually needs from Forster §20.1–20.4 and isn't covered yet": continuation
of **meromorphic** (not holomorphic) data along paths that avoid poles/zeros, in particular a
continuous branch of `log f` (equivalently: a primitive of `dlog f`) along such a path, with the
defining exponential compatibility `exp(F t) = f(γ t)`. That is genuinely new — nothing upstream
provides it — but it is a **small, self-contained** addition: **~350–450 lines across 2 load-bearing
files** plus a root file, reusing Path's entire per-path machinery *verbatim* (zero new
chain-continuation code) via one mathlib instance (open submanifolds) that resolves the design's
one real risk for free (§6.1, spike-verified §7).

**Also: one blueprint `Builds on` edge is spurious**, exactly the same class of slip
`proper-map-degree.md` and `sphere-topology.md` already flagged for their own entries (§1.3):
`canonical-forms` is *not* actually needed for the piece this unit's real consumer
(`abel-weak-solutions`) uses. See §1.3 for the DAG correction.

---

## 1. Gap analysis

### 1.1 What Forster 10.4/10.5 literally asks for — already built

Read at PDF 76–77 (book 70–71): **10.4** constructs a primitive on a disk by an explicit integral
formula (or, for holomorphic forms, Taylor-series antidifferentiation term-by-term); **10.5** then
says a primitive exists only *multi-valuedly* in general, precisely on a covering space
`p : X̃ → X`. The blueprint's own routing note says to avoid this covering-space route and instead
use "chain-of-charts continuation" (no integration, no covering space) — this is *exactly* what
`Jacobian/Path/` already built, and what `Jacobian/SphereTopology/` already specialized to the
simply-connected case:

| Forster content | Built at | Declaration(s) |
|---|---|---|
| Local primitive on a disk (10.4) | `Path/LocalPrimitive.lean`, `Path/Planar.lean` | `RS.isPrimitiveAlongMap_of_ball`, `RS.exists_hasDerivAt_ball` |
| Chain-of-charts continuation (10.4→10.5's construction, discretized) | `Path/Chain.lean`, `Path/Continuation.lean` | `RS.ChartChain`, `RS.exists_chartChain`, `RS.IsPrimitiveAlongMap`, `RS.exists_isPrimitiveAlong` |
| Homotopy invariance (replaces the covering-space monodromy argument) | `Path/HomotopySquare.lean` | `RS.exists_primitive_along_square`, `RS.pathIntegral_congr_homotopic`, `RS.pathIntegral_eq_of_simplyConnected`, `RS.period_eq_zero_of_homotopic_refl` |
| "Primitive along homotopic paths agree" (the literal monodromy theorem) | `Path/HomotopySquare.lean` | `RS.pathIntegral_congr_homotopic` |
| Global primitive on simply connected `X` (10.5's conclusion, without the covering space) | `SphereTopology/GlobalPrimitive.lean` | `RS.SphereTopology.exists_isPrimitiveAlongMap_id`, `RS.SphereTopology.contMDiff_and_mdifferential_eq_of_isPrimitiveAlongMap_id`, `RS.SphereTopology.form1_eq_zero_of_simplyConnectedSpace` |
| Perturbing a path off a finite bad set (needed to even *get* a pole-avoiding path) | `Path/Perturb.lean` | `RS.exists_homotopic_avoiding`, `RS.Loop.exists_homotopic_avoiding` |

`sphere-topology`'s own docstring (`docs/design/sphere-topology.md` §3.1, §8) is explicit that this
is a *deliberate* anticipation of monodromy's job: "The middle step ('`f` is holomorphic and
`df = η`') is *exactly* what the monodromy unit (#21) will later provide in general... monodromy
should feel free to either reuse `contMDiff_and_mdifferential_eq_of_isPrimitiveAlongMap_id`
verbatim... or re-derive it — they are not required to depend on this unit for it... **no design
incompatibility**." Verdict: **wrap/cite, do not re-prove.** See §4 for exactly how.

### 1.2 What `abel-weak-solutions` actually needs — read directly from Forster's proof text

Read at PDF 165–169 (book 159–163): Forster §20.1 defines a **weak solution** of a divisor `D`
(locally `f = ψ z^k` near each point, `k = D(a)`, `ψ` nonvanishing); §20.2 takes its **logarithmic
derivative** `df/f`, a smooth 1-form on the complement of `Supp(D)`; **Lemma 20.5** is the
construction abel-weak's blueprint text ("chain decompositions and piecewise-planar solutions...
staying in planar pieces glued by monodromy") is describing: given a curve `c` and a relatively
compact neighbourhood `U ⊇ c([0,1])`, build a weak solution `f` of `∂c` with `f ≡ 1` outside `U`,
satisfying `∫_c ω = (1/2πi)∬_X (df/f)∧ω`. Its proof:

1. **Single-chart case**: `c` lies in one chart-disk; with `a = c(0)`, `b = c(1)`, the function
   `(z−b)/(z−a)` is holomorphic and non-vanishing on the annulus `{r<|z|<1}` around `c([0,1])`
   (winding number `0`, since the enclosed zero at `b` and pole at `a` cancel — the argument
   principle). A **branch of its logarithm** on that annulus lets Forster build
   `f₀ := exp(ψ·log((z−b)/(z−a)))` — nonvanishing everywhere by construction (it is an `exp`), and
   interpolating from `(z−b)/(z−a)` (matching the required local `z^k` behaviour at `a`,`b`) to the
   constant `1` at the chart boundary via a smooth cutoff `ψ`.
2. **General case**: subdivide `c` into chart-disk pieces `c_1,…,c_n` (a `ChartChain` in this
   project's vocabulary — **already built**, `Path/Chain.lean`), build each `f_j` by step 1, and
   set `f := f_1⋯f_n` — a **pointwise product of already-globally-defined functions** (each `f_j`
   is already total on `X`, `≡1` outside its own chart neighbourhood), so the assembly across chain
   pieces needs **no further gluing/monodromy machinery**: it is literally `Set.prod`/pointwise
   multiplication, not primitive-continuation.

**What is genuinely reusable monodromy content here, pinned down precisely**: step 1's "branch of
`log((z−b)/(z−a))` on the annulus" is *itself* an instance of "continuation of a `dlog`-primitive
along a pole/zero-avoiding path", generalized so it degrades gracefully to the ad hoc annulus
picture. (Concretely: compactify the annulus's exterior region via `z ↦ 1/z` to a genuine disk
around `∞` containing neither `a` nor `b`; `(z−b)/(z−a)` is holomorphic and non-vanishing there,
including at `∞` where it is continuous with value `1` — so a log branch exists on this *simply
connected* domain by the same kind of "simply connected ⇒ nonvanishing holomorphic function has a
global log" fact that underlies `SphereTopology`'s engine, applied to `dlog` of that specific
function rather than to a general `Form1`. Equivalently and more simply: the winding-number-zero
computation is a residue computation, and *log-branch existence along a *specific* path/loop from
period-vanishing* is precisely the discrete-continuation content this unit is positioned to supply
as a reusable atom, sparing `abel-weak-solutions` from re-deriving it via Forster's own
annulus-plus-cutoff argument.) The clean, general, reusable form of this fact — a continuous branch
of `log f` along **any** path avoiding the zeros/poles of a **meromorphic function** `f`, with the
defining property `exp(F t) = f(γ t)` — is exactly what makes this atom usable regardless of which
specific construction `abel-weak-solutions`'s builder ultimately prefers for Lemma 20.5. That is
**item 2** below, and it is the one piece of genuinely new mathematics this unit contributes.

Two things Forster's proof does **not** need from a general theory: (a) it never needs a *global*
primitive of a meromorphic 1-form over all of `X` — only local, chart-by-chart branches, each
matched by hand at chart boundaries via a smooth cutoff; (b) the chain-assembly step (2 above) is
multiplicative pointwise product, not a monodromy-style gluing of local primitives. Both confirm
the unit's scope should stay small (§1.4, item 3).

### 1.3 DAG correction: `Builds on: canonical-forms` is not needed for the load-bearing piece

The blueprint's `Builds on: canonical-forms, sphere-topology` edge is only half right, for the same
reason `proper-map-degree.md` §2 and `sphere-topology.md` §8/§9 already flagged spurious
`Builds on: monodromy` edges elsewhere in the DAG:

1. `sphere-topology` is **citation-only** (§1.1/§4): its own docstring explicitly invites reuse
   *or* independent re-derivation, "no design incompatibility" either way. Fine as declared, but
   worth stating plainly: nothing here is *blocked* on it; a two-line re-derivation from
   `Path/Continuation.lean` alone would work identically if ever needed (which it isn't — §1.1's
   items are all reused by *citation*, not by new proof).
2. `canonical-forms` (the `MForm X` general meromorphic-1-form type) is **not built yet**
   (`Jacobian/CanonicalForms/` does not exist on disk) and, more importantly, **is not what
   `abel-weak-solutions`'s actual need (§1.2) requires**. Forster's Lemma 20.5 never differentiates
   an abstractly-typed meromorphic 1-form; the log-derivative `df/f` it needs is built directly
   from a **meromorphic function** `f : ℳ X` (already built, `Jacobian/Meromorphic/`) via
   `f.holoRepr`'s ordinary derivative and value — no `MForm` bundle, no canonical divisor `K`, no
   one-dimensionality machinery is ever consulted. Item 2 below is therefore built to depend on
   `meromorphic-and-divisors` **only** (already a complete, sorry-free unit), sidestepping the wait
   on `canonical-forms` entirely for the DAG-critical path.

   Item 1 (a **general** "continuation of primitives of an arbitrary `MForm X` along
   pole-avoiding paths") is designed below too, exactly as the task brief requests, and it *does*
   need `canonical-forms`'s frozen `MForm` interface — but no *currently designed* consumer needs
   it (abel-weak-solutions needs only the function-level `dlog` case, item 2). It is filed as an
   **optional, deferred** third file (§5), matching `canonical-forms.md`'s own D4 stance on its
   analogous `ord`-invariance corollary: "offered as a documented, non-blocking convenience...
   no currently-designed consumer is DAG-required to have it."

**Recommended DAG correction**: `monodromy`'s `Builds on:` line should read `meromorphic-and-divisors,
paths-and-integrals` (sphere-topology only as an optional citation), with `canonical-forms` moved to
an *optional* dependency consumed only if the deferred general-`MForm` file (§5) is ever built.

### 1.4 Gap analysis table

| Blueprint/brief ask | Status | Where |
|---|---|---|
| Local primitives on disks (10.4) | **Built** | `Path/Planar.lean`, `Path/LocalPrimitive.lean` |
| Chain-of-charts discrete continuation (10.4→10.5, no integration) | **Built** | `Path/Chain.lean`, `Path/Continuation.lean` |
| Homotopy invariance / "primitive along homotopic paths agree" | **Built** | `Path/HomotopySquare.lean` |
| Global primitive on simply connected `X` | **Built** | `SphereTopology/GlobalPrimitive.lean` |
| Loop/path perturbation off a finite bad set | **Built** | `Path/Perturb.lean` |
| Continuation of primitives of a **general `MForm`** along pole-avoiding paths (task item 1) | **Genuinely new, but not DAG-critical**; gated on unbuilt `canonical-forms` | Deferred, §5 |
| `dlog f`-continuation / log branches along paths with `exp`-compatibility (task item 2) | **Genuinely new and DAG-critical** | New, §4 |
| Chain-value/discrete-continuation bookkeeping beyond `Path/Chain` (task item 3) | **Not needed** — `ChartChain`/`exists_chartChain`/the whole `Continuation.lean` induction is already polymorphic over any manifold satisfying the standing hypotheses, hence reusable **verbatim** over the open pole-free locus (§6.1) | N/A |
| Explicit "already done, wrap don't reprove" list (task item 4) | This table + §1.1 | — |

---

## 2. What this unit re-exports/wraps rather than re-proves

Nothing in `Path/` or `SphereTopology/` is re-proved. The root file (§3, file 3) documents the
reuse explicitly; no code in this unit duplicates:

* `RS.IsPrimitiveAlongMap` and its whole API (`.mono/.add_const/.congr/.congr_map/.comp/.rechart/
  .sub_eq_sub/.glue`, `RS.isPrimitiveAlongMap_of_ball`) — used **as-is**, instantiated with
  `X := ` the open pole-free locus (§6.1), not reimplemented.
* `RS.ChartChain`/`RS.exists_chartChain`, `RS.exists_isPrimitiveAlong`, `RS.pathIntegral` — same,
  reused verbatim over the open locus.
* `RS.exists_primitive_along_square`/`RS.pathIntegral_congr_homotopic` — available for free over
  the open locus too, if `abel-weak-solutions` ever wants homotopy-invariance of a log branch
  (independence of the choice of pole-avoiding path up to a pole-avoiding homotopy); not built here
  since no current consumer asks for it, but flagged as a one-line corollary if needed (§4.4).
* `RS.SphereTopology.contMDiff_and_mdifferential_eq_of_isPrimitiveAlongMap_id` — cited, not
  reproved, in the (deferred, §5) discussion of what a *global* `MForm` primitive on a simply
  connected `X` would look like, should a future consumer want it.

---

## 3. File plan

| # | File | Content | Est. lines |
|---|------|---------|-----------|
| 1 | `Monodromy/OpenLocus.lean` | The relativization engine: open pole-free locus from a finite/closed bad set, automatic `ChartedSpace`/`IsManifold` instances (mathlib), path-lifting into the locus | ~110–150 |
| 2 | `Monodromy/LogContinuation.lean` | `dlogForm`, `exists_logBranchAlong`, the exponential-compatibility theorem — the DAG-critical deliverable for `abel-weak-solutions` | ~220–280 |
| 3 | `Jacobian/Monodromy.lean` | Unit root, API docstring, explicit "already done elsewhere" pointers | ~35–55 |

Total: **~365–485 lines**, a small unit. (A fourth, *deferred* file for the general-`MForm` case is
sketched in §5 but not costed into this total — build only if/when a consumer needs it.)

---

## 4. Exact signatures and proof plans

### 4.1 `Monodromy/OpenLocus.lean` — the open-submanifold relativization

```lean
import Jacobian.Path
import Mathlib.Geometry.Manifold.IsManifold.Basic

namespace RS.Monodromy

open scoped ContDiff Manifold
open TopologicalSpace Set

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The open locus determined by a closed "bad set" (in practice a divisor support). -/
def openLocus {S : Set X} (hS : IsClosed S) : Opens X := ⟨Sᶜ, hS.isOpen_compl⟩

/-- Finite bad sets are closed in a `T2Space` (`Set.Finite.isClosed`), hence give an open locus.
The standing surface is compact, so this is the case actually used (`(divisor f).support` is
finite by `finite_support_divisor`). -/
def openLocusOfFinite {S : Set X} (hS : S.Finite) : Opens X := openLocus hS.isClosed

/-- `ChartedSpace ℂ (openLocus hS)`: automatic (`TopologicalSpace.Opens.instChartedSpace`,
mathlib, `HasGroupoid.lean:270`) — no proof needed, `inferInstance` resolves it. -/
example {S : Set X} (hS : IsClosed S) : ChartedSpace ℂ (openLocus hS) := inferInstance

/-- `IsManifold 𝓘(ℂ) ω (openLocus hS)`: automatic (`TopologicalSpace.Opens`'s derived
`IsManifold` instance, mathlib, `IsManifold/Basic.lean:1020`) — no proof needed. -/
example {S : Set X} (hS : IsClosed S) : IsManifold 𝓘(ℂ) ω (openLocus hS) := inferInstance

/-- Lift a path of `X` whose whole range avoids `S` to a path in the open locus. -/
def Path.liftOpenLocus {S : Set X} (hS : IsClosed S) {x y : X} (γ : Path x y)
    (hγ : ∀ t : ↥unitInterval, γ t ∉ S) :
    Path (⟨x, γ.source ▸ hγ 0⟩ : openLocus hS) (⟨y, γ.target ▸ hγ 1⟩ : openLocus hS) where
  toFun t := ⟨γ t, hγ t⟩
  continuous_toFun := by fun_prop
  source' := by simp [γ.source]
  target' := by simp [γ.target]

/-- The lift's `extend` recovers `γ.extend` pointwise (needed to translate `IsPrimitiveAlong`
facts about the lift back into statements about `γ.extend`, `f.holoRepr`, etc.). -/
theorem Path.liftOpenLocus_extend {S : Set X} (hS : IsClosed S) {x y : X} (γ : Path x y)
    (hγ : ∀ t : ↥unitInterval, γ t ∉ S) (t : ℝ) :
    ((γ.liftOpenLocus hS hγ).extend t : X) = γ.extend t := ...  -- `IccExtend`/`projIcc` unfolding,
    -- routine (mirrors the `gridK_edge_fst/snd` style computations in `HomotopySquare.lean`)

end RS.Monodromy
```

No compactness/connectedness is assumed anywhere in this file — matching `Path`'s own convention
("No `T2Space`/`CompactSpace`/`ConnectedSpace` anywhere in this unit", `Jacobian/Path.lean`); the
open locus need not be connected or compact for Path's per-path/per-homotopy-square machinery to
apply (confirmed by inspection of `Path/{LocalPrimitive,Chain,Continuation,HomotopySquare}.lean`'s
own `variable` blocks — none of them ever assume it).

**Proof plan.** `openLocus`/`openLocusOfFinite`: one line each (`Set.Finite.isClosed` needs
`[T2Space X]`, already standing). The two `ChartedSpace`/`IsManifold` instances are *not*
declarations to prove — they are `inferInstance` and exist purely to record, in the design, that
this is where the risk resolves (spike-verified, §7). `Path.liftOpenLocus`: an anonymous-constructor
`Path`, continuity via `fun_prop` (`Continuous.subtype_mk` composed with `γ.continuous`, both
`fun_prop`-tagged) — spike-verified in miniature (§7, step 4). `liftOpenLocus_extend`: unfold both
sides' `IccExtend`/`projIcc` and note the subtype coercion commutes with `projIcc` (it doesn't touch
the real-number argument at all) — mechanical, ~10–15 lines, same shape as
`HomotopySquare.lean`'s `gridK_edge_fst`/`gridK_edge_snd`.

### 4.2 `Monodromy/LogContinuation.lean` — the deliverable

```lean
import Jacobian.Monodromy.OpenLocus
import Jacobian.Meromorphic

namespace RS.Monodromy

open scoped ContDiff Manifold
open Set Filter Topology IsManifold Metric

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The zero/pole locus of `f` as an open pole-free locus, via `finite_support_divisor`
(compactness) and `Set.Finite.isClosed` (`T2Space`). -/
noncomputable def poleZeroLocus (f : ℳ X) : TopologicalSpace.Opens X :=
  openLocusOfFinite (finite_support_divisor f)

/-- The log-derivative coefficient of `f`, read in the chart at `x` — built directly from
`ℳ X`'s already-built `holoRepr`/`ord` API, bypassing `MForm`/`canonical-forms` entirely (§1.3). -/
noncomputable def dlogCoeffAt (f : ℳ X) (x : X) (z : ℂ) : ℂ :=
  deriv (f.holoRepr ∘ (chartAt ℂ x).symm) z / f.holoRepr ((chartAt ℂ x).symm z)

/-- Off `f`'s zero/pole locus, `dlogCoeffAt f` assembles into a genuine holomorphic 1-form on the
pole/zero-free open locus, via `Form1CoeffData` over `chartAt`-balls shrunk to avoid the (finite)
bad set. -/
noncomputable def dlogForm (f : ℳ X) (hf : f ≠ 0) : RS.Form1 (poleZeroLocus f) := ...

/-- `dlogForm`'s coefficient in the (shrunk) chart at each point of the locus is `dlogCoeffAt f`,
matching the construction. -/
theorem coeffIn_dlogForm (f : ℳ X) (hf : f ≠ 0) (p : poleZeroLocus f) {z : ℂ}
    (hz : z ∈ (chartAt ℂ (p:X)).target) (hball : "z ranges within the shrunk ball at p") :
    RS.coeffIn (chartAt ℂ (p:X)) (dlogForm f hf) z = dlogCoeffAt f p z := ...
    -- via `Form1.coeffIn_ofCoeffs`, restricted to the shrunk ball's target

/-- **The exponential-compatibility theorem.** Any primitive of `dlogForm f hf` along a pole/zero-
avoiding path, normalized so that `exp (F 0) = f.holoRepr x`, is an honest continuous branch of
`log f` along the path: `exp (F t) = f.holoRepr (γ.extend t)` for every `t`. -/
theorem exp_eq_holoRepr_of_isPrimitiveAlong {f : ℳ X} (hf : f ≠ 0) {x y : X} {γ : Path x y}
    (hγ : ∀ t : ↥unitInterval, γ t ∉ (divisor f).support) {F : ℝ → ℂ}
    (hF : RS.IsPrimitiveAlong (γ.liftOpenLocus (finite_support_divisor f).isClosed hγ)
      (dlogForm f hf) F)
    (hc₀ : Complex.exp (F 0) = f.holoRepr x) :
    ∀ t : ℝ, Complex.exp (F t) = f.holoRepr (γ.extend t)

/-- **Existence**, with a prescribed initial branch value: a continuous branch of `log f` along
any path avoiding the zeros/poles of `f`, starting at a chosen `c₀` with `exp c₀ = f.holoRepr x`. -/
theorem exists_logBranchAlong {f : ℳ X} (hf : f ≠ 0) {x y : X} (γ : Path x y)
    (hγ : ∀ t : ↥unitInterval, γ t ∉ (divisor f).support) {c₀ : ℂ}
    (hc₀ : Complex.exp c₀ = f.holoRepr x) :
    ∃ F : ℝ → ℂ, RS.IsPrimitiveAlong (γ.liftOpenLocus (finite_support_divisor f).isClosed hγ)
      (dlogForm f hf) F ∧ F 0 = c₀ ∧ ∀ t : ℝ, Complex.exp (F t) = f.holoRepr (γ.extend t)

/-- **Uniqueness** (free, from `Path`'s own `sub_eq_sub`): two branches agreeing at `t = 0` agree
everywhere — no new proof, a direct instantiation over the open locus. -/
theorem logBranchAlong_unique {f : ℳ X} (hf : f ≠ 0) {x y : X} {γ : Path x y}
    {hγ : ∀ t : ↥unitInterval, γ t ∉ (divisor f).support} {F F' : ℝ → ℂ}
    (hF : RS.IsPrimitiveAlong (γ.liftOpenLocus (finite_support_divisor f).isClosed hγ)
      (dlogForm f hf) F)
    (hF' : RS.IsPrimitiveAlong (γ.liftOpenLocus (finite_support_divisor f).isClosed hγ)
      (dlogForm f hf) F')
    (h0 : F 0 = F' 0) : F = F' := ...
    -- `funext t; linear_combination (hF.sub_eq_sub isPreconnected_univ _ hF' (mem_univ 0)
    --   (mem_univ t)); rw [h0]` — literally `IsPrimitiveAlongMap.sub_eq_sub`, already built.

end RS.Monodromy
```

**Proof plans.**

*`dlogForm` (the one substantial new construction, ~80–120 lines).* For each point `p` of the
pole/zero-free locus (`p ∉ (divisor f).support`, i.e. `f.ord p = 0`): let `e_p := chartAt ℂ (p:X)`,
`z₀ := e_p p`.

1. `f.ord p = 0` gives, via `MeroGermOn.holoRepr_contMDiffAt isOpen_univ (mem_univ p) (le_of_eq
   rfl : (0:WithTop ℤ) ≤ f.ord p)`, that `f.holoRepr` is `ContMDiffAt` at `p`, hence (via
   `contMDiffAt_iff_analyticAt_comp_chartAt`, already used identically in
   `SphereTopology/GlobalPrimitive.lean`'s own proof of
   `contMDiff_and_mdifferential_eq_of_isPrimitiveAlongMap_id`) `AnalyticAt ℂ (f.holoRepr ∘ e_p.symm)
   z₀`.
2. `f.ord p = 0` (not merely `≥ 0`) additionally gives `f.holoRepr p ≠ 0` — a standard
   order-zero-iff-nonvanishing fact for meromorphic functions (mathlib,
   `Mathlib/Analysis/Meromorphic/Order.lean`; exact lemma name to pin at build time, low risk,
   flagged §6.3 R1).
3. Analyticity + continuity + nonvanishing at `z₀`, all open conditions, give a ball `ball z₀ r ⊆
   e_p.target` on which `f.holoRepr ∘ e_p.symm` is analytic and non-vanishing throughout (shrink `r`
   by continuity of the two open predicates, exactly the `Metric.isOpen_iff.mp`/`eventually_nhds_iff_
   ball` pattern already used pervasively in `Path/Continuation.lean` and
   `SphereTopology/GlobalPrimitive.lean`).
4. On that ball, `dlogCoeffAt f p := deriv (f.holoRepr∘e_p.symm) / (f.holoRepr∘e_p.symm)` is
   analytic (quotient of analytic functions, denominator non-vanishing).
5. Assemble a `Form1CoeffData (poleZeroLocus f) (poleZeroLocus f)` with `chart p := (chartAt ℂ
   (p:X)).restr (e_p.source ∩ e_p ⁻¹' ball z₀ r_p)` (restricted to the shrunk ball, staying in
   `maximalAtlas` via mathlib's `restr_mem_maximalAtlas (contDiffGroupoid ω 𝓘(ℂ))` — the **exact**
   technique `Jacobian/Forms/Finiteness.lean` already uses for its own shrunk-cover charts,
   `Finiteness.lean:403-404`) and `coeff p := dlogCoeffAt f p`. `exists_mem`: trivial, `p` is in its
   own chart's (shrunk) source. `analyticOnNhd`: step 4, restricted to the (smaller) restricted
   target. `compat`: the transition rule for a log-derivative under a biholomorphic chart change is
   *exactly* the CC1 transition rule (chain rule: `(f∘τ)'/(f∘τ) = τ'·((f'/f)∘τ)` for a chart
   transition `τ`) — mechanically identical in shape to `Form1CoeffData.compat`'s own defining
   equation and to `IsPrimitiveAlongMap.rechart`'s internal `coeffIn_trans`-style computation
   already proved in this codebase; ~30–50 lines, no new mathematical idea.
6. `dlogForm f hf := Form1.ofCoeffs (that data)`.

*`exp_eq_holoRepr_of_isPrimitiveAlong` (the exponential-compatibility theorem, ~50–90 lines,
the mathematical heart of this unit).* Set `H : ℝ → ℂ := fun t => f.holoRepr (γ.extend t) *
Complex.exp (-(F t))`. Claim `H` is locally constant (`IsLocallyConstant`, or directly
`∀ t₀, ∀ᶠ t in 𝓝 t₀, H t = H t₀`):

1. Unfold `hF t₀ (mem_univ t₀)`, then **`.rechart`** (already built,
   `IsPrimitiveAlongMap.rechart`) to move the local primitive data into the *preferred* chart
   `chartAt ℂ (γ.extend t₀ : X)` restricted to `dlogForm`'s own shrunk ball there — at which point,
   by `coeffIn_dlogForm` (item above), the local primitive's derivative data is *literally*
   `dlogCoeffAt f (γ.extend t₀)`, i.e. `deriv(f.holoRepr∘e.symm)/(f.holoRepr∘e.symm)` for `e` that
   chart.
2. On the ball, set `φ(w) := f.holoRepr(e.symm w) * Complex.exp(-(g w))` where `g` is the local
   primitive; compute `HasDerivAt φ 0 w` for every `w` in the ball via the product/chain rule
   (`(f.holoRepr∘e.symm)'(w)·exp(−g w) − f.holoRepr(e.symm w)·g'(w)·exp(−g w)`, and
   `f.holoRepr(e.symm w)·g'(w) = (f.holoRepr∘e.symm)'(w)` exactly by construction of `g`'s
   derivative data — the bracket vanishes identically).
3. `φ` has zero derivative on a ball (convex, connected) ⇒ `φ` is constant there — *exactly* the
   `is_const_of_fderivWithin_eq_zero` pattern **already proved** in `Path/Planar.lean`'s
   `eventuallyEq_of_hasDerivAt_eq` (reuse the same convexity/derivative-zero argument, not the
   lemma itself, since the target here is a plain equality of values, not an `EventuallyEq`).
4. Composing with continuity of `t ↦ e(γ.extend t)` transports this to: `H` is eventually equal to
   the constant `H t₀` near `t₀` — done, for every `t₀`.

`ℝ` is preconnected, so a locally-constant function on it is constant
(`IsLocallyConstant.apply_eq_of_preconnectedSpace`, **already used** for exactly this purpose in
`IsPrimitiveAlongMap.sub_eq_sub`, `Path/LocalPrimitive.lean:182-183`). Hence `H t = H 0` for all
`t`. Finally `H 0 = f.holoRepr(x)·exp(−F 0) = f.holoRepr(x)/exp(F 0) = f.holoRepr(x)/f.holoRepr(x)
= 1` (using `hc₀`, and `f.holoRepr x ≠ 0` since `exp(F 0) = f.holoRepr x` and `exp` never
vanishes), so `H ≡ 1`, i.e. `f.holoRepr(γ.extend t) = exp(F t)` for every `t`.

**No branch-cut bookkeeping anywhere**: this proof never invokes `Complex.log`'s principal branch
or any case split on `Complex.arg`; it establishes the exponential identity directly from the
defining ODE, sidestepping branch cuts entirely (unlike Forster's own ad hoc annulus-log-branch
argument, §1.2, which this unit's `dlog`-continuation atom is designed to make unnecessary for
`abel-weak-solutions` to re-derive by hand).

*`exists_logBranchAlong`/`logBranchAlong_unique`*: existence is `RS.exists_isPrimitiveAlong` (built,
gives `F 0 = 0`) shifted by `.add_const c₀` (built, `IsPrimitiveAlongMap.add_const`) to hit the
prescribed `F 0 = c₀`, then `exp_eq_holoRepr_of_isPrimitiveAlong` applied to the shifted primitive;
uniqueness is a direct citation of `IsPrimitiveAlongMap.sub_eq_sub`. Neither needs new mathematical
content — bookkeeping only, ~30–40 lines combined.

### 4.3 What `abel-weak-solutions` gets

`RS.Monodromy.exists_logBranchAlong`/`RS.Monodromy.exp_eq_holoRepr_of_isPrimitiveAlong` give it a
continuous, honestly-`exp`-compatible branch of `log f` along *any* path it can produce that avoids
`f`'s zeros/poles — whether it builds that path via Forster's own annulus-plus-cutoff picture, via
`Path/Perturb.lean`'s `exists_homotopic_avoiding` (perturb an arbitrary chain off the finite bad set
`(divisor f).support`, already built), or some other route. It does **not** need to re-derive the
winding-number/log-branch existence argument itself.

### 4.4 Optional bonus (not built, one-line corollary if ever requested)

Homotopy-invariance of a log branch — "two pole/zero-avoiding paths homotopic through
pole/zero-avoiding homotopies give the same branch up to the initial choice" — is available for
free by reusing `RS.pathIntegral_congr_homotopic`/`RS.exists_primitive_along_square` over the open
locus exactly as in §6.1, composed with `exp_eq_holoRepr_of_isPrimitiveAlong`. Not built since no
current consumer asks for it (§1.4); flagged here so a future builder does not re-derive it from
scratch.

---

## 5. Deferred: the general `MForm`-relativization (task item 1, full generality)

Not built now (§1.3: no current DAG consumer needs it; `canonical-forms`/`MForm X` does not exist
on disk yet). Sketch, for a future continuation builder, once `canonical-forms` lands:

```lean
/-- Given `ω : MForm X` with no poles on the open locus `s` (i.e. `∀ p : s, 0 ≤ ω.ord (p:X)`),
`ω` restricts to a genuine holomorphic `Form1 s`. -/
noncomputable def MForm.restrictToOpenLocus {s : TopologicalSpace.Opens X} (ω : MForm X)
    (hpole : ∀ p : s, 0 ≤ ω.ord (p:X)) : RS.Form1 s
```

**Proof plan**: identical technique to `dlogForm` above (§4.2 step-by-step), with `ω.coeffAt p`
in place of `dlogCoeffAt f p` at every step: analyticity of `ω.coeffAt p` near `chartAt ℂ p p`
follows from `ω.ord p ≥ 0` via the same "meromorphic order ≥ 0 at a point propagates to
analyticity on a full neighbourhood" fact canonical-forms's own `divisor`/local-finiteness proof
(D6) is planned to establish for itself (`eventually_ord_eq_zero`, mirroring `Divisor.lean`'s
already-built `eventually_ord_eq_zero` for `ℳ X`) — cite that corollary rather than re-derive it;
if it is not yet exported when this file is built, file a one-paragraph request in
`docs/requests/canonical-forms.md` per `CONVENTIONS.md` rule 4 (it is a two-line consequence of
`MeromorphicOn`'s order theory, not a design risk). The `Form1CoeffData` assembly (shrunk
`chartAt`-restricted balls, `restr_mem_maximalAtlas`, the CC1-shaped `compat` computation) is
**line-for-line the same recipe** as `dlogForm`'s — so if this file is ever built, the honest move
is to *factor* the shared "assemble a `Form1` on an open locus from a per-point analytic-near-`p`
coefficient family" helper out of `LogContinuation.lean` into `OpenLocus.lean`, rather than
duplicate it. Not done now to avoid speculative refactoring of code with no current caller.

Estimated size if built: ~100–150 lines, entirely mechanical given the above once `canonical-forms`
lands. **Not counted in this design's line total (§3).**

---

## 6. Risks

### 6.1 The one real design risk — resolved, spike-verified

The task brief's central open question was whether Path's machinery is already "`U`-polymorphic"
or needs a wrapper layer. **Resolved: no wrapper needed.** `Path/{LocalPrimitive,Chain,Continuation,
HomotopySquare}.lean` are *already* stated for a fully generic `X` satisfying only
`[TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]` — no compactness, connectedness, or
`T2Space` anywhere in their signatures (confirmed by direct inspection, and stated explicitly in
`Jacobian/Path.lean`'s own docstring). Mathlib already gives an open subset of a charted
space/manifold the *same* instances for free: `TopologicalSpace.Opens.instChartedSpace`
(`HasGroupoid.lean:270`) and the derived `instance : IsManifold I n s` for opens
(`IsManifold/Basic.lean:1020`, taking `{ s.instHasGroupoid (contDiffGroupoid n I) with }`). So the
open pole-free locus `s := openLocus hS` is, *with zero new proof*, an instance of exactly the same
`X`-shaped standing hypotheses Path's declarations are already stated over — every one of
`IsPrimitiveAlongMap`, `exists_isPrimitiveAlong`, `pathIntegral`, `pathIntegral_congr_homotopic`
etc. applies to it **by direct instantiation**, term-for-term, with no restatement. This was
spike-verified (§7): `RS.exists_isPrimitiveAlong`/`RS.pathIntegral_congr_homotopic`, applied with
`X := s hS`, type-check and compile with zero modification.

### 6.2 The order-zero ⇒ nonvanishing lemma name (LOW)

`dlogForm`'s step 2 (§4.2) needs "meromorphic order exactly `0` at a point ⇒ the (already known
analytic) representative is nonzero there" — a standard fact, but its exact mathlib name in
`Mathlib/Analysis/Meromorphic/Order.lean` was not pinned during this design (the design read
confirmed the *adjacent* facts `AnalyticAt.meromorphicOrderAt_nonneg`/`MeromorphicAt.analyticAt`
exist at that file, but not the precise order-zero-iff-nonvanishing statement by name). **Action
for the builder**: `grep -n "order.*zero\|zero.*order" Mathlib/Analysis/Meromorphic/*.lean` before
writing `dlogForm`; if genuinely absent, it is a two-line consequence of
`meromorphicOrderAt_eq_zero_iff`/the local `(z-z₀)^n • g` normal form already used pervasively in
this project's own `Jacobian/Meromorphic/OrderEval.lean` (`ord_mk`, `holoRepr_contMDiffAt`'s own
proof) — prove it locally in a `Compat` section per `CONVENTIONS.md` rule 4 if missing.

### 6.3 `MeroGermOn.holoRepr_contMDiffAt`'s exact hypothesis shape (LOW)

§4.2 step 1 cites `holoRepr_contMDiffAt (hU : IsOpen U) (hx : x ∈ U) (h : 0 ≤ φ.ord x)` — verified
present at `Jacobian/Meromorphic/OrderEval.lean:247` by direct read; only the specific instantiation
`U := Set.univ`/`hU := isOpen_univ` needs checking against `ℳ X := MeroGermOn X Set.univ`'s
definitional unfolding at build time (mechanical, `abbrev`-transparent per `GermSpace.lean`'s own
docstring).

### 6.4 Multi-builder churn (MEDIUM, standard)

This is a concurrently-built repository; re-verify every cited upstream name/signature immediately
before writing code that depends on it, per the same standing caution `proper-map-degree.md` §5
item 2 and `sphere-topology.md` R1/R5 record for their own designs. In particular: re-confirm
`ℳ X`'s exact API (`holoRepr`, `ord`, `divisor`, `finite_support_divisor`) is unchanged, and check
whether `Jacobian/CanonicalForms/` has appeared on disk (if so, §5's deferred file becomes
buildable, but is still not required for `LogContinuation.lean`).

---

## 7. Spike report (`scratch_mono.lean`, project root)

Gate respected (`pgrep -cx lean` < 3 at run time; 0 concurrent `lean` jobs observed). `lake env lean
scratch_mono.lean`: **compiles clean, exit 0, zero sorries.** Content (≤ 40 lines): for a generic
`X` with the (non-compact-non-connected) standing hypotheses and a finite `S : Set X`,

1. `IsOpen Sᶜ` from `hS.isClosed.isOpen_compl` (`Set.Finite.isClosed` in a `[T2Space X]`).
2. `s := (⟨Sᶜ, ...⟩ : TopologicalSpace.Opens X)`; `ChartedSpace ℂ s`/`IsManifold 𝓘(ℂ) ω s` both
   resolve via bare `inferInstance` (`noncomputable section` needed — the mathlib instances are
   themselves noncomputable, unsurprising, no other issue).
3. `RS.exists_isPrimitiveAlong` and `RS.pathIntegral_congr_homotopic`, applied with `X := s`
   directly (`γ : Path x y` for `x y : s`, `η : RS.Form1 s`) — **type-check and compile with no
   modification whatsoever** to `Path`'s own declarations. This is the load-bearing confirmation of
   §6.1.
4. Lifting a pole-avoiding continuous map `γ : C(↥unitInterval, X)` (with `∀ t, γ t ∈ Sᶜ`) into `s`
   via `fun t => (⟨γ t, h t⟩ : s)` is `Continuous` by a bare `fun_prop` call — confirms
   `Path.liftOpenLocus`'s continuity proof (§4.1) is routine.

All four items compiled with zero sorries, zero new lemmas beyond `inferInstance`/`fun_prop`/one
`Set.Finite.isClosed` citation — the strongest possible confirmation that no wrapper layer over
`Path` is needed.

---

## 8. Downstream map

| Consumer | What it needs | Our export |
|---|---|---|
| **abel-weak-solutions** (#24, primary) | A continuous branch of `log f` (`dlog f`-primitive) along a path avoiding `f`'s zeros/poles, with `exp`-compatibility, to build Forster 20.5's weak-solution pieces without re-deriving the annulus/winding-number argument by hand | `RS.Monodromy.exists_logBranchAlong`, `RS.Monodromy.exp_eq_holoRepr_of_isPrimitiveAlong`, `RS.Monodromy.logBranchAlong_unique` |
| **period-lattice-rank** (#31) | No *direct* edge — the blueprint's own DAG has `period-lattice-rank: Builds on abel-theorem` only, which in turn builds on `abel-weak-solutions`/`cech-h1-genus`. Any relevance to this unit is purely transitive, through `abel-weak-solutions` | — (no direct export) |
| **proper-map-degree** | None — the blueprint's `Builds on: monodromy` edge for this unit is spurious, already confirmed and filed by `proper-map-degree.md` §2 itself (built with zero monodromy dependency) | — |
| **sphere-topology** | None (upstream of us, citation-only in the other direction, §1.1/§4) | — |

No other unit needs anything from `monodromy` per the current blueprint edges (§1.3).
