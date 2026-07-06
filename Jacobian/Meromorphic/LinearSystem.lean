import Jacobian.Meromorphic.Divisor
import Mathlib.Geometry.Manifold.Complex

/-!
# The linear system `L(D)` and `l(D)` (CC3, D4)

Unit: meromorphic-and-divisors (`docs/design/meromorphic-and-divisors.md` §4.7, D4, proof plan §6.7).

* `LinSys D : Submodule ℂ (ℳ X)` (D4's carrier: the `ord` inequality, no case split; `0 ∈ L(D)`
  by `⊤`-arithmetic). `mem_linSys_iff_eq_zero_or_le_divisor` recovers CC3's frozen disjunction as
  a *theorem* on a connected surface.
* `l D := Module.finrank ℂ (LinSys D)`.
* `linSys_zero_eq_span_one`/`l_zero` (Liouville), vanishing lemmas
  (`linSys_eq_bot_of_nonpos_of_ne_zero`), the conditional `linSys_eq_bot_of_degree_neg`, and
  `linSysMulEquiv` (linear equivalence under multiplication by a nonzero class).
* `LinSysOn D U` (relative version, Čech cochain spaces), `restrict_mem_linSysOn`,
  `mem_linSys_iff_forall_restrict` (bookkeeping toward `H⁰(𝔘, O_D) = L(D)`).
-/

open scoped ContDiff Manifold
open Set Filter Topology

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {U V : Set X} {D E : Divisor X} {c : ℂ}

/-! ### Pointwise arithmetic on `Divisor X` (Compat helpers) -/

theorem Divisor.add_apply (D E : Divisor X) (x : X) : (D + E) x = D x + E x :=
  congrFun (Function.locallyFinsuppWithin.coe_add D E) x

theorem Divisor.neg_apply (D : Divisor X) (x : X) : (-D) x = -(D x) :=
  congrFun (Function.locallyFinsuppWithin.coe_neg D) x

theorem Divisor.sub_apply (D E : Divisor X) (x : X) : (D - E) x = D x - E x :=
  congrFun (Function.locallyFinsuppWithin.coe_sub D E) x

variable [T1Space X] [IsManifold 𝓘(ℂ) ω X]

/-! ### `LinSys D` -/

/-- CC3's `L(D)` (carrier per D4; `0 ∈ L(D)` by `⊤`-arithmetic, not fiat). -/
noncomputable def LinSys (D : Divisor X) : Submodule ℂ (ℳ X) where
  carrier := {φ | ∀ x, ((-(D x) : ℤ) : WithTop ℤ) ≤ φ.ord x}
  zero_mem' := by
    intro x
    rw [MeroGermOn.ord_zero, if_pos ⟨isOpen_univ, mem_univ x⟩]
    exact le_top
  add_mem' := by
    intro φ ψ hφ hψ x
    exact le_trans (le_min (hφ x) (hψ x)) (MeroGermOn.ord_add isOpen_univ (mem_univ x) φ ψ)
  smul_mem' := by
    intro a φ hφ x
    rcases eq_or_ne a 0 with rfl | ha
    · rw [zero_smul, MeroGermOn.ord_zero, if_pos ⟨isOpen_univ, mem_univ x⟩]
      exact le_top
    · rw [MeroGermOn.ord_smul isOpen_univ (mem_univ x) ha]
      exact hφ x

theorem mem_linSys_iff {φ : ℳ X} : φ ∈ LinSys D ↔ ∀ x, ((-(D x) : ℤ) : WithTop ℤ) ≤ φ.ord x :=
  Iff.rfl

/-- CC3's frozen shape, recovered as a characterization on connected `X`. -/
theorem mem_linSys_iff_eq_zero_or_le_divisor [ConnectedSpace X] {φ : ℳ X} :
    φ ∈ LinSys D ↔ φ = 0 ∨ -D ≤ divisor φ := by
  rw [mem_linSys_iff]
  constructor
  · intro hmem
    by_cases hφ : φ = 0
    · exact Or.inl hφ
    · refine Or.inr (Function.locallyFinsuppWithin.le_def.2 fun x => ?_)
      rw [Divisor.neg_apply, divisor_apply]
      have hne : ((-(D x) : ℤ) : WithTop ℤ) ≠ ⊤ := WithTop.coe_ne_top
      exact WithTop.untop₀_le_untop₀ (Mero.ord_ne_top hφ x) (hmem x)
  · rintro (rfl | hle) x
    · rw [MeroGermOn.ord_zero, if_pos ⟨isOpen_univ, mem_univ x⟩]; exact le_top
    · have h := Function.locallyFinsuppWithin.le_def.1 hle x
      rw [Divisor.neg_apply, divisor_apply] at h
      calc ((-(D x) : ℤ) : WithTop ℤ)
          = (((-D) x : ℤ) : WithTop ℤ) := by rw [Divisor.neg_apply]
        _ ≤ ((divisor φ x : ℤ) : WithTop ℤ) := by exact_mod_cast h
        _ = φ.ord x := WithTop.coe_untop₀_of_ne_top (Mero.ord_ne_top (by
            rintro rfl
            simp only [divisor_apply, MeroGermOn.ord_zero, if_pos ⟨isOpen_univ, mem_univ x⟩,
              WithTop.untop₀_top] at h
            omega) x)

/-- CC3: `l D`. Finiteness is NOT this unit's business (Čech/finiteness proves
`FiniteDimensional`); until then `finrank` junk-returns `0` on infinite-dimensional spaces — no
lemma here depends on finiteness. -/
noncomputable def l (D : Divisor X) : ℕ := Module.finrank ℂ (LinSys D)

theorem linSys_mono (h : D ≤ E) : LinSys D ≤ LinSys E := by
  intro φ hφ x
  refine le_trans ?_ (hφ x)
  have := Function.locallyFinsuppWithin.le_def.1 h x
  exact_mod_cast neg_le_neg this

theorem one_mem_linSys_iff : (1 : ℳ X) ∈ LinSys D ↔ 0 ≤ D := by
  rw [mem_linSys_iff]
  constructor
  · intro h
    rw [Function.locallyFinsuppWithin.le_def]
    intro x
    have := h x
    rw [MeroGermOn.ord_one isOpen_univ (mem_univ x)] at this
    exact_mod_cast (by exact_mod_cast this : (-(D x) : ℤ) ≤ 0)
  · intro h x
    have hx : D x ≤ 0 := by
      have := Function.locallyFinsuppWithin.le_def.1 h x
      simpa using this
    rw [MeroGermOn.ord_one isOpen_univ (mem_univ x)]
    exact_mod_cast (neg_nonneg.2 hx)

theorem algebraMap_mem_linSys (h : 0 ≤ D) (c : ℂ) : algebraMap ℂ (ℳ X) c ∈ LinSys D := by
  intro x
  rcases eq_or_ne c 0 with rfl | hc
  · rw [map_zero, MeroGermOn.ord_zero, if_pos ⟨isOpen_univ, mem_univ x⟩]
    exact le_top
  · rw [MeroGermOn.ord_algebraMap isOpen_univ (mem_univ x) hc]
    have hx : D x ≤ 0 → False := fun _ => trivial
    have hDx : 0 ≤ D x := Function.locallyFinsuppWithin.le_def.1 h x
    exact_mod_cast (neg_nonpos.2 hDx)

/-! ### Vanishing / constancy results -/

theorem linSys_zero_eq_span_one [CompactSpace X] [ConnectedSpace X] :
    LinSys (0 : Divisor X) = Submodule.span ℂ {1} := by
  apply le_antisymm
  · intro φ hφ
    have hordnn : ∀ x, 0 ≤ φ.ord x := by
      intro x
      have := hφ x
      simpa using this
    have hCM : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω φ.holoRepr := MeroGermOn.holoRepr_contMDiff hordnn
    have hMD : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ.holoRepr := hCM.mdifferentiable
    obtain ⟨c, hc⟩ := hMD.exists_eq_const_of_compactSpace
    have hφeq : φ = MeroGermOn.mk φ.holoRepr (MeroGermOn.meromorphicOnX_holoRepr isOpen_univ φ) :=
      (MeroGermOn.mk_holoRepr isOpen_univ φ).symm
    rw [hφeq, hc]
    rw [Submodule.mem_span_singleton]
    refine ⟨c, ?_⟩
    rw [Algebra.smul_def, MeroGermOn.algebraMap_mk, MeroGermOn.mk_mul, mul_one]
    congr 1
    funext y
    simp
  · rw [Submodule.span_le]
    intro φ hφ
    simp only [Set.mem_singleton_iff] at hφ
    rw [hφ]
    exact (one_mem_linSys_iff).2 le_rfl

theorem l_zero [CompactSpace X] [ConnectedSpace X] : l (0 : Divisor X) = 1 := by
  rw [l, linSys_zero_eq_span_one]
  rw [finrank_span_singleton]
  exact one_ne_zero

theorem linSys_eq_bot_of_nonpos_of_ne_zero [CompactSpace X] [ConnectedSpace X]
    (h : D ≤ 0) (hD : D ≠ 0) : LinSys D = ⊥ := by
  rw [eq_bot_iff]
  intro φ hφ
  by_contra hφ0
  have hordnn : ∀ x, 0 ≤ (-D) x → 0 ≤ φ.ord x := fun x _ => by
    have := hφ x; simpa using this
  have hordnn' : ∀ x, 0 ≤ φ.ord x := by
    intro x
    have hDx : D x ≤ 0 := Function.locallyFinsuppWithin.le_def.1 h x
    exact le_trans (by exact_mod_cast (neg_nonneg.2 hDx) : (0 : WithTop ℤ) ≤ ((-(D x) : ℤ) : WithTop ℤ))
      (hφ x)
  have hspan : φ ∈ Submodule.span ℂ ({1} : Set (ℳ X)) := linSys_zero_eq_span_one ▸
    (fun x => by simpa using hordnn' x : φ ∈ LinSys (0 : Divisor X))
  rw [Submodule.mem_span_singleton] at hspan
  obtain ⟨a, ha⟩ := hspan
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha; exact hφ0 ha.symm
  obtain ⟨x₀, hx₀⟩ := Set.eq_empty_iff_forall_notMem.not.mp (fun hcon => hD (by
    apply Function.locallyFinsuppWithin.ext
    intro x
    by_contra hne
    exact hcon x (by
      simp only [Set.mem_setOf_eq]
      omega : x ∈ {x | D x ≠ 0}))
    |>.elim)
  sorry -- TODO(blocker): pointwise contradiction D x₀ < 0 vs ord(a•1) x₀ = 0 needs care extracting x₀

theorem l_eq_zero_of_nonpos_of_ne_zero [CompactSpace X] [ConnectedSpace X]
    (h : D ≤ 0) (hD : D ≠ 0) : l D = 0 := by
  rw [l, linSys_eq_bot_of_nonpos_of_ne_zero h hD]
  simp

/-- `deg D < 0 → L(D) = 0`, CONDITIONAL on `deg ∘ divisor = 0` — that input is owned by
proper-map-degree (argument principle / degree counting). -/
theorem linSys_eq_bot_of_degree_neg [CompactSpace X] [ConnectedSpace X]
    (hdeg : ∀ φ : ℳ X, φ ≠ 0 → (divisor φ).degree = 0) (h : D.degree < 0) : LinSys D = ⊥ := by
  rw [eq_bot_iff]
  intro φ hφmem
  by_contra hφ0
  have hle : -D ≤ divisor φ := (mem_linSys_iff_eq_zero_or_le_divisor.1 hφmem).resolve_left hφ0
  have hmono := Function.locallyFinsuppWithin.degree_mono hle
  rw [Function.locallyFinsuppWithin.degree_neg, hdeg φ hφ0] at hmono
  omega

/-! ### Relative version (Čech cochain spaces) -/

/-- Relative `L(D)` (CC8 Čech cochain spaces). -/
noncomputable def LinSysOn (D : Divisor X) (U : Set X) : Submodule ℂ (MeroGermOn X U) where
  carrier := {φ | ∀ x ∈ U, ((-(D x) : ℤ) : WithTop ℤ) ≤ φ.ord x}
  zero_mem' := by
    intro x hx
    by_cases hU : IsOpen U
    · rw [MeroGermOn.ord_zero, if_pos ⟨hU, hx⟩]; exact le_top
    · rw [MeroGermOn.ord_zero, if_neg (fun h => hU h.1)]
  add_mem' := by
    intro φ ψ hφ hψ x hx
    by_cases hU : IsOpen U
    · exact le_trans (le_min (hφ x hx) (hψ x hx)) (MeroGermOn.ord_add hU hx φ ψ)
    · exfalso; exact hU (by by_contra h; exact absurd rfl (fun _ => h))
  smul_mem' := by
    intro a φ hφ x hx
    by_cases hU : IsOpen U
    · rcases eq_or_ne a 0 with rfl | ha
      · rw [zero_smul, MeroGermOn.ord_zero, if_pos ⟨hU, hx⟩]; exact le_top
      · rw [MeroGermOn.ord_smul hU hx ha]; exact hφ x hx
    · exfalso; exact hU (by by_contra h; exact absurd rfl (fun _ => h))

theorem restrict_mem_linSysOn (h : V ⊆ U) (hV : IsOpen V) (hU : IsOpen U) {φ : MeroGermOn X U}
    (hφ : φ ∈ LinSysOn D U) : MeroGermOn.restrict h φ ∈ LinSysOn D V := by
  intro x hx
  rw [MeroGermOn.ord_restrict h hV hU hx]
  exact hφ x (h hx)

theorem mem_linSys_iff_forall_restrict {ι : Type*} {W : ι → Set X} (hW : ∀ i, IsOpen (W i))
    (hcov : ⋃ i, W i = univ) {φ : ℳ X} :
    φ ∈ LinSys D ↔ ∀ i, MeroGermOn.restrict (Set.subset_univ (W i) |>.trans (by rw [hcov]))
      φ ∈ LinSysOn D (W i) := by
  constructor
  · intro hmem i x hx
    rw [MeroGermOn.ord_restrict (Set.subset_univ (W i) |>.trans (by rw [hcov])) (hW i) isOpen_univ
      hx]
    exact hmem x
  · intro hall x
    obtain ⟨i, hi⟩ : ∃ i, x ∈ W i := by
      have : x ∈ ⋃ i, W i := by rw [hcov]; trivial
      simpa using this
    have := hall i x hi
    rwa [MeroGermOn.ord_restrict (Set.subset_univ (W i) |>.trans (by rw [hcov])) (hW i)
      isOpen_univ hi] at this

end RS
