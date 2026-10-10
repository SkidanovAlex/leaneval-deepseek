import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-!
# Translation of places and elementary cochain lemmas (Schmidt-Wingberg Theorem 13)

Foundational bookkeeping for `Work.SSGRoute.shafarevich_theorem13`: the action of
`G_k = Ω ≃ₐ[k] Ω` on the places of `Ω` (the pointwise action on `ValuationSubring Ω`) translates
decomposition groups by conjugation, and leaves invariant finiteness, the inertia, ramification and
complete splitting of a place; and the three cochain predicates of `Interfaces.lean`
(`IsCocycleOn`, `IsCoboundaryOn`, `IsLocConstOn`) are monotone in the subgroup.
-/

open _root_.SSGRoute
open scoped Pointwise
set_option linter.unusedSectionVars false

/-! ## Foundations: translation of places

The action of `G_k = Ω ≃ₐ[k] Ω` on the places of `Ω` (pointwise action on `ValuationSubring Ω`)
translates decomposition groups by conjugation, and the whole local data (finite-ness,
inertia, ramification, complete splitting) is invariant.  These are the bookkeeping lemmas that
every local argument in the paper uses, recorded here once and for all.
-/

section Places

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

theorem valuation_lt_one_iff_not_isUnit {K : Type} [Field K] (A : ValuationSubring K)
    (x : A) : A.valuation (x : K) < 1 ↔ ¬ IsUnit x := by
  rw [lt_iff_le_and_ne]
  have h : A.valuation (x : K) ≤ 1 := ValuationSubring.valuation_le_one A x
  rw [and_iff_right h]
  exact not_congr (ValuationSubring.valuation_eq_one_iff A x).symm

/-- The valuation of the translated place: for `w ∈ A`, `g • w ∈ g • A` has valuation `< 1` in
`g • A` exactly when `w` has valuation `< 1` in `A`. -/
theorem smul_valuation_lt_one (g : Ω ≃ₐ[k] Ω) (A : ValuationSubring Ω)
    (w : Ω) (hw : w ∈ A) :
    (g • A : ValuationSubring Ω).valuation (g • w) < 1 ↔ A.valuation w < 1 := by
  let Aβ : ValuationSubring Ω := g • A
  have hmem : g • w ∈ Aβ := ValuationSubring.smul_mem_pointwise_smul g w A hw
  let φ : A ≃+* Aβ :=
  { toFun := fun x => ⟨g • x.1, ValuationSubring.smul_mem_pointwise_smul g x.1 A x.2⟩
    invFun := fun y => ⟨g⁻¹ • y.1, by
      have h2 : g⁻¹ • y.1 ∈ g⁻¹ • Aβ :=
        ValuationSubring.smul_mem_pointwise_smul g⁻¹ y.1 Aβ y.2
      have h3 : g⁻¹ • Aβ = A := by
        show g⁻¹ • (g • A) = A
        rw [smul_smul, inv_mul_cancel, one_smul]
      rwa [h3] at h2⟩
    left_inv := by intro x; ext; simp
    right_inv := by intro y; ext; simp
    map_mul' := by intro x y; ext; simp
    map_add' := by intro x y; ext; simp }
  have h := isUnit_map_iff φ ⟨w, hw⟩
  have hφ : (⟨g • w, hmem⟩ : Aβ) = φ ⟨w, hw⟩ := by ext; rfl
  rw [show (g • A : ValuationSubring Ω).valuation (g • w) =
      Aβ.valuation (↑(⟨g • w, hmem⟩ : Aβ)) from rfl,
    valuation_lt_one_iff_not_isUnit Aβ ⟨g • w, hmem⟩,
    valuation_lt_one_iff_not_isUnit A ⟨w, hw⟩, hφ]
  exact not_congr h

theorem conj_apply_smul (g τ : Ω ≃ₐ[k] Ω) (y : Ω) :
    (g * τ * g⁻¹) (g • y) = g • (τ • y) := by
  show g (τ (g⁻¹ (g • y))) = g (τ • y)
  simp

/-- **Translation of a place conjugates its inertia**: `I_{g·A} = g I_A g⁻¹`. -/
theorem isInertia_conj (A : ValuationSubring Ω) (g τ : Ω ≃ₐ[k] Ω) :
    IsInertia k (g • A) (g * τ * g⁻¹) ↔ IsInertia k A τ := by
  have hdecomp : g * τ * g⁻¹ ∈ decomp k (g • A) ↔ τ ∈ decomp k A := by
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      have h2 : g • (τ • A) = g • A := by
        rw [← h]; simp only [mul_smul, inv_smul_smul]
      exact smul_left_cancel g h2
    · intro h; rw [mul_smul, mul_smul, inv_smul_smul, h]
  constructor
  · rintro ⟨hd, hres⟩
    refine ⟨hdecomp.mp hd, fun y hy => ?_⟩
    have hgy : g • y ∈ g • A := ValuationSubring.smul_mem_pointwise_smul g y A hy
    have hτy : τ • y ∈ A := by
      have hA : τ • A = A := MulAction.mem_stabilizer_iff.mp (hdecomp.mp hd)
      exact hA ▸ ValuationSubring.smul_mem_pointwise_smul τ y A hy
    have hsub : τ • y - y ∈ A := A.sub_mem hτy hy
    have hval := hres (g • y) hgy
    rw [conj_apply_smul g τ y] at hval
    rw [show g • (τ • y) - g • y = g • (τ • y - y) from (map_sub g (τ • y) y).symm] at hval
    exact (smul_valuation_lt_one g A (τ • y - y) hsub).mp hval
  · rintro ⟨hd, hres⟩
    refine ⟨hdecomp.mpr hd, fun x hx => ?_⟩
    have hy : g⁻¹ • x ∈ A := ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem.mp hx
    have hτy : τ • (g⁻¹ • x) ∈ A := by
      have hA : τ • A = A := MulAction.mem_stabilizer_iff.mp hd
      exact hA ▸ ValuationSubring.smul_mem_pointwise_smul τ (g⁻¹ • x) A hy
    have hsub : τ • (g⁻¹ • x) - g⁻¹ • x ∈ A := A.sub_mem hτy hy
    have hval := hres (g⁻¹ • x) hy
    have hb := (smul_valuation_lt_one g A (τ • (g⁻¹ • x) - g⁻¹ • x) hsub).mpr hval
    have hgoal : (g * τ * g⁻¹) x - x = g • (τ • (g⁻¹ • x) - g⁻¹ • x) := by
      conv_lhs => rw [(smul_inv_smul g x).symm]
      rw [conj_apply_smul g τ (g⁻¹ • x)]
      exact (map_sub g (τ • (g⁻¹ • x)) (g⁻¹ • x)).symm
    rwa [hgoal]

/-- **Translation of a place conjugates its decomposition group**: `D_{g·A} = g D_A g⁻¹`. -/
theorem decomp_conj (A : ValuationSubring Ω) (g : Ω ≃ₐ[k] Ω) :
    decomp k (g • A) = (decomp k A).map (MulAut.conj g).toMonoidHom :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj g A

/-- Translating a place does not change the prime of `k` it lies over. -/
theorem comap_algebraMap_smul (A : ValuationSubring Ω) (g : Ω ≃ₐ[k] Ω) :
    (g • A).comap (algebraMap k Ω) = A.comap (algebraMap k Ω) := by
  ext x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  have hfix : (g⁻¹ : Ω ≃ₐ[k] Ω) • (algebraMap k Ω x) = algebraMap k Ω x := (g⁻¹).commutes x
  rw [hfix]

/-- Conjugation preserves the property of being a finite place. -/
theorem isFinPlace_smul_iff (A : ValuationSubring Ω) (g : Ω ≃ₐ[k] Ω) :
    IsFinPlace k (g • A) ↔ IsFinPlace k A := by
  simp only [IsFinPlace, comap_algebraMap_smul]

lemma conj_mem_iff {G : Type} [Group G] {H : Subgroup G} (hH : H.Normal) (g x : G) :
    g * x * g⁻¹ ∈ H ↔ x ∈ H := by
  constructor
  · intro h
    have := hH.conj_mem (g * x * g⁻¹) h g⁻¹
    simpa [mul_assoc] using this
  · intro h
    exact hH.conj_mem x h g

lemma comap_conj_eq {G : Type} [Group G] {H : Subgroup G} (hH : H.Normal) (g : G) :
    Subgroup.comap (MulAut.conj g).toMonoidHom H = H := by
  ext x
  rw [Subgroup.mem_comap]
  exact conj_mem_iff hH g x

/-- Complete splitting in a normal extension is conjugation-invariant. -/
theorem isSplitIn_conj (N : IntermediateField k Ω) (hNorm : (N.fixingSubgroup).Normal)
    (A : ValuationSubring Ω) (g : Ω ≃ₐ[k] Ω) :
    IsSplitIn k N (g • A) ↔ IsSplitIn k N A := by
  simp only [IsSplitIn]
  rw [decomp_conj, Subgroup.map_le_iff_le_comap, comap_conj_eq hNorm g]

/-- Ramification in a normal extension is conjugation-invariant. -/
theorem isRamifiedIn_conj (N : IntermediateField k Ω) (hNorm : (N.fixingSubgroup).Normal)
    (A : ValuationSubring Ω) (g : Ω ≃ₐ[k] Ω) :
    IsRamifiedIn k N (g • A) ↔ IsRamifiedIn k N A := by
  simp only [IsRamifiedIn]
  constructor
  · rintro ⟨σ, hI, hσ⟩
    refine ⟨g⁻¹ * σ * g, ?_, ?_⟩
    · have h2 : g * (g⁻¹ * σ * g) * g⁻¹ = σ := by group
      have hI' : IsInertia k (g • A) (g * (g⁻¹ * σ * g) * g⁻¹) := by rw [h2]; exact hI
      exact (isInertia_conj A g (g⁻¹ * σ * g)).mp hI'
    · intro hmem
      exact hσ ((conj_mem_iff hNorm g⁻¹ σ).mp hmem)
  · rintro ⟨σ, hI, hσ⟩
    refine ⟨g * σ * g⁻¹, ?_, ?_⟩
    · exact (isInertia_conj A g σ).mpr hI
    · intro hmem
      exact hσ ((conj_mem_iff hNorm g σ).mp hmem)

/-- A place of `Ω` that lies over no element of `S` is unramified in `N/k` and does not lie over
`p`: the contrapositive of the hypothesis `hSram` that `S` contains the ramified primes and the
primes over `p`. -/
theorem not_isRamifiedIn_and_not_val_p_lt_one_of_forall_not_conj [NumberField k]
    (Λ : IntermediateField k Ω) (p : ℕ) (S : Finset (ValuationSubring Ω))
    (hSram : ∀ B : ValuationSubring Ω, IsFinPlace k B →
      (IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, IsConjPlace k A B)
    (B : ValuationSubring Ω) (hB : IsFinPlace k B)
    (hconj : ∀ A ∈ S, ¬ IsConjPlace k A B) :
    ¬ IsRamifiedIn k Λ B ∧ ¬ (B.valuation (p : Ω) < 1) := by
  constructor
  · intro h
    obtain ⟨A, hA, hc⟩ := hSram B hB (Or.inl h)
    exact (hconj A hA) hc
  · intro h
    obtain ⟨A, hA, hc⟩ := hSram B hB (Or.inr h)
    exact (hconj A hA) hc

/-- The inertia group of an unramified (in `N/k`) place is contained in `G_N`. -/
theorem mem_fixingSubgroup_of_isInertia_of_not_isRamifiedIn
    (N : IntermediateField k Ω) (B : ValuationSubring Ω) (h : ¬ IsRamifiedIn k N B) :
    ∀ σ : Ω ≃ₐ[k] Ω, IsInertia k B σ → σ ∈ N.fixingSubgroup := by
  intro σ hσ
  by_contra hmem
  exact h ⟨σ, hσ, hmem⟩

end Places

/-! ## Foundations: the cochain predicates

Elementary monotonicity of the three predicates defining classes of `Interfaces.lean`.
-/

section Cochains

variable {Γ G M : Type} [Group Γ] [TopologicalSpace Γ] [Group G] [AddCommGroup M]
  [DistribMulAction G M]

theorem isCocycleOn_mono (act : Γ →* G) {H H' : Subgroup Γ} (h : H' ≤ H) {f : Γ → M}
    (hf : IsCocycleOn act H f) : IsCocycleOn act H' f :=
  fun g hg h' hh => hf g (h hg) h' (h hh)

private theorem isCoboundaryOn_mono (act : Γ →* G) {H H' : Subgroup Γ} (h : H' ≤ H) {f : Γ → M}
    (hf : IsCoboundaryOn act H f) : IsCoboundaryOn act H' f := by
  obtain ⟨m, hm⟩ := hf
  exact ⟨m, fun g hg => hm g (h hg)⟩

theorem isLocConstOn_mono {H H' : Subgroup Γ} (h : H' ≤ H) {f : Γ → M}
    (hf : IsLocConstOn H f) : IsLocConstOn H' f := by
  obtain ⟨U, hU, hc⟩ := hf
  exact ⟨U, hU, fun g hg u hu hu' => hc g (h hg) u hu (h hu')⟩

end Cochains


/-! ## `IsConjPlace` is an equivalence relation, compatible with translation -/

section ConjPlace

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

theorem isConjPlace_refl (A : ValuationSubring Ω) : IsConjPlace k A A :=
  ⟨1, one_smul _ _⟩

theorem isConjPlace_symm {A B : ValuationSubring Ω} (h : IsConjPlace k A B) :
    IsConjPlace k B A := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨σ⁻¹, by rw [← hσ, inv_smul_smul]⟩

theorem isConjPlace_trans {A B C : ValuationSubring Ω} (h₁ : IsConjPlace k A B)
    (h₂ : IsConjPlace k B C) : IsConjPlace k A C := by
  obtain ⟨σ, hσ⟩ := h₁
  obtain ⟨τ, hτ⟩ := h₂
  exact ⟨τ * σ, by rw [mul_smul, hσ, hτ]⟩

theorem isConjPlace_smul {A B : ValuationSubring Ω} (h : IsConjPlace k A B)
    (g : Ω ≃ₐ[k] Ω) : IsConjPlace k A (g • B) := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨g * σ, by rw [mul_smul, hσ]⟩


end ConjPlace

end Work.SSGRoute