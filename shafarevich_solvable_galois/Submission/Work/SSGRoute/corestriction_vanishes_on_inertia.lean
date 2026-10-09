import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.place_basics
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open _root_.SSGRoute
open scoped Pointwise

/-- Translating the second place by a Galois element does not change the property of being a
`G_k`-conjugate of a fixed place. -/
theorem isConjPlace_smul_iff {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (A B : ValuationSubring Ω) (g : Ω ≃ₐ[k] Ω) :
    IsConjPlace k A (g • B) ↔ IsConjPlace k A B := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨g⁻¹ * σ, by rw [mul_smul, hσ, inv_smul_smul]⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨g * σ, by rw [mul_smul, hσ]⟩

/-- The formal corestriction `X σ = ∑_{s : Gal(K/k)} s • y(sec(s)⁻¹ * σ * sec(s))` vanishes on the
inertia group of every finite place `B` that lies over no element of `S` and is not split in `Λ`. -/
theorem corestriction_vanishes_on_inertia (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, IsFinPlace k A)
    (hSram : ∀ B : ValuationSubring Ω, IsFinPlace k B →
      (IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → E)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyS : ∀ B : ValuationSubring Ω, IsFinPlace k B →
      (∀ A ∈ S, ¬ IsConjPlace k A B) → ¬ IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → y σ = 0)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)) (hsec : ∀ s, res k K (sec s) = s) :
    ∀ B : ValuationSubring Ω, IsFinPlace k B → (∀ A ∈ S, ¬ IsConjPlace k A B) →
      ¬ IsSplitIn k Λ B → ∀ σ : Ω ≃ₐ[k] Ω, IsInertia k B σ →
      (∑ s : K ≃ₐ[k] K, s • y ((sec s)⁻¹ * σ * sec s)) = 0 := by
  intro B hB hconj hnsplit σ hI
  -- `B` is unramified in `Λ` (indeed lies over no element of `S`), hence `I_B ≤ G_Λ ≤ G_K`.
  have hunram : ¬ IsRamifiedIn k Λ B :=
    (not_isRamifiedIn_and_not_val_p_lt_one_of_forall_not_conj Λ p S hSram B hB hconj).1
  have hσΛ : σ ∈ Λ.fixingSubgroup :=
    mem_fixingSubgroup_of_isInertia_of_not_isRamifiedIn Λ B hunram σ hI
  have hσK : σ ∈ K.fixingSubgroup := IntermediateField.fixingSubgroup_le hKΛ hσΛ
  -- `K.fixingSubgroup` is the kernel of the restriction `res k K : G_k →* Gal(K/k)`.
  have hker : ∀ (u : Ω ≃ₐ[k] Ω), res k K u = 1 ↔ u ∈ K.fixingSubgroup := by
    intro u
    rw [show res k K u = u.restrictNormal K from rfl, AlgEquiv.restrictNormal_eq_one_iff,
      IntermediateField.mem_fixingSubgroup_iff]
  have hσ1 : res k K σ = 1 := (hker σ).mpr hσK
  have hnorm : (Λ.fixingSubgroup).Normal := inferInstance
  -- Every term vanishes: the conjugate `(sec s)⁻¹ * σ * sec s` lies in the inertia group of the
  -- conjugate place `(sec s)⁻¹ • B`, which also lies over no element of `S` and is not split.
  refine Finset.sum_eq_zero (fun s _ => ?_)
  have hfin : IsFinPlace k ((sec s)⁻¹ • B) := (isFinPlace_smul_iff B (sec s)⁻¹).mpr hB
  have hconj' : ∀ A ∈ S, ¬ IsConjPlace k A ((sec s)⁻¹ • B) := fun A hA hc =>
    hconj A hA ((isConjPlace_smul_iff A B (sec s)⁻¹).mp hc)
  have hnsplit' : ¬ IsSplitIn k Λ ((sec s)⁻¹ • B) := fun hsp =>
    hnsplit ((isSplitIn_conj Λ hnorm B (sec s)⁻¹).mp hsp)
  have hmem_res : res k K ((sec s)⁻¹ * σ * sec s) = 1 := by
    rw [map_mul, map_mul, map_inv, hsec s, hσ1, mul_one, inv_mul_cancel]
  have hmem : ((sec s)⁻¹ * σ * sec s) ∈ K.fixingSubgroup := (hker _).mp hmem_res
  have hinert : IsInertia k ((sec s)⁻¹ • B) ((sec s)⁻¹ * σ * sec s) := by
    simpa using (isInertia_conj B (sec s)⁻¹ σ).mpr hI
  rw [hyS ((sec s)⁻¹ • B) hfin hconj' hnsplit' _ hmem hinert, smul_zero]

end Work.SSGRoute
