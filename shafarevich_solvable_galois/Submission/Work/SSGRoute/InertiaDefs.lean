import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.place_basics
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The inertia subgroup of a place

The inertia subgroup `I_A ≤ G_k` of a place `A` of `Ω`, its containment in the decomposition group
and its normality in it.  Definitions and elementary lemmas only; nothing here is `sorry`.
-/

open scoped Pointwise

namespace Work.SSGRoute

variable (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]

/-- **The inertia subgroup** `I_A ≤ G_k` of a place `A` of `Ω`: the elements of the decomposition
group of `A` acting trivially on its residue field, i.e. with
`SSGRoute.IsInertia k A σ = σ ∈ D_A ∧ ∀ x ∈ A, A.valuation (σ x - x) < 1`. -/
def inertiaSub (A : ValuationSubring Ω) : Subgroup (Ω ≃ₐ[k] Ω) where
  carrier := {σ | SSGRoute.IsInertia k A σ}
  one_mem' := by
    refine ⟨?_, ?_⟩
    · exact MulAction.mem_stabilizer_iff.mpr (one_smul _ _)
    · intro x _
      simp
  mul_mem' := by
    intro σ τ hσ hτ
    obtain ⟨hσD, hσv⟩ := hσ
    obtain ⟨hτD, hτv⟩ := hτ
    have hσA : σ • A = A := MulAction.mem_stabilizer_iff.mp hσD
    have hτA : τ • A = A := MulAction.mem_stabilizer_iff.mp hτD
    constructor
    · rw [MulAction.mem_stabilizer_iff, mul_smul, hτA, hσA]
    · intro x hx
      have hτx : τ x ∈ A := by
        have h := ValuationSubring.smul_mem_pointwise_smul τ x A hx
        rwa [hτA] at h
      have hdiff : τ x - x ∈ A := A.sub_mem hτx hx
      have h1 : A.valuation (σ (τ x - x)) < 1 := by
        have h2 := (smul_valuation_lt_one σ A (τ x - x) hdiff).mpr (hτv x hx)
        rwa [hσA] at h2
      have h2 : A.valuation (σ x - x) < 1 := hσv x hx
      have hsum : A.valuation (σ (τ x - x) + (σ x - x)) < 1 :=
        Valuation.map_add_lt (A.valuation) h1 h2
      rwa [show (σ * τ) x - x = σ (τ x - x) + (σ x - x) from by
        rw [show (σ * τ) x = σ (τ x) from rfl, map_sub]; abel]
  inv_mem' := by
    intro σ hσ
    obtain ⟨hσD, hσv⟩ := hσ
    have hσA : σ • A = A := MulAction.mem_stabilizer_iff.mp hσD
    have hσA' : σ⁻¹ • A = A := by
      have h := congrArg (fun X : ValuationSubring Ω => σ⁻¹ • X) hσA
      simpa using h.symm
    constructor
    · rw [MulAction.mem_stabilizer_iff]
      have h := congrArg (fun X : ValuationSubring Ω => σ⁻¹ • X) hσA
      simpa using h.symm
    · intro x hx
      have hinv : σ⁻¹ x ∈ A := by
        have h := ValuationSubring.smul_mem_pointwise_smul σ⁻¹ x A hx
        rwa [hσA'] at h
      have hdiff : σ⁻¹ x - x ∈ A := A.sub_mem hinv hx
      have hxσ : A.valuation (σ (σ⁻¹ x - x)) < 1 := by
        have heq : σ (σ⁻¹ x - x) = -(σ x - x) := by
          rw [map_sub, show σ (σ⁻¹ x) = x from AlgEquiv.apply_symm_apply σ x]
          abel
        rw [heq, (A.valuation).map_neg (σ x - x)]
        exact hσv x hx
      refine (smul_valuation_lt_one σ A (σ⁻¹ x - x) hdiff).mp ?_
      rw [hσA]
      exact hxσ

theorem mem_inertiaSub (A : ValuationSubring Ω) (σ : Ω ≃ₐ[k] Ω) :
    σ ∈ inertiaSub k Ω A ↔ SSGRoute.IsInertia k A σ := Iff.rfl

theorem inertiaSub_le_decomp (A : ValuationSubring Ω) :
    inertiaSub k Ω A ≤ SSGRoute.decomp k A := fun _ h => h.1

/-- **The inertia subgroup is normal in the decomposition group.** -/
theorem inertiaSub_normal (A : ValuationSubring Ω) :
    ∀ δ ∈ SSGRoute.decomp k A, ∀ u ∈ inertiaSub k Ω A,
      δ * u * δ⁻¹ ∈ inertiaSub k Ω A := by
  intro δ hδ u hu
  have hδA : δ • A = A := MulAction.mem_stabilizer_iff.mp hδ
  show SSGRoute.IsInertia k A (δ * u * δ⁻¹)
  rw [← hδA]
  exact (isInertia_conj A δ u).mpr hu

end Work.SSGRoute
