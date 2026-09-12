import Mathlib
import Submission.Commons.PeriodicTiling.isContinuousTiling_of_isTiling_lift
import Submission.Commons.PeriodicTiling.quotient_tiling_lift_tile0_IsTiling

open scoped Pointwise

namespace Commons.PeriodicTiling

lemma quotient_tiling_lift_tile0
    {G : Type*} [AddCommGroup G] {d : ℕ}
    (π : (Fin d → ℤ) →+ G) (hπ : Function.Surjective π)
    (D : Set (Fin d → ℤ)) (hD : AddSubgroup.IsComplement D (π.ker : Set (Fin d → ℤ))) :
    ∃ (N : ℕ) (T₁ T₂ : Set (Fin d → ℤ)),
      T₁.Finite ∧ T₂.Finite ∧ (0 : Fin d → ℤ) ∈ T₂ ∧
      ∀ {F : Set G}, F.Finite → (0 : G) ∈ F →
        let F' : Set (Fin d → ℤ) :=
          ((Set.image (fun x : Fin d → ℤ => (N : ℤ) • x)
              ((π ⁻¹' (F \ {0})) ∩ D)) + T₁) ∪ T₂
        F'.Finite ∧ F'.Nonempty ∧
        (∀ A : Set G, IsTiling F A → (0 : G) ∈ A →
          IsTiling F' (Set.image (fun x : Fin d → ℤ => (N : ℤ) • x) (π ⁻¹' A))) ∧
        (∀ A' : Set (Fin d → ℤ), IsTiling F' A' → (0 : Fin d → ℤ) ∈ A' →
          ∃ A : Set G, IsTiling F A ∧ (0 : G) ∈ A ∧
            A' = Set.image (fun x : Fin d → ℤ => (N : ℤ) • x) (π ⁻¹' A)) := by
  classical
  obtain ⟨N, T₁, T₂, hT₁fin, hT₂fin, hT₂zero, hcorr⟩ :=
    quotient_tiling_lift_tile0_IsTiling π hπ D hD
  refine ⟨N, T₁, T₂, hT₁fin, hT₂fin, hT₂zero, ?_⟩
  intro F hFfin hF0
  have h := hcorr hFfin hF0
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · intro A hA hA0
    exact h.2.2.1 A hA hA0
  · intro A' hA' hA'0
    exact h.2.2.2 A' hA' hA'0

end Commons.PeriodicTiling
