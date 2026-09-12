import Mathlib
import Submission.Commons.PeriodicTiling.isContinuousTiling_of_isTiling_lift
import Submission.Commons.PeriodicTiling.tile0_from_rigid_pair

namespace Commons.PeriodicTiling

lemma quotient_tiling_lift_tile0_IsTiling
    {G : Type*} [AddCommGroup G] {d : ℕ}
    (π : (Fin d → ℤ) →+ G) (hπ : Function.Surjective π)
    (D : Set (Fin d → ℤ)) (hD : AddSubgroup.IsComplement D (π.ker : Set (Fin d → ℤ))) :
    ∃ (N : ℕ) (T₁ T₂ : Set (Fin d → ℤ)),
      T₁.Finite ∧ T₂.Finite ∧ (0 : Fin d → ℤ) ∈ T₂ ∧
      ∀ {F : Set G}, F.Finite → (0 : G) ∈ F →
        let F' : Set (Fin d → ℤ) :=
          (Set.image2 Add.add (Set.image (fun x : Fin d → ℤ => (N : ℤ) • x)
              ((π ⁻¹' (F \ {0})) ∩ D)) T₁) ∪ T₂
        F'.Finite ∧ F'.Nonempty ∧
        (∀ A : Set G, Commons.PeriodicTiling.IsTiling F A → (0 : G) ∈ A →
          Commons.PeriodicTiling.IsTiling F'
            (Set.image (fun x : Fin d → ℤ => (N : ℤ) • x) (π ⁻¹' A))) ∧
        (∀ A' : Set (Fin d → ℤ), Commons.PeriodicTiling.IsTiling F' A' →
            (0 : Fin d → ℤ) ∈ A' →
          ∃ A : Set G, Commons.PeriodicTiling.IsTiling F A ∧ (0 : G) ∈ A ∧
            A' = Set.image (fun x : Fin d → ℤ => (N : ℤ) • x) (π ⁻¹' A)) := by
  exact tile0_from_rigid_pair π hπ D hD

end Commons.PeriodicTiling
