import Mathlib
import Submission.NK.HassePrinciple.MuLevelMap
import Submission.NK.HassePrinciple.unitsLevelMap_comp

universe u

namespace NK.HassePrinciple

theorem muLevelMap_comp {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (p : ℕ) (V : Subgroup (K' ≃ₐ[K] K')) {L₁ L₂ L₃ : FiniteGaloisIntermediateField K K'}
    (h₁ : (L₁ : IntermediateField K K') ≤ (L₂ : IntermediateField K K'))
    (h₂ : (L₂ : IntermediateField K K') ≤ (L₃ : IntermediateField K K')) :
    CategoryTheory.CategoryStruct.comp (NK.HassePrinciple.muLevelMap p V h₁)
        (NK.HassePrinciple.muLevelMap p V h₂) =
      NK.HassePrinciple.muLevelMap p V (h₁.trans h₂) := by
  simp only [NK.HassePrinciple.muLevelMap]
  rw [← groupCohomology.map_comp]
  refine groupCohomology.map_congr (NK.BrauerHasse.levelQuotHom_comp (U := V) h₁ h₂) ?_ 2
  ext x
  change muLevelIncl p L₂ L₃ h₂ (muLevelIncl p L₁ L₂ h₁ (Additive.toMul x)) =
    muLevelIncl p L₁ L₃ (h₁.trans h₂) (Additive.toMul x)
  exact Subtype.ext rfl

end NK.HassePrinciple
