import Mathlib
import Submission.NK.HassePrinciple.exists_unitsLevelMapCoeff

open CategoryTheory

set_option autoImplicit false

universe u

namespace NK.HassePrinciple

/-- **Functoriality of the units level transition maps.**  The transition maps `unitsLevelMap`
of the units level system are compatible: the composite of the transition `L₁ ≤ L₂` with the
transition `L₂ ≤ L₃` is the transition `L₁ ≤ L₃`.

Both sides are `groupCohomology.map` of the inflation
`U ⧸ (U ∩ Gal(K'/L₃)) →* U ⧸ (U ∩ Gal(K'/L₁))` along the coefficient inclusion
`L₁ˣ → L₃ˣ`, so this is Mathlib's `groupCohomology.map_comp` together with the triviality
`NK.BrauerHasse.levelQuotHom_comp` of the level quotients and the fact that the underlying
linear map of `unitsLevelMapCoeff V h` is the unit inclusion `unitsInclLinearMap h`, whose
composite is the inclusion at the transitive level.  This is the units analogue of
`NK.BrauerTwist.levelMap_comp`. -/
theorem unitsLevelMap_comp {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (V : Subgroup (K' ≃ₐ[K] K')) {L₁ L₂ L₃ : FiniteGaloisIntermediateField K K'}
    (h₁ : (L₁ : IntermediateField K K') ≤ (L₂ : IntermediateField K K'))
    (h₂ : (L₂ : IntermediateField K K') ≤ (L₃ : IntermediateField K K')) :
    CategoryTheory.CategoryStruct.comp (NK.HassePrinciple.unitsLevelMap V h₁) (NK.HassePrinciple.unitsLevelMap V h₂) =
      NK.HassePrinciple.unitsLevelMap V (h₁.trans h₂) := by
  simp only [NK.HassePrinciple.unitsLevelMap]
  rw [← groupCohomology.map_comp]
  refine groupCohomology.map_congr (NK.BrauerHasse.levelQuotHom_comp (U := V) h₁ h₂) ?_ 2
  ext x
  change Additive.ofMul (unitsInclHom L₂ L₃ h₂ (unitsInclHom L₁ L₂ h₁ (Additive.toMul x))) =
    Additive.ofMul (unitsInclHom L₁ L₃ (h₁.trans h₂) (Additive.toMul x))
  rfl

end NK.HassePrinciple
