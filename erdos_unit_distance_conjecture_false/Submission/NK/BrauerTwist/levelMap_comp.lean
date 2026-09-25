import Mathlib
import Submission.NK.BrauerTwist.Basic

namespace NK.BrauerTwist

universe u

set_option maxHeartbeats 4000000

/-- The transition maps `levelMap` of the level system of `H²(U, μ_p)` are functorial: the
composite of the transition `L₁ ≤ L₂` with the transition `L₂ ≤ L₃` is the transition `L₁ ≤ L₃`.

Both sides are `groupCohomology.map` of the inflation `U/(U ∩ Gal(K'/L₃)) →* U/(U ∩ Gal(K'/L₁))`
along the coefficient inclusion `μ_p(L₁) ↪ μ_p(L₃)`, so this is Mathlib's
`groupCohomology.map_comp` together with the triviality `levelQuotHom_comp` of the level
quotients and the fact that the underlying linear map of `levelMapCoeff p U h` is the coefficient
inclusion `muInclLinearMap h`, whose composite is the inclusion at the transitive level. -/
theorem levelMap_comp {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (p : ℕ) (U : Subgroup Gal(K'/K))
    {L₁ L₂ L₃ : FiniteGaloisIntermediateField K K'} (h₁ : L₁ ≤ L₂) (h₂ : L₂ ≤ L₃) :
    CategoryTheory.CategoryStruct.comp (NK.BrauerTwist.levelMap p U h₁)
        (NK.BrauerTwist.levelMap p U h₂) =
      NK.BrauerTwist.levelMap p U (h₁.trans h₂) := by
  simp only [NK.BrauerTwist.levelMap]
  rw [← groupCohomology.map_comp]
  refine groupCohomology.map_congr (NK.BrauerHasse.levelQuotHom_comp (U := U) h₁ h₂) ?_ 2
  ext x
  change NK.BrauerTwist.muIncl h₂ (NK.BrauerTwist.muIncl h₁ (Additive.toMul x)) =
    NK.BrauerTwist.muIncl (h₁.trans h₂) (Additive.toMul x)
  exact Subtype.ext rfl

end NK.BrauerTwist
