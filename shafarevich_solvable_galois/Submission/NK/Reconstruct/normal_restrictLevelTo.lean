import Mathlib
import Submission.NK.Reconstruct.Gamma
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Reconstruct

theorem normal_restrictLevelTo {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K']
    [IsGalois K K'] {E M : IntermediateField K K'} [FiniteDimensional K E] [FiniteDimensional K M]
    [Normal K E] (h : E ≤ M) : Normal K (NK.Reconstruct.restrictLevelTo E M h) := by
  classical
  have heq : IntermediateField.lift (NK.Reconstruct.restrictLevelTo E M h) = E := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, h hx⟩, hx, rfl⟩
  haveI : Normal K ↥(IntermediateField.lift (NK.Reconstruct.restrictLevelTo E M h)) :=
    heq.symm ▸ (inferInstance : Normal K ↥E)
  exact Normal.of_algEquiv
    (f := (IntermediateField.liftAlgEquiv (NK.Reconstruct.restrictLevelTo E M h)).symm)

end NK.Reconstruct
