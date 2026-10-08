import Mathlib.LinearAlgebra.Projectivization.Action
import Submission.Work.Models.Port.Commons.GroupTheory.GroupAction.isMultiplyPretransitive_of_surjective_hom

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.SL2

/-- The natural projection `SL(2,K) → PSL(2,K)` is compatible with the action on
`ℙ K (Fin 2 → K)`: the action of `PSL(2,K)` is the one induced by the action of
`SL(2,K)`.  Hence 2-pretransitivity of the `SL(2,K)`-action (Mathlib's
`Projectivization.Matrix.SpecialLinearGroup` instance) transfers to `PSL(2,K)`. -/
theorem isMultiplyPretransitive_projectiveSpecialLinearGroup_two {K : Type*} [Field K] :
    MulAction.IsMultiplyPretransitive (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)
      (Projectivization K (Fin 2 → K)) 2 := by
  exact Commons.GroupTheory.GroupAction.isMultiplyPretransitive_of_surjective_hom
    (G := Matrix.SpecialLinearGroup (Fin 2) K)
    (H := Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)))
    (fun g x => Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk g x)

end Commons.GroupTheory.SL2