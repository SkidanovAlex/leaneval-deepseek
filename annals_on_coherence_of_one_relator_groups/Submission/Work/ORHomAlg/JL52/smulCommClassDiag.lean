import Mathlib
import Submission.Work.ORHomAlg.JL52.DiagTensorDefs

namespace Work.ORHomAlg.JL52

universe u

/-- For a field `K`, a group `G` and left `K[G]`-modules `A` and `X` whose `K`-actions are
compatible with the `K[G]`-actions, the `K`-action and the diagonal `K[G]`-action on
`TensorProduct K A X` commute.  (The diagonal action is the one installed by
`Work.ORHomAlg.JL52.instDiagSMul`, which has higher priority than Mathlib's left-factor action.) -/
theorem smulCommClassDiag (K G : Type u) [Field K] [Group G]
    (A X : Type u) [AddCommGroup A] [Module K A] [Module (MonoidAlgebra K G) A]
    [SMulCommClass K (MonoidAlgebra K G) A]
    [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X] :
    SMulCommClass K (MonoidAlgebra K G) (TensorProduct K A X) := by
  -- The diagonal action of `r` on the tensor product is the `K`-linear endomorphism
  -- `diagRingHom A X r`; being `K`-linear it commutes with the scalar `K`-action.
  constructor
  intro c r z
  rw [diag_smul_def, diag_smul_def]
  exact ((diagRingHom A X r).map_smul c z).symm

end Work.ORHomAlg.JL52
