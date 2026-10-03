import Mathlib
import Submission.Work.ORHomAlg.JL52.DiagTensorDefs

namespace Work.ORHomAlg.JL52

universe u

/-- For a field `K`, a group `G` and left `K[G]`-modules `A` and `X` whose `K`-actions are
compatible with the `K[G]`-actions, the diagonal `K[G]`-action on `TensorProduct K A X` is a scalar
tower over `K`: `(c • r) • z = c • (r • z)`. -/
theorem isScalarTowerDiag (K G : Type u) [Field K] [Group G]
    (A X : Type u) [AddCommGroup A] [Module K A] [Module (MonoidAlgebra K G) A]
    [SMulCommClass K (MonoidAlgebra K G) A]
    [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G) X]
    [SMulCommClass K (MonoidAlgebra K G) X] :
    IsScalarTower K (MonoidAlgebra K G) (TensorProduct K A X) := by
  refine ⟨fun c r z => ?_⟩
  simp only [diag_smul_def, diagRingHom_smul A X c r]
  exact LinearMap.smul_apply c (diagRingHom A X r) z

end Work.ORHomAlg.JL52
