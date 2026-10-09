import Mathlib
import Submission.Work.CohomologicalShrinking.OperatorMap
import Submission.Work.CohomologicalShrinking.Prop7
import Submission.Work.CohomologicalShrinking.functorial.gradedMapLin_comp
import Submission.Work.CohomologicalShrinking.functorial.quotMapLin_comp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking.operator

theorem h1Map_comp (p : ℕ) [NeZero p] (G : Type*) [Group G] (i j : ℕ) (T : Type*)
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T] [SMulCommClass G (ZMod p) T]
    {m n l : ℕ} (Φ : Work.CohomologicalShrinking.OperatorMap G m n)
    (Ψ : Work.CohomologicalShrinking.OperatorMap G n l) :
    Work.CohomologicalShrinking.OperatorMap.h1Map (p := p) (G := G) (i := i) (j := j) (T := T) (Ψ.comp Φ)
      = (Work.CohomologicalShrinking.OperatorMap.h1Map (p := p) (G := G) (i := i) (j := j) (T := T) Ψ).comp
          (Work.CohomologicalShrinking.OperatorMap.h1Map (p := p) (G := G) (i := i) (j := j) (T := T) Φ) := by
  simp only [Work.CohomologicalShrinking.OperatorMap.h1Map,
    Work.CohomologicalShrinking.OperatorMap.comp_toHom]
  rw [Work.CohomologicalShrinking.functorial.quotMapLin_comp,
      Work.CohomologicalShrinking.functorial.gradedMapLin_comp]
  rw [LinearMap.rTensor_comp, TensorProduct.map_comp]

end Work.CohomologicalShrinking.operator
