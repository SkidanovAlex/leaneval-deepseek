import Mathlib
import Submission.Work.ORLyndon.CLDirect.cldDefs

namespace Work.ORLyndon.CLDirect

/-- `Θ` on a generator. Sketch: copy `Work.ORLyndon.dFox_of` in `Submission/Work/ORLyndon/lyndon_range_theta.lean` (same shape: `LinearMap.comp_apply`, `MonoidAlgebra.coeffLinearEquiv_apply`, `MonoidAlgebra.of_apply`, `MonoidAlgebra.coeff_single`, `Finsupp.linearCombination_single`, `one_smul`). -/
theorem thetaLin_of {X : Type*} [DecidableEq X] {K : Type*} [Field K] (r : FreeGroup X)
    (φ : FreeGroup X → MonoidAlgebra K (Work.ORLyndon.OneRelatorGroup r)) (f : FreeGroup X) :
    Work.ORLyndon.CLDirect.thetaLin (K := K) r φ (MonoidAlgebra.of K _ f) =
      Work.ORLyndon.CLDirect.thetaFun (K := K) r φ f := by
  simp only [thetaLin, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    MonoidAlgebra.coeffLinearEquiv_apply, MonoidAlgebra.of_apply,
    MonoidAlgebra.coeff_single, Finsupp.linearCombination_single, one_smul]

end Work.ORLyndon.CLDirect
