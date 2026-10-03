import Mathlib
import Submission.Work.ORLyndon.CLDirect.cldDefs

namespace Work.ORLyndon.CLDirect

/-- The section `presentSec r` is a section: `σ(ρ f)⁻¹ f ∈ ⟪r⟫`. Sketch: `Function.surjInv_eq` gives `presentRho r (presentSec r g) = g`; so `presentRho r (sec⁻¹ * f) = 1`; conclude with `PresentedGroup.mk_eq_one_iff`. -/
theorem presentSec_inv_mul_mem {X : Type*} [DecidableEq X] {K : Type*} [Field K] (r : FreeGroup X)
    (f : FreeGroup X) :
    (Work.ORLyndon.CLDirect.presentSec r (Work.ORLyndon.presentRho r f))⁻¹ * f ∈
      Subgroup.normalClosure ({r} : Set (FreeGroup X)) := by
  rw [← PresentedGroup.mk_eq_one_iff (rels := ({r} : Set (FreeGroup X)))]
  have hsec : Work.ORLyndon.presentRho r
      (Work.ORLyndon.CLDirect.presentSec r (Work.ORLyndon.presentRho r f)) =
      Work.ORLyndon.presentRho r f :=
    Function.surjInv_eq (PresentedGroup.mk_surjective ({r} : Set (FreeGroup X)))
      (Work.ORLyndon.presentRho r f)
  show Work.ORLyndon.presentRho r
      ((Work.ORLyndon.CLDirect.presentSec r (Work.ORLyndon.presentRho r f))⁻¹ * f) = 1
  rw [map_mul, map_inv, hsec, inv_mul_cancel]

end Work.ORLyndon.CLDirect
