import Mathlib
import Submission.Work.ORLyndon.CLDirect.cldDefs
import Submission.Work.ORLyndon.CLDirect.thetaLin_of
import Submission.Work.ORLyndon.CLDirect.presentSec_inv_mul_mem

namespace Work.ORLyndon.CLDirect

/-- Unfolding `thetaFun`. Sketch: `presentRho r (f*n) = presentRho r f` since `presentRho r n = 1` by `PresentedGroup.mk_eq_one_iff.mpr`; so the section term is unchanged; `sec⁻¹ * (f * n) = (sec⁻¹ * f) * n` by `mul_assoc`, apply `hmul` with `presentSec_inv_mul_mem`; finish with `mul_add`. -/
theorem thetaFun_mul_mem {X : Type*} [DecidableEq X] {K : Type*} [Field K] (r : FreeGroup X)
    (φ : FreeGroup X → MonoidAlgebra K (Work.ORLyndon.OneRelatorGroup r))
    (hmul : ∀ n n', n ∈ Subgroup.normalClosure ({r} : Set (FreeGroup X)) →
      n' ∈ Subgroup.normalClosure ({r} : Set (FreeGroup X)) → φ (n * n') = φ n + φ n')
    (f n : FreeGroup X) (hn : n ∈ Subgroup.normalClosure ({r} : Set (FreeGroup X))) :
    Work.ORLyndon.CLDirect.thetaFun (K := K) r φ (f * n) =
      Work.ORLyndon.CLDirect.thetaFun (K := K) r φ f +
        MonoidAlgebra.of K _ (Work.ORLyndon.presentRho r f) * φ n := by
  have hn1 : Work.ORLyndon.presentRho r n = 1 :=
    (PresentedGroup.mk_eq_one_iff (rels := ({r} : Set (FreeGroup X)))).mpr hn
  have hρ : Work.ORLyndon.presentRho r (f * n) = Work.ORLyndon.presentRho r f := by
    rw [map_mul, hn1, mul_one]
  simp only [Work.ORLyndon.CLDirect.thetaFun]
  rw [hρ]
  rw [← mul_assoc]
  rw [hmul _ _ (Work.ORLyndon.CLDirect.presentSec_inv_mul_mem (K := K) r f) hn]
  rw [mul_add]

end Work.ORLyndon.CLDirect
