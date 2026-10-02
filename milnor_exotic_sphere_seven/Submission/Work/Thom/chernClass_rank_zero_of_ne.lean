import Mathlib
import Submission.Work.Thom.chernClass

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Thom

theorem chernClass_rank_zero_of_ne {j : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 0)) ι) (hj : j ≠ 0) :
    Work.Thom.chernClass 0 j Z = 0 := by
  rw [chernClass_zero_rank]
  unfold chernClassZero
  exact dif_neg hj

end Work.Thom
