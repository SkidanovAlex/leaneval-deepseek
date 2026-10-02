import Mathlib
import Submission.Work.Thom.chernClass

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Thom

theorem chernClass_eq_zero_of_lt {m j : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (h : m < j) :
    Work.Thom.chernClass m j Z = 0 := by
  rcases m with _ | m
  · rw [chernClass_zero_rank]
    unfold chernClassZero
    exact dif_neg (by omega)
  · exact chernClass_succ_of_gt Z h

end Work.Thom
