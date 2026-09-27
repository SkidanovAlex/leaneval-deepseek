import Mathlib
import Submission.Work.EKLComp.Hcond

namespace Work.EKLComp.HcondJoin

theorem partIdx_indicator_sum {X : Type} [mX : MeasurableSpace X] {ι : Type} [Fintype ι]
    {A : ι → Set X} (hA : Work.EKLComp.Core.IsMPart A) (c : ι → ℝ) (x : X) :
    ∑ i, (A i).indicator (fun _ => c i) x = c (Work.EKLComp.Core.partIdx A hA x) := by
  classical
  rw [Finset.sum_eq_single_of_mem (Work.EKLComp.Core.partIdx A hA x) (Finset.mem_univ _)]
  · rw [Set.indicator_of_mem (Work.EKLComp.Core.partIdx_mem A hA x)]
  · intro i _ hi
    rw [Set.indicator_of_notMem]
    intro hx
    exact hi (Work.EKLComp.Core.partIdx_unique A hA x hx)

end Work.EKLComp.HcondJoin
