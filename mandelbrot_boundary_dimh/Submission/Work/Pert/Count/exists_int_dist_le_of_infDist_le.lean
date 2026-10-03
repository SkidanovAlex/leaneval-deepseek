import Mathlib
import Submission.Work.Pert.LCH.infDist_int_eq_round

namespace Work.Pert.Count

/-- If the infimum of the distances from `x` to the integers is at most `s`, then the
nearest integer `round x` already has distance at most `s` from `x`: the infimum is
attained there (`Work.Pert.LCH.infDist_int_eq_round`). -/
theorem exists_int_dist_le_of_infDist_le {x s : ℝ}
    (h : Metric.infDist x (Set.range (fun k : ℤ => (k : ℝ))) ≤ s) :
    ∃ k : ℤ, dist x (k : ℝ) ≤ s := by
  refine ⟨round x, ?_⟩
  rw [Real.dist_eq, round_eq x]
  rw [← Work.Pert.LCH.infDist_int_eq_round x]
  exact h

end Work.Pert.Count
