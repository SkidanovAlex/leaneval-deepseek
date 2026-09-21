import Mathlib
import Submission.Work.OddRadon.Core

namespace Work.OddRadon

/-- The first coordinate of the paper's normal direction `ξ(α) = (sin α, 0, …, 0, -cos α)`. -/
lemma radonXi_zero_coord (d : ℕ) [NeZero d] (α : ℝ) : (radonXi d α) 0 = Real.sin α := by
  simp [radonXi_apply]

end Work.OddRadon
