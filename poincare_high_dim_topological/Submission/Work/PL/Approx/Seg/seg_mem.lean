import Mathlib
import Submission.Work.PL.Approx.Defs

namespace Work.PL.Approx.Seg

/-- `clamp 0 1 x` always lies in `[0,1]`, whatever `x` is. -/
lemma clamp_zero_one_mem (x : ℝ) : 0 ≤ Work.PL.Approx.clamp 0 1 x ∧ Work.PL.Approx.clamp 0 1 x ≤ 1 := by
  unfold Work.PL.Approx.clamp
  exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

lemma seg_mem {a b u : ℝ} (hab : a < b) : 0 ≤ seg a b u ∧ seg a b u ≤ 1 := by
  unfold seg
  exact clamp_zero_one_mem _

end Work.PL.Approx.Seg
