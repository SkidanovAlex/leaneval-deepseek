import Mathlib
import Submission.Work.RPB1a.Defs

namespace Work.RPB1a

open Complex Set Metric
open scoped ContDiff Real

theorem range_comp_neg (v : ℝ → ℂ) : Set.range (fun t : ℝ => v (-t)) = Set.range v := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨-t, by simp⟩
  · rintro ⟨t, rfl⟩
    exact ⟨-t, by simp⟩

end Work.RPB1a
