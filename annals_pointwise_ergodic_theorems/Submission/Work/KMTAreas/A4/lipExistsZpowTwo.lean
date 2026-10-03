import Mathlib
import Submission.Work.KMTAreas.A4.lipDefs

namespace Work.KMTAreas.A4

/-- For every `r > 0` there is an integral power of `2` lying in the window `[r, 2r]`:
choose the dyadic scale just above `r`. -/
theorem lipExistsZpowTwo {r : ℝ} (hr : 0 < r) :
    ∃ k : ℤ, r ≤ (2 : ℝ) ^ k ∧ (2 : ℝ) ^ k ≤ 2 * r := by
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hr (by norm_num : (1 : ℝ) < 2)
  refine ⟨n + 1, le_of_lt hn2, ?_⟩
  rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
  linarith

end Work.KMTAreas.A4
