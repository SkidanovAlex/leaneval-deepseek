import Mathlib
import Submission.Work.C17.seventeen_defs

namespace Work.C17b

theorem xs_pos {a b : ℚ} (ha : 3 ≤ a) (hb : 3 ≤ b) : 0 < Work.C17.xs (a : ℝ) (b : ℝ) := by
  have ha' : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hb' : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have ha0 : (0 : ℝ) < (a : ℝ) := by linarith
  have hb0 : (0 : ℝ) < (b : ℝ) := by linarith
  have hsa : (0 : ℝ) ≤ Real.sqrt ((a : ℝ) ^ 2 - 1) := Real.sqrt_nonneg _
  have hsb : Real.sqrt ((b : ℝ) ^ 2 - 1) < (b : ℝ) := by
    have h2 : (b : ℝ) ^ 2 - 1 < (b : ℝ) ^ 2 := by linarith
    exact (Real.sqrt_lt' hb0).mpr h2
  rw [Work.C17.xs]
  exact mul_pos (by linarith) (by linarith)

end Work.C17b
