import Mathlib
import Submission.Work.LinnikAreas.TFDefs

namespace Work.LinnikAreas

theorem aSeq_add_shift_eq (r : ℝ) (hr1 : r < 1) (c : ℕ) :
    aSeq r c + (1 + r) * r^c / (1 - r) =
      (if c = 0 then 2/(1-r) else (1+r) * r^(c-1)/(1-r)) := by
  have hne : (1 - r : ℝ) ≠ 0 := by linarith
  rcases c with _ | k
  · simp [aSeq_zero]
    field_simp
    ring
  · rw [aSeq_succ r k, if_neg (Nat.succ_ne_zero k), Nat.succ_sub_one]
    field_simp
    ring

end Work.LinnikAreas
