import Mathlib
import Submission.Work.LinnikContract2.Areas

namespace Work.LinnikContract2.A7

theorem table13_col_le : ∀ e ∈ Work.LinnikContract2.table13, e.2.1 ≤ (58:ℝ)/100 := by
  intro e he
  fin_cases he <;> norm_num

end Work.LinnikContract2.A7
