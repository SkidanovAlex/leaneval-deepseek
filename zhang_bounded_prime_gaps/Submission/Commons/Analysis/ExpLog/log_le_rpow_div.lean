import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Commons.Analysis.ExpLog.integrableOn_log_exp_neg_Ioi

open scoped Real
set_option autoImplicit false

namespace Commons.Analysis.ExpLog

/-- Sub-polynomial growth of the logarithm: for `1 ≤ w` and `0 < a`,
`log w ≤ w^a / a`. -/
theorem log_le_rpow_div {w a : ℝ} (hw : 1 ≤ w) (ha : 0 < a) : Real.log w ≤ w ^ a / a := by
  have hw0 : 0 < w := lt_of_lt_of_le zero_lt_one hw
  have hwa : 0 < w ^ a := Real.rpow_pos_of_pos hw0 a
  calc
    Real.log w = (a * Real.log w) / a := by field_simp [ha.ne']
    _ = Real.log (w ^ a) / a := by rw [Real.log_rpow hw0 a]
    _ ≤ (w ^ a - 1) / a := by
      exact (div_le_div_iff_of_pos_right ha).2 (Real.log_le_sub_one_of_pos hwa)
    _ ≤ w ^ a / a := by
      exact (div_le_div_iff_of_pos_right ha).2 (by linarith)

end Commons.Analysis.ExpLog