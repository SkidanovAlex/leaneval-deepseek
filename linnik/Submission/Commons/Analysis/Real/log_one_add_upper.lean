import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Commons.Analysis.Real

/-- For `0 ≤ u`, `log (1 + u) ≤ u`. This is the standard upper bound
`log x ≤ x - 1` applied at `x = 1 + u`. -/
theorem log_one_add_upper {u : ℝ} (hu0 : 0 ≤ u) :
    Real.log (1 + u) ≤ u := by
  have hpos : 0 < 1 + u := by linarith
  have h := Real.log_le_sub_one_of_pos hpos
  linarith

end Commons.Analysis.Real