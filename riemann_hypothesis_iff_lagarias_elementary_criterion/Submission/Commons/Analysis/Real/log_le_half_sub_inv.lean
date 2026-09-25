import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

namespace Commons.Analysis.Real

/-- Elementary logarithmic inequality: for `u ≥ 1`, `log u ≤ (u - u⁻¹)/2`.
Proof route: put `x = log u ≥ 0`; then `u = exp x` and `u⁻¹ = exp (-x)`, so the claim is
`x ≤ Real.sinh x`, which is `Real.self_le_sinh_iff`. Use `Real.sinh_eq` (or `Real.sinh_log`) to convert
`Real.sinh (Real.log u)` into `(u - u⁻¹)/2`. -/
theorem log_le_half_sub_inv {u : ℝ} (hu : 1 ≤ u) : Real.log u ≤ (u - u⁻¹) / 2 := by
  have hpos : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hlog : 0 ≤ Real.log u := Real.log_nonneg hu
  have h1 : Real.log u ≤ Real.sinh (Real.log u) := (Real.self_le_sinh_iff).mpr hlog
  rwa [Real.sinh_log hpos] at h1

end Commons.Analysis.Real