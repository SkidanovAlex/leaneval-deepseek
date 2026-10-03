import Mathlib
import Submission.Commons.Analysis.Integral.integral_sqrt_one_sub_pow_four_ge

namespace Commons.Analysis.SpecialFunctions

open scoped Interval

/-- A published commons lower bound for the lemniscatic integral:
`∫₀¹ √(1-u⁴) du ≥ 87215/100000`.  Combining it with the upper bound
`π < 3.1416` yields `4 · ∫₀¹ √(1-u⁴) du / π > 1.11`. -/
theorem four_kappa_div_pi_gt :
    (1.11 : ℝ) < 4 * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) / Real.pi := by
  have hI : (87215 : ℝ) / 100000 ≤ ∫ u in (0)..1, Real.sqrt (1 - u ^ 4) :=
    Commons.Analysis.Integral.integral_sqrt_one_sub_pow_four_ge
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi_lt : Real.pi < (3.1416 : ℝ) := Real.pi_lt_d4
  have hkey : 4 * ((87215 : ℝ) / 100000) / (3.1416 : ℝ)
      < 4 * ((87215 : ℝ) / 100000) / Real.pi := by
    have h1 : (1 : ℝ) / (3.1416 : ℝ) < 1 / Real.pi :=
      one_div_lt_one_div_of_lt hpi_pos hpi_lt
    have hc : (0 : ℝ) < 4 * ((87215 : ℝ) / 100000) := by norm_num
    calc 4 * ((87215 : ℝ) / 100000) / (3.1416 : ℝ)
        = 4 * ((87215 : ℝ) / 100000) * (1 / (3.1416 : ℝ)) := by ring
      _ < 4 * ((87215 : ℝ) / 100000) * (1 / Real.pi) :=
          mul_lt_mul_of_pos_left h1 hc
      _ = 4 * ((87215 : ℝ) / 100000) / Real.pi := by ring
  have hle : 4 * ((87215 : ℝ) / 100000) / Real.pi
      ≤ 4 * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) / Real.pi :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hI (by norm_num)) hpi_pos.le
  have hnum : (1.11 : ℝ) < 4 * ((87215 : ℝ) / 100000) / (3.1416 : ℝ) := by
    norm_num
  linarith

end Commons.Analysis.SpecialFunctions
