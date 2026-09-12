import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.SpecialFunctions

/-- `(π/2)^p · 2^(p/2) = (π/√2)^p` for all real `p`. -/
theorem pi_sqrt2_rpow_assembly (p : ℝ) :
    (Real.pi / 2) ^ p * (2 : ℝ) ^ (p / 2) = (Real.pi / Real.sqrt 2) ^ p := by
  have h2 : 0 ≤ (2 : ℝ) := by norm_num
  have hpi2 : 0 ≤ Real.pi / 2 := div_nonneg (le_of_lt Real.pi_pos) (by norm_num)
  have hsqrt2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := Real.mul_self_sqrt h2
  have hsqrt2ne : Real.sqrt 2 ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  calc
    (Real.pi / 2) ^ p * (2 : ℝ) ^ (p / 2)
        = (Real.pi / 2) ^ p * (Real.sqrt 2) ^ p := by
          congr 1
          exact Real.rpow_div_two_eq_sqrt p h2
    _ = ((Real.pi / 2) * Real.sqrt 2) ^ p := by
          exact (Real.mul_rpow hpi2 hsqrt2).symm
    _ = (Real.pi / Real.sqrt 2) ^ p := by
          congr 1
          field_simp [hsqrt2ne]
          rw [pow_two, hs]

end Commons.Analysis.SpecialFunctions