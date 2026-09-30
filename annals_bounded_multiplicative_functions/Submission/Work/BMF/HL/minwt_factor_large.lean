import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.HL

/-- For `y ≥ 11`, `Real.log y > 1`, so `min 1 (1 / Real.log y) = 1 / Real.log y`
and the displayed factor is exactly `1`. -/
theorem minwt_factor_large {CI y : ℝ} (hCI : 0 < CI) (hy : 11 ≤ y) :
    (2 / min 1 (1 / Real.log y)) * CI / Real.log (y ^ 2) ≤ CI := by
  have h1 : (1 : ℝ) < Real.log 11 := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_three])
  have h2 : Real.log 11 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hlogy : 1 < Real.log y := lt_of_lt_of_le h1 h2
  have hpos : 0 < Real.log y := lt_trans one_pos hlogy
  have hle : 1 / Real.log y ≤ 1 := by
    rw [div_le_one hpos]; linarith
  rw [min_eq_right hle, Real.log_pow]
  have hne : Real.log y ≠ 0 := ne_of_gt hpos
  field_simp
  norm_num

end Work.BMF.HL
