import Mathlib
import Submission.Commons.NumberTheory.Linnik.exp_neg_bounds

namespace Commons.NumberTheory.Linnik

theorem linnikB_nonneg {K : ℝ} (hK : 0 < K) (x : ℝ) (hx : 0 < x) :
    0 ≤ (1 - Real.exp (-2 * K * x)) / (6 * K ^ 2 * x) +
        (2 * K * x - 1 + Real.exp (-2 * K * x)) / (2 * K ^ 2 * x ^ 2) := by
  -- t = 2*K*x is positive, hence nonnegative
  have ht : 0 ≤ 2 * K * x := by
    have h2 : (0 : ℝ) < 2 := by norm_num
    exact le_of_lt (mul_pos (mul_pos h2 hK) hx)
  have hb := exp_neg_bounds (2 * K * x) ht
  -- first numerator: 1 - exp (-2*K*x) ≥ 0
  have hA0 : 0 ≤ 1 - Real.exp (-2 * K * x) := by
    have harg : -2 * K * x = -(2 * K * x) := by ring
    rw [harg]
    exact hb.1
  -- second numerator: 2*K*x - 1 + exp (-2*K*x) ≥ 0
  have hB0 : 0 ≤ 2 * K * x - 1 + Real.exp (-2 * K * x) := by
    have harg : -2 * K * x = -(2 * K * x) := by ring
    rw [harg]
    have hsub : 2 * K * x - 1 + Real.exp (-(2 * K * x)) =
        2 * K * x - (1 - Real.exp (-(2 * K * x))) := by ring
    rw [hsub]
    exact sub_nonneg.mpr hb.2.1
  -- denominators are strictly positive
  have hpos1 : 0 < 6 * K ^ 2 * x := by
    positivity
  have hpos2 : 0 < 2 * K ^ 2 * x ^ 2 := by
    positivity
  -- each fraction is nonnegative
  have hf1 : 0 ≤ (1 - Real.exp (-2 * K * x)) / (6 * K ^ 2 * x) :=
    div_nonneg hA0 (le_of_lt hpos1)
  have hf2 : 0 ≤ (2 * K * x - 1 + Real.exp (-2 * K * x)) / (2 * K ^ 2 * x ^ 2) :=
    div_nonneg hB0 (le_of_lt hpos2)
  exact add_nonneg hf1 hf2

end Commons.NumberTheory.Linnik
