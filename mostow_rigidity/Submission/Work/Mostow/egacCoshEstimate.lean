import Mathlib

namespace Work.Mostow

/-- For `x ≥ 0` we have `cosh x - 1 ≥ x ^ 2 / 2`.
Proof: `cosh (2 y) - 1 = 2 * sinh y ^ 2` (from `cosh_two_mul` and `cosh_sq_sub_sinh_sq`)
and `sinh y ≥ y` for `y ≥ 0`. -/
lemma cosh_sub_one_ge_sq_div_two (x : ℝ) (hx : 0 ≤ x) :
    x ^ 2 / 2 ≤ Real.cosh x - 1 := by
  have hx2 : (0 : ℝ) ≤ x / 2 := by linarith
  have hsinh : x / 2 ≤ Real.sinh (x / 2) := Real.self_le_sinh_iff.mpr hx2
  have hsq : (x / 2) ^ 2 ≤ (Real.sinh (x / 2)) ^ 2 := pow_le_pow_left₀ hx2 hsinh 2
  have h2 := Real.cosh_two_mul (x / 2)
  have hsub := Real.cosh_sq_sub_sinh_sq (x / 2)
  have hxeq : 2 * (x / 2) = x := by ring
  rw [hxeq] at h2
  have key : Real.cosh x - 1 = 2 * (Real.sinh (x / 2)) ^ 2 := by linarith
  rw [key]
  nlinarith [hsq]

theorem egacCoshEstimate {η a : ℝ} (hη : 0 < η) (ha0 : 0 ≤ a) (ha : a ≤ 3 * η / 16) :
    (Real.exp 1) ^ 2 / 2 * a ^ 2 < Real.cosh η - 1 := by
  have hcosh : η ^ 2 / 2 ≤ Real.cosh η - 1 := cosh_sub_one_ge_sq_div_two η hη.le
  -- `exp 1 * a < η`, using `exp 1 < 3`, `a ≤ 3η/16` and `9/16 < 1`.
  have hea_lt : Real.exp 1 * a < η := by
    have h1 : Real.exp 1 * a ≤ 3 * a :=
      mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le ha0
    have h2 : (3 : ℝ) * a ≤ 3 * (3 * η / 16) := by linarith
    have h3 : 3 * (3 * η / 16) < η := by linarith
    linarith
  have hsq_lt : (Real.exp 1 * a) ^ 2 < η ^ 2 :=
    pow_lt_pow_left₀ hea_lt (mul_nonneg (Real.exp_pos 1).le ha0) (by norm_num)
  have heq : (Real.exp 1) ^ 2 / 2 * a ^ 2 = (Real.exp 1 * a) ^ 2 / 2 := by ring
  rw [heq]
  linarith

end Work.Mostow
