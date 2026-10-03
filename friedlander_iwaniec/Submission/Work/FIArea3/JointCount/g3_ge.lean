import Mathlib

namespace Work.FIArea3.JointCount

/-- Taylor lower bound of order two for the exponential: `1 + x + x²/2 ≤ exp x`
for `x ≥ 0`. -/
lemma exp_quad_le_exp (x : ℝ) (hx : 0 ≤ x) : 1 + x + x ^ 2 / 2 ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg (x := x) hx 3
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero] at h
  linarith

/-- Taylor lower bound of order three for the exponential: `1 + x + x²/2 + x³/6 ≤ exp x`
for `x ≥ 0`. -/
lemma exp_cubic_le_exp (x : ℝ) (hx : 0 ≤ x) :
    1 + x + x ^ 2 / 2 + x ^ 3 / 6 ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg (x := x) hx 4
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero] at h
  linarith

/-- A numerical lower bound for `exp 3`, obtained from its Taylor series. -/
lemma exp_three_ge_twenty : (20 : ℝ) ≤ Real.exp 3 := by
  have h := Real.sum_le_exp_of_nonneg (x := (3 : ℝ)) (by norm_num) 9
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero] at h
  linarith

/-- The key elementary inequality: for `0 < v < 4` one has
`12 * v ≤ exp v * (9 - 2 * v)`.  Equivalently `exp v * (3/(2v) - 1/3) ≥ 2`. -/
lemma twelve_mul_le (v : ℝ) (hv : 0 < v) (hv4 : v < 4) :
    12 * v ≤ Real.exp v * (9 - 2 * v) := by
  rcases le_or_gt v 2 with h2 | h2
  · -- `v ≤ 2`: use `exp v ≥ 1 + v + v²/2`.
    have hexp : 1 + v + v ^ 2 / 2 ≤ Real.exp v := exp_quad_le_exp v (le_of_lt hv)
    have h9 : (0 : ℝ) ≤ 9 - 2 * v := by linarith
    have hmul : (1 + v + v ^ 2 / 2) * (9 - 2 * v) ≤ Real.exp v * (9 - 2 * v) :=
      mul_le_mul_of_nonneg_right hexp h9
    have hpoly : (12 * v : ℝ) ≤ (1 + v + v ^ 2 / 2) * (9 - 2 * v) := by
      nlinarith [sq_nonneg v, sq_nonneg (v - 2),
        mul_nonneg (le_of_lt hv) (sub_nonneg.mpr h2)]
    linarith
  rcases le_or_gt v 3 with h3 | h3
  · -- `2 ≤ v ≤ 3`: use `exp v ≥ 1 + v + v²/2 + v³/6`.
    have hexp : 1 + v + v ^ 2 / 2 + v ^ 3 / 6 ≤ Real.exp v :=
      exp_cubic_le_exp v (le_of_lt hv)
    have h9 : (0 : ℝ) ≤ 9 - 2 * v := by linarith
    have hmul : (1 + v + v ^ 2 / 2 + v ^ 3 / 6) * (9 - 2 * v) ≤ Real.exp v * (9 - 2 * v) :=
      mul_le_mul_of_nonneg_right hexp h9
    have hpoly : (12 * v : ℝ) ≤ (1 + v + v ^ 2 / 2 + v ^ 3 / 6) * (9 - 2 * v) := by
      nlinarith [sq_nonneg v, mul_nonneg (sub_nonneg.mpr (le_of_lt h2)) (sub_nonneg.mpr h3)]
    linarith
  · -- `3 < v < 4`: split `v = 3 + t` and use `exp (3+t) ≥ exp 3 * (1 + t + t²/2)`
    -- together with `exp 3 ≥ 20`.
    have ht0 : 0 ≤ v - 3 := by linarith
    have ht1 : v - 3 ≤ 1 := by linarith
    have htge : 1 + (v - 3) + (v - 3) ^ 2 / 2 ≤ Real.exp (v - 3) :=
      exp_quad_le_exp (v - 3) ht0
    have hsplit : Real.exp v = Real.exp 3 * Real.exp (v - 3) := by
      conv_lhs => rw [show v = 3 + (v - 3) by ring]
      rw [Real.exp_add]
    have h9 : (0 : ℝ) < 9 - 2 * v := by linarith
    have hnn : (0 : ℝ) ≤ 1 + (v - 3) + (v - 3) ^ 2 / 2 := by nlinarith [sq_nonneg (v - 3)]
    have hA : 20 * (1 + (v - 3) + (v - 3) ^ 2 / 2)
        ≤ Real.exp 3 * (1 + (v - 3) + (v - 3) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right exp_three_ge_twenty hnn
    have hB : Real.exp 3 * (1 + (v - 3) + (v - 3) ^ 2 / 2)
        ≤ Real.exp 3 * Real.exp (v - 3) :=
      mul_le_mul_of_nonneg_left htge (Real.exp_pos 3).le
    have hC : 20 * (1 + (v - 3) + (v - 3) ^ 2 / 2) ≤ Real.exp 3 * Real.exp (v - 3) :=
      le_trans hA hB
    have hstep : 20 * (1 + (v - 3) + (v - 3) ^ 2 / 2) * (9 - 2 * v) ≤ Real.exp v * (9 - 2 * v) := by
      rw [hsplit]
      exact mul_le_mul_of_nonneg_right hC (le_of_lt h9)
    have hpoly : (12 * v : ℝ) ≤ 20 * (1 + (v - 3) + (v - 3) ^ 2 / 2) * (9 - 2 * v) := by
      have h := mul_nonneg (mul_nonneg ht0 (sub_nonneg.mpr ht1))
        (by linarith : (0 : ℝ) ≤ 1 + (v - 3))
      nlinarith [h, ht0, ht1]
    linarith

/-- `g3_ge`: for `0 < v < 4` one has `exp v * (3/(2v) - 1/3) ≥ 2`. -/
theorem g3_ge (v : ℝ) (hv : 0 < v) (hv2 : v < 4) :
    (2:ℝ) ≤ Real.exp v * (1.5/v - 1/3) := by
  have h : (1.5 : ℝ) / v - 1/3 = (9 - 2 * v) / (6 * v) := by
    field_simp
    ring
  rw [h, ← mul_div_assoc]
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < 6 * v)]
  have hkey := twelve_mul_le v hv hv2
  linarith

end Work.FIArea3.JointCount
