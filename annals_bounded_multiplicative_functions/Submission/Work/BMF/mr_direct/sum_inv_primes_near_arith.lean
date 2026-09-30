import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/--
Elementary arithmetic input for the short-interval prime-reciprocal estimate: since
`exp (-(1/K)) = exp (1/K)⁻¹`, the left-hand side rewrites as
`2 * exp (1/K) - 2 + (1 + exp (1/K)) / A`, and each piece is then bounded using
`Real.abs_exp_sub_one_le` (together with `1/K ≤ 1`) and `exp (1/K) < 3`.
-/
lemma sum_inv_primes_near_arith (A K : ℝ) (hA : 0 < A) (hK : 1 ≤ K) :
    (A + 1 - A * Real.exp (-(1 / K))) / (A * Real.exp (-(1 / K))) +
      (A * Real.exp (1 / K) + 1 - A) / A ≤ 16 * (1 / K + 1 / A) := by
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK
  set y := Real.exp (1 / K) with hydef
  set x := Real.exp (-(1 / K)) with hxdef
  have hxy : x * y = 1 := by
    rw [hxdef, hydef, ← Real.exp_add]
    have : -(1 / K) + 1 / K = 0 := by ring
    rw [this, Real.exp_zero]
  have hypos : 0 < y := Real.exp_pos _
  have hxeq : x = y⁻¹ := eq_inv_of_mul_eq_one_right (by rw [mul_comm]; exact hxy)
  have hmain : (A + 1 - A * x) / (A * x) + (A * y + 1 - A) / A = 2 * y - 2 + (1 + y) / A := by
    rw [hxeq]
    field_simp
    ring
  rw [hmain]
  have htpos : 0 < 1 / K := by positivity
  have htle : 1 / K ≤ 1 := by rw [div_le_one hKpos]; linarith
  have hyle : y ≤ 3 := by
    have h1 : y ≤ Real.exp 1 := Real.exp_le_exp.mpr htle
    linarith [Real.exp_one_lt_three]
  have hb : |y - 1| ≤ 2 * (1 / K) := by
    have h2 := Real.abs_exp_sub_one_le (x := 1 / K) (by rw [abs_of_pos htpos]; exact htle)
    rw [abs_of_pos htpos, ← hydef] at h2
    exact h2
  have hexp_le : y - 1 ≤ 2 * (1 / K) := le_trans (le_abs_self _) hb
  have hb1 : 2 * y - 2 ≤ 16 * (1 / K) := by
    have h2 : 2 * y - 2 ≤ 4 * (1 / K) := by nlinarith [hexp_le]
    have h4 : 4 * (1 / K) ≤ 16 * (1 / K) := by
      apply mul_le_mul_of_nonneg_right (by norm_num : (4:ℝ) ≤ 16) htpos.le
    linarith [h2, h4]
  have hb2 : (1 + y) / A ≤ 16 * (1 / A) := by
    have h : (1 + y) / A ≤ 16 / A := div_le_div_of_nonneg_right (by linarith) hA.le
    have e : (16:ℝ) / A = 16 * (1 / A) := by ring
    linarith [h, e]
  calc 2 * y - 2 + (1 + y) / A ≤ 16 * (1 / K) + 16 * (1 / A) := add_le_add hb1 hb2
    _ = 16 * (1 / K + 1 / A) := by ring

end Work.BMF.mr_direct
