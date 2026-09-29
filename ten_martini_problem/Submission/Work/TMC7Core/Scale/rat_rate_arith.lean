import Mathlib

namespace Work.TMC7Core.Scale

theorem rat_rate_arith (C₀ q m : ℝ) (hC₀ : 0 < C₀) (hq : 1 ≤ q) (hm : 1 ≤ m) :
    Real.log m + q * C₀ + Real.log 2 ≤ (C₀ * (q + 1) + 1) * (1 + Real.log (m * q)) := by
  have hmpos : (0 : ℝ) < m := by linarith
  have hqpos : (0 : ℝ) < q := by linarith
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg hm
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq
  have hlogmq : Real.log (m * q) = Real.log m + Real.log q :=
    Real.log_mul (ne_of_gt hmpos) (ne_of_gt hqpos)
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  set A : ℝ := C₀ * (q + 1) + 1 with hAdef
  have hA1 : 1 ≤ A := by rw [hAdef]; nlinarith [hC₀, hq]
  have hApos : 0 < A := by linarith
  have h1 : Real.log m ≤ A * Real.log m := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ A - 1) hlogm]
  have h2 : 0 ≤ A * Real.log q := mul_nonneg (le_of_lt hApos) hlogq
  have h3 : q * C₀ + Real.log 2 ≤ A := by
    rw [hAdef]; nlinarith [hC₀, hq, hlog2]
  rw [hlogmq]
  have hrew : A * (1 + (Real.log m + Real.log q)) = A + A * Real.log m + A * Real.log q := by
    ring
  rw [hrew]
  linarith [h1, h2, h3]

end Work.TMC7Core.Scale
