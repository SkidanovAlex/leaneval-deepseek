import Mathlib
import Submission.Work.Pert.PinLogDev.Prim

namespace Work.Pert.PinLogDev

/-- Centred case: if the interval `[p, p+L]` contains `0` (i.e. `-L ≤ p ≤ 0`), the integral of
`t ↦ (C + |t|)⁻¹` over it is at most `2 log (1 + L/(2C))`, its value on the symmetric interval
`[-L/2, L/2]`, which is the maximiser since the integrand is even and decreasing in `|t|`. -/
theorem G_center_le (C L p : ℝ) (hC : 0 < C) (hL : 0 ≤ L) (hp1 : -L ≤ p) (hp2 : p ≤ 0) :
    G C (p + L) - G C p ≤ 2 * Real.log (1 + L / (2 * C)) := by
  have hpL : 0 ≤ p + L := by linarith
  rw [G_of_nonneg C (p + L) hC hpL, G_of_nonpos C p hC hp2, sub_neg_eq_add]
  have h1 : (0 : ℝ) < 1 + (p + L) / C := by
    have : 0 ≤ (p + L) / C := div_nonneg hpL (le_of_lt hC)
    linarith
  have h2 : (0 : ℝ) < 1 + (-p) / C := by
    have : 0 ≤ (-p) / C := div_nonneg (by linarith) (le_of_lt hC)
    linarith
  have hprod : (1 + (p + L) / C) * (1 + (-p) / C) ≤ (1 + L / (2 * C)) ^ 2 := by
    have hC2 : (0 : ℝ) < C ^ 2 := by positivity
    have hLHS : (1 + (p + L) / C) * (1 + (-p) / C) = (C + p + L) * (C - p) / C ^ 2 := by
      field_simp
      ring
    have hRHS : (1 + L / (2 * C)) ^ 2 = (C + L / 2) ^ 2 / C ^ 2 := by
      field_simp
    rw [hLHS, hRHS]
    apply div_le_div_of_nonneg_right _ (le_of_lt hC2)
    nlinarith [sq_nonneg (p + L / 2)]
  calc Real.log (1 + (p + L) / C) + Real.log (1 + (-p) / C)
      = Real.log ((1 + (p + L) / C) * (1 + (-p) / C)) :=
        (Real.log_mul (ne_of_gt h1) (ne_of_gt h2)).symm
    _ ≤ Real.log ((1 + L / (2 * C)) ^ 2) := Real.log_le_log (mul_pos h1 h2) hprod
    _ = 2 * Real.log (1 + L / (2 * C)) := by rw [Real.log_pow]; norm_num

end Work.Pert.PinLogDev
