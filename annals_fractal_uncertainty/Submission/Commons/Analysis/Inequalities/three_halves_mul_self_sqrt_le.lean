import Mathlib.Algebra.Order.Star.Real

namespace Commons.Analysis.Inequalities

theorem three_halves_mul_self_sqrt_le (x : ℝ) (hx : 0 ≤ x) : (3 / 2) * (x * Real.sqrt x) ≤ 1 + x ^ 2 := by
  set s := Real.sqrt x with hs
  have hs0 : 0 ≤ s := by
    rw [hs]; exact Real.sqrt_nonneg x
  have hxs : x = s ^ 2 := by
    rw [hs, Real.sq_sqrt hx]
  rw [hxs]
  have hkey : 2 * (1 + (s ^ 2) ^ 2) - 3 * (s ^ 2 * s)
      = (s - 9 / 8) ^ 2 * (2 * s ^ 2 + (3 / 2) * s + 27 / 32) + 1909 / 2048 := by
    ring
  have hsq : 0 ≤ (s - 9 / 8) ^ 2 := sq_nonneg _
  have hquad : 0 ≤ 2 * s ^ 2 + (3 / 2) * s + 27 / 32 := by nlinarith [hs0]
  have hprod : 0 ≤ (s - 9 / 8) ^ 2 * (2 * s ^ 2 + (3 / 2) * s + 27 / 32) :=
    mul_nonneg hsq hquad
  nlinarith [hprod, hkey]

end Commons.Analysis.Inequalities