import Mathlib.Algebra.Order.Star.Real

namespace Commons.Analysis.Inequalities

theorem two_point_four (ρ a b : ℝ) (hρ : ρ ^ 2 ≤ 1 / 3) :
    (a + ρ * b) ^ 4 + (a - ρ * b) ^ 4 ≤ 2 * (a ^ 2 + b ^ 2) ^ 2 := by
  have h4 : ρ ^ 4 ≤ 1 := by nlinarith [sq_nonneg ρ, hρ, sq_nonneg (ρ ^ 2 - 1)]
  nlinarith [hρ, h4, sq_nonneg (a * b), sq_nonneg (a ^ 2 * b ^ 2), sq_nonneg (b ^ 2),
    sq_nonneg (a ^ 2), sq_nonneg (ρ ^ 2 * a ^ 2 * b ^ 2)]

end Commons.Analysis.Inequalities