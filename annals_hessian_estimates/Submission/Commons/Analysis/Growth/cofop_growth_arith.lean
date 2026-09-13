import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Growth

set_option linter.unusedVariables false in
/-- Arithmetic core for the `cofop` (co-factor / off-diagonal) growth estimate.

Writing the bracket in expanded form gives
`3*(-τ-1)*s + (((p+1)*τ-1) + 2*(-τ-1))*(w-s) = ((p-1)*τ-3)*w - (p+2)*τ*s`
(it is the real-variable skeleton of a quadratic-in-`τ` identity).  Hence the
whole expression equals `w*(c - 3*ε*a*(τ+1)) + ε*a*(p+2)*τ*(w-s)`, which is a
sum of two nonnegative terms: `c ≥ 12*ε*a*2^(p+2)` dominates `3*ε*a*(τ+1)`
because `τ+1 ≤ 4*2^(p+2)`, and `w - s ≥ 0`. -/
theorem cofop_growth_arith {a c p τ s w ε : ℝ} (hc : 0 < c) (ha : 0 < a) (hε : 0 < ε) (hs : 0 ≤ s) (hsw : s ≤ w) (hτ1 : 1 ≤ τ) (hτ2 : τ ≤ 2 ^ (p + 2)) (hp : 4 ≤ p) (hεa : 12 * ε * a * 2 ^ (p + 2) ≤ c) : 0 ≤ c * w + ε * (a * ((3 * (-τ - 1)) * s + (((p + 1) * τ - 1) + 2 * (-τ - 1)) * (w - s))) := by
  have hw : 0 ≤ w := le_trans hs hsw
  have hτpos : 0 < τ := lt_of_lt_of_le one_pos hτ1
  have hT1 : (1:ℝ) ≤ 2 ^ (p + 2) := Real.one_le_rpow (by norm_num) (by linarith)
  have hτ1' : τ + 1 ≤ 4 * 2 ^ (p + 2) := by nlinarith [hτ2, hT1]
  have h3ea : 0 ≤ 3 * ε * a := by nlinarith [hε, ha]
  have hkey : 3 * ε * a * (τ + 1) ≤ c := by
    have h1 : 3 * ε * a * (τ + 1) ≤ 3 * ε * a * (4 * 2 ^ (p + 2)) :=
      mul_le_mul_of_nonneg_left hτ1' h3ea
    have h2 : 3 * ε * a * (4 * 2 ^ (p + 2)) = 12 * ε * a * 2 ^ (p + 2) := by ring
    linarith [h1, h2, hεa]
  have hE : c * w + ε * (a * ((3 * (-τ - 1)) * s + (((p + 1) * τ - 1) + 2 * (-τ - 1)) * (w - s)))
      = w * (c - 3 * ε * a * (τ + 1)) + ε * a * (p + 2) * τ * (w - s) := by ring
  rw [hE]
  have h1 : 0 ≤ w * (c - 3 * ε * a * (τ + 1)) := by
    apply mul_nonneg hw
    linarith [hkey]
  have h2 : 0 ≤ ε * a * (p + 2) * τ * (w - s) := by
    have hws : 0 ≤ w - s := by linarith [hsw]
    have hp2 : 0 ≤ p + 2 := by linarith [hp]
    have hea : 0 ≤ ε * a := by nlinarith [hε, ha]
    have hτ0 : 0 ≤ τ := le_of_lt hτpos
    apply mul_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · exact hea
        · exact hp2
      · exact hτ0
    · exact hws
  linarith [h1, h2]

end Commons.Analysis.Growth