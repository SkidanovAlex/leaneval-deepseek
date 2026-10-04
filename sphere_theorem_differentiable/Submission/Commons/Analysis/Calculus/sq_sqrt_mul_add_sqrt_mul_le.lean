import Mathlib.Algebra.Order.Star.Real

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Calculus

/-- Cauchy--Schwarz in `ℝ²` in square-root form: for nonnegative `a b c d`,
`(√a * √c + √b * √d) ^ 2 ≤ (a + b) * (c + d)`. -/
theorem sq_sqrt_mul_add_sqrt_mul_le {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) :
    (Real.sqrt a * Real.sqrt c + Real.sqrt b * Real.sqrt d) ^ 2 ≤ (a + b) * (c + d) := by
  have h1 : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha
  have h2 : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb
  have h3 : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt hc
  have h4 : (Real.sqrt d) ^ 2 = d := Real.sq_sqrt hd
  nlinarith [sq_nonneg (Real.sqrt a * Real.sqrt d - Real.sqrt b * Real.sqrt c)]

end Commons.Analysis.Calculus