import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Commons.Analysis.Real

lemma product_ge_two_thirds (a b : ℝ) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hab : a + b ≤ 1) :
    2 / 3 ≤ (1 - a / 3) * (1 - b / 3) := by
  nlinarith [mul_nonneg ha0 hb0]

end Commons.Analysis.Real