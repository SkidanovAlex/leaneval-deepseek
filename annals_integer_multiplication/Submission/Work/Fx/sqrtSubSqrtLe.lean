import Mathlib

namespace Work.Fx

/-- Standard Lipschitz estimate for `Real.sqrt` against a positive lower bound for `√x`:
`|√x - √y| * δ ≤ |x - y|`.  No hypotheses on the sign of `x` are needed beyond `δ ≤ √x`. -/
theorem sqrtSubSqrtLe {x y δ : ℝ} (hδ : 0 < δ) (hx : δ ≤ Real.sqrt x) (hy : 0 ≤ y) :
    |Real.sqrt x - Real.sqrt y| ≤ |x - y| / δ := by
  have ha : 0 < Real.sqrt x := lt_of_lt_of_le hδ hx
  have hx0 : 0 ≤ x := le_of_lt (Real.sqrt_pos.mp ha)
  have hb : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hprod : x - y = (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y) := by
    conv_lhs => rw [← Real.sq_sqrt hx0, ← Real.sq_sqrt hy]
    ring
  have habs : |x - y| = |Real.sqrt x - Real.sqrt y| * |Real.sqrt x + Real.sqrt y| := by
    rw [hprod, abs_mul]
  have hsum_abs : |Real.sqrt x + Real.sqrt y| = Real.sqrt x + Real.sqrt y :=
    abs_of_nonneg (add_nonneg ha.le hb)
  rw [le_div_iff₀ hδ, habs, hsum_abs]
  exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)

end Work.Fx
