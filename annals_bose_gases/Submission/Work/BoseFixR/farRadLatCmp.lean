import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR

theorem farRadLatCmp {A B W x c1 : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hc1 : 0 < c1)
    (hx : 10 * c1 ≤ x) :
    W ^ 2 / (A * (x - 2 * c1) ^ 2 + B) ≤ (25 / (8 * A)) * (W ^ 2 / (2 * x ^ 2)) := by
  -- The denominator `D = A * (x - 2*c1)^2 + B` is positive: `A > 0`, `x - 2*c1 > 0`,
  -- and `B ≥ 0`.
  have hxd : 0 < x - 2 * c1 := by linarith
  have hDpos : 0 < A * (x - 2 * c1) ^ 2 + B := by
    have h := pow_pos hxd 2
    nlinarith [mul_pos hA h]
  -- Key numerical inequality: `16 x^2 ≤ 25 (x - 2 c1)^2` for `x ≥ 10 c1`.
  -- Equivalently `(x - 10 c1) * (9 x - 10 c1) ≥ 0`.
  have h1 : 16 * x ^ 2 ≤ 25 * (x - 2 * c1) ^ 2 := by nlinarith
  -- Multiply by `A > 0` and drop the nonnegative `B`.
  have hkey : 16 * A * x ^ 2 ≤ 25 * (A * (x - 2 * c1) ^ 2 + B) := by
    nlinarith [mul_le_mul_of_nonneg_left h1 (le_of_lt hA), hB]
  have hxpos : 0 < x := by linarith
  have hTpos : 0 < 16 * A * x ^ 2 := by
    have h := mul_pos hA (pow_pos hxpos 2)
    linarith
  -- Rewrite the right hand side as a single fraction.
  rw [show (25 / (8 * A)) * (W ^ 2 / (2 * x ^ 2)) = 25 * W ^ 2 / (16 * A * x ^ 2) by
        field_simp; ring]
  -- Cross-multiply the two positive denominators and conclude with `W ^ 2 ≥ 0`.
  rw [div_le_div_iff₀ hDpos hTpos]
  nlinarith [mul_le_mul_of_nonneg_left hkey (sq_nonneg W)]

end Work.BoseFixR
