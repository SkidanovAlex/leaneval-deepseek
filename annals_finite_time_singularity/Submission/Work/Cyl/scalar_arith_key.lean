import Mathlib.Algebra.Order.Star.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Cyl

theorem scalar_arith_key (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : |c| ≤ a * b) :
    0 ≤ 2 * a ^ 3 + a * b ^ 2 + c * (b - 4 * a) := by
  obtain ⟨hc1, hc2⟩ := abs_le.mp hc
  have hcl : -(a * b) ≤ c := by linarith
  rcases le_total (4 * a) b with h | h
  · have hd : 0 ≤ b - 4 * a := by linarith
    have hprod : -(a * b) * (b - 4 * a) ≤ c * (b - 4 * a) :=
      mul_le_mul_of_nonneg_right hcl hd
    have key : 0 ≤ 2 * a ^ 3 + a * b ^ 2 + -(a * b) * (b - 4 * a) := by
      nlinarith [mul_nonneg (sq_nonneg a) (by linarith : (0 : ℝ) ≤ a + 2 * b)]
    nlinarith [hprod, key]
  · have hd : b - 4 * a ≤ 0 := by linarith
    have hprod : a * b * (b - 4 * a) ≤ c * (b - 4 * a) :=
      mul_le_mul_of_nonpos_right hc2 hd
    have key : 0 ≤ 2 * a ^ 3 + a * b ^ 2 + a * b * (b - 4 * a) := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * a) (sq_nonneg (a - b))]
    nlinarith [hprod, key]

end Work.Cyl
