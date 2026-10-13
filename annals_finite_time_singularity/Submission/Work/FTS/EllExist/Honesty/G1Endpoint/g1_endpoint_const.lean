import Mathlib.Algebra.Order.Star.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.FTS.EllExist.Honesty.G1Endpoint

/-- For `0 ≤ A` and `0 < b` one has `A / b ≤ (A / 2 + 1 / (2b))²`; the difference of the
two sides is the manifestly nonnegative quantity `b * (A / 2 - 1 / (2b))²`. -/
theorem g1_endpoint_const {A b : ℝ} (hA : 0 ≤ A) (hb : 0 < b) :
    A / b ≤ (A / 2 + 1 / (2 * b)) ^ 2 := by
  have h : 0 ≤ b * (A / 2 - 1 / (2 * b)) ^ 2 :=
    mul_nonneg (le_of_lt hb) (sq_nonneg _)
  have hexp : b * (A / 2 - 1 / (2 * b)) ^ 2 = (A / 2 + 1 / (2 * b)) ^ 2 * b - A := by
    field_simp
    ring
  rw [div_le_iff₀ hb]
  linarith [h, hexp]

end Work.FTS.EllExist.Honesty.G1Endpoint
