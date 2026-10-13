import Mathlib.Algebra.Order.Star.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

/-- If `0 < α ≤ 1` and `X, P, Q ≥ 0` satisfy `X ≤ 4P + α²Q + (α²)⁻¹P`, then
`α² X ≤ 9 (P + α⁴ Q)`: indeed `α²X ≤ 4α²P + α⁴Q + P ≤ 5P + α⁴Q` since `α² ≤ 1`. -/
theorem AgmonArith {α X P Q : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hX : 0 ≤ X) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (h : X ≤ 4 * P + α ^ 2 * Q + (α ^ 2)⁻¹ * P) :
    α ^ 2 * X ≤ 9 * (P + α ^ 4 * Q) := by
  have hα2pos : 0 < α ^ 2 := by positivity
  have hα2le : α ^ 2 ≤ 1 := by nlinarith
  have hα4nn : 0 ≤ α ^ 4 := by positivity
  -- multiply through by `α ^ 2 ≥ 0`
  have h1 : α ^ 2 * X ≤ α ^ 2 * (4 * P + α ^ 2 * Q + (α ^ 2)⁻¹ * P) :=
    mul_le_mul_of_nonneg_left h (le_of_lt hα2pos)
  -- distribute and cancel `α ^ 2 * (α ^ 2)⁻¹`
  have h2 : α ^ 2 * (4 * P + α ^ 2 * Q + (α ^ 2)⁻¹ * P)
      = 4 * (α ^ 2 * P) + α ^ 4 * Q + P := by
    field_simp
  rw [h2] at h1
  -- now `4 α² P + α⁴ Q + P ≤ 9 (P + α⁴ Q)` since `α² ≤ 1`
  nlinarith [mul_nonneg hα4nn hQ]

end Work.FTS.EllipticEst.Blocks
