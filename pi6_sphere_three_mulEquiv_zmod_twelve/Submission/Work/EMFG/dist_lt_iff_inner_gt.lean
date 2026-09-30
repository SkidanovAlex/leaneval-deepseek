import Mathlib

namespace Work.EMFG

/-- For unit vectors `x`, `y` and `ε > 0`, the distance between `x` and `y` is less than `ε`
exactly when their inner product exceeds `1 - ε²/2`.

This is the elementary translation of `‖x - y‖² = 2 - 2⟪x, y⟫` (valid because `‖x‖ = ‖y‖ = 1`)
together with the fact that `t ↦ t²` is strictly increasing on the nonnegative reals and
`‖x - y‖ ≥ 0`, `ε > 0`. -/
theorem dist_lt_iff_inner_gt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    dist x y < ε ↔ 1 - ε ^ 2 / 2 < inner ℝ x y := by
  -- The squared distance between two unit vectors.
  have hnorm : ‖x - y‖ ^ 2 = 2 - 2 * inner ℝ x y := by
    rw [norm_sub_sq (𝕜 := ℝ), hx, hy]
    simp
    ring
  -- On the nonnegative reals, `t < ε` is equivalent to `t ^ 2 < ε ^ 2`.
  have hsq : ‖x - y‖ < ε ↔ ‖x - y‖ ^ 2 < ε ^ 2 := by
    rw [sq_lt_sq, abs_of_nonneg (norm_nonneg _), abs_of_pos hε]
  rw [dist_eq_norm, hsq, hnorm]
  constructor <;> intro h <;> linarith

end Work.EMFG
