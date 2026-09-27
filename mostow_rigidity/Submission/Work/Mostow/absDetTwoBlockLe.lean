import Mathlib

namespace Work.Mostow

/-- For `a ≡ b` modulo `2π`, the determinant of the `2 × 2` block
`!![cos a - 1, -sin b; sin a, cos b - 1]` is bounded by `2 - 2 cos a`; in fact it is
exactly `2 - 2 cos a ≥ 0`. -/
theorem absDetTwoBlockLe {a b : ℝ} (hab : (a : AddCircle (2 * Real.pi)) = (b : AddCircle (2 * Real.pi))) :
    |(!![Real.cos a - 1, -Real.sin b; Real.sin a, Real.cos b - 1] : Matrix (Fin 2) (Fin 2) ℝ).det| ≤ 2 - 2 * Real.cos a := by
  -- `AddCircle (2π) = Real.Angle`, and `cos`/`sin` descend to the circle
  have hcos : Real.cos b = Real.cos a := by
    have h : Real.Angle.cos (a : Real.Angle) = Real.Angle.cos (b : Real.Angle) := by
      rw [show (a : Real.Angle) = (b : Real.Angle) from hab]
    simpa [Real.Angle.cos_coe] using h.symm
  have hsin : Real.sin b = Real.sin a := by
    have h : Real.Angle.sin (a : Real.Angle) = Real.Angle.sin (b : Real.Angle) := by
      rw [show (a : Real.Angle) = (b : Real.Angle) from hab]
    simpa [Real.Angle.sin_coe] using h.symm
  have hdet : (!![Real.cos a - 1, -Real.sin b; Real.sin a, Real.cos b - 1] : Matrix (Fin 2) (Fin 2) ℝ).det
      = 2 - 2 * Real.cos a := by
    rw [Matrix.det_fin_two, hcos, hsin]
    simp
    nlinarith [Real.sin_sq_add_cos_sq a]
  rw [hdet, abs_of_nonneg]
  nlinarith [Real.cos_le_one a]

end Work.Mostow
