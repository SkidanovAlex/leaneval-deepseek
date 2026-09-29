import Submission.Work.TMC7Core.Cocycle

namespace Work.TMC7Core.Cocycle

/-- The Frobenius norm of a determinant-one `2 × 2` complex matrix is at least `√2`,
with equality exactly for the orthogonal matrices.

Proof: writing `a,b,c,d` for the entries, AM–GM gives
`|a|² + |d|² ≥ 2|a||d|` and `|b|² + |c|² ≥ 2|b||c|`, while
`1 = |det A| = |ad - bc| ≤ |a||d| + |b||c|`. -/
theorem frob_sqrt_two_le_of_det_one {A : Matrix (Fin 2) (Fin 2) ℂ} (h : A.det = 1) : Real.sqrt 2 ≤ frob A := by
  have h11 : 2 * ‖A 0 0‖ * ‖A 1 1‖ ≤ ‖A 0 0‖ ^ 2 + ‖A 1 1‖ ^ 2 := by
    nlinarith [sq_nonneg (‖A 0 0‖ - ‖A 1 1‖), norm_nonneg (A 0 0), norm_nonneg (A 1 1)]
  have h10 : 2 * ‖A 0 1‖ * ‖A 1 0‖ ≤ ‖A 0 1‖ ^ 2 + ‖A 1 0‖ ^ 2 := by
    nlinarith [sq_nonneg (‖A 0 1‖ - ‖A 1 0‖), norm_nonneg (A 0 1), norm_nonneg (A 1 0)]
  have hdeq : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact h
  have hdet : ‖A 0 0 * A 1 1 - A 0 1 * A 1 0‖ = 1 := by rw [hdeq, norm_one]
  have hkey : (2 : ℝ) ≤ frob A ^ 2 := by
    rw [frob_sq]
    have hs := norm_sub_le (A 0 0 * A 1 1) (A 0 1 * A 1 0)
    rw [norm_mul, norm_mul] at hs
    nlinarith [h11, h10, hs, hdet]
  calc Real.sqrt 2 ≤ Real.sqrt (frob A ^ 2) := Real.sqrt_le_sqrt hkey
    _ = frob A := Real.sqrt_sq (frob_nonneg A)

end Work.TMC7Core.Cocycle
