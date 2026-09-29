import Mathlib
import Submission.Work.TMContract.Defs

/-!
# Frobenius norm of a determinant-one `2 × 2` complex matrix

For `A ∈ SL(2,ℂ)` the Frobenius norm is at least `√2`, with equality exactly for the
orthogonal matrices.  Writing `a, b, c, d` for the entries:

* AM–GM: `2‖a‖‖d‖ ≤ ‖a‖² + ‖d‖²` and `2‖b‖‖c‖ ≤ ‖b‖² + ‖c‖²`;
* triangle inequality: `1 = ‖det A‖ = ‖ad - bc‖ ≤ ‖a‖‖d‖ + ‖b‖‖c‖`.

Adding gives `2 ≤ frob A ^ 2`, and `frob` is a square root.
-/

namespace Work.TMComp.Kotani

theorem frob_sqrt_two_le_of_det_one {A : Matrix (Fin 2) (Fin 2) ℂ} (h : A.det = 1) :
    Real.sqrt 2 ≤ Work.TMContract.frob A := by
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    rw [Matrix.det_fin_two] at h
    exact h
  have h1 : ‖A 0 0 * A 1 1 - A 0 1 * A 1 0‖ = (1 : ℝ) := by rw [hdet, norm_one]
  have htri : (1 : ℝ) ≤ ‖A 0 0‖ * ‖A 1 1‖ + ‖A 0 1‖ * ‖A 1 0‖ := by
    calc (1 : ℝ) = ‖A 0 0 * A 1 1 - A 0 1 * A 1 0‖ := by rw [h1]
      _ ≤ ‖A 0 0 * A 1 1‖ + ‖A 0 1 * A 1 0‖ := norm_sub_le _ _
      _ = ‖A 0 0‖ * ‖A 1 1‖ + ‖A 0 1‖ * ‖A 1 0‖ := by rw [norm_mul, norm_mul]
  have h2 : 2 * (‖A 0 0‖ * ‖A 1 1‖) ≤ ‖A 0 0‖ ^ 2 + ‖A 1 1‖ ^ 2 := by
    nlinarith [sq_nonneg (‖A 0 0‖ - ‖A 1 1‖)]
  have h3 : 2 * (‖A 0 1‖ * ‖A 1 0‖) ≤ ‖A 0 1‖ ^ 2 + ‖A 1 0‖ ^ 2 := by
    nlinarith [sq_nonneg (‖A 0 1‖ - ‖A 1 0‖)]
  have hsum : (2 : ℝ) ≤ ‖A 0 0‖ ^ 2 + ‖A 0 1‖ ^ 2 + ‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2 := by
    nlinarith [h2, h3]
  rw [Work.TMContract.frob]
  exact Real.sqrt_le_sqrt hsum

end Work.TMComp.Kotani
