import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Commons.Analysis.GaussianMeasure

open scoped Real BigOperators
open Matrix

set_option linter.unusedVariables false

/-- If `Aᵀ * A = Vᵀ * diagonal d * V` (in particular, if `Aᵀ * A` is diagonalized by `V`),
then the squared norm of `A x` is the `d`-weighted sum of squares of the coordinates of `V x`. -/
theorem norm_sq_eq_sum_diagonal_spectral {n : ℕ} (A V : Matrix (Fin n) (Fin n) ℝ)
    (d : Fin n → ℝ) (hV : V.transpose * V = 1)
    (hM : A.transpose * A = V.transpose * Matrix.diagonal d * V)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖(Matrix.toLpLin 2 2 A) x‖ ^ 2
      = ∑ i, d i * (V.mulVec (WithLp.ofLp x)) i ^ 2 := by
  classical
  have hL : ‖(Matrix.toLpLin 2 2 A) x‖ ^ 2
      = ∑ i, (A.mulVec (WithLp.ofLp x)) i ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Matrix.toLpLin_apply]
  rw [hL]
  have hmain : ∑ i, (A.mulVec (WithLp.ofLp x)) i ^ 2
      = ∑ i, d i * (V.mulVec (WithLp.ofLp x)) i ^ 2 := by
    have h2 : ∑ i, (A.mulVec (WithLp.ofLp x)) i ^ 2
        = (WithLp.ofLp x) ⬝ᵥ ((A.transpose * A).mulVec (WithLp.ofLp x)) := by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec (A := A), dotProduct]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h2, hM]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [Matrix.dotProduct_transpose_mulVec (A := V)]
    rw [dotProduct]
    simp only [Matrix.mulVec_diagonal]
    apply Finset.sum_congr rfl
    intro i _
    ring
  exact hmain

end Commons.Analysis.GaussianMeasure