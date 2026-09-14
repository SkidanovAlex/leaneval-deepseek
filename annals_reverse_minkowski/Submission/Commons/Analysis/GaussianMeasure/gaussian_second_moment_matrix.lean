import Mathlib
import Submission.Commons.Analysis.GaussianMeasure.second_moment_diagonal
import Submission.Commons.Analysis.GaussianMeasure.second_moment_offdiagonal

namespace Commons.Analysis.GaussianMeasure

/-- The full second-moment matrix of the standard Gaussian measure on
`EuclideanSpace ℝ (Fin n)` with density `x ↦ exp (-π‖x‖²)`: the `(i,j)` entry
`∫ x, xᵢ xⱼ exp (-π‖x‖²)` equals `1/(2π)` on the diagonal and `0` off it. -/
theorem gaussian_second_moment_matrix {n : ℕ} (i j : Fin n) :
    ∫ x : EuclideanSpace ℝ (Fin n), (x i * x j) * Real.exp (-Real.pi * ‖x‖ ^ 2)
      = if i = j then 1 / (2 * Real.pi) else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    exact second_moment_diagonal i
  · rw [if_neg hij]
    exact second_moment_offdiagonal hij

end Commons.Analysis.GaussianMeasure
