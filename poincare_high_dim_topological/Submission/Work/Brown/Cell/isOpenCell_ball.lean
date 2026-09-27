import Mathlib
import Submission.Work.Brown.Basic

namespace Work.Brown.Cell

/-- An open ball of positive radius in `ℝⁿ` is homeomorphic to `ℝⁿ`, hence an open `n`-cell.
The homeomorphism is the affine rescaling `univBall`: it is the `r`-fold dilation composed
with the translation by the centre, inverted to go from the ball to the whole space. -/
theorem isOpenCell_ball {n : ℕ} {r : ℝ} (hr : 0 < r) : Work.Brown.IsOpenCell n (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) := by
  refine ⟨Metric.isOpen_ball, ?_⟩
  refine ⟨?_⟩
  have h := (OpenPartialHomeomorph.univBall (0 : EuclideanSpace ℝ (Fin n)) r).toHomeomorphSourceTarget
  rw [OpenPartialHomeomorph.univBall_source, OpenPartialHomeomorph.univBall_target _ hr] at h
  exact h.symm.trans (Homeomorph.Set.univ _)

end Work.Brown.Cell
