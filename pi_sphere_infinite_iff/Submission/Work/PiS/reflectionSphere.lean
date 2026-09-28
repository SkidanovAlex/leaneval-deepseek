import Mathlib
import Submission.Work.PiS.Interfaces

set_option synthInstance.maxHeartbeats 400000

namespace Work.PiS

/-- Reflection of `x` in the hyperplane orthogonal to `x - y` is `y`, for points `x, y` of the
unit sphere (both have norm one, so `Submodule.reflection_sub` applies). -/
theorem reflectionSphere (n : ℕ) (x y : Sph n) :
    (((ℝ ∙ ((x : EuclideanSpace ℝ (Fin (n + 1))) - (y : EuclideanSpace ℝ (Fin (n + 1)))))ᗮ).reflection
      (x : EuclideanSpace ℝ (Fin (n + 1)))) = (y : EuclideanSpace ℝ (Fin (n + 1))) := by
  exact Submodule.reflection_sub (by simp)

end Work.PiS
