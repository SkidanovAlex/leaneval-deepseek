import Mathlib
import Submission.Work.Endgame.Defs
import Submission.Work.Endgame.Basic

namespace Work.Endgame

/-- A space homeomorphic to the one-point compactification of `ℝⁿ` is homeomorphic to the unit
sphere `𝕊ⁿ ⊂ ℝⁿ⁺¹`: compose the given homeomorphism with the stereographic
homeomorphism `OnePoint ℝⁿ ≃ₜ 𝕊ⁿ`. -/
theorem nonempty_homeomorph_sphere_of_homeomorph_onePoint {n : ℕ} {M : Type*}
    [TopologicalSpace M] (h : M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin n))) :
    Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  ⟨homeomorphSphereOfHomeomorphOnePoint h⟩

end Work.Endgame
