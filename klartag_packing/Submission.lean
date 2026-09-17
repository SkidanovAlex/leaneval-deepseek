import Mathlib
import Lake.Toml
import Lake.Util.Message
import Lean
import Submission.Helpers

namespace Submission

/-- Klartag's theorem: there is a constant `c > 0` such that in every dimension `n+1` there
is an ellipsoid (the image of the unit ball under a linear map) of volume exactly `c n^2`
containing no nonzero integer point. -/
theorem klartag_packing : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
    let V := EuclideanSpace ℝ (Fin (n + 1))
    ∃ φ : V →ₗ[ℝ] V, let E := φ '' Metric.ball (0 : V) 1
      (MeasureTheory.volume E : EReal) = c * n ^ 2 ∧
      {v ∈ E | ∀ i, v i ∈ Set.range ((↑) : ℤ → ℝ)} = {0} :=
  Submission.Helpers.klartag_of_density

end Submission
