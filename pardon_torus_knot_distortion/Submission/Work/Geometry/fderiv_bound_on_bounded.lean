import Mathlib
import Submission.Work.Core.Torus

namespace Work.Geometry

/-- The Fréchet derivative of a `C^1` map between finite-dimensional real vector
spaces is bounded in operator norm on any bounded set: the map `z ↦ ‖fderiv ℝ f z‖`
is continuous, and a bounded set has compact closure in a proper space. -/
theorem fderiv_bound_on_bounded (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hf : ContDiff ℝ 1 f) (s : Set (EuclideanSpace ℝ (Fin 3))) (hs : Bornology.IsBounded s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ s, ‖fderiv ℝ f z‖ ≤ C := by
  -- `f` is C^1, so its derivative is continuous.
  have hcont : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hcont_norm : Continuous fun z => ‖fderiv ℝ f z‖ := hcont.norm
  -- A bounded set in a proper space has compact closure.
  have hcompact : IsCompact (closure s) := hs.isCompact_closure
  -- A continuous real-valued function on a compact set is bounded above.
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hcont_norm.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun z hz => ?_⟩
  have hCz : ‖fderiv ℝ f z‖ ≤ C := by
    simpa only [norm_norm] using hC z (subset_closure hz)
  exact le_trans hCz (le_max_left _ _)

end Work.Geometry
