import Mathlib

namespace Work.Embedding

/-- The operator norm of `Dψ` is bounded on a compact set on which `ψ` is `C¹`. -/
theorem uniform_bound_fderiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ψ : E → F} {s : Set E} (hs : IsCompact s)
    (hψ : ∀ u ∈ s, ContDiffAt ℝ 1 ψ u) :
    ∃ L, 0 < L ∧ ∀ u ∈ s, ‖fderiv ℝ ψ u‖ ≤ L := by
  -- `C¹` at each point of `s` makes `fderiv ℝ ψ` continuous at each point of `s`,
  -- hence continuous on `s`; the image of the compact `s` is compact, hence bounded,
  -- and the operator norm is bounded on it.
  have hcont : ContinuousOn (fderiv ℝ ψ) s := fun u hu =>
    ((hψ u hu).continuousAt_fderiv (by norm_num)).continuousWithinAt
  have hcomp : IsCompact (fderiv ℝ ψ '' s) := hs.image_of_continuousOn hcont
  obtain ⟨r, hr⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : E →L[ℝ] F)).1 hcomp.isBounded
  refine ⟨max r 1, by positivity, ?_⟩
  intro u hu
  have hmem : fderiv ℝ ψ u ∈ Metric.closedBall (0 : E →L[ℝ] F) r := hr ⟨u, hu, rfl⟩
  have hle : dist (fderiv ℝ ψ u) 0 ≤ r := Metric.mem_closedBall.1 hmem
  rw [dist_zero_right] at hle
  exact le_trans hle (le_max_left _ _)

end Work.Embedding
