import Mathlib.Analysis.Calculus.MeanValue

namespace Commons.Geometry.Ulam

lemma dist_image_sub_le_of_norm_fderiv_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {s : Set E} {C : ℝ}
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hC : ∀ x ∈ s, ‖fderiv ℝ f x‖ ≤ C)
    (hs : Convex ℝ s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    dist (f x) (f y) ≤ C * dist x y := by
  have hnorm := hs.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) hf hC hx hy
  simpa [dist_eq_norm, norm_sub_rev] using hnorm

end Commons.Geometry.Ulam