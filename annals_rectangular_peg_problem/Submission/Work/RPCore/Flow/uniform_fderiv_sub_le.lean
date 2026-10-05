import Mathlib

namespace Work.RPCore.Flow

theorem uniform_fderiv_sub_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (X : E → F) (hX : ContDiff ℝ 1 X) {s : Set E}
    (hs : IsCompact s) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ b ∈ s, ∀ a : E, ‖a - b‖ ≤ η →
      ‖X a - X b - fderiv ℝ X b (a - b)‖ ≤ ε * ‖a - b‖ := by
  -- `X` is `C^1`, so its Fréchet derivative `x ↦ fderiv ℝ X x` is continuous.
  have hcont : Continuous (fderiv ℝ X) := hX.continuous_fderiv one_ne_zero
  -- Uniform continuity of the derivative *at the compact set `s`*: points of `s` see a
  -- neighbourhood on which the derivative varies by less than `ε`.  This is exactly
  -- `IsCompact.uniformContinuousAt_of_continuousAt`; note that it does not require the
  -- ambient space to be proper (unlike compactness of a thickening of `s`).
  have hr : {p : (E →L[ℝ] F) × (E →L[ℝ] F) | dist p.1 p.2 < ε} ∈ uniformity (E →L[ℝ] F) :=
    Metric.dist_mem_uniformity hε
  have hunif : {x : E × E | x.1 ∈ s → (fderiv ℝ X x.1, fderiv ℝ X x.2) ∈
      {p : (E →L[ℝ] F) × (E →L[ℝ] F) | dist p.1 p.2 < ε}} ∈ uniformity E :=
    hs.uniformContinuousAt_of_continuousAt (fderiv ℝ X) (fun a _ => hcont.continuousAt) hr
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_uniformity_dist.1 hunif
  refine ⟨δ / 2, by linarith, ?_⟩
  intro b hb a hab
  -- Any point of the segment `[b, a]` is within `δ / 2 < δ` of `b`, since `a` is.
  have ha_ball : a ∈ Metric.closedBall b (δ / 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact hab
  have hseg : segment ℝ b a ⊆ Metric.closedBall b (δ / 2) :=
    (convex_closedBall b (δ / 2)).segment_subset (Metric.mem_closedBall_self (by linarith)) ha_ball
  -- Hence the derivative is `ε`-close to `fderiv ℝ X b` along the whole segment.
  have hbound : ∀ x ∈ segment ℝ b a, ‖fderiv ℝ X x - fderiv ℝ X b‖ ≤ ε := by
    intro x hx
    have hxball := hseg hx
    rw [Metric.mem_closedBall] at hxball
    have hd : dist b x < δ := by rw [dist_comm]; linarith
    have key : ‖fderiv ℝ X x - fderiv ℝ X b‖ < ε := by
      have h0 : dist (fderiv ℝ X b) (fderiv ℝ X x) < ε := hδ hd hb
      rw [dist_eq_norm, norm_sub_rev] at h0
      exact h0
    exact le_of_lt key
  have hdiff : ∀ x ∈ segment ℝ b a, DifferentiableAt ℝ X x :=
    fun x _ => hX.differentiable_one.differentiableAt
  -- Mean value inequality on the convex segment, with the fixed linear map `fderiv ℝ X b`.
  exact Convex.norm_image_sub_le_of_norm_fderiv_le' hdiff hbound (convex_segment b a)
    (left_mem_segment ℝ b a) (right_mem_segment ℝ b a)

end Work.RPCore.Flow
