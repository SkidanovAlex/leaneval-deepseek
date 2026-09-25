import Mathlib

namespace Work.NN.Newton

/-- If `f` is differentiable on a convex set `s` with `‖fderiv f x - id‖ ≤ 1/2` everywhere on `s`,
then `f` moves points of `s` by at most half their distance, is `2`-expanding (up to a factor `2`
in the sense `‖x - y‖ ≤ 2 ‖f x - f y‖`), and is injective on `s`. -/
theorem expansionNearId {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {s : Set E} (hconv : Convex ℝ s)
    (hdiff : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hb : ∀ x ∈ s, ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ E‖ ≤ (1 / 2 : ℝ)) :
    (∀ x ∈ s, ∀ y ∈ s, ‖f x - f y - (x - y)‖ ≤ (1 / 2) * ‖x - y‖) ∧
    (∀ x ∈ s, ∀ y ∈ s, ‖x - y‖ ≤ 2 * ‖f x - f y‖) ∧ Set.InjOn f s := by
  -- Mean value inequality on the convex set `s`, with the fixed linear map `id` as reference point.
  have key : ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y - (x - y)‖ ≤ (1 / 2) * ‖x - y‖ := by
    intro x hx y hy
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le' (𝕜 := ℝ) hdiff hb hconv hy hx
    simpa using h
  refine ⟨key, ?_, ?_⟩
  · intro x hx y hy
    have h := key x hx y hy
    have h1 : ‖x - y‖ ≤ ‖f x - f y‖ + ‖f x - f y - (x - y)‖ :=
      calc ‖x - y‖ = ‖(f x - f y) - (f x - f y - (x - y))‖ := by congr 1; abel
        _ ≤ ‖f x - f y‖ + ‖f x - f y - (x - y)‖ := norm_sub_le _ _
    linarith [h, h1]
  · intro x hx y hy hxy
    have h := key x hx y hy
    rw [hxy, sub_self] at h
    simp only [zero_sub, norm_neg] at h
    have hz : ‖x - y‖ = 0 := le_antisymm (by linarith [h, norm_nonneg (x - y)]) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end Work.NN.Newton
