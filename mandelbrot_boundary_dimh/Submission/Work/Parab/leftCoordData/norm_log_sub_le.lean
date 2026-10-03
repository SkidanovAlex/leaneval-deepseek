import Mathlib

namespace Work.Parab.leftCoordData

/-- Quantitative Lipschitz estimate for the principal branch of the logarithm along a straight
segment.

If the whole segment joining `u` and `v` lies in the slit plane (`Complex.slitPlane`) and every
point of that segment has norm at least `h > 0`, then

`‖log u - log v‖ ≤ ‖u - v‖ / h`.

Indeed `Complex.log` is holomorphic on the open set `slitPlane` with derivative `z ↦ z⁻¹`, whose
norm is `‖z‖⁻¹ ≤ h⁻¹` on the segment; the mean value theorem on the (real-)convex segment then
gives the claim.  This is the elementary estimate used to compare Fatou coordinates. -/
theorem norm_log_sub_le {u v : ℂ} {h : ℝ} (hh : 0 < h)
    (hslit : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → (1 - t) * u + t * v ∈ Complex.slitPlane)
    (hsep : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → h ≤ ‖(1 - t) * u + t * v‖) :
    ‖Complex.log u - Complex.log v‖ ≤ ‖u - v‖ / h := by
  -- Reconcile the `ℝ`-scalar action on `ℂ` with complex multiplication.
  have hsmul : ∀ θ : ℝ, (1 - θ) • u + θ • v = (1 - θ) * u + θ * v := by
    intro θ
    rw [Complex.real_smul, Complex.real_smul]; push_cast; ring
  -- Every point of the segment lies in the slit plane.
  have hmem : ∀ x ∈ segment ℝ u v, x ∈ Complex.slitPlane := by
    intro x hx
    rw [segment_eq_image ℝ u v] at hx
    obtain ⟨θ, hθ, hxθ⟩ := hx
    simp only [] at hxθ
    rw [← hxθ, hsmul θ]
    exact hslit θ hθ
  -- Every point of the segment has norm at least `h`.
  have hsep' : ∀ x ∈ segment ℝ u v, h ≤ ‖x‖ := by
    intro x hx
    rw [segment_eq_image ℝ u v] at hx
    obtain ⟨θ, hθ, hxθ⟩ := hx
    simp only [] at hxθ
    rw [← hxθ, hsmul θ]
    exact hsep θ hθ
  -- `Complex.log` is complex differentiable on the segment ...
  have hdiff : ∀ x ∈ segment ℝ u v, DifferentiableAt ℂ Complex.log x :=
    fun x hx => (Complex.hasDerivAt_log (hmem x hx)).differentiableAt
  -- ... with derivative bounded by `1 / h`.
  have hbound : ∀ x ∈ segment ℝ u v, ‖deriv Complex.log x‖ ≤ 1 / h := by
    intro x hx
    have hxpos : 0 < ‖x‖ := lt_of_lt_of_le hh (hsep' x hx)
    rw [Complex.deriv_log (hmem x hx), norm_inv, one_div]
    exact (inv_le_inv₀ hxpos hh).mpr (hsep' x hx)
  -- Mean value theorem on the convex segment.
  have hmain := (convex_segment u v).norm_image_sub_le_of_norm_deriv_le hdiff hbound
    (left_mem_segment ℝ u v) (right_mem_segment ℝ u v)
  calc ‖Complex.log u - Complex.log v‖
      = ‖Complex.log v - Complex.log u‖ := norm_sub_rev _ _
    _ ≤ (1 / h) * ‖v - u‖ := hmain
    _ = ‖u - v‖ / h := by rw [one_div, div_eq_inv_mul, norm_sub_rev u v]

end Work.Parab.leftCoordData
