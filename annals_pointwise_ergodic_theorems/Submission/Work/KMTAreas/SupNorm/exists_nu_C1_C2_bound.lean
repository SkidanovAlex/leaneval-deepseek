import Mathlib

namespace Work.KMTAreas.SupNorm

/-- For a `C²` function `θ : ℝ → ℂ` and a base point `x₀`, there are nonnegative constants
`D`, `D₂` such that on every ball `closedBall x₀ δ` with `0 < δ ≤ 1`:
the oscillation of `θ` is bounded by `D * δ`, the first derivative by `D`, and the second
derivative by `D₂`. -/
theorem exists_nu_C1_C2_bound {θ : ℝ → ℂ} (hθ : ContDiff ℝ 2 θ) (x₀ : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ D₂ : ℝ, 0 ≤ D₂ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        (∀ y ∈ Metric.closedBall x₀ δ, ‖θ y - θ x₀‖ ≤ D * δ) ∧
        (∀ y ∈ Metric.closedBall x₀ δ, ‖deriv θ y‖ ≤ D) ∧
        (∀ y ∈ Metric.closedBall x₀ δ, ‖iteratedDeriv 2 θ y‖ ≤ D₂) := by
  have hd : Differentiable ℝ θ := hθ.differentiable (by norm_num)
  have hcont1 : Continuous (deriv θ) := by
    simpa [iteratedDeriv_one] using hθ.continuous_iteratedDeriv 1 (by norm_num)
  have hcont2 : Continuous (iteratedDeriv 2 θ) := hθ.continuous_iteratedDeriv' 2
  obtain ⟨D₁, hD₁⟩ :=
    (isCompact_closedBall x₀ (1:ℝ)).exists_bound_of_continuousOn hcont1.continuousOn
  obtain ⟨D₂₀, hD₂₀⟩ :=
    (isCompact_closedBall x₀ (1:ℝ)).exists_bound_of_continuousOn hcont2.continuousOn
  refine ⟨max D₁ 0, le_max_right _ _, max D₂₀ 0, le_max_right _ _, ?_⟩
  intro δ hδ0 hδ1
  have hsub : Metric.closedBall x₀ δ ⊆ Metric.closedBall x₀ (1:ℝ) :=
    Metric.closedBall_subset_closedBall hδ1
  have hDnn : (0:ℝ) ≤ max D₁ 0 := le_max_right _ _
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    have hbound : ∀ z ∈ Metric.closedBall x₀ δ, ‖deriv θ z‖ ≤ max D₁ 0 :=
      fun z hz => le_trans (hD₁ z (hsub hz)) (le_max_left _ _)
    have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := θ) (s := Metric.closedBall x₀ δ) (x := x₀) (y := y) (C := max D₁ 0)
      (fun z _ => hd.differentiableAt) hbound (convex_closedBall x₀ δ)
      (Metric.mem_closedBall_self (le_of_lt hδ0)) hy
    have hdist : ‖y - x₀‖ ≤ δ := by
      rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hy
    calc ‖θ y - θ x₀‖ ≤ max D₁ 0 * ‖y - x₀‖ := hmv
      _ ≤ max D₁ 0 * δ := mul_le_mul_of_nonneg_left hdist hDnn
  · intro y hy
    exact le_trans (hD₁ y (hsub hy)) (le_max_left _ _)
  · intro y hy
    exact le_trans (hD₂₀ y (hsub hy)) (le_max_left _ _)

end Work.KMTAreas.SupNorm
