import Mathlib

namespace Work.PertCrux

/-- An analytic function `h` with `h 0 = 1` is bounded by `3/2` on a small ball around `0`, and so is
its derivative by `‖deriv h 0‖ + 1`.  Both statements are immediate continuity consequences of
analyticity: `h` itself is continuous at `0`, and so is `deriv h`, since the derivative of an
analytic function is again analytic (`AnalyticAt.iterated_deriv`). -/
lemma exists_ball_bounds_analytic {h : ℂ → ℂ} (han : AnalyticAt ℂ h 0) (h0 : h 0 = 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ (∀ z ∈ Metric.ball (0 : ℂ) ρ, ‖h z‖ ≤ 3 / 2) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) ρ, ‖deriv h z‖ ≤ ‖deriv h 0‖ + 1) := by
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.continuousAt_iff.mp han.continuousAt (1 / 2) (by norm_num)
  have hdcont : ContinuousAt (deriv h) 0 := by
    simpa [iteratedDeriv_one] using (han.iterated_deriv 1).continuousAt
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.continuousAt_iff.mp hdcont 1 (by norm_num)
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, ?_, ?_⟩
  · intro z hz
    have hz1 : dist z (0 : ℂ) < δ₁ :=
      lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_left _ _)
    have h1 := hδ₁ hz1
    rw [h0, dist_eq_norm] at h1
    have h2 : ‖h z‖ ≤ ‖h z - 1‖ + 1 := by
      simpa using norm_add_le (h z - 1) (1 : ℂ)
    linarith
  · intro z hz
    have hz2 : dist z (0 : ℂ) < δ₂ :=
      lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_right _ _)
    have h1 := hδ₂ hz2
    rw [dist_eq_norm] at h1
    have h2 : ‖deriv h z‖ ≤ ‖deriv h z - deriv h 0‖ + ‖deriv h 0‖ := by
      simpa using norm_add_le (deriv h z - deriv h 0) (deriv h 0)
    linarith

end Work.PertCrux
