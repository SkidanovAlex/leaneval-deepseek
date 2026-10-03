import Mathlib
import Submission.Work.Pert.small_of_nearOn
import Submission.Work.Interfaces.Parabolic

namespace Work.Pert

open Complex Metric Filter Set

/-- Compact-`L` form of the rotation-number bound.  `small_of_nearOn` states the estimate for a
perturbation that is `δ₀`-close to `f₀` on the *closed ball* of radius `ρ` and whose germ is
`z + z(z-σ)u z`, with the extra requirement `ρ ≤ r₀` (used only to place that ball inside `D₀`).
Here closeness is assumed on an arbitrary compact `L ⊇ closedBall 0 ρ`, so `ρ` may be much larger
than the radius produced by `small_of_nearOn`; the estimate is applied at the effective radius
`min ρ r₀`. -/
theorem rotOf_bound_of_nearOn_compact {f₀ : ℂ → ℂ} {D₀ : Set ℂ}
    (h₀ : MandelDim.IsParabolicGerm f₀ D₀) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∃ C : ℝ, 0 < C ∧
    ∀ {f : ℂ → ℂ} {Df L : Set ℂ} {u : ℂ → ℂ} {σ : ℂ} {ρ δ₀ : ℝ},
      IsCompact L → L ⊆ D₀ → 0 < ρ → Metric.closedBall (0 : ℂ) ρ ⊆ L →
      0 < δ₀ → 2 * δ₀ ≤ min ρ r₀ →
      MandelDim.NearOn f₀ f Df L δ₀ → f 0 = 0 →
      DifferentiableOn ℂ u (Metric.ball (0 : ℂ) ρ) →
      (∀ z ∈ Metric.ball (0 : ℂ) ρ, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
      (∀ z ∈ Metric.ball (0 : ℂ) ρ, f z = z + z * (z - σ) * u z) →
      ‖MandelDim.rotOf f‖ ≤ C * (δ₀ / min ρ r₀) := by
  obtain ⟨r₀, hr₀, _, C, hC, H⟩ := small_of_nearOn h₀
  refine ⟨r₀, hr₀, C, hC, ?_⟩
  intro f Df L u σ ρ δ₀ _hLc _hLD hρ hballL hδ₀ h2δ hnear hf0 hdiffu hbnd hform
  -- effective radius
  have hmin_pos : 0 < min ρ r₀ := lt_min hρ hr₀
  have hmin_le_r₀ : min ρ r₀ ≤ r₀ := min_le_right _ _
  -- the ball of the effective radius still lies in `L`
  have hsub : Metric.closedBall (0 : ℂ) (min ρ r₀) ⊆ L :=
    (Metric.closedBall_subset_closedBall (min_le_left _ _)).trans hballL
  -- hence `NearOn` transfers from `L` to that ball
  have hnear' : MandelDim.NearOn f₀ f Df (Metric.closedBall (0 : ℂ) (min ρ r₀)) δ₀ :=
    ⟨hnear.1, hsub.trans hnear.2.1, hnear.2.2.1, fun z hz => hnear.2.2.2 z (hsub hz)⟩
  have h := H (ρ := min ρ r₀) hmin_pos hmin_le_r₀ hδ₀ h2δ hρ hnear' hf0 hdiffu hbnd hform
  rw [← mul_div_assoc]
  exact h.2.2

end Work.Pert
