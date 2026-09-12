import Mathlib
import Submission.Commons.Analysis.Complex.rouche_simple_zero

namespace Commons.Analysis.Complex

/-- Rouché's theorem, "single simple zero" form, for functions that are merely
`AnalyticOnNhd` on the *open* ball and continuous on the closed ball (no
differentiability hypothesis is available on the boundary circle).

Since `f` and `g` are analytic on the ball of radius `R`, on any strictly
smaller closed ball `closedBall 0 ρ` they are genuinely differentiable, so the
ready-made `rouche_simple_zero` (which assumes `DifferentiableOn` on the closed
ball) applies at the radius `ρ` supplied by
`exists_annulus_lt_of_lt_on_sphere`.  The uniqueness of the zero is then
extended from `ball 0 ρ` to `ball 0 R` using the annulus inequality. -/
theorem rouche_simple_zero_of_analyticOnNhd {R : ℝ} (hR : 0 < R) {f g : ℂ → ℂ} {a : ℂ} (ha : ‖a‖ < R)
    (hf : AnalyticOnNhd ℂ f (Metric.ball (0:ℂ) R))
    (hfc : ContinuousOn f (Metric.closedBall (0:ℂ) R))
    (hg : AnalyticOnNhd ℂ g (Metric.ball (0:ℂ) R))
    (hgc : ContinuousOn g (Metric.closedBall (0:ℂ) R))
    (h : ∀ z ∈ Metric.sphere (0:ℂ) R, ‖g z‖ < ‖f z‖)
    (hf1 : f a = 0) (hder : deriv f a ≠ 0)
    (hfonly : ∀ z ∈ Metric.ball (0:ℂ) R, f z = 0 → z = a) :
    ∃ z ∈ Metric.ball (0:ℂ) R, (f z + g z = 0) ∧
      (∀ y ∈ Metric.ball (0:ℂ) R, f y + g y = 0 → y = z) := by
  obtain ⟨ρ, hρpos, hρR, hann⟩ := exists_annulus_lt_of_lt_on_sphere hR hfc hgc h
  -- on the strictly smaller closed ball both functions are differentiable
  have hf_diff : DifferentiableOn ℂ f (Metric.closedBall (0:ℂ) ρ) := fun z hz =>
    ((hf z (Metric.closedBall_subset_ball hρR hz)).differentiableAt).differentiableWithinAt
  have hg_diff : DifferentiableOn ℂ g (Metric.closedBall (0:ℂ) ρ) := fun z hz =>
    ((hg z (Metric.closedBall_subset_ball hρR hz)).differentiableAt).differentiableWithinAt
  have hfc' : ContinuousOn f (Metric.closedBall (0:ℂ) ρ) :=
    hfc.mono (Metric.closedBall_subset_closedBall hρR.le)
  have hgc' : ContinuousOn g (Metric.closedBall (0:ℂ) ρ) :=
    hgc.mono (Metric.closedBall_subset_closedBall hρR.le)
  -- the zero `a` still lies in the smaller ball
  have ha_ball : ‖a‖ < ρ := by
    by_contra hlt
    rw [not_lt] at hlt
    have h1 := hann a hlt ha.le
    rw [hf1, norm_zero] at h1
    linarith [norm_nonneg (g a)]
  -- the strict inequality on the smaller sphere
  have hlt_sphere : ∀ z ∈ Metric.sphere (0:ℂ) ρ, ‖g z‖ < ‖f z‖ := by
    intro z hz
    have hz' : ‖z‖ = ρ := by simpa [dist_eq_norm] using Metric.mem_sphere.mp hz
    exact hann z hz'.ge (hz'.le.trans hρR.le)
  obtain ⟨z, hz_ball, hz0, hzuniq⟩ :=
    rouche_simple_zero hρpos ha_ball hf_diff hfc' hg_diff hgc' hlt_sphere hf1 hder
      (fun z hz hz0 => hfonly z (Metric.ball_subset_ball hρR.le hz) hz0)
  refine ⟨z, Metric.ball_subset_ball hρR.le hz_ball, hz0, ?_⟩
  intro y hy hy0
  apply hzuniq y ?_ hy0
  by_contra hyr
  rw [Metric.mem_ball, dist_zero_right] at hyr
  rw [not_lt] at hyr
  have hylt : ‖y‖ < R := by
    rw [Metric.mem_ball, dist_zero_right] at hy
    exact hy
  have h1 := hann y hyr hylt.le
  have hfe : f y = -g y := by linear_combination hy0
  rw [hfe] at h1
  simp at h1

end Commons.Analysis.Complex
