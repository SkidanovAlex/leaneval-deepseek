import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.locally_bij_of_close

namespace Work.Repel

/-- **Target control for the perturbed Fatou coordinate.**

`PertData.K'_sub` gives `closedBall c (2r) ⊆ P.Dφ`, and `PertData.φ_close` (applied on the compact
`K' = closedBall c (2r)`) gives `‖P.φ w - d.φ w‖ < δ` there; the latter forces `δ > 0` as soon as
`r > 0`.  Hence `P.φ` and `d.φ` are both holomorphic on `closedBall c r`, close there, and
`d.φ` is univalent with non-vanishing derivative at `c`, so
`Work.Repel.locally_bij_of_close` applies.  We only have to shrink the resulting radius so that the
whole ball stays inside `P.Dφ` (which holds since `ball c r ⊆ closedBall c (2r) ⊆ P.Dφ`). -/
theorem target_control {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) {f : ℂ → ℂ}
    {Df : Set ℂ} {η y₁ : ℝ} {K K' : Set ℂ} {δ : ℝ}
    (P : MandelDim.PertData d f Df η y₁ K K' δ)
    {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hderiv : deriv d.φ c ≠ 0)
    (hK' : K' = Metric.closedBall c (2 * r))
    (hsub : Metric.closedBall c r ⊆ d.Dφ)
    (hginj : Set.InjOn d.φ (Metric.ball c r))
    (hsmall : 128 * δ < r * ‖deriv d.φ c‖) :
    ∃ ρ σ : ℝ, 0 < ρ ∧ 0 < σ ∧ ρ ≤ r ∧ Set.InjOn P.φ (Metric.ball c ρ) ∧
      Metric.ball (d.φ c) σ ⊆ P.φ '' Metric.ball c ρ ∧ Metric.ball c ρ ⊆ P.Dφ := by
  -- `δ > 0`, forced by the closeness on the non-empty compact `K' ∋ c`.
  have hδpos : 0 < δ := by
    have hc : c ∈ K' := by
      rw [hK']; exact Metric.mem_closedBall_self (by linarith)
    have h := P.φ_close c hc
    have hnn : (0 : ℝ) ≤ ‖P.φ c - d.φ c‖ := norm_nonneg _
    linarith
  -- `closedBall c (2r) = K' ⊆ P.Dφ`
  have hK'2 : Metric.closedBall c (2 * r) ⊆ P.Dφ := by
    rw [← hK']; exact P.K'_sub
  have hballDφ : Metric.closedBall c r ⊆ P.Dφ :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hK'2
  -- differentiability of both maps on `closedBall c r`
  have hf : DifferentiableOn ℂ P.φ (Metric.closedBall c r) := P.φ_holo.mono hballDφ
  have hg : DifferentiableOn ℂ d.φ (Metric.closedBall c r) := d.φ_holo.mono hsub
  -- closeness on `closedBall c r`
  have hclose : ∀ z ∈ Metric.closedBall c r, ‖P.φ z - d.φ z‖ ≤ δ := by
    intro z hz
    have hzK : z ∈ K' := by
      rw [hK']
      exact Metric.closedBall_subset_closedBall (by linarith) hz
    exact le_of_lt (P.φ_close z hzK)
  obtain ⟨ρ, σ, hρ, hσ, hρr, hinj, hcov⟩ :=
    locally_bij_of_close (f := P.φ) (g := d.φ) (c := c) (r := r) (δ := δ)
      hr hδpos hf hg hderiv hginj hclose hsmall
  exact ⟨ρ, σ, hρ, hσ, hρr, hinj, hcov,
    (Metric.ball_subset_ball hρr).trans (Metric.ball_subset_closedBall.trans hballDφ)⟩

end Work.Repel
