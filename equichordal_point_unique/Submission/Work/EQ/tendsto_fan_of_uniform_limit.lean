import Mathlib
import Submission.Work.EQ.DefsCore

namespace Work.EQ

/-- The uniform limit of the fans `fan a h (ε k)` on the ball of radius `δ` transports the
convergence of the stable parameters `ψ₁` to the value of the fans: if `(x k).2.1 → W` and
`fan a h (ε k) ⇒ fan a h ε₀ (μ * ·)` uniformly on `ball 0 δ`, with `‖μ‖ < 1` so that the map
`u ↦ μ * u` preserves the ball, then `fan a h (ε k) ((x k).2.1) → fan a h ε₀ (μ * W)`. -/
theorem tendsto_fan_of_uniform_limit {a : ℝ} {h : ℂ → ℂ} {δ : ℝ} {ε : ℕ → List Bool}
    {ε₀ : List Bool} {μ : ℂ} {x : ℕ → Work.EQ.ChainData} {W : ℂ}
    (hunif : TendstoUniformlyOn (fun k => Work.EQ.fan a h (ε k))
      (fun u => Work.EQ.fan a h ε₀ (μ * u)) Filter.atTop (Metric.ball (0 : ℂ) δ))
    (hz : Filter.Tendsto (fun k => (x k).2.1) Filter.atTop (nhds W))
    (hzs : ∀ k, ‖(x k).2.1‖ < δ) (hW : ‖W‖ < δ) (hμ : ‖μ‖ < 1)
    (hcont : ContinuousOn (Work.EQ.fan a h ε₀) (Metric.ball (0 : ℂ) δ)) :
    Filter.Tendsto (fun k => Work.EQ.fan a h (ε k) ((x k).2.1)) Filter.atTop
      (nhds (Work.EQ.fan a h ε₀ (μ * W))) := by
  -- `u ↦ μ * u` maps the ball of radius `δ` into itself because `‖μ‖ < 1`.
  have hμs : Set.MapsTo (fun u : ℂ => μ * u) (Metric.ball (0 : ℂ) δ)
      (Metric.ball (0 : ℂ) δ) := by
    intro u hu
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hu ⊢
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg u) hμ.le) hu
  have hWs : W ∈ Metric.ball (0 : ℂ) δ := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hW
  have hμWs : μ * W ∈ Metric.ball (0 : ℂ) δ := hμs hWs
  -- The limit function `u ↦ fan a h ε₀ (μ * u)` is continuous at `W` within the ball.
  have hf : ContinuousWithinAt (fun u : ℂ => Work.EQ.fan a h ε₀ (μ * u))
      (Metric.ball (0 : ℂ) δ) W :=
    (hcont.continuousWithinAt hμWs).comp
      ((continuous_const.mul continuous_id).continuousAt.continuousWithinAt) hμs
  -- The stable parameters converge to `W` within the ball.
  have hg : Filter.Tendsto (fun k => (x k).2.1) Filter.atTop
      (nhdsWithin W (Metric.ball (0 : ℂ) δ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      hz (Filter.Eventually.of_forall fun k => by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hzs k)
  exact hunif.tendsto_comp hf hg

end Work.EQ
