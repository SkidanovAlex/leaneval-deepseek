import Mathlib

set_option linter.unusedVariables false

namespace Work.Pert

/-- A function holomorphic on a ball is locally Lipschitz at every interior point.

This is the `ε`-form of the little-`o` characterisation of the derivative at `σ`:
the first-order Taylor remainder `u τ - u σ - fderiv ℂ u σ (τ - σ)` is `o(‖τ - σ‖)`,
so near `σ` it is bounded by `‖τ - σ‖`, giving Lipschitzness with the constant
`1 + ‖fderiv ℂ u σ‖`.  (The hypotheses `hrr` and `hub` only serve to place `σ`
inside the domain of holomorphy; no bound on `u` itself is needed.) -/
theorem exists_lipschitz_near_of_diffOn {u : ℂ → ℂ} {rr : ℝ} {σ : ℂ}
    (hrr : 0 < rr) (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hub : ∀ z ∈ Metric.ball (0 : ℂ) rr, ‖u z‖ ≤ 2) (hσr : ‖σ‖ < rr) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ ζ : ℂ, ‖ζ - σ‖ ≤ δ → ‖u ζ - u σ‖ ≤ C * ‖ζ - σ‖ := by
  -- `σ` is an interior point of the ball, where `u` is complex-differentiable
  have hσ : σ ∈ Metric.ball (0 : ℂ) rr := by
    rw [Metric.mem_ball, dist_eq_norm]
    simpa using hσr
  have hd : DifferentiableAt ℂ u σ :=
    (hu σ hσ).differentiableAt (Metric.isOpen_ball.mem_nhds hσ)
  -- first-order Taylor expansion at `σ`
  have hlit : (fun τ : ℂ => u τ - u σ - fderiv ℂ u σ (τ - σ)) =o[nhds σ]
      (fun τ : ℂ => τ - σ) :=
    hd.hasFDerivAt.isLittleO
  have h := hlit.def one_pos
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨ε, hεpos, hε⟩ := h
  refine ⟨1 + ‖fderiv ℂ u σ‖, ε / 2, by positivity, by positivity, ?_⟩
  intro ζ hζ
  have hdist : dist ζ σ < ε := by
    rw [dist_eq_norm]
    linarith
  have hP : ‖u ζ - u σ - fderiv ℂ u σ (ζ - σ)‖ ≤ 1 * ‖ζ - σ‖ := hε hdist
  have h2 : ‖fderiv ℂ u σ (ζ - σ)‖ ≤ ‖fderiv ℂ u σ‖ * ‖ζ - σ‖ :=
    ContinuousLinearMap.le_opNorm _ _
  have hsplit : u ζ - u σ
      = (u ζ - u σ - fderiv ℂ u σ (ζ - σ)) + fderiv ℂ u σ (ζ - σ) := by ring
  rw [hsplit]
  calc ‖u ζ - u σ - fderiv ℂ u σ (ζ - σ) + fderiv ℂ u σ (ζ - σ)‖
      ≤ ‖u ζ - u σ - fderiv ℂ u σ (ζ - σ)‖ + ‖fderiv ℂ u σ (ζ - σ)‖ := norm_add_le _ _
    _ ≤ 1 * ‖ζ - σ‖ + ‖fderiv ℂ u σ‖ * ‖ζ - σ‖ := add_le_add hP h2
    _ = (1 + ‖fderiv ℂ u σ‖) * ‖ζ - σ‖ := by ring

end Work.Pert
