import Mathlib

namespace Work.Pert

/-- A function holomorphic at a point is locally linearly bounded there:
there are constants `C, ρ > 0` with `‖f τ - f a‖ ≤ C * ‖τ - a‖` whenever `‖τ - a‖ ≤ ρ`. -/
theorem diffAt_linear_bound {f : ℂ → ℂ} {a : ℂ} (hf : DifferentiableAt ℂ f a) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ∀ τ : ℂ, ‖τ - a‖ ≤ ρ → ‖f τ - f a‖ ≤ C * ‖τ - a‖ := by
  have hlit : (fun τ : ℂ => f τ - f a - fderiv ℂ f a (τ - a)) =o[nhds a] (fun τ : ℂ => τ - a) :=
    hf.hasFDerivAt.isLittleO
  have h := hlit.def one_pos
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨ε, hεpos, hε⟩ := h
  refine ⟨1 + ‖fderiv ℂ f a‖, ε / 2, by positivity, by positivity, ?_⟩
  intro τ hτ
  have hdist : dist τ a < ε := by
    rw [dist_eq_norm]; linarith
  have hP : ‖f τ - f a - fderiv ℂ f a (τ - a)‖ ≤ 1 * ‖τ - a‖ := hε hdist
  have h2 : ‖fderiv ℂ f a (τ - a)‖ ≤ ‖fderiv ℂ f a‖ * ‖τ - a‖ :=
    ContinuousLinearMap.le_opNorm _ _
  have hsplit : f τ - f a = (f τ - f a - fderiv ℂ f a (τ - a)) + fderiv ℂ f a (τ - a) := by ring
  rw [hsplit]
  calc ‖f τ - f a - fderiv ℂ f a (τ - a) + fderiv ℂ f a (τ - a)‖
      ≤ ‖f τ - f a - fderiv ℂ f a (τ - a)‖ + ‖fderiv ℂ f a (τ - a)‖ := norm_add_le _ _
    _ ≤ 1 * ‖τ - a‖ + ‖fderiv ℂ f a‖ * ‖τ - a‖ := add_le_add hP h2
    _ = (1 + ‖fderiv ℂ f a‖) * ‖τ - a‖ := by ring

end Work.Pert
