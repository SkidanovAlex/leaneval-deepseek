import Mathlib

namespace Work.Smooth.Morse.Regular

/-- Local regularity form of `C^1` at a point: a function `φ : ℝ → ℝ` which is `C^1` at `a`
is differentiable, with its derivative `deriv φ`, on an interval around `a`, and both `φ`
and `deriv φ` are continuous there. -/
theorem contDiffAt_one_deriv_nhds {φ : ℝ → ℝ} {a : ℝ} (h : ContDiffAt ℝ 1 φ a) :
    ∃ ρ : ℝ, 0 < ρ ∧ ContinuousOn (deriv φ) (Set.Ioo (a - ρ) (a + ρ)) ∧
      (∀ x ∈ Set.Ioo (a - ρ) (a + ρ), HasDerivAt φ (deriv φ x) x) ∧
      ContinuousOn φ (Set.Ioo (a - ρ) (a + ρ)) := by
  -- A neighbourhood of `a` on which `φ` is `C^1`.
  obtain ⟨u, hu, hu_cd⟩ := h.contDiffOn (m := 1) (n := 1) le_rfl (fun hh => by simp at hh)
  rcases Metric.mem_nhds_iff.mp hu with ⟨ε, hεpos, hε⟩
  refine ⟨ε, hεpos, ?_, ?_, ?_⟩
  · -- continuity of the derivative on the ball, transported to the interval
    have hcv : ContDiffOn ℝ 1 φ (Metric.ball a ε) := hu_cd.mono hε
    have hcont := hcv.continuousOn_deriv_of_isOpen Metric.isOpen_ball le_rfl
    rwa [Real.ball_eq_Ioo] at hcont
  · intro x hx
    have hx_ball : x ∈ Metric.ball a ε := by
      rw [Real.ball_eq_Ioo]; exact hx
    have hcv : ContDiffOn ℝ 1 φ (Metric.ball a ε) := hu_cd.mono hε
    have hdiff : DifferentiableAt ℝ φ x :=
      (hcv.differentiableOn one_ne_zero).differentiableAt (Metric.isOpen_ball.mem_nhds hx_ball)
    exact hdiff.hasDerivAt
  · have hcv : ContDiffOn ℝ 1 φ (Metric.ball a ε) := hu_cd.mono hε
    have hcont := hcv.continuousOn
    rwa [Real.ball_eq_Ioo] at hcont

end Work.Smooth.Morse.Regular
