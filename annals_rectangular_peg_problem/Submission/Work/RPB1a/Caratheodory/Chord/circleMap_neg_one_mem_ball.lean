import Mathlib

namespace Work.RPB1a.Caratheodory.Chord

open Complex Real

/-- On an interval `[θ₁, θ₂]` contained in `(-π, π)`, the cosine is bounded below by the smaller
of its two endpoint values: the extremum of `cos` on such an interval is attained at an endpoint. -/
lemma cos_ge_min_of_mem_Icc {θ₁ θ₂ θ : ℝ} (h₁ : -π < θ₁) (h₂ : θ₂ < π)
    (hθ : θ ∈ Set.Icc θ₁ θ₂) : min (Real.cos θ₁) (Real.cos θ₂) ≤ Real.cos θ := by
  rcases le_total 0 θ with hθ0 | hθ0
  · have h : Real.cos θ₂ ≤ Real.cos θ :=
      Real.cos_le_cos_of_nonneg_of_le_pi hθ0 (le_of_lt h₂) hθ.2
    exact le_trans (min_le_right _ _) h
  · have h : Real.cos (-θ₁) ≤ Real.cos (-θ) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith [hθ.1])
    rw [Real.cos_neg, Real.cos_neg] at h
    exact le_trans (min_le_left _ _) h

/-- The squared modulus of `circleMap (-1) ρ θ`: since `circleMap (-1) ρ θ = -1 + ρ e^{iθ}`, its
`normSq` is `(-1 + ρ cos θ)² + (ρ sin θ)² = 1 - 2ρ cos θ + ρ²`. -/
lemma normSq_circleMap_neg_one (ρ θ : ℝ) :
    Complex.normSq (circleMap (-1 : ℂ) ρ θ) = 1 - 2 * ρ * Real.cos θ + ρ ^ 2 := by
  rw [circleMap]
  simp only [Complex.normSq_apply, Complex.exp_ofReal_mul_I, Complex.add_re, Complex.add_im,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
  nlinarith [Real.sin_sq_add_cos_sq θ]

set_option linter.unusedVariables false in
theorem circleMap_neg_one_mem_ball {ρ θ₁ θ₂ θ : ℝ} (hρ : 0 < ρ) (hle : θ₁ ≤ θ₂)
    (hθ₁ : θ₁ ∈ Set.Ioo (-Real.pi) Real.pi) (hθ₂ : θ₂ ∈ Set.Ioo (-Real.pi) Real.pi)
    (hc₁ : ρ / 2 < Real.cos θ₁) (hc₂ : ρ / 2 < Real.cos θ₂) (hθ : θ ∈ Set.Icc θ₁ θ₂) :
    circleMap (-1 : ℂ) ρ θ ∈ Metric.ball (0 : ℂ) 1 := by
  rw [Metric.mem_ball, dist_zero_right]
  -- The cosine stays above `ρ/2` throughout the interval, since it is bounded below by the
  -- smaller endpoint value and both endpoints exceed `ρ/2`.
  have hcosθ : ρ / 2 < Real.cos θ :=
    lt_of_lt_of_le (lt_min hc₁ hc₂) (cos_ge_min_of_mem_Icc hθ₁.1 hθ₂.2 hθ)
  -- `‖circleMap (-1) ρ θ‖² = 1 - 2ρ cos θ + ρ² < 1` because `ρ < 2 cos θ`.
  have hsq : ‖circleMap (-1 : ℂ) ρ θ‖ ^ 2 < (1 : ℝ) ^ 2 := by
    rw [Complex.sq_norm, normSq_circleMap_neg_one]
    nlinarith [hcosθ, hρ]
  have hlt := sq_lt_sq.mp hsq
  simpa [abs_of_nonneg (norm_nonneg _)] using hlt

end Work.RPB1a.Caratheodory.Chord
