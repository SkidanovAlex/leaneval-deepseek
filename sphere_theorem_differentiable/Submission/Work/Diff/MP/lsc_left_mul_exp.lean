import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology

namespace Work.Diff.MP

/-- Quantitative one-sided lower semi-continuity of `f` at `t` (from the left):
`∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → f t ≤ f (t - s) + ε`, i.e. `f (t - s) ≥ f t - ε`
for small `s > 0`.  Then the function `y ↦ f y * exp (-(C y))` is bounded below near `t`
from the left: for every `η > 0` there is `δ > 0` with
`f t * exp (-(C t)) - η < f y * exp (-(C y))` for all `y ∈ (t - δ, t]`. -/
theorem lsc_left_mul_exp {f : ℝ → ℝ} {C t : ℝ}
    (hlsc : ∀ ε > 0, ∃ δ > 0, ∀ s : ℝ, 0 < s → s < δ → f t ≤ f (t - s) + ε) :
    ∀ η > 0, ∃ δ > 0, ∀ y : ℝ, t - δ < y → y ≤ t →
      f t * Real.exp (-(C * t)) - η < f y * Real.exp (-(C * y)) := by
  intro η hη
  -- Pick `ε₀ > 0` with `ε₀ * exp (-(C t)) < η`.
  obtain ⟨ε₀, hε₀pos, hε₀lt⟩ : ∃ ε : ℝ, 0 < ε ∧ ε * Real.exp (-(C * t)) < η := by
    refine ⟨η / (2 * Real.exp (-(C * t))), by positivity, ?_⟩
    rw [div_mul_eq_mul_div, mul_div_mul_right _ _ (Real.exp_ne_zero _)]
    linarith
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hlsc ε₀ hε₀pos
  -- The left-hand side: `f y ≥ f t - ε₀` for `y` just below `t`.
  have hLf : ∀ᶠ y in 𝓝[Set.Iio t] t, f t - ε₀ ≤ f y := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioi_mem_nhds (show t - δ₁ < t by linarith)] with y hy hyt
    simp only [Set.mem_Ioi] at hy
    have h1 : 0 < t - y := by simp only [Set.mem_Iio] at hyt; linarith
    have h2 : t - y < δ₁ := by linarith
    have h3 := hδ₁ (t - y) h1 h2
    have h4 : t - (t - y) = y := by ring
    rw [h4] at h3
    linarith
  -- Near `t` from the left, the weighted lower bound `(f t - ε₀) * exp (-(C y))` beats
  -- the target value `f t * exp (-(C t)) - η`.
  have hL2 : ∀ᶠ y in 𝓝[Set.Iio t] t,
      f t * Real.exp (-(C * t)) - η < (f t - ε₀) * Real.exp (-(C * y)) := by
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    have hval : f t * Real.exp (-(C * t)) - η < (f t - ε₀) * Real.exp (-(C * t)) := by
      nlinarith [hε₀lt]
    have hcont : ContinuousAt (fun y : ℝ => (f t - ε₀) * Real.exp (-(C * y))) t := by fun_prop
    exact hcont.tendsto.eventually (isOpen_Ioi.mem_nhds hval)
  have hL : ∀ᶠ y in 𝓝[Set.Iio t] t, f t * Real.exp (-(C * t)) - η < f y * Real.exp (-(C * y)) := by
    filter_upwards [hLf, hL2] with y hy1 hy2
    exact lt_of_lt_of_le hy2 (mul_le_mul_of_nonneg_right hy1 (Real.exp_pos _).le)
  -- Convert the eventual statement on `(t - δ, t)` into an explicit `δ`.
  rw [eventually_nhdsWithin_iff] at hL
  rw [Metric.eventually_nhds_iff] at hL
  obtain ⟨δ, hδpos, hδ⟩ := hL
  refine ⟨δ, hδpos, ?_⟩
  intro y hy1 hy2
  rcases lt_or_eq_of_le hy2 with hlt | heq
  · exact hδ (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith) (by simpa using hlt)
  · subst heq; linarith

end Work.Diff.MP
