import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology

namespace Work.Diff.MP

/-- If `f` is lower semi-continuous at `t` "from the left" in the quantitative form
`∀ ε > 0, ∃ δ > 0, ∀ s, 0 < s → s < δ → f t ≤ f (t - s) + ε` and continuous at `t` from the right
(`ContinuousWithinAt f (Ici t) t`), then `y ↦ f y * exp (-(C y))` is lower semi-continuous at `t`:
for every `η > 0` there is `δ > 0` with `f t * exp (-(C t)) - η < f y * exp (-(C y))` for
`|y - t| < δ`. -/
theorem lsc_mul_exp {f : ℝ → ℝ} {C t : ℝ}
    (hlsc : ∀ ε > 0, ∃ δ > 0, ∀ s : ℝ, 0 < s → s < δ → f t ≤ f (t - s) + ε)
    (hrc : ContinuousWithinAt f (Set.Ici t) t) :
    ∀ η > 0, ∃ δ > 0, ∀ y : ℝ, |y - t| < δ →
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
    simp only [Set.mem_Iio] at hyt
    have h1 : 0 < t - y := by linarith
    have h2 : t - y < δ₁ := by linarith
    have h3 := hδ₁ (t - y) h1 h2
    have h4 : t - (t - y) = y := by ring
    rw [h4] at h3
    linarith
  -- Continuity of the weighted left comparison function at `t`.
  have hL2 : ∀ᶠ y in 𝓝[Set.Iio t] t,
      f t * Real.exp (-(C * t)) - η < (f t - ε₀) * Real.exp (-(C * y)) := by
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    have hval : f t * Real.exp (-(C * t)) - η < (f t - ε₀) * Real.exp (-(C * t)) := by
      nlinarith [hε₀lt]
    have hcont : ContinuousAt (fun y : ℝ => (f t - ε₀) * Real.exp (-(C * y))) t := by fun_prop
    exact hcont.tendsto.eventually (isOpen_Ioi.mem_nhds hval)
  have hL : ∀ᶠ y in 𝓝[Set.Iio t] t,
      f t * Real.exp (-(C * t)) - η < f y * Real.exp (-(C * y)) := by
    filter_upwards [hLf, hL2] with y hy1 hy2
    exact lt_of_lt_of_le hy2 (mul_le_mul_of_nonneg_right hy1 (Real.exp_pos _).le)
  -- The right-hand side: continuity of `f` from the right.
  have hR : ∀ᶠ y in 𝓝[Set.Ici t] t,
      f t * Real.exp (-(C * t)) - η < f y * Real.exp (-(C * y)) := by
    have hcont : ContinuousWithinAt (fun y : ℝ => f y * Real.exp (-(C * y))) (Set.Ici t) t :=
      hrc.mul (by fun_prop)
    refine hcont.tendsto.eventually ?_
    exact isOpen_Ioi.mem_nhds
      (show f t * Real.exp (-(C * t)) - η < f t * Real.exp (-(C * t)) by linarith)
  rw [eventually_nhdsWithin_iff] at hL hR
  have hkey : ∀ᶠ y in 𝓝 t,
      f t * Real.exp (-(C * t)) - η < f y * Real.exp (-(C * y)) := by
    filter_upwards [hL, hR] with y h1 h2
    rcases lt_or_ge y t with hlt | hge
    · exact h1 hlt
    · exact h2 hge
  rw [Metric.eventually_nhds_iff] at hkey
  obtain ⟨δ, hδpos, hδ⟩ := hkey
  exact ⟨δ, hδpos, fun y hy => hδ (by simpa [Real.dist_eq] using hy)⟩

end Work.Diff.MP
