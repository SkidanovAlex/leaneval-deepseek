import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# A strict local maximum from a negative second derivative

`exists_ne_of_deriv_deriv_neg`: if `f` is differentiable at `0`, the derivative `deriv f` has a
**negative** derivative `c < 0` at `0`, and `f` is differentiable in a neighbourhood of `0`, then
`f` takes a value **strictly below** `f 0`.

This is the calculus input of the shortening argument of Klingenberg's estimate (Roadmap §112): the
energy of a closed geodesic has a strict local maximum at `σ = 0` when the second variation is
negative, and this is what produces the strictly shorter closed curves.

The proof splits into three cases.  If `deriv f 0 ≠ 0` then the *first* derivative already produces
the sign change (on the appropriate side of `0`), by the slope form
`hasDerivAt_iff_tendsto_slope`.  If `deriv f 0 = 0`, then `deriv f σ < 0` for `σ ∈ (0, δ)` (again by
the slope form, applied to `deriv f`), and the mean value theorem on `[0, σ]` concludes.
-/

namespace Submission.DerivShorten

open Set Filter
open scoped Topology

/-- An interval around `0` on which the slope of `g` at `0` is bounded below by `b' < b`, where `b`
is the limit of the slope. -/
private theorem exists_interval_slope_gt {g : ℝ → ℝ} {b b' : ℝ} (hb : b' < b)
    (h : Tendsto (slope g 0) (𝓝[≠] (0 : ℝ)) (𝓝 b)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ σ : ℝ, σ ≠ 0 → |σ| < δ → b' < slope g 0 σ := by
  have hev : ∀ᶠ σ in 𝓝[≠] (0 : ℝ), b' < slope g 0 σ :=
    (tendsto_order.1 h).1 b' hb
  have h2 : ∀ᶠ y in 𝓝 (0 : ℝ), y ≠ 0 → b' < slope g 0 y :=
    mem_nhdsWithin_iff_eventually.mp hev
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp h2
  refine ⟨ε, hεpos, fun σ hσ hσlt => ?_⟩
  exact hεsub (by rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact hσlt) hσ

/-- An interval around `0` on which the slope of `g` at `0` is bounded above by `b' > b`, where `b`
is the limit of the slope. -/
private theorem exists_interval_slope_lt {g : ℝ → ℝ} {b b' : ℝ} (hb : b < b')
    (h : Tendsto (slope g 0) (𝓝[≠] (0 : ℝ)) (𝓝 b)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ σ : ℝ, σ ≠ 0 → |σ| < δ → slope g 0 σ < b' := by
  have hev : ∀ᶠ σ in 𝓝[≠] (0 : ℝ), slope g 0 σ < b' :=
    (tendsto_order.1 h).2 b' hb
  have h2 : ∀ᶠ y in 𝓝 (0 : ℝ), y ≠ 0 → slope g 0 y < b' :=
    mem_nhdsWithin_iff_eventually.mp hev
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp h2
  refine ⟨ε, hεpos, fun σ hσ hσlt => ?_⟩
  exact hεsub (by rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact hσlt) hσ

/-- **A strict local maximum from a negative second derivative.** -/
theorem exists_ne_of_deriv_deriv_neg {f : ℝ → ℝ} {c : ℝ}
    (h1 : HasDerivAt f (deriv f 0) 0)
    (h2 : HasDerivAt (deriv f) c 0) (hc : c < 0)
    (h3 : ∀ᶠ σ in 𝓝 (0 : ℝ), DifferentiableAt ℝ f σ) :
    ∃ σ : ℝ, σ ≠ 0 ∧ f σ < f 0 := by
  -- an interval on which `f` is differentiable
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x| < δ → DifferentiableAt ℝ f x := by
    obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp h3
    refine ⟨ε, hεpos, fun x hx => ?_⟩
    exact hεsub (by rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact hx)
  rcases lt_trichotomy (deriv f 0) 0 with hneg | hzero | hpos
  · -- `deriv f 0 < 0`: go to the right, the slope is negative
    obtain ⟨δ, hδpos, hδ⟩ := exists_interval_slope_lt (g := f) (b := deriv f 0) (b' := 0) hneg
      (hasDerivAt_iff_tendsto_slope.mp h1)
    refine ⟨δ / 2, by positivity, ?_⟩
    have hδ2pos : (0 : ℝ) < δ / 2 := by positivity
    have h : slope f 0 (δ / 2) < 0 :=
      hδ (δ / 2) (by positivity) (by rw [abs_of_pos hδ2pos]; linarith)
    rw [slope_def_field, sub_zero] at h
    rcases div_neg_iff.mp h with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · exact absurd hB (not_lt.mpr hδ2pos.le)
    · linarith
  · -- `deriv f 0 = 0`: go to the right using the second derivative
    obtain ⟨δ, hδpos, hδ⟩ := exists_interval_slope_lt (g := deriv f) (b := c) (b' := 0) hc
      (hasDerivAt_iff_tendsto_slope.mp h2)
    set σ : ℝ := min δ δ₂ / 2 with hσdef
    have hσpos : 0 < σ := by rw [hσdef]; positivity
    have hσltδ : σ < δ := by
      rw [hσdef]; have : min δ δ₂ ≤ δ := min_le_left _ _; linarith
    have hσltδ₂ : σ < δ₂ := by
      rw [hσdef]; have : min δ δ₂ ≤ δ₂ := min_le_right _ _; linarith
    -- `deriv f` is negative on `(0, σ)`
    have hderivneg : ∀ s : ℝ, 0 < s → s < σ → deriv f s < 0 := by
      intro s hs0 hsσ
      have h := hδ s (ne_of_gt hs0) (by rw [abs_of_pos hs0]; linarith)
      rw [slope_def_field, sub_zero, hzero, sub_zero] at h
      rcases div_neg_iff.mp h with ⟨hA, hB⟩ | ⟨hA, hB⟩
      · exact absurd hB (not_lt.mpr hs0.le)
      · exact hA
    refine ⟨σ, ne_of_gt hσpos, ?_⟩
    -- mean value theorem on `[0, σ]`
    have hcont : ContinuousOn f (Icc 0 σ) := by
      intro x hx
      rcases eq_or_lt_of_le hx.1 with hx0 | hx0
      · subst hx0
        exact h1.continuousAt.continuousWithinAt
      · exact (hδ₂ x (by rw [abs_of_pos hx0]; linarith [hx.2, hσltδ₂])).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ f (Ioo 0 σ) := by
      intro x hx
      exact (hδ₂ x (by rw [abs_of_pos hx.1]; linarith [hx.2, hσltδ₂])).differentiableWithinAt
    obtain ⟨ξ, hξ, hξeq⟩ := exists_deriv_eq_slope f hσpos hcont hdiff
    have hξneg : deriv f ξ < 0 := hderivneg ξ hξ.1 hξ.2
    rw [sub_zero] at hξeq
    have hlt : (f σ - f 0) / σ < 0 := by rw [← hξeq]; exact hξneg
    rcases div_neg_iff.mp hlt with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · exact absurd hB (not_lt.mpr hσpos.le)
    · linarith
  · -- `0 < deriv f 0`: go to the left, the slope is positive
    obtain ⟨δ, hδpos, hδ⟩ := exists_interval_slope_gt (g := f) (b := deriv f 0) (b' := 0) hpos
      (hasDerivAt_iff_tendsto_slope.mp h1)
    have hδ2pos : (0 : ℝ) < δ / 2 := by positivity
    have hσneg : -(δ / 2) < 0 := by linarith
    refine ⟨-(δ / 2), ne_of_lt hσneg, ?_⟩
    have h : 0 < slope f 0 (-(δ / 2)) :=
      hδ _ (ne_of_lt hσneg) (by rw [abs_neg, abs_of_pos hδ2pos]; linarith)
    rw [slope_def_field, sub_zero] at h
    rcases div_pos_iff.mp h with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · exact absurd hB (not_lt.mpr hσneg.le)
    · linarith


/-- **A strict local maximum from a negative second derivative, one-sided form.**  Under the same
hypotheses as `exists_ne_of_deriv_deriv_neg`, the inequality `f σ < f 0` holds *for all* `σ` on one
side of `0` (an interval `(0, δ)` if `deriv f 0 ≤ 0`, and an interval `(-δ, 0)` otherwise). -/
theorem eventually_lt_or_eventually_lt_of_deriv_deriv_neg {f : ℝ → ℝ} {c : ℝ}
    (h1 : HasDerivAt f (deriv f 0) 0)
    (h2 : HasDerivAt (deriv f) c 0) (hc : c < 0)
    (h3 : ∀ᶠ σ in 𝓝 (0 : ℝ), DifferentiableAt ℝ f σ) :
    (∀ᶠ σ in 𝓝[>] (0 : ℝ), f σ < f 0) ∨ (∀ᶠ σ in 𝓝[<] (0 : ℝ), f σ < f 0) := by
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x| < δ → DifferentiableAt ℝ f x := by
    obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp h3
    refine ⟨ε, hεpos, fun x hx => ?_⟩
    exact hεsub (by rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact hx)
  rcases lt_trichotomy (deriv f 0) 0 with hneg | hzero | hpos
  · -- `deriv f 0 < 0`: the slope is negative to the right
    obtain ⟨δ, hδpos, hδ⟩ := exists_interval_slope_lt (g := f) (b := deriv f 0) (b' := 0) hneg
      (hasDerivAt_iff_tendsto_slope.mp h1)
    refine Or.inl ?_
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδpos] with σ hσ hσpos
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hσ
    have h := hδ σ (ne_of_gt hσpos) hσ
    rw [slope_def_field, sub_zero] at h
    rcases div_neg_iff.mp h with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · exact absurd hB (not_lt.mpr hσpos.le)
    · linarith
  · -- `deriv f 0 = 0`: use the second derivative to the right
    obtain ⟨δ, hδpos, hδ⟩ := exists_interval_slope_lt (g := deriv f) (b := c) (b' := 0) hc
      (hasDerivAt_iff_tendsto_slope.mp h2)
    refine Or.inl ?_
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (show 0 < min δ δ₂ / 2 by positivity)]
      with σ hσ hσpos
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt] at hσ
    have hσδ : σ < δ := by
      have h1' : σ < min δ δ₂ / 2 := hσ.2
      have := min_le_left δ δ₂; linarith
    have hσδ₂ : σ < δ₂ := by
      have h1' : σ < min δ δ₂ / 2 := hσ.2
      have := min_le_right δ δ₂; linarith
    -- `deriv f` is negative on `(0, σ)`
    have hderivneg : ∀ s : ℝ, 0 < s → s < σ → deriv f s < 0 := by
      intro s hs0 hsσ
      have h := hδ s (ne_of_gt hs0) (by rw [abs_of_pos hs0]; linarith)
      rw [slope_def_field, sub_zero, hzero, sub_zero] at h
      rcases div_neg_iff.mp h with ⟨hA, hB⟩ | ⟨hA, hB⟩
      · exact absurd hB (not_lt.mpr hs0.le)
      · exact hA
    -- mean value theorem on `[0, σ]`
    have hcont : ContinuousOn f (Icc 0 σ) := by
      intro x hx
      rcases eq_or_lt_of_le hx.1 with hx0 | hx0
      · subst hx0
        exact h1.continuousAt.continuousWithinAt
      · exact (hδ₂ x (by rw [abs_of_pos hx0]; linarith [hx.2])).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ f (Ioo 0 σ) := by
      intro x hx
      exact (hδ₂ x (by rw [abs_of_pos hx.1]; linarith [hx.2])).differentiableWithinAt
    obtain ⟨ξ, hξ, hξeq⟩ := exists_deriv_eq_slope f hσpos hcont hdiff
    have hξneg : deriv f ξ < 0 := hderivneg ξ hξ.1 hξ.2
    rw [sub_zero] at hξeq
    have hlt : (f σ - f 0) / σ < 0 := by rw [← hξeq]; exact hξneg
    rcases div_neg_iff.mp hlt with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · exact absurd hB (not_lt.mpr hσpos.le)
    · linarith
  · -- `0 < deriv f 0`: the slope is positive to the left
    obtain ⟨δ, hδpos, hδ⟩ := exists_interval_slope_gt (g := f) (b := deriv f 0) (b' := 0) hpos
      (hasDerivAt_iff_tendsto_slope.mp h1)
    refine Or.inr ?_
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδpos] with σ hσ hσneg
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hσ
    have h := hδ σ (ne_of_lt hσneg) hσ
    rw [slope_def_field, sub_zero] at h
    rcases div_pos_iff.mp h with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · exact absurd hB (not_lt.mpr hσneg.le)
    · linarith

end Submission.DerivShorten
