import Mathlib

namespace Work.C17b

/-- If a function `A` is analytic on the open ball of radius `δ` around `0` in `ℂ` and vanishes on
the positive real interval `(0, δ)`, then `A` vanishes on the whole ball. The zeros on `(0, δ)`
accumulate at `0`, which lies inside the (preconnected) ball, so the identity theorem applies. -/
theorem analyticOn_eqOn_zero_of_vanishing_Ioo {δ : ℝ} (hδ : 0 < δ) {A : ℂ → ℂ}
    (hA : AnalyticOnNhd ℂ A (Metric.ball (0 : ℂ) δ))
    (h : ∀ t : ℝ, 0 < t → t < δ → A (t : ℂ) = 0) :
    ∀ u ∈ Metric.ball (0 : ℂ) δ, A u = 0 := by
  -- `0` is an accumulation point of the zero set of `A` inside the ball
  have hcl : (0 : ℂ) ∈ closure ({z : ℂ | A z = 0} \ {0}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    set t : ℝ := min (δ / 2) (ε / 2) with ht
    have ht0 : 0 < t := lt_min (by linarith) (by linarith)
    have htδ : t < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have htε : t < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    refine ⟨(t : ℂ), ⟨h t ht0 htδ, ?_⟩, ?_⟩
    · simpa using ht0.ne'
    · rw [dist_zero_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
      exact htε
  have hz : Set.EqOn A 0 (Metric.ball (0 : ℂ) δ) :=
    hA.eqOn_zero_of_preconnected_of_mem_closure Metric.isPreconnected_ball
      (Metric.mem_ball_self hδ) hcl
  intro u hu
  simpa using hz hu

end Work.C17b
