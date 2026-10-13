import Mathlib

namespace Work.WilC4aCS

/-- If `g : ℝ → ℝ` is analytic at `0` and does not vanish identically on a neighbourhood of `0`,
then it does not vanish on a punctured neighbourhood of `0`: there is `ε > 0` such that
`g x ≠ 0` for every `x ≠ 0` with `|x| < ε`.

This is the local principle of isolated zeros for real analytic functions, extracted from
`AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`, together with the description of the
punctured neighbourhood filter `𝓝[≠] 0` in a metric space. -/
theorem analyticAt_punctured_ne_zero {g : ℝ → ℝ} (hg : AnalyticAt ℝ g 0)
    (hnz : ¬ (∀ᶠ x in nhds (0 : ℝ), g x = 0)) :
    ∃ ε > (0 : ℝ), ∀ x : ℝ, x ≠ 0 → |x| < ε → g x ≠ 0 := by
  rcases hg.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact absurd h hnz
  · -- `h : ∀ᶠ z in 𝓝[≠] 0, g z ≠ 0`; turn it into an explicit ball condition.
    simp only [Filter.Eventually] at h
    rw [Metric.mem_nhdsWithin_iff] at h
    obtain ⟨ε, hε, hball⟩ := h
    refine ⟨ε, hε, ?_⟩
    intro x hx hlt
    exact hball ⟨by simpa [Metric.mem_ball, Real.dist_eq] using hlt, hx⟩

end Work.WilC4aCS
