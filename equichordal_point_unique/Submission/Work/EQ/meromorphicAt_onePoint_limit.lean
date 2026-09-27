import Mathlib
import Submission.Work.EQ.DefsCore

namespace Work.EQ

/-- **A meromorphic germ has a limit in the Riemann sphere.**  If `f` is meromorphic at `0`, then
`f` has a limit in the one-point compactification `OnePoint ℂ` along the punctured neighbourhood of
`0` (the limit is the removable-continuation value when `f` is bounded near `0`, and `∞` when `f`
has a pole there).  This is the "the meromorphic coordinates of a puncture have `ℙ¹`-limits" input
of Rychlik's §6 step 3; Mathlib has `OnePoint ℂ` but no ready-made lemma.

Route (from Mathlib `Analysis/Meromorphic/Order.lean`): split on
`meromorphicOrderAt f 0 ≥ 0`; then use `tendsto_nhds_of_meromorphicOrderAt_nonneg` for the finite
limit and `tendsto_cobounded_of_meromorphicOrderAt_neg` together with
`OnePoint.hasBasis_nhds_infty` / `tendsto_norm_atTop_iff_cobounded` for `∞`. -/
theorem meromorphicAt_onePoint_limit {f : ℂ → ℂ} (hf : MeromorphicAt f 0) :
    ∃ L : OnePoint ℂ, Filter.Tendsto (fun z : ℂ => (f z : OnePoint ℂ))
      (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds L) := by
  rcases lt_or_ge (meromorphicOrderAt f 0) 0 with h | h
  · -- `f` has a pole at `0`: the limit in `ℙ¹` is `∞`.
    refine ⟨OnePoint.infty, ?_⟩
    have hc : Filter.Tendsto f (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ))
        (Filter.coclosedCompact ℂ) := by
      have := tendsto_cobounded_of_meromorphicOrderAt_neg h
      rwa [Metric.cobounded_eq_cocompact, ← Filter.coclosedCompact_eq_cocompact] at this
    exact OnePoint.tendsto_coe_infty.comp hc
  · -- `f` is bounded near `0`: the limit is the removable-continuation value.
    obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hf h
    exact ⟨(c : OnePoint ℂ), OnePoint.continuous_coe.continuousAt.tendsto.comp hc⟩

end Work.EQ
