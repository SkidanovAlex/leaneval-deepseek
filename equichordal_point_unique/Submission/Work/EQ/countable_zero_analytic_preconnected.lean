import Mathlib

namespace Work.EQ

/-- The zero set of a function analytic on a neighbourhood of a preconnected set `U`
is countable, provided `f` does not vanish at some point `z₀ ∈ U`.

This is the identity principle together with the fact that a discrete subset of a
second-countable space is countable: if `f` were `0` on `U` then `f z₀ = 0`, so
`AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected` gives that `f` is
nonzero along `codiscreteWithin U`, i.e. the zero set has no accumulation point in
`U` and is therefore discrete; discreteness plus Lindelöf (from second-countability
of `ℂ`) yields countability. -/
theorem countable_zero_analytic_preconnected {U : Set ℂ} (hU : IsPreconnected U) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hf₀ : f z₀ ≠ 0) :
    {z ∈ U | f z = 0}.Countable := by
  rcases hf.eqOn_zero_or_eventually_ne_zero_of_preconnected hU with h | h
  · exact absurd (h hz₀) hf₀
  · -- `f` is nonzero along `codiscreteWithin U`, so the zero set is discrete.
    have hZ : IsDiscrete ({z | f z = 0} ∩ U) := isDiscrete_of_codiscreteWithin h
    rw [show {z ∈ U | f z = 0} = {z | f z = 0} ∩ U from by ext z; simp [and_comm]]
    exact (HereditarilyLindelofSpace.isLindelof ({z | f z = 0} ∩ U)).countable_of_isDiscrete hZ

end Work.EQ
