import Mathlib

open Filter
open scoped Topology

namespace Work.EQ

/-- A function meromorphic at `0` that vanishes on a sequence of nonzero points tending to `0`
vanishes identically on a punctured neighbourhood of `0`. Route: if `meromorphicOrderAt f 0 = ⊤`
this is `meromorphicOrderAt_eq_top_iff`; otherwise the normal form
`meromorphicOrderAt_eq_int_iff` writes `f =ᶠ[𝓝[≠] 0] (·) ^ m • g` with `g` analytic at `0` and
`g 0 ≠ 0`, and `g` vanishes on the sequence, contradicting the analytic zero-isolation
`AnalyticAt.frequently_zero_iff_eventually_zero`. -/
theorem eventuallyEq_zero_of_meromorphicAt_of_seq_zero {f : ℂ → ℂ} (hf : MeromorphicAt f 0)
    {t : ℕ → ℂ} (ht0 : ∀ n, t n ≠ 0) (ht : Filter.Tendsto t Filter.atTop (nhds 0))
    (hz : ∀ n, f (t n) = 0) :
    f =ᶠ[nhdsWithin (0:ℂ) {(0:ℂ)}ᶜ] 0 := by
  have hfreq : ∃ᶠ z in 𝓝[≠] (0:ℂ), f z = 0 := by
    have ht' : Filter.Tendsto t Filter.atTop (𝓝[≠] (0:ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨ht, Filter.Eventually.of_forall (fun n => by simpa using ht0 n)⟩
    exact ht'.frequently (Filter.Frequently.of_forall hz)
  exact (MeromorphicAt.frequently_zero_iff_eventuallyEq_zero hf).mp hfreq

end Work.EQ
