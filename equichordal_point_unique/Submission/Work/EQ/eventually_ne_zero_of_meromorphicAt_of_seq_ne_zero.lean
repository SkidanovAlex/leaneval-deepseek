import Mathlib

namespace Work.EQ

/-- A function meromorphic at `0` that is nonzero on a sequence of nonzero points tending to `0`
is nonzero on a punctured disc around `0`. Route: `MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero`
gives the dichotomy `f =ᶠ[𝓝[≠] 0] 0` or `f =ᶠ[𝓝[≠] 0] ≠ 0`; the first branch is impossible because
`t n → 0` with `t n ≠ 0` makes `f (t n) = 0` for some `n`, contradicting `hz`. The second branch
converts to the claimed `ε`-shaped statement by `eventually_nhdsWithin_iff` and
`Metric.eventually_nhds_iff`. -/
theorem eventually_ne_zero_of_meromorphicAt_of_seq_ne_zero {f : ℂ → ℂ} (hf : MeromorphicAt f 0)
    {t : ℕ → ℂ} (ht0 : ∀ n, t n ≠ 0) (ht : Filter.Tendsto t Filter.atTop (nhds 0))
    (hz : ∀ n, f (t n) ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ε → f z ≠ 0 := by
  rcases MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero hf with h0 | hne
  · exfalso
    rw [eventually_nhdsWithin_iff] at h0
    have h0' : ∀ᶠ n in Filter.atTop, f (t n) = 0 := by
      filter_upwards [ht.eventually h0] with n hn
      exact hn (by simpa using ht0 n)
    obtain ⟨n, hn⟩ := h0'.exists
    exact hz n hn
  · rw [eventually_nhdsWithin_iff] at hne
    rw [Metric.eventually_nhds_iff] at hne
    obtain ⟨ε, hε, h⟩ := hne
    exact ⟨ε, hε, fun z hzpos hzlt =>
      h (by rwa [dist_zero_right]) (by simpa using hzpos.ne')⟩

end Work.EQ
