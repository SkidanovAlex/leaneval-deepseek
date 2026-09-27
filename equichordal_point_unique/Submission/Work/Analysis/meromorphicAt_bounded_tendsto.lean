import Mathlib
import Submission.Work.EQ.meromorphic_order_nonneg_of_bounded

/-! # Meromorphic functions at `0`: boundedness gives a limit

A meromorphic function at `0` that is bounded on a punctured neighbourhood has a (finite) limit
there.  This is the input that turns "the coordinates of a punctured chart are meromorphic"
(`IsPuncturedChart`) into "each coordinate either converges or blows up" — combined with
`MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero` it gives the middle-window analysis of
`Work.EQ`'s puncture-counting route.

The proof is the two-line combination of the workspace lemma
`Work.EQ.meromorphic_order_nonneg_of_bounded` with Mathlib's
`tendsto_nhds_of_meromorphicOrderAt_nonneg`. -/

namespace Work.Analysis

open Filter Set

/-- **A meromorphic function at `0` that is bounded on a punctured neighbourhood has a limit.** -/
theorem meromorphicAt_bounded_tendsto {f : ℂ → ℂ} (hf : MeromorphicAt f 0) {C : ℝ}
    (hb : ∀ᶠ z : ℂ in nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ), ‖f z‖ ≤ C) :
    ∃ L : ℂ, Filter.Tendsto f (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds L) :=
  tendsto_nhds_of_meromorphicOrderAt_nonneg hf
    (Work.EQ.meromorphic_order_nonneg_of_bounded hf hb)

/-- **A meromorphic function at `0` has a limit or blows up.**  The dichotomy form: either `f`
converges along the punctured neighbourhood filter of `0`, or `‖f‖ → ∞` there. -/
theorem meromorphicAt_tendsto_or_tendsto_atTop {f : ℂ → ℂ} (hf : MeromorphicAt f 0) :
    (∃ L : ℂ, Filter.Tendsto f (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds L)) ∨
      Filter.Tendsto (fun z : ℂ => ‖f z‖) (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) atTop := by
  rcases lt_or_ge (meromorphicOrderAt f 0) 0 with h | h
  · right
    exact tendsto_norm_atTop_iff_cobounded.2 ((tendsto_cobounded_iff_meromorphicOrderAt_neg hf).2 h)
  · left
    exact tendsto_nhds_of_meromorphicOrderAt_nonneg hf h

end Work.Analysis
