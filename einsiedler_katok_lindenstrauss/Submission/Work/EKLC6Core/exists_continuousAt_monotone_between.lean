import Mathlib

namespace Work.EKLC6Core

/-- A monotone function `ℝ → ℝ` has at least one point of continuity in every nondegenerate
closed interval `[a, b]`.  Indeed, `Monotone.countable_not_continuousAt` shows that the set of
discontinuity points is countable, while `[a, b]` is uncountable as soon as `a < b`. -/
theorem exists_continuousAt_monotone_between {f : ℝ → ℝ} (hf : Monotone f) {a b : ℝ}
    (hab : a < b) :
    ∃ r : ℝ, a ≤ r ∧ r ≤ b ∧ ContinuousAt f r := by
  by_contra h
  -- Assume no point of `[a, b]` is a continuity point: then `[a, b]` lies in the set of
  -- discontinuities of `f`, which is countable, contradicting the uncountability of `[a, b]`.
  have hsub : Set.Icc a b ⊆ {x | ¬ ContinuousAt f x} := by
    intro x hx
    exact fun hc => h ⟨x, hx.1, hx.2, hc⟩
  have hcount : (Set.Icc a b).Countable := hf.countable_not_continuousAt.mono hsub
  exact absurd (Cardinal.Real.Icc_countable_iff.mp hcount) (not_le.mpr hab)

end Work.EKLC6Core
