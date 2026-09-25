import Mathlib
import Submission.Work.LT.Defs
import Submission.Work.LT.lr_class_dot_bound

namespace Work.LT

/-- **Left-walk pair bound.** For the normalised left-averaging walk
`POp A b g = (∑ i, b (A i * g)) / Δ`, the mixed form `2 ⟨a, POp A b⟩` is at most
`μ (‖a‖² + ‖b‖²)` when `b` is mean-zero and the walk contracts mean-zero functions by `μ`
(`leftExpander A μ`). This is the left analogue of `lr_pair_bound_right`, and is the form in
which the one-sided spectral gap enters the DELLM pair bounds.

It is `lr_class_dot_bound` with `POp A b g` written out. -/
theorem lr_pair_bound_left {G : Type} [Group G] [Fintype G] {Δ : ℕ} (A : Fin Δ → G) (μ : ℝ)
    (hμ : 0 ≤ μ) (hA : leftExpander A μ) (a b : G → ℝ) (hb : ∑ g, b g = 0) :
    2 * (∑ g, a g * ((∑ i : Fin Δ, b (A i * g)) / (Δ : ℝ)))
      ≤ μ * ((∑ g, a g ^ 2) + ∑ g, b g ^ 2) := by
  simpa only [POp] using lr_class_dot_bound A μ hA hμ a b hb

end Work.LT
