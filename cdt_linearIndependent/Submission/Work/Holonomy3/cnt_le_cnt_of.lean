import Mathlib
import Submission.Work.Holonomy3.defs

namespace Work.Holonomy3

/-- **Monotonicity of the counting function for a pointwise implication.**
If every index `i` whose `u`-value lies in `[a,b)` has its `t`-value lying in `[A,B)`, then the
number of `u`-values in `[a,b)` is at most the number of `t`-values in `[A,B)`.

This is the elementary observation that the index map underlying the implication is the identity,
hence injective: `{i | u i ∈ [a,b)} ⊆ {i | t i ∈ [A,B)}`. -/
theorem cnt_le_cnt_of {n : ℕ} (t u : Fin n → ℝ) {a b A B : ℝ}
    (h : ∀ i, u i ∈ Set.Ico a b → t i ∈ Set.Ico A B) :
    Submission.CDT.Discrepancy.cnt u a b ≤ Submission.CDT.Discrepancy.cnt t A B := by
  unfold Submission.CDT.Discrepancy.cnt
  exact Finset.card_le_card fun i hi => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact h i hi

end Work.Holonomy3
