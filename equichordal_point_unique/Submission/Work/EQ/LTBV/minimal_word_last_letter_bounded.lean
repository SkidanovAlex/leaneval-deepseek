import Mathlib
import Submission.Work.EQ.la_tail_bound_value
import Submission.Work.EQ.minimal_word_last_letter
import Submission.Work.EQ.germC_leaf
import Submission.Work.EQ.H0_tail_bounded

/-! # The last letter of the minimal word of a chain is `false`, uniformly for small `ψ₁`

`Work.EQ.last_letter_false_of_isChainWord` proves the combinatorial statement: a reading word of a
chain of length exactly the tail index ends in `false` when the tail index is positive, provided
the whole recursion stays in the ball on which the principal backward branch inverts the germ step
(`invBranch a true (germC a h (λu)) = germC a h u`).

The only input needed to make that hypothesis uniform is the radius supplied by
`Work.EQ.germC_leaf`, which is independent of the chain. Together with the existence of the minimal
reading word (`Work.EQ.exists_isChainWord`, applied at `tailIdx a h q`) this gives the bounded
form of the statement. -/

namespace Work.EQ.LTBV

/-- The principal-leaf identity supplied by `Work.EQ.germC_leaf`, in the `‖·‖ < δ` shape used by
`Work.EQ.last_letter_false_of_isChainWord`. -/
lemma exists_leaf_radius {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, ‖u‖ < δ →
      Work.EQ.invBranch a true (Work.EQ.germC a h ((Work.EQ.eqLam a : ℂ) * u)) =
        Work.EQ.germC a h u := by
  obtain ⟨δ, hδ, hleaf⟩ := (Work.EQ.germC_leaf ha0 ha1 hh).2.2.2
  exact ⟨δ, hδ, fun u hu => hleaf u (by rwa [Metric.mem_ball, dist_zero_right])⟩

/-- A chain whose parameter ψ₁ is small has a reading word of length exactly its tail index whose last letter is `false` when that index is positive. -/
theorem minimal_word_last_letter_bounded {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ {q : Work.EQ.ChainData}, Work.EQ.IsChain a h q → ‖q.2.1‖ < δ₀ →
      ∃ ε : List Bool, q.1 0 = Work.EQ.fan a h ε q.2.1 ∧ ε.length = Work.EQ.tailIdx a h q ∧
        (0 < Work.EQ.tailIdx a h q → ε.getLast? = some false) := by
  obtain ⟨δl, hδl0, hleaf⟩ := exists_leaf_radius ha0 ha1 hh
  refine ⟨δl, hδl0, ?_⟩
  intro q hq hsmall
  obtain ⟨ε, hε⟩ := Work.EQ.exists_isChainWord ha0 ha1 (Work.EQ.tailIdx a h q) q hq
    (Work.EQ.TailP_of_isChain hq)
  refine ⟨ε, hε.2.1, hε.1, ?_⟩
  intro hpos
  exact Work.EQ.last_letter_false_of_isChainWord ha0 ha1 hh hq hε hpos hleaf hsmall

end Work.EQ.LTBV
