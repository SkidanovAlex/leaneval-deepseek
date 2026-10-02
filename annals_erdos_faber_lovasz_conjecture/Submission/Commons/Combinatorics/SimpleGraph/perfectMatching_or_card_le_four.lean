import Mathlib.Data.Set.Card
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Combinatorics.SimpleGraph.exists_perfectMatching_of_minDegree

namespace Commons.Combinatorics.SimpleGraph

/-- If `G` has an even number of vertices and minimum degree at least `|V| - 3`, then either `G`
has a perfect matching, or `|V| ≤ 4`.  The small cases are genuinely exceptional: the star
`K_{1,3}` on `4` vertices has minimum degree `1 = 4 - 3` but no perfect matching. -/
theorem perfectMatching_or_card_le_four {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (heven : Even (Fintype.card V))
    (hdeg : ∀ v : V, Fintype.card V - 3 ≤ G.degree v) :
    (∃ M : G.Subgraph, M.IsPerfectMatching) ∨ Fintype.card V ≤ 4 := by
  by_cases h : Fintype.card V ≤ 4
  · exact Or.inr h
  · exact Or.inl
      (exists_perfectMatching_of_minDegree V G (not_le.mp h) heven hdeg)

end Commons.Combinatorics.SimpleGraph