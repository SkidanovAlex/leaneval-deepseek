import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.nonadj_card

namespace Work.Deep.Sparse

/-- Count of non-adjacent neighbour pairs in a δ-sparse graph: for every vertex `v` of a graph
whose every neighbourhood spans at most `(1-δ)Δ²/2` edges, the number of *ordered pairs of
distinct non-adjacent neighbours* of `v` is at least `d(d-1) - (1-δ)Δ²`, where `d = deg v`. -/
theorem pt_nonadj_ge {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {δ Δ : ℝ} (hsp : ∀ v : V, (ErdosFaberLovaszConjecture.nbrEdges G v : ℝ) ≤ (1 - δ) * Δ ^ 2 / 2)
    (v : V) :
    (G.degree v : ℝ) * ((G.degree v : ℝ) - 1) - (1 - δ) * Δ ^ 2
      ≤ ((Work.Deep.Sparse.nonAdjPairs G v).card : ℝ) := by
  -- `nonadj_card` counts the ordered pairs: `|nonAdjPairs G v| = d(d-1) - 2 e(G[N(v)])`,
  -- with `d = deg v`; the sparsity hypothesis bounds `e(G[N(v)])`.
  have hcard := nonadj_card G v
  have h1 : ((Work.Deep.Sparse.nonAdjPairs G v).card : ℝ)
      = (G.degree v : ℝ) * ((G.degree v : ℝ) - 1)
        - 2 * (ErdosFaberLovaszConjecture.nbrEdges G v : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hcard
    push_cast at this
    linarith [this]
  have h2 := hsp v
  linarith [h1, h2]

end Work.Deep.Sparse
