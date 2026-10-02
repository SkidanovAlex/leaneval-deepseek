import Submission.Work.Deep.GKO.NarrowImports
import Submission.Commons.Combinatorics.SimpleGraph.vizing
import Submission.Commons.Combinatorics.SimpleGraph.vizing_two_max

set_option linter.style.haveILetI false

namespace Work.Deep.GKO.Abs

/-- Vizing's bound applied to the edges of `H` inside `A`: if every degree of `H` is at most `d`,
the edges of `H` with both endpoints in `A` admit a proper edge colouring with `d+1` colours
(two of them sharing a vertex get different colours).

The workspace already contains Vizing's bound: `Submission/Commons/Combinatorics/SimpleGraph/vizing.lean`
gives `Commons.Combinatorics.SimpleGraph.vizing (G : SimpleGraph V) : G.lineGraph.Colorable (G.maxDegree + 1)`,
and `Submission/Commons/Combinatorics/SimpleGraph/vizing_two_max.lean` gives
`Commons.Combinatorics.SimpleGraph.exists_isProper_of_colorable`, which converts a colouring of a
line graph into a function `Sym2 V → Fin k` that is proper on `G.edgeFinset`.  Two existing worked
examples of exactly this pattern are `Submission/Work/Deep/Reed/Coloring/exists_insideEdgeColouring.lean`
and `Submission/EFL/Comm/EdgeColoringPairFamily.lean`.  The graph to colour here is the subgraph of
`H` whose edges are the `e ∈ H.edgeSet` with `(e : Set (Fin n)) ⊆ A` (e.g.
`SimpleGraph.fromEdgeSet` of that edge set, whose edge set is exactly that family); its maximum
degree is `≤ d` because its neighbour sets sit inside those of `H`.

Since `H` itself already has maximum degree at most `d`, it suffices to take Vizing's proper
edge colouring of the *whole* graph `H` (with `H.maxDegree + 1 ≤ d + 1` colours) and restrict it
to the inside edges: two inside edges of `H` that share a vertex are two edges of `H` sharing a
vertex, so Vizing's colouring separates them. -/
theorem insideColouring {n : ℕ} (A : Finset (Fin n)) (H : SimpleGraph (Fin n)) {d : ℕ}
    (hd : ∀ v : Fin n, Nat.card (H.neighborSet v) ≤ d) :
    ∃ col : Sym2 (Fin n) → Fin (d + 1),
      ∀ e e' : Sym2 (Fin n), e ∈ H.edgeSet → (e : Set (Fin n)) ⊆ (A : Set (Fin n)) →
        e' ∈ H.edgeSet → (e' : Set (Fin n)) ⊆ (A : Set (Fin n)) →
        e ≠ e' → (∃ v, v ∈ e ∧ v ∈ e') → col e ≠ col e' := by
  classical
  -- Every degree of `H` is at most `d`.
  have hdeg : ∀ v : Fin n, H.degree v ≤ d := fun v => by
    rw [← Commons.Combinatorics.SimpleGraph.natcard_neighborSet_eq_degree (G := H) v]
    exact hd v
  have hmax : H.maxDegree ≤ d := H.maxDegree_le_of_forall_degree_le d hdeg
  have hle : H.maxDegree + 1 ≤ d + 1 := by omega
  haveI : NeZero (d + 1) := ⟨Nat.succ_ne_zero d⟩
  -- Vizing's theorem: a proper edge colouring of `H` with `H.maxDegree + 1 ≤ d + 1` colours.
  obtain ⟨c, hc⟩ := Commons.Combinatorics.SimpleGraph.exists_isProper_of_colorable H
    (SimpleGraph.Colorable.mono hle (Commons.Combinatorics.SimpleGraph.vizing H))
  refine ⟨c, ?_⟩
  intro e e' he _ he' _ hne hadj
  exact hc e (SimpleGraph.mem_edgeFinset.mpr he) e' (SimpleGraph.mem_edgeFinset.mpr he') hne hadj

end Work.Deep.GKO.Abs
