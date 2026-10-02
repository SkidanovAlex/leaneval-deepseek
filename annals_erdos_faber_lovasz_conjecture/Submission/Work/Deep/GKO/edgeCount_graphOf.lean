import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs

/-!
# `crossEdges (graphOf 𝓖) A B = edgeCount 𝓖 A B`

The graph-side and hypergraph-side edge counts between two disjoint vertex sets
agree.  `Disjoint A B` is essential: it guarantees `p.1 ≠ p.2` on `A ×ˢ B`,
which is exactly the extra conjunct in `(graphOf 𝓖).Adj` compared with the
`edgeCount` predicate `{p.1, p.2} ∈ 𝓖`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open ErdosFaberLovaszConjecture

namespace Work.Deep.GKO

theorem edgeCount_graphOf {n : ℕ} (𝓖 : ErdosFaberLovaszConjecture.Hypergraph (Fin n)) (A B : Finset (Fin n))
    (hAB : Disjoint A B) :
    Work.Deep.GKO.crossEdges (Work.Deep.GKO.graphOf 𝓖) A B = ErdosFaberLovaszConjecture.edgeCount 𝓖 A B := by
  classical
  simp only [Work.Deep.GKO.crossEdges, ErdosFaberLovaszConjecture.edgeCount,
    Work.Deep.GKO.graphOf_adj]
  rw [Finset.filter_congr_decidable, Finset.filter_congr_decidable]
  congr 1
  refine Finset.filter_congr (p := fun x : Fin n × Fin n => x.1 ≠ x.2 ∧ ({x.1, x.2} : Set (Fin n)) ∈ 𝓖)
    (q := fun p : Fin n × Fin n => ({p.1, p.2} : Set (Fin n)) ∈ 𝓖) ?_
  intro p hp
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
  exact ⟨fun h => h.2, fun h => ⟨Finset.disjoint_iff_ne.mp hAB p.1 h1 p.2 h2, h⟩⟩

end Work.Deep.GKO
