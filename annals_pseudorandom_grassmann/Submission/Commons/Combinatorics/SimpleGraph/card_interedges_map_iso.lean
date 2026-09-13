import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Combinatorics.SimpleGraph.Maps

namespace Commons.Combinatorics.SimpleGraph

/-- The number of edges of `G` between a finset `S` and its complement is preserved by
a graph isomorphism `e : G ≃g G'`, the two vertex sets being carried over by `e`. -/
theorem card_interedges_map_iso {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] {G : SimpleGraph V} {G' : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel G'.Adj] (e : SimpleGraph.Iso G G') (S : Finset V) : (G'.interedges (S.map e.toEquiv.toEmbedding) (Sᶜ.map e.toEquiv.toEmbedding)).card = (G.interedges S Sᶜ).card := by
  classical
  refine (Finset.card_bij (fun p (_ : p ∈ G.interedges S Sᶜ) => (e p.1, e p.2)) ?_ ?_ ?_).symm
  · rintro ⟨a, b⟩ hp
    rw [SimpleGraph.mem_interedges_iff] at hp
    rw [SimpleGraph.mem_interedges_iff]
    exact ⟨Finset.mem_map_of_mem _ hp.1, Finset.mem_map_of_mem _ hp.2.1, e.map_rel_iff.mpr hp.2.2⟩
  · rintro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h
    rw [Prod.mk.injEq] at h
    exact Prod.ext (e.toEquiv.injective h.1) (e.toEquiv.injective h.2)
  · rintro ⟨a, b⟩ hq
    rw [SimpleGraph.mem_interedges_iff] at hq
    obtain ⟨h1, h2, h3⟩ := hq
    rw [Finset.mem_map_equiv] at h1 h2
    refine ⟨(e.symm a, e.symm b), ?_, ?_⟩
    · rw [SimpleGraph.mem_interedges_iff]
      exact ⟨h1, h2, e.symm.map_rel_iff.mpr h3⟩
    · exact Prod.ext (e.apply_symm_apply a) (e.apply_symm_apply b)

end Commons.Combinatorics.SimpleGraph