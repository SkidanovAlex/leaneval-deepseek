-- Deliberately narrow imports: this module is meant to be usable (transitively) by the
-- cone files, and `import Mathlib` would re-introduce the root-level `Hypergraph`
-- structure, breaking `Solution.lean`/`Submission.lean` (see HANDOFF §3 of session 4).
import Submission.Work.Deep.GKO.NarrowImports

open SimpleGraph

namespace Work.Deep.GKO

/-- A finite vertex set in which every vertex has an `M`-neighbour inside the set is a union of `M`-edges, hence has even cardinality.  (The matching `M` is a subgraph of `R`; `M.IsMatching` gives every vertex of `M.verts` a unique `M`-neighbour.) -/
theorem even_card_of_matching_closed {k : ℕ} {R : SimpleGraph (Fin k)} {M : R.Subgraph}
    (hM : M.IsMatching) {s : Finset (Fin k)} (hcl : ∀ y ∈ s, ∃ z ∈ s, M.Adj y z) :
    Even s.card := by
  classical
  -- The induced subgraph of `M` on `s` is again a matching: the unique `M`-neighbour
  -- of a vertex of `s` lies in `s` (by `hcl`), and `s` is exactly its vertex set.
  have hM' : (M.induce (↑s)).IsMatching := by
    intro v hv
    rw [Subgraph.induce_verts] at hv
    obtain ⟨z, hzs, hzv⟩ := hcl v hv
    refine ⟨z, ?_, ?_⟩
    · show (M.induce (↑s)).Adj v z
      exact (Subgraph.induce_adj M ↑s v z).mpr ⟨hv, hzs, hzv⟩
    · intro y hy
      rw [Subgraph.induce_adj] at hy
      exact (hM.eq_of_adj_left hzv hy.2.2).symm
  have hverts : (M.induce (↑s)).verts = (↑s : Set (Fin k)) := Subgraph.induce_verts M ↑s
  have : Fintype ↥((M.induce (↑s)).verts) := Fintype.ofFinite _
  have h := hM'.even_card
  have hts : (M.induce (↑s)).verts.toFinset = s := by
    ext x
    rw [Set.mem_toFinset, hverts]
    exact Finset.mem_coe
  rwa [hts] at h

end Work.Deep.GKO
