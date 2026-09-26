import Mathlib
import Submission.Work.SG.EdgeSetDefs

namespace Work.SG

/-- Relabelling the edges of `E` by a permutation `τ` and putting them in normal form does not
change the underlying undirected edge set: `edgeSet (permE τ E) = (edgeSet E).image (Sym2.map τ)`.

The point is that the normal-form ordering introduced by `permE` is invisible to `Sym2`, since
`s((nrmEdge a b).1, (nrmEdge a b).2) = s(a, b)`. -/
theorem edgeSet_permE (τ : Equiv.Perm (Fin 4)) (E : List (Fin 4 × Fin 4)) :
    edgeSet (permE τ E) = (edgeSet E).image (Sym2.map τ) := by
  ext z
  simp only [edgeSet, permE, Finset.mem_image, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨a, ⟨q, hq, rfl⟩, ha⟩
    refine ⟨s(q.1, q.2), ⟨q, hq, rfl⟩, ?_⟩
    rw [Sym2.map_mk]
    rw [← nrmEdge_sym2 (τ q.1) (τ q.2), ha]
  · rintro ⟨a, ⟨q, hq, rfl⟩, hw⟩
    refine ⟨nrmEdge (τ q.1) (τ q.2), ⟨q, hq, rfl⟩, ?_⟩
    rw [nrmEdge_sym2]
    rw [Sym2.map_mk] at hw
    exact hw

end Work.SG
