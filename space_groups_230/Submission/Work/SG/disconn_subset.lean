import Mathlib
import Submission.Work.SG.SellingDefs

namespace Work.SG

/-- If the graph `E` on the four superbase vertices is not connected, then its vertex set splits
into a nonempty proper part `S` with no edge of `E` crossing between `S` and its complement (in
either direction).

This is the elementary combinatorial content of the "disconnected support graph" case: `S` is a
connected component, i.e. the finite set of vertices reachable from a fixed vertex `a`, which is
nonempty (contains `a`) and proper (it avoids any vertex `b` not reachable from `a`). -/
theorem disconn_subset (E : List (Fin 4 × Fin 4)) (h : ¬ IsConnGraph E) :
    ∃ S : Finset (Fin 4), S.Nonempty ∧ S ≠ Finset.univ ∧
      ∀ i ∈ S, ∀ j ∉ S, (i, j) ∉ E ∧ (j, i) ∉ E := by
  classical
  unfold IsConnGraph at h
  push Not at h
  obtain ⟨a, b, hab⟩ := h
  -- `S` = the set of vertices reachable from `a` by a walk in the underlying undirected graph.
  refine ⟨Finset.univ.filter
      (fun x => Relation.ReflTransGen (fun x y => (x, y) ∈ E ∨ (y, x) ∈ E) a x), ?_, ?_, ?_⟩
  · exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, Relation.ReflTransGen.refl⟩⟩
  · intro hS
    -- `b` would be reachable from `a` if `S` were everything.
    have hb : b ∈ Finset.univ.filter
        (fun x => Relation.ReflTransGen (fun x y => (x, y) ∈ E ∨ (y, x) ∈ E) a x) := by
      rw [hS]; exact Finset.mem_univ b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact hab hb
  · intro i hi j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    -- an edge between `i ∈ S` and `j ∉ S` would put `j` back into `S`
    exact ⟨fun hij => hj (hi.trans (Relation.ReflTransGen.single (Or.inl hij))),
           fun hji => hj (hi.trans (Relation.ReflTransGen.single (Or.inr hji)))⟩

end Work.SG
