import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs

namespace Work.Deep.GKO

open ErdosFaberLovaszConjecture

/-- If the edge set of the graph underlying a 2-uniform hypergraph is partitioned into `k` matchings, then the hypergraph is `k`-edge-colourable.  This is the final conversion step of the reduction: the edge-colouring of `𝓖` with `Δ(𝓖)` colours is produced by exhibiting a partition of `E(graphOf 𝓖)` into `Δ(𝓖)` matchings. -/
theorem colorable_of_matchingDecomposition {n : ℕ}
    (𝓖 : ErdosFaberLovaszConjecture.Hypergraph (Fin n))
    (h2 : ∀ e ∈ 𝓖, ErdosFaberLovaszConjecture.edgeSize e = 2) {k : ℕ}
    (h : Work.Deep.GKO.HasMatchingDecomposition (Work.Deep.GKO.graphOf 𝓖) k) :
    ErdosFaberLovaszConjecture.Hypergraph.Colorable k 𝓖 := by
  classical
  obtain ⟨M, hmatch, -, -, hcov⟩ := h
  -- Every edge of `𝓖` has exactly two vertices, so it gives an edge of `graphOf 𝓖`,
  -- which lies in one of the `k` matchings.
  have hex : ∀ e : 𝓖, ∃ i : Fin k, ∃ u v : Fin n, u ≠ v ∧ (e : Set (Fin n)) = {u, v} ∧
      (M i).Adj u v := by
    rintro ⟨e, he⟩
    have hncard : e.ncard = 2 := by
      rw [← ErdosFaberLovaszConjecture.edgeSize_eq_ncard e]
      exact h2 e he
    obtain ⟨x, y, hxy, heq⟩ := Set.ncard_eq_two.mp hncard
    have hmem : s(x, y) ∈ (graphOf 𝓖).edgeSet := by
      rw [SimpleGraph.mem_edgeSet]
      exact ⟨hxy, by rw [← heq]; exact he⟩
    obtain ⟨i, hi⟩ := hcov _ hmem
    exact ⟨i, x, y, hxy, heq, (SimpleGraph.mem_edgeSet (M i)).mp hi⟩
  -- Choose, for each edge, one of the matchings containing it.
  let col : 𝓖 → Fin k := fun e => (hex e).choose
  have hspec : ∀ e : 𝓖, ∃ u v : Fin n, u ≠ v ∧ (e : Set (Fin n)) = {u, v} ∧
      (M (col e)).Adj u v := fun e => (hex e).choose_spec
  refine ⟨{ labels := col, isColoring := ?_ }⟩
  intro e₁ e₂ hne hnon hcol
  obtain ⟨u₁, v₁, -, he₁, ha₁⟩ := hspec e₁
  obtain ⟨u₂, v₂, -, he₂, ha₂⟩ := hspec e₂
  rw [← hcol] at ha₂
  -- A common vertex `x` of the two hyperedges.
  obtain ⟨x, hx₁, hx₂⟩ := hnon
  have hx₁' : x ∈ s(u₁, v₁) := by
    rw [he₁] at hx₁
    simpa using hx₁
  have hx₂' : x ∈ s(u₂, v₂) := by
    rw [he₂] at hx₂
    simpa using hx₂
  -- The two graph edges through `x` come from the same matching, so they are equal,
  -- hence the hyperedges are equal.
  have hAdj₁ : (M (col e₁)).Adj x (Sym2.Mem.other hx₁') := by
    have h1 : s(x, Sym2.Mem.other hx₁') ∈ (M (col e₁)).edgeSet := by
      rw [Sym2.other_spec hx₁']
      exact (SimpleGraph.mem_edgeSet (M (col e₁))).mpr ha₁
    exact (SimpleGraph.mem_edgeSet (M (col e₁))).mp h1
  have hAdj₂ : (M (col e₁)).Adj x (Sym2.Mem.other hx₂') := by
    have h1 : s(x, Sym2.Mem.other hx₂') ∈ (M (col e₁)).edgeSet := by
      rw [Sym2.other_spec hx₂']
      exact (SimpleGraph.mem_edgeSet (M (col e₁))).mpr ha₂
    exact (SimpleGraph.mem_edgeSet (M (col e₁))).mp h1
  have hy : Sym2.Mem.other hx₁' = Sym2.Mem.other hx₂' := hmatch (col e₁) x _ _ hAdj₁ hAdj₂
  exact hne (Subtype.ext (by
    rw [he₁, he₂]
    have hsym : s(u₁, v₁) = s(u₂, v₂) := by
      rw [← Sym2.other_spec hx₁', ← Sym2.other_spec hx₂', hy]
    have hcoe := congrArg (fun z : Sym2 (Fin n) => (z : Set (Fin n))) hsym
    simpa using hcoe))

end Work.Deep.GKO
