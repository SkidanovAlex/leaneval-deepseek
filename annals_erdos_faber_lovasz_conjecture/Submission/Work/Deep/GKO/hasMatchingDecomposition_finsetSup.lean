import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs

/-!
# Matching decompositions of finite unions of edge-disjoint subgraphs

If the subgraphs `G' i` (`i ∈ s`) have pairwise disjoint edge sets and each `G' i` has a matching
decomposition into `k i` matchings, then the union `s.sup G'` has a matching decomposition into
`∑ i ∈ s, k i` matchings: we simply lay the decompositions of the parts side by side, indexing the
`∑ i ∈ s, k i` matchings by the disjoint union `s.sigma (fun i => Fin (k i))` of the index sets
(transported along the canonical bijection with `Fin (∑ i ∈ s, k i)`).

This is used at the end of the reduction, to combine the two-colour decompositions of the removed
spanning linear forests with the `r` matchings of the regular remainder.

## Implementation notes

* Adjacency of `s.sup G'` (and edge-set membership) is unfolded by induction on the finset, using
  `Finset.sup_empty`, `Finset.sup_insert` and `SimpleGraph.sup_adj`.
* The matchings belonging to indices `i ∉ s` are junk (the empty graph); they are never used
  except through the (vacuous) "these matchings cover `G' i`" clause, which is stated with a
  hypothesis `i ∈ s` guarding it.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.GKO

variable {n : ℕ}

/-! ## Auxiliary lemmas -/

/-- Every adjacency of a finite supremum of graphs occurs in one of the graphs. -/
private theorem adj_finsetSup {ι : Type*} (s : Finset ι) (G' : ι → SimpleGraph (Fin n)) :
    ∀ {u v : Fin n}, (s.sup G').Adj u v → ∃ i ∈ s, (G' i).Adj u v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro u v h
      rw [Finset.sup_empty] at h
      exact absurd h (SimpleGraph.bot_adj u v).mp
  | insert a s ha ih =>
      intro u v h
      rw [Finset.sup_insert] at h
      rcases (SimpleGraph.sup_adj (G' a) (s.sup G') u v).mp h with h | h
      · exact ⟨a, Finset.mem_insert_self a s, h⟩
      · obtain ⟨i, hi, h'⟩ := ih h
        exact ⟨i, Finset.mem_insert_of_mem hi, h'⟩

/-- Every edge of a finite supremum of graphs occurs in one of the graphs. -/
private theorem mem_edgeSet_finsetSup {ι : Type*} (s : Finset ι) (G' : ι → SimpleGraph (Fin n))
    {f : Sym2 (Fin n)} (hf : f ∈ (s.sup G').edgeSet) : ∃ i ∈ s, f ∈ (G' i).edgeSet := by
  induction f using Sym2.ind with
  | _ u v =>
      obtain ⟨i, hi, hadj⟩ := adj_finsetSup s G'
        ((SimpleGraph.mem_edgeSet (G := s.sup G') (v := u) (w := v)).mp hf)
      exact ⟨i, hi, (SimpleGraph.mem_edgeSet (G := G' i) (v := u) (w := v)).mpr hadj⟩

/-- A family of matchings covering the edge set of `G`, indexed by an arbitrary finite type,
transports along a bijection of index types to a matching decomposition of `G`. -/
private theorem hasMatchingDecomposition_of_equiv {α : Type*} [Fintype α]
    (N : α → SimpleGraph (Fin n)) (G : SimpleGraph (Fin n)) (k : ℕ) (e : α ≃ Fin k)
    (h1 : ∀ a, IsMatching' (N a)) (h2 : ∀ a, N a ≤ G)
    (h3 : ∀ a b, a ≠ b → Disjoint (N a).edgeSet (N b).edgeSet)
    (h4 : ∀ f ∈ G.edgeSet, ∃ a, f ∈ (N a).edgeSet) :
    HasMatchingDecomposition G k := by
  refine ⟨fun i => N (e.symm i), fun i => h1 _, fun i => h2 _, ?_, ?_⟩
  · intro i j hij
    exact h3 _ _ fun h => hij (by simpa using congrArg e h)
  · intro f hf
    obtain ⟨a, ha⟩ := h4 f hf
    exact ⟨e a, by simpa using ha⟩

/-! ## The main theorem -/

/-- Matching decompositions of pairwise edge-disjoint subgraphs combine into a matching decomposition of their union: if the subgraphs `G' i` (`i ∈ s`) have pairwise disjoint edge sets and each `G' i` has a matching decomposition into `k i` matchings, then `s.sup G'` has a matching decomposition into `∑ i ∈ s, k i` matchings.

Used at the end of the reduction to combine the two-colour decompositions of the removed spanning linear forests with the `r` matchings of the regular remainder. -/
theorem hasMatchingDecomposition_finsetSup {n : ℕ} {ι : Type*} (s : Finset ι)
    (G' : ι → SimpleGraph (Fin n)) (k : ι → ℕ)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (G' i).edgeSet (G' j).edgeSet)
    (h : ∀ i ∈ s, Work.Deep.GKO.HasMatchingDecomposition (G' i) (k i)) :
    Work.Deep.GKO.HasMatchingDecomposition (s.sup G') (∑ i ∈ s, k i) := by
  classical
  -- Choose a matching decomposition of every `G' i`; for `i ∉ s` we use the empty graph.
  have key : ∀ i : ι, ∃ M : Fin (k i) → SimpleGraph (Fin n),
      (∀ j, IsMatching' (M j)) ∧ (∀ j, M j ≤ G' i) ∧
      (∀ j j', j ≠ j' → Disjoint (M j).edgeSet (M j').edgeSet) ∧
      (i ∈ s → ∀ f ∈ (G' i).edgeSet, ∃ j, f ∈ (M j).edgeSet) := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨M, hM1, hM2, hM3, hM4⟩ := h i hi
      exact ⟨M, hM1, hM2, hM3, fun _ => hM4⟩
    · refine ⟨fun _ => ⊥, ?_, fun _ => bot_le, ?_, fun hmem => absurd hmem hi⟩
      · intro j v w w' hvw _
        exact absurd hvw (SimpleGraph.bot_adj v w).mp
      · intro j j' _
        rw [SimpleGraph.edgeSet_bot]
        exact disjoint_bot_left
  choose M hM1 hM2 hM3 hM4 using key
  -- The indexing set: the disjoint union of the `Fin (k i)`, `i ∈ s`.
  let T : Finset (Σ i, Fin (k i)) := s.sigma fun i => (Finset.univ : Finset (Fin (k i)))
  have hT : ∀ (i : ι) (j : Fin (k i)), (⟨i, j⟩ : Σ i, Fin (k i)) ∈ T ↔ i ∈ s := by
    intro i j
    rw [show T = s.sigma (fun i => (Finset.univ : Finset (Fin (k i)))) from rfl,
      Finset.mem_sigma]
    simp
  have hcard : T.card = ∑ i ∈ s, k i := by
    rw [show T = s.sigma (fun i => (Finset.univ : Finset (Fin (k i)))) from rfl,
      Finset.card_sigma]
    simp
  refine hasMatchingDecomposition_of_equiv (fun t : T => M t.1.1 t.1.2) (s.sup G')
    (∑ i ∈ s, k i) (T.equivFinOfCardEq hcard) ?_ ?_ ?_ ?_
  · intro t
    exact hM1 t.1.1 t.1.2
  · intro t
    exact (hM2 t.1.1 t.1.2).trans (Finset.le_sup ((hT t.1.1 t.1.2).mp t.2))
  · intro t₁ t₂ htne
    obtain ⟨⟨i, j⟩, ht₁⟩ := t₁
    obtain ⟨⟨i', j'⟩, ht₂⟩ := t₂
    have hi : i ∈ s := (hT i j).mp ht₁
    have hi' : i' ∈ s := (hT i' j').mp ht₂
    by_cases hii : i = i'
    · subst hii
      have hne : j ≠ j' := by
        intro hjj
        subst hjj
        exact htne (Subtype.ext rfl)
      exact hM3 i j j' hne
    · refine Disjoint.mono (SimpleGraph.edgeSet_mono (hM2 i j))
        (SimpleGraph.edgeSet_mono (hM2 i' j')) (hdisj i hi i' hi' hii)
  · intro f hf
    obtain ⟨i, hi, hfi⟩ := mem_edgeSet_finsetSup s G' hf
    obtain ⟨j, hj⟩ := hM4 i hi f hfi
    exact ⟨⟨⟨i, j⟩, (hT i j).mpr hi⟩, hj⟩

end Work.Deep.GKO
