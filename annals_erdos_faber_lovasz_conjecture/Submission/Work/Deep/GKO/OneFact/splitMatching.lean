import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs

namespace Work.Deep.GKO.OneFact

open scoped Sym2

/-- For a set `T` of edges of `M`, the edge set of `fromEdgeSet T` is `T` (all the edges
involved are genuine two-element edges). -/
private lemma edgeSet_fromEdgeSet_of_subset {n : ℕ} {M : SimpleGraph (Fin n)}
    {T : Set (Sym2 (Fin n))} (hT : T ⊆ M.edgeSet) :
    (SimpleGraph.fromEdgeSet T).edgeSet = T := by
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  exact Set.eq_of_subset_of_subset Set.sdiff_subset fun z hz =>
    ⟨hz, by
      rw [Sym2.mem_diagSet]
      exact SimpleGraph.not_isDiag_of_mem_edgeSet (G := M) (hT hz)⟩

/-- A matching is the disjoint union of sub-matchings with any prescribed sizes. -/
theorem splitMatching {n : ℕ} {ι : Type*} [Fintype ι] (M : SimpleGraph (Fin n))
    (hM : Work.Deep.GKO.IsMatching' M) (ν : ι → ℕ)
    (hsum : ∑ i, ν i = Nat.card M.edgeSet) :
    ∃ M' : ι → SimpleGraph (Fin n),
      (∀ i, Work.Deep.GKO.IsMatching' (M' i)) ∧
      (∀ i, M' i ≤ M) ∧
      (∀ i j, i ≠ j → Disjoint (M' i).edgeSet (M' j).edgeSet) ∧
      (∀ e ∈ M.edgeSet, ∃ i, e ∈ (M' i).edgeSet) ∧
      (∀ i, Nat.card (M' i).edgeSet = ν i) := by
  classical
  -- Index the edges of `M` by the pairs `(i, a)` with `a < ν i`: the prescribed sizes
  -- give a type of the same cardinality as `M.edgeSet`.
  have hcard : Fintype.card (Σ i : ι, Fin (ν i)) = Fintype.card ↥M.edgeSet := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [← Nat.card_eq_fintype_card]
    exact hsum
  let w : (Σ i : ι, Fin (ν i)) ≃ ↥M.edgeSet := Fintype.equivOfCardEq hcard
  -- `A i` is the set of the `ν i` edges indexed by the pairs with first coordinate `i`.
  let A : ι → Finset (Sym2 (Fin n)) := fun i =>
    (Finset.univ : Finset (Fin (ν i))).image (fun a => (w ⟨i, a⟩ : Sym2 (Fin n)))
  have hA_sub : ∀ i, (↑(A i) : Set (Sym2 (Fin n))) ⊆ M.edgeSet := by
    intro i x hx
    rw [Finset.mem_coe] at hx
    change x ∈ (Finset.univ : Finset (Fin (ν i))).image
      (fun a => (w ⟨i, a⟩ : Sym2 (Fin n))) at hx
    rw [Finset.mem_image] at hx
    obtain ⟨a, -, rfl⟩ := hx
    exact (w ⟨i, a⟩).2
  have hA_card : ∀ i, (A i).card = ν i := by
    intro i
    change ((Finset.univ : Finset (Fin (ν i))).image
      (fun a => (w ⟨i, a⟩ : Sym2 (Fin n)))).card = ν i
    rw [Finset.card_image_of_injective]
    · simp
    · intro a b hab
      have h1 : (⟨i, a⟩ : Σ i : ι, Fin (ν i)) = ⟨i, b⟩ :=
        w.injective (Subtype.ext hab)
      exact Fin.ext (congrArg (fun s : (Σ i : ι, Fin (ν i)) => s.2.val) h1)
  have hA_disj : ∀ i j, i ≠ j → Disjoint (A i) (A j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hx hx'
    change x ∈ (Finset.univ : Finset (Fin (ν i))).image
      (fun a => (w ⟨i, a⟩ : Sym2 (Fin n))) at hx
    change x ∈ (Finset.univ : Finset (Fin (ν j))).image
      (fun a => (w ⟨j, a⟩ : Sym2 (Fin n))) at hx'
    rw [Finset.mem_image] at hx hx'
    obtain ⟨a, -, ha⟩ := hx
    obtain ⟨b, -, hb⟩ := hx'
    have h1 : (w ⟨i, a⟩ : Sym2 (Fin n)) = (w ⟨j, b⟩ : Sym2 (Fin n)) := by rw [ha, hb]
    have h2 : (⟨i, a⟩ : Σ i : ι, Fin (ν i)) = ⟨j, b⟩ := w.injective (Subtype.ext h1)
    have h3 : i = j := congrArg (fun s : (Σ i : ι, Fin (ν i)) => s.1) h2
    exact hij h3
  refine ⟨fun i => SimpleGraph.fromEdgeSet (↑(A i) : Set (Sym2 (Fin n))), ?_, ?_, ?_, ?_, ?_⟩
  · -- each part is a matching, being a subgraph of `M`
    intro i
    have hle : SimpleGraph.fromEdgeSet (↑(A i) : Set (Sym2 (Fin n))) ≤ M :=
      (SimpleGraph.fromEdgeSet_le M).mpr (Set.Subset.trans Set.sdiff_subset (hA_sub i))
    intro v x y hx hy
    exact hM v x y (hle hx) (hle hy)
  · intro i
    exact (SimpleGraph.fromEdgeSet_le M).mpr (Set.Subset.trans Set.sdiff_subset (hA_sub i))
  · intro i j hij
    rw [edgeSet_fromEdgeSet_of_subset (hA_sub i), edgeSet_fromEdgeSet_of_subset (hA_sub j)]
    exact Finset.disjoint_coe.mpr (hA_disj i j hij)
  · -- every edge of `M` lies in the part indexed by the first coordinate of its index
    intro x hx
    let s : Σ i : ι, Fin (ν i) := w.symm ⟨x, hx⟩
    refine ⟨s.1, ?_⟩
    rw [edgeSet_fromEdgeSet_of_subset (hA_sub s.1)]
    have hs : w s = ⟨x, hx⟩ := Equiv.apply_symm_apply w ⟨x, hx⟩
    have hw : (w s : Sym2 (Fin n)) = x := congrArg Subtype.val hs
    rw [← hw]
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨s.2, Finset.mem_univ _, rfl⟩)
  · intro i
    rw [edgeSet_fromEdgeSet_of_subset (hA_sub i)]
    simpa using hA_card i

end Work.Deep.GKO.OneFact
