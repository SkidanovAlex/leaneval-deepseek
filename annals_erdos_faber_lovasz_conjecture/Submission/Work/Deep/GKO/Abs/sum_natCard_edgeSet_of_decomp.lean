import Submission.Work.Deep.GKO.NarrowImports

namespace Work.Deep.GKO.Abs

/-- The edge set of a graph decomposed into pairwise edge-disjoint subgraphs: the sum of the
numbers of edges of the parts is the number of edges of the whole.  (`hsub` gives one inclusion
of edge sets, `hcov` the other, and `hdisj` makes the counting additive; finite unions of the
`toFinset`s, or `Set.ncard_iUnion` together with `tsum_fintype`, are both viable routes.) -/
theorem sum_natCard_edgeSet_of_decomp {n : ℕ} {ι : Type*} [Fintype ι] {G : SimpleGraph (Fin n)}
    (P : ι → SimpleGraph (Fin n))
    (hsub : ∀ i, P i ≤ G)
    (hdisj : ∀ i j : ι, i ≠ j → Disjoint (P i).edgeSet (P j).edgeSet)
    (hcov : ∀ e ∈ G.edgeSet, ∃ i, e ∈ (P i).edgeSet) :
    ∑ i, Nat.card (P i).edgeSet = Nat.card G.edgeSet := by
  classical
  -- The parts cover `G` exactly.
  have hunion : (⋃ i, (P i).edgeSet) = G.edgeSet := by
    apply Set.Subset.antisymm
    · intro e he
      rcases Set.mem_iUnion.mp he with ⟨i, hi⟩
      exact SimpleGraph.edgeSet_mono (hsub i) hi
    · intro e he
      rcases hcov e he with ⟨i, hi⟩
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
  -- Disjointness makes the counting additive.
  have hadd : (⋃ i, (P i).edgeSet).ncard = ∑ i, ((P i).edgeSet).ncard := by
    rw [Set.ncard_iUnion_of_finite (fun i => Set.toFinite ((P i).edgeSet))
      (fun i j hij => hdisj i j hij)]
    exact finsum_eq_sum_of_fintype _
  calc ∑ i, Nat.card (P i).edgeSet
      = ∑ i, ((P i).edgeSet).ncard :=
        Finset.sum_congr rfl fun i _ => Nat.card_coe_set_eq ((P i).edgeSet)
    _ = (⋃ i, (P i).edgeSet).ncard := hadd.symm
    _ = G.edgeSet.ncard := by rw [hunion]
    _ = Nat.card G.edgeSet := (Nat.card_coe_set_eq G.edgeSet).symm

end Work.Deep.GKO.Abs
