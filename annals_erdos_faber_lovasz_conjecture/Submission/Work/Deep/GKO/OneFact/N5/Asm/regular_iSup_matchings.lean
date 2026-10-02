import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.OneFactDefs

namespace Work.Deep.GKO.OneFact.N5.Asm

/-- **The edge-disjoint union of `c` perfect matchings is `c`-regular and `1`-factorized.**

If `P 0, …, P (c-1)` are pairwise edge-disjoint perfect matchings of `G`, then their union
`⨆ i, P i` (the graph whose adjacencies are the union of the adjacencies of the `P i`) is a
subgraph of `G`, is `c`-regular, and is 1-factorized by the `P i` themselves.

The regularity is because the unique partner of a vertex `v` in each `P i` is a *distinct*
neighbour of `v` in the union: two factors giving the same partner would share the edge `s(v,w)`.
The factorization is immediate from `edgeSet_iSup`, since every edge of the union lies in some
factor. -/
theorem regular_iSup_matchings {n c : ℕ} {G : SimpleGraph (Fin n)}
    (P : Fin c → SimpleGraph (Fin n))
    (hP : ∀ i, Work.Deep.GKO.IsPerfectMatching' G (P i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (P i).edgeSet (P j).edgeSet) :
    Work.Deep.GKO.IsRegularOf (⨆ i, P i) c ∧ (⨆ i, P i) ≤ G ∧
      Work.Deep.GKO.HasOneFactorization (⨆ i, P i) c := by
  classical
  -- The family `P` itself 1-factorizes the union.
  have hOF : Work.Deep.GKO.HasOneFactorization (⨆ i, P i) c := by
    refine ⟨P, ?_, ?_, ?_⟩
    · intro i
      exact ⟨le_iSup P i, (hP i).2⟩
    · exact hdisj
    · intro e he
      rw [SimpleGraph.edgeSet_iSup, Set.mem_iUnion] at he
      exact he
  refine ⟨?_, ?_, hOF⟩
  · -- Each factor contributes exactly one neighbour of `v`, and the contributions are distinct.
    intro v
    have hcard : ∀ i : Fin c, ((P i).neighborSet v).ncard = 1 := by
      intro i
      obtain ⟨w, hw, huniq⟩ := (hP i).2 v
      refine Set.ncard_eq_one.mpr ⟨w, ?_⟩
      ext x
      exact ⟨fun hx => huniq x hx, fun hx => by rw [hx]; exact hw⟩
    have hdisjS : Pairwise (Function.onFun Disjoint fun i : Fin c => (P i).neighborSet v) := by
      intro i j hij
      show Disjoint ((P i).neighborSet v) ((P j).neighborSet v)
      rw [Set.disjoint_left]
      intro x hxi hxj
      have hmem_i : s(v, x) ∈ (P i).edgeSet := (SimpleGraph.mem_edgeSet (P i)).mpr hxi
      have hmem_j : s(v, x) ∈ (P j).edgeSet := (SimpleGraph.mem_edgeSet (P j)).mpr hxj
      exact (Set.disjoint_left.mp (hdisj i j hij)) hmem_i hmem_j
    have hunion : (⋃ i : Fin c, (P i).neighborSet v) = (⨆ i, P i).neighborSet v := by
      ext x
      simp [SimpleGraph.mem_neighborSet]
    rw [← hunion, Nat.card_coe_set_eq,
      Set.ncard_iUnion_of_finite (fun i => Set.toFinite _) hdisjS, finsum_eq_sum_of_fintype]
    rw [Finset.sum_congr rfl (fun i _ => hcard i)]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  · -- Every factor is a subgraph of `G`, hence so is their union.
    exact iSup_le fun i => (hP i).1

end Work.Deep.GKO.OneFact.N5.Asm
