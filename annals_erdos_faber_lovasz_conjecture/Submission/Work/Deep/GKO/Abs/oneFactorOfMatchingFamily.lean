import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs
import Submission.Work.Deep.GKO.RegVocab
import Submission.Work.KOApproxHam.exists_oneFactorization_of_regular_bipartite

set_option linter.unusedVariables false

namespace Work.Deep.GKO.Abs

open Work.Deep.GKO

variable {n : ℕ}

/-- If every neighbour of `v` in `N` lies in `S` and `v` has exactly one `N`-neighbour in `S`,
then `v` has a unique `N`-neighbour. -/
lemma existsUnique_adj_of_degIn_eq_one {N : SimpleGraph (Fin n)} {S : Finset (Fin n)} {v : Fin n}
    (hout : ∀ w : Fin n, N.Adj v w → w ∈ S) (hdeg : degIn N v S = 1) :
    ∃! w : Fin n, N.Adj v w := by
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hdeg
  have hu' : u ∈ nbrFinset N v S := by rw [hu]; exact Finset.mem_singleton_self u
  refine ⟨u, (mem_nbrFinset.mp hu').2, fun y hy => ?_⟩
  have hy' : y ∈ nbrFinset N v S := mem_nbrFinset.mpr ⟨hout y hy, hy⟩
  rw [hu, Finset.mem_singleton] at hy'
  exact hy'

/-- Every neighbour in a subgraph of a graph whose edges run between `A` and `B` lies on the
opposite side. -/
lemma nbr_subset_of_bip {R N : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    (hNR : N ≤ R) (hAB : Disjoint A B)
    (hbip : ∀ u v : Fin n, R.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A))
    {v : Fin n} (hv : v ∈ A) : ∀ w : Fin n, N.Adj v w → w ∈ B := by
  intro w hw
  rcases hbip v w (hNR hw) with ⟨-, h⟩ | ⟨hvb, -⟩
  · exact h
  · exact (Finset.disjoint_left.mp hAB hv hvb).elim

/-- Gluing an explicit family of pairwise edge-disjoint perfect matchings with the
one-factorization of the bipartite remainder.  If `M : Fin c → ...` are pairwise edge-disjoint
perfect matchings of `G`, and `R` is the complement of their union in `G`, is `k - c`-regular and
has all its edges between the complementary parts `A`, `B` (which are disjoint, cover everything
and have equal size), then `G` has a one-factorization with `k` factors.

The regular bipartite input is
`Submission.Work.KOApproxHam.exists_oneFactorization_of_regular_bipartite`; the case `c = k`
leaves `R` edgeless. -/
theorem oneFactorOfMatchingFamily {n k c : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n))
    (hAB : Disjoint A B) (hcov : A ∪ B = Finset.univ) (hcard : A.card = B.card)
    (M : Fin c → SimpleGraph (Fin n)) (R : SimpleGraph (Fin n))
    (hperf : ∀ j, Work.Deep.GKO.IsPerfectMatching' G (M j))
    (hdisjM : ∀ i j : Fin c, i ≠ j → Disjoint (M i).edgeSet (M j).edgeSet)
    (hR : ∀ e : Sym2 (Fin n), e ∈ R.edgeSet ↔ e ∈ G.edgeSet ∧ ∀ j, e ∉ (M j).edgeSet)
    (hbipR : ∀ u v : Fin n, R.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A))
    (hregR : ∀ v : Fin n, Nat.card (R.neighborSet v) = k - c)
    (hck : c ≤ k) :
    Work.Deep.GKO.HasOneFactorization G k := by
  classical
  -- `R` is a subgraph of `G`, being the complement of the matchings inside it.
  have hRG : R ≤ G := by
    intro u v huv
    exact (SimpleGraph.mem_edgeSet G).mp
      ((hR s(u, v)).mp ((SimpleGraph.mem_edgeSet R).mpr huv)).1
  -- the degrees of `R` into the opposite part
  have hdegA : ∀ v ∈ A, degIn R v B = k - c := by
    intro v hv
    rw [degIn_eq_ncard]
    have hsub : R.neighborSet v ⊆ (B : Set (Fin n)) := by
      intro w hw
      rcases hbipR v w hw with ⟨-, h⟩ | ⟨hvb, -⟩
      · exact h
      · exact (Finset.disjoint_left.mp hAB hv hvb).elim
    rw [Set.inter_eq_self_of_subset_left hsub, ← Nat.card_coe_set_eq]
    exact hregR v
  have hdegB : ∀ v ∈ B, degIn R v A = k - c := by
    intro v hv
    rw [degIn_eq_ncard]
    have hsub : R.neighborSet v ⊆ (A : Set (Fin n)) := by
      intro w hw
      rcases hbipR v w hw with ⟨hvb, -⟩ | ⟨-, h⟩
      · exact (Finset.disjoint_left.mp hAB hvb hv).elim
      · exact h
    rw [Set.inter_eq_self_of_subset_left hsub, ← Nat.card_coe_set_eq]
    exact hregR v
  -- in the degenerate case `k = c` the remainder `R` is edgeless
  have hnoedge : k - c = 0 → ∀ u v : Fin n, ¬ R.Adj u v := by
    intro hkc u v huv
    have hnc : (R.neighborSet u).ncard = 0 := by
      rw [← Nat.card_coe_set_eq, hregR u, hkc]
    have hne : (R.neighborSet u).Nonempty :=
      ⟨v, (SimpleGraph.mem_neighborSet R u v).mpr huv⟩
    exact absurd ((Set.ncard_pos (Set.toFinite _)).mpr hne) (by rw [hnc]; exact Nat.lt_irrefl 0)
  -- the one-factorization of the bipartite remainder
  have hNexists : ∃ N : Fin (k - c) → SimpleGraph (Fin n),
      (∀ j, N j ≤ R) ∧
      (∀ j, ∀ v ∈ A, degIn (N j) v B = 1) ∧
      (∀ j, ∀ v ∈ B, degIn (N j) v A = 1) ∧
      (∀ i j : Fin (k - c), i ≠ j → Disjoint (N i).edgeSet (N j).edgeSet) ∧
      (∀ v ∈ A, ∀ w ∈ B, R.Adj v w → ∃ j, (N j).Adj v w) := by
    rcases Nat.eq_zero_or_pos (k - c) with h0 | hpos
    · exact ⟨fun j : Fin (k - c) => (Nat.not_lt_zero j.val (h0 ▸ j.isLt)).elim,
        (fun j => (Nat.not_lt_zero j.val (h0 ▸ j.isLt)).elim),
        (fun j => (Nat.not_lt_zero j.val (h0 ▸ j.isLt)).elim),
        (fun j => (Nat.not_lt_zero j.val (h0 ▸ j.isLt)).elim),
        (fun i j _ => (Nat.not_lt_zero i.val (h0 ▸ i.isLt)).elim),
        fun v _ w _ hvw => absurd hvw (hnoedge h0 v w)⟩
    · obtain ⟨N, h1, h2, h3, h4, -, -, -, h8⟩ :=
        Work.KOApproxHam.exists_oneFactorization_of_regular_bipartite R A B hAB hpos
          hdegA hdegB
      exact ⟨N, h1, h2, h3, h4, h8⟩
  obtain ⟨N, hNle, hNdegA, hNdegB, hNdisj, hNcovAB⟩ := hNexists
  -- each `N j` is a perfect matching of `G`
  have hNperf : ∀ j : Fin (k - c), IsPerfectMatching' G (N j) := by
    intro j
    refine ⟨le_trans (hNle j) hRG, fun v => ?_⟩
    have hv : v ∈ A ∪ B := by rw [hcov]; exact Finset.mem_univ v
    rcases Finset.mem_union.mp hv with hvA | hvB
    · exact existsUnique_adj_of_degIn_eq_one
        (fun w hw => nbr_subset_of_bip (hNle j) hAB hbipR hvA w hw) (hNdegA j v hvA)
    · refine existsUnique_adj_of_degIn_eq_one ?_ (hNdegB j v hvB)
      intro w hw
      rcases hbipR v w (hNle j hw) with ⟨hvb, -⟩ | ⟨-, hwa⟩
      · exact (Finset.disjoint_left.mp hAB hvb hvB).elim
      · exact hwa
  -- the two families are edge-disjoint: `N j` lies inside the complement `R`
  have hdisjMN : ∀ i : Fin c, ∀ j : Fin (k - c), Disjoint (M i).edgeSet (N j).edgeSet := by
    intro i j
    refine Set.disjoint_left.mpr fun e heM heN => ?_
    exact ((hR e).mp (SimpleGraph.edgeSet_mono (hNle j) heN)).2 i heM
  -- the family `N` covers all edges of `R`
  have hRcover : ∀ e : Sym2 (Fin n), e ∈ R.edgeSet → ∃ j : Fin (k - c), e ∈ (N j).edgeSet := by
    intro e he
    revert he
    refine Sym2.ind (fun u v => ?_) e
    intro he
    have huv : R.Adj u v := (SimpleGraph.mem_edgeSet R).mp he
    rcases hbipR u v huv with ⟨huA, hvB⟩ | ⟨huB, hvA⟩
    · obtain ⟨j, hj⟩ := hNcovAB u huA v hvB huv
      exact ⟨j, (SimpleGraph.mem_edgeSet (N j)).mpr hj⟩
    · obtain ⟨j, hj⟩ := hNcovAB v hvA u huB ((R.adj_comm u v).mp huv)
      refine ⟨j, ?_⟩
      rw [Sym2.eq_swap]
      exact (SimpleGraph.mem_edgeSet (N j)).mpr hj
  -- assemble the `k` factors
  have hcd : c + (k - c) = k := Nat.add_sub_cancel' hck
  let e : Fin k ≃ Fin c ⊕ Fin (k - c) :=
    ((finSumFinEquiv (m := c) (n := k - c)).trans (finCongr hcd)).symm
  refine ⟨fun i => Sum.elim M N (e i), ?_, ?_, ?_⟩
  · intro i
    rcases h : e i with j | j
    · simpa [h] using hperf j
    · simpa [h] using hNperf j
  · intro i i' hii
    rcases hi : e i with j | j <;> rcases hi' : e i' with j' | j'
    · have hne : j ≠ j' := fun hh => hii (e.injective (by rw [hi, hi', hh]))
      simpa [hi, hi'] using hdisjM j j' hne
    · simpa [hi, hi'] using hdisjMN j j'
    · simpa [hi, hi'] using (hdisjMN j' j).symm
    · have hne : j ≠ j' := fun hh => hii (e.injective (by rw [hi, hi', hh]))
      simpa [hi, hi'] using hNdisj j j' hne
  · intro e0 he0
    by_cases hM : ∃ j : Fin c, e0 ∈ (M j).edgeSet
    · obtain ⟨j, hj⟩ := hM
      exact ⟨e.symm (Sum.inl j), by simp [hj]⟩
    · have hM' : ∀ j : Fin c, e0 ∉ (M j).edgeSet := fun j hj => hM ⟨j, hj⟩
      have heR : e0 ∈ R.edgeSet := (hR e0).mpr ⟨he0, fun j hj => hM' j hj⟩
      obtain ⟨j, hj⟩ := hRcover e0 heR
      exact ⟨e.symm (Sum.inr j), by simp [hj]⟩

end Work.Deep.GKO.Abs
