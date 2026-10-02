import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.OneFact.N5.Basic

namespace Work.Deep.GKO.OneFact.N5

/-- Degree loss of the deletion: after removing the edges used by `P`, and forbidding the vertex
set `F`, every vertex keeps at least `D₀ - (m+L) - |F|` available neighbours, provided it had `D₀`
neighbours in `K` and the deletion removed at most `m + L` neighbours at every vertex (the
`usedNbrs` bound).  This is the `hdeg` hypothesis of the completion step, with
`D := D₀ - (m+L) - |F|`. -/
theorem degInRemainingNeighbors {n : ℕ} (K : SimpleGraph (Fin n)) {c : ℕ}
    (P : Fin c → SimpleGraph (Fin n)) (F : Finset (Fin n)) {D₀ m L : ℕ}
    (hdeg : ∀ v, D₀ ≤ Nat.card (K.neighborSet v))
    (hused : ∀ v, (Work.Deep.GKO.OneFact.N5.usedNbrs K P v).card ≤ m + L) :
    ∀ v, D₀ - (m + L) - F.card ≤ Work.Deep.GKO.degIn (Work.Deep.GKO.OneFact.N5.remaining K P) v
      (Finset.univ \ F) := by
  intro v
  classical
  -- `A` is the set of `K`-neighbours of `v`, `U` the neighbours of `v` in `K` already used by `P`.
  set A : Finset (Fin n) := Finset.univ.filter (fun w => K.Adj v w) with hAdef
  set U : Finset (Fin n) := usedNbrs K P v with hUdef
  -- The neighbours of `v` in `K` that survive the deletion and the forbidden set `F` are exactly
  -- `A \ (U ∪ F)`, and they are neighbours in `remaining K P` inside `univ \ F`.
  have hsub2 : A \ (U ∪ F) ⊆ (Finset.univ \ F).filter (fun w => (remaining K P).Adj v w) := by
    intro w hw
    rw [Finset.mem_sdiff] at hw
    obtain ⟨hwA, hwUF⟩ := hw
    rw [Finset.mem_union, not_or] at hwUF
    obtain ⟨hwU, hwF⟩ := hwUF
    rw [Finset.mem_filter, Finset.mem_sdiff]
    refine ⟨⟨Finset.mem_univ _, hwF⟩, ?_⟩
    have hKw : K.Adj v w := by
      rw [hAdef] at hwA
      exact (Finset.mem_filter.mp hwA).2
    have hne : ¬ ∃ i : Fin c, (P i).Adj v w := by
      intro h
      refine hwU ?_
      rw [hUdef]
      obtain ⟨i, hi⟩ := h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hKw, i, hi⟩
    rw [remaining_adj]
    exact ⟨hKw, by rw [mem_usedEdges]; exact hne⟩
  have hstep : (A \ (U ∪ F)).card ≤ degIn (remaining K P) v (Finset.univ \ F) := by
    show (A \ (U ∪ F)).card ≤ ((Finset.univ \ F).filter (fun w => (remaining K P).Adj v w)).card
    exact Finset.card_le_card hsub2
  -- `D₀` bounds the size of `A`.
  have hD0 : D₀ ≤ A.card := by
    have hsub : K.neighborSet v ⊆ (A : Set (Fin n)) := by
      intro w hw
      rw [SimpleGraph.mem_neighborSet] at hw
      show w ∈ A
      rw [hAdef]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
    calc D₀ ≤ Nat.card (K.neighborSet v) := hdeg v
      _ ≤ Nat.card (A : Set (Fin n)) := Nat.card_mono A.finite_toSet hsub
      _ = A.card := by rw [Nat.card_coe_set_eq]; simp [Set.ncard_def]
  -- The deleted neighbours and the forbidden vertices together number at most `(m+L) + |F|`.
  have hUcard : (U ∪ F).card ≤ (m + L) + F.card := by
    calc (U ∪ F).card ≤ U.card + F.card := Finset.card_union_le U F
      _ ≤ (m + L) + F.card := Nat.add_le_add_right (by rw [hUdef]; exact hused v) F.card
  have h2 : A.card - ((m + L) + F.card) ≤ (A \ (U ∪ F)).card := by
    rw [Finset.card_sdiff]
    calc A.card - ((m + L) + F.card) ≤ A.card - (U ∪ F).card := Nat.sub_le_sub_left hUcard A.card
      _ ≤ A.card - ((U ∪ F) ∩ A).card :=
          Nat.sub_le_sub_left (Finset.card_le_card (Finset.inter_subset_left)) A.card
  calc D₀ - (m + L) - F.card
      = D₀ - ((m + L) + F.card) := by rw [Nat.sub_sub]
    _ ≤ A.card - ((m + L) + F.card) := Nat.sub_le_sub_right hD0 _
    _ ≤ (A \ (U ∪ F)).card := h2
    _ ≤ degIn (remaining K P) v (Finset.univ \ F) := hstep

end Work.Deep.GKO.OneFact.N5
