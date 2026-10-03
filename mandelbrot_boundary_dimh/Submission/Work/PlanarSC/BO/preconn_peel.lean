import Mathlib

namespace Work.PlanarSC.BO

/-- Auxiliary separator argument: if `S = e ∪ R` is preconnected, `e, R` are closed, `e ∩ R = {p}`,
and `R` is contained in the union of two closed sets `B, C` with `R ∩ B ∩ C = ∅`, and the glue point
`p` lies in `B`, then `R` is contained in `B` or in `C`. -/
private lemma peel {X : Type*} [TopologicalSpace X] {S e R B C : Set X} {p : X}
    (he : IsClosed e) (hR : IsClosed R) (hB : IsClosed B) (hC : IsClosed C)
    (hcover : S = e ∪ R) (hS : IsPreconnected S) (hmeet : e ∩ R = {p})
    (hsub : R ⊆ B ∪ C) (hdisj : R ∩ (B ∩ C) = ∅) (hpB : p ∈ B) :
    R ⊆ B ∨ R ⊆ C := by
  have hp_mem : p ∈ e ∩ R := by rw [hmeet]; exact Set.mem_singleton p
  rw [isPreconnected_iff_subset_of_disjoint_closed] at hS
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hnB, hnC⟩ := hcon
  have hAclosed : IsClosed (e ∪ (R ∩ B)) := he.union (hR.inter hB)
  have hDclosed : IsClosed (R ∩ C) := hR.inter hC
  have hcover' : S ⊆ (e ∪ (R ∩ B)) ∪ (R ∩ C) := by
    intro x hx
    have hx' : x ∈ e ∪ R := by rw [hcover] at hx; exact hx
    rcases hx' with hxe | hxR
    · exact Or.inl (Or.inl hxe)
    · rcases hsub hxR with hxB | hxC
      · exact Or.inl (Or.inr ⟨hxR, hxB⟩)
      · exact Or.inr ⟨hxR, hxC⟩
  have hdisj' : S ∩ ((e ∪ (R ∩ B)) ∩ (R ∩ C)) = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨x, -, hxA, hxD⟩
    rcases hxA with hxe | ⟨hxR, hxB⟩
    · have hxeR : x ∈ e ∩ R := ⟨hxe, hxD.1⟩
      rw [hmeet] at hxeR
      have hxp : x = p := Set.mem_singleton_iff.mp hxeR
      rw [hxp] at hxD
      have hmem : p ∈ R ∩ (B ∩ C) := ⟨hxD.1, hpB, hxD.2⟩
      rw [hdisj] at hmem
      exact hmem
    · have hmem : x ∈ R ∩ (B ∩ C) := ⟨hxR, hxB, hxD.2⟩
      rw [hdisj] at hmem
      exact hmem
  rcases hS (e ∪ (R ∩ B)) (R ∩ C) hAclosed hDclosed hcover' hdisj' with hA | hD
  · refine absurd ?_ hnB
    intro x hxR
    have hxS : x ∈ S := by rw [hcover]; exact Or.inr hxR
    rcases hA hxS with hxe | ⟨-, hxB⟩
    · have hxeR : x ∈ e ∩ R := ⟨hxe, hxR⟩
      rw [hmeet] at hxeR
      rw [Set.mem_singleton_iff.mp hxeR]
      exact hpB
    · exact hxB
  · exact absurd (fun x hxR => (hD (by rw [hcover]; exact Or.inr hxR)).2) hnC

/-- Put this in `Submission/Work/PlanarSC/BO/preconn_peel.lean`, with import `Mathlib`, inside
`namespace Work.PlanarSC.BO`.

Topological lemma (used to inherit preconnectedness when peeling one segment off a union of
segments): if `S = e ∪ R` with `e` and `R` closed, `S` preconnected and `e ∩ R` a single point, then
`R` is preconnected.  Route: if `R` were not preconnected, take nonempty closed `B, C` with
`R ⊆ B ∪ C`, `R ∩ B ∩ C = ∅` and points of `R` outside `B` and outside `C` (from
`isPreconnected_iff_subset_of_disjoint_closed`).  The point `p` of `e ∩ R` lies in `B` or in `C`,
say `B`; the correct repair is to use `e ∪ (R ∩ B)` and `R ∩ C` as the two pieces: both are closed
(`hR` promotes `R ∩ B` to closed), both nonempty (`p ∈ e ∪ (R ∩ B)`; `R ⊄ C`), disjoint
(`e ∩ R ⊆ {p} ⊆ R ∩ B`, and `R ∩ B ∩ C = ∅`), and they cover `S`.  Then
`isPreconnected_iff_subset_of_disjoint_closed` applied to `hS` contradicts the nonemptiness of the
pieces. -/
theorem preconn_peel {X : Type*} [TopologicalSpace X]
    {S e R : Set X} {p : X} (he : IsClosed e) (hR : IsClosed R) (hcover : S = e ∪ R)
    (hS : IsPreconnected S) (hmeet : e ∩ R = {p}) : IsPreconnected R := by
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro B C hB hC hRB hRBC
  by_cases hpB : p ∈ B
  · exact peel he hR hB hC hcover hS hmeet hRB hRBC hpB
  · have hp_mem : p ∈ e ∩ R := by rw [hmeet]; exact Set.mem_singleton p
    have hpC : p ∈ C := by
      rcases hRB hp_mem.2 with h | h
      · exact absurd h hpB
      · exact h
    have hsub' : R ⊆ C ∪ B := by rw [Set.union_comm]; exact hRB
    have hdisj' : R ∩ (C ∩ B) = ∅ := by rw [Set.inter_comm C B]; exact hRBC
    rcases peel he hR hC hB hcover hS hmeet hsub' hdisj' hpC with h | h
    · exact Or.inr h
    · exact Or.inl h

end Work.PlanarSC.BO
