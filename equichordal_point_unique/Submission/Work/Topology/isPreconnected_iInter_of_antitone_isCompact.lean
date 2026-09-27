import Mathlib

namespace Work.Topology

/-- The intersection of a decreasing sequence of compact preconnected sets in a compact
Hausdorff space is preconnected. -/
theorem isPreconnected_iInter_of_antitone_isCompact {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {K : ℕ → Set X} (hmono : Antitone K) (hcpt : ∀ n, IsCompact (K n))
    (hpre : ∀ n, IsPreconnected (K n)) : IsPreconnected (⋂ n, K n) := by
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro u v hu hv huv huvdisj
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hu_not, hv_not⟩ := hcon
  obtain ⟨x, hxK, hxu⟩ := Set.not_subset.mp hu_not
  obtain ⟨y, hyK, hyv⟩ := Set.not_subset.mp hv_not
  have hxv : x ∈ v := (huv hxK).resolve_left hxu
  have hyu : y ∈ u := (huv hyK).resolve_right hyv
  have hKclosed : IsClosed (⋂ n, K n) := isClosed_iInter fun n => (hcpt n).isClosed
  have hAclosed : IsClosed ((⋂ n, K n) ∩ u) := hKclosed.inter hu
  have hBclosed : IsClosed ((⋂ n, K n) ∩ v) := hKclosed.inter hv
  have hAne : ((⋂ n, K n) ∩ u).Nonempty := ⟨y, hyK, hyu⟩
  have hBne : ((⋂ n, K n) ∩ v).Nonempty := ⟨x, hxK, hxv⟩
  have hABdisj : Disjoint ((⋂ n, K n) ∩ u) ((⋂ n, K n) ∩ v) := by
    rw [Set.disjoint_left]
    intro z hzA hzB
    have hz : z ∈ (⋂ n, K n) ∩ (u ∩ v) := ⟨hzA.1, hzA.2, hzB.2⟩
    rw [huvdisj] at hz
    exact hz
  obtain ⟨WA, WB, hWAo, hWBo, hAW, hBW, hWdisj⟩ :=
    SeparatedNhds.of_isCompact_isCompact hAclosed.isCompact hBclosed.isCompact hABdisj
  have hKW : (⋂ n, K n) ⊆ WA ∪ WB := by
    intro z hz
    rcases (huv hz) with hzu | hzv
    · exact Or.inl (hAW ⟨hz, hzu⟩)
    · exact Or.inr (hBW ⟨hz, hzv⟩)
  let C : Set X := (WA ∪ WB)ᶜ
  have hCclosed : IsClosed C := (hWAo.union hWBo).isClosed_compl
  have htclosed : ∀ n, IsClosed (K n ∩ C) := fun n => (hcpt n).isClosed.inter hCclosed
  have hex : ∃ n, K n ∩ C = ∅ := by
    by_contra hc
    have hne : ∀ n, (K n ∩ C).Nonempty := fun n =>
      Set.nonempty_iff_ne_empty.mpr fun h => hc ⟨n, h⟩
    have htd : ∀ i, K (i + 1) ∩ C ⊆ K i ∩ C :=
      fun i => Set.inter_subset_inter (hmono (Nat.le_succ i)) (fun _ h => h)
    have h0 : IsCompact (K 0 ∩ C) := (hcpt 0).of_isClosed_subset (htclosed 0) Set.inter_subset_left
    obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (fun n => K n ∩ C) htd hne h0 htclosed
    have hzK : z ∈ ⋂ n, K n := Set.mem_iInter.mpr fun n => (Set.mem_iInter.mp hz n).1
    have hzC : z ∈ C := (Set.mem_iInter.mp hz 0).2
    exact hzC (hKW hzK)
  obtain ⟨n, hn⟩ := hex
  have hKn : K n ⊆ WA ∪ WB := by
    intro z hz
    by_contra hzc
    have hzC : z ∈ C := hzc
    have hzmem : z ∈ K n ∩ C := ⟨hz, hzC⟩
    rw [hn] at hzmem
    exact hzmem
  have hdisjK : K n ∩ (WA ∩ WB) = ∅ := by
    simp [Set.disjoint_iff_inter_eq_empty.mp hWdisj]
  rcases (isPreconnected_iff_subset_of_disjoint.mp (hpre n)) WA WB hWAo hWBo hKn hdisjK with
    hsubWA | hsubWB
  · obtain ⟨b, hbB⟩ := hBne
    exact (Set.disjoint_left.mp hWdisj (hsubWA (Set.iInter_subset K n hbB.1))) (hBW hbB)
  · obtain ⟨a, haA⟩ := hAne
    exact (Set.disjoint_left.mp hWdisj (hAW haA)) (hsubWB (Set.iInter_subset K n haA.1))

end Work.Topology
