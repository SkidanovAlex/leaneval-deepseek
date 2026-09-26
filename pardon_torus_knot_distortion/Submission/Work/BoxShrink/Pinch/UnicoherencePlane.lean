import Mathlib
import Submission.Work.BoxShrink.Pinch.borsuk_frontier_connectedComponentIn

/-!
# Unicoherence of the plane

`Work.BoxShrink.Pinch.UnicoherencePlane`: if `ℂ = P ∪ Q` with `P`, `Q` closed and preconnected,
then `P ∩ Q` is preconnected.

The proof uses the Phragmén–Brouwer property of the plane (`Work.Spike.phragmen_brouwer_closed`),
in the form of the **Brouwer property** for closed preconnected plane sets: the frontier of a
complementary domain of a closed preconnected set is preconnected
(`frontier_preconnected_of_isClosed_isPreconnected` below, reproduced from
`Submission/Work/JordanSeparation/huntTwoComponentsHardStandalone.lean`), together with Wilder's
Theorem II 3.10 (`Work.BoxShrink.Pinch.BorsukAux.exists_preconnected_closure_inter`).

The shape of the final argument: if `K = P ∩ Q = A ⊔ B` were a separation, then Wilder's theorem
produces a complementary domain `W` of the closed preconnected set `Q` whose frontier meets both
`A` and `B`; the frontier is preconnected by the Brouwer property and lies in `K = A ∪ B`, so it
must lie in `A` or in `B`, a contradiction.
-/

open Set

namespace Work.BoxShrink.Pinch

/-- **Phragmén–Brouwer, membership form, for disjoint closed sets.** -/
theorem mem_connectedComponentIn_union_of_mem_both_closed {A B : Set ℂ} (hA : IsClosed A)
    (hB : IsClosed B) (hAB : Disjoint A B) {x y : ℂ} (hx : x ∉ A ∪ B)
    (hy1 : y ∈ connectedComponentIn Aᶜ x) (hy2 : y ∈ connectedComponentIn Bᶜ x) :
    y ∈ connectedComponentIn (A ∪ B)ᶜ x := by
  rw [← Work.Spike.phragmen_brouwer_closed hA hB hAB hx]
  exact ⟨hy1, hy2⟩

/-- **Brouwer property for closed preconnected plane sets.**  For a closed preconnected `M ⊆ ℂ`
and any point `x`, the frontier of the connected component of `x` in `Mᶜ` is preconnected.

Reproduced from `Submission/Work/JordanSeparation/huntTwoComponentsHardStandalone.lean`: the
proof is the standard one, and the only place where compactness entered is the final
Phragmén–Brouwer step, which is available for closed sets. -/
theorem frontier_preconnected_of_isClosed_isPreconnected {M : Set ℂ} (hM : IsClosed M)
    (hMp : IsPreconnected M) (x : ℂ) :
    IsPreconnected (frontier (connectedComponentIn Mᶜ x)) := by
  by_cases hxM : x ∈ M
  · rw [connectedComponentIn_eq_empty (by simpa using hxM)]
    rw [frontier_empty]
    exact isPreconnected_empty
  · set C : Set ℂ := connectedComponentIn Mᶜ x with hCdef
    have hCopen : IsOpen C := hM.isOpen_compl.connectedComponentIn
    have hCpre : IsPreconnected C := hCdef ▸ isPreconnected_connectedComponentIn
    have hxmem : x ∈ C := hCdef ▸ mem_connectedComponentIn (by simpa using hxM)
    have hCsub : C ⊆ Mᶜ := connectedComponentIn_subset Mᶜ x
    have hfr_sub : frontier C ⊆ M :=
      Work.BoxShrink.Pinch.BorsukAux.frontier_connectedComponentIn_subset_closed hM x
    have hCdisjB : ∀ z, z ∈ C → z ∈ frontier C → False := by
      intro z hzC hzB
      rw [hCopen.frontier_eq] at hzB
      exact hzB.2 hzC
    have hxnotB : x ∉ frontier C := fun h => hCdisjB x hxmem h
    rw [isPreconnected_iff_subset_of_disjoint_closed]
    intro u v hu hv huv hdisj
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hnu, hnv⟩ := hcon
    have hB1ne : ((frontier C) ∩ u).Nonempty := by
      obtain ⟨z, hzB, hzv⟩ := not_subset.mp hnv
      exact ⟨z, hzB, by rcases huv hzB with h | h; exacts [h, absurd h hzv]⟩
    have hB2ne : ((frontier C) ∩ v).Nonempty := by
      obtain ⟨z, hzB, hzu⟩ := not_subset.mp hnu
      exact ⟨z, hzB, by rcases huv hzB with h | h; exacts [absurd h hzu, h]⟩
    have hB1c : IsClosed ((frontier C) ∩ u) := isClosed_frontier.inter hu
    have hB2c : IsClosed ((frontier C) ∩ v) := isClosed_frontier.inter hv
    have hdisjB : Disjoint ((frontier C) ∩ u) ((frontier C) ∩ v) := by
      rw [Set.disjoint_left]
      intro z hz1 hz2
      have hmem : z ∈ frontier C ∩ (u ∩ v) := ⟨hz1.1, hz1.2, hz2.2⟩
      rw [hdisj] at hmem
      exact hmem
    obtain ⟨G, hGpre, hGsub, hGN, hGA, hGB⟩ :=
      Work.BoxShrink.Pinch.BorsukAux.exists_preconnected_closure_inter
        (isClosed_frontier.inter hu) (isClosed_frontier.inter hv) hdisjB hMp
        ⟨_, hfr_sub hB1ne.some_mem.1, hB1ne.some_mem⟩
        ⟨_, hfr_sub hB2ne.some_mem.1, hB2ne.some_mem⟩
    obtain ⟨y, hyG, hyM⟩ := hGN
    have hynotC : y ∉ C := fun h => hCsub h hyM
    have hGsubB : G ⊆ (frontier C)ᶜ := by
      intro z hz hzB
      exact hGsub hz (by
        rcases huv hzB with h | h
        · exact Or.inl ⟨hzB, h⟩
        · exact Or.inr ⟨hzB, h⟩)
    have hCBpre : IsPreconnected (C ∪ (frontier C ∩ v)) :=
      hCpre.subset_closure subset_union_left (by
        rintro z (hz | hz)
        · exact subset_closure hz
        · exact frontier_subset_closure hz.1)
    have hCApre : IsPreconnected (C ∪ (frontier C ∩ u)) :=
      hCpre.subset_closure subset_union_left (by
        rintro z (hz | hz)
        · exact subset_closure hz
        · exact frontier_subset_closure hz.1)
    obtain ⟨w, hwcl, hwB2⟩ := hGB
    obtain ⟨w', hw'cl, hw'B1⟩ := hGA
    have hK1pre : IsPreconnected ((C ∪ (frontier C ∩ v)) ∪ G) :=
      Work.BoxShrink.Pinch.BorsukAux.IsPreconnected.union_of_closure_inter hCBpre hGpre
        ⟨w, hwcl, Or.inr hwB2⟩
    have hK2pre : IsPreconnected ((C ∪ (frontier C ∩ u)) ∪ G) :=
      Work.BoxShrink.Pinch.BorsukAux.IsPreconnected.union_of_closure_inter hCApre hGpre
        ⟨w', hw'cl, Or.inr hw'B1⟩
    have hK1sub : (C ∪ (frontier C ∩ v)) ∪ G ⊆ ((frontier C) ∩ u)ᶜ := by
      rintro z ((hz | hz) | hz)
      · exact fun h => hCdisjB z hz h.1
      · rintro ⟨hzB, hzu⟩
        have hmem : z ∈ frontier C ∩ (u ∩ v) := ⟨hzB, hzu, hz.2⟩
        rw [hdisj] at hmem
        exact hmem
      · exact fun h => hGsub hz (Or.inl h)
    have hK2sub : (C ∪ (frontier C ∩ u)) ∪ G ⊆ ((frontier C) ∩ v)ᶜ := by
      rintro z ((hz | hz) | hz)
      · exact fun h => hCdisjB z hz h.1
      · rintro ⟨hzB', hzv⟩
        have hmem : z ∈ frontier C ∩ (u ∩ v) := ⟨hzB', hz.2, hzv⟩
        rw [hdisj] at hmem
        exact hmem
      · exact fun h => hGsub hz (Or.inr h)
    have hy1 : y ∈ connectedComponentIn ((frontier C) ∩ u)ᶜ x :=
      hK1pre.subset_connectedComponentIn (Or.inl (Or.inl hxmem)) hK1sub (Or.inr hyG)
    have hy2 : y ∈ connectedComponentIn ((frontier C) ∩ v)ᶜ x :=
      hK2pre.subset_connectedComponentIn (Or.inl (Or.inl hxmem)) hK2sub (Or.inr hyG)
    have hxnotAB : x ∉ (frontier C ∩ u) ∪ (frontier C ∩ v) := by
      rintro (h | h)
      · exact hxnotB h.1
      · exact hxnotB h.1
    have hPB := mem_connectedComponentIn_union_of_mem_both_closed hB1c hB2c hdisjB hxnotAB hy1 hy2
    have hunion : (frontier C ∩ u) ∪ (frontier C ∩ v) = frontier C := by
      apply Set.Subset.antisymm
      · rintro z (h | h) <;> exact h.1
      · intro z hz
        rcases huv hz with h | h
        · exact Or.inl ⟨hz, h⟩
        · exact Or.inr ⟨hz, h⟩
    rw [hunion] at hPB
    exact hynotC (Work.BoxShrink.Pinch.BorsukAux.connectedComponentIn_compl_frontier_subset
      hCopen hxmem hPB)

/-- **Unicoherence of the plane.**  If `ℂ` is the union of two closed preconnected subsets `P`
and `Q`, then `P ∩ Q` is preconnected. -/
theorem UnicoherencePlane {P Q : Set ℂ} (hP : IsClosed P) (hQ : IsClosed Q)
    (hPp : IsPreconnected P) (hQp : IsPreconnected Q) (hcover : P ∪ Q = Set.univ) :
    IsPreconnected (P ∩ Q) := by
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro u v hu hv huv hdisj
  set A : Set ℂ := (P ∩ Q) ∩ u with hAdef
  set B : Set ℂ := (P ∩ Q) ∩ v with hBdef
  have hAcl : IsClosed A := by rw [hAdef]; exact (hP.inter hQ).inter hu
  have hBcl : IsClosed B := by rw [hBdef]; exact (hP.inter hQ).inter hv
  have hABdisj : Disjoint A B := by
    rw [hAdef, hBdef, Set.disjoint_left]
    rintro z ⟨hzPQ, hzu⟩ ⟨-, hzv⟩
    exact (Set.eq_empty_iff_forall_notMem.mp hdisj) z ⟨hzPQ, hzu, hzv⟩
  have hAuB : A ∪ B = P ∩ Q := by
    rw [hAdef, hBdef, ← Set.inter_union_distrib_left]
    exact Set.inter_eq_left.mpr huv
  by_cases hA0 : A = ∅
  · right
    intro z hz
    have hz' : z ∈ A ∪ B := by rw [hAuB]; exact hz
    rcases hz' with h | h
    · exact absurd h (by rw [hA0]; exact Set.notMem_empty z)
    · rw [hBdef] at h; exact h.2
  by_cases hB0 : B = ∅
  · left
    intro z hz
    have hz' : z ∈ A ∪ B := by rw [hAuB]; exact hz
    rcases hz' with h | h
    · rw [hAdef] at h; exact h.2
    · exact absurd h (by rw [hB0]; exact Set.notMem_empty z)
  exfalso
  have hAne : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hA0
  have hBne : B.Nonempty := Set.nonempty_iff_ne_empty.mpr hB0
  have hAsubP : A ⊆ P := by rw [hAdef]; rintro z ⟨⟨hz, -⟩, -⟩; exact hz
  have hBsubP : B ⊆ P := by rw [hBdef]; rintro z ⟨⟨hz, -⟩, -⟩; exact hz
  have hAsubQ : A ⊆ Q := by rw [hAdef]; rintro z ⟨⟨-, hz⟩, -⟩; exact hz
  have hBsubQ : B ⊆ Q := by rw [hBdef]; rintro z ⟨⟨-, hz⟩, -⟩; exact hz
  -- Wilder's Theorem II 3.10
  obtain ⟨G, hGpre, hGsub, hGNP, hGA, hGB⟩ :=
    Work.BoxShrink.Pinch.BorsukAux.exists_preconnected_closure_inter hAcl hBcl hABdisj hPp
      (Set.Nonempty.mono (fun z hz => ⟨hAsubP hz, hz⟩) hAne)
      (Set.Nonempty.mono (fun z hz => ⟨hBsubP hz, hz⟩) hBne)
  have hGsub' : G ⊆ Pᶜ ∪ Qᶜ := by
    intro z hz
    have h1 : z ∈ (A ∪ B)ᶜ := hGsub hz
    rw [hAuB, Set.compl_inter] at h1
    exact h1
  have hGor : G ⊆ Pᶜ ∨ G ⊆ Qᶜ :=
    IsPreconnected.subset_or_subset hP.isOpen_compl hQ.isOpen_compl
      (by
        rw [Set.disjoint_left]
        intro z hzP hzQ
        have h : z ∈ P ∪ Q := by rw [hcover]; exact Set.mem_univ z
        rcases h with h | h
        · exact hzP h
        · exact hzQ h)
      hGsub' hGpre
  have hGV : G ⊆ Qᶜ := by
    rcases hGor with h | h
    · exfalso
      obtain ⟨z, hzG, hzP⟩ := hGNP
      exact h hzG hzP
    · exact h
  obtain ⟨x, hxG, -⟩ := hGNP
  have hxQc : x ∈ Qᶜ := hGV hxG
  set W : Set ℂ := connectedComponentIn Qᶜ x with hWdef
  have hxW : x ∈ W := by rw [hWdef]; exact mem_connectedComponentIn hxQc
  have hGsubW : G ⊆ W := by
    rw [hWdef]
    exact hGpre.subset_connectedComponentIn hxG hGV
  have hWopen : IsOpen W := by
    rw [hWdef]; exact hQ.isOpen_compl.connectedComponentIn
  have hWsubQc : W ⊆ Qᶜ := by rw [hWdef]; exact connectedComponentIn_subset Qᶜ x
  -- the frontier of `W` meets both `A` and `B`
  have hfroWA : (frontier W ∩ A).Nonempty := by
    obtain ⟨za, hza_cl, hza_A⟩ := hGA
    refine ⟨za, ?_, hza_A⟩
    rw [hWopen.frontier_eq]
    exact ⟨closure_mono hGsubW hza_cl, fun hza_W => (hWsubQc hza_W) (hAsubQ hza_A)⟩
  have hfroWB : (frontier W ∩ B).Nonempty := by
    obtain ⟨zb, hzb_cl, hzb_B⟩ := hGB
    refine ⟨zb, ?_, hzb_B⟩
    rw [hWopen.frontier_eq]
    exact ⟨closure_mono hGsubW hzb_cl, fun hzb_W => (hWsubQc hzb_W) (hBsubQ hzb_B)⟩
  -- and it is contained in `K = A ∪ B`
  have hfroW_sub : frontier W ⊆ A ∪ B := by
    have hQcP : Qᶜ ⊆ P := by
      intro z hz
      have h : z ∈ P ∪ Q := by rw [hcover]; exact Set.mem_univ z
      rcases h with h | h
      · exact h
      · exact absurd h hz
    have hWsubP : W ⊆ P := hWsubQc.trans hQcP
    have hsubP : frontier W ⊆ P := by
      intro z hz
      have h2 : z ∈ closure P := closure_mono hWsubP (frontier_subset_closure hz)
      rwa [hP.closure_eq] at h2
    have hsubQ : frontier W ⊆ Q := by
      rw [hWdef]
      exact Work.BoxShrink.Pinch.BorsukAux.frontier_connectedComponentIn_subset_closed hQ x
    intro z hz
    have hzK : z ∈ P ∩ Q := ⟨hsubP hz, hsubQ hz⟩
    rwa [← hAuB] at hzK
  -- the Brouwer property makes the frontier preconnected
  have hfroWpre : IsPreconnected (frontier W) := by
    rw [hWdef]
    exact frontier_preconnected_of_isClosed_isPreconnected hQ hQp x
  have hfroWdisj : frontier W ∩ (A ∩ B) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨-, hzA, hzB⟩
    exact Set.disjoint_left.mp hABdisj hzA hzB
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hfroWpre) A B hAcl hBcl
      hfroW_sub hfroWdisj with h | h
  · obtain ⟨zb, hzb_fro, hzb_B⟩ := hfroWB
    exact Set.disjoint_left.mp hABdisj (h hzb_fro) hzb_B
  · obtain ⟨za, hza_fro, hza_A⟩ := hfroWA
    exact Set.disjoint_left.mp hABdisj hza_A (h hza_fro)

end Work.BoxShrink.Pinch
