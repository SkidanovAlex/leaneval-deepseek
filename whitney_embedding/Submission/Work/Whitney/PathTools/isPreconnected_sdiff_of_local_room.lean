import Mathlib

namespace Work.Whitney.PathTools

open Set Topology Filter

/-- If every point of a closed set `Y` has arbitrarily small neighbourhoods `O` whose complement
inside `O` is preconnected, then removing `Y` from an open preconnected set `T` keeps it
preconnected. -/
theorem isPreconnected_sdiff_of_local_room {X : Type*} [TopologicalSpace X]
    {T : Set X} (hT : IsPreconnected T) (hTo : IsOpen T) {Y : Set X} (hY : IsClosed Y)
    (hloc : ∀ y ∈ Y, ∀ N ∈ 𝓝 y, ∃ O : Set X, IsOpen O ∧ y ∈ O ∧ O ⊆ N ∧
      (O \ Y).Nonempty ∧ IsPreconnected (O \ Y)) :
    IsPreconnected (T \ Y) := by
  set W : Set X := T \ Y with hWdef
  by_contra hWnc
  unfold IsPreconnected at hWnc
  push_neg at hWnc
  obtain ⟨u, v, hu, hv, hWuv, hWu, hWv, hWuv'⟩ := hWnc
  have hWsub : W ⊆ T := by rw [hWdef]; exact diff_subset
  have hWopen : IsOpen W := by rw [hWdef]; exact hTo.sdiff hY
  let A : Set X := W ∩ u
  let B : Set X := W ∩ v
  let C : Set X := T ∩ Y
  have hAopen : IsOpen A := hWopen.inter hu
  have hBopen : IsOpen B := hWopen.inter hv
  have hAW : A ⊆ W := by intro x hx; simp only [A, mem_inter_iff] at hx; exact hx.1
  have hBW : B ⊆ W := by intro x hx; simp only [B, mem_inter_iff] at hx; exact hx.1
  have hAS' : A ⊆ closure A ∩ T := by
    intro x hx
    exact ⟨subset_closure hx, hWsub (hAW hx)⟩
  have hAB : A ∪ B = W := by
    show W ∩ u ∪ W ∩ v = W
    rw [← Set.inter_union_distrib_left W u v, Set.inter_eq_left.mpr hWuv]
  have hABdisj : A ∩ B = ∅ := by
    apply le_antisymm
    · intro x hx
      simp only [A, B, mem_inter_iff] at hx
      obtain ⟨⟨hxW, hxu⟩, ⟨-, hxv⟩⟩ := hx
      have hx' : x ∈ W ∩ (u ∩ v) := ⟨hxW, hxu, hxv⟩
      rw [hWuv'] at hx'
      exact hx'
    · exact Set.empty_subset _
  have hWCT : W ∪ C = T := by
    ext x
    simp only [C, hWdef, mem_union, mem_diff, mem_inter_iff]
    tauto
  -- Every point of `C = T ∩ Y` is a limit point of `A ∪ B = W`.
  have hCcl : C ⊆ closure A ∪ closure B := by
    intro y hy
    simp only [C, mem_inter_iff] at hy
    obtain ⟨hyT, hyY⟩ := hy
    have hyclW : y ∈ closure W := by
      rw [mem_closure_iff]
      intro N hN hyN
      have hmem : N ∩ T ∈ 𝓝 y := (hN.inter hTo).mem_nhds ⟨hyN, hyT⟩
      obtain ⟨O, hOo, hyO, hOT, hOne, _⟩ := hloc y hyY (N ∩ T) hmem
      have hOW : O \ Y ⊆ W := by
        rw [hWdef]
        intro x hx
        exact ⟨(hOT hx.1).2, hx.2⟩
      obtain ⟨p, hp⟩ := hOne
      exact ⟨p, (hOT hp.1).1, hOW hp⟩
    rw [← hAB] at hyclW
    rw [closure_union] at hyclW
    exact hyclW
  have hclAB : closure A ∩ B = ∅ := by
    have h := hBopen.closure_inter (s := A)
    rw [hABdisj, closure_empty] at h
    exact le_antisymm h (Set.empty_subset _)
  -- `S := closure A ∩ T` is the clopen piece we use to contradict preconnectedness of `T`.
  let S : Set X := closure A ∩ T
  have hclosST : closure S ∩ T ⊆ S := by
    intro x hx
    obtain ⟨hxclS, hxT⟩ := hx
    have hxclA : x ∈ closure A := by
      have hs : S ⊆ closure A := inter_subset_left
      have hmono := closure_mono hs
      rw [closure_closure] at hmono
      exact hmono hxclS
    exact ⟨hxclA, hxT⟩
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨hyclA, hyT⟩ := hy
    have hyWC : y ∈ W ∪ C := by rw [hWCT]; exact hyT
    rcases hyWC with hyW | hyC
    · have hyAB : y ∈ A ∪ B := by rw [hAB]; exact hyW
      rcases hyAB with hyA | hyB
      · exact Filter.mem_of_superset (hAopen.mem_nhds hyA) hAS'
      · exfalso
        have hmem : y ∈ closure A ∩ B := ⟨hyclA, hyB⟩
        rw [hclAB] at hmem
        exact hmem
    · simp only [C, mem_inter_iff] at hyC
      obtain ⟨-, hyY⟩ := hyC
      obtain ⟨O, hOo, hyO, hOT, hOne, hOpre⟩ := hloc y hyY T (hTo.mem_nhds hyT)
      have hOW : O \ Y ⊆ W := by
        rw [hWdef]
        intro x hx
        exact ⟨hOT hx.1, hx.2⟩
      have hOuW : O \ Y ⊆ (u ∩ W) ∪ (v ∩ W) := by
        intro x hx
        have hxW := hOW hx
        rcases hWuv hxW with hxu | hxv
        · exact Or.inl ⟨hxu, hxW⟩
        · exact Or.inr ⟨hxv, hxW⟩
      have hdisj : Disjoint (u ∩ W) (v ∩ W) := by
        rw [Set.disjoint_left]
        intro x hx hx'
        obtain ⟨hxu, hxW⟩ := hx
        obtain ⟨hxv, -⟩ := hx'
        have hxw : x ∈ W ∩ (u ∩ v) := ⟨hxW, hxu, hxv⟩
        rw [hWuv'] at hxw
        exact hxw
      rcases hOpre.subset_or_subset (hu.inter hWopen) (hv.inter hWopen) hdisj hOuW with h | h
      · have hOAY : O \ Y ⊆ A := by
          intro x hx
          have hx' := h hx
          exact ⟨hx'.2, hx'.1⟩
        have hOS : O ⊆ S := by
          intro x hxO
          have hxT : x ∈ T := hOT hxO
          have hxWC : x ∈ W ∪ C := by rw [hWCT]; exact hxT
          rcases hxWC with hxW | hxC
          · have hxAB : x ∈ A ∪ B := by rw [hAB]; exact hxW
            rcases hxAB with hxA | hxB
            · exact ⟨subset_closure hxA, hxT⟩
            · exfalso
              have hxOY : x ∈ O \ Y := ⟨hxO, by rw [hWdef] at hxW; exact hxW.2⟩
              have hxA' : x ∈ A := hOAY hxOY
              have hmem : x ∈ A ∩ B := ⟨hxA', hxB⟩
              rw [hABdisj] at hmem
              exact hmem
          · have hxcl : x ∈ closure A ∪ closure B := hCcl hxC
            rcases hxcl with hxclA | hxclB
            · exact ⟨hxclA, hxT⟩
            · exfalso
              have hne : (O ∩ B).Nonempty := (mem_closure_iff.mp hxclB) O hOo hxO
              obtain ⟨z, hzO, hzB⟩ := hne
              simp only [B, mem_inter_iff] at hzB
              have hzW : z ∈ W := hzB.1
              have hzOY : z ∈ O \ Y := ⟨hzO, by rw [hWdef] at hzW; exact hzW.2⟩
              have hzA : z ∈ A := hOAY hzOY
              have hmem : z ∈ A ∩ B := ⟨hzA, by exact ⟨hzB.1, hzB.2⟩⟩
              rw [hABdisj] at hmem
              exact hmem
        exact Filter.mem_of_superset (hOo.mem_nhds hyO) hOS
      · exfalso
        obtain ⟨x, hxO, hxA⟩ := (mem_closure_iff.mp hyclA) O hOo hyO
        simp only [A, mem_inter_iff] at hxA
        have hxW : x ∈ W := hxA.1
        have hxOY : x ∈ O \ Y := ⟨hxO, by rw [hWdef] at hxW; exact hxW.2⟩
        have hxB : x ∈ B := by
          have hx' := h hxOY
          exact ⟨hx'.2, hx'.1⟩
        have hxu : x ∈ u := hxA.2
        simp only [B, mem_inter_iff] at hxB
        have hmem : x ∈ W ∩ (u ∩ v) := ⟨hxW, hxu, hxB.2⟩
        rw [hWuv'] at hmem
        exact hmem
  have hTS : T ⊆ S := by
    apply hT.subset_of_closure_inter_subset hSopen
    · obtain ⟨a, ha⟩ := hWu
      exact ⟨a, hWsub (hAW ha), hAS' ha⟩
    · exact hclosST
  obtain ⟨b, hb⟩ := hWv
  have hbT : b ∈ T := hWsub (hBW hb)
  have hbS : b ∈ S := hTS hbT
  simp only [S, mem_inter_iff] at hbS
  have hmem : b ∈ closure A ∩ B := ⟨hbS.1, hb⟩
  rw [hclAB] at hmem
  exact hmem

end Work.Whitney.PathTools
