import Mathlib
import Submission.Work.Whitney.PathTools.LocalRoomAux

namespace Work.Whitney.PathTools

/-- Auxiliary lemma (the "one-sided" step of the room argument).

Let `T` be preconnected, `V ⊆ T` open, `C ⊆ V`, and suppose `T \ C` is the disjoint union of two
open sets `A`, `B`.  If moreover `V \ C ⊆ A`, then `T \ C` is contained in `A` or in `B`.

The proof pushes the "cut" of `T \ C` past the open room `V`:  since `V \ C ⊆ A`, every point of
`C` sits in the open neighbourhood `V ⊆ (A ∪ V)` which avoids `B`, so `A ∪ V` and `B` give a
separation of `T` unless `T \ C ⊆ B`. -/
lemma sdiff_subset_left_of_room {X : Type*} [TopologicalSpace X]
    {T C V A B : Set X} (hT : IsPreconnected T)
    (hAo : IsOpen A) (hBo : IsOpen B) (hVo : IsOpen V)
    (hAB : Disjoint A B) (hCV : C ⊆ V)
    (hABC : T \ C = A ∪ B) (hVA : V \ C ⊆ A) :
    T \ C ⊆ A ∨ T \ C ⊆ B := by
  -- `V` is disjoint from `B`:  a point of `V ∩ B` lies in `V \ C ⊆ A`, contradicting `A ∩ B = ∅`.
  have hVB : Disjoint V B := by
    rw [Set.disjoint_left]
    intro x hxV hxB
    have hxs : x ∈ T \ C := by rw [hABC]; exact Or.inr hxB
    exact (Set.disjoint_left.1 hAB) (hVA ⟨hxV, hxs.2⟩) hxB
  have hUo : IsOpen (A ∪ V) := hAo.union hVo
  -- `T` is covered by the two open sets `A ∪ V` and `B` …
  have hTsub : T ⊆ (A ∪ V) ∪ B := by
    intro x hxT
    by_cases hxC : x ∈ C
    · exact Or.inl (Or.inr (hCV hxC))
    · have hxs : x ∈ T \ C := ⟨hxT, hxC⟩
      rw [hABC] at hxs
      rcases hxs with hxA | hxB
      · exact Or.inl (Or.inl hxA)
      · exact Or.inr hxB
  -- … and these two open sets are disjoint.
  have hdisjT : Disjoint T ((A ∪ V) ∩ B) := by
    rw [Set.disjoint_left]
    intro x _ hx
    rcases hx.1 with hxA | hxV
    · exact (Set.disjoint_left.1 hAB) hxA hx.2
    · exact (Set.disjoint_left.1 hVB) hxV hx.2
  have hdisj : T ∩ ((A ∪ V) ∩ B) = ∅ := Set.disjoint_iff_inter_eq_empty.1 hdisjT
  rcases isPreconnected_iff_subset_of_disjoint.1 hT (A ∪ V) B hUo hBo hTsub hdisj with hTU | hTB
  · -- `T ⊆ A ∪ V`:  then `T \ C ⊆ (A ∪ V) \ C = A ∪ (V \ C) = A`.
    left
    intro x hx
    rcases hTU hx.1 with hxA | hxV
    · exact hxA
    · exact hVA ⟨hxV, hx.2⟩
  · -- `T ⊆ B`:  then `T \ C ⊆ B` directly.
    right
    intro x hx
    exact hTB hx.1

theorem isPreconnected_sdiff_of_room_of_open {X : Type*} [TopologicalSpace X]
    {T C V : Set X} (hT : IsPreconnected T) (hTCopen : IsOpen (T \ C)) (hVo : IsOpen V)
    (hCV : C ⊆ V) (hVT : V ⊆ T) (hVp : IsPreconnected (V \ C)) :
    IsPreconnected (T \ C) := by
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hsub hdisj
  -- Split `T \ C` along the two open sets `u`, `v`.
  set A := u ∩ (T \ C) with hA
  set B := v ∩ (T \ C) with hB
  have hAo : IsOpen A := by rw [hA]; exact hu.inter hTCopen
  have hBo : IsOpen B := by rw [hB]; exact hv.inter hTCopen
  have hAu : A ⊆ u := by rw [hA]; exact Set.inter_subset_left
  have hBv : B ⊆ v := by rw [hB]; exact Set.inter_subset_left
  have hAB : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    have hxs : x ∈ T \ C := (hA ▸ hxA).2
    have hxu : x ∈ u := (hA ▸ hxA).1
    have hxv : x ∈ v := (hB ▸ hxB).1
    have hmem : x ∈ (T \ C) ∩ (u ∩ v) := ⟨hxs, hxu, hxv⟩
    rw [hdisj] at hmem
    exact hmem
  -- `T \ C = A ∪ B`
  have hsAB : T \ C = A ∪ B := by
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      rcases hsub hx with hxu | hxv
      · left; rw [hA]; exact ⟨hxu, hx⟩
      · right; rw [hB]; exact ⟨hxv, hx⟩
    · intro x hx
      rcases hx with hxA | hxB
      · exact (hA ▸ hxA).2
      · exact (hB ▸ hxB).2
  -- The room `V \ C` is preconnected and contained in `A ∪ B`, so it lies in one piece.
  have hVsubAB : V \ C ⊆ A ∪ B := by
    intro x hx
    have hxs : x ∈ T \ C := ⟨hVT hx.1, hx.2⟩
    rcases hsub hxs with hxu | hxv
    · left; rw [hA]; exact ⟨hxu, hxs⟩
    · right; rw [hB]; exact ⟨hxv, hxs⟩
  rcases hVp.subset_or_subset hAo hBo hAB hVsubAB with hVA | hVB
  · rcases sdiff_subset_left_of_room hT hAo hBo hVo hAB hCV hsAB hVA with hA' | hB'
    · exact Or.inl (hA'.trans hAu)
    · exact Or.inr (hB'.trans hBv)
  · have hsBA : T \ C = B ∪ A := by rw [hsAB, Set.union_comm]
    rcases sdiff_subset_left_of_room hT hBo hAo hVo hAB.symm hCV hsBA hVB with hB' | hA'
    · exact Or.inr (hB'.trans hBv)
    · exact Or.inl (hA'.trans hAu)

end Work.Whitney.PathTools
