import Mathlib
import Submission.Work.Whitney.PathTools.arc_room_lemma

/-!
# The accumulation lemma for components of an open set minus a closed set

If `U` is an open preconnected set in a locally connected space and `C` is a nonempty closed
subset of `U`, then every connected component of `U \ C` has closure (in the ambient space)
meeting `C`.

This is the tool that turns "removing *more* of a set keeps the leftover connected" into
connectedness statements: if `X` is an open preconnected set whose intersection with an arc is
already covered by previously constructed balls, then each component of `X \ (arc)` accumulates
at a point of that intersection, hence meets the previously constructed region.
-/

namespace Work.Whitney.PathTools

open Set Topology

/-- **Accumulation lemma.**  If `U` is an open preconnected set in a locally connected space and
`C` is a nonempty closed subset of `U`, then every connected component of `U \ C` has closure
(in the ambient space) meeting `C`. -/
theorem closure_connectedComponentIn_diff_inter_nonempty {X : Type*} [TopologicalSpace X]
    [LocallyConnectedSpace X] {U C : Set X} (hUo : IsOpen U) (hUpre : IsPreconnected U)
    (hUC : IsOpen (U \ C)) (hCne : C.Nonempty) (hCU : C ⊆ U) {z : X} (hz : z ∈ U \ C) :
    (closure (connectedComponentIn (U \ C) z)) ∩ C ≠ ∅ := by
  classical
  by_contra hcon
  rw [Set.eq_empty_iff_forall_notMem] at hcon
  set W := connectedComponentIn (U \ C) z with hWdef
  have hzW : z ∈ W := mem_connectedComponentIn hz
  have hWpre : IsPreconnected W := isPreconnected_connectedComponentIn
  have hWopen : IsOpen W := hUC.connectedComponentIn
  have hWsub : W ⊆ U \ C := connectedComponentIn_subset _ _
  have hcl : closure W ∩ (U \ C) ⊆ W := by
    intro y hy
    have hunion : W ∪ {y} ⊆ U \ C := by
      rintro w (hw | rfl)
      · exact hWsub hw
      · exact hy.2
    have hpre : IsPreconnected (W ∪ {y}) := by
      rw [isPreconnected_iff_subset_of_disjoint]
      intro u v hu hv huv huvdisj
      have hWuv : W ⊆ u ∪ v := fun w hw => huv (Or.inl hw)
      have hWd : W ∩ (u ∩ v) = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro w ⟨hw, hwuv⟩
        exact Set.eq_empty_iff_forall_notMem.mp huvdisj w ⟨Or.inl hw, hwuv⟩
      rcases (isPreconnected_iff_subset_of_disjoint.mp hWpre) u v hu hv hWuv hWd with h | h
      · have hyu : y ∈ u := by
          by_contra hyu
          have hyv : y ∈ v := (huv (Or.inr rfl)).resolve_left hyu
          obtain ⟨w, hwv, hwW⟩ := mem_closure_iff.mp hy.1 v hv hyv
          exact Set.eq_empty_iff_forall_notMem.mp huvdisj w ⟨Or.inl hwW, h hwW, hwv⟩
        refine Or.inl ?_
        rintro w (hw | hwy)
        · exact h hw
        · rw [Set.mem_singleton_iff] at hwy
          subst hwy
          exact hyu
      · have hyv : y ∈ v := by
          by_contra hyv
          have hyu : y ∈ u := (huv (Or.inr rfl)).resolve_right hyv
          obtain ⟨w, hwu, hwW⟩ := mem_closure_iff.mp hy.1 u hu hyu
          exact Set.eq_empty_iff_forall_notMem.mp huvdisj w ⟨Or.inl hwW, hwu, h hwW⟩
        refine Or.inr ?_
        rintro w (hw | hwy)
        · exact h hw
        · rw [Set.mem_singleton_iff] at hwy
          subst hwy
          exact hyv
    have := IsPreconnected.subset_connectedComponentIn hpre (Or.inl hzW) hunion
    exact this (Or.inr rfl)
  have hkey : U ∩ closure W = W := by
    refine subset_antisymm ?_ ?_
    · intro y hy
      rcases hy with ⟨hyU, hycl⟩
      by_cases hyC : y ∈ C
      · exact (hcon y ⟨hycl, hyC⟩).elim
      · exact hcl ⟨hycl, hyU, hyC⟩
    · exact fun y hy => ⟨(hWsub hy).1, subset_closure hy⟩
  have hdisj : Disjoint W ((closure W)ᶜ) := by
    rw [Set.disjoint_left]
    intro y hyW hy
    exact hy (subset_closure hyW)
  have hunion : U ⊆ W ∪ (closure W)ᶜ := by
    intro y hy
    by_cases h : y ∈ closure W
    · exact Or.inl (hkey ▸ ⟨hy, h⟩)
    · exact Or.inr h
  rcases IsPreconnected.subset_or_subset hWopen isClosed_closure.isOpen_compl hdisj hunion
    hUpre with h | h
  · obtain ⟨c, hc⟩ := hCne
    exact (hWsub (h (hCU hc))).2 hc
  · exact (h hz.1) (subset_closure hzW)

end Work.Whitney.PathTools
