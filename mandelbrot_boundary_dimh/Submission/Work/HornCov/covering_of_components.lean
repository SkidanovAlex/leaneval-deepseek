import Mathlib

set_option linter.style.haveILetI false

namespace Work.HornCov

/-- For an open set `s`, a subset `A ⊆ s` is open in the ambient space iff it is open when
viewed as a subset of the subtype `s`. -/
lemma isOpen_subtype_val_preimage_iff {α : Type*} [TopologicalSpace α] {s : Set α}
    (hs : IsOpen s) {A : Set α} (hA : A ⊆ s) :
    IsOpen A ↔ IsOpen (Subtype.val ⁻¹' A : Set ↥s) := by
  refine ⟨fun h => h.preimage continuous_subtype_val, fun h => ?_⟩
  have h' := hs.isOpenMap_subtype_val (Subtype.val ⁻¹' A) h
  rwa [Subtype.image_preimage_coe, Set.inter_eq_right.mpr hA] at h'

theorem covering_of_components {X : Type*} [TopologicalSpace X] {f : X → ℂ} {S : Set ℂ}
    (hS : IsOpen S) {ι : Type*} [TopologicalSpace ι] [DiscreteTopology ι] (C : ι → Set X)
    (hCopen : ∀ i, IsOpen (C i)) (hCdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hCcov : f ⁻¹' S = ⋃ i, C i) (H : ∀ i, ↥(C i) ≃ₜ ↥S)
    (hH : ∀ i z, (H i z : ℂ) = f (z : X)) : IsCoveringMapOn f S := by
  by_cases hne : (f ⁻¹' S).Nonempty
  · -- the preimage of `S` is nonempty, so both `ι` and `X` are nonempty
    haveI hXne : Nonempty X := ⟨hne.choose⟩
    haveI hιne : Nonempty ι := by
      have hmem : hne.choose ∈ ⋃ i, C i := by rw [← hCcov]; exact hne.choose_spec
      obtain ⟨i, -⟩ := Set.mem_iUnion.mp hmem
      exact ⟨i⟩
    haveI hfne : Nonempty (ℂ → X) := ⟨fun _ => hne.choose⟩
    -- `f` is injective on each component `C i`
    have hinj : ∀ i, (C i).InjOn f := by
      intro i a ha b hb hab
      have h1 : (H i) ⟨a, ha⟩ = (H i) ⟨b, hb⟩ :=
        Subtype.ext (by rw [hH i ⟨a, ha⟩, hH i ⟨b, hb⟩]; exact hab)
      exact congrArg Subtype.val ((H i).injective h1)
    -- `f` maps each component `C i` onto `S`
    have hsurj : ∀ i, (C i).SurjOn f S := by
      intro i s hs
      refine ⟨((H i).symm ⟨s, hs⟩ : ↥(C i)), ((H i).symm ⟨s, hs⟩).2, ?_⟩
      rw [← hH i ((H i).symm ⟨s, hs⟩), Homeomorph.apply_symm_apply]
    -- the topology of `S` is determined by the topology of any component `C i`
    have hiff : ∀ i {W : Set ℂ}, W ⊆ S → (IsOpen W ↔ IsOpen (f ⁻¹' W ∩ C i)) := by
      intro i W hWS
      have h1 : (Subtype.val ⁻¹' (f ⁻¹' W ∩ C i) : Set ↥(C i))
          = (H i) ⁻¹' (Subtype.val ⁻¹' W : Set ↥S) := by
        ext z
        simp only [Set.mem_preimage, Set.mem_inter_iff, Subtype.coe_prop, and_true]
        rw [hH i z]
      rw [isOpen_subtype_val_preimage_iff (hCopen i) Set.inter_subset_right, h1,
        (H i).isOpen_preimage, isOpen_subtype_val_preimage_iff hS hWS]
    let t : Bundle.Trivialization ι f :=
      IsOpen.trivializationDiscrete C S hS hiff hinj hsurj hCdisj hCcov.le
    intro x hx
    exact (IsEvenlyCovered.of_trivialization (t := t) hx).to_isEvenlyCovered_preimage
  · -- the preimage of `S` is empty, so every fibre above `S` is empty
    intro x hx
    have hfS : f ⁻¹' S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    haveI : IsEmpty (f ⁻¹' {x}) := Set.isEmpty_coe_sort.mpr (Set.eq_empty_of_subset_empty
      ((Set.preimage_mono (Set.singleton_subset_iff.mpr hx)).trans hfS.le))
    exact IsEvenlyCovered.of_preimage_eq_empty (f ⁻¹' {x}) (hS.mem_nhds hx) hfS

end Work.HornCov
