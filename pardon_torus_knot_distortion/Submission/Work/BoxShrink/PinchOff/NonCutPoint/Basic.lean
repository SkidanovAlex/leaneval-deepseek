import Mathlib

/-!
# Separations of `X \ {x}` in a connected space

If `x` is a cut point of a connected space `X`, then `X \ {x}` splits as `A ∪ B` with `A`, `B`
nonempty, open, disjoint.  This file records the two structural facts about such a split that the
non-cut-point existence theorem needs:

* `closure_eq_union_singleton_of_sep` : `closure A = A ∪ {x}` (and symmetrically for `B`);
* `isPreconnected_union_singleton_of_sep` : `A ∪ {x}` is preconnected.

Both hold in an arbitrary connected topological space.
-/

open Set

namespace Work.BoxShrink.PinchOff

variable {X : Type*} [TopologicalSpace X]

/-- **The closure of one side of a separation of `X \ {x}` is that side with `x` adjoined.**

Let `X` be preconnected, `x ∈ X`, and let `A`, `B` be nonempty disjoint open sets with
`A ∪ B = {x}ᶜ`.  Then `closure A = A ∪ {x}` (and by symmetry `closure B = B ∪ {x}`). -/
theorem closure_eq_union_singleton_of_sep (hX : IsPreconnected (univ : Set X)) {x : X} {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hdisj : Disjoint A B) (hunion : A ∪ B = {x}ᶜ) : closure A = A ∪ {x} := by
  have hAB : A ⊆ Bᶜ := fun z hz => by
    rw [mem_compl_iff]; exact fun hzB => (Set.disjoint_left.mp hdisj hz) hzB
  have hclAB : closure A ⊆ Bᶜ := closure_minimal hAB hB.isClosed_compl
  have hsub1 : closure A ⊆ A ∪ {x} := by
    intro y hy
    by_cases hyx : y = x
    · exact Or.inr (by rwa [mem_singleton_iff])
    · refine Or.inl ?_
      have hy' : y ∈ ({x}ᶜ : Set X) := by
        rw [mem_compl_iff, mem_singleton_iff]; exact hyx
      rw [← hunion] at hy'
      rcases hy' with hyA | hyB
      · exact hyA
      · exact absurd hyB (hclAB hy)
  have hxcl : x ∈ closure A := by
    by_contra hx
    have hcA : closure A = A := by
      refine le_antisymm ?_ subset_closure
      intro y hy
      rcases hsub1 hy with hyA | hyx
      · exact hyA
      · rw [mem_singleton_iff] at hyx; exact absurd (hyx ▸ hy) hx
    have hcl : IsClosed A := hcA ▸ isClosed_closure
    have hor : univ ⊆ A ∨ univ ⊆ Aᶜ :=
      hX.subset_or_subset hA hcl.isOpen_compl disjoint_compl_right (by rw [union_compl_self])
    rcases hor with h | h
    · have hAu : A = univ := eq_univ_of_univ_subset h
      have hBA : B ⊆ A := by rw [hAu]; exact subset_univ B
      exact hBne.ne_empty (eq_empty_of_subset_empty (fun y hy => Set.disjoint_left.mp hdisj (hBA hy) hy))
    · exact hAne.ne_empty (eq_empty_of_subset_empty (fun y hy => (h (mem_univ y)) hy))
  exact le_antisymm hsub1 (union_subset subset_closure (singleton_subset_iff.mpr hxcl))

/-- **One side of a separation of `X \ {x}`, with `x` adjoined, is preconnected.**

Let `X` be preconnected, `x ∈ X`, and let `A`, `B` be nonempty disjoint open sets with
`A ∪ B = {x}ᶜ`.  Then `A ∪ {x}` is preconnected.  (For a connected space this is the classical
"the two halves of a cut are continua".) -/
theorem isPreconnected_union_singleton_of_sep (hX : IsPreconnected (univ : Set X)) {x : X} {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hdisj : Disjoint A B) (hunion : A ∪ B = {x}ᶜ) : IsPreconnected (A ∪ {x}) := by
  intro u v hu hv huv hnu hnv
  by_contra hempty
  rw [not_nonempty_iff_eq_empty] at hempty
  have hempty' : (A ∪ {x}) ∩ (u ∩ v) = ∅ := hempty
  have hxuv : x ∈ u ∪ v := huv (Or.inr (mem_singleton x))
  have hnotin : ∀ y, y ∈ A ∪ {x} → y ∈ u → y ∈ v → False := by
    intro y hy hu' hv'
    have : y ∈ (A ∪ {x}) ∩ (u ∩ v) := ⟨hy, hu', hv'⟩
    rw [hempty'] at this
    exact this
  rcases hxuv with hxu | hxv
  · have hcov : univ ⊆ (u ∪ B) ∪ (A ∩ v) := by
      intro y hy
      by_cases hyA : y ∈ A
      · rcases (huv (Or.inl hyA) : y ∈ u ∪ v) with hyu | hyv
        · exact Or.inl (Or.inl hyu)
        · exact Or.inr ⟨hyA, hyv⟩
      · by_cases hyB : y ∈ B
        · exact Or.inl (Or.inr hyB)
        · have hyx : y ∈ ({x} : Set X) := by
            by_contra h
            have h1 : y ∈ ({x}ᶜ : Set X) := by simpa using h
            rw [← hunion] at h1
            exact h1.elim hyA hyB
          rw [mem_singleton_iff] at hyx
          subst hyx
          exact Or.inl (Or.inl hxu)
    have hdis : Disjoint (u ∪ B) (A ∩ v) := by
      rw [Set.disjoint_left]
      intro y hy1 hy2
      rcases hy1 with hyu | hyB
      · exact hnotin y (Or.inl hy2.1) hyu hy2.2
      · exact (Set.disjoint_left.mp hdisj) hy2.1 hyB
    have hn1 : (univ ∩ (u ∪ B)).Nonempty := hBne.mono (fun y hy => ⟨mem_univ y, Or.inr hy⟩)
    have hn2 : (univ ∩ (A ∩ v)).Nonempty := by
      obtain ⟨y, hy⟩ := hnv
      rcases hy.1 with hyA | hyx
      · exact ⟨y, mem_univ y, hyA, hy.2⟩
      · rw [mem_singleton_iff] at hyx
        exact absurd hy.2 (fun hv' => hnotin x (Or.inr (mem_singleton x)) hxu (hyx ▸ hv'))
    obtain ⟨y, -, hy2⟩ := hX (u ∪ B) (A ∩ v) (hu.union hB) (hA.inter hv) hcov hn1 hn2
    exact (Set.disjoint_left.mp hdis) hy2.1 hy2.2
  · have hcov : univ ⊆ (v ∪ B) ∪ (A ∩ u) := by
      intro y hy
      by_cases hyA : y ∈ A
      · rcases (huv (Or.inl hyA) : y ∈ u ∪ v) with hyu | hyv
        · exact Or.inr ⟨hyA, hyu⟩
        · exact Or.inl (Or.inl hyv)
      · by_cases hyB : y ∈ B
        · exact Or.inl (Or.inr hyB)
        · have hyx : y ∈ ({x} : Set X) := by
            by_contra h
            have h1 : y ∈ ({x}ᶜ : Set X) := by simpa using h
            rw [← hunion] at h1
            exact h1.elim hyA hyB
          rw [mem_singleton_iff] at hyx
          subst hyx
          exact Or.inl (Or.inl hxv)
    have hdis : Disjoint (v ∪ B) (A ∩ u) := by
      rw [Set.disjoint_left]
      intro y hy1 hy2
      rcases hy1 with hyv | hyB
      · exact hnotin y (Or.inl hy2.1) hy2.2 hyv
      · exact (Set.disjoint_left.mp hdisj) hy2.1 hyB
    have hn1 : (univ ∩ (v ∪ B)).Nonempty := hBne.mono (fun y hy => ⟨mem_univ y, Or.inr hy⟩)
    have hn2 : (univ ∩ (A ∩ u)).Nonempty := by
      obtain ⟨y, hy⟩ := hnu
      rcases hy.1 with hyA | hyx
      · exact ⟨y, mem_univ y, hyA, hy.2⟩
      · rw [mem_singleton_iff] at hyx
        exact absurd hy.2 (fun hu' => hnotin x (Or.inr (mem_singleton x)) (hyx ▸ hu') hxv)
    obtain ⟨y, -, hy2⟩ := hX (v ∪ B) (A ∩ u) (hv.union hB) (hA.inter hu) hcov hn1 hn2
    exact (Set.disjoint_left.mp hdis) hy2.1 hy2.2

end Work.BoxShrink.PinchOff
