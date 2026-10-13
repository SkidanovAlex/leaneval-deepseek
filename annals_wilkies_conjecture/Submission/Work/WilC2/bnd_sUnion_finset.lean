import Mathlib
import Submission.Work.WilC2.BndDefs

set_option autoImplicit false

namespace Work.WilC2

variable {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]

/-- If two sets each have a neighbourhood of `x` contained in their complement, then a single
(possibly smaller) neighbourhood of `x` is contained in the complement of their union. -/
lemma exists_Ioo_subset_compl_union {A B : Set M} {x : M}
    (hA : ∃ ε : M, 0 < ε ∧ Set.Ioo (x - ε) (x + ε) ⊆ Aᶜ)
    (hB : ∃ ε : M, 0 < ε ∧ Set.Ioo (x - ε) (x + ε) ⊆ Bᶜ) :
    ∃ ε : M, 0 < ε ∧ Set.Ioo (x - ε) (x + ε) ⊆ (A ∪ B)ᶜ := by
  obtain ⟨ε₁, hε₁, hA'⟩ := hA
  obtain ⟨ε₂, hε₂, hB'⟩ := hB
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro y hy
  rw [Set.mem_compl_iff, Set.mem_union]
  rintro (hyA | hyB)
  · exact hA' (Ioo_subset_Ioo (min_le_left _ _) hy) hyA
  · exact hB' (Ioo_subset_Ioo (min_le_right _ _) hy) hyB

/-- If every member of a finite family of sets has a neighbourhood of `x` contained in its
complement, then a single neighbourhood of `x` is contained in the complement of their union. -/
lemma exists_Ioo_subset_sUnion_compl {s : Finset (Set M)} {x : M}
    (h : ∀ I ∈ s, ∃ ε : M, 0 < ε ∧ Set.Ioo (x - ε) (x + ε) ⊆ Iᶜ) :
    ∃ ε : M, 0 < ε ∧ Set.Ioo (x - ε) (x + ε) ⊆ (⋃₀ (s : Set (Set M)))ᶜ := by
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1, one_pos, ?_⟩
      intro y _
      simp
  | insert a s' ha ih =>
      obtain ⟨ε₁, hε₁, hA'⟩ := h a (Finset.mem_insert_self a s')
      obtain ⟨ε₂, hε₂, hB'⟩ := ih (fun I hI => h I (Finset.mem_insert_of_mem hI))
      refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
      intro y hy
      rw [Finset.coe_insert, Set.sUnion_insert, Set.mem_compl_iff, Set.mem_union]
      rintro (hyA | hyB)
      · exact hA' (Ioo_subset_Ioo (min_le_left _ _) hy) hyA
      · exact hB' (Ioo_subset_Ioo (min_le_right _ _) hy) hyB

/-- **A boundary point of a finite union of sets is a boundary point of one of the pieces.** -/
lemma bnd_sUnion_finset {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    {s : Finset (Set M)} {x : M}
    (hx : IsBnd (⋃₀ (s : Set (Set M))) x) : ∃ I ∈ s, IsBnd I x := by
  obtain ⟨hnotint, hlim⟩ := hx
  -- `x` is not an interior point of the union, but it is a limit point of the union.
  -- Being a limit point of a finite union, it is a limit point of one of the pieces.
  have hpiece : ∃ I ∈ s, ¬ ∃ ε : M, 0 < ε ∧ Set.Ioo (x - ε) (x + ε) ⊆ Iᶜ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨ε, hε, hsub⟩ := exists_Ioo_subset_sUnion_compl hcon
    exact hlim ⟨ε, hε, hsub⟩
  obtain ⟨I, hIs, hIlim⟩ := hpiece
  refine ⟨I, hIs, ?_, hIlim⟩
  rintro ⟨ε, hε, hsub⟩
  exact hnotint ⟨ε, hε, fun y hy => Set.mem_sUnion.mpr ⟨I, hIs, hsub hy⟩⟩

end Work.WilC2
