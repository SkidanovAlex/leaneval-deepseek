import Mathlib
import Submission.Work.Smooth.JordanSeparation.square_cut

/-!
# The square lemma (disjoint case of Phragmén–Brouwer)

`Work.Smooth.JordanSeparation.square_lemma_aux`.

Two disjoint closed subsets `S1`, `S2` of the plane, the first missing the left edge
`L = {0} × [0,1]` of the unit square, the second missing the right edge `R = {1} × [0,1]`, whose
union misses the bottom edge `Btm = [0,1] × {0}` and the top edge `T0 = [0,1] × {1}`, do not
separate the bottom-left corner `(0,0)` from the top-left corner `(0,1)`.

The proof proceeds by contradiction: if `(0,0)` and `(0,1)` are separated by `Z = (S1 ∪ S2) ∩ Q`
(`Q = [0,1]²`), then the square cut lemma (`Work.Smooth.JordanSeparation.square_cut`) produces a
preconnected `C ⊆ Z` meeting the left and the right edge.  Since `C ⊆ Z ⊆ S1 ∪ S2` and `S1`, `S2`
are disjoint closed sets, `C` lies in `S1` or in `S2`; but `S1` misses the left edge, so it cannot
contain `C` (which meets `L`), and `S2` misses the right edge, so it cannot contain `C` (which
meets `R`).  Contradiction.
-/

namespace Work.Smooth.JordanSeparation

open Set Topology

noncomputable section

/-- A preconnected set covered by two disjoint closed sets lies in one of them. -/
theorem isPreconnected_subset_left_or_right' {α : Type*} [TopologicalSpace α] {A B C : Set α}
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) (hC : IsPreconnected C)
    (hsub : C ⊆ A ∪ B) : C ⊆ A ∨ C ⊆ B := by
  have hdisj : C ∩ (A ∩ B) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨-, hz⟩
    exact Set.disjoint_left.mp hAB hz.1 hz.2
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hC) A B hA hB hsub hdisj with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem square_lemma_aux {S1 S2 : Set (ℝ × ℝ)} (h1c : IsClosed S1) (h2c : IsClosed S2)
    (hdisj : Disjoint S1 S2)
    (hL : S1 ∩ (({0} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1) = ∅)
    (hR : S2 ∩ (({1} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1) = ∅)
    (hB : (S1 ∪ S2) ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({0} : Set ℝ)) = ∅)
    (hT : (S1 ∪ S2) ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({1} : Set ℝ)) = ∅) :
    ((0, 1) : ℝ × ℝ) ∈ connectedComponentIn (S1 ∪ S2)ᶜ ((0, 0) : ℝ × ℝ) := by
  by_contra hcon
  set Q : Set (ℝ × ℝ) := Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 with hQdef
  set Z : Set (ℝ × ℝ) := (S1 ∪ S2) ∩ Q with hZdef
  have hQc : IsClosed Q := isClosed_Icc.prod isClosed_Icc
  have hSc : IsClosed (S1 ∪ S2) := h1c.union h2c
  have hZc : IsClosed Z := hSc.inter hQc
  have hZQ : Z ⊆ Q := fun z hz => hz.2
  -- `Q \ Z = Q \ (S1 ∪ S2)`
  have hQZ : Q \ Z = Q \ (S1 ∪ S2) := by
    rw [hZdef]
    ext z
    constructor
    · rintro ⟨hzQ, hzS⟩
      refine ⟨hzQ, ?_⟩
      intro hzSI
      exact hzS ⟨hzSI, hzQ⟩
    · rintro ⟨hzQ, hzS⟩
      refine ⟨hzQ, ?_⟩
      rintro ⟨hzSI, -⟩
      exact hzS hzSI
  -- `(0,0)`, `(0,1)` are in `Q \ Z`
  have h00B : ((0:ℝ), (0:ℝ)) ∈ Set.Icc (0:ℝ) 1 ×ˢ ({0} : Set ℝ) := by
    rw [Set.mem_prod]; exact ⟨⟨le_rfl, zero_le_one⟩, rfl⟩
  have h01T : ((0:ℝ), (1:ℝ)) ∈ Set.Icc (0:ℝ) 1 ×ˢ ({1} : Set ℝ) := by
    rw [Set.mem_prod]; exact ⟨⟨le_rfl, zero_le_one⟩, rfl⟩
  have h00Q : ((0:ℝ), (0:ℝ)) ∈ Q \ Z := by
    refine ⟨⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩, ?_⟩
    rintro ⟨hSI, -⟩
    exact (Set.eq_empty_iff_forall_notMem.mp hB) _ ⟨hSI, h00B⟩
  have h01Q : ((0:ℝ), (1:ℝ)) ∈ Q \ Z := by
    refine ⟨⟨⟨le_rfl, zero_le_one⟩, ⟨zero_le_one, le_rfl⟩⟩, ?_⟩
    rintro ⟨hSI, -⟩
    exact (Set.eq_empty_iff_forall_notMem.mp hT) _ ⟨hSI, h01T⟩
  -- the separation hypothesis for the cut lemma
  have hsub : Q \ Z ⊆ (S1 ∪ S2)ᶜ := by
    rw [hQZ]
    exact fun z hz => hz.2
  have hsep : ((0, 1) : ℝ × ℝ) ∉ connectedComponentIn (Q \ Z) ((0, 0) : ℝ × ℝ) :=
    fun h => hcon (connectedComponentIn_mono ((0,0):ℝ×ℝ) hsub h)
  -- edges
  have hB' : Z ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({0} : Set ℝ)) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hzZ, hzB⟩
    exact (Set.eq_empty_iff_forall_notMem.mp hB) z ⟨hzZ.1, hzB⟩
  have hT' : Z ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({1} : Set ℝ)) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hzZ, hzT⟩
    exact (Set.eq_empty_iff_forall_notMem.mp hT) z ⟨hzZ.1, hzT⟩
  obtain ⟨C, hCZ, hCpre, hCL, hCR⟩ := square_cut hZc hZQ hB' hT' hsep
  have hCsub : C ⊆ S1 ∪ S2 := fun z hz => (hCZ hz).1
  rcases isPreconnected_subset_left_or_right' h1c h2c hdisj hCpre hCsub with hC1 | hC2
  · obtain ⟨z, hzC, hzL⟩ := hCL
    have : z ∈ S1 ∩ (({0} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1) := ⟨hC1 hzC, hzL⟩
    rw [hL] at this
    exact this
  · obtain ⟨z, hzC, hzR⟩ := hCR
    have : z ∈ S2 ∩ (({1} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1) := ⟨hC2 hzC, hzR⟩
    rw [hR] at this
    exact this

end

end Work.Smooth.JordanSeparation
