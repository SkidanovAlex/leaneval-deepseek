import Mathlib
import Submission.Work.Smooth.JordanSeparation.grid_spanning_continuum

namespace Work.Smooth.JordanSeparation

open Set

noncomputable section

/-- **Separation reformulated.**  For a closed `Z` inside the unit square `Q = [0,1] × [0,1]`
disjoint from the bottom edge `Btm = [0,1] × {0}` and the top edge `T0 = [0,1] × {1}`, the point
`(0,1)` fails to lie in the connected component of `(0,0)` in `Q \ Z` if and only if no preconnected
subset of `Q \ Z` meets both `Btm` and `T0`. -/
theorem separator_iff_no_preconnected {Z : Set (ℝ × ℝ)}
    (hB : Z ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({0} : Set ℝ)) = ∅)
    (hT : Z ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({1} : Set ℝ)) = ∅) :
    (∀ P : Set (ℝ × ℝ), P ⊆ (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) \ Z → IsPreconnected P →
        (P ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({0} : Set ℝ))).Nonempty →
        (P ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({1} : Set ℝ))).Nonempty → False)
      ↔ ((0, 1) : ℝ × ℝ) ∉
          connectedComponentIn ((Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) \ Z)
            ((0, 0) : ℝ × ℝ) := by
  set Q : Set (ℝ × ℝ) := Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 with hQ
  set Btm : Set (ℝ × ℝ) := Set.Icc (0:ℝ) 1 ×ˢ ({0} : Set ℝ) with hBtm
  set T0 : Set (ℝ × ℝ) := Set.Icc (0:ℝ) 1 ×ˢ ({1} : Set ℝ) with hT0
  have h00Btm : ((0,0) : ℝ × ℝ) ∈ Btm := ⟨⟨le_rfl, zero_le_one⟩, rfl⟩
  have h01T0 : ((0,1) : ℝ × ℝ) ∈ T0 := ⟨⟨le_rfl, zero_le_one⟩, rfl⟩
  have h00Q : ((0,0) : ℝ × ℝ) ∈ Q := ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩
  have h00Z : ((0,0) : ℝ × ℝ) ∉ Z :=
    fun hz => (Set.eq_empty_iff_forall_notMem.mp hB) _ ⟨hz, h00Btm⟩
  have hBtmQ : Btm ⊆ Q := by
    rintro p ⟨hp1, hp2⟩
    refine ⟨hp1, ?_⟩
    rw [Set.mem_singleton_iff] at hp2
    rw [hp2]; exact ⟨le_rfl, zero_le_one⟩
  have hT0Q : T0 ⊆ Q := by
    rintro p ⟨hp1, hp2⟩
    refine ⟨hp1, ?_⟩
    rw [Set.mem_singleton_iff] at hp2
    rw [hp2]; exact ⟨zero_le_one, le_rfl⟩
  have hBtmQZ : Btm ⊆ Q \ Z := by
    rintro p hp
    exact ⟨hBtmQ hp, fun hz => (Set.eq_empty_iff_forall_notMem.mp hB) p ⟨hz, hp⟩⟩
  have hT0QZ : T0 ⊆ Q \ Z := by
    rintro p hp
    exact ⟨hT0Q hp, fun hz => (Set.eq_empty_iff_forall_notMem.mp hT) p ⟨hz, hp⟩⟩
  have hBtmPre : IsPreconnected Btm :=
    ((convex_Icc (0:ℝ) 1).prod (convex_singleton (0:ℝ))).isPreconnected
  have hT0Pre : IsPreconnected T0 :=
    ((convex_Icc (0:ℝ) 1).prod (convex_singleton (1:ℝ))).isPreconnected
  have h00QZ : ((0,0) : ℝ × ℝ) ∈ Q \ Z := ⟨h00Q, h00Z⟩
  have hBtmA : Btm ⊆ connectedComponentIn (Q \ Z) ((0,0) : ℝ × ℝ) :=
    hBtmPre.subset_connectedComponentIn h00Btm hBtmQZ
  constructor
  · intro h hmem
    refine h (connectedComponentIn (Q \ Z) ((0,0) : ℝ × ℝ)) (connectedComponentIn_subset _ _)
      isPreconnected_connectedComponentIn ?_ ?_
    · exact ⟨(0,0), mem_connectedComponentIn h00QZ, h00Btm⟩
    · exact ⟨(0,1), hmem, h01T0⟩
  · intro hmem P hPsub hPpre hPB hPT
    obtain ⟨p, hpP, hpBtm⟩ := hPB
    obtain ⟨q, hqP, hqT0⟩ := hPT
    have hpA : p ∈ connectedComponentIn (Q \ Z) ((0,0) : ℝ × ℝ) := hBtmA hpBtm
    have hPsubA : P ⊆ connectedComponentIn (Q \ Z) ((0,0) : ℝ × ℝ) := by
      have h1 : P ⊆ connectedComponentIn (Q \ Z) p :=
        hPpre.subset_connectedComponentIn hpP hPsub
      rwa [(connectedComponentIn_eq hpA).symm] at h1
    have hqA : q ∈ connectedComponentIn (Q \ Z) ((0,0) : ℝ × ℝ) := hPsubA hqP
    have hT0A : T0 ⊆ connectedComponentIn (Q \ Z) ((0,0) : ℝ × ℝ) := by
      have h1 : T0 ⊆ connectedComponentIn (Q \ Z) q :=
        hT0Pre.subset_connectedComponentIn hqT0 hT0QZ
      rwa [(connectedComponentIn_eq hqA).symm] at h1
    exact hmem (hT0A h01T0)

/-- **The square cut lemma.** -/
theorem square_cut_lemma {Z : Set (ℝ × ℝ)} (hZc : IsClosed Z)
    (hZQ : Z ⊆ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1)
    (hB : Z ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({0} : Set ℝ)) = ∅)
    (hT : Z ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({1} : Set ℝ)) = ∅)
    (hsep : ((0, 1) : ℝ × ℝ) ∉ connectedComponentIn
        ((Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) \ Z) ((0, 0) : ℝ × ℝ)) :
    ∃ C : Set (ℝ × ℝ), C ⊆ Z ∧ IsPreconnected C ∧
      (C ∩ (({0} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1)).Nonempty ∧
      (C ∩ (({1} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1)).Nonempty := by
  have hsep' : ∀ P : Set (ℝ × ℝ), P ⊆ (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) \ Z →
      IsPreconnected P →
      (P ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({0} : Set ℝ))).Nonempty →
      (P ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({1} : Set ℝ))).Nonempty → False :=
    (separator_iff_no_preconnected hB hT).mpr hsep
  obtain ⟨K, hKZ, hKconn, hKL, hKR⟩ :=
    grid_spanning_continuum hZc hZQ hB hT hsep'
  exact ⟨K, hKZ, hKconn.isPreconnected, hKL, hKR⟩

end

end Work.Smooth.JordanSeparation
