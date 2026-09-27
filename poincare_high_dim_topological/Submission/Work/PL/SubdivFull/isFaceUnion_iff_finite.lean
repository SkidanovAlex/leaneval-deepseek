import Mathlib
import Submission.Work.PL.SubdivFull.Defs

namespace Work.PL.SubdivFull

theorem isFaceUnion_iff_finite {N : ℕ} {K : PL.Cx N} (hK : K.faces.Finite) {L : Set (PL.E N)} :
    IsFaceUnion K L ↔ ∃ T : Finset (Finset (PL.E N)), (∀ t ∈ T, t ∈ K.faces) ∧
      L = ⋃ t ∈ T, PL.simp t := by
  constructor
  · intro h
    obtain ⟨T, hT, hL⟩ := (isFaceUnion_iff K L).mp h
    have hTfin : T.Finite := hK.subset hT
    refine ⟨hTfin.toFinset, ?_, ?_⟩
    · intro t ht
      exact hT (hTfin.mem_toFinset.mp ht)
    · rw [hL]
      ext x
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨s, hs, hx⟩
        exact ⟨s, hTfin.mem_toFinset.mpr hs, hx⟩
      · rintro ⟨s, hs, hx⟩
        exact ⟨s, hTfin.mem_toFinset.mp hs, hx⟩
  · rintro ⟨T, hT, rfl⟩
    exact isFaceUnion_of_finset_faces hT

end Work.PL.SubdivFull
