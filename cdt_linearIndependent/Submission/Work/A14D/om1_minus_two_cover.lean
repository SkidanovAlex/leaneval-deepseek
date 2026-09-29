import Mathlib
import Submission.Work.A14D.su_om1_pieces

namespace Work.A14D

theorem om1_minus_two_cover :
    (∀ z : ℂ, z ∈ Work.A14D.Om1 \ ({2} : Set ℂ) →
      z ∈ Work.A14D.pieceU ∨ z ∈ Work.A14D.pieceD ∨ z ∈ Work.A14D.piece1 ∨ z ∈ Work.A14D.piece2) ∧
    Work.A14D.pieceU ∩ Work.A14D.pieceD = ∅ ∧ Work.A14D.piece1 ∩ Work.A14D.piece2 = ∅ := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨hzO, hz2⟩ := hz
    simp only [Set.mem_singleton_iff] at hz2
    simp only [Work.A14D.Om1, Work.A14D.pieceU, Work.A14D.pieceD, Work.A14D.piece1,
      Work.A14D.piece2, Set.mem_ofPred_eq] at hzO ⊢
    rcases lt_trichotomy z.im 0 with h | h | h
    · exact Or.inr (Or.inl h)
    · have hre : 1 < z.re := by
        rcases hzO with h' | h'
        · exact absurd h h'
        · exact h'
      rcases lt_trichotomy z.re 2 with h2 | h2 | h2
      · exact Or.inr (Or.inr (Or.inl ⟨hre, h2⟩))
      · exact absurd (Complex.ext (by simpa using h2) (by simpa using h)) hz2
      · exact Or.inr (Or.inr (Or.inr h2))
    · exact Or.inl h
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨h1, h2⟩ := hz
    simp only [Work.A14D.pieceU, Work.A14D.pieceD, Set.mem_ofPred_eq] at h1 h2
    exact absurd h1 (not_lt.mpr h2.le)
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨h1, h2⟩ := hz
    simp only [Work.A14D.piece1, Work.A14D.piece2, Set.mem_ofPred_eq] at h1 h2
    exact absurd h1.2 (not_lt.mpr h2.le)

end Work.A14D
