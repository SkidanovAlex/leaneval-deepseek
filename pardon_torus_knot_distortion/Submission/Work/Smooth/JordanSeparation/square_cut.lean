import Mathlib
import Submission.Work.Smooth.JordanSeparation.square_cut_lemma

/-!
# The square cut lemma

`Work.Smooth.JordanSeparation.square_cut` is the statement of
`Work.Smooth.JordanSeparation.square_cut_lemma` (proved in
`Submission/Work/Smooth/JordanSeparation/square_cut_lemma.lean`), restated here for the use of
`Submission/Work/Smooth/JordanSeparation/square_lemma_aux.lean`.
-/

open Set

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- **The square cut lemma.** -/
theorem square_cut {Z : Set (ℝ × ℝ)} (hZc : IsClosed Z)
    (hZQ : Z ⊆ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1)
    (hB : Z ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({0} : Set ℝ)) = ∅)
    (hT : Z ∩ (Set.Icc (0:ℝ) 1 ×ˢ ({1} : Set ℝ)) = ∅)
    (hsep : ((0, 1) : ℝ × ℝ) ∉ connectedComponentIn
        ((Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) \ Z) ((0, 0) : ℝ × ℝ)) :
    ∃ C : Set (ℝ × ℝ), C ⊆ Z ∧ IsPreconnected C ∧
      (C ∩ (({0} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1)).Nonempty ∧
      (C ∩ (({1} : Set ℝ) ×ˢ Set.Icc (0:ℝ) 1)).Nonempty :=
  square_cut_lemma hZc hZQ hB hT hsep

end

end Work.Smooth.JordanSeparation
