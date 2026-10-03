import Mathlib
import Submission.Work.OROneRel.psiSubstDefs

namespace Work.OROneRel

/-- `nonTLetters t r` counts the letters of the reduced word of `r` different from `t`; since `t`
occurs in that word, this count is strictly smaller than the word length, i.e. than the norm of
`r`. -/
theorem nonTLetters_lt_norm {α : Type*} (r : FreeGroup α) (t : α)
    (ht : t ∈ Work.OROneRel.relatorLetters r) :
    Work.OROneRel.nonTLetters t r < Work.OROneRel.relatorNorm r := by
  classical
  obtain ⟨b, hb⟩ : ∃ b : Bool, (t, b) ∈ FreeGroup.toWord r := by
    simpa [Work.OROneRel.relatorLetters] using ht
  have hlt : (FreeGroup.toWord r).countP (fun p : α × Bool => decide (p.1 ≠ t)) <
      (FreeGroup.toWord r).length :=
    List.countP_lt_length_iff.mpr ⟨(t, b), hb, by simp⟩
  simpa [Work.OROneRel.nonTLetters, Work.OROneRel.relatorNorm, FreeGroup.norm] using hlt

end Work.OROneRel
