import Mathlib
import Submission.Work.OROneRel.Basic

namespace Work.OROneRel

universe u

/-- The generators occurring in a product `r * s` occur in `r` or in `s`.

The reduced word of `r * s` is a sublist of the concatenation of the reduced words of `r` and `s`
(`FreeGroup.toWord_mul_sublist`), and reducing a word only deletes pairs of letters. -/
theorem relatorLetters_mul_subset {α : Type u} (r s : FreeGroup α) :
    Work.OROneRel.relatorLetters (r * s) ⊆
      Work.OROneRel.relatorLetters r ∪ Work.OROneRel.relatorLetters s := by
  classical
  intro a ha
  simp only [relatorLetters, Set.mem_ofPred_eq] at ha ⊢
  obtain ⟨b, hb⟩ := ha
  have hsub : (r * s).toWord.Sublist (r.toWord ++ s.toWord) := FreeGroup.toWord_mul_sublist r s
  rcases List.mem_append.mp (hsub.subset hb) with h | h
  · exact Or.inl ⟨b, h⟩
  · exact Or.inr ⟨b, h⟩

end Work.OROneRel
