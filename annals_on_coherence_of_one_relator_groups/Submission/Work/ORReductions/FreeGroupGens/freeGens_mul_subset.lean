import Mathlib
import Submission.Work.ORReductions.Basic

open List

namespace Work.ORReductions.FreeGroupGens

/-- `FreeGroup.gens (x * y)` is contained in `FreeGroup.gens x ∪ FreeGroup.gens y`.

The word representing `x * y` is the reduction of `x.toWord ++ y.toWord`, hence a sublist of
that concatenation; a single letter occurring in the concatenation occurs in one of the two
factors. -/
theorem freeGens_mul_subset {α : Type*} (x y : FreeGroup α) :
    FreeGroup.gens (x * y) ⊆ FreeGroup.gens x ∪ FreeGroup.gens y := by
  classical
  intro a ha
  simp only [FreeGroup.gens, Set.mem_union] at ha ⊢
  have key : ∀ b : Bool, [(a, b)] <+ (x * y).toWord →
      ([(a, true)] <+ x.toWord ∨ [(a, false)] <+ x.toWord) ∨
      ([(a, true)] <+ y.toWord ∨ [(a, false)] <+ y.toWord) := by
    intro b h
    have h₁ : [(a, b)] <+ x.toWord ++ y.toWord :=
      h.trans (FreeGroup.toWord_mul_sublist x y)
    have h₂ : [(a, b)] <+ x.toWord ∨ [(a, b)] <+ y.toWord := by
      simpa only [List.singleton_sublist, List.mem_append] using h₁
    rcases h₂ with h₂ | h₂
    · cases b
      · exact Or.inl (Or.inr h₂)
      · exact Or.inl (Or.inl h₂)
    · cases b
      · exact Or.inr (Or.inr h₂)
      · exact Or.inr (Or.inl h₂)
  rcases ha with h | h
  · exact key true h
  · exact key false h

end Work.ORReductions.FreeGroupGens
