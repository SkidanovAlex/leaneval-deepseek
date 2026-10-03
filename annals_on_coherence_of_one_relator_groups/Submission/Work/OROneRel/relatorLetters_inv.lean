import Mathlib
import Submission.Work.OROneRel.Basic

namespace Work.OROneRel

universe u

/-- `FreeGroup.invRev` reverses a word and flips every exponent bit, so it preserves the *set* of
generators occurring in the word: the existential quantification over the `Bool` component makes
the flipped bits irrelevant. -/
lemma exists_mem_invRev {β : Type*} (a : β) (w : List (β × Bool)) :
    (∃ b, (a, b) ∈ FreeGroup.invRev w) ↔ ∃ b, (a, b) ∈ w := by
  simp only [FreeGroup.invRev, List.mem_reverse, List.mem_map]
  constructor
  · rintro ⟨b, g, hg, hgb⟩
    refine ⟨g.2, ?_⟩
    have h1 : g.1 = a := by
      have := congrArg Prod.fst hgb
      simpa using this
    have : g = (a, g.2) := by cases g; simp_all
    rwa [this] at hg
  · rintro ⟨b, hb⟩
    exact ⟨!b, (a, b), hb, rfl⟩

/-- Inverting a free-group element does not change the set of generators occurring in it. -/
theorem relatorLetters_inv {α : Type u} (r : FreeGroup α) :
    Work.OROneRel.relatorLetters r⁻¹ = Work.OROneRel.relatorLetters r := by
  classical
  unfold relatorLetters
  ext a
  simp only [Set.mem_ofPred_eq]
  rw [FreeGroup.toWord_inv]
  exact exists_mem_invRev a (FreeGroup.toWord r)

end Work.OROneRel
