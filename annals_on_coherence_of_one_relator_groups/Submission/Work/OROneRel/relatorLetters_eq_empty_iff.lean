import Mathlib
import Submission.Work.OROneRel.Basic

namespace Work.OROneRel

universe u

theorem relatorLetters_eq_empty_iff {α : Type u} (r : FreeGroup α) :
    Work.OROneRel.relatorLetters r = ∅ ↔ r = 1 := by
  classical
  constructor
  · intro h
    rw [← FreeGroup.toWord_eq_nil_iff, List.eq_nil_iff_forall_not_mem]
    intro p hp
    have : p.1 ∈ relatorLetters r := ⟨p.2, hp⟩
    rw [h] at this
    exact this
  · intro h
    subst h
    ext a
    simp [relatorLetters, FreeGroup.toWord_one]

end Work.OROneRel
