import Mathlib
import Submission.Work.OROneRel.Basic

namespace Work.OROneRel

universe u

theorem relatorLetters_pow_subset {α : Type u} (r : FreeGroup α) (n : ℕ) :
    Work.OROneRel.relatorLetters (r ^ n) ⊆ Work.OROneRel.relatorLetters r := by
  classical
  induction n with
  | zero =>
    rw [pow_zero]
    intro a ha
    exact absurd ha (by simp [relatorLetters, FreeGroup.toWord_one])
  | succ n ih =>
    rw [pow_succ]
    intro a ha
    obtain ⟨b, hb⟩ := ha
    rcases List.mem_append.mp (FreeGroup.toWord_mul_sublist (r ^ n) r |>.subset hb) with h | h
    · exact ih ⟨b, h⟩
    · exact ⟨b, h⟩

end Work.OROneRel
