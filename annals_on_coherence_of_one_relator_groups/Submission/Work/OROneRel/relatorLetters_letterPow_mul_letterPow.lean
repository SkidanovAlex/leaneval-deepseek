import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.relatorLetters_mul_subset
import Submission.Work.OROneRel.relatorLetters_pow_subset
import Submission.Work.OROneRel.relatorLetters_of_zpow

namespace Work.OROneRel

/-- The letters of a power `(of a) ^ p` of a single generator lie in `{a}`, for every `p : ℕ`
(including `p = 0`, where the power is `1` and the letter set is empty). -/
theorem relatorLetters_of_pow_subset {α : Type*} (a : α) (p : ℕ) :
    Work.OROneRel.relatorLetters ((FreeGroup.of a) ^ p) ⊆ ({a} : Set α) := by
  refine (relatorLetters_pow_subset (FreeGroup.of a) p).trans ?_
  have h : FreeGroup.of a = FreeGroup.of a ^ (1 : ℤ) := (zpow_one _).symm
  rw [h, relatorLetters_of_zpow a 1 (by norm_num)]

theorem relatorLetters_letterPow_mul_letterPow {α : Type*} {a b : α} (hab : a ≠ b) (p q : ℕ) :
    Work.OROneRel.relatorLetters ((FreeGroup.of a)^p * (FreeGroup.of b)^q) ⊆ {a, b} := by
  classical
  intro c hc
  rcases relatorLetters_mul_subset ((FreeGroup.of a) ^ p) ((FreeGroup.of b) ^ q) hc with h | h
  · have hc'a : c = a := by
      have := relatorLetters_of_pow_subset a p h
      simpa using this
    subst hc'a
    simp
  · have hc'b : c = b := by
      have := relatorLetters_of_pow_subset b q h
      simpa using this
    subst hc'b
    simp

end Work.OROneRel
