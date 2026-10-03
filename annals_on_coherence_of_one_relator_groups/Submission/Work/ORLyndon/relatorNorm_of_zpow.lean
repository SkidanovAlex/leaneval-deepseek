import Mathlib
import Submission.Work.OROneRel.Basic

/-!
# The relator norm of a power of a single generator

For a symbol `a` and an integer `s`, the reduced length of the word `of a ^ s` is `|s|`: the word
of `of a ^ s` is the reduced word consisting of `|s|` copies of the letter `a` (inverted when
`s < 0`), and no cancellation can occur.  In the vocabulary of the one-relator combinatorics
(`Submission.Work.OROneRel.Basic`) this reads `relatorNorm (of a ^ s) = s.natAbs`, which is the
length of the terminal relator `of a ^ s` -- the relator of the `ℤ/|s|` factor at the end of a
Magnus--Moldavanskii hierarchy.
-/

namespace Work.ORLyndon

/-- The reduced length of a power of a single generator is the absolute value of the exponent. -/
theorem norm_freeGroup_of_zpow {α : Type*} [DecidableEq α] (a : α) (s : ℤ) :
    FreeGroup.norm ((FreeGroup.of a : FreeGroup α) ^ s) = s.natAbs := by
  rcases s with n | n
  · change FreeGroup.norm ((FreeGroup.of a : FreeGroup α) ^ (n : ℤ)) = ((n : ℤ)).natAbs
    rw [zpow_natCast, FreeGroup.norm_of_pow, Int.natAbs_natCast]
  · rw [zpow_negSucc, FreeGroup.norm_inv_eq, FreeGroup.norm_of_pow, Int.natAbs_negSucc]

theorem relatorNorm_of_zpow {α : Type*} (a : α) (s : ℤ) :
    Work.OROneRel.relatorNorm (FreeGroup.of a ^ s) = s.natAbs := by
  classical
  have h : Work.OROneRel.relatorNorm (FreeGroup.of a ^ s)
      = FreeGroup.norm (FreeGroup.of a ^ s) := rfl
  rw [h]
  exact norm_freeGroup_of_zpow a s

end Work.ORLyndon
