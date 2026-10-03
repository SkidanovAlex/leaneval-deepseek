import Mathlib
import Submission.Work.OROneRel.Basic

namespace Work.OROneRel

universe u

/-- The length of a power of a single generator: `|a ^ m| = |m|`. -/
theorem norm_freeGroup_of_zpow {α : Type u} [DecidableEq α] (a : α) (m : ℤ) :
    FreeGroup.norm ((FreeGroup.of a : FreeGroup α) ^ m) = m.natAbs := by
  rcases m with n | n
  · change FreeGroup.norm ((FreeGroup.of a : FreeGroup α) ^ (n : ℤ)) = ((n : ℤ)).natAbs
    rw [zpow_natCast, FreeGroup.norm_of_pow, Int.natAbs_natCast]
  · rw [zpow_negSucc, FreeGroup.norm_inv_eq, FreeGroup.norm_of_pow, Int.natAbs_negSucc]

theorem relatorNorm_of_zpow {α : Type u} (a : α) (m : ℤ) :
    Work.OROneRel.relatorNorm (FreeGroup.of a ^ m) = m.natAbs := by
  classical
  have h : Work.OROneRel.relatorNorm (FreeGroup.of a ^ m) = FreeGroup.norm (FreeGroup.of a ^ m) :=
    rfl
  rw [h, norm_freeGroup_of_zpow]

end Work.OROneRel
