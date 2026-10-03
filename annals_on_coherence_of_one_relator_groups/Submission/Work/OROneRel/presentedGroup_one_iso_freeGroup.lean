import Mathlib
import Submission.Work.OROneRel.Basic

namespace Work.OROneRel

universe u

/-- The normal closure of `{1}` is trivial. -/
theorem normalClosure_singleton_one_eq_bot {α : Type u} :
    Subgroup.normalClosure ({1} : Set (FreeGroup α)) = ⊥ :=
  Subgroup.normalClosure_eq_bot_iff.mpr (by intro x hx; simpa using hx)

theorem presentedGroup_one_iso_freeGroup {α : Type u} :
    Nonempty (PresentedGroup ({1} : Set (FreeGroup α)) ≃* FreeGroup α) := by
  have h := normalClosure_singleton_one_eq_bot (α := α)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot⟩

end Work.OROneRel
