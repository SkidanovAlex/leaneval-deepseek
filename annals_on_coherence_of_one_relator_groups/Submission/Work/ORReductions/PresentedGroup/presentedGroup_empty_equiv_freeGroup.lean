import Mathlib
import Submission.Work.ORReductions.Basic

namespace Work.ORReductions.PresentedGroup

/-- The presented group on no relations is the free group: `PresentedGroup ∅ ≅* FreeGroup α`. -/
theorem presentedGroup_empty_equiv_freeGroup {α : Type*} :
    Nonempty (PresentedGroup (∅ : Set (FreeGroup α)) ≃* FreeGroup α) := by
  refine ⟨?_⟩
  exact (QuotientGroup.quotientMulEquivOfEq (Subgroup.normalClosure_empty)).trans
    QuotientGroup.quotientBot

end Work.ORReductions.PresentedGroup
