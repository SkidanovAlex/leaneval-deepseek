import Mathlib
import Submission.Work.ORReductions.Basic

namespace Work.ORReductions.PresentedGroup

theorem freeGroupCongr_singleton_image {α β : Type*} (rel : FreeGroup α) (e : α ≃ β) :
    FreeGroup.freeGroupCongr e '' ({rel} : Set (FreeGroup α)) =
      ({FreeGroup.map (e : α → β) rel} : Set (FreeGroup β)) := by
  rw [Set.image_singleton]
  rfl

theorem presentedGroup_single_equiv {α β : Type*} (rel : FreeGroup α) (e : α ≃ β) :
    Nonempty (PresentedGroup ({rel} : Set (FreeGroup α)) ≃*
      PresentedGroup ({FreeGroup.map (e : α → β) rel} : Set (FreeGroup β))) := by
  rw [← freeGroupCongr_singleton_image rel e]
  exact ⟨PresentedGroup.equivPresentedGroup {rel} e⟩

end Work.ORReductions.PresentedGroup
