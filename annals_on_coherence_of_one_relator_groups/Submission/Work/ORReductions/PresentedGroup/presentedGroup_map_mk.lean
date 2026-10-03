import Mathlib
import Submission.Work.ORReductions.Basic

namespace Work.ORReductions.PresentedGroup

/-- `PresentedGroup.map` is the induced map of `QuotientGroup.map` on normal closures, and
`PresentedGroup.mk` is `QuotientGroup.mk'`; hence the two sides are definitionally equal. -/
theorem presentedGroup_map_mk {α β : Type*} (f : FreeGroup α →* FreeGroup β) {s : Set (FreeGroup α)}
    {t : Set (FreeGroup β)} (h : Set.MapsTo f s t) (x : FreeGroup α) :
    PresentedGroup.map f h (PresentedGroup.mk s x) = PresentedGroup.mk t (f x) := by
  rfl

end Work.ORReductions.PresentedGroup
