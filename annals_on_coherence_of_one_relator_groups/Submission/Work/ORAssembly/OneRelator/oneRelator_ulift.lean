import Mathlib
import Submission.Work.ORReductions.API

/-!
# One-relator groups are closed under universe lifting

If `G` is a one-relator group in universe `u`, then `ULift.{w} G`, which lives in the universe
`max u w`, is again one-relator.  The point is that the *type of generators* of a one-relator
presentation can be transported along the bijection `α ≃ ULift.{w} α`, which puts a presentation of
`G` into the larger universe: Mathlib's `PresentedGroup.equivPresentedGroup` identifies
`PresentedGroup {rel}` with `PresentedGroup {FreeGroup.freeGroupCongr e rel}` for `e : α ≃ β`, and
for a singleton set the image is again a singleton.
-/

-- The universe variables used below.  (`autoImplicit` is off in this workspace, so they have to be
-- declared explicitly; this does not change the statements.)
universe u v w

namespace Work.ORAssembly.OneRelator

/-- If `rel : FreeGroup α` and `e : α ≃ β`, then presenting with the single relator `rel` is the
same as presenting with the single relator `FreeGroup.freeGroupCongr e rel`.  This is the singleton
case of `PresentedGroup.equivPresentedGroup`, with the image of the singleton set made explicit. -/
theorem presentedGroup_singleton_freeGroupCongr {α : Type u} {β : Type v} (e : α ≃ β)
    (rel : FreeGroup α) :
    Nonempty (PresentedGroup {FreeGroup.freeGroupCongr e rel} ≃* PresentedGroup {rel}) :=
  ⟨(Set.image_singleton (f := ⇑(FreeGroup.freeGroupCongr e)) (a := rel)) ▸
    (PresentedGroup.equivPresentedGroup ({rel} : Set (FreeGroup α)) e).symm⟩

/-- **Universe lifting**: a group is one-relator iff its `ULift` is. -/
theorem oneRelator_ulift {G : Type u} [Group G] (h : Group.OneRelator G) :
    Group.OneRelator (ULift.{w} G) := by
  obtain ⟨α, rel, ⟨e⟩⟩ := h
  -- Transport the presentation along the bijection `α ≃ ULift.{w} α`.
  refine ⟨ULift.{w} α, FreeGroup.freeGroupCongr (Equiv.ulift.symm : α ≃ ULift.{w} α) rel, ?_⟩
  obtain ⟨f⟩ := presentedGroup_singleton_freeGroupCongr (Equiv.ulift.symm : α ≃ ULift.{w} α) rel
  exact ⟨f.trans (e.trans (MulEquiv.ulift.symm : G ≃* ULift.{w} G))⟩

end Work.ORAssembly.OneRelator
