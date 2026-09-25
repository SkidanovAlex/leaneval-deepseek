import Mathlib
import Submission.Work.ProPDeficiency.Basic

namespace Work.ProPDeficiency

-- File: Submission/Work/ProPDeficiency/isPresentation_of_groupPresentation.lean, namespace `Work.ProPDeficiency`.
-- Bridge from Mathlib's data-carrying `Group.Presentation G ι` (whose `rel : Set (FreeGroup ι)` is a
-- set of relators, with `lift_ker_eq_normalClosure`) to the finite-relator presentation predicate
-- `IsPresentation ι rel G` of `Submission.Work.ProPDeficiency.Basic`
-- (`IsPresentation α rel G := Nonempty (G ≃* FreeGroup α ⧸ Subgroup.normalClosure (rel : Set _))`).
-- Mathlib's `PresentedGroup P.rel` is *definitionally* `FreeGroup ι ⧸ normalClosure P.rel`, and
-- `Group.Presentation.presentedGroupEquiv : PresentedGroup P.rel ≃* G`, so for a finite relator set
-- the transport is bookkeeping: take `rel := hrel.toFinset` (with `Set.Finite.coe_toFinset`) and
-- rewrite the normal closure, e.g. through `QuotientGroup.quotientMulEquivOfEq`; a working body is
-- `refine ⟨hrel.toFinset, rfl, ?_⟩; refine ⟨P.presentedGroupEquiv.symm.trans ?_⟩;
--  exact QuotientGroup.quotientMulEquivOfEq (congrArg Subgroup.normalClosure hrel.coe_toFinset.symm)`.
theorem isPresentation_of_groupPresentation {G ι : Type} [Group G] [Fintype ι]
    (P : Group.Presentation G ι) (hrel : P.rel.Finite) :
    ∃ rel : Finset (FreeGroup ι), rel.card = hrel.toFinset.card ∧ IsPresentation ι rel G := by
  refine ⟨hrel.toFinset, rfl, ?_⟩
  refine ⟨P.presentedGroupEquiv.symm.trans ?_⟩
  exact QuotientGroup.quotientMulEquivOfEq (congrArg Subgroup.normalClosure hrel.coe_toFinset.symm)

end Work.ProPDeficiency
