import Mathlib
import Submission.Work.ORReductions.Basic

namespace Work.ORReductions.PresentedGroup

/-- Two presentations of the same group by *equal* sets of relations are canonically isomorphic.
This is the `PresentedGroup`-instance of `QuotientGroup.quotientMulEquivOfEq`. -/
noncomputable def presentedGroupOfRelEq {α : Type*} {s t : Set (FreeGroup α)} (h : s = t) :
    PresentedGroup s ≃* PresentedGroup t :=
  QuotientGroup.quotientMulEquivOfEq (congrArg Subgroup.normalClosure h)

/-- The group presented by no relations is the free group. -/
noncomputable def presentedGroupEmptyMulEquivFreeGroup (γ : Type*) :
    PresentedGroup (∅ : Set (FreeGroup γ)) ≃* FreeGroup γ :=
  (QuotientGroup.quotientMulEquivOfEq
    (Subgroup.normalClosure_empty : Subgroup.normalClosure (∅ : Set (FreeGroup γ)) = ⊥)).trans
    QuotientGroup.quotientBot

theorem presentedGroup_coprod_single {α : Type*} (r : FreeGroup α) (γ : Type*) :
    Nonempty (PresentedGroup ({FreeGroup.map Sum.inl r} : Set (FreeGroup (α ⊕ γ))) ≃*
      Monoid.Coprod (PresentedGroup ({r} : Set (FreeGroup α))) (FreeGroup γ)) := by
  have h : (FreeGroup.map Sum.inl '' ({r} : Set (FreeGroup α))
      ∪ FreeGroup.map Sum.inr '' (∅ : Set (FreeGroup γ)))
      = ({FreeGroup.map Sum.inl r} : Set (FreeGroup (α ⊕ γ))) := by
    simp
  refine ⟨(presentedGroupOfRelEq h).symm.trans
    ((PresentedGroup.coprodPresentations ({r} : Set (FreeGroup α)) (∅ : Set (FreeGroup γ))).trans
      (MulEquiv.coprodCongr (MulEquiv.refl (PresentedGroup ({r} : Set (FreeGroup α))))
        (presentedGroupEmptyMulEquivFreeGroup γ)))⟩

end Work.ORReductions.PresentedGroup
