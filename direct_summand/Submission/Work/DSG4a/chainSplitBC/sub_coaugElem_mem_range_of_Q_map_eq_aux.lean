import Mathlib
import Submission.Work.DSG4a.sub_coaugElem_mem_range_of_Q_map_eq

namespace Work.DSG4a.chainSplitBC

open CategoryTheory AlgebraicGeometry Limits
open scoped ChangeOfRings TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
universe u

/-- **The auxiliary form of `sub_coaugElem_mem_range_of_Q_map_eq`**: the K-projectivity of `P`
is not needed, because the argument only uses the K-projectivity of the *source* `A[0]`. -/
theorem sub_coaugElem_mem_range_of_Q_map_eq_aux {A : Type u} [CommRing A]
    [HasDerivedCategory (ModuleCat.{u} A)] (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (cc cc' : Work.DSG4a.singleZ A ⟶ P)
    (h : DerivedCategory.Q.map cc = DerivedCategory.Q.map cc') :
    Work.DSG4a.Criterion.coaugElem P cc - Work.DSG4a.Criterion.coaugElem P cc' ∈
      LinearMap.range (P.d (-1) 0).hom := by
  -- `A[0]` is K-projective, so the localization out of it is injective on homotopy classes.
  haveI : CochainComplex.IsKProjective (Work.DSG4a.singleZ A) := Work.DSEQ0.singleZ_isKProjective
  -- hence `cc` and `cc'` have the same image in the homotopy category ...
  have hB : (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map cc =
      (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map cc' := by
    apply (CochainComplex.IsKProjective.Qh_map_bijective (Work.DSG4a.singleZ A)
      ((HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).obj P)).injective
    refine (cancel_mono ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).hom.app P)).mp ?_
    rw [DerivedCategory.quotientCompQhIso_hom_naturality cc,
      DerivedCategory.quotientCompQhIso_hom_naturality cc', h]
  -- ... and therefore are homotopic.
  let H := HomotopyCategory.homotopyOfEq cc cc' hB
  -- In degree `0` the homotopy relation reads
  -- `cc.f 0 = dNext 0 + prevD 0 + cc'.f 0` where `dNext 0 = (A[0]).d 0 1 ≫ − = 0`
  -- (the source is concentrated in degree `0`) and `prevD 0 = H.hom 0 (-1) ≫ P.d (-1) 0`.
  have hrel : cc.f 0 - cc'.f 0 = H.hom 0 (-1) ≫ P.d (-1) 0 := by
    have Hcomm := H.comm 0
    have hd : dNext (0:ℤ) H.hom = 0 := by
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (0:ℤ) 1 from by
        rw [ComplexShape.up_Rel]; norm_num)]
      simp [HomologicalComplex.single_obj_d]
    have hp : prevD (0:ℤ) H.hom = H.hom 0 (-1) ≫ P.d (-1) 0 := by
      rw [prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1:ℤ) 0 from by
        rw [ComplexShape.up_Rel]; norm_num)]
    rw [hd, hp] at Hcomm
    rw [sub_eq_iff_eq_add]
    simpa using Hcomm
  -- Unfolding `coaugElem` as the image of the unit under `cc.f 0`.
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)
  have hcc : Work.DSG4a.Criterion.coaugElem P cc = (cc.f 0).hom ((e.inv).hom 1) := by
    rw [Work.DSG4a.Criterion.coaugElem, ModuleCat.hom_comp]
    rfl
  have hcc' : Work.DSG4a.Criterion.coaugElem P cc' = (cc'.f 0).hom ((e.inv).hom 1) := by
    rw [Work.DSG4a.Criterion.coaugElem, ModuleCat.hom_comp]
    rfl
  have key : ((cc.f 0).hom - (cc'.f 0).hom) ((e.inv).hom 1)
      = (P.d (-1) 0).hom ((H.hom 0 (-1)).hom ((e.inv).hom 1)) := by
    have h1 := congrArg ModuleCat.Hom.hom hrel
    rw [ModuleCat.hom_sub, ModuleCat.hom_comp] at h1
    rw [h1, LinearMap.comp_apply]
  refine LinearMap.mem_range.mpr ⟨(H.hom 0 (-1)).hom ((e.inv).hom 1), ?_⟩
  rw [hcc, hcc']
  exact key.symm

end Work.DSG4a.chainSplitBC
