import Mathlib
import Submission.Work.Motivic.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Motivic

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

/-!
# The rational map of a composite of partial isomorphisms

Auxiliary computations about `PartialIso.restrictSource`, `PartialIso.restrictTarget` and
`PartialIso.trans'`, used to show that `PartialIso.toRationalMap` is compatible with
`PartialIso.trans`.
-/

section Aux

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restricting the source of a partial isomorphism does not change its rational map. -/
lemma restrictSource_toRationalMap {X Y : Scheme.{0}} (f : X.PartialIso Y) (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U ≤ f.source) :
    (f.restrictSource U hU hU').toRationalMap = f.toRationalMap := by
  have hhom : (f.restrictSource U hU hU').toPartialMap.hom =
      X.homOfLE hU' ≫ f.iso.hom ≫ f.target.ι := by
    dsimp only [Scheme.PartialIso.restrictSource]
    rw [Scheme.PartialIso.toPartialMap_hom]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Scheme.Hom.isoImage_hom_ι]
    rw [Scheme.Hom.isoImage_hom_ι_assoc]
    have h : (Opens.isoOfLE hU').inv ≫ (f.source.ι ⁻¹ᵁ U).ι = X.homOfLE hU' := by
      rw [← cancel_mono f.source.ι, Category.assoc]
      rw [Scheme.Opens.isoOfLE_inv_ι, Scheme.homOfLE_ι]
    conv_lhs => rw [← Category.assoc]
    rw [h]
  change (f.restrictSource U hU hU').toPartialMap.toRationalMap = f.toPartialMap.toRationalMap
  rw [← Scheme.PartialMap.restrict_toRationalMap f.toPartialMap U hU hU',
    Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨U, hU, le_rfl, le_rfl, ?_⟩
  rw [Scheme.PartialMap.restrict_hom, Scheme.PartialMap.restrict_hom, Scheme.homOfLE_rfl,
    Category.id_comp, hhom]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restricting the target of a partial isomorphism does not change its rational map. -/
lemma restrictTarget_toRationalMap {X Y : Scheme.{0}} (f : X.PartialIso Y) (U : Y.Opens)
    (hU : Dense (U : Set Y)) (hU' : U ≤ f.target) :
    (f.restrictTarget U hU hU').toRationalMap = f.toRationalMap := by
  have hhom : (f.restrictTarget U hU hU').toPartialMap.hom =
      X.homOfLE (f.source.ι_image_le (f.iso.inv ''ᵁ (f.target.ι ⁻¹ᵁ U))) ≫
        f.iso.hom ≫ f.target.ι := by
    dsimp only [Scheme.PartialIso.restrictTarget, Scheme.PartialIso.symm,
      Scheme.PartialIso.restrictSource]
    rw [Scheme.PartialIso.toPartialMap_hom]
    simp only [Iso.trans_inv, Iso.symm_inv, Iso.symm_hom, Category.assoc]
    rw [Scheme.Opens.isoOfLE_hom_ι]
    have hW : (f.iso.inv.isoImage (f.target.ι ⁻¹ᵁ U)).inv ≫
          ((f.target.ι ⁻¹ᵁ U).ι ≫ f.target.ι) =
        (f.iso.inv ''ᵁ (f.target.ι ⁻¹ᵁ U)).ι ≫ (f.iso.hom ≫ f.target.ι) := by
      have h' : (f.iso.inv.isoImage (f.target.ι ⁻¹ᵁ U)).inv ≫ (f.target.ι ⁻¹ᵁ U).ι =
          (f.iso.inv ''ᵁ (f.target.ι ⁻¹ᵁ U)).ι ≫ f.iso.hom := by
        simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
          congrArg (· ≫ f.iso.hom) (Scheme.Hom.isoImage_inv_ι (f.iso.inv) (f.target.ι ⁻¹ᵁ U))
      simpa only [Category.assoc] using congrArg (· ≫ f.target.ι) h'
    rw [hW, Scheme.Opens.isoImage_ι_inv_ι_assoc]
  change (f.restrictTarget U hU hU').toPartialMap.toRationalMap = f.toPartialMap.toRationalMap
  rw [Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨(f.restrictTarget U hU hU').toPartialMap.domain,
    (f.restrictTarget U hU hU').toPartialMap.dense_domain, le_rfl,
    f.source.ι_image_le (f.iso.inv ''ᵁ (f.target.ι ⁻¹ᵁ U)), ?_⟩
  rw [Scheme.PartialMap.restrict_hom, Scheme.PartialMap.restrict_hom, Scheme.homOfLE_rfl,
    Category.id_comp, hhom]
  rfl

end Aux

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The composite of partial isomorphisms along an equality `f.target = g.source` has the
composite underlying partial map. -/
private theorem transPrime_toPartialMap_equiv_aux {X Y Z : Scheme.{0}} [PreirreducibleSpace X]
    [Nonempty Y] (f : X.PartialIso Y) (g : Y.PartialIso Z) (e : f.target = g.source) :
    (f.trans' g e).toPartialMap.equiv (f.toPartialMap.comp g.toPartialMap) := by
  have hhom : X.homOfLE (f.source.ι_image_le ((f.iso.hom ≫ f.target.ι) ⁻¹ᵁ g.source)) ≫
      (f.trans' g e).toPartialMap.hom = (f.toPartialMap.comp g.toPartialMap).hom := by
    dsimp only [Scheme.PartialIso.trans', Scheme.PartialIso.toPartialMap]
    rw [Scheme.PartialMap.comp_hom]
    simp only [Iso.trans_hom, Category.assoc]
    rw [← Opens.isoImage_ι_inv_ι (f.source) ((f.iso.hom ≫ f.target.ι) ⁻¹ᵁ g.source)]
    rw [Category.assoc, cancel_epi, morphismRestrict_comp]
    have hAM : (f.target.ι ⁻¹ᵁ g.source).ι ≫ (Y.isoOfEq e).hom = (f.target.ι ∣_ g.source) := by
      rw [← cancel_mono g.source.ι, Category.assoc, Scheme.isoOfEq_hom_ι, morphismRestrict_ι]
    change ((f.iso.hom ⁻¹ᵁ (f.target.ι ⁻¹ᵁ g.source)).ι) ≫ f.iso.hom ≫ (Y.isoOfEq e).hom ≫
        g.iso.hom ≫ g.target.ι =
      (f.iso.hom ∣_ (f.target.ι ⁻¹ᵁ g.source)) ≫ (f.target.ι ∣_ g.source) ≫ g.iso.hom ≫ g.target.ι
    calc ((f.iso.hom ⁻¹ᵁ (f.target.ι ⁻¹ᵁ g.source)).ι ≫ f.iso.hom ≫ (Y.isoOfEq e).hom ≫
            g.iso.hom ≫ g.target.ι)
        = (((f.iso.hom ⁻¹ᵁ (f.target.ι ⁻¹ᵁ g.source)).ι ≫ f.iso.hom) ≫
            ((Y.isoOfEq e).hom ≫ g.iso.hom ≫ g.target.ι)) := (Category.assoc _ _ _).symm
        _ = ((f.iso.hom ∣_ (f.target.ι ⁻¹ᵁ g.source)) ≫ (f.target.ι ⁻¹ᵁ g.source).ι) ≫
            ((Y.isoOfEq e).hom ≫ g.iso.hom ≫ g.target.ι) := by
              rw [← morphismRestrict_ι f.iso.hom (f.target.ι ⁻¹ᵁ g.source)]
        _ = (f.iso.hom ∣_ (f.target.ι ⁻¹ᵁ g.source)) ≫ ((f.target.ι ⁻¹ᵁ g.source).ι ≫
            ((Y.isoOfEq e).hom ≫ g.iso.hom ≫ g.target.ι)) := Category.assoc _ _ _
        _ = (f.iso.hom ∣_ (f.target.ι ⁻¹ᵁ g.source)) ≫ (((f.target.ι ⁻¹ᵁ g.source).ι ≫
            (Y.isoOfEq e).hom) ≫ (g.iso.hom ≫ g.target.ι)) := by
              rw [← Category.assoc ((f.target.ι ⁻¹ᵁ g.source).ι) (Y.isoOfEq e).hom
                (g.iso.hom ≫ g.target.ι)]
        _ = (f.iso.hom ∣_ (f.target.ι ⁻¹ᵁ g.source)) ≫ ((f.target.ι ∣_ g.source) ≫
            (g.iso.hom ≫ g.target.ι)) := by rw [hAM]
  refine ⟨f.source.ι ''ᵁ ((f.iso.hom ≫ f.target.ι) ⁻¹ᵁ g.source), ?_,
    f.source.ι_image_le _, le_rfl, ?_⟩
  · rw [← e, Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top,
      Opens.ι_image_top]
    exact f.dense_source
  · rw [Scheme.PartialMap.restrict_hom, Scheme.PartialMap.restrict_hom, Scheme.homOfLE_rfl,
      Category.id_comp]
    exact hhom

/-- The rational map underlying a composite of partial isomorphisms is the composite of the
underlying rational maps. -/
theorem trans_toRationalMap {X Y Z : Scheme.{0}} [PreirreducibleSpace X] [Nonempty Y]
    (i : X.PartialIso Y) (j : Y.PartialIso Z) :
    (i.trans j).toRationalMap = i.toRationalMap.comp j.toRationalMap := by
  have hU : Dense (↑(i.target ⊓ j.source) : Set Y) :=
    i.dense_target.inter_of_isOpen_right j.dense_source j.source.2
  have htrans : i.trans j =
      (i.restrictTarget (i.target ⊓ j.source) hU inf_le_left).trans'
        (j.restrictSource (i.target ⊓ j.source) hU inf_le_right) rfl := rfl
  rw [htrans]
  have h1 : ((i.restrictTarget (i.target ⊓ j.source) hU inf_le_left).trans'
        (j.restrictSource (i.target ⊓ j.source) hU inf_le_right) rfl).toRationalMap =
      (i.restrictTarget (i.target ⊓ j.source) hU inf_le_left).toRationalMap.comp
        (j.restrictSource (i.target ⊓ j.source) hU inf_le_right).toRationalMap := by
    have hh := transPrime_toPartialMap_equiv_aux
      (i.restrictTarget (i.target ⊓ j.source) hU inf_le_left)
      (j.restrictSource (i.target ⊓ j.source) hU inf_le_right) rfl
    change ((i.restrictTarget (i.target ⊓ j.source) hU inf_le_left).trans'
        (j.restrictSource (i.target ⊓ j.source) hU inf_le_right) rfl).toPartialMap.toRationalMap =
      ((i.restrictTarget (i.target ⊓ j.source) hU inf_le_left).toPartialMap.toRationalMap).comp
        ((j.restrictSource (i.target ⊓ j.source) hU inf_le_right).toPartialMap.toRationalMap)
    rw [Scheme.RationalMap.toRationalMap_comp
      (i.restrictTarget (i.target ⊓ j.source) hU inf_le_left).toPartialMap
      (j.restrictSource (i.target ⊓ j.source) hU inf_le_right).toPartialMap]
    exact Scheme.PartialMap.toRationalMap_eq_iff.mpr hh
  rw [h1]
  simp only [restrictTarget_toRationalMap i (i.target ⊓ j.source) hU inf_le_left,
    restrictSource_toRationalMap j (i.target ⊓ j.source) hU inf_le_right]

end Work.Motivic
