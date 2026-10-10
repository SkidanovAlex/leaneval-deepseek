import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Auxiliary point-level lemmas about open subschemes and partial isomorphisms

These collect the "definitional bookkeeping" facts about `Scheme.Hom.isoImage`,
`Scheme.Opens.isoOfLE`, `Scheme.isoOfEq` and `Scheme.homOfLE` at the level of points,
together with the point values of `PartialIso.restrictSource` and `PartialIso.restrictTarget`.
-/

namespace Work.Motivic

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

/-! ## Point-level bookkeeping for `isoImage` -/

/-- The isomorphism `f.isoImage U : U ≅ f ''ᵁ U` commutes with the inclusions. -/
lemma isoImage_hom_apply {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (U : X.Opens) (x : U.toScheme) :
    (f ''ᵁ U).ι ((f.isoImage U).hom x) = f (U.ι x) := by
  rw [← Scheme.Hom.comp_apply, Scheme.Hom.isoImage_hom_ι, Scheme.Hom.comp_apply]

/-- The inverse of `f.isoImage U` commutes with the inclusions. -/
lemma isoImage_inv_apply {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (U : X.Opens) (x : (f ''ᵁ U).toScheme) :
    f (U.ι ((f.isoImage U).inv x)) = (f ''ᵁ U).ι x := by
  rw [← Scheme.Hom.isoImage_inv_ι]
  simp only [Scheme.Hom.comp_apply]

/-- For an isomorphism `e`, the inverse of `e.inv.isoImage U` commutes with the inclusions. -/
lemma iota_isoImage_inv_inv {X Y : Scheme.{u}} (e : X ≅ Y) (U : Y.Opens)
    (x : (e.inv ''ᵁ U).toScheme) :
    U.ι ((e.inv.isoImage U).inv x) = e.hom ((e.inv ''ᵁ U).ι x) := by
  have h := isoImage_inv_apply (f := e.inv) U x
  have h2 := congrArg e.hom h
  simpa [Iso.inv_hom_id_apply] using h2

/-! ## Point-level bookkeeping for `isoOfLE` -/

/-- The morphism `isoOfLE h : (V.ι ⁻¹ᵁ U) ≅ U` commutes with the inclusions. -/
lemma isoOfLE_inv_comp_iota {X : Scheme.{u}} {U V : X.Opens} (h : U ≤ V) :
    (Scheme.Opens.isoOfLE h).inv ≫ (V.ι ⁻¹ᵁ U).ι = X.homOfLE h := by
  rw [← cancel_mono V.ι, Category.assoc, Scheme.Opens.isoOfLE_inv_ι, Scheme.homOfLE_ι]

/-- The inverse of `isoOfLE h` commutes with the inclusions, as a point of `X`. -/
lemma isoOfLE_hom_apply {X : Scheme.{u}} {U V : X.Opens} (h : U ≤ V)
    (x : (V.ι ⁻¹ᵁ U).toScheme) :
    U.ι ((Scheme.Opens.isoOfLE h).hom x) = V.ι ((V.ι ⁻¹ᵁ U).ι x) := by
  rw [← Scheme.Hom.comp_apply, Scheme.Opens.isoOfLE_hom_ι, Scheme.Hom.comp_apply]

/-! ## Point-level bookkeeping for `isoOfEq`, `homOfLE` and `toPartialMap` -/

/-- `isoOfEq e` does not change the ambient point. -/
lemma isoOfEq_hom_val {X : Scheme.{u}} {U V : X.Opens} (e : U = V) (z : U.toScheme) :
    ((X.isoOfEq e).hom z).val = z.val := by
  rw [Scheme.isoOfEq_hom]
  exact Scheme.homOfLE_apply e.le z

/-- The ambient point of `f.iso.hom z` is `f.toPartialMap.hom z`. -/
lemma iso_hom_val {X Y : Scheme.{u}} (f : X.PartialIso Y) (z : f.source.toScheme) :
    ((f.iso.hom z).val) = f.toPartialMap.hom z := by
  rw [Scheme.PartialIso.toPartialMap_hom]
  set_option backward.isDefEq.respectTransparency false in
    rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
  rfl

/-- The underlying morphism of `trans'` is the composite of the underlying morphisms. -/
lemma transPrime_toPartialMap_hom {X Y Z : Scheme.{0}} (f : X.PartialIso Y)
    (g : Y.PartialIso Z) (e : f.target = g.source) :
    (f.trans' g e).toPartialMap.hom = f.iso.hom ≫ (Y.isoOfEq e).hom ≫ g.toPartialMap.hom := by
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
    simp only [Scheme.PartialIso.toPartialMap_hom, Scheme.PartialIso.trans'_iso,
      Scheme.PartialIso.trans'_target, Iso.trans_hom, Category.assoc]

/-! ## The point values of `restrictSource` and `restrictTarget` -/

/-- Restricting the source of a partial isomorphism does not change the underlying map. -/
theorem restrictSource_toPartialMap_hom_apply {Y Z : Scheme.{0}} (j : Y.PartialIso Z)
    (U : Y.Opens) (hU : Dense (U : Set Y)) (hU' : U ≤ j.source) (q : U.toScheme) :
    (j.restrictSource U hU hU').toPartialMap.hom q = j.toPartialMap.hom ⟨q.1, hU' q.2⟩ := by
  rw [Scheme.PartialIso.toPartialMap_hom, Scheme.PartialIso.toPartialMap_hom]
  set_option backward.defeqAttrib.useBackward true in
  simp only [Scheme.PartialIso.restrictSource_iso, Scheme.PartialIso.restrictSource_target,
    Iso.trans_hom]
  set_option backward.isDefEq.respectTransparency false in
  simp only [Scheme.Hom.comp_apply]
  set_option backward.isDefEq.respectTransparency false in
  rw [Iso.symm_hom]
  set_option backward.isDefEq.respectTransparency false in
  rw [isoImage_hom_apply, isoImage_hom_apply]
  have hpt : (j.source.ι ⁻¹ᵁ U).ι ((Scheme.Opens.isoOfLE hU').inv q) = Y.homOfLE hU' q := by
    rw [← Scheme.Hom.comp_apply, isoOfLE_inv_comp_iota]
  have hpt2 : (j.source.ι ⁻¹ᵁ U).ι ((Scheme.Opens.isoOfLE hU').inv q) = ⟨q.1, hU' q.2⟩ := by
    rw [hpt]
    exact Subtype.ext (by rw [Scheme.homOfLE_apply])
  exact congrArg (fun p => j.target.ι (j.iso.hom p)) hpt2

/-- Restricting the target of a partial isomorphism does not change the underlying map. -/
theorem restrictTarget_toPartialMap_hom_apply {X Y : Scheme.{0}} (i : X.PartialIso Y)
    (U : Y.Opens) (hU : Dense (U : Set Y)) (hU' : U ≤ i.target)
    (p : (i.restrictTarget U hU hU').source.toScheme) (hp : p.1 ∈ i.source) :
    (i.restrictTarget U hU hU').toPartialMap.hom p = i.toPartialMap.hom ⟨p.1, hp⟩ := by
  rw [Scheme.PartialIso.toPartialMap_hom, Scheme.PartialIso.toPartialMap_hom]
  set_option backward.defeqAttrib.useBackward true in
  simp only [Scheme.PartialIso.restrictTarget, Scheme.PartialIso.symm,
    Scheme.PartialIso.restrictSource_iso, Scheme.PartialIso.restrictSource_source,
    Iso.symm_hom, Iso.trans_hom]
  set_option backward.isDefEq.respectTransparency false in
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.symm_hom, Scheme.Hom.comp_apply]
  set_option backward.isDefEq.respectTransparency false in
  rw [isoOfLE_hom_apply]
  set_option backward.isDefEq.respectTransparency false in
  rw [iota_isoImage_inv_inv i.iso]
  have h : i.source.ι (((Hom.opensFunctor i.iso.inv).obj
      ((TopologicalSpace.Opens.map i.target.ι.base).obj U)).ι
      ((Hom.isoImage i.source.ι ((Hom.opensFunctor i.iso.inv).obj
        ((TopologicalSpace.Opens.map i.target.ι.base).obj U))).inv p)) = p.1 := by
    set_option backward.isDefEq.respectTransparency false in
      rw [isoImage_inv_apply]
    rfl
  exact congrArg (fun q => i.target.ι (i.iso.hom q)) (Subtype.ext h)

/-- Pointwise form of `restrictTarget_toPartialMap_hom_apply` at an explicit point. -/
theorem restrictTarget_apply' {X Y : Scheme.{0}} (i : X.PartialIso Y)
    (U : Y.Opens) (hU : Dense (U : Set Y)) (hU' : U ≤ i.target)
    {x : X} (hx : x ∈ i.source) (hx' : x ∈ (i.restrictTarget U hU hU').source) :
    (i.restrictTarget U hU hU').toPartialMap.hom ⟨x, hx'⟩ = i.toPartialMap.hom ⟨x, hx⟩ :=
  restrictTarget_toPartialMap_hom_apply i U hU hU' ⟨x, hx'⟩ hx

end Work.Motivic
