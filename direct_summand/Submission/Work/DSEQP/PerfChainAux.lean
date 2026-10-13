import Mathlib
import Submission.Work.DSEQP.cech_restrictScalars_iso
import Submission.Work.DSF1.Sheaf.mapHomologicalComplex_extendUpNat

/-!
# Auxiliary isomorphisms for `Work.DSEQP.exists_chainMap_perf`

This file collects the object-level bookkeeping which the proof of
`Work.DSEQP.exists_chainMap_perf` needs:

* `extendXCompIso`: the componentwise isomorphism `F (K.extend.X o) ≅ (F K).extend.X o`
  (identity on the degrees in the image of `ℕ ↪ ℤ`, any isomorphism of zero objects
  elsewhere);
* `mapHomologicalComplexExtendUpNatIso`: the isomorphism
  `F (K.extend e) ≅ (F K).extend e` for the embedding `e : ℕ ↪ ℤ`, constructed from
  `extendXCompIso` (this is `Work.DSF1.Sheaf.mapHomologicalComplex_extendUpNat`, but as a
  genuine `def`, so that its components can be computed);
* `cechRestrictScalarsIso`: `Work.DSEQP.cech_restrictScalars_iso` as a genuine `def`, so
  that its degree-`0` component can be computed.
-/

open CategoryTheory AlgebraicGeometry Limits Opposite

namespace Work.DSEQP

universe u u₁ u₂ u₃ v₁ v₂ v₃ w

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000

/-! ## The componentwise comparison `F (K.extend e) ≅ (F K).extend e` -/

section ExtendComp

variable {C : Type u₁} [Category C] [Preadditive C] [HasZeroObject C]
  {D : Type u₂} [Category D] [Preadditive D] [HasZeroObject D]

/-- Componentwise isomorphism underlying `mapHomologicalComplexExtendUpNatIso`: the identity
in the degrees in the image of `ℕ ↪ ℤ`, an isomorphism of the two zero objects elsewhere. -/
noncomputable def extendXCompIso (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℕ) :
    (o : Option ℕ) → F.obj (HomologicalComplex.extend.X K o) ≅
      HomologicalComplex.extend.X ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) o
  | some _ => Iso.refl _
  | none => IsZero.iso (F.map_isZero (isZero_zero C)) (isZero_zero D)

theorem extendXCompIso_some (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℕ)
    (n : ℕ) : extendXCompIso F K (some n) = Iso.refl _ := rfl

theorem extendXCompIso_some_inv (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℕ)
    (n : ℕ) : (extendXCompIso F K (some n)).inv = 𝟙 _ := rfl

theorem extendXCompIso_hom_extend_d (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℕ)
    (o o' : Option ℕ) :
    (extendXCompIso F K o).hom ≫ HomologicalComplex.extend.d
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) o o' =
      F.map (HomologicalComplex.extend.d K o o') ≫ (extendXCompIso F K o').hom := by
  rcases o with _ | n
  · rcases o' with _ | m
    · rw [HomologicalComplex.extend.d_none_eq_zero K none none rfl,
        HomologicalComplex.extend.d_none_eq_zero
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) none none rfl, F.map_zero]
      simp
    · rw [HomologicalComplex.extend.d_none_eq_zero K none (some m) rfl,
        HomologicalComplex.extend.d_none_eq_zero
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) none (some m) rfl, F.map_zero]
      simp
  · rcases o' with _ | m
    · rw [HomologicalComplex.extend.d_none_eq_zero' K (some n) none rfl,
        HomologicalComplex.extend.d_none_eq_zero'
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) (some n) none rfl, F.map_zero]
      simp
    · rw [show HomologicalComplex.extend.d
            ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) (some n) (some m) =
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).d n m from rfl,
        show HomologicalComplex.extend.d K (some n) (some m) = K.d n m from rfl]
      show 𝟙 (F.obj (K.X n)) ≫ F.map (K.d n m) = F.map (K.d n m) ≫ 𝟙 (F.obj (K.X m))
      rw [Category.id_comp, Category.comp_id]

/-- The isomorphism `F (K.extend e) ≅ (F K).extend e` for the embedding `e : ℕ ↪ ℤ`,
with components `extendXCompIso F K (e.r i')`. -/
noncomputable def mapHomologicalComplexExtendUpNatIso (F : C ⥤ D) [F.Additive]
    (K : CochainComplex C ℕ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (K.extend ComplexShape.embeddingUpNat)) ≅
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).extend
        ComplexShape.embeddingUpNat) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i' => extendXCompIso F K (ComplexShape.embeddingUpNat.r i'))
    (fun i' j' _ => extendXCompIso_hom_extend_d F K _ _)

theorem mapHomologicalComplexExtendUpNatIso_hom_f (F : C ⥤ D) [F.Additive]
    (K : CochainComplex C ℕ) (i' : ℤ) :
    (mapHomologicalComplexExtendUpNatIso F K).hom.f i' =
      (extendXCompIso F K (ComplexShape.embeddingUpNat.r i')).hom := rfl

theorem mapHomologicalComplexExtendUpNatIso_inv_f (F : C ⥤ D) [F.Additive]
    (K : CochainComplex C ℕ) (i' : ℤ) :
    (mapHomologicalComplexExtendUpNatIso F K).inv.f i' =
      (extendXCompIso F K (ComplexShape.embeddingUpNat.r i')).inv := rfl

end ExtendComp

/-! ## `eqToHom` under a functor -/

theorem map_eqToHom_of {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {X Y : C}
    (h : X = Y) : F.map (eqToHom h) = eqToHom (congrArg (fun Z : C => F.obj Z) h) := by
  cases h
  simp

/-! ## The restriction-of-scalars comparison for the Čech complex, as a `def` -/

/-- `Work.DSEQP.cech_restrictScalars_iso` upgraded to a genuine definition, so that its
components can be computed. -/
noncomputable def cechRestrictScalarsIso {A W : Type u} [CommRing A] [CommRing W]
    (ψ : A →+* W) {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (F : CategoryTheory.Functor (Opposite X.Opens) (ModuleCat.{u} W)) :
    CategoryTheory.Iso
      (((ModuleCat.restrictScalars ψ).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((CategoryTheory.cechComplexFunctor U).obj F))
      ((CategoryTheory.cechComplexFunctor U).obj
        (CategoryTheory.Functor.comp F (ModuleCat.restrictScalars ψ))) := by
  haveI hAdd : (ModuleCat.restrictScalars ψ).Additive := inferInstance
  have hF : ∀ {I : Type u} (g : I → ModuleCat.{u} W), PreservesLimit (Discrete.functor g)
      (ModuleCat.restrictScalars ψ) := by
    intro I g
    haveI h : PreservesLimitsOfShape (Discrete I)
        (ModuleCat.restrictScalars ψ : ModuleCat.{u} W ⥤ ModuleCat.{u} A) := inferInstance
    exact h.preservesLimit
  let E : SimplicialObject (FormalCoproduct X.Opens) :=
    FormalCoproduct.cech {I := ι, obj := U}
  let WS := (Functor.whiskeringLeft SimplexCategory ((FormalCoproduct X.Opens)ᵒᵖ)
    (ModuleCat.{u} W)).obj E.rightOp
  let WD := (Functor.whiskeringLeft SimplexCategory ((FormalCoproduct X.Opens)ᵒᵖ)
    (ModuleCat.{u} A)).obj E.rightOp
  exact Work.DSF1.Sheaf.alternatingCofaceMapComplexMapHomologicalComplexIso
      (ModuleCat.restrictScalars ψ)
      (WS.obj ((FormalCoproduct.evalOp X.Opens (ModuleCat.{u} W)).obj F)) ≪≫
    (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{u} A)).mapIso
      (WD.mapIso (Work.DSF1.Sheaf.evalOpObjIso (ModuleCat.restrictScalars ψ) F hF))

end Work.DSEQP
