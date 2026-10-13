import Mathlib
import Submission.Work.DSMap.Map

namespace Work.DSF1.Sheaf

universe u u₁ u₂ u₃ v₁ v₂ v₃ w

open CategoryTheory Limits

/-- The alternating coface map complex commutes with the application of an additive functor. -/
noncomputable def alternatingCofaceMapComplexMapHomologicalComplexIso
    {S : Type u₁} [Category.{v₁} S] [Preadditive S]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D] (F : S ⥤ D) [F.Additive]
    (K : CosimplicialObject S) :
    (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((AlgebraicTopology.alternatingCofaceMapComplex S).obj K) ≅
    (AlgebraicTopology.alternatingCofaceMapComplex D).obj (K ⋙ F) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun i j hij => by
    rw [ComplexShape.up_Rel] at hij
    subst hij
    simp only [Functor.mapHomologicalComplex_obj_X, Functor.mapHomologicalComplex_obj_d,
      AlgebraicTopology.alternatingCofaceMapComplex,
      AlgebraicTopology.AlternatingCofaceMapComplex.obj,
      AlgebraicTopology.AlternatingCofaceMapComplex.objD, CochainComplex.of_X, CochainComplex.of_d]
    rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id, F.map_sum]
    simp only [F.map_zsmul]
    rfl)

/-- `evalOp` commutes with post-composition by a functor that preserves the relevant products. -/
noncomputable def evalOpObjIso
    {C : Type u₁} [Category.{v₁} C]
    {S : Type u₂} [Category.{v₂} S] [HasProducts.{w} S]
    {D : Type u₃} [Category.{v₃} D] [HasProducts.{w} D]
    (F : S ⥤ D) (P : Cᵒᵖ ⥤ S)
    (hF : ∀ {I : Type w} (g : I → S), PreservesLimit (Discrete.functor g) F) :
    (FormalCoproduct.evalOp C S).obj P ⋙ F ≅ (FormalCoproduct.evalOp C D).obj (P ⋙ F) :=
  NatIso.ofComponents (fun X => by
      haveI := hF (I := (Opposite.unop X).I) (fun i => P.obj (Opposite.op ((Opposite.unop X).obj i)))
      exact PreservesProduct.iso F (fun i => P.obj (Opposite.op ((Opposite.unop X).obj i))))
    (fun {X Y} f => by
      let gX : (Opposite.unop X).I → S := fun i => P.obj (Opposite.op ((Opposite.unop X).obj i))
      let gY : (Opposite.unop Y).I → S := fun i => P.obj (Opposite.op ((Opposite.unop Y).obj i))
      simp only [PreservesProduct.iso_hom, Functor.comp_map, FormalCoproduct.evalOp_obj_map]
      change (F.map (Pi.lift fun i =>
            Pi.π gX (f.unop.f i) ≫ P.map (f.unop.φ i).op) ≫ piComparison F gY) =
        (piComparison F gX ≫ Pi.lift fun i =>
            Pi.π (fun i => F.obj (gX i)) (f.unop.f i) ≫ F.map (P.map (f.unop.φ i).op))
      rw [map_lift_piComparison]
      apply Pi.hom_ext (f := fun i => F.obj (gY i))
      intro j
      rw [Pi.lift_comp_π]
      rw [Category.assoc, Pi.lift_comp_π, ← Category.assoc]
      erw [piComparison_comp_π]
      erw [F.map_comp])

theorem gammaCechComplexFunctor (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) {ι : Type u} (U : ι → X.Opens)
    (P : CategoryTheory.Functor (Opposite (X.Opens)) (AlgebraicGeometry.Scheme.Modules X)) :
    Nonempty (CategoryTheory.Iso
      ((CategoryTheory.Functor.mapHomologicalComplex (DSMap.GammaA A X f)
          (ComplexShape.up ℕ)).obj ((CategoryTheory.cechComplexFunctor U).obj P))
      ((CategoryTheory.cechComplexFunctor U).obj
        (CategoryTheory.Functor.comp P (DSMap.GammaA A X f)))) := by
  haveI hAdd : (DSMap.GammaA A X f).Additive := inferInstance
  have hF : ∀ {I : Type u} (g : I → X.Modules), PreservesLimit (Discrete.functor g)
      (DSMap.GammaA A X f) := by
    intro I g
    haveI h : PreservesLimitsOfShape (Discrete I) (DSMap.GammaA A X f) := by
      unfold DSMap.GammaA
      have h1 : PreservesLimitsOfShape (Discrete I)
          (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤) :
            SheafOfModules.{u} X.ringCatSheaf ⥤ _) := inferInstance
      have h2 : PreservesLimitsOfShape (Discrete I)
          (ModuleCat.restrictScalars (DSMap.phi A X f) : ModuleCat.{u} _ ⥤ ModuleCat.{u} A) :=
        inferInstance
      exact @comp_preservesLimitsOfShape _ _ _ _ _ _ _ _ _ _ h1 h2
    exact h.preservesLimit
  let E : SimplicialObject (FormalCoproduct X.Opens) := FormalCoproduct.cech {I := ι, obj := U}
  let WS := (Functor.whiskeringLeft SimplexCategory ((FormalCoproduct X.Opens)ᵒᵖ) X.Modules).obj
    E.rightOp
  let WD := (Functor.whiskeringLeft SimplexCategory ((FormalCoproduct X.Opens)ᵒᵖ)
    (ModuleCat A)).obj E.rightOp
  exact ⟨alternatingCofaceMapComplexMapHomologicalComplexIso (DSMap.GammaA A X f)
      (WS.obj ((FormalCoproduct.evalOp X.Opens X.Modules).obj P)) ≪≫
    (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat A)).mapIso
      (WD.mapIso (evalOpObjIso (DSMap.GammaA A X f) P hF))⟩

end Work.DSF1.Sheaf
