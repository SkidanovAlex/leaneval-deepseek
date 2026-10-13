import Mathlib
import Submission.Work.DSF1.Sheaf.gammaCechComplexFunctor

/-!
# Cech complex and restriction of scalars

For a ring homomorphism `ψ : A →+* W`, the Cech complex construction on a presheaf of
`W`-modules commutes with restriction of scalars along `ψ`:

`cech (F ⋙ restrictScalars ψ) ≅ restrictScalars ψ (cech F)`.

This is a general fact: the Cech complex functor is built from the "evaluation" functors
`evalOp` (which are products) and the alternating coface map complex, and restriction of
scalars preserves the relevant products (it is a right adjoint, hence preserves limits) and
is additive.  The two structural lemmas `alternatingCofaceMapComplexMapHomologicalComplexIso`
and `evalOpObjIso` (proved for an arbitrary additive functor preserving products in
`Submission.Work.DSF1.Sheaf.gammaCechComplexFunctor`) supply exactly these two steps.
-/

namespace Work.DSEQP

open CategoryTheory Limits

universe u

theorem cech_restrictScalars_iso {A W : Type u} [CommRing A] [CommRing W] (ψ : A →+* W)
    {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (F : CategoryTheory.Functor (Opposite X.Opens) (ModuleCat.{u} W)) :
    Nonempty (CategoryTheory.Iso
      (((ModuleCat.restrictScalars ψ).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((CategoryTheory.cechComplexFunctor U).obj F))
      ((CategoryTheory.cechComplexFunctor U).obj
        (CategoryTheory.Functor.comp F (ModuleCat.restrictScalars ψ)))) := by
  -- restriction of scalars is additive
  haveI hAdd : (ModuleCat.restrictScalars ψ).Additive := inferInstance
  -- and, being a right adjoint, it preserves all products needed by `evalOp`
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
  exact ⟨Work.DSF1.Sheaf.alternatingCofaceMapComplexMapHomologicalComplexIso
      (ModuleCat.restrictScalars ψ)
      (WS.obj ((FormalCoproduct.evalOp X.Opens (ModuleCat.{u} W)).obj F)) ≪≫
    (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{u} A)).mapIso
      (WD.mapIso (Work.DSF1.Sheaf.evalOpObjIso (ModuleCat.restrictScalars ψ) F hF))⟩

end Work.DSEQP
