import Mathlib
import Submission.Work.DSF1.Sheaf.CechStruct
import Submission.Work.DSF1.Sheaf.gammaCechComplexFunctor

/-!
# The forgetful functor commutes with the Čech complex construction (general scheme)

For a presheaf `P` of modules over `R = Γ(X,⊤)` on the opens of a scheme `X`, the Čech
complex of `P` viewed as a complex of abelian groups (by applying the forgetful functor
`ModuleCat R ⥤ AddCommGrpCat` to each term) is canonically isomorphic to the Čech complex
of the underlying presheaf of abelian groups.

This is the general-scheme version of `Work.DSF1.Sheaf.forget_cech_iso`, and is proved by
the same two reusable bricks (`alternatingCofaceMapComplexMapHomologicalComplexIso` and
`evalOpObjIso`), exactly as `Work.DSF1.Sheaf.gammaCechComplexFunctor`.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped AlgebraicGeometry Simplicial BigOperators

namespace Work.DSF1.Sheaf

universe u

/-- The forgetful functor from `R`-modules to abelian groups. -/
noncomputable abbrev forgetMod (R : Type u) [CommRing R] : ModuleCat.{u} R ⥤ AddCommGrpCat.{u} :=
  CategoryTheory.forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}

theorem forget_cech_iso_general {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u} [Fintype ι]
    (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ ModuleCat.{u} (↥(X.presheaf.obj (op ⊤)))) :
    Nonempty (CategoryTheory.Iso
      ((CategoryTheory.Functor.mapHomologicalComplex
          (forgetMod (↥(X.presheaf.obj (op ⊤)))) (ComplexShape.up ℕ)).obj
        ((CategoryTheory.cechComplexFunctor U).obj P))
      ((CategoryTheory.cechComplexFunctor U).obj
        (CategoryTheory.Functor.comp P (forgetMod (↥(X.presheaf.obj (op ⊤))))))) := by
  haveI hAdd : (forgetMod (↥(X.presheaf.obj (op ⊤)))).Additive := inferInstance
  have hF : ∀ {I : Type u} (g : I → ModuleCat.{u} (↥(X.presheaf.obj (op ⊤)))),
      PreservesLimit (Discrete.functor g) (forgetMod (↥(X.presheaf.obj (op ⊤)))) := by
    intro I g
    haveI h : PreservesLimitsOfShape (Discrete I)
        (forgetMod (↥(X.presheaf.obj (op ⊤)))) := inferInstance
    exact h.preservesLimit
  let E : SimplicialObject (FormalCoproduct X.Opens) := FormalCoproduct.cech {I := ι, obj := U}
  let WS := (Functor.whiskeringLeft SimplexCategory ((FormalCoproduct X.Opens)ᵒᵖ)
    (ModuleCat.{u} (↥(X.presheaf.obj (op ⊤))))).obj E.rightOp
  let WD := (Functor.whiskeringLeft SimplexCategory ((FormalCoproduct X.Opens)ᵒᵖ)
    AddCommGrpCat.{u}).obj E.rightOp
  exact ⟨alternatingCofaceMapComplexMapHomologicalComplexIso
      (forgetMod (↥(X.presheaf.obj (op ⊤))))
      (WS.obj ((FormalCoproduct.evalOp X.Opens
        (ModuleCat.{u} (↥(X.presheaf.obj (op ⊤))))).obj P)) ≪≫
    (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u}).mapIso
      (WD.mapIso (evalOpObjIso (forgetMod (↥(X.presheaf.obj (op ⊤)))) P hF))⟩

end Work.DSF1.Sheaf
