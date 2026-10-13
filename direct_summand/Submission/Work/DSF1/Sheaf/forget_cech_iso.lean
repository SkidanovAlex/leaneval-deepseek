import Mathlib
import Submission.Work.DSF1.Sheaf.CechGen
import Submission.Work.DSF1.Sheaf.gammaCechComplexFunctor

/-!
# The forgetful functor commutes with the Čech complex construction

For a presheaf `P` of `R`-modules on `Spec R`, the Čech complex of `P` (in `R`-modules),
viewed as a complex of abelian groups via the forgetful functor, is canonically isomorphic
to the Čech complex of the underlying presheaf of abelian groups.

This is `Work.DSF1.Sheaf.gammaCechComplexFunctor` with the forgetful functor
`forget₂ (ModuleCat R) AddCommGrpCat` in place of `Γ(X, -)`; the two reusable bricks are
`alternatingCofaceMapComplexMapHomologicalComplexIso` and `evalOpObjIso`.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped AlgebraicGeometry Simplicial BigOperators

namespace Work.DSF1.Sheaf

universe u

theorem forget_cech_iso (R : CommRingCat.{u}) {ι : Type u} [Finite ι]
    (U : ι → Work.DSF1.Sheaf.Och R) (P : Work.DSF1.Sheaf.MPSheaf R) :
    Nonempty (CategoryTheory.Iso (Work.DSF1.Sheaf.forgetComplex R U P)
      (Work.DSF1.Sheaf.cechAb R U P)) := by
  haveI hAdd : (forgetF R).Additive := inferInstance
  have hF : ∀ {I : Type u} (g : I → ModuleCat.{u} R),
      PreservesLimit (Discrete.functor g) (forgetF R) := by
    intro I g
    haveI h : PreservesLimitsOfShape (Discrete I) (forgetF R) := inferInstance
    exact h.preservesLimit
  let E : SimplicialObject (FormalCoproduct (Och R)) :=
    FormalCoproduct.cech {I := ι, obj := U}
  let WS := (Functor.whiskeringLeft SimplexCategory ((FormalCoproduct (Och R))ᵒᵖ)
    (ModuleCat.{u} R)).obj E.rightOp
  let WD := (Functor.whiskeringLeft SimplexCategory ((FormalCoproduct (Och R))ᵒᵖ)
    AddCommGrpCat.{u}).obj E.rightOp
  exact ⟨alternatingCofaceMapComplexMapHomologicalComplexIso (forgetF R)
      (WS.obj ((FormalCoproduct.evalOp (Och R) (ModuleCat.{u} R)).obj P)) ≪≫
    (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u}).mapIso
      (WD.mapIso (evalOpObjIso (forgetF R) P hF))⟩

end Work.DSF1.Sheaf
