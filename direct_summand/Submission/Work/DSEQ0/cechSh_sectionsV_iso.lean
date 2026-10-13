import Mathlib
import Submission.Work.DSEQ0.AugDefs
import Submission.Work.DSF1.Sheaf.gammaCechComplexFunctor

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial

namespace Work.DSEQ0

universe u

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

theorem cechSh_sectionsV_iso (X : AlgebraicGeometry.Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
    (V : X.Opens) :
    ∃ (e : CategoryTheory.Iso
      ((CategoryTheory.Functor.mapHomologicalComplex (Work.DSEQ0.sectionsV X V)
          (ComplexShape.up ℕ)).obj
        ((CategoryTheory.cechComplexFunctor U).obj (Work.DSEQ0.C.cechShPresheaf X)))
      ((CategoryTheory.cechComplexFunctor U).obj
        (CategoryTheory.Functor.comp (Work.DSEQ0.C.cechShPresheaf X)
          (Work.DSEQ0.sectionsV X V)))),
      CategoryTheory.IsIso e.hom ∧
      CategoryTheory.CategoryStruct.comp
          (AlgebraicGeometry.Scheme.Modules.Hom.app (Work.DSEQ0.C.aug0 (X := X) U) V) (e.hom.f 0) =
        Work.DSEQ0.coaugAb X U (CategoryTheory.Functor.comp (Work.DSEQ0.C.cechShPresheaf X)
          (Work.DSEQ0.sectionsV X V)) := by
  haveI hAdd : (Work.DSEQ0.sectionsV X V).Additive := Work.DSEQ0.sectionsV_additive X V
  have hF : ∀ {I : Type u} (g : I → X.Modules), PreservesLimit (Discrete.functor g)
      (Work.DSEQ0.sectionsV X V) := fun {I} g => Work.DSEQ0.sectionsV_preservesProduct X V g
  let P : X.Opensᵒᵖ ⥤ X.Modules := Work.DSEQ0.C.cechShPresheaf X
  let E : SimplicialObject (FormalCoproduct X.Opens) := FormalCoproduct.cech {I := ι, obj := U}
  let WS := (Functor.whiskeringLeft SimplexCategory ((FormalCoproduct X.Opens)ᵒᵖ) X.Modules).obj E.rightOp
  let WD := (Functor.whiskeringLeft SimplexCategory ((FormalCoproduct X.Opens)ᵒᵖ) AddCommGrpCat).obj E.rightOp
  let e1 := Work.DSF1.Sheaf.alternatingCofaceMapComplexMapHomologicalComplexIso (Work.DSEQ0.sectionsV X V)
      (WS.obj ((FormalCoproduct.evalOp X.Opens X.Modules).obj P))
  let e2 := (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat).mapIso
      (WD.mapIso (Work.DSF1.Sheaf.evalOpObjIso (Work.DSEQ0.sectionsV X V) P hF))
  have hef0 : (e1 ≪≫ e2).hom.f 0 = piComparison (Work.DSEQ0.sectionsV X V)
      (fun i => P.obj (op (Work.DSF1.Cech.Eobj U 0 i))) := by
    simp only [Iso.trans_hom, HomologicalComplex.comp_f]
    rw [show e1.hom.f 0 = 𝟙 _ from rfl, Category.id_comp]
    rw [Functor.mapIso_hom, AlgebraicTopology.alternatingCofaceMapComplex_map]
    rfl
  refine ⟨e1 ≪≫ e2, inferInstance, ?_⟩
  rw [hef0]
  have hL : Scheme.Modules.Hom.app (Work.DSEQ0.C.aug0 (X := X) U) V ≫
        piComparison (Work.DSEQ0.sectionsV X V) (fun i => P.obj (op (Work.DSF1.Cech.Eobj U 0 i)))
      = Pi.lift (fun x => (Work.DSEQ0.sectionsV X V).map
          (P.map (homOfLE (le_top : Work.DSF1.Cech.Eobj U 0 x ≤ ⊤)).op)) := by
    rw [← Work.DSEQ0.sectionsV_map X V (Work.DSEQ0.C.aug0 (X := X) U)]
    rw [show Work.DSEQ0.C.aug0 (X := X) U =
        Pi.lift (fun x => P.map (homOfLE (le_top : Work.DSF1.Cech.Eobj U 0 x ≤ ⊤)).op) from rfl]
    rw [map_lift_piComparison]
  rw [hL]
  rfl

end Work.DSEQ0
