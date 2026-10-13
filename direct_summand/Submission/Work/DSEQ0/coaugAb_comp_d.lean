import Mathlib
import Submission.Work.DSEQ0.AugDefs
import Submission.Work.DSF1.Sheaf.cechTrivAll_local

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

universe u

namespace Work.DSEQ0

/-- **Component formula for the Čech differential**, with the target category
`AddCommGrpCat.{u}` (whose hom-universe is not its object-universe, so that the generic
`Work.DSF1.Cech.cechComplexFunctor_d_π` cannot be instantiated directly).

For a presheaf `Q` of abelian groups on the opens of `X` and a family `U : ι → X.Opens`, the
`x`-th component (with `x` a `(n+1)`-simplex of the Čech nerve, i.e. an `(n+2)`-tuple of
indices) of the differential `d n (n+1)` is the alternating sum of the components of the
individual cofaces. -/
lemma cech_d_comp_π_Ab (X : AlgebraicGeometry.Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
    (Q : (X.Opens)ᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ)
    (x : ((Work.DSF1.Cech.E U).obj (Opposite.op (SimplexCategory.mk (n+1)))).I) :
    ((CategoryTheory.cechComplexFunctor U).obj Q).d n (n+1) ≫
        Pi.π (fun y => Q.obj (op (Work.DSF1.Cech.Eobj U (n+1) y))) x =
      ∑ a : Fin (n+2), (-1:ℤ)^(a:ℕ) •
        (Pi.π (fun y => Q.obj (op (Work.DSF1.Cech.Eobj U n y)))
            (((Work.DSF1.Cech.E U).map (SimplexCategory.δ a).op).f x) ≫
          Q.map (((Work.DSF1.Cech.E U).map (SimplexCategory.δ a).op).φ x).op) := by
  simp only [CategoryTheory.cechComplexFunctor,
    CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor_obj_d]
  rw [CochainComplex.of_d]
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  rw [Preadditive.sum_comp, Finset.sum_congr rfl (fun i _ => Preadditive.zsmul_comp _ _ _)]
  simp only [CosimplicialObject.δ, FormalCoproduct.cosimplicialObjectFunctor_obj_map,
    Pi.lift_comp_π]

theorem coaugAb_comp_d (X : AlgebraicGeometry.Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
    (Q : CategoryTheory.Functor (Opposite (X.Opens)) AddCommGrpCat.{u}) :
    CategoryTheory.CategoryStruct.comp (Work.DSEQ0.coaugAb X U Q)
      (((CategoryTheory.cechComplexFunctor U).obj Q).d 0 1) = 0 := by
  refine Pi.hom_ext _ _ (fun y => ?_)
  simp only [zero_comp]
  change (Work.DSEQ0.coaugAb X U Q ≫
      ((CategoryTheory.cechComplexFunctor U).obj Q).d 0 1) ≫
      Pi.π (fun z => Q.obj (op (Work.DSF1.Cech.Eobj U 1 z))) y = 0
  rw [Category.assoc]
  rw [show ((CategoryTheory.cechComplexFunctor U).obj Q).d 0 1 ≫
        Pi.π (fun z => Q.obj (op (Work.DSF1.Cech.Eobj U 1 z))) y =
      ∑ a : Fin 2, (-1:ℤ)^(a:ℕ) •
        (Pi.π (fun z => Q.obj (op (Work.DSF1.Cech.Eobj U 0 z)))
            (((Work.DSF1.Cech.E U).map (SimplexCategory.δ a).op).f y) ≫
          Q.map (((Work.DSF1.Cech.E U).map (SimplexCategory.δ a).op).φ y).op) from
      cech_d_comp_π_Ab X U Q 0 y]
  rw [Preadditive.comp_sum]
  rw [Finset.sum_congr rfl (fun a _ => Preadditive.comp_zsmul _ _ _)]
  have hterm : ∀ a : Fin 2,
      (Work.DSEQ0.coaugAb X U Q ≫
          (Pi.π (fun z => Q.obj (op (Work.DSF1.Cech.Eobj U 0 z)))
              (((Work.DSF1.Cech.E U).map (SimplexCategory.δ a).op).f y) ≫
            Q.map (((Work.DSF1.Cech.E U).map (SimplexCategory.δ a).op).φ y).op)) =
        Q.map (homOfLE (le_top : Work.DSF1.Cech.Eobj U 1 y ≤ ⊤)).op := by
    intro a
    rw [← Category.assoc]
    rw [show Work.DSEQ0.coaugAb X U Q ≫
          Pi.π (fun z => Q.obj (op (Work.DSF1.Cech.Eobj U 0 z)))
              (((Work.DSF1.Cech.E U).map (SimplexCategory.δ a).op).f y) =
        Q.map (homOfLE le_top).op from Pi.lift_comp_π _ _]
    rw [← Q.map_comp]
    congr 1
  simp only [hterm]
  rw [Fin.sum_univ_two]
  simp

end Work.DSEQ0
