import Mathlib
import Submission.Work.DSEQ0.AugDefs

universe u

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

namespace Work.DSEQ0

theorem cech_d_comp_pi (X : AlgebraicGeometry.Scheme.{u}) {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (x : ((Work.DSF1.Cech.E U).obj (Opposite.op (SimplexCategory.mk (n+1)))).I) :
    CategoryTheory.CategoryStruct.comp
      (((CategoryTheory.cechComplexFunctor U).obj (Work.DSEQ0.C.cechShPresheaf X)).d n (n+1))
      (CategoryTheory.Limits.Pi.π (fun y => (Work.DSEQ0.C.cechShPresheaf X).obj
        (Opposite.op (Work.DSF1.Cech.Eobj U (n+1) y))) x) =
    Finset.univ.sum (fun a : Fin (n+2) => (-1:ℤ)^(a:ℕ) • CategoryTheory.CategoryStruct.comp
      (CategoryTheory.Limits.Pi.π (fun y => (Work.DSEQ0.C.cechShPresheaf X).obj
          (Opposite.op (Work.DSF1.Cech.Eobj U n y)))
        ((((Work.DSF1.Cech.E U).map (SimplexCategory.δ a).op)).f x))
      ((Work.DSEQ0.C.cechShPresheaf X).map
        ((((Work.DSF1.Cech.E U).map (SimplexCategory.δ a).op)).φ x).op)) := by
  simp only [CategoryTheory.cechComplexFunctor,
    CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor_obj_d]
  rw [CochainComplex.of_d]
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  rw [Preadditive.sum_comp, Finset.sum_congr rfl (fun i _ => Preadditive.zsmul_comp _ _ _)]
  simp only [CosimplicialObject.δ, FormalCoproduct.cosimplicialObjectFunctor_obj_map,
    Pi.lift_comp_π]

end Work.DSEQ0
