import Mathlib
import Submission.Work.DSEQP.PerfAlmost

namespace Work.DSEQP

universe u

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped Simplicial BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 800000

theorem perf_K_d_pi (A : Type u) [CommRing A] (p : ℕ) [Fact p.Prime] (X : AlgebraicGeometry.Scheme.{u})
    [AlgebraicGeometry.IsIntegral X] (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    (S : Work.DSEQP.PerfSetup A p X f) {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (x : (Work.DSEQP.PerfSetup.CechIdx U (n + 1)).I) :
    CategoryTheory.CategoryStruct.comp ((S.K U).d n (n + 1))
        (CategoryTheory.Limits.Pi.π (Work.DSEQP.PerfSetup.Kobj S U (n + 1)) x) =
      Finset.univ.sum fun a : Fin (n + 2) =>
        (-1 : ℤ) ^ (a : ℕ) •
          (CategoryTheory.CategoryStruct.comp
            (CategoryTheory.Limits.Pi.π (Work.DSEQP.PerfSetup.Kobj S U n)
              (((CategoryTheory.Limits.FormalCoproduct.mk ι U).cech.map
                (SimplexCategory.δ a).op).f x))
            (S.perfPresheaf.map
              (((CategoryTheory.Limits.FormalCoproduct.mk ι U).cech.map
                (SimplexCategory.δ a).op).φ x).op)) := by
  change ((cechComplexFunctor U).obj S.perfPresheaf).d n (n+1) ≫
      (Pi.π (fun y => S.perfPresheaf.obj
        (op (((FormalCoproduct.mk ι U).cech.obj (op ⦋n+1⦌)).obj y))) x) =
    ∑ a : Fin (n+2), (-1 : ℤ)^(a:ℕ) •
      (Pi.π (fun y => S.perfPresheaf.obj
        (op (((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).obj y)))
        (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ a).op).f x) ≫
       S.perfPresheaf.map (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ a).op).φ x).op)
  simp only [CategoryTheory.cechComplexFunctor,
    CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor_obj_d]
  rw [CochainComplex.of_d]
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  rw [Preadditive.sum_comp, Finset.sum_congr rfl (fun i _ => Preadditive.zsmul_comp _ _ _)]
  simp only [CosimplicialObject.δ, FormalCoproduct.cosimplicialObjectFunctor_obj_map,
    Pi.lift_comp_π]

end Work.DSEQP
