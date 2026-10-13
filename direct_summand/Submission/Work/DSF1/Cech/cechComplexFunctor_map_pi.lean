import Mathlib
import Submission.Work.DSF1.Cech.CechComponents

namespace Work.DSF1.Cech

universe u u' v w
open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000

theorem cechComplexFunctor_map_pi {C : Type u} [Category.{v} C] [HasFiniteProducts C]
    {A : Type u'} [Category.{w} A] [HasProducts.{w} A] [Preadditive A] {ι : Type w}
    (U : ι → C) {P P' : Cᵒᵖ ⥤ A} (η : P ⟶ P') (n : ℕ)
    (x : ((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).I) :
    ((cechComplexFunctor U).map η).f n ≫
        Pi.π (fun y => P'.obj (op (((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).obj y))) x =
      Pi.π (fun y => P.obj (op (((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).obj y))) x ≫
        η.app (op (((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).obj x)) := by
  simp only [cechComplexFunctor, FormalCoproduct.cochainComplexFunctor, Functor.comp_map,
    AlgebraicTopology.alternatingCofaceMapComplex_map,
    AlgebraicTopology.AlternatingCofaceMapComplex.map]
  rw [FormalCoproduct.cosimplicialObjectFunctor_map_app]
  exact Pi.map_π (fun i => η.app (op (((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).obj i))) x

end Work.DSF1.Cech
