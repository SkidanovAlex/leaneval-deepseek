import Mathlib
import Submission.Work.DSMap.Map

/-!
# Components of the Čech complex differential

We compute the components of the differential of Mathlib's Čech complex functor
`CategoryTheory.cechComplexFunctor U` applied to a presheaf `P`.

In degree `n`, the complex is the product, over all `x : E _⦋n⦌` (an index of the
Čech nerve of the family `U`), of `P (E _⦋n⦌.obj x)`.  The differential is the
alternating sum of the cofaces, and its `x`-th component (for `x` a `(n+1)`-simplex)
is the alternating sum of the maps obtained by deleting one of the indices.

-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

universe u v v' w

namespace Work.DSF1.Cech

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {A : Type v'} [Category.{v'} A]
  [HasProducts.{w} A] [Preadditive A] {ι : Type w} (U : ι → C) (P : Cᵒᵖ ⥤ A)

/-- The functor `(Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ` given by the Čech complex of the
family `U` is, in degree `n`, the product over all `x : Fin (n+1) → ι` of `P` of the
product of the `U (x a)`.  Compared with `cochainComplexFunctor_obj_X` this is stated
in terms of the Čech nerve `E` of `U`. -/
lemma cech_obj_X_eq (n : ℕ) :
    ((cechComplexFunctor U).obj P).X n =
      ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk ι U).cech).obj P).obj
        ⦋n⦌ := rfl

/-- **Component formula for the Čech differential.**  The `x`-th component of the
differential `d n (n+1)` of the Čech complex is the alternating sum of the components
of the individual cofaces. -/
theorem cechComplexFunctor_d_π (n : ℕ)
    (x : ((FormalCoproduct.mk ι U).cech.obj (op ⦋n+1⦌)).I) :
    ((cechComplexFunctor U).obj P).d n (n+1) ≫
        (Pi.π (fun y => P.obj (op (((FormalCoproduct.mk ι U).cech.obj (op ⦋n+1⦌)).obj y))) x)
      = ∑ a : Fin (n+2), (-1 : ℤ) ^ (a : ℕ) •
          ((Pi.π (fun y => P.obj (op (((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).obj y)))
              (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ a).op).f x)) ≫
            P.map (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ a).op).φ x).op) := by
  simp only [CategoryTheory.cechComplexFunctor,
    CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor_obj_d]
  rw [CochainComplex.of_d]
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  rw [Preadditive.sum_comp, Finset.sum_congr rfl (fun i _ => Preadditive.zsmul_comp _ _ _)]
  simp only [CosimplicialObject.δ, FormalCoproduct.cosimplicialObjectFunctor_obj_map,
    Pi.lift_comp_π]

end Work.DSF1.Cech
