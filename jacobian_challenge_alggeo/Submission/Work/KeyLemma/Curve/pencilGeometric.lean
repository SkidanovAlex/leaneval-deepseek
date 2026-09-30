import Mathlib
import Submission.Work.KeyLemma.Pencil
import Submission.Work.KeyLemma.Curve.pencilGeometric_of_isAlgClosed
import Submission.Work.KeyLemma.Unconditional
import Submission.Work.KeyLemma.BaseChange.SumMapBaseChange
import Submission.Work.KeyLemma.Curve.exists_ne_point_p1

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CartesianMonoidalCategory CategoryTheory.Obj

namespace Work.KeyLemma.Curve

universe u

/-- **The geometric input of the key lemma over an arbitrary field.**  Over an algebraically
closed field this is `Work.KeyLemma.Curve.pencilGeometric_of_isAlgClosed`; the general case is
obtained by base-changing the curve and the morphism `f` to the algebraic closure
`L = AlgebraicClosure k`, applying the algebraically closed case there
(`Work.KeyLemma.Curve.sumOfPoints_eq_of_linEquiv_baseChange`), and descending the resulting
equality of `L`-points with `Work.KeyLemma.Curve.Pt.baseChange_injective`.  Since every morphism
`ℙ¹ ⟶ A` into a proper group scheme is constant (`Work.KeyLemma.Curve.p1Const`), this equality
of sums is exactly the content of `Curve.PencilGeometric`. -/
theorem pencilGeometric {k : Type u} [Field k]
    (C : Work.CurveBasics.Curve k)
    {A : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))}
    [CategoryTheory.GrpObj A] [CategoryTheory.IsCommMonObj A]
    [AlgebraicGeometry.IsProper A.hom]
    (f : C.toOver ⟶ A) :
    Work.KeyLemma.Curve.PencilGeometric C f := by
  intro h hh hnc s₀ s₁ hs₀ hs₁
  -- The two sums of the pencil agree; they are computed after base change to the algebraic
  -- closure, where the algebraically closed case applies, and the equality descends.
  have heq : SumDiv.sumOfPoints C f s₀ = SumDiv.sumOfPoints C f s₁ := by
    have hlin : LinEquiv C (posPart C h) (negPart C h) :=
      ⟨h, hh, div_eq_posPart_sub_negPart C h⟩
    haveI hproper : IsProper ((baseChangeFunctor k (AlgebraicClosure k)).obj A).hom := by
      change IsProper (pullback.snd A.hom (Work.CurveBasics.Curve.specMap k (AlgebraicClosure k)))
      infer_instance
    have hgeo : PencilGeometric (Work.CurveBasics.Curve.baseChange C (AlgebraicClosure k))
        ((baseChangeFunctor k (AlgebraicClosure k)).map f) :=
      pencilGeometric_of_isAlgClosed
        (Work.CurveBasics.Curve.baseChange C (AlgebraicClosure k))
        ((baseChangeFunctor k (AlgebraicClosure k)).map f)
    have key := sumOfPoints_eq_of_linEquiv_baseChange C (AlgebraicClosure k) f hgeo hlin
        (s := SumDiv.baseChange C (AlgebraicClosure k) s₀)
        (s' := SumDiv.baseChange C (AlgebraicClosure k) s₁)
        (by rw [SumDiv.toDiv_baseChange, hs₀])
        (by rw [SumDiv.toDiv_baseChange, hs₁])
    rw [SumDiv.sumOfPoints_baseChange, SumDiv.sumOfPoints_baseChange] at key
    exact Pt.baseChange_injective (AlgebraicClosure k) key
  -- A constant morphism `ℙ¹ ⟶ A` with two distinct points of `ℙ¹` realises `Curve.PencilGeometric`.
  obtain ⟨z, i, hzi⟩ := exists_ne_point_p1 (k := k)
  refine ⟨SemiCartesianMonoidalCategory.toUnit (Work.AbVar.P1 k) ≫
      SumDiv.sumOfPoints C f s₀, z, i, hzi, ?_, ?_⟩
  · rw [← Category.assoc,
      show z ≫ SemiCartesianMonoidalCategory.toUnit (Work.AbVar.P1 k) =
        𝟙 (𝟙_ (Over (Spec (CommRingCat.of k)))) from Subsingleton.elim _ _, Category.id_comp]
  · rw [← Category.assoc,
      show i ≫ SemiCartesianMonoidalCategory.toUnit (Work.AbVar.P1 k) =
        𝟙 (𝟙_ (Over (Spec (CommRingCat.of k)))) from Subsingleton.elim _ _, Category.id_comp,
      heq]

end Work.KeyLemma.Curve
