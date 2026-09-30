import Mathlib
import Submission.Work.KeyLemma.Pencil
import Submission.Work.KeyLemma.Curve.PencilMap
import Submission.Work.KeyLemma.Curve.exists_ne_point_p1
import Submission.Work.KeyLemma.Curve.sumOfPoints_eq_of_pencil

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# The geometric input of the key lemma over an algebraically closed field

This file is the home of `Work.KeyLemma.Curve.pencilGeometric_of_isAlgClosed`, the residual
geometric input of the key lemma (area `KL`) over an algebraically closed field: see
`Submission/Work/KeyLemma/NOTES.md`, Addendum 3.

The pencil rational map `C ⇢ ℙ¹` of a rational function is in
`Submission.Work.KeyLemma.Curve.PencilMap`, and the existence of the (finite, flat, dominant)
pencil *morphism* is `Work.KeyLemma.Curve.exists_morphism_toP1`; the nondegeneracy of `ℙ¹(k)` is
`Work.KeyLemma.Curve.exists_ne_point_p1`.

The geometric content — that the two sums `Σ f(div₀ h)` and `Σ f(div_∞ h)` agree — is
`Work.KeyLemma.Curve.sumOfPoints_eq_of_pencil`, proved by constructing the fibrewise-sum
("norm") morphism `ℙ¹ ⟶ A`, `t ↦ ∏_{x ∈ h⁻¹(t)} f(x)`, and identifying its values at `0` and
`∞`.  Given that equality, the required morphism `φ : ℙ¹ ⟶ A` is the constant morphism at the
common value, and the two distinct points are supplied by `exists_ne_point_p1`.
-/

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CartesianMonoidalCategory

namespace Work.KeyLemma.Curve

open Work.CurveBasics

universe u

theorem pencilGeometric_of_isAlgClosed {k : Type u} [Field k] [IsAlgClosed k]
    (C : Work.CurveBasics.Curve k)
    {A : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))}
    [CategoryTheory.GrpObj A] [CategoryTheory.IsCommMonObj A]
    [AlgebraicGeometry.IsProper A.hom]
    (f : C.toOver ⟶ A) :
    Work.KeyLemma.Curve.PencilGeometric C f := by
  intro h hh hnc s₀ s₁ hs₀ hs₁
  obtain ⟨z, i, hzi⟩ := exists_ne_point_p1 (k := k)
  have heq : SumDiv.sumOfPoints C f s₀ = SumDiv.sumOfPoints C f s₁ :=
    sumOfPoints_eq_of_pencil f hh hnc s₀ s₁ hs₀ hs₁
  refine ⟨SemiCartesianMonoidalCategory.toUnit (Work.AbVar.P1 k) ≫ SumDiv.sumOfPoints C f s₀,
    z, i, hzi, ?_, ?_⟩
  · rw [← Category.assoc,
      show z ≫ SemiCartesianMonoidalCategory.toUnit (Work.AbVar.P1 k) =
        𝟙 (𝟙_ (Over (Spec (CommRingCat.of k)))) from Subsingleton.elim _ _, Category.id_comp]
  · rw [← Category.assoc,
      show i ≫ SemiCartesianMonoidalCategory.toUnit (Work.AbVar.P1 k) =
        𝟙 (𝟙_ (Over (Spec (CommRingCat.of k)))) from Subsingleton.elim _ _, Category.id_comp,
      heq]

end Work.KeyLemma.Curve
