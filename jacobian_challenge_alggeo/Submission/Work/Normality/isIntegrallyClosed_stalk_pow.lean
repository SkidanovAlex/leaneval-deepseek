import Mathlib
import Submission.Work.Normality.Basic
import Submission.Work.Normality.CurvePow
import Submission.Work.Normality.Scheme
import Submission.Work.Normality.hasIntegrallyClosedStalks_of_smooth

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace Work.Normality

/-- The structure morphism `Cⁿ ⟶ Spec K` of the `n`-fold product of a curve with itself is
smooth.  Indeed `Cⁿ = C^{n-1} ⊗ C` and `(C^{n-1} ⊗ C).hom = pullback.fst ≫ (C^{n-1}).hom`; the
projection is a base change of the smooth morphism `C.hom` and `(C^{n-1}).hom` is smooth by
induction. -/
private theorem pow_smooth {K : Type u} [Field K] (C : Work.CurveBasics.Curve K) (n : ℕ) :
    Smooth (Curve.pow C n).hom := by
  haveI : Smooth C.hom := SmoothOfRelativeDimension.smooth 1 C.hom
  induction n with
  | zero => exact (inferInstance : Smooth (𝟙 (Spec (CommRingCat.of K))))
  | succ n ih =>
    rw [Curve.pow_succ, Over.tensorObj_hom]
    exact inferInstance

/-- The `n`-fold product of a curve with itself is locally noetherian: its structure morphism is
smooth, hence locally of finite type, and the base `Spec K` is locally noetherian. -/
private theorem pow_isLocallyNoetherian {K : Type u} [Field K] (C : Work.CurveBasics.Curve K)
    (n : ℕ) : IsLocallyNoetherian (Curve.pow C n).left := by
  haveI : Smooth (Curve.pow C n).hom := pow_smooth C n
  exact LocallyOfFiniteType.isLocallyNoetherian (Curve.pow C n).hom

/-- The `n`-fold product of a curve with itself is integral.  For `n = 0` this is `Spec K`, and in
the step `C^{n+1} = Cⁿ ×_K C` this is the instance
`AlgebraicGeometry.GeometricallyIntegral.isIntegral_of_isLocallyNoetherian` applied to the
geometrically integral, flat and universally open morphism `C.hom`. -/
private theorem pow_isIntegral {K : Type u} [Field K] (C : Work.CurveBasics.Curve K) (n : ℕ) :
    IsIntegral (Curve.pow C n).left := by
  haveI : Smooth C.hom := SmoothOfRelativeDimension.smooth 1 C.hom
  induction n with
  | zero => exact (inferInstance : IsIntegral (Spec (CommRingCat.of K)))
  | succ n ih =>
    rw [Curve.pow_succ, Over.tensorObj_left]
    haveI : IsIntegral (Curve.pow C n).left := ih
    haveI : IsLocallyNoetherian (Curve.pow C n).left := pow_isLocallyNoetherian C n
    exact inferInstance

/-- Every local ring of the `n`-fold product `Cⁿ` of a curve with itself over `K` is integrally
closed (i.e. `Cⁿ` is normal).

Suggested proof.  Show `Work.Normality.HasIntegrallyClosedStalks (Curve.pow C n)` using
`Work.Normality.hasIntegrallyClosedStalks_of_smooth`, which needs
`AlgebraicGeometry.Smooth (Curve.pow C n).hom` and `AlgebraicGeometry.IsIntegral (Curve.pow C n).left`;
prove both by induction on `n`:
* for `n = 0`, `Curve.pow C 0 = 𝟙_ (Sch K)` has structure map `𝟙 (Spec K)`, smooth because it is
  an isomorphism, and `Spec K` is integral;
* in the step `Curve.pow C (n+1) = Curve.pow C n ⊗ C.toOver` the structure morphism is
  `pullback.fst (Curve.pow C n).hom C.hom ≫ (Curve.pow C n).hom`
  (`CategoryTheory.Over.tensorObj_hom`, `CategoryTheory.Over.tensorObj_left`); smoothness follows
  from stability of smoothness under base change (`AlgebraicGeometry.smooth_isStableUnderBaseChange`)
  and under composition.  For integrality of
  `pullback ((Curve.pow C n).hom) C.hom = (Curve.pow C n ⊗ C.toOver).left` use the instance
  `AlgebraicGeometry.GeometricallyIntegral.isIntegral_of_isLocallyNoetherian` for the square with
  `g := C.hom`: `C.hom` is geometrically integral (from the fields `geomIrred`, `geomReduced` of
  `Work.CurveBasics.Curve`), flat and universally open (both follow from
  `SmoothOfRelativeDimension 1 C.hom`), and `(Curve.pow C n).left` is integral (induction
  hypothesis) and locally noetherian.

Finally `HasIntegrallyClosedStalks` unfolds to `∀ x, IsIntegrallyClosed (stalk x)`, which is the
claim at `x`. -/
theorem isIntegrallyClosed_stalk_pow {K : Type u} [Field K] (C : Work.CurveBasics.Curve K) (n : ℕ)
    (x : (Curve.pow C n).left) :
    IsIntegrallyClosed ((Curve.pow C n).left.presheaf.stalk x) := by
  haveI : Smooth (Curve.pow C n).hom := pow_smooth C n
  haveI : IsIntegral (Curve.pow C n).left := pow_isIntegral C n
  exact hasIntegrallyClosedStalks_of_smooth (Curve.pow C n).hom x

end Work.Normality
