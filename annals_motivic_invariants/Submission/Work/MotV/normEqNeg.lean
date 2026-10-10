import Mathlib
import Submission.Work.MotC2.Relations
import Submission.Work.MotC2.Negation
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The norm on the coordinate ring of a Weierstrass curve, via the negation `[-1]`

Let `E` be a Weierstrass curve over a field `N`.  Its affine coordinate ring
`Coord E = N[X,Y]/(W_E)` is free of rank `2` over `N[X]` with basis `{1, y}`, and the norm
`Algebra.norm N[X] : Coord E → N[X]` of an element `p + q·y` is

  `p ^ 2 - p * q * (C a₁ * X + C a₃) - q ^ 2 * (X ^ 3 + C a₂ * X ^ 2 + C a₄ * X + C a₆)`,

(Mathlib: `WeierstrassCurve.Affine.CoordinateRing.norm_smul_basis`).

This file records the geometric meaning of that formula: **the norm is the product of an element
with its image under the negation `[-1]` of the curve**,

  `↑(Algebra.norm N[X] b) = b * negCoordAlgEquiv E b`   in `Coord E`,

and, after descending to the function field `L(E)` (`Work.MotC2.negAlgEquiv`), the statement
`Work.MotV.normEqNeg`.

The proof is a direct computation in the basis `{1, y}`: for `b = p • 1 + q • y` the right-hand
side is `(P + Q·y)(P - Q·y - Q·(a₁x + a₃)) = P² - PQ(a₁x + a₃) - Q²(y² + (a₁x + a₃)y)`, and
`y² + (a₁x + a₃)y = x³ + a₂x² + a₄x + a₆` is the Weierstrass relation
(`Work.MotC2.coordY_sq_relation`).
-/

open Polynomial WeierstrassCurve.Affine

namespace Work.MotV

variable {N : Type*} [Field N]

/-! ## Two `algebraMap` computations in the coordinate ring -/

/-- The `(a₁X + a₃)`-factor of the Weierstrass polynomial, read in the coordinate ring. -/
lemma algebraMap_linCoef_coord (E : WeierstrassCurve N) :
    algebraMap (N[X]) (CoordinateRing E) (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃) =
      algebraMap N (CoordinateRing E) E.a₁ * Work.MotC2.coordX E +
        algebraMap N (CoordinateRing E) E.a₃ := by
  simp only [Polynomial.C_eq_algebraMap, map_add, map_mul,
    Work.MotC2.algebraMap_X_eq_coordX,
    IsScalarTower.algebraMap_apply N (Polynomial N) (CoordinateRing E)]

/-- The cubic factor of the Weierstrass polynomial, read in the coordinate ring. -/
lemma algebraMap_cubCoef_coord (E : WeierstrassCurve N) :
    algebraMap (N[X]) (CoordinateRing E)
        (Polynomial.X ^ 3 + Polynomial.C E.a₂ * Polynomial.X ^ 2 + Polynomial.C E.a₄ *
          Polynomial.X + Polynomial.C E.a₆) =
      (Work.MotC2.coordX E) ^ 3 + algebraMap N (CoordinateRing E) E.a₂ *
        (Work.MotC2.coordX E) ^ 2 + algebraMap N (CoordinateRing E) E.a₄ *
        Work.MotC2.coordX E + algebraMap N (CoordinateRing E) E.a₆ := by
  simp only [Polynomial.C_eq_algebraMap, map_add, map_mul, map_pow,
    Work.MotC2.algebraMap_X_eq_coordX,
    IsScalarTower.algebraMap_apply N (Polynomial N) (CoordinateRing E)]

/-! ## The negation fixes the image of `N[X]` -/

/-- The negation `[-1]` of the coordinate ring fixes the image of `N[X]`: it acts on the affine
coordinates by `x ↦ x`, `y ↦ -y - (a₁x + a₃)`. -/
lemma negCoordAlgEquiv_algebraMap (E : WeierstrassCurve N) (r : N[X]) :
    Work.MotC2.negCoordAlgEquiv E (algebraMap (N[X]) (CoordinateRing E) r) =
      algebraMap (N[X]) (CoordinateRing E) r := by
  rw [Work.MotC2.negCoordAlgEquiv, AlgEquiv.ofAlgHom_apply, AdjoinRoot.algebraMap_eq]
  exact Work.MotC2.negCoordHom_of E r

/-! ## The norm is the product with the negation -/

/-- **The norm of the affine coordinate ring is the product of an element with its negation.**
For every `b : N[X,Y]/(W_E)`, the algebra norm `Algebra.norm N[X] b ∈ N[X]`, viewed in
`N[X,Y]/(W_E)`, equals `b * (-1)^* b`. -/
lemma norm_coord_eq_mul_neg (E : WeierstrassCurve N) (b : CoordinateRing E) :
    algebraMap (N[X]) (CoordinateRing E) (Algebra.norm (Polynomial N) b) =
      b * Work.MotC2.negCoordAlgEquiv E b := by
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq (W' := E) b
  rw [CoordinateRing.norm_smul_basis (W' := E)]
  -- Expand the negation of the basis element `p • 1 + q • y`.
  have hneg : Work.MotC2.negCoordAlgEquiv E
        (p • (1 : CoordinateRing E) + q • (CoordinateRing.mk E) Polynomial.X) =
      p • (1 : CoordinateRing E) + q • (- (CoordinateRing.mk E) Polynomial.X -
        (algebraMap N (CoordinateRing E) E.a₁ * Work.MotC2.coordX E +
          algebraMap N (CoordinateRing E) E.a₃)) := by
    simp only [Algebra.smul_def, mul_one]
    rw [map_add, map_mul]
    rw [negCoordAlgEquiv_algebraMap E p, negCoordAlgEquiv_algebraMap E q]
    rw [← Work.MotC2.coordY_eq_mk, Work.MotC2.negCoordAlgEquiv_coordY, Work.MotC2.linCoef,
      algebraMap_linCoef_coord E]
  rw [hneg]
  rw [show (CoordinateRing.mk E) Polynomial.X = Work.MotC2.coordY E from
    (Work.MotC2.coordY_eq_mk E).symm]
  -- Push `algebraMap` through the norm formula and the product, then use the Weierstrass relation.
  simp only [map_sub, map_mul, map_pow, Algebra.smul_def, mul_one,
    algebraMap_linCoef_coord E, algebraMap_cubCoef_coord E]
  linear_combination (norm := first | refl_ring1 | ring1) ((algebraMap (N[X]) (CoordinateRing E) q) ^ 2) *
    Work.MotC2.coordY_sq_relation E

/-! ## The statement, in the function field -/

theorem normEqNeg {N : Type*} [Field N] (E : WeierstrassCurve N)
    (a : WeierstrassCurve.Affine.CoordinateRing E) :
    algebraMap (WeierstrassCurve.Affine.CoordinateRing E) (Work.MotC2.Func E)
        (Algebra.norm (Polynomial N) a) =
      algebraMap (WeierstrassCurve.Affine.CoordinateRing E) (Work.MotC2.Func E) a *
        Work.MotC2.negAlgEquiv E
          (algebraMap (WeierstrassCurve.Affine.CoordinateRing E) (Work.MotC2.Func E) a) := by
  have h := norm_coord_eq_mul_neg E a
  rw [← AdjoinRoot.algebraMap_eq]
  rw [h, map_mul]
  congr 1
  rw [Work.MotC2.negAlgEquiv, IsFractionRing.algEquivOfAlgEquiv_algebraMap]

end Work.MotV
