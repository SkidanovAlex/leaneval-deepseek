import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.MotC2.SubstCoeffs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `cross_coeff_three`: comparing the `X³`-coefficient of the substituted Weierstrass relation

Let `E, E'` be Weierstrass curves over a field `L` and let `a b c d e : L`.  Suppose that in the
function field `L(E')` the point `(a + b·x, c + d·x + e·y)` satisfies the Weierstrass equation of
`E`.  Then `e² = b³`.

The proof is a coefficient comparison.  Writing `x = coordX E'`, `y = coordY E'` for the classes of
the coordinates in the affine coordinate ring `L[E'] = L[X,Y]/(W_{E'})`, and using the reduction
`y² = x³ + E'.a₂x² + E'.a₄x + E'.a₆ - (E'.a₁x + E'.a₃)y`, the left hand side minus the right hand
side of the equation reduces to `P(x) + Q(x)·y` with `P, Q ∈ L[X]` displayed below.  Since
`{1, y}` is an `L[X]`-basis of `L[E']` (Mathlib's `CoordinateRing.basis`), the relation forces
`P = 0`; the coefficient of `X³` of `P` is `e² - b³`.

This is the two-curve version of `Work.MotC2.SubstCoeffs`; the curve `E` supplies the coefficients
`a₁, …, a₆` while the curve `E'` supplies the function field.  Only the coefficient of `X³` is
needed, but the full normal form is most easily produced by the same `ring` computation.
-/

namespace Work.MotK.TwRuling

open Polynomial WeierstrassCurve.Affine
open Work.MotC2

/-! ## Two-curve analogues of `SubstP`, `SubstQ` and the reduction identity -/

/-- `P(X) = e²C(X) + (c+dX)² + (a₁(a+bX)+a₃)(c+dX) - C(a+bX)` reduced with the Weierstrass
relation of `E'`, i.e. with `C(X) = X³ + E'.a₂X² + E'.a₄X + E'.a₆`, while the coefficients `aᵢ` are
those of `E`; written with the powers of `X` displayed separately. -/
noncomputable def SubstP2 (L : Type*) [Field L] (E E' : WeierstrassCurve L) (a b c d e : L) : L[X] :=
  C (e ^ 2 - b ^ 3) * X ^ 3
  + C (d ^ 2 + E'.a₂ * e ^ 2 + E.a₁ * b * d - 3 * a * b ^ 2 - E.a₂ * b ^ 2) * X ^ 2
  + C (2 * c * d + E'.a₄ * e ^ 2 + (E.a₁ * a + E.a₃) * d + E.a₁ * b * c
      - 3 * a ^ 2 * b - 2 * E.a₂ * a * b - E.a₄ * b) * X
  + C (c ^ 2 + E'.a₆ * e ^ 2 + (E.a₁ * a + E.a₃) * c - a ^ 3 - E.a₂ * a ^ 2 - E.a₄ * a - E.a₆)

/-- `Q(X) = e·((2d + a₁b - E'.a₁e)X + (2c + a₁a + a₃ - e·E'.a₃))`. -/
noncomputable def SubstQ2 (L : Type*) [Field L] (E E' : WeierstrassCurve L) (a b c d e : L) : L[X] :=
  C (e * (2 * d + E.a₁ * b - E'.a₁ * e)) * X + C (e * (2 * c + E.a₁ * a + E.a₃ - e * E'.a₃))

/-- The coefficient of `X³` in `SubstP2` is `e² - b³`, independently of the curves. -/
lemma SubstP2_coeff_3 (L : Type*) [Field L] (E E' : WeierstrassCurve L) (a b c d e : L) :
    (SubstP2 L E E' a b c d e).coeff 3 = e ^ 2 - b ^ 3 := by
  simp only [SubstP2, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  norm_num

/-- Substituting `x ↦ a + b·x`, `y ↦ c + d·x + e·y` into the Weierstrass equation of `E` (with the
coordinates of `E'`), and reducing modulo the Weierstrass relation of `E'`, expresses the
difference of the two sides as `P(x) + Q(x)·y` with `P = SubstP2` and `Q = SubstQ2`. -/
lemma subst_relation_coord2 (L : Type*) [Field L] (E E' : WeierstrassCurve L) (a b c d e : L) :
    (algebraMap L (Coord E') c + algebraMap L (Coord E') d * coordX E'
        + algebraMap L (Coord E') e * coordY E') ^ 2
      + algebraMap L (Coord E') E.a₁
          * (algebraMap L (Coord E') a + algebraMap L (Coord E') b * coordX E')
          * (algebraMap L (Coord E') c + algebraMap L (Coord E') d * coordX E'
              + algebraMap L (Coord E') e * coordY E')
      + algebraMap L (Coord E') E.a₃
          * (algebraMap L (Coord E') c + algebraMap L (Coord E') d * coordX E'
              + algebraMap L (Coord E') e * coordY E')
    = (algebraMap L (Coord E') a + algebraMap L (Coord E') b * coordX E') ^ 3
      + algebraMap L (Coord E') E.a₂
          * (algebraMap L (Coord E') a + algebraMap L (Coord E') b * coordX E') ^ 2
      + algebraMap L (Coord E') E.a₄
          * (algebraMap L (Coord E') a + algebraMap L (Coord E') b * coordX E')
      + algebraMap L (Coord E') E.a₆
      + SubstP2 L E E' a b c d e • (1 : Coord E')
      + SubstQ2 L E E' a b c d e • coordY E' := by
  have hy : coordY E' ^ 2 = (coordX E') ^ 3 + algebraMap L (Coord E') E'.a₂ * (coordX E') ^ 2
      + algebraMap L (Coord E') E'.a₄ * coordX E' + algebraMap L (Coord E') E'.a₆
      - (algebraMap L (Coord E') E'.a₁ * coordX E' + algebraMap L (Coord E') E'.a₃) * coordY E' := by
    linear_combination (norm := refl_ring1) coordY_sq_relation E'
  rw [smul_one_eq E' (SubstP2 L E E' a b c d e), smul_coordY_eq E' (SubstQ2 L E E' a b c d e),
    algebraMap_poly_coord, algebraMap_poly_coord]
  simp only [SubstP2, SubstQ2, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X, Polynomial.eval₂_pow]
  simp only [map_add, map_mul, map_pow, map_sub, map_ofNat]
  ring_nf
  rw [hy]
  refl_ring1

/-! ## From the function field to the coordinate ring -/

/-- The image in `L(E')` of the coordinate-ring version of the left hand side is the function-field
version. -/
lemma algebraMap_subst_LHS2 (L : Type*) [Field L] (E E' : WeierstrassCurve L) (a b c d e : L) :
    algebraMap (Coord E') (Func E')
      ((algebraMap L (Coord E') c + algebraMap L (Coord E') d * coordX E'
          + algebraMap L (Coord E') e * coordY E') ^ 2
        + algebraMap L (Coord E') E.a₁
            * (algebraMap L (Coord E') a + algebraMap L (Coord E') b * coordX E')
            * (algebraMap L (Coord E') c + algebraMap L (Coord E') d * coordX E'
                + algebraMap L (Coord E') e * coordY E')
        + algebraMap L (Coord E') E.a₃
            * (algebraMap L (Coord E') c + algebraMap L (Coord E') d * coordX E'
                + algebraMap L (Coord E') e * coordY E'))
      = (algebraMap L (Func E') c + algebraMap L (Func E') d * genX E'
          + algebraMap L (Func E') e * genY E') ^ 2
        + algebraMap L (Func E') E.a₁
            * (algebraMap L (Func E') a + algebraMap L (Func E') b * genX E')
            * (algebraMap L (Func E') c + algebraMap L (Func E') d * genX E'
                + algebraMap L (Func E') e * genY E')
        + algebraMap L (Func E') E.a₃
            * (algebraMap L (Func E') c + algebraMap L (Func E') d * genX E'
                + algebraMap L (Func E') e * genY E') := by
  simp only [map_add, map_mul, map_pow, IsScalarTower.algebraMap_apply L (Coord E') (Func E'),
    genX, genY]

/-- The image in `L(E')` of the coordinate-ring version of the right hand side is the
function-field version. -/
lemma algebraMap_subst_RHS2 (L : Type*) [Field L] (E E' : WeierstrassCurve L) (a b : L) :
    algebraMap (Coord E') (Func E')
      ((algebraMap L (Coord E') a + algebraMap L (Coord E') b * coordX E') ^ 3
        + algebraMap L (Coord E') E.a₂
            * (algebraMap L (Coord E') a + algebraMap L (Coord E') b * coordX E') ^ 2
        + algebraMap L (Coord E') E.a₄
            * (algebraMap L (Coord E') a + algebraMap L (Coord E') b * coordX E')
        + algebraMap L (Coord E') E.a₆)
      = (algebraMap L (Func E') a + algebraMap L (Func E') b * genX E') ^ 3
        + algebraMap L (Func E') E.a₂
            * (algebraMap L (Func E') a + algebraMap L (Func E') b * genX E') ^ 2
        + algebraMap L (Func E') E.a₄
            * (algebraMap L (Func E') a + algebraMap L (Func E') b * genX E')
        + algebraMap L (Func E') E.a₆ := by
  simp only [map_add, map_mul, map_pow, IsScalarTower.algebraMap_apply L (Coord E') (Func E'),
    genX]

/-- If the substituted Weierstrass equation of `E` holds for the coordinates of `E'` in `L(E')`,
then `P(x) + Q(x)·y = 0` in the coordinate ring `L[E']`. -/
lemma subst_eq_zero2 (L : Type*) [Field L] (E E' : WeierstrassCurve L) (a b c d e : L)
    (h : (algebraMap L (Func E') c + algebraMap L (Func E') d * genX E' +
            algebraMap L (Func E') e * genY E') ^ 2
        + algebraMap L (Func E') E.a₁ *
            (algebraMap L (Func E') a + algebraMap L (Func E') b * genX E') *
            (algebraMap L (Func E') c + algebraMap L (Func E') d * genX E' +
              algebraMap L (Func E') e * genY E')
        + algebraMap L (Func E') E.a₃ *
            (algebraMap L (Func E') c + algebraMap L (Func E') d * genX E' +
              algebraMap L (Func E') e * genY E')
      = (algebraMap L (Func E') a + algebraMap L (Func E') b * genX E') ^ 3
        + algebraMap L (Func E') E.a₂ *
            (algebraMap L (Func E') a + algebraMap L (Func E') b * genX E') ^ 2
        + algebraMap L (Func E') E.a₄ *
            (algebraMap L (Func E') a + algebraMap L (Func E') b * genX E')
        + algebraMap L (Func E') E.a₆) :
    SubstP2 L E E' a b c d e • (1 : Coord E') + SubstQ2 L E E' a b c d e • coordY E' = 0 := by
  have h1 := congrArg (algebraMap (Coord E') (Func E')) (subst_relation_coord2 L E E' a b c d e)
  rw [algebraMap_subst_LHS2 L E E' a b c d e, map_add, map_add,
    algebraMap_subst_RHS2 L E E' a b, ← h] at h1
  have hZ : algebraMap (Coord E') (Func E') (SubstP2 L E E' a b c d e • (1 : Coord E')) +
      algebraMap (Coord E') (Func E') (SubstQ2 L E E' a b c d e • coordY E') = 0 := by
    linear_combination (norm := refl_ring1) h1.symm
  have hkey : algebraMap (Coord E') (Func E')
      (SubstP2 L E E' a b c d e • (1 : Coord E') + SubstQ2 L E E' a b c d e • coordY E') = 0 := by
    simpa only [map_add] using hZ
  exact IsFractionRing.injective (Coord E') (Func E') (by rw [hkey, map_zero])

/-! ## The requested lemma -/

lemma cross_coeff_three (L : Type*) [Field L] (E E' : WeierstrassCurve L) (a b c d e : L)
    (h : (algebraMap L (Work.MotC2.Func E') c + algebraMap L (Work.MotC2.Func E') d * Work.MotC2.genX E'
            + algebraMap L (Work.MotC2.Func E') e * Work.MotC2.genY E') ^ 2
        + algebraMap L (Work.MotC2.Func E') E.a₁
            * (algebraMap L (Work.MotC2.Func E') a + algebraMap L (Work.MotC2.Func E') b * Work.MotC2.genX E')
            * (algebraMap L (Work.MotC2.Func E') c + algebraMap L (Work.MotC2.Func E') d * Work.MotC2.genX E'
                + algebraMap L (Work.MotC2.Func E') e * Work.MotC2.genY E')
        + algebraMap L (Work.MotC2.Func E') E.a₃
            * (algebraMap L (Work.MotC2.Func E') c + algebraMap L (Work.MotC2.Func E') d * Work.MotC2.genX E'
                + algebraMap L (Work.MotC2.Func E') e * Work.MotC2.genY E')
      = (algebraMap L (Work.MotC2.Func E') a + algebraMap L (Work.MotC2.Func E') b * Work.MotC2.genX E') ^ 3
        + algebraMap L (Work.MotC2.Func E') E.a₂
            * (algebraMap L (Work.MotC2.Func E') a + algebraMap L (Work.MotC2.Func E') b * Work.MotC2.genX E') ^ 2
        + algebraMap L (Work.MotC2.Func E') E.a₄
            * (algebraMap L (Work.MotC2.Func E') a + algebraMap L (Work.MotC2.Func E') b * Work.MotC2.genX E')
        + algebraMap L (Work.MotC2.Func E') E.a₆) :
    e ^ 2 = b ^ 3 := by
  have hk := subst_eq_zero2 L E E' a b c d e h
  rw [coordY_eq_mk] at hk
  obtain ⟨hP, hQ⟩ := CoordinateRing.smul_basis_eq_zero hk
  have h1 : (SubstP2 L E E' a b c d e).coeff 3 = 0 := by rw [hP, coeff_zero]
  rw [SubstP2_coeff_3] at h1
  linear_combination (norm := refl_ring1) h1

end Work.MotK.TwRuling
