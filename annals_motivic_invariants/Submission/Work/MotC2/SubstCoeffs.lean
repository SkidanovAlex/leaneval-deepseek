import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Polynomial WeierstrassCurve.Affine

namespace Work.MotC2

variable {L : Type*} [Field L]

/-! ## Auxiliary: comparing coefficients in the coordinate ring

`Coord E = L[X,Y]/(W_E)` is free over `L[X]` with basis `{1, y}`; `L(E)` is its fraction field.
The element `P(x) + Q(x)·y` is therefore zero in `L(E)` (equivalently in `Coord E`) only when both
`P` and `Q` are zero.  We record the two halves of that statement. -/

/-- `algebraMap` from the polynomial ring to the coordinate ring is evaluation at `x`. -/
lemma algebraMap_poly_coord (E : WeierstrassCurve L) (p : L[X]) :
    algebraMap (L[X]) (Coord E) p = p.eval₂ (algebraMap L (Coord E)) (coordX E) := by
  have h := Polynomial.eval_unique (IsScalarTower.toAlgHom L (L[X]) (Coord E)) p
  simpa only [IsScalarTower.toAlgHom_apply, algebraMap_X_eq_coordX] using h

/-- `algebraMap` from the polynomial ring to the function field is evaluation at `x`. -/
lemma algebraMap_poly_func (E : WeierstrassCurve L) (p : L[X]) :
    algebraMap (L[X]) (Func E) p = p.eval₂ (algebraMap L (Func E)) (genX E) := by
  have h := Polynomial.eval_unique (IsScalarTower.toAlgHom L (L[X]) (Func E)) p
  have hx : (IsScalarTower.toAlgHom L (L[X]) (Func E)) X = genX E := by
    rw [IsScalarTower.toAlgHom_apply, genX,
      IsScalarTower.algebraMap_apply (L[X]) (Coord E) (Func E) X, algebraMap_X_eq_coordX]
  simpa only [IsScalarTower.toAlgHom_apply, hx] using h

lemma smul_one_eq (E : WeierstrassCurve L) (p : L[X]) :
    p • (1 : Coord E) = algebraMap (L[X]) (Coord E) p := by
  rw [Algebra.algebraMap_eq_smul_one]

lemma smul_coordY_eq (E : WeierstrassCurve L) (p : L[X]) :
    p • coordY E = algebraMap (L[X]) (Coord E) p * coordY E := by
  rw [Algebra.smul_def]

/-! ## The substituted Weierstrass relation, in normal form -/

/-- `P(X) = e²C(X) + (c+dX)² + (a₁(a+bX)+a₃)(c+dX) - C(a+bX)`, written with the coefficients of
the powers of `X` displayed separately. -/
noncomputable def SubstP (E : WeierstrassCurve L) (a b c d e : L) : L[X] :=
  C (e ^ 2 - b ^ 3) * X ^ 3
  + C (d ^ 2 + E.a₂ * e ^ 2 + E.a₁ * b * d - 3 * a * b ^ 2 - E.a₂ * b ^ 2) * X ^ 2
  + C (2 * c * d + E.a₄ * e ^ 2 + (E.a₁ * a + E.a₃) * d + E.a₁ * b * c
      - 3 * a ^ 2 * b - 2 * E.a₂ * a * b - E.a₄ * b) * X
  + C (c ^ 2 + E.a₆ * e ^ 2 + (E.a₁ * a + E.a₃) * c - a ^ 3 - E.a₂ * a ^ 2 - E.a₄ * a - E.a₆)

/-- `Q(X) = e·((2d + a₁(b-e))X + (2c + a₁a + a₃(1-e)))`. -/
noncomputable def SubstQ (E : WeierstrassCurve L) (a b c d e : L) : L[X] :=
  C (e * (2 * d + E.a₁ * (b - e))) * X + C (e * (2 * c + E.a₁ * a + E.a₃ * (1 - e)))

lemma SubstP_coeff_3 (E : WeierstrassCurve L) (a b c d e : L) :
    (SubstP E a b c d e).coeff 3 = e ^ 2 - b ^ 3 := by
  simp only [SubstP, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  norm_num

lemma SubstP_coeff_2 (E : WeierstrassCurve L) (a b c d e : L) :
    (SubstP E a b c d e).coeff 2 =
      d ^ 2 + E.a₂ * e ^ 2 + E.a₁ * b * d - 3 * a * b ^ 2 - E.a₂ * b ^ 2 := by
  simp only [SubstP, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  norm_num

lemma SubstP_coeff_1 (E : WeierstrassCurve L) (a b c d e : L) :
    (SubstP E a b c d e).coeff 1 =
      2 * c * d + E.a₄ * e ^ 2 + (E.a₁ * a + E.a₃) * d + E.a₁ * b * c
        - 3 * a ^ 2 * b - 2 * E.a₂ * a * b - E.a₄ * b := by
  simp only [SubstP, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  norm_num

lemma SubstP_coeff_0 (E : WeierstrassCurve L) (a b c d e : L) :
    (SubstP E a b c d e).coeff 0 =
      c ^ 2 + E.a₆ * e ^ 2 + (E.a₁ * a + E.a₃) * c - a ^ 3 - E.a₂ * a ^ 2 - E.a₄ * a - E.a₆ := by
  simp only [SubstP, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  norm_num

lemma SubstQ_coeff_1 (E : WeierstrassCurve L) (a b c d e : L) :
    (SubstQ E a b c d e).coeff 1 = e * (2 * d + E.a₁ * (b - e)) := by
  simp only [SubstQ, coeff_add, coeff_C_mul_X, coeff_C]
  norm_num

lemma SubstQ_coeff_0 (E : WeierstrassCurve L) (a b c d e : L) :
    (SubstQ E a b c d e).coeff 0 = e * (2 * c + E.a₁ * a + E.a₃ * (1 - e)) := by
  simp only [SubstQ, coeff_add, coeff_C_mul_X, coeff_C]
  norm_num

/-- Substituting `x ↦ a + b·x`, `y ↦ c + d·x + e·y` into the Weierstrass relation of `E`, and using
`y² = C(x) - (a₁x+a₃)y` to reduce the result mod `W_E`, expresses the substituted relation as
`P(x) + Q(x)·y` with `P` of degree `≤ 3` and `Q` of degree `≤ 1`. -/
lemma subst_relation_coord (E : WeierstrassCurve L) (a b c d e : L) :
    (algebraMap L (Coord E) c + algebraMap L (Coord E) d * coordX E
        + algebraMap L (Coord E) e * coordY E) ^ 2
      + algebraMap L (Coord E) E.a₁
          * (algebraMap L (Coord E) a + algebraMap L (Coord E) b * coordX E)
          * (algebraMap L (Coord E) c + algebraMap L (Coord E) d * coordX E
              + algebraMap L (Coord E) e * coordY E)
      + algebraMap L (Coord E) E.a₃
          * (algebraMap L (Coord E) c + algebraMap L (Coord E) d * coordX E
              + algebraMap L (Coord E) e * coordY E)
    = (algebraMap L (Coord E) a + algebraMap L (Coord E) b * coordX E) ^ 3
      + algebraMap L (Coord E) E.a₂
          * (algebraMap L (Coord E) a + algebraMap L (Coord E) b * coordX E) ^ 2
      + algebraMap L (Coord E) E.a₄
          * (algebraMap L (Coord E) a + algebraMap L (Coord E) b * coordX E)
      + algebraMap L (Coord E) E.a₆
      + SubstP E a b c d e • (1 : Coord E) + SubstQ E a b c d e • coordY E := by
  have hy : coordY E ^ 2 = (coordX E) ^ 3 + algebraMap L (Coord E) E.a₂ * (coordX E) ^ 2
      + algebraMap L (Coord E) E.a₄ * coordX E + algebraMap L (Coord E) E.a₆
      - (algebraMap L (Coord E) E.a₁ * coordX E + algebraMap L (Coord E) E.a₃) * coordY E := by
    linear_combination (norm := first | refl_ring1 | ring1) coordY_sq_relation E
  rw [smul_one_eq E (SubstP E a b c d e), smul_coordY_eq E (SubstQ E a b c d e),
    algebraMap_poly_coord, algebraMap_poly_coord]
  simp only [SubstP, SubstQ, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X, Polynomial.eval₂_pow]
  simp only [map_add, map_mul, map_pow, map_sub, map_ofNat, map_one]
  ring_nf
  rw [hy]
  first | refl_ring1 | ring

/-! ## From the function field to the coordinate ring -/

/-- The image in `L(E)` of the coordinate-ring version of the substituted relation is the
function-field version. -/
lemma algebraMap_subst_LHS (E : WeierstrassCurve L) (a b c d e : L) :
    algebraMap (Coord E) (Func E)
      ((algebraMap L (Coord E) c + algebraMap L (Coord E) d * coordX E
          + algebraMap L (Coord E) e * coordY E) ^ 2
        + algebraMap L (Coord E) E.a₁
            * (algebraMap L (Coord E) a + algebraMap L (Coord E) b * coordX E)
            * (algebraMap L (Coord E) c + algebraMap L (Coord E) d * coordX E
                + algebraMap L (Coord E) e * coordY E)
        + algebraMap L (Coord E) E.a₃
            * (algebraMap L (Coord E) c + algebraMap L (Coord E) d * coordX E
                + algebraMap L (Coord E) e * coordY E))
      = (algebraMap L (Func E) c + algebraMap L (Func E) d * genX E
          + algebraMap L (Func E) e * genY E) ^ 2
        + algebraMap L (Func E) E.a₁
            * (algebraMap L (Func E) a + algebraMap L (Func E) b * genX E)
            * (algebraMap L (Func E) c + algebraMap L (Func E) d * genX E
                + algebraMap L (Func E) e * genY E)
        + algebraMap L (Func E) E.a₃
            * (algebraMap L (Func E) c + algebraMap L (Func E) d * genX E
                + algebraMap L (Func E) e * genY E) := by
  simp only [map_add, map_mul, map_pow, IsScalarTower.algebraMap_apply L (Coord E) (Func E),
    genX, genY]

lemma algebraMap_subst_RHS (E : WeierstrassCurve L) (a b : L) :
    algebraMap (Coord E) (Func E)
      ((algebraMap L (Coord E) a + algebraMap L (Coord E) b * coordX E) ^ 3
        + algebraMap L (Coord E) E.a₂
            * (algebraMap L (Coord E) a + algebraMap L (Coord E) b * coordX E) ^ 2
        + algebraMap L (Coord E) E.a₄
            * (algebraMap L (Coord E) a + algebraMap L (Coord E) b * coordX E)
        + algebraMap L (Coord E) E.a₆)
      = (algebraMap L (Func E) a + algebraMap L (Func E) b * genX E) ^ 3
        + algebraMap L (Func E) E.a₂
            * (algebraMap L (Func E) a + algebraMap L (Func E) b * genX E) ^ 2
        + algebraMap L (Func E) E.a₄
            * (algebraMap L (Func E) a + algebraMap L (Func E) b * genX E)
        + algebraMap L (Func E) E.a₆ := by
  simp only [map_add, map_mul, map_pow, IsScalarTower.algebraMap_apply L (Coord E) (Func E),
    genX]

/-- If the substituted Weierstrass relation holds in `L(E)`, then `P(x) + Q(x)·y = 0` in the
coordinate ring. -/
lemma subst_eq_zero (E : WeierstrassCurve L) (a b c d e : L)
    (h : (algebraMap L (Func E) c + algebraMap L (Func E) d * genX E +
            algebraMap L (Func E) e * genY E) ^ 2
        + algebraMap L (Func E) E.a₁ *
            (algebraMap L (Func E) a + algebraMap L (Func E) b * genX E) *
            (algebraMap L (Func E) c + algebraMap L (Func E) d * genX E +
              algebraMap L (Func E) e * genY E)
        + algebraMap L (Func E) E.a₃ *
            (algebraMap L (Func E) c + algebraMap L (Func E) d * genX E +
              algebraMap L (Func E) e * genY E)
      = (algebraMap L (Func E) a + algebraMap L (Func E) b * genX E) ^ 3
        + algebraMap L (Func E) E.a₂ *
            (algebraMap L (Func E) a + algebraMap L (Func E) b * genX E) ^ 2
        + algebraMap L (Func E) E.a₄ *
            (algebraMap L (Func E) a + algebraMap L (Func E) b * genX E)
        + algebraMap L (Func E) E.a₆) :
    SubstP E a b c d e • (1 : Coord E) + SubstQ E a b c d e • coordY E = 0 := by
  have h1 := congrArg (algebraMap (Coord E) (Func E)) (subst_relation_coord E a b c d e)
  rw [algebraMap_subst_LHS E a b c d e, map_add, map_add, algebraMap_subst_RHS E a b,
    ← h] at h1
  have hZ : algebraMap (Coord E) (Func E) (SubstP E a b c d e • (1 : Coord E)) +
      algebraMap (Coord E) (Func E) (SubstQ E a b c d e • coordY E) = 0 := by
    linear_combination (norm := first | refl_ring1 | ring1) h1.symm
  have hkey : algebraMap (Coord E) (Func E)
      (SubstP E a b c d e • (1 : Coord E) + SubstQ E a b c d e • coordY E) = 0 := by
    simpa only [map_add] using hZ
  exact IsFractionRing.injective (Coord E) (Func E) (by rw [hkey, map_zero])

/-- Substituting `x ↦ a + b·x`, `y ↦ c + d·x + e·y` into the Weierstrass relation and comparing
coefficients of the resulting element `P(x) + Q(x)·y` of `L(E)` (using that `{1, y}` is a basis of
`L(E)` over `L(x)`, resp. of `Coord E` over `L[X]`) gives the six scalar relations below.  These are
exactly the coefficients of
`P(X) = e²C(X) + (c+dX)² + (a₁(a+bX)+a₃)(c+dX) - C(a+bX)` (degree ≤ 3) and
`Q(X) = e·((2d + a₁(b-e))X + (2c + a₁a + a₃(1-e)))` (degree ≤ 1), where
`C(X) = X³ + a₂X² + a₄X + a₆`. -/
theorem SubstCoeffs (L : Type*) [Field L] (E : WeierstrassCurve L) [E.IsElliptic]
    (a b c d e : L)
    (h : (algebraMap L (Work.MotC2.Func E) c + algebraMap L (Work.MotC2.Func E) d * Work.MotC2.genX E +
            algebraMap L (Work.MotC2.Func E) e * Work.MotC2.genY E) ^ 2
        + algebraMap L (Work.MotC2.Func E) E.a₁ *
            (algebraMap L (Work.MotC2.Func E) a + algebraMap L (Work.MotC2.Func E) b * Work.MotC2.genX E) *
            (algebraMap L (Work.MotC2.Func E) c + algebraMap L (Work.MotC2.Func E) d * Work.MotC2.genX E +
              algebraMap L (Work.MotC2.Func E) e * Work.MotC2.genY E)
        + algebraMap L (Work.MotC2.Func E) E.a₃ *
            (algebraMap L (Work.MotC2.Func E) c + algebraMap L (Work.MotC2.Func E) d * Work.MotC2.genX E +
              algebraMap L (Work.MotC2.Func E) e * Work.MotC2.genY E)
      = (algebraMap L (Work.MotC2.Func E) a + algebraMap L (Work.MotC2.Func E) b * Work.MotC2.genX E) ^ 3
        + algebraMap L (Work.MotC2.Func E) E.a₂ *
            (algebraMap L (Work.MotC2.Func E) a + algebraMap L (Work.MotC2.Func E) b * Work.MotC2.genX E) ^ 2
        + algebraMap L (Work.MotC2.Func E) E.a₄ *
            (algebraMap L (Work.MotC2.Func E) a + algebraMap L (Work.MotC2.Func E) b * Work.MotC2.genX E)
        + algebraMap L (Work.MotC2.Func E) E.a₆) :
    e ^ 2 = b ^ 3 ∧
    e * (2 * d + E.a₁ * (b - e)) = 0 ∧
    e * (2 * c + E.a₁ * a + E.a₃ * (1 - e)) = 0 ∧
    d ^ 2 + E.a₂ * e ^ 2 + E.a₁ * b * d - 3 * a * b ^ 2 - E.a₂ * b ^ 2 = 0 ∧
    2 * c * d + E.a₄ * e ^ 2 + (E.a₁ * a + E.a₃) * d + E.a₁ * b * c - 3 * a ^ 2 * b -
      2 * E.a₂ * a * b - E.a₄ * b = 0 ∧
    c ^ 2 + E.a₆ * e ^ 2 + (E.a₁ * a + E.a₃) * c - a ^ 3 - E.a₂ * a ^ 2 - E.a₄ * a - E.a₆ = 0 := by
  have hk := subst_eq_zero E a b c d e h
  rw [coordY_eq_mk] at hk
  obtain ⟨hP, hQ⟩ := CoordinateRing.smul_basis_eq_zero hk
  have h1 : e ^ 2 = b ^ 3 := by
    have hc := congrArg (fun p : L[X] => p.coeff 3) hP
    simp only [SubstP_coeff_3, coeff_zero] at hc
    exact sub_eq_zero.mp hc
  have h2 : e * (2 * d + E.a₁ * (b - e)) = 0 := by
    have hc := congrArg (fun p : L[X] => p.coeff 1) hQ
    simpa only [SubstQ_coeff_1, coeff_zero] using hc
  have h3 : e * (2 * c + E.a₁ * a + E.a₃ * (1 - e)) = 0 := by
    have hc := congrArg (fun p : L[X] => p.coeff 0) hQ
    simpa only [SubstQ_coeff_0, coeff_zero] using hc
  have h4 : d ^ 2 + E.a₂ * e ^ 2 + E.a₁ * b * d - 3 * a * b ^ 2 - E.a₂ * b ^ 2 = 0 := by
    have hc := congrArg (fun p : L[X] => p.coeff 2) hP
    simpa only [SubstP_coeff_2, coeff_zero] using hc
  have h5 : 2 * c * d + E.a₄ * e ^ 2 + (E.a₁ * a + E.a₃) * d + E.a₁ * b * c - 3 * a ^ 2 * b -
      2 * E.a₂ * a * b - E.a₄ * b = 0 := by
    have hc := congrArg (fun p : L[X] => p.coeff 1) hP
    simpa only [SubstP_coeff_1, coeff_zero] using hc
  have h6 : c ^ 2 + E.a₆ * e ^ 2 + (E.a₁ * a + E.a₃) * c - a ^ 3 - E.a₂ * a ^ 2 - E.a₄ * a - E.a₆ = 0 := by
    have hc := congrArg (fun p : L[X] => p.coeff 0) hP
    simpa only [SubstP_coeff_0, coeff_zero] using hc
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end Work.MotC2
