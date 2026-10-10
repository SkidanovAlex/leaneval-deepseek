import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.MotC2.Negation
import Submission.Work.MotV.invDerivAux
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Polynomial WeierstrassCurve.Affine

namespace Work.MotV

open MotC2

/-- The `N`-algebra homomorphism `N[X,Y] → N[E] = Coord E` sending the two variables to
`coordX E` and `coordY E`; it is the quotient map by the Weierstrass polynomial. -/
noncomputable def mkAlgHom {N : Type*} [Field N] (E : WeierstrassCurve N) :
    Polynomial (Polynomial N) →ₐ[N] MotC2.Coord E :=
  { AdjoinRoot.mk (WeierstrassCurve.Affine.polynomial E) with
    commutes' := by
      intro n
      rw [IsScalarTower.algebraMap_apply N (Polynomial N)
        (AdjoinRoot (WeierstrassCurve.Affine.polynomial E))]
      show AdjoinRoot.mk (WeierstrassCurve.Affine.polynomial E)
        (Polynomial.C (algebraMap N (Polynomial N) n)) = _
      rw [AdjoinRoot.mk_C]
      rfl }

variable {N : Type*} [Field N]

/-- The image of `polynomialY = 2Y + a₁X + a₃` (the `Y`-partial of the Weierstrass polynomial)
under the quotient map is `2 * y + a₁ * x + a₃`. -/
lemma mkAlgHom_polynomialY (E : WeierstrassCurve N) :
    (mkAlgHom E) (WeierstrassCurve.Affine.polynomialY E) =
      2 * MotC2.coordY E + algebraMap N (MotC2.Coord E) E.a₁ * MotC2.coordX E +
        algebraMap N (MotC2.Coord E) E.a₃ := by
  change AdjoinRoot.mk (WeierstrassCurve.Affine.polynomial E)
    (WeierstrassCurve.Affine.polynomialY E) = _
  rw [WeierstrassCurve.Affine.polynomialY]
  rw [map_add]
  rw [map_mul]
  rw [AdjoinRoot.mk_C, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
  rw [MotC2.of_poly_C]
  rw [map_add]
  rw [map_mul]
  rw [MotC2.of_poly_C, MotC2.of_poly_C]
  rw [show AdjoinRoot.of (WeierstrassCurve.Affine.polynomial E) Polynomial.X = MotC2.coordX E from rfl]
  rw [show AdjoinRoot.root (WeierstrassCurve.Affine.polynomial E) = MotC2.coordY E from rfl]
  rw [map_ofNat]
  first | refl_ring1 | ring

/-- The image of `-polynomialX = 3X² + 2a₂X + a₄ - a₁Y` under the quotient map is
`3x² + 2a₂x + a₄ - a₁y`. -/
lemma mkAlgHom_polynomialX (E : WeierstrassCurve N) :
    (mkAlgHom E) (-(WeierstrassCurve.Affine.polynomialX E)) =
      3 * (MotC2.coordX E) ^ 2 + 2 * algebraMap N (MotC2.Coord E) E.a₂ * MotC2.coordX E +
        algebraMap N (MotC2.Coord E) E.a₄ - algebraMap N (MotC2.Coord E) E.a₁ * MotC2.coordY E := by
  change AdjoinRoot.mk (WeierstrassCurve.Affine.polynomial E)
    (-(WeierstrassCurve.Affine.polynomialX E)) = _
  rw [map_neg]
  rw [WeierstrassCurve.Affine.polynomialX]
  rw [map_sub]
  rw [map_mul]
  rw [AdjoinRoot.mk_C, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
  rw [MotC2.of_poly_C]
  rw [map_add]
  rw [map_add]
  rw [map_mul]
  rw [map_mul]
  rw [map_pow]
  rw [MotC2.of_poly_C, MotC2.of_poly_C, MotC2.of_poly_C]
  rw [show AdjoinRoot.of (WeierstrassCurve.Affine.polynomial E) Polynomial.X = MotC2.coordX E from rfl]
  rw [show AdjoinRoot.root (WeierstrassCurve.Affine.polynomial E) = MotC2.coordY E from rfl]
  rw [show (algebraMap N (MotC2.Coord E)) (2 * E.a₂) = 2 * algebraMap N (MotC2.Coord E) E.a₂ from by
      rw [map_mul, map_ofNat]]
  rw [map_ofNat]
  first | refl_ring1 | ring

theorem invDeriv {N : Type*} [Field N] (E : WeierstrassCurve N) [E.IsElliptic] :
    ∃ D : Derivation N (Work.MotC2.Func E) (Work.MotC2.Func E),
      D (Work.MotC2.genX E) = 2 * Work.MotC2.genY E +
          algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genX E +
          algebraMap N (Work.MotC2.Func E) E.a₃ ∧
      D (Work.MotC2.genY E) = 3 * (Work.MotC2.genX E) ^ 2 +
          2 * algebraMap N (Work.MotC2.Func E) E.a₂ * Work.MotC2.genX E +
          algebraMap N (Work.MotC2.Func E) E.a₄ -
          algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genY E := by
  obtain ⟨d, hdX, hdY, hdW⟩ := BivDeriv.exists_deriv_bivariate (N := N) E
  have hfsurj : Function.Surjective (mkAlgHom E) := AdjoinRoot.mk_surjective
  have hker : ∀ x : Polynomial (Polynomial N), (mkAlgHom E) x = 0 → (mkAlgHom E) (d x) = 0 := by
    intro x hx
    have hx' : AdjoinRoot.mk (WeierstrassCurve.Affine.polynomial E) x = 0 := hx
    rw [AdjoinRoot.mk_eq_zero] at hx'
    obtain ⟨q, rfl⟩ := hx'
    have hW : (mkAlgHom E) (WeierstrassCurve.Affine.polynomial E) = 0 := AdjoinRoot.mk_self
    rw [Derivation.leibniz, map_add]
    simp only [smul_eq_mul, map_mul, map_zero, mul_zero, add_zero, hdW, hW, zero_mul]
  let Dcoord : Derivation N (MotC2.Coord E) (MotC2.Coord E) :=
    Derivation.liftOfSurjective (f := mkAlgHom E) hfsurj (d := d) hker
  have hcoordX : (mkAlgHom E) (Polynomial.C Polynomial.X) = MotC2.coordX E := by
    change AdjoinRoot.mk (WeierstrassCurve.Affine.polynomial E) (Polynomial.C Polynomial.X) = _
    rw [AdjoinRoot.mk_C]
    rfl
  have hcoordY : (mkAlgHom E) Polynomial.X = MotC2.coordY E := by
    change AdjoinRoot.mk (WeierstrassCurve.Affine.polynomial E) Polynomial.X = _
    rw [AdjoinRoot.mk_X]
    rfl
  have hvalX : Dcoord (MotC2.coordX E) = (mkAlgHom E) (WeierstrassCurve.Affine.polynomialY E) := by
    dsimp only [Dcoord]
    rw [← hcoordX, Derivation.liftOfSurjective_apply, hdX]
  have hvalY : Dcoord (MotC2.coordY E) = (mkAlgHom E) (-(WeierstrassCurve.Affine.polynomialX E)) := by
    dsimp only [Dcoord]
    rw [← hcoordY, Derivation.liftOfSurjective_apply, hdY]
  have : IsDomain (MotC2.Coord E) := inferInstance
  obtain ⟨D, hD⟩ := FracDeriv.exists_deriv_fractionRing Dcoord
  refine ⟨D, ?_, ?_⟩
  · have h1 : D (MotC2.genX E) =
        algebraMap (MotC2.Coord E) (MotC2.Func E) (Dcoord (MotC2.coordX E)) :=
      hD (MotC2.coordX E)
    rw [h1, hvalX, mkAlgHom_polynomialY]
    simp only [map_add, map_mul, map_ofNat,
      IsScalarTower.algebraMap_apply N (MotC2.Coord E) (MotC2.Func E)]
    rw [show (algebraMap (MotC2.Coord E) (MotC2.Func E)) (MotC2.coordX E) = MotC2.genX E from rfl]
    rw [show (algebraMap (MotC2.Coord E) (MotC2.Func E)) (MotC2.coordY E) = MotC2.genY E from rfl]
  · have h1 : D (MotC2.genY E) =
        algebraMap (MotC2.Coord E) (MotC2.Func E) (Dcoord (MotC2.coordY E)) :=
      hD (MotC2.coordY E)
    rw [h1, hvalY, mkAlgHom_polynomialX]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat,
      IsScalarTower.algebraMap_apply N (MotC2.Coord E) (MotC2.Func E)]
    rw [show (algebraMap (MotC2.Coord E) (MotC2.Func E)) (MotC2.coordX E) = MotC2.genX E from rfl]
    rw [show (algebraMap (MotC2.Coord E) (MotC2.Func E)) (MotC2.coordY E) = MotC2.genY E from rfl]

end Work.MotV
