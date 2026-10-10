import Mathlib
import Submission.Work.MotC2Cls.Setup
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

namespace Work.MotC2Cls

/-- The kernel of the evaluation `L`-algebra homomorphism `Coord E →ₐ[L] L` at a rational point
`(a, b)` of `E` is the ideal `⟨X - a, Y - b⟩` of the affine coordinate ring.  The point lies on the
curve because `φ` is an algebra homomorphism and the Weierstrass relation holds in `Coord E`, so the
ideal is the kernel of the quotient map onto the residue field `L` at `(a, b)`; it is maximal by
`CoordinateRing.quotientXYIdealEquiv`. -/
theorem ker_eq_XYIdeal {L : Type*} [Field L] (E : WeierstrassCurve L)
    (φ : Work.MotC2.Coord E →ₐ[L] L) :
    RingHom.ker (φ : Work.MotC2.Coord E →+* L) =
      WeierstrassCurve.Affine.CoordinateRing.XYIdeal E (φ (Work.MotC2.coordX E))
        (Polynomial.C (φ (Work.MotC2.coordY E))) := by
  -- The image `(a, b)` of `(x, y)` satisfies the Weierstrass equation.
  have hEq : Polynomial.evalEval (φ (Work.MotC2.coordX E)) (φ (Work.MotC2.coordY E))
      (WeierstrassCurve.Affine.polynomial E) = 0 := by
    have hrel : φ (Work.MotC2.coordY E) ^ 2 +
        (E.a₁ * φ (Work.MotC2.coordX E) + E.a₃) * φ (Work.MotC2.coordY E)
        = φ (Work.MotC2.coordX E) ^ 3 + E.a₂ * φ (Work.MotC2.coordX E) ^ 2
          + E.a₄ * φ (Work.MotC2.coordX E) + E.a₆ := by
      have h := congrArg (φ : Work.MotC2.Coord E → L) (Work.MotC2.coordY_sq_relation E)
      simp only [map_add, map_mul, map_pow] at h
      simp only [AlgHom.commutes] at h
      simpa using h
    rw [WeierstrassCurve.Affine.evalEval_polynomial]
    linear_combination (norm := first | refl_ring1 | ring1) hrel
  -- Hence `⟨X - a, Y - b⟩` is a maximal ideal.
  have hmax : (WeierstrassCurve.Affine.CoordinateRing.XYIdeal E (φ (Work.MotC2.coordX E))
      (Polynomial.C (φ (Work.MotC2.coordY E)))).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (MulEquiv.isField (Field.toIsField L)
      (WeierstrassCurve.Affine.CoordinateRing.quotientXYIdealEquiv (W' := E) hEq).toMulEquiv)
  -- `⟨X - a, Y - b⟩` is contained in the kernel, so the maximality finishes the proof.
  refine (hmax.eq_of_le (RingHom.ker_ne_top (φ : Work.MotC2.Coord E →+* L)) ?_).symm
  rw [WeierstrassCurve.Affine.CoordinateRing.XYIdeal, Ideal.span_le]
  rintro _ (rfl | rfl)
  · change φ (CoordinateRing.XClass E (φ (Work.MotC2.coordX E))) = 0
    rw [Work.MotC2.XClass_eq_coordX_sub]
    simp
  · change φ (CoordinateRing.YClass E (Polynomial.C (φ (Work.MotC2.coordY E)))) = 0
    rw [Work.MotC2.YClass_eq_coordY_sub]
    simp

end Work.MotC2Cls
