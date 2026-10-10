import Mathlib
import Submission.Work.MotC2.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

variable {L : Type*} [Field L]

/-- The `L[X]`-algebra structure on the affine coordinate ring `L[X,Y]/(W_E)` sends `X` to
`coordX E`, hence is evaluation of polynomials at `coordX E`. -/
lemma algebraMap_polynomial_eq_aeval_coordX (E : WeierstrassCurve L) (Q : Polynomial L) :
    algebraMap (Polynomial L) (Coord E) Q = Polynomial.aeval (coordX E) Q := by
  have h : (Polynomial.aeval (coordX E) : Polynomial L →ₐ[L] Coord E) =
      IsScalarTower.toAlgHom L (Polynomial L) (Coord E) := by
    apply Polynomial.algHom_ext
    rw [IsScalarTower.toAlgHom_apply, Polynomial.aeval_X]
    simp [coordX, AdjoinRoot.algebraMap_eq]
  exact (DFunLike.congr_fun h Q).symm

/-- The `L[X]`-algebra structure on the function field `L(E)` sends `X` to `genX E`, hence is
evaluation of polynomials at `genX E`. -/
lemma algebraMap_polynomial_eq_aeval_genX (E : WeierstrassCurve L) (Q : Polynomial L) :
    algebraMap (Polynomial L) (Func E) Q = Polynomial.aeval (genX E) Q := by
  have h : (Polynomial.aeval (genX E) : Polynomial L →ₐ[L] Func E) =
      IsScalarTower.toAlgHom L (Polynomial L) (Func E) := by
    apply Polynomial.algHom_ext
    rw [IsScalarTower.toAlgHom_apply, Polynomial.aeval_X,
      IsScalarTower.algebraMap_apply (Polynomial L) (Coord E) (Func E) Polynomial.X]
    simp [genX, coordX, AdjoinRoot.algebraMap_eq]
  exact (DFunLike.congr_fun h Q).symm

/-- The class of `Y` in the coordinate ring, seen in the function field, is `genY E`. -/
lemma algebraMap_mk_X_eq_genY (E : WeierstrassCurve L) :
    algebraMap (Coord E) (Func E)
      (WeierstrassCurve.Affine.CoordinateRing.mk E (Polynomial.X : Polynomial (Polynomial L))) =
      genY E := by
  rw [show (WeierstrassCurve.Affine.CoordinateRing.mk E
      (Polynomial.X : Polynomial (Polynomial L)) : Coord E) = coordY E from
    (coordY_eq_mk E).symm]
  rfl

theorem algebraMap_smul_eq_aeval (L : Type*) [Field L] (E : WeierstrassCurve L)
    (P : Polynomial L) :
    algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) (P • (1 : Work.MotC2.Coord E)) =
        Polynomial.aeval (Work.MotC2.genX E) P ∧
      algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E)
          (P • (WeierstrassCurve.Affine.CoordinateRing.mk E Polynomial.X)) =
        Polynomial.aeval (Work.MotC2.genX E) P * Work.MotC2.genY E := by
  constructor
  · rw [Algebra.smul_def, mul_one,
      ← IsScalarTower.algebraMap_apply (Polynomial L) (Coord E) (Func E) P,
      algebraMap_polynomial_eq_aeval_genX E P]
  · rw [Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply (Polynomial L) (Coord E) (Func E) P,
      algebraMap_polynomial_eq_aeval_genX E P, algebraMap_mk_X_eq_genY E]

end Work.MotC2
