import Mathlib
import Submission.Work.MotK.TGen.ZElim2Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TGen.ZElim2AuxC

/-- `finSuccEquiv` sends the constants `C r` to the constants `C (C r)`. -/
theorem finSuccEquiv_C_eq {L : Type*} [CommSemiring L] (r : L) :
    MvPolynomial.finSuccEquiv L 1 (MvPolynomial.C r) = Polynomial.C (MvPolynomial.C r) := by
  rw [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C]
  rfl

/-- `finSuccEquiv` sends `X 1` to the constant polynomial `C (X 0)`. -/
theorem finSuccEquiv_X_one {L : Type*} [CommSemiring L] :
    MvPolynomial.finSuccEquiv L 1 (MvPolynomial.X (1 : Fin 2)) = Polynomial.C (MvPolynomial.X 0) :=
  MvPolynomial.finSuccEquiv_X_succ (R := L) (n := 1) (j := (0 : Fin 1))

theorem finSucc_g0p {L : Type*} [Field L] (r : L) :
    MvPolynomial.finSuccEquiv L 1 (Work.MotK.TGen.g0p r)
      = Polynomial.C (MvPolynomial.C (r ^ 7)) * Polynomial.X ^ 5
        + Polynomial.C (-(MvPolynomial.C (r ^ 3 * (3 + r ^ 5)) * MvPolynomial.X 0)) * Polynomial.X ^ 2
        + Polynomial.C (MvPolynomial.C (1 + 2 * r ^ 5) * (MvPolynomial.X 0) ^ 3) * Polynomial.X ^ 1
        + Polynomial.C (MvPolynomial.C (r ^ 2) - MvPolynomial.C (r ^ 2) * (MvPolynomial.X 0) ^ 5) := by
  rw [Work.MotK.TGen.g0p]
  simp only [map_add, map_sub, map_mul, map_pow, map_one,
    finSuccEquiv_C_eq, MvPolynomial.finSuccEquiv_X_zero, finSuccEquiv_X_one]
  simp only [Polynomial.C_neg, Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow]
  first | refl_ring1 | ring

end Work.MotK.TGen.ZElim2AuxC
