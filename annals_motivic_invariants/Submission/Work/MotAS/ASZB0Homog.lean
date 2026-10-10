import Mathlib
import Submission.Work.MotAS.ASZElimData

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS

/-- The eliminant `P` is weighted homogeneous of degree `5` in `(a,b)`: specialising `b = 0` and
rescaling `a ↦ 1` multiplies `P` by `C (a ^ 5)`.  (Equivalently, with `b = 0` every one of the
sixteen coefficients of `P a 0 g` is `a ^ 5` times the corresponding coefficient of `P 1 0 g`.)
The proof is a coefficientwise computation: push `C` through the ring operations of
`MvPolynomial (Fin 2) K` and normalise the resulting polynomial identity. -/
theorem ASZB0Homog (K : Type) [Field K] (a g : K) :
    Work.MotAS.ASZElim.P a 0 g = MvPolynomial.C (a ^ 5) * Work.MotAS.ASZElim.P 1 0 g := by
  unfold Work.MotAS.ASZElim.P
  simp only [MvPolynomial.C_add, MvPolynomial.C_mul, MvPolynomial.C_pow, MvPolynomial.C_neg,
    MvPolynomial.C_0, MvPolynomial.C_1, map_ofNat]
  ring_nf

end Work.MotAS
