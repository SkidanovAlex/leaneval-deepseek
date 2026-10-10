import Mathlib
import Submission.Work.MotAS.ASZElimData
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS

/-- `P` is homogeneous of degree `5` in the pair `(a, b)`: scaling `a` and `b` by `c`
scales `P` by `c ^ 5`.  Each of the fifteen coefficients of `P` is a homogeneous polynomial of
degree `5` in `(a, b)`, so the identity follows by pushing `MvPolynomial.C` through the ring
operations and normalising. -/
theorem P_homog (K : Type) [Field K] (c a b g : K) :
    Work.MotAS.ASZElim.P (c * a) (c * b) g = MvPolynomial.C (c ^ 5) * Work.MotAS.ASZElim.P a b g := by
  simp only [Work.MotAS.ASZElim.P, MvPolynomial.C_mul, MvPolynomial.C_add, MvPolynomial.C_pow,
    MvPolynomial.C_neg]
  first | refl_ring1 | ring

end Work.MotAS
