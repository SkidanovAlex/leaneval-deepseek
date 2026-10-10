import Mathlib
import Submission.Work.MotK.TwCensus.ZTwist

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Normalised plane model of the residual curve (definitions)

`g0p r` is the normalised five-term `μ₅`-invariant quintic
`r^7X^5 − r^3(3+r^5)X²Y + (1+2r^5)XY³ − r²Y^5 + r²`; `Work.MotK.TwCensus.ZElim2 a b h` is
`a^8` times the diagonal substitution `(X0,X1) ↦ (w²X0, wX1)` of `g0p (b/a)` with `w^5 = h`.

`Q23`, `C23` are the shapes of the two factors in a `(2,3)` factorization of `g0p r` (normalised
so that `Q23` has `X`-degree `2` with leading coefficient `1`; the coefficients `c2,c1,c0` of
`C23` are the ones forced by the coefficient matching).
-/

set_option autoImplicit false

namespace Work.MotK.TGen

open MvPolynomial

variable {L : Type*} [Field L]

noncomputable def g0p (r : L) : MvPolynomial (Fin 2) L :=
  C (r ^ 7) * (X 0) ^ 5 - C (r ^ 3 * (3 + r ^ 5)) * (X 0) ^ 2 * X 1
    + C (1 + 2 * r ^ 5) * X 0 * (X 1) ^ 3 - C (r ^ 2) * (X 1) ^ 5 + C (r ^ 2)

noncomputable def q1p (u1 u0 : L) : MvPolynomial (Fin 2) L := C u1 * X 1 + C u0

noncomputable def q0p (v2 v1 v0 : L) : MvPolynomial (Fin 2) L :=
  C v2 * (X 1) ^ 2 + C v1 * X 1 + C v0

noncomputable def Q23 (u1 u0 v2 v1 v0 : L) : MvPolynomial (Fin 2) L :=
  (X 0) ^ 2 + q1p u1 u0 * X 0 + q0p v2 v1 v0

noncomputable def C23 (r u1 u0 v2 v1 v0 : L) : MvPolynomial (Fin 2) L :=
  C (r ^ 7) * (X 0) ^ 3 - C (r ^ 7) * q1p u1 u0 * (X 0) ^ 2
    + C (r ^ 7) * (q1p u1 u0 ^ 2 - q0p v2 v1 v0) * X 0
    - C (r ^ 3 * (3 + r ^ 5)) * X 1
    - C (r ^ 7) * q1p u1 u0 * (q1p u1 u0 ^ 2 - 2 * q0p v2 v1 v0)

end Work.MotK.TGen
