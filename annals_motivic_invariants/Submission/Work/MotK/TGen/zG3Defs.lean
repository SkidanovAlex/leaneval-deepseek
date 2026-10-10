import Mathlib
import Submission.Work.MotK.TGen.ZPlaneDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The third Gröbner generator `G₃ = e·x₀ + R` of `ZI`

`e = a⁹h·x₂⁵ − a⁴b⁵` and `R` are the coefficients of the third Gröbner generator `zG3` of the
chart ideal `ZI` in lex order `x₀ > x₁ > x₂` (see `GUIDE_ker_zPsi.md`).  These three
*definitions* are separated from their uses so that the consumers on the K5 critical path
(`Work.MotK.TGen.RadSatDefs` and its descendants) do not have to import the whole
`Work.MotK.TGen.ker_zPsi_le_radical_aux` module.
-/

set_option maxHeartbeats 4000000

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type} [Field K]

/-- `e = a⁹h·x₂⁵ − a⁴b⁵`, the coefficient of `x₀` in the third Gröbner generator `zG3`. -/
noncomputable def zE (a b h : K) : MvPolynomial (Fin 3) K :=
  C (a^9*h) * (X 2)^5 - C (a^4*b^5)

/-- `R`, the `x₀`-free part of the third Gröbner generator `zG3`. -/
noncomputable def zR3 (a b h : K) : MvPolynomial (Fin 3) K :=
  C (a^8*b) * (X 2)^3 - C (a^7*b^2*h) * (X 1)^2 * (X 2)^4
    + C (2*a^5*b^4) * X 1 * X 2 - C (a^4*b^5*h) * (X 1)^3 * (X 2)^2
    - C (a^3*b^6) * (X 2)^3 - C (a*b^8*h) * (X 1)^4 + C (b^9) * X 1 * X 2

/-- The third Gröbner generator `G₃ = e·x₀ + R` of `ZI`. -/
noncomputable def zG3 (a b h : K) : MvPolynomial (Fin 3) K := zE a b h * X 0 + zR3 a b h

end Work.MotK.TGen
