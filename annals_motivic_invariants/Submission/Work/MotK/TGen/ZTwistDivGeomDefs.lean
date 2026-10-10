import Mathlib
import Submission.Work.MotK.TwCensus.ZTwist
import Submission.Work.MotK.KleinTwData

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.ZTwistDivGeomDefs`

Vocabulary and the explicit polynomial certificates for the geometric leaf
`Work.MotK.TGen.ZTwistDivPlaneGeom` (node K6 of the T-twisted Crauder--Katz link).

* `zpgE a b h` is the **eliminant** of the chart `y₀ = 1` of the twisted Klein curve
  `C_{h²} = V(kleinTwP a b h²)` in the coordinates `(y₁,y₃)`; it is the plane model of the
  residual curve, obtained from `ZElim2 a b h` by the invertible *diagonal* substitution
  `X₀ ↦ (a/b)y₁`, `X₁ ↦ -(a/b)h y₃` (up to the unit `a³/b⁴`).
* `zpgQ a b h k` are the five chart quadrics (the twisted Pfaffians `kleinTwP a b h²` with
  `y₀ = 1`), in the four variables `y₁,y₂,y₃,y₄`; `zpgI4` is the ideal they generate and
  `zpgG3 = h²·W·y₄ - c` is the linear-in-`y₄` chart relation.
The certificates about these objects live in `Work.MotK.TGen.ZTwistDivGeomAux`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type} [Field K]

/-! ## 1. The eliminant and the chart quadrics -/

/-- The eliminant `zpgE a b h` of the chart `y₀ = 1` of `C_{h²}` in the coordinates `(y₁,y₃)`. -/
noncomputable def zpgE (a b h : K) : MvPolynomial (Fin 2) K :=
  C (-(a^9*h^4)) * X 0 * (X 1)^3 + C (a^8*b*h^6) * (X 1)^5
    + C (3*a^5*b^4*h^2) * (X 0)^2 * X 1 + C (-(2*a^4*b^5*h^4)) * X 0 * (X 1)^3
    + C (a^3*b^6*h^2) * (X 0)^5 + C (a^3*b^6) + C (b^9*h^2) * (X 0)^2 * X 1

/-- `W = b⁴y₁ - a⁴h²y₃²`, the denominator of the inverse chart map. -/
noncomputable def zpgW (a b h : K) : MvPolynomial (Fin 2) K :=
  C (b^4) * X 0 - C (a^4*h^2) * (X 1)^2

/-- `c = -ab(b² + a²h²y₁²y₃)`, the numerator of the inverse chart map. -/
noncomputable def zpgC (a b h : K) : MvPolynomial (Fin 2) K :=
  C (-(a*b^3)) - C (a^3*b*h^2) * (X 0)^2 * X 1

/-- The eliminant, read in the four chart coordinates `y₁,y₂,y₃,y₄`. -/
noncomputable def zpgE4 (a b h : K) : MvPolynomial (Fin 4) K :=
  C (-(a^9*h^4)) * X 0 * (X 2)^3 + C (a^8*b*h^6) * (X 2)^5
    + C (3*a^5*b^4*h^2) * (X 0)^2 * X 2 + C (-(2*a^4*b^5*h^4)) * X 0 * (X 2)^3
    + C (a^3*b^6*h^2) * (X 0)^5 + C (a^3*b^6) + C (b^9*h^2) * (X 0)^2 * X 2

/-- `W`, read in the four chart coordinates. -/
noncomputable def zpgW4 (a b h : K) : MvPolynomial (Fin 4) K :=
  C (b^4) * X 0 - C (a^4*h^2) * (X 2)^2

/-- `c`, read in the four chart coordinates. -/
noncomputable def zpgC4 (a b h : K) : MvPolynomial (Fin 4) K :=
  C (-(a*b^3)) - C (a^3*b*h^2) * (X 0)^2 * X 2

/-- The five chart quadrics: the twisted Pfaffians `kleinTwP a b h²` at `y₀ = 1`, in the
coordinates `y₁,y₂,y₃,y₄`. -/
noncomputable def zpgQ (a b h : K) : Fin 5 → MvPolynomial (Fin 4) K :=
  ![-C (a*b) + C (a^2*h^2) * X 1 * X 2 - C (b^2*h^2) * X 0 * X 3,
    -(C (a*b)) * (X 1)^2 + C (a^2) * X 3 - C (b^2) * X 0 * X 2,
    -(C (a*b*h^2)) * (X 3)^2 + C (a^2) * X 0 * X 1 - C (b^2) * X 2,
    -(C (a*b)) * (X 0)^2 + C (a^2*h^2) * X 2 * X 3 - C (b^2) * X 1,
    -(C (a*b*h^2)) * (X 2)^2 + C (a^2) * X 0 - C (b^2*h^2) * X 1 * X 3]

/-- The ideal of the affine chart `y₀ = 1` of the twisted Klein curve. -/
noncomputable def zpgI4 (a b h : K) : Ideal (MvPolynomial (Fin 4) K) :=
  Ideal.span (Set.range (zpgQ a b h))

/-- The chart relation `h²·W·y₄ - c`, linear in `y₄`. -/
noncomputable def zpgG3 (a b h : K) : MvPolynomial (Fin 4) K :=
  C (h^2) * zpgW4 a b h * X 3 - zpgC4 a b h


end Work.MotK.TGen
