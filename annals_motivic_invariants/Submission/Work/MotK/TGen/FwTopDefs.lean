import Mathlib
import Submission.Work.MotK.TGen.CensusFactors
import Submission.Work.MotK.TGen.ChartDefs
import Submission.Work.MotA.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The top forms of `sT` and of `fwVec 4`

This file fixes the notation used to prove `Work.MotK.TGen.fwVec_four_notMem_of_sT`:
the "leading form" of a polynomial (`topForm`), the degree-2 and degree-1 parts `yQ`, `yL` of
the stereographic point `y = kleinTwStereo p chart3` at which the two divisor polynomials are
evaluated, and the explicit forms `S10` (the degree-10 part of `sT`) and `F4` (the degree-4 part
of `fwVec a b h 4`).

* `sT a b h = kleinTwS a b h y` with `y = yQ + yL`, so its degree-10 part is
  `kleinTwS a b h yQ = S10 a b h`;
* `fwVec a b h 4 = kleinTwP a b h y 4`, a quadratic form in `y`, whose degree-4 part is `F4 a b h`
  (which factors as `-a⁵h · X₂ · G₃`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.MotK.TGen

open MvPolynomial

noncomputable section

variable {K : Type*} [Field K]

/-- The **leading form** of `p`: its homogeneous component of maximal degree. -/
def topForm (p : MvPolynomial (Fin 3) K) : MvPolynomial (Fin 3) K :=
  MvPolynomial.homogeneousComponent p.totalDegree p

/-- The stereographic point `y = kleinTwStereo p chart3` at which the two divisor polynomials of
the `T`-twisted link are evaluated. -/
def ypt (a b h : K) : Fin 5 → MvPolynomial (Fin 3) K :=
  Work.MotK.kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
    (pRa a b h) (Work.MotK.chart3 K)

/-- The degree-`2` part of `ypt`. -/
def yQ (a b h : K) : Fin 5 → MvPolynomial (Fin 3) K :=
  ![MvPolynomial.C (a ^ 2 * h) * MvPolynomial.X 1 * MvPolynomial.X 2,
    -(MvPolynomial.C (a * b) * MvPolynomial.X 0 * MvPolynomial.X 1)
      - MvPolynomial.C (a ^ 2 * h) * MvPolynomial.X 0 * MvPolynomial.X 2,
    -(MvPolynomial.C (a * b)) * MvPolynomial.X 1 ^ 2,
    -(MvPolynomial.C (a ^ 2 * h)) * MvPolynomial.X 2 ^ 2,
    0]

/-- The degree-`1` part of `ypt`. -/
def yL (a b h : K) : Fin 5 → MvPolynomial (Fin 3) K :=
  ![-(MvPolynomial.C (b ^ 2 * h)) * MvPolynomial.X 0,
    0,
    -(MvPolynomial.C (b ^ 2 * h)) * MvPolynomial.X 0,
    -(MvPolynomial.C (b ^ 3 / a)) * MvPolynomial.X 0,
    -(MvPolynomial.C (a * b) * MvPolynomial.X 1 + MvPolynomial.C (a ^ 2 * h) * MvPolynomial.X 2)]

/-- `S10 a b h = kleinTwS a b h (yQ a b h)`: the degree-`10` part of `sT a b h`. -/
def S10 (a b h : K) : MvPolynomial (Fin 3) K :=
  Work.MotK.kleinTwS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) (yQ a b h)

/-- The cubic `G3 a b h = b·X₀X₁² + a h·X₀X₁X₂ + b h²·X₂³`. -/
def G3 (a b h : K) : MvPolynomial (Fin 3) K :=
  MvPolynomial.C b * MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2
    + MvPolynomial.C (a * h) * MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2
    + MvPolynomial.C (b * h ^ 2) * MvPolynomial.X 2 ^ 3

/-- `F4 a b h = -a⁵h·X₂·G3 a b h`: the degree-`4` part of `fwVec a b h 4`. -/
def F4 (a b h : K) : MvPolynomial (Fin 3) K :=
  MvPolynomial.C (-(a ^ 5 * h)) * MvPolynomial.X 2 * G3 a b h

end

end Work.MotK.TGen
