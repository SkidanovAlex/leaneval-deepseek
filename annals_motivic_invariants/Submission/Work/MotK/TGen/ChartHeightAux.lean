import Mathlib
import Submission.Work.MotK.TGen.ChartSetup

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Auxiliary elements for `Work.MotK.TGen.ChartHeightBound`

`Work.MotK.TGen.chartIdeal K D H = Qideal D.a D.b H ⊔ (X 0 - 1) ⊆ MvPolynomial (Fin 5) K` is the
ideal of the affine chart `{y₀ = 1}` of the twisted Klein quintic.  This file collects the explicit
elements of that ideal which are used to bound its height from below.

In the chart `y₀ = 1` the five twisted Pfaffians
`p₀ = -ab y₂² + a²y₀y₄ - b²y₁y₃`, `p₁ = -abh y₄² + a²y₁y₂ - b²y₀y₃`, … (`Work.MotK.kleinTwP`)
become, after substituting `y₁ = (abH y₃² + b²H y₂y₄)/a²` (which is `G1v/a²`), the elements

* `G1v  = a²y₁ - abH y₃² - b²H y₂y₄`                      (from `p₄`, linear in `y₁`),
* `Av   = -ab y₂² - (b⁴H/a²) y₂y₃y₄ + a²y₄ - (b³H/a) y₃³` (from `p₁`, quadratic in `y₂`),
* `Bv   = a²H y₂y₃ - ab - (b³H²/a) y₃²y₄ - (b⁴H²/a²) y₂y₄²` (from `p₀`, linear in `y₂`),

together with the resultant in the variable `y₂`

* `Resv = b₁²a₀ - a₁b₀b₁ + a₂b₀²`,

where `Av = a₂y₂² + a₁y₂ + a₀` and `Bv = b₁y₂ + b₀`; `Resv` depends only on `y₃, y₄` and is monic
of degree `5` in `y₃`, and the identity `Resv = b₁²·Av - a₂(b₁y₂ + a₁b₁/a₂ - b₀)·Bv` exhibits it as
an element of the ideal.

The "level `k`" versions (`G1v4`, `Av4`, `Av3`, `ResPoly3`, `ResPoly`) are the same polynomials
written in the variables of `MvPolynomial (Fin k) K`: they are the `MvPolynomial.finSuccEquiv`
images of the corresponding higher-level elements, which is what the height recursion of
`ChartHeightBound` uses them for.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type*} [Field K]

/-! ## The five-variable elements -/

/-- `a²y₁ - abH y₃² - b²H y₂y₄`, the chart form of the Pfaffian `p₄` (linear in `y₁`). -/
noncomputable def G1v (a b H : K) : MvPolynomial (Fin 5) K :=
  C (a ^(2:ℕ)) * X 1 - C (a * b * H) * (X 3) ^(2:ℕ) - C (b ^(2:ℕ) * H) * X 2 * X 4

/-- The chart form of `p₁` after substituting `y₁ = (abH y₃² + b²H y₂y₄)/a²`; quadratic in `y₂`. -/
noncomputable def Av (a b H : K) : MvPolynomial (Fin 5) K :=
  -C (a * b) * (X 2) ^(2:ℕ) - C (b ^(4:ℕ) * H / a ^(2:ℕ)) * X 2 * X 3 * X 4 + C (a ^(2:ℕ)) * X 4
    - C (b ^(3:ℕ) * H / a) * (X 3) ^(3:ℕ)

/-- The chart form of `p₀` after substituting `y₁ = (abH y₃² + b²H y₂y₄)/a²`; linear in `y₂`. -/
noncomputable def Bv (a b H : K) : MvPolynomial (Fin 5) K :=
  C (a ^(2:ℕ) * H) * X 2 * X 3 - C (a * b) - C (b ^(3:ℕ) * H ^(2:ℕ) / a) * (X 3) ^(2:ℕ) * X 4
    - C (b ^(4:ℕ) * H ^(2:ℕ) / a ^(2:ℕ)) * X 2 * (X 4) ^(2:ℕ)

/-- The resultant of `Av` and `Bv` in the variable `y₂`; it lies in `K[y₃,y₄]` and is monic of
degree `5` in `y₃`. -/
noncomputable def Resv (a b H : K) : MvPolynomial (Fin 5) K :=
  (C (a ^(2:ℕ) * H) * X 3 - C (b ^(4:ℕ) * H ^(2:ℕ) / a ^(2:ℕ)) * (X 4) ^(2:ℕ)) ^(2:ℕ)
      * (C (a ^(2:ℕ)) * X 4 - C (b ^(3:ℕ) * H / a) * (X 3) ^(3:ℕ))
    - (C (-(b ^(4:ℕ) * H / a ^(2:ℕ))) * X 3 * X 4)
        * (C (-(a * b)) - C (b ^(3:ℕ) * H ^(2:ℕ) / a) * (X 3) ^(2:ℕ) * X 4)
        * (C (a ^(2:ℕ) * H) * X 3 - C (b ^(4:ℕ) * H ^(2:ℕ) / a ^(2:ℕ)) * (X 4) ^(2:ℕ))
    + C (-(a * b)) * (C (-(a * b)) - C (b ^(3:ℕ) * H ^(2:ℕ) / a) * (X 3) ^(2:ℕ) * X 4) ^(2:ℕ)

/-! ## The lower-level versions -/

/-- The polynomial `abH y₂² + b²H y₁y₂` in three variables (the part of `G1v4` other than `a²y₁`). -/
noncomputable def g13 (a b H : K) : MvPolynomial (Fin 3) K :=
  C (a * b * H) * (X 1) ^(2:ℕ) + C (b ^(2:ℕ) * H) * X 0 * X 2

/-- `G1v` written in the variables of `MvPolynomial (Fin 4) K` (i.e. with `y i ↦ y (i+1)`): it is
`a²·y₁ - (abH y₃² + b²H y₂y₄)`. -/
noncomputable def G1v4 (a b H : K) : MvPolynomial (Fin 4) K :=
  C (a ^(2:ℕ)) * X 0 - C (a * b * H) * (X 2) ^(2:ℕ) - C (b ^(2:ℕ) * H) * X 1 * X 3

/-- `Av` written in the variables of `MvPolynomial (Fin 4) K`. -/
noncomputable def Av4 (a b H : K) : MvPolynomial (Fin 4) K :=
  -C (a * b) * (X 1) ^(2:ℕ) - C (b ^(4:ℕ) * H / a ^(2:ℕ)) * X 1 * X 2 * X 3 + C (a ^(2:ℕ)) * X 3
    - C (b ^(3:ℕ) * H / a) * (X 2) ^(3:ℕ)

/-- `Av` written in the variables of `MvPolynomial (Fin 3) K`. -/
noncomputable def Av3 (a b H : K) : MvPolynomial (Fin 3) K :=
  -C (a * b) * (X 0) ^(2:ℕ) - C (b ^(4:ℕ) * H / a ^(2:ℕ)) * X 0 * X 1 * X 2 + C (a ^(2:ℕ)) * X 2
    - C (b ^(3:ℕ) * H / a) * (X 1) ^(3:ℕ)

/-- `Resv` written in the variables of `MvPolynomial (Fin 2) K` (with `y₃ ↦ X 0`, `y₄ ↦ X 1`). -/
noncomputable def ResPoly (a b H : K) : MvPolynomial (Fin 2) K :=
  (C (a ^(2:ℕ) * H) * X 0 - C (b ^(4:ℕ) * H ^(2:ℕ) / a ^(2:ℕ)) * (X 1) ^(2:ℕ)) ^(2:ℕ)
      * (C (a ^(2:ℕ)) * X 1 - C (b ^(3:ℕ) * H / a) * (X 0) ^(3:ℕ))
    - (C (-(b ^(4:ℕ) * H / a ^(2:ℕ))) * X 0 * X 1)
        * (C (-(a * b)) - C (b ^(3:ℕ) * H ^(2:ℕ) / a) * (X 0) ^(2:ℕ) * X 1)
        * (C (a ^(2:ℕ) * H) * X 0 - C (b ^(4:ℕ) * H ^(2:ℕ) / a ^(2:ℕ)) * (X 1) ^(2:ℕ))
    + C (-(a * b)) * (C (-(a * b)) - C (b ^(3:ℕ) * H ^(2:ℕ) / a) * (X 0) ^(2:ℕ) * X 1) ^(2:ℕ)

/-- `Resv` written in the variables of `MvPolynomial (Fin 3) K`. -/
noncomputable def ResPoly3 (a b H : K) : MvPolynomial (Fin 3) K :=
  (C (a ^(2:ℕ) * H) * X 1 - C (b ^(4:ℕ) * H ^(2:ℕ) / a ^(2:ℕ)) * (X 2) ^(2:ℕ)) ^(2:ℕ)
      * (C (a ^(2:ℕ)) * X 2 - C (b ^(3:ℕ) * H / a) * (X 1) ^(3:ℕ))
    - (C (-(b ^(4:ℕ) * H / a ^(2:ℕ))) * X 1 * X 2)
        * (C (-(a * b)) - C (b ^(3:ℕ) * H ^(2:ℕ) / a) * (X 1) ^(2:ℕ) * X 2)
        * (C (a ^(2:ℕ) * H) * X 1 - C (b ^(4:ℕ) * H ^(2:ℕ) / a ^(2:ℕ)) * (X 2) ^(2:ℕ))
    + C (-(a * b)) * (C (-(a * b)) - C (b ^(3:ℕ) * H ^(2:ℕ) / a) * (X 1) ^(2:ℕ) * X 2) ^(2:ℕ)

/-- `Resv` written in the variables of `MvPolynomial (Fin 4) K`. -/
noncomputable def ResPoly4 (a b H : K) : MvPolynomial (Fin 4) K :=
  (C (a ^(2:ℕ) * H) * X 2 - C (b ^(4:ℕ) * H ^(2:ℕ) / a ^(2:ℕ)) * (X 3) ^(2:ℕ)) ^(2:ℕ)
      * (C (a ^(2:ℕ)) * X 3 - C (b ^(3:ℕ) * H / a) * (X 2) ^(3:ℕ))
    - (C (-(b ^(4:ℕ) * H / a ^(2:ℕ))) * X 2 * X 3)
        * (C (-(a * b)) - C (b ^(3:ℕ) * H ^(2:ℕ) / a) * (X 2) ^(2:ℕ) * X 3)
        * (C (a ^(2:ℕ) * H) * X 2 - C (b ^(4:ℕ) * H ^(2:ℕ) / a ^(2:ℕ)) * (X 3) ^(2:ℕ))
    + C (-(a * b)) * (C (-(a * b)) - C (b ^(3:ℕ) * H ^(2:ℕ) / a) * (X 2) ^(2:ℕ) * X 3) ^(2:ℕ)

end Work.MotK.TGen
