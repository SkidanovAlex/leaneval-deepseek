import Mathlib
import Submission.Work.MotAS.ASData

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.ASZChartData` — the chart data of the AS link

Self-contained copies of the chart data defined in
`Submission/Work/MotC5N3/ASZTwistDivPlaneGeomGen.lean`, so that the leaves of the K6 node can be
stated without depending on that (large) module.

* `aszD1`, `aszPb1`–`aszPb4`: the cleared denominators/numerators of the linear solution of
  `(phiAS a b) y = (1, X₀, X₁, X₂, 0)`;
* `aszAsY`: the ruling-line vector `(D1·S, t·Pb₁, …, t·Pb₄)`;
* `aszAco`, `aszBco`, `aszCco`: the coefficients of `S²`, `S·t`, `t²` in `kleinPAS k (3g) (aszAsY)`;
* `aszLco`: the consistency residual at `S = -C₁/B₁`, i.e.
  `aszLco k = aszAco k · C₁² - aszBco k · C₁ · B₁ + aszCco k · B₁²`.
-/

set_option autoImplicit false

namespace Work.MotC5N3

open MvPolynomial

variable {K : Type} [Field K]

/-- The cleared common denominator `D1 = (3a+b)(a+2b)(4a+3b)`. -/
noncomputable def aszD1 (a b : K) : K :=
  (3 * a + b) * (a + 2 * b) * (4 * a + 3 * b)

/-- Cleared numerator of the `X₀` chart coordinate. -/
noncomputable def aszPb1 (a b : K) : MvPolynomial (Fin 3) K :=
  C ((a + 2 * b) * (4 * a + 3 * b)) - C ((4 * a + 3 * b) * (3 * a + 4 * b)) * X 1

/-- Cleared numerator of the `X₁` chart coordinate. -/
noncomputable def aszPb2 (a b : K) : MvPolynomial (Fin 3) K :=
  C ((a + 2 * b) * (4 * a + 3 * b)) * X 0 - C ((a + 2 * b) * (a + 3 * b)) * X 2

/-- Cleared numerator of the `X₂` chart coordinate. -/
noncomputable def aszPb3 (a b : K) : MvPolynomial (Fin 3) K :=
  C ((3 * a + b) * (4 * a + 3 * b)) * X 1

/-- Cleared numerator of the fourth chart coordinate. -/
noncomputable def aszPb4 (a b : K) : MvPolynomial (Fin 3) K :=
  C ((3 * a + b) * (a + 2 * b)) * X 2

/-- The argument vector `y` of `kleinPAS` paired with the chart coordinates: `y 0 = D1·S`,
`y (j+1) = t·Pb(j+1)`; homogeneous of degree `2` in `(S,t)`. -/
noncomputable def aszAsY (a b : K) (S t : MvPolynomial (Fin 3) K) :
    Fin 5 → MvPolynomial (Fin 3) K :=
  ![C (aszD1 a b) * S, t * aszPb1 a b, t * aszPb2 a b, t * aszPb3 a b, t * aszPb4 a b]

/-- `A k`: the coefficient of `S²` in `kleinPAS k (3g) (aszAsY a b S t)`. -/
noncomputable def aszAco (a b g : K) (k : Fin 5) : MvPolynomial (Fin 3) K :=
  Work.MotAS.kleinPAS (C a) (C b) (C (3 * g)) (aszAsY a b 1 0) k

/-- `C k`: the coefficient of `t²` in `kleinPAS k (3g) (aszAsY a b S t)`. -/
noncomputable def aszCco (a b g : K) (k : Fin 5) : MvPolynomial (Fin 3) K :=
  Work.MotAS.kleinPAS (C a) (C b) (C (3 * g)) (aszAsY a b 0 1) k

/-- `B k`: the coefficient of `S·t` in `kleinPAS k (3g) (aszAsY a b S t)`. -/
noncomputable def aszBco (a b g : K) (k : Fin 5) : MvPolynomial (Fin 3) K :=
  Work.MotAS.kleinPAS (C a) (C b) (C (3 * g)) (aszAsY a b 1 1) k - aszAco a b g k
    - aszCco a b g k

/-- The consistency residual of the `k`-th transported Pfaffian at `S = -C₁/B₁`:
`aszLco k = kleinPAS k (3g) (aszAsY a b (-C₁) B₁)`. -/
noncomputable def aszLco (a b g : K) (k : Fin 5) : MvPolynomial (Fin 3) K :=
  aszAco a b g k * (aszCco a b g 1) ^ 2 - aszBco a b g k * aszCco a b g 1 * aszBco a b g 1
    + aszCco a b g k * (aszBco a b g 1) ^ 2

end Work.MotC5N3
