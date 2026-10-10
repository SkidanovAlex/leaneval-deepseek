import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotC5N3.AK
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.ASZTwistDefs
import Submission.Work.MotAS.PhiSDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.ASZParam` — the explicit parametrisation data of the AS residual

The shared definitions behind the explicit chart parametrisation of the AS residual
(`V(ZIAS a b g)`) by the AS-twisted Klein curve `C_{3g} = V(kleinPAS a b (3g))` under the linear
projection `phiAS a b`.  They live here (rather than in `ASZTwistDivPlaneGeomGen`) so that the
certificate lemmas about them can be stated and proved *below* the target file and imported by it.

* `D1 a b = (3a+b)(a+2b)(4a+3b)` and `Pb1..Pb4`: the cleared chart-coordinate numerators, i.e.
  the linear system `phiAS · Y = t·(1, X₀, X₁, X₂, 0)` solved for `Y₁..Y₄` as `t·(Pb_j/D1)`.
* `asY a b S t`: the vector `(D1·S, t·Pb₁, …, t·Pb₄)`, homogeneous of degree `2` in `(S,t)`.
* `Aco`, `Bco`, `Cco`: the coefficients of `S²`, `S·t`, `t²` in `kleinPAS k (3g) (asY a b S t)`.
* `Lco`: the consistency residual `A k·C₁² - B k·C₁·B₁ + C k·B₁²` at `S = -C₁/B₁`.
* `Zk`: the linear forms `Z k = Σ_j phiAS a b k j · Y_j` on the chart of `C_{3g}`.
* `ZX`: their pullback `Z^(X)_k = Σ_{j≥1} phiAS a b k j · Pb_j` along `X_i ↦ Z_{i+1}/Z₀`; the
  identities `Z^(X)_0 = D1`, `Z^(X)_{i+1} = D1·X_i` give `Xᵢ = Θ(Z_{i+1})/Θ(Z₀)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotC5N3

open MvPolynomial

variable {K : Type} [Field K] [CharP K 5]

/-- The cleared common denominator `D1 = (3a+b)(a+2b)(4a+3b)` of the chart coordinates. -/
def D1 (a b : K) : K := (3 * a + b) * (a + 2 * b) * (4 * a + 3 * b)

/-- Cleared numerator of the `X₀` chart coordinate: `Pb₁ = D1·(1 - (3a+4b)X₁/(a+2b))/(3a+b)`. -/
noncomputable def Pb1 (a b : K) : MvPolynomial (Fin 3) K :=
  C ((a + 2 * b) * (4 * a + 3 * b)) - C ((4 * a + 3 * b) * (3 * a + 4 * b)) * X 1

/-- Cleared numerator of the `X₁` chart coordinate: `Pb₂ = D1·(X₀ - (a+3b)X₂/(4a+3b))/(3a+b)`. -/
noncomputable def Pb2 (a b : K) : MvPolynomial (Fin 3) K :=
  C ((a + 2 * b) * (4 * a + 3 * b)) * X 0 - C ((a + 2 * b) * (a + 3 * b)) * X 2

/-- Cleared numerator of the `X₂` chart coordinate: `Pb₃ = D1·X₁/(a+2b)`. -/
noncomputable def Pb3 (a b : K) : MvPolynomial (Fin 3) K :=
  C ((3 * a + b) * (4 * a + 3 * b)) * X 1

/-- Cleared numerator of the fourth chart coordinate: `Pb₄ = D1·X₂/(4a+3b)`. -/
noncomputable def Pb4 (a b : K) : MvPolynomial (Fin 3) K :=
  C ((3 * a + b) * (a + 2 * b)) * X 2

/-- The argument vector `y` of `kleinPAS` paired with the chart coordinates: `y 0 = D1·S`,
`y (j+1) = t·Pb(j+1)`; homogeneous of degree `2` in `(S,t)`. -/
noncomputable def asY (a b : K) (S t : MvPolynomial (Fin 3) K) : Fin 5 → MvPolynomial (Fin 3) K :=
  ![C (D1 a b) * S, t * Pb1 a b, t * Pb2 a b, t * Pb3 a b, t * Pb4 a b]

/-- `A k`: the coefficient of `S²` in `kleinPAS k (3g) (asY a b S t)`. -/
noncomputable def Aco (a b g : K) (k : Fin 5) : MvPolynomial (Fin 3) K :=
  Work.MotAS.kleinPAS (C a) (C b) (C (3 * g)) (asY a b 1 0) k

/-- `C k`: the coefficient of `t²` in `kleinPAS k (3g) (asY a b S t)`. -/
noncomputable def Cco (a b g : K) (k : Fin 5) : MvPolynomial (Fin 3) K :=
  Work.MotAS.kleinPAS (C a) (C b) (C (3 * g)) (asY a b 0 1) k

/-- `B k`: the coefficient of `S·t` in `kleinPAS k (3g) (asY a b S t)`. -/
noncomputable def Bco (a b g : K) (k : Fin 5) : MvPolynomial (Fin 3) K :=
  Work.MotAS.kleinPAS (C a) (C b) (C (3 * g)) (asY a b 1 1) k - Aco a b g k - Cco a b g k

/-- The consistency residual of the `k`-th transported Pfaffian at `S = -C₁/B₁`. -/
noncomputable def Lco (a b g : K) (k : Fin 5) : MvPolynomial (Fin 3) K :=
  Aco a b g k * (Cco a b g 1) ^ 2 - Bco a b g k * Cco a b g 1 * Bco a b g 1
    + Cco a b g k * (Bco a b g 1) ^ 2

/-- The linear form `Z k = Σ_j phiAS a b k j · Y_j` on the chart of `C_{3g}`, as a polynomial in
the chart variables `Y_j` of `MvPolynomial (Fin 5) K`.  Component values: `Z 0 = (3a+b)Y₁+(3a+4b)Y₃`,
`Z 1 = (3a+b)Y₂+(a+3b)Y₄`, `Z 2 = (a+2b)Y₃`, `Z 3 = (4a+3b)Y₄`, `Z 4 = 0`. -/
noncomputable def Zk (a b : K) : Fin 5 → MvPolynomial (Fin 5) K :=
  fun k => ∑ j : Fin 5, C (Work.MotAS.phiAS a b k j) * X j

/-- `Z^(X)_k = Σ_{j=1..4} phiAS a b k j · Pb_j`: the pullback of `Z_k` along `X_i ↦ Z_{i+1}/Z₀`.
The identities behind `Xᵢ = Θ(Z_{i+1})/Θ(Z₀)` are `Z^(X)_0 = D1` and `Z^(X)_{i+1} = D1·X_i`. -/
noncomputable def ZX (a b : K) (k : Fin 5) : MvPolynomial (Fin 3) K :=
  C (Work.MotAS.phiAS a b k 1) * Pb1 a b + C (Work.MotAS.phiAS a b k 2) * Pb2 a b
    + C (Work.MotAS.phiAS a b k 3) * Pb3 a b + C (Work.MotAS.phiAS a b k 4) * Pb4 a b

end Work.MotC5N3
