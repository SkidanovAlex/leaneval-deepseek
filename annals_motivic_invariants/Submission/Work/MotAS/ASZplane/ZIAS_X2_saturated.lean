import Mathlib
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.AK
import Submission.Work.MotAS.notMem_minimalPrimes_of_quotient_finite
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Work.MotAS.ASZplane

open MvPolynomial

section Certificates

variable {R : Type*} [CommRing R]

/-- The `X 2`-free part of `kleinRAS 0` at the chart `(1,X0,X1,X2,0)`. -/
noncomputable def zQ0 (a b g : R) : MvPolynomial (Fin 3) R :=
  2 * C a ^(4:ℕ) * C g * X 0 * X 1 ^(2:ℕ) - C a ^(4:ℕ) * X 0 ^(2:ℕ) - C a ^(4:ℕ) * X 1 ^(2:ℕ) + 2 * C a ^(4:ℕ) * X 1 - C a ^(4:ℕ) + C a ^(3:ℕ) * C b * C g * X 0 * X 1 ^(2:ℕ) + C a ^(3:ℕ) * C b * X 0 ^(2:ℕ) + 2 * C a ^(3:ℕ) * C b * X 1 ^(3:ℕ) + -2 * C a ^(3:ℕ) * C b * X 1 ^(2:ℕ) + -2 * C a ^(3:ℕ) * C b * X 1 + 2 * C a ^(3:ℕ) * C b + -2 * C a ^(2:ℕ) * C b ^(2:ℕ) * C g * X 0 * X 1 ^(2:ℕ) + C a ^(2:ℕ) * C b ^(2:ℕ) - C a * C b ^(3:ℕ) * C g * X 0 * X 1 ^(2:ℕ) + C a * C b ^(3:ℕ) * X 0 ^(2:ℕ) + 2 * C a * C b ^(3:ℕ) * X 1 ^(3:ℕ) + 2 * C a * C b ^(3:ℕ) * X 1 ^(2:ℕ) + -2 * C a * C b ^(3:ℕ) * X 1 + -2 * C a * C b ^(3:ℕ) + 2 * C b ^(4:ℕ) * C g * X 0 * X 1 ^(2:ℕ) + C b ^(4:ℕ) * X 0 ^(2:ℕ) - C b ^(4:ℕ) * X 1 ^(2:ℕ) + -2 * C b ^(4:ℕ) * X 1 - C b ^(4:ℕ)

/-- The `X 2`-free part of `kleinRAS 1` at the chart `(1,X0,X1,X2,0)`. -/
noncomputable def zQ1 (a b g : R) : MvPolynomial (Fin 3) R :=
  -1 * C a ^(4:ℕ) * C g * X 1 ^(3:ℕ) - C a ^(4:ℕ) * X 0 ^(3:ℕ) + C a ^(4:ℕ) * X 0 * X 1 ^(2:ℕ) + 2 * C a ^(4:ℕ) * X 0 + 2 * C a ^(3:ℕ) * C b * C g * X 1 ^(3:ℕ) + C a ^(3:ℕ) * C b * X 0 ^(3:ℕ) - C a ^(3:ℕ) * C b * X 0 * X 1 ^(2:ℕ) + C a ^(3:ℕ) * C b * X 0 + C a ^(2:ℕ) * C b ^(2:ℕ) * C g * X 1 ^(3:ℕ) + -2 * C a ^(2:ℕ) * C b ^(2:ℕ) * X 0 * X 1 ^(2:ℕ) + -2 * C a ^(2:ℕ) * C b ^(2:ℕ) * X 0 + -2 * C a * C b ^(3:ℕ) * C g * X 1 ^(3:ℕ) + C a * C b ^(3:ℕ) * X 0 ^(3:ℕ) + C a * C b ^(3:ℕ) * X 0 * X 1 ^(2:ℕ) - C a * C b ^(3:ℕ) * X 0 - C b ^(4:ℕ) * C g * X 1 ^(3:ℕ) + C b ^(4:ℕ) * X 0 ^(3:ℕ) + C b ^(4:ℕ) * X 0 * X 1 ^(2:ℕ) + 2 * C b ^(4:ℕ) * X 0

/-- The `X 2`-free part of `kleinRAS 2` at the chart `(1,X0,X1,X2,0)`. -/
noncomputable def zQ2 (a b g : R) : MvPolynomial (Fin 3) R :=
  2 * C a ^(4:ℕ) * X 0 ^(2:ℕ) * X 1 + 2 * C a ^(4:ℕ) * X 0 ^(2:ℕ) + -2 * C a ^(4:ℕ) * X 1 ^(3:ℕ) + 2 * C a ^(4:ℕ) * X 1 + -2 * C a ^(3:ℕ) * C b * X 0 ^(2:ℕ) * X 1 + C a ^(3:ℕ) * C b * X 0 ^(2:ℕ) + C a ^(3:ℕ) * C b * X 1 + -2 * C a ^(2:ℕ) * C b ^(2:ℕ) * X 0 ^(2:ℕ) + C a ^(2:ℕ) * C b ^(2:ℕ) * X 1 ^(3:ℕ) + -2 * C a ^(2:ℕ) * C b ^(2:ℕ) * X 1 + -2 * C a * C b ^(3:ℕ) * X 0 ^(2:ℕ) * X 1 - C a * C b ^(3:ℕ) * X 0 ^(2:ℕ) - C a * C b ^(3:ℕ) * X 1 + -2 * C b ^(4:ℕ) * X 0 ^(2:ℕ) * X 1 + 2 * C b ^(4:ℕ) * X 0 ^(2:ℕ) + -2 * C b ^(4:ℕ) * X 1 ^(3:ℕ) + 2 * C b ^(4:ℕ) * X 1

/-- The `X 2`-free part of `kleinRAS 3` at the chart `(1,X0,X1,X2,0)`. -/
noncomputable def zQ3 (a b g : R) : MvPolynomial (Fin 3) R :=
  -1 * C a ^(4:ℕ) * X 0 ^(3:ℕ) + C a ^(4:ℕ) * X 0 * X 1 ^(2:ℕ) - C a ^(4:ℕ) * X 0 * X 1 + 2 * C a ^(3:ℕ) * C b * X 0 ^(3:ℕ) - C a ^(3:ℕ) * C b * X 0 * X 1 ^(2:ℕ) + 2 * C a ^(3:ℕ) * C b * X 0 * X 1 + C a ^(2:ℕ) * C b ^(2:ℕ) * X 0 ^(3:ℕ) + C a ^(2:ℕ) * C b ^(2:ℕ) * X 0 * X 1 + -2 * C a * C b ^(3:ℕ) * X 0 ^(3:ℕ) - C a * C b ^(3:ℕ) * X 0 * X 1 ^(2:ℕ) + -2 * C a * C b ^(3:ℕ) * X 0 * X 1 - C b ^(4:ℕ) * X 0 ^(3:ℕ) - C b ^(4:ℕ) * X 0 * X 1 ^(2:ℕ) - C b ^(4:ℕ) * X 0 * X 1

/-- The `X 2`-free part of `kleinRAS 4` at the chart `(1,X0,X1,X2,0)`. -/
noncomputable def zQ4 (a b g : R) : MvPolynomial (Fin 3) R :=
  2 * C a ^(4:ℕ) * X 0 ^(2:ℕ) * X 1 + -2 * C a ^(4:ℕ) * X 1 ^(3:ℕ) + 2 * C a ^(4:ℕ) * X 1 ^(2:ℕ) + C a ^(3:ℕ) * C b * X 0 ^(2:ℕ) * X 1 + 2 * C a ^(3:ℕ) * C b * X 1 ^(3:ℕ) + C a ^(3:ℕ) * C b * X 1 ^(2:ℕ) + -2 * C a ^(2:ℕ) * C b ^(2:ℕ) * X 0 ^(2:ℕ) * X 1 + -2 * C a ^(2:ℕ) * C b ^(2:ℕ) * X 1 ^(2:ℕ) - C a * C b ^(3:ℕ) * X 0 ^(2:ℕ) * X 1 + 2 * C a * C b ^(3:ℕ) * X 1 ^(3:ℕ) - C a * C b ^(3:ℕ) * X 1 ^(2:ℕ) + 2 * C b ^(4:ℕ) * X 0 ^(2:ℕ) * X 1 + 2 * C b ^(4:ℕ) * X 1 ^(3:ℕ) + 2 * C b ^(4:ℕ) * X 1 ^(2:ℕ)

/-- The coefficient of `X 2` in `kleinRAS 0` at the chart `(1,X0,X1,X2,0)`. -/
noncomputable def zH0 (a b g : R) : MvPolynomial (Fin 3) R :=
  2 * C a ^(4:ℕ) * C g * X 0 ^(2:ℕ) + 2 * C a ^(4:ℕ) * C g * X 0 * X 2 - C a ^(4:ℕ) * C g * X 1 ^(2:ℕ) - C a ^(4:ℕ) * C g * X 1 + C a ^(4:ℕ) * C g * X 2 ^(2:ℕ) + 2 * C a ^(4:ℕ) * X 0 - C a ^(4:ℕ) * X 2 + C a ^(3:ℕ) * C b * C g * X 0 ^(2:ℕ) + -2 * C a ^(3:ℕ) * C b * C g * X 0 * X 2 + C a ^(3:ℕ) * C b * C g * X 1 ^(2:ℕ) + 2 * C a ^(3:ℕ) * C b * C g * X 1 + C a ^(3:ℕ) * C b * C g * X 2 ^(2:ℕ) - C a ^(3:ℕ) * C b * X 0 * X 1 - C a ^(3:ℕ) * C b * X 0 + C a ^(3:ℕ) * C b * X 1 * X 2 + -2 * C a ^(2:ℕ) * C b ^(2:ℕ) * C g * X 0 ^(2:ℕ) + C a ^(2:ℕ) * C b ^(2:ℕ) * C g * X 1 + C a ^(2:ℕ) * C b ^(2:ℕ) * C g * X 2 ^(2:ℕ) - C a * C b ^(3:ℕ) * C g * X 0 ^(2:ℕ) + -2 * C a * C b ^(3:ℕ) * C g * X 0 * X 2 + C a * C b ^(3:ℕ) * C g * X 1 ^(2:ℕ) + -2 * C a * C b ^(3:ℕ) * C g * X 1 - C a * C b ^(3:ℕ) * C g * X 2 ^(2:ℕ) - C a * C b ^(3:ℕ) * X 0 * X 1 + C a * C b ^(3:ℕ) * X 0 - C a * C b ^(3:ℕ) * X 1 * X 2 + 2 * C b ^(4:ℕ) * C g * X 0 ^(2:ℕ) + -2 * C b ^(4:ℕ) * C g * X 0 * X 2 + C b ^(4:ℕ) * C g * X 1 ^(2:ℕ) - C b ^(4:ℕ) * C g * X 1 + C b ^(4:ℕ) * C g * X 2 ^(2:ℕ) + 2 * C b ^(4:ℕ) * X 0 + C b ^(4:ℕ) * X 2

/-- The coefficient of `X 2` in `kleinRAS 1` at the chart `(1,X0,X1,X2,0)`. -/
noncomputable def zH1 (a b g : R) : MvPolynomial (Fin 3) R :=
  -1 * C a ^(4:ℕ) * C g * X 0 * X 1 + -2 * C a ^(4:ℕ) * C g * X 1 * X 2 + 2 * C a ^(4:ℕ) * C g * X 2 - C a ^(4:ℕ) * X 0 ^(2:ℕ) + C a ^(4:ℕ) * X 0 * X 2 - C a ^(4:ℕ) * X 1 ^(2:ℕ) + 2 * C a ^(4:ℕ) * X 1 + C a ^(4:ℕ) * X 2 ^(2:ℕ) + C a ^(4:ℕ) + 2 * C a ^(3:ℕ) * C b * C g * X 0 * X 1 + 2 * C a ^(3:ℕ) * C b * C g * X 1 * X 2 + C a ^(3:ℕ) * C b * C g * X 2 + 2 * C a ^(3:ℕ) * C b * X 1 ^(2:ℕ) + -2 * C a ^(3:ℕ) * C b * X 1 - C a ^(3:ℕ) * C b * X 2 ^(2:ℕ) - C a ^(3:ℕ) * C b + C a ^(2:ℕ) * C b ^(2:ℕ) * C g * X 0 * X 1 + -2 * C a ^(2:ℕ) * C b ^(2:ℕ) * C g * X 2 + -2 * C a ^(2:ℕ) * C b ^(2:ℕ) * X 0 ^(2:ℕ) + C a ^(2:ℕ) * C b ^(2:ℕ) * X 1 + C a ^(2:ℕ) * C b ^(2:ℕ) * X 2 ^(2:ℕ) + -2 * C a * C b ^(3:ℕ) * C g * X 0 * X 1 + 2 * C a * C b ^(3:ℕ) * C g * X 1 * X 2 - C a * C b ^(3:ℕ) * C g * X 2 + 2 * C a * C b ^(3:ℕ) * X 1 ^(2:ℕ) + 2 * C a * C b ^(3:ℕ) * X 1 + C a * C b ^(3:ℕ) * X 2 ^(2:ℕ) - C a * C b ^(3:ℕ) - C b ^(4:ℕ) * C g * X 0 * X 1 + 2 * C b ^(4:ℕ) * C g * X 1 * X 2 + 2 * C b ^(4:ℕ) * C g * X 2 - C b ^(4:ℕ) * X 0 ^(2:ℕ) - C b ^(4:ℕ) * X 0 * X 2 + C b ^(4:ℕ) * X 1 ^(2:ℕ) + 2 * C b ^(4:ℕ) * X 1 + C b ^(4:ℕ) * X 2 ^(2:ℕ) - C b ^(4:ℕ)

/-- The coefficient of `X 2` in `kleinRAS 2` at the chart `(1,X0,X1,X2,0)`. -/
noncomputable def zH2 (a b g : R) : MvPolynomial (Fin 3) R :=
  2 * C a ^(4:ℕ) * C g * X 0 * X 2 + 2 * C a ^(4:ℕ) * C g * X 1 ^(2:ℕ) + 2 * C a ^(4:ℕ) * C g * X 2 ^(2:ℕ) - C a ^(4:ℕ) * X 0 * X 1 + C a ^(4:ℕ) * X 0 + 2 * C a ^(4:ℕ) * X 1 * X 2 - C a ^(4:ℕ) * X 2 + C a ^(3:ℕ) * C b * C g * X 0 * X 2 + C a ^(3:ℕ) * C b * C g * X 1 ^(2:ℕ) + -2 * C a ^(3:ℕ) * C b * C g * X 2 ^(2:ℕ) + 2 * C a ^(3:ℕ) * C b * X 0 * X 1 - C a ^(3:ℕ) * C b * X 0 + 2 * C a ^(3:ℕ) * C b * X 1 * X 2 + -2 * C a ^(2:ℕ) * C b ^(2:ℕ) * C g * X 0 * X 2 + -2 * C a ^(2:ℕ) * C b ^(2:ℕ) * C g * X 1 ^(2:ℕ) + C a ^(2:ℕ) * C b ^(2:ℕ) * X 0 * X 1 + -2 * C a ^(2:ℕ) * C b ^(2:ℕ) * X 2 - C a * C b ^(3:ℕ) * C g * X 0 * X 2 - C a * C b ^(3:ℕ) * C g * X 1 ^(2:ℕ) + -2 * C a * C b ^(3:ℕ) * C g * X 2 ^(2:ℕ) + -2 * C a * C b ^(3:ℕ) * X 0 * X 1 - C a * C b ^(3:ℕ) * X 0 + 2 * C a * C b ^(3:ℕ) * X 1 * X 2 + 2 * C b ^(4:ℕ) * C g * X 0 * X 2 + 2 * C b ^(4:ℕ) * C g * X 1 ^(2:ℕ) + -2 * C b ^(4:ℕ) * C g * X 2 ^(2:ℕ) - C b ^(4:ℕ) * X 0 * X 1 - C b ^(4:ℕ) * X 0 + -2 * C b ^(4:ℕ) * X 1 * X 2 - C b ^(4:ℕ) * X 2

/-- The coefficient of `X 2` in `kleinRAS 3` at the chart `(1,X0,X1,X2,0)`. -/
noncomputable def zH3 (a b g : R) : MvPolynomial (Fin 3) R :=
  2 * C a ^(4:ℕ) * C g * X 1 * X 2 - C a ^(4:ℕ) * X 0 ^(2:ℕ) + C a ^(4:ℕ) * X 0 * X 2 - C a ^(4:ℕ) * X 1 ^(2:ℕ) - C a ^(4:ℕ) * X 1 + C a ^(4:ℕ) * X 2 ^(2:ℕ) + 2 * C a ^(4:ℕ) + C a ^(3:ℕ) * C b * C g * X 1 * X 2 + C a ^(3:ℕ) * C b * X 0 ^(2:ℕ) - C a ^(3:ℕ) * C b * X 0 * X 2 + C a ^(3:ℕ) * C b * X 1 + -2 * C a ^(3:ℕ) * C b * X 2 ^(2:ℕ) + C a ^(3:ℕ) * C b + -2 * C a ^(2:ℕ) * C b ^(2:ℕ) * C g * X 1 * X 2 + -2 * C a ^(2:ℕ) * C b ^(2:ℕ) * X 0 * X 2 + -2 * C a ^(2:ℕ) * C b ^(2:ℕ) * X 1 ^(2:ℕ) + -2 * C a ^(2:ℕ) * C b ^(2:ℕ) - C a * C b ^(3:ℕ) * C g * X 1 * X 2 + C a * C b ^(3:ℕ) * X 0 ^(2:ℕ) + C a * C b ^(3:ℕ) * X 0 * X 2 + C a * C b ^(3:ℕ) * X 1 + -2 * C a * C b ^(3:ℕ) * X 2 ^(2:ℕ) - C a * C b ^(3:ℕ) + 2 * C b ^(4:ℕ) * C g * X 1 * X 2 + C b ^(4:ℕ) * X 0 ^(2:ℕ) + C b ^(4:ℕ) * X 0 * X 2 - C b ^(4:ℕ) * X 1 ^(2:ℕ) + C b ^(4:ℕ) * X 1 - C b ^(4:ℕ) * X 2 ^(2:ℕ) + 2 * C b ^(4:ℕ)

/-- The coefficient of `X 2` in `kleinRAS 4` at the chart `(1,X0,X1,X2,0)`. -/
noncomputable def zH4 (a b g : R) : MvPolynomial (Fin 3) R :=
  -1 * C a ^(4:ℕ) * C g * X 2 ^(2:ℕ) - C a ^(4:ℕ) * X 0 * X 1 - C a ^(4:ℕ) * X 0 + 2 * C a ^(4:ℕ) * X 1 * X 2 + -2 * C a ^(4:ℕ) * X 2 + 2 * C a ^(3:ℕ) * C b * C g * X 2 ^(2:ℕ) + C a ^(3:ℕ) * C b * X 0 * X 1 + 2 * C a ^(3:ℕ) * C b * X 0 + C a ^(3:ℕ) * C b * X 1 * X 2 + 2 * C a ^(3:ℕ) * C b * X 2 + C a ^(2:ℕ) * C b ^(2:ℕ) * C g * X 2 ^(2:ℕ) + C a ^(2:ℕ) * C b ^(2:ℕ) * X 0 + -2 * C a ^(2:ℕ) * C b ^(2:ℕ) * X 1 * X 2 + -2 * C a * C b ^(3:ℕ) * C g * X 2 ^(2:ℕ) + C a * C b ^(3:ℕ) * X 0 * X 1 + -2 * C a * C b ^(3:ℕ) * X 0 - C a * C b ^(3:ℕ) * X 1 * X 2 + 2 * C a * C b ^(3:ℕ) * X 2 - C b ^(4:ℕ) * C g * X 2 ^(2:ℕ) + C b ^(4:ℕ) * X 0 * X 1 - C b ^(4:ℕ) * X 0 + 2 * C b ^(4:ℕ) * X 1 * X 2 + 2 * C b ^(4:ℕ) * X 2

/-- `s = a - 3b`. -/
noncomputable def zS (a b : R) : MvPolynomial (Fin 3) R := C a - 3 * C b

/-- The affine relation `s X0^2 - (s+b) X1^2 + s X1`. -/
noncomputable def zE (a b : R) : MvPolynomial (Fin 3) R :=
  zS a b * X 0 ^(2:ℕ) - (zS a b + C b) * X 1 ^(2:ℕ) + zS a b * X 1

noncomputable def zA1 (a b : R) : MvPolynomial (Fin 3) R :=
  C a ^(2:ℕ) * X 1 + 2 * C a ^(2:ℕ) + 4 * C a * C b * X 1 ^(2:ℕ) + 3 * C a * C b + C b ^(2:ℕ) * X 1 + 3 * C b ^(2:ℕ)

noncomputable def zB1 (a b g : R) : MvPolynomial (Fin 3) R :=
  4 * C a ^(2:ℕ) * C g * X 1 ^(3:ℕ) + C a * C b * C g * X 1 ^(3:ℕ) + C b ^(2:ℕ) * C g * X 1 ^(3:ℕ)

noncomputable def zA2 (a b g : R) : MvPolynomial (Fin 3) R :=
  2 * C a ^(3:ℕ) * C g * X 1 ^(2:ℕ) + -18 * C a ^(2:ℕ) * C b * C g * X 1 ^(2:ℕ) + 54 * C a * C b ^(2:ℕ) * C g * X 1 ^(2:ℕ) + -54 * C b ^(3:ℕ) * C g * X 1 ^(2:ℕ)

noncomputable def zB2 (a b g : R) : MvPolynomial (Fin 3) R :=
  3 * C a ^(3:ℕ) * X 1 ^(2:ℕ) + 3 * C a ^(3:ℕ) * X 1 + 4 * C a ^(3:ℕ) + 2 * C a ^(2:ℕ) * C b * X 1 ^(3:ℕ) + 2 * C a ^(2:ℕ) * C b * X 1 ^(2:ℕ) + C a ^(2:ℕ) * C b * X 1 + 4 * C a ^(2:ℕ) * C b + C a * C b ^(2:ℕ) * X 1 ^(3:ℕ) + 4 * C a * C b ^(2:ℕ) * X 1 ^(2:ℕ) + 3 * C a * C b ^(2:ℕ) * X 1 + 3 * C a * C b ^(2:ℕ) + 4 * C b ^(3:ℕ) * X 1 ^(2:ℕ) + C b ^(3:ℕ) * X 1 + 2 * C b ^(3:ℕ)

/-- The eliminant, as a polynomial in the three variables. -/
noncomputable def zR (a b g : R) : MvPolynomial (Fin 3) R :=
  3 * C a ^(5:ℕ) * C g ^(2:ℕ) * X 1 ^(5:ℕ) + 2 * C a ^(5:ℕ) * X 1 ^(3:ℕ) + C a ^(5:ℕ) * X 1 ^(2:ℕ) + 2 * C a ^(5:ℕ) + C a ^(4:ℕ) * C b * X 1 ^(4:ℕ) + 2 * C a ^(4:ℕ) * C b * X 1 ^(3:ℕ) + 2 * C a ^(3:ℕ) * C b ^(2:ℕ) * X 1 ^(5:ℕ) + C a ^(3:ℕ) * C b ^(2:ℕ) * X 1 ^(4:ℕ) + C a ^(3:ℕ) * C b ^(2:ℕ) * X 1 ^(3:ℕ) + C a ^(2:ℕ) * C b ^(3:ℕ) * X 1 ^(5:ℕ) + 2 * C a ^(2:ℕ) * C b ^(3:ℕ) * X 1 ^(4:ℕ) + 3 * C a ^(2:ℕ) * C b ^(3:ℕ) * X 1 ^(3:ℕ) + 3 * C a * C b ^(4:ℕ) * X 1 ^(4:ℕ) + 4 * C a * C b ^(4:ℕ) * X 1 ^(3:ℕ) + C b ^(5:ℕ) * C g ^(2:ℕ) * X 1 ^(5:ℕ) + C b ^(5:ℕ) * X 1 ^(3:ℕ) + 2 * C b ^(5:ℕ) * X 1 ^(2:ℕ) + 4 * C b ^(5:ℕ)

/-- The same quintic in one variable. -/
noncomputable def zRp (a b g : R) : Polynomial R :=
  Polynomial.C (3 * a ^(5:ℕ) * g ^(2:ℕ) + 2 * a ^(3:ℕ) * b ^(2:ℕ) + a ^(2:ℕ) * b ^(3:ℕ) + b ^(5:ℕ) * g ^(2:ℕ)) * Polynomial.X ^(5:ℕ) + Polynomial.C (a ^(4:ℕ) * b + a ^(3:ℕ) * b ^(2:ℕ) + 2 * a ^(2:ℕ) * b ^(3:ℕ) + 3 * a * b ^(4:ℕ)) * Polynomial.X ^(4:ℕ) + Polynomial.C (2 * a ^(5:ℕ) + 2 * a ^(4:ℕ) * b + a ^(3:ℕ) * b ^(2:ℕ) + 3 * a ^(2:ℕ) * b ^(3:ℕ) + 4 * a * b ^(4:ℕ) + b ^(5:ℕ)) * Polynomial.X ^(3:ℕ) + Polynomial.C (a ^(5:ℕ) + 2 * b ^(5:ℕ)) * Polynomial.X ^(2:ℕ) + Polynomial.C (2 * a ^(5:ℕ) + 4 * b ^(5:ℕ))

noncomputable def zT1 (a b g : R) : MvPolynomial (Fin 3) R :=
  zQ1 a b g + zS a b * ((C a) ^(2:ℕ) + (C b) ^(2:ℕ)) * X 0 * zE a b

noncomputable def zT2 (a b g : R) : MvPolynomial (Fin 3) R :=
  zS a b * zQ0 a b g - 4 * (zS a b) ^(3:ℕ) * (zS a b + C b) * zE a b

noncomputable def zJ1 (a b : R) : MvPolynomial (Fin 3) R :=
  C a ^(4:ℕ) * C b * X 0 ^(2:ℕ) * X 1 + -5 * C a ^(4:ℕ) * C b * X 0 ^(2:ℕ) + 5 * C a ^(4:ℕ) * C b * X 1 ^(2:ℕ) + -5 * C a ^(4:ℕ) * C b * X 1 + -2 * C a ^(3:ℕ) * C b ^(2:ℕ) * X 0 ^(2:ℕ) * X 1 + 37 * C a ^(3:ℕ) * C b ^(2:ℕ) * X 0 ^(2:ℕ) - C a ^(3:ℕ) * C b ^(2:ℕ) * X 1 ^(3:ℕ) + -32 * C a ^(3:ℕ) * C b ^(2:ℕ) * X 1 ^(2:ℕ) + 37 * C a ^(3:ℕ) * C b ^(2:ℕ) * X 1 + C a ^(2:ℕ) * C b ^(3:ℕ) * X 0 ^(2:ℕ) * X 1 + -109 * C a ^(2:ℕ) * C b ^(3:ℕ) * X 0 ^(2:ℕ) + C a ^(2:ℕ) * C b ^(3:ℕ) * X 1 ^(3:ℕ) + 87 * C a ^(2:ℕ) * C b ^(3:ℕ) * X 1 ^(2:ℕ) + -109 * C a ^(2:ℕ) * C b ^(3:ℕ) * X 1 + 161 * C a * C b ^(4:ℕ) * X 0 ^(2:ℕ) + -118 * C a * C b ^(4:ℕ) * X 1 ^(2:ℕ) + 161 * C a * C b ^(4:ℕ) * X 1 + -2 * C b ^(5:ℕ) * X 0 ^(2:ℕ) * X 1 + -96 * C b ^(5:ℕ) * X 0 ^(2:ℕ) + -2 * C b ^(5:ℕ) * X 1 ^(3:ℕ) + 64 * C b ^(5:ℕ) * X 1 ^(2:ℕ) + -96 * C b ^(5:ℕ) * X 1

noncomputable def zJ2 (a b g : R) : MvPolynomial (Fin 3) R :=
  -1 * C a ^(7:ℕ) * C g ^(2:ℕ) * X 1 ^(5:ℕ) + C a ^(7:ℕ) * X 0 ^(2:ℕ) * X 1 + 2 * C a ^(7:ℕ) * X 0 ^(2:ℕ) - C a ^(7:ℕ) * X 1 ^(3:ℕ) - C a ^(7:ℕ) * X 1 ^(2:ℕ) + C a ^(7:ℕ) * X 1 + 8 * C a ^(6:ℕ) * C b * C g ^(2:ℕ) * X 1 ^(5:ℕ) + -2 * C a ^(6:ℕ) * C b * C g * X 0 ^(3:ℕ) * X 1 ^(2:ℕ) + -5 * C a ^(6:ℕ) * C b * C g * X 0 * X 1 ^(3:ℕ) + -6 * C a ^(6:ℕ) * C b * C g * X 0 * X 1 ^(2:ℕ) + 4 * C a ^(6:ℕ) * C b * X 0 ^(2:ℕ) * X 1 ^(2:ℕ) + -12 * C a ^(6:ℕ) * C b * X 0 ^(2:ℕ) * X 1 + -21 * C a ^(6:ℕ) * C b * X 0 ^(2:ℕ) + -3 * C a ^(6:ℕ) * C b * X 1 ^(4:ℕ) + 13 * C a ^(6:ℕ) * C b * X 1 ^(3:ℕ) + 11 * C a ^(6:ℕ) * C b * X 1 ^(2:ℕ) + -19 * C a ^(6:ℕ) * C b * X 1 + C a ^(6:ℕ) * C b + -23 * C a ^(5:ℕ) * C b ^(2:ℕ) * C g ^(2:ℕ) * X 1 ^(5:ℕ) + 22 * C a ^(5:ℕ) * C b ^(2:ℕ) * C g * X 0 ^(3:ℕ) * X 1 ^(2:ℕ) + -14 * C a ^(5:ℕ) * C b ^(2:ℕ) * C g * X 0 * X 1 ^(4:ℕ) + 37 * C a ^(5:ℕ) * C b ^(2:ℕ) * C g * X 0 * X 1 ^(3:ℕ) + 21 * C a ^(5:ℕ) * C b ^(2:ℕ) * C g * X 0 * X 1 ^(2:ℕ) + -48 * C a ^(5:ℕ) * C b ^(2:ℕ) * X 0 ^(2:ℕ) * X 1 ^(2:ℕ) + 64 * C a ^(5:ℕ) * C b ^(2:ℕ) * X 0 ^(2:ℕ) * X 1 + 93 * C a ^(5:ℕ) * C b ^(2:ℕ) * X 0 ^(2:ℕ) + -2 * C a ^(5:ℕ) * C b ^(2:ℕ) * X 1 ^(5:ℕ) + 43 * C a ^(5:ℕ) * C b ^(2:ℕ) * X 1 ^(4:ℕ) + -94 * C a ^(5:ℕ) * C b ^(2:ℕ) * X 1 ^(3:ℕ) + -25 * C a ^(5:ℕ) * C b ^(2:ℕ) * X 1 ^(2:ℕ) + 96 * C a ^(5:ℕ) * C b ^(2:ℕ) * X 1 + -4 * C a ^(5:ℕ) * C b ^(2:ℕ) + 28 * C a ^(4:ℕ) * C b ^(3:ℕ) * C g ^(2:ℕ) * X 1 ^(5:ℕ) + -92 * C a ^(4:ℕ) * C b ^(3:ℕ) * C g * X 0 ^(3:ℕ) * X 1 ^(2:ℕ) + 82 * C a ^(4:ℕ) * C b ^(3:ℕ) * C g * X 0 * X 1 ^(4:ℕ) + -114 * C a ^(4:ℕ) * C b ^(3:ℕ) * C g * X 0 * X 1 ^(3:ℕ) + 252 * C a ^(4:ℕ) * C b ^(3:ℕ) * X 0 ^(2:ℕ) * X 1 ^(2:ℕ) + -185 * C a ^(4:ℕ) * C b ^(3:ℕ) * X 0 ^(2:ℕ) * X 1 + -193 * C a ^(4:ℕ) * C b ^(3:ℕ) * X 0 ^(2:ℕ) + 7 * C a ^(4:ℕ) * C b ^(3:ℕ) * X 1 ^(5:ℕ) + -221 * C a ^(4:ℕ) * C b ^(3:ℕ) * X 1 ^(4:ℕ) + 390 * C a ^(4:ℕ) * C b ^(3:ℕ) * X 1 ^(3:ℕ) + -39 * C a ^(4:ℕ) * C b ^(3:ℕ) * X 1 ^(2:ℕ) + -190 * C a ^(4:ℕ) * C b ^(3:ℕ) * X 1 + 2 * C a ^(4:ℕ) * C b ^(3:ℕ) + -4 * C a ^(3:ℕ) * C b ^(4:ℕ) * C g ^(2:ℕ) * X 1 ^(5:ℕ) + 184 * C a ^(3:ℕ) * C b ^(4:ℕ) * C g * X 0 ^(3:ℕ) * X 1 ^(2:ℕ) + -168 * C a ^(3:ℕ) * C b ^(4:ℕ) * C g * X 0 * X 1 ^(4:ℕ) + 198 * C a ^(3:ℕ) * C b ^(4:ℕ) * C g * X 0 * X 1 ^(3:ℕ) + -30 * C a ^(3:ℕ) * C b ^(4:ℕ) * C g * X 0 * X 1 ^(2:ℕ) + -692 * C a ^(3:ℕ) * C b ^(4:ℕ) * X 0 ^(2:ℕ) * X 1 ^(2:ℕ) + 301 * C a ^(3:ℕ) * C b ^(4:ℕ) * X 0 ^(2:ℕ) * X 1 + 146 * C a ^(3:ℕ) * C b ^(4:ℕ) * X 0 ^(2:ℕ) + -4 * C a ^(3:ℕ) * C b ^(4:ℕ) * X 1 ^(5:ℕ) + 548 * C a ^(3:ℕ) * C b ^(4:ℕ) * X 1 ^(4:ℕ) + -910 * C a ^(3:ℕ) * C b ^(4:ℕ) * X 1 ^(3:ℕ) + 204 * C a ^(3:ℕ) * C b ^(4:ℕ) * X 1 ^(2:ℕ) + 140 * C a ^(3:ℕ) * C b ^(4:ℕ) * X 1 + 4 * C a ^(3:ℕ) * C b ^(4:ℕ) + -29 * C a ^(2:ℕ) * C b ^(5:ℕ) * C g ^(2:ℕ) * X 1 ^(5:ℕ) + -198 * C a ^(2:ℕ) * C b ^(5:ℕ) * C g * X 0 ^(3:ℕ) * X 1 ^(2:ℕ) + 176 * C a ^(2:ℕ) * C b ^(5:ℕ) * C g * X 0 * X 1 ^(4:ℕ) + -205 * C a ^(2:ℕ) * C b ^(5:ℕ) * C g * X 0 * X 1 ^(3:ℕ) + 952 * C a ^(2:ℕ) * C b ^(5:ℕ) * X 0 ^(2:ℕ) * X 1 ^(2:ℕ) + -302 * C a ^(2:ℕ) * C b ^(5:ℕ) * X 0 ^(2:ℕ) * X 1 + -63 * C a ^(2:ℕ) * C b ^(5:ℕ) * X 0 ^(2:ℕ) + 3 * C a ^(2:ℕ) * C b ^(5:ℕ) * X 1 ^(5:ℕ) + -686 * C a ^(2:ℕ) * C b ^(5:ℕ) * X 1 ^(4:ℕ) + 1171 * C a ^(2:ℕ) * C b ^(5:ℕ) * X 1 ^(3:ℕ) + -241 * C a ^(2:ℕ) * C b ^(5:ℕ) * X 1 ^(2:ℕ) + -68 * C a ^(2:ℕ) * C b ^(5:ℕ) * X 1 + -2 * C a ^(2:ℕ) * C b ^(5:ℕ) + 12 * C a * C b ^(6:ℕ) * C g ^(2:ℕ) * X 1 ^(5:ℕ) + 162 * C a * C b ^(6:ℕ) * C g * X 0 ^(3:ℕ) * X 1 ^(2:ℕ) + -114 * C a * C b ^(6:ℕ) * C g * X 0 * X 1 ^(4:ℕ) + 161 * C a * C b ^(6:ℕ) * C g * X 0 * X 1 ^(3:ℕ) + 33 * C a * C b ^(6:ℕ) * C g * X 0 * X 1 ^(2:ℕ) + -516 * C a * C b ^(6:ℕ) * X 0 ^(2:ℕ) * X 1 ^(2:ℕ) + 238 * C a * C b ^(6:ℕ) * X 0 ^(2:ℕ) * X 1 + 327 * C a * C b ^(6:ℕ) * X 0 ^(2:ℕ) + 339 * C a * C b ^(6:ℕ) * X 1 ^(4:ℕ) + -697 * C a * C b ^(6:ℕ) * X 1 ^(3:ℕ) + -20 * C a * C b ^(6:ℕ) * X 1 ^(2:ℕ) + 317 * C a * C b ^(6:ℕ) * X 1 + 9 * C b ^(7:ℕ) * C g ^(2:ℕ) * X 1 ^(5:ℕ) + -108 * C b ^(7:ℕ) * C g * X 0 ^(3:ℕ) * X 1 ^(2:ℕ) + 54 * C b ^(7:ℕ) * C g * X 0 * X 1 ^(4:ℕ) + -96 * C b ^(7:ℕ) * C g * X 0 * X 1 ^(3:ℕ) + -18 * C b ^(7:ℕ) * C g * X 0 * X 1 ^(2:ℕ) + -129 * C b ^(7:ℕ) * X 0 ^(2:ℕ) * X 1 + -387 * C b ^(7:ℕ) * X 0 ^(2:ℕ) + 84 * C b ^(7:ℕ) * X 1 ^(3:ℕ) + 123 * C b ^(7:ℕ) * X 1 ^(2:ℕ) + -393 * C b ^(7:ℕ) * X 1 + -9 * C b ^(7:ℕ)

/-- Chart substitution for the 0-th cubic. -/
theorem zcub0 (a b g : R) :
    kleinRAS (C a) (C b) (C g) ![1, X 0, X 1, X 2, 0] 0 = zQ0 a b g + X 2 * zH0 a b g := by
  simp only [zQ0, zH0, kleinRAS, kleinRAS0, kleinRAS1, kleinRAS2, kleinRAS3, kleinRAS4,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  refl_ring1

/-- Chart substitution for the 1-th cubic. -/
theorem zcub1 (a b g : R) :
    kleinRAS (C a) (C b) (C g) ![1, X 0, X 1, X 2, 0] 1 = zQ1 a b g + X 2 * zH1 a b g := by
  simp only [zQ1, zH1, kleinRAS, kleinRAS0, kleinRAS1, kleinRAS2, kleinRAS3, kleinRAS4,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  refl_ring1

/-- Chart substitution for the 2-th cubic. -/
theorem zcub2 (a b g : R) :
    kleinRAS (C a) (C b) (C g) ![1, X 0, X 1, X 2, 0] 2 = zQ2 a b g + X 2 * zH2 a b g := by
  simp only [zQ2, zH2, kleinRAS, kleinRAS0, kleinRAS1, kleinRAS2, kleinRAS3, kleinRAS4,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  refl_ring1

/-- Chart substitution for the 3-th cubic. -/
theorem zcub3 (a b g : R) :
    kleinRAS (C a) (C b) (C g) ![1, X 0, X 1, X 2, 0] 3 = zQ3 a b g + X 2 * zH3 a b g := by
  simp only [zQ3, zH3, kleinRAS, kleinRAS0, kleinRAS1, kleinRAS2, kleinRAS3, kleinRAS4,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  refl_ring1

/-- Chart substitution for the 4-th cubic. -/
theorem zcub4 (a b g : R) :
    kleinRAS (C a) (C b) (C g) ![1, X 0, X 1, X 2, 0] 4 = zQ4 a b g + X 2 * zH4 a b g := by
  simp only [zQ4, zH4, kleinRAS, kleinRAS0, kleinRAS1, kleinRAS2, kleinRAS3, kleinRAS4,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  refl_ring1

/-- **The affine relation.** `2 s^4 E = s Q2 - (s+b) Q4` modulo `5`. -/
theorem zE_cert (a b g : R) :
    2 * (zS a b) ^(4:ℕ) * zE a b
      = zS a b * zQ2 a b g - (zS a b + C b) * zQ4 a b g + 5 * zJ1 a b := by
  simp only [zS, zE, zQ2, zQ4, zJ1]
  refl_ring1

/-- **The eliminant.** `A2 T1 - A1 T2 = s^2 R` modulo `5`. -/
theorem zR_cert (a b g : R) :
    zA2 a b g * zT1 a b g - zA1 a b * zT2 a b g = (zS a b) ^(2:ℕ) * zR a b g + 5 * zJ2 a b g := by
  simp only [zA2, zT1, zA1, zT2, zS, zE, zQ0, zQ1, zR, zJ2]
  refl_ring1

/-- The one-variable quintic is the image of the three-variable version under `X 1`. -/
theorem zR_bridge (a b g : R) :
    Polynomial.aeval (X 1 : MvPolynomial (Fin 3) R) (zRp a b g) = zR a b g := by
  simp only [zRp, zR, Polynomial.aeval_C, Polynomial.aeval_X, map_add, map_mul, map_pow,
    map_ofNat, MvPolynomial.algebraMap_eq]
  refl_ring1

end Certificates

/-! ## §2 Finiteness of the AS chart slice -/

/-- A `K`-algebra generated by two integral elements is a finite `K`-module. -/
theorem module_finite_of_adjoin_pair {K B : Type*} [Field K] [CommRing B] [Algebra K B]
    (x0 x1 : B) (hgen : Algebra.adjoin K ({x0, x1} : Set B) = ⊤)
    (h0 : IsIntegral K x0) (h1 : IsIntegral K x1) : Module.Finite K B := by
  have hInt : Algebra.IsIntegral K B := by
    rw [← integralClosure_eq_top_iff, eq_top_iff, ← hgen]
    refine Algebra.adjoin_le ?_
    intro y hy
    rcases Set.mem_insert_iff.mp hy with h | h
    · rw [h]; exact (mem_integralClosure_iff K B).mpr h0
    · rw [Set.mem_singleton_iff.mp h]; exact (mem_integralClosure_iff K B).mpr h1
  haveI : Algebra.IsIntegral K B := hInt
  haveI : Algebra.FiniteType K B := by
    classical
    exact ⟨({x0, x1} : Finset B), by simpa using hgen⟩
  exact Algebra.IsIntegral.finite

theorem ZIAS_X2_saturated (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) :
    Module.Finite (RatFunc 𝕜) (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸
        (Work.MotAS.ZIAS (Work.MotAS.aK D) (Work.MotAS.bK D) (Work.MotV.fAS 𝕜)
          ⊔ Ideal.span {(MvPolynomial.X 2 : MvPolynomial (Fin 3) (RatFunc 𝕜))})) := by
  set K := RatFunc 𝕜 with hK
  set a : K := Work.MotAS.aK D with ha
  set b : K := Work.MotAS.bK D with hb
  set g : K := Work.MotV.fAS 𝕜 with hg
  have haK : a = algebraMap 𝕜 K D.a := ha
  have hbK : b = algebraMap 𝕜 K D.b := hb
  have h5K : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h5X : (5 : MvPolynomial (Fin 3) K) = 0 := by
    rw [← map_ofNat (algebraMap K (MvPolynomial (Fin 3) K)) 5, h5K, map_zero]
  have halg_zero : ∀ c : 𝕜, algebraMap 𝕜 K c = 0 → c = 0 := by
    intro c hc
    by_contra hne
    have h1 : algebraMap 𝕜 K (c * c⁻¹) = 1 := by rw [mul_inv_cancel₀ hne, map_one]
    rw [map_mul, hc, zero_mul] at h1
    exact one_ne_zero h1.symm
  have hab : D.a * D.b ≠ 0 := hD.1.ab_ne
  have ha0 : a ≠ 0 := by
    intro h
    exact (mul_ne_zero_iff.mp hab).1 (halg_zero D.a (by rw [← haK, h]))
  have hb0 : b ≠ 0 := by
    intro h
    exact (mul_ne_zero_iff.mp hab).2 (halg_zero D.b (by rw [← hbK, h]))
  have hs2 : (a - 3 * b) ^(2:ℕ) = algebraMap 𝕜 K (D.a ^(2:ℕ) - D.a * D.b - D.b ^(2:ℕ)) := by
    have hcorr : (a - 3 * b) ^(2:ℕ)
        = algebraMap 𝕜 K (D.a ^(2:ℕ) - D.a * D.b - D.b ^(2:ℕ)) + 5 * (2 * b ^(2:ℕ) - a * b) := by
      rw [haK, hbK]
      simp only [map_sub, map_mul, map_pow]
      refl_ring1
    rw [hcorr, h5K]
    refl_ring1
  have hs : a - 3 * b ≠ 0 := by
    intro h
    apply hD.2.2.2
    apply halg_zero
    have h3 : (a - 3 * b) ^(2:ℕ) = 0 := by rw [h]; ring
    rw [hs2] at h3
    simpa using h3
  have h2ne : (2 : K) ≠ 0 := by
    intro h
    have hd : (5 : ℕ) ∣ 2 := (CharP.cast_eq_zero_iff K 5 2).mp h
    norm_num at hd
  have hcne : (2 : K) * (a - 3 * b) ^(4:ℕ) ≠ 0 :=
    mul_ne_zero h2ne (pow_ne_zero 4 hs)
  have hcne2 : (a - 3 * b) ^(2:ℕ) ≠ 0 := pow_ne_zero 2 hs
  set I : Ideal (MvPolynomial (Fin 3) K) :=
    Work.MotAS.ZIAS a b g ⊔ Ideal.span {(MvPolynomial.X 2 : MvPolynomial (Fin 3) K)} with hI
  have hX2 : (MvPolynomial.X 2 : MvPolynomial (Fin 3) K) ∈ I :=
    Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _))
  have hQ (k : Fin 5) : zcubAS a b g k ∈ I :=
    Ideal.mem_sup_left (Ideal.subset_span ⟨k, rfl⟩)
  have hQ' (k : Fin 5) :
      kleinRAS (C a) (C b) (C g) ![1, X 0, X 1, X 2, 0] k ∈ I := hQ k
  have hQ0 : zQ0 a b g ∈ I := by
    have h := zcub0 (R := K) a b g
    have h' : zQ0 a b g
        = kleinRAS (C a) (C b) (C g) ![1, X 0, X 1, X 2, 0] 0 - X 2 * zH0 a b g := by
      rw [h]; ring
    rw [h']
    exact sub_mem (hQ' 0) (Ideal.mul_mem_right (zH0 a b g) I hX2)
  have hQ1 : zQ1 a b g ∈ I := by
    have h := zcub1 (R := K) a b g
    have h' : zQ1 a b g
        = kleinRAS (C a) (C b) (C g) ![1, X 0, X 1, X 2, 0] 1 - X 2 * zH1 a b g := by
      rw [h]; ring
    rw [h']
    exact sub_mem (hQ' 1) (Ideal.mul_mem_right (zH1 a b g) I hX2)
  have hQ2 : zQ2 a b g ∈ I := by
    have h := zcub2 (R := K) a b g
    have h' : zQ2 a b g
        = kleinRAS (C a) (C b) (C g) ![1, X 0, X 1, X 2, 0] 2 - X 2 * zH2 a b g := by
      rw [h]; ring
    rw [h']
    exact sub_mem (hQ' 2) (Ideal.mul_mem_right (zH2 a b g) I hX2)
  have hQ3 : zQ3 a b g ∈ I := by
    have h := zcub3 (R := K) a b g
    have h' : zQ3 a b g
        = kleinRAS (C a) (C b) (C g) ![1, X 0, X 1, X 2, 0] 3 - X 2 * zH3 a b g := by
      rw [h]; ring
    rw [h']
    exact sub_mem (hQ' 3) (Ideal.mul_mem_right (zH3 a b g) I hX2)
  have hQ4 : zQ4 a b g ∈ I := by
    have h := zcub4 (R := K) a b g
    have h' : zQ4 a b g
        = kleinRAS (C a) (C b) (C g) ![1, X 0, X 1, X 2, 0] 4 - X 2 * zH4 a b g := by
      rw [h]; ring
    rw [h']
    exact sub_mem (hQ' 4) (Ideal.mul_mem_right (zH4 a b g) I hX2)
  have hSc : zS a b = C (a - 3 * b) := by
    rw [zS]
    simp only [map_sub, map_mul, map_ofNat]
  have hE : zE a b ∈ I := by
    have hcert := zE_cert (R := K) a b g
    have hmem : 2 * (zS a b) ^(4:ℕ) * zE a b ∈ I := by
      rw [hcert]
      have hz : zS a b * zQ2 a b g - (zS a b + C b) * zQ4 a b g + 5 * zJ1 a b
          = zS a b * zQ2 a b g - (zS a b + C b) * zQ4 a b g := by
        rw [h5X]; ring
      rw [hz]
      exact sub_mem (Ideal.mul_mem_left I (zS a b) hQ2)
        (Ideal.mul_mem_left I (zS a b + C b) hQ4)
    have hunit : 2 * (zS a b) ^(4:ℕ) = C (2 * (a - 3 * b) ^(4:ℕ)) := by
      rw [hSc, ← map_ofNat MvPolynomial.C 2, ← map_pow, ← map_mul]
    have heq : zE a b = C (((2 : K) * (a - 3 * b) ^(4:ℕ))⁻¹) * (2 * (zS a b) ^(4:ℕ) * zE a b) := by
      rw [hunit, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hcne, map_one, one_mul]
    rw [heq]
    exact Ideal.mul_mem_left I _ hmem
  have hRmem : zR a b g ∈ I := by
    have hcert := zR_cert (R := K) a b g
    have hT1 : zT1 a b g ∈ I := by
      rw [zT1]
      exact add_mem hQ1
        (Ideal.mul_mem_left I (zS a b * ((C a) ^(2:ℕ) + (C b) ^(2:ℕ)) * X 0) hE)
    have hT2 : zT2 a b g ∈ I := by
      rw [zT2]
      exact sub_mem (Ideal.mul_mem_left I (zS a b) hQ0)
        (Ideal.mul_mem_left I (4 * (zS a b) ^(3:ℕ) * (zS a b + C b)) hE)
    have hmem : zA2 a b g * zT1 a b g - zA1 a b * zT2 a b g ∈ I :=
      sub_mem (Ideal.mul_mem_left I (zA2 a b g) hT1) (Ideal.mul_mem_left I (zA1 a b) hT2)
    have hsz : (zS a b) ^(2:ℕ) * zR a b g ∈ I := by
      have heq : (zS a b) ^(2:ℕ) * zR a b g
          = zA2 a b g * zT1 a b g - zA1 a b * zT2 a b g := by
        rw [hcert]; rw [h5X]; ring
      rw [heq]; exact hmem
    have hSc2 : (zS a b) ^(2:ℕ) = C ((a - 3 * b) ^(2:ℕ)) := by
      rw [hSc, ← map_pow]
    have heq : zR a b g = C (((a - 3 * b) ^(2:ℕ))⁻¹) * ((zS a b) ^(2:ℕ) * zR a b g) := by
      rw [hSc2, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hcne2, map_one, one_mul]
    rw [heq]
    exact Ideal.mul_mem_left I _ hsz
  set B := MvPolynomial (Fin 3) K ⧸ I with hB
  set x : Fin 3 → B := fun i => Ideal.Quotient.mk I (MvPolynomial.X i) with hx
  have haeval : MvPolynomial.aeval x = Ideal.Quotient.mkₐ K I := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [MvPolynomial.aeval_X, Ideal.Quotient.mkₐ_eq_mk, hx]
  have hmem_eval : ∀ p ∈ I, MvPolynomial.aeval x p = 0 := by
    intro p hp
    rw [haeval, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hp
  have hx2 : x 2 = 0 := by
    rw [hx]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hX2
  -- the eliminated quintic vanishes at `x 1`
  have hcomp : (MvPolynomial.aeval x).comp
        (Polynomial.aeval (X 1 : MvPolynomial (Fin 3) K))
      = Polynomial.aeval (x 1) := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, Polynomial.aeval_X, MvPolynomial.aeval_X]
  have hz : Polynomial.aeval (x 1) (zRp a b g) = 0 := by
    have h := hmem_eval (zR a b g) hRmem
    rw [← zR_bridge, ← AlgHom.comp_apply, hcomp] at h
    exact h
  have hcoeff5 : (zRp a b g).coeff 5
      = 3 * a ^(5:ℕ) * g ^(2:ℕ) + 2 * a ^(3:ℕ) * b ^(2:ℕ) + a ^(2:ℕ) * b ^(3:ℕ) + b ^(5:ℕ) * g ^(2:ℕ) := by
    simp only [zRp, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C]
    norm_num
  have hcoeff2 : (zRp a b g).coeff 2 = a ^(5:ℕ) + 2 * b ^(5:ℕ) := by
    simp only [zRp, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C]
    norm_num
  have hzp : zRp a b g ≠ 0 := by
    by_cases hk : a ^(5:ℕ) + 2 * b ^(5:ℕ) = 0
    · have h3 : 3 * a ^(5:ℕ) + b ^(5:ℕ) = 0 := by
        have hid : 3 * (a ^(5:ℕ) + 2 * b ^(5:ℕ)) - 5 * b ^(5:ℕ) = 3 * a ^(5:ℕ) + b ^(5:ℕ) := by ring
        rw [← hid, hk]
        rw [show (5 : K) * b ^(5:ℕ) = 0 from by rw [h5K]; ring]
        refl_ring1
      have h2ab : 2 * a + b ≠ 0 := by
        intro h
        have hb2 : b = -(2 * a) := by linear_combination h
        rw [hb2] at hk
        have hid : a ^(5:ℕ) + 2 * (-(2 * a)) ^(5:ℕ) = 2 * a ^(5:ℕ) - 5 * (13 * a ^(5:ℕ)) := by ring
        rw [hid] at hk
        rw [show (5 : K) * (13 * a ^(5:ℕ)) = 0 from by rw [h5K]; ring] at hk
        have h2a : 2 * a ^(5:ℕ) = 0 := by simpa using hk
        have h5a : a ^(5:ℕ) = 0 := by
          rcases mul_eq_zero.mp h2a with h' | h'
          · exact absurd h' h2ne
          · exact h'
        exact ha0 (eq_zero_of_pow_eq_zero h5a)
      have hc5 : 3 * a ^(5:ℕ) * g ^(2:ℕ) + 2 * a ^(3:ℕ) * b ^(2:ℕ) + a ^(2:ℕ) * b ^(3:ℕ) + b ^(5:ℕ) * g ^(2:ℕ)
          = a ^(2:ℕ) * b ^(2:ℕ) * (2 * a + b) := by
        have hid : 3 * a ^(5:ℕ) * g ^(2:ℕ) + 2 * a ^(3:ℕ) * b ^(2:ℕ) + a ^(2:ℕ) * b ^(3:ℕ) + b ^(5:ℕ) * g ^(2:ℕ)
            = (3 * a ^(5:ℕ) + b ^(5:ℕ)) * g ^(2:ℕ) + a ^(2:ℕ) * b ^(2:ℕ) * (2 * a + b) := by ring
        rw [hid, h3]
        refl_ring1
      intro hzero
      have hc := congrArg (fun p : Polynomial K => p.coeff 5) hzero
      rw [hcoeff5, hc5] at hc
      simp only [Polynomial.coeff_zero] at hc
      exact (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ha0) (pow_ne_zero 2 hb0)) h2ab) hc
    · intro hzero
      have hc := congrArg (fun p : Polynomial K => p.coeff 2) hzero
      rw [hcoeff2] at hc
      simp only [Polynomial.coeff_zero] at hc
      exact hk hc
  have h1int : IsIntegral K (x 1) :=
    (show IsAlgebraic K (x 1) from ⟨zRp a b g, hzp, hz⟩).isIntegral
  -- the affine relation, and integrality of `x 0`
  have hEx : algebraMap K B (a - 3 * b) * (x 0) ^(2:ℕ)
      - (algebraMap K B (a - 3 * b) + algebraMap K B b) * (x 1) ^(2:ℕ)
      + algebraMap K B (a - 3 * b) * (x 1) = 0 := by
    have h := hmem_eval (zE a b) hE
    rw [zE, zS] at h
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, MvPolynomial.aeval_C,
      MvPolynomial.aeval_X] at h
    simpa only [map_sub, map_mul, map_ofNat] using h
  have hmain : algebraMap K B (a - 3 * b) * (x 0) ^(2:ℕ)
      = (algebraMap K B (a - 3 * b) + algebraMap K B b) * (x 1) ^(2:ℕ)
        - algebraMap K B (a - 3 * b) * (x 1) := by
    linear_combination (norm := refl_ring1) hEx
  have hint_sxsq : IsIntegral K (algebraMap K B (a - 3 * b) * (x 0) ^(2:ℕ)) := by
    rw [hmain]
    exact IsIntegral.sub
      (IsIntegral.mul (IsIntegral.add isIntegral_algebraMap isIntegral_algebraMap)
        (h1int.pow 2))
      (IsIntegral.mul isIntegral_algebraMap h1int)
  have hsqint : IsIntegral K ((x 0) ^(2:ℕ)) := by
    have heq : (x 0) ^(2:ℕ)
        = algebraMap K B ((a - 3 * b)⁻¹) * (algebraMap K B (a - 3 * b) * (x 0) ^(2:ℕ)) := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hs, map_one, one_mul]
    rw [heq]
    exact IsIntegral.mul isIntegral_algebraMap hint_sxsq
  have h0int : IsIntegral K (x 0) := IsIntegral.of_pow (by norm_num) hsqint
  have hgen : Algebra.adjoin K ({x 0, x 1} : Set B) = ⊤ := by
    have h1 : Algebra.adjoin K (Set.range x) = ⊤ := by
      rw [← MvPolynomial.aeval_range]
      refine (AlgHom.range_eq_top (MvPolynomial.aeval x)).mpr ?_
      rw [haeval]
      intro bb
      obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (I := I) bb
      exact ⟨p, by rw [Ideal.Quotient.mkₐ_eq_mk]; exact hp⟩
    rw [← h1]
    apply le_antisymm
    · refine Algebra.adjoin_le ?_
      rintro y (rfl | rfl)
      · exact Algebra.subset_adjoin ⟨0, rfl⟩
      · exact Algebra.subset_adjoin ⟨1, rfl⟩
    · refine Algebra.adjoin_le ?_
      rintro y ⟨i, rfl⟩
      fin_cases i
      · exact Algebra.subset_adjoin (Set.mem_insert_iff.mpr (Or.inl rfl))
      · exact Algebra.subset_adjoin (Set.mem_insert_iff.mpr (Or.inr rfl))
      · show x 2 ∈ Algebra.adjoin K ({x 0, x 1} : Set B)
        rw [hx2]
        exact Subalgebra.zero_mem _
  exact module_finite_of_adjoin_pair (x 0) (x 1) hgen h0int h1int

end Work.MotAS.ASZplane
