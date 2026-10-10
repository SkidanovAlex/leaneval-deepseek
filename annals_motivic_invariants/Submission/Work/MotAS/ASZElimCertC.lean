import Mathlib
import Submission.Work.MotAS.ASResidual

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedVariables false

namespace Work.MotAS

open MvPolynomial

section Certs

variable {K : Type*} [Field K] [CharP K 5]

noncomputable def ASZMemCorr4 (a b g : K) : MvPolynomial (Fin 3) K :=
  (1 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g * X 0
  + (-8 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g * X 0 * X 2 ^(2:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g * X 0 * X 2 ^(4:ℕ)
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g * X 0 * X 1
  + (-3 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g * X 0 * X 1 * X 2 ^(2:ℕ)
  + (-5 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g * X 0 * X 1 ^(2:ℕ)
  + (4 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g * X 0 * X 1 ^(2:ℕ) * X 2 ^(2:ℕ)
  + (-6 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g * X 0 * X 1 ^(3:ℕ)
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g * X 0 * X 1 ^(4:ℕ)
  + (-3 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g * X 0 ^(2:ℕ) * X 2
  + (1 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g * X 0 ^(2:ℕ) * X 2 ^(3:ℕ)
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g * X 0 ^(2:ℕ) * X 1 * X 2
  + (-3 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g * X 0 ^(2:ℕ) * X 1 ^(2:ℕ) * X 2
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g * X 0 ^(3:ℕ)
  + (-7 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g * X 0 ^(3:ℕ) * X 2 ^(2:ℕ)
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g * X 0 ^(3:ℕ) * X 1
  + (1 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g * X 0 ^(4:ℕ) * X 2
  + (2 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g ^(2:ℕ) * X 2 ^(2:ℕ)
  + (-5 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g ^(2:ℕ) * X 2 ^(4:ℕ)
  + (-3 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g ^(2:ℕ) * X 1 * X 2 ^(2:ℕ)
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g ^(2:ℕ) * X 1 * X 2 ^(4:ℕ)
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g ^(2:ℕ) * X 1 ^(2:ℕ) * X 2 ^(2:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g ^(2:ℕ) * X 1 ^(3:ℕ)
  + (-4 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g ^(2:ℕ) * X 1 ^(5:ℕ)
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g ^(2:ℕ) * X 0 * X 2 ^(3:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g ^(2:ℕ) * X 0 * X 1 * X 2
  + (-5 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g ^(2:ℕ) * X 0 * X 1 ^(2:ℕ) * X 2
  + (-3 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g ^(2:ℕ) * X 0 * X 1 ^(3:ℕ) * X 2
  + (1 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g ^(2:ℕ) * X 0 ^(2:ℕ) * X 2 ^(2:ℕ)
  + (-9 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g ^(2:ℕ) * X 0 ^(2:ℕ) * X 1 * X 2 ^(2:ℕ)
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g ^(2:ℕ) * X 0 ^(2:ℕ) * X 1 ^(3:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g ^(2:ℕ) * X 0 ^(3:ℕ) * X 2
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g ^(2:ℕ) * X 0 ^(3:ℕ) * X 1 * X 2
  + (3 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g ^(3:ℕ) * X 2 ^(5:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g ^(3:ℕ) * X 1 * X 2 ^(3:ℕ)

noncomputable def ASZMemCorr5 (a b g : K) : MvPolynomial (Fin 3) K :=
  (-4 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g ^(3:ℕ) * X 1 ^(2:ℕ) * X 2 ^(3:ℕ)
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g ^(3:ℕ) * X 1 ^(4:ℕ) * X 2
  + (-2 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g ^(3:ℕ) * X 0 * X 2 ^(4:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g ^(3:ℕ) * X 0 * X 1 ^(2:ℕ) * X 2 ^(2:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(6:ℕ) * C g ^(3:ℕ) * X 0 ^(2:ℕ) * X 2 ^(3:ℕ)
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ)
  + (-4 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * X 2 ^(2:ℕ)
  + (-5 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * X 1
  + (-2 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * X 1 * X 2 ^(4:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * X 1 ^(2:ℕ)
  + (6 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * X 1 ^(2:ℕ) * X 2 ^(2:ℕ)
  + (6 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * X 1 ^(3:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * X 1 ^(3:ℕ) * X 2 ^(2:ℕ)
  + (-2 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * X 1 ^(5:ℕ)
  + (-2 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * X 0 * X 2
  + (-5 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * X 0 * X 1 * X 2
  + (4 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * X 0 * X 1 * X 2 ^(3:ℕ)
  + (-2 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * X 0 * X 1 ^(2:ℕ) * X 2
  + (6 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * X 0 * X 1 ^(3:ℕ) * X 2
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * X 0 ^(2:ℕ) * X 2 ^(2:ℕ)
  + (-2 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * X 0 ^(2:ℕ) * X 1 * X 2 ^(2:ℕ)
  + (-3 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * X 0 ^(2:ℕ) * X 1 ^(2:ℕ)
  + (6 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * X 0 ^(3:ℕ) * X 2
  + (2 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * X 0 ^(4:ℕ)
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * X 0 ^(4:ℕ) * X 1
  + (-3 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g * X 2
  + (-4 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g * X 2 ^(3:ℕ)
  + (-8 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g * X 1 * X 2
  + (-7 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g * X 1 * X 2 ^(3:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g * X 1 ^(2:ℕ) * X 2 ^(3:ℕ)
  + (9 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g * X 1 ^(3:ℕ) * X 2
  + (1 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g * X 1 ^(4:ℕ) * X 2
  + (1 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g * X 0
  + (-4 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g * X 0 * X 2 ^(2:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g * X 0 * X 2 ^(4:ℕ)

noncomputable def ASZMemCorr6 (a b g : K) : MvPolynomial (Fin 3) K :=
  (-6 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g * X 0 * X 1
  + (-8 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g * X 0 * X 1 ^(2:ℕ)
  + (7 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g * X 0 * X 1 ^(3:ℕ)
  + (8 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g * X 0 * X 1 ^(4:ℕ)
  + (-13 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g * X 0 ^(2:ℕ) * X 2 ^(3:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g * X 0 ^(2:ℕ) * X 1 * X 2
  + (-3 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g * X 0 ^(2:ℕ) * X 1 ^(2:ℕ) * X 2
  + (-3 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g * X 0 ^(3:ℕ) * X 2 ^(2:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g * X 0 ^(3:ℕ) * X 1
  + (1 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g * X 0 ^(3:ℕ) * X 1 ^(2:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g ^(2:ℕ) * X 2 ^(4:ℕ)
  + (-5 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g ^(2:ℕ) * X 1 * X 2 ^(4:ℕ)
  + (-6 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g ^(2:ℕ) * X 1 ^(2:ℕ) * X 2 ^(2:ℕ)
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g ^(2:ℕ) * X 1 ^(3:ℕ)
  + (15 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g ^(2:ℕ) * X 1 ^(3:ℕ) * X 2 ^(2:ℕ)
  + (-3 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g ^(2:ℕ) * X 1 ^(5:ℕ)
  + (-3 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g ^(2:ℕ) * X 0 * X 2 ^(3:ℕ)
  + (-4 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g ^(2:ℕ) * X 0 * X 1 * X 2
  + (2 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g ^(2:ℕ) * X 0 * X 1 * X 2 ^(3:ℕ)
  + (-2 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g ^(2:ℕ) * X 0 * X 1 ^(2:ℕ) * X 2
  + (1 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g ^(2:ℕ) * X 0 ^(2:ℕ) * X 2 ^(2:ℕ)
  + (-5 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g ^(2:ℕ) * X 0 ^(2:ℕ) * X 1 * X 2 ^(2:ℕ)
  + (-4 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g ^(2:ℕ) * X 0 ^(2:ℕ) * X 1 ^(3:ℕ)
  + (-2 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g ^(2:ℕ) * X 0 ^(3:ℕ) * X 2
  + (3 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g ^(2:ℕ) * X 0 ^(3:ℕ) * X 1 * X 2
  + (1 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g ^(3:ℕ) * X 2 ^(5:ℕ)
  + (-2 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g ^(3:ℕ) * X 1 * X 2 ^(3:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g ^(3:ℕ) * X 1 ^(2:ℕ) * X 2 ^(3:ℕ)
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g ^(3:ℕ) * X 0 * X 1 ^(2:ℕ) * X 2 ^(2:ℕ)
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(5:ℕ) * C g ^(3:ℕ) * X 0 ^(2:ℕ) * X 2 ^(3:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * X 2 ^(4:ℕ)
  + (-5 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * X 1
  + (2 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * X 1 ^(2:ℕ)
  + (9 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * X 1 ^(2:ℕ) * X 2 ^(2:ℕ)
  + (-2 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * X 1 ^(3:ℕ) * X 2 ^(2:ℕ)

noncomputable def ASZMemCorr7 (a b g : K) : MvPolynomial (Fin 3) K :=
  (-3 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * X 1 ^(4:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * X 1 ^(5:ℕ)
  + (-10 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * X 0 * X 2 ^(3:ℕ)
  + (5 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * X 0 * X 1 * X 2
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * X 0 * X 1 * X 2 ^(3:ℕ)
  + (-2 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * X 0 * X 1 ^(3:ℕ) * X 2
  + (3 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * X 0 ^(2:ℕ)
  + (-2 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * X 0 ^(2:ℕ) * X 2 ^(2:ℕ)
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * X 0 ^(3:ℕ) * X 2
  + (5 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * X 0 ^(4:ℕ)
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g * X 2
  + (-4 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g * X 2 ^(5:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g * X 1 * X 2
  + (-4 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g * X 1 ^(2:ℕ) * X 2
  + (3 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g * X 1 ^(2:ℕ) * X 2 ^(3:ℕ)
  + (5 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g * X 1 ^(3:ℕ) * X 2
  + (-3 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g * X 0 * X 2 ^(4:ℕ)
  + (4 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g * X 0 * X 1
  + (4 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g * X 0 * X 1 * X 2 ^(2:ℕ)
  + (-9 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g * X 0 * X 1 ^(2:ℕ) * X 2 ^(2:ℕ)
  + (-2 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g * X 0 * X 1 ^(3:ℕ)
  + (3 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g * X 0 ^(2:ℕ) * X 2 ^(3:ℕ)
  + (4 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g * X 0 ^(2:ℕ) * X 1 * X 2
  + (-2 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g * X 0 ^(3:ℕ)
  + (-3 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g * X 0 ^(3:ℕ) * X 2 ^(2:ℕ)
  + (-2 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g * X 0 ^(3:ℕ) * X 1
  + (3 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g * X 0 ^(3:ℕ) * X 1 ^(2:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g * X 0 ^(4:ℕ) * X 2
  + (-2 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g ^(2:ℕ) * X 2 ^(4:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g ^(2:ℕ) * X 1 * X 2 ^(2:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g ^(2:ℕ) * X 1 * X 2 ^(4:ℕ)
  + (3 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g ^(2:ℕ) * X 1 ^(3:ℕ) * X 2 ^(2:ℕ)
  + (-8 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g ^(2:ℕ) * X 0 * X 2 ^(3:ℕ)
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g ^(2:ℕ) * X 0 * X 1 * X 2
  + (5 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g ^(2:ℕ) * X 0 * X 1 * X 2 ^(3:ℕ)
end Certs

end Work.MotAS
