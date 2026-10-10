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

noncomputable def ASZMemCorr8 (a b g : K) : MvPolynomial (Fin 3) K :=
  (1 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g ^(2:ℕ) * X 0 * X 1 ^(2:ℕ) * X 2
  + (2 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g ^(2:ℕ) * X 0 ^(2:ℕ) * X 1 * X 2 ^(2:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g ^(2:ℕ) * X 0 ^(2:ℕ) * X 1 ^(2:ℕ)
  + (-6 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g ^(2:ℕ) * X 0 ^(2:ℕ) * X 1 ^(3:ℕ)
  + (-6 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g ^(2:ℕ) * X 0 ^(3:ℕ) * X 1 * X 2
  + (1 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g ^(3:ℕ) * X 1 * X 2 ^(3:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g ^(3:ℕ) * X 1 ^(4:ℕ) * X 2
  + (-2 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g ^(3:ℕ) * X 0 * X 2 ^(4:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(4:ℕ) * C g ^(3:ℕ) * X 0 * X 1 ^(2:ℕ) * X 2 ^(2:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ)
  + (-2 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * X 2 ^(2:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * X 1
  + (-3 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * X 1 * X 2 ^(2:ℕ)
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * X 1 * X 2 ^(4:ℕ)
  + (-8 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * X 1 ^(2:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * X 1 ^(2:ℕ) * X 2 ^(2:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * X 1 ^(3:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * X 1 ^(3:ℕ) * X 2 ^(2:ℕ)
  + (5 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * X 1 ^(4:ℕ)
  + (7 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * X 0 * X 2
  + (5 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * X 0 * X 1 * X 2 ^(3:ℕ)
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * X 0 * X 1 ^(2:ℕ) * X 2
  + (3 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * X 0 * X 1 ^(3:ℕ) * X 2
  + (1 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * X 0 ^(2:ℕ)
  + (-5 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * X 0 ^(2:ℕ) * X 2 ^(2:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * X 0 ^(2:ℕ) * X 1
  + (4 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * X 0 ^(2:ℕ) * X 1 * X 2 ^(2:ℕ)
  + (-5 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * X 0 ^(2:ℕ) * X 1 ^(2:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * X 0 ^(2:ℕ) * X 1 ^(3:ℕ)
  + (3 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * X 0 ^(3:ℕ) * X 2
  + (-7 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * X 0 ^(3:ℕ) * X 1 * X 2
  + (2 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * X 0 ^(4:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * X 0 ^(4:ℕ) * X 1
  + (-2 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g * X 2
  + (5 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g * X 2 ^(3:ℕ)

noncomputable def ASZMemCorr9 (a b g : K) : MvPolynomial (Fin 3) K :=
  (2 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g * X 1 * X 2
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g * X 1 * X 2 ^(3:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g * X 1 ^(2:ℕ) * X 2 ^(3:ℕ)
  + (-3 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g * X 1 ^(3:ℕ) * X 2
  + (2 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g * X 1 ^(4:ℕ) * X 2
  + (-2 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g * X 0 * X 2 ^(4:ℕ)
  + (5 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g * X 0 * X 1
  + (7 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g * X 0 * X 1 * X 2 ^(2:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g * X 0 * X 1 ^(2:ℕ)
  + (6 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g * X 0 * X 1 ^(2:ℕ) * X 2 ^(2:ℕ)
  + (-9 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g * X 0 * X 1 ^(3:ℕ)
  + (4 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g * X 0 ^(2:ℕ) * X 2 ^(3:ℕ)
  + (-6 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g * X 0 ^(2:ℕ) * X 1 * X 2
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g * X 0 ^(2:ℕ) * X 1 ^(2:ℕ) * X 2
  + (5 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g * X 0 ^(3:ℕ)
  + (-3 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g * X 0 ^(3:ℕ) * X 2 ^(2:ℕ)
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g ^(2:ℕ) * X 2 ^(4:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g ^(2:ℕ) * X 1 * X 2 ^(2:ℕ)
  + (-2 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g ^(2:ℕ) * X 1 * X 2 ^(4:ℕ)
  + (5 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g ^(2:ℕ) * X 1 ^(2:ℕ) * X 2 ^(2:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g ^(2:ℕ) * X 1 ^(3:ℕ)
  + (13 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g ^(2:ℕ) * X 1 ^(3:ℕ) * X 2 ^(2:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g ^(2:ℕ) * X 1 ^(5:ℕ)
  + (-4 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g ^(2:ℕ) * X 0 * X 2 ^(3:ℕ)
  + (4 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g ^(2:ℕ) * X 0 * X 1 * X 2
  + (4 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g ^(2:ℕ) * X 0 * X 1 ^(2:ℕ) * X 2
  + (-5 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g ^(2:ℕ) * X 0 ^(2:ℕ) * X 1 * X 2 ^(2:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g ^(2:ℕ) * X 0 ^(2:ℕ) * X 1 ^(3:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g ^(2:ℕ) * X 0 ^(3:ℕ) * X 1 * X 2
  + (2 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g ^(3:ℕ) * X 1 * X 2 ^(3:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g ^(3:ℕ) * X 1 ^(2:ℕ) * X 2 ^(3:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g ^(3:ℕ) * X 1 ^(4:ℕ) * X 2
  + (-4 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g ^(3:ℕ) * X 0 * X 2 ^(4:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(3:ℕ) * C g ^(3:ℕ) * X 0 * X 1 ^(2:ℕ) * X 2 ^(2:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * X 2 ^(4:ℕ)

noncomputable def ASZMemCorr10 (a b g : K) : MvPolynomial (Fin 3) K :=
  (2 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * X 1
  + (2 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * X 1 * X 2 ^(2:ℕ)
  + (3 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * X 1 ^(2:ℕ)
  + (6 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * X 1 ^(2:ℕ) * X 2 ^(2:ℕ)
  + (-3 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * X 1 ^(3:ℕ)
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * X 1 ^(4:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * X 1 ^(5:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * X 0 * X 2
  + (-2 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * X 0 * X 2 ^(3:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * X 0 * X 1 * X 2
  + (6 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * X 0 * X 1 * X 2 ^(3:ℕ)
  + (-6 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * X 0 * X 1 ^(2:ℕ) * X 2
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * X 0 * X 1 ^(3:ℕ) * X 2
  + (-2 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * X 0 ^(2:ℕ) * X 2 ^(2:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * X 0 ^(2:ℕ) * X 1
  + (-5 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * X 0 ^(2:ℕ) * X 1 * X 2 ^(2:ℕ)
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * X 0 ^(2:ℕ) * X 1 ^(2:ℕ)
  + (3 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * X 0 ^(3:ℕ) * X 1 * X 2
  + (4 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g * X 2
  + (-2 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g * X 2 ^(5:ℕ)
  + (3 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g * X 1 * X 2
  + (-4 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g * X 1 * X 2 ^(3:ℕ)
  + (-2 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g * X 1 ^(2:ℕ) * X 2 ^(3:ℕ)
  + (4 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g * X 1 ^(3:ℕ) * X 2
  + (2 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g * X 1 ^(4:ℕ) * X 2
  + (-2 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g * X 0 * X 2 ^(2:ℕ)
  + (4 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g * X 0 * X 2 ^(4:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g * X 0 * X 1 * X 2 ^(2:ℕ)
  + (7 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g * X 0 * X 1 ^(2:ℕ)
  + (-2 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g * X 0 * X 1 ^(3:ℕ)
  + (-2 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g * X 0 * X 1 ^(4:ℕ)
  + (3 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g * X 0 ^(2:ℕ) * X 2
  + (4 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g * X 0 ^(2:ℕ) * X 2 ^(3:ℕ)
  + (6 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g * X 0 ^(2:ℕ) * X 1 * X 2
  + (1 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g * X 0 ^(3:ℕ)

noncomputable def ASZMemCorr11 (a b g : K) : MvPolynomial (Fin 3) K :=
  (7 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g * X 0 ^(3:ℕ) * X 2 ^(2:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g * X 0 ^(3:ℕ) * X 1 ^(2:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g * X 0 ^(4:ℕ) * X 2
  + (1 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g ^(2:ℕ) * X 2 ^(4:ℕ)
  + (3 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g ^(2:ℕ) * X 1 * X 2 ^(2:ℕ)
  + (4 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g ^(2:ℕ) * X 1 * X 2 ^(4:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g ^(2:ℕ) * X 1 ^(2:ℕ) * X 2 ^(2:ℕ)
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g ^(2:ℕ) * X 1 ^(3:ℕ) * X 2 ^(2:ℕ)
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g ^(2:ℕ) * X 1 ^(5:ℕ)
  + (5 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g ^(2:ℕ) * X 0 * X 1 * X 2 ^(3:ℕ)
  + (-3 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g ^(2:ℕ) * X 0 * X 1 ^(3:ℕ) * X 2
  + (1 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g ^(2:ℕ) * X 0 ^(2:ℕ) * X 2 ^(2:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g ^(2:ℕ) * X 0 ^(2:ℕ) * X 1 * X 2 ^(2:ℕ)
  + (7 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g ^(2:ℕ) * X 0 ^(2:ℕ) * X 1 ^(3:ℕ)
  + (6 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g ^(2:ℕ) * X 0 ^(3:ℕ) * X 1 * X 2
  + (2 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g ^(3:ℕ) * X 2 ^(5:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(2:ℕ) * C g ^(3:ℕ) * X 0 * X 2 ^(4:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(7:ℕ) * C b * X 1
  + (-3 : MvPolynomial (Fin 3) K) * C a ^(7:ℕ) * C b * X 1 * X 2 ^(2:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a ^(7:ℕ) * C b * X 1 ^(2:ℕ)
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(7:ℕ) * C b * X 1 ^(2:ℕ) * X 2 ^(2:ℕ)
  + (5 : MvPolynomial (Fin 3) K) * C a ^(7:ℕ) * C b * X 1 ^(3:ℕ) * X 2 ^(2:ℕ)
  + (-3 : MvPolynomial (Fin 3) K) * C a ^(7:ℕ) * C b * X 1 ^(4:ℕ)
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(7:ℕ) * C b * X 0 * X 2
  + (-6 : MvPolynomial (Fin 3) K) * C a ^(7:ℕ) * C b * X 0 * X 2 ^(3:ℕ)
  + (5 : MvPolynomial (Fin 3) K) * C a ^(7:ℕ) * C b * X 0 * X 1 * X 2
  + (2 : MvPolynomial (Fin 3) K) * C a ^(7:ℕ) * C b * X 0 * X 1 ^(2:ℕ) * X 2
  + (-4 : MvPolynomial (Fin 3) K) * C a ^(7:ℕ) * C b * X 0 * X 1 ^(3:ℕ) * X 2
  + (2 : MvPolynomial (Fin 3) K) * C a ^(7:ℕ) * C b * X 0 ^(2:ℕ)
  + (4 : MvPolynomial (Fin 3) K) * C a ^(7:ℕ) * C b * X 0 ^(2:ℕ) * X 2 ^(2:ℕ)
  + (4 : MvPolynomial (Fin 3) K) * C a ^(7:ℕ) * C b * X 0 ^(2:ℕ) * X 1
  + (2 : MvPolynomial (Fin 3) K) * C a ^(7:ℕ) * C b * X 0 ^(2:ℕ) * X 1 * X 2 ^(2:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(7:ℕ) * C b * X 0 ^(2:ℕ) * X 1 ^(3:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(7:ℕ) * C b * X 0 ^(4:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a ^(7:ℕ) * C b * C g * X 2
end Certs

end Work.MotAS
