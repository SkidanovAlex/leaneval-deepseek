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

noncomputable def ASZMem0 (a b g : K) : MvPolynomial (Fin 3) K :=
  (1 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) + (-4 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * X 2 ^(2:ℕ)
  + (3 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * X 1
  + (4 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * X 0 * X 2
  + (1 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * X 0 ^(2:ℕ)
  + (-1 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * C g * X 2
  + (-4 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * C g * X 1 * X 2
  + (2 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * C g * X 0
  + (3 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * C g * X 0 * X 1
  + (2 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * C g ^(2:ℕ) * X 2 ^(2:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ)
  + (-4 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ) * X 1
  + (4 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ) * X 1 ^(2:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ) * X 0 * X 2
  + (4 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ) * X 0 ^(2:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ) * C g * X 2
  + (-4 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ) * C g * X 1 * X 2
  + (-4 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ) * C g * X 0
  + (1 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ) * C g * X 0 * X 1
  + (-4 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ) * C g ^(2:ℕ) * X 2 ^(2:ℕ)
  + (4 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(2:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(2:ℕ) * X 1
  + (-4 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(2:ℕ) * X 1 ^(2:ℕ)
  + (6 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(2:ℕ) * X 0 * X 2
  + (4 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(2:ℕ) * X 0 ^(2:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(2:ℕ) * C g * X 2
  + (3 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(2:ℕ) * C g * X 1 * X 2
  + (1 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(2:ℕ) * C g * X 0
  + (9 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(2:ℕ) * C g * X 0 * X 1
  + (2 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(2:ℕ) * C g ^(2:ℕ) * X 2 ^(2:ℕ)
  + (3 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b
  + (-3 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b * X 2 ^(2:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b * X 1
  + (3 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b * X 1 ^(2:ℕ)
  + (6 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b * X 0 * X 2
  + (2 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b * X 0 ^(2:ℕ)
  + (4 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b * C g * X 2
  + (3 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b * C g * X 1 * X 2
  + (1 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b * C g * X 0 * X 1
  + (1 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) + (4 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * X 2 ^(2:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * X 1 + (3 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * X 1 ^(2:ℕ)
  + (-4 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * X 0 * X 2
  + (2 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * X 0 ^(2:ℕ)
  + (3 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C g * X 2
  + (3 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C g * X 1 * X 2
  + (1 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C g * X 0
  + (-4 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C g * X 0 * X 1
  + (2 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C g ^(2:ℕ) * X 2 ^(2:ℕ)

noncomputable def ASZMem1 (a b g : K) : MvPolynomial (Fin 3) K :=
  (1 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * X 2 + (4 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * X 1 * X 2
  + (3 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * X 0 * X 1
  + (6 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * C g
  + (3 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * C g * X 2 ^(2:ℕ)
  + (-2 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * C g * X 1 ^(2:ℕ)
  + (6 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * C g ^(2:ℕ) * X 1 * X 2
  + (1 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ) * X 2
  + (1 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ) * X 0 * X 1
  + (-2 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ) * C g
  + (2 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ) * C g * X 2 ^(2:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ) * C g * X 1 ^(2:ℕ)
  + (4 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ) * C g * X 0 * X 2
  + (3 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ) * C g ^(2:ℕ) * X 1 * X 2
  + (3 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(2:ℕ) * X 2
  + (4 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(2:ℕ) * X 1 * X 2
  + (1 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(2:ℕ) * X 0
  + (3 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(2:ℕ) * C g
  + (-4 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(2:ℕ) * C g * X 2 ^(2:ℕ)
  + (7 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(2:ℕ) * C g * X 1 ^(2:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(2:ℕ) * C g * X 0 * X 2
  + (3 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(2:ℕ) * C g ^(2:ℕ) * X 1 * X 2
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b * X 2
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b * X 1 * X 2
  + (1 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b * X 0
  + (1 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b * C g * X 1 ^(2:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * X 2
  + (4 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * X 1 * X 2
  + (4 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * X 0 + (3 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C g
  + (-3 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C g * X 2 ^(2:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C g * X 1 ^(2:ℕ)
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C g * X 0 * X 2
  + (3 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C g ^(2:ℕ) * X 1 * X 2

noncomputable def ASZMem2 (a b g : K) : MvPolynomial (Fin 3) K :=
  (-1 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * X 2 ^(2:ℕ) + (4 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * X 1
  + (4 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * X 0 ^(2:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * C g * X 2
  + (3 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * C g * X 1 * X 2
  + (1 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * C g * X 0
  + (1 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * C g * X 0 * X 1
  + (2 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * C g ^(2:ℕ) * X 2 ^(2:ℕ)
  + (3 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * C g ^(2:ℕ) * X 1 ^(2:ℕ)
  + (-2 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * C g ^(2:ℕ) * X 0 * X 2
  + (4 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ) * X 1
  + (-1 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ) * X 0 * X 2
  + (3 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ) * X 0 ^(2:ℕ)
  + (1 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ) * C g * X 1 * X 2
  + (3 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ) * C g * X 0
  + (4 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ) * C g ^(2:ℕ) * X 1 ^(2:ℕ)
  + (4 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ) * C g ^(2:ℕ) * X 0 * X 2
  + (1 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(2:ℕ)
  + (-2 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(2:ℕ) * X 2 ^(2:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(2:ℕ) * X 1
  + (1 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(2:ℕ) * X 1 ^(2:ℕ)
  + (9 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(2:ℕ) * X 0 * X 2
  + (1 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(2:ℕ) * C g * X 2
  + (1 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(2:ℕ) * C g * X 1 * X 2
  + (4 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(2:ℕ) * C g * X 0
  + (3 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(2:ℕ) * C g * X 0 * X 1
  + (4 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(2:ℕ) * C g ^(2:ℕ) * X 1 ^(2:ℕ)
  + (3 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(2:ℕ) * C g ^(2:ℕ) * X 0 * X 2
  + (2 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b
  + (4 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b * X 1
  + (3 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b * X 1 ^(2:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b * C g * X 2
  + (1 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b * C g * X 1 * X 2
  + (1 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b * C g * X 0
  + (-2 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b * C g * X 0 * X 1
  + (2 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * X 2 ^(2:ℕ) + (1 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * X 1
  + (3 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * X 0 * X 2
  + (1 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C g * X 2
  + (1 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C g * X 1 * X 2
  + (2 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C g * X 0
  + (1 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C g * X 0 * X 1
  + (4 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C g ^(2:ℕ) * X 1 ^(2:ℕ)
  + (3 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C g ^(2:ℕ) * X 0 * X 2

noncomputable def ASZMem3 (a b g : K) : MvPolynomial (Fin 3) K :=
  (2 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * X 2 + (4 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * X 0
  + (-1 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * C g * X 2 ^(2:ℕ)
  + (3 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * C g * X 1
  + (3 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * C g * X 1 ^(2:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * C g * X 0 * X 2
  + (4 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * C g ^(2:ℕ) * X 1 * X 2
  + (2 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ) * X 2
  + (4 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ) * X 1 * X 2
  + (4 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ) * X 0
  + (2 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ) * C g
  + (4 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ) * C g * X 2 ^(2:ℕ)
  + (4 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ) * C g * X 1
  + (4 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ) * C g * X 1 ^(2:ℕ)
  + (2 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ) * C g * X 0 * X 2
  + (2 : MvPolynomial (Fin 3) K) * C a * C b ^(3:ℕ) * C g ^(2:ℕ) * X 1 * X 2
  + (4 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(2:ℕ) * X 0
  + (2 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(2:ℕ) * C g
  + (3 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(2:ℕ) * C g ^(2:ℕ) * X 2
  + (-1 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b * X 2
  + (1 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b * X 1 * X 2
  + (1 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b * X 0
  + (3 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b * C g
  + (2 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * X 1 * X 2
  + (4 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * X 0
  + (3 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C g ^(2:ℕ) * X 2

noncomputable def ASZMem4 (a b g : K) : MvPolynomial (Fin 3) K :=
  (3 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) + (2 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * X 2 ^(2:ℕ)
  + (4 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * X 1
  + (4 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * X 0 * X 2
  + (6 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * C g ^(2:ℕ) * X 2 ^(2:ℕ)
  + (4 : MvPolynomial (Fin 3) K) * C b ^(4:ℕ) * C g ^(2:ℕ) * X 0 * X 2
end Certs

end Work.MotAS
