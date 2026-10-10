import Mathlib
import Submission.Work.MotC5N3.X2AuxInputs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace Work.MotC5N3
open MvPolynomial

variable {K : Type} [Field K] [CharP K 5]

noncomputable def f20 (a b g : K) : MvPolynomial (Fin 3) K :=
  C ((2)*a^(4:ℕ)*g^(1:ℕ))*X 1^(2:ℕ)*X 2
  + C ((2)*a^(4:ℕ)*g^(1:ℕ))*X 2^(3:ℕ)
  + C ((-2)*a^(4:ℕ))*X 1^(3:ℕ)
  + C ((2)*a^(4:ℕ))*X 1*X 2^(2:ℕ)
  + C ((2)*a^(4:ℕ))*X 1
  + C ((-1)*a^(4:ℕ))*X 2^(2:ℕ)
  + C ((1)*a^(3:ℕ)*b^(1:ℕ)*g^(1:ℕ))*X 1^(2:ℕ)*X 2
  + C ((-2)*a^(3:ℕ)*b^(1:ℕ)*g^(1:ℕ))*X 2^(3:ℕ)
  + C ((2)*a^(3:ℕ)*b^(1:ℕ))*X 1*X 2^(2:ℕ)
  + C ((1)*a^(3:ℕ)*b^(1:ℕ))*X 1
  + C ((-2)*a^(2:ℕ)*b^(2:ℕ)*g^(1:ℕ))*X 1^(2:ℕ)*X 2
  + C ((1)*a^(2:ℕ)*b^(2:ℕ))*X 1^(3:ℕ)
  + C ((-2)*a^(2:ℕ)*b^(2:ℕ))*X 1
  + C ((-2)*a^(2:ℕ)*b^(2:ℕ))*X 2^(2:ℕ)
  + C ((-1)*a^(1:ℕ)*b^(3:ℕ)*g^(1:ℕ))*X 1^(2:ℕ)*X 2
  + C ((-2)*a^(1:ℕ)*b^(3:ℕ)*g^(1:ℕ))*X 2^(3:ℕ)
  + C ((2)*a^(1:ℕ)*b^(3:ℕ))*X 1*X 2^(2:ℕ)
  + C ((-1)*a^(1:ℕ)*b^(3:ℕ))*X 1
  + C ((2)*b^(4:ℕ)*g^(1:ℕ))*X 1^(2:ℕ)*X 2
  + C ((-2)*b^(4:ℕ)*g^(1:ℕ))*X 2^(3:ℕ)
  + C ((-2)*b^(4:ℕ))*X 1^(3:ℕ)
  + C ((-2)*b^(4:ℕ))*X 1*X 2^(2:ℕ)
  + C ((2)*b^(4:ℕ))*X 1
  + C ((-1)*b^(4:ℕ))*X 2^(2:ℕ)

noncomputable def f21 (a b g : K) : MvPolynomial (Fin 3) K :=
  C ((2)*a^(4:ℕ)*g^(1:ℕ))*X 2^(2:ℕ)
  + C ((-1)*a^(4:ℕ))*X 1*X 2
  + C ((1)*a^(4:ℕ))*X 2
  + C ((1)*a^(3:ℕ)*b^(1:ℕ)*g^(1:ℕ))*X 2^(2:ℕ)
  + C ((2)*a^(3:ℕ)*b^(1:ℕ))*X 1*X 2
  + C ((-1)*a^(3:ℕ)*b^(1:ℕ))*X 2
  + C ((-2)*a^(2:ℕ)*b^(2:ℕ)*g^(1:ℕ))*X 2^(2:ℕ)
  + C ((1)*a^(2:ℕ)*b^(2:ℕ))*X 1*X 2
  + C ((-1)*a^(1:ℕ)*b^(3:ℕ)*g^(1:ℕ))*X 2^(2:ℕ)
  + C ((-2)*a^(1:ℕ)*b^(3:ℕ))*X 1*X 2
  + C ((-1)*a^(1:ℕ)*b^(3:ℕ))*X 2
  + C ((2)*b^(4:ℕ)*g^(1:ℕ))*X 2^(2:ℕ)
  + C ((-1)*b^(4:ℕ))*X 1*X 2
  + C ((-1)*b^(4:ℕ))*X 2

noncomputable def f22 (a b g : K) : MvPolynomial (Fin 3) K :=
  C ((2)*a^(4:ℕ))*X 1
  + C ((2)*a^(4:ℕ))
  + C ((-2)*a^(3:ℕ)*b^(1:ℕ))*X 1
  + C ((1)*a^(3:ℕ)*b^(1:ℕ))
  + C ((-2)*a^(2:ℕ)*b^(2:ℕ))
  + C ((-2)*a^(1:ℕ)*b^(3:ℕ))*X 1
  + C ((-1)*a^(1:ℕ)*b^(3:ℕ))
  + C ((-2)*b^(4:ℕ))*X 1
  + C ((2)*b^(4:ℕ))

noncomputable def S2 (a b g : K) : MvPolynomial (Fin 3) K :=
  C ((2)*a^(11:ℕ))*X 1^(2:ℕ)
  + C ((2)*a^(11:ℕ))*X 1
  + C ((1)*a^(10:ℕ)*b^(1:ℕ))*X 1^(2:ℕ)
  + C ((-1)*a^(10:ℕ)*b^(1:ℕ))*X 1
  + C ((-2)*a^(6:ℕ)*b^(5:ℕ))*X 1^(2:ℕ)
  + C ((-2)*a^(6:ℕ)*b^(5:ℕ))*X 1
  + C ((-1)*a^(5:ℕ)*b^(6:ℕ))*X 1^(2:ℕ)
  + C ((1)*a^(5:ℕ)*b^(6:ℕ))*X 1
  + C ((-2)*a^(1:ℕ)*b^(10:ℕ))*X 1^(2:ℕ)
  + C ((-2)*a^(1:ℕ)*b^(10:ℕ))*X 1
  + C ((-1)*b^(11:ℕ))*X 1^(2:ℕ)
  + C ((1)*b^(11:ℕ))*X 1

end Work.MotC5N3
