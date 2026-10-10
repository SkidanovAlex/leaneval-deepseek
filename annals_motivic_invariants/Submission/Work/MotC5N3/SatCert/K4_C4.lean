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

noncomputable def C4_4 (a b g : K) : MvPolynomial (Fin 3) K :=
  C ((-11)*a^1*b^15)*X 1^2*X 2^2
  + C ((-2)*a^1*b^15)*X 1*X 2^2
  + C ((3)*a^1*b^15)*X 2^2
  + C ((-3)*b^16*g^2)*X 1^5*X 2^2
  + C ((-1)*b^16*g^2)*X 1^4*X 2^2
  + C ((8)*b^16*g^2)*X 1^3*X 2^4
  + C ((6)*b^16*g^2)*X 1^2*X 2^4
  + C ((2)*b^16*g^2)*X 1*X 2^4
  + C ((-2)*b^16*g^1)*X 1^5*X 2
  + C ((-1)*b^16*g^1)*X 1^4*X 2
  + C ((12)*b^16*g^1)*X 1^3*X 2^3
  + C ((-2)*b^16*g^1)*X 1^3*X 2
  + C ((5)*b^16*g^1)*X 1^2*X 2^3
  + C ((1)*b^16*g^1)*X 1*X 2^3
  + C ((-1)*b^16)*X 1^4
  + C ((5)*b^16)*X 1^3*X 2^2
  + C ((2)*b^16)*X 1^2
  + C ((1)*b^16)*X 1*X 2^2
  + C ((2)*b^16)*X 2^2

end Work.MotC5N3
