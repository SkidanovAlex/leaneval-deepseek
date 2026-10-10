import Submission.Work.MotC5N3.SatCert2.K1_f
import Submission.Work.MotC5N3.SatCert2.K1_C0
import Submission.Work.MotC5N3.SatCert2.K1_C1
import Submission.Work.MotC5N3.SatCert2.K1_C2
import Submission.Work.MotC5N3.SatCert2.K1_C3

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

noncomputable def C1 (a b g : K) : MvPolynomial (Fin 3) K :=
  C1_0 a b g + C1_1 a b g + C1_2 a b g + C1_3 a b g

noncomputable def N1 (a b g : K) : MvPolynomial (Fin 3) K :=
  f10 a b g * (X2AuxInputs.D a b g) ^ 3
  + f11 a b g * (X2AuxInputs.D a b g) ^ 2 * (-(X2AuxInputs.R a b g))
  + f12 a b g * (X2AuxInputs.D a b g) * (-(X2AuxInputs.R a b g)) ^ 2
  + f13 a b g * (-(X2AuxInputs.R a b g)) ^ 3

noncomputable def W1 (a b g : K) : MvPolynomial (Fin 3) K :=
  f11 a b g * (X2AuxInputs.D a b g) ^ 2
  + f12 a b g * (X2AuxInputs.D a b g) * ((X2AuxInputs.D a b g) * X 0 + (-(X2AuxInputs.R a b g)))
  + f13 a b g * (((X2AuxInputs.D a b g) * X 0) ^ 2 + ((X2AuxInputs.D a b g) * X 0) * (-(X2AuxInputs.R a b g)) + (-(X2AuxInputs.R a b g)) ^ 2)

end Work.MotC5N3
