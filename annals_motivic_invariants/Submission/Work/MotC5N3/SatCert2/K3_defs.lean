import Submission.Work.MotC5N3.SatCert2.K3_f
import Submission.Work.MotC5N3.SatCert2.K3_C0
import Submission.Work.MotC5N3.SatCert2.K3_C1
import Submission.Work.MotC5N3.SatCert2.K3_C2
import Submission.Work.MotC5N3.SatCert2.K3_C3

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

noncomputable def C3 (a b g : K) : MvPolynomial (Fin 3) K :=
  C3_0 a b g + C3_1 a b g + C3_2 a b g + C3_3 a b g

noncomputable def N3 (a b g : K) : MvPolynomial (Fin 3) K :=
  f30 a b g * (X2AuxInputs.D a b g) ^ 3
  + f31 a b g * (X2AuxInputs.D a b g) ^ 2 * (-(X2AuxInputs.R a b g))
  + f32 a b g * (X2AuxInputs.D a b g) * (-(X2AuxInputs.R a b g)) ^ 2
  + f33 a b g * (-(X2AuxInputs.R a b g)) ^ 3

noncomputable def W3 (a b g : K) : MvPolynomial (Fin 3) K :=
  f31 a b g * (X2AuxInputs.D a b g) ^ 2
  + f32 a b g * (X2AuxInputs.D a b g) * ((X2AuxInputs.D a b g) * X 0 + (-(X2AuxInputs.R a b g)))
  + f33 a b g * (((X2AuxInputs.D a b g) * X 0) ^ 2 + ((X2AuxInputs.D a b g) * X 0) * (-(X2AuxInputs.R a b g)) + (-(X2AuxInputs.R a b g)) ^ 2)

end Work.MotC5N3
