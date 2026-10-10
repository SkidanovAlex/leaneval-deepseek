import Submission.Work.MotC5N3.SatCert.K2_f
import Submission.Work.MotC5N3.SatCert.K2_C0
import Submission.Work.MotC5N3.SatCert.K2_C1
import Submission.Work.MotC5N3.SatCert.K2_C2
import Submission.Work.MotC5N3.SatCert.K2_C3
import Submission.Work.MotC5N3.SatCert.K2_C4
import Submission.Work.MotC5N3.SatCert.K2_C5

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

noncomputable def C2 (a b g : K) : MvPolynomial (Fin 3) K :=
  C2_0 a b g + C2_1 a b g + C2_2 a b g + C2_3 a b g + C2_4 a b g + C2_5 a b g

noncomputable def N2 (a b g : K) : MvPolynomial (Fin 3) K :=
  f20 a b g * (X2AuxInputs.D a b g) ^ 2
  + f21 a b g * (X2AuxInputs.D a b g) * (-(X2AuxInputs.R a b g))
  + f22 a b g * (-(X2AuxInputs.R a b g)) ^ 2

noncomputable def W2 (a b g : K) : MvPolynomial (Fin 3) K :=
  f21 a b g * (X2AuxInputs.D a b g)
  + f22 a b g * ((X2AuxInputs.D a b g) * X 0 + (-(X2AuxInputs.R a b g)))

end Work.MotC5N3
