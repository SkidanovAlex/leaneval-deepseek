import Submission.Work.MotC5N3.SatCert.K0_f
import Submission.Work.MotC5N3.SatCert.K0_C0
import Submission.Work.MotC5N3.SatCert.K0_C1
import Submission.Work.MotC5N3.SatCert.K0_C2
import Submission.Work.MotC5N3.SatCert.K0_C3
import Submission.Work.MotC5N3.SatCert.K0_C4
import Submission.Work.MotC5N3.SatCert.K0_C5
import Submission.Work.MotC5N3.SatCert.K0_C6

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

noncomputable def C0 (a b g : K) : MvPolynomial (Fin 3) K :=
  C0_0 a b g + C0_1 a b g + C0_2 a b g + C0_3 a b g + C0_4 a b g + C0_5 a b g + C0_6 a b g

noncomputable def N0 (a b g : K) : MvPolynomial (Fin 3) K :=
  f00 a b g * (X2AuxInputs.D a b g) ^ 2
  + f01 a b g * (X2AuxInputs.D a b g) * (-(X2AuxInputs.R a b g))
  + f02 a b g * (-(X2AuxInputs.R a b g)) ^ 2

noncomputable def W0 (a b g : K) : MvPolynomial (Fin 3) K :=
  f01 a b g * (X2AuxInputs.D a b g)
  + f02 a b g * ((X2AuxInputs.D a b g) * X 0 + (-(X2AuxInputs.R a b g)))

end Work.MotC5N3
