import Submission.Work.MotC5N3.SatCert.K4_f
import Submission.Work.MotC5N3.SatCert.K4_C0
import Submission.Work.MotC5N3.SatCert.K4_C1
import Submission.Work.MotC5N3.SatCert.K4_C2
import Submission.Work.MotC5N3.SatCert.K4_C3
import Submission.Work.MotC5N3.SatCert.K4_C4

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

noncomputable def C4 (a b g : K) : MvPolynomial (Fin 3) K :=
  C4_0 a b g + C4_1 a b g + C4_2 a b g + C4_3 a b g + C4_4 a b g

noncomputable def N4 (a b g : K) : MvPolynomial (Fin 3) K :=
  f40 a b g * (X2AuxInputs.D a b g) ^ 2
  + f41 a b g * (X2AuxInputs.D a b g) * (-(X2AuxInputs.R a b g))
  + f42 a b g * (-(X2AuxInputs.R a b g)) ^ 2

noncomputable def W4 (a b g : K) : MvPolynomial (Fin 3) K :=
  f41 a b g * (X2AuxInputs.D a b g)
  + f42 a b g * ((X2AuxInputs.D a b g) * X 0 + (-(X2AuxInputs.R a b g)))

end Work.MotC5N3
