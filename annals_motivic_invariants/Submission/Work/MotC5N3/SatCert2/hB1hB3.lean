import Mathlib
import Submission.Work.MotC5N3.SatCert2.K1_defs
import Submission.Work.MotC5N3.SatCert2.K3_defs
import Submission.Work.MotC5N3.SatCert2.hB1hB3_c1_c
import Submission.Work.MotC5N3.SatCert2.hB1hB3_c3_c

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC5N3.SatCert2

theorem hB1hB3 (K : Type) [Field K] [CharP K 5] (a b g : K) :
    (Work.MotC5N3.N1 a b g - Work.MotC5N3.X2AuxInputs.Pemb a b g * Work.MotC5N3.S1 a b g
        = (5 : MvPolynomial (Fin 3) K) * Work.MotC5N3.C1 a b g)
    ∧ (Work.MotC5N3.N3 a b g - Work.MotC5N3.X2AuxInputs.Pemb a b g * Work.MotC5N3.S3 a b g
        = (5 : MvPolynomial (Fin 3) K) * Work.MotC5N3.C3 a b g) :=
  ⟨Work.MotC5N3.CertDemo.hB1 a b g, Work.MotC5N3.CertDemo.hB3 a b g⟩

end Work.MotC5N3.SatCert2
