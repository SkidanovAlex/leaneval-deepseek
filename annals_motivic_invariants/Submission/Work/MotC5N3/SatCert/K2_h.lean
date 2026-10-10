import Submission.Work.MotC5N3.SatCert.K2_defs
import Submission.Work.MotC5N3.SatCert.K2_z
import Submission.Work.Reflect.PolyId

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

lemma hB2 (a b g : K) :
    N2 a b g - X2AuxInputs.Pemb a b g * S2 a b g
      = (5 : MvPolynomial (Fin 3) K) * C2 a b g := by
  have h0 : (Fin.succ (0 : Fin 2) : Fin 3) = 1 := by decide
  have h1 : (Fin.succ (1 : Fin 2) : Fin 3) = 2 := by decide
  simp only [f20, f21, f22, S2, N2, C2_0, C2_1, C2_2, C2_3, C2_4, C2_5, C2, X2AuxInputs.D, X2AuxInputs.R, X2AuxInputs.Pemb, Work.MotAS.ASZElim.P,
    map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_zero, map_ofNat,
    MvPolynomial.C_add, MvPolynomial.C_mul, MvPolynomial.C_pow, MvPolynomial.C_neg,
    MvPolynomial.C_sub,
    MvPolynomial.rename_C, MvPolynomial.rename_X]
  rw [h0, h1]
  refl_ring1

end Work.MotC5N3
