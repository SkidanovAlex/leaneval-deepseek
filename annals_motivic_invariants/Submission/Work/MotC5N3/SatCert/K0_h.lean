import Submission.Work.MotC5N3.SatCert.K0_defs
import Submission.Work.MotC5N3.SatCert.K0_z
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

lemma hB0 (a b g : K) :
    N0 a b g - X2AuxInputs.Pemb a b g * S0 a b g
      = (5 : MvPolynomial (Fin 3) K) * C0 a b g := by
  have h0 : (Fin.succ (0 : Fin 2) : Fin 3) = 1 := by decide
  have h1 : (Fin.succ (1 : Fin 2) : Fin 3) = 2 := by decide
  simp only [f00, f01, f02, S0, N0, C0_0, C0_1, C0_2, C0_3, C0_4, C0_5, C0_6, C0, X2AuxInputs.D, X2AuxInputs.R, X2AuxInputs.Pemb, Work.MotAS.ASZElim.P,
    map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_zero, map_ofNat,
    MvPolynomial.C_add, MvPolynomial.C_mul, MvPolynomial.C_pow, MvPolynomial.C_neg,
    MvPolynomial.C_sub,
    MvPolynomial.rename_C, MvPolynomial.rename_X]
  rw [h0, h1]
  refl_ring1

end Work.MotC5N3
