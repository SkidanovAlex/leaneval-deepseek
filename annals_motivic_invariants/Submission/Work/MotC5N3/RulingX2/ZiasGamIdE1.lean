import Submission.Work.MotC5N3.RulingX2.ZiasGamNeTopInfra
import Submission.Work.MotC5N3.RulingX2.ZiasGamData1
import Submission.Work.MotC5N3.RulingX2.ZiasGamData2
import Submission.Work.MotC5N3.RulingX2.ZiasGamData2b
import Submission.Work.MotC5N3.RulingX2.ZiasGamData3
import Submission.Work.MotC5N3.RulingX2.ZiasGamData4
import Submission.Work.Reflect.PolyId

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace Work.MotC5N3.RulingX2

open MvPolynomial

variable {K : Type} [Field K] [CharP K 5]

theorem E1_eq (a b g : K) :
    C ((2 : K) * (a - 3 * b) ^ 5) * Slice.Rhat a b g ^ 2 = E1v a b g := by
  rw [denden]
  dsimp only [E1v_0, E1v_1, E1v_2, E1v_3, E1v_4, E1v_5, E1v_6, E1v_7, E1v_8, E1v_9, E1v_10, E1v, Slice.Rhat]
  simp only [map_add, map_mul, map_pow, map_sub, map_one, map_zero, map_ofNat]
  refl_ring1 (mod := 5)

end Work.MotC5N3.RulingX2
