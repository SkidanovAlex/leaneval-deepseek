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

theorem E2_eq (a b g : K) :
    A0mv a b g * Slice.Rhat a b g * Slice.Dhat a b g = E2v a b g := by
  dsimp only [E2v_0, E2v_1, E2v_2, E2v_3, E2v_4, E2v_5, E2v_6, E2v_7, E2v_8, E2v_9, E2v_10, E2v, A0mv_0, A0mv, Slice.Rhat, Slice.Dhat]
  simp only [map_add, map_mul, map_pow, map_sub, map_one, map_zero, map_ofNat]
  refl_ring1 (mod := 5)

end Work.MotC5N3.RulingX2
