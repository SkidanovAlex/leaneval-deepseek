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

theorem E3_eq (a b g : K) :
    B0mv a b g * Slice.Dhat a b g ^ 2 = E3v a b g := by
  dsimp only [E3v_0, E3v_1, E3v_2, E3v_3, E3v_4, E3v_5, E3v_6, E3v_7, E3v_8, E3v_9, E3v_10, E3v_11, E3v, B0mv_0, B0mv_1, B0mv, Slice.Dhat]
  simp only [map_add, map_mul, map_pow, map_sub, map_one, map_zero, map_ofNat]
  refl_ring1 (mod := 5)

end Work.MotC5N3.RulingX2
