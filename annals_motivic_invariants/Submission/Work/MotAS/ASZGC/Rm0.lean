import Submission.Work.MotAS.ASZGC.Rm0_0
import Submission.Work.MotAS.ASZGC.Rm0_1
import Submission.Work.MotAS.ASZGC.Rm0_2
import Submission.Work.MotAS.ASZGC.Rm0_3
import Submission.Work.MotAS.ASZGC.Rm0_4
import Submission.Work.MotAS.ASZGC.Rm0_5
import Submission.Work.MotAS.ASZGC.Rm0_6
import Submission.Work.MotAS.ASZGC.Rm0_7
import Submission.Work.MotAS.ASZGC.Rm0_8
import Submission.Work.MotAS.ASZGC.Rm0_9
import Submission.Work.MotAS.ASZGC.Rm0_10
import Submission.Work.MotAS.ASZGC.Rm0_11
import Submission.Work.MotAS.ASZGC.Rm0_12
import Submission.Work.MotAS.ASZGC.Rm0_13
import Submission.Work.MotAS.ASZGC.Rm0_14
import Submission.Work.MotAS.ASZGC.Rm0_15
import Submission.Work.MotAS.ASZGC.Rm0_16
import Submission.Work.MotAS.ASZGC.Rm0_17
import Submission.Work.MotAS.ASZGC.Rm0_18
import Submission.Work.MotAS.ASZGC.Rm0_19
import Submission.Work.MotAS.ASZGC.Rm0_20
import Submission.Work.MotAS.ASZGC.Rm0_21
import Submission.Work.MotAS.ASZGC.Rm0_22
import Mathlib

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
open MvPolynomial
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Work.MotAS.ASZGC
variable {K : Type*} [Field K] [CharP K 5]
noncomputable def Rm0 (a b g : K) : MvPolynomial (Fin 2) K :=
  Rm0_0 a b g
  + Rm0_1 a b g
  + Rm0_2 a b g
  + Rm0_3 a b g
  + Rm0_4 a b g
  + Rm0_5 a b g
  + Rm0_6 a b g
  + Rm0_7 a b g
  + Rm0_8 a b g
  + Rm0_9 a b g
  + Rm0_10 a b g
  + Rm0_11 a b g
  + Rm0_12 a b g
  + Rm0_13 a b g
  + Rm0_14 a b g
  + Rm0_15 a b g
  + Rm0_16 a b g
  + Rm0_17 a b g
  + Rm0_18 a b g
  + Rm0_19 a b g
  + Rm0_20 a b g
  + Rm0_21 a b g
  + Rm0_22 a b g
end Work.MotAS.ASZGC
