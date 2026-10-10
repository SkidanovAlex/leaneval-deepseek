import Submission.Work.MotAS.ASZGC.Qq0_0
import Submission.Work.MotAS.ASZGC.Qq0_1
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
noncomputable def Qq0 (a b g : K) : MvPolynomial (Fin 2) K :=
  Qq0_0 a b g
  + Qq0_1 a b g
end Work.MotAS.ASZGC
