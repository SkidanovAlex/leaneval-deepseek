import ChallengeDeps
import Submission.Helpers
import Submission.Work.BSFinal.Final
import Submission.OddOrder.FeitThompson

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open LeanEval.GroupTheory
open LeanEval.GroupTheory.Defs

namespace Submission

theorem bender_suzuki {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    (M : Subgroup X) (h : IsStronglyEmbedded M) :
    IsSimpleBenderGroup X :=
  bender_suzuki_final (fun G _ _ h => OddOrder.feitThompson h) M h

end Submission
