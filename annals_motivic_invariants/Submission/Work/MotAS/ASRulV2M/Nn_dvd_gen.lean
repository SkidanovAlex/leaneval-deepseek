import Mathlib
import Submission.Work.MotAS.ASZElimData
import Submission.Work.MotAS.ASZGC.Defs
import Submission.Work.MotAS.ASZGC.Lc0_ne_zero
import Submission.Work.MotAS.ASZGC.Qq0
import Submission.Work.MotAS.ASZGC.Rm0

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS.ASRulV2M

theorem Nn_dvd_gen (K : Type) [Field K] [CharP K 5] (a b g : K)
    (ha : a ^ 2 - a * b - b ^ 2 ≠ 0) (hg : ¬ ∃ c : K, c ^ 5 - c = g) :
    (Work.MotAS.ASZElim.P a b g ∣ Work.MotAS.ASZGC.Nn0 a b g) ∧
    (Work.MotAS.ASZElim.P a b g ∣ Work.MotAS.ASZGC.Nn1 a b g) ∧
    (Work.MotAS.ASZElim.P a b g ∣ Work.MotAS.ASZGC.Nn2 a b g) ∧
    (Work.MotAS.ASZElim.P a b g ∣ Work.MotAS.ASZGC.Nn3 a b g) ∧
    (Work.MotAS.ASZElim.P a b g ∣ Work.MotAS.ASZGC.Nn4 a b g) := by sorry

end Work.MotAS.ASRulV2M
