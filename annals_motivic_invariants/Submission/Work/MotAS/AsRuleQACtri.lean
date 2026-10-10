import Mathlib
import Submission.Work.MotAS.AsRuleQAAex
import Submission.Work.MotAS.AsRuleQABex
import Submission.Work.MotAS.AsCoeff6Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace Work.MotAS

open MvPolynomial Polynomial

variable {K : Type} [Field K] [CharP K 5]

noncomputable def asCt1 (a b g : K) : K :=
    - b ^ 4 - 2 * a * b ^ 3 + a ^ 2 * b ^ 2 + 2 * a ^ 3 * b - a ^ 4

noncomputable def asCt2 (a b g : K) : K :=
    - 2 * b ^ 4 - 2 * a * b ^ 3 - 2 * a ^ 3 * b + 2 * a ^ 4

noncomputable def asCt3 (a b g : K) : K :=
    b ^ 4 + a * b ^ 3 + a ^ 3 * b - a ^ 4

noncomputable def asCt4 (a b g : K) : K :=
    2 * b ^ 4 + a * b ^ 3 - a ^ 3 * b + 2 * a ^ 4

noncomputable def asCt5 (a b g : K) : K :=
    - b ^ 4 + 2 * a * b ^ 3 - 2 * a ^ 3 * b - a ^ 4

noncomputable def asCt6 (a b g : K) : K :=
    - b ^ 4 * g - 2 * a * b ^ 3 * g + a ^ 2 * b ^ 2 * g + 2 * a ^ 3 * b * g - a ^ 4 * g

noncomputable def asCt7 (a b g : K) : K :=
    b ^ 4 - a ^ 4

noncomputable def asCt8 (a b g : K) : K :=
    2 * b ^ 4 * g - a * b ^ 3 * g - 2 * a ^ 2 * b ^ 2 * g + a ^ 3 * b * g + 2 * a ^ 4 * g

noncomputable def asCt9 (a b g : K) : K :=
    2 * b ^ 4 * g - a * b ^ 3 * g - 2 * a ^ 2 * b ^ 2 * g + a ^ 3 * b * g + 2 * a ^ 4 * g

noncomputable def asCt10 (a b g : K) : K :=
    - a * b ^ 3 - a ^ 3 * b

noncomputable def asCt11 (a b g : K) : K :=
    - 2 * b ^ 4 * g - 2 * a * b ^ 3 * g - 2 * a ^ 3 * b * g + 2 * a ^ 4 * g

noncomputable def asCt12 (a b g : K) : K :=
    2 * a * b ^ 3 + 2 * a ^ 3 * b

noncomputable def asCt13 (a b g : K) : K :=
    b ^ 4 * g + a * b ^ 3 * g + a ^ 3 * b * g - a ^ 4 * g

noncomputable def asCt14 (a b g : K) : K :=
    - a * b ^ 3 + a ^ 3 * b

noncomputable def asCt15 (a b g : K) : K :=
    b ^ 4 * g - a * b ^ 3 * g + a ^ 2 * b ^ 2 * g + a ^ 3 * b * g + a ^ 4 * g

end Work.MotAS
