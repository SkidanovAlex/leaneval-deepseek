import Submission.Work.MotC5N3.RulingX2.ZiasGamNeTopInfra
import Submission.Work.MotC5N3.RulingX2.ZiasGamData1

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

variable {K : Type} [Field K] [CharP K 5]

noncomputable def q0 (a b g : K) : K := 2 * a^5 * g^3 + 4 * a^5 * g + a^4 * b + 3 * a^3 * b^2 + 4 * a^2 * b^3 + 2 * a * b^4 + 4 * b^5 * g^3 + 3 * b^5 * g + b^5

noncomputable def q1 (a b g : K) : K := 4 * a^5 * g^2 + 3 * a^5 * g + 4 * a^5 + 3 * a^4 * b * g + 4 * a^4 * b + 4 * a^3 * b^2 * g + 4 * a^3 * b^2 + 2 * a^2 * b^3 * g + 3 * a^2 * b^3 + a * b^4 * g + 2 * a * b^4 + 3 * b^5 * g^2 + 4 * b^5 * g + 3 * b^5

noncomputable def q2 (a b g : K) : K := 2 * a^5 + a^4 * b * g + a^4 * b + a^3 * b^2 * g + 2 * a^3 * b^2 + 2 * a^2 * b^3 * g + a^2 * b^3 + 3 * a * b^4 * g + 2 * a * b^4 + 4 * b^5

noncomputable def q3 (a b g : K) : K := 3 * a^5 * g + 4 * a^5 + 4 * a^4 * b + 3 * a^3 * b^2 + 3 * a^2 * b^3 + 3 * a * b^4 + b^5 * g + 2 * b^5

noncomputable def q5 (a b g : K) : K := a^5 * g^2 + 4 * a^3 * b^2 + 2 * a^2 * b^3 + 2 * b^5 * g^2
end Work.MotC5N3.RulingX2
