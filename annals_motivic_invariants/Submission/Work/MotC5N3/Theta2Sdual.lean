import Mathlib
import Submission.Work.MotC5N3.Ruling
import Submission.Work.MotC5N3.asY0_curve
import Submission.Work.MotC5N3.asPhi2_denom
import Submission.Work.MotC5N3.asTheta2_sdualAS2_aux

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.Theta2Sdual` — the target ruling quintic lies in the kernel of `asTheta2`

The unconditional form of `Work.MotC5N3.asTheta2_sdualAS2_aux`, obtained from the two non-degeneracy
inputs `asY0_curve` (the generic curve point satisfies the AS Pfaffians) and `asPhi2_denom`
(`W 0 ≠ 0`).  It depends only on the definitions (`Ruling`, `Defs`) and the two proved bricks, so it
builds independently of the chart-2 `rho` input.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotC5N3

variable {K : Type} [Field K] [CharP K 5]
variable {𝕜 : Type} [Field 𝕜] [Algebra 𝕜 K]

/-- **The target ruling quintic lies in the kernel of the chart presentation `asTheta2`.** -/
theorem asTheta2_sdualAS2 (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : K) :
    Work.MotC5N3.asTheta2 D g
      (Work.MotAS.sdualAS2 (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) g) = 0 :=
  asTheta2_sdualAS2_aux K D hD g (asY0_curve K D hD g) (asPhi2_denom K D hD g)

end Work.MotC5N3
