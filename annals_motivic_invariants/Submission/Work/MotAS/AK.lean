import Mathlib
import Submission.Work.MotAS.TwistField
import Submission.Work.MotAS.ChartDefs
import Submission.Work.MotV.Defs
import Submission.Work.MotV5.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.aK`, `Work.MotAS.bK` — the Klein parameters pushed to `K = RatFunc 𝕜`

These two definitions used to live in `Submission/Work/MotAS/linkCertAS.lean`.  They are moved here
so that the census modules (`CensusLinAS`, `CensusAS2`, …) can use them **without** importing
`linkCertAS.lean`; that import would create a cycle now that the target theorem `linkCertAS` is
proved from the census.
-/

set_option autoImplicit false

namespace Work.MotAS

variable {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5]

/-- The coefficient `a` of the Klein datum, pushed to `K = RatFunc 𝕜`. -/
noncomputable def aK (D : Work.MotV.KleinData 𝕜) : RatFunc 𝕜 :=
  algebraMap 𝕜 (RatFunc 𝕜) D.a

/-- The coefficient `b` of the Klein datum, pushed to `K = RatFunc 𝕜`. -/
noncomputable def bK (D : Work.MotV.KleinData 𝕜) : RatFunc 𝕜 :=
  algebraMap 𝕜 (RatFunc 𝕜) D.b

end Work.MotAS
