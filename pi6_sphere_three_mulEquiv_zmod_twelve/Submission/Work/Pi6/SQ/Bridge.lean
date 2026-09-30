import Mathlib
import Submission.Work.Pi6.SQ.Defs
import Submission.Work.Pi6.SQ.cup1Coboundary
import Submission.Work.Pi6.SQ.cartanInstance
import Submission.Work.Pi6.SQ.sqOps
import Submission.Work.Pi6.SQM.Defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Area SQ: bridges to the lead's `SQM` contracts

The three cochain-level facts proved in area SQ — the mod-2 coboundary formula for `∪₁`
(`Work.Pi6.SQ.cup1Coboundary`), the Cartan instance `δH(x) = (x∪x)∪₂(x∪x) + (x∪₁x)∪(x∪₁x)`
(`Work.Pi6.SQ.cartanInstance`) and the well-definedness of the classes `[x∪₁x]`, `[x∪₂x]`
(`Work.Pi6.SQ.sqOps`) — restated as the lead's contracts `Work.Pi6.SQM.Cup1Cob`,
`Work.Pi6.SQM.CartanProp`, `Work.Pi6.SQM.SqOpsProp` (they differ only in the proof terms of the
degree casts, which are definitionally equal by proof irrelevance).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.Pi6.SQ

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff)

/-- **Bridge**: area SQ's mod-2 `∪₁` coboundary formula is `Work.Pi6.SQM.Cup1Cob`. -/
theorem cup1Cob : Work.Pi6.SQM.Cup1Cob := by
  intro X n m u v hn hm
  exact cup1Coboundary X n m u v hn hm

/-- **Bridge**: area SQ's Cartan instance is `Work.Pi6.SQM.CartanProp`. -/
theorem cartanProp : Work.Pi6.SQM.CartanProp := by
  intro X x hx
  exact cartanInstance X x hx

/-- **Bridge**: area SQ's `sqOps` (well-definedness of `[x∪₁x]`, `[x∪₂x]`) is
`Work.Pi6.SQM.SqOpsProp`. -/
theorem sqOpsProp : Work.Pi6.SQM.SqOpsProp := by
  exact sqOps

end

end Work.Pi6.SQ
