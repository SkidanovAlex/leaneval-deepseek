import Mathlib
import Submission.Work.Pi6.SQ.Defs
import Submission.Work.Pi6.SQ.C2.cup2Coboundary
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Area SQ: the `∪₂` coboundary formula, re-exported from `SQM`

The lead's restructuring moves the proof of the mod-2 coboundary formula for `∪₂` to
`Work.Pi6.SQ.C2.cup2CoboundaryM`; this file re-exports it in the exact shape area SQ's `sqOps`
uses (`Work.Pi6.SQ.cup2Coboundary`), the two statements differing only in the proof terms of the
degree casts.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.Pi6.SQ

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff)

/-- Mod-2 coboundary formula for the cup-2 product (Steenrod's interval convention, as in `REFS/pi6_cupi_check.py`): for cochains `u`, `v` of degrees `n`, `m`, `δ(u ∪₂ v) = u ∪₁ v + v ∪₁ u + δu ∪₂ v + u ∪₂ δv`, where `∪₁ = Work.Pi6.SQ.cup1m` and `∪₂ = Work.Pi6.SQ.cup2` are the workspace's mod-2 products. -/
theorem cup2Coboundary (X : SSet) (n m : ℕ) (u : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X n) (v : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X m) (hn : 1 ≤ n) (hm : 1 ≤ m) : (by omega : (n + m - 2) + 1 = n + m - 1) ▸ (Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X (Work.Pi6.SQ.cup2 X n m u v)) = Work.Pi6.SQ.cup1m X n m u v + (by omega : m + n - 1 = n + m - 1) ▸ Work.Pi6.SQ.cup1m X m n v u + (by omega : (n + 1) + m - 2 = n + m - 1) ▸ Work.Pi6.SQ.cup2 X (n + 1) m (Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X u) v + (by omega : n + (m + 1) - 2 = n + m - 1) ▸ Work.Pi6.SQ.cup2 X n (m + 1) u (Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X v) :=
  Work.Pi6.SQ.C2.cup2CoboundaryM X n m u v hn hm

end

end Work.Pi6.SQ
