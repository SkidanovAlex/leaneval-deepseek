import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Decidable equality on the edge type

`Work.BMF.Edge` (from `Defs.lean`) carries no `DecidableEq` instance, because the shared
definition file is fixed.  The counting argument of `adi_cycles` forms *images* of sets of
bicycles under `t ↦ t.1`, which needs `DecidableEq Edge`; this module provides it under a
distinctive name (so that it cannot clash with an anonymous `instDecidableEqEdge` declared
elsewhere).
-/

namespace Work.BMF

/-- Classical decidable equality on the edges of the quadruple graph. -/
noncomputable instance bmfEdgeDecidableEq : DecidableEq Edge := Classical.decEq _

end Work.BMF
