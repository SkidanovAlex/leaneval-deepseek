/-
# `Submission/Work/GATE/` — the whole chapter

```lean
import Submission.Work.GATE.All
```

brings in the vocabulary (`Submission/Work/GATE/Defs.lean`), the segment lemma of §2.1
(`Submission/Work/GATE/Segment/`), the nest-angle lemma `A1` of §2.2
(`Submission/Work/GATE/Nest/`) and the assembly `Work.GATE.twoSided`
(`Submission/Work/GATE/TwoSided.lean`), which is *verbatim* the `twoSided` field of
`Work.Final.FinalInputs`.
-/
import Submission.Work.GATE.Defs
import Submission.Work.GATE.TwoSided
import Submission.Work.GATE.Integration
import Submission.Work.GATE.Segment.exists_segment_near
import Submission.Work.GATE.Segment.exists_two_lattice_hits
import Submission.Work.GATE.Segment.blowup_at_endpoint
import Submission.Work.GATE.Segment.crossing_two_tongues
import Submission.Work.GATE.Segment.seg_tongues
import Submission.Work.GATE.Segment.seg_tongues_parabolic
import Submission.Work.GATE.Nest.mem_paramRay_of_notMem_K
import Submission.Work.GATE.Nest.ray_angle_of_near_sides
import Submission.Work.GATE.Nest.nest_angle_window
import Submission.Work.GATE.Nest.exists_nest_level_window
import Submission.Work.GATE.Nest.nest_angle_z1
import Submission.Work.GATE.Nest.nest_angle_design
import Submission.Work.GATE.Gate.Defs
import Submission.Work.GATE.Gate.Transport
import Submission.Work.GATE.Gate.Residual
import Submission.Work.GATE.TwoSided_of_residual
import Submission.Work.GATE.Gate.branchData_alpha1_of_rootParabolic
import Submission.Work.GATE.Gate.base_at_root
import Submission.Work.GATE.Nest.deviation_eq_of_mem_paramRay
import Submission.Work.GATE.Nest.base_window
import Submission.Work.GATE.Bridge.transitData_of_PARIMPL
import Submission.Work.GATE.Bridge.transitData_fields_of_PARIMPL

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

