import Submission.Work.PTGeometric.LocalLevel
import Submission.Work.PTGeometric.localLevelPreimageTheorem

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the local preimage theorem, proved

`Work.PTGeometric.LocalPreimageTheorem` (`Defs.lean`, G4 of the blueprint) is the statement that the
transverse preimage of the core of a `LocalCoreTarget` — a target whose non-trivial normal bundle is
described by *local* defining functions, so that `CoreTarget`'s global `Φ` is unavailable — is a
compact smooth `9`-manifold with boundary, with boundary the end preimage of the core.

It follows from the local level-set form of the theorem, whose gluing step is proved in
`Submission/Work/PTGeometric/localLevelPreimageTheorem.lean` (and its auxiliary development
`Submission/Work/PTGeometric/Lvl/`):
`localLevelData_of_coreTransverse` extracts the local level-set data from chart-by-chart
transversality, and `localLevelPreimageTheorem` provides the manifold structure.
-/

namespace Work.PTGeometric

noncomputable section

/-- **The local preimage theorem (G4), proved.** -/
theorem localPreimageTheorem : LocalPreimageTheorem :=
  localPreimageTheorem_of_level localLevelPreimageTheorem

end

end Work.PTGeometric
