import Mathlib
import Submission.Work.SSGRoute.C6Detector.detector_algClosedExt
import Submission.Work.SSGRoute.C6Detector.rankOneBrick_of_datum_and_transport
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A lean copy of the ambient-detector glue

`Work.SSGRoute.C6Detector.C6Glue` bundles the (proved, axiom-clean) ambient independence of the
unramified detector together with the *other* leaf of the `C6` chain, the canonical-ambient level
datum `Work.SSGRoute.C6Detector.rankOneLevelDatumAlgClosure`.  The assembly
`Work.SSGRoute.SSGate.assembly` obtains the level datum from the concentrated level data instead
(`Work.SSGate.concentratedLevelDataGate`), so it only needs the detector half.

This file records that half in the `Work.SSGRoute.SSGate` namespace so that the assembly — and
through it `Work.SSGRoute.stage_global_lifting` — does not have to import the volatile
level-datum leaf.
-/

namespace Work.SSGRoute.SSGate

/-- **The ambient independence of the unramified detector**, re-exported from the (proved)
declaration `Work.SSGRoute.C6Detector.detector_algClosedExt`. -/
theorem detectorAlgClosedExt_holds' (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [NumberField k] :
    Work.SSGRoute.C6Detector.DetectorAlgClosedExt p k := by
  intro K _ _ _ _ _ Ω₀ Ω _ _ _ _ _ _ _ _ _ _ φ hφ hφK w q hwq M h
  exact Work.SSGRoute.C6Detector.detector_algClosedExt p k K Ω₀ Ω φ hφ hφK w q hwq M h

end Work.SSGRoute.SSGate
