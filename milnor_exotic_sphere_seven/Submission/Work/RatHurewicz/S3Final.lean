import Mathlib
import Submission.Work.RatHurewicz.TruncationFromTrackInjective
import Submission.Work.RatHurewicz.trackRelPairMap_injective
import Submission.Work.RatHurewicz.S3Contracts

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The drive's contracts from the range-model acyclicity alone

Area **RATHUREWICZ**.  `Work.RatHurewicz.trackRelPairMap_injective` (proved) supplies the injectivity
of the stable-range Serre comparison for the mapping track; `S3Inj.truncationHomologyTransfer_of_track_injective`
turns it, together with the rational acyclicity of the range models, into the chapter's single
intermediate input.  Hence the drive's contracts now rest on **one** statement,

`Work.RatHurewicz.RangeModelRatAcyclic` — the rational homology of a range model of `K(A,k)` vanishes
in degrees `k < j ≤ 2k-1` (C2/C3 of `Submission/Work/Drive/SERRE_BLUEPRINT.md`), whose finitely
generated case is H5's and whose compactness reduction is H7's (`StemsB/rangeModelRatAcyclic_of_fgCase`).
-/

open scoped Topology

namespace Work.RatHurewicz

noncomputable section

/-- **The homology transfer of the truncation step, from the range-model acyclicity alone.** -/
theorem truncationHomologyTransfer_of_rangeModel (hem : RangeModelRatAcyclic) :
    TruncationHomologyTransfer :=
  S3Inj.truncationHomologyTransfer_of_track_injective
    (fun inc x₀ k n hk hmodel hconn hrange =>
      trackRelPairMap_injective inc x₀ k n hk hmodel hconn hrange) hem

/-- **The range form of the rational Hurewicz theorem**, from the range-model acyclicity alone. -/
theorem hurewiczModTorsionRange_of_rangeModel (hem : RangeModelRatAcyclic) :
    HurewiczModTorsionRange :=
  hurewiczModTorsionRange_of_transfer (truncationHomologyTransfer_of_rangeModel hem)

/-- **The drive's contract `Work.Drive.RationalHurewiczStable`**, from the range-model acyclicity
alone. -/
theorem rationalHurewiczStable_of_rangeModel (hem : RangeModelRatAcyclic) :
    Work.Drive.RationalHurewiczStable :=
  rationalHurewiczStable_of_transfer (truncationHomologyTransfer_of_rangeModel hem)

/-- **The one-degree-short contract `Work.Drive.RationalHurewiczStable3`** (area THOM), from the
range-model acyclicity alone. -/
theorem rationalHurewiczStable3_of_rangeModel (hem : RangeModelRatAcyclic) :
    Work.Drive.RationalHurewiczStable3 :=
  rationalHurewiczStable3_of_transfer (truncationHomologyTransfer_of_rangeModel hem)

/-- **The contract of area STEMS `Work.Drive.StableStemsTorsion`**, from the range-model acyclicity
alone. -/
theorem stableStemsTorsion_of_rangeModel (hem : RangeModelRatAcyclic) :
    Work.Drive.StableStemsTorsion :=
  stableStemsTorsion_of_rationalHurewiczStable3 (rationalHurewiczStable3_of_rangeModel hem)

end

end Work.RatHurewicz
