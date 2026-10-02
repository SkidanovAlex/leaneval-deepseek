import Mathlib
import Submission.Work.RatHurewicz.S3Assembly
import Submission.Work.RatHurewicz.towerStepData
import Submission.Work.RatHurewicz.SerreHurewicz3
import Submission.Work.RatHurewicz.stableStemsTorsion_of_stable3

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The rational Hurewicz theorem from the single homology-transfer input

Area **RATHUREWICZ**.  `S3Assembly.lean` proves the stem induction and reduces the drive's contract
to the two inputs `Work.RatHurewicz.TruncationHomologyTransfer` and
`Work.RatHurewicz.TowerStepData`; `towerStepData.lean` discharges the second.  This module wires the
result: **the contract follows from `Work.RatHurewicz.TruncationHomologyTransfer` alone.**

* `Work.RatHurewicz.hurewiczModTorsionRange_of_transfer` — the range form
  `Work.RatHurewicz.HurewiczModTorsionRange` (the full stable range `n+1 ≤ 2k-2`);
* `Work.RatHurewicz.rationalHurewiczStable_of_transfer` — the drive's contract
  `Work.Drive.RationalHurewiczStable` (area THOM and area STEMS);
* `Work.RatHurewicz.rationalHurewiczStable3_of_transfer` — the one-degree-short contract
  `Work.Drive.RationalHurewiczStable3`;
* `Work.RatHurewicz.stableStemsTorsion_of_transfer` — the contract of area STEMS,
  `Work.Drive.StableStemsTorsion`.

The single remaining input is the homology transfer of the truncation step: for a map `inc : X → Z`
whose homotopy fibre `F` is `k`-connected and whose target `Z` is a range model of `K(π_kX,k)` up to
degree `2k-1`, the fibre inclusion induces on `H_{n+1}` (for `k < n+1 ≤ 2k-2`) a map with torsion
kernel.  Its mathematical content is Serre's exact sequence in the stable range together with the
computation of the rational homology of an Eilenberg–MacLane space below `2k` — C2/C3 and
E3(a)/E3(b) of `Submission/Work/Drive/SERRE_BLUEPRINT.md`, the chapter of area SERRE.  See the
module docstring of `S3Inputs.lean` for the precise derivation.
-/

open scoped Topology

namespace Work.RatHurewicz

noncomputable section

/-- **The range form of the rational Hurewicz theorem from the homology-transfer input.** -/
theorem hurewiczModTorsionRange_of_transfer (h : TruncationHomologyTransfer) :
    HurewiczModTorsionRange :=
  hurewiczModTorsionRange_of_inputs h towerStepData

/-- **The drive's contract `Work.Drive.RationalHurewiczStable` from the homology-transfer
input.** -/
theorem rationalHurewiczStable_of_transfer (h : TruncationHomologyTransfer) :
    Work.Drive.RationalHurewiczStable :=
  rationalHurewiczStable_of_inputs h towerStepData

/-- **The one-degree-short contract `Work.Drive.RationalHurewiczStable3`** (the form consumed by
area THOM) from the homology-transfer input. -/
theorem rationalHurewiczStable3_of_transfer (h : TruncationHomologyTransfer) :
    Work.Drive.RationalHurewiczStable3 :=
  rationalHurewiczStable3_of_inputs h towerStepData

/-- **The contract of area STEMS `Work.Drive.StableStemsTorsion`** from the homology-transfer
input. -/
theorem stableStemsTorsion_of_transfer (h : TruncationHomologyTransfer) :
    Work.Drive.StableStemsTorsion :=
  stableStemsTorsion_of_rationalHurewiczStable3 (rationalHurewiczStable3_of_transfer h)

end

end Work.RatHurewicz
