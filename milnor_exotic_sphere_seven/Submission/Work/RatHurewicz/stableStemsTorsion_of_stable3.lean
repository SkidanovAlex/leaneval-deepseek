import Mathlib
import Submission.Work.RatHurewicz.SerreHurewicz3
import Submission.Work.RatHurewicz.freudenthalTorsionTransfer
import Submission.Work.Stems.stableStemsTorsion_of_stable3
import Submission.Work.Drive.Interfaces

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The stable stems are torsion, from the one-short rational Hurewicz contract

Area **RATHUREWICZ**.  The drive's contract for the stable stems,
`Work.Drive.StableStemsTorsion` (the target of the area STEMS), follows from *either* form of this
area's rational Hurewicz contract:

* from the full contract `Work.Drive.RationalHurewiczStable` —
  `Work.RatHurewicz.stableStemsTorsion_of_rationalHurewiczStable'`
  (`SphereConnectivity.lean`), the direct rational-Hurewicz argument;
* from the **one-short** contract `Work.Drive.RationalHurewiczStable3`, the form that area THOM
  consumes — this module, using Freudenthal's suspension result to move the boundary case
  `n = i + 3` from `Sⁿ` to `S^{n+1}`:
  `Work.Stems.stableStemsTorsion_of_stable3` applies `RationalHurewiczStable3` at `Sⁿ` (for
  `i + 4 ≤ n`, where the range `n + i + 1 ≤ 2n - 3` holds) and reduces the boundary case
  `i + 3 = n` to it by suspending, using `Work.Stems.FreudenthalTorsionTransfer`, which is proved
  here as `Work.RatHurewicz.freudenthalTorsionTransfer` from homotopy excision.
-/

open scoped Topology

namespace Work.RatHurewicz

noncomputable section

/-- **The stable stems are torsion, from the one-short rational Hurewicz contract.**  The contract
`Work.Drive.RationalHurewiczStable3` (range `i + 1 ≤ 2k - 3`, the form area THOM consumes) implies
the STEMS contract `Work.Drive.StableStemsTorsion`, with no further hypothesis: the boundary case
`n = i + 3` of the stable range is moved to `S^{n+1}` by `freudenthalTorsionTransfer`
(Freudenthal's suspension result, proved in this directory from homotopy excision). -/
theorem stableStemsTorsion_of_rationalHurewiczStable3
    (h : Work.Drive.RationalHurewiczStable3) : Work.Drive.StableStemsTorsion :=
  Work.Stems.stableStemsTorsion_of_stable3 h freudenthalTorsionTransfer

end

end Work.RatHurewicz
