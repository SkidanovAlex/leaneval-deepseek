import Mathlib
import Submission.Work.PSTAB.Defs
import Submission.OddOrder.BG.Ch2_Uniqueness.S09_ChiefSeriesStabilizer

/-!
# PSTAB/StabilityLift — import prelude

Bundles the imports needed by the lemmas of the `StabilityLift` development:

* `Submission.Work.PSTAB.Defs` — the area vocabulary (`Work.PSTAB.*`, `Work.GW2.*`);
* `Submission.OddOrder.BG.Ch2_Uniqueness.S09_ChiefSeriesStabilizer` — the odd-order
  library's chief series machinery and, crucially,

  `OddOrder.BG.Ch2.S09.coprime_chiefSeries_stabilizer_le_centralizer`:
  a subgroup `D` of `M` of order coprime to the normal `p`-subgroup `K` that stabilizes
  every factor of the chief series of `K` inside `M` centralizes `K` (BG Lemma 1.9).
-/
