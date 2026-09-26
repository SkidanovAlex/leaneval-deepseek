import Mathlib
import Submission.Work.Drive.ofatEndgameSOfTopEnd
import Submission.Work.Drive.ofatTopEnd_of_wideEnd
import Submission.Work.Drive.wideEndSigmaFirstUniform

/-!
# The single pin of the `OFat` endgame: the top end

`Work.Drive.ofatEndgameS_of_topEnd` (`Drive/ofatEndgameSOfTopEnd.lean`) proves the pin
`Work.Drive.OFatCrosscutEndgameS` from exactly one input, the **top end** `Work.Drive.NeedleTopEnd`
at a needle slice in the bottom trough of the schedule.  This module names that input as the single
`Prop` pin of the lane:

    Work.Drive.OFatTopEndAll

and records it as a `sorry` (the pin).  Its producer is the theorem
`Work.Drive.needleTopEnd_of_schedSlot` (`Drive/needleTopEnd_of_schedSlot.lean`, another lane, in
flight); when it lands, replace this pin by it, i.e.

    theorem ofatEndgameS_all : ∀ r, OFatCrosscutEndgameS r :=
      ofatEndgameS_of_topEnd needleTopEnd_of_schedSlot

Everything else of the endgame is *proved* in this lane: the crosscut ⟹ band arc + `SweepData` +
middle-freeness + non-tangency (`Drive/sweepData_of_stripCrosscutOFatS.lean`), the scheduling slot
from the crosscut data plus the ball-uniform tools (`Drive/ofatSchedSlotOfCrosscut.lean`, using the
repaired injectivity lemma `Work.Drive.chamferLoopGenInjOnScheduledC4`), the needle end
(`Drive/ofatNeedleEnd.lean`) and the glue (`Drive/ofatNeedleTroughGlue.lean`).
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **The top end for every knot, every `SweepData` and every trough slice** — the single pin of the
`OFat` endgame (the shape of `Work.Drive.ofatEndgameS_of_topEnd`'s `htop` argument). -/
def OFatTopEndAll : Prop :=
  ∀ (r : ℝ → Space) (hr : IsSmoothKnot r) {d : BandArcData} (D : SweepData d) {δs ε : ℝ},
    0 < δs → 0 < ε → ε < 1 / 2 →
    (∀ σ ∈ Set.Icc (ε / 2) (3 * ε / 2), 4 * schedC D σ ≤ δs) →
    (∀ Lmax : ℝ, 0 < Lmax → ∀ ε' σ₀ : ℝ, 0 < ε' → ε' < σ₀ → σ₀ < 1 →
      SchedSlot r D δs Lmax ε' σ₀) →
    NeedleTopEnd r D ε

/-- **The top end for every knot, `SweepData` and trough slice** — *proved*, from the transcriptions
`Work.Drive.ofatTopEnd_of_wideEnd` (the top end from the wide-end estimate) and
`Work.Drive.wideEndSigmaFirstUniform` (that estimate).  The pin it replaces has been discharged; the
alternative producer `Work.Drive.needleTopEnd_of_schedSlot`
(`Drive/needleTopEnd_of_schedSlot.lean`, another lane) proves the same statement directly. -/
theorem ofatTopEndAll : OFatTopEndAll := by
  intro r hr d D δs ε hδs hε0 hε1 htrough hslot
  exact ofatTopEnd_of_wideEnd (r := r) (d := d) hr D hδs hε0 hε1
    (wideEndSigmaFirstUniform (r := r) (d := d) hr D hδs) htrough hslot

end Work.Drive
