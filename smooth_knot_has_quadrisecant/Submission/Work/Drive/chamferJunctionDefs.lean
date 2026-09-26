import Mathlib
import Submission.Work.Drive.chamferLoopGenDefs
import Submission.Work.Drive.chamferSchedule

/-!
# The junction condition of the scheduled chamfer loop (lead's `NOTES_LEAD_scheduledBlur.md` §1)

`Work.Drive.ChamferJunctionOK r D α β σ` collects the *non-degeneracy of the four junctions* of the
scheduled loop `chamferLoopGen r D lay α β` at the slice `σ`: the two cut points and the two chord
points are distinct, and at each of the four junctions the outgoing secant direction is not the
reverse of the incoming one (with a *positive* factor).  Its only role is to make the *secant cone*
of the loop well behaved: at a junction, the sum of the two one-sided secant bounds with a common
direction `n` is positive exactly when no reversal occurs.

The four reversals are: `J1` (arc → head connector), `J2` (head connector → chord), `J3` (chord →
tail connector), `J4` (tail connector → arc); the loop parameter runs
`u = 0 → 1/2 → 1/2 + lay/2 → 1 - lay/2 → 1`, i.e. the *tail* connector is at the wrap `u = 0`.
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **The junction non-degeneracy of the scheduled loop at the slice `σ`.** -/
def ChamferJunctionOK (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (α β : ℝ → ℝ)
    (σ : ℝ) : Prop :=
  r (taR D σ) ≠ r (tbR D σ) ∧ 0 < sweepW' D σ ∧ 0 < α σ ∧ 2 * α σ < 1 ∧ 0 < β σ ∧ 2 * β σ < 1 ∧
  sweepArc' r D σ (α σ) ≠ sweepChord' r D σ (β σ) ∧
  sweepArc' r D σ (1 - α σ) ≠ sweepChord' r D σ (1 - β σ) ∧
  (∀ k : ℝ, 0 < k → sweepChord' r D σ (1 - β σ) - sweepArc' r D σ (1 - α σ)
      ≠ (-k) • velocity r (taR D σ + (1 - α σ) * sweepW' D σ)) ∧
  (∀ k : ℝ, 0 < k → sweepChord' r D σ (1 - β σ) - sweepArc' r D σ (1 - α σ)
      ≠ k • (r (tbR D σ) - r (taR D σ))) ∧
  (∀ k : ℝ, 0 < k → sweepArc' r D σ (α σ) - sweepChord' r D σ (β σ)
      ≠ k • (r (tbR D σ) - r (taR D σ))) ∧
  (∀ k : ℝ, 0 < k → sweepArc' r D σ (α σ) - sweepChord' r D σ (β σ)
      ≠ (-k) • velocity r (taR D σ + α σ * sweepW' D σ))

end Work.Drive
