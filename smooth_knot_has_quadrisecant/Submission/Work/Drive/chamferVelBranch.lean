import Mathlib
import Submission.Work.Drive.sweepWideEndDefs
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.chordSweepDefs

/-!
# The four branches of `chamferVel`

`Work.Drive.chamferVel r D lam sig t` is defined by a four-fold case split on the profile
`u = sweepParam t`; this file names the four branch *expressions* as standalone functions of
`t`, so that statements about them (bounds, Lipschitz constants) can be made without any case
split.  The naming is purely bureaucratic: `chamferVel` is *by definition* the `if`-expression
selecting these four functions (see `chamferVel_eq_ite`).

* `chamferVelArc` — the arc side, `u ≤ 1/2`;
* `chamferVelChamfer₁` — the first chamfer, `1/2 < u ≤ 1/2 + lam/2`;
* `chamferVelChord` — the chord side, `1/2 + lam/2 < u ≤ 1 - lam/2`;
* `chamferVelChamfer₂` — the second chamfer, `u > 1 - lam/2`.

Only `chamferVelArc` depends on the loop parameter `t` non-trivially; the other three depend on
`sig` only.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- The arc-side branch of `chamferVel` (as a function of the loop parameter `t`). -/
def chamferVelArc (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam sig t : ℝ) : Space :=
  (((1 - 2 * lam) * (2 / period)) * sweepW' D sig) •
    velocity r (taR D sig + (lam + (1 - 2 * lam) * (2 * sweepParam t)) * sweepW' D sig)

/-- The first-chamfer branch of `chamferVel` (from the arc at fraction `1 - lam` to the chord at
fraction `1 - lam`). -/
def chamferVelChamfer₁ (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam sig _t : ℝ) :
    Space :=
  ((2 / lam) * (1 / period)) • (sweepChord' r D sig (1 - lam) - sweepArc' r D sig (1 - lam))

/-- The chord-side branch of `chamferVel`. -/
def chamferVelChord (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam sig _t : ℝ) :
    Space :=
  (-((1 - 2 * lam) / ((1 / 2 - lam) * period))) • (r (tbR D sig) - r (taR D sig))

/-- The second-chamfer branch of `chamferVel` (from the chord at fraction `lam` to the arc at
fraction `lam`). -/
def chamferVelChamfer₂ (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam sig _t : ℝ) :
    Space :=
  ((2 / lam) * (1 / period)) • (sweepArc' r D sig lam - sweepChord' r D sig lam)

/-- `chamferVel` is, by definition, the selection of the four branches above by the profile
`sweepParam t`. -/
lemma chamferVel_eq_ite (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam sig t : ℝ) :
    chamferVel r D lam sig t =
      (if sweepParam t ≤ 1 / 2 then chamferVelArc r D lam sig t
        else if sweepParam t ≤ 1 / 2 + lam / 2 then chamferVelChamfer₁ r D lam sig t
        else if sweepParam t ≤ 1 - lam / 2 then chamferVelChord r D lam sig t
        else chamferVelChamfer₂ r D lam sig t) := by
  simp only [chamferVel, chamferVelArc, chamferVelChamfer₁, chamferVelChord, chamferVelChamfer₂]

end Work.Drive
