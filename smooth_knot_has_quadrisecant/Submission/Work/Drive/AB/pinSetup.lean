import Submission.Work.Drive.AB.needleShiftedPinDep
import Submission.Work.Drive.needleNumerator
import Submission.Work.Drive.needleAngVelAssembly

/-!
# The chart data of the needle's angular-velocity pin

This module fixes the *vocabulary* of the angular-velocity pin `Work.Drive.NeedleShiftedAngVelDep`
so that its proof can be split into (i) a *per-loop geometric margin* (the crux: the centre of the
chart lies inside every loop's lens) and (ii) an *oscillation bound* of the loop coordinates over
the blur window, assembled by `Work.Drive.needle_num_pos_of_diag_osc`.

The pin's chart is `(v, e)` with

* `v` the (unit) direction of the needle's chord `chordEndB - chordEndA` (a hypothesis of the pin),
* `e = Work.Drive.chartE` the unit "up" direction `‖chartUp‖⁻¹ • chartUp`,

and the centre is `Work.Drive.chartC = chordEndA + (nCoord 0) • v + (‖chartUp‖ / 2) • e`: the needle's
base point `shiftedNeedle 0` lowered by half its height `‖chartUp‖` above the chord's line.  With
these, the pin's expression is

    (nHeight … e t - ‖chartUp‖ / 2) * deriv (nCoord … v) t - (nCoord … v t - nCoord … v 0) *
      deriv (nHeight … e) t,

which is exactly the numerator of the *averaged* curve about `chartC` in the `(e, v)` orientation —
the object compared by `Work.Drive.needle_num_pos_of_diag_osc` with the weighted average of the
*individual* loops' numerators about the same point.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology intervalIntegral

/-- **The "up" direction of the needle's chart**: the unit vector along `chartUp`. -/
def chartE (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam δ₁ δ₂ ε : ℝ) (v : Space) :
    Space :=
  (‖chartUp r D lam δ₁ δ₂ ε v‖)⁻¹ • chartUp r D lam δ₁ δ₂ ε v

/-- **The centre of the needle's chart**: the needle's base point lowered by half its height above
the chord's line, i.e. `chordEndA + (nCoord 0) • v + (‖chartUp‖ / 2) • e`. -/
def chartC (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam δ₁ δ₂ ε : ℝ) (v : Space) :
    Space :=
  chordEndA r D δ₂ ε + (nCoord r D lam δ₁ δ₂ ε v 0) • v
    + (‖chartUp r D lam δ₁ δ₂ ε v‖ / 2) • chartE r D lam δ₁ δ₂ ε v

end Work.Drive
