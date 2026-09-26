import Mathlib
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.chordSweepDefs

/-!
# Vocabulary for the wide-end estimate of the chord sweep

This file fixes the vocabulary used by `Work.Drive.sweepFam_wideEnd_estimate`: the (a.e.)
velocity of the chamfered loop, the corner set of the loop parameter, the arc-side knot
parameter, the unit tangent of the knot and its arclength function.  The analytic facts are
stated (and proved) in the sibling modules.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-! ## The velocity of the chamfered loop -/

/-- **The velocity of the chamfered loop.**  For the loop parameter `t` with fraction
`u = sweepParam t`: on the arc branch (`u ≤ 1/2`) it is the tangent of the arc point times
the rate `((1 - 2 lam) * 2 / period) * w` at which the arc parameter advances; on the
chamfer branch `u ∈ (1/2, 1/2 + lam/2]` it is the constant chord velocity
`(2 / (lam * period)) • (B - A)`; on the chord branch it is the constant velocity
`-((1-2lam)/((1/2-lam) * period)) • (r (b) - r (a))`; and on the last chamfer it is
`(2 / (lam * period)) • (D - C)`.  This is the (a.e.) `t`-derivative of
`Work.Drive.sweepLoopChamfer r D lam sig ·`. -/
def chamferVel (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam : ℝ)
    (sig t : ℝ) : Space :=
  let u := sweepParam t
  if u ≤ 1 / 2 then
    (((1 - 2 * lam) * (2 / period)) * sweepW' D sig) •
      velocity r (taR D sig + (lam + (1 - 2 * lam) * (2 * u)) * sweepW' D sig)
  else if u ≤ 1 / 2 + lam / 2 then
    ((2 / lam) * (1 / period)) •
      (sweepChord' r D sig (1 - lam) - sweepArc' r D sig (1 - lam))
  else if u ≤ 1 - lam / 2 then
    (-((1 - 2 * lam) / ((1 / 2 - lam) * period))) • (r (tbR D sig) - r (taR D sig))
  else
    ((2 / lam) * (1 / period)) • (sweepArc' r D sig lam - sweepChord' r D sig lam)

/-- The loop parameter is a "corner" of the chamfered loop when the branch formula changes,
i.e. when its fraction `sweepParam t` is one of `0`, `1/2`, `1/2 + lam/2`, `1 - lam/2`. -/
def chamferCorner (lam t : ℝ) : Prop :=
  sweepParam t = 0 ∨ sweepParam t = 1 / 2 ∨ sweepParam t = 1 / 2 + lam / 2 ∨
    sweepParam t = 1 - lam / 2

/-- The knot parameter of the point of the retained arc of fraction `xi` at sweep parameter
`sig`. -/
def arcPar {d : BandArcData} (D : SweepData d) (sig xi : ℝ) : ℝ :=
  taR D sig + xi * sweepW' D sig

/-- The arc parameter of the loop at fraction `u = sweepParam t` on the arc branch. -/
def arcParOfLoop {d : BandArcData} (D : SweepData d) (lam sig t : ℝ) : ℝ :=
  arcPar D sig (lam + (1 - 2 * lam) * (2 * sweepParam t))

@[simp] lemma arcPar_zero {d : BandArcData} (D : SweepData d) (sig : ℝ) :
    arcPar D sig 0 = taR D sig := by simp [arcPar]

@[simp] lemma arcPar_one {d : BandArcData} (D : SweepData d) (sig : ℝ) :
    arcPar D sig 1 = tbR D sig := by simp [arcPar, sweepW']

lemma arcParOfLoop_zero {d : BandArcData} (D : SweepData d) (lam sig : ℝ) :
    arcParOfLoop D lam sig 0 = arcPar D sig lam := by
  simp [arcParOfLoop, sweepParam, Int.floor_zero, zero_div, sub_zero]

/-! ## The unit tangent and the arclength of a curve -/

/-- The unit tangent of a curve at a parameter; the junk value `0` where the velocity
vanishes (which never happens for a smooth knot). -/
def unitTangent (r : ℝ → Space) (x : ℝ) : Space := (‖velocity r x‖)⁻¹ • velocity r x

/-- The arclength of a curve from `0` to `x`. -/
def curveArcl (r : ℝ → Space) (x : ℝ) : ℝ := ∫ y in (0)..x, ‖velocity r y‖

end Work.Drive
