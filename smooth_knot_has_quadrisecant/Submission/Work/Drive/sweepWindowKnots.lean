import Mathlib
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.chordSweepDefs
import Submission.Work.Drive.sweepLoop_injective
import Submission.Work.Drive.sweepFam_slices_knots

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant


/-- **The (a.e.) derivative of the chamfered sweep loop in its loop parameter.**
The four branches are the derivatives of the four branches of `sweepLoopChamfer` w.r.t. the loop
parameter `t`; the (measure-zero) breakpoints are assigned the preceding branch, which is
irrelevant for the `intervalIntegral` identities.  Combined with the fundamental theorem of
calculus along the loop this is the workhorse for turning differences
`sweepFam … (t+h) - sweepFam … t` into box integrals of these directions. -/
noncomputable def sweepLoopChamferDeriv (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam s : ℝ) : ℝ → Space :=
  fun t =>
    let u := sweepParam t
    (1 / period) •
      (if u ≤ 1 / 2 then
        (2 * (1 - 2 * lam)) •
          ((sweepW' D s) •
            deriv r (taR D s + (lam + (1 - 2 * lam) * (2 * u)) * sweepW' D s))
      else if u ≤ 1 / 2 + lam / 2 then
        (2 / lam) • (sweepChord' r D s (1 - lam) - sweepArc' r D s (1 - lam))
      else if u ≤ 1 - lam / 2 then
        (-(1 - 2 * lam) / (1 / 2 - lam)) • (r (tbR D s) - r (taR D s))
      else
        (2 / lam) • (sweepArc' r D s lam - sweepChord' r D s lam))


end Work.Drive
