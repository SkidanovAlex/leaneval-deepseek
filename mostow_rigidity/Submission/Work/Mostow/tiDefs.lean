import Mathlib
import Submission.Mostow.GapADefs
import Submission.Work.Mostow.fermi_inv

/-!
# `Work.Mostow.tiDefs`

Vocabulary for the tube inequality `Work.Mostow.tubeIneq` (G3' of the strata chapter): the
**tube slice** over (a measurable hull of) a fundamental domain of the stratum stabiliser.

`tiTubeSlice j m DY ρ` is the set of points of `E (j + m)` whose tangential Fermi coordinate lies in
the measurable hull of `DY` and whose normal Fermi coordinate lies in the closed ball of radius `ρ`.
It is a measurable hull of `fermi '' (DY' ×ˢ closedBall 0 ρ)`, where `DY' = toMeasurable (volH j) DY`.

Its measure is `volH j DY * tubeMeasure j m (closedBall 0 ρ)` (`Work.Mostow.volH_tiTubeSlice`), it is
contained in the Fermi tube `tube j m ρ`, and it meets every orbit of the stratum stabiliser at most
`Nat.card {c | c ∈ Λ, c commutes with b, resStd c = 1}` times: this is the fibre count behind the tube
inequality.
-/

open LeanEval.Geometry.MostowRigidity MeasureTheory

namespace Work.Mostow

noncomputable section

/-- The Fermi tube slice over (the measurable hull of) `DY`. -/
def tiTubeSlice (j m : ℕ) (DY : Set (Submission.Mostow.E j)) (ρ : ℝ) :
    Set (Submission.Mostow.E (j + m)) :=
  toMeasurable (Submission.Mostow.volH (j + m))
    ((fun p : Submission.Mostow.E j × Submission.Mostow.E m =>
        Submission.Mostow.fermi j m p.1 p.2) ''
      (toMeasurable (Submission.Mostow.volH j) DY ×ˢ Metric.closedBall 0 ρ))

end

end Work.Mostow
