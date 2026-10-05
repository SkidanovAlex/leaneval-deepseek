import Mathlib

/-!
# The phase turning a `φ`-rectangle into normal form (`Work.RPV.HrectPhase`)

Given the diagonal `d = x - y` of a `φ`-rectangle (Greene–Lobb normal form
`x' - y' = e^{iφ}(x - y)`, `x + y = x' + y'`), the rectangle can be written as
`R z w θ` for

* the unit complex number `c = i·e^{iφ/2}·d/‖d‖`, and
* `z = x·conj c`, `w = y·conj c`, `θ` any angle with `θ.toCircle = c`.

This file only records the definition of that unit complex number; the algebraic
facts about it are proved in the sibling modules
`Submission.Work.RPV.HrectPhaseFacts` and `Submission.Work.RPV.ExpHalfReIm`.
-/

noncomputable section

namespace Work.RPV

/-- The unit complex number `c = i·exp(iφ/2)·d/‖d‖`. -/
def hrectC (φ : ℝ) (d : ℂ) : ℂ :=
  Complex.I * Complex.exp (((φ / 2 : ℝ) : ℂ) * Complex.I) * (d / (‖d‖ : ℂ))

end Work.RPV
