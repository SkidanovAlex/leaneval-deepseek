import Mathlib
import Submission.Work.Mostow.fermiTwoDefs

/-!
# Auxiliary definitions for the volume of the standard Fermi rectangle

`Work.Mostow.FermiTwo.stdFermiVolume` computes the hyperbolic area of the image of a rectangle
`[0,L) × (-ρ,ρ)` under the standard Fermi chart of `ℍ²`.  The chart is split here into

* `coordMap : ℝ × ℝ → E 2`, the linear coordinate identification `(s,r) ↦ s • e₁ + r • e₂`, and
* `fermiSelf : E 2 → E 2`, the Fermi chart of `E 2` read in these coordinates, so that
  `stdFermi p = fermiSelf (coordMap p)` and the Jacobian of `fermiSelf` at `x` is the honest
  `fderiv` in the chart.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal

namespace FermiTwo

noncomputable section

/-- The coordinate identification `ℝ × ℝ → E 2`, `(s,r) ↦ s • e₁ + r • e₂`. -/
def coordMap (p : ℝ × ℝ) : E 2 := p.1 • axis + p.2 • axisPerp

/-- The standard Fermi chart of `E 2`, as a self-map in the coordinates of `E 2`. -/
def fermiSelf (x : E 2) : E 2 :=
  Real.cosh (x 1) • lineStd (x 0) + Real.sinh (x 1) • axisPerp

/-- The coordinate box `{x : E 2 | x 0 ∈ Ico 0 L ∧ x 1 ∈ Ioo (-ρ) ρ}`. -/
def boxSq (L ρ : ℝ) : Set (E 2) :=
  {x : E 2 | x 0 ∈ Set.Ico 0 L ∧ x 1 ∈ Set.Ioo (-ρ) ρ}

end

end FermiTwo

end Work.Mostow
