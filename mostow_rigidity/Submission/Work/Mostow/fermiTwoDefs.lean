import Mathlib
import Submission.Work.Mostow.QIDefs

/-!
# The standard geodesic line of `E 2` and its standard Fermi chart

This file fixes the reference objects used to build the Fermi parametrisation of an
arbitrary unit-speed geodesic line of the hyperbolic plane `ℍ² = E 2`.

* `axis`, `axisPerp` are the two standard basis vectors of `E 2` (so `axis = e₁`),
* `lineStd s = sinh s • axis` is the standard unit-speed geodesic,
* `stdFermi (s, r) = cosh r • lineStd s + sinh r • axisPerp` is the Fermi parametrisation
  of `E 2` about `lineStd`: the second coordinate is the signed hyperbolic distance to the
  line and `lineStd s` is the foot.

In the graph chart of `hlift`, `stdFermi (s, r)` is the chart point `(cosh r sinh s, sinh r)`,
and the hyperbolic area element in these coordinates is `cosh r ds dr`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

namespace FermiTwo

noncomputable section

/-- The first standard basis vector of `E 2`. -/
def axis : E 2 := EuclideanSpace.single (0 : Fin 2) 1

/-- The second standard basis vector of `E 2` (perpendicular to `axis`). -/
def axisPerp : E 2 := EuclideanSpace.single (1 : Fin 2) 1

/-- The standard unit-speed geodesic line of `E 2`. -/
def lineStd (s : ℝ) : E 2 := Real.sinh s • axis

/-- The standard Fermi chart about `lineStd`. -/
def stdFermi (p : ℝ × ℝ) : E 2 := Real.cosh p.2 • lineStd p.1 + Real.sinh p.2 • axisPerp

/-- Expanded form of `stdFermi`, convenient for computation. -/
lemma stdFermi_apply (s r : ℝ) :
    stdFermi (s, r) = (Real.cosh r * Real.sinh s) • axis + Real.sinh r • axisPerp := by
  simp [stdFermi, lineStd, smul_smul]

end

end FermiTwo

end Work.Mostow
