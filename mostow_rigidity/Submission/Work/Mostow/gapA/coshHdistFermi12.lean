import Mathlib
import Submission.Work.Mostow.gapA.slabDefs
import Submission.Work.Mostow.fermi_inv
import Submission.Work.Mostow.cosh_hdist_fermi

/-!
# The `(k,m) = (1,2)` instance of the Fermi distance formula

`Submission.Work.Mostow.cosh_hdist_fermi` proves the Fermi-coordinate distance formula F2 in
every dimension pair `(k,m)`:

`cosh (hdist (fermi k m v w) (fermi k m v' w')) =
   cosh ‖w‖ * cosh ‖w'‖ * cosh (hdist v v') - sinhc ‖w‖ * sinhc ‖w'‖ * ⟪w,w'⟫`.

The gap-A (`n = 3`, geodesic stratum) development only needs the case `k = 1`, `m = 2`, i.e. the
Fermi chart about a geodesic in `ℍ³`; this file states that instance under its local name.
-/

namespace Work.Mostow.gapA

/-- **F2 for the geodesic stratum in `ℍ³`** (`k = 1`, `m = 2`): the hyperbolic cosine of the
distance between two points of `ℍ³` written in Fermi coordinates `(v,w)`, `(v',w')` about the
standard geodesic, in terms of the foot distance `hdist v v'` and the normal inner product
`⟪w,w'⟫`. -/
theorem coshHdistFermi12 (v v' : Submission.Mostow.E 1) (w w' : Submission.Mostow.E 2) :
    Real.cosh (Submission.Mostow.hdist (Submission.Mostow.fermi 1 2 v w)
        (Submission.Mostow.fermi 1 2 v' w'))
      = Real.cosh ‖w‖ * Real.cosh ‖w'‖ * Real.cosh (Submission.Mostow.hdist v v')
          - Submission.Mostow.sinhc ‖w‖ * Submission.Mostow.sinhc ‖w'‖ * inner ℝ w w' := by
  exact Work.Mostow.cosh_hdist_fermi 1 2 v v' w w'

end Work.Mostow.gapA
