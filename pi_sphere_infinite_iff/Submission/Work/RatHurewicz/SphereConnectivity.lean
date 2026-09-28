import Mathlib
import Submission.Work.RatHurewicz.SerreHurewicz
import Submission.Work.RatHurewicz.stableStemsTorsion_of_rationalHurewiczStable
import Submission.Work.Stems.sphereConnectivity

/-!
# The connectivity of spheres, and the unconditional corollary for `Sⁿ`

Area **RATHUREWICZ** (`Submission/Work/RatHurewicz/`).  The corollary of the drive's contract for
`Sⁿ` (`Work.RatHurewicz.stableStemsTorsion_of_rationalHurewiczStable`) takes the classical
connectivity of the sphere `Work.RatHurewicz.SphereConnected` as an explicit hypothesis.  That
hypothesis is a theorem of the area STEMS:

* `Work.Stems.sphereConnectivity : Work.Stems.SphereConnectivity` (the geometric general-position
  result `Work.Stems.sphereMap_null_of_lt`: a based map `S^j → Sⁿ` with `j < n` is null-homotopic),
* `Work.Stems.ratHurewiczSphereConnected' : Work.RatHurewicz.SphereConnected` (the same statement in
  the vocabulary of this area, `Submission/Work/Stems/sphereConnected_drive.lean`).

This module discharges the hypothesis, so that

* `Work.RatHurewicz.sphereConnected` is a proof of `Work.RatHurewicz.SphereConnected`, and
* `Work.RatHurewicz.stableStemsTorsion_of_rationalHurewiczStable'` is the **unconditional** form of
  the corollary: the drive's contract `Work.Drive.RationalHurewiczStable` alone implies the STEMS
  contract `Work.Drive.StableStemsTorsion`.

The remaining input of the whole STEMS branch of the project is therefore exactly the contract of
this area (the rational Hurewicz statement in the stable range); see `README.md` §5.
-/

open scoped Topology

namespace Work.RatHurewicz

noncomputable section

/-- **`Sⁿ` is `(n-1)`-connected**, proved in the area STEMS (via the general-position argument that
a based map `S^j → Sⁿ` with `j < n` misses a point and is therefore null-homotopic). -/
theorem sphereConnected : SphereConnected := Work.Stems.ratHurewiczSphereConnected'

/-- **The contract for spheres, unconditionally.**  The drive's contract
`Work.Drive.RationalHurewiczStable` implies the STEMS contract `Work.Drive.StableStemsTorsion`:
the connectivity hypothesis of `stableStemsTorsion_of_rationalHurewiczStable` is discharged by
`sphereConnected`. -/
theorem stableStemsTorsion_of_rationalHurewiczStable' (h : Work.Drive.RationalHurewiczStable) :
    Work.Drive.StableStemsTorsion :=
  stableStemsTorsion_of_rationalHurewiczStable h sphereConnected

end

end Work.RatHurewicz
