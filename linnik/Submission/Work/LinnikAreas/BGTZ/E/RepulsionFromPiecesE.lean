import Mathlib
import Submission.Work.LinnikAreas.BGTZ.RepulsionFromPiecesC2
import Submission.Work.LinnikAreas.BGTZ.DetectorEDefs

/-!
**L10 of the BGTZ/E route (see `BGTZ/BGTZ_ROUTE_LEAD.md` section 2.7).**

The assembly of BGTZ Theorem 1.3 against the corrected detector interface `DetectorPropE`: it is
`Work.LinnikAreas.BGTZ.RepulsionFromPiecesC2_aux` (in
`Submission/Work/LinnikAreas/BGTZ/RepulsionFromPiecesC2.lean`), whose detector hypothesis is taken
in the interface `DetectorPropE` instead of the retired `DetectorMainPropPinned`.

The three edits with respect to `RepulsionFromPiecesC2_aux` are the sizes
(`E.RepulsionSizesE`, the scale `detNE`), case (c) (`E.caseC_bound_far`, `Re rho < 3/4`), and the
detector hypotheses (`3/4 <= Re rho`, `1 + |Im rho| <= T`).  `HypB`, `SelbergSieveMainProp` and
`RatioLoneProp` are not used.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.BGTZ.E

/-- **From the detector and the zero-free region to `RepulsionGenC`** (the assembly of
`BGTZ_ROUTE_LEAD.md` section 2.7): BGTZ Theorem 1.3 with the additive constant displayed. -/
theorem RepulsionFromPiecesE (cZ : ℝ) (hcZ : 0 < cZ)
    (hA : ∃ A : ℝ, Work.LinnikAreas.BGTZ.HypA A Work.LinnikAreas.BGTZ.thA)
    (hZ : ∃ Cz : ℝ, Work.LinnikAreas.BGTZ.HypZeta Cz)
    (hSW : Work.LinnikAreas.BGTZ.SieveWeightsProp)
    (hDet : Work.LinnikAreas.BGTZ.DetectorPropE)
    (hzfr : Work.LinnikAreas.BGTZ.ZFRInputL cZ) :
    Work.LinnikAreas.BGTZ.RepulsionGenC (11 / 5) (11 / 10) (max (1000 / cZ) 1000) :=
  Work.LinnikAreas.BGTZ.RepulsionFromPiecesC2E_aux cZ hcZ hA hZ hSW hDet hzfr

end Work.LinnikAreas.BGTZ.E
