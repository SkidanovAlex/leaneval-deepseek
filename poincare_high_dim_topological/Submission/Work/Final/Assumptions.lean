import Submission.Work.Final.Inputs
import Submission.Work.Final.Forms
import Submission.Work.Geo.Radial.ForConnell

/-!
# `Work.Final.assumptionsOfInputs`: the bundle `Assumptions n M` of the Connell area

`Work.Cells.Connell.Assumptions n M` is the interface through which the cell-count reduction
(`Work.Cells.Connell.connell_step`) consumes the other areas.  This file builds it from

* the single holder `Work.Final.FinalInputs n` (the engulfing theorem `E0`), and
* the delivered results of `Work.Geo.Radial` (`A7`: `G8`, `C1`, `C0`, `LocCube.open_subset`),
  `Work.Final.skeletonData` (`A6`/`G7`) and `Work.Final.{cubeTriangulationForm,
  domDimAffineForm}` (`A2`/`G10`, `G7`).
-/

universe u

namespace Work.Final

/-- **The `Assumptions` of the Connell area, from the holders and the delivered areas.** -/
noncomputable def assumptionsOfInputs {n : ℕ} (I : FinalInputs.{u} n) (M : Type u) :
    Work.Cells.Connell.Assumptions.{u} n M where
  engulf := I.engulf
  skeleton := skeletonData n
  annulus := Work.Geo.Radial.annulusForm n
  cubeMinus := Work.Geo.Radial.cubeMinusForm n
  extHomeo := Work.Geo.Radial.extHomeoForm n
  locCubeOpen := Work.Geo.Radial.locCubeOpenForm n
  triangulation := cubeTriangulationForm n
  domDimAffine := domDimAffineForm n

end Work.Final
