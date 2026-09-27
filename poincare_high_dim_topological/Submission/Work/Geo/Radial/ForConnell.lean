import Submission.Work.Cells.Connell.Defs
import Submission.Work.Geo.Radial.annulus_conn
import Submission.Work.Geo.Radial.ext_homeo_open
import Submission.Work.Geo.Radial.LocCube
import Submission.Work.Geo.Radial.radial_expand
import Submission.Work.Geo.Radial.conn_minus_cube

/-!
# The `A7` results in the `Form`s used by `Cells/Connell` (`A8`)

`Submission/Work/Cells/Connell/Defs.lean` (area `A8`) bundles the hypotheses it needs from the
other areas in `Work.Cells.Connell.Assumptions`, with one field per blueprint item.  This file
fills the `A7` fields from the results of this area, so that instantiating `Assumptions` needs no
further work:

* `annulusForm` : blueprint `G8` (`Work.Cells.Connell.AnnulusForm`);
* `cubeMinusForm` : blueprint `C1` (`Work.Cells.Connell.CubeMinusForm`);
* `extHomeoForm` : blueprint `C0` (`Work.Cells.Connell.ExtHomeoForm`);
* `locCubeOpenForm` : blueprint `A7`/`LocCube.open_subset`
  (`Work.Cells.Connell.LocCubeOpenForm`);
* `radialExpandForm` : blueprint `G9` (`Work.Cells.Connell.RadialExpandForm`).
-/

open Set Metric

namespace Work.Geo.Radial

/-- Blueprint `G8` in the `A8` form: `Work.Geo.Radial.annulus_conn`. -/
theorem annulusForm (n : ℕ) : Work.Cells.Connell.AnnulusForm n := by
  intro β h0 h1 j hj
  exact annulus_conn (by omega) β h0 h1 j hj

/-- Blueprint `C1` in the `A8` form: `Work.Geo.Radial.conn_minus_cube`. -/
theorem cubeMinusForm (n : ℕ) : Work.Cells.Connell.CubeMinusForm n := by
  intro M inst c β h0 h1 j hj hconn
  exact conn_minus_cube c β h0 h1 j hj hconn

/-- Blueprint `C0` in the `A8` form: `Work.Geo.Radial.ext_homeo_open`. -/
theorem extHomeoForm (n : ℕ) : Work.Cells.Connell.ExtHomeoForm n := by
  intro M inst inst' O hO h C hC hid
  exact ext_homeo_open O hO h C hC hid

/-- Blueprint `A7` (`LocCube.open_subset`) in the `A8` form. -/
theorem locCubeOpenForm (n : ℕ) : Work.Cells.Connell.LocCubeOpenForm n := by
  intro M inst O hO h
  exact LocCube_open_subset h hO

/-- Blueprint `G9` in the `A8` form: `Work.Geo.Radial.radial_expand`. -/
theorem radialExpandForm (n : ℕ) : Work.Cells.Connell.RadialExpandForm n := by
  intro ε R hε hR
  exact radial_expand ε R hε hR

end Work.Geo.Radial
