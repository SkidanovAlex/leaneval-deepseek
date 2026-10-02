/-
# Area `Submission/Work/TopJordan` -- the Jordan curve theorem, discharged

**Import this module to get the whole area.**

* `Work.TopJordan.jordanForm : Work.Top.JordanForm` -- the Jordan curve theorem in the form
  needed by the mandelbar endgame, proved (not assumed).
* `Work.TopJordan.sidesOf`, `Work.TopJordan.sidesOfCurve` -- the two sides of a Jordan curve
  (`Work.Top.Sides C`), without the hypothesis `Work.Top.JordanForm`.
* `Work.TopJordan.not_isPathConnected_of_twoSidedPinch`,
  `Work.TopJordan.mandelbar_not_isPathConnected_of_twoSidedPinch`,
  `Work.TopJordan.scale_separation` -- the endgame of `Submission/Work/Top`, verbatim but with
  `hJ : Work.Top.JordanForm` removed.

See the headers of the individual modules for the rest of the interface.
-/
import Submission.Work.TopJordan.Components
import Submission.Work.TopJordan.CurveModel
import Submission.Work.TopJordan.Sides
import Submission.Work.TopJordan.Jordan
import Submission.Work.TopJordan.SidesAPI
import Submission.Work.TopJordan.isJordanCurve_of_two_arcs
import Submission.Work.TopJordan.isJordanCurve_of_two_paths
import Submission.Work.TopJordan.exists_two_paths_of_isJordanCurve
import Submission.Work.TopJordan.sidesOfCurve_I_eq_of_range_eq
import Submission.Work.TopJordan.sidesOfCurve_O_eq_of_range_eq
import Submission.Work.TopJordan.Endgame

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

