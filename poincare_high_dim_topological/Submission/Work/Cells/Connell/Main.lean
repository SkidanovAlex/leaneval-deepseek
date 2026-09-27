import Submission.Work.Cells.Connell.Defs
import Submission.Work.Cells.Connell.Basic
import Submission.Work.Cells.Connell.Glue
import Submission.Work.Cells.Connell.connell_step
import Submission.Work.Cells.Connell.two_cells_sphere
import Submission.Work.Cells.Connell.cubeChart_injOn
import Submission.Work.Cells.Connell.cubeChart_isOpen_image_openCube
import Submission.Work.Cells.Connell.cubeChart_isCompact_image_closedCube
import Submission.Work.Cells.Connell.cubeChart_homeoOn
import Submission.Work.Cells.Connell.cubeChart_homeoOn_apply
import Submission.Work.Cells.Connell.cubeChart_of_isOpenCell
import Submission.Work.Cells.Connell.exists_cubeChart_subcube
import Submission.Work.Cells.Connell.exists_notMem_image_of_thinFamily
import Submission.Work.Cells.Connell.exists_thinFamily_of_domDim
import Submission.Work.Cells.Connell.interior_simp_eq_empty
import Submission.Work.Cells.Connell.meshLT_dist_lt
import Submission.Work.Cells.Connell.extOverDisc_of_homeomorph
import Submission.Work.Cells.Connell.cellCover_of_two_more
import Submission.Work.Cells.Connell.exists_isCompact_subset_covering
import Submission.Work.Cells.Connell.exists_closedCube_subset_of_isCompact_subset_openCube
import Submission.Work.Cells.Connell.exists_closedCube_of_isCompact_subset_image_openCube
import Submission.Work.Cells.Connell.exists_mesh_of_chart_cover
import Submission.Work.Cells.Connell.exists_notMem_of_isOpenCell_compactSpace
import Submission.Work.Cells.Connell.exists_openCell_of_compact_subset_compl_point

/-!
# `Work.Cells.Connell`: Connell's cell-count reduction (blueprint area `A8`)

Import this module to get the whole chapter.  Main entry points:

* `Work.Cells.Connell.connell_step` (blueprint `C2`): `CellCover n M (k+3) → CellCover n M (k+2)`
  for `n ≥ 5`, modulo the hypotheses bundled in `Work.Cells.Connell.Assumptions`.
* `Work.Cells.Connell.cellCover_two` (blueprint `C3` glue): iterating the step down to two cells.
* `Work.Cells.Connell.two_cells_sphere` (blueprint `C4`): a two-cell cover of a compact metric
  space of dimension `n ≥ 1` has a point whose complement is `ℝⁿ` (Brown's criterion).
* `Work.Cells.Connell.exists_compl_homeomorph_of_cellCover`,
  `Work.Cells.Connell.exists_compl_homeomorph_of_exists_cellCover`,
  `Work.Cells.Connell.nonempty_homeomorph_sphere_of_cellCover`: the assembled consequences,
  the last one in the shape of the challenge conclusion.

See `NOTES_Connell.md` for the bookkeeping and the list of auxiliary lemmas.
-/
