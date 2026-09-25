import Submission.Work.Tower.MinkowskiGS.Defs
import Submission.Work.Tower.MinkowskiGS.Endgame
import Submission.Work.Tower.MinkowskiGS.Bridge
import Submission.Work.Tower.MinkowskiGS.Numeric.exists_minkowski_parameters
import Submission.Work.Tower.MinkowskiGS.Numeric.minkowski_numeric_dimCl_eventually
import Submission.Work.Tower.MinkowskiGS.Minkowski.classGroupTorsion_finrank_le_minkowski
import Submission.Work.Tower.MinkowskiGS.Assembly

/-!
# The `Work.Tower.MinkowskiGS` area: the (a)-only tower

This area re-architects the class-field tower of the unit-distance construction so that its
relation-rank input is **Koch's fact (a) alone** — no class-group rank formula (b′), and hence no
Artin reciprocity.

## Main results (see `README.md` for the full account)

* `Work.Tower.MinkowskiGS.unramified_tower_gs_classGroup` — the Golod–Šafarevič endgame with the
  per-field relation bound `proPRelationRank ≤ M + |T|`.
* `Work.Tower.MinkowskiGS.classGroupRelationBound_of_kochInjectionInput`,
  `Work.Tower.MinkowskiGS.classGroupRelationBound_of_abstractKochInput` — fact (a) (in the
  finite `T`-split or in the abstract `∃ G` form) gives `ClassGroupRelationBound`.
* `Work.Tower.MinkowskiGS.exists_minkowski_parameters` — the numerical heart.
* `Work.Tower.MinkowskiGS.classGroupTorsion_finrank_le_minkowski` — Minkowski's bound on
  `dim Cl_F[3]`.
* `Work.Tower.MinkowskiGS.exists_tower_of_kochInjectionInput` — **the deliverable**: fact (a)
  implies the statement of `Work.Interface.exists_tower`.
-/
