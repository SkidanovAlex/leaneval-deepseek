import Submission.Lib.Unif2.Commons.Topology.Plane.dyadicPolyomino_deformationRetract
import Submission.Lib.Unif2.Commons.Topology.Plane.exists_dyadic_exhaustion_of_isOpen_complex
import Submission.Lib.Unif2.Commons.Topology.Plane.union_of_retracts
import Submission.Lib.Unif2.Commons.Topology.Plane.convex_tree_retract
import Submission.Lib.Unif2.Commons.Topology.Homotopy.simplyConnectedSpace_of_retraction
import Submission.Lib.Unif2.Commons.Topology.Connected.frontier_component_compl_range
import Submission.Lib.Unif2.Commons.Topology.Jordan.plane_separation
import Submission.Lib.Unif2.Work.Spine.Plane.Dyadic

/-!
# Tools for the planar simple-connectivity area

Bundle of the (sorry-free) library modules that the lemmas of
`Submission/Work/PlanarSC/` build on:

* `Commons.Topology.Plane.dSq` — the closed dyadic squares of level `n` (the level-`n` "polyomino"
  cells), together with the scaling `dsc n` identifying them with the unit squares;
* `Commons.Topology.Plane.dyadicPolyomino_deformationRetract` — a finite union of dyadic cells
  strongly deformation retracts onto a `1`-dimensional CW spine;
* `Commons.Topology.Plane.{union_of_retracts, convex_tree_retract, union_retract}` — Borsuk's
  gluing theorem for plane retracts, and the retraction of `ℂ` onto a "tree" of convex pieces;
* `Commons.Topology.Homotopy.simplyConnectedSpace_of_retraction` — a retract of a contractible space
  is simply connected;
* `Commons.Topology.Connected.frontier_component_compl_range` — the frontier of a complementary
  component of a Jordan curve is the curve;
* `Commons.Topology.Jordan.plane_separation` — the Jordan separation theorem (the complement of the
  image of an injective circle map has exactly two components, one bounded);
* `Work.Spine.Plane.Dyadic` — the canonical dyadic exhaustion `polyK U hU n` of an open set.
-/
