import Submission.Work.Topology.SphereSlicing.Defs
import Submission.Work.Topology.SphereSlicing.boxNorm_continuous
import Submission.Work.Topology.SphereSlicing.boxNorm_homogeneous
import Submission.Work.Topology.SphereSlicing.isOpen_PBox
import Submission.Work.Topology.SphereSlicing.convex_PBox
import Submission.Work.Topology.SphereSlicing.frontier_PBox
import Submission.Work.Topology.SphereSlicing.isClosed_BoxSphere
import Submission.Work.Topology.SphereSlicing.isCompact_BoxSphere
import Submission.Work.Topology.SphereSlicing.homeomorph_BoxSphere
import Submission.Work.Topology.SphereSlicing.isEmbeddedSphere_BoxSphere
import Submission.Work.Topology.SphereSlicing.preconnected_finite_closed_cover
import Submission.Work.Topology.SphereSlicing.range_closedCurve_isCompact
import Submission.Work.Topology.SphereSlicing.encard_range_inter_le_encard_param
import Submission.Work.Topology.SphereSlicing.exists_rank_of_strict_order
import Submission.Work.Topology.SphereSlicing.sliceData_covers
import Submission.Work.Topology.SphereSlicing.sliceData_inside_subset
import Submission.Work.Topology.SphereSlicing.sliceData_inter_eq_iUnion
import Submission.Work.Topology.SphereSlicing.transverseSphere_covers
import Submission.Work.Topology.SphereSlicing.not_containsEssentialLoop_of_finite_inter
import Submission.Work.Topology.SphereSlicing.transverseSphere_map_homeomorph_iff
import Submission.Work.Topology.SphereSlicing.Transport
import Submission.Work.Topology.SphereSlicing.sliceData_map_homeomorph_iff
import Submission.Work.Topology.SphereSlicing.cleanOneCurve_map_homeomorph_iff
import Submission.Work.Topology.SphereSlicing.removesOneCurve_of_cleanOneCurve
import Submission.Work.Topology.SphereSlicing.cleansDiscs_of_cleanOneCurve
import Submission.Work.Topology.SphereSlicing.Slice.Base
import Submission.Work.Topology.SphereSlicing.Slice.Nest
import Submission.Work.Topology.SphereSlicing.Slice.Reduce
import Submission.Work.Topology.SphereSlicing.Clean.Reduce
import Submission.Work.Topology.SphereSlicing.GeneralPosition
import Submission.Work.Topology.SphereSlicing.Assembly

/-!
# `Work.Topology.SphereSlicing` — the classical surface-topology chapter behind Pardon's Lemma 4.2

Entry point: import `Submission.Work.Topology.SphereSlicing.All`.  See
`Submission/Work/Topology/SphereSlicing/README.md` for what is proved, what is reduced to what, and
the exact names of the remaining hypotheses.

Summary of the interface:

* `Work.Topology.SphereSlicing.BoxSphere s c σ` — the boundary `∂PBox s c σ = {y | boxNorm c σ y = s}`
  of Pardon's box, a genuine embedded `S²` (`isEmbeddedSphere_BoxSphere`), with an explicit
  homeomorphism to `Metric.sphere 0 1` (`homeomorph_BoxSphere`).
* `Work.Topology.SphereSlicing.SliceData P S` — the classical slicing datum of a sphere `S` by
  `F = P.carrier`, with `SliceInput P` its global form.
* `Work.Topology.SphereSlicing.SliceDisc P`, `CleanOneCurve P` — the local model of Pardon's single
  cut-and-paste.
* `Work.Topology.SphereSlicing.ClassicalInput P` — the chapter's single classical hypothesis,
  `SliceInput P ∧ CleanOneCurve P`.
* `Work.Topology.SphereSlicing.mustbeinessentialBox_of_sliceData` /
  `mustbeinessentialBox_of_classicalInput` / `mustbeinessentialBox_of_classicalInput_standard` —
  Pardon's Lemma 4.2 at the box boundary for the tori of the challenge, with the intersection count
  in the parameter form of Pardon's sweep and `I(F, β) = min p q`, the latter in the normal form
  where only the *standard* torus needs the classical input.
-/
