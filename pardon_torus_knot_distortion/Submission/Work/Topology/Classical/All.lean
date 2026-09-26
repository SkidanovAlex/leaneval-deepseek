import Submission.Work.Topology.Classical.Defs
import Submission.Work.Topology.Classical.exists_homeomorph_roundSphere
import Submission.Work.Topology.Classical.sliceData_standard_of_homeomorph
import Submission.Work.Topology.Classical.jordanSchoenflies_single
import Submission.Work.Topology.Classical.SingleDisc
import Submission.Work.Topology.Classical.exists_notMem_range_of_jordanSchoenflies
import Submission.Work.Topology.Classical.Separation
import Submission.Work.Topology.Classical.isPreconnected_openDiscs_of_schoenfliesData
import Submission.Work.Topology.Classical.schoenfliesData_of_jordanSchoenflies
import Submission.Work.Topology.Classical.SchoenfliesSphere
import Submission.Work.Topology.Classical.nested_discs_of_schoenfliesData
import Submission.Work.Topology.Classical.Nesting
import Submission.Work.Topology.Classical.cleanOneCurve_of_pushThroughInnermost
import Submission.Work.Topology.Classical.PushThrough
import Submission.Work.Topology.Classical.SliceInput
import Submission.Work.Topology.Classical.Assembly

/-!
# `Work.Topology.Classical` — the classical topology behind Pardon's Lemma 4.2

Entry point: import `Submission.Work.Topology.Classical.All`.  See
`Submission/Work/Topology/Classical/README.md` for what is proved, what is reduced to what, and
the exact names of the remaining hypotheses.

The chapter isolates the classical theorems of geometric topology which the last obstruction of
Pardon's development — `Work.Topology.SphereSlicing.ClassicalInput` — needs and which Mathlib does
not have (there is no Jordan curve theorem in Mathlib at all):

* `Work.Topology.Classical.JordanSchoenfliesSphere` — Jordan–Schoenflies on the round `2`-sphere,
  together with the standard position (nesting) of finitely many pairwise disjoint Jordan curves
  on it, equivalently the availability of a `SchoenfliesData`
  (`jordanSchoenfliesSphere_iff_schoenfliesData`);
* the cut-and-paste of Pardon's second innermost argument, either packaged as
  `Work.Topology.Classical.PushThroughInnermost` or decomposed into its two classical ingredients
  `InnermostCurveExists` (Jordan separation in the disc) and `CutsAlongSubdisc` (Alexander's
  theorem plus isotopy extension), via
  `pushThroughInnermost_of_innermostCurveExists_of_cutsAlongSubdisc`.

Their conjunction is `Work.Topology.Classical.ClassicalTopology`, and from it the chapter proves

* `sliceInput_standard_of_jordanSchoenflies`, `sliceInput_mapHomeomorph_of_jordanSchoenflies` —
  `SliceInput standard`, and `SliceInput (mapHomeomorph ψ)`;
* `cleanOneCurve_of_pushThroughInnermost`, `cleanOneCurve_mapHomeomorph_of_classicalTopology` —
  `CleanOneCurve`;
* `classicalInput_standard_of_classicalTopology`, `classicalInput_mapHomeomorph_of_classicalTopology`
  — **`ClassicalInput standard`** and `ClassicalInput (mapHomeomorph ψ)`;
* `mustbeinessentialBox_of_classicalTopology` — **Pardon's Lemma 4.2 at the box boundary** for the
  tori `F = ψ(F_standard)` of the challenge, in exactly the form
  `Work.BoxBubble.mustbeinessentialBox` consumes (the only extra hypothesis is the general position
  `TransverseSphere (mapHomeomorph ψ) (BoxSphere s c σ)` of the box boundary with `F`);
* `cleansInSphere_standard_of_classicalTopology`, `mustbeinessential_standard_of_classicalTopology`
  — Pardon's Lemma 4.2 in the vocabulary of `Work.InnermostDisk`;
* `jordanSchoenflies_single`, `bounds_disc_interior_disjoint`,
  `exists_notMem_range_of_jordanSchoenflies`, `nonempty_schoenfliesData_of_embeddedSphere`,
  `nonempty_schoenfliesData_BoxSphere` — the sharp single-curve Jordan–Schoenflies statement, the
  literal "the curve bounds a disc whose interior misses it", the non-vacuity of the complement of
  finitely many disjoint Jordan curves on `S²`, and Jordan–Schoenflies on an arbitrary embedded
  sphere and on the box boundary, all derived from `JordanSchoenfliesSphere`;
* `Work.Topology.Classical.AlexanderSphereTheorem` — Alexander's separation theorem, recorded (as a
  `Prop`) for the archive; `CutsAlongSubdisc` is the piece of it (with isotopy extension) that the
  argument consumes.
-/
