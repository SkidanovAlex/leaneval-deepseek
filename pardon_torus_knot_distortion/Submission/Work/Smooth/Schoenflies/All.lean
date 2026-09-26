import Submission.Work.Smooth.Schoenflies.ChordDefs
import Submission.Work.Smooth.Schoenflies.Geometry
import Submission.Work.Smooth.Schoenflies.Separation
import Submission.Work.Smooth.Schoenflies.Injectivity
import Submission.Work.Smooth.Schoenflies.Main
import Submission.Work.Smooth.Schoenflies.caratheodory_extension_continuous
import Submission.Work.Smooth.Schoenflies.Unconditional
import Submission.Work.Smooth.Schoenflies.NullHomotopy
import Submission.Work.Smooth.Schoenflies.NullHomotopyRel
import Submission.Work.Smooth.Schoenflies.RelExtension
import Submission.Work.Smooth.Schoenflies.PlaneJordanDataRel
import Submission.Work.Smooth.Schoenflies.ConvexRel
import Submission.Work.Smooth.Schoenflies.ConvexRepair

/-!
# `Work.Smooth.Schoenflies` — the planar Jordan–Schoenflies theorem via Carathéodory

Import `Submission.Work.Smooth.Schoenflies.All` for the whole chapter (namespace
`Work.Smooth.Schoenflies`); see `README.md`.

## Main results

The chapter proves the **boundary correspondence** for a Carathéodory extension and assembles it
into the planar Jordan–Schoenflies theorem:

* `injOn_of_extension` (`Injectivity.lean`) — if `Ω` is a Jordan domain, `f : 𝔻 → Ω` a
  biholomorphism and `G` a continuous extension to the closed disc with boundary values in
  `frontier Ω`, then `G` is **injective**;
* `caratheodoryJordan_of_extension` (`Main.lean`) — hence the closure of a Jordan domain is
  homeomorphic to the closed disc (the hypothesis `H` of
  `Work.Smooth.SphereJordan.planeHypothesis_of_caratheodoryJordan`);
* `planeHypothesis_of_caratheodoryExtension` — `Work.Smooth.SphereJordan.PlaneHypothesis`;
* `classicalInput_of_caratheodoryExtension` — `Work.Smooth.Jordan.ClassicalInput`;
* `schoenfliesInput_of_caratheodoryExtension`, `nonempty_planeSchoenflies_of_caratheodoryExtension`
  — the `C¹` forms.

**Unconditional statements** (`Unconditional.lean`), with the input
`CaratheodoryExtensionInput` proved in `caratheodory_extension_continuous.lean` (the
length–area/cap argument, ported from `Submission/Work/Smooth/SphereJordan/Caratheodory/` and
completed here):

* `classicalInput : Work.Smooth.Jordan.ClassicalInput`;
* `planeHypothesis : Work.Smooth.SphereJordan.PlaneHypothesis`;
* `schoenfliesInput`, `nonempty_planeSchoenflies`, `nonempty_planeSchoenflies_of_smooth`.

## The corrected null-homotopy predicate

`Work.Smooth.Plane.NullHomotopicAvoiding` (the "does not wind around `x`" hypothesis of the planar
innermost-disc chapter) lacks the condition that the homotopy go through loops based at `c 0`; the
cone homotopy shows that it is satisfied by every point off the trace, so the chapter's classical
input `Work.Smooth.Plane.PlaneJordanInput` is **false**:

* `NullHomotopy.lean` — `nullHomotopicAvoiding_of_notMem_range`, `not_nonempty_planeJordanData`,
  `not_planeJordanInput`;

with the corrected predicate `NullHomotopicRel` (a homotopy of loops relative to the base point) the
classical statement becomes true and is proved here:

* `NullHomotopyRel.lean` — `conePoint`, `NullHomotopicRel`, `NullHomotopicRel.of_discExtension`;
* `RelExtension.lean` — `exists_discExtension_of_nullHomotopicRel` (the quotient descent through
  `conePoint`);
* `PlaneJordanDataRel.lean` — `not_nullHomotopicRel_of_mem_V` (**the hard direction of the Jordan
  curve theorem**, corrected), `PlaneJordanDataRel`, `PlaneJordanInputRel`,
  `nonempty_planeJordanDataRel_of_smooth` (**unconditional** for `C¹` curves);
* `ConvexRel.lean` — `nullHomotopicRel_of_convex`, `PlaneJordanDataRel.e_mem_of_convex`,
  `planeJordanInputRel_of_smooth` (the convexity form of planar Jordan–Schoenflies, corrected);
* `ConvexRepair.lean` — `planeJordanInputRel` (**the corrected classical input, unconditionally**),
  `exists_spanningDisc_of_convex_planar_rel`, `exists_spanningDisc_of_closedCurve_rel` (the repaired
  convexity form of the sibling chapter `Work.Smooth.Plane`, with no input).
-/
