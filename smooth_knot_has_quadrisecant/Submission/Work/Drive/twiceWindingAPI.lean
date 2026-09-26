import Mathlib
import Submission.TrappedWinding
import Submission.ComponentWindingData
import Submission.ComponentNullHomotopy
import Submission.ComponentIntervalSide
import Submission.TrisecantStructure

/-!
# Import wrapper: the trisecant-component / winding vocabulary

Thin re-export module so that sibling developments under `Submission/Work/` can name, in a
`depends_on` list, the vocabulary of the winding (trapped-middle) analysis of a circular component of
the trisecant locus:

* `OSub r`, `TrisecantComponent r c₀`, `TrisecantComponent_dichotomy`, `componentClassMap`,
  `componentMiddle` (`Submission/ComponentIntervalSide.lean`,
  `Submission/ComponentWindingData.lean`);
* `OnceWindingData`, `TwiceWindingEndpointsData`, `MiddleNonZeroAdvance`,
  `once_winding_component_contradiction_holds`, `twice_winding_data_false`,
  `advance_eq_of_class_ne` (`Submission/TrappedWinding.lean`);
* `not_every_image_point_between` (Pannwitz's extremal lemma,
  `Submission/TrisecantStructure.lean`);
* `circular_component_curve_nullHomotopic` (`Submission/ComponentNullHomotopy.lean`).

Those modules live outside `Submission/Work/`, so they cannot be named in a `depends_on` list; this
file puts the vocabulary one hop closer.  It contains no declarations of its own.
-/
