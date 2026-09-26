import Submission.Work.Smooth.Plane.Defs
import Submission.Work.Smooth.Plane.Jordan
import Submission.Work.Smooth.Plane.Convex
import Submission.Work.Smooth.Plane.Convex.lift_eq_of_notMem_convex
import Submission.Work.Smooth.Plane.Slicing
import Submission.Work.Smooth.Plane.SlicingReduce
import Submission.Work.Smooth.Plane.Slicing.planeSliceData_covers
import Submission.Work.Smooth.Plane.Slicing.planeSliceData_inside_subset
import Submission.Work.Smooth.Plane.Slicing.not_isEssential_of_range_subset_arc
import Submission.Work.Smooth.Plane.Slicing.innermostDiscInput_of_slicing
import Submission.Work.Smooth.Plane.Cleaning
import Submission.Work.Smooth.Plane.SlicedClean
import Submission.Work.Smooth.Plane.Consequence
import Submission.Work.Smooth.Plane.encard_pardonSlice_inter_lt_pardonsI
import Submission.Work.Smooth.Plane.PardonSlice

/-!
# `Work.Smooth.Plane` — the planar innermost-disc / cut-and-paste chapter

Entry point: import `Submission.Work.Smooth.Plane.All`.  See
`Submission/Work/Smooth/Plane/README.md` for the full account.

This chapter is the *planar* counterpart of `Work.InnermostDisk` (which works inside a sphere): it
proves Pardon's two innermost arguments for a **convex planar region** `D ⊆ ℝ³` — in the
application the slice `D = PBox s c σ ∩ {y | y (σ 2) = c (σ 2) + u}` of Pardon's box by the cutting
plane of the double-bubble core `Work.BoxShrink.CruxCore` — and derives from them the fact that the
core needs: **the closed slice carries no essential loop of the surface**.

## The setting

* `F = P.carrier` is the surface of a parametrised torus `P`; in the application
  `P = Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph` for the diffeomorphism
  `ψ : Submission.Diffeo` of the challenge.
* `Work.Smooth.Plane.IsConvexPlanar D` — `D` is convex and contained in a plane;
  `Work.Smooth.Plane.PardonSlice s c σ u` — the slice of Pardon's box by the cutting plane;
  `Work.Smooth.Plane.planeProj σ`, `planeLift σ h` — the coordinates `σ 0`, `σ 1` identify the
  plane `{y | y (σ 2) = h}` with `ℂ`.

## The four items

1. **Planar Jordan–Schoenflies, convexity form.**
   `Work.Smooth.Plane.nullHomotopicAvoiding_of_convex` (the straight-line homotopy),
   `Work.Smooth.Plane.PlaneJordanData.e_mem_of_convex` (in `ℂ`),
   `Work.Smooth.Plane.exists_spanningDisc_of_convex_planar` and
   `Work.Smooth.Plane.exists_spanningDisc_of_closedCurve` (in `ℝ³`): a simple closed curve in a
   convex planar region bounds an embedded disc contained in that region.  The classical input is
   `Work.Smooth.Plane.PlaneJordanInput` (Jordan–Schoenflies plus the hard direction of the Jordan
   curve theorem in homotopy form).

2. **Planar slicing.**  `Work.Smooth.Plane.PlaneSliceData P D` (the classical facts),
   `Work.Smooth.Plane.PlaneSlicing P D` (the full datum: closed components and arcs, the discs they
   bound inside `D`, the nesting rank, the covering property), the reduction
   `Work.Smooth.Plane.planeSlicingOfSliceData` with
   `Work.Smooth.Plane.Slicing.planeSliceData_covers` and
   `Work.Smooth.Plane.Slicing.planeSliceData_inside_subset`, the input
   `Work.Smooth.Plane.PlaneSliceInput P` / `TransversePlane P D`, and the general-position predicate
   `Work.Smooth.Plane.SlicedPlane P D`.

3. **Innermost selection and cleaning.**  `Work.Smooth.Plane.Slicing.innermostDiscInput_of_slicing`
   (Pardon's first innermost step for a planar slice: an essential loop inside `D` lies on an
   essential closed component of minimal rank, whose disc then meets `F` only in inessential
   curves), and `Work.Smooth.Plane.CleansInConvexPlane P D` (Pardon's cut-and-paste cleaning:
   every essential loop inside `D` can be replaced by a simple essential loop inside `D` bounding a
   disc in the complement of `F`), derived from the slicing and the cut-and-paste in
   `Work.Smooth.Plane.SlicedClean`.

1'. **The same, through the winding-number machinery** (the alternative route hinted at by the
   requester): `Work.Smooth.Plane.Convex.lift_eq_of_notMem_convex` — a loop lying in a convex set winds zero
   times around any point outside it, in the degree form "any lift of the normalised loop returns to
   its starting value", proved from the covering-space monodromy
   `Work.CoreTopology.circle_lift_eq_of_extends_disk` / `Circle.isCoveringMap_exp`.

4. **The consequence.**  `Work.Smooth.Plane.windingSpan_eq_bot_of_cleansInConvexPlane` (Pardon's
   counting argument), and its application to the slice of Pardon's box:
   `Work.Smooth.Plane.windingSpan_pardonSlice_eq_bot`,
   `Work.Smooth.Plane.not_containsEssentialLoop_pardonSlice`,
   `Work.Smooth.Plane.windingSpan_pardonSlice_inter_PBox_eq_bot` (the literal form
   `WindingSpan P (D ∩ PBox s c σ) = ⊥`), and the forms taking the classical inputs of the core:
   `Work.Smooth.Plane.windingSpan_pardonSlice_eq_bot_of_sliced` (from the general position
   `SlicedPlane` and the global cut-and-paste `Work.InnermostDisk.CleansDiscs`) and
   `Work.Smooth.Plane.windingSpan_pardonSlice_eq_bot_of_sliceInput` (from `TransversePlane` and
   `PlaneSliceInput`).
-/

namespace Work.Smooth.Plane

end Work.Smooth.Plane
