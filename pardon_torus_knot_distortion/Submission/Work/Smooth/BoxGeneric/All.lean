import Submission.Work.Smooth.BoxGeneric.Defs
import Submission.Work.Smooth.BoxGeneric.Bridge
import Submission.Work.Smooth.BoxGeneric.Vertex
import Submission.Work.Smooth.BoxGeneric.Vertex.volume_carrier_eq_zero
import Submission.Work.Smooth.BoxGeneric.Vertex.aeNoVertex_of_ae_centre
import Submission.Work.Smooth.BoxGeneric.Vertex.vertexDir_mem_fderiv_range_of_not_isolated
import Submission.Work.Smooth.BoxGeneric.LocalArc.local_arc_of_max_of_isInvertible
import Submission.Work.Smooth.BoxGeneric.LocalArc.local_arc_of_max_of_tangential
import Submission.Work.Smooth.BoxGeneric.LocalArc.local_arc_of_max_three_tangent
import Submission.Work.Smooth.BoxGeneric.LocalSurface.isLocalArcAt_of_uniqueActiveFace
import Submission.Work.Smooth.BoxGeneric.LocalSurface.isLocalArcAt_of_corner
import Submission.Work.Smooth.BoxGeneric.LocalSurface.isLocalArcAt_of_tangentialCorner
import Submission.Work.Smooth.BoxGeneric.LocalSurface.isLocalArcAt_of_vertex_tangent
import Submission.Work.Smooth.BoxGeneric.Case.exists_active_signed_of_not_vertex
import Submission.Work.Smooth.BoxGeneric.FaceRegular.ae_comp_affine
import Submission.Work.Smooth.BoxGeneric.FaceRegular.ae_face_regular_of_sardCoord
import Submission.Work.Smooth.BoxGeneric.PlaneTransverse.ae_transverseSphere_coord
import Submission.Work.Smooth.BoxGeneric.PlaneTransverse.ae_transverseSphere_face
import Submission.Work.Smooth.BoxGeneric.PlaneTransverse.ae_transversePlane
import Submission.Work.Smooth.BoxGeneric.PlaneTransverse.ae_pair_regular
import Submission.Work.Smooth.BoxGeneric.PlaneTransverse.ae_pair_regular_pardonSlice
import Submission.Work.Smooth.BoxGeneric.Sard.Reduce
import Submission.Work.Smooth.BoxGeneric.Sard.criticalValues_null_of_contDiffTwo_periodic
import Submission.Work.Smooth.BoxGeneric.Sard.SardCoord
import Submission.Work.Smooth.BoxGeneric.Sard.criticalValues_null_of_contDiffTwo_periodic_pair
import Submission.Work.Smooth.BoxGeneric.Sard.exists_isOpen_volume_image_restrictedCritical_null
import Submission.Work.Smooth.BoxGeneric.AeCorner.ae_transverseCorner_of_regularBisector
import Submission.Work.Smooth.BoxGeneric.AeBox
import Submission.Work.Smooth.BoxGeneric.AeMain
import Submission.Work.Smooth.BoxGeneric.Final
import Submission.Work.Smooth.BoxGeneric.AeCentre
import Submission.Work.Smooth.BoxGeneric.AeVertex
import Submission.Work.Smooth.BoxGeneric.Obstruction.not_nonempty_sphereSlicing_of_local_singleton

/-!
# `Work.Smooth.BoxGeneric` — general position of the box-norm level sets

This is the entry point of the chapter: importing this module gives the whole area.  See
`Submission/Work/Smooth/BoxGeneric/README.md` for the prose account of what is proved, of which
inputs remain, and of how the pieces fit.

Pardon's box norm `Submission.boxNorm c σ y = max_i |y (σ i) - c (σ i)| / boxSide i` is only
piecewise smooth, so the smooth level-set theory of the sibling chapter
`Submission/Work/Smooth/Morse` does not apply to it directly.  This chapter proves the
almost-everywhere general position of its level sets on the surface `F = ψ(standard torus)`,
`ψ : Submission.Diffeo`.

## The target, and the main theorem

`Work.BoxShrink.AeSlicedAll` — for every `ψ`, `c` and `σ`, for almost every `s` the box sphere
`{y | boxNorm c σ y = s}` meets `F` in finitely many pairwise disjoint simple closed curves, each
bounding a disc inside the sphere, nested, and covering every loop of `F` inside the sphere
(`Work.InnermostDisk.SphereSlicing`) — **proved here from exactly two classical inputs**:

* `Work.Smooth.BoxGeneric.aeSlicedAll_of_classicalInput :
  BoxGenericClassicalInput → Work.BoxShrink.AeSlicedAll`, where `BoxGenericClassicalInput` bundles
  `Work.Smooth.Morse.CompactOneManifoldInput` (the classification of compact `1`-manifolds, absent
  from Mathlib) and `Work.Topology.Classical.JordanSchoenfliesSphere` (the sphere-side
  Jordan–Schoenflies theorem, which the sibling chapter `Submission/Work/Smooth/SphereJordan`
  derives from the planar Jordan–Schoenflies theorem);
* equivalently `Work.Smooth.BoxGeneric.aeSlicedAll_of_classify_of_jordanSchoenflies`,
  `..._of_planeHypothesis` and `..._of_classicalInput`, and the pointwise forms
  `aeSliced_unconditional` / `aeSliced_of_classicalInput`.

## What is proved (all unconditional, no `sorry`, no `axiom`)

* **two-dimensional Sard** (`Sard/`): the critical values of a periodic `C²` function `ℝ² → ℝ` are
  null (`Sard.criticalValues_null_of_contDiffTwo_periodic`), and the same for maps into `ℝ²`
  (`Sard.criticalValues_null_of_contDiffTwo_periodic_pair`); hence **`Sard.sardCoord ψ :
  SardCoord ψ`** — almost every level of every coordinate function on the surface is a regular
  value.  Everything smooth in the chapter is deduced from this.
* **the local models of the level set** (`LocalArc/`, `LocalSurface/`): at a point of the level set
  where a single signed face is tight (`isLocalArcAt_of_uniqueActiveFace`), where two tight faces
  meet with an invertible pair of derivatives (`isLocalArcAt_of_corner`), where the two tight faces
  are tangent with a critical bisector (`isLocalArcAt_of_tangentialCorner`), or where all three
  faces are tight and the vertex ray is tangent (`isLocalArcAt_of_vertex_tangent`, whose `ℝ²`
  content is `LocalArc.local_arc_of_max_three_tangent`), the level set is locally an arc.
* **the a.e. corner transversality** (`AeCorner/`): for almost every level, a corner at which the
  two faces and their difference are regular is transverse.
* **the vertex strata are handled** (`AeVertex.lean`): at a vertex point the box sphere is locally
  the corner cone `C = {v | max_i v_i = 0}`; if the vertex-ray direction is tangent to the surface
  the level set is locally the two branches of `T_yF ∩ C`, a "V" — a topological arc; and if it is
  not tangent then the vertex level is an *isolated* point of the corresponding ray-intersection set,
  and isolated points of a subset of `ℝ` are countable.  Hence **`AeVertexTangent ψ c σ`** holds for
  every `ψ, c, σ` and no vertex genericity input is needed.
* **`Work.Smooth.BoxGeneric.ae_isCompact_isLocalArc_levelSet_unconditional`** — for almost every
  level the level set is compact and locally an arc, i.e. a compact `1`-manifold, with **no input at
  all** (the "essential content" of the chapter);
  **`ae_isCircleUnion_levelSet_unconditional`** — the same with the classification of compact
  `1`-manifolds, giving a finite disjoint union of simple closed curves;
  **`aeTransverseBox_unconditional`** — `AeTransverseBox ψ c σ`: for almost every `s` the box sphere
  meets `F` in general position in the sense of `Work.Topology.SphereSlicing.TransverseSphere`.
* **item 4** (`PlaneTransverse/`): for almost every `u` the cutting plane
  `{y | y (σ 2) = c (σ 2) + u}` is transverse to `F` in the sense of
  `Work.Smooth.Plane.TransversePlane` (`PlaneTransverse.ae_transversePlane_pardonSlice`), for almost
  every `s` each of the six face planes is (`ae_transversePlane_face`), and for almost every *pair*
  `(u, s)` the cutting plane and the box sphere are in joint general position
  (`PlaneTransverse.ae_pair_regular_pardonSlice`).

## The remaining inputs — the complete list

* `Work.Smooth.Morse.CompactOneManifoldInput` — a compact subset of the surface which is locally an
  arc is a finite disjoint union of simple closed curves (the classification of compact
  `1`-manifolds, absent from Mathlib; it is the sibling chapter's input);
* `Work.Topology.Classical.JordanSchoenfliesSphere` — the sphere-side Jordan–Schoenflies theorem,
  derived in the sibling chapter `Submission/Work/Smooth/SphereJordan` from the planar
  Jordan–Schoenflies theorem (`Work.Smooth.SphereJordan.PlaneHypothesis`).

Superseded earlier interfaces (still present, with the same conclusions from stronger hypotheses):
`AeNoVertex` and the theorems of `AeMain.lean` and `AeCentre.lean` that use it, and
`AeBox.isLocalArc_levelSet` / `AeBox.aeTransverseBox_of_inputs` (which use `AeTransverseCorner`).
The general fact that an *isolated* intersection point obstructs a slicing is recorded in
`Obstruction.not_nonempty_sphereSlicing_of_local_singleton`.
-/

open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.BoxGeneric

end Work.Smooth.BoxGeneric
