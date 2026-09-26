import Submission.Work.Smooth.OneManifold.Defs
import Submission.Work.Smooth.OneManifold.Basic
import Submission.Work.Smooth.OneManifold.Bridge
import Submission.Work.Smooth.OneManifold.exists_finite_component_decomposition
import Submission.Work.Smooth.OneManifold.Classify
import Submission.Work.Smooth.OneManifold.Counterexample
import Submission.Work.Smooth.OneManifold.levelSet_isLocallyEuclidean_of_regularValue
import Submission.Work.Smooth.OneManifold.Consumer
import Submission.Work.Smooth.OneManifold.Plane.Basic
import Submission.Work.Smooth.OneManifold.Plane.Corner
import Submission.Work.Smooth.OneManifold.Plane.Tangential
import Submission.Work.Smooth.OneManifold.isLocallyEuclidean_image_of_param
import Submission.Work.Smooth.OneManifold.boxNorm_eq_max_of_corner
import Submission.Work.Smooth.OneManifold.isLocallyEuclideanAt_of_uniqueActiveFace
import Submission.Work.Smooth.OneManifold.isLocallyEuclideanAt_of_corner
import Submission.Work.Smooth.OneManifold.isLocallyEuclideanAt_of_tangentialCorner
import Submission.Work.Smooth.OneManifold.isLocallyEuclidean_of_forall
import Submission.Work.Smooth.OneManifold.isLocallyEuclidean_levelSet_of_regular
import Submission.Work.Smooth.OneManifold.ae_isLocallyEuclidean_levelSet
import Submission.Work.Smooth.OneManifold.ae_niceLevel
import Submission.Work.Smooth.OneManifold.Plane.Vertex
import Submission.Work.Smooth.OneManifold.isLocallyEuclideanAt_of_vertex_tangent
import Submission.Work.Smooth.OneManifold.isLocallyEuclidean_levelSet_of_regular_tangent
import Submission.Work.Smooth.OneManifold.ae_unconditional

/-!
# The classification of compact one-dimensional subsets of a surface

This chapter proves the classification input of the smooth level-set chapter of the Pardon
project, and records that the input as originally stated is false.

## The result

A compact subset `Z` of the surface `F = torus ψ` which is *locally Euclidean of dimension one*
(`Work.Smooth.OneManifold.IsLocallyEuclidean`: every point of `Z` has a neighbourhood in `Z`
homeomorphic to `ℝ`) is a finite disjoint union of embedded circles of `F`
(`Work.Smooth.Morse.IsCircleUnion`):

* `Work.Smooth.OneManifold.isCircleUnion_of_isCompact_of_isLocallyEuclidean` —
  `IsLocallyEuclidean Z → IsCompact Z → Z ⊆ F → IsCircleUnion ψ Z`;
* `Work.Smooth.OneManifold.isCircleUnion_of_isCompact_of_isLocalArcEmbedding` — the same with the
  local hypothesis `Work.Smooth.OneManifold.IsLocalArcEmbedding`, the repaired form of
  `Work.Smooth.Morse.IsLocalArc` in which the local arc is required to be an embedding onto the
  piece of `Z` it cuts out;
* `Work.Smooth.OneManifold.IsLocallyEuclidean.of_subset` — local Euclideanness restricts to
  relatively open subsets;
* `Work.Smooth.OneManifold.isLocalArcEmbedding_of_isLocallyEuclidean` — conversely, a locally
  Euclidean `Z ⊆ F` satisfies the repaired arc hypothesis, so on a subset of the surface
  `IsLocalArcEmbedding ψ Z` and `IsLocallyEuclidean Z` are equivalent;
* `Work.Smooth.OneManifold.levelSet_isLocallyEuclidean_of_regularValue`,
  `Work.Smooth.OneManifold.levelSet_isCircleUnion_of_regularValue` — the producer and the
  end-to-end statement for regular level sets of a `C¹` function on the surface;
* `Work.Smooth.OneManifold.exists_finite_component_decomposition` — a compact locally Euclidean
  `Z` is the union of finitely many pairwise disjoint, compact, preconnected components, each of
  which is again locally Euclidean;
* `Work.Smooth.OneManifold.exists_closedCurve_of_component` — a compact connected locally Euclidean
  `C ⊆ F` is a circle of `F` (parametrised by an injective `2π`-periodic curve).

The classification is `Work.Smooth.OneManifold.Classify.CompactOneManifoldInput'`:

`∀ Z, Z ⊆ F → IsCompact Z → IsLocallyEuclidean Z → IsCircleUnion ψ Z`.

## The literal statement is false

`Work.Smooth.Morse.CompactOneManifoldInput ψ` asks for the same conclusion from the weaker
hypothesis `Work.Smooth.Morse.IsLocalArc ψ Z`, which allows the neighbourhood `U = Set.univ`
(so that *any* compact set which is the image of an injective continuous map `ℝ → ℝ³` qualifies,
even when it does not lie on the surface `F`):

* `Work.Smooth.OneManifold.isLocalArc_range_of_injective_continuous` — `IsLocalArc ψ (range γ)` for
  every injective continuous `γ : ℝ → ℝ³`, with `U = Set.univ`;
* `Work.Smooth.OneManifold.exists_compact_isLocalArc_not_isCircleUnion` — the "figure eight"
  (two tangent unit circles in the plane `z = 100`) is compact, is `IsLocalArc` for every `ψ`, and
  is not a circle union (it misses the surface `F = torus ψ` entirely when `ψ` is the identity);
* `Work.Smooth.OneManifold.not_compactOneManifoldInput` —
  `¬ ∀ ψ, Work.Smooth.Morse.CompactOneManifoldInput ψ`.

## What to use instead

`Work.Smooth.OneManifold.CompactOneManifoldInput' ψ` is the corrected input; for the level sets of
a `C¹` function the classification is available unconditionally at a regular value as
`Work.Smooth.OneManifold.levelSet_isCircleUnion_of_regularValue`.  The general bridge from the
arc-based local hypothesis to the local `1`-manifold structure is
`Work.Smooth.OneManifold.isLocallyEuclidean_of_isLocalArcEmbedding` (and conversely
`Work.Smooth.OneManifold.isLocalArcEmbedding_of_isLocallyEuclidean`).
-/

open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.OneManifold

end Work.Smooth.OneManifold
