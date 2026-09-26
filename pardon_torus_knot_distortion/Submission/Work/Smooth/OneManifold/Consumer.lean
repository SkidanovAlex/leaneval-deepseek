import Mathlib
import Submission.Work.Smooth.OneManifold.Classify
import Submission.Work.Smooth.OneManifold.levelSet_isLocallyEuclidean_of_regularValue
import Submission.Work.Smooth.Morse.Surface.isCompact_levelSet
import Submission.Work.Smooth.BoxGeneric.Bridge

/-!
# The classification applied to the level sets of the challenge

The classification `isCircleUnion_of_isCompact_of_isLocallyEuclidean` needs the local hypothesis
`IsLocallyEuclidean` (locally a `1`-manifold) and the containment `Z ⊆ F`.  For the level sets of
the smooth level-set chapter both are available — the containment is built into the definition and
the local structure is the one produced by the implicit function theorem
(`levelSet_isLocallyEuclidean_of_regularValue`) — so we obtain the statement in the shape in which
the chapter `Submission/Work/Smooth/BoxGeneric` uses it:

`levelSet_isCircleUnion_of_regularValue`:
a regular level set `F ∩ {g = t}` of a `C¹` function on the surface is a finite disjoint union of
embedded circles of `F`.

This is the drop-in replacement for the use of `Work.Smooth.Morse.CompactOneManifoldInput` at a
*regular* level (`Work.Smooth.Morse.Regular.levelSet_isLocalArc_of_regularValue` supplies the local
arc and this file upgrades it).  For the box norm (only `C^{0,1}`) the same upgrade must be done by
hand on the faces of the box; see the README.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.OneManifold

noncomputable section

/-- **A regular level set of `g|_F` is a finite disjoint union of embedded circles of `F`.** -/
theorem levelSet_isCircleUnion_of_regularValue (ψ : Submission.Diffeo) {g : R3 → ℝ}
    (hg : ContDiff ℝ 1 g) {t : ℝ} (hreg : Work.Smooth.Morse.IsRegularValue ψ g t) :
    IsCircleUnion ψ (Work.Smooth.Morse.levelSet ψ g t) :=
  isCircleUnion_of_isCompact_of_isLocallyEuclidean ψ
    (Work.Smooth.Morse.levelSet_subset_carrier ψ g t)
    (Work.Smooth.Morse.Surface.isCompact_levelSet ψ hg.continuous t)
    (levelSet_isLocallyEuclidean_of_regularValue ψ hg hreg)

/-- **The `BoxGeneric` bridge with the corrected hypothesis.**

`Work.Smooth.BoxGeneric.transverseSphere_of_compact_isLocalArc` produces the transversality witness
`Work.Topology.SphereSlicing.TransverseSphere (torus ψ) S` from a compact `S` whose trace on the
surface is locally an arc.  Its hypothesis `Work.Smooth.Morse.IsLocalArc` is too weak (see
`not_compactOneManifoldInput`); this is the same statement with the trace required to be *locally
Euclidean of dimension one*, which is the hypothesis the level-set analysis actually provides
(`levelSet_isLocallyEuclidean_of_regularValue`, and the corresponding statement for the box norm). -/
theorem transverseSphere_of_isCompact_isLocallyEuclidean (ψ : Submission.Diffeo) {S : Set R3}
    (hcomp : IsCompact (S ∩ (Work.Smooth.Morse.torus ψ).carrier))
    (hloc : IsLocallyEuclidean (S ∩ (Work.Smooth.Morse.torus ψ).carrier)) :
    Work.Topology.SphereSlicing.TransverseSphere (Work.Smooth.Morse.torus ψ) S :=
  Work.Smooth.BoxGeneric.transverseSphere_of_isCircleUnion
    (Z := S ∩ (Work.Smooth.Morse.torus ψ).carrier)
    (isCircleUnion_of_isCompact_of_isLocallyEuclidean ψ inter_subset_right hcomp hloc)
    inter_subset_left subset_rfl

end

end Work.Smooth.OneManifold
