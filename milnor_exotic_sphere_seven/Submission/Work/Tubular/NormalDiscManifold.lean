import Submission.Work.Tubular.tubeCollapseClass_span_top
import Mathlib.Geometry.Manifold.Instances.Real

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# The disc bundle as a smooth manifold with boundary — the interface

The disc bundle `D_ε(ν)` of the normal bundle of an embedded `8`-manifold `V ↪ ℝ^{8+k}` should be a
compact smooth `(8+k)`-manifold with boundary `S_ε(ν)` (the sphere bundle), modelled on the
half-space.  This is the input of the ORIENT relative-fundamental-class theorem
(`Work.Orient.Boundary.RelativeFundamentalClassExists`), i.e. of step (T)(a) of README §32.

This module only *states* the interface; `Submission/Work/Tubular/normalDiscSub_charted.lean`
supplies the instance (the atlas comes from the charts of `V` and the trivialising sets of `ν`:
over a chart the disc bundle is `ℝ⁸ × [0,ε] × S^{k-1}`-ish).  The sphere-bundle part is already
charted in `Submission/Work/Tubular/PuncturedDiscPair/sphSub_charted.lean`, which is the precedent
to imitate.
-/

open scoped Manifold Topology
open Work.ThomBordism.PontryaginThom (EmbeddingData)

namespace Work.Tubular

noncomputable section

variable {V : Work.ThomBordism.Man8}

/-- **The disc bundle as a charted space modelled on the half-space, carrying a `C^∞` manifold
structure with boundary.** -/
structure NormalDiscManifold (k : ℕ) (E : EmbeddingData V (8 + k)) (ε : ℝ) where
  /-- the atlas of the disc bundle, modelled on the half-space of dimension `8 + k` -/
  charted : ChartedSpace (EuclideanHalfSpace (8 + k)) (NormalDiscSub E ε)
  /-- the atlas makes the disc bundle a `C^∞` manifold with boundary -/
  isManifold : letI : ChartedSpace (EuclideanHalfSpace (8 + k)) (NormalDiscSub E ε) := charted
    IsManifold (modelWithCornersEuclideanHalfSpace (8 + k)) 1 (NormalDiscSub E ε)

end

end Work.Tubular
