import Mathlib
import Submission.Work.Tubular.NormalDiscManifold
import Submission.Work.Tubular.DiscManifold.Defs
import Submission.Work.SignatureBordism.BallBoundary
import Submission.Work.Tubular.PuncturedDiscPair.sphSub_charted
import Submission.Work.Tubular.exists_euclidean_normalBundle
import Submission.Work.Tubular.normalThomSpace_scale
import Submission.Work.Tubular.DiscManifold.Manifold
import Submission.Work.Tubular.DiscManifold.Transfer

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Tubular

/-- **The normal disc bundle of an embedded `8`-manifold is a smooth manifold with boundary.**

For a compact smooth `8`-manifold `V` embedded in `ℝ^{8+k}` (`k ≥ 1`), the closed `ε`-disc bundle
`D_ε(ν)` of the normal bundle carries the structure of a `C¹` manifold with boundary modelled on
`EuclideanHalfSpace (8+k)`.  This is the manifold structure of step (T)(a) of the Milnor
exotic-sphere project (the ORIENT relative-fundamental-class theorem).

The proof has two cases.  If `V.pt` is nonempty, the tubular neighbourhood theorem gives a
`TubeChart E ε₀`, from which `Work.Tubular.nonempty_normalDiscManifold_of_tubeChart` produces the
manifold structure at radius `ε₀`; the structure at the requested radius `ε` is obtained by
transferring along the scaling homeomorphism `D_{ε₀}(ν) ≃ D_ε(ν)`.  If `V.pt` is empty, so is
`D_ε(ν)`, and the structure is the empty one. -/
theorem exists_normalDiscManifold {V : Work.ThomBordism.Man8} {k : ℕ} (hk : 1 ≤ k)
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ} (hε : 0 < ε) :
    Nonempty (Work.Tubular.NormalDiscManifold (V := V) k E ε) := by
  haveI : NeZero k := ⟨by omega⟩
  by_cases hV : Nonempty V.pt
  · haveI := hV
    obtain ⟨ε₀, hε₀, ⟨C⟩⟩ := hasTubularNeighbourhood E
    obtain ⟨M⟩ := nonempty_normalDiscManifold_of_tubeChart (V := V) C
    let e : NormalDiscSub E ε₀ ≃ₜ NormalDiscSub E ε :=
      normalDiscScaleHomeomorph E hε₀ hε
    let T : ChartedSpace (EuclideanHalfSpace (8 + k)) (NormalDiscSub E ε) :=
      chartedSpaceOfHomeomorph M.charted e
    refine ⟨{ charted := T, isManifold := ?_ }⟩
    letI : ChartedSpace (EuclideanHalfSpace (8 + k)) (NormalDiscSub E ε₀) := M.charted
    letI : ChartedSpace (EuclideanHalfSpace (8 + k)) (NormalDiscSub E ε) := T
    haveI : HasGroupoid (NormalDiscSub E ε₀)
        (contDiffGroupoid 1 (modelWithCornersEuclideanHalfSpace (8 + k))) :=
      M.isManifold.toHasGroupoid
    haveI : HasGroupoid (NormalDiscSub E ε)
        (contDiffGroupoid 1 (modelWithCornersEuclideanHalfSpace (8 + k))) :=
      hasGroupoid_chartedSpaceOfHomeomorph M.charted e
        (contDiffGroupoid 1 (modelWithCornersEuclideanHalfSpace (8 + k)))
    exact IsManifold.mk' _ _ _
  · haveI : IsEmpty (NormalDiscSub E ε) := ⟨fun q => hV ⟨q.1.1.1⟩⟩
    let T : ChartedSpace (EuclideanHalfSpace (8 + k)) (NormalDiscSub E ε) :=
      ChartedSpace.empty (EuclideanHalfSpace (8 + k)) (NormalDiscSub E ε)
    refine ⟨{ charted := T, isManifold := ?_ }⟩
    letI : ChartedSpace (EuclideanHalfSpace (8 + k)) (NormalDiscSub E ε) := T
    haveI : HasGroupoid (NormalDiscSub E ε)
        (contDiffGroupoid 1 (modelWithCornersEuclideanHalfSpace (8 + k))) :=
      ⟨fun {_ _} he _ => absurd he (Set.notMem_empty _)⟩
    exact IsManifold.mk' _ _ _

end Work.Tubular
