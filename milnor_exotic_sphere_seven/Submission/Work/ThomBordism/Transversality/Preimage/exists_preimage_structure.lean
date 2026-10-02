import Mathlib
import Submission.Work.ThomBordism.Transversality.Pullback
import Submission.Work.ThomBordism.Transversality.Sard.Strat
import Submission.Work.Surgery.BoundaryInstances
import Submission.Work.ThomBordism.Transversality.Preimage.Manifold

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism.Transversality.Preimage

open scoped Manifold Topology ContDiff
open Function Set Manifold
open ModelWithCorners

/-- **The preimage theorem.**  A smooth map `F : M → E` into a `CoreTarget`, transverse to the core,
whose boundary restriction is transverse as well, has a transverse preimage `F ⁻¹' X.core` which is
a compact smooth `9`-manifold with boundary, whose boundary is the end preimage of the core. -/
theorem exists_preimage_structure {k : ℕ}
    (X : Work.ThomBordism.Transversality.CoreTarget ((8 + k) + 1) k)
    (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      Work.ThomBordism.Transversality.smoothHeight M]
    [CompactSpace M] [T2Space M] (F : M → X.E)
    (hF : ContMDiff (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin ((8 + k) + 1))))
      Work.ThomBordism.Transversality.smoothHeight F)
    (htr : Work.ThomBordism.Transversality.IsTransverse X
      (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) F)
    (hbnd : ∀ (x : M)
      (hx : x ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M),
      X.Φ (F x) = 0 →
      Manifold.IsSubmersionAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (8 + k))))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
        Work.ThomBordism.Transversality.smoothHeight
        (fun y : ↥((modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).boundary M) =>
          X.Φ (F (y : M))) ⟨x, hx⟩) :
    ∃ (W : Type) (_ : TopologicalSpace W) (_ : ChartedSpace (EuclideanHalfSpace 9) W)
      (_ : IsManifold (modelWithCornersEuclideanHalfSpace 9)
        Work.ThomBordism.Transversality.smoothHeight W)
      (_ : CompactSpace W) (_ : T2Space W)
      (hW : W ≃ₜ ↥(F ⁻¹' X.core)),
      (∀ w : W, w ∈ (modelWithCornersEuclideanHalfSpace 9).boundary W ↔
        (hW w : M) ∈ Work.ThomBordism.Transversality.endPreimage
          (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) F) := by
  classical
  let S : CoreSetup k :=
    { X := X, M := M, topologicalSpace := inferInstance, chartedSpace := inferInstance,
      isManifold := inferInstance, compactSpace := inferInstance, t2Space := inferInstance,
      F := F, contMDiff := hF, isTransverse := htr, bndSubmersion := hbnd }
  refine ⟨S.Pre, inferInstance, CoreSetup.instChartedSpace S, CoreSetup.instIsManifold S,
    CoreSetup.instCompactSpace S, inferInstance, Homeomorph.refl S.Pre, ?_⟩
  intro w
  rw [CoreSetup.mem_boundary_iff S w, Work.ThomBordism.Transversality.mem_endPreimage]
  exact ⟨fun h => ⟨h, CoreSetup.zero_mem_coreMap S w⟩, fun h => h.1⟩

end Work.ThomBordism.Transversality.Preimage
