import Submission.Work.Tubular.DiscManifold.HalfModel
import Submission.Work.Tubular.NormalDiscManifold
import Submission.Work.Tubular.Global

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# The normal disc bundle is a smooth manifold with boundary (half-space model)

This file packages `HalfModel.lean` into the statement that the normal disc bundle `D_ε(ν)` of an
embedding `E : V ↪ ℝ^{8+k}` is a `C¹` manifold with boundary modelled on
`EuclideanHalfSpace (8 + k)`, i.e. `Work.Tubular.NormalDiscManifold`.
-/

open scoped Manifold ContDiff Topology
open Function Filter
open OpenPartialHomeomorph

open Work.ThomBordism.PontryaginThom (EmbeddingData CoverIdx)

namespace Work.Tubular

open Work.ThomBordism Work.ThomBordism.PontryaginThom Work.SignatureBordism

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ} [NeZero k] {ε : ℝ}

/-- **The normal disc bundle is a smooth manifold with boundary**, modelled on the half-space: the
charted space is obtained from `discChartedSpace` by the reindexing `Λ`. -/
theorem disc_isManifold_half {E : EmbeddingData V (8 + k)} (C : TubeChart E ε)
    (R : DiscManifold.HalfModelReindex k) :
    letI := chartedSpaceOfModelHomeo (discChartedSpace C) R.Λ
    IsManifold (modelWithCornersEuclideanHalfSpace (8 + k)) 1 (NormalDiscSub E ε) := by
  letI := chartedSpaceOfModelHomeo (discChartedSpace C) R.Λ
  refine isManifold_of_contDiffOn (modelWithCornersEuclideanHalfSpace (8 + k)) 1
    (NormalDiscSub E ε) ?_
  intro e e' he he'
  obtain ⟨-, ⟨p, rfl⟩, rfl⟩ := he
  obtain ⟨-, ⟨q, rfl⟩, rfl⟩ := he'
  have hΨsymm : (R.Λ.symm.toOpenPartialHomeomorph).symm = R.Λ.toOpenPartialHomeomorph := by
    rw [Homeomorph.symm_toOpenPartialHomeomorph R.Λ]
    simp
  have htrans : (discChart C p ≫ₕ R.Λ.symm.toOpenPartialHomeomorph).symm ≫ₕ
      (discChart C q ≫ₕ R.Λ.symm.toOpenPartialHomeomorph)
      = R.Λ.toOpenPartialHomeomorph ≫ₕ
        ((discChart C p).symm ≫ₕ discChart C q) ≫ₕ R.Λ.symm.toOpenPartialHomeomorph := by
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, hΨsymm]
    rw [OpenPartialHomeomorph.trans_assoc]
    rw [← OpenPartialHomeomorph.trans_assoc (discChart C p).symm (discChart C q)
      R.Λ.symm.toOpenPartialHomeomorph]
  rw [htrans]
  exact contDiffOn_conj_chart R (transitionSmooth C p q)

/-- **The normal disc bundle of a tubular neighbourhood is a `NormalDiscManifold`.** -/
theorem nonempty_normalDiscManifold_of_tubeChart {E : EmbeddingData V (8 + k)} {ε : ℝ}
    (C : TubeChart E ε) :
    Nonempty (NormalDiscManifold (V := V) k E ε) := by
  obtain ⟨R⟩ := DiscManifold.exists_halfModelReindex k
  refine ⟨{ charted := chartedSpaceOfModelHomeo (discChartedSpace C) R.Λ, isManifold := ?_ }⟩
  exact disc_isManifold_half C R

end

end Work.Tubular
