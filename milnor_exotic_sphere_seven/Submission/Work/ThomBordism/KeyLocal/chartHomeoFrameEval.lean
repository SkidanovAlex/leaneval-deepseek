import Mathlib
import Submission.Work.ThomBordism.frameEval_realThomClassOf
import Submission.Work.ThomBordism.Grassmann.PlaneCoord

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The chart homeomorphism reads the frame evaluation as the frame gauge

For the tautological oriented bundle `γ = tautologicalBundle k 10` over `G̃r_k(ℝ^{k+10})`, a chart
`S` of the Grassmannian, a frame `σ` whose plane `ogMk k 10 σ` lies in the base set of `S`, and a
coordinate vector `v : Amb k`, the chart homeomorphism of the piece over `S` reads the point
`feFrameEvalPiece S σ hP v` (the point of `γ` over the plane of `σ` whose ambient vector is
`∑ v_j σ_j`) as the pair of the base point and the *constant* gauge `feFrameGauge S σ`.

The content is the two transition-function facts already available in the library:

* `Work.ThomBordism.Grassmann.coordChange_toECoordAt` — the transition function of the tautological
  bundle takes the coordinate in the chart of the plane to the coordinate in *any* chart `S`
  containing `P` (the `coordChange` of `tautologicalBundle` is the orientation-corrected one, so
  this is a statement about the corrected trivialisations);
* `Work.ThomBordism.feToECoordAt_frameLI` — the `S`-coordinate of the ambient vector
  `∑ v_j σ_j` is `matLin (orientMat S (ogMk k 10 σ) * frameMatrix S σ.1) v`, which is
  definitionally `feFrameGauge S σ v`.
-/

namespace Work.ThomBordism.KeyLocal

theorem chartHomeoFrameEval {k : ℕ} (S : Work.ThomBordism.Grassmann.ChartIdx k 10)
    (σ : Work.ThomBordism.Grassmann.Stiefel k 10)
    (hP : Work.ThomBordism.Grassmann.ogMk k 10 σ
      ∈ (Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S)
    (v : Work.ThomBordism.Grassmann.Amb k) :
    ((Work.Thom.chartHomeo (Work.ThomBordism.Grassmann.tautologicalBundle k 10) k
        (Work.Thom.oriE k) S ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S)
        subset_rfl :
        C(↥((Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj ⁻¹'
            (Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S),
          ↥((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S) ×
            Work.ThomBordism.Grassmann.Amb k))
      (Work.ThomBordism.feFrameEvalPiece S σ hP v))
      = (⟨Work.ThomBordism.Grassmann.ogMk k 10 σ, hP⟩,
          Work.ThomBordism.feFrameGauge S σ v) := by
  show Work.Thom.chartHomeo (Work.ThomBordism.Grassmann.tautologicalBundle k 10) k
        (Work.Thom.oriE k) S
        ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S)
        subset_rfl (Work.ThomBordism.feFrameEvalPiece S σ hP v)
      = (⟨Work.ThomBordism.Grassmann.ogMk k 10 σ, hP⟩,
          Work.ThomBordism.feFrameGauge S σ v)
  rw [Work.Thom.chartHomeo_apply]
  refine Prod.ext ?_ ?_
  · refine Subtype.ext ?_
    show (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj
        (Work.ThomBordism.frameEval k σ v) = Work.ThomBordism.Grassmann.ogMk k 10 σ
    exact Work.ThomBordism.frameEval_base k σ v
  · show Work.Thom.oriE k
        ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).coordChange
          ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).indexAt
            (Work.ThomBordism.Grassmann.ogMk k 10 σ)) S
          (Work.ThomBordism.Grassmann.ogMk k 10 σ)
          (Work.ThomBordism.Grassmann.toECoordAt
            ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).indexAt
              (Work.ThomBordism.Grassmann.ogMk k 10 σ))
            (Work.ThomBordism.Grassmann.ogMk k 10 σ)
            (Work.ThomBordism.frameLI k σ v)))
      = Work.ThomBordism.feFrameGauge S σ v
    rw [Work.ThomBordism.Grassmann.coordChange_toECoordAt S
      (Work.ThomBordism.Grassmann.ogMk k 10 σ) hP (Work.ThomBordism.frameLI k σ v)
      (Work.ThomBordism.frameVec_memPlane k σ v)]
    rw [Work.ThomBordism.feToECoordAt_frameLI S σ v]
    rfl

end Work.ThomBordism.KeyLocal
