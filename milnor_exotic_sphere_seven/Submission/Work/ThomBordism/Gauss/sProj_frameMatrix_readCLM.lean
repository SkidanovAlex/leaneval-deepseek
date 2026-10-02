import Mathlib
import Submission.Work.ThomBordism.gaussDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism.Gauss

open Work.ThomBordism.PontryaginThom Work.ThomBordism.Grassmann Work.Tubular
open scoped BigOperators

/-- **The `sProj`-coordinates of a vector expanded in a frame.**  For a frame `F : Fin k → ℝ^{8+k}`
and a coordinate vector `v : ℝ^k`, the `S`-matrix of `ambFrame F` applied to `v` is the `S`-part of
the ambient vector `∑ j, v j • F j`.  This is the linear-algebra identity behind
`matLin (frameMatrix S (ambFrame F)) = sProj S ∘ insCLM`. -/
theorem matLin_frameMatrix_ambFrame {k : ℕ} (S : ChartIdx k 8)
    (F : Fin k → Work.Tubular.Euc (8 + k)) (v : Amb k) :
    matLin (frameMatrix S (ambFrame F)) v = sProj S (∑ j, eucToFun k v j • F j) := by
  ext i
  rw [matLin_apply, sProj_apply]
  simp only [Matrix.mulVec_apply, Matrix.row_apply, dotProduct,
    WithLp.ofLp_sum, Finset.sum_apply, eucToFun_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [frameMatrix_ambFrame, sProj_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem sProj_frameMatrix_readCLM {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (S : Work.ThomBordism.Grassmann.ChartIdx k 8)
    (t : Work.ThomBordism.PontryaginThom.CoverIdx V k) {x : V.pt}
    (hx : x ∈ ND.D.baseSet t) (w : Work.Tubular.Euc (8 + k))
    (hw : w ∈ Work.Tubular.normalSpace E x) :
    Work.ThomBordism.Grassmann.matLin
        (Work.ThomBordism.Grassmann.frameMatrix S
          (Work.ThomBordism.Gauss.ambFrame (Work.Tubular.orthFrame E ND t x)))
        (Work.Tubular.readCLM E ND t x w) = Work.ThomBordism.Gauss.sProj S w := by
  rw [matLin_frameMatrix_ambFrame S (orthFrame E ND t x) (readCLM E ND t x w),
    ← insCLM_apply E ND t x (readCLM E ND t x w)]
  rw [insCLM_readCLM_of_mem E ND t hx hw]

end Work.ThomBordism.Gauss
