import Mathlib
import Submission.Work.Tubular.exists_euclidean_normalBundle
import Submission.Work.ThomBordism.orthFrameOrientation
import Submission.Work.ThomBordism.Grassmann.Grassmannian
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.ThomBordism.Grassmann.Frame
import Submission.Work.ThomBordism.PontryaginThom.NormalData
import Submission.Work.ThomBordism.gaussDefs
import Submission.Work.ThomBordism.Gauss.sProj_frameMatrix_readCLM
import Submission.Work.ThomBordism.Gauss.continuousOn_phiCLM
import Submission.Work.ThomBordism.Gauss.continuousOn_phiInvCLM
import Submission.Work.Gen.EulerToolkit

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Gauss classifying map of an embedded `8`-manifold

`Work.ThomBordism.gaussClassifying`: for an embedding `E : V ↪ ℝ^{8+k}` of a closed oriented smooth
`8`-manifold with `k ≥ 1` there are a normal data `ND` of the embedding and a continuous **Gauss
map** `gauss : V → G̃r_k(ℝ^{k+8})` whose pulled-back tautological oriented `k`-plane bundle is
isomorphic to the normal bundle `ν = normalBundle E ND` of the embedding.

* `Work.ThomBordism.Gauss.gauss` (in `gaussDefs.lean`) is the Gauss map: the chartwise orthonormal
  frames `orthFrame E ND i x` of `ν_x` are corrected by a sign cocycle `sigma` so that the corrected
  frames are related by elements of `SO(k)`; the corrected frame defines a point of the oriented
  Grassmannian, independently of the chart (`Work.ThomBordism.Gauss.gaussFun_eq`).
* `Work.ThomBordism.Gauss.phiCLM` is the gauge transformation, in the coordinates of a chart `S` of
  the Grassmannian and a chart `t` of the normal bundle, from the tautological `S`-coordinates to
  the normal `t`-coordinates: `φ = (frameMatrix S (ambFrame (orthFrame t x)))⁻¹ · orientMat S (gauss x)`.
  Its compatibility with the two bundles' transition functions is
  `normalBundle_coordChange_comp_phiCLM` and `phiCLM_comp_coordChangeO` (and the inverse statements
  `phiInvCLM_comp_transFun`, `coordChangeO_comp_phiInvCLM`); continuity is the delegated
  `continuousOn_phiCLM`/`continuousOn_phiInvCLM`, and the inverse laws are
  `phiInvCLM_comp_phiCLM`/`phiCLM_comp_phiInvCLM` in `gaussDefs.lean`.  The bundle isomorphism is
  then `Work.Thom.nonempty_bundleIso_of_gauge`.
* The geometric input relating the two coordinate systems is the delegated
  `sProj_frameMatrix_readCLM`: the orthonormal frame of the chart `t` reads the `S`-coordinates of a
  vector of the normal plane.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped Manifold ContDiff Topology

namespace Work.ThomBordism

open Work.ThomBordism.Gauss Work.ThomBordism.PontryaginThom Work.ThomBordism.Grassmann
open Work.Tubular

noncomputable section

variable {V : Man8} {k : ℕ}

theorem phiCLM_apply' (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) (S : ChartIdx k 8)
    (t : CoverIdx V k) (x : V.pt) (v : Amb k) :
    phiCLM E ND S t x v
      = matLin ((frameMatrix S (ambFrame (orthFrame E ND t x)))⁻¹)
          (matLin (orientMat S (gauss E ND x)) v) := by
  rw [phiCLM, phiMat, matLin_mul_apply]

theorem phiInvCLM_apply' (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (S : ChartIdx k 8) (t : CoverIdx V k) (x : V.pt) (v : Amb k) :
    phiInvCLM E ND S t x v
      = matLin (orientMat S (gauss E ND x))
          (matLin (frameMatrix S (ambFrame (orthFrame E ND t x))) v) := by
  rw [phiInvCLM, phiInvMat, matLin_mul_apply]

theorem coordChange_gauss (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (S S' : ChartIdx k 8) (t : CoverIdx V k) {x : V.pt}
    (hS' : gauss E ND x ∈ baseSet S') (ht : x ∈ ND.D.baseSet t) :
    coordChange S' S (gauss E ND x)
      = matLin (frameMatrix S (ambGframe E ND t x)
          * (frameMatrix S' (ambGframe E ND t x))⁻¹) := by
  have hg : gauss E ND x
      = Quotient.mk'' (⟨ambGframe E ND t x, orthonormal_ambGframe E ND t ht⟩ : Stiefel k 8) :=
    gauss_eq_ogMk E ND t ht
  rw [hg, coordChange_mk, coordChangeAux,
    dif_pos (det_frameMatrix_ambGframe_ne_zero E ND S' t ht hS')]

/-! ## The naturality in the target chart -/

theorem normalBundle_coordChange_comp_phiCLM (E : EmbeddingData V (8 + k))
    (ND : NormalData V k E.e) (S : ChartIdx k 8) (t t' : CoverIdx V k) {x : V.pt}
    (hS : gauss E ND x ∈ baseSet S) (ht : x ∈ ND.D.baseSet t) (ht' : x ∈ ND.D.baseSet t') :
    ((normalBundle E ND).coordChange t t' x).comp (phiCLM E ND S t x)
      = phiCLM E ND S t' x := by
  rw [normalBundle_coordChange, transFun_of_mem E ND t t' x ⟨ht, ht'⟩]
  refine ContinuousLinearMap.ext fun v => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, phiCLM_apply',
    phiCLM_apply']
  set c : Amb k := matLin ((frameMatrix S (ambFrame (orthFrame E ND t x)))⁻¹)
      (matLin (orientMat S (gauss E ND x)) v) with hc
  have hdet : (frameMatrix S (ambFrame (orthFrame E ND t x))).det ≠ 0 :=
    det_frameMatrix_orthFrame_ne_zero E ND S t ht hS
  have hdet' : (frameMatrix S (ambFrame (orthFrame E ND t' x))).det ≠ 0 :=
    det_frameMatrix_orthFrame_ne_zero E ND S t' ht' hS
  have hsp : matLin (orientMat S (gauss E ND x)) v = sProj S (insCLM E ND t x c) := by
    have h := sProj_frameMatrix_readCLM E ND S t ht (insCLM E ND t x c) (insCLM_mem E ND t ht c)
    rw [readCLM_insCLM E ND t ht c, hc, matLin_mul_inv_apply hdet] at h
    exact h
  have hsp' : matLin (frameMatrix S (ambFrame (orthFrame E ND t' x)))
      (readCLM E ND t' x (insCLM E ND t x c)) = sProj S (insCLM E ND t x c) :=
    sProj_frameMatrix_readCLM E ND S t' ht' (insCLM E ND t x c) (insCLM_mem E ND t ht c)
  rw [hsp, ← hsp', matLin_inv_mul_apply hdet' (readCLM E ND t' x (insCLM E ND t x c))]

theorem phiInvCLM_comp_transFun (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (S : ChartIdx k 8) (t t' : CoverIdx V k) {x : V.pt}
    (hS : gauss E ND x ∈ baseSet S) (ht : x ∈ ND.D.baseSet t) (ht' : x ∈ ND.D.baseSet t') :
    (phiInvCLM E ND S t x).comp (transFun E ND t' t x) = phiInvCLM E ND S t' x := by
  rw [transFun_of_mem E ND t' t x ⟨ht', ht⟩]
  refine ContinuousLinearMap.ext fun v => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, phiInvCLM_apply',
    phiInvCLM_apply']
  have h1 := sProj_frameMatrix_readCLM E ND S t ht (insCLM E ND t' x v) (insCLM_mem E ND t' ht' v)
  have h2 := sProj_frameMatrix_readCLM E ND S t' ht' (insCLM E ND t' x v) (insCLM_mem E ND t' ht' v)
  rw [readCLM_insCLM E ND t' ht' v] at h2
  rw [h1, h2]

/-! ## The naturality in the source chart -/

theorem phiCLM_comp_coordChangeO (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (S S' : ChartIdx k 8) (t : CoverIdx V k) {x : V.pt}
    (hS : gauss E ND x ∈ baseSet S) (hS' : gauss E ND x ∈ baseSet S') (ht : x ∈ ND.D.baseSet t) :
    (phiCLM E ND S t x).comp (coordChangeO S' S (gauss E ND x)) = phiCLM E ND S' t x := by
  have hdet : (frameMatrix S (ambFrame (orthFrame E ND t x))).det ≠ 0 :=
    det_frameMatrix_orthFrame_ne_zero E ND S t ht hS
  have hunitF' : IsUnit (frameMatrix S' (ambGframe E ND t x)).det :=
    isUnit_iff_ne_zero.mpr (det_frameMatrix_ambGframe_ne_zero E ND S' t ht hS')
  have hkey : (frameMatrix S (ambFrame (orthFrame E ND t x)))⁻¹
        * frameMatrix S (ambGframe E ND t x)
      = (frameMatrix S' (ambFrame (orthFrame E ND t x)))⁻¹
        * frameMatrix S' (ambGframe E ND t x) := by
    rw [frameMatrix_ambGframe E ND S t x, frameMatrix_ambGframe E ND S' t x,
      Matrix.nonsing_inv_mul_cancel_left (frameMatrix S (ambFrame (orthFrame E ND t x)))
        (gauge E ND t x) (isUnit_iff_ne_zero.mpr hdet),
      Matrix.nonsing_inv_mul_cancel_left (frameMatrix S' (ambFrame (orthFrame E ND t x)))
        (gauge E ND t x) (isUnit_iff_ne_zero.mpr
          (det_frameMatrix_orthFrame_ne_zero E ND S' t ht hS'))]
  have hkey2 : ((frameMatrix S (ambFrame (orthFrame E ND t x)))⁻¹
        * frameMatrix S (ambGframe E ND t x))
        * (frameMatrix S' (ambGframe E ND t x))⁻¹
      = (frameMatrix S' (ambFrame (orthFrame E ND t x)))⁻¹ := by
    calc ((frameMatrix S (ambFrame (orthFrame E ND t x)))⁻¹
          * frameMatrix S (ambGframe E ND t x))
          * (frameMatrix S' (ambGframe E ND t x))⁻¹
        = (frameMatrix S' (ambFrame (orthFrame E ND t x)))⁻¹
            * (frameMatrix S' (ambGframe E ND t x) * (frameMatrix S' (ambGframe E ND t x))⁻¹) := by
          rw [hkey, Matrix.mul_assoc]
      _ = (frameMatrix S' (ambFrame (orthFrame E ND t x)))⁻¹ * 1 := by
          rw [Matrix.mul_nonsing_inv _ hunitF']
      _ = (frameMatrix S' (ambFrame (orthFrame E ND t x)))⁻¹ := Matrix.mul_one _
  refine ContinuousLinearMap.ext fun v => ?_
  rw [ContinuousLinearMap.comp_apply, phiCLM_apply', coordChangeO_apply,
    coordChange_gauss E ND S S' t hS' ht, phiCLM_apply']
  have hO : matLin (orientMat S (gauss E ND x))
      (matLin (orientMat S (gauss E ND x))
        (matLin (frameMatrix S (ambGframe E ND t x)
          * (frameMatrix S' (ambGframe E ND t x))⁻¹) (matLin (orientMat S' (gauss E ND x)) v)))
      = matLin (frameMatrix S (ambGframe E ND t x)
          * (frameMatrix S' (ambGframe E ND t x))⁻¹) (matLin (orientMat S' (gauss E ND x)) v) :=
    matLin_orientMat_self E ND S hS _
  rw [hO]
  calc matLin ((frameMatrix S (ambFrame (orthFrame E ND t x)))⁻¹)
        (matLin (frameMatrix S (ambGframe E ND t x)
          * (frameMatrix S' (ambGframe E ND t x))⁻¹) (matLin (orientMat S' (gauss E ND x)) v))
      = matLin ((frameMatrix S (ambFrame (orthFrame E ND t x)))⁻¹
          * (frameMatrix S (ambGframe E ND t x)
            * (frameMatrix S' (ambGframe E ND t x))⁻¹)) (matLin (orientMat S' (gauss E ND x)) v)
        := (matLin_mul_apply _ _ _).symm
    _ = matLin (((frameMatrix S (ambFrame (orthFrame E ND t x)))⁻¹
          * frameMatrix S (ambGframe E ND t x))
          * (frameMatrix S' (ambGframe E ND t x))⁻¹) (matLin (orientMat S' (gauss E ND x)) v) := by
        rw [← Matrix.mul_assoc]
    _ = matLin (frameMatrix S' (ambFrame (orthFrame E ND t x)))⁻¹
          (matLin (orientMat S' (gauss E ND x)) v) := by rw [hkey2]

theorem coordChangeO_comp_phiInvCLM (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (S S' : ChartIdx k 8) (t : CoverIdx V k) {x : V.pt}
    (hS : gauss E ND x ∈ baseSet S) (hS' : gauss E ND x ∈ baseSet S') (ht : x ∈ ND.D.baseSet t) :
    (coordChangeO S S' (gauss E ND x)).comp (phiInvCLM E ND S t x) = phiInvCLM E ND S' t x := by
  have hdet : (frameMatrix S (ambFrame (orthFrame E ND t x))).det ≠ 0 :=
    det_frameMatrix_orthFrame_ne_zero E ND S t ht hS
  have hunitG : IsUnit (frameMatrix S (ambFrame (orthFrame E ND t x))).det :=
    isUnit_iff_ne_zero.mpr hdet
  have hunitH : IsUnit (gauge E ND t x).det := gauge_isUnit_det E ND t x
  have hkey1 : (frameMatrix S (ambGframe E ND t x))⁻¹
        * frameMatrix S (ambFrame (orthFrame E ND t x)) = (gauge E ND t x)⁻¹ := by
    rw [frameMatrix_ambGframe E ND S t x]
    calc ((frameMatrix S (ambFrame (orthFrame E ND t x)) * gauge E ND t x))⁻¹
          * frameMatrix S (ambFrame (orthFrame E ND t x))
        = ((gauge E ND t x)⁻¹ * (frameMatrix S (ambFrame (orthFrame E ND t x)))⁻¹)
            * frameMatrix S (ambFrame (orthFrame E ND t x)) := by
          rw [inv_mul_eq' hdet (gauge_det_ne_zero E ND t x)]
      _ = (gauge E ND t x)⁻¹
            * ((frameMatrix S (ambFrame (orthFrame E ND t x)))⁻¹
              * frameMatrix S (ambFrame (orthFrame E ND t x))) := Matrix.mul_assoc _ _ _
      _ = (gauge E ND t x)⁻¹ * 1 := by rw [Matrix.nonsing_inv_mul _ hunitG]
      _ = (gauge E ND t x)⁻¹ := Matrix.mul_one _
  have hkey2 : frameMatrix S' (ambGframe E ND t x)
        * ((frameMatrix S (ambGframe E ND t x))⁻¹
          * frameMatrix S (ambFrame (orthFrame E ND t x)))
      = frameMatrix S' (ambFrame (orthFrame E ND t x)) := by
    calc frameMatrix S' (ambGframe E ND t x)
          * ((frameMatrix S (ambGframe E ND t x))⁻¹
            * frameMatrix S (ambFrame (orthFrame E ND t x)))
        = (frameMatrix S' (ambFrame (orthFrame E ND t x)) * gauge E ND t x)
            * (gauge E ND t x)⁻¹ := by
          rw [hkey1, frameMatrix_ambGframe E ND S' t x]
      _ = frameMatrix S' (ambFrame (orthFrame E ND t x)) * (gauge E ND t x * (gauge E ND t x)⁻¹) :=
          Matrix.mul_assoc _ _ _
      _ = frameMatrix S' (ambFrame (orthFrame E ND t x)) * 1 := by
          rw [Matrix.mul_nonsing_inv _ hunitH]
      _ = frameMatrix S' (ambFrame (orthFrame E ND t x)) := Matrix.mul_one _
  refine ContinuousLinearMap.ext fun v => ?_
  rw [ContinuousLinearMap.comp_apply, coordChangeO_apply,
    coordChange_gauss E ND S' S t hS ht, phiInvCLM_apply', phiInvCLM_apply']
  have hO : matLin (orientMat S (gauss E ND x))
      (matLin (orientMat S (gauss E ND x))
        (matLin (frameMatrix S (ambFrame (orthFrame E ND t x))) v))
      = matLin (frameMatrix S (ambFrame (orthFrame E ND t x))) v :=
    matLin_orientMat_self E ND S hS _
  rw [hO]
  have hF : (orientMat S' (gauss E ND x)
        * (frameMatrix S' (ambGframe E ND t x) * (frameMatrix S (ambGframe E ND t x))⁻¹))
        * frameMatrix S (ambFrame (orthFrame E ND t x))
      = orientMat S' (gauss E ND x) * frameMatrix S' (ambFrame (orthFrame E ND t x)) := by
    calc (orientMat S' (gauss E ND x)
          * (frameMatrix S' (ambGframe E ND t x) * (frameMatrix S (ambGframe E ND t x))⁻¹))
          * frameMatrix S (ambFrame (orthFrame E ND t x))
        = orientMat S' (gauss E ND x)
            * ((frameMatrix S' (ambGframe E ND t x) * (frameMatrix S (ambGframe E ND t x))⁻¹)
              * frameMatrix S (ambFrame (orthFrame E ND t x))) := Matrix.mul_assoc _ _ _
      _ = orientMat S' (gauss E ND x)
            * (frameMatrix S' (ambGframe E ND t x)
              * ((frameMatrix S (ambGframe E ND t x))⁻¹
                * frameMatrix S (ambFrame (orthFrame E ND t x)))) := by rw [Matrix.mul_assoc]
      _ = orientMat S' (gauss E ND x) * frameMatrix S' (ambFrame (orthFrame E ND t x)) := by
          rw [hkey2]
  calc matLin (orientMat S' (gauss E ND x))
        (matLin (frameMatrix S' (ambGframe E ND t x) * (frameMatrix S (ambGframe E ND t x))⁻¹)
          (matLin (frameMatrix S (ambFrame (orthFrame E ND t x))) v))
      = matLin (orientMat S' (gauss E ND x)
          * (frameMatrix S' (ambGframe E ND t x) * (frameMatrix S (ambGframe E ND t x))⁻¹))
          (matLin (frameMatrix S (ambFrame (orthFrame E ND t x))) v) := (matLin_mul_apply _ _ _).symm
    _ = matLin ((orientMat S' (gauss E ND x)
          * (frameMatrix S' (ambGframe E ND t x) * (frameMatrix S (ambGframe E ND t x))⁻¹))
          * frameMatrix S (ambFrame (orthFrame E ND t x))) v := (matLin_mul_apply _ _ v).symm
    _ = matLin (orientMat S' (gauss E ND x) * frameMatrix S' (ambFrame (orthFrame E ND t x))) v := by
        rw [hF]
    _ = matLin (orientMat S' (gauss E ND x)) (matLin (frameMatrix S' (ambFrame (orthFrame E ND t x))) v) :=
        matLin_mul_apply _ _ v

/-- A normal data of the embedding. -/
noncomputable def gaussND {V : Man8} {k : ℕ} (E : EmbeddingData V (8 + k)) :
    NormalData V k E.e :=
  Classical.choice (Work.ThomBordism.PontryaginThom.exists_normalData_of_immersion E.e
    (E.smooth.of_le (by simp)) E.injective_mfderiv)

theorem gaussClassifying {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (hk : 1 ≤ k) :
    ∃ (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
      (gauss : C(V.pt, Work.ThomBordism.Grassmann.OG k 8)),
      Nonempty (Work.Thom.BundleIso
        (Work.Thom.bundleComap (Work.ThomBordism.Grassmann.tautologicalBundle k 8) gauss)
        (Work.Tubular.normalBundle E ND)) := by
  refine ⟨gaussND E, gauss E (gaussND E), ?_⟩
  refine Work.Thom.nonempty_bundleIso_of_gauge
    (Z := Work.Thom.bundleComap (tautologicalBundle k 8) (gauss E (gaussND E)))
    (Z' := normalBundle E (gaussND E))
    (fun S t x => phiCLM E (gaussND E) S t x)
    (fun S t x => phiInvCLM E (gaussND E) S t x) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i i'
    exact continuousOn_phiCLM E (gaussND E) i i'
  · intro i i'
    exact continuousOn_phiInvCLM E (gaussND E) i i'
  · intro i t t' x hi ht ht'
    exact normalBundle_coordChange_comp_phiCLM E (gaussND E) i t t' hi ht ht'
  · intro i t i' x hi hi' ht
    rw [Work.Thom.bundleComap_coordChange]
    exact phiCLM_comp_coordChangeO E (gaussND E) i i' t hi hi' ht
  · intro i t t' x hi ht ht'
    exact phiInvCLM_comp_transFun E (gaussND E) i t t' hi ht ht'
  · intro i t i' x hi hi' ht
    rw [Work.Thom.bundleComap_coordChange]
    exact coordChangeO_comp_phiInvCLM E (gaussND E) i i' t hi hi' ht
  · intro i i' b v hx
    rw [← ContinuousLinearMap.comp_apply,
      phiInvCLM_comp_phiCLM E (gaussND E) i i' hx.1
        (det_frameMatrix_orthFrame_ne_zero E (gaussND E) i i' hx.2 hx.1),
      ContinuousLinearMap.one_apply]
  · intro i i' b v hx
    rw [← ContinuousLinearMap.comp_apply,
      phiCLM_comp_phiInvCLM E (gaussND E) i i' hx.1
        (det_frameMatrix_orthFrame_ne_zero E (gaussND E) i i' hx.2 hx.1),
      ContinuousLinearMap.one_apply]

end

end Work.ThomBordism
