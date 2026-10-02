import Mathlib
import Submission.Work.ThomBordism.frameClassDefs
import Submission.Work.ThomBordism.coorientationRef
import Submission.Work.Thom.realThomClassOf_natural
import Submission.Work.Thom.Orientation.Mpun_gaugeEnd_neg
import Submission.Work.Thom.isOrientedOver_of_det_pos
import Submission.Work.ThomBordism.FrameSigns.gaugeOrientationPos
import Submission.Work.Thom.localThomOfOrientedCover_subset
import Submission.Work.ThomBordism.gtdUWith_frameEval

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000


set_option maxHeartbeats 3200000

namespace Work.ThomBordism

open CategoryTheory
open Work.ThomBordism.Grassmann

noncomputable section

variable {k : ℕ}

/-- The chart of the plane of a frame `σ`. -/
abbrev fePlaneChart (k : ℕ) (σ : Stiefel k 10) : ChartIdx k 10 :=
  (tautologicalBundle k 10).indexAt (ogMk k 10 σ)

/-- The piece of the base over the chart of the plane of `σ`. -/
abbrev fePlanePiece (k : ℕ) (σ : Stiefel k 10) : Set (OG k 10) :=
  (tautologicalBundle k 10).baseSet (fePlaneChart k σ)

/-- The identification `ℝ^k ≅ pt × ℝ^k` underlying `Work.ThomBordism.stdModelGen`. -/
def fePtAmb (k : ℕ) : C(Amb k, PUnit × Amb k) :=
  ⟨fun v => (PUnit.unit, v), continuous_const.prodMk continuous_id⟩

theorem feStdModelGen_eq_ptAmb (k : ℕ) :
    stdModelGen k
      = (Work.Thom.relCohMap (fePtAmb k) (framePunct k) (Work.Thom.Punct PUnit k)
          (fun _ hv => hv) ℤ k).hom (Work.Thom.Mpun k PUnit) := rfl

/-! ## The chart reading of a frame combination -/

/-- `matLin` is multiplicative, in the applied form. -/
theorem feMatLin_mul_apply {k : ℕ} (M N : Matrix (Fin k) (Fin k) ℝ) (v : Amb k) :
    matLin (M * N) v = matLin M (matLin N v) := by
  rw [matLin_mul, ContinuousLinearMap.comp_apply]

/-- A matrix is the sum of its columns, weighted by a vector. -/
theorem feSum_smul_col {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    (∑ j, v j • M.col j) = M.mulVec v := by
  funext i
  rw [Matrix.mulVec_apply_eq_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, Matrix.col_apply]
  ring

/-- The `S`-coordinates of `∑ j, v j • σ j` are the matrix product `frameMatrix S σ *ᵥ v`. -/
theorem feCoordProj_frameLI (S : ChartIdx k 10) (σ : Stiefel k 10) (v : Amb k) :
    coordProj S (WithLp.ofLp (frameLI k σ v))
      = (frameMatrix S σ.1).mulVec (WithLp.ofLp v) := by
  have h1 : WithLp.ofLp (frameLI k σ v)
      = ∑ j, (v j) • WithLp.ofLp (σ.1 j) := by
    rw [frameLI_apply, frameLM_apply, WithLp.ofLp_sum]
    exact Finset.sum_congr rfl fun j _ => WithLp.ofLp_smul _ _ _
  rw [h1, map_sum]
  have h2 : ∀ j : Fin k, coordProj S ((v j) • WithLp.ofLp (σ.1 j))
      = (v j) • (frameMatrix S σ.1).col j := fun j => by
    simp only [map_smul, coordProj_frame S σ j, Matrix.mulVec_single_one]
  rw [Finset.sum_congr rfl fun j _ => h2 j]
  exact feSum_smul_col (frameMatrix S σ.1) (WithLp.ofLp v)

/-- **The chart reading of the frame combination `∑ j, v j • σ j`** in the chart of the plane of
`σ`, computed as `orientMat * frameMatrix` applied to `v`. -/
theorem feToECoordAt_frameLI (S : ChartIdx k 10) (σ : Stiefel k 10) (v : Amb k) :
    toECoordAt S (ogMk k 10 σ) (frameLI k σ v)
      = matLin (orientMat S (ogMk k 10 σ) * frameMatrix S σ.1) v := by
  have h : matLin (orientMat S (ogMk k 10 σ) * frameMatrix S σ.1) v
      = matLin (orientMat S (ogMk k 10 σ))
          (WithLp.toLp 2 ((frameMatrix S σ.1).mulVec (WithLp.ofLp v))) := by
    rw [feMatLin_mul_apply]
    exact congrArg (matLin (orientMat S (ogMk k 10 σ))) (matLin_apply (frameMatrix S σ.1) v)
  rw [h, toECoordAt, feCoordProj_frameLI S σ v]

/-! ## The frame gauge and its determinant -/

/-- The gauge (family of linear endomorphisms of `ℝ^k`) by which the chart homeomorphism of the
chart of the plane of `σ` reads the frame evaluation `frameEval σ`. -/
def feFrameGauge (S : ChartIdx k 10) (σ : Stiefel k 10) : Work.Thom.Gauge k :=
  matLin (orientMat S (ogMk k 10 σ) * frameMatrix S σ.1)

theorem feFrameGauge_apply (S : ChartIdx k 10) (σ : Stiefel k 10) (v : Amb k) :
    feFrameGauge S σ v = matLin (orientMat S (ogMk k 10 σ) * frameMatrix S σ.1) v := rfl

/-- **The frame gauge is orientation preserving**: the sign gauge `orientMat` cancels the sign of
the chart determinant of `σ`. -/
theorem feDet_frameGauge_pos (S : ChartIdx k 10) (σ : Stiefel k 10)
    (hσ : σ ∈ chartSet S) :
    0 < LinearMap.det (feFrameGauge S σ).toLinearMap := by
  have hmem : ogMk k 10 σ ∈ (tautologicalBundle k 10).baseSet S :=
    (mem_baseSet_iff S σ).mpr hσ
  have hε : frameSign S (ogMk k 10 σ) * frameSign S (ogMk k 10 σ) = 1 :=
    frameSign_mul_self S (ogMk k 10 σ) hmem
  have hd : (frameMatrix S σ.1).det
      = frameSign S (ogMk k 10 σ) * |(frameMatrix S σ.1).det| :=
    frameMatrix_det_eq_sign S σ hσ
  rw [feFrameGauge, det_matLin, Matrix.det_mul, orientMat_det, hd, ← mul_assoc, hε, one_mul]
  exact abs_pos.mpr hσ

/-! ## The frame evaluation inside the chart piece -/

/-- The frame evaluation, regarded as a map into the piece of the total space over the chart `S`
of its plane. -/
def feFrameEvalPiece (S : ChartIdx k 10) (σ : Stiefel k 10)
    (hP : ogMk k 10 σ ∈ (tautologicalBundle k 10).baseSet S) :
    C(Amb k, ↥((tautologicalBundle k 10).proj ⁻¹' (tautologicalBundle k 10).baseSet S)) where
  toFun v := ⟨frameEval k σ v, by
    show (frameEval k σ v).1 ∈ (tautologicalBundle k 10).baseSet S
    rw [frameEval_base]
    exact hP⟩
  continuous_toFun := Continuous.subtype_mk (continuous_frameEval_snd k σ) (fun v => by
    show (frameEval k σ v).1 ∈ (tautologicalBundle k 10).baseSet S
    rw [frameEval_base]
    exact hP)

theorem feFrameEvalPiece_apply (S : ChartIdx k 10) (σ : Stiefel k 10)
    (hP : ogMk k 10 σ ∈ (tautologicalBundle k 10).baseSet S) (v : Amb k) :
    ((feFrameEvalPiece S σ hP v : ↥((tautologicalBundle k 10).proj ⁻¹'
      (tautologicalBundle k 10).baseSet S)) : (tautologicalBundle k 10).TotalSpace)
      = frameEval k σ v := rfl

/-- **The chart homeomorphism of the chart of the plane of `σ` reads the frame evaluation as the
constant gauge `feFrameGauge S σ`** (pointwise form). -/
theorem chartHomeo_feFrameEvalPiece_apply (S : ChartIdx k 10) (σ : Stiefel k 10)
    (hP : ogMk k 10 σ ∈ (tautologicalBundle k 10).baseSet S)
    (hS : S = (tautologicalBundle k 10).indexAt (ogMk k 10 σ)) (v : Amb k) :
    Work.Thom.chartHomeo (tautologicalBundle k 10) k (Work.Thom.oriE k) S
        ((tautologicalBundle k 10).baseSet S) subset_rfl (feFrameEvalPiece S σ hP v)
      = (⟨ogMk k 10 σ, hP⟩, feFrameGauge S σ v) := by
  subst hS
  rw [Work.Thom.chartHomeo_apply]
  refine Prod.ext ?_ ?_
  · refine Subtype.ext ?_
    show (tautologicalBundle k 10).proj (frameEval k σ v) = ogMk k 10 σ
    exact frameEval_base k σ v
  · show Work.Thom.oriE k ((tautologicalBundle k 10).coordChange
          ((tautologicalBundle k 10).indexAt (ogMk k 10 σ))
          ((tautologicalBundle k 10).indexAt (ogMk k 10 σ)) (ogMk k 10 σ)
          (toECoordAt ((tautologicalBundle k 10).indexAt (ogMk k 10 σ)) (ogMk k 10 σ)
            (frameLI k σ v)))
        = feFrameGauge ((tautologicalBundle k 10).indexAt (ogMk k 10 σ)) σ v
    rw [show (tautologicalBundle k 10).coordChange
          ((tautologicalBundle k 10).indexAt (ogMk k 10 σ))
          ((tautologicalBundle k 10).indexAt (ogMk k 10 σ)) (ogMk k 10 σ)
          (toECoordAt ((tautologicalBundle k 10).indexAt (ogMk k 10 σ)) (ogMk k 10 σ)
            (frameLI k σ v))
        = toECoordAt ((tautologicalBundle k 10).indexAt (ogMk k 10 σ)) (ogMk k 10 σ)
            (frameLI k σ v) from
      (tautologicalBundle k 10).coordChange_self _ _ hP _]
    show toECoordAt ((tautologicalBundle k 10).indexAt (ogMk k 10 σ)) (ogMk k 10 σ)
        (frameLI k σ v)
      = feFrameGauge ((tautologicalBundle k 10).indexAt (ogMk k 10 σ)) σ v
    exact feToECoordAt_frameLI _ σ v

/-- **The chart homeomorphism of the chart of the plane of `σ` reads the frame evaluation as the
constant gauge `feFrameGauge S σ`** (map form). -/
theorem chartHomeo_feFrameEvalPiece (S : ChartIdx k 10) (σ : Stiefel k 10)
    (hP : ogMk k 10 σ ∈ (tautologicalBundle k 10).baseSet S)
    (hS : S = (tautologicalBundle k 10).indexAt (ogMk k 10 σ)) :
    ((Work.Thom.chartHomeo (tautologicalBundle k 10) k (Work.Thom.oriE k) S
        ((tautologicalBundle k 10).baseSet S) subset_rfl) :
        C(↥((tautologicalBundle k 10).proj ⁻¹' (tautologicalBundle k 10).baseSet S),
          ↥((tautologicalBundle k 10).baseSet S) × Amb k)).comp
      (feFrameEvalPiece S σ hP)
      = (Work.Thom.gaugeEnd
          (fun _ : ↥((tautologicalBundle k 10).baseSet S) => feFrameGauge S σ) continuous_const).comp
        (⟨fun v : Amb k => (⟨ogMk k 10 σ, hP⟩, v), continuous_const.prodMk continuous_id⟩) := by
  apply ContinuousMap.ext
  intro v
  rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply]
  show Work.Thom.chartHomeo (tautologicalBundle k 10) k (Work.Thom.oriE k) S
      ((tautologicalBundle k 10).baseSet S) subset_rfl (feFrameEvalPiece S σ hP v)
    = (⟨ogMk k 10 σ, hP⟩, feFrameGauge S σ
        ((⟨fun v : Amb k => (⟨ogMk k 10 σ, hP⟩, v),
          continuous_const.prodMk continuous_id⟩ : C(Amb k, ↥((tautologicalBundle k 10).baseSet S) × Amb k)) v).2)
  rw [show ((⟨fun v : Amb k => (⟨ogMk k 10 σ, hP⟩, v),
        continuous_const.prodMk continuous_id⟩ : C(Amb k, ↥((tautologicalBundle k 10).baseSet S) × Amb k)) v)
      = (⟨ogMk k 10 σ, hP⟩, v) from rfl]
  exact chartHomeo_feFrameEvalPiece_apply S σ hP hS v

/-! ## The main theorem -/

theorem frameEval_realThomClassOf (k : ℕ) (hk : 1 ≤ k)
    (horiO : ∀ (i j : Work.ThomBordism.Grassmann.ChartIdx k 10)
      (x : ↥((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet i
        ∩ (Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet j)),
      0 < LinearMap.det (((Work.ThomBordism.Grassmann.tautologicalBundle k 10).coordChange i j
        (x : Work.ThomBordism.Grassmann.OG k 10)).toLinearMap)) :
    ∀ σ : Work.ThomBordism.Grassmann.Stiefel k 10,
      (Work.Thom.relCohMap (Work.ThomBordism.frameEvalMap k σ)
        (Work.ThomBordism.framePunct k)
        (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
        (Work.ThomBordism.frameEvalMap_mem k σ) ℤ k).hom
        ((Work.Thom.realThomClassOf hk (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
          horiO).τ)
      = Work.ThomBordism.stdModelGen k := by
  intro σ
  classical
  have hmem : ogMk k 10 σ ∈ fePlanePiece k σ :=
    (tautologicalBundle k 10).mem_baseSet_at (ogMk k 10 σ)
  have hσc : σ ∈ chartSet (fePlaneChart k σ) := (mem_baseSet_iff (fePlaneChart k σ) σ).mp hmem
  -- the frame evaluation into the piece over the chart of the plane
  let Φ : C(Amb k, ↥((tautologicalBundle k 10).proj ⁻¹' fePlanePiece k σ)) :=
    feFrameEvalPiece (fePlaneChart k σ) σ hmem

  -- the chart homeomorphism of the piece over the chart of the plane
  let ch : C(↥((tautologicalBundle k 10).proj ⁻¹' fePlanePiece k σ),
      ↥(fePlanePiece k σ) × Amb k) :=
    (Work.Thom.chartHomeo (tautologicalBundle k 10) k (Work.Thom.oriE k)
      (fePlaneChart k σ) (fePlanePiece k σ) subset_rfl :
      C(↥((tautologicalBundle k 10).proj ⁻¹' fePlanePiece k σ),
        ↥(fePlanePiece k σ) × Amb k))
  -- the constant gauge by which the chart reads the frame evaluation
  let gE : C(↥(fePlanePiece k σ) × Amb k, ↥(fePlanePiece k σ) × Amb k) :=
    Work.Thom.gaugeEnd (fun _ : ↥(fePlanePiece k σ) => feFrameGauge (fePlaneChart k σ) σ)
      continuous_const
  -- the constant base map `v ↦ (ogMk σ, v)`
  let base : C(Amb k, ↥(fePlanePiece k σ) × Amb k) :=
    ⟨fun v => (⟨ogMk k 10 σ, hmem⟩, v), continuous_const.prodMk continuous_id⟩
  -- the two membership statements of the two maps of the gauge factorisation
  let chmem : ∀ p ∈ Work.Thom.pieceZero (tautologicalBundle k 10) (fePlanePiece k σ),
      ch p ∈ Work.Thom.Punct ↥(fePlanePiece k σ) k :=
    Work.Thom.chartHomeo_mem (tautologicalBundle k 10) k (Work.Thom.oriE k)
      (fePlaneChart k σ) (fePlanePiece k σ) subset_rfl
  let gmem : ∀ p ∈ Work.Thom.Punct ↥(fePlanePiece k σ) k,
      gE p ∈ Work.Thom.Punct ↥(fePlanePiece k σ) k :=
    Work.Thom.gaugeEnd_mem (fun _ : ↥(fePlanePiece k σ) => feFrameGauge (fePlaneChart k σ) σ)
      continuous_const
      (fun _ => Work.Thom.gaugeEnd_bijective_of_det_ne_zero
        (feFrameGauge (fePlaneChart k σ) σ)
        (ne_of_gt (feDet_frameGauge_pos (fePlaneChart k σ) σ hσc)))
  have hΦmem : ∀ v ∈ framePunct k,
      Φ v ∈ Work.Thom.pieceZero (tautologicalBundle k 10) (fePlanePiece k σ) := by
    intro v hv
    exact frameEvalMap_mem k σ v hv
  have hincl_mem : ∀ v ∈ framePunct k,
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥((tautologicalBundle k 10).proj ⁻¹' fePlanePiece k σ),
          (tautologicalBundle k 10).TotalSpace)) (Φ v)
        ∈ Work.Thom.zeroComplement (tautologicalBundle k 10) :=
    fun v hv => hΦmem v hv
  -- Step A: the restriction of the canonical class to the piece is the chart class
  have hA : (Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥((tautologicalBundle k 10).proj ⁻¹' fePlanePiece k σ),
          (tautologicalBundle k 10).TotalSpace))
        (Work.Thom.pieceZero (tautologicalBundle k 10) (fePlanePiece k σ))
        (Work.Thom.zeroComplement (tautologicalBundle k 10))
        (fun _ hp => hp) ℤ k).hom
        ((Work.Thom.realThomClassOf hk (tautologicalBundle k 10) horiO).τ)
      = (Work.Thom.localThomOfChart (tautologicalBundle k 10) k (Work.Thom.oriE k)
          (fePlaneChart k σ) (fePlanePiece k σ) subset_rfl).τ := by
    have hcomp : ((⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥((tautologicalBundle k 10).proj ⁻¹' (Set.univ : Set (OG k 10))),
            (tautologicalBundle k 10).TotalSpace)).comp
          (Work.Thom.pieceIncl (tautologicalBundle k 10) (fePlanePiece k σ) Set.univ
            (Set.subset_univ _)))
        = (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥((tautologicalBundle k 10).proj ⁻¹' fePlanePiece k σ),
              (tautologicalBundle k 10).TotalSpace)) := by
      apply ContinuousMap.ext
      intro p
      rfl
    have hspec := Work.Thom.realThomClassOf_spec hk (tautologicalBundle k 10) horiO
    have hsub := Work.Thom.localThomOfOrientedCover_subset hk (tautologicalBundle k 10) horiO
      (fePlaneChart k σ) (hW := subset_rfl)
    have hcompA := Work.Thom.relCohMap_compA_apply
      (A := Work.Thom.pieceZero (tautologicalBundle k 10) (fePlanePiece k σ))
      (B := Work.Thom.pieceZero (tautologicalBundle k 10) (Set.univ : Set (OG k 10)))
      (C := Work.Thom.zeroComplement (tautologicalBundle k 10))
      (Work.Thom.pieceIncl (tautologicalBundle k 10) (fePlanePiece k σ) Set.univ (Set.subset_univ _))
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥((tautologicalBundle k 10).proj ⁻¹' (Set.univ : Set (OG k 10))),
          (tautologicalBundle k 10).TotalSpace))
      (fun _ hp => hp) (fun _ hp => hp) (fun _ hp => hp) ℤ k
      ((Work.Thom.realThomClassOf hk (tautologicalBundle k 10) horiO).τ)
    have hpd : (Work.Cohomology.pdCohMap
          (TopCat.of (tautologicalBundle k 10).TotalSpace)
          (Work.Thom.zeroComplement (tautologicalBundle k 10))
          ((tautologicalBundle k 10).proj ⁻¹' (Set.univ : Set (OG k 10)))
          ((tautologicalBundle k 10).proj ⁻¹' fePlanePiece k σ)
          (Set.preimage_mono (Set.subset_univ _)) k)
        = (Work.Thom.relCohMap
            (Work.Thom.pieceIncl (tautologicalBundle k 10) (fePlanePiece k σ) Set.univ
              (Set.subset_univ _))
            (Work.Thom.pieceZero (tautologicalBundle k 10) (fePlanePiece k σ))
            (Work.Thom.pieceZero (tautologicalBundle k 10) (Set.univ : Set (OG k 10)))
            (fun _ hp => hp) ℤ k) :=
      Work.Thom.pdCohMap_eq_relCohMap (tautologicalBundle k 10) (fePlanePiece k σ) Set.univ
        (Set.subset_univ _) k
    have hcongr : (Work.Thom.relCohMap
          (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥((tautologicalBundle k 10).proj ⁻¹' fePlanePiece k σ),
              (tautologicalBundle k 10).TotalSpace))
          (Work.Thom.pieceZero (tautologicalBundle k 10) (fePlanePiece k σ))
          (Work.Thom.zeroComplement (tautologicalBundle k 10))
          (fun _ hp => hp) ℤ k).hom
          ((Work.Thom.realThomClassOf hk (tautologicalBundle k 10) horiO).τ)
        = (Work.Thom.relCohMap
            ((⟨Subtype.val, continuous_subtype_val⟩ :
              C(↥((tautologicalBundle k 10).proj ⁻¹' (Set.univ : Set (OG k 10))),
                (tautologicalBundle k 10).TotalSpace)).comp
              (Work.Thom.pieceIncl (tautologicalBundle k 10) (fePlanePiece k σ) Set.univ
                (Set.subset_univ _)))
            (Work.Thom.pieceZero (tautologicalBundle k 10) (fePlanePiece k σ))
            (Work.Thom.zeroComplement (tautologicalBundle k 10))
            (fun _ hp => hp) ℤ k).hom
          ((Work.Thom.realThomClassOf hk (tautologicalBundle k 10) horiO).τ) :=
      congrArg (fun φ => φ.hom
        ((Work.Thom.realThomClassOf hk (tautologicalBundle k 10) horiO).τ))
        (Work.Thom.relCohMap_congrA
          (Work.Thom.pieceZero (tautologicalBundle k 10) (fePlanePiece k σ))
          (Work.Thom.zeroComplement (tautologicalBundle k 10)) hcomp.symm
          (fun _ hp => hp) (fun _ hp => hp) ℤ k)
    refine hcongr.trans ?_
    refine hcompA.symm.trans ?_
    refine (congrArg (fun z => (Work.Thom.relCohMap
        (Work.Thom.pieceIncl (tautologicalBundle k 10) (fePlanePiece k σ) Set.univ
          (Set.subset_univ _))
        (Work.Thom.pieceZero (tautologicalBundle k 10) (fePlanePiece k σ))
        (Work.Thom.pieceZero (tautologicalBundle k 10) (Set.univ : Set (OG k 10)))
        (fun _ hp => hp) ℤ k).hom z) hspec).trans ?_
    rw [← hpd]
    exact hsub
  -- Step C: the chart homeomorphism reads the frame evaluation as the constant gauge
  have hG : ch.comp Φ = gE.comp base :=
    chartHomeo_feFrameEvalPiece (fePlaneChart k σ) σ hmem rfl
  -- Step D: the gauge is orientation preserving, so it fixes the model class
  have hD : (Work.Thom.relCohMap gE (Work.Thom.Punct ↥(fePlanePiece k σ) k)
        (Work.Thom.Punct ↥(fePlanePiece k σ) k) gmem ℤ k).hom
        (Work.Thom.Mpun k ↥(fePlanePiece k σ))
      = Work.Thom.Mpun k ↥(fePlanePiece k σ) :=
    FrameSigns.gaugeOrientationPos hk
      (fun _ : ↥(fePlanePiece k σ) => feFrameGauge (fePlaneChart k σ) σ) continuous_const
      (fun _ => feDet_frameGauge_pos (fePlaneChart k σ) σ hσc)
      (Work.Thom.Mpun k ↥(fePlanePiece k σ))
  -- Step E: the constant base map reduces the model class to the standard generator
  have hE : (Work.Thom.relCohMap base (framePunct k)
        (Work.Thom.Punct ↥(fePlanePiece k σ) k) (fun _ hp => hp) ℤ k).hom
        (Work.Thom.Mpun k ↥(fePlanePiece k σ))
      = stdModelGen k := by
    set PB : C(PUnit, ↥(fePlanePiece k σ)) :=
      ⟨fun _ => ⟨ogMk k 10 σ, hmem⟩, continuous_const⟩ with hPBdef
    have hPB : (Work.Thom.prodMapA PB (EuclideanSpace ℝ (Fin k))).comp (fePtAmb k)
        = (⟨fun v : Amb k => (⟨ogMk k 10 σ, hmem⟩, v),
            continuous_const.prodMk continuous_id⟩ :
            C(Amb k, ↥(fePlanePiece k σ) × Amb k)) := by
      apply ContinuousMap.ext
      intro v
      rfl
    have hcompA := Work.Thom.relCohMap_compA_apply
      (A := framePunct k) (B := Work.Thom.Punct PUnit k)
      (C := Work.Thom.Punct ↥(fePlanePiece k σ) k)
      (fePtAmb k) (Work.Thom.prodMapA PB (EuclideanSpace ℝ (Fin k)))
      (fun _ hp => hp) (fun _ hp => hp) (fun _ hp => hp) ℤ k
      (Work.Thom.Mpun k ↥(fePlanePiece k σ))
    calc (Work.Thom.relCohMap
          (⟨fun v : Amb k => (⟨ogMk k 10 σ, hmem⟩, v),
            continuous_const.prodMk continuous_id⟩ :
            C(Amb k, ↥(fePlanePiece k σ) × Amb k))
          (framePunct k) (Work.Thom.Punct ↥(fePlanePiece k σ) k) (fun _ hp => hp) ℤ k).hom
          (Work.Thom.Mpun k ↥(fePlanePiece k σ))
        = (Work.Thom.relCohMap
            ((Work.Thom.prodMapA PB (EuclideanSpace ℝ (Fin k))).comp (fePtAmb k))
            (framePunct k) (Work.Thom.Punct ↥(fePlanePiece k σ) k) (fun _ hp => hp) ℤ k).hom
            (Work.Thom.Mpun k ↥(fePlanePiece k σ)) :=
          congrArg (fun φ => φ.hom (Work.Thom.Mpun k ↥(fePlanePiece k σ)))
            (Work.Thom.relCohMap_congrA (framePunct k)
              (Work.Thom.Punct ↥(fePlanePiece k σ) k) hPB.symm
              (fun _ hp => hp) (fun _ hp => hp) ℤ k)
      _ = (Work.Thom.relCohMap (fePtAmb k) (framePunct k) (Work.Thom.Punct PUnit k)
              (fun _ hp => hp) ℤ k).hom
            ((Work.Thom.relCohMap (Work.Thom.prodMapA PB (EuclideanSpace ℝ (Fin k)))
              (Work.Thom.Punct PUnit k) (Work.Thom.Punct ↥(fePlanePiece k σ) k)
              (fun _ hp => hp) ℤ k).hom (Work.Thom.Mpun k ↥(fePlanePiece k σ))) :=
          hcompA.symm
      _ = (Work.Thom.relCohMap (fePtAmb k) (framePunct k) (Work.Thom.Punct PUnit k)
              (fun _ hp => hp) ℤ k).hom (Work.Thom.Mpun k PUnit) :=
          congrArg (fun z => (Work.Thom.relCohMap (fePtAmb k) (framePunct k)
            (Work.Thom.Punct PUnit k) (fun _ hp => hp) ℤ k).hom z)
            (Work.Thom.Mpun_natural_map PB)
      _ = stdModelGen k := (feStdModelGen_eq_ptAmb k).symm
  -- functoriality: the frame evaluation is the inclusion of the piece composed with `Φ`
  have hfact : frameEvalMap k σ
      = (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥((tautologicalBundle k 10).proj ⁻¹' fePlanePiece k σ),
            (tautologicalBundle k 10).TotalSpace)).comp Φ := by
    apply ContinuousMap.ext
    intro v
    rfl
  have hsplit1 := Work.Thom.relCohMap_compA_apply
    (A := framePunct k)
    (B := Work.Thom.pieceZero (tautologicalBundle k 10) (fePlanePiece k σ))
    (C := Work.Thom.zeroComplement (tautologicalBundle k 10))
    Φ (⟨Subtype.val, continuous_subtype_val⟩ :
      C(↥((tautologicalBundle k 10).proj ⁻¹' fePlanePiece k σ),
        (tautologicalBundle k 10).TotalSpace))
    hΦmem (fun _ hp => hp) (fun v hv => hΦmem v hv) ℤ k
    ((Work.Thom.realThomClassOf hk (tautologicalBundle k 10) horiO).τ)
  have hsplit2 := Work.Thom.relCohMap_compA_apply
    (A := framePunct k)
    (B := Work.Thom.pieceZero (tautologicalBundle k 10) (fePlanePiece k σ))
    (C := Work.Thom.Punct ↥(fePlanePiece k σ) k)
    Φ ch hΦmem chmem
    (fun v hv => chmem _ (hΦmem v hv)) ℤ k
    (Work.Thom.Mpun k ↥(fePlanePiece k σ))
  have hsplit3 := Work.Thom.relCohMap_compA_apply
    (A := framePunct k)
    (B := Work.Thom.Punct ↥(fePlanePiece k σ) k)
    (C := Work.Thom.Punct ↥(fePlanePiece k σ) k)
    base gE (fun _ hp => hp) gmem (fun v hv => gmem (base v) hv) ℤ k
    (Work.Thom.Mpun k ↥(fePlanePiece k σ))
  calc
    (Work.Thom.relCohMap (frameEvalMap k σ) (framePunct k)
        (Work.Thom.zeroComplement (tautologicalBundle k 10))
        (frameEvalMap_mem k σ) ℤ k).hom
        ((Work.Thom.realThomClassOf hk (tautologicalBundle k 10) horiO).τ)
      = (Work.Thom.relCohMap
          ((⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥((tautologicalBundle k 10).proj ⁻¹' fePlanePiece k σ),
              (tautologicalBundle k 10).TotalSpace)).comp Φ)
          (framePunct k) (Work.Thom.zeroComplement (tautologicalBundle k 10))
          (fun v hv => hΦmem v hv) ℤ k).hom
          ((Work.Thom.realThomClassOf hk (tautologicalBundle k 10) horiO).τ) :=
        congrArg (fun φ => φ.hom
          ((Work.Thom.realThomClassOf hk (tautologicalBundle k 10) horiO).τ))
          (Work.Thom.relCohMap_congrA (framePunct k)
            (Work.Thom.zeroComplement (tautologicalBundle k 10)) hfact
            (frameEvalMap_mem k σ) (fun v hv => hΦmem v hv) ℤ k)
    _ = (Work.Thom.relCohMap Φ (framePunct k)
          (Work.Thom.pieceZero (tautologicalBundle k 10) (fePlanePiece k σ)) hΦmem ℤ k).hom
          ((Work.Thom.relCohMap
            (⟨Subtype.val, continuous_subtype_val⟩ :
              C(↥((tautologicalBundle k 10).proj ⁻¹' fePlanePiece k σ),
                (tautologicalBundle k 10).TotalSpace))
            (Work.Thom.pieceZero (tautologicalBundle k 10) (fePlanePiece k σ))
            (Work.Thom.zeroComplement (tautologicalBundle k 10))
            (fun _ hp => hp) ℤ k).hom
            ((Work.Thom.realThomClassOf hk (tautologicalBundle k 10) horiO).τ)) :=
        hsplit1.symm
    _ = (Work.Thom.relCohMap Φ (framePunct k)
          (Work.Thom.pieceZero (tautologicalBundle k 10) (fePlanePiece k σ)) hΦmem ℤ k).hom
          ((Work.Thom.localThomOfChart (tautologicalBundle k 10) k (Work.Thom.oriE k)
            (fePlaneChart k σ) (fePlanePiece k σ) subset_rfl).τ) :=
        congrArg (fun z => (Work.Thom.relCohMap Φ (framePunct k)
          (Work.Thom.pieceZero (tautologicalBundle k 10) (fePlanePiece k σ)) hΦmem ℤ k).hom z)
          hA
    _ = (Work.Thom.relCohMap Φ (framePunct k)
          (Work.Thom.pieceZero (tautologicalBundle k 10) (fePlanePiece k σ)) hΦmem ℤ k).hom
          ((Work.Thom.relCohMap ch
            (Work.Thom.pieceZero (tautologicalBundle k 10) (fePlanePiece k σ))
            (Work.Thom.Punct ↥(fePlanePiece k σ) k) chmem ℤ k).hom
            (Work.Thom.Mpun k ↥(fePlanePiece k σ))) := rfl
    _ = (Work.Thom.relCohMap (ch.comp Φ) (framePunct k)
          (Work.Thom.Punct ↥(fePlanePiece k σ) k)
          (fun v hv => chmem _ (hΦmem v hv)) ℤ k).hom
          (Work.Thom.Mpun k ↥(fePlanePiece k σ)) := hsplit2
    _ = (Work.Thom.relCohMap (gE.comp base) (framePunct k)
          (Work.Thom.Punct ↥(fePlanePiece k σ) k)
          (fun v hv => gmem (base v) hv) ℤ k).hom
          (Work.Thom.Mpun k ↥(fePlanePiece k σ)) :=
        congrArg (fun φ => φ.hom (Work.Thom.Mpun k ↥(fePlanePiece k σ)))
          (Work.Thom.relCohMap_congrA (framePunct k)
            (Work.Thom.Punct ↥(fePlanePiece k σ) k) hG
            (fun v hv => chmem _ (hΦmem v hv)) (fun v hv => gmem (base v) hv) ℤ k)
    _ = (Work.Thom.relCohMap base (framePunct k)
          (Work.Thom.Punct ↥(fePlanePiece k σ) k) (fun _ hp => hp) ℤ k).hom
          ((Work.Thom.relCohMap gE (Work.Thom.Punct ↥(fePlanePiece k σ) k)
            (Work.Thom.Punct ↥(fePlanePiece k σ) k) gmem ℤ k).hom
            (Work.Thom.Mpun k ↥(fePlanePiece k σ))) := hsplit3.symm
    _ = (Work.Thom.relCohMap base (framePunct k)
          (Work.Thom.Punct ↥(fePlanePiece k σ) k) (fun _ hp => hp) ℤ k).hom
          (Work.Thom.Mpun k ↥(fePlanePiece k σ)) :=
        congrArg (fun z => (Work.Thom.relCohMap base (framePunct k)
          (Work.Thom.Punct ↥(fePlanePiece k σ) k) (fun _ hp => hp) ℤ k).hom z) hD
    _ = stdModelGen k := hE


end

end Work.ThomBordism
