import Mathlib
import Submission.Work.ThomBordism.KeyLocal.tubeSets
import Submission.Work.ThomBordism.KeyLocal.tubeNormDefs
import Submission.Work.ThomBordism.KeyLocal.tubeNormAux
import Submission.Work.ThomBordism.KeyLocal.mpunPullbackSnd
import Submission.Work.ThomBordism.KeyLocal.varyingMatGauge
import Submission.Work.ThomBordism.KeyLocal.gaussPlaneSingleChart
import Submission.Work.ThomBordism.KeyLocal.gaussMapTubeFrameEval
import Submission.Work.ThomBordism.KeyLocal.chartHomeoFrameEval
import Submission.Work.ThomBordism.gtdGaussCandidate
import Submission.Work.ThomBordism.frameEval_realThomClassOf
import Submission.Work.Thom.realThomClassOf_natural
import Submission.Work.ThomBordism.Grassmann.PlaneCoord
import Submission.Work.ThomBordism.KeyLocal.mpunPullbackSnd
import Submission.Work.ThomBordism.KeyLocal.varyingMatGauge
import Submission.Work.ThomBordism.gtdGaussCandidate
import Submission.Work.ThomBordism.frameEval_realThomClassOf
import Submission.Work.Thom.realThomClassOf_natural
import Submission.Work.ThomBordism.Grassmann.PlaneCoord

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

open CategoryTheory

namespace Work.ThomBordism.KeyLocal

open Work.Tubular Work.ThomBordism.PontryaginThom Work.ThomBordism.Grassmann

/-- **The tube-level normal reading of the canonical class.**

Restricted to the part of the tube lying over a chart `i` of the normal datum, the pullback of the
canonical class `Ucan = gtdUWith E ND G hgm (realThomClassOf hk (tautologicalBundle k 10) horiO)`
along the tube inverse `C.inv` is the pullback of the standard generator `stdModelGen k` along the
*coordinate reading* of the normal vector in the σ-corrected frame `Gauss.gframe E ND i` (the
hypothesis `hB` pins the continuous map `B` to that reading pointwise; `hBmem` is the
non-vanishing condition on the punctured part).

This is piece (T2) of the last-mile plan (`_kl/NOTE_SESSION9.md`): it is the tube-level version of
the PROVED fibre statement `Work.ThomBordism.nfRes_gtdUWith_realThomClassOf_eq_coorFibre`, and it
feeds the product formula `Work.ThomBordism.KeyLocal.tcmRelCup_stdModelGen`.

Proof route (all inputs available): Step A of `frameEval_realThomClassOf` restricts `U.τ` to the
chart piece and identifies it with `localThomOfChart`, which is *defined* as
`(relCohMap (chartHomeo …))^*(Mpun k ↥W)`; `relCohMap_compA_apply` then turns the composite into
`(chartHomeo ∘ Θ)^*(Mpun k ↥W)`; `chartHomeo_apply` identifies `chartHomeo ∘ Θ` with
`y ↦ (P y, feFrameGauge S σ_y (V y))` (positive determinant by `feDet_frameGauge_pos`);
`Work.ThomBordism.KeyLocal.mpunPullbackSnd` removes the base coordinate and
`Work.ThomBordism.KeyLocal.varyingMatGauge` removes the (varying, positive-determinant) gauge. -/
theorem tubeNormReading {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ} (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
    (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
      G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
    (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
      = Work.ThomBordism.Grassmann.padGaussFun E ND p.1)
    (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
      = Work.PTGeometric.padEuc k 10 (by norm_num)
          (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε)
    (i : Work.ThomBordism.PontryaginThom.CoverIdx V k)
    (B : C(↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i), EuclideanSpace ℝ (Fin k)))
    (hB : ∀ y, B y = Work.ThomBordism.KeyLocal.tubeNormCoord E C ND i y)
    (hBmem : ∀ y ∈ Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i,
      B y ∈ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k)))) :
    (Work.Thom.relCohMap (Work.ThomBordism.KeyLocal.tubeBaseSetIncl E C ND i)
        (Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i) (Work.Tubular.normalNonzero E)
        (fun y hy => hy) ℤ k).hom
      (Work.ThomBordism.gtdUWith E ND G hgm
        (Work.Thom.realThomClassOf hk (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
          (Work.ThomBordism.tautologicalBundle_horiO k)))
    = (Work.Thom.relCohMap B (Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i)
        ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))) hBmem ℤ k).hom
      (Work.ThomBordism.stdModelGen k) := by
  classical
  set S : Work.ThomBordism.Grassmann.ChartIdx k 10 :=
    Work.ThomBordism.KeyLocal.padComplChart i with hSdef
  set Ucan : Work.Thom.ThomClass (Work.ThomBordism.Grassmann.tautologicalBundle k 10) k :=
    Work.Thom.realThomClassOf hk (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
      (Work.ThomBordism.tautologicalBundle_horiO k) with hUcandef
  have hchartSet : ∀ y : ↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i), Work.ThomBordism.KeyLocal.tubeFrame E C ND i y ∈ Work.ThomBordism.Grassmann.chartSet S :=
    fun y => (Work.ThomBordism.Grassmann.mem_chartSet S _).mpr
      (Work.ThomBordism.KeyLocal.gaussPlaneSingleChart E ND i y.2)
  have hPS : ∀ y : ↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i), Work.ThomBordism.Grassmann.ogMk k 10 (Work.ThomBordism.KeyLocal.tubeFrame E C ND i y) ∈ ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S) :=
    fun y => (Work.ThomBordism.Grassmann.mem_baseSet_iff S _).mpr (hchartSet y)
  set nb : C(Work.Tubular.NormalTotal E, (Work.Tubular.normalBundle E ND).TotalSpace) :=
    ((Work.Tubular.eucNormalHomeomorph E ND).symm :
      C(Work.Tubular.NormalTotal E, (Work.Tubular.normalBundle E ND).TotalSpace)) with hnbdef
  set Tht : C(↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i), (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace) :=
    G.comp (nb.comp (Work.ThomBordism.KeyLocal.tubeBaseSetIncl E C ND i)) with hThtdef
  have hTht_apply : ∀ y : ↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i),
      Tht y = G (nb ((Work.ThomBordism.KeyLocal.tubeBaseSetIncl E C ND i) y)) := fun y => rfl
  have hmem1 : ∀ y ∈ Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i,
      nb ((Work.ThomBordism.KeyLocal.tubeBaseSetIncl E C ND i) y) ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND) :=
    fun y hy => gtd_mem E ND _ hy
  have hThtmem : ∀ y ∈ Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i, Tht y ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10) :=
    fun y hy => hgm _ (hmem1 y hy)
  have hThtpt : ∀ y : ↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i), Tht y = frameEval k (Work.ThomBordism.KeyLocal.tubeFrame E C ND i y) (B y) := by
    intro y
    rw [hTht_apply]
    rw [show nb ((Work.ThomBordism.KeyLocal.tubeBaseSetIncl E C ND i) y) = Work.Tubular.normalToBundle E ND (C.inv y.1.1) from
      Work.ThomBordism.gtdEucNormalHomeomorph_symm_apply E ND _]
    rw [Work.ThomBordism.KeyLocal.gaussMapTubeFrameEval E ND G hbp hvec C i y]
    rw [hB y]
  have hstep1 : (Work.Thom.relCohMap (Work.ThomBordism.KeyLocal.tubeBaseSetIncl E C ND i) (Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i) (Work.Tubular.normalNonzero E)
        (fun y hy => hy) ℤ k).hom
      (Work.ThomBordism.gtdUWith E ND G hgm Ucan)
      = (Work.Thom.relCohMap Tht (Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i) (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)) hThtmem ℤ k).hom Ucan.τ := by
    rw [show Work.ThomBordism.gtdUWith E ND G hgm Ucan
        = (Work.Thom.relCohMap ((Work.Tubular.eucNormalHomeomorph E ND).symm :
              C(Work.Tubular.NormalTotal E, (Work.Tubular.normalBundle E ND).TotalSpace))
            (Work.Tubular.normalNonzero E)
            (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
            (gtd_mem E ND) ℤ k).hom
          ((Work.Thom.relCohMap G (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
            (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)) hgm ℤ k).hom Ucan.τ) from rfl]
    rw [Work.Thom.relCohMap_compA_apply
      (A := Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i) (B := Work.Tubular.normalNonzero E)
      (C := Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
      (f := (Work.ThomBordism.KeyLocal.tubeBaseSetIncl E C ND i))
      (g := ((Work.Tubular.eucNormalHomeomorph E ND).symm :
        C(Work.Tubular.NormalTotal E, (Work.Tubular.normalBundle E ND).TotalSpace)))
      (fun y hy => hy) (gtd_mem E ND) hmem1 ℤ k _]
    exact Work.Thom.relCohMap_compA_apply
      (A := Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i) (B := Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
      (C := Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
      (f := ((Work.Tubular.eucNormalHomeomorph E ND).symm :
        C(Work.Tubular.NormalTotal E, (Work.Tubular.normalBundle E ND).TotalSpace)).comp
        (Work.ThomBordism.KeyLocal.tubeBaseSetIncl E C ND i))
      (g := G) hmem1 hgm hThtmem ℤ k _
  -- the subtype map into the piece over the chart, and the membership conditions
  have hThtW : ∀ y : ↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i), Tht y ∈ (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj ⁻¹' ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S) := by
    intro y
    rw [Set.mem_preimage, hThtpt y]
    show (frameEval k (Work.ThomBordism.KeyLocal.tubeFrame E C ND i y) (B y)).1 ∈ ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S)
    rw [Work.ThomBordism.frameEval_base]
    exact hPS y
  set Tht' : C(↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i), ↥((Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj ⁻¹' ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S))) :=
    ⟨fun y => ⟨Tht y, hThtW y⟩, Continuous.subtype_mk Tht.continuous hThtW⟩ with hTht'def
  set incl : C(↥((Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj ⁻¹' ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S)), (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace) :=
    ⟨Subtype.val, continuous_subtype_val⟩ with hinCldef
  set inclU : C(↥((Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj ⁻¹' (Set.univ : Set (Work.ThomBordism.Grassmann.OG k 10))),
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace) :=
    ⟨Subtype.val, continuous_subtype_val⟩ with hinclUdef
  have hfact : incl.comp Tht' = Tht := by
    apply ContinuousMap.ext; intro y; rfl
  have hTht'punc : ∀ y ∈ Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i, Tht' y ∈ Work.Thom.pieceZero (Work.ThomBordism.Grassmann.tautologicalBundle k 10) (((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S)) :=
    fun y hy => hThtmem y hy
  have hTht'c : ∀ y ∈ Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i, incl (Tht' y) ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10) :=
    fun y hy => hThtmem y hy
  -- Step A: the canonical class restricts to the chart class over the piece of the chart `S`
  have hA : (Work.Thom.relCohMap incl (Work.Thom.pieceZero (Work.ThomBordism.Grassmann.tautologicalBundle k 10) (((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S))) (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)) (fun _ hp => hp) ℤ k).hom Ucan.τ
      = (Work.Thom.localThomOfChart (Work.ThomBordism.Grassmann.tautologicalBundle k 10) k (Work.Thom.oriE k) S ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S) subset_rfl).τ := by
    have hcomp : inclU.comp
        (Work.Thom.pieceIncl (Work.ThomBordism.Grassmann.tautologicalBundle k 10) ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S) Set.univ (Set.subset_univ _)) = incl := by
      apply ContinuousMap.ext
      intro p
      rfl
    have hspec := Work.Thom.realThomClassOf_spec hk (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
      (Work.ThomBordism.tautologicalBundle_horiO k)
    have hsub := Work.Thom.localThomOfOrientedCover_subset hk (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
      (Work.ThomBordism.tautologicalBundle_horiO k) S (hW := subset_rfl)
    have hcompA := Work.Thom.relCohMap_compA_apply
      (A := Work.Thom.pieceZero (Work.ThomBordism.Grassmann.tautologicalBundle k 10) (((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S)))
      (B := Work.Thom.pieceZero (Work.ThomBordism.Grassmann.tautologicalBundle k 10) (Set.univ : Set (Work.ThomBordism.Grassmann.OG k 10)))
      (C := Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
      (Work.Thom.pieceIncl (Work.ThomBordism.Grassmann.tautologicalBundle k 10) ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S) Set.univ (Set.subset_univ _))
      inclU
      (fun _ hp => hp) (fun _ hp => hp) (fun _ hp => hp) ℤ k Ucan.τ
    have hpd : (Work.Cohomology.pdCohMap
          (TopCat.of (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace) (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
          ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj ⁻¹' (Set.univ : Set (Work.ThomBordism.Grassmann.OG k 10)))
          ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj ⁻¹' ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S)) (Set.preimage_mono (Set.subset_univ _)) k)
        = (Work.Thom.relCohMap
            (Work.Thom.pieceIncl (Work.ThomBordism.Grassmann.tautologicalBundle k 10) ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S) Set.univ (Set.subset_univ _))
            (Work.Thom.pieceZero (Work.ThomBordism.Grassmann.tautologicalBundle k 10) (((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S)))
            (Work.Thom.pieceZero (Work.ThomBordism.Grassmann.tautologicalBundle k 10) (Set.univ : Set (Work.ThomBordism.Grassmann.OG k 10)))
            (fun _ hp => hp) ℤ k) :=
      Work.Thom.pdCohMap_eq_relCohMap (Work.ThomBordism.Grassmann.tautologicalBundle k 10) ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S) Set.univ (Set.subset_univ _) k
    have hcongr : (Work.Thom.relCohMap incl (Work.Thom.pieceZero (Work.ThomBordism.Grassmann.tautologicalBundle k 10) (((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S))) (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)) (fun _ hp => hp) ℤ k).hom Ucan.τ
        = (Work.Thom.relCohMap (inclU.comp
              (Work.Thom.pieceIncl (Work.ThomBordism.Grassmann.tautologicalBundle k 10) ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S) Set.univ (Set.subset_univ _)))
            (Work.Thom.pieceZero (Work.ThomBordism.Grassmann.tautologicalBundle k 10) (((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S))) (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)) (fun _ hp => hp) ℤ k).hom Ucan.τ :=
      congrArg (fun φ => φ.hom Ucan.τ)
        (Work.Thom.relCohMap_congrA (Work.Thom.pieceZero (Work.ThomBordism.Grassmann.tautologicalBundle k 10) (((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S))) (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)) hcomp.symm
          (fun _ hp => hp) (fun _ hp => hp) ℤ k)
    refine hcongr.trans ?_
    refine hcompA.symm.trans ?_
    refine (congrArg (fun z => (Work.Thom.relCohMap
        (Work.Thom.pieceIncl (Work.ThomBordism.Grassmann.tautologicalBundle k 10) ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S) Set.univ (Set.subset_univ _))
        (Work.Thom.pieceZero (Work.ThomBordism.Grassmann.tautologicalBundle k 10) (((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S)))
        (Work.Thom.pieceZero (Work.ThomBordism.Grassmann.tautologicalBundle k 10) (Set.univ : Set (Work.ThomBordism.Grassmann.OG k 10)))
        (fun _ hp => hp) ℤ k).hom z) hspec).trans ?_
    rw [← hpd]
    exact hsub
  -- the chart homeomorphism of the piece, and the coordinate maps
  set chH : C(↥((Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj ⁻¹' ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S)), (↥(((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S))) × EuclideanSpace ℝ (Fin k)) :=
    ((Work.Thom.chartHomeo (Work.ThomBordism.Grassmann.tautologicalBundle k 10) k (Work.Thom.oriE k) S ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S) subset_rfl) :
      C(↥((Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj ⁻¹' ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S)), (↥(((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S))) × EuclideanSpace ℝ (Fin k))) with hchHdef
  have hchHmem : ∀ p ∈ Work.Thom.pieceZero (Work.ThomBordism.Grassmann.tautologicalBundle k 10) (((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S)), chH p ∈ Work.Thom.Punct (↥(((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S))) k :=
    Work.Thom.chartHomeo_mem (Work.ThomBordism.Grassmann.tautologicalBundle k 10) k (Work.Thom.oriE k) S ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S) subset_rfl
  have hAcont : Continuous (fun y : ↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i) => feFrameGauge S (Work.ThomBordism.KeyLocal.tubeFrame E C ND i y)) :=
    continuous_feFrameGauge_tubeFrame E C ND i S hchartSet
  set A : C(↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i), EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) :=
    ⟨fun y => feFrameGauge S (Work.ThomBordism.KeyLocal.tubeFrame E C ND i y), hAcont⟩ with hAdef
  have hPcont : Continuous (fun y : ↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i) =>
      (⟨ogMk k 10 (Work.ThomBordism.KeyLocal.tubeFrame E C ND i y), hPS y⟩ : ↥(((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S)))) :=
    Continuous.subtype_mk ((ogMk k 10).continuous.comp (continuous_tubeFrame E C ND i)) hPS
  set P : C(↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i), ↥(((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S))) :=
    ⟨fun y => ⟨ogMk k 10 (Work.ThomBordism.KeyLocal.tubeFrame E C ND i y), hPS y⟩, hPcont⟩ with hPdef
  set V : C(↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i), EuclideanSpace ℝ (Fin k)) :=
    ⟨fun y => A y (B y), A.continuous.clm_apply B.continuous⟩ with hVdef
  have hch_eq : chH.comp Tht'
      = (⟨fun y => (P y, V y), P.continuous.prodMk V.continuous⟩ :
          C(↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i), (↥(((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S))) × EuclideanSpace ℝ (Fin k))) := by
    apply ContinuousMap.ext
    intro y
    show Work.Thom.chartHomeo (Work.ThomBordism.Grassmann.tautologicalBundle k 10) k (Work.Thom.oriE k) S ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S) subset_rfl (Tht' y)
      = (P y, V y)
    have h1 : Tht' y = feFrameEvalPiece S (Work.ThomBordism.KeyLocal.tubeFrame E C ND i y) (hPS y) (B y) :=
      Subtype.ext (hThtpt y)
    rw [h1]
    exact Work.ThomBordism.KeyLocal.chartHomeoFrameEval S (Work.ThomBordism.KeyLocal.tubeFrame E C ND i y) (hPS y) (B y)
  have hFeDet : ∀ y : ↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i), 0 < LinearMap.det (A y).toLinearMap :=
    fun y => feDet_frameGauge_pos S (Work.ThomBordism.KeyLocal.tubeFrame E C ND i y) (hchartSet y)
  have hSV : ∀ y ∈ Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i, V y ∈ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))) := by
    intro y hy
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hV0
    have hinj : Function.Injective (A y) :=
      (Work.Thom.gaugeEnd_bijective_of_det_ne_zero (A y) (ne_of_gt (hFeDet y))).1
    have hV0' : A y (B y) = 0 := by
      rw [hVdef] at hV0
      exact hV0
    have hB0 : B y = 0 := hinj (by rw [hV0', map_zero])
    exact (hBmem y hy) (Set.mem_singleton_iff.mpr hB0)
  -- Step 2: split `Tht` along the inclusion of the piece
  have hstep2 : (Work.Thom.relCohMap Tht (Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i) (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)) hThtmem ℤ k).hom Ucan.τ
      = (Work.Thom.relCohMap Tht' (Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i) (Work.Thom.pieceZero (Work.ThomBordism.Grassmann.tautologicalBundle k 10) (((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S))) hTht'punc ℤ k).hom
        ((Work.Thom.relCohMap incl (Work.Thom.pieceZero (Work.ThomBordism.Grassmann.tautologicalBundle k 10) (((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S))) (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)) (fun _ hp => hp) ℤ k).hom Ucan.τ) := by
    rw [← Work.Thom.relCohMap_congrA (Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i) (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)) hfact hTht'c hThtmem ℤ k]
    exact (Work.Thom.relCohMap_compA_apply (A := Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i) (B := Work.Thom.pieceZero (Work.ThomBordism.Grassmann.tautologicalBundle k 10) (((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S))) (C := Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
      Tht' incl hTht'punc (fun _ hp => hp) hTht'c ℤ k Ucan.τ).symm
  -- Step 3: replace the restriction of the canonical class by the chart class (Step A)
  have hstep3 : (Work.Thom.relCohMap Tht' (Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i) (Work.Thom.pieceZero (Work.ThomBordism.Grassmann.tautologicalBundle k 10) (((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S))) hTht'punc ℤ k).hom
        ((Work.Thom.relCohMap incl (Work.Thom.pieceZero (Work.ThomBordism.Grassmann.tautologicalBundle k 10) (((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S))) (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)) (fun _ hp => hp) ℤ k).hom Ucan.τ)
      = (Work.Thom.relCohMap Tht' (Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i) (Work.Thom.pieceZero (Work.ThomBordism.Grassmann.tautologicalBundle k 10) (((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S))) hTht'punc ℤ k).hom
        ((Work.Thom.localThomOfChart (Work.ThomBordism.Grassmann.tautologicalBundle k 10) k (Work.Thom.oriE k) S ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S) subset_rfl).τ) :=
    congrArg (fun z => (Work.Thom.relCohMap Tht' (Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i) (Work.Thom.pieceZero (Work.ThomBordism.Grassmann.tautologicalBundle k 10) (((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S))) hTht'punc ℤ k).hom z) hA
  -- Step 4: read the chart class through the chart homeomorphism
  have hstep4 : (Work.Thom.relCohMap Tht' (Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i) (Work.Thom.pieceZero (Work.ThomBordism.Grassmann.tautologicalBundle k 10) (((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S))) hTht'punc ℤ k).hom
        ((Work.Thom.localThomOfChart (Work.ThomBordism.Grassmann.tautologicalBundle k 10) k (Work.Thom.oriE k) S ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S) subset_rfl).τ)
      = (Work.Thom.relCohMap (chH.comp Tht') (Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i) (Work.Thom.Punct (↥(((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S))) k)
          (fun y hy => hchHmem _ (hTht'punc y hy)) ℤ k).hom (Work.Thom.Mpun k (↥(((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S)))) := by
    rw [show (Work.Thom.localThomOfChart (Work.ThomBordism.Grassmann.tautologicalBundle k 10) k (Work.Thom.oriE k) S ((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S) subset_rfl).τ
        = (Work.Thom.relCohMap chH (Work.Thom.pieceZero (Work.ThomBordism.Grassmann.tautologicalBundle k 10) (((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S))) (Work.Thom.Punct (↥(((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S))) k) hchHmem ℤ k).hom (Work.Thom.Mpun k (↥(((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S)))) from rfl]
    exact Work.Thom.relCohMap_compA_apply (A := Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i) (B := Work.Thom.pieceZero (Work.ThomBordism.Grassmann.tautologicalBundle k 10) (((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S))) (C := Work.Thom.Punct (↥(((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S))) k)
      Tht' chH hTht'punc hchHmem (fun y hy => hchHmem _ (hTht'punc y hy)) ℤ k (Work.Thom.Mpun k (↥(((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S))))
  -- Step 5: the chart homeomorphism of the frame evaluation
  have hstep5 : (Work.Thom.relCohMap (chH.comp Tht') (Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i) (Work.Thom.Punct (↥(((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S))) k)
          (fun y hy => hchHmem _ (hTht'punc y hy)) ℤ k).hom (Work.Thom.Mpun k (↥(((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S))))
      = (Work.Thom.relCohMap
          (⟨fun y => (P y, V y), P.continuous.prodMk V.continuous⟩ :
            C(↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i), (↥(((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S))) × EuclideanSpace ℝ (Fin k)))
          (Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i) (Work.Thom.Punct (↥(((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S))) k) (fun y hy => hSV y hy) ℤ k).hom (Work.Thom.Mpun k (↥(((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S)))) := by
    rw [Work.Thom.relCohMap_congrA (Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i) (Work.Thom.Punct (↥(((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet S))) k) hch_eq
      (fun y hy => hchHmem _ (hTht'punc y hy)) (fun y hy => hSV y hy) ℤ k]
  -- Step 6: the model class only sees the second coordinate
  have hstep6 := mpunPullbackSnd_punct (X := ↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i)) P V (Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i) hSV
  -- Step 7: the varying positive-determinant gauge is harmless
  have hstep7 := varyingMatGauge hk A hFeDet B (Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i) hSV hBmem
  exact hstep1.trans (hstep2.trans (hstep3.trans (hstep4.trans (hstep5.trans
    (hstep6.trans hstep7)))))


end Work.ThomBordism.KeyLocal
