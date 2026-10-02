import Mathlib
import Submission.Work.Gen.EulerBundles
import Submission.Work.Gen.EulerGaugeCLMDefs
import Submission.Work.Gen.EulerModel
import Submission.Work.Gen.EulerSplit
import Submission.Work.Gen.EulerGauge
import Submission.Work.Gen.EulerStdTangent

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Continuity of the Euler-sequence gauge

`Work.Gen.gaugeCLM p t b = Tgt.coordChange (diagIdx p) t b ∘ MCLM p b` is the gauge of the
complexified Euler sequence `(TℂP⁴ ⊗ ℂ) ⊕ ε² ≅ (ℂ ⊗ O(1))⁵` in the source chart `p` and the target
chart `t`; the bundle isomorphisms of `Work.Thom.nonempty_bundleIso_of_gauge` require
`b ↦ gaugeCLM p t b` (and its inverse) to be continuous on `Src.baseSet (p,β) ∩ Tgt.baseSet t`.

Here we prove this.  Everything the gauge is built from depends on `b` only through the chart
coordinate `chartFun p b ∈ ℂ⁴`, so it suffices to prove continuity in the chart variable `u` of
each of the elementary pieces (`vVec`, `ipCLM`, `prV`, the blocks `GblockCLM`, `HblockCLM` and
their explicit inverses), combine them into `blockFibre`/`blockInv` and then into
`MCLM`/`MInvCLM`, and finally multiply by the (continuous, by definition of a `VectorBundleCore`)
chart changes of the target bundle.
-/

namespace Work.Gen

open Work.Projective

noncomputable section

set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

/-! ## The elementary pieces, as functions of the chart variable -/

/-- `u ↦ vVec i u = Fin.insertNth i 1 u` is continuous (it is affine). -/
lemma continuous_vVec {n : ℕ} (i : Fin (n + 1)) :
    Continuous (fun u : Fin n → ℂ => vVec i u) :=
  continuous_insertNth_one i

/-- `u ↦ ipCLM (vVec i u)` is continuous. -/
lemma continuous_ipCLM_vVec {n : ℕ} (i : Fin (n + 1)) :
    Continuous (fun u : Fin n → ℂ => ipCLM (vVec i u)) := by
  rw [show (fun u : Fin n → ℂ => ipCLM (vVec i u))
      = fun u => ∑ m, (star (vVec i u m)) •
          (ContinuousLinearMap.proj m : (Fin (n + 1) → ℂ) →L[ℂ] ℂ) from by
        funext u; rw [ipCLM]]
  have hv : Continuous (fun u : Fin n → ℂ => vVec i u) := continuous_vVec i
  refine continuous_finsetSum _ (fun m _ => ?_)
  exact (continuous_star.comp ((continuous_apply m).comp hv)).smul continuous_const

/-- `u ↦ Qfun i u = ‖vVec i u‖²` is continuous (and never vanishes). -/
lemma continuous_Qfun {n : ℕ} (i : Fin (n + 1)) :
    Continuous (fun u : Fin n → ℂ => Qfun i u) := by
  rw [show (fun u : Fin n → ℂ => Qfun i u)
      = fun u => ipCLM (vVec i u) (vVec i u) from by funext u; rw [Qfun]]
  exact (continuous_ipCLM_vVec i).clm_apply (continuous_vVec i)

/-- `u ↦ prV i u`, the orthogonal projection off the line `ℂ vVec i u`, is continuous. -/
lemma continuous_prV {n : ℕ} (i : Fin (n + 1)) :
    Continuous (fun u : Fin n → ℂ => prV i u) := by
  have hv : Continuous (fun u : Fin n → ℂ => vVec i u) := continuous_vVec i
  have hip : Continuous (fun u : Fin n → ℂ => ipCLM (vVec i u)) := continuous_ipCLM_vVec i
  have hQ : Continuous (fun u : Fin n → ℂ => ipCLM (vVec i u) (vVec i u)) := hip.clm_apply hv
  have hQne : ∀ u : Fin n → ℂ, ipCLM (vVec i u) (vVec i u) ≠ 0 :=
    fun u => ipCLM_self_ne_zero (vVec_ne_zero i u)
  have hvec : Continuous (fun u : Fin n → ℂ =>
      (ipCLM (vVec i u) (vVec i u))⁻¹ • vVec i u) := (hQ.inv₀ hQne).smul hv
  have hsm : Continuous (fun u : Fin n → ℂ => (ipCLM (vVec i u)).smulRight
      ((ipCLM (vVec i u) (vVec i u))⁻¹ • vVec i u)) := by
    have h2 : Continuous (fun u : Fin n → ℂ =>
        (ContinuousLinearMap.smulRightL ℂ (Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ))
          (ipCLM (vVec i u)) ((ipCLM (vVec i u) (vVec i u))⁻¹ • vVec i u)) :=
      (ContinuousLinearMap.smulRightL ℂ (Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ)).continuous₂.comp
        (hip.prodMk hvec)
    refine h2.congr (fun u => ?_)
    simp only [ContinuousLinearMap.smulRightL_apply_apply]
  rw [show (fun u : Fin n → ℂ => prV i u)
      = fun u => ContinuousLinearMap.id ℂ (Fin (n + 1) → ℂ) -
          (ipCLM (vVec i u)).smulRight ((ipCLM (vVec i u) (vVec i u))⁻¹ • vVec i u) from by
        funext u; rw [prV, prCLM]]
  exact continuous_const.sub hsm

/-- `u ↦ GblockCLM i u` is continuous. -/
lemma continuous_GblockCLM {n : ℕ} (i : Fin (n + 1)) :
    Continuous (fun u : Fin n → ℂ => GblockCLM i u) := by
  have hv : Continuous (fun u : Fin n → ℂ => vVec i u) := continuous_vVec i
  have hprV : Continuous (fun u : Fin n → ℂ => prV i u) := continuous_prV i
  have h1 : Continuous (fun u : Fin n → ℂ => (prV i u).comp
      ((insCLM i).comp (ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ))) :=
    hprV.clm_comp_const _
  have h2 : Continuous (fun u : Fin n → ℂ =>
      (ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ).smulRight (vVec i u)) := by
    have h3 : Continuous (fun u : Fin n → ℂ =>
        (ContinuousLinearMap.smulRightL ℂ ((Fin n → ℂ) × ℂ) (Fin (n + 1) → ℂ))
          (ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ) (vVec i u)) :=
      (ContinuousLinearMap.smulRightL ℂ ((Fin n → ℂ) × ℂ) (Fin (n + 1) → ℂ)).continuous₂.comp
        (continuous_const.prodMk hv)
    refine h3.congr (fun u => ?_)
    simp only [ContinuousLinearMap.smulRightL_apply_apply]
  rw [show (fun u : Fin n → ℂ => GblockCLM i u) = fun u =>
      (prV i u).comp ((insCLM i).comp (ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ)) +
      (ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ).smulRight (vVec i u) from by
        funext u; rw [GblockCLM]]
  exact h1.add h2

/-- `u ↦ HblockCLM i u` is continuous. -/
lemma continuous_HblockCLM {n : ℕ} (i : Fin (n + 1)) :
    Continuous (fun u : Fin n → ℂ => HblockCLM i u) := by
  have hG : Continuous (fun u : Fin n → ℂ => GblockCLM i u) := continuous_GblockCLM i
  have hQ : Continuous (fun u : Fin n → ℂ => Qfun i u) := continuous_Qfun i
  have hQne : ∀ u : Fin n → ℂ, Qfun i u ≠ 0 := fun u => Qfun_ne_zero i u
  rw [show (fun u : Fin n → ℂ => HblockCLM i u)
      = fun u => (Qfun i u)⁻¹ • GblockCLM i (star u) from by funext u; rw [HblockCLM]]
  exact (hQ.inv₀ hQne).smul (hG.comp continuous_star)

/-- `u ↦ GblockInv i u` is continuous. -/
lemma continuous_GblockInv {n : ℕ} (i : Fin (n + 1)) :
    Continuous (fun u : Fin n → ℂ => GblockInv i u) := by
  have hv : Continuous (fun u : Fin n → ℂ => vVec i u) := continuous_vVec i
  have hprV : Continuous (fun u : Fin n → ℂ => prV i u) := continuous_prV i
  have hip : Continuous (fun u : Fin n → ℂ => ipCLM (vVec i u)) := continuous_ipCLM_vVec i
  have hQ : Continuous (fun u : Fin n → ℂ => Qfun i u) := continuous_Qfun i
  have hQne : ∀ u : Fin n → ℂ, Qfun i u ≠ 0 := fun u => Qfun_ne_zero i u
  have hmid : Continuous (fun u : Fin n → ℂ =>
      (ContinuousLinearMap.proj i).comp (prV i u)) :=
    continuous_const.clm_comp hprV
  have hsm : Continuous (fun u : Fin n → ℂ =>
      ((ContinuousLinearMap.proj i).comp (prV i u)).smulRight (vVec i u)) := by
    have h3 : Continuous (fun u : Fin n → ℂ =>
        (ContinuousLinearMap.smulRightL ℂ (Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ))
          ((ContinuousLinearMap.proj i).comp (prV i u)) (vVec i u)) :=
      (ContinuousLinearMap.smulRightL ℂ (Fin (n + 1) → ℂ) (Fin (n + 1) → ℂ)).continuous₂.comp
        (hmid.prodMk hv)
    refine h3.congr (fun u => ?_)
    simp only [ContinuousLinearMap.smulRightL_apply_apply]
  have hinner : Continuous (fun u : Fin n → ℂ =>
      prV i u - ((ContinuousLinearMap.proj i).comp (prV i u)).smulRight (vVec i u)) :=
    hprV.sub hsm
  have hF : ∀ k : Fin n, Continuous (fun u : Fin n → ℂ =>
      (ContinuousLinearMap.proj (i.succAbove k)).comp
        (prV i u - ((ContinuousLinearMap.proj i).comp (prV i u)).smulRight (vVec i u))) :=
    fun k => continuous_const.clm_comp hinner
  have hpi : Continuous (fun u : Fin n → ℂ => ContinuousLinearMap.pi (fun k : Fin n =>
      (ContinuousLinearMap.proj (i.succAbove k)).comp
        (prV i u - ((ContinuousLinearMap.proj i).comp (prV i u)).smulRight (vVec i u)))) :=
    (ContinuousLinearMap.piEquivL ℂ (Fin (n + 1) → ℂ) (fun _ : Fin n => ℂ)).continuous.comp
      (continuous_pi hF)
  have hsec : Continuous (fun u : Fin n → ℂ => (Qfun i u)⁻¹ • ipCLM (vVec i u)) :=
    (hQ.inv₀ hQne).smul hip
  rw [show (fun u : Fin n → ℂ => GblockInv i u) = fun u =>
      (ContinuousLinearMap.pi fun k : Fin n =>
        (ContinuousLinearMap.proj (i.succAbove k)).comp
          (prV i u - ((ContinuousLinearMap.proj i).comp (prV i u)).smulRight (vVec i u))).prod
      ((Qfun i u)⁻¹ • ipCLM (vVec i u)) from by funext u; rw [GblockInv]]
  exact (ContinuousLinearMap.prodₗᵢ ℂ).continuous.comp (hpi.prodMk hsec)

/-- `u ↦ HblockInv i u` is continuous. -/
lemma continuous_HblockInv {n : ℕ} (i : Fin (n + 1)) :
    Continuous (fun u : Fin n → ℂ => HblockInv i u) := by
  have hGi : Continuous (fun u : Fin n → ℂ => GblockInv i u) := continuous_GblockInv i
  have hQ : Continuous (fun u : Fin n → ℂ => Qfun i u) := continuous_Qfun i
  rw [show (fun u : Fin n → ℂ => HblockInv i u)
      = fun u => Qfun i u • GblockInv i (star u) from by funext u; rw [HblockInv]]
  exact hQ.smul (hGi.comp continuous_star)

/-! ## The block gauge and its inverse -/

/-- `u ↦ blockFibre p u` is continuous. -/
lemma continuous_blockFibre (p : Fin 5) :
    Continuous (fun u : Fin 4 → ℂ => blockFibre p u) := by
  have hG : Continuous (fun u : Fin 4 → ℂ => GblockCLM p u) := continuous_GblockCLM p
  have hH : Continuous (fun u : Fin 4 → ℂ => HblockCLM p u) := continuous_HblockCLM p
  have hA : Continuous (fun u : Fin 4 → ℂ =>
      (wlpC 5).symm.toContinuousLinearMap.comp
        ((GblockCLM p u).comp
          ((holPart.comp (ContinuousLinearMap.fst ℂ _ _)).prod
            (c0CLM.comp (ContinuousLinearMap.snd ℂ _ _))))) :=
    (hG.clm_comp_const _).const_clm_comp _
  have hB : Continuous (fun u : Fin 4 → ℂ =>
      (wlpC 5).symm.toContinuousLinearMap.comp
        ((HblockCLM p u).comp
          ((antiPart.comp (ContinuousLinearMap.fst ℂ _ _)).prod
            (c1CLM.comp (ContinuousLinearMap.snd ℂ _ _))))) :=
    (hH.clm_comp_const _).const_clm_comp _
  rw [show (fun u : Fin 4 → ℂ => blockFibre p u) = fun u =>
      ((wlpC 5).symm.toContinuousLinearMap.comp
        ((GblockCLM p u).comp
          ((holPart.comp (ContinuousLinearMap.fst ℂ _ _)).prod
            (c0CLM.comp (ContinuousLinearMap.snd ℂ _ _))))).prod
      ((wlpC 5).symm.toContinuousLinearMap.comp
        ((HblockCLM p u).comp
          ((antiPart.comp (ContinuousLinearMap.fst ℂ _ _)).prod
            (c1CLM.comp (ContinuousLinearMap.snd ℂ _ _))))) from by funext u; rw [blockFibre]]
  exact (ContinuousLinearMap.prodₗᵢ ℂ).continuous.comp (hA.prodMk hB)

/-- `u ↦ blockInv p u` is continuous. -/
lemma continuous_blockInv (p : Fin 5) :
    Continuous (fun u : Fin 4 → ℂ => blockInv p u) := by
  have hGi : Continuous (fun u : Fin 4 → ℂ => GblockInv p u) := continuous_GblockInv p
  have hHi : Continuous (fun u : Fin 4 → ℂ => HblockInv p u) := continuous_HblockInv p
  have hA : Continuous (fun u : Fin 4 → ℂ => blkA p u) :=
    (hGi.clm_comp_const _).const_clm_comp _
  have hB : Continuous (fun u : Fin 4 → ℂ => blkB p u) :=
    (hHi.clm_comp_const _).const_clm_comp _
  have hC : Continuous (fun u : Fin 4 → ℂ => blkC p u) :=
    (hGi.clm_comp_const _).const_clm_comp _
  have hD : Continuous (fun u : Fin 4 → ℂ => blkD p u) :=
    (hHi.clm_comp_const _).const_clm_comp _
  have hAB : Continuous (fun u : Fin 4 → ℂ => (blkA p u).prod (blkB p u)) :=
    (ContinuousLinearMap.prodₗᵢ ℂ).continuous.comp (hA.prodMk hB)
  have h1 : Continuous (fun u : Fin 4 → ℂ =>
      XiEquiv.toContinuousLinearMap.comp ((blkA p u).prod (blkB p u))) :=
    hAB.const_clm_comp _
  have hCD : Continuous (fun u : Fin 4 → ℂ => (blkC p u).prod (blkD p u)) :=
    (ContinuousLinearMap.prodₗᵢ ℂ).continuous.comp (hC.prodMk hD)
  have h2 : Continuous (fun u : Fin 4 → ℂ =>
      pair2CLM.comp ((blkC p u).prod (blkD p u))) :=
    hCD.const_clm_comp _
  rw [show (fun u : Fin 4 → ℂ => blockInv p u) = fun u =>
      (XiEquiv.toContinuousLinearMap.comp ((blkA p u).prod (blkB p u))).prod
        (pair2CLM.comp ((blkC p u).prod (blkD p u))) from by funext u; rw [blockInv]]
  exact (ContinuousLinearMap.prodₗᵢ ℂ).continuous.comp (h1.prodMk h2)

/-! ## The gauge in the standard fibre -/

/-- `b ↦ MCLM p b` is continuous on the chart `p`. -/
lemma continuousOn_MCLM (p : Fin 5) :
    ContinuousOn (fun b : CP 4 => MCLM p b) (chartSet p) := by
  have hbf : Continuous (fun u : Fin 4 → ℂ => blockFibre p u) := continuous_blockFibre p
  have h1 : Continuous (fun u : Fin 4 → ℂ =>
      (blockFibre p u).comp (Work.Whitney.sumFibreC 8 2).symm.toContinuousLinearMap) :=
    hbf.clm_comp_const _
  have h2 : Continuous (fun u : Fin 4 → ℂ => CbigCLM.comp
      ((blockFibre p u).comp (Work.Whitney.sumFibreC 8 2).symm.toContinuousLinearMap)) :=
    h1.const_clm_comp CbigCLM
  refine (h2.comp_continuousOn (continuousOn_chartFun p)).congr (fun b _ => ?_)
  show MCLM p b = CbigCLM.comp ((blockFibre p (chartFun p b)).comp
    (Work.Whitney.sumFibreC 8 2).symm.toContinuousLinearMap)
  rw [MCLM]

/-- `b ↦ MInvCLM p b` is continuous on the chart `p`. -/
lemma continuousOn_MInvCLM (p : Fin 5) :
    ContinuousOn (fun b : CP 4 => MInvCLM p b) (chartSet p) := by
  have hbi : Continuous (fun u : Fin 4 → ℂ => blockInv p u) := continuous_blockInv p
  have h1 : Continuous (fun u : Fin 4 → ℂ =>
      (blockInv p u).comp CbigInv) :=
    hbi.clm_comp_const _
  have h2 : Continuous (fun u : Fin 4 → ℂ => (Work.Whitney.sumFibreC 8 2).toContinuousLinearMap.comp
      ((blockInv p u).comp CbigInv)) :=
    h1.const_clm_comp _
  refine (h2.comp_continuousOn (continuousOn_chartFun p)).congr (fun b _ => ?_)
  show MInvCLM p b = (Work.Whitney.sumFibreC 8 2).toContinuousLinearMap.comp
    ((blockInv p (chartFun p b)).comp CbigInv)
  rw [MInvCLM]

/-- The base set of the source bundle over the index `(p, β)`. -/
lemma Src_baseSet_eq (p : Fin 5) (β : Fin 1) : Src.baseSet (p, β) = chartSet p := by
  show (stdTangentC 4).baseSet p ∩ (Set.univ : Set (CP 4)) = chartSet p
  rw [stdTangentC_baseSet, Set.inter_univ]

/-- The base set of the target bundle over the diagonal index `diagIdx p`. -/
lemma Tgt_baseSet_diagIdx (p : Fin 5) : Tgt.baseSet (diagIdx p) = chartSet p :=
  eulerTarget_baseSet_diagIdx p

/-- `b ↦ gaugeCLM p t b` is continuous on `Src.baseSet (p,β) ∩ Tgt.baseSet t`. -/
lemma continuousOn_gaugeCLM (p : Fin 5) (β : Fin 1) (t : TgtIdx) :
    ContinuousOn (fun b : CP 4 => gaugeCLM p t b)
      (Src.baseSet (p, β) ∩ Tgt.baseSet t) := by
  have hsub1 : Src.baseSet (p, β) ∩ Tgt.baseSet t ⊆ chartSet p := by
    intro b hb
    rw [Src_baseSet_eq] at hb
    exact hb.1
  have hsub2 : Src.baseSet (p, β) ∩ Tgt.baseSet t ⊆ Tgt.baseSet (diagIdx p) ∩ Tgt.baseSet t := by
    intro b hb
    rw [Tgt_baseSet_diagIdx]
    exact ⟨hsub1 hb, hb.2⟩
  have hA : ContinuousOn (fun b : CP 4 => Tgt.coordChange (diagIdx p) t b)
      (Src.baseSet (p, β) ∩ Tgt.baseSet t) :=
    (Tgt.continuousOn_coordChange (diagIdx p) t).mono hsub2
  have hB : ContinuousOn (fun b : CP 4 => MCLM p b)
      (Src.baseSet (p, β) ∩ Tgt.baseSet t) :=
    (continuousOn_MCLM p).mono hsub1
  refine (hA.clm_comp hB).congr (fun b _ => ?_)
  rw [gaugeCLM]

/-- `b ↦ gaugeInvCLM p t b` is continuous on `Src.baseSet (p,β) ∩ Tgt.baseSet t`. -/
lemma continuousOn_gaugeInvCLM (p : Fin 5) (β : Fin 1) (t : TgtIdx) :
    ContinuousOn (fun b : CP 4 => gaugeInvCLM p t b)
      (Src.baseSet (p, β) ∩ Tgt.baseSet t) := by
  have hsub1 : Src.baseSet (p, β) ∩ Tgt.baseSet t ⊆ chartSet p := by
    intro b hb
    rw [Src_baseSet_eq] at hb
    exact hb.1
  have hsub2 : Src.baseSet (p, β) ∩ Tgt.baseSet t ⊆ Tgt.baseSet t ∩ Tgt.baseSet (diagIdx p) := by
    intro b hb
    rw [Tgt_baseSet_diagIdx]
    exact ⟨hb.2, hsub1 hb⟩
  have hA : ContinuousOn (fun b : CP 4 => Tgt.coordChange t (diagIdx p) b)
      (Src.baseSet (p, β) ∩ Tgt.baseSet t) :=
    (Tgt.continuousOn_coordChange t (diagIdx p)).mono hsub2
  have hB : ContinuousOn (fun b : CP 4 => MInvCLM p b)
      (Src.baseSet (p, β) ∩ Tgt.baseSet t) :=
    (continuousOn_MInvCLM p).mono hsub1
  refine (hB.clm_comp hA).congr (fun b _ => ?_)
  rw [gaugeInvCLM]

/-! ## The statement -/

theorem gauge_continuous :
    (∀ (p : Fin 5), ContinuousOn (fun b : Work.Projective.CP 4 => Work.Gen.MCLM p b)
      (Work.Projective.chartSet p)) ∧
    (∀ (p : Fin 5), ContinuousOn (fun b : Work.Projective.CP 4 => Work.Gen.MInvCLM p b)
      (Work.Projective.chartSet p)) ∧
    (∀ (p : Fin 5) (β : Fin 1) (t : Work.Gen.TgtIdx),
      ContinuousOn (fun b : Work.Projective.CP 4 => Work.Gen.gaugeCLM p t b)
        (Work.Gen.Src.baseSet (p, β) ∩ Work.Gen.Tgt.baseSet t)) ∧
    (∀ (p : Fin 5) (β : Fin 1) (t : Work.Gen.TgtIdx),
      ContinuousOn (fun b : Work.Projective.CP 4 => Work.Gen.gaugeInvCLM p t b)
        (Work.Gen.Src.baseSet (p, β) ∩ Work.Gen.Tgt.baseSet t)) :=
  ⟨continuousOn_MCLM, continuousOn_MInvCLM, continuousOn_gaugeCLM, continuousOn_gaugeInvCLM⟩

end

end Work.Gen
