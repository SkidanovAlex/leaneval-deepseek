import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SourceBound.weakSliceBounds
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.remov.wsMomentId
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData6.zfarR_jet_le6_of_jets
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.Honesty.psiTrunc_tendsto_psiSeries
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.PhiStar.Series.eFam_sup_le
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6.HkN_sepF_le
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.KsAux
import Submission.Work.FTS.StrongPersist.N6Trans.HonestEasyMajorAsmA
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.ExcBoundOpen
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS.Vocab
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXR1.HJ.AKBounds
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.ExcBoundQ
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.H2.T1Q.SlotPtQ
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H2.T1Q.T1EasyContQ
import Submission.Work.H2W.FstarDzIterFourPsiAe
import Submission.Work.H2W.PsiSlices.shiftedSourcePoleBound
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.TraceEngine.traceBrick =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5.TraceEngine

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
/-! ## The brick -/

theorem traceBrick : ∃ C : ℝ, 0 < C ∧ ∀ (G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.SmoothOpen G →
    (∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => Work.Spaces.Dz G z θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) →
    (∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => Work.Spaces.Dz G z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.Dz (Work.Spaces.pth G) p.1 p.2) ^ 2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) →
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.Dz G p.1 p.2) ^ 2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) →
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2
      * (Work.Spaces.DzIter 2 G p.1 p.2
          + ((p.1 - 3) / (1 + p.1)) * Work.Spaces.Dz G p.1 p.2) ^ 2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) →
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.pthIter 2 G p.1 p.2) ^ 2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) →
    (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.Dz (Work.Spaces.pth G) p.1 p.2) ^ 2)
      ≤ C * ((∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
            * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.Dz G p.1 p.2) ^ 2)
          + Real.sqrt ((∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
                * Work.FTS.EllipticEst.thEta p.2
                * (Work.Spaces.DzIter 2 G p.1 p.2
                    + ((p.1 - 3) / (1 + p.1)) * Work.Spaces.Dz G p.1 p.2) ^ 2)
              * (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
                  * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.pthIter 2 G p.1 p.2) ^ 2))) := by
  refine ⟨400, by norm_num, ?_⟩
  intro G hG htr0 htr1 hX hZ hXi hT
  -- abbreviations
  set ψ : ℝ → ℝ → ℝ := Work.Spaces.Dz G with hψdef
  set X : ℝ := ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2
      * (Work.Spaces.Dz (Work.Spaces.pth G) p.1 p.2) ^ 2 with hXdef
  set Z : ℝ := ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.Dz G p.1 p.2) ^ 2 with hZdef
  set DD : ℝ := ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2
      * (Work.Spaces.DzIter 2 G p.1 p.2
          + ((p.1 - 3) / (1 + p.1)) * Work.Spaces.Dz G p.1 p.2) ^ 2 with hDDdef
  set TT : ℝ := ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.pthIter 2 G p.1 p.2) ^ 2 with hTTdef
  have hψsm : Work.FTS.EllipticEst.SmoothOpen ψ := by rw [hψdef]; exact hG.Dz
  have hψpsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pth ψ) := hψsm.pth
  have hZnn : 0 ≤ Z := by
    rw [hZdef]
    refine MeasureTheory.setIntegral_nonneg (measurableSet_Ici.prod measurableSet_Icc)
      (fun p hp => ?_)
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hp.2))
      (sq_nonneg _)
  -- the Clairaut transfer
  have hae := ae_pth_sq_eq (G := G) hG
  have hXψ : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.pth ψ p.1 p.2) ^ 2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := hX.congr hae
  have hXid : X = ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.pth ψ p.1 p.2) ^ 2 := by
    rw [hXdef]
    exact MeasureTheory.integral_congr_ae hae
  -- the cut-off family and the convergence of the truncated functionals
  obtain ⟨χ, K, hχ⟩ := Work.FTS.EllSol.PkgK5.cutFam_exists
  obtain ⟨hAKint, hAKtend⟩ := cutIntegralTendsto (χ := χ) (K := K) hχ
    (F := Work.Spaces.pth ψ) hψpsm hXψ
  obtain ⟨hMKint, hMKtend⟩ := cutIntegralTendsto (χ := χ) (K := K) hχ
    (F := ψ) hψsm hZ
  have hXtend : Filter.Tendsto (fun k : ℕ => ∫ θ in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.thEta θ * Work.FTS.EllSol.PkgK5.cAK χ k ψ θ)
      Filter.atTop (nhds X) := by
    rw [hXid]
    exact hAKtend
  have hZtend : Filter.Tendsto (fun k : ℕ => ∫ θ in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.thEta θ * Work.FTS.EllSol.PkgK5.cMK χ k ψ θ)
      Filter.atTop (nhds Z) := by
    have h := hMKtend
    simp only [hψdef] at h
    rw [← hZdef] at h
    exact h
  -- the Agmon hypothesis of the engine
  have hAgmon : ∀ f : ℝ → ℝ,
      ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ : ℝ => f θ * deriv (deriv f) θ
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      (1 / 200) * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ - (∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ)
          + 2 * Work.Spaces.eta * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ) :=
    fun f hf h0 h1 h2 h3 h4 => sliceAgmonOpenCoreExplicit f hf h0 h1 h2 h3 h4
  -- the m_k facts
  have hmk : ∀ (k : ℕ) (θ : ℝ), θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
      → HasDerivAt (Work.FTS.EllSol.PkgK5.cMK χ k ψ)
          (2 * Work.FTS.EllSol.PkgK5.cPK χ k ψ θ) θ :=
    fun k θ hθ => Work.FTS.EllSol.PkgK5.InterpTrace.mK_hasDerivAt hχ k hψsm hθ
  have hmP : ∀ (k : ℕ) (θ : ℝ), θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
      → HasDerivAt (Work.FTS.EllSol.PkgK5.cPK χ k ψ)
          (Work.FTS.EllSol.PkgK5.cAK χ k ψ θ + Work.FTS.EllSol.PkgK5.cBK χ k ψ θ) θ :=
    fun k θ hθ => Work.FTS.EllSol.PkgK5.InterpTrace.mK_hasDerivAt_two hχ k hψsm hθ
  have hcont : ∀ k : ℕ, ContinuousOn (fun θ : ℝ => Work.FTS.EllSol.PkgK5.cAK χ k ψ θ
      + Work.FTS.EllSol.PkgK5.cBK χ k ψ θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    fun k => ((Work.FTS.EllSol.PkgK5.InterpTrace.continuousOn_mK hχ k hψsm).2.2.1).add
      ((Work.FTS.EllSol.PkgK5.InterpTrace.continuousOn_mK hχ k hψsm).2.2.2)
  have hmnn : ∀ (k : ℕ) (θ : ℝ), 0 ≤ Work.FTS.EllSol.PkgK5.cMK χ k ψ θ := by
    intro k θ
    unfold Work.FTS.EllSol.PkgK5.cMK
    refine intervalIntegral.integral_nonneg (Work.FTS.EllSol.PkgK5.cA_le_cB k)
      (fun u hu => ?_)
    have hu0 : 0 < u := lt_of_lt_of_le (Work.FTS.EllSol.PkgK5.cA_pos k) hu.1
    exact mul_nonneg (mul_nonneg (hχ.bnd k u hu0).1 (sq_nonneg _)) (sq_nonneg _)
  have hAnk : ∀ (k : ℕ) (θ : ℝ), 0 ≤ Work.FTS.EllSol.PkgK5.cAK χ k ψ θ := by
    intro k θ
    unfold Work.FTS.EllSol.PkgK5.cAK
    refine intervalIntegral.integral_nonneg (Work.FTS.EllSol.PkgK5.cA_le_cB k)
      (fun u hu => ?_)
    have hu0 : 0 < u := lt_of_lt_of_le (Work.FTS.EllSol.PkgK5.cA_pos k) hu.1
    exact mul_nonneg (mul_nonneg (hχ.bnd k u hu0).1 (sq_nonneg _)) (sq_nonneg _)
  have hcs : ∀ (k : ℕ) (θ : ℝ), θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
      → (Work.FTS.EllSol.PkgK5.cPK χ k ψ θ) ^ 2
        ≤ Work.FTS.EllSol.PkgK5.cMK χ k ψ θ * Work.FTS.EllSol.PkgK5.cAK χ k ψ θ :=
    fun k θ hθ => Work.FTS.EllSol.PkgK5.InterpTrace.cs_mK hχ k hψsm hθ
  have htr : ∀ k : ℕ,
      Filter.Tendsto (Work.FTS.EllSol.PkgK5.cMK χ k ψ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)
        ∧ Filter.Tendsto (Work.FTS.EllSol.PkgK5.cMK χ k ψ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    intro k
    refine massK_tendsto_zero hχ k hψsm (fun z hz => ?_) (fun z hz => ?_) ?_
    · exact htr0 z hz
    · exact htr1 z hz
    · refine (hXψ.mono_set ?_).congr (Filter.Eventually.of_forall (fun p => by ring))
      intro p hp
      exact ⟨le_trans (le_of_lt (Work.FTS.EllSol.PkgK5.cA_pos k)) (Set.mem_Icc.mp hp.1).1,
        hp.2⟩
  -- σ-integrability of the truncated functionals
  have hAint : ∀ k : ℕ, MeasureTheory.IntegrableOn (fun θ : ℝ =>
      Work.FTS.EllSol.PkgK5.cAK χ k ψ θ * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
    fun k => (hAKint k).congr (Filter.Eventually.of_forall (fun θ => mul_comm _ _))
  have hmInt : ∀ k : ℕ, MeasureTheory.IntegrableOn (fun θ : ℝ =>
      Work.FTS.EllSol.PkgK5.cMK χ k ψ θ * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
    fun k => (hMKint k).congr (Filter.Eventually.of_forall (fun θ => mul_comm _ _))
  have hBint : ∀ k : ℕ, MeasureTheory.IntegrableOn (fun θ : ℝ =>
      Work.FTS.EllSol.PkgK5.cBK χ k ψ θ * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
    fun k => (cBK_integrable (χ := χ) (K := K) hχ k hG hXi hT hZ).congr
      (Filter.Eventually.of_forall (fun θ => mul_comm _ _))
  -- the per-k chain
  have hperk : ∀ k : ℕ, (1 / 200) * (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.thEta θ * Work.FTS.EllSol.PkgK5.cAK χ k ψ θ)
      ≤ 2 * Work.Spaces.eta * (∫ θ in Work.Spaces.Iθ,
          Work.FTS.EllipticEst.thEta θ * Work.FTS.EllSol.PkgK5.cMK χ k ψ θ)
        - ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ
          * Work.FTS.EllSol.PkgK5.cBK χ k ψ θ := by
    intro k
    have h := agmonChainShift hAgmon (hmk k) (hmP k) (hcont k) (hmnn k) (hAnk k) (hcs k)
      (htr k).1 (htr k).2 (hAint k) (hmInt k) (hBint k)
    have e1 : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllSol.PkgK5.cAK χ k ψ θ
        * Work.FTS.EllipticEst.thEta θ)
        = ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ
          * Work.FTS.EllSol.PkgK5.cAK χ k ψ θ :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
    have e2 : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllSol.PkgK5.cMK χ k ψ θ
        * Work.FTS.EllipticEst.thEta θ)
        = ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ
          * Work.FTS.EllSol.PkgK5.cMK χ k ψ θ :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
    have e3 : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllSol.PkgK5.cBK χ k ψ θ
        * Work.FTS.EllipticEst.thEta θ)
        = ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ
          * Work.FTS.EllSol.PkgK5.cBK χ k ψ θ :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
    rw [e1, e2, e3] at h
    exact h
  -- the radial IBP bound
  have hbk : ∀ k : ℕ, - (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ
        * Work.FTS.EllSol.PkgK5.cBK χ k ψ θ)
      ≤ Real.sqrt (DD * TT) + (K / Real.log ((k : ℝ) + 2)) * Real.sqrt (Z * TT) := by
    intro k
    have h := cutBkBound (χ := χ) (K := K) hχ k hG hXi hT hZ
      (cBK_integrable (χ := χ) (K := K) hχ k hG hXi hT hZ)
    rw [← hDDdef, ← hTTdef, ← hZdef] at h
    exact h
  -- the per-k estimate
  have hbound : ∀ k : ℕ, (1 / 200) * (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.thEta θ * Work.FTS.EllSol.PkgK5.cAK χ k ψ θ)
      ≤ 2 * Work.Spaces.eta * (∫ θ in Work.Spaces.Iθ,
          Work.FTS.EllipticEst.thEta θ * Work.FTS.EllSol.PkgK5.cMK χ k ψ θ)
        + Real.sqrt (DD * TT) + (K / Real.log ((k : ℝ) + 2)) * Real.sqrt (Z * TT) := by
    intro k
    have h1 := hperk k
    have h2 := hbk k
    linarith
  -- the limit
  have hlimR : Filter.Tendsto (fun k : ℕ => 2 * Work.Spaces.eta
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ
            * Work.FTS.EllSol.PkgK5.cMK χ k ψ θ)
      + Real.sqrt (DD * TT) + (K / Real.log ((k : ℝ) + 2)) * Real.sqrt (Z * TT))
      Filter.atTop (nhds (2 * Work.Spaces.eta * Z + Real.sqrt (DD * TT))) := by
    have hlog : Filter.Tendsto (fun k : ℕ => K / Real.log ((k : ℝ) + 2))
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun k : ℕ => ((k : ℝ) + 2)) Filter.atTop Filter.atTop :=
        tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      have h2 : Filter.Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 2)) Filter.atTop
          Filter.atTop := Real.tendsto_log_atTop.comp h1
      simpa using h2.const_div_atTop K
    have h := ((hZtend.const_mul (2 * Work.Spaces.eta)).add_const (Real.sqrt (DD * TT))).add
      (hlog.mul_const (Real.sqrt (Z * TT)))
    simpa using h
  have hmain : (1 / 200) * X ≤ 2 * Work.Spaces.eta * Z + Real.sqrt (DD * TT) :=
    le_of_tendsto_of_tendsto (hXtend.const_mul (1 / 200)) hlimR
      (Filter.Eventually.of_forall (fun k => hbound k))
  -- final arithmetic
  have hη : (2 : ℝ) * Work.Spaces.eta = 99 / 50 := by norm_num [Work.Spaces.eta]
  have hsnn : 0 ≤ Real.sqrt (DD * TT) := Real.sqrt_nonneg _
  have h1 : X ≤ 200 * (2 * Work.Spaces.eta * Z + Real.sqrt (DD * TT)) := by linarith
  have h2 : 200 * (2 * Work.Spaces.eta * Z + Real.sqrt (DD * TT))
      ≤ 400 * (Z + Real.sqrt (DD * TT)) := by
    nlinarith [hZnn, hsnn, hη]
  exact le_trans h1 h2

end Work.FTS.EllSol.PkgK5.TraceEngine
end
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.divSinK5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.PkgK5

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

theorem divSinK5 (k : ℕ) (hk : 1 ≤ k) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (Φ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen Φ →
      (∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k → ContDiffOn ℝ Work.Stability.smoothOrder
        (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ) (Set.Ioo 0 (Real.pi / 2))) →
      (∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k → Filter.Tendsto
        (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) →
      (∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k → Filter.Tendsto
        (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
      Work.Spaces.HkMem α k (Work.Spaces.pth Φ) →
      Work.Spaces.HkMem α k (fun z θ => Φ z θ / Real.sin (2 * θ)) ∧
      Work.Spaces.HkNorm α k (fun z θ => Φ z θ / Real.sin (2 * θ))
        ≤ C * Work.Spaces.HkNorm α k (Work.Spaces.pth Φ) := by
  obtain ⟨K, hKpos, hperz⟩ := perSliceCmpK k hk
  refine ⟨Real.sqrt K, Real.sqrt_pos.mpr hKpos, ?_⟩
  intro α Φ hα hα1 hSO hsl ht0 ht1 hmem
  set U : ℝ → ℝ → ℝ := fun z θ => Φ z θ / Real.sin (2 * θ) with hUdef
  have hcmp : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k U z θ)
        ≤ K * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.pth Φ) z θ) :=
    fun z hz => (hperz α Φ hα hα1 hSO hsl ht0 ht1 hmem z hz).2
  have hint : ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k U z θ)
        Work.Spaces.Iθ :=
    fun z hz => (hperz α Φ hα hα1 hSO hsl ht0 ht1 hmem z hz).1
  have hsq : Work.Spaces.HkSq α k U ≤ K * Work.Spaces.HkSq α k (Work.Spaces.pth Φ) := by
    rw [Work.Spaces.HkSq, Work.Spaces.HkSq, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun z =>
      MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k U z θ)
      (hmem.2.const_mul K) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    exact hcmp z hz
  have hnorm : Work.Spaces.HkNorm α k U
      ≤ Real.sqrt K * Work.Spaces.HkNorm α k (Work.Spaces.pth Φ) := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, ← Real.sqrt_mul hKpos.le]
    exact Real.sqrt_le_sqrt hsq
  have hmemQ : Work.Spaces.HkMem α k U := by
    refine ⟨hint, ?_⟩
    have hKnn : ∀ z ∈ Work.Spaces.Iz, 0 ≤ ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k U z θ :=
      fun z _ => MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k U z θ
    refine MeasureTheory.Integrable.mono' (hmem.2.const_mul K) ?_ ?_
    · have hSOQ : Work.FTS.EllipticEst.SmoothOpen U := by
        rw [hUdef]
        exact Work.FTS.EllipticEst.RPFresh.smoothOpen_div_sin hSO
      have hprod : AEStronglyMeasurable
          (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k U p.1 p.2)
          ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
            (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)))) := by
        rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
        exact (hSOQ.continuousOn_HkIntegrand α k).aestronglyMeasurable
          (isOpen_Ioi.prod isOpen_Ioo).measurableSet
      have h2 : AEStronglyMeasurable
          (fun z => ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.Spaces.HkIntegrand α k U z θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
        have h1 := hprod.integral_prod_right'
        rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
        exact h1
      have hfun : (fun z => ∫ θ in Set.Ioo 0 (Real.pi / 2),
            Work.Spaces.HkIntegrand α k U z θ)
          = fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k U z θ := by
        funext z
        exact MeasureTheory.setIntegral_congr_set
          (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
            (b := Real.pi / 2))
      rw [← hfun]
      exact h2
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      rw [Real.norm_of_nonneg (hKnn z hz)]
      exact hcmp z hz
  refine ⟨?_, ?_⟩
  · simpa only [hUdef] using hmemQ
  · simpa only [hUdef] using hnorm

end Work.FTS.EllSol.PkgK5
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SourceBound.dzPsiLimits =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 800000

local notation "Iθ" => Work.Spaces.Iθ
local notation "sEta" => Work.FTS.EllipticEst.sEta
local notation "ψ" => Work.Elliptic.sinCos2

/-! ## The weak class descends in the level -/

theorem EllWeakPos_of_le_level {α : ℝ} {k l : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hkl : l ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    Work.FTS.EllipticEst.TT.EllWeakPos α l F Ψ := by
  obtain ⟨hsw1, hsw2, hsw3, hsw4⟩ := Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h 0
  have hFso : Work.FTS.EllipticEst.SmoothOpen F := hsw1
  have hAso : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    hsw3
  have hBso : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := hsw4
  exact ⟨h.eq, h.zero, h.pi_half, h.orthF, h.orthPsi, h.smooth,
    Work.FTS.EllipticEst.TT.HkMem_descend_open hkl
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall F).mp hFso) h.memF,
    Work.FTS.EllipticEst.TT.HkMem_descend_open hkl
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hAso) h.memA,
    Work.FTS.EllipticEst.TT.HkMem_descend_open hkl
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hBso) h.memB,
    Work.FTS.EllipticEst.TT.HkMem_descend_open hkl
      (Work.FTS.EllipticEst.TT.smoothOpen_diagHon
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hBso)) h.memZPth2⟩

/-! ## Elementary integrability helpers -/

/-- `sEta` is a.e. strongly measurable on `Iθ`. -/
theorem aesm_sEta_Iθ : AEStronglyMeasurable (fun θ => sEta θ) (volume.restrict Iθ) := by
  have h : AEStronglyMeasurable (fun θ => sEta θ)
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    continuousOn_sEta_Ioo.aestronglyMeasurable measurableSet_Ioo
  rwa [MeasureTheory.restrict_Ioo_eq_restrict_Icc] at h

/-- A bounded slice has an integrable `ψ`-moment. -/
theorem integrableOn_mul_sinCos2_of_abs_le {g : ℝ → ℝ} {M : ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict Iθ))
    (hbd : ∀ θ ∈ Iθ, |g θ| ≤ M) :
    MeasureTheory.IntegrableOn (fun θ => g θ * ψ θ) Iθ := by
  have hcont : Continuous ψ := by
    unfold Work.Elliptic.sinCos2
    exact Real.continuous_sin.mul (Real.continuous_cos.pow 2)
  have hψ : MeasureTheory.IntegrableOn (fun θ => |ψ θ|) Iθ :=
    (hcont.abs.continuousOn).integrableOn_compact isCompact_Icc
  refine Integrable.mono' (hψ.const_mul M) (hg.mul hcont.aestronglyMeasurable) ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hbd θ hθ) (abs_nonneg _)

/-- A bounded slice has an integrable constant multiple of `(c·g)² · sEta`. -/
theorem integrableOn_const_mul_sq_mul_sEta_of_abs_le {g : ℝ → ℝ} {c M : ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict Iθ))
    (hbd : ∀ θ ∈ Iθ, |g θ| ≤ M) :
    MeasureTheory.IntegrableOn (fun θ => (c * g θ) ^ 2 * sEta θ) Iθ := by
  have hdom : MeasureTheory.IntegrableOn (fun θ => c ^ 2 * (M ^ 2 * sEta θ)) Iθ :=
    (ws_sEta_integrableOn.const_mul (M ^ 2)).const_mul (c ^ 2)
  refine Integrable.mono' hdom (((hg.const_mul c).pow 2).mul aesm_sEta_Iθ) ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
  have h1 : |g θ| ≤ M := hbd θ hθ
  have h2 : (g θ) ^ 2 ≤ M ^ 2 := sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
  have h3 : 0 ≤ sEta θ := ws_sEta_nonneg hθ
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) h3), mul_pow]
  have h4 : c ^ 2 * (g θ) ^ 2 ≤ c ^ 2 * M ^ 2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg c)
  calc c ^ 2 * (g θ) ^ 2 * sEta θ ≤ c ^ 2 * M ^ 2 * sEta θ :=
        mul_le_mul_of_nonneg_right h4 h3
    _ = c ^ 2 * (M ^ 2 * sEta θ) := by ring

/-! ## The `∂_z`-slice of a weak datum -/

/-- **Smoothness of the `∂_z`-slice** on the open angular interval. -/
theorem dzSlice_contDiffOn {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    ∀ n : ℕ, ContDiffOn ℝ n (fun θ => Work.Spaces.pz Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) := by
  intro n
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  exact contDiffOn_iff_forall_nat_le.mp
    (Work.FTS.EllipticEst.SmoothOpen.curry_θ
      (Work.FTS.EllipticEst.SmoothOpen.pz hΨso) hz) n le_top

/-- **`(∂_θθ ∂_zΨ)² · sEta` is integrable.**  The second `θ`-derivative of the slice
`θ ↦ ∂_zΨ(z,θ)` is `∂_z(∂_θθΨ)`, the `i = 1` `D_z`-slot of `Work.Spaces.pthIter 2 Ψ`. -/
theorem dzSlice_secondDeriv_integrableOn {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hk : 2 ≤ k) (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun θ' => Work.Spaces.pz Ψ z θ') t) θ) ^ 2
        * sEta θ) Iθ := by
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hBso : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    smoothOpen_pthIter hΨso 2
  have h1 := Work.FTS.EllipticEst.remov.ws_slot_slice hBso h.memB 1 (by omega) hz
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2 * sEta θ) Iθ := by
    refine (h1.const_mul ((z ^ 2)⁻¹)).congr ?_
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    show (z ^ 2)⁻¹ * ((Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2 * sEta θ)
      = (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2 * sEta θ
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz]
    field_simp
  refine h2.congr ?_
  refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
  have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hcl : Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) z θ
      = Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ := pthIter2_pz_eqOn hΨso hQ
  show (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2 * sEta θ
    = (deriv (fun t => deriv (fun θ' => Work.Spaces.pz Ψ z θ') t) θ) ^ 2 * sEta θ
  rw [← hcl]
  rfl

/-- **Boundedness of the `∂_z`-slice** (and of its `θ`-derivative) on the open interval. -/
theorem dzSlice_bdd {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hk : 2 ≤ k) (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv (fun θ' => Work.Spaces.pz Ψ z θ') θ| ≤ C ∧ |Work.Spaces.pz Ψ z θ| ≤ C :=
  exists_bdd_of_sq_mul_sEta (dzSlice_contDiffOn h hz 2) (fun _ _ => rfl)
    (dzSlice_secondDeriv_integrableOn hk h hz)

/-- **`(∂_θ∂_zΨ(z,·))²` is integrable**, from the boundedness of the `θ`-derivative of the
slice and the finiteness of the angular interval. -/
theorem dzSlice_deriv_sq_integrableOn {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hk : 2 ≤ k) (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun θ' => Work.Spaces.pz Ψ z θ') θ) ^ 2) Iθ := by
  obtain ⟨C, hCpos, hCbd⟩ := dzSlice_bdd hk h hz
  refine Integrable.mono' (g := fun _ : ℝ => C ^ 2)
    (MeasureTheory.integrableOn_const ws_vol_Iθ_ne_top)
    ((measurable_deriv (fun θ' => Work.Spaces.pz Ψ z θ')).aestronglyMeasurable.pow 2) ?_
  filter_upwards [ws_ae_mem_Ioo] with θ hθ
  have h1 : |deriv (fun θ' => Work.Spaces.pz Ψ z θ') θ| ≤ C := (hCbd θ hθ).1
  have h2 : (deriv (fun θ' => Work.Spaces.pz Ψ z θ') θ) ^ 2 ≤ C ^ 2 :=
    sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact h2

/-- **`(∂_zΨ(z,·))²` is integrable**: the slice is bounded on the closed angular interval
(`weakSliceBounds`) and the interval has finite measure. -/
theorem dzSlice_sq_integrableOn {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hk : 2 ≤ k) (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pz Ψ z θ) ^ 2) Iθ := by
  obtain ⟨M, hMnn, hMbd⟩ := weakSliceBounds hk h z hz
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have haesm : AEStronglyMeasurable (fun θ => Work.Spaces.pz Ψ z θ) (volume.restrict Iθ) :=
    Work.FTS.EllipticEst.remov.ws_aesm_slice (Work.FTS.EllipticEst.SmoothOpen.pz hΨso) hz
  refine Integrable.mono' (g := fun _ : ℝ => M ^ 2)
    (MeasureTheory.integrableOn_const ws_vol_Iθ_ne_top) (haesm.pow 2) ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
  have h1 : |Work.Spaces.pz Ψ z θ| ≤ M := (hMbd θ hθ).2.2.1
  have h2 : (Work.Spaces.pz Ψ z θ) ^ 2 ≤ M ^ 2 :=
    sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact h2

/-- **`(∂_z F(z,·))² · sEta` is integrable** — the `i = 1` `D_z`-slot of `HkMem α k F`. -/
theorem dzSource_sq_integrableOn {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hk : 2 ≤ k) (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pz F z θ) ^ 2 * sEta θ) Iθ := by
  obtain ⟨hsw1, -, -, -⟩ := Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h 0
  have hFso : Work.FTS.EllipticEst.SmoothOpen F := hsw1
  have h1 := Work.FTS.EllipticEst.remov.ws_slot_slice hFso h.memF 1 (by omega) hz
  refine (h1.const_mul ((z ^ 2)⁻¹)).congr ?_
  refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
  show (z ^ 2)⁻¹ * ((Work.Spaces.DzIter 1 F z θ) ^ 2 * sEta θ)
    = (Work.Spaces.pz F z θ) ^ 2 * sEta θ
  simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz]
  field_simp

/-- **`(z ∂_z²Ψ(z,·))² · sEta` is integrable** — the `i = 0` `D_z`-slot of
`HkMem α k (z²∂_z²Ψ)`. -/
theorem zSlice2_sq_integrableOn {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hk : 2 ≤ k) (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (z * Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * sEta θ) Iθ := by
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hAso : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.H2W.smoothOpen_zsq hΨso
  have h1 := Work.FTS.EllipticEst.remov.ws_slot_slice hAso h.memA 0 (by omega) hz
  refine (h1.const_mul ((z ^ 2)⁻¹)).congr ?_
  refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
  show (z ^ 2)⁻¹ * ((Work.Spaces.DzIter 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      z θ) ^ 2 * sEta θ) = (z * Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * sEta θ
  simp only [Work.Spaces.DzIter_zero]
  field_simp

/-- **`(∂_z(z²∂_z²Ψ)(z,·))² · sEta` is integrable** — the `i = 1` `D_z`-slot of
`HkMem α k (z²∂_z²Ψ)`. -/
theorem pzZsqSlice2_sq_integrableOn {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hk : 2 ≤ k) (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
        * sEta θ) Iθ := by
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hAso : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.H2W.smoothOpen_zsq hΨso
  have h1 := Work.FTS.EllipticEst.remov.ws_slot_slice hAso h.memA 1 (by omega) hz
  refine (h1.const_mul ((z ^ 2)⁻¹)).congr ?_
  refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
  show (z ^ 2)⁻¹
      * ((Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
        * sEta θ)
    = (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2 * sEta θ
  simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz]
  field_simp

/-! ## The weighted `L²`-bound on `Lzero1 V` -/

/-- **`(Lzero1 V)² · sEta` is integrable**, where `V = θ ↦ ∂_zΨ(z,θ)`.  By
`sliceShiftedDecomposition`,

  `Lzero1 V = α(5+α)·V + α²·∂_z(z²∂_z²Ψ) + ∂_zF + (α²+5α)·z∂_z²Ψ`

on the open interval, and each of the four summands is a constant multiple of one of the four
integrable quantities `V`, `∂_z(z²∂_z²Ψ)`, `∂_zF`, `z∂_z²Ψ`. -/
theorem dzSlice_Lzero1_sq_integrableOn {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hk : 2 ≤ k) (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ) ^ 2
        * sEta θ) Iθ := by
  have hps : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hAso : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.H2W.smoothOpen_zsq hps
  obtain ⟨M, hMnn, hMbd⟩ := weakSliceBounds hk h z hz
  have hVbd : ∀ θ ∈ Iθ, |Work.Spaces.pz Ψ z θ| ≤ M := fun θ hθ => (hMbd θ hθ).2.2.1
  have hVaesm : AEStronglyMeasurable (fun θ => Work.Spaces.pz Ψ z θ) (volume.restrict Iθ) :=
    Work.FTS.EllipticEst.remov.ws_aesm_slice (Work.FTS.EllipticEst.SmoothOpen.pz hps) hz
  -- the four summands
  have ha : MeasureTheory.IntegrableOn
      (fun θ => (α * (5 + α) * Work.Spaces.pz Ψ z θ) ^ 2 * sEta θ) Iθ :=
    integrableOn_const_mul_sq_mul_sEta_of_abs_le (c := α * (5 + α)) hVaesm hVbd
  have hc : MeasureTheory.IntegrableOn
      (fun θ => (α ^ 2 * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        z θ) ^ 2 * sEta θ) Iθ := by
    refine ((pzZsqSlice2_sq_integrableOn hk h hz).const_mul ((α ^ 2) ^ 2)).congr ?_
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ _ => ?_)
    ring
  have hb : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pz F z θ) ^ 2 * sEta θ) Iθ := dzSource_sq_integrableOn hk h hz
  have hd : MeasureTheory.IntegrableOn
      (fun θ => ((α ^ 2 + 5 * α) * (z * Work.Spaces.pzIter 2 Ψ z θ)) ^ 2 * sEta θ) Iθ := by
    refine ((zSlice2_sq_integrableOn hk h hz).const_mul ((α ^ 2 + 5 * α) ^ 2)).congr ?_
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ _ => ?_)
    ring
  -- the pointwise identity of `sliceShiftedDecomposition`
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ
        = α * (5 + α) * Work.Spaces.pz Ψ z θ
          + α ^ 2 * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
          + (Work.Spaces.pz F z θ
            + (α ^ 2 + 5 * α) * (z * Work.Spaces.pzIter 2 Ψ z θ)) := by
    intro θ hθ
    have h1 := sliceShiftedDecomposition hk h z hz θ hθ
    linarith
  -- the dominating function: four times the sum of the four squares
  have hsum : MeasureTheory.IntegrableOn
      (fun θ => (α * (5 + α) * Work.Spaces.pz Ψ z θ
          + α ^ 2 * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
          + (Work.Spaces.pz F z θ
            + (α ^ 2 + 5 * α) * (z * Work.Spaces.pzIter 2 Ψ z θ))) ^ 2 * sEta θ) Iθ := by
    have hdom : MeasureTheory.IntegrableOn
        (fun θ => (4 * ((α * (5 + α) * Work.Spaces.pz Ψ z θ) ^ 2 * sEta θ)
          + 4 * ((α ^ 2 * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              z θ) ^ 2 * sEta θ))
          + (4 * ((Work.Spaces.pz F z θ) ^ 2 * sEta θ)
            + 4 * (((α ^ 2 + 5 * α) * (z * Work.Spaces.pzIter 2 Ψ z θ)) ^ 2 * sEta θ))) Iθ :=
      ((ha.const_mul 4).add (hc.const_mul 4)).add ((hb.const_mul 4).add (hd.const_mul 4))
    have haesm2 : AEStronglyMeasurable
        (fun θ => (α * (5 + α) * Work.Spaces.pz Ψ z θ
          + α ^ 2 * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
          + (Work.Spaces.pz F z θ
            + (α ^ 2 + 5 * α) * (z * Work.Spaces.pzIter 2 Ψ z θ))) ^ 2 * sEta θ)
        (volume.restrict Iθ) := by
      have hFso : Work.FTS.EllipticEst.SmoothOpen F :=
        (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h 0).1
      have h1 : AEStronglyMeasurable (fun θ => α * (5 + α) * Work.Spaces.pz Ψ z θ)
          (volume.restrict Iθ) := hVaesm.const_mul _
      have h2 : AEStronglyMeasurable (fun θ => Work.Spaces.pz F z θ)
          (volume.restrict Iθ) :=
        Work.FTS.EllipticEst.remov.ws_aesm_slice (Work.FTS.EllipticEst.SmoothOpen.pz hFso) hz
      have h3 : AEStronglyMeasurable
          (fun θ => Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)
          (volume.restrict Iθ) :=
        Work.FTS.EllipticEst.remov.ws_aesm_slice (Work.FTS.EllipticEst.SmoothOpen.pz hAso) hz
      have h4 : AEStronglyMeasurable (fun θ => z * Work.Spaces.pzIter 2 Ψ z θ)
          (volume.restrict Iθ) :=
        (Work.FTS.EllipticEst.remov.ws_aesm_slice
          (Work.FTS.EllipticEst.SmoothOpen.pzIter hps 2) hz).const_mul z
      exact (((h1.add (h3.const_mul _)).add (h2.add (h4.const_mul _))).pow 2).mul aesm_sEta_Iθ
    refine Integrable.mono' hdom haesm2 ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
    have h3 : 0 ≤ sEta θ := ws_sEta_nonneg hθ
    have h4 : 0 ≤ (α * (5 + α) * Work.Spaces.pz Ψ z θ
        + α ^ 2 * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        + (Work.Spaces.pz F z θ
          + (α ^ 2 + 5 * α) * (z * Work.Spaces.pzIter 2 Ψ z θ))) ^ 2 := sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h4 h3)]
    nlinarith [sq_nonneg (α * (5 + α) * Work.Spaces.pz Ψ z θ
        - (α ^ 2 * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)),
      sq_nonneg (α * (5 + α) * Work.Spaces.pz Ψ z θ - Work.Spaces.pz F z θ),
      sq_nonneg (α * (5 + α) * Work.Spaces.pz Ψ z θ
        - (α ^ 2 + 5 * α) * (z * Work.Spaces.pzIter 2 Ψ z θ)),
      sq_nonneg (α ^ 2 * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        - Work.Spaces.pz F z θ),
      sq_nonneg (α ^ 2 * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        - (α ^ 2 + 5 * α) * (z * Work.Spaces.pzIter 2 Ψ z θ)),
      sq_nonneg (Work.Spaces.pz F z θ
        - (α ^ 2 + 5 * α) * (z * Work.Spaces.pzIter 2 Ψ z θ)),
      sq_nonneg (α * (5 + α) * Work.Spaces.pz Ψ z θ),
      sq_nonneg (α ^ 2 * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ),
      sq_nonneg (Work.Spaces.pz F z θ),
      sq_nonneg ((α ^ 2 + 5 * α) * (z * Work.Spaces.pzIter 2 Ψ z θ))]
  refine hsum.congr ?_
  refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
  dsimp only
  rw [hpt θ hθ]

/-- **The unweighted square of the source is integrable** (the `sEta ≥ 1` version of
`dzSlice_Lzero1_sq_integrableOn`), which is the hypothesis of the right-endpoint lemma
`coerc.slice_limit_at_right_eq_zero`. -/
theorem dzSlice_Lzero1_sq_integrableOn_plain {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hk : 2 ≤ k) (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ) ^ 2) Iθ := by
  refine Integrable.mono' (g := fun θ => (Work.FTS.EllipticEst.Lzero1
      (fun t => Work.Spaces.pz Ψ z t) θ) ^ 2 * sEta θ)
    (dzSlice_Lzero1_sq_integrableOn hk h hz) ?_ ?_
  · have hcont : ContinuousOn (Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t))
        (Set.Ioo 0 (Real.pi / 2)) :=
      (Work.FTS.EllipticEst.remov.SliceTopAux.contDiffOnLzero1 0
        (by simpa using dzSlice_contDiffOn h hz 2)).continuousOn
    have h1 : AEStronglyMeasurable
        (fun θ => (Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ) ^ 2)
        (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
      (hcont.aestronglyMeasurable measurableSet_Ioo).pow 2
    rwa [MeasureTheory.restrict_Ioo_eq_restrict_Icc] at h1
  · filter_upwards [ws_ae_mem_Ioo] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact le_mul_of_one_le_right (sq_nonneg _) (ws_one_le_sEta hθ)

/-! ## Integrability of the `ψ`-moments of the summands -/

/-- `(D_zΨ(z,·)) · ψ` is integrable (the slice is bounded). -/
theorem integrableOn_DzMulSinCos2 {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.Dz Ψ z θ * ψ θ) Iθ := by
  obtain ⟨M, hMnn, hMbd⟩ := weakSliceBounds hk h z hz
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  refine integrableOn_mul_sinCos2_of_abs_le (g := fun θ => Work.Spaces.Dz Ψ z θ) (M := z * M)
    ((Work.FTS.EllipticEst.remov.ws_aesm_slice
      (Work.FTS.EllipticEst.SmoothOpen.pz hΨso) hz).const_mul z) ?_
  intro θ hθ
  rw [show Work.Spaces.Dz Ψ z θ = z * Work.Spaces.pz Ψ z θ from rfl, abs_mul, abs_of_pos hz]
  exact mul_le_mul_of_nonneg_left ((hMbd θ hθ).2.2.1) hz.le

/-- `(z² ∂_z²Ψ(z,·)) · ψ` is integrable. -/
theorem integrableOn_zsqPzIter2MulSinCos2 {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ) Iθ := by
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hAso : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.H2W.smoothOpen_zsq hΨso
  exact (Work.FTS.EllipticEst.remov.ws_absMoment
    (Work.FTS.EllipticEst.remov.ws_aesm_slice hAso hz)
    (Work.FTS.EllipticEst.remov.ws_slot_slice hAso h.memA 0 (by omega) hz)).1

/-- `(∂_z(z² ∂_z²Ψ)(z,·)) · ψ` is integrable. -/
theorem integrableOn_pzZsqSlice2MulSinCos2 {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ)
      Iθ := by
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hAso : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.H2W.smoothOpen_zsq hΨso
  exact (Work.FTS.EllipticEst.remov.ws_absMoment
    (Work.FTS.EllipticEst.remov.ws_aesm_slice (Work.FTS.EllipticEst.SmoothOpen.pz hAso) hz)
    (pzZsqSlice2_sq_integrableOn hk h hz)).1

/-- `(∂_z F(z,·)) · ψ` is integrable. -/
theorem integrableOn_pzFMulSinCos2 {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pz F z θ * ψ θ) Iθ := by
  have hFso : Work.FTS.EllipticEst.SmoothOpen F :=
    (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h 0).1
  exact (Work.FTS.EllipticEst.remov.ws_absMoment
    (Work.FTS.EllipticEst.remov.ws_aesm_slice (Work.FTS.EllipticEst.SmoothOpen.pz hFso) hz)
    (dzSource_sq_integrableOn hk h hz)).1

/-- `(z ∂_z²Ψ(z,·)) · ψ` is integrable. -/
theorem integrableOn_zPzIter2MulSinCos2 {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ) Iθ := by
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  exact (Work.FTS.EllipticEst.remov.ws_absMoment
    ((Work.FTS.EllipticEst.remov.ws_aesm_slice
      (Work.FTS.EllipticEst.SmoothOpen.pzIter hΨso 2) hz).const_mul z)
    (zSlice2_sq_integrableOn hk h hz)).1

/-- `(D_z²Ψ(z,·)) · ψ` is integrable (`D_z²Ψ = D_zΨ + z²∂_z²Ψ`). -/
theorem integrableOn_DzIter2MulSinCos2 {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.DzIter 2 Ψ z θ * ψ θ) Iθ := by
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  refine ((integrableOn_DzMulSinCos2 hk h hz).add
    (integrableOn_zsqPzIter2MulSinCos2 hk h hz)).congr ?_
  refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
  show Work.Spaces.Dz Ψ z θ * ψ θ + (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ
      = Work.Spaces.DzIter 2 Ψ z θ * ψ θ
  have h2 := Work.FTS.EllipticEst.H2W.zsq_pzIter2_eq hΨso hz hθ
  rw [show Work.Spaces.DzIter 2 Ψ z θ
      = Work.Spaces.Dz Ψ z θ + z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ from by linarith]
  ring

/-- `(D_z³Ψ(z,·)) · ψ` is integrable (`D_z³Ψ = D_z²Ψ + D_z(z²∂_z²Ψ)`). -/
theorem integrableOn_DzIter3MulSinCos2 {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => Work.Spaces.DzIter 3 Ψ z θ * ψ θ) Iθ := by
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hAso : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.H2W.smoothOpen_zsq hΨso
  have hA : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        * ψ θ) Iθ :=
    (Work.FTS.EllipticEst.remov.ws_absMoment
      (Work.FTS.EllipticEst.remov.ws_aesm_slice
        (Work.FTS.EllipticEst.SmoothOpen.DzIter hAso 1) hz)
      (Work.FTS.EllipticEst.remov.ws_slot_slice hAso h.memA 1 (by omega) hz)).1
  refine ((integrableOn_DzIter2MulSinCos2 hk h hz).add hA).congr ?_
  refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
  show Work.Spaces.DzIter 2 Ψ z θ * ψ θ
      + Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ
      = Work.Spaces.DzIter 3 Ψ z θ * ψ θ
  have h3 := Work.FTS.EllipticEst.H2W.DzIter_three_eq hΨso hz hθ
  rw [show Work.Spaces.DzIter 3 Ψ z θ
      = Work.Spaces.DzIter 2 Ψ z θ
        + Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      from h3]
  ring

/-! ## The four angular moments -/

/-- **`∫_θ ∂_zΨ(z,θ) sinθcos²θ = 0`**, because the left-hand side is `F_*(D_zΨ)(z)/z`. -/
theorem moment_pzPsi {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Iθ, Work.Spaces.pz Ψ z θ * ψ θ) = 0 := by
  have hk2 : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ := EllWeakPos_of_le_level (by omega) h
  have hFst := Work.FTS.EllipticEst.H2W.Fstar_DzIter_le_Psi α F Ψ hk2 1 (by omega) z hz
  rw [show Work.Spaces.DzIter 1 Ψ = Work.Spaces.Dz Ψ from rfl,
    Work.FTS.EllipticEst.H2W.Fstar_Dz_eq Ψ z, Work.Elliptic.Fstar] at hFst
  exact (mul_eq_zero.mp hFst).resolve_left hz.ne'

/-- **`∫_θ ∂_zF(z,θ) sinθcos²θ = 0`**, because the left-hand side is `F_*(D_zF)(z)/z`. -/
theorem moment_pzF {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Iθ, Work.Spaces.pz F z θ * ψ θ) = 0 := by
  have hFst := Work.FTS.EllipticEst.remov.Fstar_DzIter_one_of_two_le hk h z hz
  rw [show Work.Spaces.DzIter 1 F = Work.Spaces.Dz F from rfl,
    Work.FTS.EllipticEst.H2W.Fstar_Dz_eq F z, Work.Elliptic.Fstar] at hFst
  exact (mul_eq_zero.mp hFst).resolve_left hz.ne'

/-- **`∫_θ z ∂_z²Ψ(z,θ) sinθcos²θ = 0`**, from `D_z²Ψ = D_zΨ + z²∂_z²Ψ` and
`F_*(D_z²Ψ) = F_*(D_zΨ) = 0`. -/
theorem moment_zPzIter2 {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Iθ, (z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ) = 0 := by
  have hk2 : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ := EllWeakPos_of_le_level (by omega) h
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hIntDz := integrableOn_DzMulSinCos2 hk h hz
  have hIntz2 := integrableOn_zsqPzIter2MulSinCos2 hk h hz
  have hFst := Work.FTS.EllipticEst.H2W.Fstar_DzIter_le_Psi α F Ψ hk2 2 (by omega) z hz
  rw [Work.Elliptic.Fstar] at hFst
  have hcongr : (fun θ => Work.Spaces.DzIter 2 Ψ z θ * ψ θ)
      =ᵐ[volume.restrict Iθ]
        (fun θ => Work.Spaces.Dz Ψ z θ * ψ θ + (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ) := by
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    dsimp only
    have h2 := Work.FTS.EllipticEst.H2W.zsq_pzIter2_eq hΨso hz hθ
    rw [show Work.Spaces.DzIter 2 Ψ z θ
        = Work.Spaces.Dz Ψ z θ + z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ from by linarith]
    ring
  have hsum : (∫ θ in Iθ, Work.Spaces.Dz Ψ z θ * ψ θ)
      + (∫ θ in Iθ, (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ) = 0 := by
    rw [← MeasureTheory.integral_add (f := fun θ => Work.Spaces.Dz Ψ z θ * ψ θ)
      (g := fun θ => (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ) hIntDz hIntz2]
    rw [← MeasureTheory.integral_congr_ae hcongr]
    exact hFst
  have hDz0 : (∫ θ in Iθ, Work.Spaces.Dz Ψ z θ * ψ θ) = 0 := by
    rw [show (fun θ => Work.Spaces.Dz Ψ z θ * ψ θ)
        = fun θ => z * (Work.Spaces.pz Ψ z θ * ψ θ) from by
      funext θ; simp only [Work.Spaces.Dz]; ring,
      MeasureTheory.integral_const_mul, moment_pzPsi hk h hz, mul_zero]
  have hz2P : (∫ θ in Iθ, (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ) = 0 := by
    rw [hDz0, zero_add] at hsum
    exact hsum
  have hmid : (∫ θ in Iθ, Work.Spaces.pzIter 2 Ψ z θ * ψ θ) = 0 := by
    have h1 : (∫ θ in Iθ, (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ)
        = z ^ 2 * (∫ θ in Iθ, Work.Spaces.pzIter 2 Ψ z θ * ψ θ) := by
      rw [show (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ)
          = fun θ => z ^ 2 * (Work.Spaces.pzIter 2 Ψ z θ * ψ θ) from by
        funext θ; ring,
        MeasureTheory.integral_const_mul]
    rw [h1] at hz2P
    exact (mul_eq_zero.mp hz2P).resolve_left (pow_ne_zero 2 hz.ne')
  rw [show (fun θ => (z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ)
      = fun θ => z * (Work.Spaces.pzIter 2 Ψ z θ * ψ θ) from by funext θ; ring,
    MeasureTheory.integral_const_mul, hmid, mul_zero]

/-- **`∫_θ ∂_z(z²∂_z²Ψ)(z,θ) sinθcos²θ = 0`**, from `D_z(z²∂_z²Ψ) = D_z³Ψ - D_z²Ψ` and the
vanishing of `F_*(D_z²Ψ)`, `F_*(D_z³Ψ)`. -/
theorem moment_pzZsqSlice2 {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Iθ,
        Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ) = 0 := by
  have hk2 : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ := EllWeakPos_of_le_level (by omega) h
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hAso : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.H2W.smoothOpen_zsq hΨso
  have hIntA : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        * ψ θ) Iθ :=
    (Work.FTS.EllipticEst.remov.ws_absMoment
      (Work.FTS.EllipticEst.remov.ws_aesm_slice
        (Work.FTS.EllipticEst.SmoothOpen.DzIter hAso 1) hz)
      (Work.FTS.EllipticEst.remov.ws_slot_slice hAso h.memA 1 (by omega) hz)).1
  have hInt2 := integrableOn_DzIter2MulSinCos2 hk h hz
  have hInt3 := integrableOn_DzIter3MulSinCos2 hk h hz
  have hmain : (∫ θ in Iθ,
      Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ) = 0 := by
    have hFst3 := Work.FTS.EllipticEst.H2W.Fstar_DzIter_le_Psi α F Ψ hk2 3 (by omega) z hz
    have hFst2 := Work.FTS.EllipticEst.H2W.Fstar_DzIter_le_Psi α F Ψ hk2 2 (by omega) z hz
    rw [Work.Elliptic.Fstar] at hFst3 hFst2
    have hcongr : (fun θ => Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ
          z θ) z θ * ψ θ)
        =ᵐ[volume.restrict Iθ]
          (fun θ => Work.Spaces.DzIter 3 Ψ z θ * ψ θ
            - Work.Spaces.DzIter 2 Ψ z θ * ψ θ) := by
      refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
      show Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ
          = Work.Spaces.DzIter 3 Ψ z θ * ψ θ - Work.Spaces.DzIter 2 Ψ z θ * ψ θ
      have h3 := Work.FTS.EllipticEst.H2W.DzIter_zsq_pzIter2_eq hΨso 1 hz hθ
      rw [show (1 + 2 : ℕ) = 3 from rfl, show (1 + 1 : ℕ) = 2 from rfl] at h3
      rw [h3]
      ring
    have hsplit : (∫ θ in Iθ,
          Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ)
        = (∫ θ in Iθ, Work.Spaces.DzIter 3 Ψ z θ * ψ θ)
          - (∫ θ in Iθ, Work.Spaces.DzIter 2 Ψ z θ * ψ θ) :=
      (MeasureTheory.integral_congr_ae hcongr).trans
        (MeasureTheory.integral_sub (f := fun θ => Work.Spaces.DzIter 3 Ψ z θ * ψ θ)
          (g := fun θ => Work.Spaces.DzIter 2 Ψ z θ * ψ θ) hInt3 hInt2)
    rw [hsplit, hFst3, hFst2, sub_zero]
  have hkey : (∫ θ in Iθ, Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        * ψ θ)
      = z⁻¹ * (∫ θ in Iθ,
          Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
            * ψ θ) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae ?_
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    dsimp only
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz]
    field_simp
  rw [hkey, hmain, mul_zero]

/-! ## The angular moment of `Lzero1 V` -/

/-- **The angular moment of the source of the `∂_z`-slice vanishes.** -/
theorem dzSlice_Lzero1_moment {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Iθ,
      Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ * ψ θ) = 0 := by
  have hps : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  obtain ⟨M, hMnn, hMbd⟩ := weakSliceBounds hk h z hz
  -- integrability of the four moments
  have hI1 : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pz Ψ z θ * ψ θ) Iθ :=
    integrableOn_mul_sinCos2_of_abs_le
      (Work.FTS.EllipticEst.remov.ws_aesm_slice (Work.FTS.EllipticEst.SmoothOpen.pz hps) hz)
      (fun θ hθ => (hMbd θ hθ).2.2.1)
  have hI2 := integrableOn_pzFMulSinCos2 hk h hz
  have hI3 := integrableOn_pzZsqSlice2MulSinCos2 hk h hz
  have hI4 := integrableOn_zPzIter2MulSinCos2 hk h hz
  -- the pointwise identity
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ
        = α * (5 + α) * Work.Spaces.pz Ψ z θ
          + (Work.Spaces.pz F z θ
            + (α ^ 2 * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
              + (α ^ 2 + 5 * α) * (z * Work.Spaces.pzIter 2 Ψ z θ))) := by
    intro θ hθ
    have h1 := sliceShiftedDecomposition hk h z hz θ hθ
    linarith
  have hae : (fun θ => Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ * ψ θ)
      =ᵐ[volume.restrict Iθ]
        (fun θ => (α * (5 + α) * Work.Spaces.pz Ψ z θ
          + (Work.Spaces.pz F z θ
            + (α ^ 2 * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
              + (α ^ 2 + 5 * α) * (z * Work.Spaces.pzIter 2 Ψ z θ)))) * ψ θ) := by
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    show Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.pz Ψ z t) θ * ψ θ
      = (α * (5 + α) * Work.Spaces.pz Ψ z θ
          + (Work.Spaces.pz F z θ
            + (α ^ 2 * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
              + (α ^ 2 + 5 * α) * (z * Work.Spaces.pzIter 2 Ψ z θ)))) * ψ θ
    rw [hpt θ hθ]
  have hFun : (fun θ => (α * (5 + α) * Work.Spaces.pz Ψ z θ
        + (Work.Spaces.pz F z θ
          + (α ^ 2 * Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
            + (α ^ 2 + 5 * α) * (z * Work.Spaces.pzIter 2 Ψ z θ)))) * ψ θ)
      = fun θ => α * (5 + α) * (Work.Spaces.pz Ψ z θ * ψ θ)
        + (Work.Spaces.pz F z θ * ψ θ
          + (α ^ 2 * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ)
            + (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ))) := by
    funext θ; ring
  rw [MeasureTheory.integral_congr_ae hae, hFun]
  -- the four moments, and the additivity of the integral
  have hA : (∫ θ in Iθ, α * (5 + α) * (Work.Spaces.pz Ψ z θ * ψ θ)) = 0 := by
    rw [MeasureTheory.integral_const_mul, moment_pzPsi hk h hz, mul_zero]
  have hB : (∫ θ in Iθ, Work.Spaces.pz F z θ * ψ θ) = 0 := moment_pzF hk h hz
  have hC : (∫ θ in Iθ,
      α ^ 2 * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ)) = 0 := by
    rw [MeasureTheory.integral_const_mul, moment_pzZsqSlice2 hk h hz, mul_zero]
  have hD : (∫ θ in Iθ, (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ)) = 0 := by
    rw [MeasureTheory.integral_const_mul, moment_zPzIter2 hk h hz, mul_zero]
  -- integrability of the summands, in the exact lambda shapes
  have hI1L : Integrable (fun θ => α * (5 + α) * (Work.Spaces.pz Ψ z θ * ψ θ))
      (volume.restrict Iθ) := hI1.const_mul (α * (5 + α))
  have hI3L : Integrable (fun θ => α ^ 2
      * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ))
      (volume.restrict Iθ) := hI3.const_mul (α ^ 2)
  have hI4L : Integrable (fun θ => (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ))
      (volume.restrict Iθ) := hI4.const_mul (α ^ 2 + 5 * α)
  have hI34 : Integrable (fun θ => α ^ 2
        * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ)
        + (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ)) (volume.restrict Iθ) :=
    (hI3L.add hI4L).congr (by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ _
      simp only [Pi.add_apply])
  have hI234 : Integrable (fun θ => Work.Spaces.pz F z θ * ψ θ
        + (α ^ 2 * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ)
          + (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ))) (volume.restrict Iθ) :=
    (hI2.add hI34).congr (by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ _
      simp only [Pi.add_apply])
  have hI1234 : Integrable (fun θ => α * (5 + α) * (Work.Spaces.pz Ψ z θ * ψ θ)
        + (Work.Spaces.pz F z θ * ψ θ
          + (α ^ 2 * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ)
            + (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ))))
      (volume.restrict Iθ) :=
    (hI1L.add hI234).congr (by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ _
      simp only [Pi.add_apply])
  have hBC : (∫ θ in Iθ, Work.Spaces.pz F z θ * ψ θ
        + (α ^ 2 * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ)
          + (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ)))
      = (∫ θ in Iθ, Work.Spaces.pz F z θ * ψ θ)
        + (∫ θ in Iθ,
            α ^ 2 * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ)
            + (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ)) :=
    MeasureTheory.integral_add (f := fun θ => Work.Spaces.pz F z θ * ψ θ)
      (g := fun θ => α ^ 2 * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          z θ * ψ θ) + (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ))
      hI2 hI34
  have hCD : (∫ θ in Iθ,
        α ^ 2 * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ)
          + (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ))
      = (∫ θ in Iθ,
          α ^ 2 * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ))
        + (∫ θ in Iθ, (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ)) :=
    MeasureTheory.integral_add
      (f := fun θ => α ^ 2 * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        z θ * ψ θ))
      (g := fun θ => (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ))
      hI3L hI4L
  calc (∫ θ in Iθ, α * (5 + α) * (Work.Spaces.pz Ψ z θ * ψ θ)
        + (Work.Spaces.pz F z θ * ψ θ
          + (α ^ 2 * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ)
            + (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ))))
      = (∫ θ in Iθ, α * (5 + α) * (Work.Spaces.pz Ψ z θ * ψ θ))
        + (∫ θ in Iθ, Work.Spaces.pz F z θ * ψ θ
          + (α ^ 2 * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ)
            + (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ))) :=
        MeasureTheory.integral_add
          (f := fun θ => α * (5 + α) * (Work.Spaces.pz Ψ z θ * ψ θ))
          (g := fun θ => Work.Spaces.pz F z θ * ψ θ
            + (α ^ 2 * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ)
              + (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ)))
          hI1L hI234
    _ = (∫ θ in Iθ, α * (5 + α) * (Work.Spaces.pz Ψ z θ * ψ θ))
        + ((∫ θ in Iθ, Work.Spaces.pz F z θ * ψ θ)
          + (∫ θ in Iθ,
              α ^ 2 * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ)
              + (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ))) := by rw [hBC]
    _ = (∫ θ in Iθ, α * (5 + α) * (Work.Spaces.pz Ψ z θ * ψ θ))
        + ((∫ θ in Iθ, Work.Spaces.pz F z θ * ψ θ)
          + ((∫ θ in Iθ,
              α ^ 2 * (Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * ψ θ))
            + (∫ θ in Iθ, (α ^ 2 + 5 * α) * ((z * Work.Spaces.pzIter 2 Ψ z θ) * ψ θ)))) := by
        rw [hCD]
    _ = 0 := by rw [hA, hB, hC, hD]; ring

theorem dzPsiLimits {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ z, 0 < z →
      Filter.Tendsto (fun θ => Work.Spaces.pz Ψ z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun θ => Work.Spaces.pz Ψ z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  intro z hz
  constructor
  · -- the left endpoint: the angular moment of the source vanishes
    exact sliceTendstoZeroOfMoment (fun θ => Work.Spaces.pz Ψ z θ) (dzSlice_contDiffOn h hz 2)
      (dzSlice_secondDeriv_integrableOn hk h hz) (dzSlice_Lzero1_sq_integrableOn hk h hz)
      (dzSlice_sq_integrableOn hk h hz) (dzSlice_Lzero1_moment hk h hz)
  · -- the right endpoint: the limit exists, and is zero because `Lzero1 V ∈ L²`
    obtain ⟨-, ν, hν⟩ :=
      Work.FTS.EllipticEst.remov.coerc.tendsTo_atEnds_of_integrableOn_sq_deriv
        (u := fun θ => Work.Spaces.pz Ψ z θ) (L := Real.pi / 2) (by linarith [Real.pi_pos])
        (dzSlice_contDiffOn h hz 2) (dzSlice_deriv_sq_integrableOn hk h hz)
    have hν0 : ν = 0 :=
      Work.FTS.EllipticEst.remov.coerc.slice_limit_at_right_eq_zero
        (u := fun θ => Work.Spaces.pz Ψ z θ) (ν := ν) (dzSlice_contDiffOn h hz 2)
        (dzSlice_sq_integrableOn hk h hz) (dzSlice_deriv_sq_integrableOn hk h hz)
        (dzSlice_Lzero1_sq_integrableOn_plain hk h hz) hν
    simpa [hν0] using hν

end Work.FTS.EllipticEst.remov.SourceBound
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeL2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison

noncomputable section

set_option autoImplicit false

set_option maxHeartbeats 1000000


theorem SlotsZeroModeL2 {α : ℝ} {Φ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hHk : Work.Spaces.HkMem α 6 (fun z θ => Φ z θ / Work.Construction.s2 θ)) :
    (∀ m : ℕ,
      MeasureTheory.LocallyIntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) (Set.Ioi 0) ∧
      MeasureTheory.IntegrableOn (fun z => (∫ θ in Work.Spaces.Iθ,
        Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2 * z ^ (-4 : ℝ))
        (Set.Ioi 0)) ∧
    (∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => |Φ z θ|) Work.Spaces.Iθ) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ z ∈ Set.Ioi (0 : ℝ),
      ∫ θ in Work.Spaces.Iθ, |Φ z θ|
        ≤ C * Real.sqrt (Work.FTS.StrongEps.EComparison.sliceEnergy Φ z)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ z ∈ Set.Ioi (0 : ℝ), ∀ δ ∈ Set.Ioc (0 : ℝ) (π / 4),
      (∫ θ in Set.Ioo 0 δ, |Φ z θ|
          ≤ C * Real.sqrt (Work.FTS.StrongEps.EComparison.sliceEnergy Φ z)
              * δ ^ ((3 + Work.Spaces.eta) / 2)) ∧
      (∫ θ in Set.Ioo (π / 2 - δ) (π / 2), |Φ z θ|
          ≤ C * Real.sqrt (Work.FTS.StrongEps.EComparison.sliceEnergy Φ z)
              * δ ^ ((3 + Work.Spaces.eta) / 2))) ∧
    (∀ a b : ℝ, 0 < a → a ≤ b →
      MeasureTheory.IntegrableOn (fun z => Real.sqrt (Work.FTS.StrongEps.EComparison.sliceEnergy Φ z))
        (Set.Icc a b)) ∧
    (∀ a b : ℝ, 0 < a → a ≤ b →
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        Φ z θ ^ 2 * Work.FTS.StrongEps.EComparison.rootWeight θ) (Set.Icc a b)) ∧
    (∀ a b : ℝ, 0 < a → a ≤ b →
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, |Φ z θ|) (Set.Icc a b)) := by
  have hHk' : Work.Spaces.HkMem α 6 (psi Φ) := hHk
  have hHk_int : MeasureTheory.IntegrableOn (fun z => sliceHk α Φ z) Work.Spaces.Iz := hHk.2
  -- ### the `(0,0)`-slot of `Ψ` is `θ`-integrable for `z > 0`
  have hint : ∀ z ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn
      (fun θ => (psi Φ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) Work.Spaces.Iθ :=
    fun z hz => integrableOn_psi_sq_rpow hsm hHk' hz
  -- ### conjunct 2 : `|Φ z ·|` is `θ`-integrable on `Iθ`
  have claim2 : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => |Φ z θ|) Work.Spaces.Iθ :=
    fun z hz => integrableOn_abs_Phi hsm hz (hint z hz)
  -- ### conjunct 3 : the slice Cauchy–Schwarz bound
  have claim3 : ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Set.Ioi (0 : ℝ),
      ∫ θ in Work.Spaces.Iθ, |Φ z θ| ≤ C * Real.sqrt (sliceEnergy Φ z) := by
    refine ⟨K3, K3_pos, fun z hz => ?_⟩
    calc ∫ θ in Work.Spaces.Iθ, |Φ z θ|
        ≤ Real.sqrt (sliceEnergy Φ z)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta)) :=
          slice_abs_le_sqrt hint hz (fun _ hθ => hθ)
      _ ≤ Real.sqrt (sliceEnergy Φ z) * K3 :=
          mul_le_mul_of_nonneg_left sqrt_sin_int_Iθ_le (Real.sqrt_nonneg _)
      _ = K3 * Real.sqrt (sliceEnergy Φ z) := by ring
  have claim3c := claim3
  obtain ⟨C3, hC3pos, hC3⟩ := claim3c
  -- ### conjunct 4 : the boundary-layer decay
  have claim4 : ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Set.Ioi (0 : ℝ), ∀ δ ∈ Set.Ioc (0 : ℝ) (π / 4),
      (∫ θ in Set.Ioo 0 δ, |Φ z θ|
          ≤ C * Real.sqrt (sliceEnergy Φ z) * δ ^ ((3 + Work.Spaces.eta) / 2)) ∧
      (∫ θ in Set.Ioo (π / 2 - δ) (π / 2), |Φ z θ|
          ≤ C * Real.sqrt (sliceEnergy Φ z) * δ ^ ((3 + Work.Spaces.eta) / 2)) := by
    refine ⟨K4, K4_pos, fun z hz δ hδ => ?_⟩
    obtain ⟨hδ0, hδ4⟩ := hδ
    obtain ⟨hL, hR⟩ := sqrt_sin_int_layer_le hδ0 hδ4
    have hsub1 : Set.Ioo (0 : ℝ) δ ⊆ Work.Spaces.Iθ := fun θ hθ =>
      ⟨le_of_lt hθ.1, by linarith [hθ.2, hδ4, Real.pi_pos]⟩
    have hsub2 : Set.Ioo (π / 2 - δ) (π / 2) ⊆ Work.Spaces.Iθ := fun θ hθ =>
      ⟨by linarith [hθ.1, hδ4, Real.pi_pos], le_of_lt hθ.2⟩
    have h1 := slice_abs_le_sqrt hint hz hsub1
    have h2 := slice_abs_le_sqrt hint hz hsub2
    refine ⟨?_, ?_⟩
    · calc ∫ θ in Set.Ioo 0 δ, |Φ z θ|
          ≤ Real.sqrt (sliceEnergy Φ z)
              * Real.sqrt (∫ θ in Set.Ioo 0 δ, (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta)) := h1
        _ ≤ Real.sqrt (sliceEnergy Φ z) * (K4 * δ ^ ((3 + Work.Spaces.eta) / 2)) :=
            mul_le_mul_of_nonneg_left hL (Real.sqrt_nonneg _)
        _ = K4 * Real.sqrt (sliceEnergy Φ z) * δ ^ ((3 + Work.Spaces.eta) / 2) := by ring
    · calc ∫ θ in Set.Ioo (π / 2 - δ) (π / 2), |Φ z θ|
          ≤ Real.sqrt (sliceEnergy Φ z)
              * Real.sqrt (∫ θ in Set.Ioo (π / 2 - δ) (π / 2),
                  (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta)) := h2
        _ ≤ Real.sqrt (sliceEnergy Φ z) * (K4 * δ ^ ((3 + Work.Spaces.eta) / 2)) :=
            mul_le_mul_of_nonneg_left hR (Real.sqrt_nonneg _)
        _ = K4 * Real.sqrt (sliceEnergy Φ z) * δ ^ ((3 + Work.Spaces.eta) / 2) := by ring
  -- ### the `z`-integrability of `sliceHk` on compact subintervals of `(0,∞)`
  have hSliceHk_Icc : ∀ a b : ℝ, 0 < a → a ≤ b →
      MeasureTheory.IntegrableOn (fun z => sliceHk α Φ z) (Set.Icc a b) := fun a b ha _ =>
    hHk_int.mono_set (fun z hz => le_trans (le_of_lt ha) hz.1)
  have hOne_Icc : ∀ a b : ℝ, 0 < a → a ≤ b →
      MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b) := by
    intro a b _ _
    haveI : MeasureTheory.IsFiniteMeasure (volume.restrict (Set.Icc a b)) := ⟨by
      rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Icc]
      exact ENNReal.ofReal_lt_top⟩
    exact MeasureTheory.integrable_const (1 : ℝ)
  -- ### conjunct 6 : `sliceEnergy` is `z`-integrable on `[a,b]`
  have claim6 : ∀ a b : ℝ, 0 < a → a ≤ b → MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Φ z θ ^ 2 * rootWeight θ) (Set.Icc a b) := by
    intro a b ha hab
    have hs : Set.Icc a b ⊆ Work.Spaces.Iz := fun z hz => le_trans (le_of_lt ha) hz.1
    have hAESM : AEStronglyMeasurable
        (fun z => ∫ θ in Work.Spaces.Iθ, Φ z θ ^ 2 * rootWeight θ)
        (volume.restrict (Set.Icc a b)) :=
      aesm_sliceIntegral_of_subset (continuousOn_PhiSqRoot hsm) hs measurableSet_Icc
    refine MeasureTheory.Integrable.mono'
      ((hSliceHk_Icc a b ha hab).add (hOne_Icc a b ha hab)) hAESM ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with z hz
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    rw [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ,
      Φ z θ ^ 2 * rootWeight θ from sliceEnergy_nonneg Φ z)]
    exact le_trans (sliceEnergy_le_sliceHk hHk' hz0) (le_add_of_nonneg_right zero_le_one)
  -- ### conjunct 5 : `√(sliceEnergy)` is `z`-integrable on `[a,b]`
  have claim5 : ∀ a b : ℝ, 0 < a → a ≤ b → MeasureTheory.IntegrableOn
      (fun z => Real.sqrt (sliceEnergy Φ z)) (Set.Icc a b) := by
    intro a b ha hab
    have hs : Set.Icc a b ⊆ Work.Spaces.Iz := fun z hz => le_trans (le_of_lt ha) hz.1
    have hAESM : AEStronglyMeasurable (fun z => Real.sqrt (sliceEnergy Φ z))
        (volume.restrict (Set.Icc a b)) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable
        (aesm_sliceIntegral_of_subset (continuousOn_PhiSqRoot hsm) hs measurableSet_Icc)
    refine MeasureTheory.Integrable.mono'
      ((hSliceHk_Icc a b ha hab).add (hOne_Icc a b ha hab)) hAESM ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with z hz
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact le_trans (Real.sqrt_le_sqrt (sliceEnergy_le_sliceHk hHk' hz0))
      (sqrt_le_add_one (sliceHk_nonneg Φ z))
  -- ### conjunct 7 : the slice integral `∫_θ |Φ z θ|` is `z`-integrable on `[a,b]`
  have claim7 : ∀ a b : ℝ, 0 < a → a ≤ b → MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, |Φ z θ|) (Set.Icc a b) := by
    intro a b ha hab
    have hs : Set.Icc a b ⊆ Work.Spaces.Iz := fun z hz => le_trans (le_of_lt ha) hz.1
    have hAESM : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ, |Φ z θ|)
        (volume.restrict (Set.Icc a b)) :=
      aesm_sliceIntegral_of_subset (continuousOn_absPhi hsm) hs measurableSet_Icc
    refine MeasureTheory.Integrable.mono'
      (((hSliceHk_Icc a b ha hab).add (hOne_Icc a b ha hab)).const_mul C3) hAESM ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with z hz
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun θ => abs_nonneg _)]
    calc ∫ θ in Work.Spaces.Iθ, |Φ z θ| ≤ C3 * Real.sqrt (sliceEnergy Φ z) := hC3 z hz0
      _ ≤ C3 * (sliceHk α Φ z + 1) :=
          mul_le_mul_of_nonneg_left
            (le_trans (Real.sqrt_le_sqrt (sliceEnergy_le_sliceHk hHk' hz0))
              (sqrt_le_add_one (sliceHk_nonneg Φ z))) (le_of_lt hC3pos)
  -- ### conjunct 1 : the modal coefficients
  obtain ⟨Ce, hCe, heFam⟩ := Work.FTS.PhiStar.Series.eFam_sup_le
  have claim1 : ∀ m : ℕ, MeasureTheory.LocallyIntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ,
          Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) (Set.Ioi 0) ∧
      MeasureTheory.IntegrableOn (fun z => (∫ θ in Work.Spaces.Iθ,
        Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2
          * z ^ (-4 : ℝ)) (Set.Ioi 0) := by
    intro m
    -- the pointwise moment bound
    have hmode_le : ∀ z : ℝ, 0 < z → |modeCoeff Φ m z| ≤
        Ce * ((m : ℝ) + 1) * (∫ θ in Work.Spaces.Iθ, |Φ z θ|) := by
      intro z hz
      have hint2 := claim2 z hz
      have hbnd : ∀ θ ∈ Work.Spaces.Iθ,
          |Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ| ≤
            (Ce * ((m : ℝ) + 1)) * |Φ z θ| := by
        intro θ hθ
        have h1 : |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ Ce * ((m : ℝ) + 1) :=
          heFam m θ hθ
        have h2 : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
        have h3 : (0 : ℝ) ≤ Ce * ((m : ℝ) + 1) := by positivity
        calc |Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ|
            = |Φ z θ| * |Work.FTS.PhiStar.Gegenbauer.eFam m θ| * |Real.cos θ| := by
              rw [abs_mul, abs_mul]
          _ ≤ |Φ z θ| * (Ce * ((m : ℝ) + 1)) * 1 :=
              mul_le_mul (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) h2 (abs_nonneg _)
                (by positivity)
          _ = (Ce * ((m : ℝ) + 1)) * |Φ z θ| := by ring
      calc |modeCoeff Φ m z|
          = |∫ θ in Work.Spaces.Iθ,
              Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ| := by
            simp only [modeCoeff]
        _ ≤ ∫ θ in Work.Spaces.Iθ,
              |Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ| :=
            abs_integral_le_integral_abs
        _ ≤ ∫ θ in Work.Spaces.Iθ, (Ce * ((m : ℝ) + 1)) * |Φ z θ| :=
            MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ => abs_nonneg _)
              (hint2.const_mul _)
              (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hbnd)
        _ = Ce * ((m : ℝ) + 1) * ∫ θ in Work.Spaces.Iθ, |Φ z θ| :=
            MeasureTheory.integral_const_mul _ _
    have hmode_le' : ∀ z : ℝ, 0 < z → |modeCoeff Φ m z| ≤
        Ce * ((m : ℝ) + 1) * (C3 * Real.sqrt (sliceEnergy Φ z)) := by
      intro z hz
      refine le_trans (hmode_le z hz) ?_
      exact mul_le_mul_of_nonneg_left (hC3 z hz) (by positivity)
    -- a.e. strong measurability of the moment
    have haesm_m : ∀ {s : Set ℝ}, s ⊆ Work.Spaces.Iz → MeasurableSet s →
        AEStronglyMeasurable (fun z => modeCoeff Φ m z) (volume.restrict s) := by
      intro s hs hms
      exact aesm_sliceIntegral_of_subset (continuousOn_mode hsm m) hs hms
    have hzpow_aesm : AEStronglyMeasurable (fun z : ℝ => z ^ (-4 : ℝ))
        (volume.restrict (Set.Ioi 0)) :=
      (continuousOn_id.rpow_const (fun z hz => Or.inl (ne_of_gt hz))).aestronglyMeasurable
        measurableSet_Ioi
    refine ⟨?_, ?_⟩
    · -- local integrability in `z`
      rw [MeasureTheory.locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
      intro k hks hk
      rcases Set.eq_empty_or_nonempty k with hk0 | hne
      · rw [hk0]
        exact MeasureTheory.integrableOn_empty
      · obtain ⟨a, hak, ha⟩ := hk.exists_isMinOn hne continuous_id.continuousOn
        obtain ⟨b, hbk, hb⟩ := hk.exists_isMaxOn hne continuous_id.continuousOn
        have ha0 : 0 < a := hks hak
        have hab : a ≤ b := ha hbk
        have hs : Set.Icc a b ⊆ Work.Spaces.Iz := fun z hz => le_trans (le_of_lt ha0) hz.1
        have hInt : MeasureTheory.IntegrableOn (fun z => modeCoeff Φ m z) (Set.Icc a b) := by
          refine MeasureTheory.Integrable.mono'
            (((hSliceHk_Icc a b ha0 hab).add (hOne_Icc a b ha0 hab)).const_mul
              (Ce * ((m : ℝ) + 1) * C3)) (haesm_m hs measurableSet_Icc) ?_
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with z hz
          have hz0 : 0 < z := lt_of_lt_of_le ha0 hz.1
          rw [Real.norm_eq_abs]
          calc |modeCoeff Φ m z| ≤ Ce * ((m : ℝ) + 1) * (C3 * Real.sqrt (sliceEnergy Φ z)) :=
                hmode_le' z hz0
            _ ≤ Ce * ((m : ℝ) + 1) * (C3 * (sliceHk α Φ z + 1)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left
                    (le_trans (Real.sqrt_le_sqrt (sliceEnergy_le_sliceHk hHk' hz0))
                      (sqrt_le_add_one (sliceHk_nonneg Φ z))) (le_of_lt hC3pos))
                  (by positivity)
            _ = (Ce * ((m : ℝ) + 1) * C3) * (sliceHk α Φ z + 1) := by ring
        exact hInt.mono_set (fun z hz => ⟨ha hz, hb hz⟩)
    · -- integrability of the squared moment against `z^{-4}`
      have hdom : ∀ z ∈ Set.Ioi (0 : ℝ),
          ‖(modeCoeff Φ m z) ^ 2 * z ^ (-4 : ℝ)‖
            ≤ (Ce * ((m : ℝ) + 1) * C3) ^ 2 * sliceHk α Φ z := by
        intro z hz
        have hb := hmode_le' z hz
        have hsq : |modeCoeff Φ m z| ^ 2
            ≤ (Ce * ((m : ℝ) + 1) * C3) ^ 2 * sliceEnergy Φ z := by
          have h1 := pow_le_pow_left₀ (abs_nonneg _) hb 2
          have h2 : (Ce * ((m : ℝ) + 1) * (C3 * Real.sqrt (sliceEnergy Φ z))) ^ 2
              = (Ce * ((m : ℝ) + 1) * C3) ^ 2 * sliceEnergy Φ z := by
            rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (sliceEnergy_nonneg Φ z)]
            ring
          rwa [h2] at h1
        rw [Real.norm_eq_abs, abs_mul, abs_pow,
          abs_of_nonneg (Real.rpow_nonneg (le_of_lt hz) _)]
        calc |modeCoeff Φ m z| ^ 2 * z ^ (-4 : ℝ)
            ≤ ((Ce * ((m : ℝ) + 1) * C3) ^ 2 * sliceEnergy Φ z) * z ^ (-4 : ℝ) :=
              mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg (le_of_lt hz) _)
          _ = (Ce * ((m : ℝ) + 1) * C3) ^ 2 * (sliceEnergy Φ z * z ^ (-4 : ℝ)) := by ring
          _ ≤ (Ce * ((m : ℝ) + 1) * C3) ^ 2 * sliceHk α Φ z :=
              mul_le_mul_of_nonneg_left (sliceEnergy_mul_rpow_le_sliceHk hHk' hz) (sq_nonneg _)
      refine MeasureTheory.Integrable.mono'
        ((hHk_int.mono_set (s := Set.Ioi 0) (fun z hz => mem_Iz_of_mem_Ioi hz)).const_mul
          ((Ce * ((m : ℝ) + 1) * C3) ^ 2))
        (((haesm_m (fun z hz => mem_Iz_of_mem_Ioi hz) measurableSet_Ioi).pow 2).mul
          hzpow_aesm) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      exact hdom z hz
  exact ⟨claim1, claim2, claim3, claim4, claim5, claim6, claim7⟩


end

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.IbdLocalIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

-- `hab : a ≤ b` is part of the requested statement but is not needed: `Icc a b` is
-- contained in `Iz` as soon as `a > 0`, and is empty otherwise.
set_option linter.unusedVariables false

/-! ## The weighted angular energy `Ibd` is dominated by the `ℋ¹`-integrand

The pointwise core of the local integrability of `z ↦ Ibd α f z`: for `z > 0` the radial weight
satisfies `w(z)² ≥ 1`, so that the *single* `γ`-weighted slot

`(mixed 0 1 f z σ · Wt α z σ)² = sin(2σ)² (∂_θ f z σ)² w(z)² sin(2σ)^{-γ}`

of the `ℋ¹`-integrand dominates `sin(2σ)^{2-γ} (∂_θ f z σ)²` — indeed
`sin(2σ)² sin(2σ)^{-γ} = sin(2σ)^{2-γ}` and `w(z)² ≥ 1`.
-/

/-- `Ibd α f z` is nonnegative (its integrand is a nonnegative multiple of a square). -/
theorem Ibd_nonneg (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ Ibd α f z := by
  rw [Ibd, Work.Spaces.Iθ]
  refine MeasureTheory.integral_nonneg_of_ae ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
  exact mul_nonneg (Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])) _) (sq_nonneg _)

/-- **The weighted angular energy is dominated by the `ℋ¹`-integrand of the same slice.**
For `z > 0` the weight `w(z) = (1+z)²/z²` satisfies `w(z)² ≥ 1`, while the `ℋ¹`-integrand
contains the slot `(mixed 0 1 f z σ · Wt α z σ)² = sin(2σ)² (∂_θf)² w(z)² sin(2σ)^{-γ}`,
which is `sin(2σ)^{2-γ} (∂_θf)²` up to the factor `w(z)² ≥ 1`. -/
theorem Ibd_le_HkIntegrand {α : ℝ} {f : ℝ → ℝ → ℝ} (hm : Work.Spaces.HkMem α 1 f)
    {z : ℝ} (hz : 0 < z) :
    Ibd α f z ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ := by
  have hzIz : z ∈ Work.Spaces.Iz := le_of_lt hz
  rw [Ibd, Work.Spaces.Iθ]
  refine MeasureTheory.integral_mono_of_nonneg ?_ (hm.1 z hzIz) ?_
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
    exact mul_nonneg (Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])) _) (sq_nonneg _)
  · change ∀ᵐ θ ∂(volume.restrict (Set.Icc 0 (π / 2))),
      (fun σ => Real.sin (2 * σ) ^ (2 - Work.Spaces.gam α) * Work.Spaces.pth f z σ ^ 2) θ
        ≤ Work.Spaces.HkIntegrand α 1 f z θ
    -- the only angles where the comparison `sin(2θ)² sin(2θ)^{-γ} = sin(2θ)^{2-γ}` could fail
    -- are the two endpoints of `Iθ`, which form a null set
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null (t := ({0, π / 2} : Set ℝ)) ?_ ?_
    · intro θ hθ
      by_contra hnot
      refine hθ ?_
      intro hmem
      have h0 : θ ≠ 0 := by rintro rfl; exact hnot (by simp)
      have h2 : θ ≠ π / 2 := by rintro rfl; exact hnot (by simp)
      have hθ0 : 0 < θ := lt_of_le_of_ne hmem.1 (Ne.symm h0)
      have hθ1 : θ < π / 2 := lt_of_le_of_ne hmem.2 h2
      have hs : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      -- the square of the product weight `Wt = w·sin(2θ)^{-γ/2}`
      have hWt2 : (Work.Spaces.Wt α z θ) ^ 2
          = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
        rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow]
        congr 1
        rw [← Real.rpow_natCast (Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) 2,
            ← Real.rpow_mul (le_of_lt hs)]
        norm_num
      -- the exponent split `sin(2θ)^{2-γ} = sin(2θ)² · sin(2θ)^{-γ}`
      have hs2 : (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          = (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
        rw [show (2 : ℝ) - Work.Spaces.gam α = 2 + (-(Work.Spaces.gam α)) by ring,
            Real.rpow_add hs, Real.rpow_two]
      -- `w(z)² ≥ 1` for `z > 0`
      have hw1 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := by
        rw [Work.Spaces.w]
        have hle : (1 : ℝ) ≤ (1 + z) ^ 2 / z ^ 2 := by
          rw [le_div_iff₀ (by positivity)]
          nlinarith
        nlinarith
      refine le_trans ?_
        (Work.Spaces.sq_le_HkIntegrand_mixed α 1 f z θ 1 0 le_rfl (by norm_num))
      simp only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero,
        Work.Spaces.Dth, mul_pow, hWt2, hs2]
      have hABC : (0 : ℝ) ≤ Real.sin (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.pth f z θ) ^ 2 :=
        mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hs) _)) (sq_nonneg _)
      calc Real.sin (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.pth f z θ) ^ 2
          ≤ (Real.sin (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.pth f z θ) ^ 2) * (Work.Spaces.w z) ^ 2 :=
            le_mul_of_one_le_right hABC hw1
        _ = Real.sin (2 * θ) ^ 2 * (Work.Spaces.pth f z θ) ^ 2
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
    · rw [Set.Finite.measure_zero]
      exact (Set.finite_singleton (π / 2)).insert 0

/-- **Measurability of the weighted angular energy.**  For `f` smooth on the open quadrant the
uncurried integrand `(z,σ) ↦ sin(2σ)^{2-γ} (∂_θf z σ)²` is continuous on the open quadrant, hence
a.e. strongly measurable for the product of the restrictions of Lebesgue measure to `Iz` and `Iθ`
(`Work.Spaces.aesm_of_continuousOn_Qd`); Fubini's measurability theorem
(`MeasureTheory.AEStronglyMeasurable.integral_prod_right'`) then gives the a.e. strong
measurability of `z ↦ Ibd α f z` for the restriction of Lebesgue measure to `Iz`. -/
theorem aesm_Ibd {α : ℝ} {f : ℝ → ℝ → ℝ} (hso : Work.FTS.EllipticEst.SmoothOpen f) :
    MeasureTheory.AEStronglyMeasurable (fun z : ℝ => Ibd α f z)
      (volume.restrict Work.Spaces.Iz) := by
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α) * (Work.Spaces.pth f p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
        (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
    have h2 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.pth f p.1 p.2) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := ((hso.pth).continuousOn).pow 2
    exact h1.mul h2
  have h := (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'
  simpa [Ibd, Function.uncurry] using h

/-- **Local integrability of the weighted angular energy.**  With
`Ibd α f z = ∫_{σ ∈ Iθ} sin(2σ)^{2-γ} (∂_θ f z σ)² dσ` (defined in
`Submission/Work/FTS/StrongEps/EpsLocalPStar/JepsMarginalDefs.lean`, `γ = Work.Spaces.gam α`),
for `f` smooth on the open quadrant and `HkMem α 1 f`, the function `z ↦ Ibd α f z` is integrable
on every compact subinterval of `(0,∞)`.

Route: `1 ≤ w(z)²` and `sin(2σ)^{2-γ} ≤ w(z)² sin(2σ)^{-γ}`, so
`Ibd α f z ≤ ∫_σ HkIntegrand α 1 f z σ` for every `z > 0` (identify
`(mixed 0 1 f z σ * Wt α z σ)² = (∂_θ f z σ)² w(z)² sin(2σ)^{-γ}` and use
`Work.Spaces.sq_le_HkIntegrand_mixed` with `i = 1`, `j = 0`); integrate over `z ∈ [a,b] ⊆ Iz`
with `MeasureTheory.integral_mono_of_nonneg` and use `hm.2`.
Measurability of `z ↦ Ibd α f z` comes from the joint measurability of
`(z,σ) ↦ sin(2σ)^{2-γ} (∂_θ f z σ)²` on the open strip (`Work.Spaces.aesm_slice_of_continuousOn_Qd`,
`Work.Spaces.integrable_prod_of_iterated`; the product measures used in
`Submission/Work/FTS/EllipticEst/AeSlotOneAe/Interp/TkA_slotIntegrable.lean` are exactly the
right setting).
Declare the result in the namespace `Work.FTS.StrongEps.EpsLocalPStar`. -/
theorem IbdLocalIntegrable {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 1 f)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    MeasureTheory.IntegrableOn (fun z : ℝ => Ibd α f z) (Set.Icc a b) := by
  -- `[a,b] ⊆ (0,∞) ⊆ Iz`
  have hsub : Set.Icc a b ⊆ Work.Spaces.Iz := fun z hz => le_of_lt (lt_of_lt_of_le ha hz.1)
  have hle : volume.restrict (Set.Icc a b) ≤ volume.restrict Work.Spaces.Iz :=
    Measure.restrict_mono hsub le_rfl
  -- the dominating function is the `z`-slice of the `ℋ¹`-integrand, integrable on `Iz`
  have hdom : Integrable (fun z : ℝ =>
      ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ) (volume.restrict (Set.Icc a b)) :=
    MeasureTheory.Integrable.mono_measure hm.2 hle
  have haesm : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => Ibd α f z)
      (volume.restrict (Set.Icc a b)) := (aesm_Ibd hso).mono_measure hle
  refine MeasureTheory.Integrable.mono' hdom haesm ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun z hz => ?_
  rw [Real.norm_of_nonneg (Ibd_nonneg α f z)]
  exact Ibd_le_HkIntegrand hm (lt_of_lt_of_le ha hz.1)

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.AngSlotBounds2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.H5

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-!
# Angular slot bounds for the three `F_*`-angular profiles

This file proves `AngSlotBounds2`: for every `α ∈ (0,1]` there are constants `B0, B1 > 0` with
`|SAi α θ| ≤ B0` on `Iθ` and `|D_θ^j (SAi α ·)|(0,θ)| ≤ B1 · SGmj α θ` on `Iθ`, where
`SA0 α = αΓ/c`, `SA1 α = α D_θΓ/c` and `SA2 α = α D_θ²Γ/c` are the three angular profiles of
the scaled `F_*`-atoms and `SGmj α θ = Γ(θ)(α + sin 2θ)`.

Everything rests on the crude angular-jet bound `DthIter_Gam_abs_le6`
(`|D_θ^m Γ| ≤ 10⁵ Γ` for `m ≤ 6`), the majorant inequality `Γ ≤ SGmj/α` on `Iθ`, and
`c_bounds` (`1/10 ≤ c(α) ≤ 10`).  Concretely `B0 = B1 = 10⁶` works: the factor `α/c ≤ 10α`
supplies the `α` that is `≤ α + sin 2θ`, and the remaining `10⁶ Γ` is `≤ 10⁶ Γ(α + sin 2θ)`.
-/

/-- `sin (2θ) ≥ 0` on `Iθ = [0, π/2]`. -/
lemma AngSlot_sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩

/-- The `D_θ`-iterates of the `θ`-only function `SA0 α` are `(α/c)` times those of `Γ`. -/
lemma DthIter_SA0_repr' (α : ℝ) (i : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.FTS.StrongEps.ClassCRHS.SA0 α θ') z θ
      = (α / Work.Spaces.c α) * Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ := by
  have hfun : (fun t : ℝ => Work.FTS.StrongEps.ClassCRHS.SA0 α t)
      = (fun t : ℝ => (α / Work.Spaces.c α) * (fun s => Work.Spaces.Gam α s) t) := by
    funext t
    show α * (fun s => Work.Spaces.Gam α s) t / Work.Spaces.c α
        = (α / Work.Spaces.c α) * (fun s => Work.Spaces.Gam α s) t
    ring
  rw [Work.FTS.LocData.DthIter_rad_eq i (fun θ' => Work.FTS.StrongEps.ClassCRHS.SA0 α θ') z θ,
    hfun, Work.Spaces.dthU_iter_const_mul i (α / Work.Spaces.c α)
      (fun s => Work.Spaces.Gam α s)]

/-- The `D_θ`-iterates of `SA1 α = (α/c) D_θΓ` are `(α/c)` times those of `Γ`, shifted by one. -/
lemma DthIter_SA1_repr' (α : ℝ) (i : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.FTS.StrongEps.ClassCRHS.SA1 α θ') z θ
      = (α / Work.Spaces.c α) * Work.Spaces.dthU^[i + 1] (fun t => Work.Spaces.Gam α t) θ := by
  have hfun : (fun t : ℝ => Work.FTS.StrongEps.ClassCRHS.SA1 α t)
      = (fun t : ℝ => (α / Work.Spaces.c α)
          * Work.Spaces.dthU (fun s => Work.Spaces.Gam α s) t) := by
    funext t
    show α * Work.Spaces.dthU (fun s => Work.Spaces.Gam α s) t / Work.Spaces.c α
        = (α / Work.Spaces.c α) * Work.Spaces.dthU (fun s => Work.Spaces.Gam α s) t
    ring
  rw [Work.FTS.LocData.DthIter_rad_eq i (fun θ' => Work.FTS.StrongEps.ClassCRHS.SA1 α θ') z θ,
    hfun, Work.Spaces.dthU_iter_const_mul i (α / Work.Spaces.c α)
      (Work.Spaces.dthU (fun s => Work.Spaces.Gam α s)),
    Work.Spaces.dthU_iter_comp i (fun s => Work.Spaces.Gam α s)]

/-- The `D_θ`-iterates of `SA2 α = (α/c) D_θ²Γ` are `(α/c)` times those of `Γ`, shifted by two. -/
lemma DthIter_SA2_repr' (α : ℝ) (i : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.FTS.StrongEps.H5.SA2 α θ') z θ
      = (α / Work.Spaces.c α) * Work.Spaces.dthU^[i + 2] (fun t => Work.Spaces.Gam α t) θ := by
  have hfun : (fun t : ℝ => Work.FTS.StrongEps.H5.SA2 α t)
      = (fun t : ℝ => (α / Work.Spaces.c α)
          * Work.Spaces.dthU^[2] (fun s => Work.Spaces.Gam α s) t) := by
    funext t
    show α * Work.Spaces.dthU^[2] (fun s => Work.Spaces.Gam α s) t / Work.Spaces.c α
        = (α / Work.Spaces.c α) * Work.Spaces.dthU^[2] (fun s => Work.Spaces.Gam α s) t
    ring
  rw [Work.FTS.LocData.DthIter_rad_eq i (fun θ' => Work.FTS.StrongEps.H5.SA2 α θ') z θ, hfun,
    Work.Spaces.dthU_iter_const_mul i (α / Work.Spaces.c α)
      (Work.Spaces.dthU^[2] (fun s => Work.Spaces.Gam α s))]
  rw [← Function.iterate_add_apply]

/-- **The pointwise bound `|(α/c)·D_θ^mΓ| ≤ 10⁶`** for `m ≤ 6` on `Iθ`. -/
lemma AngProfAbsLe' (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    {m : ℕ} (hm : m ≤ 6) :
    |(α / Work.Spaces.c α) * Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
      ≤ 10 ^ 6 := by
  have hc := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith [hc.1]
  have hdc : 0 ≤ α / Work.Spaces.c α := div_nonneg hα.le hcpos.le
  have hdiv : α / Work.Spaces.c α ≤ 10 * α := by
    rw [div_le_iff₀ hcpos]; nlinarith [hc.1, hα]
  have hG := Work.Spaces.Gam_bounds α θ hα hθ
  have hjet : |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
      ≤ 100000 * Work.Spaces.Gam α θ := by
    rw [← Work.FTS.LocData.DthIter_rad_eq m (fun t => Work.Spaces.Gam α t) 0 θ]
    exact Work.FTS.LocData6.DthIter_Gam_abs_le6 m hm α hα hα1 hθ
  have hnn : 0 ≤ 100000 * Work.Spaces.Gam α θ := by nlinarith [hG.1]
  calc |(α / Work.Spaces.c α) * Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
      = (α / Work.Spaces.c α) * |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ| := by
        rw [abs_mul, abs_of_nonneg hdc]
    _ ≤ (α / Work.Spaces.c α) * (100000 * Work.Spaces.Gam α θ) :=
        mul_le_mul_of_nonneg_left hjet hdc
    _ ≤ (10 * α) * (100000 * Work.Spaces.Gam α θ) := mul_le_mul_of_nonneg_right hdiv hnn
    _ = 10 ^ 6 * (α * Work.Spaces.Gam α θ) := by ring
    _ ≤ 10 ^ 6 * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        simpa using mul_le_mul hα1 hG.2 hG.1 (by norm_num : (0 : ℝ) ≤ 1)
    _ = 10 ^ 6 := by norm_num

/-- **The pointwise jet bound `|(α/c)·D_θ^mΓ| ≤ 10⁶·SGmj α θ`** for `m ≤ 6` on `Iθ`. -/
lemma AngProfJetLe' (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    {m : ℕ} (hm : m ≤ 6) :
    |(α / Work.Spaces.c α) * Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
      ≤ 10 ^ 6 * Work.FTS.StrongEps.ClassCRHS.SGmj α θ := by
  have hc := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith [hc.1]
  have hdc : 0 ≤ α / Work.Spaces.c α := div_nonneg hα.le hcpos.le
  have hdiv : α / Work.Spaces.c α ≤ 10 * α := by
    rw [div_le_iff₀ hcpos]; nlinarith [hc.1, hα]
  have hG := Work.Spaces.Gam_bounds α θ hα hθ
  have hsin := AngSlot_sin_two_nonneg hθ
  have hjet : |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
      ≤ 100000 * Work.Spaces.Gam α θ := by
    rw [← Work.FTS.LocData.DthIter_rad_eq m (fun t => Work.Spaces.Gam α t) 0 θ]
    exact Work.FTS.LocData6.DthIter_Gam_abs_le6 m hm α hα hα1 hθ
  have hnn : 0 ≤ 100000 * Work.Spaces.Gam α θ := by nlinarith [hG.1]
  calc |(α / Work.Spaces.c α) * Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
      = (α / Work.Spaces.c α) * |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ| := by
        rw [abs_mul, abs_of_nonneg hdc]
    _ ≤ (α / Work.Spaces.c α) * (100000 * Work.Spaces.Gam α θ) :=
        mul_le_mul_of_nonneg_left hjet hdc
    _ ≤ (10 * α) * (100000 * Work.Spaces.Gam α θ) := mul_le_mul_of_nonneg_right hdiv hnn
    _ = 10 ^ 6 * (α * Work.Spaces.Gam α θ) := by ring
    _ ≤ 10 ^ 6 * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        calc α * Work.Spaces.Gam α θ ≤ (α + Real.sin (2 * θ)) * Work.Spaces.Gam α θ :=
              mul_le_mul_of_nonneg_right (by linarith) hG.1
          _ = Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) := by ring
    _ = 10 ^ 6 * Work.FTS.StrongEps.ClassCRHS.SGmj α θ := by
        rw [Work.FTS.StrongEps.ClassCRHS.SGmj]

/-- Angular slot bounds for the three `F_*`-angular profiles: `SA0 α θ = αΓ(θ)/c`,
`SA1 α θ = α D_θΓ(θ)/c` (`Work.FTS.StrongEps.ClassCRHS.SA0`, `SA1`) and
`SA2 α θ = α D_θ²Γ(θ)/c` (`Work.FTS.StrongEps.H5.SA2`), against the sharp majorant
`SGmj α θ = Γ(θ)(α + sin 2θ)`.

For each `α ∈ (0,1]` there are constants `B0, B1 > 0` with `|SAi α θ| ≤ B0` on `Iθ` and
`|DthIter j (fun _ θ' => SAi α θ') 0 θ| ≤ B1·SGmj α θ` for the indicated orders.  The proof is
immediate from the crude angular-jet bound `Work.FTS.LocData6.DthIter_Gam_abs_le6`
(`|D_θ^m Γ| ≤ 10⁵ Γ` for `m ≤ 6`), the majorant inequality `Γ ≤ SGmj/α` on `Iθ`, and
`Work.Spaces.c_bounds` (`1/10 ≤ c(α) ≤ 10`); the orders are chosen so that `SA0` needs `m ≤ 5`,
`SA1` needs `m ≤ 6` and `SA2` needs `m ≤ 6`. -/
theorem AngSlotBounds2 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ B0 B1 : ℝ, 0 < B0 ∧ 0 < B1 ∧
      (∀ θ ∈ Work.Spaces.Iθ, |Work.FTS.StrongEps.ClassCRHS.SA0 α θ| ≤ B0) ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ 5 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ θ' => Work.FTS.StrongEps.ClassCRHS.SA0 α θ') 0 θ|
          ≤ B1 * Work.FTS.StrongEps.ClassCRHS.SGmj α θ) ∧
      (∀ θ ∈ Work.Spaces.Iθ, |Work.FTS.StrongEps.ClassCRHS.SA1 α θ| ≤ B0) ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ 5 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ θ' => Work.FTS.StrongEps.ClassCRHS.SA1 α θ') 0 θ|
          ≤ B1 * Work.FTS.StrongEps.ClassCRHS.SGmj α θ) ∧
      (∀ θ ∈ Work.Spaces.Iθ, |Work.FTS.StrongEps.H5.SA2 α θ| ≤ B0) ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ θ' => Work.FTS.StrongEps.H5.SA2 α θ') 0 θ|
          ≤ B1 * Work.FTS.StrongEps.ClassCRHS.SGmj α θ) := by
  refine ⟨10 ^ 6, 10 ^ 6, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `|SA0| ≤ 10⁶`
    intro θ hθ
    have h := AngProfAbsLe' α hα hα1 hθ (m := 0) (by omega)
    have heq : Work.FTS.StrongEps.ClassCRHS.SA0 α θ
        = (α / Work.Spaces.c α) * Work.Spaces.dthU^[0] (fun t => Work.Spaces.Gam α t) θ := by
      rw [Function.iterate_zero_apply]
      simp only [Work.FTS.StrongEps.ClassCRHS.SA0]
      ring
    rw [heq]; exact h
  · -- the `SA0`-slots, `i ≤ 5`
    intro i hi1 hi5 θ hθ
    rw [DthIter_SA0_repr' α i 0 θ]
    exact AngProfJetLe' α hα hα1 hθ (by omega)
  · -- `|SA1| ≤ 10⁶`
    intro θ hθ
    have h := AngProfAbsLe' α hα hα1 hθ (m := 1) (by omega)
    have heq : Work.FTS.StrongEps.ClassCRHS.SA1 α θ
        = (α / Work.Spaces.c α) * Work.Spaces.dthU^[1] (fun t => Work.Spaces.Gam α t) θ := by
      rw [Function.iterate_one]
      simp only [Work.FTS.StrongEps.ClassCRHS.SA1]
      ring
    rw [heq]; exact h
  · -- the `SA1`-slots, `i ≤ 5`
    intro i hi1 hi5 θ hθ
    rw [DthIter_SA1_repr' α i 0 θ]
    exact AngProfJetLe' α hα hα1 hθ (by omega)
  · -- `|SA2| ≤ 10⁶`
    intro θ hθ
    have h := AngProfAbsLe' α hα hα1 hθ (m := 2) (by omega)
    have heq : Work.FTS.StrongEps.H5.SA2 α θ
        = (α / Work.Spaces.c α) * Work.Spaces.dthU^[2] (fun t => Work.Spaces.Gam α t) θ := by
      simp only [Work.FTS.StrongEps.H5.SA2]
      ring
    rw [heq]; exact h
  · -- the `SA2`-slots, `i ≤ 4`
    intro i hi1 hi4 θ hθ
    rw [DthIter_SA2_repr' α i 0 θ]
    exact AngProfJetLe' α hα hα1 hθ (by omega)

end

end Work.FTS.StrongEps.H5
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.HonestEasyMajorAsmB =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.Spaces
open Work.FTS.H2
open Work.H2.T1Q

namespace Work.FTS.StrongPersist.N6Trans.HonestEasyMajorAux

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! ## The per-summand bounds -/

/-- Each `D_z`-slot Leibniz summand (with the hard one removed) is integrable on the product
measure and bounded by `16` times the total. -/
theorem xD_summand_bound_q_o (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f g : ℝ → ℝ → ℝ)
    (Kf Kg K3 : ℝ) (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hdecg : Work.Spaces.DecayAll 4 g)
    (hmemf : Work.Spaces.HkMem α 4 f) (hmemg : Work.Spaces.HkMem α 4 g)
    (hKf : ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a f z θ| ≤ Kf)
    (hKg : ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a g z θ| ≤ Kg)
    (hKf0 : 0 ≤ Kf) (hKg0 : 0 ≤ Kg) (hK3 : 0 ≤ K3) (i b : ℕ) (hi : i ≤ 4) (hbi : b ≤ i) :
    MeasureTheory.Integrable
        (fun p : ℝ × ℝ => if i = 4 ∧ b = 0 then 0 else |xD f g i b p.1 p.2|)
        Work.FTS.H2.pm ∧
      ∫ p, (if i = 4 ∧ b = 0 then 0 else |xD f g i b p.1 p.2|) ∂Work.FTS.H2.pm
        ≤ 16 * TTot α f g Kf Kg K3 := by
  have hT := TTot_nonneg α f g Kf Kg K3 hKf0 hKg0 hK3
  by_cases hcase : i = 4 ∧ b = 0
  · have hz : (fun p : ℝ × ℝ => if i = 4 ∧ b = 0 then 0 else |xD f g i b p.1 p.2|)
        = fun _ => 0 := by funext p; rw [if_pos hcase]
    rw [hz]
    refine ⟨integrable_zero _ _ _, ?_⟩
    rw [MeasureTheory.integral_zero]
    exact mul_nonneg (by norm_num) hT
  · have hz : (fun p : ℝ × ℝ => if i = 4 ∧ b = 0 then 0 else |xD f g i b p.1 p.2|)
        = fun p => |xD f g i b p.1 p.2| := by funext p; rw [if_neg hcase]
    rw [hz]
    have hch : (i.choose b : ℝ) ≤ 16 := choose_le_16 hi hbi
    have hc0 : 0 ≤ (i.choose b : ℝ) := by positivity
    by_cases hb2 : b ≤ 2
    · have hib : i - b ≤ 3 := by
        by_contra hcon
        push_neg at hcon
        exact hcase ⟨by omega, by omega⟩
      obtain ⟨hslot_int, hslot_le⟩ := xD_Kf_int_q_o α g Kf hKf0 hg hmemg i b hi hib
      have hle : ∀ᵐ p ∂Work.FTS.H2.pm, |xD f g i b p.1 p.2| ≤ (i.choose b : ℝ) *
          (Kf * ((|Work.Spaces.mixed (i - b) 1 g p.1 p.2| * Wm α p.1 p.2)
            * (|Work.Spaces.DzIter i g p.1 p.2| * Whz p.1 p.2))) := by
        filter_upwards [ae_pm_z_pos_o, ae_pm_theta_mem_Ioo] with p hzpos hθ
        have hpt := xD_Kf_pt α hα f g Kf hKf0 hKf i b hi hbi hib hb2 p.1 p.2 hzpos hθ.1 hθ.2
        calc |xD f g i b p.1 p.2|
            ≤ (i.choose b : ℝ) * Kf * ((|Work.Spaces.mixed (i - b) 1 g p.1 p.2| * Wm α p.1 p.2)
              * (|Work.Spaces.DzIter i g p.1 p.2| * Whz p.1 p.2)) := hpt
          _ = (i.choose b : ℝ) * (Kf * ((|Work.Spaces.mixed (i - b) 1 g p.1 p.2| * Wm α p.1 p.2)
              * (|Work.Spaces.DzIter i g p.1 p.2| * Whz p.1 p.2))) := by ring
      obtain ⟨hint, hbd⟩ := xD_finish (f := f) (g := g) (i := i) (b := b) (c := (i.choose b : ℝ))
        (K := Kf * Work.Spaces.HkNorm α 4 g * Work.Spaces.HkNorm α 4 g)
        (S := fun p : ℝ × ℝ => Kf * ((|Work.Spaces.mixed (i - b) 1 g p.1 p.2| * Wm α p.1 p.2)
          * (|Work.Spaces.DzIter i g p.1 p.2| * Whz p.1 p.2)))
        hc0 hslot_int hslot_le hle (abs_aesm_pm (xD_aesm_q_o f g hf hg i b))
      refine ⟨hint, ?_⟩
      have hK : Kf * Work.Spaces.HkNorm α 4 g * Work.Spaces.HkNorm α 4 g
          = Kf * Work.Spaces.HkSq α 4 g := by
        have h2 : Work.Spaces.HkNorm α 4 g * Work.Spaces.HkNorm α 4 g
            = Work.Spaces.HkSq α 4 g := Real.mul_self_sqrt (Work.Spaces.HkSq_nonneg α 4 g)
        rw [mul_assoc, h2]
      calc ∫ p, |xD f g i b p.1 p.2| ∂Work.FTS.H2.pm
          ≤ (i.choose b : ℝ) * (Kf * Work.Spaces.HkNorm α 4 g * Work.Spaces.HkNorm α 4 g) := hbd
        _ = (i.choose b : ℝ) * (Kf * Work.Spaces.HkSq α 4 g) := by rw [hK]
        _ ≤ 16 * (Kf * Work.Spaces.HkSq α 4 g) :=
            mul_le_mul_of_nonneg_right hch (mul_nonneg hKf0 (Work.Spaces.HkSq_nonneg α 4 g))
        _ ≤ 16 * TTot α f g Kf Kg K3 :=
            mul_le_mul_of_nonneg_left (le_TTot_Kf α f g Kf Kg K3 hKg0 hK3) (by norm_num)
    · have hb3 : 3 ≤ b := by omega
      obtain ⟨hslot_int, hslot_le⟩ := xD_Kg_int_q_o α f g Kg hKg0 hf hg hmemf hmemg i b hi hb3 hbi
      have hle : ∀ᵐ p ∂Work.FTS.H2.pm, |xD f g i b p.1 p.2| ≤ (i.choose b : ℝ) *
          (Kg * ((|Work.Spaces.DzIter b f p.1 p.2| * Whz p.1 p.2)
            * (|Work.Spaces.DzIter i g p.1 p.2| * Whz p.1 p.2))) := by
        filter_upwards [ae_pm_z_pos_o, ae_pm_theta_mem_Ioo] with p hzpos hθ
        have hpt := xD_Kg_pt α hα f g Kg hKg0 hKg i b hi hbi hb3 p.1 p.2 hzpos hθ.1 hθ.2
        calc |xD f g i b p.1 p.2|
            ≤ (i.choose b : ℝ) * Kg * ((|Work.Spaces.DzIter b f p.1 p.2| * Whz p.1 p.2)
              * (|Work.Spaces.DzIter i g p.1 p.2| * Whz p.1 p.2)) := hpt
          _ = (i.choose b : ℝ) * (Kg * ((|Work.Spaces.DzIter b f p.1 p.2| * Whz p.1 p.2)
              * (|Work.Spaces.DzIter i g p.1 p.2| * Whz p.1 p.2))) := by ring
      obtain ⟨hint, hbd⟩ := xD_finish (f := f) (g := g) (i := i) (b := b) (c := (i.choose b : ℝ))
        (K := Kg * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g)
        (S := fun p : ℝ × ℝ => Kg * ((|Work.Spaces.DzIter b f p.1 p.2| * Whz p.1 p.2)
          * (|Work.Spaces.DzIter i g p.1 p.2| * Whz p.1 p.2)))
        hc0 hslot_int hslot_le hle (abs_aesm_pm (xD_aesm_q_o f g hf hg i b))
      refine ⟨hint, ?_⟩
      calc ∫ p, |xD f g i b p.1 p.2| ∂Work.FTS.H2.pm
          ≤ (i.choose b : ℝ) * (Kg * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g) := hbd
        _ ≤ 16 * (Kg * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g) :=
            mul_le_mul_of_nonneg_right hch
              (mul_nonneg (mul_nonneg hKg0 (Work.Spaces.HkNorm_nonneg α 4 f))
                (Work.Spaces.HkNorm_nonneg α 4 g))
        _ ≤ 16 * TTot α f g Kf Kg K3 :=
            mul_le_mul_of_nonneg_left (le_TTot_Kg α f g Kf Kg K3 hKf0 hK3) (by norm_num)

/-- Each mixed-slot Leibniz summand (with the hard ones removed) is integrable on the product
measure and bounded by `256` times the total. -/
theorem yM_summand_bound_q_o (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f g : ℝ → ℝ → ℝ)
    (Kf Kg K3 : ℝ) (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hdecg : Work.Spaces.DecayAll 4 g)
    (hmemf : Work.Spaces.HkMem α 4 f) (hmemg : Work.Spaces.HkMem α 4 g)
    (hKf : ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a f z θ| ≤ Kf)
    (hKg : ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed b a g z θ| ≤ Kg)
    (hKf0 : 0 ≤ Kf) (hKg0 : 0 ≤ Kg) (hK3 : 0 ≤ K3)
    (hGint : MeasureTheory.IntegrableOn
      (fun z => (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter 3 f) z * Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz)
    (hGle : (∫ z in Work.Spaces.Iz,
      (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter 3 f) z * Work.Spaces.w z) ^ 2) ≤ K3)
    (i j a b : ℕ) (hi4 : i ≤ 4) (hj4 : j ≤ 4) (hai : a ≤ i) (hbj : b ≤ j) :
    MeasureTheory.Integrable
        (fun p : ℝ × ℝ => if 1 ≤ i ∧ i + j ≤ 4 then
          (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b p.1 p.2|) else 0)
        Work.FTS.H2.pm ∧
      ∫ p, (if 1 ≤ i ∧ i + j ≤ 4 then
          (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b p.1 p.2|) else 0)
          ∂Work.FTS.H2.pm
        ≤ 256 * TTot α f g Kf Kg K3 := by
  have hT := TTot_nonneg α f g Kf Kg K3 hKf0 hKg0 hK3
  by_cases houter : 1 ≤ i ∧ i + j ≤ 4
  · have hzo : (fun p : ℝ × ℝ => if 1 ≤ i ∧ i + j ≤ 4 then
          (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b p.1 p.2|) else 0)
        = fun p => (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0
            else |yM α f g i j a b p.1 p.2|) := by
      funext p; rw [if_pos houter]
    rw [hzo]
    obtain ⟨hi1, hij4⟩ := houter
    by_cases hex : a = 0 ∧ b = 0 ∧ i + j = 4
    · have hz : (fun p : ℝ × ℝ =>
          if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b p.1 p.2|)
          = fun _ => 0 := by funext p; rw [if_pos hex]
      rw [hz]
      refine ⟨integrable_zero _ _ _, ?_⟩
      rw [MeasureTheory.integral_zero]
      exact mul_nonneg (by norm_num) hT
    · have hz : (fun p : ℝ × ℝ =>
          if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b p.1 p.2|)
          = fun p => |yM α f g i j a b p.1 p.2| := by funext p; rw [if_neg hex]
      rw [hz]
      have hch : (i.choose a : ℝ) * (j.choose b : ℝ) ≤ 256 :=
        choose_mul_le_256 hi4 hai hj4 hbj
      have hc0 : 0 ≤ (i.choose a : ℝ) * (j.choose b : ℝ) := by positivity
      by_cases hab2 : a + b ≤ 2
      · obtain ⟨hslot_int, hslot_le⟩ := yM_Kf_int_q_o α g Kf hKf0 hg hmemg i j a b hi1 hij4
          hai hbj hex
        have hle : ∀ᵐ p ∂Work.FTS.H2.pm, |yM α f g i j a b p.1 p.2|
            ≤ ((i.choose a : ℝ) * (j.choose b : ℝ)) *
              (Kf * ((|Work.Spaces.mixed (j - b) (i - a + 1) g p.1 p.2| * Wm α p.1 p.2)
                * (|Work.Spaces.mixed j i g p.1 p.2| * Wm α p.1 p.2))) := by
          filter_upwards [ae_pm_z_pos_o, ae_pm_theta_mem_Ioo] with p hzpos hθ
          have hpt := yM_Kf_pt α f g Kf hKf0 hKf i j a b hi1 hij4 hai hbj hab2 p.1 p.2 hzpos
            hθ.1 hθ.2
          calc |yM α f g i j a b p.1 p.2|
              ≤ (i.choose a : ℝ) * (j.choose b : ℝ) * Kf
                * ((|Work.Spaces.mixed (j - b) (i - a + 1) g p.1 p.2| * Wm α p.1 p.2)
                  * (|Work.Spaces.mixed j i g p.1 p.2| * Wm α p.1 p.2)) := hpt
            _ = ((i.choose a : ℝ) * (j.choose b : ℝ))
                * (Kf * ((|Work.Spaces.mixed (j - b) (i - a + 1) g p.1 p.2| * Wm α p.1 p.2)
                  * (|Work.Spaces.mixed j i g p.1 p.2| * Wm α p.1 p.2))) := by ring
        obtain ⟨hint, hbd⟩ := yM_finish hc0 hslot_int hslot_le hle
          (abs_aesm_pm (yM_aesm_q_o α f g hf hg i j a b))
        refine ⟨hint, ?_⟩
        have hK : Kf * Work.Spaces.HkNorm α 4 g * Work.Spaces.HkNorm α 4 g
            = Kf * Work.Spaces.HkSq α 4 g := by
          have h2 : Work.Spaces.HkNorm α 4 g * Work.Spaces.HkNorm α 4 g
              = Work.Spaces.HkSq α 4 g := Real.mul_self_sqrt (Work.Spaces.HkSq_nonneg α 4 g)
          rw [mul_assoc, h2]
        calc ∫ p, |yM α f g i j a b p.1 p.2| ∂Work.FTS.H2.pm
            ≤ ((i.choose a : ℝ) * (j.choose b : ℝ))
                * (Kf * Work.Spaces.HkNorm α 4 g * Work.Spaces.HkNorm α 4 g) := hbd
          _ = ((i.choose a : ℝ) * (j.choose b : ℝ)) * (Kf * Work.Spaces.HkSq α 4 g) := by rw [hK]
          _ ≤ 256 * (Kf * Work.Spaces.HkSq α 4 g) :=
              mul_le_mul_of_nonneg_right hch (mul_nonneg hKf0 (Work.Spaces.HkSq_nonneg α 4 g))
          _ ≤ 256 * TTot α f g Kf Kg K3 :=
              mul_le_mul_of_nonneg_left (le_TTot_Kf α f g Kf Kg K3 hKg0 hK3) (by norm_num)
      · by_cases ha1 : 1 ≤ a
        · have hab3 : 3 ≤ a + b := by omega
          obtain ⟨hslot_int, hslot_le⟩ := yM_Kg_int_q_o α f g Kg hKg0 hf hg hmemf hmemg i j a b
            hi1 hij4 hai hbj ha1 hab3
          have hle : ∀ᵐ p ∂Work.FTS.H2.pm, |yM α f g i j a b p.1 p.2|
              ≤ ((i.choose a : ℝ) * (j.choose b : ℝ)) *
                (Kg * ((|Work.Spaces.mixed b a f p.1 p.2| * Wm α p.1 p.2)
                  * (|Work.Spaces.mixed j i g p.1 p.2| * Wm α p.1 p.2))) := by
            filter_upwards [ae_pm_z_pos_o, ae_pm_theta_mem_Ioo] with p hzpos hθ
            have hpt := yM_Kg_mixed_pt α f g Kg hKg0 hKg i j a b hi1 hij4 hai hbj ha1 hab3 p.1
              p.2 hzpos hθ.1 hθ.2
            calc |yM α f g i j a b p.1 p.2|
                ≤ (i.choose a : ℝ) * (j.choose b : ℝ) * Kg
                  * ((|Work.Spaces.mixed b a f p.1 p.2| * Wm α p.1 p.2)
                    * (|Work.Spaces.mixed j i g p.1 p.2| * Wm α p.1 p.2)) := hpt
              _ = ((i.choose a : ℝ) * (j.choose b : ℝ))
                  * (Kg * ((|Work.Spaces.mixed b a f p.1 p.2| * Wm α p.1 p.2)
                    * (|Work.Spaces.mixed j i g p.1 p.2| * Wm α p.1 p.2))) := by ring
          obtain ⟨hint, hbd⟩ := yM_finish hc0 hslot_int hslot_le hle
            (abs_aesm_pm (yM_aesm_q_o α f g hf hg i j a b))
          refine ⟨hint, ?_⟩
          calc ∫ p, |yM α f g i j a b p.1 p.2| ∂Work.FTS.H2.pm
              ≤ ((i.choose a : ℝ) * (j.choose b : ℝ))
                  * (Kg * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g) := hbd
            _ ≤ 256 * (Kg * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g) :=
                mul_le_mul_of_nonneg_right hch
                  (mul_nonneg (mul_nonneg hKg0 (Work.Spaces.HkNorm_nonneg α 4 f))
                    (Work.Spaces.HkNorm_nonneg α 4 g))
            _ ≤ 256 * TTot α f g Kf Kg K3 :=
                mul_le_mul_of_nonneg_left (le_TTot_Kg α f g Kf Kg K3 hKf0 hK3) (by norm_num)
        · -- the exceptional summand `(i,j,a,b) = (1,3,0,3)`
          have ha0 : a = 0 := by omega
          subst ha0
          have hb3 : 3 ≤ b := by omega
          have hj3 : j = 3 := by omega
          subst hj3
          have hi1' : i = 1 := by omega
          subst hi1'
          have hb3' : b = 3 := by omega
          subst hb3'
          obtain ⟨⟨hexc_int, hexc_le⟩, _⟩ := Work.FTS.StrongPersist.N6Trans.OpenTwins.ExcBoundOpen α f g K3 hα hα1 hf hg
            hdecg hmemf hmemg hGint hGle hK3
          have hyMeq : (fun p : ℝ × ℝ => |Work.Spaces.DzIter 3 f p.1 p.2
                * Work.Spaces.mixed 0 2 g p.1 p.2
                * Work.Spaces.mixed 3 1 g p.1 p.2 * (Wm α p.1 p.2) ^ 2|)
              =ᵐ[Work.FTS.H2.pm] fun p => |yM α f g 1 3 0 3 p.1 p.2| := by
            filter_upwards with p
            have hinner : yM α f g 1 3 0 3 p.1 p.2
                = Work.Spaces.DzIter 3 f p.1 p.2 * Work.Spaces.mixed 0 2 g p.1 p.2
                  * Work.Spaces.mixed 3 1 g p.1 p.2 * (Wm α p.1 p.2) ^ 2 := by
              simp only [yM, Work.Spaces.mixed_zero_right]
              norm_num
              try ring
            exact (congrArg abs hinner).symm
          refine ⟨hexc_int.congr hyMeq, ?_⟩
          rw [← integral_congr_ae hyMeq]
          have h5 : Real.sqrt K3 * Work.Spaces.HkSq α 4 g ≤ TTot α f g Kf Kg K3 :=
            le_TTot_sqrt α f g Kf Kg K3 hKf0 hKg0
          have h6 : TTot α f g Kf Kg K3 ≤ 256 * TTot α f g Kf Kg K3 := by linarith
          linarith
  · have hz : (fun p : ℝ × ℝ => if 1 ≤ i ∧ i + j ≤ 4 then
        (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b p.1 p.2|) else 0)
        = fun _ => 0 := by funext p; rw [if_neg houter]
    rw [hz]
    refine ⟨integrable_zero _ _ _, ?_⟩
    rw [MeasureTheory.integral_zero]
    exact mul_nonneg (by norm_num) hT


end Work.FTS.StrongPersist.N6Trans.HonestEasyMajorAux
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXB.l12dens_weighted_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS_RegExport.RXB

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## The two-sided weighted radial Hardy inequality

The auxiliary weight `ψ t = t/(1+t)² = 1/(t·w t)`, two elementary integral estimates for it, and
the Hardy inequality itself (proved by integrating from `0` resp. from `+∞` and letting the
endpoint tend to `0⁺` resp. `+∞`). -/

/-- `ψ t = t/(1+t)²`, the reciprocal of `t·w(t)`. -/
private def psi (t : ℝ) : ℝ := t / (1 + t) ^ 2

private lemma psi_sq_eq (t : ℝ) : psi t ^ 2 = t ^ 2 / (1 + t) ^ 4 := by
  unfold psi
  rw [div_pow, show ((1 + t) ^ 2) ^ 2 = (1 + t) ^ 4 by ring]

private lemma psi_mul (c : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    (t * c t * Work.Spaces.w t) * psi t = c t := by
  have h1 : (1 + t) ≠ 0 := by positivity
  have ht0 : t ≠ 0 := ne_of_gt ht
  unfold psi Work.Spaces.w
  field_simp

private lemma psi_cont : ContinuousOn psi (Set.Ioi (-1 : ℝ)) := by
  unfold psi
  refine ContinuousOn.div continuousOn_id ((continuousOn_const.add continuousOn_id).pow 2)
    (fun x hx => pow_ne_zero 2 (ne_of_gt (by linarith [Set.mem_Ioi.mp hx])))

/-- The pointwise bound `ψ t ^ 2 ≤ t ^ 2` for `t ≥ 0`. -/
private lemma psi_sq_le_sq {t : ℝ} (ht : 0 ≤ t) : psi t ^ 2 ≤ t ^ 2 := by
  rw [psi_sq_eq, div_le_iff₀ (by positivity : (0 : ℝ) < (1 + t) ^ 4)]
  have h1 : (1 : ℝ) ≤ (1 + t) ^ 4 := one_le_pow₀ (by linarith)
  nlinarith [sq_nonneg t]

/-- The pointwise bound `ψ t ^ 2 ≤ 1/t²` for `t > 0`. -/
private lemma psi_sq_le_inv_sq {t : ℝ} (ht : 0 < t) : psi t ^ 2 ≤ 1 / t ^ 2 := by
  rw [psi_sq_eq, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (1 + t), sq_nonneg t, ht]

/-- `√(∫_0^s ψ²) ≤ 4·(√s·s/(1+s)²)` for `0 < s ≤ 1`. -/
private lemma psi_sqrt_small {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    Real.sqrt (∫ t in (0 : ℝ)..s, psi t ^ 2) ≤ 4 * (Real.sqrt s * s / (1 + s) ^ 2) := by
  have hcont1 : ContinuousOn (fun t : ℝ => psi t ^ 2) (Set.uIcc (0 : ℝ) s) := by
    rw [Set.uIcc_of_le hs.le]
    exact (psi_cont.mono (fun x hx => by
      have h1 : (0 : ℝ) ≤ x := hx.1
      show (-1 : ℝ) < x
      linarith)).pow 2
  have hcont2 : ContinuousOn (fun t : ℝ => t ^ 2) (Set.uIcc (0 : ℝ) s) := by
    rw [Set.uIcc_of_le hs.le]
    exact continuousOn_id.pow 2
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hs.le
    (hcont1.intervalIntegrable (μ := volume)) (hcont2.intervalIntegrable (μ := volume))
    (fun t ht => psi_sq_le_sq ht.1)
  have hval : (∫ t in (0 : ℝ)..s, t ^ 2) = s ^ 3 / 3 := by
    rw [integral_pow]; norm_num
  rw [hval] at hmono
  have h2 : (∫ t in (0 : ℝ)..s, psi t ^ 2) ≤ s ^ 3 := by
    have h3 : (0 : ℝ) ≤ s ^ 3 := by positivity
    linarith
  have h4 : Real.sqrt (s ^ 3) = Real.sqrt s * s := by
    rw [show s ^ 3 = s * s ^ 2 by ring, Real.sqrt_mul hs.le, Real.sqrt_sq hs.le]
  have h5 : Real.sqrt (∫ t in (0 : ℝ)..s, psi t ^ 2) ≤ Real.sqrt s * s := by
    rw [← h4]; exact Real.sqrt_le_sqrt h2
  refine le_trans h5 ?_
  have hsq : (1 + s) ^ 2 ≤ 4 := by nlinarith
  have hnn : 0 ≤ Real.sqrt s * s := mul_nonneg (Real.sqrt_nonneg _) hs.le
  rw [show (4 : ℝ) * (Real.sqrt s * s / (1 + s) ^ 2) = (4 * (Real.sqrt s * s)) / (1 + s) ^ 2
    by ring]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (1 + s) ^ 2)]
  nlinarith [hnn, hsq]

/-- `√(∫_s^B ψ²) ≤ 4·(√s·s/(1+s)²)` for `1 ≤ s ≤ B`. -/
private lemma psi_sqrt_large {s B : ℝ} (hs : 1 ≤ s) (hsB : s ≤ B) :
    Real.sqrt (∫ t in s..B, psi t ^ 2) ≤ 4 * (Real.sqrt s * s / (1 + s) ^ 2) := by
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le one_pos hs
  have hcont1 : ContinuousOn (fun t : ℝ => psi t ^ 2) (Set.uIcc s B) := by
    rw [Set.uIcc_of_le hsB]
    exact (psi_cont.mono (fun x hx => by
      have h1 : s ≤ x := hx.1
      show (-1 : ℝ) < x
      linarith)).pow 2
  have hcont2 : ContinuousOn (fun t : ℝ => 1 / t ^ 2) (Set.uIcc s B) := by
    rw [Set.uIcc_of_le hsB]
    refine ContinuousOn.div continuousOn_const (continuousOn_id.pow 2) ?_
    intro x hx
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hs0 hx.1))
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hsB
    (hcont1.intervalIntegrable (μ := volume)) (hcont2.intervalIntegrable (μ := volume))
    (fun t ht => psi_sq_le_inv_sq (lt_of_lt_of_le hs0 ht.1))
  -- the exact value of `∫_s^B 1/t²`
  have hderiv : ∀ x ∈ Set.uIcc s B, HasDerivAt (fun y : ℝ => -y⁻¹) (1 / x ^ 2) x := by
    intro x hx
    rw [Set.uIcc_of_le hsB] at hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hs0 hx.1)
    have h1 : HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x := hasDerivAt_inv hx0
    have h2 : HasDerivAt (fun y : ℝ => -y⁻¹) (-(-(x ^ 2)⁻¹)) x := h1.neg
    simpa only [neg_neg, inv_eq_one_div] using h2
  have hintInt : IntervalIntegrable (fun x : ℝ => 1 / x ^ 2) volume s B :=
    hcont2.intervalIntegrable (μ := volume)
  have hval : (∫ t in s..B, 1 / t ^ 2) = 1 / s - 1 / B := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hintInt
    rw [h]
    simp only [inv_eq_one_div]
    ring
  have hle1 : (∫ t in s..B, 1 / t ^ 2) ≤ 1 / s := by
    rw [hval]
    have hB0 : (0 : ℝ) ≤ B := le_trans (le_trans (by norm_num : (0 : ℝ) ≤ 1) hs) hsB
    have h1B : 0 ≤ 1 / B := div_nonneg (by norm_num) hB0
    linarith
  have hbound : (∫ t in s..B, psi t ^ 2) ≤ 1 / s := le_trans hmono hle1
  -- conclude
  have hsqrt : Real.sqrt (1 / s) ≤ 4 * (Real.sqrt s * s / (1 + s) ^ 2) := by
    rw [one_div, Real.sqrt_inv, inv_eq_one_div, div_le_iff₀ (Real.sqrt_pos.mpr hs0)]
    have hsp : Real.sqrt s * Real.sqrt s = s := by
      rw [← sq]; exact Real.sq_sqrt hs0.le
    have hkey : 4 * (Real.sqrt s * s / (1 + s) ^ 2) * Real.sqrt s
        = 4 * ((Real.sqrt s * Real.sqrt s) * s) / (1 + s) ^ 2 := by ring
    rw [hkey, hsp, le_div_iff₀ (by positivity : (0 : ℝ) < (1 + s) ^ 2)]
    nlinarith
  calc Real.sqrt (∫ t in s..B, psi t ^ 2) ≤ Real.sqrt (1 / s) := Real.sqrt_le_sqrt hbound
    _ ≤ 4 * (Real.sqrt s * s / (1 + s) ^ 2) := hsqrt

/-- **Two-sided weighted radial Hardy inequality.**  For `g` differentiable on `(0,∞)` with
derivative `c` continuous there, vanishing at `0⁺` and at `+∞`, and with `t·c·w ∈ L²(0,∞)`
(`w t = (1+t)²/t²`),

  `|g s| ≤ 4·(√s·s/(1+s)²)·√(∫_{t>0} (t·c t·w t)²)`.

The two sides of the cut `s = 1` are handled by integrating from `0` (using `g 0⁺ = 0`) resp.
from `+∞` (using `g → 0` at infinity), and the two elementary estimates
`∫_0^s ψ² ≤ s³` (`s ≤ 1`) resp. `∫_s^B ψ² ≤ 1/s` (`s ≥ 1`) with `ψ t = t/(1+t)² = 1/(t·w t)`. -/
theorem weighted_hardy_two_sided_of_continuousOn {g c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi (0 : ℝ)))
    (hderiv : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivAt g (c t) t)
    (hlim0 : Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hliminf : Tendsto g atTop (nhds 0))
    (hint : IntegrableOn (fun t => (t * c t * Work.Spaces.w t) ^ 2) (Set.Ioi 0))
    {s : ℝ} (hs : 0 < s) :
    |g s| ≤ 4 * (Real.sqrt s * s / (1 + s) ^ 2) *
      Real.sqrt (∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2) := by
  -- the fundamental-theorem + Cauchy-Schwarz step on an interval `[a,b]`, `0 < a ≤ b`
  have hkey : ∀ a b : ℝ, 0 < a → a ≤ b →
      |g b - g a| ≤ Real.sqrt (∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2)
        * Real.sqrt (∫ t in a..b, psi t ^ 2) := by
    intro a b ha hab
    have hmem : ∀ x ∈ Set.uIcc a b, (0 : ℝ) < x := by
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      exact lt_of_lt_of_le ha hx.1
    have hin : ∀ x ∈ Set.uIcc a b, x ∈ Set.Ioi (0 : ℝ) := fun x hx => hmem x hx
    have hIntc : IntervalIntegrable c volume a b :=
      (hc.mono hin).intervalIntegrable (μ := volume)
    have hFTC : ∫ t in a..b, c t = g b - g a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x hx => hderiv x (hmem x hx)) hIntc
    have hcongr : (∫ t in a..b, c t)
        = ∫ t in a..b, (t * c t * Work.Spaces.w t) * psi t :=
      intervalIntegral.integral_congr (fun x hx => (psi_mul c (hmem x hx)).symm)
    have hcontW : ContinuousOn (fun t : ℝ => Work.Spaces.w t) (Set.uIcc a b) := by
      unfold Work.Spaces.w
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
        (continuousOn_id.pow 2) ?_
      intro x hx
      exact pow_ne_zero 2 (ne_of_gt (hmem x hx))
    have hcont1 : ContinuousOn (fun t : ℝ => t * c t * Work.Spaces.w t) (Set.uIcc a b) :=
      (continuousOn_id.mul (hc.mono hin)).mul hcontW
    have hcont2 : ContinuousOn (fun t : ℝ => psi t) (Set.uIcc a b) :=
      psi_cont.mono (fun x hx => by
        show (-1 : ℝ) < x
        linarith [hmem x hx])
    have hcs := Work.Spaces.hardyZ_interval_integral_mul_le_sqrt a b hab hcont1 hcont2
    have hleI : (∫ t in a..b, (t * c t * Work.Spaces.w t) ^ 2)
        ≤ ∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2 := by
      rw [intervalIntegral.integral_of_le hab]
      refine MeasureTheory.setIntegral_mono_set hint (Eventually.of_forall fun x => sq_nonneg _)
        (Eventually.of_forall fun x hx => ?_)
      exact hmem x (by rw [Set.uIcc_of_le hab]; exact ⟨le_of_lt hx.1, hx.2⟩)
    rw [← hFTC, hcongr]
    calc |∫ t in a..b, (t * c t * Work.Spaces.w t) * psi t|
        ≤ Real.sqrt (∫ t in a..b, (t * c t * Work.Spaces.w t) ^ 2)
            * Real.sqrt (∫ t in a..b, psi t ^ 2) := hcs
      _ ≤ Real.sqrt (∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2)
            * Real.sqrt (∫ t in a..b, psi t ^ 2) :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hleI) (Real.sqrt_nonneg _)
  rcases le_total s 1 with hs1 | hs1
  · -- ## small `s`: integrate from `0`
    have hcontPsi : ContinuousOn (fun t : ℝ => psi t ^ 2) (Set.Icc (0 : ℝ) s) :=
      (psi_cont.mono (fun x hx => by
        have h1 : (0 : ℝ) ≤ x := hx.1
        show (-1 : ℝ) < x
        linarith)).pow 2
    have hbound : ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) s →
        |g s| - |g ε| ≤ Real.sqrt (∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2)
          * Real.sqrt (∫ t in (0 : ℝ)..s, psi t ^ 2) := by
      intro ε hε
      have hεs : ε ≤ s := le_of_lt hε.2
      have h1 := hkey ε s hε.1 hεs
      have h2 : |g s| - |g ε| ≤ |g s - g ε| := abs_sub_abs_le_abs_sub (g s) (g ε)
      have hlepsi : (∫ t in ε..s, psi t ^ 2) ≤ ∫ t in (0 : ℝ)..s, psi t ^ 2 := by
        rw [intervalIntegral.integral_of_le hεs, intervalIntegral.integral_of_le hs.le]
        refine MeasureTheory.setIntegral_mono_set
          (hcontPsi.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
          (Eventually.of_forall fun x => sq_nonneg _) (Eventually.of_forall fun x hx => ?_)
        exact ⟨lt_trans hε.1 hx.1, hx.2⟩
      calc |g s| - |g ε| ≤ |g s - g ε| := h2
        _ ≤ Real.sqrt (∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2)
              * Real.sqrt (∫ t in ε..s, psi t ^ 2) := h1
        _ ≤ Real.sqrt (∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2)
              * Real.sqrt (∫ t in (0 : ℝ)..s, psi t ^ 2) :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlepsi) (Real.sqrt_nonneg _)
    have htend : Tendsto (fun ε : ℝ => |g s| - |g ε|) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (|g s|)) := by
      have h : Tendsto (fun ε : ℝ => |g s| - |g ε|) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (|g s| - |0|)) := tendsto_const_nhds.sub hlim0.abs
      simpa using h
    have hev : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
        |g s| - |g ε| ≤ Real.sqrt (∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2)
          * Real.sqrt (∫ t in (0 : ℝ)..s, psi t ^ 2) := by
      filter_upwards [self_mem_nhdsWithin,
        (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ 𝓝 0)
          (Iio_mem_nhds (show (0 : ℝ) < s from hs))] with ε hε0 hεs
      exact hbound ε ⟨hε0, hεs⟩
    have hmain := le_of_tendsto htend hev
    calc |g s| ≤ Real.sqrt (∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2)
            * Real.sqrt (∫ t in (0 : ℝ)..s, psi t ^ 2) := by simpa using hmain
      _ ≤ Real.sqrt (∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2)
            * (4 * (Real.sqrt s * s / (1 + s) ^ 2)) :=
          mul_le_mul_of_nonneg_left (psi_sqrt_small hs hs1) (Real.sqrt_nonneg _)
      _ = 4 * (Real.sqrt s * s / (1 + s) ^ 2)
            * Real.sqrt (∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2) := by ring
  · -- ## large `s`: integrate towards `+∞`
    have hbound : ∀ B : ℝ, s ≤ B →
        |g s| - |g B| ≤ Real.sqrt (∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2)
          * (4 * (Real.sqrt s * s / (1 + s) ^ 2)) := by
      intro B hsB
      have h1 := hkey s B hs hsB
      have h2 : |g s| - |g B| ≤ |g B - g s| := by
        rw [abs_sub_comm (g B) (g s)]
        exact abs_sub_abs_le_abs_sub (g s) (g B)
      have h3 := psi_sqrt_large hs1 hsB
      calc |g s| - |g B| ≤ |g B - g s| := h2
        _ ≤ Real.sqrt (∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2)
              * Real.sqrt (∫ t in s..B, psi t ^ 2) := h1
        _ ≤ Real.sqrt (∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2)
              * (4 * (Real.sqrt s * s / (1 + s) ^ 2)) :=
            mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
    have htend : Tendsto (fun B : ℝ => |g s| - |g B|) atTop (nhds (|g s|)) := by
      have h : Tendsto (fun B : ℝ => |g s| - |g B|) atTop (nhds (|g s| - |0|)) :=
        tendsto_const_nhds.sub hliminf.abs
      simpa using h
    have hev : ∀ᶠ B in atTop,
        |g s| - |g B| ≤ Real.sqrt (∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2)
          * (4 * (Real.sqrt s * s / (1 + s) ^ 2)) := by
      filter_upwards [eventually_ge_atTop s] with B hB
      exact hbound B hB
    have hmain := le_of_tendsto htend hev
    calc |g s| ≤ Real.sqrt (∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2)
            * (4 * (Real.sqrt s * s / (1 + s) ^ 2)) := by simpa using hmain
      _ = 4 * (Real.sqrt s * s / (1 + s) ^ 2)
            * Real.sqrt (∫ t in Set.Ioi 0, (t * c t * Work.Spaces.w t) ^ 2) := by ring

/-! ## The density bound -/

theorem l12dens_weighted_bound {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ → ℝ,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.FTS.Nonlin.BdryTraces α 4 f →
      ∀ s : ℝ, 0 < s →
        |Work.Construction.L12dens f s|
          ≤ C * (Real.sqrt s / (1 + s) ^ 2) * Work.Spaces.HkNorm α 4 f := by
  refine ⟨20, by norm_num, ?_⟩
  intro f hF hmem hbd s hs
  -- the `θ`-side package: a.e. radial-slice integrability, measurability of the Hardy square
  -- root, its `L²`-mass bound, and the Cauchy–Schwarz bound against `K`
  obtain ⟨hsliceInt, hGaesm, hG2int, hG2le⟩ := DzSlice_l2 (α := α) (f := f) hF hmem
  obtain ⟨hKGint, hKGle⟩ :=
    K_mul_sqrt_le_of_L2 (M := Work.Spaces.HkSq α 4 f) hGaesm
      (fun θ => Real.sqrt_nonneg _) hG2int hG2le (Work.Spaces.HkSq_nonneg α 4 f)
  set G : ℝ → ℝ := fun θ => Real.sqrt (∫ t in Set.Ioi (0 : ℝ),
      (Work.Spaces.DzIter 1 f t θ * Work.Spaces.w t) ^ 2) with hGdef
  set c4 : ℝ := 4 * (Real.sqrt s * s / (1 + s) ^ 2) with hc4
  -- almost every angle is interior
  have hioo : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
    filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := π / 2)]
      with σ h hmem'
    exact h.mpr hmem'
  -- the a.e. two-sided radial Hardy bound at the angle `θ`
  have hpoint : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), |f s θ| ≤ c4 * G θ := by
    filter_upwards [hsliceInt, hioo] with θ hint hθ
    have hsint : MeasureTheory.IntegrableOn
        (fun t => (t * Work.Spaces.pz f t θ * Work.Spaces.w t) ^ 2) (Set.Ioi 0) := by
      simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz] using hint
    have hderiv : ∀ t ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (fun t : ℝ => f t θ) (Work.Spaces.pz f t θ) t :=
      fun t ht => hF.hasDerivAt_slice hθ ht
    have hc : ContinuousOn (fun t : ℝ => Work.Spaces.pz f t θ) (Set.Ioi 0) :=
      (hF.pz).curry_z hθ |>.continuousOn
    have hb := (hbd 0 0 (by norm_num)).1 θ hθ
    have hlim0 : Tendsto (fun z => f z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      tendsto_nhdsGT_zero_of_radial_trace (by
        simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero]
          using hb.1)
    have hliminf : Tendsto (fun z => f z θ) atTop (nhds 0) :=
      Work.FTS.H2.HQ.tendsto_atTop_zero_of_traces (by
        simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero]
          using hb.2)
    have h := weighted_hardy_two_sided_of_continuousOn hc hderiv hlim0 hliminf hsint hs
    simpa only [hc4, hGdef, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz]
      using h
  -- integrability of the majorant
  have hmajInt : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * (c4 * G θ))
      Work.Spaces.Iθ := by
    have h : MeasureTheory.IntegrableOn (fun θ => c4 * (Work.Spaces.K θ * G θ))
        Work.Spaces.Iθ := hKGint.integrable.const_mul c4
    exact h.congr (Filter.Eventually.of_forall fun θ => by ring)
  -- integrability of the minorant `θ ↦ K θ |f s θ|`
  have hfaesm : MeasureTheory.AEStronglyMeasurable (fun θ => f s θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => f p.1 p.2)
      hF.continuousOn hs
  have hKcont : Continuous (fun θ : ℝ => Work.Spaces.K θ) := by
    unfold Work.Spaces.K; fun_prop
  have hKfInt : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * |f s θ|)
      Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' hmajInt (hKcont.aestronglyMeasurable.mul ?_) ?_
    · simpa only [Real.norm_eq_abs] using hfaesm.norm
    · filter_upwards [hpoint, MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hpt hθmem
      rw [Real.norm_of_nonneg
        (mul_nonneg (Work.FTS.GalBasis.cc.K_nonneg_of_mem_Iθ hθmem) (abs_nonneg _))]
      exact mul_le_mul_of_nonneg_left hpt (Work.FTS.GalBasis.cc.K_nonneg_of_mem_Iθ hθmem)
  have hmono : (fun θ => Work.Spaces.K θ * |f s θ|)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ => Work.Spaces.K θ * (c4 * G θ)) := by
    filter_upwards [hpoint, MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hpt hθmem
    exact mul_le_mul_of_nonneg_left hpt (Work.FTS.GalBasis.cc.K_nonneg_of_mem_Iθ hθmem)
  -- the density is the angular integral of `K f` divided by `s`
  have hL12 : Work.Construction.L12dens f s
      = (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f s θ) / s := by
    rw [Work.Construction.L12dens, Work.FM.L12dens, Work.Spaces.Iθ,
      ← MeasureTheory.integral_div]
  have hpull : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * (c4 * G θ))
      = c4 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * G θ := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
  have hKGle' : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * G θ)
      ≤ 5 * Work.Spaces.HkNorm α 4 f := by
    simpa only [hGdef, Work.Spaces.HkNorm] using hKGle
  calc |Work.Construction.L12dens f s|
      = |(∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f s θ) / s| := by rw [hL12]
    _ = |∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * f s θ| / s := by
        rw [abs_div, abs_of_pos hs]
    _ ≤ (∫ θ in Work.Spaces.Iθ, |Work.Spaces.K θ * f s θ|) / s := by
        gcongr
        simpa only [Real.norm_eq_abs] using
          MeasureTheory.norm_integral_le_integral_norm
            (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
            (f := fun θ => Work.Spaces.K θ * f s θ)
    _ = (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |f s θ|) / s := by
        congr 1
        exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ hθ => by
          rw [abs_mul, abs_of_nonneg (Work.FTS.GalBasis.cc.K_nonneg_of_mem_Iθ hθ)]
    _ ≤ (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * (c4 * G θ)) / s := by
        gcongr 1
        exact MeasureTheory.integral_mono_ae hKfInt hmajInt hmono
    _ = (c4 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * G θ)) / s := by rw [hpull]
    _ ≤ (c4 * (5 * Work.Spaces.HkNorm α 4 f)) / s := by
        gcongr
    _ = 20 * (Real.sqrt s / (1 + s) ^ 2) * Work.Spaces.HkNorm α 4 f := by
        rw [hc4]
        field_simp
        ring

end Work.FTS_RegExport.RXB
end
end
