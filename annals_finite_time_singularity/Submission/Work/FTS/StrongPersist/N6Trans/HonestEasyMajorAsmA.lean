import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.NormNum.RealSqrt
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SourceBound.sliceMomentIdentity
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.PhiStar.Honesty.psiTrunc_tendsto_psiSeries
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.eFam_sup_le
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeDefs
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6.HkN_sepF_le
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.KsAux
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.contDiffOn_two_of_sliceData
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.ExcBoundQ
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.H2.T1Q.SlotPtQ
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H2.T1Q.T1EasyContQ
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.H2W.FstarDzIterFourPsiAe
import Submission.Work.H2W.fstarDzIterFourAe
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.ThetaAgmon.agmon_interval
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.ClassCHon.sliceMass_continuous =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter
open scoped ENNReal

namespace Work.FTS.ClassCHon

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- Assembly step: the same proof as `sliceMass_continuous`, with the four auxiliary facts
(delegated and proved in `SliceMassAux`) as explicit hypotheses. -/
theorem sliceMass_aux {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (h0 : Work.Spaces.HkMem α 0 F)
    (h1 : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz F z θ))
    (hPAMG : ∀ s θ a b : ℝ, 0 < s → θ ∈ Work.Spaces.Iθ →
      2 * |a * b| * Work.FTS.EllipticEst.sEta θ
        ≤ a ^ 2 * (Work.Spaces.w s) ^ 2 * Work.FTS.EllipticEst.sEta θ
          + (s * b) ^ 2 * (Work.Spaces.w s) ^ 2 * Work.FTS.EllipticEst.sEta θ)
    (hFTC : ∀ z₁ z₂ θ : ℝ, 0 < z₁ → z₁ ≤ z₂ → θ ∈ Set.Ioo 0 (π / 2) →
      (F z₂ θ) ^ 2 - (F z₁ θ) ^ 2
        = ∫ s in z₁..z₂, 2 * F s θ * Work.Spaces.pz F s θ)
    (hINT : MeasureTheory.Integrable
      (Function.uncurry (fun s θ => 2 * F s θ * Work.Spaces.pz F s θ
        * Work.FTS.EllipticEst.sEta θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hCONT : ∀ {m Φ : ℝ → ℝ}, MeasureTheory.IntegrableOn Φ (Set.Ioi (0 : ℝ)) →
      (∀ z, 0 ≤ Φ z) →
      (∀ z₁ z₂ : ℝ, 0 < z₁ → z₁ ≤ z₂ → |m z₂ - m z₁| ≤ ∫ s in z₁..z₂, Φ s) →
      ContinuousOn m (Set.Ioi (0 : ℝ))) :
    ContinuousOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) (Set.Ioi 0) := by
  -- `sEta` is nonnegative on `Iθ`
  have hsEta_nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Work.FTS.EllipticEst.sEta θ := fun θ hθ => by
    simpa only [Work.FTS.EllipticEst.sEta, Work.FTS.EllipticEst.AngSecond.sig]
      using Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ
  -- the per-slice integrability of the `σ`-weighted slice masses
  have hsliceF : ∀ z ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn
      (fun θ => (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := fun z hz =>
    Work.FTS.PhiStar.Honesty.integrableOn_sq_sEta_of_HkMem h0 (show (0 : ℝ) < z from hz)
  have hsliceZ : ∀ z ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn
      (fun θ => (z * Work.Spaces.pz F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := fun z hz =>
    Work.FTS.PhiStar.Honesty.integrableOn_sq_sEta_of_HkMem h1 (show (0 : ℝ) < z from hz)
  -- the outer integrability of the two slice masses
  have hGzInt : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
        (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iz :=
    (Work.FTS.EllipticEst.AngAWeak.integrableOn_wSq_sliceSq_sEta (f := F) h0).1
  have hGzpInt : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
        (z * Work.Spaces.pz F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iz :=
    (Work.FTS.EllipticEst.AngAWeak.integrableOn_wSq_sliceSq_sEta
      (f := fun z θ => z * Work.Spaces.pz F z θ) h1).1
  -- the dominating density
  set G : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      + (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
        (z * Work.Spaces.pz F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ with hGdef
  have hGint : MeasureTheory.IntegrableOn G (Set.Ioi (0 : ℝ)) := by
    rw [hGdef]
    exact (hGzInt.add hGzpInt).mono_set
      (fun z hz => (show z ∈ Work.Spaces.Iz from le_of_lt (show (0 : ℝ) < z from hz)))
  have hGnn : ∀ z, 0 ≤ G z := by
    intro z
    rw [hGdef]
    refine add_nonneg ?_ ?_
    · exact mul_nonneg (sq_nonneg _) (setIntegral_nonneg measurableSet_Icc fun θ hθ =>
        mul_nonneg (sq_nonneg _) (hsEta_nn θ hθ))
    · exact mul_nonneg (sq_nonneg _) (setIntegral_nonneg measurableSet_Icc fun θ hθ =>
        mul_nonneg (sq_nonneg _) (hsEta_nn θ hθ))
  -- the difference bound
  have hdiff : ∀ z₁ z₂ : ℝ, 0 < z₁ → z₁ ≤ z₂ →
      |(∫ θ in Work.Spaces.Iθ, (F z₂ θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        - (∫ θ in Work.Spaces.Iθ, (F z₁ θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)|
      ≤ ∫ s in z₁..z₂, G s := by
    intro z₁ z₂ hz₁ hz₁₂
    have hsubIoc : Set.Ioc z₁ z₂ ⊆ Work.Spaces.Iz :=
      fun z hz => le_of_lt (lt_trans hz₁ hz.1)
    -- product-integrability of the joint integrand on the box
    have hbox : MeasureTheory.Integrable
        (Function.uncurry (fun s θ => 2 * F s θ * Work.Spaces.pz F s θ
          * Work.FTS.EllipticEst.sEta θ))
        ((MeasureTheory.volume.restrict (Set.uIoc z₁ z₂)).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      have hfull : MeasureTheory.IntegrableOn
          (Function.uncurry (fun s θ => 2 * F s θ * Work.Spaces.pz F s θ
            * Work.FTS.EllipticEst.sEta θ))
          (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) MeasureTheory.volume := by
        rw [MeasureTheory.IntegrableOn, MeasureTheory.Measure.volume_eq_prod,
          ← MeasureTheory.Measure.prod_restrict]
        exact hINT
      have hsub : Set.uIoc z₁ z₂ ⊆ Work.Spaces.Iz := by
        rw [Set.uIoc_of_le hz₁₂]; exact hsubIoc
      have hsmall := hfull.mono_set (Set.prod_mono hsub subset_rfl)
      rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
      simpa only [MeasureTheory.IntegrableOn] using hsmall
    -- (a) the difference of the two masses
    have hstep1 : (∫ θ in Work.Spaces.Iθ, (F z₂ θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        - (∫ θ in Work.Spaces.Iθ, (F z₁ θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        = ∫ θ in Work.Spaces.Iθ,
            ((F z₂ θ) ^ 2 - (F z₁ θ) ^ 2) * Work.FTS.EllipticEst.sEta θ := by
      rw [← MeasureTheory.integral_sub (hsliceF z₂ (by exact lt_of_lt_of_le hz₁ hz₁₂))
        (hsliceF z₁ hz₁)]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
    -- (b) the fundamental theorem of calculus on each slice
    have hstep2 : (∫ θ in Work.Spaces.Iθ,
            ((F z₂ θ) ^ 2 - (F z₁ θ) ^ 2) * Work.FTS.EllipticEst.sEta θ)
        = ∫ θ in Work.Spaces.Iθ,
            (∫ s in z₁..z₂, 2 * F s θ * Work.Spaces.pz F s θ)
              * Work.FTS.EllipticEst.sEta θ := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [Work.FTS.EllipticEst.Honest.ae_mem_Ioo_Iθ] with θ hθ
      rw [hFTC z₁ z₂ θ hz₁ hz₁₂ hθ]
    -- (c) bring `σ` inside the interval integral
    have hstep3 : (∫ θ in Work.Spaces.Iθ,
            (∫ s in z₁..z₂, 2 * F s θ * Work.Spaces.pz F s θ)
              * Work.FTS.EllipticEst.sEta θ)
        = ∫ θ in Work.Spaces.Iθ, ∫ s in z₁..z₂,
            2 * F s θ * Work.Spaces.pz F s θ * Work.FTS.EllipticEst.sEta θ := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      show (∫ s in z₁..z₂, 2 * F s θ * Work.Spaces.pz F s θ)
          * Work.FTS.EllipticEst.sEta θ
        = ∫ s in z₁..z₂,
            2 * F s θ * Work.Spaces.pz F s θ * Work.FTS.EllipticEst.sEta θ
      rw [intervalIntegral.integral_mul_const]
    -- (d) Fubini
    have hstep4 : (∫ θ in Work.Spaces.Iθ, ∫ s in z₁..z₂,
            2 * F s θ * Work.Spaces.pz F s θ * Work.FTS.EllipticEst.sEta θ)
        = ∫ s in z₁..z₂, ∫ θ in Work.Spaces.Iθ,
            2 * F s θ * Work.Spaces.pz F s θ * Work.FTS.EllipticEst.sEta θ :=
      (MeasureTheory.intervalIntegral_integral_swap
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (a := z₁) (b := z₂)
        (f := fun s θ => 2 * F s θ * Work.Spaces.pz F s θ
          * Work.FTS.EllipticEst.sEta θ) hbox).symm
    -- (e) the a.e. pointwise bound on the `z`-slices
    have hΦbound : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioc z₁ z₂)),
        |∫ θ in Work.Spaces.Iθ, 2 * F s θ * Work.Spaces.pz F s θ
            * Work.FTS.EllipticEst.sEta θ| ≤ G s := by
      have hslice_ae : ∀ᵐ s ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
          MeasureTheory.Integrable (fun θ => 2 * F s θ * Work.Spaces.pz F s θ
            * Work.FTS.EllipticEst.sEta θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        MeasureTheory.Integrable.prod_right_ae hINT
      have hmono : MeasureTheory.volume.restrict (Set.Ioc z₁ z₂)
          ≤ MeasureTheory.volume.restrict Work.Spaces.Iz :=
        MeasureTheory.Measure.restrict_mono hsubIoc le_rfl
      filter_upwards [hslice_ae.filter_mono (MeasureTheory.ae_mono hmono),
        MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs_int hs_mem
      have hspos : 0 < s := lt_of_lt_of_le hz₁ (le_of_lt hs_mem.1)
      have hA : MeasureTheory.IntegrableOn
          (fun θ => (F s θ) ^ 2 * (Work.Spaces.w s) ^ 2
            * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
        MeasureTheory.IntegrableOn.congr_fun
          ((hsliceF s ((show (0 : ℝ) < s from hspos) : s ∈ Set.Ioi (0 : ℝ))).const_mul
            ((Work.Spaces.w s) ^ 2))
          (fun θ _ => by ring) measurableSet_Icc
      have hB : MeasureTheory.IntegrableOn
          (fun θ => (s * Work.Spaces.pz F s θ) ^ 2 * (Work.Spaces.w s) ^ 2
            * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
        MeasureTheory.IntegrableOn.congr_fun
          ((hsliceZ s ((show (0 : ℝ) < s from hspos) : s ∈ Set.Ioi (0 : ℝ))).const_mul
            ((Work.Spaces.w s) ^ 2))
          (fun θ _ => by ring) measurableSet_Icc
      have hAB : MeasureTheory.IntegrableOn
          (fun θ => (F s θ) ^ 2 * (Work.Spaces.w s) ^ 2 * Work.FTS.EllipticEst.sEta θ
            + (s * Work.Spaces.pz F s θ) ^ 2 * (Work.Spaces.w s) ^ 2
              * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := hA.add hB
      have h2 : (∫ θ in Work.Spaces.Iθ,
            |2 * F s θ * Work.Spaces.pz F s θ * Work.FTS.EllipticEst.sEta θ|)
          ≤ ∫ θ in Work.Spaces.Iθ,
            ((F s θ) ^ 2 * (Work.Spaces.w s) ^ 2 * Work.FTS.EllipticEst.sEta θ
              + (s * Work.Spaces.pz F s θ) ^ 2 * (Work.Spaces.w s) ^ 2
                * Work.FTS.EllipticEst.sEta θ) := by
        refine MeasureTheory.integral_mono_ae (MeasureTheory.Integrable.abs hs_int) hAB ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        have hp := hPAMG s θ (F s θ) (Work.Spaces.pz F s θ) hspos hθ
        have hleft : |2 * F s θ * Work.Spaces.pz F s θ * Work.FTS.EllipticEst.sEta θ|
            = 2 * |F s θ * Work.Spaces.pz F s θ| * Work.FTS.EllipticEst.sEta θ := by
          rw [show (2 * F s θ * Work.Spaces.pz F s θ * Work.FTS.EllipticEst.sEta θ)
              = 2 * (F s θ * Work.Spaces.pz F s θ) * Work.FTS.EllipticEst.sEta θ
            from by ring,
            abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
            abs_of_nonneg (hsEta_nn θ hθ)]
        rw [hleft]; exact hp
      have h3 : (∫ θ in Work.Spaces.Iθ,
            ((F s θ) ^ 2 * (Work.Spaces.w s) ^ 2 * Work.FTS.EllipticEst.sEta θ
              + (s * Work.Spaces.pz F s θ) ^ 2 * (Work.Spaces.w s) ^ 2
                * Work.FTS.EllipticEst.sEta θ)) = G s := by
        rw [hGdef]
        show (∫ θ in Work.Spaces.Iθ,
            ((F s θ) ^ 2 * (Work.Spaces.w s) ^ 2 * Work.FTS.EllipticEst.sEta θ
              + (s * Work.Spaces.pz F s θ) ^ 2 * (Work.Spaces.w s) ^ 2
                * Work.FTS.EllipticEst.sEta θ))
          = (Work.Spaces.w s) ^ 2 * (∫ θ in Work.Spaces.Iθ,
              (F s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            + (Work.Spaces.w s) ^ 2 * ∫ θ in Work.Spaces.Iθ,
              (s * Work.Spaces.pz F s θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        rw [MeasureTheory.integral_add hA hB, ← MeasureTheory.integral_const_mul,
          ← MeasureTheory.integral_const_mul]
        congr 1
        · exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
        · exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
      calc |∫ θ in Work.Spaces.Iθ, 2 * F s θ * Work.Spaces.pz F s θ
              * Work.FTS.EllipticEst.sEta θ|
          ≤ ∫ θ in Work.Spaces.Iθ,
              |2 * F s θ * Work.Spaces.pz F s θ
                * Work.FTS.EllipticEst.sEta θ| :=
            MeasureTheory.abs_integral_le_integral_abs
        _ ≤ _ := h2
        _ = G s := h3
    -- (f) assemble
    rw [hstep1, hstep2, hstep3, hstep4]
    refine le_trans (intervalIntegral.norm_integral_le_integral_norm
      (f := fun s => ∫ θ in Work.Spaces.Iθ, 2 * F s θ * Work.Spaces.pz F s θ
        * Work.FTS.EllipticEst.sEta θ) hz₁₂) ?_
    simp only [Real.norm_eq_abs]
    rw [intervalIntegral.integral_of_le hz₁₂, intervalIntegral.integral_of_le hz₁₂]
    have hbase : MeasureTheory.Integrable
        (fun s => ∫ θ in Work.Spaces.Iθ, 2 * F s θ * Work.Spaces.pz F s θ
          * Work.FTS.EllipticEst.sEta θ) (MeasureTheory.volume.restrict (Set.Ioc z₁ z₂)) := by
      have h := MeasureTheory.Integrable.integral_prod_left hbox
      rw [Set.uIoc_of_le hz₁₂] at h
      exact MeasureTheory.Integrable.congr h (Filter.Eventually.of_forall fun s => rfl)
    refine MeasureTheory.integral_mono_ae hbase.abs
      (hGint.mono_set (fun z hz => (show z ∈ Set.Ioi (0 : ℝ) from lt_trans hz₁ hz.1)))
      hΦbound
  exact hCONT hGint hGnn hdiff

/-- **Continuity of the angular slice mass of an `ℋ⁰`-honest function with honest radial derivative.**

For `F` which is `C^∞` on the open quadrant `(0,∞) × (0,π/2)`, whose level-`0` `ℋ`-integrand is
honest (`HkMem α 0 F`) and whose radial derivative `z ∂_z F` is also `ℋ⁰`-honest
(`HkMem α 0 (fun z θ => z * pz F z θ)`), the angular slice mass

  `m F z := ∫_θ (F z θ)² · sin(2θ)^{-η}`

is continuous on `(0,∞)` (hence locally bounded there).

**Proof.** For each fixed `θ ∈ (0,π/2)` the slice `z ↦ F z θ` is `C^∞` on `(0,∞)`, so the FTC in
`z` gives `F(z₂,θ)² - F(z₁,θ)² = ∫_{z₁}^{z₂} 2 F(s,θ) ∂_zF(s,θ) ds` for `0 < z₁ ≤ z₂`. Multiplying
by `σ θ = sin(2θ)^{-η}` and integrating in `θ` (Fubini; the double integral of `|F ∂_zF| σ` is
finite by two Cauchy–Schwarz inequalities, using on `[z₁,z₂]` that `w² ≥ c > 0` and
`z² ≥ z₁²` together with the two outer conjuncts of `HkMem`) gives

  `m F z₂ - m F z₁ = ∫_{z₁}^{z₂} Φ s ds`,   `Φ s := ∫_θ 2 F(s,θ) ∂_zF(s,θ) σ θ dθ`,

with `∫_{z₁}^{z₂}|Φ| < ∞`; so `m F` is absolutely continuous, hence continuous, on every compact
subinterval of `(0,∞)`. -/
theorem sliceMass_continuous {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (h0 : Work.Spaces.HkMem α 0 F)
    (h1 : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz F z θ)) :
    ContinuousOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) (Set.Ioi 0) := by
  exact sliceMass_aux hsm h0 h1
    (fun s θ a b hs hθ => Work.FTS.ClassCHon.SliceMassAux.pointwise_amgm hs hθ)
    (fun z₁ z₂ θ hz hz' hθ =>
      Work.FTS.ClassCHon.SliceMassAux.slice_sq_ftc (F := F) hsm hz hz' hθ)
    (Work.FTS.ClassCHon.SliceMassAux.integrable_prod_mixed hsm h0 h1)
    (fun {m Φ} hΦ hnn h => Work.FTS.ClassCHon.SliceMassAux.continuousOn_of_integral_bound hΦ hnn h)

/-! ## The weakened interface: the honest radial derivative replaced by its two *outer* bounds

The proof of `sliceMass_continuous` uses the hypothesis `h1 : HkMem α 0 (z ∂_z F)` through exactly
two facts about the function `G := z ∂_z F`:

* the *slice* conjunct: `∫_θ (G z θ)² σ θ < ∞` for every `z ∈ Ioi 0`
  (`integrableOn_sq_sEta_of_HkMem`), and
* the *outer* conjunct: `∫_z w(z)² ∫_θ (G z θ)² σ θ < ∞`.

Both are *consequences* of the two outer `∫⁻`-bounds of `HkIntegrand α 0 G` and
`HkIntegrand α 1 G`, by the every-`z` upgrade `SliceMassUpgrade.HkMem_of_outer` (the level-`1`
bound, i.e. one `D_z`-order up, is exactly the slack the repaired node `EllNode8pp` provides).
The statement below takes the two outer bounds (plus the measurabilities they need) as
hypotheses, so that a consumer which only has the *integrated* estimate at hand can still
conclude the continuity of the slice mass.

The passage from `h1` to the four outer facts is
`SliceMassUpgrade.HkMem_of_outer` applied to `G = z ∂_z F`; note that the level-`(k+1)` integrand
of `G` is the one containing `D_z²F`, i.e. the statement consumes *two* orders of the source. -/

end Work.FTS.ClassCHon
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.PerSliceK =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllSol

namespace Work.FTS.EllSol.PkgK5

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The per-slice comparison.**  For every `z ∈ Iz` the `ℋ^k`-integrand of the quotient
`Φ/sin 2θ` is honest on the angular slice and its `θ`-integral is bounded by a universal multiple
of the `θ`-integral of the `ℋ^k`-integrand of `∂_θΦ`. -/
theorem perSliceCmpK (k : ℕ) (hk : 1 ≤ k) : ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (Φ : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 →
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
    ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.HkIntegrand α k
          (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
            (fun z θ => Φ z θ / Real.sin (2 * θ)) z θ)
          ≤ K * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
              (Work.Spaces.pth Φ) z θ) := by
  obtain ⟨Kg, hKgpos, hgroup⟩ := groupCmpK k
  refine ⟨Kg, hKgpos, ?_⟩
  intro α Φ hα hα1 hSO hsl ht0 ht1 hmem z hz
  set U : ℝ → ℝ → ℝ := fun z' θ' => Φ z' θ' / Real.sin (2 * θ') with hUdef
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · subst hz0
    have hzero : (fun θ : ℝ => Work.Spaces.HkIntegrand α k U 0 θ) = fun _ : ℝ => (0 : ℝ) := by
      funext θ
      rw [Work.Spaces.HkIntegrand]
      simp only [hUdef, Work.Spaces.Wt, Work.Spaces.w]
      simp
    refine ⟨?_, ?_⟩
    · rw [hzero]
      exact integrableOn_zero
    · rw [hzero, MeasureTheory.integral_zero]
      exact mul_nonneg hKgpos.le (MeasureTheory.integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α k (Work.Spaces.pth Φ) 0 θ)
  · -- the honest slice `z > 0`
    have hgrpInt : ∀ j : ℕ, j ≤ k → MeasureTheory.IntegrableOn
        (fun θ => Work.FTS.EllipticEst.sliceGroup α k j U z θ) Work.Spaces.Iθ :=
      fun j hj => (hgroup α Φ hα hα1 hSO hsl ht0 ht1 hmem z hzpos hz j hj).1
    have hgrpIntR : ∀ j : ℕ, j ≤ k → MeasureTheory.IntegrableOn
        (fun θ => Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pth Φ) z θ)
        Work.Spaces.Iθ := by
      intro j hj
      refine (Work.FTS.EllipticEst.integrableOn_zSummand α k hSO.pth hmem j hj hz).add ?_
      refine MeasureTheory.integrable_finsetSum _ (fun i hi => ?_)
      obtain ⟨hi1, hikj⟩ := Finset.mem_Icc.mp hi
      exact Work.FTS.EllipticEst.integrableOn_mixedSummand α k hSO.pth hmem i j hi1
        (by omega) hz
    have hsumfun : (fun θ : ℝ => Work.Spaces.HkIntegrand α k U z θ)
        = fun θ : ℝ => ∑ j ∈ Finset.range (k + 1),
            Work.FTS.EllipticEst.sliceGroup α k j U z θ := by
      funext θ
      exact Work.FTS.EllipticEst.HkIntegrand_eq_slice_sum α k U z θ
    have hsumfunR : (fun θ : ℝ => Work.Spaces.HkIntegrand α k (Work.Spaces.pth Φ) z θ)
        = fun θ : ℝ => ∑ j ∈ Finset.range (k + 1),
            Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pth Φ) z θ := by
      funext θ
      exact Work.FTS.EllipticEst.HkIntegrand_eq_slice_sum α k (Work.Spaces.pth Φ) z θ
    refine ⟨?_, ?_⟩
    · rw [MeasureTheory.IntegrableOn, hsumfun]
      exact MeasureTheory.integrable_finsetSum _
        (fun j hj => hgrpInt j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
    · have hL : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k U z θ)
          = ∑ j ∈ Finset.range (k + 1),
              (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α k j U z θ) := by
        rw [hsumfun]
        exact MeasureTheory.integral_finset_sum _
          (fun j hj => hgrpInt j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
      have hR : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.pth Φ) z θ)
          = ∑ j ∈ Finset.range (k + 1),
              (∫ θ in Work.Spaces.Iθ,
                Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pth Φ) z θ) := by
        rw [hsumfunR]
        exact MeasureTheory.integral_finset_sum _
          (fun j hj => hgrpIntR j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
      rw [hL, hR, Finset.mul_sum]
      exact Finset.sum_le_sum (fun j hj =>
        (hgroup α Φ hα hα1 hSO hsl ht0 ht1 hmem z hzpos hz j
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).2)
end Work.FTS.EllSol.PkgK5
end
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.TraceEngine.cBK_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllSol.PkgK5.TraceEngine

open CutBk

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

theorem cBK_integrable {χ : ℕ → ℝ → ℝ} {K : ℝ} (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ)
    {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G)
    (hXi : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.DzIter 2 G p.1 p.2
            + ((p.1 - 3) / (1 + p.1)) * Work.Spaces.Dz G p.1 p.2) ^ 2)
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hT : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.pthIter 2 G p.1 p.2) ^ 2)
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hD : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.Dz G p.1 p.2) ^ 2)
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ
        * Work.FTS.EllSol.PkgK5.cBK χ k (Work.Spaces.Dz G) θ) Work.Spaces.Iθ := by
  -- ## the three hypotheses in the notation of `CutBk`
  have hXiM : MeasureTheory.Integrable (fun p : ℝ × ℝ => cutRho p * cutXi G p ^ 2) Mu := hXi
  have hTM : MeasureTheory.Integrable (fun p : ℝ × ℝ => cutRho p * cutD2 G p ^ 2) Mu := hT
  have hDM : MeasureTheory.Integrable (fun p : ℝ × ℝ => cutRho p * cutPs G p ^ 2) Mu := hD
  -- ## integrability of the two joint integrands on the strip
  have hPsiM := integrable_cutPsi hχ k hG hXiM hTM
  have hPsiBM := integrable_cutPsiB hχ k hG hDM hTM
  have hPsiM' : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => cutRho p * χ k p.1 * cutXi G p * cutD2 G p)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [← Mu_eq_prod]; exact hPsiM
  have hPsiBM' : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [← Mu_eq_prod]; exact hPsiBM
  -- ## the two marginal integrabilities (Fubini), identified with the two IBP pieces
  have hIntA : MeasureTheory.Integrable (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ *
      (∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2
        * cutXi G (z, θ) * cutD2 G (z, θ))) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h0 : MeasureTheory.Integrable (fun θ : ℝ => ∫ z, (fun p : ℝ × ℝ =>
        cutRho p * χ k p.1 * cutXi G p * cutD2 G p) (z, θ)
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      hPsiM'.integral_prod_right
    exact h0.congr (ae_of_mem_Iθ (fun θ _ => bridge_cutPsi hχ k θ))
  have hIntB : MeasureTheory.Integrable (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ *
      (∫ z in (cA k)..(cB k), (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
        * cutPs G (z, θ) * cutD2 G (z, θ))) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h0 : MeasureTheory.Integrable (fun θ : ℝ => ∫ z, (fun p : ℝ × ℝ =>
        (p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p) (z, θ)
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      hPsiBM'.integral_prod_right
    exact h0.congr (ae_of_mem_Iθ (fun θ _ => bridge_cutPsiB hχ k θ))
  -- ## the radial integration by parts at each angle of `Iθ`
  have hslice : ∀ θ ∈ Work.Spaces.Iθ,
      Work.FTS.EllipticEst.thEta θ * cBK χ k (Work.Spaces.Dz G) θ
        = - (Work.FTS.EllipticEst.thEta θ *
              (∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2
                * cutXi G (z, θ) * cutD2 G (z, θ))
            + Work.FTS.EllipticEst.thEta θ *
              (∫ z in (cA k)..(cB k), (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
                * cutPs G (z, θ) * cutD2 G (z, θ))) := by
    intro θ hθ
    have hmem : θ ∈ Set.Icc (0 : ℝ) (π / 2) := hθ
    rcases lt_or_eq_of_le hmem.1 with h0 | h0
    · rcases lt_or_eq_of_le hmem.2 with h1 | h1
      · have h := gK_ibp_fts hχ k hG ⟨h0, h1⟩
        have hA : (∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2
              * cutXi G (z, θ) * cutD2 G (z, θ))
            = (∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2
                * (Work.Spaces.DzIter 2 G z θ + ((z - 3) / (1 + z)) * Work.Spaces.Dz G z θ)
                * Work.Spaces.pthIter 2 G z θ) := by
          refine intervalIntegral.integral_congr (fun z _ => ?_)
          rw [show cutXi G (z, θ) = Work.Spaces.DzIter 2 G z θ
                + ((z - 3) / (1 + z)) * Work.Spaces.Dz G z θ from rfl,
              show cutD2 G (z, θ) = Work.Spaces.pthIter 2 G z θ from rfl]
        have hB : (∫ z in (cA k)..(cB k), (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
              * cutPs G (z, θ) * cutD2 G (z, θ))
            = (∫ z in (cA k)..(cB k), (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
                * Work.Spaces.Dz G z θ * Work.Spaces.pthIter 2 G z θ) := by
          refine intervalIntegral.integral_congr (fun z _ => ?_)
          rw [show cutPs G (z, θ) = Work.Spaces.Dz G z θ from rfl,
              show cutD2 G (z, θ) = Work.Spaces.pthIter 2 G z θ from rfl]
        have hc : cBK χ k (Work.Spaces.Dz G) θ
            = - (∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2
                  * cutXi G (z, θ) * cutD2 G (z, θ))
              - (∫ z in (cA k)..(cB k), (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
                  * cutPs G (z, θ) * cutD2 G (z, θ)) := by
          rw [show cBK χ k (Work.Spaces.Dz G) θ
              = (∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2 * Work.Spaces.Dz G z θ
                  * Work.Spaces.pthIter 2 (Work.Spaces.Dz G) z θ) from rfl, h, hA, hB]
        rw [hc]
        ring
      · rw [h1, thEta_piHalf]
        ring
    · rw [← h0, thEta_zero]
      ring
  -- ## assembly: the target is the negative of the sum of the two integrable pieces
  refine ((hIntA.add hIntB).neg).congr (ae_of_mem_Iθ (fun θ hθ => ?_))
  simp only [Pi.neg_apply, Pi.add_apply]
  rw [hslice θ hθ]

end Work.FTS.EllSol.PkgK5.TraceEngine
end
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.TraceEngine.cutBkBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllSol.PkgK5.TraceEngine

open CutBk

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The main bound -/

theorem cutBkBound {χ : ℕ → ℝ → ℝ} {K : ℝ} (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ)
    {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G)
    (hXi : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.DzIter 2 G p.1 p.2
            + ((p.1 - 3) / (1 + p.1)) * Work.Spaces.Dz G p.1 p.2) ^ 2)
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hT : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.pthIter 2 G p.1 p.2) ^ 2)
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hD : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.Dz G p.1 p.2) ^ 2)
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hL : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ
        * Work.FTS.EllSol.PkgK5.cBK χ k (Work.Spaces.Dz G) θ) Work.Spaces.Iθ) :
    - (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ
        * Work.FTS.EllSol.PkgK5.cBK χ k (Work.Spaces.Dz G) θ)
      ≤ Real.sqrt ((∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
              * Work.FTS.EllipticEst.thEta p.2
              * (Work.Spaces.DzIter 2 G p.1 p.2
                  + ((p.1 - 3) / (1 + p.1)) * Work.Spaces.Dz G p.1 p.2) ^ 2)
          * (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
              * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.pthIter 2 G p.1 p.2) ^ 2))
        + (K / Real.log ((k : ℝ) + 2)) * Real.sqrt (
            (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
              * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.Dz G p.1 p.2) ^ 2)
            * (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
              * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.pthIter 2 G p.1 p.2) ^ 2)) := by
  -- ## the hypotheses in the local notation
  have hXiM : Integrable (fun p : ℝ × ℝ => cutRho p * cutXi G p ^ 2) Mu := hXi
  have hTM : Integrable (fun p : ℝ × ℝ => cutRho p * cutD2 G p ^ 2) Mu := hT
  have hDM : Integrable (fun p : ℝ × ℝ => cutRho p * cutPs G p ^ 2) Mu := hD
  have hPsiM := integrable_cutPsi hχ k hG hXiM hTM
  have hPsiBM := integrable_cutPsiB hχ k hG hDM hTM
  have hPsiM' : Integrable (fun p : ℝ × ℝ => cutRho p * χ k p.1 * cutXi G p * cutD2 G p)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [← Mu_eq_prod]; exact hPsiM
  have hPsiBM' : Integrable
      (fun p : ℝ × ℝ => (p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [← Mu_eq_prod]; exact hPsiBM
  -- ## nonnegativity of the three slot integrals and of `K / log (k+2)`
  have hnonnegΞ : 0 ≤ ∫ p in Izθ, cutRho p * cutXi G p ^ 2 :=
    integral_nonneg_of_ae (ae_of_mem_Izθ fun p hp => mul_nonneg (cutRho_nonneg hp) (sq_nonneg _))
  have hnonnegD : 0 ≤ ∫ p in Izθ, cutRho p * cutD2 G p ^ 2 :=
    integral_nonneg_of_ae (ae_of_mem_Izθ fun p hp => mul_nonneg (cutRho_nonneg hp) (sq_nonneg _))
  have hnonnegPs : 0 ≤ ∫ p in Izθ, cutRho p * cutPs G p ^ 2 :=
    integral_nonneg_of_ae (ae_of_mem_Izθ fun p hp => mul_nonneg (cutRho_nonneg hp) (sq_nonneg _))
  have hKL : 0 ≤ K / Real.log ((k : ℝ) + 2) := div_nonneg hχ.K0 (log_k_pos k).le
  -- ## step 1: the radial integration by parts at each angle
  have hslice : ∀ θ ∈ Work.Spaces.Iθ,
      Work.FTS.EllipticEst.thEta θ * cBK χ k (Work.Spaces.Dz G) θ
        = - (Work.FTS.EllipticEst.thEta θ *
              (∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2
                * cutXi G (z, θ) * cutD2 G (z, θ))
            + Work.FTS.EllipticEst.thEta θ *
              (∫ z in (cA k)..(cB k), (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
                * cutPs G (z, θ) * cutD2 G (z, θ))) := by
    intro θ hθ
    have hmem : θ ∈ Set.Icc (0 : ℝ) (π / 2) := hθ
    rcases lt_or_eq_of_le hmem.1 with h0 | h0
    · rcases lt_or_eq_of_le hmem.2 with h1 | h1
      · have h := gK_ibp_fts hχ k hG ⟨h0, h1⟩
        have hA : (∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2
              * cutXi G (z, θ) * cutD2 G (z, θ))
            = (∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2
                * (Work.Spaces.DzIter 2 G z θ + ((z - 3) / (1 + z)) * Work.Spaces.Dz G z θ)
                * Work.Spaces.pthIter 2 G z θ) := by
          refine intervalIntegral.integral_congr (fun z _ => ?_)
          rw [show cutXi G (z, θ) = Work.Spaces.DzIter 2 G z θ
                + ((z - 3) / (1 + z)) * Work.Spaces.Dz G z θ from rfl,
              show cutD2 G (z, θ) = Work.Spaces.pthIter 2 G z θ from rfl]
        have hB : (∫ z in (cA k)..(cB k), (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
              * cutPs G (z, θ) * cutD2 G (z, θ))
            = (∫ z in (cA k)..(cB k), (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
                * Work.Spaces.Dz G z θ * Work.Spaces.pthIter 2 G z θ) := by
          refine intervalIntegral.integral_congr (fun z _ => ?_)
          rw [show cutPs G (z, θ) = Work.Spaces.Dz G z θ from rfl,
              show cutD2 G (z, θ) = Work.Spaces.pthIter 2 G z θ from rfl]
        have hc : cBK χ k (Work.Spaces.Dz G) θ
            = - (∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2
                  * cutXi G (z, θ) * cutD2 G (z, θ))
              - (∫ z in (cA k)..(cB k), (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
                  * cutPs G (z, θ) * cutD2 G (z, θ)) := by
          rw [show cBK χ k (Work.Spaces.Dz G) θ
              = (∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2 * Work.Spaces.Dz G z θ
                  * Work.Spaces.pthIter 2 (Work.Spaces.Dz G) z θ) from rfl, h, hA, hB]
        rw [hc]
        ring
      · rw [h1, thEta_piHalf]
        ring
    · rw [← h0, thEta_zero]
      ring
  -- ## step 2: the two `θ`-integrals as integrals over the strip (Fubini)
  have hbridgeA := bridge_cutPsi hχ k (G := G)
  have hbridgeB := bridge_cutPsiB hχ k (G := G)
  have hIntA : Integrable (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ *
        (∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2
          * cutXi G (z, θ) * cutD2 G (z, θ))) (volume.restrict Work.Spaces.Iθ) := by
    have h0 : Integrable (fun θ : ℝ => ∫ z, (fun p : ℝ × ℝ =>
        cutRho p * χ k p.1 * cutXi G p * cutD2 G p) (z, θ)
        ∂(volume.restrict Work.Spaces.Iz)) (volume.restrict Work.Spaces.Iθ) :=
      hPsiM'.integral_prod_right
    exact h0.congr (ae_of_mem_Iθ (fun θ _ => hbridgeA θ))
  have hIntB : Integrable (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ *
        (∫ z in (cA k)..(cB k), (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
          * cutPs G (z, θ) * cutD2 G (z, θ))) (volume.restrict Work.Spaces.Iθ) := by
    have h0 : Integrable (fun θ : ℝ => ∫ z, (fun p : ℝ × ℝ =>
        (p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p) (z, θ)
        ∂(volume.restrict Work.Spaces.Iz)) (volume.restrict Work.Spaces.Iθ) :=
      hPsiBM'.integral_prod_right
    exact h0.congr (ae_of_mem_Iθ (fun θ _ => hbridgeB θ))
  have hkeyA : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ *
        (∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2
          * cutXi G (z, θ) * cutD2 G (z, θ)))
      = ∫ p in Izθ, cutRho p * χ k p.1 * cutXi G p * cutD2 G p := by
    rw [setIntegral_congr_fun measurableSet_Iθ (fun θ _ => (hbridgeA θ).symm)]
    rw [setIntegral_Izθ_eq_prod]
    exact (integral_prod_symm (μ := volume.restrict Work.Spaces.Iz)
      (ν := volume.restrict Work.Spaces.Iθ)
      (fun p : ℝ × ℝ => cutRho p * χ k p.1 * cutXi G p * cutD2 G p) hPsiM').symm
  have hkeyB : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ *
        (∫ z in (cA k)..(cB k), (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
          * cutPs G (z, θ) * cutD2 G (z, θ)))
      = ∫ p in Izθ, (p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p := by
    rw [setIntegral_congr_fun measurableSet_Iθ (fun θ _ => (hbridgeB θ).symm)]
    rw [setIntegral_Izθ_eq_prod]
    exact (integral_prod_symm (μ := volume.restrict Work.Spaces.Iz)
      (ν := volume.restrict Work.Spaces.Iθ)
      (fun p : ℝ × ℝ => (p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p)
      hPsiBM').symm
  have hLHSelim : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ
        * cBK χ k (Work.Spaces.Dz G) θ)
      = - ((∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ *
              (∫ z in (cA k)..(cB k), χ k z * (Work.Spaces.w z) ^ 2
                * cutXi G (z, θ) * cutD2 G (z, θ)))
          + (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ *
              (∫ z in (cA k)..(cB k), (z * deriv (χ k) z) * (Work.Spaces.w z) ^ 2
                * cutPs G (z, θ) * cutD2 G (z, θ)))) := by
    rw [setIntegral_congr_fun measurableSet_Iθ hslice, integral_neg, integral_add hIntA hIntB]
  have hmain : - (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ
        * cBK χ k (Work.Spaces.Dz G) θ)
      = (∫ p in Izθ, cutRho p * χ k p.1 * cutXi G p * cutD2 G p)
        + (∫ p in Izθ, (p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p) := by
    rw [hLHSelim, neg_neg, hkeyA, hkeyB]
  -- ## step 3: the two Cauchy–Schwarz bounds
  have hcsA := csSqrt_ae (μ := Mu) (ρ := cutRho) (Ξ := cutXi G) (Φ := cutD2 G)
    (ae_of_mem_Izθ (fun p hp => cutRho_nonneg hp)) hXiM hTM
  have hcsB := csSqrt_ae (μ := Mu) (ρ := cutRho) (Ξ := cutPs G) (Φ := cutD2 G)
    (ae_of_mem_Izθ (fun p hp => cutRho_nonneg hp)) hDM hTM
  have hboundA : (∫ p in Izθ, cutRho p * χ k p.1 * cutXi G p * cutD2 G p)
      ≤ Real.sqrt ((∫ p in Izθ, cutRho p * cutXi G p ^ 2)
          * (∫ p in Izθ, cutRho p * cutD2 G p ^ 2)) := by
    calc (∫ p in Izθ, cutRho p * χ k p.1 * cutXi G p * cutD2 G p)
        ≤ ∫ p in Izθ, cutRho p * |cutXi G p| * |cutD2 G p| := by
          refine integral_mono_ae hPsiM hcsA.1 ?_
          exact ae_of_mem_Izθ (fun p hp => cutPsi_le_abs hχ k hp)
      _ ≤ Real.sqrt (∫ p in Izθ, cutRho p * cutXi G p ^ 2)
            * Real.sqrt (∫ p in Izθ, cutRho p * cutD2 G p ^ 2) := hcsA.2
      _ = Real.sqrt ((∫ p in Izθ, cutRho p * cutXi G p ^ 2)
            * (∫ p in Izθ, cutRho p * cutD2 G p ^ 2)) :=
          (Real.sqrt_mul hnonnegΞ _).symm
  have hboundB : (∫ p in Izθ, (p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p)
      ≤ (K / Real.log ((k : ℝ) + 2)) * Real.sqrt ((∫ p in Izθ, cutRho p * cutPs G p ^ 2)
          * (∫ p in Izθ, cutRho p * cutD2 G p ^ 2)) := by
    calc (∫ p in Izθ, (p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p)
        ≤ (K / Real.log ((k : ℝ) + 2))
            * (∫ p in Izθ, cutRho p * |cutPs G p| * |cutD2 G p|) := by
          rw [← integral_const_mul]
          refine integral_mono_ae hPsiBM (hcsB.1.const_mul _) ?_
          exact ae_of_mem_Izθ (fun p hp => cutPsiB_le hχ k hp)
      _ ≤ (K / Real.log ((k : ℝ) + 2)) * (Real.sqrt (∫ p in Izθ, cutRho p * cutPs G p ^ 2)
            * Real.sqrt (∫ p in Izθ, cutRho p * cutD2 G p ^ 2)) :=
          mul_le_mul_of_nonneg_left hcsB.2 hKL
      _ = (K / Real.log ((k : ℝ) + 2)) * Real.sqrt ((∫ p in Izθ, cutRho p * cutPs G p ^ 2)
            * (∫ p in Izθ, cutRho p * cutD2 G p ^ 2)) := by
          rw [Real.sqrt_mul hnonnegPs]
  -- ## assembly
  calc - (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ
        * cBK χ k (Work.Spaces.Dz G) θ)
      = (∫ p in Izθ, cutRho p * χ k p.1 * cutXi G p * cutD2 G p)
        + (∫ p in Izθ, (p.1 * deriv (χ k) p.1) * cutRho p * cutPs G p * cutD2 G p) := hmain
    _ ≤ Real.sqrt ((∫ p in Izθ, cutRho p * cutXi G p ^ 2)
          * (∫ p in Izθ, cutRho p * cutD2 G p ^ 2))
        + (K / Real.log ((k : ℝ) + 2)) * Real.sqrt ((∫ p in Izθ, cutRho p * cutPs G p ^ 2)
          * (∫ p in Izθ, cutRho p * cutD2 G p ^ 2)) := add_le_add hboundA hboundB

end Work.FTS.EllSol.PkgK5.TraceEngine
end
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.TraceEngine.cutIntegralTendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllSol.PkgK5.TraceEngine

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The measure of the strip `Iz ×ˢ Iθ` is the product of the two restricted measures. -/
private theorem restr_eq_prod :
    volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
  rw [Measure.prod_restrict, Measure.volume_eq_prod]

/-- The cut-off product `χ k p.1 · w(p.1)² · thEta(p.2) · F(p.1,p.2)²` is integrable on the strip
as soon as the un-cut product `w(p.1)² · thEta(p.2) · F(p.1,p.2)²` is: it is dominated by it
because `0 ≤ χ k z ≤ 1` for `z > 0` and the exceptional set `{p.1 ≤ 0}` is null. -/
private theorem cutKIntegrable_aux {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) {F : ℝ → ℝ → ℝ}
    (hFi : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2)
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => χ k p.1 * (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2)
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have hp1 : ∀ᵐ p ∂(volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)), 0 ≤ p.1 :=
    CutBk.ae_of_mem_Izθ (fun p hp => hp.1)
  have hp2 : ∀ᵐ p ∂(volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)),
      p.2 ∈ Work.Spaces.Iθ :=
    CutBk.ae_of_mem_Izθ (fun p hp => hp.2)
  have hcut : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => χ k p.1)
      (volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    rw [restr_eq_prod]
    exact aestronglyMeasurable_of_continuousOn_openQuad (CutBk.continuousOn_cutChi hχ k)
  have hfmeas : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => χ k p.1 * (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2)
      (volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    have h := hcut.mul hFi.aestronglyMeasurable
    refine h.congr ?_
    filter_upwards with p
    show χ k p.1 * ((Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        * (F p.1 p.2) ^ 2)
      = χ k p.1 * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        * (F p.1 p.2) ^ 2
    ring
  refine MeasureTheory.Integrable.mono' hFi hfmeas ?_
  filter_upwards [hp1, hp2] with p h1 h2
  have hth : 0 ≤ Work.FTS.EllipticEst.thEta p.2 := Work.FTS.EllipticEst.thEta_nonneg h2
  rcases eq_or_lt_of_le h1 with h0 | h0
  · -- `p.1 = 0`: both integrands vanish
    rw [← h0]
    simp [Work.Spaces.w]
  · have hb := hχ.bnd k p.1 h0
    have hg : 0 ≤ (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        * (F p.1 p.2) ^ 2 :=
      mul_nonneg (mul_nonneg (sq_nonneg _) hth) (sq_nonneg _)
    have hfeq : χ k p.1 * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        * (F p.1 p.2) ^ 2
        = χ k p.1 * ((Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
          * (F p.1 p.2) ^ 2) := by ring
    rw [hfeq, Real.norm_of_nonneg (mul_nonneg hb.1 hg)]
    exact mul_le_of_le_one_left hg hb.2

/-- The fibre bridge: the iterated cut-off integral over `θ` equals the product integral of the
cut-off integrand over the strip, and each `θ`-fibre is integrable. -/
private theorem cutBridgeK_aux {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) (k : ℕ) {F : ℝ → ℝ → ℝ}
    (hIntk : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => χ k p.1 * (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2)
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ
        * (∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
            χ k z * (Work.Spaces.w z) ^ 2 * (F z θ) ^ 2)) Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ
        * (∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
            χ k z * (Work.Spaces.w z) ^ 2 * (F z θ) ^ 2))
      = ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, χ k p.1 * (Work.Spaces.w p.1) ^ 2
          * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2 := by
  set Hk : ℝ × ℝ → ℝ := fun p => χ k p.1 * (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2 with hHk
  have hInt' : MeasureTheory.Integrable Hk
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [← restr_eq_prod]
    exact hIntk
  -- the θ-slice bridge, for every `θ`
  have hbridge : ∀ θ : ℝ, (∫ z, Hk (z, θ) ∂(volume.restrict Work.Spaces.Iz))
      = Work.FTS.EllipticEst.thEta θ
        * (∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
            χ k z * (Work.Spaces.w z) ^ 2 * (F z θ) ^ 2) := by
    intro θ
    have h1 : (∫ z in Work.Spaces.Iz, Hk (z, θ))
        = ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.thEta θ
            * (χ k z * (Work.Spaces.w z) ^ 2 * (F z θ) ^ 2) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      show χ k z * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ * (F z θ) ^ 2
        = Work.FTS.EllipticEst.thEta θ * (χ k z * (Work.Spaces.w z) ^ 2 * (F z θ) ^ 2)
      ring
    rw [h1, MeasureTheory.integral_const_mul]
    rw [Work.FTS.EllSol.PkgK5.InterpTrace.bridge_Iz_interval hχ k
      (fun z => χ k z * (Work.Spaces.w z) ^ 2 * (F z θ) ^ 2) (fun z hz hout => by
        have hχz : χ k z = 0 := hχ.supp k z hz
          (hout.elim (fun h => Or.inl h.le) (fun h => Or.inr h.le))
        simp [hχz])]
  have hIntθ : MeasureTheory.Integrable
      (fun θ => ∫ z, Hk (z, θ) ∂(volume.restrict Work.Spaces.Iz))
      (volume.restrict Work.Spaces.Iθ) := hInt'.integral_prod_right
  have hIntθ' : MeasureTheory.Integrable (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ
        * (∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
            χ k z * (Work.Spaces.w z) ^ 2 * (F z θ) ^ 2))
      (volume.restrict Work.Spaces.Iθ) :=
    hIntθ.congr (Filter.Eventually.of_forall hbridge)
  refine ⟨hIntθ', ?_⟩
  have hfub := MeasureTheory.integral_prod_symm Hk hInt'
  calc (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ
        * (∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
            χ k z * (Work.Spaces.w z) ^ 2 * (F z θ) ^ 2))
      = ∫ θ in Work.Spaces.Iθ, ∫ z, Hk (z, θ) ∂(volume.restrict Work.Spaces.Iz) :=
        MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall (fun θ => (hbridge θ).symm))
    _ = ∫ p, Hk p ∂((volume.restrict Work.Spaces.Iz).prod
          (volume.restrict Work.Spaces.Iθ)) := hfub.symm
    _ = ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, Hk p := by rw [restr_eq_prod]
    _ = ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, χ k p.1 * (Work.Spaces.w p.1) ^ 2
          * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2 := rfl

/-- The dominated convergence step: the product integrals of the cut-off integrands converge to
the full product integral. -/
private theorem cutLimitK_aux {χ : ℕ → ℝ → ℝ} {K : ℝ}
    (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K) {F : ℝ → ℝ → ℝ}
    (hIntk : ∀ k : ℕ, MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => χ k p.1
        * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2)
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hFi : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2)
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Filter.Tendsto (fun k : ℕ => ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
        χ k p.1 * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2)
      Filter.atTop
      (nhds (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2)) := by
  have hp1 : ∀ᵐ p ∂(volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)), 0 ≤ p.1 :=
    CutBk.ae_of_mem_Izθ (fun p hp => hp.1)
  have hp2 : ∀ᵐ p ∂(volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)),
      p.2 ∈ Work.Spaces.Iθ :=
    CutBk.ae_of_mem_Izθ (fun p hp => hp.2)
  have hw0 : Work.Spaces.w 0 = 0 := by simp [Work.Spaces.w]
  have hconvχ : ∀ z : ℝ, 0 < z → Filter.Tendsto (fun k : ℕ => χ k z) Filter.atTop (nhds 1) := by
    intro z hz
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hχ.conv z hz ε hε
    refine ⟨N, fun k hk => ?_⟩
    have hb := hχ.bnd k z hz
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [hN k hk], by linarith [hb.2]⟩
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2) ?_ hFi ?_ ?_
  · intro k
    exact (hIntk k).aestronglyMeasurable
  · intro k
    filter_upwards [hp1, hp2] with p h1 h2
    have hth : 0 ≤ Work.FTS.EllipticEst.thEta p.2 := Work.FTS.EllipticEst.thEta_nonneg h2
    rcases eq_or_lt_of_le h1 with h0 | h0
    · rw [← h0, hw0]
      norm_num
    · have hb := hχ.bnd k p.1 h0
      have hgnn : 0 ≤ (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
          * (F p.1 p.2) ^ 2 :=
        mul_nonneg (mul_nonneg (sq_nonneg _) hth) (sq_nonneg _)
      have hfeq : χ k p.1 * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
          * (F p.1 p.2) ^ 2
          = χ k p.1 * ((Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
            * (F p.1 p.2) ^ 2) := by ring
      rw [hfeq, Real.norm_of_nonneg (mul_nonneg hb.1 hgnn)]
      exact mul_le_of_le_one_left hgnn hb.2
  · filter_upwards [hp1] with p h1
    rcases eq_or_lt_of_le h1 with h0 | h0
    · have hzero : (fun k : ℕ => χ k p.1 * (Work.Spaces.w p.1) ^ 2
          * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2) = fun _ => 0 := by
        funext k
        rw [← h0, hw0]
        norm_num
      rw [hzero]
      have hgzero : (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
          * (F p.1 p.2) ^ 2 = 0 := by
        rw [← h0, hw0]; norm_num
      rw [hgzero]
      exact tendsto_const_nhds
    · have h1' : Filter.Tendsto (fun k : ℕ => χ k p.1
          * ((Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2))
          Filter.atTop (nhds (1 * ((Work.Spaces.w p.1) ^ 2
            * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2))) :=
        (hconvχ p.1 h0).mul_const _
      rw [one_mul] at h1'
      refine h1'.congr (fun k => ?_)
      ring

/-- For the logarithmic cut-off family `χ` of `CutFam χ K` and an integrable weighted square
`w(z)²·thEta(θ)·F(z,θ)²`, the iterated cut-off integrals
`∫ θ in Iθ, thEta θ · ∫ z in cA k..cB k, χ k z · w(z)² · F(z,θ)²` converge, as `k → ∞`, to the
full integral over the strip `Iz ×ˢ Iθ`; each of the `θ`-fibres is integrable. -/
theorem cutIntegralTendsto {χ : ℕ → ℝ → ℝ} {K : ℝ} (hχ : Work.FTS.EllSol.PkgK5.CutFam χ K)
    {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hFi : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    (∀ k : ℕ, MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ
        * (∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
            χ k z * (Work.Spaces.w z) ^ 2 * (F z θ) ^ 2)) Work.Spaces.Iθ) ∧
    Filter.Tendsto (fun k : ℕ => ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ
        * (∫ z in (Work.FTS.EllSol.PkgK5.cA k)..(Work.FTS.EllSol.PkgK5.cB k),
            χ k z * (Work.Spaces.w z) ^ 2 * (F z θ) ^ 2))
      Filter.atTop
      (nhds (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2)) := by
  have hIntk : ∀ k : ℕ, MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => χ k p.1
      * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := fun k => cutKIntegrable_aux hχ k hFi
  refine ⟨fun k => (cutBridgeK_aux hχ k (hIntk k)).1, ?_⟩
  refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun k =>
    ((cutBridgeK_aux hχ k (hIntk k)).2).symm) (cutLimitK_aux hχ hIntk hFi)

end Work.FTS.EllSol.PkgK5.TraceEngine
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.MomentChiaAux.CoefSummable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux.MomentChiaAux

theorem CoefSummable (ψ : ℝ → ℝ)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (j : ℕ) (hj : 1 ≤ j) :
    Summable (fun m : ℕ => |Work.FTS.PhiStar.FlatWAux.MomentChiaAux.bco ψ j m|
        * ((m : ℝ) + 1) ^ 2) ∧
      Summable (fun m : ℕ => |Work.FTS.PhiStar.FlatWAux.MomentChiaAux.bco ψ j m
          * Work.FTS.PhiStar.Gegenbauer.lam m| * ((m : ℝ) + 1)) := by
  obtain ⟨C, hCpos, hdec'⟩ := hdec
  -- the summable majorant `m ↦ (2m+1)/(λ_m √(2m+1))`, of decay `(m+1)^{-3/2}`
  have hG := Work.FTS.PhiStar.FlatWAux.WtDerivAux.summable_lam_sqrt
  -- per-term comparison for `m ≥ 1`
  have key : ∀ m : ℕ, 1 ≤ m →
      |bco ψ j m| * ((m : ℝ) + 1) ^ 2
          ≤ C * ((2 * (m : ℝ) + 1)
              / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) ∧
      |bco ψ j m * Work.FTS.PhiStar.Gegenbauer.lam m| * ((m : ℝ) + 1)
          ≤ C * ((2 * (m : ℝ) + 1)
              / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by
    intro m hm
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hLpos : 0 < Work.FTS.PhiStar.Gegenbauer.lam m := by
      rw [Work.FTS.PhiStar.Gegenbauer.lam]; nlinarith
    have hLge1 : 1 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
      rw [Work.FTS.PhiStar.Gegenbauer.lam]; nlinarith
    have hLx2 : ((m : ℝ) + 1) ^ 2 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
      rw [Work.FTS.PhiStar.Gegenbauer.lam]; nlinarith
    have hLle : Work.FTS.PhiStar.Gegenbauer.lam m
        ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j := by
      simpa using pow_le_pow_right₀ hLge1 hj
    have hs_pos : 0 < Real.sqrt (2 * (m : ℝ) + 1) := Real.sqrt_pos.mpr (by linarith)
    have hden1 : 0 < Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1) :=
      mul_pos hLpos hs_pos
    have hden2 : 0 < Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)
        * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j :=
      mul_pos hden1 (pow_pos hLpos j)
    have hb := hdec' m hm
    -- `bco` as an explicit product, using `λ_m > 0`
    have hbco : |bco ψ j m| = |Work.FTS.PhiStar.Series.bmode m ψ|
        * ((Work.FTS.PhiStar.Gegenbauer.lam m) ^ j)⁻¹ := by
      rw [bco, abs_mul, abs_pow, abs_inv, abs_of_pos hLpos, inv_pow]
    have hbco_le : |bco ψ j m| ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m
        * Real.sqrt (2 * (m : ℝ) + 1) * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j) := by
      rw [hbco]
      calc |Work.FTS.PhiStar.Series.bmode m ψ| * ((Work.FTS.PhiStar.Gegenbauer.lam m) ^ j)⁻¹
          ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
              * ((Work.FTS.PhiStar.Gegenbauer.lam m) ^ j)⁻¹ :=
            mul_le_mul_of_nonneg_right hb (by positivity)
        _ = C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)
              * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j) := by
            rw [inv_eq_one_div, div_mul_div_comm, mul_one]
    -- the two core inequalities `(m+1)² ≤ (2m+1)λ^j` and `(m+1)λ ≤ (2m+1)λ^j`
    have hcore : ((m : ℝ) + 1) ^ 2
        ≤ (2 * (m : ℝ) + 1) * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j := by
      have h3 : (1 : ℝ) ≤ 2 * (m : ℝ) + 1 := by linarith
      nlinarith [hLx2, hLle, h3, pow_pos hLpos j]
    have hcore2 : ((m : ℝ) + 1) * Work.FTS.PhiStar.Gegenbauer.lam m
        ≤ (2 * (m : ℝ) + 1) * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j := by
      have h3 : ((m : ℝ) + 1) ≤ 2 * (m : ℝ) + 1 := by linarith
      nlinarith [hLx2, hLle, h3, pow_pos hLpos j, hLpos]
    have hmul : (2 * (m : ℝ) + 1)
          / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
        * (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)
            * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j)
        = (2 * (m : ℝ) + 1) * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j := by
      rw [div_mul_eq_mul_div, mul_div_assoc,
        mul_div_cancel_left₀ _ (ne_of_gt hden1)]
    have hfrac : ((m : ℝ) + 1) ^ 2 / (Work.FTS.PhiStar.Gegenbauer.lam m
          * Real.sqrt (2 * (m : ℝ) + 1) * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j)
        ≤ (2 * (m : ℝ) + 1)
          / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) := by
      rw [div_le_iff₀ hden2, hmul]
      exact hcore
    have hfrac2 : ((m : ℝ) + 1) * Work.FTS.PhiStar.Gegenbauer.lam m
          / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)
              * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j)
        ≤ (2 * (m : ℝ) + 1)
          / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) := by
      rw [div_le_iff₀ hden2, hmul]
      exact hcore2
    have hexpr : C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)
          * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j) * ((m : ℝ) + 1) ^ 2
        = C * (((m : ℝ) + 1) ^ 2 / (Work.FTS.PhiStar.Gegenbauer.lam m
            * Real.sqrt (2 * (m : ℝ) + 1) * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j)) := by
      rw [div_eq_mul_inv, mul_assoc, inv_mul_eq_div]
    have hexpr2 : C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)
          * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j)
          * Work.FTS.PhiStar.Gegenbauer.lam m * ((m : ℝ) + 1)
        = C * (((m : ℝ) + 1) * Work.FTS.PhiStar.Gegenbauer.lam m
            / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)
                * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j)) := by
      field_simp
    constructor
    · calc |bco ψ j m| * ((m : ℝ) + 1) ^ 2
          ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)
              * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j) * ((m : ℝ) + 1) ^ 2 :=
            mul_le_mul_of_nonneg_right hbco_le (by positivity)
        _ = C * (((m : ℝ) + 1) ^ 2 / (Work.FTS.PhiStar.Gegenbauer.lam m
              * Real.sqrt (2 * (m : ℝ) + 1) * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j)) :=
            hexpr
        _ ≤ C * ((2 * (m : ℝ) + 1) / (Work.FTS.PhiStar.Gegenbauer.lam m
              * Real.sqrt (2 * (m : ℝ) + 1))) := mul_le_mul_of_nonneg_left hfrac hCpos.le
    · calc |bco ψ j m * Work.FTS.PhiStar.Gegenbauer.lam m| * ((m : ℝ) + 1)
          = |bco ψ j m| * Work.FTS.PhiStar.Gegenbauer.lam m * ((m : ℝ) + 1) := by
            rw [abs_mul, abs_of_pos hLpos]
        _ ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)
              * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j)
              * Work.FTS.PhiStar.Gegenbauer.lam m * ((m : ℝ) + 1) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbco_le hLpos.le)
              (by positivity)
        _ = C * (((m : ℝ) + 1) * Work.FTS.PhiStar.Gegenbauer.lam m
              / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)
                  * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ j)) := hexpr2
        _ ≤ C * ((2 * (m : ℝ) + 1) / (Work.FTS.PhiStar.Gegenbauer.lam m
              * Real.sqrt (2 * (m : ℝ) + 1))) := mul_le_mul_of_nonneg_left hfrac2 hCpos.le
  -- the `m = 0` term of the majorant vanishes (`lam 0 = 0`)
  have hG0 : (2 * ((0 : ℕ) : ℝ) + 1)
      / (Work.FTS.PhiStar.Gegenbauer.lam 0 * Real.sqrt (2 * ((0 : ℕ) : ℝ) + 1)) = 0 := by
    rw [Work.FTS.PhiStar.Gegenbauer.lam]
    norm_num
  have bnd1 : ∀ m : ℕ, |bco ψ j m| * ((m : ℝ) + 1) ^ 2
      ≤ C * ((2 * (m : ℝ) + 1)
          / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by
    intro m
    by_cases hm : m = 0
    · subst hm
      rw [bco_apply_zero ψ hj, abs_zero, zero_mul, hG0, mul_zero]
    · exact (key m (Nat.one_le_iff_ne_zero.mpr hm)).1
  have bnd2 : ∀ m : ℕ, |bco ψ j m * Work.FTS.PhiStar.Gegenbauer.lam m| * ((m : ℝ) + 1)
      ≤ C * ((2 * (m : ℝ) + 1)
          / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by
    intro m
    by_cases hm : m = 0
    · subst hm
      rw [bco_apply_zero ψ hj, zero_mul, abs_zero, zero_mul, hG0, mul_zero]
    · exact (key m (Nat.one_le_iff_ne_zero.mpr hm)).2
  constructor
  · refine (hG.mul_left C).of_norm_bounded (fun m => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact bnd1 m
  · refine (hG.mul_left C).of_norm_bounded (fun m => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact bnd2 m

end Work.FTS.PhiStar.FlatWAux.MomentChiaAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.NodeAux2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.NodeAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "psiTrunc" => Work.FTS.PhiStar.Series.psiTrunc
local notation "Q0" => Work.FTS.EllipticEst.Q0
local notation "Iθ" => Work.Spaces.Iθ
local notation "Psis" => Work.FTS.H2.ModalSol.Psi

/-- **Uniform convergence of the partial sums on a rectangular box inside the quadrant.** -/
theorem tendstoUniformlyOn_psiTrunc_box {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {F : ℝ → ℝ → ℝ} (horth : Work.Elliptic.OrthCond F)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2) Q0)
    {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc0 : 0 < c) (hcd : c < d) (hd : d < π / 2) :
    TendstoUniformlyOn (fun N : ℕ => fun p : ℝ × ℝ => psiTrunc α F N p.1 p.2)
      (fun p : ℝ × ℝ => Psis α F p.1 p.2) atTop (Set.Icc a b ×ˢ Set.Icc c d) := by
  obtain ⟨K, hK0, b, hbnn, hbT, htail⟩ := psiTrunc_tail_uniform hα hα1 hsm hL2 hcd hc0 hd
  have haK : 0 < K * a ^ (-(1 / 2) : ℝ) := mul_pos hK0 (Real.rpow_pos_of_pos ha _)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hε' : 0 < ε / (K * a ^ (-(1 / 2) : ℝ)) := by positivity
  have hev : ∀ᶠ N in Filter.atTop, b N < ε / (K * a ^ (-(1 / 2) : ℝ)) :=
    hbT.eventually (eventually_lt_nhds hε')
  filter_upwards [hev] with N hN
  intro p hp
  have hp1 : 0 < p.1 := lt_of_lt_of_le ha hp.1.1
  have hp2 : p.2 ∈ Set.Ioo 0 (π / 2) :=
    ⟨lt_of_lt_of_le hc0 hp.2.1, lt_of_le_of_lt hp.2.2 hd⟩
  have hlim := Work.FTS.H2.ModalSolR.psiTrunc_tendsto_Psi α hα hα1 horth hsm hL2 hp1 hp2
  have hdiff : Tendsto (fun M : ℕ => |psiTrunc α F N p.1 p.2 - psiTrunc α F M p.1 p.2|)
      Filter.atTop (nhds |psiTrunc α F N p.1 p.2 - Psis α F p.1 p.2|) :=
    (tendsto_const_nhds.sub hlim).abs
  have hbd : Tendsto (fun M : ℕ => K * a ^ (-(1 / 2) : ℝ) * (b N + b M)) Filter.atTop
      (nhds (K * a ^ (-(1 / 2) : ℝ) * (b N + 0))) :=
    (tendsto_const_nhds.add hbT).const_mul _
  have hstep : ∀ M : ℕ, |psiTrunc α F N p.1 p.2 - psiTrunc α F M p.1 p.2|
      ≤ K * a ^ (-(1 / 2) : ℝ) * (b N + b M) := by
    intro M
    have h := htail N M p.1 p.2 hp1 hp.2
    have hp1a : p.1 ^ (-(1 / 2) : ℝ) ≤ a ^ (-(1 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos ha hp.1.1 (by norm_num)
    calc |psiTrunc α F N p.1 p.2 - psiTrunc α F M p.1 p.2|
        ≤ K * p.1 ^ (-(1 / 2) : ℝ) * (b N + b M) := h
      _ ≤ K * a ^ (-(1 / 2) : ℝ) * (b N + b M) := by
          refine mul_le_mul_of_nonneg_right ?_ (by linarith [hbnn N, hbnn M])
          exact mul_le_mul_of_nonneg_left hp1a hK0.le
  have hle : |psiTrunc α F N p.1 p.2 - Psis α F p.1 p.2| ≤ K * a ^ (-(1 / 2) : ℝ) * b N := by
    have h0 := le_of_tendsto_of_tendsto' hdiff hbd hstep
    simpa using h0
  have h2 : K * a ^ (-(1 / 2) : ℝ) * b N < ε := by
    rw [lt_div_iff₀ haK] at hN
    calc K * a ^ (-(1 / 2) : ℝ) * b N = b N * (K * a ^ (-(1 / 2) : ℝ)) := by ring
      _ < ε := hN
  rw [Real.dist_eq, abs_sub_comm]
  exact lt_of_le_of_lt hle h2

/-- **The modal solution is continuous on the open quadrant** (clean reproof). -/
theorem continuousOn_uncurry_Psi_mod (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {F : ℝ → ℝ → ℝ} (horth : Work.Elliptic.OrthCond F)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2) Q0) :
    ContinuousOn (Function.uncurry (Psis α F)) Q0 := by
  refine continuousOn_of_forall_continuousAt (fun p hp => ?_)
  obtain ⟨hz0, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  set ε : ℝ := min (p.1 / 2) (min (p.2 / 2) ((π / 2 - p.2) / 2)) with hεdef
  have hε0 : 0 < ε := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hεz : ε ≤ p.1 / 2 := min_le_left _ _
  have hεθ : ε ≤ p.2 / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hεπ : ε ≤ (π / 2 - p.2) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hbox : Set.Icc (p.1 - ε) (p.1 + ε) ×ˢ Set.Icc (p.2 - ε) (p.2 + ε) ⊆ Q0 := by
    intro q hq
    exact Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨by linarith [hq.1.1, hεz, hz0], by linarith [hq.2.1, hεθ, hθ0],
        by linarith [hq.2.2, hεπ, hθ1]⟩
  have hunif := tendstoUniformlyOn_psiTrunc_box hα hα1 horth hsm hL2
    (a := p.1 - ε) (b := p.1 + ε) (c := p.2 - ε) (d := p.2 + ε)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  have hcont : ContinuousOn (Function.uncurry (Psis α F))
      (Set.Icc (p.1 - ε) (p.1 + ε) ×ˢ Set.Icc (p.2 - ε) (p.2 + ε)) :=
    hunif.continuousOn (Filter.Eventually.of_forall (fun N =>
      (Work.FTS.H2.ModalSolR.continuousOn_uncurry_psiTrunc α hα hα1 hsm hL2 N).mono
        hbox)).frequently
  have hnb : Set.Ioo (p.1 - ε) (p.1 + ε) ×ˢ Set.Ioo (p.2 - ε) (p.2 + ε) ∈ 𝓝 p :=
    (isOpen_Ioo.prod isOpen_Ioo).mem_nhds
      ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hbox_nhds : Set.Icc (p.1 - ε) (p.1 + ε) ×ˢ Set.Icc (p.2 - ε) (p.2 + ε) ∈ 𝓝 p :=
    Filter.mem_of_superset hnb (fun q hq =>
      ⟨⟨le_of_lt hq.1.1, le_of_lt hq.1.2⟩, ⟨le_of_lt hq.2.1, le_of_lt hq.2.2⟩⟩)
  exact hcont.continuousAt hbox_nhds

/-- **The modal solution is bounded by `z^{-1/2}` on a closed angular subinterval**, with a
constant coming from the uniform tail estimate and the vanishing of the `m = 0` mode. -/
theorem Psi_bound_mod (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (horth : Work.Elliptic.OrthCond F)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2) Q0)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ4 : δ < π / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Icc δ (π / 2 - δ),
      |Psis α F z θ| ≤ C * z ^ (-(1 / 2) : ℝ) := by
  have hcd : δ < π / 2 - δ := by linarith [Real.pi_pos]
  have hd : π / 2 - δ < π / 2 := by linarith
  obtain ⟨K, hK0, b, hbnn, hbT, htail⟩ :=
    psiTrunc_tail_uniform hα hα1 hsm hL2 hcd hδ0 hd
  have hpsi0 : ∀ z θ : ℝ, psiTrunc α F 0 z θ = 0 := by
    intro z θ
    rw [Work.FTS.PhiStar.Series.psiTrunc, Finset.range_one, Finset.sum_singleton,
      Work.FTS.H2.ModalSol.acoeff_zero_of_orth horth α z]
    ring
  refine ⟨max 1 (K * b 0), lt_max_of_lt_left one_pos, fun z hz θ hθ => ?_⟩
  have hθ0 : 0 < θ := lt_of_lt_of_le hδ0 hθ.1
  have hθ1 : θ < π / 2 := lt_of_le_of_lt hθ.2 (by linarith [hδ0])
  have hlim := Work.FTS.H2.ModalSolR.psiTrunc_tendsto_Psi α hα hα1 horth hsm hL2 hz
    (show θ ∈ Set.Ioo 0 (π / 2) from ⟨hθ0, hθ1⟩)
  have hdiff : Tendsto (fun N : ℕ => |psiTrunc α F 0 z θ - psiTrunc α F N z θ|) Filter.atTop
      (nhds |psiTrunc α F 0 z θ - Psis α F z θ|) := (tendsto_const_nhds.sub hlim).abs
  have hbd : Tendsto (fun N : ℕ => K * z ^ (-(1 / 2) : ℝ) * (b 0 + b N)) Filter.atTop
      (nhds (K * z ^ (-(1 / 2) : ℝ) * (b 0 + 0))) :=
    (tendsto_const_nhds.add hbT).const_mul _
  have hle : |psiTrunc α F 0 z θ - Psis α F z θ| ≤ K * z ^ (-(1 / 2) : ℝ) * b 0 := by
    have h := le_of_tendsto_of_tendsto' hdiff hbd (fun N => htail 0 N z θ hz hθ)
    simpa using h
  rw [hpsi0, zero_sub, abs_neg] at hle
  refine le_trans hle ?_
  calc K * z ^ (-(1 / 2) : ℝ) * b 0 = (K * b 0) * z ^ (-(1 / 2) : ℝ) := by ring
    _ ≤ max 1 (K * b 0) * z ^ (-(1 / 2) : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hz.le _)

/-- **The modal solution decays at `z → ∞` in every direction of `Iθ`** (clean reproof). -/
theorem Psi_tendsto_atTop_zero_mod (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {F : ℝ → ℝ → ℝ} (horth : Work.Elliptic.OrthCond F)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2) Q0) :
    ∀ θ ∈ Iθ, Tendsto (fun z => Psis α F z θ) atTop (nhds 0) := by
  intro θ hθ
  rcases lt_or_eq_of_le hθ.1 with hθ0 | rfl
  · rcases lt_or_eq_of_le hθ.2 with hθ1 | rfl
    · set δ : ℝ := min θ (π / 2 - θ) / 2 with hδdef
      have hδ0 : 0 < δ := div_pos (lt_min hθ0 (sub_pos.mpr hθ1)) (by norm_num)
      have hδ4 : δ < π / 4 := by
        have h2 : δ ≤ θ / 2 := by
          rw [hδdef]
          exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
        linarith
      have hmem : θ ∈ Set.Icc δ (π / 2 - δ) := by
        refine ⟨?_, ?_⟩
        · rw [hδdef]
          exact le_trans (div_le_self (le_of_lt (lt_min hθ0 (sub_pos.mpr hθ1)))
            (by norm_num : (1 : ℝ) ≤ 2)) (min_le_left _ _)
        · rw [hδdef]
          have h2 : min θ (π / 2 - θ) ≤ π / 2 - θ := min_le_right _ _
          linarith
      obtain ⟨C, hC0, hbnd⟩ := Psi_bound_mod α hα hα1 horth hsm hL2 hδ0 hδ4
      have h1 : Tendsto (fun z : ℝ => C * z ^ (-(1 / 2) : ℝ)) atTop (nhds 0) := by
        simpa using tendsto_const_nhds.mul
          (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 2 by norm_num))
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero' (Filter.Eventually.of_forall (fun z => norm_nonneg _)) ?_ h1
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
      rw [Real.norm_eq_abs]
      exact hbnd z hz θ hmem
    · exact tendsto_const_nhds.congr' (Filter.Eventually.of_forall
        (fun z => (Work.FTS.H2.ModalSol.Psi_apply_pi_half α F z).symm))
  · exact tendsto_const_nhds.congr' (Filter.Eventually.of_forall
      (fun z => (Work.FTS.H2.ModalSol.Psi_apply_zero α F z).symm))

end Work.FTS.PhiStar.Honesty.NodeAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.SZML2.Local =====
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

/-! ## Continuity on the open quadrant, and a.e. strong measurability of the slices -/

/-- The open quadrant `(0,∞) × (0,π/2)`. -/
def Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

lemma continuousOn_psi {Φ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    ContinuousOn (fun p : ℝ × ℝ => psi Φ p.1 p.2) Qd := by
  have hΦ : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) Qd := (hsm 0).continuousOn
  have hs2 : ContinuousOn (fun p : ℝ × ℝ => Work.Construction.s2 p.2) Qd :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  exact ContinuousOn.div hΦ hs2 (fun p hp => ne_of_gt (sin_two_pos_of_mem hp.2))

lemma continuousOn_slot {Φ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    ContinuousOn (fun p : ℝ × ℝ => (psi Φ p.1 p.2
      * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2) Qd := by
  have hpsi := continuousOn_psi (Φ := Φ) hsm
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Qd :=
    ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  have hs : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) Qd :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (sin_two_pos_of_mem hp.2)))
  exact (hpsi.mul (hw.div hs (fun p hp =>
    ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_of_mem hp.2) _)))).pow 2

lemma continuousOn_absPhi {Φ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    ContinuousOn (fun p : ℝ × ℝ => |Φ p.1 p.2|) Qd :=
  (hsm 0).continuousOn.abs

lemma continuousOn_PhiSqRoot {Φ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2 ^ 2 * rootWeight p.2) Qd := by
  have hΦ : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) Qd := (hsm 0).continuousOn
  have hrw : ContinuousOn (fun p : ℝ × ℝ => rootWeight p.2) Qd := by
    show ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(2 + Work.Spaces.eta))) Qd
    exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (sin_two_pos_of_mem hp.2)))
  exact (hΦ.pow 2).mul hrw

lemma continuousOn_mode {Φ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) (m : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ =>
      Φ p.1 p.2 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2 * Real.cos p.2) Qd := by
  have hΦ : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) Qd := (hsm 0).continuousOn
  have he : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m p.2) Qd :=
    (((Real.continuous_cos.mul ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC
      (2 * m + 1)).continuous.comp Real.continuous_sin)).comp continuous_snd)).continuousOn
  have hc : ContinuousOn (fun p : ℝ × ℝ => Real.cos p.2) Qd :=
    (Real.continuous_cos.comp continuous_snd).continuousOn
  exact (hΦ.mul he).mul hc

/-- Marginal measurability: a function continuous on the open quadrant has `θ`-integrals
that are a.e. strongly measurable in `z` on `Iz = [0,∞)`. -/
lemma aesm_sliceIntegral {g : ℝ × ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ, g (z, θ))
      (volume.restrict Work.Spaces.Iz) :=
  (Work.Spaces.aesm_of_continuousOn_Qd g hg).integral_prod_right'
    (ν := volume.restrict Work.Spaces.Iθ)

/-- The same, on a measurable subset of `Iz`. -/
lemma aesm_sliceIntegral_of_subset {g : ℝ × ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) {s : Set ℝ}
    (hs : s ⊆ Work.Spaces.Iz) (hsm : MeasurableSet s) :
    AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ, g (z, θ)) (volume.restrict s) := by
  have h := aesm_sliceIntegral hg
  have hEq : volume.restrict s = (volume.restrict Work.Spaces.Iz).restrict s := by
    rw [MeasureTheory.Measure.restrict_restrict hsm, Set.inter_eq_left.mpr hs]
  rw [hEq]
  exact h.restrict

/-! ## `θ`-integrability of the `(0,0)` slot of `Ψ` and of `|Φ|` -/

/-- `θ ∈ (0,π/2)` for a.e. `θ` of `Iθ` (the two endpoints are null). -/
lemma ae_mem_Ioo_Iθ : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  have hEq : volume.restrict Work.Spaces.Iθ
      = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl]
    exact MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc).symm
  rw [hEq]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- The `(0,0)` slot of `Ψ` is `θ`-integrable on `Iθ` for every `z > 0` (and the constant
`w(z)² ≠ 0` can be removed). -/
lemma integrableOn_psi_sq_rpow {α : ℝ} {Φ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hHk : Work.Spaces.HkMem α 6 (psi Φ)) {z : ℝ} (hz : z ∈ Set.Ioi 0) :
    MeasureTheory.IntegrableOn (fun θ => (psi Φ z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) Work.Spaces.Iθ := by
  have hquad := continuousOn_slot (Φ := Φ) hsm
  have hslot : MeasureTheory.IntegrableOn (fun θ => (psi Φ z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono'
      (hHk.1 z (by show (0 : ℝ) ≤ z; exact le_of_lt hz))
      (Work.Spaces.aesm_slice_of_continuousOn_Qd _ hquad hz) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact Work.Spaces.sq_le_HkIntegrand_z α 6 (psi Φ) z θ 0 (by norm_num)
  have h2 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.w z) ^ 2
      * ((psi Φ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))) Work.Spaces.Iθ :=
    hslot.congr (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => slot0_integrand_eq Φ z hθ))
  have h3 : MeasureTheory.Integrable (fun θ => ((Work.Spaces.w z) ^ 2)⁻¹
      * ((Work.Spaces.w z) ^ 2
        * ((psi Φ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))))
      (volume.restrict Work.Spaces.Iθ) := h2.const_mul _
  refine h3.congr (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => ?_))
  exact inv_mul_cancel_left₀ (ne_of_gt (w_sq_pos hz)) _

/-- `|Φ z ·|` is `θ`-integrable on `Iθ` for `z > 0`: AM–GM with the pair
`|Ψ| sin(2θ)^{-η/2}` and `sin(2θ)^{1+η/2}`. -/
lemma integrableOn_abs_Phi {Φ : ℝ → ℝ → ℝ} {z : ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hz : 0 < z)
    (hint : MeasureTheory.IntegrableOn (fun θ => (psi Φ z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => |Φ z θ|) Work.Spaces.Iθ := by
  haveI : MeasureTheory.IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) := ⟨by
    rw [MeasureTheory.Measure.restrict_apply_univ, show Work.Spaces.Iθ
      = Set.Icc (0 : ℝ) (π / 2) from rfl, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩
  have hsin : MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta))
      Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ)) ?_ ?_
    · exact (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
        (fun θ _ => Or.inr (le_of_lt two_add_eta_pos))).aestronglyMeasurable measurableSet_Icc
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ' hθ) _)]
      exact Real.rpow_le_one (sin_two_nonneg_of_mem_Iθ' hθ) (Real.sin_le_one (2 * θ))
        (le_of_lt two_add_eta_pos)
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ => |Φ z θ|)
      (volume.restrict Work.Spaces.Iθ) :=
    (Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry Φ) (hsm 0).continuousOn hz).norm
  have hsum : MeasureTheory.IntegrableOn (fun θ => ((psi Φ z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
        + (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta)) / 2) Work.Spaces.Iθ :=
    (hint.add hsin).div_const 2
  refine MeasureTheory.Integrable.mono' hsum haesm ?_
  filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem hθ
  simp only [Real.norm_eq_abs, abs_abs]
  have hΦ : Φ z θ = psi Φ z θ * Real.sin (2 * θ) := by
    rw [psi_apply, Work.Construction.s2, div_mul_cancel₀ _ (ne_of_gt hs)]
  have hsqrt : Real.sqrt ((Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      * Real.sqrt ((Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta)) = Real.sin (2 * θ) := by
    rw [← Real.sqrt_mul (Real.rpow_nonneg (le_of_lt hs) _)]
    have h : (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
        * (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta) = (Real.sin (2 * θ)) ^ (2 : ℕ) := by
      rw [← Real.rpow_add hs (-Work.Spaces.eta) (2 + Work.Spaces.eta),
        show (-Work.Spaces.eta) + (2 + Work.Spaces.eta) = (2 : ℝ) by ring]
      exact Real.rpow_natCast _ 2
    rw [h, Real.sqrt_sq (le_of_lt hs)]
  have habs : |Φ z θ| = |psi Φ z θ| * Real.sin (2 * θ) := by
    rw [hΦ, abs_mul, abs_of_pos hs]
  have hamgm : |psi Φ z θ| * Real.sin (2 * θ)
      ≤ ((psi Φ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
          + (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta)) / 2 := by
    have hsquare := sq_nonneg (|psi Φ z θ| * Real.sqrt ((Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      - Real.sqrt ((Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta)))
    have h1 : (|psi Φ z θ| * Real.sqrt ((Real.sin (2 * θ)) ^ (-Work.Spaces.eta))) ^ 2
        = (psi Φ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
      rw [mul_pow, sq_abs, Real.sq_sqrt (Real.rpow_nonneg (le_of_lt hs) _)]
    have h2 : (Real.sqrt ((Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta))) ^ 2
        = (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta) :=
      Real.sq_sqrt (Real.rpow_nonneg (le_of_lt hs) _)
    have h3 : |psi Φ z θ| * Real.sin (2 * θ)
        = (|psi Φ z θ| * Real.sqrt ((Real.sin (2 * θ)) ^ (-Work.Spaces.eta)))
            * Real.sqrt ((Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta)) := by
      rw [mul_assoc, hsqrt]
    rw [h3]
    nlinarith [hsquare, h1, h2]
  rw [habs]
  exact hamgm

/-! ## The `θ`-integral bounds for `sin(2θ)^{2+η}` -/

/-- Constant bounding `∫_{Iθ} sin(2θ)^{2+η}`: `√(π/2)`. -/
def K3 : ℝ := Real.sqrt (Real.pi / 2)

/-- Constant bounding the boundary-layer factor `√(∫_E sin(2θ)^{2+η})` by
`C·δ^{(3+η)/2}`. -/
def K4 : ℝ := Real.sqrt ((2 : ℝ) ^ (2 + Work.Spaces.eta))

lemma K3_pos : 0 < K3 := Real.sqrt_pos_of_pos (by positivity)

lemma K4_pos : 0 < K4 := Real.sqrt_pos_of_pos (by positivity)

lemma sqrt_sin_int_Iθ_le : Real.sqrt (∫ θ in Work.Spaces.Iθ,
    (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta)) ≤ K3 := by
  rw [K3]
  exact Real.sqrt_le_sqrt (sin_two_rpow_integral_le (1 / 2) (by norm_num) (by
    linarith [Real.pi_gt_three])).2.2

/-- `√(∫_E sin(2θ)^{2+η}) ≤ K4 δ^{(3+η)/2}` for the boundary layers `E`. -/
lemma sqrt_sin_int_layer_le {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ Real.pi / 4) :
    Real.sqrt (∫ θ in Set.Ioo (0 : ℝ) δ, (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta))
        ≤ K4 * δ ^ ((3 + Work.Spaces.eta) / 2) ∧
      Real.sqrt (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
          (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta))
        ≤ K4 * δ ^ ((3 + Work.Spaces.eta) / 2) := by
  have hsq : Real.sqrt (δ ^ (3 + Work.Spaces.eta))
      = δ ^ ((3 + Work.Spaces.eta) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hδ) (3 + Work.Spaces.eta) (1 / 2 : ℝ)]
    congr 1
    ring
  have hreal : Real.sqrt ((2 : ℝ) ^ (2 + Work.Spaces.eta) * δ ^ (3 + Work.Spaces.eta))
      = K4 * δ ^ ((3 + Work.Spaces.eta) / 2) := by
    rw [Real.sqrt_mul (Real.rpow_nonneg (by norm_num) _), K4, hsq]
  obtain ⟨hb1, hb2, -⟩ := sin_two_rpow_integral_le δ hδ hδ4
  refine ⟨?_, ?_⟩
  · rw [← hreal]
    exact Real.sqrt_le_sqrt hb1
  · rw [← hreal]
    exact Real.sqrt_le_sqrt hb2

/-! ## The slice Cauchy–Schwarz bound (the interface of the target statement) -/

/-- The Cauchy–Schwarz slice bound, with the constant `√(sliceEnergy Φ z)` factored out. -/
lemma slice_abs_le_sqrt {Φ : ℝ → ℝ → ℝ} (hint : ∀ z ∈ Set.Ioi (0 : ℝ),
    MeasureTheory.IntegrableOn
    (fun θ => (psi Φ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) Work.Spaces.Iθ)
    {z : ℝ} (hz : z ∈ Set.Ioi 0) {E : Set ℝ} (hE : E ⊆ Work.Spaces.Iθ) :
    ∫ θ in E, |Φ z θ| ≤ Real.sqrt (sliceEnergy Φ z)
      * Real.sqrt (∫ θ in E, (Real.sin (2 * θ)) ^ (2 + Work.Spaces.eta)) :=
  slice_abs_le_sqrt_sliceEnergy (Φ := Φ) (z := z) (E := E) hE
    (by simpa only [psi_apply, Work.Construction.s2] using hint z hz)

end

end Work.FTS.StrongEps.EComparison
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.WProd5.mslot_le_winf5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real

open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5.WProd5

open Work.Spaces

open Work.FTS.OpenPkg.WProdWin (TW)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Elementary angular and weight algebra -/

/-- The binomial coefficients of the rows `0 ≤ n ≤ 5` are at most `16` (for `n ≤ 4` because
`n.choose k ≤ 2^n ≤ 16`, and for `n = 5` by direct evaluation: the largest entry of the fifth
row is `5.choose 2 = 10`), hence their squares are at most `256`. -/
private theorem choose_sq_le_256_five (n k : ℕ) (hkn : k ≤ n) (hn : n ≤ 5) :
    ((n.choose k : ℕ) : ℝ) ^ 2 ≤ 256 := by
  have h1 : n.choose k ≤ 16 := by
    rcases Nat.lt_or_ge n 5 with h | h
    · have h2 : n.choose k ≤ 2 ^ n := Nat.choose_le_two_pow n k
      have h3 : 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h4 : (2 : ℕ) ^ 4 = 16 := by norm_num
      omega
    · have hn5 : n = 5 := by omega
      subst hn5
      interval_cases k <;> decide
  have h1' : ((n.choose k : ℕ) : ℝ) ≤ 16 := by exact_mod_cast h1
  have h0 : (0 : ℝ) ≤ ((n.choose k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hm := mul_self_le_mul_self h0 h1'
  rw [sq]
  norm_num at hm ⊢
  linarith [hm]

private theorem sin_two_nonneg_of_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 ≤ Real.sin (2 * θ) :=
  (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])).le

/-- The square of the `f`-side angular factor `(α + sin 2θ) sin(2θ)^{α/5}` is
`(α + sin 2θ)² sin(2θ)^{2α/5}`. -/
private theorem phi_sq {α θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
      = (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5) := by
  rw [mul_pow]
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Ioo hθ
  have hss : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 = (Real.sin (2 * θ)) ^ (2 * α / 5) := by
    rw [show ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2
          = ((Real.sin (2 * θ)) ^ (α / 5)) ^ ((2 : ℝ)) from (Real.rpow_natCast _ 2).symm,
      ← Real.rpow_mul hs, show (α / 5) * (2 : ℝ) = 2 * α / 5 by ring]
  rw [hss]

/-- `(α + sin 2θ)² sin(2θ)^{2α/5} ≤ 4` for `0 < α ≤ 1` and `0 < θ < π/2`. -/
private theorem psi2_le_four {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5) ≤ 4 := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Ioo hθ
  have h1 : (Real.sin (2 * θ)) ^ (2 * α / 5) ≤ 1 :=
    Real.rpow_le_one hs (Real.sin_le_one _) (by linarith)
  have h2 : (α + Real.sin (2 * θ)) ^ 2 ≤ 4 := by
    nlinarith [hs, Real.sin_le_one (2 * θ), hα, hα1]
  nlinarith [h1, h2, Real.rpow_nonneg hs (2 * α / 5)]

/-- On the open quadrant, `(x·W)² = (x·w)² sin(2θ)^{-γ}`. -/
private theorem mul_Wt_sq {α z θ x : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (x * Work.Spaces.Wt α z θ) ^ 2
      = (x * Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hstep : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [pow_two, ← Real.rpow_add hs]
    congr 1
    ring
  simp only [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, hstep]
  ring

/-! ## The `g`-side step: the mean-term hypothesis produces the `TW`-block of `GmajW5` -/

private theorem mslot_gside_le5 {α CB : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hgm : Work.Spaces.HkMem α 5 g)
    (hCB : ∀ d : ℕ, d ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
          ≤ CB * ((Work.Spaces.w z) ^ 2
                * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
              + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z))
    {d : ℕ} (hd : d ≤ 4) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
        * (Work.Spaces.DzIter d g z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ max CB 1 * GmajW5 α g z θ := by
  have hγ1 : (0 : ℝ) < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hγinv : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ := inv_nonneg.mpr hγ1.le
  have hCBB0 : (0 : ℝ) ≤ max CB 1 := le_trans zero_le_one (le_max_right CB 1)
  have hCBle : CB ≤ max CB 1 := le_max_left CB 1
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Ioo hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hTWnn : 0 ≤ Work.FTS.OpenPkg.WProdWin.TW α θ :=
    Work.FTS.OpenPkg.WProdWin.TW_nonneg hα.le hθI
  -- the mean-term block is nonnegative
  have hX0 : 0 ≤ (Work.Spaces.w z) ^ 2
        * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
      + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z :=
    add_nonneg (mul_nonneg (sq_nonneg _)
        (setIntegral_nonneg measurableSet_Icc (fun σ _ => sq_nonneg _)))
      (mul_nonneg hγinv (Work.FTS.H2.WPQ.Aang_nonneg α g d z))
  have hg1 : (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
      ≤ max CB 1 * ((Work.Spaces.w z) ^ 2
          * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
        + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z) :=
    le_trans (hCB d hd z θ hz hθ.1 hθ.2) (mul_le_mul_of_nonneg_right hCBle hX0)
  -- the mean term and the single `Aang` term are both dominated by `HgInt5`/`∑Aang`
  have hmem : d ∈ Finset.range 5 := Finset.mem_range.mpr (by omega)
  have hAang_le : Work.FTS.H2.WPQ.Aang α g d z
      ≤ ∑ d' ∈ Finset.range 5, Work.FTS.H2.WPQ.Aang α g d' z :=
    Finset.single_le_sum (fun d' _ => Work.FTS.H2.WPQ.Aang_nonneg α g d' z) hmem
  have hw : (Work.Spaces.w z) ^ 2
        * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2) ≤ HgInt5 α g z :=
    w_sq_mul_slice_le_HgInt5 hgm (by omega) hz
  have hXle : (Work.Spaces.w z) ^ 2
          * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
        + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z
      ≤ HgInt5 α g z + (Work.Spaces.gam α - 1)⁻¹
          * ∑ d' ∈ Finset.range 5, Work.FTS.H2.WPQ.Aang α g d' z :=
    add_le_add hw (mul_le_mul_of_nonneg_left hAang_le hγinv)
  -- `(D_z^d g · W)² · (α+sin2θ)²sin(2θ)^{2α/5} = (D_z^d g · w)² · TW`
  rw [mul_Wt_sq hθ]
  have hBS : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)) = TW α θ := by
    rw [Work.FTS.OpenPkg.WProdWin.TW_eq_mul hθ]; ring
  rw [show ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
        * ((Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2 * TW α θ from by rw [← hBS]; ring]
  refine le_trans (mul_le_mul_of_nonneg_right hg1 hTWnn) ?_
  have hXTW : ((Work.Spaces.w z) ^ 2
          * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
        + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z) * TW α θ
      ≤ GmajW5 α g z θ := by
    simp only [GmajW5]
    exact le_trans (mul_le_mul_of_nonneg_right hXle hTWnn)
      (le_add_of_nonneg_left (Work.Spaces.HkIntegrand_nonneg α 5 g z θ))
  calc (max CB 1 * ((Work.Spaces.w z) ^ 2
            * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
          + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z)) * TW α θ
      = max CB 1 * (((Work.Spaces.w z) ^ 2
            * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
          + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z) * TW α θ) := by ring
    _ ≤ max CB 1 * GmajW5 α g z θ := mul_le_mul_of_nonneg_left hXTW hCBB0

/-! ## The mixed slots -/

/-- **The mixed slots of the level-`5` `𝒲^{5,∞}`-priced product rule.**

The literal `4 ↦ 5` shift of the *proved* `Work.FTS.OpenPkg.WProdWin.mslot_le_winf`
(`Submission/Work/FTS/OpenPkg/WProdWin/mslot_le_winf.lean`), and at the same time the `6 ↦ 5`
shift of the *proved* `Work.FTS.StrongPersist.H6Rows.WProd6.mslot_le_winf6`
(`Submission/Work/FTS/StrongPersist/H6Rows/wprod6/mslot_le_winf6.lean`): `WlInfMem α 4 → 5`,
`HkMem α 4 → 5`, `I + J ≤ 4 → 5`, `HkIntegrand α 4 → 5`, `GmajW → GmajW5`, and the mean-term
hypothesis `CB` for `d ≤ 4`.  In the `a = I` branch (all `θ`-derivatives on `f`) one needs
`d ≤ 4` for the `g`-slot `D_z^{J-b} g`, and the `f`-side bound is
`Pointwise5.mixed_le_WlInf5`. -/
theorem mslot_le_winf5 (CB : ℝ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 5 f →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 5 g →
      (∀ d : ℕ, d ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
          ≤ CB * ((Work.Spaces.w z) ^ 2
                * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
              + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z)) →
      ∀ I J : ℕ, 1 ≤ I → I + J ≤ 5 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.mixed J I (fun z θ => f z θ * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ C * (Work.Spaces.WlInf α 5 f) ^ 2
            * Work.FTS.StrongEps.H5.WProd5.GmajW5 α g z θ := by
  have hCpos : (0 : ℝ) < 2 * 10 ^ 12 * (1 + max CB 1) := by
    have h2 : (0 : ℝ) < 2 * 10 ^ 12 := by norm_num
    have h1 : (1 : ℝ) ≤ max CB 1 := le_max_right CB 1
    have h3 : (0 : ℝ) < 1 + max CB 1 := by linarith
    exact mul_pos h2 h3
  refine ⟨2 * 10 ^ 12 * (1 + max CB 1), hCpos, ?_⟩
  intro α f g hα hα1 hf hfm hg hgm hCB I J hI hIJ z θ hz hθ0 hθ1
  have hW : 0 ≤ Work.Spaces.WlInf α 5 f := Work.Spaces.WlInf_nonneg α 5 f hfm
  have hWsq : 0 ≤ (Work.Spaces.WlInf α 5 f) ^ 2 := sq_nonneg _
  have hγinv : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ :=
    inv_nonneg.mpr (by rw [Work.Spaces.gam_sub_one]; linarith)
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_Ioo hθ
  have hGnn : 0 ≤ GmajW5 α g z θ := GmajW5_nonneg hα g hθI
  have hTWnn : 0 ≤ TW α θ := Work.FTS.OpenPkg.WProdWin.TW_nonneg hα.le hθI
  have hHknn : 0 ≤ Work.Spaces.HkIntegrand α 5 g z θ := Work.Spaces.HkIntegrand_nonneg α 5 g z θ
  have hHkG : Work.Spaces.HkIntegrand α 5 g z θ ≤ GmajW5 α g z θ := HkIntegrand_le_GmajW5 hα g hθI
  have hCBB0 : (0 : ℝ) ≤ max CB 1 := le_trans zero_le_one (le_max_right CB 1)
  have hKper_nn : (0 : ℝ) ≤ 65536 * 40000 * (1 + max CB 1) :=
    mul_nonneg (by norm_num) (by linarith)
  have hJ5 : J ≤ 5 := by omega
  have hI5 : I ≤ 5 := by omega
  have hA2nn : 0 ≤ (α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
  -- Leibniz in the open class
  have heq := Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed J I f g hf hg z θ hz hθ0 hθ1
  set Y : ℕ → ℕ → ℝ := fun a b => (I.choose a : ℝ) * (J.choose b : ℝ)
    * ((Work.Spaces.mixed b a f z θ)
        * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) with hYdef
  have hYsplit : (Work.Spaces.mixed J I (fun z θ => f z θ * g z θ) z θ
        * Work.Spaces.Wt α z θ) ^ 2
      = (∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b) ^ 2 := by
    have hkey : (Work.Spaces.mixed J I (fun z θ => f z θ * g z θ) z θ)
          * Work.Spaces.Wt α z θ
        = ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b := by
      rw [heq, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b hb
      simp only [hYdef]
      ring
    rw [hkey]
  -- the pointwise bound for each summand of the double sum
  have hper : ∀ a ∈ Finset.range (I + 1), ∀ b ∈ Finset.range (J + 1),
      (Y a b) ^ 2 ≤ (65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 5 f) ^ 2
        * GmajW5 α g z θ := by
    intro a ha b hb
    have haI : a ≤ I := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    have hbJ : b ≤ J := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hch : (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2 ≤ 65536 :=
      calc (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2 ≤ 256 * 256 :=
            mul_le_mul (choose_sq_le_256_five I a (by omega) hI5)
              (choose_sq_le_256_five J b (by omega) hJ5) (by positivity) (by norm_num)
        _ = 65536 := by norm_num
    have hY : (Y a b) ^ 2 = (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2
        * ((Work.Spaces.mixed b a f z θ)
            * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2 := by
      rw [hYdef]; ring
    rw [hY]
    by_cases hlt : a < I
    · -- at least one `θ`-derivative falls on `g`
      have hIa : 1 ≤ I - a := by omega
      have hma : (Work.Spaces.mixed b a f z θ) ^ 2
          ≤ 40000 * (Work.Spaces.WlInf α 5 f) ^ 2 := by
        rcases eq_or_ne a 0 with ha0 | ha0
        · subst ha0
          have h : |Work.Spaces.DzIter b f z θ| ≤ 100 * Work.Spaces.WlInf α 5 f :=
            dzIter_le_WlInf5 (α := α) (f := f) (b := b) (z := z) (θ := θ)
              hf hfm (by omega) hz hθ
          have h1 : (Work.Spaces.DzIter b f z θ) ^ 2
              ≤ (100 * Work.Spaces.WlInf α 5 f) ^ 2 := Work.Spaces.sq_le_sq_of_abs_le h
          show (Work.Spaces.DzIter b f z θ) ^ 2 ≤ 40000 * (Work.Spaces.WlInf α 5 f) ^ 2
          nlinarith [h1, sq_nonneg (100 * Work.Spaces.WlInf α 5 f)]
        · have ha1 : 1 ≤ a := by omega
          have h := mixed_le_WlInf5 (α := α) (f := f) (a := a) (b := b)
            (z := z) (θ := θ) hα hf hfm ha1 (by omega) hz hθ
          calc (Work.Spaces.mixed b a f z θ) ^ 2
              ≤ (100 * (Work.Spaces.WlInf α 5 f
                  * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) ^ 2 :=
                Work.Spaces.sq_le_sq_of_abs_le h
            _ = (100 * Work.Spaces.WlInf α 5 f) ^ 2
                  * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)) := by
                rw [mul_pow, mul_pow, phi_sq hθ]; ring
            _ ≤ (100 * Work.Spaces.WlInf α 5 f) ^ 2 * 4 :=
                mul_le_mul_of_nonneg_left (psi2_le_four hα hα1 hθ) (sq_nonneg _)
            _ = 40000 * (Work.Spaces.WlInf α 5 f) ^ 2 := by ring
      have hmg : (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α 5 g z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α 5 g z θ (I - a) (J - b) hIa (by omega)
      have hbase2 : ((Work.Spaces.mixed b a f z θ)
            * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2
          ≤ (40000 * (Work.Spaces.WlInf α 5 f) ^ 2) * Work.Spaces.HkIntegrand α 5 g z θ := by
        rw [mul_pow]
        calc (Work.Spaces.mixed b a f z θ) ^ 2
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ) ^ 2
            ≤ (40000 * (Work.Spaces.WlInf α 5 f) ^ 2)
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ) ^ 2 :=
              mul_le_mul_of_nonneg_right hma (sq_nonneg _)
          _ ≤ (40000 * (Work.Spaces.WlInf α 5 f) ^ 2) * Work.Spaces.HkIntegrand α 5 g z θ :=
              mul_le_mul_of_nonneg_left hmg (by nlinarith [hWsq])
      calc (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2
            * ((Work.Spaces.mixed b a f z θ)
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2
          ≤ 65536 * ((Work.Spaces.mixed b a f z θ)
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2 :=
            mul_le_mul_of_nonneg_right hch (sq_nonneg _)
        _ ≤ 65536 * ((40000 * (Work.Spaces.WlInf α 5 f) ^ 2)
              * Work.Spaces.HkIntegrand α 5 g z θ) :=
            mul_le_mul_of_nonneg_left hbase2 (by norm_num)
        _ ≤ 65536 * 40000 * (1 + max CB 1) * (Work.Spaces.WlInf α 5 f) ^ 2 * GmajW5 α g z θ := by
            rw [show 65536 * ((40000 * (Work.Spaces.WlInf α 5 f) ^ 2)
                  * Work.Spaces.HkIntegrand α 5 g z θ)
                = (65536 * 40000 : ℝ) * ((Work.Spaces.WlInf α 5 f) ^ 2
                  * Work.Spaces.HkIntegrand α 5 g z θ) from by ring]
            calc (65536 * 40000 : ℝ) * ((Work.Spaces.WlInf α 5 f) ^ 2
                  * Work.Spaces.HkIntegrand α 5 g z θ)
                ≤ (65536 * 40000 : ℝ) * ((Work.Spaces.WlInf α 5 f) ^ 2 * GmajW5 α g z θ) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hHkG hWsq) (by norm_num)
              _ ≤ (65536 * 40000 * (1 + max CB 1))
                    * ((Work.Spaces.WlInf α 5 f) ^ 2 * GmajW5 α g z θ) :=
                  mul_le_mul_of_nonneg_right (by nlinarith [hCBB0]) (mul_nonneg hWsq hGnn)
              _ = 65536 * 40000 * (1 + max CB 1) * (Work.Spaces.WlInf α 5 f) ^ 2
                    * GmajW5 α g z θ := by ring
    · -- all `θ`-derivatives fall on `f`: the mean-term hypothesis is used
      have hac : a = I := by omega
      have hsub : I - a = 0 := by omega
      have hdJ : J - b ≤ 4 := by omega
      have hmb : (Work.Spaces.mixed b a f z θ) ^ 2
          ≤ (100 * Work.Spaces.WlInf α 5 f) ^ 2
            * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)) := by
        have ha1 : 1 ≤ a := by omega
        have h := mixed_le_WlInf5 (α := α) (f := f) (a := a) (b := b)
          (z := z) (θ := θ) hα hf hfm ha1 (by omega) hz hθ
        calc (Work.Spaces.mixed b a f z θ) ^ 2
            ≤ (100 * (Work.Spaces.WlInf α 5 f
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) ^ 2 :=
              Work.Spaces.sq_le_sq_of_abs_le h
          _ = (100 * Work.Spaces.WlInf α 5 f) ^ 2
                * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)) := by
              rw [mul_pow, mul_pow, phi_sq hθ]; ring
      have hT : (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ) ^ 2
          = (Work.Spaces.DzIter (J - b) g z θ * Work.Spaces.Wt α z θ) ^ 2 := by
        have he : Work.Spaces.mixed (J - b) (I - a) g = Work.Spaces.DzIter (J - b) g := by
          rw [hsub, Work.Spaces.mixed_zero_right]
        rw [he]
      have hgside : ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
            * (Work.Spaces.DzIter (J - b) g z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ max CB 1 * GmajW5 α g z θ :=
        mslot_gside_le5 (α := α) (CB := CB) (g := g) (d := J - b) hα hgm hCB hdJ hz hθ
      have hbase2 : ((Work.Spaces.mixed b a f z θ)
            * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2
          ≤ (100 * Work.Spaces.WlInf α 5 f) ^ 2 * (max CB 1) * GmajW5 α g z θ := by
        rw [mul_pow]
        calc (Work.Spaces.mixed b a f z θ) ^ 2
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ) ^ 2
            = (Work.Spaces.mixed b a f z θ) ^ 2
              * (Work.Spaces.DzIter (J - b) g z θ * Work.Spaces.Wt α z θ) ^ 2 := by rw [hT]
          _ ≤ ((100 * Work.Spaces.WlInf α 5 f) ^ 2
                * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5)))
              * (Work.Spaces.DzIter (J - b) g z θ * Work.Spaces.Wt α z θ) ^ 2 :=
              mul_le_mul_of_nonneg_right hmb (sq_nonneg _)
          _ = (100 * Work.Spaces.WlInf α 5 f) ^ 2
              * (((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5))
                * (Work.Spaces.DzIter (J - b) g z θ * Work.Spaces.Wt α z θ) ^ 2) := by ring
          _ ≤ (100 * Work.Spaces.WlInf α 5 f) ^ 2 * (max CB 1 * GmajW5 α g z θ) :=
              mul_le_mul_of_nonneg_left hgside (sq_nonneg _)
          _ = (100 * Work.Spaces.WlInf α 5 f) ^ 2 * (max CB 1) * GmajW5 α g z θ := by ring
      calc (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2
            * ((Work.Spaces.mixed b a f z θ)
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2
          ≤ 65536 * ((Work.Spaces.mixed b a f z θ)
              * (Work.Spaces.mixed (J - b) (I - a) g z θ * Work.Spaces.Wt α z θ)) ^ 2 :=
            mul_le_mul_of_nonneg_right hch (sq_nonneg _)
        _ ≤ 65536 * ((100 * Work.Spaces.WlInf α 5 f) ^ 2 * (max CB 1) * GmajW5 α g z θ) :=
            mul_le_mul_of_nonneg_left hbase2 (by norm_num)
        _ ≤ 65536 * 40000 * (1 + max CB 1) * (Work.Spaces.WlInf α 5 f) ^ 2 * GmajW5 α g z θ := by
            rw [show 65536 * ((100 * Work.Spaces.WlInf α 5 f) ^ 2 * (max CB 1) * GmajW5 α g z θ)
                = (65536 * 10000 * (max CB 1)) * ((Work.Spaces.WlInf α 5 f) ^ 2
                    * GmajW5 α g z θ) from by ring]
            have hAB : (65536 * 10000 * (max CB 1) : ℝ)
                ≤ 65536 * 40000 * (1 + max CB 1) := by nlinarith [hCBB0]
            calc (65536 * 10000 * (max CB 1)) * ((Work.Spaces.WlInf α 5 f) ^ 2
                    * GmajW5 α g z θ)
                ≤ (65536 * 40000 * (1 + max CB 1))
                    * ((Work.Spaces.WlInf α 5 f) ^ 2 * GmajW5 α g z θ) :=
                  mul_le_mul_of_nonneg_right hAB (mul_nonneg hWsq hGnn)
              _ = 65536 * 40000 * (1 + max CB 1) * (Work.Spaces.WlInf α 5 f) ^ 2
                    * GmajW5 α g z θ := by ring
  -- Cauchy–Schwarz on the double sum
  have hIJ25 : ((I : ℝ) + 1) * ((J : ℝ) + 1) ≤ 25 := by
    have h1 : (I : ℝ) + (J : ℝ) ≤ 5 := by exact_mod_cast hIJ
    have h2 : (0 : ℝ) ≤ (I : ℝ) + 1 := by positivity
    have h3 : (0 : ℝ) ≤ (J : ℝ) + 1 := by positivity
    nlinarith [sq_nonneg ((I : ℝ) + 1 - ((J : ℝ) + 1))]
  have hsum2 : ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2
      ≤ ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
          ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 5 f) ^ 2
            * GmajW5 α g z θ) :=
    Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => hper a ha b hb))
  have hsumconst : ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
        ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 5 f) ^ 2 * GmajW5 α g z θ)
      = ((I : ℝ) + 1) * ((J : ℝ) + 1)
        * ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 5 f) ^ 2
            * GmajW5 α g z θ) := by
    rw [Finset.sum_const, Finset.sum_const, Finset.card_range, Finset.card_range,
      nsmul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  rw [hYsplit]
  have hcardI : (((Finset.range (I + 1)).card : ℕ) : ℝ) = (I : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hcardJ : (((Finset.range (J + 1)).card : ℕ) : ℝ) = (J : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  calc (∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b) ^ 2
      ≤ ((I : ℝ) + 1) * ∑ a ∈ Finset.range (I + 1),
          ((J : ℝ) + 1) * ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2 := by
        have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (I + 1))
          (f := fun a => ∑ b ∈ Finset.range (J + 1), Y a b)
        rw [hcardI] at hcs
        refine hcs.trans ?_
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => ?_)) (by positivity)
        have hcs2 := sq_sum_le_card_mul_sum_sq (s := Finset.range (J + 1))
          (f := fun b => Y a b)
        rwa [hcardJ] at hcs2
    _ = ((I : ℝ) + 1) * ((J : ℝ) + 1)
          * ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2 := by
        rw [← Finset.mul_sum]; ring
    _ ≤ ((I : ℝ) + 1) * ((J : ℝ) + 1)
          * ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
              ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 5 f) ^ 2
                * GmajW5 α g z θ) :=
        mul_le_mul_of_nonneg_left hsum2 (by positivity)
    _ = (((I : ℝ) + 1) * ((J : ℝ) + 1)) ^ 2
          * ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 5 f) ^ 2
              * GmajW5 α g z θ) := by rw [hsumconst]; ring
    _ ≤ 625 * ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 5 f) ^ 2
            * GmajW5 α g z θ) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (mul_nonneg hKper_nn hWsq) hGnn)
        have h0 : (0 : ℝ) ≤ ((I : ℝ) + 1) * ((J : ℝ) + 1) := by positivity
        nlinarith [hIJ25, h0]
    _ ≤ (2 * 10 ^ 12 * (1 + max CB 1)) * (Work.Spaces.WlInf α 5 f) ^ 2 * GmajW5 α g z θ := by
        rw [show 625 * ((65536 * 40000 * (1 + max CB 1)) * (Work.Spaces.WlInf α 5 f) ^ 2
              * GmajW5 α g z θ)
            = (625 * (65536 * 40000 * (1 + max CB 1))) * ((Work.Spaces.WlInf α 5 f) ^ 2
              * GmajW5 α g z θ) from by ring]
        have hle : 625 * (65536 * 40000 * (1 + max CB 1)) ≤ 2 * 10 ^ 12 * (1 + max CB 1) := by
          nlinarith [hCBB0]
        calc (625 * (65536 * 40000 * (1 + max CB 1)))
              * ((Work.Spaces.WlInf α 5 f) ^ 2 * GmajW5 α g z θ)
            ≤ (2 * 10 ^ 12 * (1 + max CB 1))
              * ((Work.Spaces.WlInf α 5 f) ^ 2 * GmajW5 α g z θ) :=
              mul_le_mul_of_nonneg_right hle (mul_nonneg hWsq hGnn)
          _ = (2 * 10 ^ 12 * (1 + max CB 1)) * (Work.Spaces.WlInf α 5 f) ^ 2
                * GmajW5 α g z θ := by ring

end Work.FTS.StrongEps.H5.WProd5
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.HonestEasyMajorAsmA =====
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

/-! ## Open-class twins of the two continuity lemmas used below -/

/-- Continuity of the `i`-th pure `D_z`-slot on the open quadrant, in the open class
(`Work.H2.T1Q.continuousOn_dzIter_qd` with `SmoothQuad` replaced by `SmoothOpen`; the domain
`quadQ = Ioi 0 ×ˢ Ioo 0 (π/2)` is exactly `SmoothOpen`'s domain). -/
theorem continuousOn_dzIter_qd_open (u : ℝ → ℝ → ℝ) (hu : Work.FTS.EllipticEst.SmoothOpen u)
    (i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i u p.1 p.2) Work.FTS.H2.HQ.quadQ :=
  (hu.DzIter i).continuousOn

/-- Continuity of the `(j,i)`-th mixed slot on the open quadrant, in the open class. -/
theorem continuousOn_mixed_qd_open (u : ℝ → ℝ → ℝ) (hu : Work.FTS.EllipticEst.SmoothOpen u)
    (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i u p.1 p.2) Work.FTS.H2.HQ.quadQ :=
  (hu.mixed j i).continuousOn


set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.FTS.H2

/-! ## The `2`-dimensional assembly of the interior `T1Easy` estimate

This file assembles the interior (`SmoothQuad`) version of the pointwise majorant bound of
`Submission/Work/FTS/H2/T1EasyBound.lean` (`EMS_int_and_le`), replacing

* the closed-quadrant slot bounds `xDKf_bound`/`xDKg_bound`/`yMKf_bound`/`yMKg_bound` by
  bounds whose pointwise comparison is the *open-quadrant* `SlotPtQ` estimate
  (`xD_Kf_pt`, `xD_Kg_pt`, `yM_Kf_pt`, `yM_Kg_mixed_pt`) and whose integral is bounded by
  `Work.H2.T1Q.term_of_slot_open` (`slotIntBoundQ_o` below);
* the closed-quadrant `V`-bound of `term_of_slot` by the open-quadrant one;
* the exceptional summand `(i,j,a,b) = (1,3,0,3)` by `Work.H2.T1Q.ExcBoundOpen`. -/

/-! ## Almost-everywhere positivity of the radial variable -/

/-- Almost every point of the product measure `pm` has a positive radial coordinate: the
radial measure is `volume.restrict Iz`, and `{0}` is null for it. -/
theorem ae_pm_z_pos_o : ∀ᵐ p ∂Work.FTS.H2.pm, 0 < p.1 := by
  rw [Work.FTS.H2.pm, MeasureTheory.ae_iff]
  have hset : {p : ℝ × ℝ | ¬ (0 < p.1)} = Set.Iic (0 : ℝ) ×ˢ Set.univ := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_Iic, Set.mem_univ, and_true,
      Set.mem_setOf_eq, not_lt]
  rw [hset, MeasureTheory.Measure.prod_prod]
  have h0 : (MeasureTheory.volume.restrict Work.Spaces.Iz) (Set.Iic (0 : ℝ)) = 0 := by
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Iic]
    have hz : Set.Iic (0 : ℝ) ∩ Work.Spaces.Iz = {0} := by
      ext x
      simp only [Work.Spaces.Iz, Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ici,
        Set.mem_singleton_iff]
      constructor
      · intro h; exact le_antisymm h.1 h.2
      · intro h; simp [h]
    rw [hz]
    exact MeasureTheory.measure_singleton 0
  rw [h0, zero_mul]

/-! ## Measurability of the Leibniz summands -/

/-- A.e. strong measurability of the `D_z`-slot summand for `SmoothQuad` data. -/
theorem xD_aesm_q_o (f g : ℝ → ℝ → ℝ) (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (i b : ℕ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => xD f g i b p.1 p.2) Work.FTS.H2.pm := by
  have h1 := continuousOn_dzIter_qd_open f hf b
  have h2 := continuousOn_mixed_qd_open g hg (i - b) 1
  have h3 := continuousOn_dzIter_qd_open g hg i
  refine aesm_of_Qd ?_
  simp only [xD]
  exact continuousOn_const.mul (((h1.mul h2).mul h3).mul (continuousOn_Whz_quad.pow 2))

/-- A.e. strong measurability of the mixed-slot summand for `SmoothQuad` data. -/
theorem yM_aesm_q_o (α : ℝ) (f g : ℝ → ℝ → ℝ) (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (i j a b : ℕ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => yM α f g i j a b p.1 p.2) Work.FTS.H2.pm := by
  have h1 := continuousOn_mixed_qd_open f hf b a
  have h2 := continuousOn_mixed_qd_open g hg (j - b) (i - a + 1)
  have h3 := continuousOn_mixed_qd_open g hg j i
  refine aesm_of_Qd ?_
  simp only [yM]
  exact continuousOn_const.mul (((h1.mul h2).mul h3).mul ((continuousOn_Wm_quad α).pow 2))

/-! ## The generic slot pairing -/

/-- **Slot pairing with a bounded third factor.**  If `A`, `B` are nonnegative and their squares
are dominated by the `ℋ⁴`-integrands of `u`, `v`, and if `K ≥ 0`, then `K·(A·B)` is integrable
on `pm` with integral at most `K·|u|_{ℋ⁴}·|v|_{ℋ⁴}`.

This is `Work.H2.T1Q.term_of_slot_open` with the third factor `V` equal to the constant `K`
(so that `V`'s open-quadrant bound `|K| ≤ K` is `hK`). -/
theorem slotIntBoundQ_o (α : ℝ) (u v : ℝ → ℝ → ℝ) (hmu : Work.Spaces.HkMem α 4 u)
    (hmv : Work.Spaces.HkMem α 4 v) (A B : ℝ → ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hA0 : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ A z θ)
    (hB0 : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ B z θ)
    (hA : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (A z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 u z θ)
    (hB : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (B z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 v z θ)
    (hAcont : ContinuousOn (Function.uncurry A) Work.FTS.H2.Qd)
    (hBcont : ContinuousOn (Function.uncurry B) Work.FTS.H2.Qd)
    (hA0z : ∀ θ : ℝ, A 0 θ = 0) (hB0z : ∀ θ : ℝ, B 0 θ = 0) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => K * (A p.1 p.2 * B p.1 p.2))
        Work.FTS.H2.pm ∧
      ∫ p, K * (A p.1 p.2 * B p.1 p.2) ∂Work.FTS.H2.pm
        ≤ K * Work.Spaces.HkNorm α 4 u * Work.Spaces.HkNorm α 4 v := by
  have hAmeas : ∀ z ∈ Work.Spaces.Iz,
      AEStronglyMeasurable (fun θ => A z θ) (volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h | h
    · subst h
      exact aestronglyMeasurable_const.congr (Eventually.of_forall fun θ => (hA0z θ).symm)
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry A) hAcont h
  have hBmeas : ∀ z ∈ Work.Spaces.Iz,
      AEStronglyMeasurable (fun θ => B z θ) (volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h | h
    · subst h
      exact aestronglyMeasurable_const.congr (Eventually.of_forall fun θ => (hB0z θ).symm)
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry B) hBcont h
  have hVABmeas : AEStronglyMeasurable
      (Function.uncurry (fun z θ => |K * A z θ * B z θ|)) Work.FTS.H2.pm :=
    aesm_of_Qd (((continuousOn_const.mul hAcont).mul hBcont).abs)
  obtain ⟨hint, hbd⟩ := term_of_slot_open α u v hmu hmv A B (fun _ _ => K) K hK
    (fun z hz θ hθ => by simp [abs_of_nonneg hK]) hA0 hB0 hA hB hAmeas hBmeas hVABmeas
  have hae : (fun p : ℝ × ℝ => |K * A p.1 p.2 * B p.1 p.2|)
      =ᵐ[Work.FTS.H2.pm] (fun p : ℝ × ℝ => K * (A p.1 p.2 * B p.1 p.2)) := by
    filter_upwards [Work.FTS.H2.ae_pm_mem] with p hp
    rw [abs_of_nonneg
      (mul_nonneg (mul_nonneg hK (hA0 p.1 hp.1 p.2 hp.2)) (hB0 p.1 hp.1 p.2 hp.2))]
    ring
  exact ⟨hint.congr hae, by rw [← integral_congr_ae hae]; exact hbd⟩

/-! ## The four per-summand slot bounds -/

/-- The `D_z`-slot with an `f`-factor of order `≤ 2`: the `g`-factors are the two `ℋ⁴`-slots
and the `f`-factor is bounded by the constant `Kf`. -/
theorem xD_Kf_int_q_o (α : ℝ) (g : ℝ → ℝ → ℝ) (Kf : ℝ) (hKf0 : 0 ≤ Kf)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmemg : Work.Spaces.HkMem α 4 g)
    (i b : ℕ) (hi : i ≤ 4) (hib : i - b ≤ 3) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Kf *
        ((|Work.Spaces.mixed (i - b) 1 g p.1 p.2| * Wm α p.1 p.2)
          * (|Work.Spaces.DzIter i g p.1 p.2| * Whz p.1 p.2))) Work.FTS.H2.pm ∧
      ∫ p, Kf * ((|Work.Spaces.mixed (i - b) 1 g p.1 p.2| * Wm α p.1 p.2)
          * (|Work.Spaces.DzIter i g p.1 p.2| * Whz p.1 p.2)) ∂Work.FTS.H2.pm
        ≤ Kf * Work.Spaces.HkNorm α 4 g * Work.Spaces.HkNorm α 4 g :=
  slotIntBoundQ_o α g g hmemg hmemg
    (fun z θ => |Work.Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
    (fun z θ => |Work.Spaces.DzIter i g z θ| * Whz z θ) Kf hKf0
    (fun z hz θ hθ => mul_nonneg (abs_nonneg _) (Wm_nonneg α hθ))
    (fun z hz θ hθ => mul_nonneg (abs_nonneg _) (Whz_nonneg hθ))
    (fun z hz θ hθ => by
      simpa only [Wm, mul_pow, sq_abs] using
        Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ 1 (i - b) (le_refl 1) (by omega))
    (fun z hz θ hθ => by
      simpa only [Whz, mul_pow, sq_abs] using Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ i hi)
    ((continuousOn_mixed_qd_open g hg (i - b) 1).abs.mul (continuousOn_Wm_quad α))
    ((continuousOn_dzIter_qd_open g hg i).abs.mul continuousOn_Whz_quad)
    (fun θ => by rw [Wm, Work.Spaces.Wt, w_zero, zero_mul, mul_zero])
    (fun θ => by rw [Whz, w_zero, zero_div, mul_zero])

/-- The `D_z`-slot with the `g`-factor `D_z^{i-b}D_θg` of order `≤ 2` (i.e. `b ≥ 3`): the
`f`- and `g`-slots are the two `ℋ⁴`-slots and the remaining `g`-factor is bounded by `Kg`. -/
theorem xD_Kg_int_q_o (α : ℝ) (f g : ℝ → ℝ → ℝ) (Kg : ℝ) (hKg0 : 0 ≤ Kg)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmemf : Work.Spaces.HkMem α 4 f) (hmemg : Work.Spaces.HkMem α 4 g)
    (i b : ℕ) (hi : i ≤ 4) (hb3 : 3 ≤ b) (hbi : b ≤ i) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Kg *
        ((|Work.Spaces.DzIter b f p.1 p.2| * Whz p.1 p.2)
          * (|Work.Spaces.DzIter i g p.1 p.2| * Whz p.1 p.2))) Work.FTS.H2.pm ∧
      ∫ p, Kg * ((|Work.Spaces.DzIter b f p.1 p.2| * Whz p.1 p.2)
          * (|Work.Spaces.DzIter i g p.1 p.2| * Whz p.1 p.2)) ∂Work.FTS.H2.pm
        ≤ Kg * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g :=
  slotIntBoundQ_o α f g hmemf hmemg
    (fun z θ => |Work.Spaces.DzIter b f z θ| * Whz z θ)
    (fun z θ => |Work.Spaces.DzIter i g z θ| * Whz z θ) Kg hKg0
    (fun z hz θ hθ => mul_nonneg (abs_nonneg _) (Whz_nonneg hθ))
    (fun z hz θ hθ => mul_nonneg (abs_nonneg _) (Whz_nonneg hθ))
    (fun z hz θ hθ => by
      simpa only [Whz, mul_pow, sq_abs] using Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ b
        (by omega))
    (fun z hz θ hθ => by
      simpa only [Whz, mul_pow, sq_abs] using Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ i hi)
    ((continuousOn_dzIter_qd_open f hf b).abs.mul continuousOn_Whz_quad)
    ((continuousOn_dzIter_qd_open g hg i).abs.mul continuousOn_Whz_quad)
    (fun θ => by rw [Whz, w_zero, zero_div, mul_zero])
    (fun θ => by rw [Whz, w_zero, zero_div, mul_zero])

/-- The mixed slot with an `f`-factor of order `≤ 2`: the two `g`-factors are the `ℋ⁴`-slots
and the `f`-factor is bounded by `Kf`. -/
theorem yM_Kf_int_q_o (α : ℝ) (g : ℝ → ℝ → ℝ) (Kf : ℝ) (hKf0 : 0 ≤ Kf)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmemg : Work.Spaces.HkMem α 4 g)
    (i j a b : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) (hai : a ≤ i) (hbj : b ≤ j)
    (hnh : ¬(a = 0 ∧ b = 0 ∧ i + j = 4)) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Kf *
        ((|Work.Spaces.mixed (j - b) (i - a + 1) g p.1 p.2| * Wm α p.1 p.2)
          * (|Work.Spaces.mixed j i g p.1 p.2| * Wm α p.1 p.2))) Work.FTS.H2.pm ∧
      ∫ p, Kf * ((|Work.Spaces.mixed (j - b) (i - a + 1) g p.1 p.2| * Wm α p.1 p.2)
          * (|Work.Spaces.mixed j i g p.1 p.2| * Wm α p.1 p.2)) ∂Work.FTS.H2.pm
        ≤ Kf * Work.Spaces.HkNorm α 4 g * Work.Spaces.HkNorm α 4 g := by
  have hord : (i - a + 1) + (j - b) ≤ 4 := by
    by_cases hab0 : a + b = 0
    · have ha0 : a = 0 := by omega
      have hb0 : b = 0 := by omega
      have hij3 : i + j ≤ 3 := by
        by_contra hcon
        exact hnh ⟨ha0, hb0, by omega⟩
      omega
    · omega
  exact slotIntBoundQ_o α g g hmemg hmemg
    (fun z θ => |Work.Spaces.mixed (j - b) (i - a + 1) g z θ| * Wm α z θ)
    (fun z θ => |Work.Spaces.mixed j i g z θ| * Wm α z θ) Kf hKf0
    (fun z hz θ hθ => mul_nonneg (abs_nonneg _) (Wm_nonneg α hθ))
    (fun z hz θ hθ => mul_nonneg (abs_nonneg _) (Wm_nonneg α hθ))
    (fun z hz θ hθ => by
      simpa only [Wm, mul_pow, sq_abs] using
        Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ (i - a + 1) (j - b) (by omega) hord)
    (fun z hz θ hθ => by
      simpa only [Wm, mul_pow, sq_abs] using
        Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ i j hi hij)
    ((continuousOn_mixed_qd_open g hg (j - b) (i - a + 1)).abs.mul (continuousOn_Wm_quad α))
    ((continuousOn_mixed_qd_open g hg j i).abs.mul (continuousOn_Wm_quad α))
    (fun θ => by rw [Wm, Work.Spaces.Wt, w_zero, zero_mul, mul_zero])
    (fun θ => by rw [Wm, Work.Spaces.Wt, w_zero, zero_mul, mul_zero])

/-- The mixed slot whose `g`-factor `D_z^{j-b}D_θ^{i-a+1}g` has `θ`-order `≥ 1` and total order
`≤ 2`: the `f`- and `g`-slots are the two `ℋ⁴`-slots and the remaining `g`-factor is bounded
by `Kg`. -/
theorem yM_Kg_int_q_o (α : ℝ) (f g : ℝ → ℝ → ℝ) (Kg : ℝ) (hKg0 : 0 ≤ Kg)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmemf : Work.Spaces.HkMem α 4 f) (hmemg : Work.Spaces.HkMem α 4 g)
    (i j a b : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) (hai : a ≤ i) (hbj : b ≤ j)
    (ha1 : 1 ≤ a) (hab3 : 3 ≤ a + b) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Kg *
        ((|Work.Spaces.mixed b a f p.1 p.2| * Wm α p.1 p.2)
          * (|Work.Spaces.mixed j i g p.1 p.2| * Wm α p.1 p.2))) Work.FTS.H2.pm ∧
      ∫ p, Kg * ((|Work.Spaces.mixed b a f p.1 p.2| * Wm α p.1 p.2)
          * (|Work.Spaces.mixed j i g p.1 p.2| * Wm α p.1 p.2)) ∂Work.FTS.H2.pm
        ≤ Kg * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g :=
  slotIntBoundQ_o α f g hmemf hmemg
    (fun z θ => |Work.Spaces.mixed b a f z θ| * Wm α z θ)
    (fun z θ => |Work.Spaces.mixed j i g z θ| * Wm α z θ) Kg hKg0
    (fun z hz θ hθ => mul_nonneg (abs_nonneg _) (Wm_nonneg α hθ))
    (fun z hz θ hθ => mul_nonneg (abs_nonneg _) (Wm_nonneg α hθ))
    (fun z hz θ hθ => by
      simpa only [Wm, mul_pow, sq_abs] using
        Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ a b ha1 (by omega))
    (fun z hz θ hθ => by
      simpa only [Wm, mul_pow, sq_abs] using
        Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ i j hi hij)
    ((continuousOn_mixed_qd_open f hf b a).abs.mul (continuousOn_Wm_quad α))
    ((continuousOn_mixed_qd_open g hg j i).abs.mul (continuousOn_Wm_quad α))
    (fun θ => by rw [Wm, Work.Spaces.Wt, w_zero, zero_mul, mul_zero])
    (fun θ => by rw [Wm, Work.Spaces.Wt, w_zero, zero_mul, mul_zero])


end Work.FTS.StrongPersist.N6Trans.HonestEasyMajorAux
end
end
