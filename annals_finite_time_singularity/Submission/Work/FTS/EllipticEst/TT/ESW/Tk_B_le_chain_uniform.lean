import Mathlib
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.EllipticEst.ZCuts.zHardy_compact
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.T2Qaux.SupAux
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.HkIntegrand_zfar_Fstar_le
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongPersist.N6.Swap6
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.WPQ.hardy_slice_Aang
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.H2W.PsiSlices.shiftedSourcePoleBound
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.HProductRule_Badsummand
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.continuousOn_HkIntegrand_Qd
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.thetaInterpCoreOfTraceVanishing =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit true
set_option maxHeartbeats 4000000

namespace Work.EllipticEst.Core.i0Aux

theorem thetaInterpCoreOfTraceVanishing
    (TV : ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ → ℝ,
      ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ C * ((∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
            + Real.sqrt ((∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
                * (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))))

    (htr : ∃ F₀ F₁ : ℝ,
      Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds F₀)
      ∧ Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds F₁)) :

    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ,
    ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
    f 0 = 0 → f (Real.pi / 2) = 0 →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ C * ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + Real.sqrt ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
              * (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))) := by
  obtain ⟨CTV, hCTVpos, hTV⟩ := TV
  obtain ⟨ψ, Cb, hbump⟩ := TVRed.bumpExists
  have hCbpos : 0 < Cb := hbump.C_pos
  have hψcd : ContDiff ℝ 2 ψ := hbump.contDiff
  set K1 : ℝ := 1000 * (Cb + 1) ^ 2 * 201 with hK1
  set K2 : ℝ := 1000 * (Cb + 1) ^ 2 * 3204 with hK2
  have hK1nn : 0 ≤ K1 := by rw [hK1]; positivity
  have hK2nn : 0 ≤ K2 := by rw [hK2]; positivity
  refine ⟨CTV * (2 + 2 * K1) + CTV * Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2))
    + 4 * Real.sqrt K2 + 1, by positivity, ?_⟩
  intro f hf hf0 hfpi hP hA hE
  obtain ⟨K0, hK0pos, hSL⟩ := Work.EllipticEst.Core.sliceBoundaryLimit
  have hf1 : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)) := hf.of_le (by norm_num)
  have hAoo : IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := tvc_integrableOn_Ioo_of_Iθ hA
  obtain ⟨hLft, hRgt⟩ := hSL f hf1 hAoo
  obtain ⟨F₀, hF₀t, -⟩ := hLft
  obtain ⟨F₁, hF₁t, -⟩ := hRgt
  have hPoo : IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := tvc_integrableOn_Ioo_of_Iθ hP
  have hEoo : IntegrableOn
      (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := tvc_integrableOn_Ioo_of_Iθ hE
  have hPoo_eq : (∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      = ∫ x in Work.Spaces.Iθ, (f x) ^ 2 * Work.FTS.EllipticEst.thEta x :=
    (tvc_setIntegral_Iθ_eq_Ioo _).symm
  have hEoo_eq : (∫ x in Set.Ioo 0 (Real.pi / 2),
        (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      = ∫ x in Work.Spaces.Iθ, (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x :=
    (tvc_setIntegral_Iθ_eq_Ioo _).symm
  by_cases hP0 : (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) = 0
  · -- ### degenerate case: the two traces vanish, so `TV` applies to `f` itself
    have hF₀0 : F₀ = 0 := by
      have hbd : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          F₀ ^ 2 ≤ 2 * t ^ (3 + Work.Spaces.eta)
            * (∫ x in Set.Ioo 0 (Real.pi / 2),
                (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x) := by
        intro t ht
        have h := TVRed.endpointParamLeftW f F₀ t ht.1 ht.2 hf hF₀t hEoo hPoo
        have hz : (∫ x in Set.Ioo 0 (Real.pi / 2),
            (f x) ^ 2 * Work.FTS.EllipticEst.thEta x) = 0 := by
          rw [hPoo_eq]; exact hP0
        rw [hz, mul_zero, add_zero] at h
        exact h
      have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          F₀ ^ 2 ≤ 2 * t ^ (3 + Work.Spaces.eta)
            * (∫ x in Set.Ioo 0 (Real.pi / 2),
                (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x) := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds
            (isOpen_Iio.mem_nhds (by rw [Set.mem_Iio]; exact half_pos Real.pi_pos)), self_mem_nhdsWithin]
          with t ht hpos
        exact hbd t ⟨hpos, ht⟩
      have htend : Tendsto (fun t : ℝ => 2 * t ^ (3 + Work.Spaces.eta)
            * (∫ x in Set.Ioo 0 (Real.pi / 2),
                (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
        have h1 : Tendsto (fun t : ℝ => t ^ (3 + Work.Spaces.eta))
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
          Work.FTS.EllipticEst.AngAWeak.tendsto_rpow_nhdsGT_zero
            (by rw [Work.Spaces.eta]; norm_num)
        simpa using ((h1.const_mul 2).mul_const _)
      have hle : F₀ ^ 2 ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds htend hev
      exact (sq_eq_zero_iff).mp (le_antisymm hle (sq_nonneg F₀))
    have hF₁0 : F₁ = 0 := by
      have hbd : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          F₁ ^ 2 ≤ 2 * t ^ (3 + Work.Spaces.eta)
            * (∫ x in Set.Ioo 0 (Real.pi / 2),
                (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x) := by
        intro t ht
        have h := TVRed.endpointParamRightW f F₁ t ht.1 ht.2 hf hF₁t hEoo hPoo
        have hz : (∫ x in Set.Ioo 0 (Real.pi / 2),
            (f x) ^ 2 * Work.FTS.EllipticEst.thEta x) = 0 := by
          rw [hPoo_eq]; exact hP0
        rw [hz, mul_zero, add_zero] at h
        exact h
      have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          F₁ ^ 2 ≤ 2 * t ^ (3 + Work.Spaces.eta)
            * (∫ x in Set.Ioo 0 (Real.pi / 2),
                (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x) := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds
            (isOpen_Iio.mem_nhds (by rw [Set.mem_Iio]; exact half_pos Real.pi_pos)), self_mem_nhdsWithin]
          with t ht hpos
        exact hbd t ⟨hpos, ht⟩
      have htend : Tendsto (fun t : ℝ => 2 * t ^ (3 + Work.Spaces.eta)
            * (∫ x in Set.Ioo 0 (Real.pi / 2),
                (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
        have h1 : Tendsto (fun t : ℝ => t ^ (3 + Work.Spaces.eta))
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
          Work.FTS.EllipticEst.AngAWeak.tendsto_rpow_nhdsGT_zero
            (by rw [Work.Spaces.eta]; norm_num)
        simpa using ((h1.const_mul 2).mul_const _)
      have hle : F₁ ^ 2 ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds htend hev
      exact (sq_eq_zero_iff).mp (le_antisymm hle (sq_nonneg F₁))
    have ht0 : Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have h := hF₀t; rw [hF₀0] at h; exact h
    have ht1 : Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have h := hF₁t; rw [hF₁0] at h; exact h
    have hTVf := hTV f hf ht0 ht1 hP hA hE
    have hsum0 : (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + Real.sqrt ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
            * (∫ θ in Work.Spaces.Iθ,
                (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)) = 0 := by
      rw [hP0, zero_mul, Real.sqrt_zero, add_zero]
    have hTVf' : (∫ θ in Work.Spaces.Iθ,
        (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) ≤ 0 := by
      have h2 : CTV * ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + Real.sqrt ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
              * (∫ θ in Work.Spaces.Iθ,
                  (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))) = 0 := by
        rw [hsum0, mul_zero]
      rw [h2] at hTVf
      exact hTVf
    rw [hsum0, mul_zero]
    exact hTVf'
  · -- ### main case
    have hPnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ))
    have hPpos : 0 < ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
      lt_of_le_of_ne hPnn (Ne.symm hP0)
    have hEnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
        (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ))
    set P : ℝ := ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ with hPdef
    set E : ℝ := ∫ θ in Work.Spaces.Iθ,
      (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ with hEdef
    set A : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ with hAdef
    have hPpos' : 0 < P := hPpos
    have hEnn' : 0 ≤ E := hEnn
    have hLpos : 0 < sScale P E := sScale_pos hPpos' hEnn'
    have hLhalf : sScale P E ≤ 1 / 2 := sScale_le_half hPpos' hEnn'
    have hLpi : sScale P E ≤ Real.pi / 4 := by nlinarith [hLhalf, Real.pi_gt_three]
    have hLlt : sScale P E < Real.pi / 2 := by nlinarith [hLhalf, Real.pi_gt_three]
    have hF0b : F₀ ^ 2 ≤ 2 * (sScale P E) ^ (3 + Work.Spaces.eta) * E
        + 100 * (sScale P E) ^ (Work.Spaces.eta - 1) * P := by
      have h := TVRed.endpointParamLeftW f F₀ (sScale P E) hLpos hLlt hf hF₀t hEoo hPoo
      have hJE : (∫ x in Set.Ioo 0 (Real.pi / 2),
          (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x) = E :=
        hEoo_eq.trans hEdef.symm
      have hXP : (∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 * Work.FTS.EllipticEst.thEta x) = P :=
        hPoo_eq.trans hPdef.symm
      rwa [hJE, hXP] at h
    have hF1b : F₁ ^ 2 ≤ 2 * (sScale P E) ^ (3 + Work.Spaces.eta) * E
        + 100 * (sScale P E) ^ (Work.Spaces.eta - 1) * P := by
      have h := TVRed.endpointParamRightW f F₁ (sScale P E) hLpos hLlt hf hF₁t hEoo hPoo
      have hJE : (∫ x in Set.Ioo 0 (Real.pi / 2),
          (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x) = E :=
        hEoo_eq.trans hEdef.symm
      have hXP : (∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 * Work.FTS.EllipticEst.thEta x) = P :=
        hPoo_eq.trans hPdef.symm
      rwa [hJE, hXP] at h
    have hSb : F₀ ^ 2 + F₁ ^ 2 ≤ 4 * (sScale P E) ^ (3 + Work.Spaces.eta) * E
        + 200 * (sScale P E) ^ (Work.Spaces.eta - 1) * P := by linarith
    obtain ⟨hArith1, hArith2⟩ := TVRed.sScaleBounds hPpos' hEnn' hCbpos hSb
    obtain ⟨hX1b, hX2b, hX3b, hX4b⟩ :=
      TVRed.surrIntegrals (ψ := ψ) (C := Cb) (F₀ := F₀) (F₁ := F₁) (L := sScale P E)
        hbump hLpos hLpi
    have hN1 : (∫ θ in Work.Spaces.Iθ, (surrFun ψ F₀ F₁ (sScale P E) θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) ≤ K1 * P := by
      have h1 : 1000 * (Cb + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2)
          * (sScale P E) ^ (1 - Work.Spaces.eta) ≤ K1 * P := by
        rw [hK1]; exact hArith1
      exact le_trans hX1b h1
    have hN2 : (∫ θ in Work.Spaces.Iθ,
        (deriv (deriv (surrFun ψ F₀ F₁ (sScale P E))) θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) ≤ K2 * (P + E) := by
      have h1 : 1000 * (Cb + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2)
          * (sScale P E) ^ (-(3 + Work.Spaces.eta)) ≤ K2 * (P + E) := by
        rw [hK2]; exact hArith2
      exact le_trans hX3b h1
    have hN3 : (∫ θ in Work.Spaces.Iθ, (deriv (surrFun ψ F₀ F₁ (sScale P E)) θ) ^ 2
        * (qTh θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) ≤ K2 * (P + E) := by
      have h1 : 1000 * (Cb + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2)
          * (sScale P E) ^ (-(3 + Work.Spaces.eta)) ≤ K2 * (P + E) := by
        rw [hK2]; exact hArith2
      exact le_trans hX4b h1
    obtain ⟨hℓ2int, hℓ1int, hℓ2int', hℓq2int⟩ :=
      TVRed.tvh_surr_integrable4 (ψ := ψ) (C := Cb) (F₀ := F₀) (F₁ := F₁) (L := sScale P E)
        hbump hLpos hLpi
    obtain ⟨hgC2, hglim0, hglim1, hgPint, hgAint, hgEint⟩ :=
      TVRed.tvHypBundle (ψ := ψ) (C := Cb) (F₀ := F₀) (F₁ := F₁) (L := sScale P E)
        hbump hLpos hLpi hf hF₀t hF₁t hP hA hE
    have hℓq2int' : IntegrableOn
        (fun θ : ℝ => (deriv (surrFun ψ F₀ F₁ (sScale P E)) θ * qTh θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
      refine hℓq2int.congr ?_
      filter_upwards with θ
      ring
    have hG1b : (∫ θ in Work.Spaces.Iθ,
        (f θ - surrFun ψ F₀ F₁ (sScale P E) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ (2 + 2 * K1) * P := by
      have h := tvc_g1_bound (F₀ := F₀) (F₁ := F₁) (L := sScale P E) (ne_of_gt hLpos)
        hψcd hP hℓ2int hgPint
      have h2 : 2 * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, (surrFun ψ F₀ F₁ (sScale P E) θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ) ≤ (2 + 2 * K1) * P := by
        rw [← hPdef]
        linarith [hN1]
      linarith
    have hG2b : (∫ θ in Work.Spaces.Iθ,
        (deriv (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ (sScale P E) θ)) θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) ≤ (2 + 2 * K2) * (P + E) := by
      have h := tvc_g2_bound (F₀ := F₀) (F₁ := F₁) (L := sScale P E) (ne_of_gt hLpos)
        hψcd hf hE hℓ2int' hgEint
      have h2 : 2 * (∫ θ in Work.Spaces.Iθ,
            (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + 2 * (∫ θ in Work.Spaces.Iθ,
              (deriv (deriv (surrFun ψ F₀ F₁ (sScale P E))) θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ) ≤ (2 + 2 * K2) * (P + E) := by
        rw [← hEdef]
        linarith [hN2]
      linarith
    have hTVg := hTV (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ (sScale P E) θ)
      hgC2 hglim0 hglim1 hgPint hgAint hgEint
    have hibp := TVRed.ibpSurr (ψ := ψ) (C := Cb) (F₀ := F₀) (F₁ := F₁)
      (L := sScale P E) hbump hLpos hLpi hf
    set X2 : ℝ := ∫ θ in Work.Spaces.Iθ,
      (deriv (deriv (surrFun ψ F₀ F₁ (sScale P E))) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
      with hX2def
    set X3 : ℝ := ∫ θ in Work.Spaces.Iθ,
      (deriv (surrFun ψ F₀ F₁ (sScale P E)) θ * qTh θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ with hX3def
    set Y : ℝ := ∫ θ in Work.Spaces.Iθ, deriv f θ * deriv (surrFun ψ F₀ F₁ (sScale P E)) θ
      * Work.FTS.EllipticEst.thEta θ with hYdef
    have hX2le : X2 ≤ K2 * (P + E) := by rw [hX2def]; exact hN2
    have hX3eq : X3 = ∫ θ in Work.Spaces.Iθ,
        (deriv (surrFun ψ F₀ F₁ (sScale P E)) θ) ^ 2 * (qTh θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ := by
      rw [hX3def]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
      ring
    have hX3le : X3 ≤ K2 * (P + E) := by rw [hX3eq]; exact hN3
    have hX2nn : 0 ≤ X2 := by
      rw [hX2def]
      exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ))
    have hX3nn : 0 ≤ X3 := by
      rw [hX3def]
      exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ))
    -- Cauchy-Schwarz for the two IBP terms
    have hcs1 := TVRed.csThEta (g := f)
      (h := fun θ : ℝ => deriv (deriv (surrFun ψ F₀ F₁ (sScale P E))) θ) hP hℓ2int'
    have hcs2 := TVRed.csThEta (g := f)
      (h := fun θ : ℝ => deriv (surrFun ψ F₀ F₁ (sScale P E)) θ * qTh θ) hP hℓq2int'
    have hZ1 : |∫ θ in Work.Spaces.Iθ,
        f θ * deriv (deriv (surrFun ψ F₀ F₁ (sScale P E))) θ
          * Work.FTS.EllipticEst.thEta θ| ≤ Real.sqrt (P * X2) := by
      refine tvc_abs_le_sqrt (mul_nonneg hPpos'.le hX2nn) ?_
      have h := hcs1
      rw [← hPdef, ← hX2def] at h
      exact h
    have hZ2' : |∫ θ in Work.Spaces.Iθ,
        f θ * (deriv (surrFun ψ F₀ F₁ (sScale P E)) θ * qTh θ)
          * Work.FTS.EllipticEst.thEta θ| ≤ Real.sqrt (P * X3) := by
      refine tvc_abs_le_sqrt (mul_nonneg hPpos'.le hX3nn) ?_
      have h := hcs2
      rw [← hPdef, ← hX3def] at h
      exact h
    have hZ2 : |∫ θ in Work.Spaces.Iθ,
        f θ * deriv (surrFun ψ F₀ F₁ (sScale P E)) θ * qTh θ
          * Work.FTS.EllipticEst.thEta θ| ≤ Real.sqrt (P * X3) := by
      rw [show (∫ θ in Work.Spaces.Iθ, f θ * deriv (surrFun ψ F₀ F₁ (sScale P E)) θ
            * qTh θ * Work.FTS.EllipticEst.thEta θ)
          = (∫ θ in Work.Spaces.Iθ, f θ * (deriv (surrFun ψ F₀ F₁ (sScale P E)) θ * qTh θ)
              * Work.FTS.EllipticEst.thEta θ) from ?_]
      · exact hZ2'
      · refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
        ring
    have hYle : Y ≤ Real.sqrt (P * X2) + Real.sqrt (P * X3) := by
      have h := hibp
      rw [hYdef]
      calc (∫ θ in Work.Spaces.Iθ, deriv f θ * deriv (surrFun ψ F₀ F₁ (sScale P E)) θ
            * Work.FTS.EllipticEst.thEta θ)
          = - (∫ θ in Work.Spaces.Iθ,
                f θ * deriv (deriv (surrFun ψ F₀ F₁ (sScale P E))) θ
                  * Work.FTS.EllipticEst.thEta θ)
            + (∫ θ in Work.Spaces.Iθ,
                f θ * deriv (surrFun ψ F₀ F₁ (sScale P E)) θ * qTh θ
                  * Work.FTS.EllipticEst.thEta θ) := h
        _ ≤ |∫ θ in Work.Spaces.Iθ,
                f θ * deriv (deriv (surrFun ψ F₀ F₁ (sScale P E))) θ
                  * Work.FTS.EllipticEst.thEta θ|
              + |∫ θ in Work.Spaces.Iθ,
                f θ * deriv (surrFun ψ F₀ F₁ (sScale P E)) θ * qTh θ
                  * Work.FTS.EllipticEst.thEta θ| := by
            have h1 := neg_le_abs (∫ θ in Work.Spaces.Iθ,
              f θ * deriv (deriv (surrFun ψ F₀ F₁ (sScale P E))) θ
                * Work.FTS.EllipticEst.thEta θ)
            have h2 := le_abs_self (∫ θ in Work.Spaces.Iθ,
              f θ * deriv (surrFun ψ F₀ F₁ (sScale P E)) θ * qTh θ
                * Work.FTS.EllipticEst.thEta θ)
            linarith
        _ ≤ Real.sqrt (P * X2) + Real.sqrt (P * X3) := add_le_add hZ1 hZ2
    -- the exponential-scale comparison
    have hsq1 : Real.sqrt (P * X2) ≤ Real.sqrt K2 * (P + Real.sqrt (P * E)) := by
      have h1 : P * X2 ≤ K2 * (P * (P + E)) := by
        have h3 : P * X2 ≤ P * (K2 * (P + E)) := mul_le_mul_of_nonneg_left hX2le hPpos'.le
        linarith
      calc Real.sqrt (P * X2) ≤ Real.sqrt (K2 * (P * (P + E))) := Real.sqrt_le_sqrt h1
        _ = Real.sqrt K2 * Real.sqrt (P * (P + E)) := by
            rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ K2)]
        _ ≤ Real.sqrt K2 * (P + Real.sqrt (P * E)) :=
            mul_le_mul_of_nonneg_left (tvc_sqrt_mul_le hPpos'.le hEnn') (Real.sqrt_nonneg _)
    have hsq2 : Real.sqrt (P * X3) ≤ Real.sqrt K2 * (P + Real.sqrt (P * E)) := by
      have h1 : P * X3 ≤ K2 * (P * (P + E)) := by
        have h3 : P * X3 ≤ P * (K2 * (P + E)) := mul_le_mul_of_nonneg_left hX3le hPpos'.le
        linarith
      calc Real.sqrt (P * X3) ≤ Real.sqrt (K2 * (P * (P + E))) := Real.sqrt_le_sqrt h1
        _ = Real.sqrt K2 * Real.sqrt (P * (P + E)) := by
            rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ K2)]
        _ ≤ Real.sqrt K2 * (P + Real.sqrt (P * E)) :=
            mul_le_mul_of_nonneg_left (tvc_sqrt_mul_le hPpos'.le hEnn') (Real.sqrt_nonneg _)
    -- the TV bound on `g`
    have hG1nn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
        (f θ - surrFun ψ F₀ F₁ (sScale P E) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ))
    have hG2nn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
        (deriv (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ (sScale P E) θ)) θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ))
    have hGprod : Real.sqrt ((∫ θ in Work.Spaces.Iθ,
          (f θ - surrFun ψ F₀ F₁ (sScale P E) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        * (∫ θ in Work.Spaces.Iθ,
          (deriv (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ (sScale P E) θ)) θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ))
        ≤ Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2)) * (P + Real.sqrt (P * E)) := by
      have h1 : (∫ θ in Work.Spaces.Iθ,
            (f θ - surrFun ψ F₀ F₁ (sScale P E) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          * (∫ θ in Work.Spaces.Iθ,
            (deriv (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ (sScale P E) θ)) θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ)
          ≤ ((2 + 2 * K1) * (2 + 2 * K2)) * (P * (P + E)) := by
        have h4 : (∫ θ in Work.Spaces.Iθ,
              (f θ - surrFun ψ F₀ F₁ (sScale P E) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
            * (∫ θ in Work.Spaces.Iθ,
              (deriv (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ (sScale P E) θ)) θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ)
            ≤ ((2 + 2 * K1) * P) * ((2 + 2 * K2) * (P + E)) :=
          mul_le_mul hG1b hG2b hG2nn (by nlinarith [hPpos'.le, hK1nn, hK1])
        linarith [h4]
      calc Real.sqrt ((∫ θ in Work.Spaces.Iθ,
              (f θ - surrFun ψ F₀ F₁ (sScale P E) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
            * (∫ θ in Work.Spaces.Iθ,
              (deriv (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ (sScale P E) θ)) θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ))
          ≤ Real.sqrt (((2 + 2 * K1) * (2 + 2 * K2)) * (P * (P + E))) := Real.sqrt_le_sqrt h1
        _ = Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2)) * Real.sqrt (P * (P + E)) := by
            rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ (2 + 2 * K1) * (2 + 2 * K2))]
        _ ≤ Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2)) * (P + Real.sqrt (P * E)) :=
            mul_le_mul_of_nonneg_left (tvc_sqrt_mul_le hPpos'.le hEnn') (Real.sqrt_nonneg _)
    -- assemble
    have hTVg' : (∫ θ in Work.Spaces.Iθ,
          (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ (sScale P E) θ) θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ)
        ≤ CTV * ((2 + 2 * K1) * P
            + Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2)) * (P + Real.sqrt (P * E))) := by
      refine le_trans hTVg ?_
      have h2 : (∫ θ in Work.Spaces.Iθ,
            (f θ - surrFun ψ F₀ F₁ (sScale P E) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          ≤ (2 + 2 * K1) * P := hG1b
      have h3 : (∫ θ in Work.Spaces.Iθ,
            (f θ - surrFun ψ F₀ F₁ (sScale P E) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + Real.sqrt ((∫ θ in Work.Spaces.Iθ,
              (f θ - surrFun ψ F₀ F₁ (sScale P E) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
            * (∫ θ in Work.Spaces.Iθ,
              (deriv (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ (sScale P E) θ)) θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ))
          ≤ (2 + 2 * K1) * P
            + Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2)) * (P + Real.sqrt (P * E)) := by
        linarith [h2, hGprod]
      exact mul_le_mul_of_nonneg_left h3 hCTVpos.le
    -- the `A ≤ A(g) + 2Y` relation
    have hcross : IntegrableOn (fun θ : ℝ =>
        deriv f θ * deriv (surrFun ψ F₀ F₁ (sScale P E)) θ
          * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
      tvc_integrableOn_cross (ψ := ψ) (F₀ := F₀) (F₁ := F₁) (L := sScale P E) hψcd hA hℓ1int
    have hAg_eq : (∫ θ in Work.Spaces.Iθ,
          (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ (sScale P E) θ) θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ)
        = A - 2 * Y + (∫ θ in Work.Spaces.Iθ,
            (deriv (surrFun ψ F₀ F₁ (sScale P E)) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
      have h := tvc_derivg2_eq (F₀ := F₀) (F₁ := F₁) (L := sScale P E) (ne_of_gt hLpos)
        hψcd hf hA hℓ1int hcross
      rw [hAdef, hYdef]
      exact h
    have hArel : A ≤ (∫ θ in Work.Spaces.Iθ,
          (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ (sScale P E) θ) θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ) + 2 * Y := by
      have hℓ1nn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
          (deriv (surrFun ψ F₀ F₁ (sScale P E)) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
        MeasureTheory.setIntegral_nonneg measurableSet_Icc
          (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ))
      linarith [hAg_eq, hℓ1nn]
    -- final assembly
    have hYbound : Y ≤ 2 * Real.sqrt K2 * (P + Real.sqrt (P * E)) := by
      linarith [hYle, hsq1, hsq2]
    have hmain : A ≤ (CTV * (2 + 2 * K1) + CTV * Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2))
        + 4 * Real.sqrt K2 + 1) * (P + Real.sqrt (P * E)) := by
      have h1 : A ≤ CTV * ((2 + 2 * K1) * P
          + Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2)) * (P + Real.sqrt (P * E)))
          + 2 * (2 * Real.sqrt K2 * (P + Real.sqrt (P * E))) := by
        linarith [hArel, hTVg', hYbound]
      have h2 : CTV * ((2 + 2 * K1) * P
          + Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2)) * (P + Real.sqrt (P * E)))
          + 2 * (2 * Real.sqrt K2 * (P + Real.sqrt (P * E)))
          ≤ (CTV * (2 + 2 * K1) + CTV * Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2))
            + 4 * Real.sqrt K2 + 1) * (P + Real.sqrt (P * E)) := by
        have h4 : 0 ≤ P + Real.sqrt (P * E) :=
          add_nonneg hPpos'.le (Real.sqrt_nonneg _)
        have h5 : CTV * ((2 + 2 * K1) * P
              + Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2)) * (P + Real.sqrt (P * E)))
            + 2 * (2 * Real.sqrt K2 * (P + Real.sqrt (P * E)))
            ≤ (CTV * (2 + 2 * K1) + CTV * Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2))
              + 4 * Real.sqrt K2) * (P + Real.sqrt (P * E)) := by
          have hprod : 0 ≤ CTV * (2 + 2 * K1) * Real.sqrt (P * E) :=
            mul_nonneg (by positivity) (Real.sqrt_nonneg _)
          have hexp : (CTV * (2 + 2 * K1) + CTV * Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2))
                + 4 * Real.sqrt K2) * (P + Real.sqrt (P * E))
              = CTV * (2 + 2 * K1) * P + CTV * (2 + 2 * K1) * Real.sqrt (P * E)
                + CTV * Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2)) * P
                + CTV * Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2)) * Real.sqrt (P * E)
                + 4 * Real.sqrt K2 * P + 4 * Real.sqrt K2 * Real.sqrt (P * E) := by ring
          rw [hexp]
          linarith [hprod]
        calc CTV * ((2 + 2 * K1) * P
              + Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2)) * (P + Real.sqrt (P * E)))
            + 2 * (2 * Real.sqrt K2 * (P + Real.sqrt (P * E)))
            ≤ (CTV * (2 + 2 * K1) + CTV * Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2))
              + 4 * Real.sqrt K2) * (P + Real.sqrt (P * E)) := h5
          _ ≤ (CTV * (2 + 2 * K1) + CTV * Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2))
              + 4 * Real.sqrt K2 + 1) * (P + Real.sqrt (P * E)) := by
              nlinarith [h4]
      exact le_trans h1 h2
    rw [hAdef, hPdef, hEdef]
    exact hmain


end Work.EllipticEst.Core.i0Aux
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.Q0.RRTransport2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.InteriorRegularity.Q0

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Test functions obtained as natural multiples -/

theorem tsupport_nsmul_add_subset {f g : ℝ → ℝ → ℝ} (n : ℕ) :
    tsupport (Function.uncurry (fun z θ : ℝ => f z θ + n * g z θ))
      ⊆ tsupport (Function.uncurry f) ∪ tsupport (Function.uncurry g) := by
  have hfun : Function.uncurry (fun z θ : ℝ => f z θ + n * g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p + n * Function.uncurry g p := by
    funext p; rfl
  have hs : Function.support (fun p : ℝ × ℝ =>
        Function.uncurry f p + (n : ℝ) * Function.uncurry g p)
      ⊆ Function.support (Function.uncurry f) ∪ Function.support (Function.uncurry g) := by
    intro p hp
    rw [Function.mem_support] at hp
    by_contra hcon
    have h1 : Function.uncurry f p = 0 := by
      by_contra h
      exact hcon (Or.inl (by rwa [Function.mem_support]))
    have h2 : Function.uncurry g p = 0 := by
      by_contra h
      exact hcon (Or.inr (by rwa [Function.mem_support]))
    exact hp (by rw [h1, h2, mul_zero, add_zero])
  rw [hfun]
  exact subset_trans (closure_mono hs) (le_of_eq closure_union)

/-- The `C^∞`, compactly supported combination `f + n * g` of two test functions on `Q0`. -/
theorem test_nsmul_add {f g : ℝ → ℝ → ℝ} (n : ℕ)
    (hfsm : ∀ m : ℕ, ContDiff ℝ m (Function.uncurry f))
    (hfc : HasCompactSupport (Function.uncurry f))
    (hfQ : tsupport (Function.uncurry f) ⊆ Work.FTS.EllipticEst.Q0)
    (hgsm : ∀ m : ℕ, ContDiff ℝ m (Function.uncurry g))
    (hgc : HasCompactSupport (Function.uncurry g))
    (hgQ : tsupport (Function.uncurry g) ⊆ Work.FTS.EllipticEst.Q0) :
    (∀ m : ℕ, ContDiff ℝ m (Function.uncurry (fun z θ : ℝ => f z θ + n * g z θ))) ∧
    HasCompactSupport (Function.uncurry (fun z θ : ℝ => f z θ + n * g z θ)) ∧
    tsupport (Function.uncurry (fun z θ : ℝ => f z θ + n * g z θ))
      ⊆ Work.FTS.EllipticEst.Q0 := by
  have hfun : Function.uncurry (fun z θ : ℝ => f z θ + n * g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p + n * Function.uncurry g p := by
    funext p; rfl
  refine ⟨?_, ?_, ?_⟩
  · intro m
    rw [hfun]
    exact (hfsm m).add ((contDiff_const (c := (n : ℝ))).mul (hgsm m))
  · rw [hfun]
    exact hfc.add (hgc.mul_left (f := fun _ : ℝ × ℝ => ((n : ℕ) : ℝ)))
  · exact subset_trans (tsupport_nsmul_add_subset n) (union_subset hfQ hgQ)

/-! ## The two-point trick -/

/-- The weak identity tested against the combination `f + n * g`. -/
theorem hweak_nsmul {α : ℝ} {Ψ F : ℝ → ℝ → ℝ}
    (hweak : ∀ φ : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) →
      HasCompactSupport (Function.uncurry φ) →
      tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 →
      (∫ p in Work.FTS.EllipticEst.Q0, Lint α Ψ φ p)
        = ∫ p in Work.FTS.EllipticEst.Q0, Gint α F φ p)
    {f g : ℝ → ℝ → ℝ} (n : ℕ)
    (hfsm : ∀ m : ℕ, ContDiff ℝ m (Function.uncurry f))
    (hfc : HasCompactSupport (Function.uncurry f))
    (hfQ : tsupport (Function.uncurry f) ⊆ Work.FTS.EllipticEst.Q0)
    (hgsm : ∀ m : ℕ, ContDiff ℝ m (Function.uncurry g))
    (hgc : HasCompactSupport (Function.uncurry g))
    (hgQ : tsupport (Function.uncurry g) ⊆ Work.FTS.EllipticEst.Q0)
    (hfI : MeasureTheory.IntegrableOn (Lint α Ψ f) Work.FTS.EllipticEst.Q0)
    (hgI : MeasureTheory.IntegrableOn (Lint α Ψ g) Work.FTS.EllipticEst.Q0) :
    (∫ p in Work.FTS.EllipticEst.Q0, Gint α F (fun z θ : ℝ => f z θ + n * g z θ) p)
      = Lam α Ψ f + n * Lam α Ψ g := by
  obtain ⟨hνsm, hνc, hνQ⟩ := test_nsmul_add n hfsm hfc hfQ hgsm hgc hgQ
  have hhw := hweak (fun z θ : ℝ => f z θ + n * g z θ) hνsm hνc hνQ
  rw [← hhw]
  have hpoint : Set.EqOn (Lint α Ψ (fun z θ : ℝ => f z θ + n * g z θ))
      (fun p : ℝ × ℝ => Lint α Ψ f p + n * Lint α Ψ g p) Work.FTS.EllipticEst.Q0 :=
    Lint_nsmul_add α n (fun z θ _ => (hfsm 2).contDiffAt) (fun z θ _ => (hgsm 2).contDiffAt)
  have hQ0m : MeasurableSet Work.FTS.EllipticEst.Q0 := by
    rw [Q0_eq_prod]
    exact MeasurableSet.prod measurableSet_Ioi measurableSet_Ioo
  have hae : ∀ᵐ p ∂(MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)),
      p ∈ Work.FTS.EllipticEst.Q0 →
        Lint α Ψ (fun z θ : ℝ => f z θ + n * g z θ) p
          = Lint α Ψ f p + n * Lint α Ψ g p :=
    Filter.Eventually.of_forall (fun p hp => hpoint hp)
  rw [MeasureTheory.setIntegral_congr_ae hQ0m hae,
    MeasureTheory.integral_add hfI (hgI.const_mul n),
    MeasureTheory.integral_const_mul ((n : ℕ) : ℝ) (Lint α Ψ g), Lam_apply α Ψ f,
    Lam_apply α Ψ g]

/-- If `Ψ` is non-degenerate, then the source-side integrand is integrable. -/
theorem integrableOn_Gint_of_nondeg {α : ℝ} (hα : 0 < α) {F Ψ : ℝ → ℝ → ℝ}
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0)
    (hweak : ∀ φ : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) →
      HasCompactSupport (Function.uncurry φ) →
      tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 →
      (∫ p in Work.FTS.EllipticEst.Q0, Lint α Ψ φ p)
        = ∫ p in Work.FTS.EllipticEst.Q0, Gint α F φ p)
    (hnd : Nondeg α Ψ)
    {ψ φ : ℝ → ℝ → ℝ} (hψ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ))
    (hψc : HasCompactSupport (Function.uncurry ψ))
    (hψs : tsupport (Function.uncurry ψ) ⊆ stripRR)
    (hφsm : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφQ : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0)
    (hφval : ∀ z θ : ℝ, 0 < z → φ z θ = ψ ((1 / α) * Real.log z) θ)
    (hφbsl : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Elliptic.bslOp α φ z θ = kopDr ψ ((1 / α) * Real.log z) θ) :
    MeasureTheory.IntegrableOn (Gint α F φ) Work.FTS.EllipticEst.Q0 := by
  obtain ⟨η, hηsm, hηc, hηQ, hηne⟩ := hnd
  have hIntψ : MeasureTheory.Integrable (fun q : ℝ × ℝ => VRR α Ψ q.1 q.2 * kopDr ψ q.1 q.2) :=
    integrable_VRR_kopDr hα hΨ hψ hψc hψs
  have hφI : MeasureTheory.IntegrableOn (Lint α Ψ φ) Work.FTS.EllipticEst.Q0 :=
    integrableOn_qint_of_pullback hα hIntψ
      (fun q => (bsl_pullback_VRR hα hφQ hφbsl q).symm)
  have hηI : MeasureTheory.IntegrableOn (Lint α Ψ η) Work.FTS.EllipticEst.Q0 := by
    refine MeasureTheory.Integrable.of_integral_ne_zero ?_
    rwa [Lam_apply α Ψ η] at hηne
  by_cases h0 : Lam α Ψ φ = 0
  · -- use the multiples `1` and `2`
    have h1 : (∫ p in Work.FTS.EllipticEst.Q0,
          Gint α F (fun z θ : ℝ => φ z θ + ((1 : ℕ) : ℝ) * η z θ) p)
        = Lam α Ψ φ + ((1 : ℕ) : ℝ) * Lam α Ψ η :=
      hweak_nsmul hweak 1 hφsm hφc hφQ hηsm hηc hηQ hφI hηI
    have h2 : (∫ p in Work.FTS.EllipticEst.Q0,
          Gint α F (fun z θ : ℝ => φ z θ + ((2 : ℕ) : ℝ) * η z θ) p)
        = Lam α Ψ φ + ((2 : ℕ) : ℝ) * Lam α Ψ η :=
      hweak_nsmul hweak 2 hφsm hφc hφQ hηsm hηc hηQ hφI hηI
    have hI1 : MeasureTheory.IntegrableOn
        (Gint α F (fun z θ : ℝ => φ z θ + ((1 : ℕ) : ℝ) * η z θ))
        Work.FTS.EllipticEst.Q0 := by
      refine MeasureTheory.Integrable.of_integral_ne_zero ?_
      rw [h1, h0]
      simpa using hηne
    have hI2 : MeasureTheory.IntegrableOn
        (Gint α F (fun z θ : ℝ => φ z θ + ((2 : ℕ) : ℝ) * η z θ))
        Work.FTS.EllipticEst.Q0 := by
      refine MeasureTheory.Integrable.of_integral_ne_zero ?_
      rw [h2, h0]
      intro hcon
      have hcon' : (2 : ℝ) * Lam α Ψ η = 0 := by simpa using hcon
      exact hηne ((mul_eq_zero.mp hcon').resolve_left (by norm_num))
    have hsub : (fun p : ℝ × ℝ => Gint α F (fun z θ : ℝ => φ z θ + ((2 : ℕ) : ℝ) * η z θ) p
          - Gint α F (fun z θ : ℝ => φ z θ + ((1 : ℕ) : ℝ) * η z θ) p)
        = Gint α F η := by
      funext p
      simp only [Gint]
      push_cast
      ring
    have hηG : MeasureTheory.IntegrableOn (Gint α F η) Work.FTS.EllipticEst.Q0 := by
      rw [← hsub]
      exact hI2.sub hI1
    have hφG : (fun p : ℝ × ℝ => Gint α F (fun z θ : ℝ => φ z θ + ((1 : ℕ) : ℝ) * η z θ) p
          - Gint α F η p) = Gint α F φ := by
      funext p
      simp only [Gint]
      push_cast
      ring
    rw [← hφG]
    exact hI1.sub hηG
  · -- the functional does not vanish on `φ` itself
    have hG0 : (∫ p in Work.FTS.EllipticEst.Q0, Gint α F φ p) ≠ 0 := by
      rw [← hweak φ hφsm hφc hφQ]
      rwa [Lam_apply α Ψ φ] at h0
    exact MeasureTheory.Integrable.of_integral_ne_zero hG0

/-- The (real) transport of the weak formulation to the half-strip. -/
theorem transport_real {α : ℝ} (hα : 0 < α) {F Ψ : ℝ → ℝ → ℝ}
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0)
    (hweak : ∀ φ : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) →
      HasCompactSupport (Function.uncurry φ) →
      tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 →
      (∫ p in Work.FTS.EllipticEst.Q0, Lint α Ψ φ p)
        = ∫ p in Work.FTS.EllipticEst.Q0, Gint α F φ p)
    {τ : ℝ → ℝ → ℝ} (hτ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry τ))
    (hτc : HasCompactSupport (Function.uncurry τ))
    (hτs : tsupport (Function.uncurry τ) ⊆ stripRR)
    {φ : ℝ → ℝ → ℝ} (hφsm : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφQ : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0)
    (hφval : ∀ z θ : ℝ, 0 < z → φ z θ = τ ((1 / α) * Real.log z) θ)
    (hφbsl : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Elliptic.bslOp α φ z θ = kopDr τ ((1 / α) * Real.log z) θ) :
    (∫ q : ℝ × ℝ, VRR α Ψ q.1 q.2 * kopDr τ q.1 q.2)
      = ∫ q : ℝ × ℝ, GRR α F q.1 q.2 * τ q.1 q.2 := by
  have hchain := LHS_chain hα hΨ hτ hτc hτs hφQ hφbsl
  have hhweak : (∫ p in Work.FTS.EllipticEst.Q0,
        Ψ p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = ∫ p in Work.FTS.EllipticEst.Q0, Gint α F φ p :=
    hweak φ hφsm hφc hφQ
  by_cases hint : MeasureTheory.Integrable (fun q : ℝ × ℝ => GRR α F q.1 q.2 * τ q.1 q.2)
  · have hright : (∫ q : ℝ × ℝ, GRR α F q.1 q.2 * τ q.1 q.2)
        = ∫ p in Work.FTS.EllipticEst.Q0, Gint α F φ p :=
      RHS_chain hα hφval hφQ hint
    rw [hchain, hhweak, hright]
  · have hG : ¬ MeasureTheory.IntegrableOn (Gint α F φ) Work.FTS.EllipticEst.Q0 :=
      fun hcon => hint ((integrable_GRR_iff hα hφval hφQ).mpr hcon)
    have hL0 : (∫ p in Work.FTS.EllipticEst.Q0,
          Ψ p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) = 0 :=
      hhweak.trans (MeasureTheory.integral_undef hG)
    rw [hchain, hL0, MeasureTheory.integral_undef hint]

/-- In the degenerate case, the left-hand side functional vanishes identically. -/
theorem VRR_kopDr_eq_zero_of_not_nondeg {α : ℝ} (hα : 0 < α) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0)
    (hnd : ¬ Nondeg α Ψ) {τ : ℝ → ℝ → ℝ} (hτ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry τ))
    (hτc : HasCompactSupport (Function.uncurry τ))
    (hτs : tsupport (Function.uncurry τ) ⊆ stripRR)
    {φ : ℝ → ℝ → ℝ} (hφsm : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ))
    (hφc : HasCompactSupport (Function.uncurry φ))
    (hφQ : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0)
    (hφval : ∀ z θ : ℝ, 0 < z → φ z θ = τ ((1 / α) * Real.log z) θ)
    (hφbsl : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Elliptic.bslOp α φ z θ = kopDr τ ((1 / α) * Real.log z) θ) :
    (∫ q : ℝ × ℝ, VRR α Ψ q.1 q.2 * kopDr τ q.1 q.2) = 0 := by
  rw [LHS_chain hα hΨ hτ hτc hτs hφQ hφbsl]
  have h : Lam α Ψ φ = 0 := by
    by_contra hne
    exact hnd ⟨φ, hφsm, hφc, hφQ, hne⟩
  exact h

end Work.EllipticEst.InteriorRegularity.Q0
end
end
-- ===== merged: Submission.Work.FTS.Apriori.Limit.SlotCalc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.Apriori.Limit

set_option autoImplicit false

open Work.FTS.LocData (SmoothQuad)

/-! ## Elementary facts about the open quadrant -/

theorem mem_Qd_iff {p : ℝ × ℝ} :
    p ∈ Qd ↔ 0 < p.1 ∧ 0 < p.2 ∧ p.2 < π / 2 := by
  simp [Qd, Set.mem_Ioi, Set.mem_Ioo, and_assoc]

theorem Qd_subset_quadU : Qd ⊆ Work.Spaces.quadU := by
  intro p hp
  obtain ⟨h1, h2⟩ := mem_Qd_iff.mp hp
  show -1 < p.1 ∧ (0 < p.2 ∧ p.2 < π / 2)
  exact ⟨by linarith, h2⟩

theorem sin_two_pos_of_mem_Qd {p : ℝ × ℝ} (hp : p ∈ Qd) : 0 < Real.sin (2 * p.2) := by
  obtain ⟨-, h0, h1⟩ := mem_Qd_iff.mp hp
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])

/-! ## The slot weights -/

@[simp] theorem slotWeight_zero (α : ℝ) (j : ℕ) (z θ : ℝ) :
    slotWeight α (j, 0) z θ
      = Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
  simp [slotWeight]

@[simp] theorem slotWeight_succ (α : ℝ) (j i : ℕ) (z θ : ℝ) :
    slotWeight α (j, i + 1) z θ = Work.Spaces.Wt α z θ := by
  simp [slotWeight]

/-! ## Membership in `activeSlots` -/


/-! ## The slot decomposition of `HkIntegrand` -/


/-! ## Smoothness of the slot weights on the open quadrant -/

theorem contDiffOn_w_Qd :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Work.Spaces.w p.1) Qd := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
    funext p; rfl
  rw [hfun]
  exact ContDiffOn.div ((contDiffOn_const.add contDiffOn_fst).pow 2) (contDiffOn_fst.pow 2)
    (fun p hp => pow_ne_zero 2 (ne_of_gt (mem_Qd_iff.mp hp).1))

theorem contDiffOn_sin_rpow_Qd (c : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Qd := by
  have hsin : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Qd :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  exact hsin.rpow_const_of_ne (fun p hp => ne_of_gt (sin_two_pos_of_mem_Qd hp))


/-! ## Integrability helpers -/

/-- The product measure is the restriction of the planar Lebesgue measure to the closed
quadrant. -/
theorem Qμ_eq_restrict :
    Qμ = (volume.prod volume).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  rw [Qμ, Measure.prod_restrict]

/-- A function which is continuous on the open quadrant and vanishes outside a compact subset
of it is integrable with respect to `Qμ`. -/
theorem integrable_of_continuousOn_of_support {F : ℝ × ℝ → ℝ} (hF : ContinuousOn F Qd)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKQ : K ⊆ Qd) (hsupp : Function.support F ⊆ K) :
    Integrable F Qμ := by
  rw [← MeasureTheory.integrableOn_iff_integrable_of_support_subset hsupp]
  have hfin : Qμ K < ∞ := by
    rw [Qμ_eq_restrict, Measure.restrict_apply hK.measurableSet]
    exact lt_of_le_of_lt (measure_mono Set.inter_subset_left) hK.measure_lt_top
  have haesm : AEStronglyMeasurable F (Qμ.restrict K) :=
    (hF.mono hKQ).aestronglyMeasurable hK.measurableSet
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hF.mono hKQ)
  refine IntegrableOn.of_bound hfin haesm C ?_
  exact ae_restrict_of_forall_mem hK.measurableSet (fun x hx => hC x hx)

/-- The weighted slot `slot α ji f` is continuous on the open quadrant whenever `f` is smooth
there. -/
theorem continuousOn_slot {f : ℝ → ℝ → ℝ} (hf : SmoothQuad f) (α : ℝ) (ji : ℕ × ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => slot α ji f p.1 p.2) Qd := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed ji.1 ji.2 f p.1 p.2) Qd :=
    ((Work.FTS.LocData.contDiffOn_mixed Work.Spaces.isOpen_quadU hf ji.1 ji.2).continuousOn).mono
      Qd_subset_quadU
  have h2 : ContinuousOn (fun p : ℝ × ℝ => slotWeight α ji p.1 p.2) Qd := by
    by_cases hi : ji.2 = 0
    · have hfun : (fun p : ℝ × ℝ => slotWeight α ji p.1 p.2)
          = fun p : ℝ × ℝ => Work.Spaces.w p.1
              / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2) := by
        funext p; simp [slotWeight, hi]
      rw [hfun]
      exact contDiffOn_w_Qd.continuousOn.div (contDiffOn_sin_rpow_Qd _).continuousOn
        (fun p hp => ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_of_mem_Qd hp) _))
    · have hfun : (fun p : ℝ × ℝ => slotWeight α ji p.1 p.2)
          = fun p : ℝ × ℝ => Work.Spaces.w p.1
              * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
        funext p; simp [slotWeight, hi, Work.Spaces.Wt, Work.Spaces.wTheta]
      rw [hfun]
      exact contDiffOn_w_Qd.continuousOn.mul (contDiffOn_sin_rpow_Qd _).continuousOn
  have h3 : (fun p : ℝ × ℝ => slot α ji f p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.mixed ji.1 ji.2 f p.1 p.2 * slotWeight α ji p.1 p.2 := by
    funext p; rfl
  rw [h3]
  exact h1.mul h2


end Work.FTS.Apriori.Limit
end
end
-- ===== merged: Submission.Work.FTS.Apriori.Limit.exists_test_cutoff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Apriori.Limit

set_option autoImplicit false















end Work.FTS.Apriori.Limit
end
end
-- ===== merged: Submission.Work.FTS.Apriori.Limit.ofReal_HkSq_le_lintegral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.Apriori.Limit

set_option autoImplicit false

/-- **`ofReal` of a Bochner integral is bounded by the `lintegral` of `ofReal`.**  For a
nonnegative function on a measurable set the comparison holds unconditionally: if the function
is not integrable the Bochner integral is `0` (`MeasureTheory.integral_undef`), and
`0 ≤ ∫⁻ x in s, ofReal (F x)`. -/
theorem ofReal_setIntegral_le_lintegral {s : Set ℝ} (hs : MeasurableSet s) {F : ℝ → ℝ}
    (hF : ∀ x ∈ s, 0 ≤ F x) :
    ENNReal.ofReal (∫ x in s, F x) ≤ ∫⁻ x in s, ENNReal.ofReal (F x) := by
  by_cases h : Integrable F (volume.restrict s)
  · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal h
      (MeasureTheory.ae_restrict_of_forall_mem hs hF)]
  · rw [MeasureTheory.integral_undef h, ENNReal.ofReal_zero]
    exact bot_le


end Work.FTS.Apriori.Limit
end
end
-- ===== merged: Submission.Work.FTS.ClassC.PureVanishingReduction =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

/-- **The pointwise slot reduction.**  For `f` smooth on the open quadrant, the `ℋ^k`-integrand
is dominated by the sum of the pure radial level-`0` integrands and the `vanC`-weighted
vanishing-weight angular slots.  (This is the pointwise core of `HkMem_of_pure_and_vanishing`.) -/
theorem HkIntegrand_le_pure_vanishing {α : ℝ} (hα : 0 < α)
    (hγ : Work.Spaces.gam α ≤ 3 / 2) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (k : ℕ) (z θ : ℝ)
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k f z θ
      ≤ (∑ j ∈ Finset.range (k + 1), Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j f) z θ)
        + ∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.Icc 1 (k - j),
            (if h : 1 ≤ i then vanC α hα hγ f hsm i j h else 0)
              * ∑ r ∈ Finset.Icc 1 i, vig α f r j z θ := by
  have hGrp : ∀ j ∈ Finset.range (k + 1),
      Work.FTS.EllipticEst.sliceGroup α k j f z θ
        = Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j f) z θ
          + ∑ i ∈ Finset.Icc 1 (k - j),
              (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    intro j _
    rw [Work.FTS.EllipticEst.sliceGroup, HkIntegrand_zero_eq_classC]
  rw [Work.FTS.EllipticEst.HkIntegrand_eq_slice_sum,
    Finset.sum_congr rfl hGrp, Finset.sum_add_distrib]
  refine add_le_add le_rfl (Finset.sum_le_sum fun j _ => ?_)
  refine Finset.sum_le_sum fun i hi => ?_
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  rw [dif_pos hi1]
  exact vanC_spec α hα hγ f hsm i j hi1 z hz θ hθ

end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.ClassC.UopGenAux.MollConvAux.zmollDzPthEq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC.UopGenAux.MollConvAux

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Elementary facts about the mollifying kernels -/

/-- `sKer δ` is continuous. -/
private lemma sKer_cont (δ : ℝ) : Continuous (Work.FTS.EllSol.PkgK5.K5c.sKer δ) := by
  have h : (fun t : ℝ => (δ * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ *
      Work.FTS.EllSol.PkgK5.K5c.sBump (t / δ)) = Work.FTS.EllSol.PkgK5.K5c.sKer δ := by
    funext t; simp only [Work.FTS.EllSol.PkgK5.K5c.sKer]
  rw [← h]
  exact continuous_const.mul (Work.FTS.EllSol.PkgK5.K5c.sBump_continuous.comp
    (continuous_id.div_const δ))


/-- `sKerd ε = deriv (sKer ε)` is continuous. -/
private lemma sKerd_cont (ε : ℝ) : Continuous (Work.FTS.EllSol.EllPkgAux.sKerd ε) := by
  have h : ContDiff ℝ 1 (Work.FTS.EllSol.PkgK5.K5c.sKer ε) :=
    Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 1)
  simpa [Work.FTS.EllSol.EllPkgAux.sKerd] using h.continuous_deriv_one

/-- `sKerd ε = deriv (sKer ε)` vanishes outside `[-ε, ε]`. -/
private lemma sKerd_eq_zero_of_lt_abs {ε t : ℝ} (hε : 0 < ε) (ht : ε < |t|) :
    Work.FTS.EllSol.EllPkgAux.sKerd ε t = 0 := by
  have hev : Work.FTS.EllSol.PkgK5.K5c.sKer ε =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) := by
    show ∀ᶠ y in 𝓝 t, Work.FTS.EllSol.PkgK5.K5c.sKer ε y = 0
    rw [Metric.eventually_nhds_iff]
    refine ⟨(|t| - ε) / 2, by linarith, ?_⟩
    intro y hy
    have h1 : |y - t| < (|t| - ε) / 2 := by simpa [Real.dist_eq] using hy
    have h2 : ε < |y| := by
      have h3 : |t| ≤ |y| + |y - t| := by simpa [abs_sub_comm] using abs_sub_le y 0 (y - t)
      linarith
    exact Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε (le_of_lt h2)
  rw [Work.FTS.EllSol.EllPkgAux.sKerd, hev.deriv_eq, deriv_const]


/-- A global bound for `sKer δ`. -/
private lemma exists_bound_sKer (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ t : ℝ, ‖Work.FTS.EllSol.PkgK5.K5c.sKer δ t‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -δ) (b := δ)).exists_bound_of_continuousOn
    (sKer_cont δ).continuousOn
  refine ⟨max C 0, fun t => ?_⟩
  by_cases ht : t ∈ Set.Icc (-δ) δ
  · exact le_trans (hC t ht) (le_max_left _ _)
  · rw [Set.mem_Icc, not_and_or] at ht
    have hz : Work.FTS.EllSol.PkgK5.K5c.sKer δ t = 0 := by
      refine Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ ?_
      rcases ht with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rw [hz, norm_zero]
    exact le_max_right _ _

/-- A global bound for `sKerd ε`. -/
private lemma exists_bound_sKerd (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ t : ℝ, ‖Work.FTS.EllSol.EllPkgAux.sKerd ε t‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -ε) (b := ε)).exists_bound_of_continuousOn
    (sKerd_cont ε).continuousOn
  refine ⟨max C 0, fun t => ?_⟩
  by_cases ht : t ∈ Set.Icc (-ε) ε
  · exact le_trans (hC t ht) (le_max_left _ _)
  · rw [Set.mem_Icc, not_and_or] at ht
    have hz : Work.FTS.EllSol.EllPkgAux.sKerd ε t = 0 := by
      refine sKerd_eq_zero_of_lt_abs hε ?_
      rcases ht with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rw [hz, norm_zero]
    exact le_max_right _ _

/-- `sKer δ (c - t) = 0` when `t` lies outside the interval `[c - δ, c + δ]`. -/
private lemma sKer_eq_zero_of_notMem_Icc {δ c t : ℝ} (hδ : 0 < δ)
    (h : t ∉ Set.Icc (c - δ) (c + δ)) : Work.FTS.EllSol.PkgK5.K5c.sKer δ (c - t) = 0 := by
  refine Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ (le_of_lt ?_)
  rw [Set.mem_Icc, not_and_or] at h
  rcases h with h | h
  · rw [abs_of_pos (by linarith)]; linarith
  · rw [abs_of_neg (by linarith)]; linarith

/-- `sKerd ε (c - t) = 0` when `t` lies outside the interval `[c - ε, c + ε]`. -/
private lemma sKerd_eq_zero_of_notMem_Icc {ε c t : ℝ} (hε : 0 < ε)
    (h : t ∉ Set.Icc (c - ε) (c + ε)) : Work.FTS.EllSol.EllPkgAux.sKerd ε (c - t) = 0 := by
  refine sKerd_eq_zero_of_lt_abs hε ?_
  rw [Set.mem_Icc, not_and_or] at h
  rcases h with h | h
  · rw [abs_of_pos (by linarith)]; linarith
  · rw [abs_of_neg (by linarith)]; linarith

/-- `sKerd ε (y - p) = 0` when `y` is within distance `1` of `c` while `p` is farther than
`1 + ε` from `c`. -/
private lemma sKerd_eq_zero_of_notMem_Icc_shift {ε y p c : ℝ} (hε : 0 < ε)
    (hy : y ∈ Set.Icc (c - 1) (c + 1)) (h : p ∉ Set.Icc (c - 1 - ε) (c + 1 + ε)) :
    Work.FTS.EllSol.EllPkgAux.sKerd ε (y - p) = 0 := by
  refine sKerd_eq_zero_of_lt_abs hε ?_
  rw [Set.mem_Icc] at hy
  rw [Set.mem_Icc, not_and_or] at h
  rcases h with h | h
  · rw [abs_of_pos (by linarith)]; linarith
  · rw [abs_of_neg (by linarith)]; linarith

/-! ## The two partial derivatives of the doubly-mollified convolution -/

/-- **The `θ`-derivative.**  For a locally integrable `H`, the `θ`-partial of the doubly
mollified convolution `∫ p, H p · sKer δ (x₁ - p₁) · sKer ε (θ - p₂)` is obtained by moving
the derivative onto the *inner* kernel. -/
private lemma hasDerivAt_slice_snd (H : ℝ × ℝ → ℝ)
    (hH : MeasureTheory.LocallyIntegrable H MeasureTheory.volume)
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (x : ℝ × ℝ) :
    HasDerivAt (fun y : ℝ => ∫ p : ℝ × ℝ,
        H p * (Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1)
          * Work.FTS.EllSol.PkgK5.K5c.sKer ε (y - p.2)))
      (∫ p : ℝ × ℝ, H p * (Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1)
          * Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2))) x.2 := by
  obtain ⟨C₁, hC₁⟩ := exists_bound_sKer δ hδ
  obtain ⟨C₂, hC₂⟩ := exists_bound_sKerd ε hε
  have hδc : Continuous (Work.FTS.EllSol.PkgK5.K5c.sKer δ) := sKer_cont δ
  have hεc : Continuous (Work.FTS.EllSol.PkgK5.K5c.sKer ε) := sKer_cont ε
  have hεdc : Continuous (Work.FTS.EllSol.EllPkgAux.sKerd ε) := sKerd_cont ε
  set Kbox : Set (ℝ × ℝ) :=
    Set.Icc (x.1 - δ) (x.1 + δ) ×ˢ Set.Icc (x.2 - 1 - ε) (x.2 + 1 + ε) with hKbox
  have hKc : IsCompact Kbox := isCompact_Icc.prod isCompact_Icc
  have hKmeas : MeasurableSet Kbox := measurableSet_Icc.prod measurableSet_Icc
  have hbnd_int : Integrable
      (fun p : ℝ × ℝ => C₁ * C₂ * Kbox.indicator (fun q : ℝ × ℝ => ‖H q‖) p)
      MeasureTheory.volume := by
    have h1 : Integrable (Kbox.indicator (fun q : ℝ × ℝ => ‖H q‖)) MeasureTheory.volume := by
      have h2 : Integrable (fun q : ℝ × ℝ => ‖Kbox.indicator H q‖) MeasureTheory.volume :=
        ((integrable_indicator_iff hKmeas).mpr (hH.integrableOn_isCompact hKc)).norm
      refine h2.congr ?_
      filter_upwards with q
      by_cases hq : q ∈ Kbox
      · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq]
      · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq, norm_zero]
    exact h1.const_mul (C₁ * C₂)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := MeasureTheory.volume)
    (F := fun y : ℝ => fun p : ℝ × ℝ => H p * (Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1)
        * Work.FTS.EllSol.PkgK5.K5c.sKer ε (y - p.2)))
    (F' := fun y : ℝ => fun p : ℝ × ℝ => H p * (Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1)
        * Work.FTS.EllSol.EllPkgAux.sKerd ε (y - p.2)))
    (bound := fun p : ℝ × ℝ => C₁ * C₂ * Kbox.indicator (fun q : ℝ × ℝ => ‖H q‖) p)
    (x₀ := x.2) (s := Set.Ioo (x.2 - 1) (x.2 + 1))
    (Ioo_mem_nhds (by linarith) (by linarith)) ?_ ?_ ?_ ?_ hbnd_int ?_).2
  · refine Filter.Eventually.of_forall fun y => ?_
    have hc : Continuous (fun p : ℝ × ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1)
        * Work.FTS.EllSol.PkgK5.K5c.sKer ε (y - p.2)) :=
      (hδc.comp (continuous_const.sub continuous_fst)).mul
        (hεc.comp (continuous_const.sub continuous_snd))
    exact hH.aestronglyMeasurable.mul hc.aestronglyMeasurable
  · have hc : Continuous (fun p : ℝ × ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1)
        * Work.FTS.EllSol.PkgK5.K5c.sKer ε (x.2 - p.2)) :=
      (hδc.comp (continuous_const.sub continuous_fst)).mul
        (hεc.comp (continuous_const.sub continuous_snd))
    have hcs : HasCompactSupport (fun p : ℝ × ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1)
        * Work.FTS.EllSol.PkgK5.K5c.sKer ε (x.2 - p.2)) := by
      refine HasCompactSupport.intro
        (K := Set.Icc (x.1 - δ) (x.1 + δ) ×ˢ Set.Icc (x.2 - ε) (x.2 + ε))
        (isCompact_Icc.prod isCompact_Icc) ?_
      intro p hp
      rw [Set.mem_prod, not_and_or] at hp
      rcases hp with hp | hp
      · rw [sKer_eq_zero_of_notMem_Icc hδ hp, zero_mul]
      · rw [sKer_eq_zero_of_notMem_Icc hε hp, mul_zero]
    have h := hH.integrable_smul_left_of_hasCompactSupport hc hcs
    refine h.congr ?_
    filter_upwards with p
    rw [smul_eq_mul]; ring
  · have hc : Continuous (fun p : ℝ × ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1)
        * Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2)) :=
      (hδc.comp (continuous_const.sub continuous_fst)).mul
        (hεdc.comp (continuous_const.sub continuous_snd))
    exact hH.aestronglyMeasurable.mul hc.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun p => ?_
    intro y hy
    by_cases hp : p ∈ Kbox
    · rw [Set.indicator_of_mem hp]
      have hA : ‖Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1)‖ ≤ C₁ := hC₁ _
      have hB : ‖Work.FTS.EllSol.EllPkgAux.sKerd ε (y - p.2)‖ ≤ C₂ := hC₂ _
      have hAnn : (0 : ℝ) ≤ ‖Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1)‖ := norm_nonneg _
      have hBnn : (0 : ℝ) ≤ ‖Work.FTS.EllSol.EllPkgAux.sKerd ε (y - p.2)‖ := norm_nonneg _
      have hC₁nn : (0 : ℝ) ≤ C₁ := le_trans hAnn hA
      have hprod : ‖Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1)‖
          * ‖Work.FTS.EllSol.EllPkgAux.sKerd ε (y - p.2)‖ ≤ C₁ * C₂ :=
        mul_le_mul hA hB hBnn hC₁nn
      calc ‖H p * (Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1)
            * Work.FTS.EllSol.EllPkgAux.sKerd ε (y - p.2))‖
          = ‖H p‖ * ‖Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1)
              * Work.FTS.EllSol.EllPkgAux.sKerd ε (y - p.2)‖ := norm_mul _ _
        _ = ‖H p‖ * (‖Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1)‖
              * ‖Work.FTS.EllSol.EllPkgAux.sKerd ε (y - p.2)‖) := by rw [norm_mul]
        _ ≤ ‖H p‖ * (C₁ * C₂) := mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
        _ = C₁ * C₂ * ‖H p‖ := by ring
    · rw [Set.indicator_of_notMem hp]
      rw [hKbox] at hp
      rw [Set.mem_prod, not_and_or] at hp
      rcases hp with hp | hp
      · have hz : Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1) = 0 :=
          sKer_eq_zero_of_notMem_Icc hδ hp
        simp [hz]
      · have hz : Work.FTS.EllSol.EllPkgAux.sKerd ε (y - p.2) = 0 :=
          sKerd_eq_zero_of_notMem_Icc_shift hε
            (Set.mem_Icc.mpr ⟨le_of_lt hy.1, le_of_lt hy.2⟩) hp
        simp [hz]
  · refine Filter.Eventually.of_forall fun p => ?_
    intro y _
    have hsm : HasDerivAt (fun y : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer ε (y - p.2))
        (Work.FTS.EllSol.EllPkgAux.sKerd ε (y - p.2)) y :=
      (show HasDerivAt (Work.FTS.EllSol.PkgK5.K5c.sKer ε)
          (Work.FTS.EllSol.EllPkgAux.sKerd ε (y - p.2)) (y - p.2) from
        (((Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 1)).differentiable_one)
          (y - p.2)).hasDerivAt).comp_sub_const y p.2
    exact (hsm.const_mul (Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1))).const_mul (H p)

/-- **The `z`-derivative.**  For a locally integrable `H`, the first partial of
`∫ p, H p · sKer δ (x₁ - p₁) · sKerd ε (x₂ - p₂)` is obtained by moving the derivative onto
the *outer* kernel. -/
private lemma hasDerivAt_slice_fst (H : ℝ × ℝ → ℝ)
    (hH : MeasureTheory.LocallyIntegrable H MeasureTheory.volume)
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (x : ℝ × ℝ) :
    HasDerivAt (fun y : ℝ => ∫ p : ℝ × ℝ,
        H p * (Work.FTS.EllSol.PkgK5.K5c.sKer δ (y - p.1)
          * Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2)))
      (∫ p : ℝ × ℝ, H p * (Work.FTS.EllSol.EllPkgAux.sKerd δ (x.1 - p.1)
          * Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2))) x.1 := by
  obtain ⟨C₁, hC₁⟩ := exists_bound_sKerd δ hδ
  obtain ⟨C₂, hC₂⟩ := exists_bound_sKerd ε hε
  have hδc : Continuous (Work.FTS.EllSol.PkgK5.K5c.sKer δ) := sKer_cont δ
  have hδdc : Continuous (Work.FTS.EllSol.EllPkgAux.sKerd δ) := sKerd_cont δ
  have hεdc : Continuous (Work.FTS.EllSol.EllPkgAux.sKerd ε) := sKerd_cont ε
  set Kbox : Set (ℝ × ℝ) :=
    Set.Icc (x.1 - 1 - δ) (x.1 + 1 + δ) ×ˢ Set.Icc (x.2 - ε) (x.2 + ε) with hKbox
  have hKc : IsCompact Kbox := isCompact_Icc.prod isCompact_Icc
  have hKmeas : MeasurableSet Kbox := measurableSet_Icc.prod measurableSet_Icc
  have hbnd_int : Integrable
      (fun p : ℝ × ℝ => C₁ * C₂ * Kbox.indicator (fun q : ℝ × ℝ => ‖H q‖) p)
      MeasureTheory.volume := by
    have h1 : Integrable (Kbox.indicator (fun q : ℝ × ℝ => ‖H q‖)) MeasureTheory.volume := by
      have h2 : Integrable (fun q : ℝ × ℝ => ‖Kbox.indicator H q‖) MeasureTheory.volume :=
        ((integrable_indicator_iff hKmeas).mpr (hH.integrableOn_isCompact hKc)).norm
      refine h2.congr ?_
      filter_upwards with q
      by_cases hq : q ∈ Kbox
      · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq]
      · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq, norm_zero]
    exact h1.const_mul (C₁ * C₂)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := MeasureTheory.volume)
    (F := fun t : ℝ => fun p : ℝ × ℝ => H p * (Work.FTS.EllSol.PkgK5.K5c.sKer δ (t - p.1)
        * Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2)))
    (F' := fun t : ℝ => fun p : ℝ × ℝ => H p * (Work.FTS.EllSol.EllPkgAux.sKerd δ (t - p.1)
        * Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2)))
    (bound := fun p : ℝ × ℝ => C₁ * C₂ * Kbox.indicator (fun q : ℝ × ℝ => ‖H q‖) p)
    (x₀ := x.1) (s := Set.Ioo (x.1 - 1) (x.1 + 1))
    (Ioo_mem_nhds (by linarith) (by linarith)) ?_ ?_ ?_ ?_ hbnd_int ?_).2
  · refine Filter.Eventually.of_forall fun t => ?_
    have hc : Continuous (fun p : ℝ × ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (t - p.1)
        * Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2)) :=
      (hδc.comp (continuous_const.sub continuous_fst)).mul
        (hεdc.comp (continuous_const.sub continuous_snd))
    exact hH.aestronglyMeasurable.mul hc.aestronglyMeasurable
  · have hc : Continuous (fun p : ℝ × ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1)
        * Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2)) :=
      (hδc.comp (continuous_const.sub continuous_fst)).mul
        (hεdc.comp (continuous_const.sub continuous_snd))
    have hcs : HasCompactSupport (fun p : ℝ × ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (x.1 - p.1)
        * Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2)) := by
      refine HasCompactSupport.intro
        (K := Set.Icc (x.1 - δ) (x.1 + δ) ×ˢ Set.Icc (x.2 - ε) (x.2 + ε))
        (isCompact_Icc.prod isCompact_Icc) ?_
      intro p hp
      rw [Set.mem_prod, not_and_or] at hp
      rcases hp with hp | hp
      · rw [sKer_eq_zero_of_notMem_Icc hδ hp, zero_mul]
      · rw [sKerd_eq_zero_of_notMem_Icc hε hp, mul_zero]
    have h := hH.integrable_smul_left_of_hasCompactSupport hc hcs
    refine h.congr ?_
    filter_upwards with p
    rw [smul_eq_mul]; ring
  · have hc : Continuous (fun p : ℝ × ℝ => Work.FTS.EllSol.EllPkgAux.sKerd δ (x.1 - p.1)
        * Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2)) :=
      (hδdc.comp (continuous_const.sub continuous_fst)).mul
        (hεdc.comp (continuous_const.sub continuous_snd))
    exact hH.aestronglyMeasurable.mul hc.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun p => ?_
    intro t ht
    by_cases hp : p ∈ Kbox
    · rw [Set.indicator_of_mem hp]
      have hA : ‖Work.FTS.EllSol.EllPkgAux.sKerd δ (t - p.1)‖ ≤ C₁ := hC₁ _
      have hB : ‖Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2)‖ ≤ C₂ := hC₂ _
      have hAnn : (0 : ℝ) ≤ ‖Work.FTS.EllSol.EllPkgAux.sKerd δ (t - p.1)‖ := norm_nonneg _
      have hBnn : (0 : ℝ) ≤ ‖Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2)‖ := norm_nonneg _
      have hC₁nn : (0 : ℝ) ≤ C₁ := le_trans hAnn hA
      have hprod : ‖Work.FTS.EllSol.EllPkgAux.sKerd δ (t - p.1)‖
          * ‖Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2)‖ ≤ C₁ * C₂ :=
        mul_le_mul hA hB hBnn hC₁nn
      calc ‖H p * (Work.FTS.EllSol.EllPkgAux.sKerd δ (t - p.1)
            * Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2))‖
          = ‖H p‖ * ‖Work.FTS.EllSol.EllPkgAux.sKerd δ (t - p.1)
              * Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2)‖ := norm_mul _ _
        _ = ‖H p‖ * (‖Work.FTS.EllSol.EllPkgAux.sKerd δ (t - p.1)‖
              * ‖Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2)‖) := by rw [norm_mul]
        _ ≤ ‖H p‖ * (C₁ * C₂) := mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
        _ = C₁ * C₂ * ‖H p‖ := by ring
    · rw [Set.indicator_of_notMem hp]
      rw [hKbox] at hp
      rw [Set.mem_prod, not_and_or] at hp
      rcases hp with hp | hp
      · have hz : Work.FTS.EllSol.EllPkgAux.sKerd δ (t - p.1) = 0 :=
          sKerd_eq_zero_of_notMem_Icc_shift hδ
            (Set.mem_Icc.mpr ⟨le_of_lt ht.1, le_of_lt ht.2⟩) hp
        simp [hz]
      · have hz : Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2) = 0 :=
          sKerd_eq_zero_of_notMem_Icc hε hp
        simp [hz]
  · refine Filter.Eventually.of_forall fun p => ?_
    intro t _
    have hsm : HasDerivAt (fun y : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (y - p.1))
        (Work.FTS.EllSol.EllPkgAux.sKerd δ (t - p.1)) t :=
      (show HasDerivAt (Work.FTS.EllSol.PkgK5.K5c.sKer δ)
          (Work.FTS.EllSol.EllPkgAux.sKerd δ (t - p.1)) (t - p.1) from
        (((Work.FTS.EllSol.EllPkgAux.contDiff_sKer δ (n := 1)).differentiable_one)
          (t - p.1)).hasDerivAt).comp_sub_const t p.1
    exact (hsm.mul_const (Work.FTS.EllSol.EllPkgAux.sKerd ε (x.2 - p.2))).const_mul (H p)


end

end Work.FTS.ClassC.UopGenAux.MollConvAux
end
-- ===== merged: Submission.Work.FTS.ClassC.VanishWeightDom =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

/-- `sin(2θ) ∈ [0,1]` on the angular interval `Iθ = [0,π/2]`. -/
theorem sin_two_mem_Icc {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.sin (2 * θ) ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨sin_two_nonneg_of_mem_Iθ' hθ, ?_⟩
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_le_one _

/-- `sin(2θ) > 0` on the open interval `(0,π/2)`. -/
theorem sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `(s^{e/2})² = s^e` for `s > 0`. -/
theorem sq_rpow_half {s e : ℝ} (hs : 0 < s) : (s ^ (e / 2)) ^ 2 = s ^ e := by
  rw [sq, ← Real.rpow_add hs, show e / 2 + e / 2 = e by ring]

/-- The angular weight of `HkIntegrand α 0 h` is `(h·w)² · s^{-η}` on the open interval. -/
theorem HkIntegrand_zero_eq_sq_mul_rpow (α : ℝ) (h : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.HkIntegrand α 0 h z θ
      = (h z θ * Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθ
  rw [HkIntegrand_zero_eq_classC, div_eq_mul_inv, mul_pow, mul_pow, inv_pow,
    sq_rpow_half hs, ← Real.rpow_neg (le_of_lt hs)]
  ring

/-- **Domination of a vanishing weight by the singular `ℋ^0`-integrand**: for `a ≥ -η`,
`(h·w)²·s^a ≤ HkIntegrand α 0 h` on the open interval. -/
theorem sq_mul_sin_le_HkIntegrand_zero (α : ℝ) (h : ℝ → ℝ → ℝ) {z θ : ℝ} {a : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (ha : -(Work.Spaces.eta) ≤ a) :
    (h z θ * Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ a
      ≤ Work.Spaces.HkIntegrand α 0 h z θ := by
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := (sin_two_mem_Icc ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩).2
  rw [HkIntegrand_zero_eq_sq_mul_rpow α h hθ]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  exact Real.rpow_le_rpow_of_exponent_ge hs hs1 ha

/-- **Monotonicity in the exponent of the vanishing weights**, on the open interval:
for `0 ≤ b ≤ a`, the weight `s^b` dominates `s^a`. -/
theorem sq_mul_sin_le_sq_mul_sin {X θ : ℝ} {a b : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (_hb : 0 ≤ b) (hba : b ≤ a) :
    X ^ 2 * (Real.sin (2 * θ)) ^ a ≤ X ^ 2 * (Real.sin (2 * θ)) ^ b := by
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := (sin_two_mem_Icc ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩).2
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  exact Real.rpow_le_rpow_of_exponent_ge hs hs1 hba

end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.ClassC.VopGen.muSliceAgmonPointwise =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC.VopGen

open MeasureTheory Set Filter
open scoped Real Topology

/-- The light angular weight of the `μ`-slot: `σ = TT.sigR (2 - γ(α))`. -/
local notation "𝔰[" α "]" => Work.FTS.EllipticEst.TT.sigR (2 - Work.Spaces.gam α)

/-- The derivative of the light angular weight: `σ' = TT.sigDR (2 - γ(α))`. -/
local notation "𝔡[" α "]" => Work.FTS.EllipticEst.TT.sigDR (2 - Work.Spaces.gam α)

/-! ## The slice Agmon inequality -/

theorem muSliceAgmonPointwise {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {f : ℝ → ℝ}
    (hcd : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hT0 : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hT1 : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hD : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) (Set.Ioo 0 (Real.pi / 2))) :
    (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      ≤ -(∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := by
  have hα1 : α ≤ 1 := by linarith
  have hp0 : 0 < 2 - Work.Spaces.gam α := Work.FTS.EllipticEst.Cores.sub_gam_pos hα1
  have hp1 : 2 - Work.Spaces.gam α < 1 := Work.FTS.EllipticEst.Cores.sub_gam_lt_one hα
  have hpne : 2 - Work.Spaces.gam α ≠ 0 := ne_of_gt hp0
  have hp1m : 0 ≤ 1 - (2 - Work.Spaces.gam α) := by linarith
  -- the weight, its continuity and its integrability on `(0, π/2)`
  have hsigRcont : Continuous (𝔰[α]) := by
    have h : (𝔰[α]) = fun t : ℝ => (Real.sin (2 * t)) ^ (2 - Work.Spaces.gam α) := rfl
    rw [h]
    exact Work.FTS.EllipticEst.Cores.sigA_continuous α hα1
  have hσIoo : IntegrableOn (𝔰[α]) (Set.Ioo 0 (Real.pi / 2)) :=
    (hsigRcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hσnn : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ 𝔰[α] θ := fun θ hθ => (sigR_gam_pos α θ hθ).le
  -- the hypothesis in the `sigA` spelling, for the endpoint-control lemmas
  have hD' : IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.Cores.sigA α θ)
      (Set.Ioo 0 (Real.pi / 2)) := hD
  obtain ⟨M, hMpos, hMbd⟩ :=
    Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.exists_deriv_abs_bound hα hα1 hcd hD'
  have hMnn : 0 ≤ M := hMpos.le
  -- ## endpoint control of `f` and `f'`
  have hdcont : ContinuousOn (deriv f) (Set.Ioo 0 (Real.pi / 2)) :=
    (hcd.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).continuousOn
  have hddcont : ContinuousOn (deriv (deriv f)) (Set.Ioo 0 (Real.pi / 2)) :=
    (((hcd.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).deriv_of_isOpen isOpen_Ioo
      (m := 0) (by norm_num))).continuousOn
  have hdint : IntegrableOn (deriv f) (Set.Ioo 0 (Real.pi / 2)) := by
    have hconst : IntegrableOn (fun _ : ℝ => M) (Set.Ioo 0 (Real.pi / 2)) := by
      refine MeasureTheory.integrableOn_const ?_ ?_
      · rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
      · simp
    exact integrableOn_Ioo_of_le hconst hdcont (fun θ hθ => hMbd θ hθ)
  have hvalL := Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.value_abs_le_mul_left
    hcd hdint hT0 hMnn hMbd
  have hvalR := Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.value_abs_le_mul_right
    hcd hdint hT1 hMnn hMbd
  have hfS : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ M * Real.sin (2 * θ) := by
    intro θ hθ
    have hSnn : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])
    rcases le_or_gt θ (Real.pi / 4) with hle | hlt
    · have hge : (4 / Real.pi) * θ ≤ Real.sin (2 * θ) := by
        have h := Real.mul_le_sin (x := 2 * θ) (by linarith [hθ.1])
          (by linarith [hle, Real.pi_pos])
        rwa [show (2 : ℝ) / Real.pi * (2 * θ) = (4 / Real.pi) * θ by ring] at h
      have hge' : θ ≤ (Real.pi / 4) * Real.sin (2 * θ) := by
        have h1 : (Real.pi / 4) * ((4 / Real.pi) * θ) ≤ (Real.pi / 4) * Real.sin (2 * θ) :=
          mul_le_mul_of_nonneg_left hge (by positivity)
        rwa [show (Real.pi / 4) * ((4 / Real.pi) * θ) = θ by field_simp] at h1
      calc |f θ| ≤ M * θ := hvalL θ hθ
        _ ≤ M * ((Real.pi / 4) * Real.sin (2 * θ)) := mul_le_mul_of_nonneg_left hge' hMnn
        _ ≤ M * Real.sin (2 * θ) :=
            mul_le_mul_of_nonneg_left (by nlinarith [hSnn, Real.pi_lt_four]) hMnn
    · have hge : (4 / Real.pi) * (Real.pi / 2 - θ)
          ≤ Real.sin (2 * (Real.pi / 2 - θ)) := by
        have h := Real.mul_le_sin (x := 2 * (Real.pi / 2 - θ)) (by linarith [hθ.2])
          (by linarith [hlt, Real.pi_pos])
        rwa [show (2 : ℝ) / Real.pi * (2 * (Real.pi / 2 - θ))
          = (4 / Real.pi) * (Real.pi / 2 - θ) by ring] at h
      have h2θ : Real.sin (2 * (Real.pi / 2 - θ)) = Real.sin (2 * θ) := by
        rw [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]
      rw [h2θ] at hge
      have hge' : Real.pi / 2 - θ ≤ (Real.pi / 4) * Real.sin (2 * θ) := by
        have h1 : (Real.pi / 4) * ((4 / Real.pi) * (Real.pi / 2 - θ))
            ≤ (Real.pi / 4) * Real.sin (2 * θ) := mul_le_mul_of_nonneg_left hge (by positivity)
        rwa [show (Real.pi / 4) * ((4 / Real.pi) * (Real.pi / 2 - θ)) = Real.pi / 2 - θ from by
          field_simp] at h1
      calc |f θ| ≤ M * (Real.pi / 2 - θ) := hvalR θ hθ
        _ ≤ M * ((Real.pi / 4) * Real.sin (2 * θ)) := mul_le_mul_of_nonneg_left hge' hMnn
        _ ≤ M * Real.sin (2 * θ) :=
            mul_le_mul_of_nonneg_left (by nlinarith [hSnn, Real.pi_lt_four]) hMnn
  -- ## the five integrability clauses of the light-weight integration by parts
  have hI1 : IntegrableOn (fun θ : ℝ => deriv f θ ^ 2 * 𝔰[α] θ) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.integrableOn_Iθ_of_Ioo
      (integrableOn_Ioo_of_le (hσIoo.const_mul (M ^ 2)) ((hdcont.pow 2).mul hsigRcont.continuousOn)
        (fun θ hθ => by
          have hsq : (deriv f θ) ^ 2 ≤ M ^ 2 := by
            have h := hMbd θ hθ
            have h2 := pow_le_pow_left₀ (abs_nonneg (deriv f θ)) h 2
            rwa [sq_abs] at h2
          rw [abs_mul, abs_of_nonneg (sq_nonneg (deriv f θ)), abs_of_nonneg (hσnn θ hθ)]
          exact mul_le_mul_of_nonneg_right hsq (hσnn θ hθ)))
  have hddσIoo : IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * 𝔰[α] θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    simpa only [Work.FTS.EllipticEst.TT.sigR] using hD
  have hI2 : IntegrableOn (fun θ : ℝ => f θ * deriv (deriv f) θ * 𝔰[α] θ) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.integrableOn_Iθ_of_Ioo
      (integrableOn_Ioo_of_le ((hσIoo.const_mul (M ^ 2)).add hddσIoo)
        ((hcd.continuousOn.mul hddcont).mul hsigRcont.continuousOn)
        (fun θ hθ => by
          have hfabs : |f θ| ≤ M := by
            calc |f θ| ≤ M * Real.sin (2 * θ) := hfS θ hθ
              _ ≤ M * 1 := mul_le_mul_of_nonneg_left (Real.sin_le_one _) hMnn
              _ = M := by ring
          have hamb : M * |deriv (deriv f) θ| ≤ (M ^ 2 + (deriv (deriv f) θ) ^ 2) / 2 := by
            have h := two_mul_le_add_sq M |deriv (deriv f) θ|
            rw [sq_abs] at h
            linarith [h]
          calc |f θ * deriv (deriv f) θ * 𝔰[α] θ|
              = |f θ| * |deriv (deriv f) θ| * 𝔰[α] θ := by
                rw [abs_mul, abs_mul, abs_of_nonneg (hσnn θ hθ)]
            _ ≤ M * |deriv (deriv f) θ| * 𝔰[α] θ :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfabs (abs_nonneg _))
                  (hσnn θ hθ)
            _ ≤ ((M ^ 2 + (deriv (deriv f) θ) ^ 2) / 2) * 𝔰[α] θ :=
                mul_le_mul_of_nonneg_right hamb (hσnn θ hθ)
            _ ≤ M ^ 2 * 𝔰[α] θ + (deriv (deriv f) θ) ^ 2 * 𝔰[α] θ := by
                nlinarith [hσnn θ hθ, sq_nonneg M, sq_nonneg (deriv (deriv f) θ)]))
  have hI3 : IntegrableOn (fun θ : ℝ => f θ * deriv f θ * 𝔡[α] θ) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.integrableOn_Iθ_of_Ioo
      (integrableOn_Ioo_of_le (hσIoo.const_mul (2 * (2 - Work.Spaces.gam α) * M ^ 2))
        ((hcd.continuousOn.mul hdcont).mul (sigDR_gam_continuousOn α))
        (fun θ hθ => by
          have hSp : 0 < Real.sin (2 * θ) := Work.FTS.EllipticEst.TT.sin_two_pos_of_mem_Ioo hθ
          have hSnn : 0 ≤ Real.sin (2 * θ) := hSp.le
          have hpowid : Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) - 1)
              = 𝔰[α] θ := by
            simp only [Work.FTS.EllipticEst.TT.sigR]
            exact Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.mul_rpow_sub_one hSp hpne
          calc |f θ * deriv f θ * 𝔡[α] θ|
              = |f θ| * |deriv f θ| * |𝔡[α] θ| := by rw [abs_mul, abs_mul]
            _ ≤ (M * Real.sin (2 * θ)) * M
                  * (2 * (2 - Work.Spaces.gam α)
                    * (Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) - 1)) :=
                mul_le_mul (mul_le_mul (hfS θ hθ) (hMbd θ hθ) (abs_nonneg _)
                  (mul_nonneg hMnn hSnn)) (sigDR_gam_abs_le hα1 hSp) (abs_nonneg _)
                  (mul_nonneg (mul_nonneg hMnn hSnn) hMnn)
            _ = 2 * (2 - Work.Spaces.gam α) * M ^ 2
                  * (Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) - 1)) := by ring
            _ = 2 * (2 - Work.Spaces.gam α) * M ^ 2 * 𝔰[α] θ := by rw [hpowid]))
  have hI4 : IntegrableOn (fun θ : ℝ => f θ ^ 2 * 𝔰[α] θ) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.integrableOn_Iθ_of_Ioo
      (integrableOn_Ioo_of_le (hσIoo.const_mul (M ^ 2)) ((hcd.continuousOn.pow 2).mul hsigRcont.continuousOn)
        (fun θ hθ => by
          have hu2 : (f θ) ^ 2 ≤ (M * Real.sin (2 * θ)) ^ 2 := by
            have h0' : (0:ℝ) ≤ |f θ| := abs_nonneg _
            calc (f θ) ^ 2 = |f θ| ^ 2 := (sq_abs (f θ)).symm
              _ ≤ (M * Real.sin (2 * θ)) ^ 2 := pow_le_pow_left₀ h0' (hfS θ hθ) 2
          have hMS : (M * Real.sin (2 * θ)) ^ 2 ≤ M ^ 2 := by
            have hSnn : 0 ≤ Real.sin (2 * θ) :=
              Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
                (by linarith [hθ.2, Real.pi_pos])
            have h1 : M * Real.sin (2 * θ) ≤ M * 1 :=
              mul_le_mul_of_nonneg_left (Real.sin_le_one _) hMnn
            calc (M * Real.sin (2 * θ)) ^ 2 ≤ (M * 1) ^ 2 :=
                  pow_le_pow_left₀ (mul_nonneg hMnn hSnn) h1 2
              _ = M ^ 2 := by ring
          rw [abs_mul, abs_of_nonneg (sq_nonneg (f θ)), abs_of_nonneg (hσnn θ hθ)]
          exact mul_le_mul_of_nonneg_right (le_trans hu2 hMS) (hσnn θ hθ)))
  have hcos2cont : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) :=
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn).pow 2
  have hsin2cont : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2))
      (Set.Ioo 0 (Real.pi / 2)) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun x hx => Or.inl (ne_of_gt (Work.FTS.EllipticEst.TT.sin_two_pos_of_mem_Ioo hx)))
  have hI5 : IntegrableOn (fun θ : ℝ => f θ ^ 2 * Real.cos (2 * θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2)) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.integrableOn_Iθ_of_Ioo
      (integrableOn_Ioo_of_le (hσIoo.const_mul (M * M))
        (((hcd.continuousOn.pow 2).mul hcos2cont).mul hsin2cont)
        (fun θ hθ => by
          have hSp : 0 < Real.sin (2 * θ) := Work.FTS.EllipticEst.TT.sin_two_pos_of_mem_Ioo hθ
          have hSpow : 0 ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2) :=
            Real.rpow_nonneg hSp.le _
          have hc2 : Real.cos (2 * θ) ^ 2 ≤ 1 := by
            have h1 : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
            have h2 : |Real.cos (2 * θ)| ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
            rwa [sq_abs, one_pow] at h2
          have hu2 : (f θ) ^ 2 ≤ (M * Real.sin (2 * θ)) ^ 2 := by
            have h0' : (0:ℝ) ≤ |f θ| := abs_nonneg _
            calc (f θ) ^ 2 = |f θ| ^ 2 := (sq_abs (f θ)).symm
              _ ≤ (M * Real.sin (2 * θ)) ^ 2 := pow_le_pow_left₀ h0' (hfS θ hθ) 2
          have h5 : (M * Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2) ≤ M * M * 𝔰[α] θ := by
            have hstep : (M * Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2)
                ≤ M * M * ((Real.sin (2 * θ)) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2)) := by
              calc (M * Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2)
                  = ((M * Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ) ^ 2)
                      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2) := by ring
                _ ≤ ((M * Real.sin (2 * θ)) ^ 2 * 1)
                      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2) :=
                    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc2 (sq_nonneg _)) hSpow
                _ = M * M * ((Real.sin (2 * θ)) ^ 2
                      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2)) := by ring
            rw [Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.mul_rpow_sub_two hSp] at hstep
            simpa only [Work.FTS.EllipticEst.TT.sigR] using hstep
          have hnn : 0 ≤ (f θ) ^ 2 * Real.cos (2 * θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2) :=
            mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hSpow
          rw [abs_of_nonneg hnn]
          calc (f θ) ^ 2 * Real.cos (2 * θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2)
              = (f θ) ^ 2 * (Real.cos (2 * θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2)) := by ring
            _ ≤ (M * Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2)) :=
                mul_le_mul_of_nonneg_right hu2 (mul_nonneg (sq_nonneg _) hSpow)
            _ = (M * Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2) := by ring
            _ ≤ M * M * 𝔰[α] θ := h5))
  -- ## the four boundary clauses
  have hb1 := tendsto_ff'_sigR_zero (α := α) (M := M) hα1 hMnn hfS hMbd
  have hb2 := tendsto_ff'_sigR_zero_right (α := α) (M := M) hα1 hMnn hfS hMbd
  have hb3 := tendsto_sq_sigDR_zero (α := α) (M := M) hα1 hMnn hfS
  have hb4 := tendsto_sq_sigDR_zero_right (α := α) (M := M) hα1 hMnn hfS
  -- ## the double angular integration by parts
  have hibp := Work.FTS.EllipticEst.TT.slice_ibp_light (2 - Work.Spaces.gam α) hp0 hp1 hcd
    hI1 hI2 hI3 hI4 hI5 hb1 hb2 hb3 hb4
  -- ## the two leftover terms are nonnegative
  have hD0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, f θ ^ 2 * 𝔰[α] θ :=
    setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sigR_gam_nonneg α θ hθ))
  have hE0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, f θ ^ 2 * Real.cos (2 * θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2) :=
    setIntegral_nonneg measurableSet_Icc (fun θ hθ => mul_nonneg
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])) _))
  have hmain : (∫ θ in Work.Spaces.Iθ, deriv f θ ^ 2 * 𝔰[α] θ)
      ≤ -(∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * 𝔰[α] θ) := by
    have h2a : 0 ≤ 2 * (2 - Work.Spaces.gam α) * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * 𝔰[α] θ) :=
      mul_nonneg (mul_nonneg (by norm_num) hp0.le) hD0
    have h2b : 0 ≤ 2 * (2 - Work.Spaces.gam α) * (1 - (2 - Work.Spaces.gam α))
        * (∫ θ in Work.Spaces.Iθ, f θ ^ 2 * Real.cos (2 * θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α - 2)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hp0.le) hp1m) hE0
    rw [hibp]
    linarith
  simpa only [Work.FTS.EllipticEst.TT.sigR] using hmain

end Work.FTS.ClassC.VopGen
end
-- ===== merged: Submission.Work.FTS.ClassC.intervalIntegrable_rpow_Fstar_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

open MeasureTheory Set Filter
open scoped Real Topology

/-! ## Interval integrability of `s^{(5-α)/α}·F_*(g)(s)` for an open-quadrant smooth source

The singular radial piece
`Ḡ(α,g)(z) = -(3/(4α)) z^{-5/α} ∫_0^z s^{(5-α)/α} F_*(g)(s) ds` of §'The singular term' is only
a genuine integral if `s ↦ s^{(5-α)/α}·F_*(g)(s)` is interval integrable on `[0,z]`.  This is
proved here for every `α > 0` and every datum `g` which is `C^∞` on the open quadrant
`(0,∞)×(0,π/2)` (`SmoothOpen`, i.e. no boundary regularity at `θ = 0, π/2` is required) and
lies honestly in the weighted space `ℋ⁴` (`HkMem α 4`).

The mathematics, for `z > 0`:

* **Continuity of the moment.**  `F_*(g) = PsiInt g 0` is continuous on `(0,∞)` by
  `Work.FTS.EllipticEst.PsiInt_continuousOn` (the moment tower plus the Cauchy–Schwarz
  majorant `A_1 ∈ L¹`).  Hence so is `s ↦ s^{(5-α)/α}·F_*(g)(s)` on `(0,∞)`.
* **The `L¹` bound.**  `Work.FTS.EllipticEst.GbarSin.Fstar_div_le_majorant` at `j = 0` gives,
  for `s > 0`,
  `|F_*(g)(s)|/s ≤ ((π/2)·∫_θ HkIntegrand α 4 g s θ + 1)/2`,
  and multiplying by `s > 0` bounds `|F_*(g)(s)|` itself.
* **The radial exponent.**  Multiplying by `s^c`, `c = (5-α)/α`, and using
  `s^c·s = s^{c+1}` together with `c + 1 = 5/α > 0`, we get on `(0,z]`
  `‖s^c·F_*(g)(s)‖ ≤ z^{c+1}·((π/2)·G(s) + 1)/2`, where
  `G(s) = ∫_θ HkIntegrand α 4 g s θ` is integrable on `(0,z]` by `HkMem` (`z ∈ Iz`): the
  majorant is an integrable function of `s` on the *finite* interval `(0,z]`. -/
theorem intervalIntegrable_rpow_Fstar_open (α : ℝ) (hα : 0 < α) (g : ℝ → ℝ → ℝ)
    (hso : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    {z : ℝ} (hz : 0 < z) :
    IntervalIntegrable (fun s : ℝ => s ^ ((5 - α) / α) * Work.Elliptic.Fstar g s)
      MeasureTheory.volume 0 z := by
  set c : ℝ := (5 - α) / α with hc
  have hcp1 : c + 1 = 5 / α := by
    rw [hc]; field_simp; ring
  have hc1 : 0 < c + 1 := by rw [hcp1]; exact div_pos (by norm_num) hα
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hz.le]
  -- (1) the angular moment is continuous on `(0,∞)`
  have hcont : ContinuousOn (fun s : ℝ => Work.Elliptic.Fstar g s) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.PsiInt_continuousOn α 4 g hso hmem 0 (by norm_num)
  -- (2) a.e. strong measurability of the integrand on `(0,z]`
  have haesm : AEStronglyMeasurable (fun s : ℝ => s ^ c * Work.Elliptic.Fstar g s)
      (volume.restrict (Set.Ioc 0 z)) := by
    have hrpow : ContinuousOn (fun s : ℝ => s ^ c) (Set.Ioi 0) :=
      continuousOn_id.rpow_const (fun s hs => Or.inl (ne_of_gt hs))
    exact ((hrpow.mul hcont).mono (fun s hs => hs.1)).aestronglyMeasurable measurableSet_Ioc
  -- (3) the angular slice `G(s) = ∫_θ HkIntegrand α 4 g s θ` is integrable on `(0,z]`
  have hGint : IntegrableOn
      (fun s : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ)
      (Set.Ioc 0 z) :=
    hmem.2.mono_set (fun s hs => by rw [Work.Spaces.Iz]; exact le_of_lt hs.1)
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 z) :=
    integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hdom : Integrable (fun s : ℝ => z ^ (c + 1) *
      (((Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) + 1) / 2))
      (volume.restrict (Set.Ioc 0 z)) :=
    ((hGint.const_mul (Real.pi / 2)).add hone).div_const 2 |>.const_mul (z ^ (c + 1))
  -- (4) the pointwise domination
  have hpt : ∀ s ∈ Set.Ioc 0 z, ‖s ^ c * Work.Elliptic.Fstar g s‖
      ≤ z ^ (c + 1) * (((Real.pi / 2)
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) + 1) / 2) := by
    intro s hs
    have hs0 : 0 < s := hs.1
    have hsz : s ≤ z := hs.2
    have hGnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ :=
      integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g s θ
    have hpiG : 0 ≤ (Real.pi / 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) :=
      mul_nonneg (by positivity) hGnn
    have hX0 : 0 ≤ ((Real.pi / 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) + 1) / 2 := by
      linarith
    -- Cauchy–Schwarz for the angular moment, in `L¹` form
    have hdiv := Work.FTS.EllipticEst.GbarSin.Fstar_div_le_majorant α 4 g hso hmem 0
      (by norm_num) hs0
    have hdiv' : |Work.Elliptic.Fstar g s| / s ≤ ((Real.pi / 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) + 1) / 2 := by
      simpa only [Work.Spaces.DzIter_zero] using hdiv
    have hAbs : |Work.Elliptic.Fstar g s| ≤ s * (((Real.pi / 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) + 1) / 2) := by
      have h := (div_le_iff₀ hs0).mp hdiv'
      simpa only [mul_comm] using h
    have hstep1 : s ^ c * |Work.Elliptic.Fstar g s| ≤ s ^ c * (s * (((Real.pi / 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) + 1) / 2)) :=
      mul_le_mul_of_nonneg_left hAbs (Real.rpow_nonneg hs0.le c)
    have hstep2 : s ^ c * (s * (((Real.pi / 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) + 1) / 2))
        = s ^ (c + 1) * (((Real.pi / 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) + 1) / 2) := by
      have hsc : s ^ (c + 1) = s ^ c * s := by
        rw [Real.rpow_add hs0 c 1, Real.rpow_one]
      rw [hsc, mul_assoc]
    have hstep3 : s ^ (c + 1) * (((Real.pi / 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) + 1) / 2)
        ≤ z ^ (c + 1) * (((Real.pi / 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g s θ) + 1) / 2) :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hs0.le hsz hc1.le) hX0
    have hnorm : ‖s ^ c * Work.Elliptic.Fstar g s‖
        = s ^ c * |Work.Elliptic.Fstar g s| := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le c)]
    rw [hnorm]
    exact le_trans hstep1 (le_trans (le_of_eq hstep2) hstep3)
  exact Integrable.mono' hdom haesm (ae_restrict_of_forall_mem measurableSet_Ioc hpt)

end Work.FTS.ClassC
end
-- ===== merged: Submission.Work.FTS.ClassC.zTail_hardy =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.ClassC

theorem zTail_hardy {g : ℝ → ℝ → ℝ} (hso : Work.FTS.EllipticEst.SmoothOpen g)
    (hdec : ∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => g z θ) Filter.atTop (nhds 0))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hfin : Work.FTS.ClassC.zTail g θ ≠ ⊤) :
    ∀ z ∈ Set.Ioi (0 : ℝ), (g z θ) ^ 2 ≤ Work.FTS.ClassC.zTailR g θ := by
  intro z hz
  -- `θ` is an interior angle, so it lies in `Iθ`
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  -- the `z`-slice is `C¹` on `(0,∞)`, since `g` is `C^∞` on the open quadrant
  have hcd : ContDiffOn ℝ 1 (fun s : ℝ => g s θ) (Set.Ioi (0 : ℝ)) :=
    (hso.curry_z hθ).of_le (by simp [Work.Stability.smoothOrder])
  have hdec' : Filter.Tendsto (fun s : ℝ => g s θ) Filter.atTop (nhds 0) := hdec θ hθI
  -- the radial Hardy inequality in `lintegral` form
  have hkey := Work.FTS.H2.T2Qaux.hardyZQ_lintegral hcd hdec' hz
  -- `zTail g θ` is the lintegral of exactly that integrand
  have hzTail : Work.FTS.ClassC.zTail g θ =
      MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iz)
        (fun s : ℝ =>
          ENNReal.ofReal ((s * deriv (fun s' => g s' θ) s) ^ 2 * (Work.Spaces.w s) ^ 2)) := by
    rw [Work.FTS.ClassC.zTail_eq_lintegral]
    apply MeasureTheory.lintegral_congr
    intro s
    simp only [Work.Spaces.Dz, Work.Spaces.pz]
  calc (g z θ) ^ 2
      = ENNReal.toReal (ENNReal.ofReal ((g z θ) ^ 2)) :=
        (ENNReal.toReal_ofReal (sq_nonneg _)).symm
    _ ≤ ENNReal.toReal (Work.FTS.ClassC.zTail g θ) :=
        ENNReal.toReal_mono hfin (by rw [hzTail]; exact hkey)
    _ = Work.FTS.ClassC.zTailR g θ := rfl

end Work.FTS.ClassC
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Assembly.HkSq_Dth_le_ge =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

/-! ## The measure-theoretic transfer -/

/-- **Iterated integrals of a pointwise-dominated nonnegative integrand.**

If `0 ≤ A ≤ B` pointwise on `Iz × Iθ`, if every angular slice of `B` is integrable and
`z ↦ ∫_θ B z θ` is integrable on `Iz`, then `∫_z ∫_θ A ≤ ∫_z ∫_θ B`.

No measurability of `A` is assumed: where the slice `θ ↦ A z θ` is not integrable the
inner integral is `0 ≤ ∫_θ B z θ` (the latter being nonnegative by `0 ≤ B` on the slice),
and `MeasureTheory.integral_mono_of_nonneg` applies in each case. -/
private lemma iterated_integral_le {A B : ℝ → ℝ → ℝ}
    (hA0 : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ A z θ)
    (hAB : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, A z θ ≤ B z θ)
    (hB : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => B z θ) Work.Spaces.Iθ)
    (hBz : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, B z θ) Work.Spaces.Iz) :
    ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, A z θ) ≤
      ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, B z θ) := by
  have hmesθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hmesz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  refine integral_mono_of_nonneg ?_ hBz ?_
  · -- nonnegativity of the inner integral of `A` on `Iz`
    refine ae_restrict_of_forall_mem hmesz (fun z hz => ?_)
    exact integral_nonneg_of_ae (ae_restrict_of_forall_mem hmesθ (fun θ hθ => hA0 z hz θ hθ))
  · -- `z ↦ ∫_θ A z θ ≤ z ↦ ∫_θ B z θ` on `Iz`
    refine ae_restrict_of_forall_mem hmesz (fun z hz => ?_)
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem hmesθ (fun θ hθ => hA0 z hz θ hθ))
      (hB z hz)
      (ae_restrict_of_forall_mem hmesθ (fun θ hθ => hAB z hz θ hθ))

/-! ## The target -/

/-- The squared `ℋⁿ`-norm of `D_θ f` is dominated by the squared `ℋ^{n+1}`-norm of `f`,
for every `f` with honest `ℋ^{n+1}`-integrand and every `α ≥ -1/10`. -/
theorem HkSq_Dth_le_ge (α : ℝ) (hα : -(1/10 : ℝ) ≤ α) (n : ℕ) {f : ℝ → ℝ → ℝ}
    (h : Work.Spaces.HkMem α (n + 1) f) :
    Work.Spaces.HkSq α n (Work.Spaces.Dth f) ≤ Work.Spaces.HkSq α (n + 1) f :=
  iterated_integral_le
    (fun z _ θ _ => Work.Spaces.HkIntegrand_nonneg α n (Work.Spaces.Dth f) z θ)
    (fun z hz θ hθ =>
      Work.FTS.CoercivityFix.E2Bound.HkIntegrand_Dth_le_ge α hα n f z θ hz hθ)
    (fun z hz => h.1 z hz) h.2

end Work.FTS.CoercivityFix.Assembly
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.E2Bound.E2hat_slice_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.E2Bound

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.FTS.CoercivityFix.E2Bound.SlotMul

/-! ## The multiplier `φ(z) = z/(1+z)²` and the auxiliary function `G = 2f + 3D_θf` -/

/-- The radial profile of the commutator defect: `φ(z) = z/(1+z)²`. -/
private def phiZ : ℝ → ℝ := fun z => z / (1 + z) ^ 2


/-- `φ` is `C^∞` on `(-1,∞)` (a quotient with non-vanishing denominator). -/
private lemma phiZ_contDiffOn :
    ContDiffOn ℝ Work.Stability.smoothOrder phiZ (Set.Ioi (-1)) := by
  have hnum : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => z) (Set.Ioi (-1)) :=
    contDiff_id.contDiffOn
  have hden : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => (1 + z) ^ 2)
      (Set.Ioi (-1)) :=
    (contDiffOn_const.add contDiff_id.contDiffOn).pow 2
  have hne : ∀ z ∈ Set.Ioi (-1 : ℝ), (fun z : ℝ => (1 + z) ^ 2) z ≠ 0 := fun z hz => by
    have h1 : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
    positivity
  have h : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => z / (1 + z) ^ 2) (Set.Ioi (-1)) :=
    hnum.div hden hne
  exact h





/-! ## Vanishing at `z = 0` -/

/-- `HkIntegrand` vanishes at `z = 0` (the weight `w 0 = 0` kills every summand). -/
private lemma HkIntegrand_eq_zero_of_z_eq_zero (α : ℝ) (n : ℕ) (h : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α n h 0 θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  have hw : Work.Spaces.w 0 = 0 := by simp [Work.Spaces.w]
  have h1 : ∀ i : ℕ,
      (Work.Spaces.DzIter i h 0 θ
        * (Work.Spaces.w 0 / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 = 0 := by
    intro i
    rw [hw, zero_div, mul_zero, zero_pow (by norm_num)]
  have h2 : ∀ i j : ℕ,
      (if 1 ≤ i ∧ i + j ≤ n
        then (Work.Spaces.mixed j i h 0 θ * Work.Spaces.Wt α 0 θ) ^ 2 else 0) = 0 := by
    intro i j
    by_cases hc : 1 ≤ i ∧ i + j ≤ n
    · rw [if_pos hc]
      have hW : Work.Spaces.Wt α 0 θ = 0 := by simp [Work.Spaces.Wt, Work.Spaces.w]
      rw [hW, mul_zero, zero_pow (by norm_num)]
    · rw [if_neg hc]
  rw [Finset.sum_eq_zero (fun i _ => h1 i),
    Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => h2 i j)), add_zero]

/-! ## `Iθ` and `(0,π/2)` carry the same measure -/

/-- The two boundary points `{0, π/2}` are null, so `Iθ` and `(0,π/2)` carry the same
restricted Lebesgue measure. -/
private lemma restrict_Iθ_eq_Ioo :
    (volume : Measure ℝ).restrict Work.Spaces.Iθ
      = (volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2)) :=
  (restrict_Ioo_eq_restrict_Icc (μ := (volume : Measure ℝ)) (a := 0) (b := π / 2)).symm

/-! ## Measurability of the angular slices -/



/-! ## The slice inequality -/


end Work.FTS.CoercivityFix.E2Bound
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollAssem.StripAdm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace MollAssem

/-! ## Strip-admissibility and slice honesty of the approximants -/

/-- The slice domination `|G w τ| ≤ MG G w` (the second-order Taylor formula at `θ = π/4`
plus the weighted Cauchy--Schwarz `sliceIntBoundMFA`).  This is `MollSmooth.sliceDom` with the
missing ingredient filled in, so that the present module does not depend on a `sorry`. -/
theorem sliceDomMFA (G : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen G)
    (hH : Work.EllipticEst.Core.i0Aux.SliceHonestOpen G) :
    ∀ w : ℝ, 0 < w → ∀ τ : ℝ, τ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      |G w τ| ≤ Work.FTS.EllSol.EllPkgAux.MG G w := by
  intro w hw τ hτ
  have hτ0 : 0 < τ := hτ.1
  have hτ1 : τ < Real.pi / 2 := hτ.2
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsmo : (2 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
    simp [Work.Stability.smoothOrder]
  have hf2 : ContDiffOn ℝ 2 (fun θ : ℝ => G w θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hS.curry_θ hw).of_le hsmo
  have ha0 : (0 : ℝ) < Real.pi / 4 := by linarith
  have ha1 : Real.pi / 4 < Real.pi / 2 := by linarith
  have ha_mem : (Real.pi / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨ha0, ha1⟩
  have hHint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
    have hc : (0 : ℝ) < (Work.Spaces.w w) ^ 2 := by
      rw [Work.Spaces.w]; positivity
    have h0 := hH.1 w hw
    have hEq : ∀ θ : ℝ, ((Work.Spaces.w w) ^ 2)⁻¹ *
        (Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * (Work.Spaces.w w) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
        = Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * Work.FTS.EllipticEst.thEta θ := by
      intro θ
      rw [show Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * (Work.Spaces.w w) ^ 2
            * Work.FTS.EllipticEst.thEta θ
          = (Work.Spaces.w w) ^ 2 * (Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2
            * Work.FTS.EllipticEst.thEta θ) from by ring]
      exact inv_mul_cancel_left₀ (ne_of_gt hc) _
    rw [show (fun θ : ℝ => Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2
          * Work.FTS.EllipticEst.thEta θ)
        = fun θ : ℝ => ((Work.Spaces.w w) ^ 2)⁻¹ *
          (Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * (Work.Spaces.w w) ^ 2
            * Work.FTS.EllipticEst.thEta θ) from funext (fun θ => (hEq θ).symm)]
    exact h0.const_mul _
  have hT := Work.FTS.EllSol.EllPkgAux.MollSmooth.slice_taylor_two hf2 ha_mem hτ
  have hTail : |∫ t in (Real.pi / 4)..τ,
        (τ - t) * deriv (deriv (fun θ : ℝ => G w θ)) t|
      ≤ (Real.pi / 4) * Real.sqrt (Real.pi / 4) *
        Real.sqrt (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
    rcases le_total (Real.pi / 4) τ with hle | hle
    · have hcont : ContinuousOn (fun t : ℝ => deriv (deriv (fun θ : ℝ => G w θ)) t)
          (Set.uIcc (Real.pi / 4) τ) :=
        Work.FTS.EllSol.EllPkgAux.MollSmooth.slice_dd_cont hf2 ha_mem hτ
      have hc : ∀ t ∈ Set.Icc (Real.pi / 4) τ, |τ - t| ≤ Real.pi / 4 := by
        intro t ht
        rw [abs_of_nonneg (by linarith [ht.2])]
        linarith [ht.1]
      exact sliceIntBoundMFA hle ha0 hτ1 (by linarith)
        hcont hc hHint
    · have hcont : ContinuousOn (fun t : ℝ => deriv (deriv (fun θ : ℝ => G w θ)) t)
          (Set.uIcc τ (Real.pi / 4)) :=
        Work.FTS.EllSol.EllPkgAux.MollSmooth.slice_dd_cont hf2 hτ ha_mem
      have hc : ∀ t ∈ Set.Icc τ (Real.pi / 4), |τ - t| ≤ Real.pi / 4 := by
        intro t ht
        rw [abs_of_nonpos (by linarith [ht.1])]
        linarith [ht.2]
      have h := sliceIntBoundMFA hle hτ0 ha1 (by linarith)
        hcont hc hHint
      rw [intervalIntegral.integral_symm, abs_neg]
      exact h
  have hMG : Work.FTS.EllSol.EllPkgAux.MG G w
      = |G w (Real.pi / 4)| + |Work.Spaces.pth G w (Real.pi / 4)|
        + Real.sqrt (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := rfl
  rw [hMG]
  have habs : |τ - Real.pi / 4| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [Real.pi_le_four, Real.pi_pos]
  have hdnn : (0 : ℝ) ≤ |deriv (fun θ : ℝ => G w θ) (Real.pi / 4)| := abs_nonneg _
  have hcoef : (Real.pi / 4) * Real.sqrt (Real.pi / 4) ≤ 1 := by
    have h1 : Real.pi / 4 ≤ 1 := by linarith [Real.pi_le_four]
    have h2 : Real.sqrt (Real.pi / 4) ≤ 1 := Real.sqrt_le_one.mpr h1
    nlinarith [Real.sqrt_nonneg (Real.pi / 4)]
  have hsnn : (0 : ℝ) ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * Work.FTS.EllipticEst.thEta θ) :=
    Real.sqrt_nonneg _
  calc |G w τ|
      = |G w (Real.pi / 4) + (τ - Real.pi / 4) * deriv (fun θ : ℝ => G w θ) (Real.pi / 4)
          + ∫ t in (Real.pi / 4)..τ, (τ - t) * deriv (deriv (fun θ : ℝ => G w θ)) t| := by
        rw [hT]
    _ ≤ |G w (Real.pi / 4)| + |τ - Real.pi / 4| * |deriv (fun θ : ℝ => G w θ) (Real.pi / 4)|
          + |∫ t in (Real.pi / 4)..τ, (τ - t) * deriv (deriv (fun θ : ℝ => G w θ)) t| := by
        have h1 := abs_add_le
          (G w (Real.pi / 4) + (τ - Real.pi / 4) * deriv (fun θ : ℝ => G w θ) (Real.pi / 4))
          (∫ t in (Real.pi / 4)..τ, (τ - t) * deriv (deriv (fun θ : ℝ => G w θ)) t)
        have h2 := abs_add_le (G w (Real.pi / 4))
          ((τ - Real.pi / 4) * deriv (fun θ : ℝ => G w θ) (Real.pi / 4))
        rw [abs_mul] at h2
        linarith [h1, h2]
    _ ≤ |G w (Real.pi / 4)| + 1 * |deriv (fun θ : ℝ => G w θ) (Real.pi / 4)|
          + 1 * Real.sqrt (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
        have hmul : |τ - Real.pi / 4| * |deriv (fun θ : ℝ => G w θ) (Real.pi / 4)|
            ≤ 1 * |deriv (fun θ : ℝ => G w θ) (Real.pi / 4)| :=
          mul_le_mul_of_nonneg_right habs hdnn
        have hc2 : (Real.pi / 4) * Real.sqrt (Real.pi / 4) *
              Real.sqrt (∫ θ in Work.Spaces.Iθ,
                Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * Work.FTS.EllipticEst.thEta θ)
            ≤ 1 * Real.sqrt (∫ θ in Work.Spaces.Iθ,
                Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * Work.FTS.EllipticEst.thEta θ) :=
          mul_le_mul_of_nonneg_right hcoef hsnn
        linarith [hmul, hc2, hTail]
    _ = |G w (Real.pi / 4)| + |Work.Spaces.pth G w (Real.pi / 4)|
          + Real.sqrt (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
        rw [one_mul, one_mul]
        rfl

/-- **Strip-admissibility of the approximant**: `zmoll G δ ε` is `C^∞` on the half strip
`(0,∞) × (-1, π/2+1)` and vanishes at `θ = 0, π/2`, from the trace class and the four
integrabilities of `G`.  (Same statement as `mollAdm`, assembled here from the sorry-free
`MollSmooth` pieces and the locally proved `sliceDomMFA`.) -/
theorem mollAdmMFA : ∀ (G : ℝ → ℝ → ℝ), Work.FTS.EllSol.EllPkgAux.TraceClass G →
    Work.FTS.EllSol.EllPkgAux.FourInts G → ∀ (δ ε : ℝ), Work.FTS.EllSol.EllPkgAux.Params δ ε →
      Work.FTS.EllSol.EllPkgAux.StripAdm G δ ε := by
  intro G hTC hFI δ ε hP
  obtain ⟨hεpos, hεle, hδpos, hδle⟩ := hP
  obtain ⟨hS, h0, hpi0, hlim0, hlimpi, hdz0, hdzpi, hhon⟩ := hTC
  have hdom := sliceDomMFA G hS hhon
  have hint := Work.FTS.EllSol.EllPkgAux.MollSmooth.MG_integrableOn G hS hFI
  have hloc := Work.FTS.EllSol.EllPkgAux.MollSmooth.Hxy_quad_locallyIntegrable G hS hdom hint
  refine ⟨?_, ?_, ?_⟩
  · intro n
    have hKsm : ContDiff ℝ n (Work.FTS.EllSol.EllPkgAux.Kd δ ε) :=
      Work.FTS.EllSol.EllPkgAux.Kd_contDiff δ ε n
    have hKcs : HasCompactSupport (Work.FTS.EllSol.EllPkgAux.Kd δ ε) :=
      Work.FTS.EllSol.EllPkgAux.Kd_hasCompactSupport δ ε hδpos hεpos
    have hconvsm : ContDiff ℝ n
        (MeasureTheory.convolution
          (Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G))
          (Work.FTS.EllSol.EllPkgAux.Kd δ ε)
          (ContinuousLinearMap.mul ℝ ℝ) MeasureTheory.volume) :=
      hKcs.contDiff_convolution_right (n := (n : ℕ∞))
        (ContinuousLinearMap.mul ℝ ℝ) hloc hKsm
    have hlog : ContDiffOn ℝ n (fun q : ℝ × ℝ => Real.log q.1)
        Work.FTS.EllSol.EllPkgAux.Strp := by
      have h : ContDiffOn ℝ n (Real.log ∘ Prod.fst) Work.FTS.EllSol.EllPkgAux.Strp :=
        Real.contDiffOn_log.comp contDiffOn_fst (fun q hq => by
          simp only [Work.FTS.EllSol.EllPkgAux.Strp, Set.mem_prod, Set.mem_Ioi,
            Set.mem_Ioo] at hq
          exact ne_of_gt hq.1)
      simpa only [Function.comp_def] using h
    have hmap : ContDiffOn ℝ n (fun q : ℝ × ℝ => (Real.log q.1, q.2))
        Work.FTS.EllSol.EllPkgAux.Strp :=
      hlog.prodMk contDiffOn_snd
    have hcomp : ContDiffOn ℝ n (fun q : ℝ × ℝ =>
        MeasureTheory.convolution
          (Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G))
          (Work.FTS.EllSol.EllPkgAux.Kd δ ε)
          (ContinuousLinearMap.mul ℝ ℝ) MeasureTheory.volume (Real.log q.1, q.2))
        Work.FTS.EllSol.EllPkgAux.Strp :=
      hconvsm.comp_contDiffOn hmap
    refine hcomp.congr ?_
    rintro ⟨z, θ⟩ hq
    simp only [Work.FTS.EllSol.EllPkgAux.Strp, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hq
    obtain ⟨hz, hθ1, hθ2⟩ := hq
    show Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε z θ
        = MeasureTheory.convolution
            (Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G))
            (Work.FTS.EllSol.EllPkgAux.Kd δ ε)
            (ContinuousLinearMap.mul ℝ ℝ) MeasureTheory.volume (Real.log z, θ)
    rw [← Work.FTS.EllSol.EllPkgAux.MollSmooth.zmoll_Gquad_eq_zmoll G h0 hpi0 δ ε hεpos hεle
      z θ ⟨hθ1, hθ2⟩]
    exact Work.FTS.EllSol.EllPkgAux.MollSmooth.zmoll_Gquad_eq_conv G hloc δ ε hδpos hεpos
      z θ hz
  · exact Work.FTS.EllSol.EllPkgAux.MollSmooth.zmoll_theta_zero G δ ε hεpos hεle
  · exact Work.FTS.EllSol.EllPkgAux.MollSmooth.zmoll_theta_pihalf G δ ε hεpos hεle

end MollAssem

end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.MuDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open Work.FTS.EllSol.PkgK5.K5c

set_option maxHeartbeats 4000000
set_option maxRecDepth 2000

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "σθ" => Work.FTS.EllipticEst.thEta

/-! ## The `ℝ≥0∞`-valued vocabulary of the estimate

Everything in the proof of `mollMasterUnif` is nonnegative, so the whole estimate is carried out in
`ℝ≥0∞` (`ofReal` of each kernel and each weight) and only at the very end converted back to a
Bochner statement.  The `mu`-prefixed names are local to this file family. -/

/-- `ofReal` of the square of the radial weight. -/
def muWHat (z : ℝ) : ℝ≥0∞ := ENNReal.ofReal ((Work.Spaces.w z) ^ 2)

/-- `ofReal` of the logarithmic mollification kernel. -/
def muKHat (δ z t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (sKer δ (Real.log z - t))

/-- `ofReal` of the angular three-image kernel. -/
def muJHat (ε θ s : ℝ) : ℝ≥0∞ := ENNReal.ofReal (KJ ε θ s)

/-- `ofReal` of the angular weight `sin(2θ)^{-η}`. -/
def muSigHat (θ : ℝ) : ℝ≥0∞ := ENNReal.ofReal (σθ θ)

/-- `ofReal` of the square of a slice of `X`. -/
def muXsHat (X : ℝ → ℝ → ℝ) (t s : ℝ) : ℝ≥0∞ := ENNReal.ofReal ((X (Real.exp t) s) ^ 2)

/-- The `θ`-integrated angular kernel `∫⁻_θ σ(θ) KJ ε θ s`. -/
def muBHat (ε s : ℝ) : ℝ≥0∞ := ∫⁻ θ in Iθ, muSigHat θ * muJHat ε θ s

/-- The two-kernel pairing of one slice: `∫⁻_t k δ z t (∫⁻_s KJ ε θ s (X(e^t,s))²)`. -/
def muQHat (δ ε : ℝ) (X : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ≥0∞ :=
  ∫⁻ t, muKHat δ z t * (∫⁻ s in Iθ, muJHat ε θ s * muXsHat X t s)

/-- The `w²`-weighted `σ_η`-functional of `F`, in `ℝ≥0∞`. -/
def muMHat (F : ℝ → ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Iz, muWHat z * (∫⁻ θ in Iθ, ENNReal.ofReal ((F z θ) ^ 2 * σθ θ))

/-- The `w²`-weighted two-kernel functional of `X`, in `ℝ≥0∞`. -/
def muNHat (δ ε : ℝ) (X : ℝ → ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Iz, muWHat z * (∫⁻ θ in Iθ, muSigHat θ * muQHat δ ε X z θ)

/-! ## The defining equations of the vocabulary (as rewrite rules) -/

lemma muWHat_def (z : ℝ) : muWHat z = ENNReal.ofReal ((Work.Spaces.w z) ^ 2) := rfl
lemma muKHat_def (δ z t : ℝ) : muKHat δ z t = ENNReal.ofReal (sKer δ (Real.log z - t)) := rfl
lemma muJHat_def (ε θ s : ℝ) : muJHat ε θ s = ENNReal.ofReal (KJ ε θ s) := rfl
lemma muSigHat_def (θ : ℝ) : muSigHat θ = ENNReal.ofReal (σθ θ) := rfl
lemma muXsHat_def (X : ℝ → ℝ → ℝ) (t s : ℝ) :
    muXsHat X t s = ENNReal.ofReal ((X (Real.exp t) s) ^ 2) := rfl
lemma muBHat_def (ε s : ℝ) : muBHat ε s = ∫⁻ θ in Iθ, muSigHat θ * muJHat ε θ s := rfl
lemma muQHat_def (δ ε : ℝ) (X : ℝ → ℝ → ℝ) (z θ : ℝ) : muQHat δ ε X z θ =
    ∫⁻ t, muKHat δ z t * (∫⁻ s in Iθ, muJHat ε θ s * muXsHat X t s) := rfl

/-! ## Elementary facts about the measures, the weights and the kernels -/

/-- `Iz = [0,∞)` and `(0,∞)` carry the same restricted measure. -/
lemma mu_Ioi : volume.restrict Iz = volume.restrict (Set.Ioi (0 : ℝ)) := by
  rw [Work.Spaces.Iz]
  exact (MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))).symm

lemma mu_measurable_w : Measurable Work.Spaces.w := by
  unfold Work.Spaces.w
  fun_prop

lemma mu_measurable_kHat (δ z : ℝ) : Measurable (fun t : ℝ => muKHat δ z t) := by
  unfold muKHat
  exact ENNReal.measurable_ofReal.comp
    ((Work.FTS.EllSol.K5cAux.continuous_sKer δ).measurable.comp
      (measurable_const.sub measurable_id))

lemma mu_measurable_kHat' (δ : ℝ) : Measurable (fun p : ℝ × ℝ => muKHat δ p.1 p.2) := by
  unfold muKHat
  exact ENNReal.measurable_ofReal.comp
    ((Work.FTS.EllSol.K5cAux.continuous_sKer δ).measurable.comp
      ((Real.measurable_log.comp measurable_fst).sub measurable_snd))

lemma mu_measurable_KJhat (ε : ℝ) : Measurable (fun p : ℝ × ℝ => muJHat ε p.1 p.2) := by
  unfold muJHat
  exact ENNReal.measurable_ofReal.comp (Work.FTS.EllSol.EllPkgAux.continuous_KJ ε).measurable

lemma mu_aemeasurable_sigHat : AEMeasurable muSigHat (volume.restrict Iθ) :=
  ENNReal.measurable_ofReal.comp_aemeasurable
    (Work.FTS.EllipticEst.integrableOn_thEta.1).aemeasurable

lemma mu_aemeasurable_XsHat {X : ℝ → ℝ → ℝ}
    (hXmeas : AEMeasurable (fun p : ℝ × ℝ => X (Real.exp p.1) p.2)
      (volume.prod (volume.restrict Iθ))) :
    AEMeasurable (fun p : ℝ × ℝ => muXsHat X p.1 p.2)
      (volume.prod (volume.restrict Iθ)) := by
  unfold muXsHat
  exact ENNReal.measurable_ofReal.comp_aemeasurable (hXmeas.pow_const 2)

/-- The product of the angular kernel and the slice square, as `ofReal` of the product. -/
lemma muJHat_mul_muXsHat (X : ℝ → ℝ → ℝ) (ε θ t s : ℝ) (hε : 0 < ε) :
    muJHat ε θ s * muXsHat X t s = ENNReal.ofReal (KJ ε θ s * (X (Real.exp t) s) ^ 2) := by
  rw [muJHat_def, muXsHat_def]
  exact (ENNReal.ofReal_mul (KJ_nonneg hε θ s)).symm

/-- The product of the slice square and the angular weight, as `ofReal` of the product. -/
lemma muXsHat_mul_muSigHat (X : ℝ → ℝ → ℝ) (t s : ℝ) :
    muXsHat X t s * muSigHat s = ENNReal.ofReal ((X (Real.exp t) s) ^ 2 * σθ s) := by
  rw [muXsHat_def, muSigHat_def]
  exact (ENNReal.ofReal_mul (sq_nonneg _)).symm

/-- The product of the radial weight and the log-mollification kernel, as `ofReal`. -/
lemma muWHat_mul_muKHat (δ z t : ℝ) :
    muWHat z * muKHat δ z t
      = ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * sKer δ (Real.log z - t)) := by
  rw [muWHat_def, muKHat_def]
  exact (ENNReal.ofReal_mul (sq_nonneg _)).symm

/-- The product of the angular weight and the angular kernel, as `ofReal`. -/
lemma muSigHat_mul_muJHat (ε θ s : ℝ) (hε : 0 < ε) :
    muSigHat θ * muJHat ε θ s = ENNReal.ofReal (σθ θ * KJ ε θ s) := by
  rw [muSigHat_def, muJHat_def]
  exact (ENNReal.ofReal_mul' (KJ_nonneg hε θ s)).symm

/-- `muWHat z * ofReal u = ofReal (w z² * u)`. -/
lemma muWHat_mul_ofReal (u : ℝ) (hu : 0 ≤ u) (z : ℝ) :
    muWHat z * ENNReal.ofReal u = ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * u) := by
  rw [muWHat_def]
  exact (ENNReal.ofReal_mul (sq_nonneg _)).symm

/-- The `s`-functional of `X` at fixed `t`, as `ofReal` of the honest slice functional. -/
lemma mu_VsHat_eq {X : ℝ → ℝ → ℝ}
    (hXhon : ∀ z : ℝ, 0 < z → IntegrableOn (fun θ : ℝ => (X z θ) ^ 2 * σθ θ) Iθ) (t : ℝ) :
    (∫⁻ s in Iθ, muXsHat X t s * muSigHat s) = ENNReal.ofReal (MmV X t) := by
  have hInt : IntegrableOn (fun s : ℝ => (X (Real.exp t) s) ^ 2 * σθ s) Iθ :=
    hXhon (Real.exp t) (Real.exp_pos t)
  have hnn : 0 ≤ᵐ[volume.restrict Iθ]
      (fun s : ℝ => (X (Real.exp t) s) ^ 2 * σθ s) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun s hs => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hs))
  have hfun : (fun s : ℝ => muXsHat X t s * muSigHat s)
      = fun s : ℝ => ENNReal.ofReal ((X (Real.exp t) s) ^ 2 * σθ s) := by
    funext s
    exact muXsHat_mul_muSigHat X t s
  rw [hfun]
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn).symm

/-- **The `KJ`-slice conversion.**  If `s ↦ KJ ε θ s (X(e^t,s))²` is integrable on `Iθ`, then
`ofReal` of its Bochner integral is the lintegral of `muJHat · muXsHat`. -/
lemma mu_ofReal_integral_eq_lintegral_KJ {X : ℝ → ℝ → ℝ} (ε θ t : ℝ) (hε : 0 < ε)
    (hInt : IntegrableOn (fun s : ℝ => KJ ε θ s * (X (Real.exp t) s) ^ 2) Iθ) :
    ENNReal.ofReal (∫ s in Iθ, KJ ε θ s * (X (Real.exp t) s) ^ 2)
      = ∫⁻ s in Iθ, muJHat ε θ s * muXsHat X t s := by
  refine (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt ?_).trans ?_
  · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun s _ => mul_nonneg (KJ_nonneg hε θ s) (sq_nonneg _))
  · have hfun : (fun s : ℝ => ENNReal.ofReal (KJ ε θ s * (X (Real.exp t) s) ^ 2))
        = fun s : ℝ => muJHat ε θ s * muXsHat X t s := by
      funext s
      exact (muJHat_mul_muXsHat X ε θ t s hε).symm
    rw [hfun]


/-- `ofReal u * muSigHat θ = ofReal (u * σθ θ)`. -/
lemma mu_ofReal_mul_muSigHat (u : ℝ) (hu : 0 ≤ u) (θ : ℝ) :
    ENNReal.ofReal u * muSigHat θ = ENNReal.ofReal (u * σθ θ) := by
  rw [muSigHat_def]
  exact (ENNReal.ofReal_mul hu).symm

/-- `(3 : ℝ≥0∞) ≠ ⊤`. -/
lemma mu_three_ne_top : (3 : ℝ≥0∞) ≠ ⊤ := by norm_num

/-- Squaring is monotone in `ℝ≥0∞`. -/
lemma mu_sq_le_sq {a b : ℝ≥0∞} (h : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  rw [sq, sq]
  exact mul_le_mul' h h

/-- Continuity of the angular slice `s ↦ KJ ε θ s`. -/
lemma mu_continuous_KJ_slice (ε θ : ℝ) : Continuous (fun s : ℝ => KJ ε θ s) := by
  have h1 : Continuous (fun s : ℝ => (θ, s)) := continuous_const.prodMk continuous_id
  have h2 := (Work.FTS.EllSol.EllPkgAux.continuous_KJ ε).comp h1
  have hfun : ((fun p : ℝ × ℝ => KJ ε p.1 p.2) ∘ fun s : ℝ => (θ, s)) = fun s : ℝ => KJ ε θ s := by
    funext s
    rfl
  rwa [hfun] at h2

/-! ## The two measure-theoretic tools -/

/-- For a nonnegative real function, `ofReal` of the Bochner integral is at most the lintegral of
the `ofReal`s (no integrability hypothesis needed). -/
lemma mu_ofReal_integral_le_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : 0 ≤ᵐ[μ] f) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases h : Integrable f μ
  · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal h hf]
  · rw [MeasureTheory.integral_undef h, ENNReal.ofReal_zero]
    exact zero_le

/-- **Cauchy–Schwarz in `ℝ≥0∞`** (the `√k`–`√k·g` splitting of `∫⁻ k·g`). -/
lemma mu_ofReal_cs {α : Type*} [MeasurableSpace α] {μ : Measure α} {k g : α → ℝ}
    (hk : AEMeasurable k μ) (hg : AEMeasurable g μ) (hknn : ∀ a, 0 ≤ k a)
    (hgnn : ∀ a, 0 ≤ g a) :
    (∫⁻ a, ENNReal.ofReal (k a) * ENNReal.ofReal (g a) ∂μ) ^ 2
      ≤ (∫⁻ a, ENNReal.ofReal (k a) ∂μ)
        * (∫⁻ a, ENNReal.ofReal (k a) * (ENNReal.ofReal (g a)) ^ 2 ∂μ) := by
  have hks : AEMeasurable (fun a => Real.sqrt (k a)) μ :=
    Real.continuous_sqrt.measurable.comp_aemeasurable hk
  have hf : AEMeasurable (fun a => ENNReal.ofReal (Real.sqrt (k a))) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable hks
  have hg' : AEMeasurable (fun a => ENNReal.ofReal (Real.sqrt (k a) * g a)) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hks.mul hg)
  have hhold := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (p := 2) (q := 2)
    Real.HolderConjugate.two_two hf hg'
  simp only [Pi.mul_apply] at hhold
  have hL : (∫⁻ a, (fun x => ENNReal.ofReal (Real.sqrt (k x))) a
        * (fun x => ENNReal.ofReal (Real.sqrt (k x) * g x)) a ∂μ)
      = ∫⁻ a, ENNReal.ofReal (k a) * ENNReal.ofReal (g a) ∂μ := by
    refine lintegral_congr (fun a => ?_)
    have h1 : ENNReal.ofReal (Real.sqrt (k a)) * ENNReal.ofReal (Real.sqrt (k a) * g a)
        = ENNReal.ofReal (Real.sqrt (k a) * (Real.sqrt (k a) * g a)) :=
      (ENNReal.ofReal_mul (Real.sqrt_nonneg (k a))).symm
    rw [h1, ← ENNReal.ofReal_mul (hknn a)]
    congr 1
    rw [← mul_assoc, Real.mul_self_sqrt (hknn a)]
  rw [hL] at hhold
  have hA : (∫⁻ a, (fun x => ENNReal.ofReal (Real.sqrt (k x))) a ^ (2 : ℝ) ∂μ)
      = ∫⁻ a, ENNReal.ofReal (k a) ∂μ := by
    refine lintegral_congr (fun a => ?_)
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg (k a)) (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_two, Real.sq_sqrt (hknn a)]
  have hB : (∫⁻ a, (fun x => ENNReal.ofReal (Real.sqrt (k x) * g x)) a ^ (2 : ℝ) ∂μ)
      = ∫⁻ a, ENNReal.ofReal (k a) * (ENNReal.ofReal (g a)) ^ 2 ∂μ := by
    refine lintegral_congr (fun a => ?_)
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (Real.sqrt_nonneg (k a)) (hgnn a))
        (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two, mul_pow, Real.sq_sqrt (hknn a)]
    rw [← ENNReal.ofReal_pow (hgnn a) 2, ← ENNReal.ofReal_mul (hknn a)]
  rw [hA, hB] at hhold
  calc (∫⁻ a, ENNReal.ofReal (k a) * ENNReal.ofReal (g a) ∂μ) ^ 2
      ≤ ((∫⁻ a, ENNReal.ofReal (k a) ∂μ) ^ (1 / 2 : ℝ)
          * (∫⁻ a, ENNReal.ofReal (k a) * (ENNReal.ofReal (g a)) ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by
        rw [sq, sq]
        exact mul_le_mul' hhold hhold
    _ = (∫⁻ a, ENNReal.ofReal (k a) ∂μ)
          * (∫⁻ a, ENNReal.ofReal (k a) * (ENNReal.ofReal (g a)) ^ 2 ∂μ) := by
        rw [mul_pow]
        congr 1
        · rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
            show (1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, ENNReal.rpow_one]
        · rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
            show (1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, ENNReal.rpow_one]

/-- The logarithmic kernel has total mass `1` in `ℝ≥0∞`. -/
lemma mu_kHat_lintegral_one (δ : ℝ) (hδ : 0 < δ) (z : ℝ) :
    ∫⁻ t, muKHat δ z t = 1 := by
  have hint : Integrable (fun t : ℝ => sKer δ (Real.log z - t)) volume :=
    Work.FTS.EllSol.EllPkgAux.lj_sKer_integrable_sub hδ (Real.log z)
  have hnn : 0 ≤ᵐ[volume] (fun t : ℝ => sKer δ (Real.log z - t)) :=
    Eventually.of_forall (fun t => sKer_nonneg hδ _)
  have h1 : (∫⁻ t, ENNReal.ofReal (sKer δ (Real.log z - t)))
      = ENNReal.ofReal (∫ t, sKer δ (Real.log z - t)) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn).symm
  have h2 : (∫ t, sKer δ (Real.log z - t)) = 1 :=
    Work.FTS.EllSol.EllPkgAux.lj_sKer_integral_sub δ hδ (Real.log z)
  simp only [muKHat]
  rw [h1, h2, ENNReal.ofReal_one]

end Work.FTS.EllSol.EllPkgAux.MollDom
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.abs_interval_integral_le_sqrt_thEta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

theorem abs_interval_integral_le_sqrt_thEta {h : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn h (Set.uIcc a b))
    (hint : MeasureTheory.IntegrableOn (fun θ : ℝ => h θ ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < Real.pi / 2) (hlen : b - a ≤ Real.pi / 4) :
    |∫ t in a..b, h t|
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, h θ ^ 2 * Work.FTS.EllipticEst.thEta θ)
        * Real.sqrt (Real.pi / 4) := by
  -- On `[a,b] ⊆ (0, π/2)` the weight satisfies `thEta ≥ 1`, so `∫_a^b h² ≤ ∫_Iθ h²·thEta`
  -- (`interval_sq_le_Itheta`), and the interval length is at most `π/4`.
  have hcontIcc : ContinuousOn h (Set.Icc a b) := by rwa [Set.uIcc_of_le hab] at hcont
  have hint2 : MeasureTheory.IntegrableOn (fun x : ℝ => h x ^ 2) (Set.Icc a b) :=
    (hcontIcc.pow 2).integrableOn_compact isCompact_Icc
  -- Cauchy–Schwarz for the interval integral of `h` against the constant `1`.
  have hcs :=
    Work.FTS.EllSol.VthAux.endpoint.abs_integral_le_sqrt_mul_sqrt hab hcontIcc hint2
  have hmono : ∫ x in a..b, h x ^ 2
      ≤ ∫ θ in Work.Spaces.Iθ, h θ ^ 2 * Work.FTS.EllipticEst.thEta θ :=
    Work.FTS.EllSol.EllPkgAux.MollDom.interval_sq_le_Itheta hint ha hab hb
  have hsqrt1 : Real.sqrt (∫ x in a..b, h x ^ 2)
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, h θ ^ 2 * Work.FTS.EllipticEst.thEta θ) :=
    Real.sqrt_le_sqrt hmono
  have hsqrt2 : Real.sqrt (b - a) ≤ Real.sqrt (Real.pi / 4) := Real.sqrt_le_sqrt hlen
  have hstep : Real.sqrt (b - a) * Real.sqrt (∫ x in a..b, h x ^ 2)
      ≤ Real.sqrt (Real.pi / 4)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, h θ ^ 2 * Work.FTS.EllipticEst.thEta θ) :=
    mul_le_mul hsqrt2 hsqrt1 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc |∫ t in a..b, h t|
      ≤ Real.sqrt (b - a) * Real.sqrt (∫ x in a..b, h x ^ 2) := hcs
    _ ≤ Real.sqrt (Real.pi / 4)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, h θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := hstep
    _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, h θ ^ 2 * Work.FTS.EllipticEst.thEta θ)
          * Real.sqrt (Real.pi / 4) := by rw [mul_comm]

end Work.FTS.EllSol.EllPkgAux.MollDom
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.integrable_sKer_slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

set_option linter.unusedVariables false

open MeasureTheory Set Filter
open scoped Real Topology

/-!
# Integrability of the logarithmic slice of the mollification kernel

The mollification `zmoll` of the datum `X` in the logarithmic radial variable convolves the
`σ_η`-weighted angular slice functional against the kernel `sKer δ (log z - t)`.  This file
proves that this is legitimate, i.e. that the slice is integrable as soon as the weighted
slice functional is integrable on `Iz`:

`Integrable (fun t => sKer δ (log z - t) * ∫_{Iθ} X (e^t) s² σ_η(s) ds)`.

The proof is a three-line reduction.

* `sKer δ` is supported in `[-δ, δ]`, so the `t`-integrand lives on the compact interval
  `[log z - δ, log z + δ]`; it therefore suffices to prove integrability there and to glue
  with `MeasureTheory.integrableOn_iff_integrable_of_support_subset`.
* on a compact subinterval `[a, b]` of `(0, ∞)` the weight `w` is bounded below, so the
  hypothesis `IntegrableOn (w z ² ∫_{Iθ} X z s² σ_η s) Iz` gives integrability of the raw
  slice functional `F u = ∫_{Iθ} X u s² σ_η s` there (multiply by the continuous factor
  `(w · ²)⁻¹`);
* the change of variables `u = e^t` (`integrableOn_exp_comp`) converts that into integrability
  of `t ↦ F (e^t)`, and `sKer δ (log z - ·)` is continuous, so
  `IntegrableOn.mul_continuousOn` finishes.
-/

theorem integrable_sKer_slice {X : ℝ → ℝ → ℝ}
    (hX : ContinuousOn (Function.uncurry X) Work.FTS.EllipticEst.Q0)
    {δ z : ℝ} (hδ : 0 < δ) (hz : 0 < z)
    (hdd : MeasureTheory.IntegrableOn (fun u : ℝ => (Work.Spaces.w u) ^ 2 *
      (∫ s in Work.Spaces.Iθ, X u s ^ 2 * Work.FTS.EllipticEst.thEta s)) Work.Spaces.Iz) :
    MeasureTheory.Integrable (fun t : ℝ =>
      Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t) *
        (∫ s in Work.Spaces.Iθ, X (Real.exp t) s ^ 2 * Work.FTS.EllipticEst.thEta s))
      MeasureTheory.volume := by
  -- ### Step 1: the raw slice functional is integrable on compact subintervals of `(0,∞)`
  have hFint : ∀ a b : ℝ, 0 < a → a ≤ b →
      MeasureTheory.IntegrableOn (fun u : ℝ =>
        ∫ s in Work.Spaces.Iθ, X u s ^ 2 * Work.FTS.EllipticEst.thEta s) (Set.Icc a b) := by
    intro a b ha _hab
    -- restrict the hypothesis to the compact subinterval
    have hsub : Set.Icc a b ⊆ Work.Spaces.Iz := by
      intro u hu
      exact le_of_lt (lt_of_lt_of_le ha hu.1)
    have h1 := hdd.mono_set hsub
    -- the weight `w²` does not vanish on `[a,b]` (`a > 0`)
    have hw2 : ∀ u ∈ Set.Icc a b, (Work.Spaces.w u) ^ 2 ≠ 0 := by
      intro u hu
      have hu0 : 0 < u := lt_of_lt_of_le ha hu.1
      have hw : Work.Spaces.w u ≠ 0 := by
        rw [Work.Spaces.w]
        exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hu0))
      exact pow_ne_zero 2 hw
    -- hence `(w · ²)⁻¹` is continuous there and we may divide
    have hwcont : ContinuousOn (fun u : ℝ => ((Work.Spaces.w u) ^ 2)⁻¹) (Set.Icc a b) := by
      refine ContinuousOn.inv₀ ?_ hw2
      refine ContinuousOn.pow ?_ 2
      have hw : Work.Spaces.w = fun u : ℝ => (1 + u) ^ 2 / u ^ 2 := rfl
      rw [hw]
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
        (continuousOn_id.pow 2) ?_
      intro u hu
      exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le ha hu.1))
    have h2 := h1.mul_continuousOn hwcont isCompact_Icc
    refine h2.congr_fun (fun u hu => ?_) measurableSet_Icc
    have h0 := hw2 u hu
    show (Work.Spaces.w u ^ 2 *
          (∫ s in Work.Spaces.Iθ, X u s ^ 2 * Work.FTS.EllipticEst.thEta s))
        * (Work.Spaces.w u ^ 2)⁻¹
      = ∫ s in Work.Spaces.Iθ, X u s ^ 2 * Work.FTS.EllipticEst.thEta s
    rw [show (Work.Spaces.w u ^ 2 *
            (∫ s in Work.Spaces.Iθ, X u s ^ 2 * Work.FTS.EllipticEst.thEta s))
          * (Work.Spaces.w u ^ 2)⁻¹
        = (∫ s in Work.Spaces.Iθ, X u s ^ 2 * Work.FTS.EllipticEst.thEta s)
          * ((Work.Spaces.w u ^ 2) * (Work.Spaces.w u ^ 2)⁻¹) from by ring,
      mul_inv_cancel₀ h0, mul_one]
  -- ### Step 2: change variables `u = exp t`
  have hexp := integrableOn_exp_comp hFint (Real.log z - δ) (Real.log z + δ)
  -- ### Step 3: multiply by the (continuous) compactly supported kernel
  have hKcont : ContinuousOn (fun t : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t))
      (Set.Icc (Real.log z - δ) (Real.log z + δ)) :=
    ((Work.FTS.EllSol.K5cAux.continuous_sKer δ).comp
      (continuous_const.sub continuous_id)).continuousOn
  have hInt := hexp.mul_continuousOn hKcont isCompact_Icc
  have hInt' : MeasureTheory.IntegrableOn (fun t : ℝ =>
      Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t) *
        (∫ s in Work.Spaces.Iθ, X (Real.exp t) s ^ 2 * Work.FTS.EllipticEst.thEta s))
      (Set.Icc (Real.log z - δ) (Real.log z + δ)) :=
    hInt.congr_fun (fun t _ => mul_comm _ _) measurableSet_Icc
  -- ### Step 4: the integrand vanishes off the support of the kernel
  have hsup : Function.support (fun t : ℝ =>
      Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t) *
        (∫ s in Work.Spaces.Iθ, X (Real.exp t) s ^ 2 * Work.FTS.EllipticEst.thEta s))
      ⊆ Set.Icc (Real.log z - δ) (Real.log z + δ) := by
    intro t ht
    have hmul := Function.mem_support.mp ht
    have hK0 : Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t) ≠ 0 :=
      fun h0 => hmul (by rw [h0, zero_mul])
    have habs : |Real.log z - t| < δ := by
      by_contra hle
      exact hK0 (Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ (not_lt.mp hle))
    rw [Set.mem_Icc]
    rw [abs_lt] at habs
    exact ⟨by linarith [habs.2], by linarith [habs.1]⟩
  exact (integrableOn_iff_integrable_of_support_subset hsup).mp hInt'

end Work.FTS.EllSol.EllPkgAux.MollDom
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.schur_sq_window_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom


end Work.FTS.EllSol.EllPkgAux.MollDom
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDzAux.zmollKernel_hasDerivAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDzAux

open scoped Real Topology
open MeasureTheory Set Filter

theorem zmollKernel_hasDerivAt {H : ℝ → ℝ} (hH : MeasureTheory.LocallyIntegrable H MeasureTheory.volume)
    {δ M : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hM : ∀ x : ℝ, |Work.FTS.EllSol.EllPkgAux.sKerd δ x| ≤ M) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' : ℝ => ∫ t : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z' - t) * H t)
      (z⁻¹ * ∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) * H t) z := by
  -- The fixed interval `[a, b]` in the logarithmic variable on which the kernel lives.
  set a : ℝ := Real.log z - 2 with ha
  set b : ℝ := Real.log z + 2 with hb
  have hab : a ≤ b := by rw [ha, hb]; linarith
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM (Real.log z))
  -- The window of `x` around `z` on which `log x - log z` varies by less than `1/2`.
  set s : Set ℝ := Set.Ioo (z / 2) (2 * z) with hs
  have hz2 : (0 : ℝ) < z / 2 := by linarith
  have hs_nhds : s ∈ 𝓝 z := by
    rw [hs]; exact Ioo_mem_nhds (by linarith) (by linarith)
  have hs_pos : ∀ x ∈ s, 0 < x := by
    intro x hx; rw [hs] at hx; linarith [hx.1, hz]
  have hlog2 : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (x := 2) (by norm_num) (by norm_num)
    norm_num at h; exact h
  have hlog_lt : ∀ x ∈ s, Real.log x < Real.log z + 1 := by
    intro x hx
    have hx0 : 0 < x := hs_pos x hx
    have hlt : x < 2 * z := by rw [hs] at hx; exact hx.2
    have h1 : Real.log x < Real.log (2 * z) := Real.log_lt_log hx0 hlt
    have h2 : Real.log (2 * z) = Real.log 2 + Real.log z :=
      Real.log_mul (by norm_num) (ne_of_gt hz)
    linarith
  have hlog_gt : ∀ x ∈ s, Real.log z - 1 < Real.log x := by
    intro x hx
    have h1 : Real.log (z / 2) < Real.log x :=
      Real.log_lt_log hz2 (by rw [hs] at hx; exact hx.1)
    have h2 : Real.log (z / 2) = Real.log z - Real.log 2 :=
      Real.log_div (ne_of_gt hz) (by norm_num)
    linarith
  -- Vanishing of the two kernels far from the window.
  have hker_van : ∀ (x t : ℝ), x ∈ s → t ∉ Set.Ioc a b →
      Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log x - t) = 0 := by
    intro x t hx ht
    have hgt : Real.log z - 1 < Real.log x := hlog_gt x hx
    have hlt : Real.log x < Real.log z + 1 := hlog_lt x hx
    by_cases h : t ≤ a
    · have h2 : 1 ≤ Real.log x - t := by rw [ha] at h; linarith
      exact Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ0
        (by rw [abs_of_nonneg (by linarith)]; linarith)
    · have hbt : b < t := by
        by_contra hc
        exact ht ⟨lt_of_not_ge h, le_of_not_gt hc⟩
      have h2 : 1 ≤ t - Real.log x := by rw [hb] at hbt; linarith
      exact Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ0
        (by rw [abs_of_nonpos (by linarith)]; linarith)
  have hkerd_van : ∀ t : ℝ, t ∉ Set.Ioc a b →
      Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) = 0 := by
    intro t ht
    by_cases h : t ≤ a
    · have h2 : 1 < Real.log z - t := by rw [ha] at h; linarith
      exact sKerd_eq_zero_of_lt_abs hδ0
        (by rw [abs_of_nonneg (by linarith)]; linarith)
    · have hbt : b < t := by
        by_contra hc
        exact ht ⟨lt_of_not_ge h, le_of_not_gt hc⟩
      have h2 : 1 < t - Real.log z := by rw [hb] at hbt; linarith
      exact sKerd_eq_zero_of_lt_abs hδ0
        (by rw [abs_of_nonpos (by linarith)]; linarith)
  -- Interval integrability of the datum.
  have hsub : Set.uIoc a b ⊆ Set.Icc a b := by
    rw [Set.uIoc_of_le hab]; exact fun t ht => ⟨le_of_lt ht.1, ht.2⟩
  have hF_int : IntervalIntegrable
      (fun t : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t) * H t) volume a b := by
    rw [intervalIntegrable_iff]
    have hcont : ContinuousOn (fun t : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t))
        (Set.Icc a b) :=
      (((Work.FTS.EllSol.EllPkgAux.contDiff_sKer δ (n := 1)).continuous).comp
        (continuous_const.sub continuous_id)).continuousOn
    have hH_Icc : IntegrableOn H (Set.Icc a b) volume :=
      (hH.locallyIntegrableOn (Set.Icc a b)).integrableOn_isCompact isCompact_Icc
    have hprod : IntegrableOn
        (fun t : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t) * H t)
        (Set.Icc a b) volume :=
      MeasureTheory.IntegrableOn.continuousOn_mul hcont hH_Icc isCompact_Icc
    exact hprod.mono_set hsub
  -- Interval integrability of the dominating function.
  have hbound_int : IntervalIntegrable (fun t : ℝ => M * (2 * z⁻¹) * |H t|) volume a b := by
    rw [intervalIntegrable_iff]
    have h1 : IntegrableOn (fun t : ℝ => M * (2 * z⁻¹) * |H t|) (Set.Icc a b) volume := by
      have h2 : IntegrableOn (fun t : ℝ => ‖H t‖) (Set.Icc a b) volume :=
        (hH.locallyIntegrableOn (Set.Icc a b)).norm.integrableOn_isCompact isCompact_Icc
      have h3 : Integrable (fun t : ℝ => M * (2 * z⁻¹) * |H t|)
          (volume.restrict (Set.Icc a b)) := by
        have h4 := h2.const_mul (M * (2 * z⁻¹))
        simpa [Real.norm_eq_abs] using h4
      exact h3
    exact h1.mono_set hsub
  -- The main differentiation under the integral sign.
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := a) (b := b) (x₀ := z)
    (F := fun x t : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log x - t) * H t)
    (F' := fun x t : ℝ => (x⁻¹ * Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log x - t)) * H t)
    (bound := fun t : ℝ => M * (2 * z⁻¹) * |H t|)
    (s := s) hs_nhds
    (by
      refine Filter.Eventually.of_forall fun x => ?_
      have hcont : Continuous
          (fun t : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log x - t)) :=
        ((Work.FTS.EllSol.EllPkgAux.contDiff_sKer δ (n := 1)).continuous).comp
          (continuous_const.sub continuous_id)
      exact hcont.aestronglyMeasurable.mul
        (hH.locallyIntegrableOn (Set.uIoc a b)).aestronglyMeasurable)
    hF_int
    (by
      have hcont : Continuous
          (fun t : ℝ => z⁻¹ * Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t)) :=
        continuous_const.mul ((continuous_sKerd δ).comp (continuous_const.sub continuous_id))
      exact hcont.aestronglyMeasurable.mul
        (hH.locallyIntegrableOn (Set.uIoc a b)).aestronglyMeasurable)
    (by
      refine Filter.Eventually.of_forall fun t _ x hx => ?_
      have hx0 : 0 < x := hs_pos x hx
      have hxinv : x⁻¹ ≤ 2 * z⁻¹ := by
        have h1 : (1 : ℝ) / x ≤ 1 / (z / 2) :=
          one_div_le_one_div_of_le hz2 (by rw [hs] at hx; linarith [hx.1])
        have h2 : (1 : ℝ) / (z / 2) = 2 * z⁻¹ := by rw [one_div, inv_div]; ring
        simpa [one_div, h2] using h1
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hx0)]
      calc x⁻¹ * |Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log x - t)| * |H t|
          ≤ (2 * z⁻¹) * M * |H t| := by
            refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
            exact mul_le_mul hxinv (hM _) (abs_nonneg _) (by positivity)
        _ = M * (2 * z⁻¹) * |H t| := by ring)
    hbound_int
    (by
      refine Filter.Eventually.of_forall fun t _ x hx => ?_
      have hx0 : 0 < x := hs_pos x hx
      have hker : HasDerivAt (fun y : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log y - t))
          (Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log x - t) * x⁻¹) x := by
        have h1 : HasDerivAt (Work.FTS.EllSol.PkgK5.K5c.sKer δ)
            (Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log x - t)) (Real.log x - t) := by
          simpa [Work.FTS.EllSol.EllPkgAux.sKerd] using
            (((Work.FTS.EllSol.EllPkgAux.contDiff_sKer δ (n := 1)).differentiable_one
              (Real.log x - t)).hasDerivAt)
        have h2 := h1.comp x ((Real.hasDerivAt_log (ne_of_gt hx0)).sub_const t)
        simpa [Function.comp_def] using h2
      have h3 := hker.mul_const (H t)
      refine h3.congr_deriv ?_
      ring)
  -- Transfer to the integral over `ℝ`.
  have key2 : HasDerivAt (fun x : ℝ => ∫ t : ℝ,
      Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log x - t) * H t)
      (∫ t in a..b, (z⁻¹ * Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t)) * H t) z := by
    refine (Filter.EventuallyEq.hasDerivAt_iff ?_).mpr key.2
    filter_upwards [hs_nhds] with x hx
    rw [intervalIntegral.integral_of_le hab]
    refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
    intro t ht
    rw [hker_van x t hx ht, zero_mul]
  -- Identification of the derivative.
  have hval : (∫ t in a..b,
        (z⁻¹ * Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t)) * H t)
      = z⁻¹ * ∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) * H t := by
    have s1 : (∫ t in a..b,
          (z⁻¹ * Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t)) * H t)
        = ∫ t in a..b,
            z⁻¹ * (Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) * H t) := by
      refine intervalIntegral.integral_congr ?_
      intro t _
      ring
    have s2 : (∫ t in a..b,
          z⁻¹ * (Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) * H t))
        = z⁻¹ * ∫ t in a..b, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) * H t :=
      intervalIntegral.integral_const_mul z⁻¹ _
    have s3 : (∫ t in a..b, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) * H t)
        = ∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) * H t := by
      rw [intervalIntegral.integral_of_le hab]
      exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun t ht => by rw [hkerd_van t ht, zero_mul])
    rw [s1, s2, s3]
  exact key2.congr_deriv hval

end Work.FTS.EllSol.EllPkgAux.MollDzAux
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.ibp_kern_first =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux


end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.ibp_kern_second =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux


end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.mollAdm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux

theorem mollAdm : ∀ (G : ℝ → ℝ → ℝ), Work.FTS.EllSol.EllPkgAux.TraceClass G → Work.FTS.EllSol.EllPkgAux.FourInts G → ∀ (δ ε : ℝ), Work.FTS.EllSol.EllPkgAux.Params δ ε → Work.FTS.EllSol.EllPkgAux.StripAdm G δ ε := by
  intro G hTC hFI δ ε hP
  obtain ⟨hεpos, hεle, hδpos, hδle⟩ := hP
  obtain ⟨hS, h0, hpi0, hlim0, hlimpi, hdz0, hdzpi, hhon⟩ := hTC
  have hdom := Work.FTS.EllSol.EllPkgAux.MollSmooth.sliceDom G hS hhon
  have hint := Work.FTS.EllSol.EllPkgAux.MollSmooth.MG_integrableOn G hS hFI
  have hloc := Work.FTS.EllSol.EllPkgAux.MollSmooth.Hxy_quad_locallyIntegrable G hS hdom hint
  refine ⟨?_, ?_, ?_⟩
  · intro n
    have hKsm : ContDiff ℝ n (Kd δ ε) := Kd_contDiff δ ε n
    have hKcs : HasCompactSupport (Kd δ ε) := Kd_hasCompactSupport δ ε hδpos hεpos
    have hconvsm : ContDiff ℝ n
        (MeasureTheory.convolution (Hxy (Gquad G)) (Kd δ ε)
          (ContinuousLinearMap.mul ℝ ℝ) MeasureTheory.volume) :=
      hKcs.contDiff_convolution_right (n := (n : ℕ∞))
        (ContinuousLinearMap.mul ℝ ℝ) hloc hKsm
    have hlog : ContDiffOn ℝ n (fun q : ℝ × ℝ => Real.log q.1) Strp := by
      have h : ContDiffOn ℝ n (Real.log ∘ Prod.fst) Strp :=
        Real.contDiffOn_log.comp contDiffOn_fst (fun q hq => by
          simp only [Strp, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hq
          exact ne_of_gt hq.1)
      simpa only [Function.comp_def] using h
    have hmap : ContDiffOn ℝ n (fun q : ℝ × ℝ => (Real.log q.1, q.2)) Strp :=
      hlog.prodMk contDiffOn_snd
    have hcomp : ContDiffOn ℝ n (fun q : ℝ × ℝ =>
        MeasureTheory.convolution (Hxy (Gquad G)) (Kd δ ε)
          (ContinuousLinearMap.mul ℝ ℝ) MeasureTheory.volume (Real.log q.1, q.2)) Strp :=
      hconvsm.comp_contDiffOn hmap
    refine hcomp.congr ?_
    rintro ⟨z, θ⟩ hq
    simp only [Strp, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hq
    obtain ⟨hz, hθ1, hθ2⟩ := hq
    show Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε z θ
        = MeasureTheory.convolution (Hxy (Gquad G)) (Kd δ ε)
            (ContinuousLinearMap.mul ℝ ℝ) MeasureTheory.volume (Real.log z, θ)
    rw [← Work.FTS.EllSol.EllPkgAux.MollSmooth.zmoll_Gquad_eq_zmoll G h0 hpi0 δ ε hεpos hεle
      z θ ⟨hθ1, hθ2⟩]
    exact Work.FTS.EllSol.EllPkgAux.MollSmooth.zmoll_Gquad_eq_conv G hloc δ ε hδpos hεpos
      z θ hz
  · exact Work.FTS.EllSol.EllPkgAux.MollSmooth.zmoll_theta_zero G δ ε hεpos hεle
  · exact Work.FTS.EllSol.EllPkgAux.MollSmooth.zmoll_theta_pihalf G δ ε hεpos hεle

end Work.FTS.EllSol.EllPkgAux
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.mollHon =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

/-!
# `mollHon` — a.e. strong measurability of the approximant's slice integrand

`mollHon` is the measurability half of the Fatou step of the mollification transfer
(`mollFatou`): the slice integrand

`θ ↦ (D_z∂_θ Φ(z,θ))² σ_η(θ)`,   `Φ = zmoll G t t`,

is a.e. strongly measurable on `Iθ`, *given* the identity `hid` that rewrites `D_z∂_θΦ` as the
double convolution of the datum `G` against the derivative kernels `sKerd t`.

The point of the lemmas below is that the datum `G` is only assumed `C^∞` on the **open**
quadrant `Q0` (`SmoothOpen G`): its values on the angular boundary lines `θ = 0, π/2` and
outside the closed quadrant are junk and need never enter.  We therefore

* replace `G` by its trivial extension `Kq G` off `Q0` (measurable, by
  `ContinuousOn.measurable_piecewise`), and
* replace the doubly-odd extension `Qext G (exp t') ·` of `Hxyc` by the branch function `Hm G`,
  which is *globally* measurable and agrees with `Qext G (exp t') ·` wherever the kernel
  `sKerd t (θ - ·)` is non-zero, for `θ ∈ Iθ` and `t ≤ 1/2` (up to the null set `{0, π/2}`).

Then two applications of Fubini's measurability theorem
(`MeasureTheory.AEStronglyMeasurable.integral_prod_right'`) give the a.e. strong measurability
of the double convolution, and `hid` transfers it to the slice integrand.
-/

/-- The trivial extension of the datum to the whole plane: the datum on the open quadrant, zero
elsewhere.  Its only role is to make the angular integrand of the two convolutions *globally*
measurable. -/
def Kq (G : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => if 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2 then G p.1 p.2 else 0

theorem measurable_Kq (G : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen G) :
    Measurable (Kq G) := by
  classical
  have h := ContinuousOn.measurable_piecewise (f := Function.uncurry G)
    (g := fun _ : ℝ × ℝ => (0 : ℝ)) hS.continuousOn continuousOn_const
    Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  convert h using 1
  funext p
  unfold Kq Set.piecewise Function.uncurry
  by_cases hp : 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2
  · rw [if_pos hp, if_pos (Work.FTS.EllipticEst.mem_Q0.mpr hp)]
  · rw [if_neg hp, if_neg (fun hh => hp (Work.FTS.EllipticEst.mem_Q0.mp hh))]

/-- The branch function replacing the doubly-odd extension `Qext G (exp t') s` in the angular
convolution: on `s < 0` it is the reflected branch `-G (exp t') (-s)`, on `0 ≤ s ≤ π/2` the
datum itself and on `s > π/2` the second reflected branch `-G (exp t') (π - s)`, each read
through the trivial extension `Kq G` of the datum. -/
def Hm (G : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p =>
    if p.2 < 0 then -Kq G (Real.exp p.1, -p.2)
    else if p.2 ≤ Real.pi / 2 then Kq G (Real.exp p.1, p.2)
    else -Kq G (Real.exp p.1, Real.pi - p.2)

theorem measurable_Hm (G : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen G) :
    Measurable (Hm G) := by
  have hK : Measurable (Kq G) := measurable_Kq G hS
  have hA : Measurable (fun p : ℝ × ℝ => -Kq G (Real.exp p.1, -p.2)) :=
    Measurable.neg (hK.comp ((Real.continuous_exp.comp continuous_fst).prodMk
      continuous_snd.neg).measurable)
  have hB : Measurable (fun p : ℝ × ℝ => Kq G (Real.exp p.1, p.2)) :=
    hK.comp ((Real.continuous_exp.comp continuous_fst).prodMk continuous_snd).measurable
  have hC : Measurable (fun p : ℝ × ℝ => -Kq G (Real.exp p.1, Real.pi - p.2)) :=
    Measurable.neg (hK.comp ((Real.continuous_exp.comp continuous_fst).prodMk
      (continuous_const.sub continuous_snd)).measurable)
  have hinner : Measurable (fun p : ℝ × ℝ =>
      if p.2 ≤ Real.pi / 2 then Kq G (Real.exp p.1, p.2)
      else -Kq G (Real.exp p.1, Real.pi - p.2)) :=
    Measurable.ite (measurableSet_le measurable_snd measurable_const) hB hC
  have houter : Measurable (fun p : ℝ × ℝ =>
      if p.2 < 0 then -Kq G (Real.exp p.1, -p.2)
      else if p.2 ≤ Real.pi / 2 then Kq G (Real.exp p.1, p.2)
      else -Kq G (Real.exp p.1, Real.pi - p.2)) :=
    Measurable.ite (measurableSet_lt measurable_snd measurable_const) hA hinner
  unfold Hm
  exact houter

/-- **The angular integrands of `Hxyc` and of `Hm` have the same convolution integral.**
For `θ ∈ Iθ` and any `t'`, the two `s`-integrands agree except on the null set `{0, π/2}`:
off the kernel window `|θ - s| ≤ t` the factor `sKerd t (θ - s)` vanishes, and inside it every
argument at which `Kq G` is evaluated lies in the open quadrant, where `Kq G` is the datum and
the branches of `Qext` reproduce the three cases of `Hm G`. -/
theorem sKerd_mul_Hxyc_eq_Hm (G : ℝ → ℝ → ℝ)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 2) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (t' : ℝ) :
    ∫ s : ℝ, sKerd t (θ - s) * Hxyc G t' s
      = ∫ s : ℝ, sKerd t (θ - s) * Hm G (t', s) := by
  have key : ∀ s : ℝ, s ≠ 0 → s ≠ Real.pi / 2 →
      sKerd t (θ - s) * Hxyc G t' s = sKerd t (θ - s) * Hm G (t', s) := by
    intro s hs0 hspi
    by_cases hk : sKerd t (θ - s) = 0
    · rw [hk, zero_mul, zero_mul]
    · have hwin : |θ - s| ≤ t := by
        by_contra hlt
        exact hk (MollDzAux.sKerd_eq_zero_of_lt_abs ht0 (lt_of_not_ge hlt))
      have hb : -t ≤ θ - s ∧ θ - s ≤ t := abs_le.mp hwin
      obtain ⟨hθ0, hθ1⟩ := Set.mem_Icc.mp hθ
      have hpt : Hxyc G t' s = Hm G (t', s) := by
        rcases lt_trichotomy s 0 with hs | hs | hs
        · have hmem : 0 < -s ∧ -s < Real.pi / 2 :=
            ⟨by linarith, by linarith [hb.2, ht1, Real.pi_gt_three]⟩
          have hKq : Kq G (Real.exp t', -s) = G (Real.exp t') (-s) := by
            unfold Kq
            rw [if_pos ⟨Real.exp_pos t', hmem.1, hmem.2⟩]
          unfold Hxyc Hm
          rw [if_pos hs, MollDzAux.Qext_of_lt_zero G (Real.exp t') s hs, hKq]
        · exact absurd hs hs0
        · by_cases hsle : s ≤ Real.pi / 2
          · have hmem : 0 < s ∧ s < Real.pi / 2 := ⟨hs, lt_of_le_of_ne hsle hspi⟩
            have hKq : Kq G (Real.exp t', s) = G (Real.exp t') s := by
              unfold Kq
              rw [if_pos ⟨Real.exp_pos t', hmem.1, hmem.2⟩]
            unfold Hxyc Hm
            rw [if_neg (not_lt.mpr (le_of_lt hs)), if_pos hsle,
              Work.FTS.EllSol.PkgK5.K5c.Qext_of_mem G (Real.exp t') s ⟨le_of_lt hs, hsle⟩,
              hKq]
          · have hmem : 0 < Real.pi - s ∧ Real.pi - s < Real.pi / 2 :=
              ⟨by linarith [hb.1, hθ1, ht1, Real.pi_gt_three], by linarith⟩
            have hKq : Kq G (Real.exp t', Real.pi - s) = G (Real.exp t') (Real.pi - s) := by
              unfold Kq
              rw [if_pos ⟨Real.exp_pos t', hmem.1, hmem.2⟩]
            unfold Hxyc Hm
            rw [if_neg (not_lt.mpr (le_of_lt hs)), if_neg hsle,
              MollDzAux.Qext_of_pihalf_lt G (Real.exp t') s (not_le.mp hsle), hKq]
      rw [hpt]
  refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_iff.mpr ?_)
  refine measure_mono_null ?_ (Set.Finite.measure_zero
    ((Set.finite_singleton (Real.pi / 2)).insert 0) volume)
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  by_contra hcon
  push_neg at hcon
  exact hs (key s hcon.1 hcon.2)

theorem mollHon (G : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen G) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1 / 2) (z : ℝ) (hz : 0 < z) (hid : ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ → Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G t t)) z θ = ∫ t' : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd t (Real.log z - t') * (∫ s : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd t (θ - s) * Work.FTS.EllSol.EllPkgAux.Hxyc G t' s)) : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G t t)) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  set μθ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict Work.Spaces.Iθ with hμθ
  -- the angular weight `σ_η` is a.e. strongly measurable on `Iθ`
  have hth : MeasureTheory.AEStronglyMeasurable Work.FTS.EllipticEst.thEta μθ := by
    have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)
    have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * θ) ≠ 0 := by
      intro θ hθ
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos]))
    have hcont : ContinuousOn Work.FTS.EllipticEst.thEta (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      change ContinuousOn (fun θ : ℝ => Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
        (Set.Ioo (0 : ℝ) (Real.pi / 2))
      exact hsin.rpow_const (fun θ hθ => Or.inl (hne θ hθ))
    have hrest : MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) = μθ := by
      rw [hμθ]
      exact Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc
        (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (a := 0) (b := Real.pi / 2))
    rw [← hrest]
    exact hcont.aestronglyMeasurable measurableSet_Ioo
  -- the whole triple integrand is globally measurable
  have hf : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      sKerd t (Real.log z - p.1.2) * (sKerd t (p.1.1 - p.2) * Hm G (p.1.2, p.2))) := by
    have h1 : Measurable (fun p : (ℝ × ℝ) × ℝ => sKerd t (Real.log z - p.1.2)) :=
      (MollDzAux.continuous_sKerd t).measurable.comp
        (continuous_const.sub (continuous_snd.comp continuous_fst)).measurable
    have h2 : Measurable (fun p : (ℝ × ℝ) × ℝ => sKerd t (p.1.1 - p.2)) :=
      (MollDzAux.continuous_sKerd t).measurable.comp
        ((continuous_fst.comp continuous_fst).sub continuous_snd).measurable
    have h3 : Measurable (fun p : (ℝ × ℝ) × ℝ => Hm G (p.1.2, p.2)) :=
      (measurable_Hm G hS).comp ((continuous_snd.comp continuous_fst).prodMk
        continuous_snd).measurable
    exact h1.mul (h2.mul h3)
  -- Fubini, twice
  have h1 : MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × ℝ => ∫ s : ℝ,
        sKerd t (Real.log z - q.2) * (sKerd t (q.1 - s) * Hm G (q.2, s)))
      (μθ.prod MeasureTheory.volume) :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := μθ.prod MeasureTheory.volume) (ν := MeasureTheory.volume)
      (hf.aestronglyMeasurable)
  have h2 : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => ∫ t' : ℝ, ∫ s : ℝ,
        sKerd t (Real.log z - t') * (sKerd t (θ - s) * Hm G (t', s))) μθ :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := μθ) (ν := MeasureTheory.volume) h1
  -- pull the radial kernel factor out of the inner integral
  have hfix : (fun θ : ℝ => ∫ t' : ℝ, ∫ s : ℝ,
        sKerd t (Real.log z - t') * (sKerd t (θ - s) * Hm G (t', s)))
      = fun θ : ℝ => ∫ t' : ℝ, sKerd t (Real.log z - t')
          * (∫ s : ℝ, sKerd t (θ - s) * Hm G (t', s)) := by
    funext θ
    simp only [MeasureTheory.integral_const_mul]
  have h2r : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => ∫ t' : ℝ, sKerd t (Real.log z - t')
        * (∫ s : ℝ, sKerd t (θ - s) * Hm G (t', s))) μθ := hfix ▸ h2
  have hsq : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (∫ t' : ℝ, sKerd t (Real.log z - t')
        * (∫ s : ℝ, sKerd t (θ - s) * Hm G (t', s))) ^ 2
        * Work.FTS.EllipticEst.thEta θ) μθ :=
    (h2r.pow 2).mul hth
  -- transfer along `hid`, using the identity of the two angular integrands
  have hfun : (fun θ : ℝ => (∫ t' : ℝ, sKerd t (Real.log z - t')
        * (∫ s : ℝ, sKerd t (θ - s) * Hm G (t', s))) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      =ᵐ[μθ] (fun θ : ℝ =>
        (Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G t t)) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
    have hint : (∫ t' : ℝ, sKerd t (Real.log z - t')
          * (∫ s : ℝ, sKerd t (θ - s) * Hm G (t', s)))
        = ∫ t' : ℝ, sKerd t (Real.log z - t')
          * (∫ s : ℝ, sKerd t (θ - s) * Hxyc G t' s) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t' => ?_)
      change sKerd t (Real.log z - t') * (∫ s : ℝ, sKerd t (θ - s) * Hm G (t', s))
        = sKerd t (Real.log z - t') * (∫ s : ℝ, sKerd t (θ - s) * Hxyc G t' s)
      rw [← sKerd_mul_Hxyc_eq_Hm G ht0 ht1 hθ t']
    rw [hint, hid θ hθ]
  exact hμθ ▸ hsq.congr hfun

end Work.FTS.EllSol.EllPkgAux

-- end of file
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.mollSliceBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option autoImplicit false

/-! ## Elementary one-dimensional and angular facts -/

/-- `√a ≤ 1 + a` for `a ≥ 0`. -/
theorem sqrt_le_one_add_self {a : ℝ} (ha : 0 ≤ a) : Real.sqrt a ≤ 1 + a := by
  have h : a ≤ (1 + a) ^ 2 := by nlinarith
  calc Real.sqrt a ≤ Real.sqrt ((1 + a) ^ 2) := Real.sqrt_le_sqrt h
    _ = 1 + a := Real.sqrt_sq (by linarith)

/-- The radial weight is at least `1`. -/
theorem one_le_w {w : ℝ} (hw : 0 < w) : 1 ≤ Work.Spaces.w w := by
  rw [Work.Spaces.w, one_le_div (by positivity : (0 : ℝ) < w ^ 2)]
  nlinarith

/-- The squared radial weight is at least `1`. -/
theorem one_le_w_sq {w : ℝ} (hw : 0 < w) : 1 ≤ (Work.Spaces.w w) ^ 2 := by
  calc (1 : ℝ) = 1 ^ 2 := by norm_num
    _ ≤ (Work.Spaces.w w) ^ 2 := pow_le_pow_left₀ (by norm_num) (one_le_w hw) 2

/-- The radial weight is positive for `w > 0`. -/
theorem w_pos {w : ℝ} (hw : 0 < w) : 0 < Work.Spaces.w w := by
  rw [Work.Spaces.w]
  exact div_pos (by positivity) (by positivity)

/-- The angular weight is nonnegative on `Iθ`. -/
theorem thEta_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.thEta θ := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.rpow_nonneg
    (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])) _

/-- Almost every point of `Iθ` is an interior point. -/
theorem ae_mem_Ioo_Iθ : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
    θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [Work.Spaces.Iθ, ← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2))]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- The angular weight is at least `1` almost everywhere on `Iθ`. -/
theorem one_le_thEta_ae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
    1 ≤ Work.FTS.EllipticEst.thEta θ := by
  filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
  exact one_le_thEta_of_mem_Ioo hθ

/-! ## The slice energy and the honest `H^0`-mass -/

/-- The angular slice energy is nonnegative. -/
theorem e2s_nonneg (G : ℝ → ℝ → ℝ) (w : ℝ) : 0 ≤ E2s G w := by
  rw [E2s]
  refine MeasureTheory.setIntegral_nonneg (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc) ?_
  intro θ hθ
  exact mul_nonneg (sq_nonneg _) (thEta_nonneg_of_mem_Iθ hθ)

/-- `ttIntS` is the squared radial weight times the slice energy. -/
theorem ttIntS_eq (G : ℝ → ℝ → ℝ) (w : ℝ) :
    Work.EllipticEst.Core.ttIntS G w = (Work.Spaces.w w) ^ 2 * E2s G w := rfl

/-- The honest `H^0`-mass of `∂_θ²G` is nonnegative. -/
theorem ttIntS_nonneg (G : ℝ → ℝ → ℝ) (w : ℝ) : 0 ≤ Work.EllipticEst.Core.ttIntS G w := by
  rw [ttIntS_eq]
  exact mul_nonneg (sq_nonneg _) (e2s_nonneg G w)

/-- **The square root of the slice energy is dominated by the honest `H^0`-mass.**  Since the
radial weight is at least `1`, `√(E2s) = √(ttIntS)/w ≤ √(ttIntS) ≤ 1 + ttIntS`. -/
theorem sqrt_e2s_le_one_add_ttIntS (G : ℝ → ℝ → ℝ) {w : ℝ} (hw : 0 < w) :
    Real.sqrt (E2s G w) ≤ 1 + Work.EllipticEst.Core.ttIntS G w := by
  have hww : 1 ≤ Work.Spaces.w w := one_le_w hw
  have hwwpos : 0 < Work.Spaces.w w := w_pos hw
  have hsq : Real.sqrt (Work.EllipticEst.Core.ttIntS G w)
      = Work.Spaces.w w * Real.sqrt (E2s G w) := by
    rw [ttIntS_eq, Real.sqrt_mul (le_of_lt (pow_pos hwwpos 2)) (E2s G w),
      Real.sqrt_sq (le_of_lt hwwpos)]
  have h1 : Real.sqrt (E2s G w)
      = Real.sqrt (Work.EllipticEst.Core.ttIntS G w) / Work.Spaces.w w := by
    rw [hsq, mul_div_cancel_left₀ _ (ne_of_gt hwwpos)]
  have hT0 : 0 ≤ Work.EllipticEst.Core.ttIntS G w := ttIntS_nonneg G w
  calc Real.sqrt (E2s G w) = Real.sqrt (Work.EllipticEst.Core.ttIntS G w) / Work.Spaces.w w := h1
    _ ≤ Real.sqrt (Work.EllipticEst.Core.ttIntS G w) := by
        rw [div_le_iff₀ hwwpos]
        nlinarith [Real.sqrt_nonneg (Work.EllipticEst.Core.ttIntS G w), hww]
    _ ≤ 1 + Work.EllipticEst.Core.ttIntS G w := sqrt_le_one_add_self hT0

/-! ## The two Taylor bounds for a `C²` slice -/

/-- `|∫_a^b (b - t) g t| ≤ (b - a) ∫_a^b |g t|` for a continuous `g`. -/
theorem abs_integral_linear_mul_le {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Set.uIcc a b)) :
    |∫ t in a..b, (b - t) * g t| ≤ (b - a) * ∫ t in a..b, |g t| := by
  have hcont1 : ContinuousOn (fun t : ℝ => (b - t) * |g t|) (Set.uIcc a b) :=
    (continuousOn_const.sub continuousOn_id).mul hg.abs
  calc |∫ t in a..b, (b - t) * g t| ≤ ∫ t in a..b, |(b - t) * g t| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ = ∫ t in a..b, (b - t) * |g t| := by
        refine intervalIntegral.integral_congr ?_
        intro t ht
        rw [Set.uIcc_of_le hab] at ht
        simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ b - t from by linarith [ht.2])]
    _ ≤ ∫ t in a..b, (b - a) * |g t| := by
        refine intervalIntegral.integral_mono_on hab hcont1.intervalIntegrable
          ((hg.abs.const_mul (b - a)).intervalIntegrable) ?_
        intro t ht
        exact mul_le_mul_of_nonneg_right (by linarith [ht.1]) (abs_nonneg _)
    _ = (b - a) * ∫ t in a..b, |g t| := intervalIntegral.integral_const_mul _ _

/-- **Taylor about the left endpoint.**  For `0 < θ₀ < θ < π/2` and a `C²` slice,
`|f θ - f θ₀ - f' θ₀ (θ - θ₀)| ≤ (θ - θ₀) ∫_{θ₀}^{θ} |f''|`. -/
theorem sliceTaylorLeft {f : ℝ → ℝ} {θ θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hlt : θ₀ < θ)
    (hθ : θ < Real.pi / 2) (hC2 : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) :
    |f θ - f θ₀ - deriv f θ₀ * (θ - θ₀)| ≤ (θ - θ₀) * ∫ t in θ₀..θ, |deriv (deriv f) t| := by
  have hT := Work.FTS.EllSol.ASlotRoute.Auxiliary.taylorSecondOrderIntegral
    (a := Real.pi / 2) (y := θ₀) (x := θ) (u := f) hθ₀ hlt hθ hC2
  have hEq : f θ - f θ₀ - deriv f θ₀ * (θ - θ₀)
      = ∫ t in θ₀..θ, (θ - t) * deriv (deriv f) t := by
    rw [hT]; ring
  have hcont : ContinuousOn (deriv (deriv f)) (Set.uIcc θ₀ θ) := by
    refine (Work.FTS.EllSol.c2_continuousOn_deriv_deriv hC2).mono ?_
    intro t ht
    rw [Set.uIcc_of_le hlt.le] at ht
    exact ⟨lt_of_lt_of_le hθ₀ ht.1, lt_of_le_of_lt ht.2 hθ⟩
  rw [hEq]
  exact abs_integral_linear_mul_le hlt.le hcont

/-- **Taylor about the right endpoint.**  For `0 < θ < θ₀ < π/2` and a `C²` slice,
`|f θ - f θ₀ - f' θ₀ (θ - θ₀)| ≤ 2 (θ₀ - θ) ∫_{θ}^{θ₀} |f''|`. -/
theorem sliceTaylorRight {f : ℝ → ℝ} {θ θ₀ : ℝ} (hθ : 0 < θ) (hlt : θ < θ₀)
    (hθ₀ : θ₀ < Real.pi / 2) (hC2 : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) :
    |f θ - f θ₀ - deriv f θ₀ * (θ - θ₀)| ≤ 2 * (θ₀ - θ) * ∫ t in θ..θ₀, |deriv (deriv f) t| := by
  have hT := Work.FTS.EllSol.ASlotRoute.Auxiliary.taylorSecondOrderIntegral
    (a := Real.pi / 2) (y := θ) (x := θ₀) (u := f) hθ hlt hθ₀ hC2
  have hftc : deriv f θ₀ - deriv f θ = ∫ t in θ..θ₀, deriv (deriv f) t :=
    Work.FTS.EllSol.c2_deriv_sub_eq_intervalIntegral hC2 hθ hlt.le hθ₀
  have hEq : f θ - f θ₀ - deriv f θ₀ * (θ - θ₀)
      = (θ₀ - θ) * (∫ t in θ..θ₀, deriv (deriv f) t)
        - ∫ t in θ..θ₀, (θ₀ - t) * deriv (deriv f) t := by
    rw [← hftc, hT]; ring
  have hcont : ContinuousOn (deriv (deriv f)) (Set.uIcc θ θ₀) := by
    refine (Work.FTS.EllSol.c2_continuousOn_deriv_deriv hC2).mono ?_
    intro t ht
    rw [Set.uIcc_of_le hlt.le] at ht
    exact ⟨lt_of_lt_of_le hθ ht.1, lt_of_le_of_lt ht.2 hθ₀⟩
  have hA : |(θ₀ - θ) * (∫ t in θ..θ₀, deriv (deriv f) t)|
      ≤ (θ₀ - θ) * ∫ t in θ..θ₀, |deriv (deriv f) t| := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ θ₀ - θ)]
    exact mul_le_mul_of_nonneg_left
      (intervalIntegral.abs_integral_le_integral_abs hlt.le) (by linarith)
  have hB := abs_integral_linear_mul_le hlt.le hcont
  rw [hEq]
  have htri : |(θ₀ - θ) * (∫ t in θ..θ₀, deriv (deriv f) t)
      - ∫ t in θ..θ₀, (θ₀ - t) * deriv (deriv f) t|
      ≤ |(θ₀ - θ) * (∫ t in θ..θ₀, deriv (deriv f) t)|
        + |∫ t in θ..θ₀, (θ₀ - t) * deriv (deriv f) t| :=
    abs_sub_le_iff.mpr
      ⟨by linarith [le_abs_self ((θ₀ - θ) * ∫ t in θ..θ₀, deriv (deriv f) t),
          neg_le_abs (∫ t in θ..θ₀, (θ₀ - t) * deriv (deriv f) t)],
       by linarith [le_abs_self (∫ t in θ..θ₀, (θ₀ - t) * deriv (deriv f) t),
          neg_le_abs ((θ₀ - θ) * ∫ t in θ..θ₀, deriv (deriv f) t)]⟩
  linarith [htri, hA, hB]

/-! ## The weighted Cauchy–Schwarz bound for the slice energy -/

/-- **`∫_{Iθ} |h| ≤ √(π/2) √(∫_{Iθ} h² σ)`** for the angular weight `σ = sin(2θ)^{-99/100}`. -/
theorem integral_abs_le_sqrt_thEta {h : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => h θ ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (Set.Icc 0 (Real.pi / 2))) :
    (∫ θ in Set.Icc 0 (Real.pi / 2), |h θ|) ≤ Real.sqrt (Real.pi / 2) *
      Real.sqrt (∫ θ in Set.Icc 0 (Real.pi / 2),
        h θ ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))) :=
  Work.FTS.EllSol.EllPkgAux.MollAux.integralAbsLeSqrtWeighted hint

/-! ## Integrability of the slice of the second derivative -/

/-- The `θ`-slice of `∂_θ²G` at `w` is integrable against `σ` (the constant `(w w)²` is
stripped off the honest hypothesis). -/
theorem integrableOn_second_deriv {G : ℝ → ℝ → ℝ}
    (hhon : Work.EllipticEst.Core.i0Aux.SliceHonestOpen G) {w : ℝ} (hw : 0 < w) :
    MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
  have h := hhon.1 w hw
  have hc : ((Work.Spaces.w w) ^ 2) ≠ 0 := ne_of_gt (pow_pos (w_pos hw) 2)
  have h2 : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ * ((Work.Spaces.w w) ^ 2)) Work.Spaces.Iθ :=
    h.congr (Filter.Eventually.of_forall (fun θ => by ring))
  refine (h2.mul_const (((Work.Spaces.w w) ^ 2)⁻¹)).congr
    (Filter.Eventually.of_forall (fun θ => ?_))
  simp only
  rw [mul_assoc, mul_inv_cancel₀ hc, mul_one]

/-- The absolute value of the second derivative of the slice is integrable on `Iθ`. -/
theorem integrableOn_abs_second_deriv {G : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen G)
    (hhon : Work.EllipticEst.Core.i0Aux.SliceHonestOpen G) {w : ℝ} (hw : 0 < w) :
    MeasureTheory.IntegrableOn (fun θ : ℝ =>
      |Work.Spaces.pth (Work.Spaces.pth G) w θ|) Work.Spaces.Iθ := by
  have h1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.integrableOn_const
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
  have hbulk : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2 * ((Work.Spaces.w w) ^ 2)
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
    hhon.1 w hw
  have hdom := h1.add hbulk
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => |Work.Spaces.pth (Work.Spaces.pth G) w θ|)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => |Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2|)
      ((hsm.pth.pth).continuousOn.abs) hw
  refine hdom.mono' haesm ?_
  filter_upwards [one_le_thEta_ae] with θ hθ1
  have hA0 : 0 ≤ (Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2 := sq_nonneg _
  have hc1 : 1 ≤ (Work.Spaces.w w) ^ 2 := one_le_w_sq hw
  have hB0 : 0 ≤ (Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2 * ((Work.Spaces.w w) ^ 2)
      * Work.FTS.EllipticEst.thEta θ :=
    mul_nonneg (mul_nonneg hA0 (by linarith)) (by linarith)
  have hkey : (Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2
      ≤ (Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2 * ((Work.Spaces.w w) ^ 2)
        * Work.FTS.EllipticEst.thEta θ := by
    calc (Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2
        ≤ (Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2 * ((Work.Spaces.w w) ^ 2) :=
          le_mul_of_one_le_right hA0 hc1
      _ ≤ (Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2 * ((Work.Spaces.w w) ^ 2)
            * Work.FTS.EllipticEst.thEta θ :=
          le_mul_of_one_le_right (mul_nonneg hA0 (by linarith)) hθ1
  have hbd : |Work.Spaces.pth (Work.Spaces.pth G) w θ|
      ≤ 1 + (Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2 * ((Work.Spaces.w w) ^ 2)
          * Work.FTS.EllipticEst.thEta θ := by
    calc |Work.Spaces.pth (Work.Spaces.pth G) w θ|
        = Real.sqrt ((Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2) := by
          rw [Real.sqrt_sq_eq_abs]
      _ ≤ Real.sqrt ((Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2 * ((Work.Spaces.w w) ^ 2)
            * Work.FTS.EllipticEst.thEta θ) := Real.sqrt_le_sqrt hkey
      _ ≤ 1 + (Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2 * ((Work.Spaces.w w) ^ 2)
            * Work.FTS.EllipticEst.thEta θ := sqrt_le_one_add_self hB0
  have hpos : 0 ≤ 1 + (Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2 * ((Work.Spaces.w w) ^ 2)
      * Work.FTS.EllipticEst.thEta θ := by linarith [hB0]
  simp only [Pi.add_apply, Real.norm_eq_abs, abs_abs, abs_of_nonneg hpos]
  exact hbd

/-! ## The pointwise slice bound -/

/-- **The second-order Taylor slice estimate about `π/4`.** -/
theorem slice_pointwise_le {G : ℝ → ℝ → ℝ} {w θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2)
    (hC2 : ContDiffOn ℝ 2 (fun t : ℝ => G w t) (Set.Ioo 0 (Real.pi / 2)))
    (habs : MeasureTheory.IntegrableOn
      (fun t : ℝ => |deriv (deriv (fun t : ℝ => G w t)) t|) Work.Spaces.Iθ)
    (hCS : (∫ t in Work.Spaces.Iθ, |deriv (deriv (fun t : ℝ => G w t)) t|)
      ≤ Real.sqrt (Real.pi / 2) * Real.sqrt (E2s G w)) :
    |G w θ| ≤ |G w (Real.pi / 4)| + (Real.pi / 4) * |deriv (fun t : ℝ => G w t) (Real.pi / 4)|
      + (Real.pi / 2) * Real.sqrt (Real.pi / 2) * Real.sqrt (E2s G w) := by
  have hπ4pos : 0 < Real.pi / 4 := by linarith [Real.pi_pos]
  have hπ4lt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hIθnn : 0 ≤ ∫ t in Work.Spaces.Iθ, |deriv (deriv (fun t : ℝ => G w t)) t| := by
    refine MeasureTheory.setIntegral_nonneg (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
      (fun t _ => abs_nonneg _)
  have hsubI : ∀ {c d : ℝ}, c ≤ d → 0 < c → d < Real.pi / 2 →
      ∫ t in c..d, |deriv (deriv (fun t : ℝ => G w t)) t|
        ≤ ∫ t in Work.Spaces.Iθ, |deriv (deriv (fun t : ℝ => G w t)) t| := by
    intro c d hcd hc hd
    rw [intervalIntegral.integral_of_le hcd]
    refine MeasureTheory.setIntegral_mono_set habs
      (Filter.Eventually.of_forall (fun t => abs_nonneg _)) ?_
    filter_upwards with t ht using ⟨le_of_lt (lt_trans hc ht.1), le_of_lt (lt_of_le_of_lt ht.2 hd)⟩
  -- the Taylor remainder is controlled by `(π/2) ∫_{Iθ} |f''|`
  have hrem : |G w θ - G w (Real.pi / 4)
      - deriv (fun t : ℝ => G w t) (Real.pi / 4) * (θ - Real.pi / 4)|
      ≤ (Real.pi / 2) * ∫ t in Work.Spaces.Iθ, |deriv (deriv (fun t : ℝ => G w t)) t| := by
    rcases lt_trichotomy θ (Real.pi / 4) with hlt | heq | hgt
    · have hT := sliceTaylorRight hθ0 hlt hπ4lt hC2
      have hI := hsubI hlt.le hθ0 hπ4lt
      have hnn : 0 ≤ ∫ t in θ..Real.pi / 4, |deriv (deriv (fun t : ℝ => G w t)) t| :=
        intervalIntegral.integral_nonneg hlt.le (fun t _ => abs_nonneg _)
      refine hT.trans ?_
      refine mul_le_mul ?_ hI hnn (by linarith [Real.pi_pos])
      linarith [hθ0]
    · subst heq
      simp only [sub_self, mul_zero, abs_zero]
      exact mul_nonneg (by linarith [Real.pi_pos]) hIθnn
    · have hT := sliceTaylorLeft hπ4pos hgt hθ1 hC2
      have hI := hsubI hgt.le hπ4pos hθ1
      have hnn : 0 ≤ ∫ t in Real.pi / 4..θ, |deriv (deriv (fun t : ℝ => G w t)) t| :=
        intervalIntegral.integral_nonneg hgt.le (fun t _ => abs_nonneg _)
      refine hT.trans ?_
      refine (mul_le_mul (le_refl _) hI hnn (by linarith [Real.pi_pos])).trans ?_
      exact mul_le_mul_of_nonneg_right (by linarith [hθ1, Real.pi_pos]) hIθnn
  -- the Taylor remainder is additive, and the linear term is bounded
  have hsplit : G w θ - G w (Real.pi / 4)
      = deriv (fun t : ℝ => G w t) (Real.pi / 4) * (θ - Real.pi / 4)
        + (G w θ - G w (Real.pi / 4)
            - deriv (fun t : ℝ => G w t) (Real.pi / 4) * (θ - Real.pi / 4)) := by ring
  have htri : |G w θ| ≤ |G w (Real.pi / 4)| + |G w θ - G w (Real.pi / 4)| := by
    have h := abs_add_le (G w (Real.pi / 4)) (G w θ - G w (Real.pi / 4))
    rw [add_sub_cancel] at h
    exact h
  have hsec : |G w θ - G w (Real.pi / 4)|
      ≤ (Real.pi / 4) * |deriv (fun t : ℝ => G w t) (Real.pi / 4)|
        + (Real.pi / 2) * ∫ t in Work.Spaces.Iθ, |deriv (deriv (fun t : ℝ => G w t)) t| := by
    rw [hsplit]
    refine (abs_add_le _ _).trans (add_le_add ?_ hrem)
    have hθm : |θ - Real.pi / 4| ≤ Real.pi / 4 := by
      rw [abs_le]
      constructor <;> linarith [hθ0, hθ1, Real.pi_pos]
    rw [abs_mul]
    nlinarith [hθm, abs_nonneg (deriv (fun t : ℝ => G w t) (Real.pi / 4))]
  -- assembly
  have hfin : |G w θ| ≤ |G w (Real.pi / 4)|
      + (Real.pi / 4) * |deriv (fun t : ℝ => G w t) (Real.pi / 4)|
      + (Real.pi / 2) * ∫ t in Work.Spaces.Iθ, |deriv (deriv (fun t : ℝ => G w t)) t| := by
    linarith [htri, hsec]
  refine hfin.trans ?_
  have hstep : (Real.pi / 2) * (∫ t in Work.Spaces.Iθ,
      |deriv (deriv (fun t : ℝ => G w t)) t|)
      ≤ (Real.pi / 2) * (Real.sqrt (Real.pi / 2) * Real.sqrt (E2s G w)) :=
    mul_le_mul_of_nonneg_left hCS (by linarith [Real.pi_pos])
  linarith [hstep]

/-! ## The main theorem -/

theorem mollSliceBound : ∃ C : ℝ, 0 < C ∧ ∀ (G : ℝ → ℝ → ℝ),
    Work.FTS.EllSol.EllPkgAux.TraceClass G → Work.FTS.EllSol.EllPkgAux.FourInts G →
    (∀ w : ℝ, 0 < w → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |G w θ| ≤ C * Work.FTS.EllSol.EllPkgAux.MGf G w) ∧
    (∀ a b : ℝ, 0 < a → a ≤ b →
      MeasureTheory.IntegrableOn (Work.FTS.EllSol.EllPkgAux.MGf G) (Set.Icc a b)) := by
  refine ⟨4, by norm_num, ?_⟩
  intro G hT hF
  obtain ⟨hsm, -, -, -, -, -, -, hhon⟩ := hT
  constructor
  · -- ## the pointwise bound
    intro w hw θ hθ0 hθ1
    have hC2 : ContDiffOn ℝ 2 (fun t : ℝ => G w t) (Set.Ioo 0 (Real.pi / 2)) :=
      (hsm.curry_θ hw).of_le (by simp [Work.Stability.smoothOrder])
    have hE2 : MeasureTheory.IntegrableOn (fun t : ℝ =>
        (deriv (deriv (fun t : ℝ => G w t)) t) ^ 2 * Work.FTS.EllipticEst.thEta t)
        Work.Spaces.Iθ := by
      simpa only [Work.Spaces.pth] using integrableOn_second_deriv hhon hw
    have habs : MeasureTheory.IntegrableOn (fun t : ℝ =>
        |deriv (deriv (fun t : ℝ => G w t)) t|) Work.Spaces.Iθ := by
      simpa only [Work.Spaces.pth] using integrableOn_abs_second_deriv hsm hhon hw
    have hE2' : MeasureTheory.IntegrableOn (fun t : ℝ =>
        (deriv (deriv (fun t : ℝ => G w t)) t) ^ 2 * (Real.sin (2 * t)) ^ (-(99 / 100 : ℝ)))
        (Set.Icc 0 (Real.pi / 2)) := by
      simpa only [Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta, Work.Spaces.eta] using hE2
    have hE2s_eq : E2s G w = ∫ θ in Set.Icc (0 : ℝ) (Real.pi / 2),
        (deriv (deriv (fun t : ℝ => G w t)) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)) := by
      simp only [E2s, Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta, Work.Spaces.eta,
        Work.Spaces.pth]
    have hCS : (∫ t in Work.Spaces.Iθ, |deriv (deriv (fun t : ℝ => G w t)) t|)
        ≤ Real.sqrt (Real.pi / 2) * Real.sqrt (E2s G w) := by
      have h := integral_abs_le_sqrt_thEta hE2'
      rw [← hE2s_eq] at h
      simpa only [Work.Spaces.Iθ] using h
    have hbound := slice_pointwise_le hθ0 hθ1 hC2 habs hCS
    have hsp : Work.Spaces.pth G w (Real.pi / 4) = deriv (fun t : ℝ => G w t) (Real.pi / 4) :=
      rfl
    rw [← hsp] at hbound
    -- the numerical comparison
    have hπ4 : (Real.pi / 4 : ℝ) ≤ 4 := by linarith [Real.pi_lt_four]
    have hsqrtpi : Real.sqrt (Real.pi / 2) ≤ 2 := by
      calc Real.sqrt (Real.pi / 2) ≤ Real.sqrt ((2 : ℝ) ^ 2) :=
            Real.sqrt_le_sqrt (by linarith [Real.pi_lt_four])
        _ = 2 := Real.sqrt_sq (by norm_num)
    have hc3 : (Real.pi / 2) * Real.sqrt (Real.pi / 2) ≤ 4 := by
      have h1 : Real.pi / 2 ≤ 2 := by linarith [Real.pi_lt_four]
      calc (Real.pi / 2) * Real.sqrt (Real.pi / 2) ≤ 2 * 2 :=
            mul_le_mul h1 hsqrtpi (Real.sqrt_nonneg _) (by norm_num)
        _ = 4 := by norm_num
    have hb0 : |G w (Real.pi / 4)| ≤ 4 * MGf G w := by
      rw [MGf]
      nlinarith [abs_nonneg (G w (Real.pi / 4)), abs_nonneg (Work.Spaces.pth G w (Real.pi / 4)),
        Real.sqrt_nonneg (E2s G w)]
    rw [MGf]
    have hBnd1 := mul_le_mul_of_nonneg_right hπ4
      (abs_nonneg (Work.Spaces.pth G w (Real.pi / 4)))
    have hBnd2 := mul_le_mul_of_nonneg_right hc3 (Real.sqrt_nonneg (E2s G w))
    linarith [hbound, hBnd1, hBnd2, abs_nonneg (G w (Real.pi / 4)),
      abs_nonneg (Work.Spaces.pth G w (Real.pi / 4)), Real.sqrt_nonneg (E2s G w)]
  · -- ## local integrability of `MGf`
    intro a b ha hab
    have hπ4pos : 0 < Real.pi / 4 := by linarith [Real.pi_pos]
    have hπ4lt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
    have hsubIoi : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun w hw => lt_of_lt_of_le ha hw.1
    have hsubIz : Set.Icc a b ⊆ Work.Spaces.Iz := fun w hw => le_trans ha.le hw.1
    have h1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b) :=
      MeasureTheory.integrableOn_const
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
    have h2 : MeasureTheory.IntegrableOn (fun w : ℝ => |G w (Real.pi / 4)|) (Set.Icc a b) :=
      (((hsm.curry_z ⟨hπ4pos, hπ4lt⟩).continuousOn.mono hsubIoi).abs).integrableOn_compact
        isCompact_Icc
    have h3 : MeasureTheory.IntegrableOn (fun w : ℝ => |Work.Spaces.pth G w (Real.pi / 4)|)
        (Set.Icc a b) :=
      ((((hsm.pth).curry_z ⟨hπ4pos, hπ4lt⟩).continuousOn.mono hsubIoi).abs).integrableOn_compact
        isCompact_Icc
    have h4 : MeasureTheory.IntegrableOn (fun w : ℝ => Real.sqrt (E2s G w)) (Set.Icc a b) := by
      have htt : MeasureTheory.IntegrableOn (fun w : ℝ => Work.EllipticEst.Core.ttIntS G w)
          (Set.Icc a b) := hF.2.2.1.mono_set hsubIz
      have hdom : MeasureTheory.IntegrableOn
          (fun w : ℝ => 1 + Work.EllipticEst.Core.ttIntS G w) (Set.Icc a b) := h1.add htt
      have haesm : MeasureTheory.AEStronglyMeasurable (fun w : ℝ => Real.sqrt (E2s G w))
          (MeasureTheory.volume.restrict (Set.Icc a b)) :=
        Real.continuous_sqrt.comp_aestronglyMeasurable
          (Work.FTS.EllSol.EllPkgAux.MollAux.aesmE2s hsm ha)
      refine hdom.mono' haesm ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with w hw
      have hpos : 0 ≤ 1 + Work.EllipticEst.Core.ttIntS G w := by
        linarith [ttIntS_nonneg G w]
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg (E2s G w)),
        abs_of_nonneg hpos]
        using sqrt_e2s_le_one_add_ttIntS G (lt_of_lt_of_le ha hw.1)
    have hsum : MeasureTheory.IntegrableOn (fun w : ℝ => 1 + |G w (Real.pi / 4)|
        + |Work.Spaces.pth G w (Real.pi / 4)| + Real.sqrt (E2s G w)) (Set.Icc a b) :=
      ((h1.add h2).add h3).add h4
    have hEq : MGf G = fun w : ℝ => 1 + |G w (Real.pi / 4)|
        + |Work.Spaces.pth G w (Real.pi / 4)| + Real.sqrt (E2s G w) := by
      funext w
      rfl
    rw [hEq]
    exact hsum

end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.sKerdFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

open Work.FTS.EllSol.PkgK5.K5c

/-- `sKerd 1` vanishes *strictly* beyond the support: at a point `u` with `|u| > 1` the
function `sKer 1` is identically zero on a neighbourhood, hence so is its derivative. -/
private theorem skerd_eq_zero_of_one_lt_abs {u : ℝ} (hu : 1 < |u|) : sKerd 1 u = 0 := by
  have hzero : ∀ x : ℝ, 1 ≤ |x| → sKer 1 x = 0 := fun x hx =>
    sKer_eq_zero_of_le_abs (ε := 1) one_pos hx
  have hev : sKer 1 =ᶠ[𝓝 u] (fun _ : ℝ => (0 : ℝ)) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    rcases (lt_abs.mp hu) with h | h
    · refine ⟨Set.Ioi 1, isOpen_Ioi.mem_nhds (show u ∈ Set.Ioi 1 from h), ?_⟩
      intro x hx
      have hx' : (1 : ℝ) < x := hx
      exact hzero x (by rw [abs_of_pos (by linarith)]; linarith)
    · refine ⟨Set.Iio (-1), isOpen_Iio.mem_nhds (by simp only [Set.mem_Iio]; linarith), ?_⟩
      intro x hx
      have hx' : x < (-1 : ℝ) := hx
      exact hzero x (by rw [abs_of_neg (by linarith)]; linarith)
  show deriv (sKer 1) u = 0
  rw [hev.deriv_eq, deriv_const]

/-- At the two endpoints `u = ±1` of the support the kernel `sKer 1` is nonnegative with a
zero, so `u` is a local minimum and the derivative vanishes there. -/
private theorem skerd_eq_zero_of_abs_eq_one {u : ℝ} (hu : |u| = 1) : sKerd 1 u = 0 := by
  have hzu : sKer 1 u = 0 := sKer_eq_zero_of_le_abs (ε := 1) one_pos (le_of_eq hu.symm)
  have hmin : IsLocalMin (sKer 1) u := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [hzu]
    exact sKer_nonneg one_pos x
  show deriv (sKer 1) u = 0
  exact hmin.deriv_eq_zero

theorem sKerdFacts :
    Continuous (Work.FTS.EllSol.EllPkgAux.sKerd 1) ∧
    HasCompactSupport (Work.FTS.EllSol.EllPkgAux.sKerd 1) ∧
    (∀ u : ℝ, 1 ≤ |u| → Work.FTS.EllSol.EllPkgAux.sKerd 1 u = 0) ∧
    (∫ u : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd 1 u = 0) ∧
    (∫ u : ℝ, u * Work.FTS.EllSol.EllPkgAux.sKerd 1 u = -1) ∧
    MeasureTheory.Integrable (Work.FTS.EllSol.EllPkgAux.sKerd 1) ∧
    MeasureTheory.Integrable (fun u : ℝ => u * Work.FTS.EllSol.EllPkgAux.sKerd 1 u) ∧
    MeasureTheory.Integrable (fun u : ℝ => u ^ 2 * Work.FTS.EllSol.EllPkgAux.sKerd 1 u) ∧
    (∀ t : ℝ, 0 < t → ∀ u : ℝ,
            Work.FTS.EllSol.EllPkgAux.sKerd t u = (1 / t ^ 2) * Work.FTS.EllSol.EllPkgAux.sKerd 1 (u / t)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- continuity: `sKer 1` is `C^∞`, so its derivative is continuous
    exact (contDiff_sKer (1 : ℝ)).continuous_deriv_one
  · -- compact support: the support of the derivative is contained in that of `sKer 1`
    simpa [sKerd] using (mk_hasCompactSupport_sKer (ε := 1) one_pos).deriv
  · -- vanishing for `|u| ≥ 1`
    intro u hu
    rcases lt_or_eq_of_le hu with h | h
    · exact skerd_eq_zero_of_one_lt_abs h
    · exact skerd_eq_zero_of_abs_eq_one h.symm
  · -- `∫ sKerd 1 = 0`
    simpa [sKerd] using mk_integral_sKerd_eq_zero (ε := 1) one_pos
  · -- `∫ u * sKerd 1 u = -1`
    simpa [sKerd] using mk_integral_id_sKerd (ε := 1) one_pos
  · -- integrability of `sKerd 1`
    simpa [sKerd] using mk_integrable_deriv_sKer (ε := 1) one_pos
  · -- integrability of `u * sKerd 1 u`
    simpa [sKerd] using mk_integrable_id_deriv_sKer (ε := 1) one_pos
  · -- integrability of `u ^ 2 * sKerd 1 u`
    simpa [sKerd] using mk_integrable_sq_deriv_sKer (ε := 1) one_pos
  · -- the parabolic scaling of the derivative kernel
    intro t ht u
    show deriv (sKer t) u = (1 / t ^ 2) * deriv (sKer 1) (u / t)
    rw [mk_deriv_sKerd_scale]
    have h2 : t ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt ht)
    field_simp

end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.FlatFT.integrable_weighted_slice1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.FlatFT

/-- **The weighted square of the `t`-Fourier slice is integrable, in every order.**  For
`h : ℝ → ℂ` of class `C^n` with compact support, `ξ ↦ (2πξ)^{2n} ‖slice1 h ξ‖²` is integrable.

Induction on `n`: the weight `(2πξ)²` is exactly the squared modulus of the Fourier multiplier
`2πIξ`, so shifting it onto the slice is the same as differentiating `h` (`slice1_deriv`). -/
theorem integrable_weighted_slice1_aux (n : ℕ) {h : ℝ → ℂ} (hh : ContDiff ℝ n h)
    (hs : HasCompactSupport h) :
    MeasureTheory.Integrable
      (fun ξ : ℝ => (2 * Real.pi * ξ) ^ (2 * n) * ‖slice1 h ξ‖ ^ 2) := by
  induction n generalizing h with
  | zero =>
      simpa using integrable_normSq_slice1 hh.continuous hs
  | succ n ih =>
      have h1 : ContDiff ℝ 1 h :=
        hh.of_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n))
      have hd : ContDiff ℝ n (deriv h) := hh.deriv'
      have hs' : HasCompactSupport (deriv h) := hs.deriv
      refine (ih hd hs').congr (Filter.Eventually.of_forall fun ξ => ?_)
      beta_reduce
      rw [slice1_deriv h h1 hs ξ, norm_sq_mul_two_pi_I]
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, pow_add]
      ring

theorem integrable_weighted_slice1 {k : ℕ} (hk : k ≤ 2) {h : ℝ → ℂ} (hh : ContDiff ℝ k h)
    (hs : HasCompactSupport h) :
    MeasureTheory.Integrable (fun ξ : ℝ => (2 * Real.pi * ξ) ^ (2 * k) * ‖Work.FTS.EllSol.FlatFT.slice1 h ξ‖ ^ 2) := by
  have _ := hk
  exact integrable_weighted_slice1_aux k hh hs

end Work.FTS.EllSol.FlatFT
end
-- ===== merged: Submission.Work.FTS.EllSol.ShiftFT.Aux2.gcDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT.Aux2

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

theorem gcDeriv (N b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    (∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pz (Gc N b u) t θ
        = Work.FTS.EllSol.Trunc.chi N t * (Work.Spaces.pz u t θ - b * u t θ) + b * Gc N b u t θ)
    ∧ (∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pz (Work.Spaces.pz (Gc N b u)) t θ
        = deriv (Work.FTS.EllSol.Trunc.chi N) t * Work.Spaces.pz u t θ
          + Work.FTS.EllSol.Trunc.chi N t * Work.Spaces.pz (Work.Spaces.pz u) t θ
          + b ^ 2 * Gc N b u t θ - b ^ 2 * Work.FTS.EllSol.Trunc.chi N t * u t θ
          - b * deriv (Work.FTS.EllSol.Trunc.chi N) t * u t θ)
    ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Differentiable ℝ (fun s => Gc N b u s θ))
    ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Differentiable ℝ (fun s => Work.Spaces.pz (Gc N b u) s θ)) := by
  -- the `t`-slices of `u` and of `∂_t u` are differentiable everywhere
  have hsliceDAt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ t : ℝ,
      DifferentiableAt ℝ (fun s : ℝ => u s θ) t :=
    fun θ hθ t => ((gcSliceData u hu).1 θ hθ).differentiableAt
  have hpzSliceDAt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ t : ℝ,
      DifferentiableAt ℝ (fun s : ℝ => Work.Spaces.pz u s θ) t :=
    fun θ hθ t => ((gcSliceData u hu).2 θ hθ).differentiableAt
  -- the fundamental theorem of calculus for the lower limit of the integral in `Gc`
  have hJd := gcJHasDeriv N b u hu
  -- the derivative of the exponential-times-integral factor
  have hFHas : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => Real.exp (b * s) * ∫ y in s..(2 * N),
            Real.exp (-(b * y)) * deriv (Work.FTS.EllSol.Trunc.chi N) y * u y θ)
        (b * (Real.exp (b * t) * ∫ y in t..(2 * N),
            Real.exp (-(b * y)) * deriv (Work.FTS.EllSol.Trunc.chi N) y * u y θ)
          - deriv (Work.FTS.EllSol.Trunc.chi N) t * u t θ) t := by
    intro θ hθ t
    have hexpD : HasDerivAt (fun s : ℝ => Real.exp (b * s)) (b * Real.exp (b * t)) t := by
      have h : HasDerivAt (fun s : ℝ => b * s) b t := by
        simpa using (hasDerivAt_id t).const_mul b
      simpa [mul_comm] using h.exp
    have hmain := hexpD.mul (hJd θ hθ t)
    refine hmain.congr_deriv ?_
    have hee : Real.exp (b * t) * Real.exp (-(b * t)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [show Real.exp (b * t)
          * (-(Real.exp (-(b * t)) * deriv (Work.FTS.EllSol.Trunc.chi N) t * u t θ))
        = -(Real.exp (b * t) * Real.exp (-(b * t)))
            * (deriv (Work.FTS.EllSol.Trunc.chi N) t * u t θ) from by ring]
    rw [hee]
    ring
  -- the pointwise identity `∂_t (Gc) = χ·∂_t u + b·e^{bt}∫…` (from `Gc_sh`)
  have hE1 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ s : ℝ,
      Work.Spaces.pz (Gc N b u) s θ
        = Work.FTS.EllSol.Trunc.chi N s * Work.Spaces.pz u s θ
          + b * (Real.exp (b * s) * ∫ y in s..(2 * N),
              Real.exp (-(b * y)) * deriv (Work.FTS.EllSol.Trunc.chi N) y * u y θ) := by
    intro θ hθ s
    have h := Gc_sh N b u hu s θ hθ
    have hG : Gc N b u s θ = Work.FTS.EllSol.Trunc.chi N s * u s θ
        + Real.exp (b * s) * ∫ y in s..(2 * N),
            Real.exp (-(b * y)) * deriv (Work.FTS.EllSol.Trunc.chi N) y * u y θ := rfl
    rw [hG] at h
    linear_combination h
  -- the derivative of the `t`-slice of `Gc`
  have hGHas : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => Gc N b u s θ)
        (Work.FTS.EllSol.Trunc.chi N t * Work.Spaces.pz u t θ
          + b * (Real.exp (b * t) * ∫ y in t..(2 * N),
              Real.exp (-(b * y)) * deriv (Work.FTS.EllSol.Trunc.chi N) y * u y θ)) t := by
    intro θ hθ t
    have hchiD : DifferentiableAt ℝ (Work.FTS.EllSol.Trunc.chi N) t :=
      (Work.FTS.EllSol.Trunc.chi_contDiff 1 N).differentiable (by norm_num) t
    have h1 : HasDerivAt (fun s : ℝ => Work.FTS.EllSol.Trunc.chi N s * u s θ)
        (deriv (Work.FTS.EllSol.Trunc.chi N) t * u t θ
          + Work.FTS.EllSol.Trunc.chi N t * deriv (fun s : ℝ => u s θ) t) t :=
      hchiD.hasDerivAt.mul (hsliceDAt θ hθ t).hasDerivAt
    have hsum := h1.add (hFHas θ hθ t)
    refine hsum.congr_deriv ?_
    rw [show deriv (fun s : ℝ => u s θ) t = Work.Spaces.pz u t θ from rfl]
    ring
  -- the derivative of the `t`-slice of `∂_t Gc`
  have hPzHas : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => Work.Spaces.pz (Gc N b u) s θ)
        (deriv (Work.FTS.EllSol.Trunc.chi N) t * Work.Spaces.pz u t θ
          + Work.FTS.EllSol.Trunc.chi N t * Work.Spaces.pz (Work.Spaces.pz u) t θ
          + b ^ 2 * Gc N b u t θ - b ^ 2 * Work.FTS.EllSol.Trunc.chi N t * u t θ
          - b * deriv (Work.FTS.EllSol.Trunc.chi N) t * u t θ) t := by
    intro θ hθ t
    have hchiD : DifferentiableAt ℝ (Work.FTS.EllSol.Trunc.chi N) t :=
      (Work.FTS.EllSol.Trunc.chi_contDiff 1 N).differentiable (by norm_num) t
    have h1 : HasDerivAt (fun s : ℝ =>
          Work.FTS.EllSol.Trunc.chi N s * Work.Spaces.pz u s θ)
        (deriv (Work.FTS.EllSol.Trunc.chi N) t * Work.Spaces.pz u t θ
          + Work.FTS.EllSol.Trunc.chi N t * deriv (fun s : ℝ => Work.Spaces.pz u s θ) t) t :=
      hchiD.hasDerivAt.mul (hpzSliceDAt θ hθ t).hasDerivAt
    have hsum := h1.add ((hFHas θ hθ t).const_mul b)
    have heq : (fun s : ℝ => Work.Spaces.pz (Gc N b u) s θ)
        =ᶠ[𝓝 t] ((fun s : ℝ => Work.FTS.EllSol.Trunc.chi N s * Work.Spaces.pz u s θ)
            + fun y : ℝ => b * (Real.exp (b * y) * ∫ x in y..(2 * N),
                Real.exp (-(b * x)) * deriv (Work.FTS.EllSol.Trunc.chi N) x * u x θ)) := by
      filter_upwards with s
      exact hE1 θ hθ s
    refine (hsum.congr_of_eventuallyEq heq).congr_deriv ?_
    rw [show deriv (fun s : ℝ => Work.Spaces.pz u s θ) t
        = Work.Spaces.pz (Work.Spaces.pz u) t θ from rfl]
    rw [show Gc N b u t θ = Work.FTS.EllSol.Trunc.chi N t * u t θ
        + Real.exp (b * t) * ∫ y in t..(2 * N),
            Real.exp (-(b * y)) * deriv (Work.FTS.EllSol.Trunc.chi N) y * u y θ from rfl]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the first-order identity
    intro t θ hθ
    have h := Gc_sh N b u hu t θ hθ
    linear_combination h
  · -- the second-order identity
    intro t θ hθ
    exact (hPzHas θ hθ t).deriv
  · -- differentiability of the `t`-slice of `Gc`
    intro θ hθ t
    exact (hGHas θ hθ t).differentiableAt
  · -- differentiability of the `t`-slice of `∂_t Gc`
    intro θ hθ t
    exact (hPzHas θ hθ t).differentiableAt

end

end Work.FTS.EllSol.ShiftFT.Aux2
end
-- ===== merged: Submission.Work.FTS.EllSol.ShiftFT.Aux2.gcIBP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllSol.ShiftFT.Aux2

theorem gcIBP (N b : ℝ) (u : ℝ → ℝ → ℝ) (hN : 0 < N)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ t : ℝ,
      (∫ s in (-(2 * N))..(2 * N),
          Real.exp (b * (t - s)) * Work.FTS.EllSol.Trunc.chi N s
            * (Work.Spaces.pz u s θ - b * u s θ))
        = -(Real.exp (b * t) * ∫ s in (-(2 * N))..(2 * N),
            Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ) := by
  intro θ hθ t
  obtain ⟨hsliceD, hpzD⟩ := gcSliceData u hu
  have hslice' : Differentiable ℝ (fun s : ℝ => u s θ) := hsliceD θ hθ
  have hpz' : Differentiable ℝ (fun s : ℝ => Work.Spaces.pz u s θ) := hpzD θ hθ
  -- The antiderivative `P s = e^{b(t-s)} χ(s) u(s,θ)`, whose total derivative is
  -- the integrand of the left-hand side plus the term `e^{b(t-s)} χ'(s) u(s,θ)`.
  set P : ℝ → ℝ := fun s => Real.exp (b * (t - s)) * (Work.FTS.EllSol.Trunc.chi N s * u s θ)
    with hP
  set Pexp : ℝ → ℝ := fun s => -b * Real.exp (b * (t - s))
        * (Work.FTS.EllSol.Trunc.chi N s * u s θ)
      + Real.exp (b * (t - s)) * (deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ
          + Work.FTS.EllSol.Trunc.chi N s * Work.Spaces.pz u s θ) with hPexp
  have hPd : ∀ s, HasDerivAt P (Pexp s) s := by
    intro s
    have hlin : HasDerivAt (fun s : ℝ => b * (t - s)) (-b) s := by
      have h0 : HasDerivAt (fun s : ℝ => t - s) (-1) s := (hasDerivAt_id s).const_sub t
      simpa using h0.const_mul b
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (b * (t - s)))
        (Real.exp (b * (t - s)) * (-b)) s := hlin.exp
    have hchi : HasDerivAt (Work.FTS.EllSol.Trunc.chi N)
        (deriv (Work.FTS.EllSol.Trunc.chi N) s) s :=
      ((Work.FTS.EllSol.Trunc.chi_contDiff 1 N).differentiable (by norm_num) s).hasDerivAt
    have hslice : HasDerivAt (fun s : ℝ => u s θ) (Work.Spaces.pz u s θ) s :=
      (hslice' s).hasDerivAt
    rw [hP]
    simp only [hPexp]
    exact (hexp.mul (hchi.mul hslice)).congr_deriv (by simp only [Pi.mul_apply]; ring)
  have hcont_exp : Continuous (fun s : ℝ => Real.exp (b * (t - s))) := by
    apply Real.continuous_exp.comp
    fun_prop
  have hcont_chi : Continuous (Work.FTS.EllSol.Trunc.chi N) :=
    (Work.FTS.EllSol.Trunc.chi_contDiff 0 N).continuous
  have hcont_dchi : Continuous (deriv (Work.FTS.EllSol.Trunc.chi N)) :=
    (Work.FTS.EllSol.Trunc.chi_contDiff 1 N).continuous_deriv_one
  have hcont_u : Continuous (fun s : ℝ => u s θ) := hslice'.continuous
  have hcont_pz : Continuous (fun s : ℝ => Work.Spaces.pz u s θ) := hpz'.continuous
  have hcont_Pexp : Continuous Pexp := by
    rw [hPexp]
    exact ((hcont_exp.const_mul (-b)).mul (hcont_chi.mul hcont_u)).add
      (hcont_exp.mul ((hcont_dchi.mul hcont_u).add (hcont_chi.mul hcont_pz)))
  have hcont_R : Continuous (fun s : ℝ =>
      Real.exp (b * (t - s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ) :=
    (hcont_exp.mul hcont_dchi).mul hcont_u
  have hIntPexp : IntervalIntegrable Pexp volume (-(2 * N)) (2 * N) :=
    hcont_Pexp.intervalIntegrable _ _
  have hIntR : IntervalIntegrable (fun s : ℝ =>
      Real.exp (b * (t - s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ) volume
        (-(2 * N)) (2 * N) := hcont_R.intervalIntegrable _ _
  -- Fundamental theorem of calculus; the boundary values vanish because `χ(±2N) = 0`.
  have hFTC : ∫ s in (-(2 * N))..(2 * N), Pexp s = P (2 * N) - P (-(2 * N)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hPd s) hIntPexp
  have hPtwo : P (2 * N) = 0 := by
    rw [hP]
    change Real.exp (b * (t - 2 * N))
      * (Work.FTS.EllSol.Trunc.chi N (2 * N) * u (2 * N) θ) = 0
    have h2N : (0 : ℝ) < 2 * N := by linarith
    rw [Work.FTS.EllSol.Trunc.chi_eq_zero hN (by simp [abs_of_pos h2N]), zero_mul, mul_zero]
  have hPneg : P (-(2 * N)) = 0 := by
    rw [hP]
    change Real.exp (b * (t - -(2 * N)))
      * (Work.FTS.EllSol.Trunc.chi N (-(2 * N)) * u (-(2 * N)) θ) = 0
    have h2N : (0 : ℝ) < 2 * N := by linarith
    rw [Work.FTS.EllSol.Trunc.chi_eq_zero hN (by simp [abs_neg, abs_of_pos h2N]),
      zero_mul, mul_zero]
  have hpoint : ∀ s, Real.exp (b * (t - s)) * Work.FTS.EllSol.Trunc.chi N s
        * (Work.Spaces.pz u s θ - b * u s θ)
      = Pexp s - Real.exp (b * (t - s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ := by
    intro s
    simp only [hPexp]
    ring_nf
  have hRfac : ∫ s in (-(2 * N))..(2 * N),
        Real.exp (b * (t - s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ
      = Real.exp (b * t) * ∫ s in (-(2 * N))..(2 * N),
          Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    show Real.exp (b * (t - s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ
      = Real.exp (b * t) * (Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s
          * u s θ)
    have hexp : Real.exp (b * (t - s)) = Real.exp (b * t) * Real.exp (-(b * s)) := by
      rw [← Real.exp_add, show b * t + -(b * s) = b * (t - s) from by ring]
    rw [hexp]
    ring
  calc ∫ s in (-(2 * N))..(2 * N), Real.exp (b * (t - s)) * Work.FTS.EllSol.Trunc.chi N s
          * (Work.Spaces.pz u s θ - b * u s θ)
      = ∫ s in (-(2 * N))..(2 * N), (Pexp s - Real.exp (b * (t - s))
            * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ) := by
          apply intervalIntegral.integral_congr
          intro s _
          exact hpoint s
    _ = (∫ s in (-(2 * N))..(2 * N), Pexp s) - ∫ s in (-(2 * N))..(2 * N),
            Real.exp (b * (t - s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ :=
          intervalIntegral.integral_sub hIntPexp hIntR
    _ = (P (2 * N) - P (-(2 * N))) - ∫ s in (-(2 * N))..(2 * N),
            Real.exp (b * (t - s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ := by
          rw [hFTC]
    _ = (0 - 0) - ∫ s in (-(2 * N))..(2 * N),
            Real.exp (b * (t - s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ := by
          rw [hPtwo, hPneg]
    _ = -(Real.exp (b * t) * ∫ s in (-(2 * N))..(2 * N),
            Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ) := by
          rw [hRfac]
          ring

end Work.FTS.EllSol.ShiftFT.Aux2
end
-- ===== merged: Submission.Work.FTS.EllSol.ShiftFT.Aux2.windowMarginal =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.EllSol.ShiftFT.Aux2

/-- Window/marginal Fubini–monotonicity, the `≤`-analogue of `marginal`'s `marginal_aux`.

Let `f` be jointly integrable on `μ.prod ν` and nonnegative there.  For any measurable `A`
the marginal `y ↦ ∫ x in A, f x y ∂μ` is `ν`-integrable, and its integral is at most the
joint integral: restricting the inner integration to the measurable window `A` can only
decrease the value, by monotonicity of the integral in the domain for nonnegative
integrands.  (The indicator `1_{A × univ}` is applied to `f` and Fubini is used twice.) -/
private theorem window_le_aux {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {A : Set α} (hA : MeasurableSet A) (f : α → β → ℝ)
    (hf : Integrable (fun p : α × β => f p.1 p.2) (μ.prod ν))
    (h0 : 0 ≤ᵐ[μ.prod ν] fun p : α × β => f p.1 p.2) :
    Integrable (fun y => ∫ x in A, f x y ∂μ) ν ∧
      ∫ y, (∫ x in A, f x y ∂μ) ∂ν ≤ ∫ p, f p.1 p.2 ∂(μ.prod ν) := by
  classical
  set F : α × β → ℝ := fun p => f p.1 p.2 with hF
  set F' : α × β → ℝ := (A ×ˢ Set.univ).indicator F with hF'
  have hAsm : MeasurableSet (A ×ˢ (Set.univ : Set β)) := hA.prod MeasurableSet.univ
  have hF_int : Integrable F (μ.prod ν) := hf
  have hF'_int : Integrable F' (μ.prod ν) := by
    refine Integrable.mono' hF_int.norm (hF_int.aestronglyMeasurable.indicator hAsm) ?_
    filter_upwards with p
    rw [hF', Set.indicator_apply]
    split_ifs with hp
    · exact le_rfl
    · simp
  have hkey : ∀ (x : α) (y : β), F' (x, y) = A.indicator (fun x => f x y) x := by
    intro x y
    by_cases h : x ∈ A
    · rw [hF', Set.indicator_of_mem (show (x, y) ∈ A ×ˢ (Set.univ : Set β) from ⟨h, Set.mem_univ _⟩),
        hF, Set.indicator_of_mem h]
    · rw [hF', Set.indicator_of_notMem (show (x, y) ∉ A ×ˢ (Set.univ : Set β) from fun hp => h hp.1),
        Set.indicator_of_notMem h]
  have hfun : (fun y => ∫ x, F' (x, y) ∂μ) = fun y => ∫ x in A, f x y ∂μ := by
    funext y
    rw [← integral_indicator hA]
    exact integral_congr_ae (Eventually.of_forall fun x => hkey x y)
  constructor
  · have h1 : Integrable (fun y => ∫ x, F' (x, y) ∂μ) ν := hF'_int.integral_prod_right
    rwa [hfun] at h1
  · have hprod' : ∫ p, F' p ∂(μ.prod ν) = ∫ y, ∫ x, F' (x, y) ∂μ ∂ν :=
      integral_prod_symm F' hF'_int
    have hEq : ∫ y, (∫ x, F' (x, y) ∂μ) ∂ν = ∫ y, (∫ x in A, f x y ∂μ) ∂ν := by
      rw [hfun]
    have hle : F' ≤ᵐ[μ.prod ν] F := by
      filter_upwards [h0] with p hp
      rw [hF', Set.indicator_apply]
      split_ifs with h
      · rfl
      · exact hp
    have hmono : ∫ p, F' p ∂(μ.prod ν) ≤ ∫ p, F p ∂(μ.prod ν) :=
      integral_mono_ae hF'_int hF_int hle
    calc ∫ y, (∫ x in A, f x y ∂μ) ∂ν
        = ∫ y, (∫ x, F' (x, y) ∂μ) ∂ν := hEq.symm
      _ = ∫ p, F' p ∂(μ.prod ν) := hprod'.symm
      _ ≤ ∫ p, F p ∂(μ.prod ν) := hmono
      _ = ∫ p, f p.1 p.2 ∂(μ.prod ν) := by rw [hF]

theorem windowMarginal (b N : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hJ : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.Integrable (fun θ => (∫ s in Set.Icc (-(2 * N)) (2 * N),
        (Work.Spaces.pz u s θ - b * u s θ) ^ 2) * Work.FTS.EllSol.FlatFT.wE θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)
    ∧ (∫ θ in Work.Spaces.Iθ, (∫ s in Set.Icc (-(2 * N)) (2 * N),
        (Work.Spaces.pz u s θ - b * u s θ) ^ 2) * Work.FTS.EllSol.FlatFT.wE θ)
      ≤ ∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2 := by
  classical
  have _ := hu
  -- The product measure `volume.prod (volume.restrict Iθ)` is the volume of `univ ×ˢ Iθ`.
  have hmeas : (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ) :
      MeasureTheory.Measure (ℝ × ℝ)) = MeasureTheory.volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ) := by
    have h := MeasureTheory.Measure.prod_restrict (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (ν := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (Set.univ : Set ℝ) Work.Spaces.Iθ
    rw [MeasureTheory.Measure.restrict_univ] at h
    exact h
  -- Joint integrability of the shifted square against `wE`.
  have hf : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ) :
        MeasureTheory.Measure (ℝ × ℝ)) := by
    rw [hmeas]
    exact hJ
  -- The integrand is nonnegative on the strip (as `wE ≥ 0` on `Iθ`).
  have h0 : 0 ≤ᵐ[(MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ) :
        MeasureTheory.Measure (ℝ × ℝ))]
      (fun p : ℝ × ℝ => (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2
        * Work.FTS.EllSol.FlatFT.wE p.2) := by
    rw [hmeas]
    refine (MeasureTheory.ae_restrict_iff' ?_).2 (Filter.Eventually.of_forall ?_)
    · exact MeasurableSet.univ.prod measurableSet_Icc
    · intro p hp
      exact mul_nonneg (sq_nonneg _) (Work.FTS.EllSol.FlatFT.wE_nonneg hp.2)
  -- `wE θ` is a constant for the inner (`s`-)integration.
  have hinner : ∀ θ : ℝ, (∫ s in Set.Icc (-(2 * N)) (2 * N),
        (Work.Spaces.pz u s θ - b * u s θ) ^ 2 * Work.FTS.EllSol.FlatFT.wE θ)
      = (∫ s in Set.Icc (-(2 * N)) (2 * N), (Work.Spaces.pz u s θ - b * u s θ) ^ 2)
        * Work.FTS.EllSol.FlatFT.wE θ := fun θ => integral_mul_const _ _
  obtain ⟨hInt, hineq⟩ := window_le_aux
    (μ := MeasureTheory.volume) (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (A := Set.Icc (-(2 * N)) (2 * N)) measurableSet_Icc
    (fun s θ => (Work.Spaces.pz u s θ - b * u s θ) ^ 2 * Work.FTS.EllSol.FlatFT.wE θ) hf h0
  refine ⟨hInt.congr (Filter.Eventually.of_forall hinner), ?_⟩
  calc (∫ θ in Work.Spaces.Iθ, (∫ s in Set.Icc (-(2 * N)) (2 * N),
        (Work.Spaces.pz u s θ - b * u s θ) ^ 2) * Work.FTS.EllSol.FlatFT.wE θ)
      = ∫ θ in Work.Spaces.Iθ, ∫ s in Set.Icc (-(2 * N)) (2 * N),
          (Work.Spaces.pz u s θ - b * u s θ) ^ 2 * Work.FTS.EllSol.FlatFT.wE θ := by
        apply integral_congr_ae
        filter_upwards with θ
        exact (hinner θ).symm
    _ ≤ ∫ p, (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2
          ∂(MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ) :
            MeasureTheory.Measure (ℝ × ℝ)) := hineq
    _ = ∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2 := by
        rw [hmeas]

end Work.FTS.EllSol.ShiftFT.Aux2
end
-- ===== merged: Submission.Work.FTS.EllSol.ShiftFT.uTrAthree.TailECont =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT.uTrAthree

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

noncomputable section

set_option autoImplicit false

/-- **Parametric continuity of an interval integral with a variable lower endpoint**, for an
integrand which is only known to be continuous on `Set.univ ×ˢ V`. -/
theorem continuousOn_intervalIntegral_param {g : ℝ → ℝ → ℝ} (V : Set ℝ) (C : ℝ)
    (hg : ContinuousOn (Function.uncurry g) (Set.univ ×ˢ V)) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ s in p.1..C, g s p.2) (Set.univ ×ˢ V) := by
  let S : Set (ℝ × ℝ) := Set.univ ×ˢ V
  have hint : Continuous (Function.uncurry (fun (x : ↥S) (s : ℝ) => g s x.1.2)) := by
    have hphi : Continuous (fun p : ↥S × ℝ => (p.2, p.1.1.2)) := by fun_prop
    exact hg.comp_continuous hphi (fun p => ⟨trivial, p.1.2.2⟩)
  have hbase : Continuous (fun x : ↥S => ∫ s in C..x.1.1, g s x.1.2) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hint (by fun_prop)
  have hmain : Continuous (fun x : ↥S => ∫ s in x.1.1..C, g s x.1.2) := by
    refine hbase.neg.congr (fun x => ?_)
    simp only [Pi.neg_apply]
    rw [intervalIntegral.integral_symm x.1.1 C, neg_neg]
  rw [continuousOn_iff_continuous_domRestrict]
  exact hmain

/-- **Continuity of the tail integral `tailE`.**  `tailE N b f t θ` is the product of the
elementary prefactor `exp (b*t)` with a parametric interval integral; both factors are
continuous on `Set.univ ×ˢ Set.Ioo 0 (π/2)` as soon as the `θ`-dependent integrand is. -/
theorem TailECont (f : ℝ → ℝ → ℝ) (N b : ℝ)
    (hf : ContinuousOn (Function.uncurry f) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllSol.ShiftFT.uTrAthree.tailE N b f p.1 p.2)
      (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hchi : Continuous (deriv (Work.FTS.EllSol.Trunc.chi N)) :=
    (Work.FTS.EllSol.Trunc.chi_contDiff 2 N).continuous_deriv (by norm_num)
  have hlin : Continuous (fun q : ℝ × ℝ => -(b * q.1)) := by fun_prop
  have hA : ContinuousOn (fun q : ℝ × ℝ =>
      Real.exp (-(b * q.1)) * deriv (Work.FTS.EllSol.Trunc.chi N) q.1)
      (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((Real.continuous_exp.comp hlin).mul (hchi.comp continuous_fst)).continuousOn
  have hg := hA.mul hf
  have hmain : ContinuousOn (fun p : ℝ × ℝ => ∫ s in p.1..(2 * N),
      Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * f s p.2)
      (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_intervalIntegral_param (Set.Ioo 0 (Real.pi / 2)) (2 * N)
      (g := fun s θ => Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * f s θ) hg
  have hexp : ContinuousOn (fun p : ℝ × ℝ => Real.exp (b * p.1))
      (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_exp.comp (by fun_prop)).continuousOn
  exact hexp.mul hmain

end

end Work.FTS.EllSol.ShiftFT.uTrAthree
end
-- ===== merged: Submission.Work.FTS.EllSol.ShiftFT.uTrAthree.UTrPthPth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT.uTrAthree

noncomputable section

set_option autoImplicit false

/-- **The first angular derivative of `uTr`.**  Since `uTr N b u = phiTr N · Gc N b u` and
`phiTr N t` does not depend on the angle, the constant factor comes out of the derivative. -/
theorem uTr_pth_eq (N b : ℝ) (u : ℝ → ℝ → ℝ) (t : ℝ) :
    Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.uTr N b u) t
      = fun θ => Work.FTS.EllSol.ShiftFT.phiTr N t
          * Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.Gc N b u) t θ := by
  funext θ
  simp only [Work.Spaces.pth, Work.FTS.EllSol.ShiftFT.uTr]
  exact deriv_const_mul_field _

/-- The tail integral `tailE` is, by definition, the second summand of `Gc N b u` with `u`
replaced by `f`. -/
theorem tailE_eq_tail (N b : ℝ) (f : ℝ → ℝ → ℝ) (t θ : ℝ) :
    tailE N b f t θ
      = Real.exp (b * t) * ∫ s in t..(2 * N),
          Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * f s θ := rfl

/-- **The second angular derivative of the truncated data.**  The double `θ`-derivative of
`uTr N b u` is `phiTr N t` times the double `θ`-derivative of `Gc N b u`, which by `Gc_pth_pth`
is `chi N t · ∂_θ²u + tailE N b (∂_θ²u)`. -/
theorem UTrPthPth (N b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ t : ℝ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Spaces.pth (Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.uTr N b u)) t θ
        = Work.FTS.EllSol.ShiftFT.phiTr N t
          * (Work.FTS.EllSol.Trunc.chi N t
              * Work.Spaces.pth (Work.Spaces.pth u) t θ
              + Work.FTS.EllSol.ShiftFT.uTrAthree.tailE N b
                  (Work.Spaces.pth (Work.Spaces.pth u)) t θ) := by
  intro t θ hθ
  have hGc := Work.FTS.EllSol.ShiftFT.Gc_pth_pth N b u hu t θ hθ
  calc Work.Spaces.pth (Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.uTr N b u)) t θ
      = deriv (fun θ' => Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.uTr N b u) t θ') θ := rfl
    _ = deriv (fun θ' => Work.FTS.EllSol.ShiftFT.phiTr N t
            * Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.Gc N b u) t θ') θ := by
          rw [uTr_pth_eq N b u t]
    _ = Work.FTS.EllSol.ShiftFT.phiTr N t
          * deriv (fun θ' => Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.Gc N b u) t θ') θ :=
          deriv_const_mul_field _
    _ = Work.FTS.EllSol.ShiftFT.phiTr N t
          * Work.Spaces.pth (Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.Gc N b u)) t θ := rfl
    _ = Work.FTS.EllSol.ShiftFT.phiTr N t
          * (Work.FTS.EllSol.Trunc.chi N t
              * Work.Spaces.pth (Work.Spaces.pth u) t θ
              + Work.FTS.EllSol.ShiftFT.uTrAthree.tailE N b
                  (Work.Spaces.pth (Work.Spaces.pth u)) t θ) := by
          rw [hGc, tailE_eq_tail]

end

end Work.FTS.EllSol.ShiftFT.uTrAthree
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeS1.sigmaUpD =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeS1

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

/-!
**The σ-Poincaré upgrade of the `u`-norm** in the almost-everywhere class `H2W.Ae.AeData`:
`HkSq α 0 u ≤ C · L2Sq (∂_θu · w)`, i.e. `‖u‖_ρ ≤ C‖∂_θu‖_{w²}`.

The *same* statement is already proved in this workspace as `Dispatch.aeSigmaUpD`
(`Dispatch/cores_level_zero.lean`, from the axiom-clean `H2W.AeProof.AeSigmaUpgradeU_all` via
`MeasureTheory.integral_eq_lintegral_of_nonneg_ae`), but that module's import cone currently
contains `Honest/firstOrderHonest`, which is mid-refactor and fails to build; the proof body
there is ported into this file (set the slice integrands
`z ↦ ∫θ u²σ`, `z ↦ ∫θ (∂_θu)²`, compare them with the `∫⁻`-inequality of
`AeSigmaUpgradeU_all` via `ofReal_integral_eq_lintegral_ofReal` /
`lintegral_ofReal_ne_top_iff_integrable`, and finish with `integral_mono_ae`), so that this
version is self-contained.  It does not import `Dispatch.cores_level_zero` nor
`H2W.Ae.hkMem_u`.
-/
theorem sigmaUpD : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.L2Mem (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z) →
      Work.Spaces.HkSq α 0 u
        ≤ C * Work.Spaces.L2Sq (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.FTS.EllipticEst.H2W.AeProof.AeSigmaUpgradeU_all
  refine ⟨C₀, hC₀pos, ?_⟩
  intro α u G hA hL2
  -- ## abbreviations
  set Asl : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    with hAsl
  set Bsl : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2 with hBsl
  set Apr : ℝ → ℝ≥0∞ := fun z => ∫⁻ θ in Work.Spaces.Iθ,
    ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) with hApr
  set Bpr : ℝ → ℝ≥0∞ := fun z => ∫⁻ θ in Work.Spaces.Iθ,
    ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2) with hBpr
  -- ## elementary facts
  have hsEta_nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Work.FTS.EllipticEst.sEta θ := by
    intro θ hθ
    show 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    exact Real.rpow_nonneg (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ) _
  have hAsl_nn : ∀ z, 0 ≤ Asl z := by
    intro z
    rw [hAsl]
    exact setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (hsEta_nn θ hθ))
  have hBsl_nn : ∀ z, 0 ≤ Bsl z := by
    intro z
    rw [hBsl]
    exact setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  -- ## the level-`0` integrand is `w²·(u²σ)`
  have hptid : ∀ z θ, θ ∈ Work.Spaces.Iθ →
      Work.Spaces.HkIntegrand α 0 u z θ
        = (Work.Spaces.w z) ^ 2 * ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    intro z θ hθ
    rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq, mul_pow,
      Work.FTS.EllipticEst.Honest.sq_weight_eq (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ)]
    simp only [Work.FTS.EllipticEst.sEta]
    ring
  have hslice : ∀ z, (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
      = (Work.Spaces.w z) ^ 2 * Asl z := by
    intro z
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    exact hptid z θ hθ
  -- ## `HkSq` as a `toReal` of a `lintegral`
  have hHk : Work.Spaces.HkSq α 0 u
      = (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * Asl z)).toReal := by
    rw [Work.FTS.EllipticEst.HkSq_eq_lintegral α 0 u hA.smooth]
    congr 1
    exact MeasureTheory.lintegral_congr fun z => by rw [hslice z]
  -- ## `L2Sq` as a `toReal` of a `lintegral`
  have hL2pt : (fun z => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2)
      = fun z => (Work.Spaces.w z) ^ 2 * Bsl z := by
    funext z
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    ring
  have hL2mem : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * Bsl z) Work.Spaces.Iz :=
    hL2.2.congr_fun (fun z _ => congr_fun hL2pt z) measurableSet_Ici
  have hL2l : Work.Spaces.L2Sq (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z)
      = (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * Bsl z)).toReal := by
    rw [Work.Spaces.L2Sq, hL2pt]
    exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (hBsl_nn z))
      hL2mem.aestronglyMeasurable
  -- ## the slicewise measurability of `u²σ`
  have hslice_smooth : ∀ z, 0 < z →
      ContDiffOn ℝ 1 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) := by
    intro z hz
    have hmap : MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun θ hθ => ⟨hz, hθ⟩
    exact (hA.smooth 1).comp (by fun_prop) hmap
  have haesm_slice : ∀ z, 0 < z → AEStronglyMeasurable
      (fun θ => (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    exact ((Work.FTS.EllipticEst.Honest.aesm_of_contDiffOn_Ioo (hslice_smooth z hz)).pow 2).mul
      (Work.FTS.EllipticEst.H2W.Ae.measurable_sEta.aestronglyMeasurable)
  -- ## the slicewise identity `Asl z = (∫⁻ ...).toReal`
  have hAsl_eq : ∀ z, 0 < z → Asl z = (Apr z).toReal := by
    intro z hz
    rw [hAsl, hApr]
    refine MeasureTheory.integral_eq_lintegral_of_nonneg_ae ?_ (haesm_slice z hz)
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (hsEta_nn θ hθ))
  -- ## pointwise domination, a.e. in `z`
  have hdom_ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * Asl z)
        ≤ ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Apr z := by
    rw [Work.Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici]
    have hne : ∀ᵐ z ∂(MeasureTheory.volume : Measure ℝ), z ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [hne] with z hz hzI
    have hzpos : 0 < z := lt_of_le_of_ne hzI (Ne.symm hz)
    rw [ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z))]
    refine mul_le_mul_of_nonneg_left ?_ bot_le
    rw [hAsl_eq z hzpos]
    exact ENNReal.ofReal_toReal_le
  have hstepA : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * Asl z))
      ≤ ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Apr z :=
    MeasureTheory.lintegral_mono_ae hdom_ae
  -- ## the proved slicewise upgrade
  have hup : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Apr z)
      ≤ ENNReal.ofReal C₀ * (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Bpr z) :=
    hC₀ α u G hA
  -- ## the two `∫⁻`-expressions agree with the Bochner ones
  have hint2 : ∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pth u z θ) ^ 2) Work.Spaces.Iθ := by
    intro z hz
    have hwz : Work.Spaces.w z ≠ 0 := by
      rw [Work.Spaces.w]; positivity
    have hint : MeasureTheory.Integrable
        (fun θ => (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hL2.1 z (le_of_lt hz)
    have hdiv : MeasureTheory.Integrable
        (fun θ => (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2 / (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hint.div_const _
    have haeeq : (fun θ => (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2
          / (Work.Spaces.w z) ^ 2) =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ => (Work.Spaces.pth u z θ) ^ 2) := by
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => ?_)
      field_simp
    exact hdiv.congr haeeq
  have hBsl_eq : ∀ z, 0 < z → Bsl z = (Bpr z).toReal := by
    intro z hz
    rw [hBsl, hBpr]
    refine MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun θ => sq_nonneg _) (hint2 z hz).aestronglyMeasurable
  have hBpr_ne : ∀ z, 0 < z → Bpr z ≠ ⊤ := by
    intro z hz
    rw [hBpr]
    exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable (hint2 z hz).aestronglyMeasurable
      (Filter.Eventually.of_forall fun θ => sq_nonneg _)).mpr (hint2 z hz)
  have hCeq_ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Bpr z
        = ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * Bsl z) := by
    rw [Work.Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici]
    have hne : ∀ᵐ z ∂(MeasureTheory.volume : Measure ℝ), z ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [hne] with z hz hzI
    have hzpos : 0 < z := lt_of_le_of_ne hzI (Ne.symm hz)
    rw [hBsl_eq z hzpos, ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z)),
      ENNReal.ofReal_toReal (hBpr_ne z hzpos)]
  have hstepC : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Bpr z)
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * Bsl z) :=
    MeasureTheory.lintegral_congr_ae hCeq_ae
  -- ## finiteness of the right-hand side
  have hYne : (∫⁻ z in Work.Spaces.Iz,
      ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * Bsl z)) ≠ ⊤ := by
    refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      hL2mem.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (hBsl_nn z))).mpr hL2mem
  have hBne : (∫⁻ z in Work.Spaces.Iz,
      ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Bpr z) ≠ ⊤ := by
    rw [hstepC]; exact hYne
  have hBne' : ENNReal.ofReal C₀ * (∫⁻ z in Work.Spaces.Iz,
      ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Bpr z) ≠ ⊤ := by
    rw [hstepC]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hYne
  have hAne : (∫⁻ z in Work.Spaces.Iz,
      ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Apr z) ≠ ⊤ :=
    ne_top_of_le_ne_top hBne' hup
  -- ## assembly
  calc Work.Spaces.HkSq α 0 u
      = (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * Asl z)).toReal := hHk
    _ ≤ (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Apr z).toReal :=
        ENNReal.toReal_mono hAne hstepA
    _ ≤ (ENNReal.ofReal C₀ * ∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Bpr z).toReal :=
        ENNReal.toReal_mono hBne' hup
    _ = C₀ * (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Bpr z).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC₀pos.le]
    _ = C₀ * Work.Spaces.L2Sq (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z) := by
        rw [hstepC, ← hL2l]

end Work.FTS.EllipticEst.AeS1
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Blocks.DzAgmon1D =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Blocks

/-- **The weighted Agmon inequality for `D = z∂_z` on the half-line, `lintegral` form.**

There is a universal `C > 0` such that for every `0 < α ≤ 1` and every `h` of class `C^∞` on
`(0,∞)` (in terms of `Work.Stability.smoothOrder`, the *genuine* `C^∞` order, not the analytic
order `⊤`),

`ofReal (α²) * ∫⁻_{Ioi 0} ofReal (w(z)² (z h')²) ≤ ofReal (C²) *
   (ofReal (α⁴) * ∫⁻_{Ioi 0} ofReal (w(z)² (z²h'')²) + ∫⁻_{Ioi 0} ofReal (w(z)² h²))`.

No integrability hypothesis is required: if one of the two data integrals is `⊤` the inequality is
trivial, and otherwise it also yields the finiteness of `∫⁻ ρ (zh')²`. -/
theorem DzAgmon1D_lintegral : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (h : ℝ → ℝ), 0 < α → α ≤ 1 →
      ContDiffOn ℝ Work.Stability.smoothOrder h (Set.Ioi (0 : ℝ)) →
      ENNReal.ofReal (α ^ 2) *
          MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
            (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2))
        ≤ ENNReal.ofReal (C ^ 2) *
            (ENNReal.ofReal (α ^ 4) *
                MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                  (fun z => ENNReal.ofReal
                    ((Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2))
              + MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                  (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (h z) ^ 2))) := by
  obtain ⟨C₀, hC₀, hfts⟩ := Work.FTS.EllipticEst.AgmonFts.rDz_agmon_lintegral_fts
  refine ⟨Real.sqrt C₀, Real.sqrt_pos_of_pos hC₀, ?_⟩
  rw [Real.sq_sqrt hC₀.le]
  intro α h hα hα1 hh
  -- `Iz` and `Ioi 0` carry the same measure
  have hIz : ∀ F : ℝ → ENNReal, (MeasureTheory.lintegral
        (MeasureTheory.volume.restrict Work.Spaces.Iz) F)
      = MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) F := by
    intro F
    show MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))) F
        = MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) F
    rw [← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
  have hineq := hfts α hα hα1 h hh
  -- `rDz h z = z h'(z)` definitionally
  have hrDz : ∀ z : ℝ, Work.FTS.EllipticEst.rDz h z = z * deriv h z := fun z => rfl
  simp only [hrDz] at hineq
  have e1 : (MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iz)
        (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (h z) ^ 2)))
      = MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (h z) ^ 2)) := hIz _
  have e2 : (MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iz)
        (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2)))
      = MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2)) :=
    hIz _
  have e3 : (MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iz)
        (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2)))
      = MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2)) := hIz _
  rw [e1, e2, e3] at hineq
  refine hineq.trans (le_of_eq ?_)
  rw [add_comm]

end Work.FTS.EllipticEst.Blocks
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.HonSlot =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores

set_option autoImplicit false

/-! ## The level-`0` integrand -/

/-- At order `0` the `ℋ^0`-integrand is the single weighted square of the function itself (the
mixed sum is empty because every mixed slot carries `1 ≤ i` with `i + j ≤ 0`, which is
unsatisfiable). -/
theorem HkIntegrand_zero_apply (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

/-! ## Single-slot honesty -/

/-- **A single pure `D_z`-slot of an honest `ℋ^k`-function is honest at order `0`.**  This is the
`ℋ^k`-analogue of `TT.HkMem_descend_open` for *other* slots than the function itself: the slot
`D_z^i f` is bounded pointwise by the whole integrand (`Work.Spaces.sq_le_HkIntegrand_z`), and the
open-quadrant smoothness of `f` makes the smaller integrand continuous there, hence a.e. strongly
measurable. -/
theorem HkMem_zero_of_DzIter_slot {α : ℝ} {k i : ℕ} {f : ℝ → ℝ → ℝ} (hi : i ≤ k)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α 0 (Work.Spaces.DzIter i f) :=
  Work.FTS.LocData.HkMem_of_majorant α 0
    ((hf.DzIter i).continuousOn_HkIntegrand α 0) hm.1 hm.2
    (fun z _ θ _ => by
      rw [HkIntegrand_zero_apply]
      exact Work.Spaces.sq_le_HkIntegrand_z α k f z θ i hi)


/-! ## The honesty the trace-free class supplies -/

/-- `SmoothQuad f` implies `SmoothOpen f` (the strip of `SmoothQuad` contains the open
quadrant). -/
theorem smoothOpen_of_smoothQuad {f : ℝ → ℝ → ℝ}
    (h : Work.FTS.LocData.SmoothQuad f) : Work.FTS.EllipticEst.SmoothOpen f :=
  h.mono (by
    rw [Work.FTS.EllipticEst.Q0]
    exact Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num)) (le_refl _))




end Work.FTS.EllipticEst.Cores
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.PsiSlices.ReductionsA =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.PsiSlices

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-! ## Elementary comparison facts for the weight `sinθcos²θ` -/






/-- `sinθcos²θ ≥ 0` on the closed interval `Iθ`. -/
theorem sinCos2_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Elliptic.sinCos2 θ := by
  obtain ⟨h0, h1⟩ := hθ
  rw [Work.Elliptic.sinCos2]
  exact mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [h1, Real.pi_pos]))
    (sq_nonneg _)




/-! ## The level-`0` identity and propagation -/



end

/- Datum-side (`Ψ`-side) angular-endpoint statement of the weak class `WeakPos2`: for a.e. `z > 0`,
each angular slice `θ ↦ ∂_z^m Ψ(z,θ)` with `m ≤ 4` is integrable against `sinθcos²θ` on
`Iθ = [0, π/2]`.

What is and is not being asked.  The weight `sinθcos²θ` vanishes like `t²` at `θ = π/2`
(`t = π/2-θ`) and like `θ` at `θ = 0`, so the conclusion tolerates any growth `o(t^{-3})` at
`π/2` and any growth `o(θ^{-2})` at `0` — in particular the genuine `t^{-1}` pole and even
`t^{-1}log^k(1/t)`.  This is *strictly weaker* than the pole bound
`|∂_z^m Ψ| ≤ C(θ⁻¹ + (π/2-θ)⁻¹)` (which is equivalent to *boundedness* of the slices, see
`H2W/WeakPureAux/NOTES_weakPzPoleBound.md` §0).  It is *not* refuted by the
"mixture"/hidden-`t log t`-mode datum of `H2W/NOTES_pzIterSliceGrowth3Loc.md` §3 (a `t^{-1}`
pole whose `t^{-1}` source coefficient is cancelled by a hidden `t log t` indicial mode): that
datum satisfies this statement.

Why it is needed.  It is the single remaining input of `Work.FTS.EllipticEst.H2W.lzeroSliceL1Ae`
(carried there in-file as `pzIterSliceIntegrableInput`), which combines it with the level
identities `Lzero(∂_z^j Ψ) = ∂_z^j F + α²z²∂_z^{j+2}Ψ + α(5+α)(z∂_z^{j+1}Ψ + j∂_z^j Ψ)` and with
the delivered source-side sibling `H2W.lzeroSliceFiber` (slices of `F`, `i ≤ 2`).  The same
statement is the target of `H2W/pzIterSliceIntegrableUpTo4.lean` (whose source no longer
elaborates: module docstring before the `import` block) and it is *also* implied by the pole
bound `H2W.pzIterPoleBoundUpTo4` (whose final declaration is `sorry`).

Ingredients available in the tree.  `H2W.pzSlice.*` — `LzeroSolSpan` (every solution of
`Lzero1 u = 0` is `a·sin 2θ + b·LzeroSing`), `LzeroSingPole`, `VdpDefs`/`vdpSolves` (the
variation-of-parameters solution with the two bounded kernels), `kernelBound`, `lzeroSingBounds`,
`growthOfMinSource` (pole bound from an honest source), all `sorry`-free; the separable case of
the rigidity `H2W/SeparableCase.lean`; the level-0 weak-class slice growth
`H2W/WeakPureAux/sliceGrowth_of_weakPos0.lean` and its two open conjuncts
`weakPzPoleBound`/`weakPzIter2PoleBound`; `Mine/SliceMomentTaylor`
(`∫ f²·sEta < ∞ ⟹ ∫|f|·sinθcos²θ < ∞`, with the accompanying
`Remov.SourceBound.absIntegrableOfSqMulSeta` variants); and the `D_z`-shift
`H2W/shiftWeakClass.lean` (`WeakPos2 ⟹ WeakPos0 (D_z^j F) (D_z^j Ψ)`, `j ≤ 2`, two `sorry`s in
its Ψ-moment clauses).  Note `m ≤ 3` alone follows from the (in-file `sorry`-free)
`H2W.pzIterSliceGrowth3` pole bound, so the genuinely new content is the top level `m = 4`. -/

/-! ## Where the gap exactly is (analysis, not a proof)

The reductions in this file are *sharp*: the `z`-regress of the tower closes downward from the
levels `3, 4` (using the shifted bridges and the source honesty `F_0, F_1, F_2` supplied by
`H2W.lzeroSliceFiber`), and it cannot be started any lower, because a downward step from level
`j` needs the honesty of the *source* `D_z^j F`, which the class provides only for `j ≤ 2`.
Hence the target is *equivalent* to the `sinθcos²θ`-honesty of the two top levels.

Two facts about the obstruction, verified in this session (recorded for the next stretch; both
are stated as prose, neither is used by any declaration below):

* **Compatible profiles have order `≤ 1`.**  Expand a slice near `θ = π/2` in the pure powers
  `t^{-M}` (`t = π/2-θ`).  The tower
  `Lzero1(∂_z^mΨ) = ∂_z^mF + α²z²∂_z^{m+2}Ψ + α(5+α)z∂_z^{m+1}Ψ` becomes, at the order
  `t^{-(M+2)}`,
  `(1-M²)a_M = (6+R)a_{M+2} - (M+1)∑_{j≥1}d_j a_{M+2j} + f_{M+2}`, `R = α²z²∂_z²+5αz∂_z`,
  where `d_j` are the coefficients of `cot t = ∑d_jt^{2j-1}` and `f` the coefficients of `F`.
  `HkMem α 2 F` (per fibre, at *every* `z`) forces `f_M = 0` for `M ≥ 3`, so for `M ≥ 2` the
  coefficient `a_M` is *determined* by the higher ones through a second-order ODE in `z`; if all
  the higher coefficients vanish then `(1-M²)a_M = 0`, i.e. `a_M = 0` for `M ≥ 2`.  The only
  "free" levels are the resonances `M = ±1` (the two kernel elements `sin 2θ`, `LzeroSing`).
  Consequently a slice of order `≥ 2` is *impossible* with finitely many profiles, and any
  counterexample would have to be an *infinite* cascade, whose coefficient functions `a_M(z)`
  are related by repeated applications of the second-order operator `(6+R)^{-1}` (which is
  *unbounded at `z = 0`*, with kernel spanned by `z^{-2/α}, z^{-3/α}`), while the source's
  `HkMem` (a `z`-integrability of `F` against `w² = z^{-4}(1+z)^4` near `0`) constrains how
  badly the cascade may blow up at `z = 0`.  Deciding whether the cascade can be summed to a
  `C^∞` function is exactly the open "Gevrey/cascade" problem of
  `H2W/WeakPureAux/NOTES_cascade.md`, `H2W/WeakPureAux/NOTES_weakPhiPoleBound.md` §K, §U.
* **The a.e.-relaxation does not help.**  The class and the conclusion are both covariant under
  the radial dilations `z ↦ λz` (`H2W.PsiSlices.weakPos2_dilate`, `H2W.PsiSlices.pzIter_dilate`),
  so the a.e.-statement is *equivalent* to the pointwise statement at the single point `z = 1`
  (`pzIterSliceIntegrable_of_at_one_clean`): a counterexample only has to exist at one `z`, and
  a proof only has to work at one `z`.  In particular no null-set argument can replace the
  endpoint rigidity. -/


end Work.FTS.EllipticEst.H2W.PsiSlices
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.WeakPureAux.cascadeBalance =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `WeakPureAux/cascadeBalance` — the exact amplitude balance of the cascade at `θ = π/2`

`WeakPureAux/NOTES_weakPhiPoleBound.md` §K records (numerically confirmed, by hand) that the
level amplitudes `a_k` of a slice expanded in `θ`-profiles `t^{-k}` satisfy the *linear* recursion

  `(R - λ_k) a_k = (1 - (k-2)²) a_{k-2} + ((k+1)/3 - 6) a_k`,

whose coefficients grow like `6^m m!`, so the cascade cannot be summed.  This module formalises
the *first* half of that statement, which is the part that needs no arithmetic:

**if the source has no component of order `N+2` (`(π/2-θ)^{N+2}·G(z,θ) → 0`) and the slice has a
pure power of order `N ≥ 2` with amplitude `B`, then**

  `(1 - N²)·B = α²z²·B₂ + α(5+α)z·B₁`,   (⋆)

where `B₁`, `B₂` are the order-`(N+2)` amplitudes of `∂_zΦ(z,·)` resp. `∂_z²Φ(z,·)`.  Reading
`(⋆)` as a recursion `N ↦ N+2` (the radial operator `R = α²z²∂_z² + α(5+α)z∂_z` applied to the
*next* amplitude is `(1-N²)` times the current one), it is exactly the statement that the
`θ`-order of the slice can only be pushed upwards along the levels — the mechanism of §K.

The engine is the proved `SliceA.Lzero1_order_shift`: at `θ = π/2` the operator `Lzero1` shifts a
pure power of order `N` to order `N+2` with the coefficient `1 - N²`, and no term of order `N`
(the radial part of the equation) can cancel that leading term.
-/

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

namespace Work.FTS.EllipticEst.H2W.WeakPureAux

local notation "Lθ" => nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))



end Work.FTS.EllipticEst.H2W.WeakPureAux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.sliceSourceMassBound_of_external =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-! ### STUBS for the two delegated lemmas (will become imports) -/

/-! ### 1. Small helpers -/











/-! ### 2. The `∂_z`-slices of the source, bounded by the `D_z`-slices -/



/-! ### 3. Mass bound for the `∂_z`-slices of the source -/



/-! ### 4. Definitions used by the per-slice estimate -/






/-! ### 5. The per-slice estimate -/


/-! ### 5b. The expansion of `Lzero (∂_z^m Ψ)` for `m ≤ 3`

The identity that turns the `WeakPos2` equation `bslOp α Ψ = F` into a bound on the source
`Lzero1 (∂_z^m Ψ(z,·))` in terms of the slices of `Ψ` and `F`.  Levels `0`, `1`, `2` are the
lemmas `lzero_level0_pt`, `lzero_level1_pt`, `lzero_level2_pt` of
`Submission/Work/FTS/EllipticEst/H2W/lzeroSliceL1Ae.lean`; level `3` is proved here from the
same template. -/


/-! ## Differentiability of the `z`-slices on the open quadrant -/


/-! ## The level-`0` form of the equation -/


/-! ## `∂_z` commutes with `Lzero` on the open quadrant -/



/-! ## Product rules (used by the Leibniz expansion of `Lzero (∂_z^jΨ)`) -/


















/-! ### 6. Constant integrability on `Iθ` -/


/-! ### 7. The main theorem -/


end

end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.ESW.Tk_B_le_chain_uniform =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ESW.Tk_B_le_chain_uniform`: the top angular slot, with a constant uniform in `α` and `Ψ`

`Tk_B_le_chain` (in `ChainAux.lean`) proves, for *fixed* `α` and `Ψ`,

`Step.Tk α k (∂_θθΨ) ≤ C(α,Ψ) · (Σ_{1 ≤ r ≤ k-1} ∫∫ (∂_θ^r∂_θθΨ)² w² sin^{2r-γ}
   + ∫∫ (∂_θ^{k+2}Ψ)² w² sin^{2k-γ})`

with a constant `C(α,Ψ)` that is allowed to depend on the datum.  Here we remove that
dependence: the assembly `Tk_chain_of` and the pointwise chain both use a constant depending
on `k` only, so a single constant works for all `α` and all `Ψ` simultaneously.

The content is

* `TkChain_pointwise`: the pointwise forward chain
  `(D_θ^k v · W_t)² ≤ C_k · Σ_{1 ≤ r ≤ k} w² (∂_θ^r v)² sin(2θ)^{2r-γ}`,
  obtained from the *exact* expansion `D_θ^k v = Σ_{r ≤ k} a_{k,r}(θ) ∂_θ^r v` with
  `a_{k,r} = sin(2θ)^r · b_{k,r}` (`b_{k,r}` bounded, `a_{k,0} = 0`) followed by
  Cauchy–Schwarz.  The constant is `k · K²` with `K` a bound for the `b_{k,r}`, hence
  depends on `k` but neither on `α` nor on `v`;
* `Tk_B_le_chain_fixed`: the measure-theoretic assembly `Tk_chain_of` +
  `Icc 1 k = insert k (Icc 1 (k-1))` + `∂_θ^k∂_θ²Ψ = ∂_θ^{k+2}Ψ`, with the constant kept
  explicit (`Ca` on both sides) instead of hidden behind an existential;
* the target `Tk_B_le_chain_uniform`, by pulling the existential out of `α`, `Ψ`.
-/

namespace Work.FTS.EllipticEst.TT.ESW

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Two elementary bookkeeping lemmas -/

/-- The weight split `sin(2θ)^{2r-γ} = sin(2θ)^{2r}·sin(2θ)^{-γ}` in the shape needed by the
chain: on the interval where `sin(2θ) > 0`, `Real.rpow_add` gives the additive splitting and
`Real.rpow_natCast` converts the natural power `sin(2θ)^{2r}`. -/
theorem sin_rpow_split {θ : ℝ} (hs : 0 < Real.sin (2 * θ)) (r : ℕ) (γ : ℝ) :
    Real.sin (2 * θ) ^ (2 * (r : ℝ) - γ)
      = (Real.sin (2 * θ) ^ r) ^ 2 * Real.sin (2 * θ) ^ (-γ) := by
  have h1 : (2 * (r : ℝ) - γ) = ((2 * r : ℕ) : ℝ) + (-γ) := by push_cast; ring
  rw [h1, Real.rpow_add hs, Real.rpow_natCast, ← pow_mul, Nat.mul_comm 2 r]

/-- Reindexing `Icc 1 k` against `range k`: `Σ_{1 ≤ r ≤ k} f r = Σ_{i < k} f (i+1)`. -/
theorem sumIccOne_eq (k : ℕ) (f : ℕ → ℝ) :
    ∑ r ∈ Finset.Icc 1 k, f r = ∑ i ∈ Finset.range k, f (i + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-! ## The pointwise forward chain -/

/-- **The pointwise `D_θ`-chain, with a constant depending on `k` only.**  For `k ≥ 1`, at every
point where `v` is `C^∞`, the top angular slot `(D_θ^k v · W_t)²` is dominated by the plain
angular slots `(∂_θ^r v)² sin(2θ)^{2r-γ}`, `1 ≤ r ≤ k`.

The proof uses the exact expansion `D_θ^k v = Σ_{r ≤ k} a_{k,r}(θ) ∂_θ^r v`
(`selfdth.DthIter_expansion_local`) together with the divisibility `a_{k,r} = sin(2θ)^r b_{k,r}`
with `b_{k,r}` bounded (`selfdth.dthCoef_eq_sin_pow_mul_dB`, `selfdth.dB_bounded`) and the
vanishing of the `r = 0` coefficient (`selfdth.dB_apply_zero_of_one_le`); Cauchy–Schwarz on the
resulting `k`-term sum and the weight identity `sin^{-γ}·sin^{2r} = sin^{2r-γ}` finish it. -/
theorem TkChain_pointwise (k : ℕ) (hk : 1 ≤ k) :
    ∃ Ca : ℝ, 0 < Ca ∧ ∀ (α : ℝ) (v : ℝ → ℝ → ℝ) (z θ : ℝ),
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (∀ n : ℕ, ContDiffAt ℝ n (Function.uncurry v) (z, θ)) →
      (Work.Spaces.DthIter k v z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Ca * ∑ r ∈ Finset.Icc 1 k, ChainG α v z θ r := by
  classical
  choose KB hKB using fun r : ℕ => Work.FTS.EllipticEst.remov.selfdth.dB_bounded k r
  set KD : ℝ := 1 + ∑ r ∈ Finset.Icc 1 k, (KB r + 1) with hKD
  have hKD1 : 1 ≤ KD := by
    rw [hKD]
    have h : 0 ≤ ∑ r ∈ Finset.Icc 1 k, (KB r + 1) :=
      Finset.sum_nonneg (fun r _ => by linarith [(hKB r).1])
    linarith
  have hKDb : ∀ (r : ℕ) (θ : ℝ), 1 ≤ r → r ≤ k →
      |Work.FTS.EllipticEst.remov.selfdth.dB k r θ| ≤ KD := by
    intro r θ hr1 hrk
    have h1 : KB r + 1 ≤ ∑ r' ∈ Finset.Icc 1 k, (KB r' + 1) :=
      Finset.single_le_sum (f := fun r' => KB r' + 1)
        (fun r' _ => by linarith [(hKB r').1]) (Finset.mem_Icc.mpr ⟨hr1, hrk⟩)
    have h2 : |Work.FTS.EllipticEst.remov.selfdth.dB k r θ| ≤ KB r := (hKB r).2 θ
    rw [hKD] at *
    linarith
  refine ⟨(k : ℝ) * KD ^ 2, by positivity, ?_⟩
  intro α v z θ hθ hf
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hdB0 : Work.FTS.EllipticEst.remov.selfdth.dB k 0 θ = 0 :=
    congrFun (Work.FTS.EllipticEst.remov.selfdth.dB_apply_zero_of_one_le k hk) θ
  have hdc0 : Work.FTS.EllipticEst.remov.selfdth.dthCoef k 0 θ = 0 := by
    rw [congrFun (Work.FTS.EllipticEst.remov.selfdth.dthCoef_eq_sin_pow_mul_dB k 0) θ,
      hdB0, mul_zero]
  -- Step 1: the triangular expansion, with the `r = 0` term dropped
  have hstep1 : |Work.Spaces.DthIter k v z θ|
      ≤ KD * ∑ r ∈ Finset.Icc 1 k,
          (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r v z θ| := by
    have hexp : Work.Spaces.DthIter k v z θ
        = ∑ r ∈ Finset.range (k + 1),
            Work.FTS.EllipticEst.remov.selfdth.dthCoef k r θ
              * Work.Spaces.pthIter r v z θ :=
      Work.FTS.EllipticEst.remov.selfdth.DthIter_expansion_local k v z θ hf
    rw [hexp, Finset.sum_range_succ']
    simp only [hdc0, zero_mul, add_zero]
    have h1 : |∑ i ∈ Finset.range k, Work.FTS.EllipticEst.remov.selfdth.dthCoef k (i + 1) θ
          * Work.Spaces.pthIter (i + 1) v z θ|
        ≤ ∑ i ∈ Finset.range k,
            (Real.sin (2 * θ)) ^ (i + 1)
              * |Work.FTS.EllipticEst.remov.selfdth.dB k (i + 1) θ|
              * |Work.Spaces.pthIter (i + 1) v z θ| := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine Finset.sum_le_sum fun i _ => ?_
      rw [show Work.FTS.EllipticEst.remov.selfdth.dthCoef k (i + 1) θ
          = (Real.sin (2 * θ)) ^ (i + 1) * Work.FTS.EllipticEst.remov.selfdth.dB k (i + 1) θ
          from congrFun (Work.FTS.EllipticEst.remov.selfdth.dthCoef_eq_sin_pow_mul_dB k (i + 1)) θ,
        abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hs.le _)]
    have h2 : ∑ i ∈ Finset.range k,
            (Real.sin (2 * θ)) ^ (i + 1)
              * |Work.FTS.EllipticEst.remov.selfdth.dB k (i + 1) θ|
              * |Work.Spaces.pthIter (i + 1) v z θ|
        ≤ ∑ i ∈ Finset.range k,
            KD * ((Real.sin (2 * θ)) ^ (i + 1) * |Work.Spaces.pthIter (i + 1) v z θ|) := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hi1 : i + 1 ≤ k := by have := Finset.mem_range.mp hi; omega
      have hb : |Work.FTS.EllipticEst.remov.selfdth.dB k (i + 1) θ| ≤ KD :=
        hKDb (i + 1) θ (by omega) hi1
      have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (i + 1) := pow_nonneg hs.le _
      have ha : 0 ≤ |Work.Spaces.pthIter (i + 1) v z θ| := abs_nonneg _
      calc (Real.sin (2 * θ)) ^ (i + 1)
            * |Work.FTS.EllipticEst.remov.selfdth.dB k (i + 1) θ|
            * |Work.Spaces.pthIter (i + 1) v z θ|
          ≤ (Real.sin (2 * θ)) ^ (i + 1) * KD
              * |Work.Spaces.pthIter (i + 1) v z θ| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hsnn) ha
        _ = KD * ((Real.sin (2 * θ)) ^ (i + 1)
              * |Work.Spaces.pthIter (i + 1) v z θ|) := by ring
    have h3 : (∑ i ∈ Finset.range k,
            KD * ((Real.sin (2 * θ)) ^ (i + 1) * |Work.Spaces.pthIter (i + 1) v z θ|))
        = KD * ∑ r ∈ Finset.Icc 1 k,
            (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r v z θ| := by
      rw [sumIccOne_eq k (fun r => (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r v z θ|),
        Finset.mul_sum]
    calc |∑ i ∈ Finset.range k, Work.FTS.EllipticEst.remov.selfdth.dthCoef k (i + 1) θ
          * Work.Spaces.pthIter (i + 1) v z θ| ≤ _ := h1
      _ ≤ _ := h2
      _ = _ := h3
  -- Step 2: Cauchy-Schwarz on the `k`-term chain
  have hcs : (Work.Spaces.DthIter k v z θ) ^ 2 ≤ KD ^ 2 *
      ((k : ℝ) * ∑ r ∈ Finset.Icc 1 k,
        ((Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r v z θ|) ^ 2) := by
    have h1 : (Work.Spaces.DthIter k v z θ) ^ 2 = |Work.Spaces.DthIter k v z θ| ^ 2 :=
      (sq_abs _).symm
    rw [h1]
    have h2 : |Work.Spaces.DthIter k v z θ| ^ 2
        ≤ (KD * ∑ r ∈ Finset.Icc 1 k,
            (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r v z θ|) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hstep1 2
    have h4 : (∑ r ∈ Finset.Icc 1 k,
          (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r v z θ|) ^ 2
        ≤ (k : ℝ) * ∑ r ∈ Finset.Icc 1 k,
            ((Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r v z θ|) ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq (s := Finset.Icc 1 k)
        (f := fun r => (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r v z θ|)
      rw [Nat.card_Icc, show k + 1 - 1 = k from by omega] at h
      exact h
    calc |Work.Spaces.DthIter k v z θ| ^ 2
        ≤ (KD * ∑ r ∈ Finset.Icc 1 k,
            (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r v z θ|) ^ 2 := h2
      _ = KD ^ 2 * (∑ r ∈ Finset.Icc 1 k,
            (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r v z θ|) ^ 2 := by rw [mul_pow]
      _ ≤ KD ^ 2 * ((k : ℝ) * ∑ r ∈ Finset.Icc 1 k,
            ((Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r v z θ|) ^ 2) :=
          mul_le_mul_of_nonneg_left h4 (sq_nonneg KD)
  -- Step 3: insert the weight `(W_t)² = w² sin^{-γ}` slot by slot
  have hWt : (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow]
    congr 1
    rw [sq, ← Real.rpow_add hs]
    congr 1
    ring
  have hXnn : 0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs.le _)
  have hterm : ∀ r ∈ Finset.Icc 1 k,
      ((Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r v z θ|) ^ 2
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        = ChainG α v z θ r := by
    intro r _
    rw [ChainG]
    change ((Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r v z θ|) ^ 2
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = Work.Spaces.w z ^ 2 * (Work.Spaces.pthIter r v z θ ^ 2
          * Real.sin (2 * θ) ^ (2 * (r : ℝ) - Work.Spaces.gam α))
    rw [sin_rpow_split hs r (Work.Spaces.gam α), mul_pow, sq_abs]
    ring
  rw [mul_pow, hWt]
  calc (Work.Spaces.DthIter k v z θ) ^ 2
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ (KD ^ 2 * ((k : ℝ) * ∑ r ∈ Finset.Icc 1 k,
            ((Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r v z θ|) ^ 2))
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
        mul_le_mul_of_nonneg_right hcs hXnn
    _ = KD ^ 2 * ((k * (∑ r ∈ Finset.Icc 1 k,
            ((Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r v z θ|) ^ 2))
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
        ring
    _ = KD ^ 2 * (k * ∑ r ∈ Finset.Icc 1 k,
            (((Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r v z θ|) ^ 2
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))) := by
        rw [mul_assoc, Finset.sum_mul]
    _ = KD ^ 2 * (k * ∑ r ∈ Finset.Icc 1 k, ChainG α v z θ r) := by
        rw [Finset.sum_congr rfl hterm]
    _ = (k : ℝ) * KD ^ 2 * ∑ r ∈ Finset.Icc 1 k, ChainG α v z θ r := by
        ring

/-! ## The measure-theoretic assembly, with the constant kept explicit -/

/-- **`Tk_B_le_chain_aux` with the constant explicit.**  The pointwise chain with the fixed
constant `Ca` (the content of `TkChain_pointwise`) together with the integrability of the chain
slots gives the chain bound for `Bsl Ψ = ∂_θθΨ` with that same constant. -/
theorem Tk_B_le_chain_fixed {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {Ca : ℝ} (hCa_pos : 0 < Ca)
    (hCa : ∀ (α' : ℝ) (v : ℝ → ℝ → ℝ) (z θ : ℝ), θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (∀ n : ℕ, ContDiffAt ℝ n (Function.uncurry v) (z, θ)) →
      (Work.Spaces.DthIter k v z θ * Work.Spaces.Wt α' z θ) ^ 2
        ≤ Ca * ∑ r ∈ Finset.Icc 1 k, ChainG α' v z θ r)
    (hintθ : ∀ m : ℕ, 1 ≤ m → m ≤ k → ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => ChainG α (Bsl Ψ) z θ m) Work.Spaces.Iθ)
    (hintz : ∀ m : ℕ, 1 ≤ m → m ≤ k →
      MeasureTheory.IntegrableOn (fun z => ChainH α (Bsl Ψ) z m) Work.Spaces.Iz) :
    Work.FTS.EllipticEst.remov.Step.Tk α k (Bsl Ψ) ≤ Ca *
        ((∑ r ∈ Finset.Icc 1 (k - 1), ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter r (Bsl Ψ) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α))
          + ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter (k + 2) Ψ z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) := by
  have hSO : Work.FTS.EllipticEst.SmoothOpen (Bsl Ψ) := SmoothOpen.pthIter hΨ 2
  have hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Bsl Ψ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hSO n
  have hcore := Tk_chain_of hk hCa_pos hsm (fun z θ hθ hs => hCa α (Bsl Ψ) z θ hθ hs) hintθ hintz
  have htop : (∫ z in Work.Spaces.Iz, ChainH α (Bsl Ψ) z k)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter (k + 2) Ψ z θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - Work.Spaces.gam α)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    show (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pthIter k (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - Work.Spaces.gam α)) = _
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
    rw [← pthIter_add k 2 Ψ]
  calc Work.FTS.EllipticEst.remov.Step.Tk α k (Bsl Ψ)
      ≤ Ca * ∑ r ∈ Finset.Icc 1 k, ∫ z in Work.Spaces.Iz, ChainH α (Bsl Ψ) z r := hcore
    _ = Ca * ((∫ z in Work.Spaces.Iz, ChainH α (Bsl Ψ) z k)
          + (∑ r ∈ Finset.Icc 1 (k - 1), ∫ z in Work.Spaces.Iz, ChainH α (Bsl Ψ) z r)) := by
        rw [Icc_one_split hk, Finset.sum_insert (not_mem_Icc_pred hk)]
    _ = Ca * ((∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter (k + 2) Ψ z θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - Work.Spaces.gam α))
          + (∑ r ∈ Finset.Icc 1 (k - 1), ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter r (Bsl Ψ) z θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (r : ℝ) - Work.Spaces.gam α))) := by
        rw [htop]
    _ = Ca * ((∑ r ∈ Finset.Icc 1 (k - 1), ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter r (Bsl Ψ) z θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (r : ℝ) - Work.Spaces.gam α))
          + ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter (k + 2) Ψ z θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - Work.Spaces.gam α)) := by
        ring

/-- **The target.**  The constant of the chain `Tk_B_le_chain` can be taken independent of the
datum `(α,Ψ)`: it is the constant of the pointwise chain (`TkChain_pointwise`), which depends on
`k` only, and the assembly is uniform in the datum. -/
theorem Tk_B_le_chain_uniform (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (Ψ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen Ψ →
      Work.Spaces.HkMem α k (Work.FTS.EllipticEst.TT.ESW.Bsl Ψ) →
      Work.FTS.EllipticEst.remov.Step.Tk α k (Work.FTS.EllipticEst.TT.ESW.Bsl Ψ) ≤ C *
        ((∑ r ∈ Finset.Icc 1 (k - 1), ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter r (Work.FTS.EllipticEst.TT.ESW.Bsl Ψ) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α))
          + ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter (k + 2) Ψ z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) := by
  obtain ⟨Ca, hCa_pos, hCa⟩ := TkChain_pointwise k hk
  refine ⟨Ca, hCa_pos, ?_⟩
  intro α Ψ hΨ hmem
  have hSO : Work.FTS.EllipticEst.SmoothOpen (Bsl Ψ) := SmoothOpen.pthIter hΨ 2
  have hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Bsl Ψ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hSO n
  have hintθ : ∀ m : ℕ, 1 ≤ m → m ≤ k → ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => ChainG α (Bsl Ψ) z θ m) Work.Spaces.Iθ :=
    fun m hm hmk z hz =>
      (TkChainIntegrable (α := α) (K := k) (v := Bsl Ψ) (m := m) hm hmk hsm hmem).1 z hz
  have hintz : ∀ m : ℕ, 1 ≤ m → m ≤ k →
      MeasureTheory.IntegrableOn (fun z => ChainH α (Bsl Ψ) z m) Work.Spaces.Iz :=
    fun m hm hmk =>
      (TkChainIntegrable (α := α) (K := k) (v := Bsl Ψ) (m := m) hm hmk hsm hmem).2
  exact Tk_B_le_chain_fixed hk hΨ hCa_pos
    (fun α' v z θ hθ hs => hCa α' v z θ hθ hs) hintθ hintz

end Work.FTS.EllipticEst.TT.ESW
end
