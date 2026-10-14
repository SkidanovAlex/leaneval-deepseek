import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.ClassCHon.CmodeDefs
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.Honest.I4UpperHonest
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.TT.psiDerivSq_lower
import Submission.Work.FTS.EllipticEst.ZCuts.zHardy_compact
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.LocDataExt.Defs
import Submission.Work.FTS.PhiStar.Honesty.CptApp.momentDzZero
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongPersist.N6.Swap6
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.HProductRule_Badsummand
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.StabilityFar.Decay.hasDerivAt_biotSavart
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.EllipticEst.Assembly.bslOp_eq_of_weak_of_smooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Assembly

set_option autoImplicit false
set_option maxHeartbeats 3200000

theorem bslOp_eq_of_weak_of_smooth {α : ℝ} (hα : 0 < α) {F Φ : ℝ → ℝ → ℝ}
    (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ) (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hweak : ∀ φ : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) →
      HasCompactSupport (Function.uncurry φ) →
      tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 →
      (∫ p in Work.FTS.EllipticEst.Q0,
          Φ p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
        = ∫ p in Work.FTS.EllipticEst.Q0,
            F p.1 p.2 * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) :
    ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 → Work.Elliptic.bslOp α Φ z θ = F z θ := by
  have hQ0 : MeasurableSet Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  -- The weighted residual is orthogonal to every test function.
  have hres : ∀ ψ : ℝ × ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
      tsupport ψ ⊆ Work.FTS.EllipticEst.Q0 →
      ∫ x in Work.FTS.EllipticEst.Q0,
        ((Work.Elliptic.bslOp α Φ x.1 x.2 - F x.1 x.2)
          * (x.1 ^ ((5 - α) / α) * Real.cos x.2)) * ψ x = 0 := by
    intro ψ hψ hcψ hsubψ
    set φc : ℝ → ℝ → ℝ := Function.curry ψ with hφcdef
    have huncurry : Function.uncurry φc = ψ := by
      rw [hφcdef, Function.uncurry_curry]
    have huncurry_apply : ∀ p : ℝ × ℝ, φc p.1 p.2 = ψ p := fun p => by
      simpa only [Function.uncurry_def] using congrFun huncurry p
    have hweakφ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry φc) := fun n => by
      rw [huncurry]; exact hψ n
    have hφc_smooth : Work.FTS.EllipticEst.SmoothOpen φc := by
      refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
      rw [huncurry]
      exact (hψ n).contDiffOn
    have hcφc : HasCompactSupport (Function.uncurry φc) := by rw [huncurry]; exact hcψ
    have hsubφc : tsupport (Function.uncurry φc) ⊆ Work.FTS.EllipticEst.Q0 := by
      rw [huncurry]; exact hsubψ
    have hψcont : Continuous ψ := contDiff_zero.mp (hψ 0)
    -- the two pairing identities
    have hpair :=
      Work.EllipticEst.Assembly.bslOp_pairing_self hα hΦ hφc_smooth hcφc hsubφc
    have hwk := hweak φc hweakφ hcφc hsubφc
    -- ## the two integrands and their difference
    let A : ℝ × ℝ → ℝ := fun p => Work.Elliptic.bslOp α Φ p.1 p.2 * φc p.1 p.2
      * (p.1 ^ ((5 - α) / α) * Real.cos p.2)
    let B : ℝ × ℝ → ℝ := fun p => F p.1 p.2 * φc p.1 p.2
      * (p.1 ^ ((5 - α) / α) * Real.cos p.2)
    have hkey : (∫ p in Work.FTS.EllipticEst.Q0, A p) =
        ∫ p in Work.FTS.EllipticEst.Q0, B p := by
      show (∫ p in Work.FTS.EllipticEst.Q0,
          Work.Elliptic.bslOp α Φ p.1 p.2 * φc p.1 p.2
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) = _
      exact hpair.trans hwk
    -- ## continuity on the open quadrant
    have hcurry_cont : ContinuousOn (fun p : ℝ × ℝ => φc p.1 p.2)
        Work.FTS.EllipticEst.Q0 := by
      rw [← Function.uncurry_def, huncurry]
      exact hψcont.continuousOn
    have hAcont : ContinuousOn A Work.FTS.EllipticEst.Q0 := by
      show ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.bslOp α Φ p.1 p.2 * φc p.1 p.2
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) _
      exact ((continuousOn_bslOp_smoothOpen hΦ).mul hcurry_cont).mul
        (continuousOn_pairWeight α)
    have hBcont : ContinuousOn B Work.FTS.EllipticEst.Q0 := by
      show ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2 * φc p.1 p.2
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) _
      exact (hF.continuousOn.mul hcurry_cont).mul (continuousOn_pairWeight α)
    -- ## vanishing off the compact support of `ψ`
    have hAsupp : ∀ p ∉ tsupport ψ, A p = 0 := by
      intro p hp
      have h0 : ψ p = 0 := image_eq_zero_of_notMem_tsupport hp
      show Work.Elliptic.bslOp α Φ p.1 p.2 * φc p.1 p.2
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2) = 0
      rw [huncurry_apply p, h0, mul_zero, zero_mul]
    have hBsupp : ∀ p ∉ tsupport ψ, B p = 0 := by
      intro p hp
      have h0 : ψ p = 0 := image_eq_zero_of_notMem_tsupport hp
      show F p.1 p.2 * φc p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2) = 0
      rw [huncurry_apply p, h0, mul_zero, zero_mul]
    have hGsupp : ∀ p ∉ tsupport ψ,
        ((Work.Elliptic.bslOp α Φ p.1 p.2 - F p.1 p.2)
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) * ψ p = 0 := by
      intro p hp
      rw [image_eq_zero_of_notMem_tsupport hp, mul_zero]
    -- ## move the integrals to the compact support of `ψ`
    have hAK : (∫ p in Work.FTS.EllipticEst.Q0, A p) = ∫ p in tsupport ψ, A p :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hQ0 hsubψ
        (fun p hp => hAsupp p hp.2)
    have hBK : (∫ p in Work.FTS.EllipticEst.Q0, B p) = ∫ p in tsupport ψ, B p :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hQ0 hsubψ
        (fun p hp => hBsupp p hp.2)
    -- ## integrability on the compact support
    have hKcomp : IsCompact (tsupport ψ) := hcψ
    have hKmeas : MeasurableSet (tsupport ψ) := hKcomp.isClosed.measurableSet
    have hAKint : IntegrableOn A (tsupport ψ) :=
      (hAcont.mono hsubψ).integrableOn_compact hKcomp
    have hBKint : IntegrableOn B (tsupport ψ) :=
      (hBcont.mono hsubψ).integrableOn_compact hKcomp
    -- ## the conclusion
    have hzero : (∫ p in tsupport ψ,
        ((Work.Elliptic.bslOp α Φ p.1 p.2 - F p.1 p.2)
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) * ψ p) = 0 := by
      calc (∫ p in tsupport ψ,
            ((Work.Elliptic.bslOp α Φ p.1 p.2 - F p.1 p.2)
              * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) * ψ p)
          = ∫ p in tsupport ψ, (A p - B p) := by
              refine setIntegral_congr_fun hKmeas (fun p _ => ?_)
              show ((Work.Elliptic.bslOp α Φ p.1 p.2 - F p.1 p.2)
                  * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) * ψ p
                = Work.Elliptic.bslOp α Φ p.1 p.2 * φc p.1 p.2
                    * (p.1 ^ ((5 - α) / α) * Real.cos p.2)
                  - F p.1 p.2 * φc p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2)
              rw [huncurry_apply p]
              ring
        _ = (∫ p in tsupport ψ, A p) - ∫ p in tsupport ψ, B p :=
              integral_sub hAKint hBKint
        _ = (∫ p in Work.FTS.EllipticEst.Q0, A p)
              - ∫ p in Work.FTS.EllipticEst.Q0, B p := by rw [hAK, hBK]
        _ = 0 := by rw [hkey, sub_self]
    have hGK : (∫ x in Work.FTS.EllipticEst.Q0,
          ((Work.Elliptic.bslOp α Φ x.1 x.2 - F x.1 x.2)
            * (x.1 ^ ((5 - α) / α) * Real.cos x.2)) * ψ x)
        = ∫ x in tsupport ψ,
          ((Work.Elliptic.bslOp α Φ x.1 x.2 - F x.1 x.2)
            * (x.1 ^ ((5 - α) / α) * Real.cos x.2)) * ψ x :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hQ0 hsubψ
        (fun p hp => hGsupp p hp.2)
    rw [hGK]
    exact hzero
  -- ## the variational lemma
  have hcont : ContinuousOn (fun x : ℝ × ℝ =>
      (Work.Elliptic.bslOp α Φ x.1 x.2 - F x.1 x.2)
        * (x.1 ^ ((5 - α) / α) * Real.cos x.2)) Work.FTS.EllipticEst.Q0 :=
    ((continuousOn_bslOp_smoothOpen hΦ).sub hF.continuousOn).mul (continuousOn_pairWeight α)
  have hzero := eq_zero_of_test_integral_zero Work.FTS.EllipticEst.isOpen_Q0 hcont hres
  intro z hz θ hθ0 hθ1
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩
  have h1 : (Work.Elliptic.bslOp α Φ z θ - F z θ)
      * (z ^ ((5 - α) / α) * Real.cos θ) = 0 := hzero (z, θ) hmem
  have hw : z ^ ((5 - α) / α) * Real.cos θ ≠ 0 :=
    mul_ne_zero (ne_of_gt (Real.rpow_pos_of_pos hz _))
      (ne_of_gt (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩))
  exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hw)

end Work.EllipticEst.Assembly
end
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.TVRed.MainScratch =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 4000000

noncomputable section

/-- `|a| ≤ √B` from `a² ≤ B` and `0 ≤ B`. -/
lemma tvc_abs_le_sqrt {a B : ℝ} (hB : 0 ≤ B) (h : a ^ 2 ≤ B) : |a| ≤ Real.sqrt B := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt h

/-- The derivative identities for `g = f - surrFun ψ F₀ F₁ L` on `Iθ`. -/
lemma tvc_deriv_g_ae {f : ℝ → ℝ} {ψ : ℝ → ℝ} {F₀ F₁ L : ℝ} (hL : L ≠ 0)
    (hψ : ContDiff ℝ 2 ψ)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) :
    ((fun θ : ℝ => deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ L θ) θ)
        =ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ : ℝ => deriv f θ - deriv (surrFun ψ F₀ F₁ L) θ)) ∧
    ((fun θ : ℝ => deriv (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ L θ)) θ)
        =ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ : ℝ => deriv (deriv f) θ - deriv (deriv (surrFun ψ F₀ F₁ L)) θ)) := by
  have hsmooth : ContDiff ℝ 2 (surrFun ψ F₀ F₁ L) := by
    have hdiv1 : ContDiff ℝ 2 (fun θ : ℝ => θ / L) := by
      have he : (fun θ : ℝ => θ / L) = fun θ : ℝ => θ * (1 / L) := by funext θ; ring
      rw [he]; fun_prop
    have hdiv2 : ContDiff ℝ 2 (fun θ : ℝ => (Real.pi / 2 - θ) / L) := by
      have he : (fun θ : ℝ => (Real.pi / 2 - θ) / L)
          = fun θ : ℝ => (Real.pi / 2 - θ) * (1 / L) := by funext θ; ring
      rw [he]; fun_prop
    have h1 : ContDiff ℝ 2 (fun θ : ℝ => ψ (θ / L)) := hψ.comp hdiv1
    have h2 : ContDiff ℝ 2 (fun θ : ℝ => ψ ((Real.pi / 2 - θ) / L)) := hψ.comp hdiv2
    have h3 : ContDiff ℝ 2 (fun θ : ℝ => F₀ * ψ (θ / L) + F₁ * ψ ((Real.pi / 2 - θ) / L)) :=
      (contDiff_const.mul h1).add (contDiff_const.mul h2)
    have hfun : surrFun ψ F₀ F₁ L
        = fun θ : ℝ => F₀ * ψ (θ / L) + F₁ * ψ ((Real.pi / 2 - θ) / L) := rfl
    rw [hfun]; exact h3
  have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    rw [Measure.restrict_congr_set tvc_ae_eq_Iθ_Ioo]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  have hpt1 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ L θ) θ
        = deriv f θ - deriv (surrFun ψ F₀ F₁ L) θ := by
    intro θ hθ
    have h1 : DifferentiableAt ℝ f θ :=
      (hf.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)
    have h2 : DifferentiableAt ℝ (surrFun ψ F₀ F₁ L) θ :=
      (hsmooth.differentiable (by norm_num)).differentiableAt
    exact deriv_sub h1 h2
  have hpt2 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ L θ)) θ
        = deriv (deriv f) θ - deriv (deriv (surrFun ψ F₀ F₁ L)) θ := by
    intro θ hθ
    have hd1 : DifferentiableAt ℝ (deriv f) θ := by
      have h1 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo 0 (Real.pi / 2)) :=
        hf.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
      exact (h1.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)
    have hd2 : DifferentiableAt ℝ (deriv (surrFun ψ F₀ F₁ L)) θ := by
      have h1 : ContDiffOn ℝ 1 (deriv (surrFun ψ F₀ F₁ L)) (Set.Ioo 0 (Real.pi / 2)) :=
        (hsmooth.contDiffOn).deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
      exact (h1.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)
    have hev : deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ L θ)
        =ᶠ[𝓝 θ] (fun y : ℝ => deriv f y - deriv (surrFun ψ F₀ F₁ L) y) := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with y hy
      exact hpt1 y hy
    rw [hev.deriv_eq]
    exact deriv_sub hd1 hd2
  exact ⟨by
      filter_upwards [hae] with θ hθ
      exact hpt1 θ hθ, by
      filter_upwards [hae] with θ hθ
      exact hpt2 θ hθ⟩

/-- The first-order bound for `g = f - surrFun ψ F₀ F₁ L`. -/
lemma tvc_g1_bound {f : ℝ → ℝ} {ψ : ℝ → ℝ} {F₀ F₁ L : ℝ} (hL : L ≠ 0)
    (hψ : ContDiff ℝ 2 ψ)
    (hP : IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hX1int : IntegrableOn
      (fun θ : ℝ => (surrFun ψ F₀ F₁ L θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hG1int : IntegrableOn
      (fun θ : ℝ => (f θ - surrFun ψ F₀ F₁ L θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, (f θ - surrFun ψ F₀ F₁ L θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ 2 * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + 2 * (∫ θ in Work.Spaces.Iθ, (surrFun ψ F₀ F₁ L θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ) := by
  have hRint : IntegrableOn
      (fun θ : ℝ => 2 * ((f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + 2 * ((surrFun ψ F₀ F₁ L θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)) Work.Spaces.Iθ :=
    (hP.const_mul 2).add (hX1int.const_mul 2)
  have hmono : (∫ θ in Work.Spaces.Iθ,
        (f θ - surrFun ψ F₀ F₁ L θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ ∫ θ in Work.Spaces.Iθ, 2 * ((f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + 2 * ((surrFun ψ F₀ F₁ L θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
    refine MeasureTheory.integral_mono_ae hG1int hRint ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    have hs : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
    have h2 : (f θ - surrFun ψ F₀ F₁ L θ) ^ 2
        ≤ 2 * (f θ) ^ 2 + 2 * (surrFun ψ F₀ F₁ L θ) ^ 2 := by
      nlinarith [sq_nonneg (f θ + surrFun ψ F₀ F₁ L θ)]
    calc (f θ - surrFun ψ F₀ F₁ L θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
        ≤ (2 * (f θ) ^ 2 + 2 * (surrFun ψ F₀ F₁ L θ) ^ 2) * Work.FTS.EllipticEst.thEta θ :=
          mul_le_mul_of_nonneg_right h2 hs
      _ = 2 * ((f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + 2 * ((surrFun ψ F₀ F₁ L θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by ring
  calc (∫ θ in Work.Spaces.Iθ, (f θ - surrFun ψ F₀ F₁ L θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ ∫ θ in Work.Spaces.Iθ, 2 * ((f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + 2 * ((surrFun ψ F₀ F₁ L θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := hmono
    _ = 2 * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + 2 * (∫ θ in Work.Spaces.Iθ, (surrFun ψ F₀ F₁ L θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ) := by
        rw [MeasureTheory.integral_add (hP.const_mul 2) (hX1int.const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-- The second-order bound for `g = f - surrFun ψ F₀ F₁ L`. -/
lemma tvc_g2_bound {f : ℝ → ℝ} {ψ : ℝ → ℝ} {F₀ F₁ L : ℝ} (hL : L ≠ 0)
    (hψ : ContDiff ℝ 2 ψ)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hE : IntegrableOn
      (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hX3int : IntegrableOn
      (fun θ : ℝ => (deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hG2int : IntegrableOn
      (fun θ : ℝ => (deriv (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ L θ)) θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, (deriv (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ L θ)) θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ)
      ≤ 2 * (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
        + 2 * (∫ θ in Work.Spaces.Iθ, (deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ) := by
  have hcongr : (fun θ : ℝ => (deriv (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ L θ)) θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ)
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => (deriv (deriv f) θ - deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) := by
    filter_upwards [(tvc_deriv_g_ae hL hψ hf).2] with θ hθ
    rw [hθ]
  rw [integral_congr_ae hcongr]
  have hRint : IntegrableOn
      (fun θ : ℝ => 2 * ((deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + 2 * ((deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ)) Work.Spaces.Iθ :=
    (hE.const_mul 2).add (hX3int.const_mul 2)
  have hmono : (∫ θ in Work.Spaces.Iθ,
        (deriv (deriv f) θ - deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
      ≤ ∫ θ in Work.Spaces.Iθ, 2 * ((deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + 2 * ((deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) := by
    refine MeasureTheory.integral_mono_ae
      (hG2int.congr hcongr) hRint ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    have hs : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
    have h2 : (deriv (deriv f) θ - deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2
        ≤ 2 * (deriv (deriv f) θ) ^ 2 + 2 * (deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2 := by
      nlinarith [sq_nonneg (deriv (deriv f) θ + deriv (deriv (surrFun ψ F₀ F₁ L)) θ)]
    calc (deriv (deriv f) θ - deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ
        ≤ (2 * (deriv (deriv f) θ) ^ 2
            + 2 * (deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2) * Work.FTS.EllipticEst.thEta θ :=
          mul_le_mul_of_nonneg_right h2 hs
      _ = 2 * ((deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + 2 * ((deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) := by ring
  calc (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ - deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ)
      ≤ ∫ θ in Work.Spaces.Iθ, 2 * ((deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + 2 * ((deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) := hmono
    _ = 2 * (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
        + 2 * (∫ θ in Work.Spaces.Iθ, (deriv (deriv (surrFun ψ F₀ F₁ L)) θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ) := by
        rw [MeasureTheory.integral_add (hE.const_mul 2) (hX3int.const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-- Auxiliary: `X2`-type bound helpers (kept local to the main proof are inlined). -/
lemma tvc_integrableOn_cross {f : ℝ → ℝ} {ψ : ℝ → ℝ} {F₀ F₁ L : ℝ}
    (hψ : ContDiff ℝ 2 ψ)
    (hA : IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hℓ1int : IntegrableOn
      (fun θ : ℝ => (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ) :
    IntegrableOn (fun θ : ℝ => deriv f θ * deriv (surrFun ψ F₀ F₁ L) θ
      * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
  refine Integrable.mono' (hA.add hℓ1int) ?_ ?_
  · exact (((measurable_deriv f).mul (measurable_deriv _)).aestronglyMeasurable.mul tvc_aesm_thEta)
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    have hs : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
    rw [Real.norm_eq_abs,
      show |deriv f θ * deriv (surrFun ψ F₀ F₁ L) θ * Work.FTS.EllipticEst.thEta θ|
          = |deriv f θ| * |deriv (surrFun ψ F₀ F₁ L) θ| * Work.FTS.EllipticEst.thEta θ by
        rw [abs_mul, abs_mul, abs_of_nonneg hs]]
    have h2 : |deriv f θ| * |deriv (surrFun ψ F₀ F₁ L) θ|
        ≤ (deriv f θ) ^ 2 / 2 + (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 / 2 := by
      nlinarith [sq_nonneg (|deriv f θ| - |deriv (surrFun ψ F₀ F₁ L) θ|), sq_abs (deriv f θ),
        sq_abs (deriv (surrFun ψ F₀ F₁ L) θ)]
    calc |deriv f θ| * |deriv (surrFun ψ F₀ F₁ L) θ| * Work.FTS.EllipticEst.thEta θ
        ≤ ((deriv f θ) ^ 2 / 2 + (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 / 2)
            * Work.FTS.EllipticEst.thEta θ := mul_le_mul_of_nonneg_right h2 hs
      _ = (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ / 2
          + (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ / 2 := by ring
      _ ≤ (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
          + (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
          nlinarith [mul_nonneg (sq_nonneg (deriv f θ)) hs,
            mul_nonneg (sq_nonneg (deriv (surrFun ψ F₀ F₁ L) θ)) hs]

/-- The `∫(deriv g)²σ` identity. -/
lemma tvc_derivg2_eq {f : ℝ → ℝ} {ψ : ℝ → ℝ} {F₀ F₁ L : ℝ} (hL : L ≠ 0)
    (hψ : ContDiff ℝ 2 ψ)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hA : IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hℓ1int : IntegrableOn
      (fun θ : ℝ => (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ)
    (hcross : IntegrableOn (fun θ : ℝ => deriv f θ * deriv (surrFun ψ F₀ F₁ L) θ
      * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ,
        (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ L θ) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      = (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        - 2 * (∫ θ in Work.Spaces.Iθ, deriv f θ * deriv (surrFun ψ F₀ F₁ L) θ
            * Work.FTS.EllipticEst.thEta θ)
        + (∫ θ in Work.Spaces.Iθ,
            (deriv (surrFun ψ F₀ F₁ L) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  have hcongr : (fun θ : ℝ =>
        (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ L θ) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => (deriv f θ - deriv (surrFun ψ F₀ F₁ L) θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) := by
    filter_upwards [(tvc_deriv_g_ae hL hψ hf).1] with θ hθ
    rw [hθ]
  rw [integral_congr_ae hcongr]
  exact Work.EllipticEst.Core.i0Aux.TVRed.integralSqSub hA hℓ1int hcross

end

end Work.EllipticEst.Core.i0Aux
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.sliceAgmonOpenCore =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Core.i0Aux

/-- The integrand of the integration-by-parts identity `PhiIdentity`. -/
private def agIntegrand (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x
    + f x * deriv (deriv f) x * Work.FTS.EllipticEst.thEta x
    - 2 * Work.Spaces.eta * (f x) ^ 2 * Work.FTS.EllipticEst.thEta x
    - 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * (f x) ^ 2
        * (Real.cos (2 * x)) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))

/-- Splitting the integral of a linear combination into the combination of the integrals. -/
private theorem integral_decomp {F G H K : ℝ → ℝ} {c d : ℝ} {s : Set ℝ}
    (hF : MeasureTheory.IntegrableOn F s) (hG : MeasureTheory.IntegrableOn G s)
    (hH : MeasureTheory.IntegrableOn (fun x => c * H x) s)
    (hK : MeasureTheory.IntegrableOn (fun x => d * K x) s) :
    (∫ x in s, (F x + G x - c * H x - d * K x))
      = (∫ x in s, F x) + (∫ x in s, G x) - c * (∫ x in s, H x)
        - d * (∫ x in s, K x) := by
  have h1 : MeasureTheory.IntegrableOn (fun x => F x + G x) s := hF.add hG
  have h2 : MeasureTheory.IntegrableOn (fun x => F x + G x - c * H x) s := h1.sub hH
  have e1 : (∫ x in s, (F x + G x - c * H x - d * K x))
      = (∫ x in s, (F x + G x - c * H x)) - (∫ x in s, d * K x) :=
    MeasureTheory.integral_sub h2 hK
  have e2 : (∫ x in s, (F x + G x - c * H x))
      = (∫ x in s, (F x + G x)) - (∫ x in s, c * H x) :=
    MeasureTheory.integral_sub h1 hH
  have e3 : (∫ x in s, (F x + G x)) = (∫ x in s, F x) + (∫ x in s, G x) :=
    MeasureTheory.integral_add hF hG
  have e4 : (∫ x in s, c * H x) = c * (∫ x in s, H x) :=
    MeasureTheory.integral_const_mul c H
  have e5 : (∫ x in s, d * K x) = d * (∫ x in s, K x) :=
    MeasureTheory.integral_const_mul d K
  rw [e1, e2, e3, e4, e5]


end Work.EllipticEst.Core.i0Aux
end
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.Q0.RRTransport =====
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
set_option maxHeartbeats 1600000

/-- The open quadrant, in the product form used by the change-of-variables lemmas. -/
theorem Q0_eq_prod : Work.FTS.EllipticEst.Q0 = Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := rfl


/-! ## The real change of variables `Q0 → stripRR` for integrals -/

/-- The real-valued version of `IR.integralQ0eqStrip`. -/
theorem integral_Q0_eq_strip_real {α : ℝ} (hα : 0 < α) {f : ℝ × ℝ → ℝ}
    (hf : MeasureTheory.IntegrableOn f Work.FTS.EllipticEst.Q0) :
    (∫ p in Work.FTS.EllipticEst.Q0, f p)
      = ∫ q in stripRR, f (Real.exp (α * q.1), q.2) * (α * Real.exp (α * q.1)) := by
  rw [Q0_eq_prod] at hf
  have hmain := Work.EllipticEst.InteriorRegularity.IR.integralQ0eqStrip (α := α) hα
    (X := fun p : ℝ × ℝ => ((f p : ℝ) : ℂ)) hf.ofReal
  have hcast : (∫ q in (Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2),
        ((f (Real.exp (α * q.1), q.2) * (α * Real.exp (α * q.1)) : ℝ) : ℂ))
      = ((∫ q in (Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2),
          f (Real.exp (α * q.1), q.2) * (α * Real.exp (α * q.1)) : ℝ) : ℂ) :=
    integral_complex_ofReal
  have hL : (∫ p in Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2), ((f p : ℝ) : ℂ))
      = ((∫ p in Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2), f p : ℝ) : ℂ) :=
    integral_complex_ofReal
  have hmid : (∫ p in Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2), ((f p : ℝ) : ℂ))
      = (∫ q in (Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2),
          ((f (Real.exp (α * q.1), q.2) * (α * Real.exp (α * q.1)) : ℝ) : ℂ)) := by
    rw [hmain]
    refine setIntegral_congr_fun (MeasurableSet.univ.prod measurableSet_Ioo) (fun q _ => ?_)
    push_cast
    ring
  have hstep : ((∫ p in Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2), f p : ℝ) : ℂ)
      = ((∫ q in (Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2),
          f (Real.exp (α * q.1), q.2) * (α * Real.exp (α * q.1)) : ℝ) : ℂ) := by
    rw [← hL, hmid, hcast]
  exact Complex.ofReal_injective hstep

/-! ## The two change-of-variable identities (the "chains") -/

/-- The `Q0`-side integrand of the weak formulation. -/
def qint (α : ℝ) (F : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => F p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2)


/-- Pulling `qint α F` back along `(σ,θ) ↦ (exp (ασ), θ)` gives `GRR α F · ψ`. -/
theorem qint_pullback_GRR {α : ℝ} (hα : 0 < α) {F : ℝ → ℝ → ℝ} {ψ : ℝ → ℝ → ℝ}
    {φ : ℝ → ℝ → ℝ} (hφval : ∀ z θ : ℝ, 0 < z → φ z θ = ψ ((1 / α) * Real.log z) θ)
    (hφQ : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0) :
    ∀ q : ℝ × ℝ, (α * Real.exp (α * q.1))
        * (F (Real.exp (α * q.1)) q.2 * φ (Real.exp (α * q.1)) q.2
            * ((Real.exp (α * q.1)) ^ ((5 - α) / α) * Real.cos q.2))
      = GRR α F q.1 q.2 * ψ q.1 q.2 := by
  intro q
  by_cases hq : q.2 ∈ Set.Ioo 0 (π / 2)
  · have he : 0 < Real.exp (α * q.1) := Real.exp_pos _
    have hlog : (1 / α) * Real.log (Real.exp (α * q.1)) = q.1 := by
      rw [Real.log_exp]; field_simp
    rw [hφval _ _ he, hlog, exp_mul_rpow hα.ne']
    simp only [GRR, hq, if_true, wtRR]
    rw [show (5 - α) * q.1 = 5 * q.1 + -(α * q.1) from by ring, Real.exp_add, Real.exp_neg]
    field_simp
    try ring
  · have h0 : φ (Real.exp (α * q.1)) q.2 = 0 := by
      by_contra hne
      have hmem : (Real.exp (α * q.1), q.2) ∈ tsupport (Function.uncurry φ) :=
        subset_tsupport _ (Function.mem_support.mpr hne)
      exact hq (hφQ hmem).2
    simp only [GRR, hq, if_false, h0, mul_zero]
    ring

/-- Pulling back the `bslOp α φ`-integrand along `(σ,θ) ↦ (exp (ασ), θ)` gives
`VRR α Ψ · kopDr ψ`. -/
theorem bsl_pullback_VRR {α : ℝ} (hα : 0 < α) {Ψ : ℝ → ℝ → ℝ} {ψ : ℝ → ℝ → ℝ}
    {φ : ℝ → ℝ → ℝ} (hφQ : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0)
    (hφbsl : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Elliptic.bslOp α φ z θ = kopDr ψ ((1 / α) * Real.log z) θ) :
    ∀ q : ℝ × ℝ, (α * Real.exp (α * q.1))
        * (Ψ (Real.exp (α * q.1)) q.2 * (Work.Elliptic.bslOp α φ (Real.exp (α * q.1)) q.2)
            * ((Real.exp (α * q.1)) ^ ((5 - α) / α) * Real.cos q.2))
      = VRR α Ψ q.1 q.2 * kopDr ψ q.1 q.2 := by
  intro q
  by_cases hq : q.2 ∈ Set.Ioo 0 (π / 2)
  · have he : 0 < Real.exp (α * q.1) := Real.exp_pos _
    have hlog : (1 / α) * Real.log (Real.exp (α * q.1)) = q.1 := by
      rw [Real.log_exp]; field_simp
    rw [hφbsl _ _ he hq, hlog, exp_mul_rpow hα.ne']
    simp only [VRR, hq, if_true, wtRR]
    rw [show (5 - α) * q.1 = 5 * q.1 + -(α * q.1) from by ring, Real.exp_add, Real.exp_neg]
    field_simp
    try ring
  · have h0 : Work.Elliptic.bslOp α φ (Real.exp (α * q.1)) q.2 = 0 := by
      refine bslOp_eq_zero_of_notMem_tsupport ?_
      intro hmem
      exact hq (hφQ hmem).2
    simp only [VRR, hq, if_false, h0, mul_zero]
    ring

/-! ## Integrability of the transported integrand -/

theorem integrable_VRR_kopDr {α : ℝ} (hα : 0 < α) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0)
    {ψ : ℝ → ℝ → ℝ} (hψ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ))
    (hψc : HasCompactSupport (Function.uncurry ψ))
    (hψs : tsupport (Function.uncurry ψ) ⊆ stripRR) :
    MeasureTheory.Integrable (fun q : ℝ × ℝ => VRR α Ψ q.1 q.2 * kopDr ψ q.1 q.2) := by
  set K : Set (ℝ × ℝ) := tsupport (Function.uncurry ψ) with hK
  have hKc : IsCompact K := hψc
  have hcont : ContinuousOn (fun q : ℝ × ℝ => wtRR α q.1 q.2 * kopDr ψ q.1 q.2) K :=
    ((continuous_wtRR α).continuousOn).mul ((continuousOn_kopDr hψ).mono hψs)
  have hΦ : MeasureTheory.IntegrableOn
      (fun q : ℝ × ℝ => if q.2 ∈ Set.Ioo 0 (π / 2) then Ψ (Real.exp (α * q.1)) q.2 else 0)
      K :=
    integrableOn_barPsi_compact hα hΨ hKc hψs
  have hprod : MeasureTheory.IntegrableOn
      (fun q : ℝ × ℝ =>
        (if q.2 ∈ Set.Ioo 0 (π / 2) then Ψ (Real.exp (α * q.1)) q.2 else 0)
          * (wtRR α q.1 q.2 * kopDr ψ q.1 q.2)) K :=
    hΦ.mul_continuousOn hcont hKc
  have hEq : Set.EqOn (fun q : ℝ × ℝ =>
        (if q.2 ∈ Set.Ioo 0 (π / 2) then Ψ (Real.exp (α * q.1)) q.2 else 0)
          * (wtRR α q.1 q.2 * kopDr ψ q.1 q.2))
      (fun q : ℝ × ℝ => VRR α Ψ q.1 q.2 * kopDr ψ q.1 q.2) K := by
    intro q _
    by_cases hq : q.2 ∈ Set.Ioo 0 (π / 2)
    · simp only [hq, if_true, VRR]
      ring
    · simp only [hq, if_false, VRR]
      ring
  have hOn : MeasureTheory.IntegrableOn (fun q : ℝ × ℝ => VRR α Ψ q.1 q.2 * kopDr ψ q.1 q.2) K :=
    (integrableOn_congr_fun hEq hKc.measurableSet).mp hprod
  have hsupp : Function.support (fun q : ℝ × ℝ => VRR α Ψ q.1 q.2 * kopDr ψ q.1 q.2) ⊆ K := by
    intro q hq
    by_contra hcon
    have h1 : kopDr ψ q.1 q.2 = 0 := kopDr_eq_zero_of_notMem_tsupport hcon
    exact (Function.mem_support.mp hq) (by rw [h1, mul_zero])
  have hind : K.indicator (fun q : ℝ × ℝ => VRR α Ψ q.1 q.2 * kopDr ψ q.1 q.2)
      = (fun q : ℝ × ℝ => VRR α Ψ q.1 q.2 * kopDr ψ q.1 q.2) := by
    funext q
    by_cases hq : q ∈ K
    · rw [Set.indicator_of_mem hq]
    · rw [Set.indicator_of_notMem hq]
      by_contra hne
      exact hq (hsupp (Function.mem_support.mpr (fun h => hne h.symm)))
  rw [← hind, integrable_indicator_iff hKc.measurableSet]
  exact hOn

/-- The integrand on the `Q0`-side of the weak formulation is integrable. -/
theorem integrableOn_qint_of_pullback {α : ℝ} (hα : 0 < α) {f g : ℝ × ℝ → ℝ}
    (hf : MeasureTheory.Integrable (g))
    (heq : ∀ q : ℝ × ℝ, g q = (α * Real.exp (α * q.1)) * f (Real.exp (α * q.1), q.2)) :
    MeasureTheory.IntegrableOn f Work.FTS.EllipticEst.Q0 := by
  rw [integrableOn_Q0_iff_strip hα f]
  exact (hf.congr (by filter_upwards with q; rw [smul_eq_mul]; exact heq q)).integrableOn

/-! ## The chains -/

theorem LHS_chain {α : ℝ} (hα : 0 < α) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0)
    {ψ : ℝ → ℝ → ℝ} (hψ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ))
    (hψc : HasCompactSupport (Function.uncurry ψ))
    (hψs : tsupport (Function.uncurry ψ) ⊆ stripRR)
    {φ : ℝ → ℝ → ℝ}
    (hφQ : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0)
    (hφbsl : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Elliptic.bslOp α φ z θ = kopDr ψ ((1 / α) * Real.log z) θ) :
    (∫ q : ℝ × ℝ, VRR α Ψ q.1 q.2 * kopDr ψ q.1 q.2)
      = ∫ p in Work.FTS.EllipticEst.Q0,
          Ψ p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2) := by
  set X : ℝ × ℝ → ℝ := fun p => Ψ p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
      * (p.1 ^ ((5 - α) / α) * Real.cos p.2) with hX
  have hInt : MeasureTheory.Integrable (fun q : ℝ × ℝ => VRR α Ψ q.1 q.2 * kopDr ψ q.1 q.2) :=
    integrable_VRR_kopDr hα hΨ hψ hψc hψs
  have hpb := bsl_pullback_VRR hα (Ψ := Ψ) (ψ := ψ) hφQ hφbsl
  have hIntOn : MeasureTheory.IntegrableOn X Work.FTS.EllipticEst.Q0 :=
    integrableOn_qint_of_pullback hα hInt (fun q => (hpb q).symm)
  have hOff : ∀ q : ℝ × ℝ, q ∉ stripRR → VRR α Ψ q.1 q.2 * kopDr ψ q.1 q.2 = 0 := by
    intro q hq
    have hq2 : ¬ (q.2 ∈ Set.Ioo 0 (π / 2)) := fun h => hq ⟨trivial, h⟩
    simp only [VRR, hq2, if_false, zero_mul]
  have h1 : (∫ q in stripRR, VRR α Ψ q.1 q.2 * kopDr ψ q.1 q.2)
      = ∫ q : ℝ × ℝ, VRR α Ψ q.1 q.2 * kopDr ψ q.1 q.2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hOff
  have h2 : (∫ q in stripRR, VRR α Ψ q.1 q.2 * kopDr ψ q.1 q.2)
      = ∫ q in stripRR, (α * Real.exp (α * q.1)) * X (Real.exp (α * q.1), q.2) :=
    setIntegral_congr_fun (MeasurableSet.univ.prod measurableSet_Ioo)
      (fun q _ => (hpb q).symm)
  have h3 := integral_Q0_eq_strip_real hα hIntOn
  calc ∫ q : ℝ × ℝ, VRR α Ψ q.1 q.2 * kopDr ψ q.1 q.2
      = ∫ q in stripRR, VRR α Ψ q.1 q.2 * kopDr ψ q.1 q.2 := h1.symm
    _ = ∫ q in stripRR, (α * Real.exp (α * q.1)) * X (Real.exp (α * q.1), q.2) := h2
    _ = ∫ q in stripRR, X (Real.exp (α * q.1), q.2) * (α * Real.exp (α * q.1)) := by
        refine setIntegral_congr_fun (MeasurableSet.univ.prod measurableSet_Ioo)
          (fun q _ => by ring)
    _ = ∫ p in Work.FTS.EllipticEst.Q0, X p := h3.symm

theorem RHS_chain {α : ℝ} (hα : 0 < α) {F : ℝ → ℝ → ℝ} {ψ φ : ℝ → ℝ → ℝ}
    (hφval : ∀ z θ : ℝ, 0 < z → φ z θ = ψ ((1 / α) * Real.log z) θ)
    (hφQ : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0)
    (hint : MeasureTheory.Integrable (fun q : ℝ × ℝ => GRR α F q.1 q.2 * ψ q.1 q.2)) :
    (∫ q : ℝ × ℝ, GRR α F q.1 q.2 * ψ q.1 q.2)
      = ∫ p in Work.FTS.EllipticEst.Q0,
          F p.1 p.2 * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2) := by
  set Y : ℝ × ℝ → ℝ := fun p =>
    F p.1 p.2 * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2) with hY
  have hpb := qint_pullback_GRR hα (F := F) (ψ := ψ) hφval hφQ
  have hIntOn : MeasureTheory.IntegrableOn Y Work.FTS.EllipticEst.Q0 :=
    integrableOn_qint_of_pullback hα hint (fun q => (hpb q).symm)
  have hOff : ∀ q : ℝ × ℝ, q ∉ stripRR → GRR α F q.1 q.2 * ψ q.1 q.2 = 0 := by
    intro q hq
    have hq2 : ¬ (q.2 ∈ Set.Ioo 0 (π / 2)) := fun h => hq ⟨trivial, h⟩
    simp only [GRR, hq2, if_false, zero_mul]
  have h1 : (∫ q in stripRR, GRR α F q.1 q.2 * ψ q.1 q.2)
      = ∫ q : ℝ × ℝ, GRR α F q.1 q.2 * ψ q.1 q.2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hOff
  have h2 : (∫ q in stripRR, GRR α F q.1 q.2 * ψ q.1 q.2)
      = ∫ q in stripRR, (α * Real.exp (α * q.1)) * Y (Real.exp (α * q.1), q.2) :=
    setIntegral_congr_fun (MeasurableSet.univ.prod measurableSet_Ioo)
      (fun q _ => (hpb q).symm)
  have h3 := integral_Q0_eq_strip_real hα hIntOn
  calc ∫ q : ℝ × ℝ, GRR α F q.1 q.2 * ψ q.1 q.2
      = ∫ q in stripRR, GRR α F q.1 q.2 * ψ q.1 q.2 := h1.symm
    _ = ∫ q in stripRR, (α * Real.exp (α * q.1)) * Y (Real.exp (α * q.1), q.2) := h2
    _ = ∫ q in stripRR, Y (Real.exp (α * q.1), q.2) * (α * Real.exp (α * q.1)) := by
        refine setIntegral_congr_fun (MeasurableSet.univ.prod measurableSet_Ioo)
          (fun q _ => by ring)
    _ = ∫ p in Work.FTS.EllipticEst.Q0, Y p := h3.symm

/-! ## The functionals `Lam` and `Gint` and the non-degeneracy -/

/-- The `Q0`-side integrand of the weak formulation tested against `f`. -/
def Gint (α : ℝ) (F : ℝ → ℝ → ℝ) (φ : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => F p.1 p.2 * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2)

/-- The left-hand side integrand of the weak formulation. -/
def Lint (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (φ : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => Ψ p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2) * (p.1 ^ ((5 - α) / α) * Real.cos p.2)

/-- The left-hand side functional of the weak formulation. -/
def Lam (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (φ : ℝ → ℝ → ℝ) : ℝ := ∫ p in Work.FTS.EllipticEst.Q0, Lint α Ψ φ p

/-- Non-degeneracy of `Ψ`: there is a `Q0`-test function on which the left-hand side functional
of the weak formulation does not vanish. -/
def Nondeg (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : Prop :=
  ∃ η : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry η)) ∧
    HasCompactSupport (Function.uncurry η) ∧
    tsupport (Function.uncurry η) ⊆ Work.FTS.EllipticEst.Q0 ∧ Lam α Ψ η ≠ 0


theorem Lam_apply (α : ℝ) (Ψ φ : ℝ → ℝ → ℝ) :
    Lam α Ψ φ = ∫ p in Work.FTS.EllipticEst.Q0, Lint α Ψ φ p := rfl

/-! ## Linear combinations of the transported test functions -/

/-- `bslOp` is additive for a natural multiple of the second argument. -/
theorem bslOp_nsmul_add (α : ℝ) {f g : ℝ → ℝ → ℝ} (n : ℕ) {z θ : ℝ} (hθ : Real.cos θ ≠ 0)
    (hf : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ))
    (hg : ContDiffAt ℝ 2 (Function.uncurry g) (z, θ)) :
    Work.Elliptic.bslOp α (fun z θ : ℝ => f z θ + n * g z θ) z θ
      = Work.Elliptic.bslOp α f z θ + n * Work.Elliptic.bslOp α g z θ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : (fun z θ : ℝ => f z θ + (↑(n + 1) : ℝ) * g z θ)
        = (fun z θ : ℝ => (f z θ + ↑n * g z θ) + g z θ) := by
      funext z θ; push_cast; ring
    rw [hsplit]
    have hcmb : ContDiffAt ℝ 2 (Function.uncurry (fun z θ : ℝ => f z θ + ↑n * g z θ)) (z, θ) := by
      have hfun : Function.uncurry (fun z θ : ℝ => f z θ + ↑n * g z θ)
          = fun p : ℝ × ℝ => Function.uncurry f p + ↑n * Function.uncurry g p := by
        funext p; rfl
      rw [hfun]
      exact hf.add ((contDiffAt_const (c := (↑n : ℝ))).mul hg)
    rw [Work.Elliptic.bslOp_add α _ g z θ hθ hcmb hg, ih]
    push_cast
    ring

/-- The left-hand integrand is additive in the natural-multiple sense. -/
theorem Lint_nsmul_add (α : ℝ) {Ψ f g : ℝ → ℝ → ℝ} (n : ℕ)
    (hfc : ∀ z θ : ℝ, Real.cos θ ≠ 0 → ContDiffAt ℝ 2 (Function.uncurry f) (z, θ))
    (hgc : ∀ z θ : ℝ, Real.cos θ ≠ 0 → ContDiffAt ℝ 2 (Function.uncurry g) (z, θ)) :
    Set.EqOn (Lint α Ψ (fun z θ : ℝ => f z θ + n * g z θ))
      (fun p : ℝ × ℝ => Lint α Ψ f p + n * Lint α Ψ g p)
      (Work.FTS.EllipticEst.Q0) := by
  intro p hp
  have hθ : Real.cos p.2 ≠ 0 := by
    obtain ⟨-, h1, h2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h2⟩)
  simp only [Lint]
  rw [bslOp_nsmul_add α n hθ (hfc p.1 p.2 hθ) (hgc p.1 p.2 hθ)]
  ring

/-! ## Integrability transfer for the source side -/

theorem integrableOn_strip_iff {f : ℝ × ℝ → ℝ}
    (h : ∀ q : ℝ × ℝ, q ∉ (Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2) → f q = 0) :
    MeasureTheory.IntegrableOn f ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))
      ↔ MeasureTheory.Integrable f := by
  constructor
  · intro hf
    have hind : ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)).indicator f = f := by
      funext q
      by_cases hq : q ∈ (Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)
      · rw [Set.indicator_of_mem hq]
      · rw [Set.indicator_of_notMem hq]
        exact (h q hq).symm
    have h2 : MeasureTheory.Integrable
        (((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)).indicator f) := by
      rw [MeasureTheory.integrable_indicator_iff (MeasurableSet.univ.prod measurableSet_Ioo)]
      exact hf
    rwa [hind] at h2
  · intro hf; exact hf.integrableOn

theorem Gint_eq_qint_mul (α : ℝ) (F φ : ℝ → ℝ → ℝ) :
    Gint α F φ = fun p : ℝ × ℝ => qint α F p * φ p.1 p.2 := by
  funext p; simp only [Gint, qint]; ring

theorem integrable_GRR_iff {α : ℝ} (hα : 0 < α) {F ψ φ : ℝ → ℝ → ℝ}
    (hφval : ∀ z θ : ℝ, 0 < z → φ z θ = ψ ((1 / α) * Real.log z) θ)
    (hφQ : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0) :
    MeasureTheory.Integrable (fun q : ℝ × ℝ => GRR α F q.1 q.2 * ψ q.1 q.2)
      ↔ MeasureTheory.IntegrableOn (Gint α F φ) Work.FTS.EllipticEst.Q0 := by
  have hpb := qint_pullback_GRR hα (F := F) (ψ := ψ) hφval hφQ
  rw [Gint_eq_qint_mul α F φ,
    integrableOn_Q0_iff_strip hα (fun p : ℝ × ℝ => qint α F p * φ p.1 p.2)]
  have hsupp : ∀ q : ℝ × ℝ,
      q ∉ (Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2) →
        (α * Real.exp (α * q.1)) • (qint α F (Real.exp (α * q.1), q.2)
          * φ (Real.exp (α * q.1)) q.2) = 0 := by
    intro q hq
    have hq2 : ¬ (q.2 ∈ Set.Ioo 0 (π / 2)) := fun h => hq ⟨trivial, h⟩
    have h0 : φ (Real.exp (α * q.1)) q.2 = 0 := by
      by_contra hne
      have hmem : (Real.exp (α * q.1), q.2) ∈ tsupport (Function.uncurry φ) :=
        subset_tsupport _ (Function.mem_support.mpr hne)
      exact hq2 (hφQ hmem).2
    rw [h0, mul_zero, smul_zero]
  rw [integrableOn_strip_iff hsupp]
  constructor
  · intro hf
    refine hf.congr (Filter.Eventually.of_forall fun q => ?_)
    show GRR α F q.1 q.2 * ψ q.1 q.2
        = (α * Real.exp (α * q.1)) • (qint α F (Real.exp (α * q.1), q.2) * φ (Real.exp (α * q.1)) q.2)
    rw [smul_eq_mul,
      show (α * Real.exp (α * q.1)) * (qint α F (Real.exp (α * q.1), q.2) * φ (Real.exp (α * q.1)) q.2)
          = (α * Real.exp (α * q.1)) * (F (Real.exp (α * q.1)) q.2 * φ (Real.exp (α * q.1)) q.2
              * ((Real.exp (α * q.1)) ^ ((5 - α) / α) * Real.cos q.2)) from by
            simp only [qint]; ring]
    exact (hpb q).symm
  · intro hg
    refine hg.congr (Filter.Eventually.of_forall fun q => ?_)
    show (α * Real.exp (α * q.1)) • (qint α F (Real.exp (α * q.1), q.2) * φ (Real.exp (α * q.1)) q.2)
        = GRR α F q.1 q.2 * ψ q.1 q.2
    rw [smul_eq_mul,
      show (α * Real.exp (α * q.1)) * (qint α F (Real.exp (α * q.1), q.2) * φ (Real.exp (α * q.1)) q.2)
          = (α * Real.exp (α * q.1)) * (F (Real.exp (α * q.1)) q.2 * φ (Real.exp (α * q.1)) q.2
              * ((Real.exp (α * q.1)) ^ ((5 - α) / α) * Real.cos q.2)) from by
            simp only [qint]; ring]
    exact hpb q



end Work.EllipticEst.InteriorRegularity.Q0
end
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.Q0.ae_eq_of_ae_eq_Vf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity.Q0

open MeasureTheory Set Filter
open scoped Real Topology

/-- On the strip, the transported unknown is the product of the weight with `Ψ` evaluated at the
chart point. -/
theorem aeVf_Vf_coords (α : ℝ) (Ψ : ℝ → ℝ → ℝ) {σ θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Vf α Ψ (coords σ θ) = wt α (coords σ θ) * Ψ (Real.exp (α * σ)) θ := by
  have hmem : coords σ θ ∈ stripE := by
    rw [VT.mem_stripE, VT.coords_one]
    exact hθ
  rw [Vf, Set.indicator_of_mem hmem]
  simp only [VT.coords_zero, VT.coords_one]

/-- The exponential substitution is the inverse of the chart on the quadrant. -/
theorem aeVf_exp_log {α : ℝ} (hα : 0 < α) {z : ℝ} (hz : 0 < z) :
    Real.exp (α * ((1 / α) * Real.log z)) = z := by
  have h1 : α * ((1 / α) * Real.log z) = Real.log z := by
    rw [← mul_assoc, mul_one_div_cancel hα.ne', one_mul]
  rw [h1, Real.exp_log hz]

theorem ae_eq_of_ae_eq_Vf {α : ℝ} (hα : 0 < α) {Ψ : ℝ → ℝ → ℝ} {Φt : E2 → ℂ}
    (h : (fun x : E2 => (Work.EllipticEst.InteriorRegularity.Q0.Vf α Ψ x : ℂ))
      =ᵐ[MeasureTheory.volume.restrict Work.EllipticEst.InteriorRegularity.stripE] Φt) :
    (fun p : ℝ × ℝ => (Ψ p.1 p.2 : ℂ))
      =ᵐ[MeasureTheory.volume.restrict Work.FTS.EllipticEst.Q0]
        (fun p : ℝ × ℝ => Φt (Work.EllipticEst.InteriorRegularity.coords ((1 / α) * Real.log p.1) p.2)
          / (Work.EllipticEst.InteriorRegularity.Q0.wt α
              (Work.EllipticEst.InteriorRegularity.coords ((1 / α) * Real.log p.1) p.2) : ℂ)) := by
  -- the bad set of the strip is null
  have hbadE : volume ({x : E2 | (Vf α Ψ x : ℂ) ≠ Φt x} ∩ stripE) = 0 := by
    have h' := h
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff] at h'
    rwa [MeasureTheory.Measure.restrict_apply' VT.isOpen_stripE.measurableSet] at h'
  -- pull it back along the measure-preserving coordinate map `q ↦ coords q.1 q.2`
  have hB : volume ((fun p : ℝ × ℝ => coords p.1 p.2) ⁻¹'
      ({x : E2 | (Vf α Ψ x : ℂ) ≠ Φt x} ∩ stripE)) = 0 :=
    VT.coords_measurePreserving.quasiMeasurePreserving.preimage_null hbadE
  -- the differentiable exponential substitution maps it onto a null set
  have hT : volume (VT.TsubV α '' ((fun p : ℝ × ℝ => coords p.1 p.2) ⁻¹'
      ({x : E2 | (Vf α Ψ x : ℂ) ≠ Φt x} ∩ stripE))) = 0 :=
    MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (VT.differentiable_TsubV α).differentiableOn hB
  -- every bad point of the quadrant is the image of a bad point of the half-strip
  have hsub : {p : ℝ × ℝ | ¬ ((Ψ p.1 p.2 : ℂ)
        = Φt (coords ((1 / α) * Real.log p.1) p.2)
          / (wt α (coords ((1 / α) * Real.log p.1) p.2) : ℂ))}
      ∩ Work.FTS.EllipticEst.Q0 ⊆
      VT.TsubV α '' ((fun p : ℝ × ℝ => coords p.1 p.2) ⁻¹'
        ({x : E2 | (Vf α Ψ x : ℂ) ≠ Φt x} ∩ stripE)) := by
    rintro p ⟨hpb, hpQ⟩
    rw [Work.FTS.EllipticEst.mem_Q0] at hpQ
    obtain ⟨hz, hθ⟩ := hpQ
    have hstrip : coords ((1 / α) * Real.log p.1) p.2 ∈ stripE := by
      rw [VT.mem_stripE, VT.coords_one]
      exact hθ
    have hexp : Real.exp (α * ((1 / α) * Real.log p.1)) = p.1 := aeVf_exp_log hα hz
    have hTq : VT.TsubV α ((1 / α) * Real.log p.1, p.2) = p := by
      simp only [VT.TsubV]
      rw [hexp]
    refine ⟨((1 / α) * Real.log p.1, p.2), ⟨?_, hstrip⟩, hTq⟩
    intro hEq
    -- if `coords q.1 q.2` is not bad, dividing the identity by the non-vanishing weight
    -- gives back the definition of goodness at `p`
    have hEq' : (Vf α Ψ (coords ((1 / α) * Real.log p.1) p.2) : ℂ)
        = Φt (coords ((1 / α) * Real.log p.1) p.2) := hEq
    have hW := aeVf_Vf_coords α Ψ (σ := (1 / α) * Real.log p.1) hθ
    rw [hexp] at hW
    have hwt : (wt α (coords ((1 / α) * Real.log p.1) p.2) : ℂ) ≠ 0 := by
      have h0 : wt α (coords ((1 / α) * Real.log p.1) p.2) ≠ 0 := wt_ne_zero hα hstrip
      exact_mod_cast h0
    have hmul : (wt α (coords ((1 / α) * Real.log p.1) p.2) : ℂ) * (Ψ p.1 p.2 : ℂ)
        = Φt (coords ((1 / α) * Real.log p.1) p.2) := by
      rw [← hEq', hW, Complex.ofReal_mul]
    have hpb' : ¬ ((Ψ p.1 p.2 : ℂ)
        = Φt (coords ((1 / α) * Real.log p.1) p.2)
          / (wt α (coords ((1 / α) * Real.log p.1) p.2) : ℂ)) := hpb
    refine hpb' ?_
    rw [eq_div_iff hwt, mul_comm]
    exact hmul
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff,
    MeasureTheory.Measure.restrict_apply' Work.FTS.EllipticEst.isOpen_Q0.measurableSet]
  exact MeasureTheory.measure_mono_null hsub hT

end Work.EllipticEst.InteriorRegularity.Q0
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.Q0.locallyIntegrable_Vf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.InteriorRegularity.Q0

/-- **Local integrability of the `(σ,θ)`-transported unknown on the half-strip.**

The half-strip `stripRR = ℝ × (0,π/2)` is open, so by the compact-set criterion
`MeasureTheory.locallyIntegrableOn_iff` it suffices to check integrability on a compact
`K ⊆ stripRR`; there `VRR α Ψ` coincides with the pure change-of-variables integrand
`wtRR α σ θ · Ψ (e^{ασ}, θ)` handled by `integrableOn_pullback_wtRR` (the `if θ ∈ (0,π/2)` in the
definition of `VRR` is discharged by the hypothesis `K ⊆ stripRR`). -/
theorem locallyIntegrableOn_VRR {α : ℝ} (hα : α ≠ 0) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0) :
    MeasureTheory.LocallyIntegrableOn
      (fun q : ℝ × ℝ => (VRR α Ψ q.1 q.2 : ℂ)) stripRR := by
  have hopen : IsLocallyClosed (stripRR : Set (ℝ × ℝ)) :=
    (isOpen_univ.prod isOpen_Ioo).isLocallyClosed
  rw [MeasureTheory.locallyIntegrableOn_iff hopen]
  intro K hK hKc
  refine (integrableOn_pullback_wtRR hα hΨ hKc hK).congr_fun (fun p hp => ?_) hKc.measurableSet
  have hp' : p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := (hK hp).2
  rw [VRR, if_pos hp']

/-- The transported unknown of `Q0.Defs` agrees with the `(σ,θ)`-transported unknown of
`Q0.RRDefs` under the coordinate identification: this is `Q0.VRR_eq_Vf` at the coordinates of
the point `x`. -/
theorem cplx_Vf_eq_VRR (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (x : E2) :
    ((Vf α Ψ x : ℝ) : ℂ) = ((VRR α Ψ (x 0) (x 1) : ℝ) : ℂ) := by
  have h := VRR_eq_Vf α Ψ (x 0) (x 1)
  rw [coords_mk x] at h
  exact congrArg (fun r : ℝ => (r : ℂ)) h.symm

theorem locallyIntegrable_Vf {α : ℝ} (hα : α ≠ 0) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0) :
    MeasureTheory.LocallyIntegrableOn
      (fun x : E2 => (Work.EllipticEst.InteriorRegularity.Q0.Vf α Ψ x : ℂ))
      Work.EllipticEst.InteriorRegularity.stripE := by
  have h1 : MeasureTheory.LocallyIntegrableOn
      (fun x : E2 => (VRR α Ψ (x 0) (x 1) : ℂ))
      Work.EllipticEst.InteriorRegularity.stripE :=
    locallyIntegrableOn_coords_of_stripRR (locallyIntegrableOn_VRR hα hΨ)
  exact h1.congr (Filter.Eventually.of_forall fun x => (cplx_Vf_eq_VRR α Ψ x).symm)

end Work.EllipticEst.InteriorRegularity.Q0
end
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.Q0.pullbackExists =====
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

set_option maxHeartbeats 1600000

/-! ## Auxiliary facts about supports -/

/-- A norm bound for the (topological) support of a compactly supported function on `ℝ × ℝ`. -/
lemma exists_norm_bound_tsupport {ψ : ℝ → ℝ → ℝ}
    (hψc : HasCompactSupport (Function.uncurry ψ)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ p ∈ tsupport (Function.uncurry ψ), ‖p‖ ≤ R := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ × ℝ)).mp
    hψc.isCompact.isBounded
  refine ⟨|r|, abs_nonneg r, fun p hp => ?_⟩
  have hd : dist p (0 : ℝ × ℝ) ≤ r := Metric.mem_closedBall.mp (hr hp)
  have h1 : ‖p‖ ≤ r := by simpa using hd
  exact le_trans h1 (le_abs_self r)

/-- The `θ`-projection of a compact subset of the open half-strip `ℝ × (0,π/2)` stays a positive
distance away from both endpoints. -/
lemma thetaWindow {K : Set (ℝ × ℝ)} (hKc : IsCompact K)
    (hsub : K ⊆ Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ Real.pi / 4 ∧ Prod.snd '' K ⊆ Set.Icc δ (Real.pi / 2 - δ) := by
  obtain ⟨ε, hεpos, hεsub⟩ :=
    hKc.exists_cthickening_subset_open
      (t := Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) (isOpen_univ.prod isOpen_Ioo) hsub
  refine ⟨min ε (Real.pi / 4), lt_min hεpos (by linarith [Real.pi_gt_three]),
    min_le_right _ _, ?_⟩
  rintro θ ⟨p, hp, rfl⟩
  have hdist_up : dist (p.1, p.2 + ε) (p.1, p.2) ≤ ε := by
    have h1 : dist (p.1 : ℝ) p.1 = 0 := dist_self _
    have h2 : dist (p.2 + ε) p.2 = ε := by
      rw [Real.dist_eq]
      have h3 : (p.2 + ε) - p.2 = ε := by ring
      rw [h3, abs_of_pos hεpos]
    rw [Prod.dist_eq, h1, h2]
    exact max_le (le_of_lt hεpos) le_rfl
  have hdist_dn : dist (p.1, p.2 - ε) (p.1, p.2) ≤ ε := by
    have h1 : dist (p.1 : ℝ) p.1 = 0 := dist_self _
    have h2 : dist (p.2 - ε) p.2 = ε := by
      rw [Real.dist_eq]
      have h3 : (p.2 - ε) - p.2 = -ε := by ring
      rw [h3, abs_neg, abs_of_pos hεpos]
    rw [Prod.dist_eq, h1, h2]
    exact max_le (le_of_lt hεpos) le_rfl
  have hup : p.2 ≤ Real.pi / 2 - ε := by
    have hmem := hεsub (Metric.mem_cthickening_of_dist_le (p.1, p.2 + ε) p ε K hp hdist_up)
    have hlt : p.2 + ε < Real.pi / 2 := (Set.mem_prod.mp hmem).2.2
    linarith
  have hlow : ε ≤ p.2 := by
    have hmem := hεsub (Metric.mem_cthickening_of_dist_le (p.1, p.2 - ε) p ε K hp hdist_dn)
    have hpos : 0 < p.2 - ε := (Set.mem_prod.mp hmem).2.1
    linarith
  exact ⟨le_trans (min_le_left _ _) hlow, by linarith [min_le_left ε (Real.pi / 4), hup]⟩

/-- If `ψ : ℝ → ℝ → ℝ` is smooth and `χ : ℝ → ℝ` is smooth and vanishes on `(-∞,A]`
(`χ z ≠ 0 → A < z` with `A > 0`), then `(z,θ) ↦ χ z * ψ ((1/α) log z) θ` is smooth on `ℝ²`:
the logarithm is smooth on `(0,∞)` and the vanishing of `χ` near `0` covers the rest. -/
lemma contDiff_cut_logComp {α : ℝ} (hα : 0 < α) {ψ : ℝ → ℝ → ℝ}
    (hψ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ))
    {χ : ℝ → ℝ} (hχ : ∀ n : ℕ, ContDiff ℝ n χ) {A : ℝ} (hA : 0 < A)
    (hχA : ∀ z : ℝ, χ z ≠ 0 → A < z) :
    ∀ n : ℕ, ContDiff ℝ n (Function.uncurry (fun z θ : ℝ => χ z * ψ ((1 / α) * Real.log z) θ)) := by
  intro n
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : 0 < p.1
  · have hVo : IsOpen {q : ℝ × ℝ | 0 < q.1} := isOpen_lt continuous_const continuous_fst
    have hcd : ContDiffOn ℝ (n : WithTop ℕ∞)
        (Function.uncurry (fun z θ : ℝ => χ z * ψ ((1 / α) * Real.log z) θ))
        {q : ℝ × ℝ | 0 < q.1} := by
      have hχ1 : ContDiffOn ℝ (n : WithTop ℕ∞) (fun q : ℝ × ℝ => χ q.1)
          {q : ℝ × ℝ | 0 < q.1} :=
        ((hχ n).comp (contDiff_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ))).contDiffOn
      have hlog : ContDiffOn ℝ (n : WithTop ℕ∞) (fun q : ℝ × ℝ => Real.log q.1)
          {q : ℝ × ℝ | 0 < q.1} :=
        Real.contDiffOn_log.comp (contDiff_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ)).contDiffOn
          (fun q hq => by simpa using ne_of_gt hq)
      have hsm : ContDiffOn ℝ (n : WithTop ℕ∞) (fun q : ℝ × ℝ => (1 / α) * Real.log q.1)
          {q : ℝ × ℝ | 0 < q.1} := by
        simpa only [smul_eq_mul] using ContDiffOn.const_smul (𝕜 := ℝ) (1 / α) hlog
      have hsnd : ContDiffOn ℝ (n : WithTop ℕ∞) (fun q : ℝ × ℝ => q.2)
          {q : ℝ × ℝ | 0 < q.1} :=
        (contDiff_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ)).contDiffOn
      have hinner : ContDiffOn ℝ (n : WithTop ℕ∞)
          (fun q : ℝ × ℝ => ψ ((1 / α) * Real.log q.1) q.2) {q : ℝ × ℝ | 0 < q.1} :=
        (ContDiff.contDiffOn (hψ n) (s := Set.univ)).comp (hsm.prodMk hsnd)
          (fun q _ => trivial)
      exact hχ1.mul hinner
    exact hcd.contDiffAt (hVo.mem_nhds hp)
  · simp only [not_lt] at hp
    have hplt : p.1 < A := lt_of_le_of_lt hp hA
    have hVo : IsOpen {q : ℝ × ℝ | q.1 < A} := isOpen_lt continuous_fst continuous_const
    have hcd : ContDiffOn ℝ (n : WithTop ℕ∞)
        (Function.uncurry (fun z θ : ℝ => χ z * ψ ((1 / α) * Real.log z) θ))
        {q : ℝ × ℝ | q.1 < A} := by
      refine (contDiffOn_const (c := (0 : ℝ))).congr (fun q hq => ?_)
      show Function.uncurry (fun z θ : ℝ => χ z * ψ ((1 / α) * Real.log z) θ) q = (0 : ℝ)
      have h0 : χ q.1 = 0 := by
        by_contra hne
        exact absurd (hχA q.1 hne) (not_lt.mpr (le_of_lt hq))
      simp only [Function.uncurry, h0, zero_mul]
    exact hcd.contDiffAt (hVo.mem_nhds hplt)

/-! ## The pull-back -/

theorem pullbackExists {α : ℝ} (hα : 0 < α) {ψ : ℝ → ℝ → ℝ}
    (hψ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ))
    (hψc : HasCompactSupport (Function.uncurry ψ))
    (hψs : tsupport (Function.uncurry ψ) ⊆ Work.EllipticEst.InteriorRegularity.Q0.stripRR) :
    ∃ φ : ℝ → ℝ → ℝ,
      (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) ∧
      HasCompactSupport (Function.uncurry φ) ∧
      tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 ∧
      (∀ z θ : ℝ, 0 < z → φ z θ = ψ ((1 / α) * Real.log z) θ) ∧
      (∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
        Work.Elliptic.bslOp α φ z θ = Work.EllipticEst.InteriorRegularity.Q0.kopDr ψ ((1 / α) * Real.log z) θ) := by
  -- a Euclidean bound for the support of `ψ`, and the `θ`-window around its `θ`-projection
  obtain ⟨R, hR0, hR⟩ := exists_norm_bound_tsupport hψc
  obtain ⟨δ, hδpos, _hδ4, hδsub⟩ := thetaWindow hψc.isCompact hψs
  -- the `z`-cut-off
  set Az : ℝ := Real.exp (-(α * (R + 2))) / 2 with hAz
  set Lz : ℝ := Real.exp (-(α * (R + 1))) with hLz
  set Uz : ℝ := Real.exp (α * (R + 1)) with hUz
  set Bz : ℝ := 2 * Real.exp (α * (R + 1)) with hBz
  have hAzpos : 0 < Az := by rw [hAz]; positivity
  have hAzLz : Az < Lz := by
    rw [hAz, hLz]
    have h1 : Real.exp (-(α * (R + 2))) < Real.exp (-(α * (R + 1))) :=
      Real.exp_lt_exp.mpr (by nlinarith [hα, hR0])
    have h2 : 0 < Real.exp (-(α * (R + 1))) := Real.exp_pos _
    linarith
  have hLzUz : Lz ≤ Uz := by
    rw [hLz, hUz]
    exact Real.exp_le_exp.mpr (by nlinarith [hα, hR0])
  have hUzBz : Uz < Bz := by
    rw [hUz, hBz]
    linarith [Real.exp_pos (α * (R + 1))]
  obtain ⟨χz, hχzsm, hχzsupp, hχz1⟩ := exists_cutoff hAzpos hAzLz hLzUz hUzBz
  -- the support of the pull-back is contained in a compact box;
  -- `ψ` vanishes outside the `θ`-window, so the `θ`-coordinates of the box are strictly inside
  have hsuppK :
      Function.support (Function.uncurry (fun z θ : ℝ => χz z * ψ ((1 / α) * Real.log z) θ))
        ⊆ Set.Icc Az Bz ×ˢ Set.Icc δ (Real.pi / 2 - δ) := by
    intro p hp
    rw [Function.mem_support] at hp
    have hz0 : χz p.1 ≠ 0 := fun h => hp (by simp only [Function.uncurry, h, zero_mul])
    have hψ0 : ψ ((1 / α) * Real.log p.1) p.2 ≠ 0 :=
      fun h => hp (by simp only [Function.uncurry, h, mul_zero])
    have hmem : ((1 / α) * Real.log p.1, p.2) ∈ tsupport (Function.uncurry ψ) :=
      subset_tsupport _ (Function.mem_support.mpr
        (by simpa only [Function.uncurry] using hψ0))
    exact ⟨⟨le_of_lt (hχzsupp p.1 hz0).1, le_of_lt (hχzsupp p.1 hz0).2⟩,
      hδsub ⟨_, hmem, rfl⟩⟩
  have hsubK :
      tsupport (Function.uncurry (fun z θ : ℝ => χz z * ψ ((1 / α) * Real.log z) θ))
        ⊆ Set.Icc Az Bz ×ˢ Set.Icc δ (Real.pi / 2 - δ) :=
    (IsClosed.closure_subset_iff (isClosed_Icc.prod isClosed_Icc)).mpr hsuppK
  refine ⟨fun z θ => χz z * ψ ((1 / α) * Real.log z) θ, ?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness
    intro n
    exact contDiff_cut_logComp hα hψ hχzsm hAzpos (fun z hz => (hχzsupp z hz).1) n
  · -- compact support
    exact (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset (isClosed_tsupport _) hsubK
  · -- the support lies in the open quadrant
    intro p hpk
    have hmem := hsubK hpk
    have h1 : Az ≤ p.1 ∧ p.1 ≤ Bz := hmem.1
    have h2 : δ ≤ p.2 ∧ p.2 ≤ Real.pi / 2 - δ := hmem.2
    simp only [Work.FTS.EllipticEst.Q0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
    exact ⟨by linarith [h1.1, hAzpos], by linarith [h2.1, hδpos],
      by linarith [h2.2, hδpos]⟩
  · -- agreement with the composition at `z > 0`
    intro z θ hz
    by_cases h0 : ψ ((1 / α) * Real.log z) θ = 0
    · simp only [h0, mul_zero]
    · have hmem : ((1 / α) * Real.log z, θ) ∈ tsupport (Function.uncurry ψ) :=
        subset_tsupport _ (Function.mem_support.mpr
          (by simpa only [Function.uncurry] using h0))
      have hbnd : |(1 / α) * Real.log z| ≤ R :=
        le_trans (by simpa using norm_fst_le ((1 / α) * Real.log z, θ)) (hR _ hmem)
      obtain ⟨hl, hu⟩ := abs_le.mp hbnd
      have hmul : α * ((1 / α) * Real.log z) = Real.log z := by
        rw [← mul_assoc, one_div, mul_inv_cancel₀ (ne_of_gt hα), one_mul]
      have hlogl : -(α * R) ≤ Real.log z :=
        calc -(α * R) = α * (-R) := by ring
          _ ≤ α * ((1 / α) * Real.log z) := mul_le_mul_of_nonneg_left hl hα.le
          _ = Real.log z := hmul
      have hlogu : Real.log z ≤ α * R :=
        calc Real.log z = α * ((1 / α) * Real.log z) := hmul.symm
          _ ≤ α * R := mul_le_mul_of_nonneg_left hu hα.le
      have hzL : Lz ≤ z := by
        rw [hLz, ← Real.exp_log hz]
        exact Real.exp_le_exp.mpr (by nlinarith [hα, hlogl])
      have hzU : z ≤ Uz := by
        rw [hUz, ← Real.exp_log hz]
        exact Real.exp_le_exp.mpr (by nlinarith [hα, hlogu])
      simp only [hχz1 z hzL hzU, one_mul]
  · -- the chain rule on the quadrant
    intro z θ hz hθ
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)
    have hexp : Real.exp (α * ((1 / α) * Real.log z)) = z := exp_alpha_eq_self hα hz
    have hce : Work.Elliptic.bslOp α (fun z θ' : ℝ => ψ ((1 / α) * Real.log z) θ') z θ
        = kopDr ψ ((1 / α) * Real.log z) θ := by
      have h := bslOp_comp_exp (α := α) hα (ψ := ψ) hψ (s := (1 / α) * Real.log z)
        (θ := θ) hcos
      rwa [hexp] at h
    by_cases hmem : ((1 / α) * Real.log z, θ) ∈ tsupport (Function.uncurry ψ)
    · -- near the support of `ψ` the cut-off is `1`
      have hbnd : |(1 / α) * Real.log z| ≤ R :=
        le_trans (by simpa using norm_fst_le ((1 / α) * Real.log z, θ)) (hR _ hmem)
      obtain ⟨hl, hu⟩ := abs_le.mp hbnd
      have hmul : α * ((1 / α) * Real.log z) = Real.log z := by
        rw [← mul_assoc, one_div, mul_inv_cancel₀ (ne_of_gt hα), one_mul]
      have hlogl : -(α * R) ≤ Real.log z :=
        calc -(α * R) = α * (-R) := by ring
          _ ≤ α * ((1 / α) * Real.log z) := mul_le_mul_of_nonneg_left hl hα.le
          _ = Real.log z := hmul
      have hlogu : Real.log z ≤ α * R :=
        calc Real.log z = α * ((1 / α) * Real.log z) := hmul.symm
          _ ≤ α * R := mul_le_mul_of_nonneg_left hu hα.le
      have hzI1 : Lz < z := by
        rw [hLz, ← Real.exp_log hz]
        exact Real.exp_lt_exp.mpr (by nlinarith [hα, hlogl])
      have hzI2 : z < Uz := by
        rw [hUz, ← Real.exp_log hz]
        exact Real.exp_lt_exp.mpr (by nlinarith [hα, hlogu])
      have hV : IsOpen (Set.Ioo Lz Uz ×ˢ Set.univ) :=
        isOpen_Ioo.prod (isOpen_univ : IsOpen (Set.univ : Set ℝ))
      have hEq : Set.EqOn
          (Function.uncurry (fun z θ : ℝ => χz z * ψ ((1 / α) * Real.log z) θ))
          (Function.uncurry (fun z θ' : ℝ => ψ ((1 / α) * Real.log z) θ'))
          (Set.Ioo Lz Uz ×ˢ Set.univ) := by
        intro q hq
        simp only [Function.uncurry]
        rw [hχz1 q.1 (le_of_lt hq.1.1) (le_of_lt hq.1.2), one_mul]
      have hcongr := bslOp_congr_of_isOpen (α := α) hV hEq
        (show (z, θ) ∈ Set.Ioo Lz Uz ×ˢ Set.univ from ⟨⟨hzI1, hzI2⟩, trivial⟩)
      simp only [Function.uncurry] at hcongr
      rw [hcongr, hce]
    · -- off the support of `ψ` the pull-back vanishes near `(z,θ)`, so both sides are `0`
      have hnear : Function.uncurry (fun z θ : ℝ => χz z * ψ ((1 / α) * Real.log z) θ)
          =ᶠ[𝓝 (z, θ)] 0 := by
        have hcont : ContinuousAt (fun q : ℝ × ℝ => ((1 / α) * Real.log q.1, q.2)) (z, θ) := by
          have hlog : ContinuousAt (fun q : ℝ × ℝ => Real.log q.1) (z, θ) :=
            ContinuousAt.log (f := fun q : ℝ × ℝ => q.1) continuousAt_fst
              (by simpa using ne_of_gt hz)
          exact ContinuousAt.prodMk (ContinuousAt.const_mul hlog (1 / α)) continuousAt_snd
        have hU : (fun q : ℝ × ℝ => ((1 / α) * Real.log q.1, q.2)) ⁻¹'
            (tsupport (Function.uncurry ψ))ᶜ ∈ 𝓝 (z, θ) :=
          hcont.preimage_mem_nhds ((isClosed_tsupport _).isOpen_compl.mem_nhds hmem)
        filter_upwards [hU] with q hq
        have h0 : ψ ((1 / α) * Real.log q.1) q.2 = 0 := by
          have hval := (notMem_tsupport_iff_eventuallyEq.mp hq).eq_of_nhds
          simpa [Function.uncurry] using hval
        have hval : Function.uncurry (fun z θ : ℝ => χz z * ψ ((1 / α) * Real.log z) θ) q = (0 : ℝ) := by
          simp only [Function.uncurry, h0, mul_zero]
        simpa using hval
      exact (bslOp_eq_zero_of_notMem_tsupport (notMem_tsupport_iff_eventuallyEq.mpr hnear)).trans
        (kopDr_eq_zero_of_notMem_tsupport hmem).symm

end Work.EllipticEst.InteriorRegularity.Q0
end
end
-- ===== merged: Submission.Work.FTS.ClassC.RopGen.Trace.ZmollAux.kernelSliceBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC.RopGen.Trace.ZmollAux

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.deprecated false
set_option linter.unusedVariables false

open Work.FTS.EllSol.PkgK5.K5c (Qext Qext_of_mem)
open Work.FTS.EllSol.EllPkgAux.MollDzAux (piece_neg_le piece_pi_le)

/-! ## Elementary facts about the doubly odd extension -/

/-- Left of the origin the doubly odd extension is the negated reflected datum. -/
theorem Qext_of_neg (G : ℝ → ℝ → ℝ) (w s : ℝ) (hs : s < 0) : Qext G w s = -G w (-s) := by
  rw [Qext, if_neg (fun h => absurd h.1 (not_le.mpr hs)), if_pos hs]

/-- Right of `π/2` the doubly odd extension is the negated reflected datum. -/
theorem Qext_of_pihalf_lt (G : ℝ → ℝ → ℝ) (w s : ℝ) (hs : Real.pi / 2 < s) :
    Qext G w s = -G w (Real.pi - s) := by
  rw [Qext, if_neg (fun h => absurd h.2 (not_le.mpr hs)), if_neg (by linarith [Real.pi_pos])]

/-- The reflection `t ↦ π - t` of the real line, as a homeomorphism. -/
private def piSubHomeo : ℝ ≃ₜ ℝ where
  toFun := fun t => Real.pi - t
  invFun := fun t => Real.pi - t
  left_inv := fun t => by ring
  right_inv := fun t => by ring
  continuous_toFun := continuous_const.sub continuous_id
  continuous_invFun := continuous_const.sub continuous_id

/-! ## The target estimate -/

theorem kernelSliceBound (G : ℝ → ℝ → ℝ) (w : ℝ)
    (hQ : ContinuousOn (fun s : ℝ => Work.FTS.EllSol.PkgK5.K5c.Qext G w s)
      (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)))
    {k : ℝ → ℝ} (hk : Continuous k) {ε M θ : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) (hM0 : 0 ≤ M)
    (hM : ∀ x : ℝ, |k x| ≤ M) (hvan : ∀ x : ℝ, ε < |x| → k x = 0)
    (hθ : θ ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4)) :
    |∫ s : ℝ, k (θ - s) * Work.FTS.EllSol.PkgK5.K5c.Qext G w s|
      ≤ 3 * M * ∫ s in Work.Spaces.Iθ, |Work.FTS.EllSol.PkgK5.K5c.Qext G w s| := by
  set ρ : ℝ → ℝ := k with hρ
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun s : ℝ => G w s := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, F = fun s : ℝ => |ρ (θ - s)| * |Qext G w s| := ⟨_, rfl⟩
  have hρc : Continuous ρ := by rw [hρ]; exact hk
  -- the slice is continuous on `Iθ`
  have hIθ_sub : Work.Spaces.Iθ ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := by
    intro x hx
    exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2]⟩
  have hgB : ContinuousOn g Work.Spaces.Iθ := by
    rw [hg]
    exact (hQ.mono hIθ_sub).congr (fun s hs => (Qext_of_mem G w s hs).symm)
  have hgabsIθ : IntegrableOn (fun s : ℝ => |g s|) Work.Spaces.Iθ :=
    hgB.abs.integrableOn_compact isCompact_Icc
  have hMgabsIθ : IntegrableOn (fun s : ℝ => M * |g s|) Work.Spaces.Iθ :=
    hgabsIθ.const_mul M
  -- ## Step 1: the crude bound by the absolute value
  have hbase : |∫ s : ℝ, ρ (θ - s) * Qext G w s| ≤ ∫ s : ℝ, F s := by
    have h1 := abs_integral_le_integral_abs (μ := volume)
      (f := fun s : ℝ => ρ (θ - s) * Qext G w s)
    have h2 : (∫ s : ℝ, |ρ (θ - s) * Qext G w s|) = ∫ s : ℝ, F s := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
      simp only [hF, abs_mul]
    rwa [h2] at h1
  -- ## The pointwise identifications of `F` on the two reflected pieces
  have hcongrA : EqOn F (fun s : ℝ => |ρ (θ - s)| * |g (-s)|) (Set.Iio (0 : ℝ)) := by
    intro s hs
    have hs' : s < 0 := hs
    simp only [hF, Qext_of_neg G w s hs', abs_neg, hg]
  have hcongrC : EqOn F (fun s : ℝ => |ρ (θ - s)| * |g (Real.pi - s)|) (Set.Ioi (Real.pi / 2)) := by
    intro s hs
    have hs' : Real.pi / 2 < s := hs
    simp only [hF, Qext_of_pihalf_lt G w s hs', abs_neg, hg]
  -- ## Step 2: integrability of `F` on the three pieces
  have hFintB : IntegrableOn F Work.Spaces.Iθ := by
    have hcont1 : ContinuousOn (fun s : ℝ => |ρ (θ - s)| * |g s|) Work.Spaces.Iθ :=
      ((hρc.comp (continuous_const.sub continuous_id)).abs).continuousOn.mul hgB.abs
    have hint1 : IntegrableOn (fun s : ℝ => |ρ (θ - s)| * |g s|) Work.Spaces.Iθ :=
      hcont1.integrableOn_compact isCompact_Icc
    refine hint1.congr_fun ?_ measurableSet_Icc
    intro s hs
    have h1 := (hF ▸ rfl : F s = |ρ (θ - s)| * |Qext G w s|)
    rw [h1, Qext_of_mem G w s hs, hg]
  have hFintA : IntegrableOn F (Set.Iio (0 : ℝ)) := by
    have hzero : ∀ s ∈ Set.Iic (-3 / 4 : ℝ), |ρ (θ - s)| * |g (-s)| = 0 := by
      intro s hs
      have hs' : s ≤ -3 / 4 := hs
      have hle : ε < |θ - s| := by
        have hpos : 0 < θ - s := by linarith [hθ.1, hs']
        rw [abs_of_pos hpos]
        linarith [hε1, hθ.1, hs']
      rw [hvan _ hle, abs_zero, zero_mul]
    have hInt1 : IntegrableOn (fun s : ℝ => |ρ (θ - s)| * |g (-s)|) (Set.Iic (-3 / 4 : ℝ)) :=
      (MeasureTheory.integrableOn_zero (μ := (volume : Measure ℝ)) (s := Set.Iic (-3 / 4 : ℝ)) :
        IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Set.Iic (-3 / 4 : ℝ)) volume).congr_fun
        (fun x hx => (hzero x hx).symm) measurableSet_Iic
    have hInt2 : IntegrableOn (fun s : ℝ => |ρ (θ - s)| * |g (-s)|) (Set.Ioo (-3 / 4 : ℝ) 0) := by
      have hcont : ContinuousOn (fun s : ℝ => |ρ (θ - s)| * |g (-s)|) (Set.Icc (-3 / 4 : ℝ) 0) :=
        ((hρc.comp (continuous_const.sub continuous_id)).abs).continuousOn.mul
          (hgB.comp' continuous_neg.continuousOn
            (fun s hs => ⟨by linarith [hs.2],
              by linarith [hs.1, Real.pi_gt_three]⟩)).abs
      exact (hcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
    have hcov : Set.Iic (-3 / 4 : ℝ) ∪ Set.Ioo (-3 / 4 : ℝ) 0 = Set.Iio (0 : ℝ) := by
      ext x
      simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ioo, Set.mem_Iio]
      constructor
      · rintro (h | h)
        · linarith
        · exact h.2
      · intro hx
        by_cases h : x ≤ -3 / 4
        · exact Or.inl h
        · exact Or.inr ⟨not_le.mp h, hx⟩
    have hInt : IntegrableOn (fun s : ℝ => |ρ (θ - s)| * |g (-s)|) (Set.Iio (0 : ℝ)) := by
      rw [← hcov]
      exact hInt1.union hInt2
    exact hInt.congr_fun hcongrA.symm measurableSet_Iio
  have hFintC : IntegrableOn F (Set.Ioi (Real.pi / 2)) := by
    have hzero : ∀ s ∈ Set.Ici (Real.pi / 2 + 3 / 4 : ℝ),
        |ρ (θ - s)| * |g (Real.pi - s)| = 0 := by
      intro s hs
      have hs' : Real.pi / 2 + 3 / 4 ≤ s := hs
      have hle : ε < |θ - s| := by
        have hneg : θ - s < 0 := by linarith [hθ.2, hs']
        rw [abs_of_neg hneg]
        linarith [hε1, hθ.2, hs']
      rw [hvan _ hle, abs_zero, zero_mul]
    have hInt1 : IntegrableOn (fun s : ℝ => |ρ (θ - s)| * |g (Real.pi - s)|)
        (Set.Ici (Real.pi / 2 + 3 / 4 : ℝ)) :=
      (MeasureTheory.integrableOn_zero (μ := (volume : Measure ℝ))
        (s := Set.Ici (Real.pi / 2 + 3 / 4 : ℝ)) :
        IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Set.Ici (Real.pi / 2 + 3 / 4 : ℝ)) volume).congr_fun
        (fun x hx => (hzero x hx).symm) measurableSet_Ici
    have hInt2 : IntegrableOn (fun s : ℝ => |ρ (θ - s)| * |g (Real.pi - s)|)
        (Set.Ioo (Real.pi / 2 : ℝ) (Real.pi / 2 + 3 / 4)) := by
      have hcont : ContinuousOn (fun s : ℝ => |ρ (θ - s)| * |g (Real.pi - s)|)
          (Set.Icc (Real.pi / 2 : ℝ) (Real.pi / 2 + 3 / 4)) :=
        ((hρc.comp (continuous_const.sub continuous_id)).abs).continuousOn.mul
          (hgB.comp' ((continuous_const.sub continuous_id).continuousOn)
            (fun s hs => by
              show Real.pi - s ∈ Set.Icc (0 : ℝ) (Real.pi / 2)
              refine ⟨?_, ?_⟩
              · have h1 : s ≤ Real.pi / 2 + 3 / 4 := hs.2
                have h2 : (3 / 4 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
                linarith
              · have h1 : Real.pi / 2 ≤ s := hs.1
                linarith)).abs
      exact (hcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
    have hcov : Set.Ioo (Real.pi / 2 : ℝ) (Real.pi / 2 + 3 / 4) ∪ Set.Ici (Real.pi / 2 + 3 / 4)
        = Set.Ioi (Real.pi / 2) := by
      ext x
      simp only [Set.mem_union, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi]
      constructor
      · rintro (h | h)
        · exact h.1
        · linarith
      · intro hx
        rcases lt_or_ge x (Real.pi / 2 + 3 / 4) with h | h
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr h
    have hInt : IntegrableOn (fun s : ℝ => |ρ (θ - s)| * |g (Real.pi - s)|)
        (Set.Ioi (Real.pi / 2)) := by
      rw [← hcov]
      exact hInt2.union hInt1
    exact hInt.congr_fun hcongrC.symm measurableSet_Ioi
  -- ## Step 3: the three bounds
  have hB : (∫ s in Work.Spaces.Iθ, F s) ≤ M * ∫ s in Work.Spaces.Iθ, |g s| := by
    have hcont1 : ContinuousOn (fun s : ℝ => |ρ (θ - s)| * |g s|) Work.Spaces.Iθ :=
      ((hρc.comp (continuous_const.sub continuous_id)).abs).continuousOn.mul hgB.abs
    have hint1 : IntegrableOn (fun s : ℝ => |ρ (θ - s)| * |g s|) Work.Spaces.Iθ :=
      hcont1.integrableOn_compact isCompact_Icc
    have hcongr : EqOn (fun s : ℝ => |ρ (θ - s)| * |g s|) F Work.Spaces.Iθ := by
      intro s hs
      have h1 : F s = |ρ (θ - s)| * |Qext G w s| := hF ▸ rfl
      rw [h1, Qext_of_mem G w s hs, hg]
    have hle : ∀ s ∈ Work.Spaces.Iθ, F s ≤ M * |g s| := by
      intro s hs
      rw [← hcongr hs]
      exact mul_le_mul_of_nonneg_right (hM (θ - s)) (abs_nonneg _)
    calc (∫ s in Work.Spaces.Iθ, F s)
        ≤ ∫ s in Work.Spaces.Iθ, M * |g s| :=
          setIntegral_mono_on hFintB hMgabsIθ measurableSet_Icc hle
      _ = M * ∫ s in Work.Spaces.Iθ, |g s| := integral_const_mul M _
  have hA : (∫ s in Set.Iio (0 : ℝ), F s) ≤ M * ∫ s in Work.Spaces.Iθ, |g s| := by
    have hnegIoi : Neg.neg '' Set.Ioi (0 : ℝ) = Set.Iio (0 : ℝ) := by
      ext x
      simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Iio]
      constructor
      · rintro ⟨t, ht, rfl⟩
        linarith
      · intro hx
        exact ⟨-x, by linarith, by ring⟩
    calc (∫ s in Set.Iio (0 : ℝ), F s)
        = ∫ s in Neg.neg '' Set.Ioi (0 : ℝ), F s := by rw [hnegIoi]
      _ = ∫ t in Set.Ioi (0 : ℝ), F (-t) :=
          (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_image_emb
            (Homeomorph.neg ℝ).measurableEmbedding F (Set.Ioi (0 : ℝ))
      _ = ∫ t in Set.Ioi (0 : ℝ), |ρ (θ + t)| * |g t| := by
          refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
          have ht' : (0 : ℝ) < t := ht
          have h1 : F (-t) = |ρ (θ - -t)| * |g (- -t)| :=
            hcongrA (show -t ∈ Set.Iio (0 : ℝ) from by simpa using neg_lt_zero.mpr ht')
          simpa using h1
      _ ≤ M * ∫ t in Work.Spaces.Iθ, |g t| :=
          piece_neg_le hρc hε0 hε1 hM0 hM hvan hgB hθ
  have hC : (∫ s in Set.Ioi (Real.pi / 2), F s) ≤ M * ∫ s in Work.Spaces.Iθ, |g s| := by
    have hpiIio : (fun t : ℝ => Real.pi - t) '' Set.Iio (Real.pi / 2) = Set.Ioi (Real.pi / 2) := by
      ext x
      simp only [Set.mem_image, Set.mem_Iio, Set.mem_Ioi]
      constructor
      · rintro ⟨t, ht, rfl⟩
        linarith
      · intro hx
        exact ⟨Real.pi - x, by linarith, by ring⟩
    calc (∫ s in Set.Ioi (Real.pi / 2), F s)
        = ∫ s in (fun t : ℝ => Real.pi - t) '' Set.Iio (Real.pi / 2), F s := by rw [hpiIio]
      _ = ∫ t in Set.Iio (Real.pi / 2), F (Real.pi - t) :=
          (Measure.measurePreserving_sub_left (volume : Measure ℝ) Real.pi).setIntegral_image_emb
            piSubHomeo.measurableEmbedding F (Set.Iio (Real.pi / 2))
      _ = ∫ t in Set.Iio (Real.pi / 2), |ρ (θ + t - Real.pi)| * |g t| := by
          refine setIntegral_congr_fun measurableSet_Iio (fun t ht => ?_)
          have ht' : t < Real.pi / 2 := ht
          have h1 : F (Real.pi - t) = |ρ (θ - (Real.pi - t))| * |g (Real.pi - (Real.pi - t))| :=
            hcongrC (show Real.pi - t ∈ Set.Ioi (Real.pi / 2) from by
              simp only [Set.mem_Ioi]; linarith [ht'])
          rw [show θ - (Real.pi - t) = θ + t - Real.pi by ring,
            show Real.pi - (Real.pi - t) = t by ring] at h1
          exact h1
      _ ≤ M * ∫ t in Work.Spaces.Iθ, |g t| :=
          piece_pi_le hρc hε0 hε1 hM0 hM hvan hgB hθ
  -- ## Step 4: the disjoint cover of `ℝ` and the splitting of the integral
  have hdisjAB : Disjoint (Set.Iio (0 : ℝ)) Work.Spaces.Iθ := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    have h1 : x < 0 := hx1
    have h2 : (0 : ℝ) ≤ x := hx2.1
    linarith
  have hdisjABC : Disjoint (Set.Iio (0 : ℝ) ∪ Work.Spaces.Iθ) (Set.Ioi (Real.pi / 2)) := by
    rw [Set.disjoint_left]
    intro x hx hx3
    simp only [Set.mem_union, Set.mem_Iio] at hx
    have h3 : Real.pi / 2 < x := hx3
    rcases hx with hx | hx
    · linarith [Real.pi_pos]
    · linarith [hx.2]
  have hcover : Set.Iio (0 : ℝ) ∪ Work.Spaces.Iθ ∪ Set.Ioi (Real.pi / 2) = (Set.univ : Set ℝ) := by
    ext x
    constructor
    · intro _
      exact Set.mem_univ x
    · intro _
      rcases lt_or_ge x 0 with h | h
      · exact Or.inl (Or.inl h)
      · by_cases h2 : x ≤ Real.pi / 2
        · exact Or.inl (Or.inr ⟨h, h2⟩)
        · exact Or.inr (lt_of_not_ge h2)
  have hsplit : (∫ s : ℝ, F s)
      = (∫ s in Set.Iio (0 : ℝ), F s) + (∫ s in Work.Spaces.Iθ, F s)
        + ∫ s in Set.Ioi (Real.pi / 2), F s := by
    rw [← MeasureTheory.setIntegral_univ, ← hcover,
      MeasureTheory.setIntegral_union hdisjABC measurableSet_Ioi (hFintA.union hFintB) hFintC,
      MeasureTheory.setIntegral_union hdisjAB measurableSet_Icc hFintA hFintB]
  -- ## Step 5: assembly
  have hQeq : (∫ s in Work.Spaces.Iθ, |g s|)
      = ∫ s in Work.Spaces.Iθ, |Qext G w s| :=
    setIntegral_congr_fun measurableSet_Icc (fun s hs => by simp only [hg, Qext_of_mem G w s hs])
  calc |∫ s : ℝ, ρ (θ - s) * Qext G w s|
      ≤ ∫ s : ℝ, F s := hbase
    _ ≤ 3 * M * ∫ s in Work.Spaces.Iθ, |Qext G w s| := by
        rw [← hQeq]
        linarith [hsplit, hA, hB, hC]

end Work.FTS.ClassC.RopGen.Trace.ZmollAux
end
end
-- ===== merged: Submission.Work.FTS.ClassC.RopGen.Trace.ZmollAux.logConvDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC.RopGen.Trace.ZmollAux

open scoped Real Topology
open MeasureTheory

set_option autoImplicit false

/-- `sKer δ` has compact support (contained in `[-δ, δ]`) when `δ > 0`. -/
private theorem sKer_hasCompactSupport {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (Work.FTS.EllSol.PkgK5.K5c.sKer δ) := by
  refine HasCompactSupport.intro (K := Set.Icc (-δ) δ) isCompact_Icc ?_
  intro t ht
  refine Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ ?_
  rw [Set.mem_Icc, not_and_or] at ht
  rcases ht with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-- The logarithmic convolution `s ↦ ∫ t, sKer δ (s - t) * F t` is differentiable at every
point with derivative `∫ t, sKerd δ (s - t) * F t`, the derivative having been moved onto the
(compactly supported, smooth) kernel.  This is
`HasCompactSupport.hasDerivAt_convolution_right` for the convolution
`F ⋆[mul, volume] sKer δ`, rewritten as the iterated integral appearing in `zmoll`. -/
private theorem hasDerivAt_logConv (F : ℝ → ℝ)
    (hF : MeasureTheory.LocallyIntegrable F MeasureTheory.volume) {δ : ℝ} (hδ : 0 < δ) :
    ∀ s : ℝ, HasDerivAt (fun x : ℝ => ∫ t : ℝ,
        Work.FTS.EllSol.PkgK5.K5c.sKer δ (x - t) * F t)
      (∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (s - t) * F t) s := by
  have hcs : HasCompactSupport (Work.FTS.EllSol.PkgK5.K5c.sKer δ) :=
    sKer_hasCompactSupport hδ
  have hcd : ContDiff ℝ 1 (Work.FTS.EllSol.PkgK5.K5c.sKer δ) :=
    Work.FTS.EllSol.EllPkgAux.contDiff_sKer δ (n := 1)
  -- the convolution is the iterated integral
  have hconv : ∀ (k : ℝ → ℝ) (x : ℝ),
      MeasureTheory.convolution F k (ContinuousLinearMap.mul ℝ ℝ) MeasureTheory.volume x
        = ∫ t : ℝ, k (x - t) * F t := by
    intro k x
    rw [MeasureTheory.convolution_mul]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)
  intro s
  have hbase : HasDerivAt
      (MeasureTheory.convolution F (fun u : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ u)
        (ContinuousLinearMap.mul ℝ ℝ) MeasureTheory.volume)
      (MeasureTheory.convolution F (fun u : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd δ u)
        (ContinuousLinearMap.mul ℝ ℝ) MeasureTheory.volume s) s := by
    have h := hcs.hasDerivAt_convolution_right (L := ContinuousLinearMap.mul ℝ ℝ)
      (μ := MeasureTheory.volume) hF hcd s
    have hfun : (fun u : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd δ u)
        = deriv (fun u : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ u) := by
      funext u
      rw [Work.FTS.EllSol.EllPkgAux.sKerd]
    rw [hfun]
    exact h
  simpa only [← hconv] using hbase

theorem logConvDeriv (F : ℝ → ℝ)
    (hF : MeasureTheory.LocallyIntegrable F MeasureTheory.volume) {δ : ℝ} (hδ0 : 0 < δ) :
    ∀ z : ℝ, 0 < z → z * deriv (fun z' : ℝ => ∫ t : ℝ,
        Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z' - t) * F t) z
      = ∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) * F t := by
  intro z hz
  have hz' : z ≠ 0 := ne_of_gt hz
  have hchain : HasDerivAt
      (fun z' : ℝ => ∫ t : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z' - t) * F t)
      ((∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) * F t) * z⁻¹) z :=
    (hasDerivAt_logConv F hF hδ0 (Real.log z)).comp z (Real.hasDerivAt_log hz')
  rw [hchain.deriv]
  field_simp

end Work.FTS.ClassC.RopGen.Trace.ZmollAux
end
-- ===== merged: Submission.Work.FTS.ClassC.RopGen.sliceAgmonEta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC.RopGen

set_option autoImplicit false

/-! ## The sharp arithmetic of the final step -/


/-! ## The integrand of the integration by parts -/

/-- The integrand of the integration-by-parts identity `PhiIdentity`. -/
private def agIntegrand (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x
    + f x * deriv (deriv f) x * Work.FTS.EllipticEst.thEta x
    - 2 * Work.Spaces.eta * (f x) ^ 2 * Work.FTS.EllipticEst.thEta x
    - 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * (f x) ^ 2
        * (Real.cos (2 * x)) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))

/-- Splitting the integral of a linear combination into the combination of the integrals. -/
private theorem integral_decomp {F G H K : ℝ → ℝ} {c d : ℝ} {s : Set ℝ}
    (hF : MeasureTheory.IntegrableOn F s) (hG : MeasureTheory.IntegrableOn G s)
    (hH : MeasureTheory.IntegrableOn (fun x => c * H x) s)
    (hK : MeasureTheory.IntegrableOn (fun x => d * K x) s) :
    (∫ x in s, (F x + G x - c * H x - d * K x))
      = (∫ x in s, F x) + (∫ x in s, G x) - c * (∫ x in s, H x)
        - d * (∫ x in s, K x) := by
  have h1 : MeasureTheory.IntegrableOn (fun x => F x + G x) s := hF.add hG
  have h2 : MeasureTheory.IntegrableOn (fun x => F x + G x - c * H x) s := h1.sub hH
  have e1 : (∫ x in s, (F x + G x - c * H x - d * K x))
      = (∫ x in s, (F x + G x - c * H x)) - (∫ x in s, d * K x) :=
    MeasureTheory.integral_sub h2 hK
  have e2 : (∫ x in s, (F x + G x - c * H x))
      = (∫ x in s, (F x + G x)) - (∫ x in s, c * H x) :=
    MeasureTheory.integral_sub h1 hH
  have e3 : (∫ x in s, (F x + G x)) = (∫ x in s, F x) + (∫ x in s, G x) :=
    MeasureTheory.integral_add hF hG
  have e4 : (∫ x in s, c * H x) = c * (∫ x in s, H x) :=
    MeasureTheory.integral_const_mul c H
  have e5 : (∫ x in s, d * K x) = d * (∫ x in s, K x) :=
    MeasureTheory.integral_const_mul d K
  rw [e1, e2, e3, e4, e5]

/-! ## The main theorem -/


end Work.FTS.ClassC.RopGen
end
end
-- ===== merged: Submission.Work.FTS.ClassC.VanishFamilyDefs =====
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

/-- The integrand of the `hV` hypothesis of `HkMem_seven_slots_of_vanishing_family`, as a
curried function: `(D_z^l ∂_θ^t Ψ · w)² · sin(2θ)^{2t - 4 - γ}`. -/
def hVint (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (t l : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => (Work.Spaces.DzIter l (Work.Spaces.pthIter t Ψ) z θ * Work.Spaces.w z) ^ 2
    * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α)


/-- The sum of the constants `vanC` of `HkMem_of_pure_and_vanishing` over all the mixed slots
of level `k`; the constant of the pointwise reduction `HkIntegrand_le_pure_vanishing`. -/
def vanSum (α : ℝ) (hα : 0 < α) (hγ : Work.Spaces.gam α ≤ 3 / 2)
    (f : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen f) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.Icc 1 (k - j),
    (if h : 1 ≤ i then vanC α hα hγ f hsm i j h else 0)


/-- `vanSum` is nonnegative. -/
theorem vanSum_nonneg (α : ℝ) (hα : 0 < α) (hγ : Work.Spaces.gam α ≤ 3 / 2)
    (f : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen f) (k : ℕ) :
    0 ≤ vanSum α hα hγ f hsm k := by
  rw [vanSum]
  refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => ?_
  split_ifs with h
  · exact le_of_lt (vanC_pos α hα hγ f hsm i j h)
  · exact le_refl 0

end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.ClassC.VopGen.muSliceAgmonPointwiseAux =====
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

/-! ## Elementary facts about the weight -/

lemma sigR_gam_pos (α θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < 𝔰[α] θ := by
  simpa only [Work.FTS.EllipticEst.TT.sigR, Work.FTS.EllipticEst.TT.sigA,
    Work.FTS.EllipticEst.Cores.sigA]
    using Work.FTS.EllipticEst.Cores.sigA_pos' (α := α) hθ

lemma sigR_gam_nonneg (α θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ 𝔰[α] θ := by
  simpa only [Work.FTS.EllipticEst.TT.sigR, Work.FTS.EllipticEst.TT.sigA]
    using Work.FTS.EllipticEst.TT.sigA_nonneg α θ hθ

/-- `|σ'| ≤ 2a sin(2θ)^{a-1}` on the open interval. -/
lemma sigDR_gam_abs_le {α y : ℝ} (hα1 : α ≤ 1) (hSp : 0 < Real.sin (2 * y)) :
    |𝔡[α] y| ≤ 2 * (2 - Work.Spaces.gam α) * (Real.sin (2 * y)) ^ ((2 - Work.Spaces.gam α) - 1) := by
  have hp0 : 0 < 2 - Work.Spaces.gam α := Work.FTS.EllipticEst.Cores.sub_gam_pos hα1
  rw [Work.FTS.EllipticEst.TT.sigDR_apply, abs_mul, abs_mul,
    abs_of_pos (show (0:ℝ) < 2 * (2 - Work.Spaces.gam α) by linarith),
    abs_of_nonneg (Real.rpow_nonneg hSp.le _)]
  have hc : |Real.cos (2 * y)| ≤ 1 := Real.abs_cos_le_one _
  have h2 : 2 * (2 - Work.Spaces.gam α) * |Real.cos (2 * y)| ≤ 2 * (2 - Work.Spaces.gam α) := by
    simpa using mul_le_mul_of_nonneg_left hc (show (0:ℝ) ≤ 2 * (2 - Work.Spaces.gam α) by linarith)
  exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hSp.le _)

/-- `σ'(π/2 - y) = -σ'(y)`, hence equal absolute values. -/
lemma sigDR_gam_abs_reflect {α y : ℝ} : |𝔡[α] (Real.pi / 2 - y)| = |𝔡[α] y| := by
  have hsinref : Real.sin (2 * (Real.pi / 2 - y)) = Real.sin (2 * y) := by
    rw [show 2 * (Real.pi / 2 - y) = Real.pi - 2 * y by ring, Real.sin_pi_sub]
  have hcref : Real.cos (2 * (Real.pi / 2 - y)) = -Real.cos (2 * y) := by
    rw [show 2 * (Real.pi / 2 - y) = Real.pi - 2 * y by ring, Real.cos_pi_sub]
  simp only [Work.FTS.EllipticEst.TT.sigDR]
  rw [hsinref, hcref]
  have heq : ((2 * (2 - Work.Spaces.gam α)) * (-Real.cos (2 * y)))
      * (Real.sin (2 * y)) ^ ((2 - Work.Spaces.gam α) - 1)
      = -(((2 * (2 - Work.Spaces.gam α)) * Real.cos (2 * y))
        * (Real.sin (2 * y)) ^ ((2 - Work.Spaces.gam α) - 1)) := by ring
  rw [heq, abs_neg]

lemma sigDR_gam_continuousOn (α : ℝ) : ContinuousOn (𝔡[α]) (Set.Ioo 0 (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hcos : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
  have hp : ContinuousOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) - 1))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hsin.rpow_const (fun x hx => Or.inl (ne_of_gt
      (Work.FTS.EllipticEst.TT.sin_two_pos_of_mem_Ioo hx)))
  have hcont : ContinuousOn (fun θ : ℝ => (2 * (2 - Work.Spaces.gam α)) * Real.cos (2 * θ)
      * (Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) - 1)) (Set.Ioo 0 (Real.pi / 2)) :=
    (continuousOn_const.mul hcos).mul hp
  refine hcont.congr ?_
  intro x hx
  simp only [Work.FTS.EllipticEst.TT.sigDR_apply]

/-- Domination by an integrable function gives integrability on the open interval. -/
lemma integrableOn_Ioo_of_le {g D : ℝ → ℝ}
    (hD : IntegrableOn D (Set.Ioo 0 (Real.pi / 2)))
    (hg : ContinuousOn g (Set.Ioo 0 (Real.pi / 2)))
    (hbound : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |g θ| ≤ D θ) :
    IntegrableOn g (Set.Ioo 0 (Real.pi / 2)) := by
  refine MeasureTheory.Integrable.mono' hD (hg.aestronglyMeasurable measurableSet_Ioo) ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  rw [Real.norm_eq_abs]
  exact hbound θ hθ

/-! ## The boundary limits

Both boundary products `f f' σ` and `f² σ'` are `O(sin(2θ)^{1+a})` near the endpoints, hence tend
to `0`. -/

/-- `f f' σ → 0` at `0⁺`. -/
lemma tendsto_ff'_sigR_zero {α M : ℝ} {f : ℝ → ℝ} (hα1 : α ≤ 1) (hMnn : 0 ≤ M)
    (hfS : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ M * Real.sin (2 * θ))
    (hdS : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv f θ| ≤ M) :
    Filter.Tendsto (fun t : ℝ => f t * deriv f t * 𝔰[α] t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hp0 : 0 < 2 - Work.Spaces.gam α := Work.FTS.EllipticEst.Cores.sub_gam_pos hα1
  refine Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.tendsto_zero_of_abs_le_eventually
    (A := M * M * 2 ^ (1 + (2 - Work.Spaces.gam α)))
    (e := 1 + (2 - Work.Spaces.gam α)) (ε := Real.pi / 4) (by linarith) (by linarith [Real.pi_pos]) ?_
  intro y hy
  have hyO : y ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hy.1, by linarith [hy.2, Real.pi_pos]⟩
  have hSp : 0 < Real.sin (2 * y) := Work.FTS.EllipticEst.TT.sin_two_pos_of_mem_Ioo hyO
  have hSle : Real.sin (2 * y) ≤ 2 * y := Real.sin_le (by linarith [hy.1])
  have hchain : |f y * deriv f y * 𝔰[α] y|
      ≤ M * M * (Real.sin (2 * y)) ^ (1 + (2 - Work.Spaces.gam α)) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sigR_gam_pos α y hyO).le]
    calc |f y| * |deriv f y| * (Real.sin (2 * y)) ^ (2 - Work.Spaces.gam α)
        ≤ (M * Real.sin (2 * y)) * M * (Real.sin (2 * y)) ^ (2 - Work.Spaces.gam α) :=
          mul_le_mul (mul_le_mul (hfS y hyO) (hdS y hyO) (abs_nonneg _)
            (mul_nonneg hMnn hSp.le)) le_rfl (Real.rpow_nonneg hSp.le _)
            (mul_nonneg (mul_nonneg hMnn hSp.le) hMnn)
      _ = M * M * ((Real.sin (2 * y)) * (Real.sin (2 * y)) ^ (2 - Work.Spaces.gam α)) := by ring
      _ = M * M * (Real.sin (2 * y)) ^ (1 + (2 - Work.Spaces.gam α)) := by
          rw [← Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.rpow_one_add hSp]
  calc |f y * deriv f y * 𝔰[α] y|
        ≤ M * M * (Real.sin (2 * y)) ^ (1 + (2 - Work.Spaces.gam α)) := hchain
    _ ≤ M * M * (2 * y) ^ (1 + (2 - Work.Spaces.gam α)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Real.rpow_le_rpow hSp.le hSle (by linarith)
    _ = M * M * 2 ^ (1 + (2 - Work.Spaces.gam α)) * y ^ (1 + (2 - Work.Spaces.gam α)) := by
        rw [Real.mul_rpow (by norm_num) (le_of_lt hy.1)]; ring

/-- `f f' σ → 0` at `(π/2)⁻`. -/
lemma tendsto_ff'_sigR_zero_right {α M : ℝ} {f : ℝ → ℝ} (hα1 : α ≤ 1) (hMnn : 0 ≤ M)
    (hfS : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ M * Real.sin (2 * θ))
    (hdS : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv f θ| ≤ M) :
    Filter.Tendsto (fun t : ℝ => f t * deriv f t * 𝔰[α] t)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hp0 : 0 < 2 - Work.Spaces.gam α := Work.FTS.EllipticEst.Cores.sub_gam_pos hα1
  refine Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.tendsto_zero_of_abs_le_eventually_right
    (A := M * M * 2 ^ (1 + (2 - Work.Spaces.gam α)))
    (e := 1 + (2 - Work.Spaces.gam α)) (ε := Real.pi / 4) (by linarith) (by linarith [Real.pi_pos]) ?_
  intro y hy
  have hyO : Real.pi / 2 - y ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [hy.2, Real.pi_pos], by linarith [hy.1]⟩
  have hSy : 0 < Real.sin (2 * y) :=
    Work.FTS.EllipticEst.TT.sin_two_pos_of_mem_Ioo ⟨hy.1, by linarith [hy.2, Real.pi_pos]⟩
  have hSle : Real.sin (2 * y) ≤ 2 * y := Real.sin_le (by linarith [hy.1])
  have hsinref : Real.sin (2 * (Real.pi / 2 - y)) = Real.sin (2 * y) := by
    rw [show 2 * (Real.pi / 2 - y) = Real.pi - 2 * y by ring, Real.sin_pi_sub]
  have hsref : 𝔰[α] (Real.pi / 2 - y) = 𝔰[α] y := by
    simp only [Work.FTS.EllipticEst.TT.sigR]
    rw [hsinref]
  have hfθ : |f (Real.pi / 2 - y)| ≤ M * Real.sin (2 * y) := by
    have h := hfS (Real.pi / 2 - y) hyO
    rwa [hsinref] at h
  have hchain : |f (Real.pi / 2 - y) * deriv f (Real.pi / 2 - y) * 𝔰[α] (Real.pi / 2 - y)|
      ≤ M * M * (Real.sin (2 * y)) ^ (1 + (2 - Work.Spaces.gam α)) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sigR_gam_pos α _ hyO).le, hsref]
    calc |f (Real.pi / 2 - y)| * |deriv f (Real.pi / 2 - y)|
          * (Real.sin (2 * y)) ^ (2 - Work.Spaces.gam α)
        ≤ (M * Real.sin (2 * y)) * M * (Real.sin (2 * y)) ^ (2 - Work.Spaces.gam α) :=
          mul_le_mul (mul_le_mul hfθ (hdS _ hyO) (abs_nonneg _) (mul_nonneg hMnn hSy.le))
            le_rfl (Real.rpow_nonneg hSy.le _) (mul_nonneg (mul_nonneg hMnn hSy.le) hMnn)
      _ = M * M * ((Real.sin (2 * y)) * (Real.sin (2 * y)) ^ (2 - Work.Spaces.gam α)) := by ring
      _ = M * M * (Real.sin (2 * y)) ^ (1 + (2 - Work.Spaces.gam α)) := by
          rw [← Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.rpow_one_add hSy]
  calc |f (Real.pi / 2 - y) * deriv f (Real.pi / 2 - y) * 𝔰[α] (Real.pi / 2 - y)|
        ≤ M * M * (Real.sin (2 * y)) ^ (1 + (2 - Work.Spaces.gam α)) := hchain
    _ ≤ M * M * (2 * y) ^ (1 + (2 - Work.Spaces.gam α)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Real.rpow_le_rpow hSy.le hSle (by linarith)
    _ = M * M * 2 ^ (1 + (2 - Work.Spaces.gam α)) * y ^ (1 + (2 - Work.Spaces.gam α)) := by
        rw [Real.mul_rpow (by norm_num) (le_of_lt hy.1)]; ring

/-- `f² σ' → 0` at `0⁺`. -/
lemma tendsto_sq_sigDR_zero {α M : ℝ} {f : ℝ → ℝ} (hα1 : α ≤ 1) (hMnn : 0 ≤ M)
    (hfS : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ M * Real.sin (2 * θ)) :
    Filter.Tendsto (fun t : ℝ => f t ^ 2 * 𝔡[α] t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hp0 : 0 < 2 - Work.Spaces.gam α := Work.FTS.EllipticEst.Cores.sub_gam_pos hα1
  have hpne : 2 - Work.Spaces.gam α ≠ 0 := ne_of_gt hp0
  have hA : (0:ℝ) ≤ 2 * (2 - Work.Spaces.gam α) * M * M := by
    have h1 : 0 ≤ M * M := mul_nonneg hMnn hMnn
    nlinarith [hp0, h1]
  refine Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.tendsto_zero_of_abs_le_eventually
    (A := 2 * (2 - Work.Spaces.gam α) * M * M * 2 ^ (1 + (2 - Work.Spaces.gam α)))
    (e := 1 + (2 - Work.Spaces.gam α)) (ε := Real.pi / 4) (by linarith) (by linarith [Real.pi_pos]) ?_
  intro y hy
  have hyO : y ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hy.1, by linarith [hy.2, Real.pi_pos]⟩
  have hSp : 0 < Real.sin (2 * y) := Work.FTS.EllipticEst.TT.sin_two_pos_of_mem_Ioo hyO
  have hSle : Real.sin (2 * y) ≤ 2 * y := Real.sin_le (by linarith [hy.1])
  have hu2 : (f y) ^ 2 ≤ (M * Real.sin (2 * y)) ^ 2 := by
    have h0' : (0:ℝ) ≤ |f y| := abs_nonneg _
    calc (f y) ^ 2 = |f y| ^ 2 := (sq_abs (f y)).symm
      _ ≤ (M * Real.sin (2 * y)) ^ 2 := pow_le_pow_left₀ h0' (hfS y hyO) 2
  have hpow : (Real.sin (2 * y)) ^ 2 * (Real.sin (2 * y)) ^ ((2 - Work.Spaces.gam α) - 1)
      = (Real.sin (2 * y)) ^ (1 + (2 - Work.Spaces.gam α)) := by
    rw [show (Real.sin (2 * y)) ^ 2 = Real.sin (2 * y) * Real.sin (2 * y) by ring, mul_assoc,
      Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.mul_rpow_sub_one hSp hpne,
      ← Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.rpow_one_add hSp]
  have hbound : |f y ^ 2 * 𝔡[α] y|
      ≤ 2 * (2 - Work.Spaces.gam α) * M * M * (Real.sin (2 * y)) ^ (1 + (2 - Work.Spaces.gam α)) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (f y))]
    calc (f y) ^ 2 * |𝔡[α] y|
        ≤ (M * Real.sin (2 * y)) ^ 2
            * (2 * (2 - Work.Spaces.gam α) * (Real.sin (2 * y)) ^ ((2 - Work.Spaces.gam α) - 1)) :=
          mul_le_mul hu2 (sigDR_gam_abs_le hα1 hSp) (abs_nonneg _) (sq_nonneg _)
      _ = 2 * (2 - Work.Spaces.gam α) * M * M
            * ((Real.sin (2 * y)) ^ 2 * (Real.sin (2 * y)) ^ ((2 - Work.Spaces.gam α) - 1)) := by ring
      _ = 2 * (2 - Work.Spaces.gam α) * M * M
            * (Real.sin (2 * y)) ^ (1 + (2 - Work.Spaces.gam α)) := by rw [hpow]
  calc |f y ^ 2 * 𝔡[α] y|
        ≤ 2 * (2 - Work.Spaces.gam α) * M * M
            * (Real.sin (2 * y)) ^ (1 + (2 - Work.Spaces.gam α)) := hbound
    _ ≤ 2 * (2 - Work.Spaces.gam α) * M * M * (2 * y) ^ (1 + (2 - Work.Spaces.gam α)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hSp.le hSle (by linarith)) hA
    _ = 2 * (2 - Work.Spaces.gam α) * M * M * 2 ^ (1 + (2 - Work.Spaces.gam α))
          * y ^ (1 + (2 - Work.Spaces.gam α)) := by
        rw [Real.mul_rpow (by norm_num) (le_of_lt hy.1)]; ring

/-- `f² σ' → 0` at `(π/2)⁻`. -/
lemma tendsto_sq_sigDR_zero_right {α M : ℝ} {f : ℝ → ℝ} (hα1 : α ≤ 1) (hMnn : 0 ≤ M)
    (hfS : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ M * Real.sin (2 * θ)) :
    Filter.Tendsto (fun t : ℝ => f t ^ 2 * 𝔡[α] t)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hp0 : 0 < 2 - Work.Spaces.gam α := Work.FTS.EllipticEst.Cores.sub_gam_pos hα1
  have hpne : 2 - Work.Spaces.gam α ≠ 0 := ne_of_gt hp0
  have hA : (0:ℝ) ≤ 2 * (2 - Work.Spaces.gam α) * M * M := by
    have h1 : 0 ≤ M * M := mul_nonneg hMnn hMnn
    nlinarith [hp0, h1]
  refine Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.tendsto_zero_of_abs_le_eventually_right
    (A := 2 * (2 - Work.Spaces.gam α) * M * M * 2 ^ (1 + (2 - Work.Spaces.gam α)))
    (e := 1 + (2 - Work.Spaces.gam α)) (ε := Real.pi / 4) (by linarith) (by linarith [Real.pi_pos]) ?_
  intro y hy
  have hyO : Real.pi / 2 - y ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [hy.2, Real.pi_pos], by linarith [hy.1]⟩
  have hSy : 0 < Real.sin (2 * y) :=
    Work.FTS.EllipticEst.TT.sin_two_pos_of_mem_Ioo ⟨hy.1, by linarith [hy.2, Real.pi_pos]⟩
  have hSle : Real.sin (2 * y) ≤ 2 * y := Real.sin_le (by linarith [hy.1])
  have hsinref : Real.sin (2 * (Real.pi / 2 - y)) = Real.sin (2 * y) := by
    rw [show 2 * (Real.pi / 2 - y) = Real.pi - 2 * y by ring, Real.sin_pi_sub]
  have hfθ : |f (Real.pi / 2 - y)| ≤ M * Real.sin (2 * y) := by
    have h := hfS (Real.pi / 2 - y) hyO
    rwa [hsinref] at h
  have hu2 : (f (Real.pi / 2 - y)) ^ 2 ≤ (M * Real.sin (2 * y)) ^ 2 := by
    have h0' : (0:ℝ) ≤ |f (Real.pi / 2 - y)| := abs_nonneg _
    calc (f (Real.pi / 2 - y)) ^ 2 = |f (Real.pi / 2 - y)| ^ 2 := (sq_abs _).symm
      _ ≤ (M * Real.sin (2 * y)) ^ 2 := pow_le_pow_left₀ h0' hfθ 2
  have hdr : |𝔡[α] (Real.pi / 2 - y)|
      ≤ 2 * (2 - Work.Spaces.gam α) * (Real.sin (2 * y)) ^ ((2 - Work.Spaces.gam α) - 1) := by
    rw [sigDR_gam_abs_reflect]; exact sigDR_gam_abs_le hα1 hSy
  have hpow : (Real.sin (2 * y)) ^ 2 * (Real.sin (2 * y)) ^ ((2 - Work.Spaces.gam α) - 1)
      = (Real.sin (2 * y)) ^ (1 + (2 - Work.Spaces.gam α)) := by
    rw [show (Real.sin (2 * y)) ^ 2 = Real.sin (2 * y) * Real.sin (2 * y) by ring, mul_assoc,
      Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.mul_rpow_sub_one hSy hpne,
      ← Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.rpow_one_add hSy]
  have hbound : |f (Real.pi / 2 - y) ^ 2 * 𝔡[α] (Real.pi / 2 - y)|
      ≤ 2 * (2 - Work.Spaces.gam α) * M * M * (Real.sin (2 * y)) ^ (1 + (2 - Work.Spaces.gam α)) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (f (Real.pi / 2 - y)))]
    calc (f (Real.pi / 2 - y)) ^ 2 * |𝔡[α] (Real.pi / 2 - y)|
        ≤ (M * Real.sin (2 * y)) ^ 2
            * (2 * (2 - Work.Spaces.gam α) * (Real.sin (2 * y)) ^ ((2 - Work.Spaces.gam α) - 1)) :=
          mul_le_mul hu2 hdr (abs_nonneg _) (sq_nonneg _)
      _ = 2 * (2 - Work.Spaces.gam α) * M * M
            * ((Real.sin (2 * y)) ^ 2 * (Real.sin (2 * y)) ^ ((2 - Work.Spaces.gam α) - 1)) := by ring
      _ = 2 * (2 - Work.Spaces.gam α) * M * M
            * (Real.sin (2 * y)) ^ (1 + (2 - Work.Spaces.gam α)) := by rw [hpow]
  calc |f (Real.pi / 2 - y) ^ 2 * 𝔡[α] (Real.pi / 2 - y)|
        ≤ 2 * (2 - Work.Spaces.gam α) * M * M
            * (Real.sin (2 * y)) ^ (1 + (2 - Work.Spaces.gam α)) := hbound
    _ ≤ 2 * (2 - Work.Spaces.gam α) * M * M * (2 * y) ^ (1 + (2 - Work.Spaces.gam α)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hSy.le hSle (by linarith)) hA
    _ = 2 * (2 - Work.Spaces.gam α) * M * M * 2 ^ (1 + (2 - Work.Spaces.gam α))
          * y ^ (1 + (2 - Work.Spaces.gam α)) := by
        rw [Real.mul_rpow (by norm_num) (le_of_lt hy.1)]; ring


end Work.FTS.ClassC.VopGen
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollAssem.FatouCore =====
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

/-! ## The Fatou assembly -/

/-- The Fatou assembly, with the slice honesty of the diagonal approximants as an explicit
hypothesis. -/
theorem mollFatouCore (G : ℝ → ℝ → ℝ) (hT : TraceClass G) (hF : FourInts G)
    (hint : ∀ δ ε : ℝ, Params δ ε → MeasureTheory.IntegrableOn
      (fun z : ℝ => Work.EllipticEst.Core.mixIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z)
      Work.Spaces.Iz)
    (hconv : ∀ z : ℝ, 0 < z → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Filter.Tendsto (fun n : ℕ => (Work.Spaces.Dz (Work.Spaces.pth
        (Work.FTS.EllSol.PkgK5.K5c.zmoll G (tseq n) (tseq n))) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) Filter.atTop
        (nhds ((Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)))
    (hhon : ∀ (n : ℕ) (z : ℝ), 0 < z → MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.pth
        (Work.FTS.EllSol.PkgK5.K5c.zmoll G (tseq n) (tseq n))) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hhonest : ∀ (n : ℕ) (z : ℝ), 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.pth
        (Work.FTS.EllSol.PkgK5.K5c.zmoll G (tseq n) (tseq n))) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) :
    ∀ η : ℝ, 0 < η → ∃ δ ε : ℝ, Params δ ε ∧
      (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z)
        ≤ (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS
            (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z) + η := by
  intro η hη
  -- Step 1: for every `z > 0`, Fatou in `θ` compares the angular slices.
  have key1 : ∀ z : ℝ, 0 < z → ENNReal.ofReal (Work.EllipticEst.Core.mixIntS G z)
      ≤ Filter.liminf (fun n : ℕ => ENNReal.ofReal (Work.EllipticEst.Core.mixIntS
          (Work.FTS.EllSol.PkgK5.K5c.zmoll G (tseq n) (tseq n)) z)) Filter.atTop := by
    intro z hz
    set c : ℝ := (Work.Spaces.w z) ^ 2 with hc
    set u : ℝ → ℝ := fun θ => (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
      * Work.FTS.EllipticEst.thEta θ with hu
    set un : ℕ → ℝ → ℝ := fun n θ => (Work.Spaces.Dz (Work.Spaces.pth
      (Work.FTS.EllSol.PkgK5.K5c.zmoll G (tseq n) (tseq n))) z θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ with hun
    have hun' : ∀ n θ, un n θ = (Work.Spaces.Dz (Work.Spaces.pth
        (Work.FTS.EllSol.PkgK5.K5c.zmoll G (tseq n) (tseq n))) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ := fun n θ => rfl
    have hcnn : 0 ≤ c := by rw [hc]; exact sq_nonneg _
    have hunn : ∀ n, 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] un n := by
      intro n
      refine ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      rw [hun' n θ]
      exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
    have hunn' : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] u := by
      refine ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
    have hFatouθ : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (c * u θ))
        ≤ Filter.liminf (fun n : ℕ => ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (c * un n θ)) Filter.atTop := by
      refine fatou_lintegral_le_liminf
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (G := fun n θ => c * un n θ) (f := fun θ => c * u θ) ?_ ?_
      · intro n
        exact aemeasurable_ofReal_of_aestronglyMeasurable
          ((hhon n z hz).const_mul c)
      · filter_upwards [hconv z hz] with θ hθ
        exact le_of_eq (ENNReal.tendsto_ofReal (hθ.const_mul c)).liminf_eq.symm
    -- The left-hand end: the honest `θ`-integral is below the `θ`-lower integral.
    have hLHS : ENNReal.ofReal (c * (∫ θ in Work.Spaces.Iθ, u θ))
        ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (c * u θ) := by
      by_cases hintg : Integrable u (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      · rw [ENNReal.ofReal_mul hcnn,
          MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintg hunn']
        rw [show (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (c * u θ))
            = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal c * ENNReal.ofReal (u θ) from
          lintegral_congr (fun θ => ENNReal.ofReal_mul hcnn)]
        exact le_of_eq (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      · rw [MeasureTheory.integral_undef hintg, mul_zero, ENNReal.ofReal_zero]
        exact zero_le
    -- The right-hand end: honesty of the approximant's `θ`-slices.
    have hRHS : ∀ n : ℕ, (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (c * un n θ))
        = ENNReal.ofReal (c * (∫ θ in Work.Spaces.Iθ, un n θ)) := by
      intro n
      have hintn : Integrable (un n) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        hhonest n z hz
      rw [show (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (c * un n θ))
            = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal c * ENNReal.ofReal (un n θ) from
          lintegral_congr (fun θ => ENNReal.ofReal_mul hcnn),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintn (hunn n)]
      exact (ENNReal.ofReal_mul hcnn).symm
    have hlim_eq : Filter.liminf (fun n : ℕ => ENNReal.ofReal (Work.EllipticEst.Core.mixIntS
          (Work.FTS.EllSol.PkgK5.K5c.zmoll G (tseq n) (tseq n)) z)) Filter.atTop
        = Filter.liminf (fun n : ℕ => ENNReal.ofReal
            (c * (∫ θ in Work.Spaces.Iθ, un n θ))) Filter.atTop :=
      Filter.liminf_congr (Filter.Eventually.of_forall (fun n => by
        rw [show Work.EllipticEst.Core.mixIntS
            (Work.FTS.EllSol.PkgK5.K5c.zmoll G (tseq n) (tseq n)) z
            = c * (∫ θ in Work.Spaces.Iθ, un n θ) from rfl]))
    have hMG : Work.EllipticEst.Core.mixIntS G z = c * (∫ θ in Work.Spaces.Iθ, u θ) := rfl
    rw [hMG, hlim_eq]
    exact hLHS.trans (hFatouθ.trans (le_of_eq (Filter.liminf_congr
      (Filter.Eventually.of_forall hRHS))))
  -- Step 2: the pointwise bound holds a.e. on `Iz` (only `z = 0` is not covered).
  have key2 : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ENNReal.ofReal (Work.EllipticEst.Core.mixIntS G z)
        ≤ Filter.liminf (fun n : ℕ => ENNReal.ofReal (Work.EllipticEst.Core.mixIntS
            (Work.FTS.EllSol.PkgK5.K5c.zmoll G (tseq n) (tseq n)) z)) Filter.atTop := by
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
    refine Filter.Eventually.of_forall (fun z hz => ?_)
    by_cases hz0 : 0 < z
    · exact key1 z hz0
    · have hz_eq : z = 0 := le_antisymm (not_lt.mp hz0) hz
      subst hz_eq
      rw [show Work.EllipticEst.Core.mixIntS G 0 = 0 from ?_]
      · rw [ENNReal.ofReal_zero]; exact zero_le
      · rw [Work.EllipticEst.Core.mixIntS]
        have hw0 : Work.Spaces.w (0 : ℝ) = 0 := by rw [Work.Spaces.w]; norm_num
        rw [hw0]
        ring
  -- Step 3: Fatou in `z`.
  have hzmeas : ∀ n : ℕ, AEMeasurable (fun z : ℝ => ENNReal.ofReal
      (Work.EllipticEst.Core.mixIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G
        (tseq n) (tseq n)) z)) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    fun n => aemeasurable_ofReal_of_aestronglyMeasurable
      ((hint _ _ (params_tseq n)).integrable).aestronglyMeasurable
  have hzFatou := fatou_lintegral_le_liminf
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz) hzmeas key2
  have hLconvert : (∫⁻ z, ENNReal.ofReal (Work.EllipticEst.Core.mixIntS G z)
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      = ENNReal.ofReal (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hF.1
      (ae_of_all _ (fun z => mixIntS_nonneg_mfa G z))).symm
  have hRconvert : ∀ n : ℕ, (∫⁻ z, ENNReal.ofReal (Work.EllipticEst.Core.mixIntS
        (Work.FTS.EllSol.PkgK5.K5c.zmoll G (tseq n) (tseq n)) z)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      = ENNReal.ofReal (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS
          (Work.FTS.EllSol.PkgK5.K5c.zmoll G (tseq n) (tseq n)) z) := by
    intro n
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      ((hint _ _ (params_tseq n)).integrable)
      (ae_of_all _ (fun z => mixIntS_nonneg_mfa _ z))).symm
  have key3 : ENNReal.ofReal (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z)
      ≤ Filter.liminf (fun n : ℕ => ENNReal.ofReal (∫ z in Work.Spaces.Iz,
          Work.EllipticEst.Core.mixIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G
            (tseq n) (tseq n)) z)) Filter.atTop := by
    rw [← hLconvert, ← Filter.liminf_congr (Filter.Eventually.of_forall hRconvert)]
    exact hzFatou
  -- Step 4: extract a single index `n`.
  by_cases hsmall : (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z) ≤ η
  · refine ⟨tseq 0, tseq 0, params_tseq 0, ?_⟩
    have hb0 : 0 ≤ ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS
        (Work.FTS.EllSol.PkgK5.K5c.zmoll G (tseq 0) (tseq 0)) z :=
      MeasureTheory.integral_nonneg_of_ae (ae_of_all _ (fun z => mixIntS_nonneg_mfa _ z))
    linarith
  · have hsmall' : η < (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z) :=
      not_le.mp hsmall
    by_contra hcon
    have hb : ∀ n : ℕ, (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS
          (Work.FTS.EllSol.PkgK5.K5c.zmoll G (tseq n) (tseq n)) z)
        ≤ (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z) - η := by
      intro n
      have h : ¬ ((∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z)
          ≤ (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS
              (Work.FTS.EllSol.PkgK5.K5c.zmoll G (tseq n) (tseq n)) z) + η) :=
        fun hh => hcon ⟨tseq n, tseq n, params_tseq n, hh⟩
      linarith [not_le.mp h]
    have hlimle : Filter.liminf (fun n : ℕ => ENNReal.ofReal (∫ z in Work.Spaces.Iz,
          Work.EllipticEst.Core.mixIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G
            (tseq n) (tseq n)) z)) Filter.atTop
        ≤ ENNReal.ofReal ((∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z) - η) :=
      Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall
        (fun n => ENNReal.ofReal_le_ofReal (hb n)))
    have hfinal := key3.trans hlimle
    have hpos : 0 ≤ (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z) - η := by
      linarith
    have hfin := (ENNReal.ofReal_le_ofReal_iff hpos).mp hfinal
    linarith

end MollAssem

end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollAux.aesmE2s =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllSol.EllPkgAux.MollAux

/-- **Measurability of an angular slice energy.**  If `u` is continuous on the open quadrant,
then `w ↦ ∫_{Iθ} (u w θ)² σ_η(θ)` is a.e. strongly measurable on `[a,b]` for every `0 < a`.

(The only use of the open quadrant is joint a.e. strong measurability of `u` on the product
`(volume.restrict (Icc a b)).prod (volume.restrict Iθ)`, whose underlying set differs from
`Icc a b ×ˢ Ioo 0 (π/2) ⊆ Q0` by a null set.) -/
theorem aesm_sliceEnergy_of_continuousOn {u : ℝ → ℝ → ℝ}
    (hu : ContinuousOn (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    {a b : ℝ} (ha : 0 < a) :
    MeasureTheory.AEStronglyMeasurable
      (fun w : ℝ => ∫ θ in Work.Spaces.Iθ,
        (u w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (MeasureTheory.volume.restrict (Set.Icc a b)) := by
  set F : ℝ × ℝ → ℝ := fun p => (u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.thEta p.2 with hF
  -- `σ_η` is continuous on the open quadrant
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hcont2 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.thEta p.2)
      Work.FTS.EllipticEst.Q0 := by
    simp only [Work.FTS.EllipticEst.thEta]
    exact hsin.rpow_const (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  -- hence so is the integrand, and it is a.e. strongly measurable for the planar measure
  have hFcont : ContinuousOn F Work.FTS.EllipticEst.Q0 := (hu.pow 2).mul hcont2
  have hFaesm : AEStronglyMeasurable F (volume.restrict Work.FTS.EllipticEst.Q0) :=
    hFcont.aestronglyMeasurable Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  -- `Icc a b ⊆ Ioi 0`, so the rectangle is inside the open quadrant up to the null angular
  -- boundary lines
  have hsub : Set.Icc a b ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.FTS.EllipticEst.Q0 :=
    fun p hp => Set.mem_prod.mpr ⟨lt_of_lt_of_le ha hp.1.1, hp.2⟩
  have hFaesm' : AEStronglyMeasurable F
      (volume.restrict (Set.Icc a b ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hFaesm.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hae : (Set.Icc a b : Set ℝ) ×ˢ Work.Spaces.Iθ
      =ᵐ[(volume : Measure (ℝ × ℝ))] Set.Icc a b ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    refine Measure.set_prod_ae_eq (Filter.EventuallyEq.refl _ _) ?_
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Ioo_ae_eq_Icc.symm
  have hprod : AEStronglyMeasurable F
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [Measure.prod_restrict]
    change AEStronglyMeasurable F (volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ))
    rw [Measure.restrict_congr_set hae]
    exact hFaesm'
  -- Fubini-measurability of the Bochner integral
  have key : AEStronglyMeasurable
      (fun w : ℝ => ∫ θ, F (w, θ) ∂(volume.restrict Work.Spaces.Iθ))
      (volume.restrict (Set.Icc a b)) :=
    hprod.integral_prod_right' (ν := volume.restrict Work.Spaces.Iθ)
  have hEq : (fun w : ℝ => ∫ θ in Work.Spaces.Iθ,
        (u w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      = fun w : ℝ => ∫ θ, F (w, θ) ∂(volume.restrict Work.Spaces.Iθ) := by
    funext w
    simp only [hF]
  rw [hEq]
  exact key

theorem aesmE2s {G : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen G)
    {a b : ℝ} (ha : 0 < a) :
    MeasureTheory.AEStronglyMeasurable (Work.FTS.EllSol.EllPkgAux.E2s G)
      (MeasureTheory.volume.restrict (Set.Icc a b)) := by
  have hEq : (Work.FTS.EllSol.EllPkgAux.E2s G)
      = fun w : ℝ => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ := by
    funext w
    simp only [Work.FTS.EllSol.EllPkgAux.E2s]
  rw [hEq]
  exact aesm_sliceEnergy_of_continuousOn (hsm.pth.pth).continuousOn ha

end Work.FTS.EllSol.EllPkgAux.MollAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.ZmollTTDefs =====
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

set_option autoImplicit false

open Work.FTS.EllSol.PkgK5.K5c (sKer Qext)

/-- `sKer ε` has compact support (inside `[-ε, ε]`). -/
theorem hasCompactSupport_sKer {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (sKer ε) := by
  refine HasCompactSupport.intro (K := Set.Icc (-ε) ε) isCompact_Icc ?_
  intro t ht
  refine Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε ?_
  rw [Set.mem_Icc, not_and_or] at ht
  rcases ht with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-- `sKerd ε = (sKer ε)'` is smooth. -/
theorem contDiff_sKerd (ε : ℝ) {n : ℕ∞} : ContDiff ℝ n (Work.FTS.EllSol.EllPkgAux.sKerd ε) := by
  have h : ContDiff ℝ (n + 1) (Work.FTS.EllSol.PkgK5.K5c.sKer ε) :=
    Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε
  simpa only [Work.FTS.EllSol.EllPkgAux.sKerd] using h.deriv'

/-- The second derivative of the mollifying kernel, `sKerd2 ε = (sKer ε)''`. -/
def sKerd2 (ε : ℝ) : ℝ → ℝ := deriv (Work.FTS.EllSol.EllPkgAux.sKerd ε)


theorem contDiff_sKerd2 (ε : ℝ) {n : ℕ∞} : ContDiff ℝ n (sKerd2 ε) := by
  have h : ContDiff ℝ (n + 1) (Work.FTS.EllSol.EllPkgAux.sKerd ε) := contDiff_sKerd ε
  simpa only [sKerd2] using h.deriv'

/-- `sKerd ε` has compact support. -/
theorem hasCompactSupport_sKerd {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (Work.FTS.EllSol.EllPkgAux.sKerd ε) :=
  (hasCompactSupport_sKer hε).deriv

/-- `sKerd2 ε` has compact support. -/
theorem hasCompactSupport_sKerd2 {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (sKerd2 ε) :=
  (hasCompactSupport_sKerd hε).deriv

theorem sKerd_bdd' {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, |Work.FTS.EllSol.EllPkgAux.sKerd ε x| ≤ M := by
  have hc : Continuous (Work.FTS.EllSol.EllPkgAux.sKerd ε) :=
    (contDiff_sKerd ε (n := 0)).continuous
  have hcs : HasCompactSupport (Work.FTS.EllSol.EllPkgAux.sKerd ε) := hasCompactSupport_sKerd hε
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hc
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x => ?_⟩
  have h := hC x
  rw [Real.norm_eq_abs] at h
  exact le_trans h (le_max_left _ _)

/-- A bound for `sKerd2 ε`. -/
theorem sKerd2_bdd {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, |sKerd2 ε x| ≤ M := by
  have hc : Continuous (sKerd2 ε) := (contDiff_sKerd2 ε (n := 0)).continuous
  have hcs : HasCompactSupport (sKerd2 ε) := hasCompactSupport_sKerd2 hε
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hc
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x => ?_⟩
  have h := hC x
  rw [Real.norm_eq_abs] at h
  exact le_trans h (le_max_left _ _)

/-! ## The signed three-image kernel and its derivatives -/

/-- The signed three-image kernel of the fold of the doubly odd extension. -/
def km (ε θ s : ℝ) : ℝ :=
  sKer ε (θ - s) - sKer ε (θ + s) - sKer ε (θ + s - Real.pi)

/-- `∂_θ` of `km`. -/
def kmθ (ε θ s : ℝ) : ℝ :=
  Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s) - Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s)
    - Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s - Real.pi)

/-- `∂_s` of `km`. -/
def kms (ε θ s : ℝ) : ℝ :=
  - Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s) - Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s)
    - Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s - Real.pi)

/-- `∂_θ² km = ∂_s² km` (and `∂_θ kmθ = ∂_s kms`). -/
def kmθθ (ε θ s : ℝ) : ℝ :=
  sKerd2 ε (θ - s) - sKerd2 ε (θ + s) - sKerd2 ε (θ + s - Real.pi)

/-! ## `HasDerivAt` in `θ` -/

theorem hasDerivAt_km_theta (ε θ s : ℝ) :
    HasDerivAt (fun θ' : ℝ => km ε θ' s) (kmθ ε θ s) θ := by
  have h1 : HasDerivAt (fun x : ℝ => sKer ε (x - s))
      (Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s)) θ := by
    have hderiv : HasDerivAt (sKer ε) (deriv (sKer ε) (θ - s)) (θ - s) :=
      (((Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 1)).differentiable_one) (θ - s)).hasDerivAt
    have hcomp := hderiv.comp θ ((hasDerivAt_id θ).sub_const s)
    simpa [Function.comp_def, Work.FTS.EllSol.EllPkgAux.sKerd] using hcomp
  have h2 : HasDerivAt (fun x : ℝ => sKer ε (x + s))
      (Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s)) θ := by
    have hderiv : HasDerivAt (sKer ε) (deriv (sKer ε) (θ + s)) (θ + s) :=
      (((Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 1)).differentiable_one) (θ + s)).hasDerivAt
    have hcomp := hderiv.comp θ ((hasDerivAt_id θ).add_const s)
    simpa [Function.comp_def, Work.FTS.EllSol.EllPkgAux.sKerd] using hcomp
  have h3 : HasDerivAt (fun x : ℝ => sKer ε (x + s - Real.pi))
      (Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s - Real.pi)) θ := by
    have hderiv : HasDerivAt (sKer ε) (deriv (sKer ε) (θ + s - Real.pi)) (θ + s - Real.pi) :=
      (((Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 1)).differentiable_one) _).hasDerivAt
    have hcomp := hderiv.comp θ (((hasDerivAt_id θ).add_const s).sub_const Real.pi)
    simpa [Function.comp_def, Work.FTS.EllSol.EllPkgAux.sKerd] using hcomp
  exact (h1.sub h2).sub h3

theorem hasDerivAt_kmθ_theta (ε θ s : ℝ) :
    HasDerivAt (fun θ' : ℝ => kmθ ε θ' s) (kmθθ ε θ s) θ := by
  have h1 : HasDerivAt (fun x : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd ε (x - s))
      (sKerd2 ε (θ - s)) θ := by
    have hderiv : HasDerivAt (Work.FTS.EllSol.EllPkgAux.sKerd ε)
        (deriv (Work.FTS.EllSol.EllPkgAux.sKerd ε) (θ - s)) (θ - s) :=
      (((contDiff_sKerd ε (n := 1)).differentiable_one) (θ - s)).hasDerivAt
    have hcomp := hderiv.comp θ ((hasDerivAt_id θ).sub_const s)
    simpa [Function.comp_def, sKerd2] using hcomp
  have h2 : HasDerivAt (fun x : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd ε (x + s))
      (sKerd2 ε (θ + s)) θ := by
    have hderiv : HasDerivAt (Work.FTS.EllSol.EllPkgAux.sKerd ε)
        (deriv (Work.FTS.EllSol.EllPkgAux.sKerd ε) (θ + s)) (θ + s) :=
      (((contDiff_sKerd ε (n := 1)).differentiable_one) (θ + s)).hasDerivAt
    have hcomp := hderiv.comp θ ((hasDerivAt_id θ).add_const s)
    simpa [Function.comp_def, sKerd2] using hcomp
  have h3 : HasDerivAt (fun x : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd ε (x + s - Real.pi))
      (sKerd2 ε (θ + s - Real.pi)) θ := by
    have hderiv : HasDerivAt (Work.FTS.EllSol.EllPkgAux.sKerd ε)
        (deriv (Work.FTS.EllSol.EllPkgAux.sKerd ε) (θ + s - Real.pi)) (θ + s - Real.pi) :=
      (((contDiff_sKerd ε (n := 1)).differentiable_one) _).hasDerivAt
    have hcomp := hderiv.comp θ (((hasDerivAt_id θ).add_const s).sub_const Real.pi)
    simpa [Function.comp_def, sKerd2] using hcomp
  exact (h1.sub h2).sub h3

theorem hasDerivAt_km_s (ε θ s : ℝ) :
    HasDerivAt (fun x : ℝ => km ε θ x) (kms ε θ s) s := by
  have h1 : HasDerivAt (fun x : ℝ => sKer ε (θ - x))
      (-(Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s))) s := by
    have hderiv : HasDerivAt (sKer ε) (deriv (sKer ε) (θ - s)) (θ - s) :=
      (((Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 1)).differentiable_one) (θ - s)).hasDerivAt
    have hcomp := hderiv.comp s ((hasDerivAt_id s).const_sub θ)
    simpa [Function.comp_def, Work.FTS.EllSol.EllPkgAux.sKerd] using hcomp
  have h2 : HasDerivAt (fun x : ℝ => sKer ε (θ + x))
      (Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s)) s := by
    have hderiv : HasDerivAt (sKer ε) (deriv (sKer ε) (θ + s)) (θ + s) :=
      (((Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 1)).differentiable_one) (θ + s)).hasDerivAt
    have hcomp := hderiv.comp s ((hasDerivAt_id s).const_add θ)
    simpa [Function.comp_def, Work.FTS.EllSol.EllPkgAux.sKerd, add_comm] using hcomp
  have h3 : HasDerivAt (fun x : ℝ => sKer ε (θ + x - Real.pi))
      (Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s - Real.pi)) s := by
    have hderiv : HasDerivAt (sKer ε) (deriv (sKer ε) (θ + s - Real.pi)) (θ + s - Real.pi) :=
      (((Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 1)).differentiable_one) _).hasDerivAt
    have hcomp := hderiv.comp s (((hasDerivAt_id s).const_add θ).sub_const Real.pi)
    simpa [Function.comp_def, Work.FTS.EllSol.EllPkgAux.sKerd, add_comm, add_assoc] using hcomp
  exact (h1.sub h2).sub h3

theorem hasDerivAt_kms_s (ε θ s : ℝ) :
    HasDerivAt (fun x : ℝ => kms ε θ x) (kmθθ ε θ s) s := by
  have h1 : HasDerivAt (fun x : ℝ => -(Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - x)))
      (sKerd2 ε (θ - s)) s := by
    have hpos : HasDerivAt (fun x : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - x))
        (-(sKerd2 ε (θ - s))) s := by
      have hderiv : HasDerivAt (Work.FTS.EllSol.EllPkgAux.sKerd ε)
          (deriv (Work.FTS.EllSol.EllPkgAux.sKerd ε) (θ - s)) (θ - s) :=
        (((contDiff_sKerd ε (n := 1)).differentiable_one) (θ - s)).hasDerivAt
      have hcomp := hderiv.comp s ((hasDerivAt_id s).const_sub θ)
      simpa [Function.comp_def, sKerd2] using hcomp
    have hn := hpos.neg
    have hfun : (-(fun x : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - x)))
        = fun x : ℝ => -(Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - x)) := rfl
    rw [hfun] at hn
    simpa using hn
  have h2 : HasDerivAt (fun x : ℝ => -(Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + x)))
      (-(sKerd2 ε (θ + s))) s := by
    have hpos : HasDerivAt (fun x : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + x))
        (sKerd2 ε (θ + s)) s := by
      have hderiv : HasDerivAt (Work.FTS.EllSol.EllPkgAux.sKerd ε)
          (deriv (Work.FTS.EllSol.EllPkgAux.sKerd ε) (θ + s)) (θ + s) :=
        (((contDiff_sKerd ε (n := 1)).differentiable_one) (θ + s)).hasDerivAt
      have hcomp := hderiv.comp s ((hasDerivAt_id s).const_add θ)
      simpa [Function.comp_def, sKerd2, add_comm] using hcomp
    have hn := hpos.neg
    have hfun : (-(fun x : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + x)))
        = fun x : ℝ => -(Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + x)) := rfl
    rw [hfun] at hn
    simpa using hn
  have h3 : HasDerivAt (fun x : ℝ => -(Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + x - Real.pi)))
      (-(sKerd2 ε (θ + s - Real.pi))) s := by
    have hpos : HasDerivAt (fun x : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + x - Real.pi))
        (sKerd2 ε (θ + s - Real.pi)) s := by
      have hderiv : HasDerivAt (Work.FTS.EllSol.EllPkgAux.sKerd ε)
          (deriv (Work.FTS.EllSol.EllPkgAux.sKerd ε) (θ + s - Real.pi)) (θ + s - Real.pi) :=
        (((contDiff_sKerd ε (n := 1)).differentiable_one) _).hasDerivAt
      have hcomp := hderiv.comp s (((hasDerivAt_id s).const_add θ).sub_const Real.pi)
      simpa [Function.comp_def, sKerd2, add_comm, add_assoc] using hcomp
    have hn := hpos.neg
    have hfun : (-(fun x : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + x - Real.pi)))
        = fun x : ℝ => -(Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + x - Real.pi)) := rfl
    rw [hfun] at hn
    simpa using hn
  exact (h1.add h2).add h3



/-! ## Continuity -/

theorem continuous_sKer (ε : ℝ) : Continuous (sKer ε) :=
  (Work.FTS.EllSol.EllPkgAux.contDiff_sKer ε (n := 0)).continuous

theorem continuous_sKerd (ε : ℝ) : Continuous (Work.FTS.EllSol.EllPkgAux.sKerd ε) :=
  (contDiff_sKerd ε (n := 0)).continuous

theorem continuous_sKerd2 (ε : ℝ) : Continuous (sKerd2 ε) :=
  (contDiff_sKerd2 ε (n := 0)).continuous

theorem continuous_km (ε θ : ℝ) : Continuous (fun s : ℝ => km ε θ s) := by
  have h1 : Continuous (fun s : ℝ => sKer ε (θ - s)) :=
    (continuous_sKer ε).comp (continuous_const.sub continuous_id)
  have h2 : Continuous (fun s : ℝ => sKer ε (θ + s)) :=
    (continuous_sKer ε).comp (continuous_const.add continuous_id)
  have h3 : Continuous (fun s : ℝ => sKer ε (θ + s - Real.pi)) :=
    (continuous_sKer ε).comp ((continuous_const.add continuous_id).sub continuous_const)
  exact (h1.sub h2).sub h3

theorem continuous_kmθ (ε θ : ℝ) : Continuous (fun s : ℝ => kmθ ε θ s) := by
  have h1 : Continuous (fun s : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s)) :=
    (continuous_sKerd ε).comp (continuous_const.sub continuous_id)
  have h2 : Continuous (fun s : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s)) :=
    (continuous_sKerd ε).comp (continuous_const.add continuous_id)
  have h3 : Continuous (fun s : ℝ => Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s - Real.pi)) :=
    (continuous_sKerd ε).comp ((continuous_const.add continuous_id).sub continuous_const)
  exact (h1.sub h2).sub h3

theorem continuous_kms (ε θ : ℝ) : Continuous (fun s : ℝ => kms ε θ s) := by
  have h1 : Continuous (fun s : ℝ => -(Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s))) :=
    ((continuous_sKerd ε).comp (continuous_const.sub continuous_id)).neg
  have h2 : Continuous (fun s : ℝ => -(Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s))) :=
    ((continuous_sKerd ε).comp (continuous_const.add continuous_id)).neg
  have h3 : Continuous (fun s : ℝ => -(Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s - Real.pi))) :=
    ((continuous_sKerd ε).comp ((continuous_const.add continuous_id).sub continuous_const)).neg
  have h := (h1.add h2).add h3
  have hfun : ((fun s : ℝ => -(Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s)))
      + (fun s : ℝ => -(Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s)))
      + (fun s : ℝ => -(Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s - Real.pi))))
      = fun s : ℝ => kms ε θ s := by
    funext s
    simp only [Pi.add_apply, kms]
    ring
  rwa [hfun] at h

theorem continuous_kmθθ (ε θ : ℝ) : Continuous (fun s : ℝ => kmθθ ε θ s) := by
  have h1 : Continuous (fun s : ℝ => sKerd2 ε (θ - s)) :=
    (continuous_sKerd2 ε).comp (continuous_const.sub continuous_id)
  have h2 : Continuous (fun s : ℝ => sKerd2 ε (θ + s)) :=
    (continuous_sKerd2 ε).comp (continuous_const.add continuous_id)
  have h3 : Continuous (fun s : ℝ => sKerd2 ε (θ + s - Real.pi)) :=
    (continuous_sKerd2 ε).comp ((continuous_const.add continuous_id).sub continuous_const)
  exact (h1.sub h2).sub h3



/-! ## The endpoint values of the folded kernel -/

theorem km_zero_left {ε θ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    km ε θ 0 = - sKer ε (θ - Real.pi) := by
  simp only [km, sub_zero, add_zero]
  ring

theorem km_zero_left' {ε θ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hθ : θ ∈ Work.Spaces.Iθ) : km ε θ 0 = 0 := by
  rw [km_zero_left hε0 hε1]
  refine neg_eq_zero.mpr (Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε0 ?_)
  have h1 : (0 : ℝ) ≤ θ := hθ.1
  have h2 : θ ≤ Real.pi / 2 := hθ.2
  rw [show θ - Real.pi = -(Real.pi - θ) by ring, abs_neg, abs_of_nonneg (by linarith [h2])]
  linarith [Real.pi_gt_three]

theorem km_zero_right {ε θ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hθ : θ ∈ Work.Spaces.Iθ) : km ε θ (Real.pi / 2) = 0 := by
  have h1 : (0 : ℝ) ≤ θ := hθ.1
  have hright : sKer ε (θ + Real.pi / 2) = 0 := by
    refine Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε0 ?_
    rw [abs_of_nonneg (by linarith [Real.pi_pos])]
    linarith [Real.pi_gt_three, hε1, h1]
  have hthird : θ + Real.pi / 2 - Real.pi = θ - Real.pi / 2 := by ring
  simp only [km]
  rw [hthird, hright]
  ring

/-! ## Bounds -/

theorem kmθ_bdd {ε : ℝ} (hε : 0 < ε) : ∃ C : ℝ, 0 ≤ C ∧ ∀ θ s : ℝ, |kmθ ε θ s| ≤ C := by
  obtain ⟨M, hM0, hM⟩ := sKerd_bdd' hε
  refine ⟨3 * M, by positivity, fun θ s => ?_⟩
  have h1 := hM (θ - s)
  have h2 := hM (θ + s)
  have h3 := hM (θ + s - Real.pi)
  simp only [kmθ]
  calc |Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s) - Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s)
        - Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s - Real.pi)|
      ≤ |Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s) - Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s)|
        + |Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s - Real.pi)| := abs_sub _ _
    _ ≤ (|Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s)|
          + |Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s)|)
        + |Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s - Real.pi)| := by
        linarith [abs_sub (Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s))
          (Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s)),
          abs_nonneg (Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s - Real.pi))]
    _ ≤ M + M + M := by linarith [abs_nonneg (Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s))]
    _ = 3 * M := by ring

theorem kms_bdd {ε : ℝ} (hε : 0 < ε) : ∃ C : ℝ, 0 ≤ C ∧ ∀ θ s : ℝ, |kms ε θ s| ≤ C := by
  obtain ⟨M, hM0, hM⟩ := sKerd_bdd' hε
  refine ⟨3 * M, by positivity, fun θ s => ?_⟩
  have h1 := hM (θ - s)
  have h2 := hM (θ + s)
  have h3 := hM (θ + s - Real.pi)
  simp only [kms]
  calc |-Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s)
        - Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s)
        - Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s - Real.pi)|
      ≤ |-Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s)
          - Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s)|
        + |Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s - Real.pi)| := abs_sub _ _
    _ ≤ (|Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s)|
          + |Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s)|)
        + |Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s - Real.pi)| := by
        have h := abs_sub (-Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s))
          (Work.FTS.EllSol.EllPkgAux.sKerd ε (θ + s))
        rw [abs_neg] at h
        linarith [h, h1, h2, h3, abs_nonneg (Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s))]
    _ ≤ M + M + M := by linarith [abs_nonneg (Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s))]
    _ = 3 * M := by ring

theorem kmθθ_bdd {ε : ℝ} (hε : 0 < ε) : ∃ C : ℝ, 0 ≤ C ∧ ∀ θ s : ℝ, |kmθθ ε θ s| ≤ C := by
  obtain ⟨M, hM0, hM⟩ := sKerd2_bdd hε
  refine ⟨3 * M, by positivity, fun θ s => ?_⟩
  have h1 := hM (θ - s)
  have h2 := hM (θ + s)
  have h3 := hM (θ + s - Real.pi)
  simp only [kmθθ]
  calc |sKerd2 ε (θ - s) - sKerd2 ε (θ + s) - sKerd2 ε (θ + s - Real.pi)|
      ≤ |sKerd2 ε (θ - s) - sKerd2 ε (θ + s)| + |sKerd2 ε (θ + s - Real.pi)| := abs_sub _ _
    _ ≤ (|sKerd2 ε (θ - s)| + |sKerd2 ε (θ + s)|) + |sKerd2 ε (θ + s - Real.pi)| := by
        linarith [abs_sub (sKerd2 ε (θ - s)) (sKerd2 ε (θ + s)),
          abs_nonneg (sKerd2 ε (θ + s - Real.pi))]
    _ ≤ M + M + M := by linarith [abs_nonneg (sKerd2 ε (θ - s))]
    _ = 3 * M := by ring

/-- The pointwise domination of the signed kernel by the (nonnegative) three-image kernel. -/
theorem abs_km_le_KJ {ε : ℝ} (hε : 0 < ε) (θ s : ℝ) :
    |km ε θ s| ≤ Work.FTS.EllSol.EllPkgAux.KJ ε θ s := by
  have h1 : 0 ≤ sKer ε (θ - s) := Work.FTS.EllSol.PkgK5.K5c.sKer_nonneg hε _
  have h2 : 0 ≤ sKer ε (θ + s) := Work.FTS.EllSol.PkgK5.K5c.sKer_nonneg hε _
  have h3 : 0 ≤ sKer ε (θ + s - Real.pi) := Work.FTS.EllSol.PkgK5.K5c.sKer_nonneg hε _
  have h4 : |sKer ε (θ - s) - sKer ε (θ + s) - sKer ε (θ + s - Real.pi)|
      ≤ sKer ε (θ - s) + sKer ε (θ + s) + sKer ε (θ + s - Real.pi) := by
    rw [abs_le]
    constructor <;> linarith
  simpa only [km, Work.FTS.EllSol.EllPkgAux.KJ] using h4

end Work.FTS.EllSol.EllPkgAux.MollDom
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.mmDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open Work.FTS.EllSol.PkgK5.K5c

local notation "Iθ" => Work.Spaces.Iθ

/-- The `σ_η`-weighted slice functional of `X` in the logarithmic radial variable:
`MmV X t = ∫_{Iθ} (X (e^t) s)² σ_η(s) ds`. -/
def MmV (X : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in Iθ, (X (Real.exp t) s) ^ 2 * Work.FTS.EllipticEst.thEta s

/-- The angular convolution of `|X (e^t) ·|` with the three-image kernel `KJ ε θ ·`. -/
def MmPsi (ε : ℝ) (X : ℝ → ℝ → ℝ) (θ t : ℝ) : ℝ :=
  ∫ s in Iθ, Work.FTS.EllSol.EllPkgAux.KJ ε θ s * |X (Real.exp t) s|





/-- A.e. strong measurability of the angular convolution `MmPsi ε X θ` in the radial variable
`t` (for fixed `θ`), from the joint measurability of `(t,s) ↦ X (e^t) s`. -/
theorem MmPsi_aesm {X : ℝ → ℝ → ℝ}
    (hXmeas : AEMeasurable (fun p : ℝ × ℝ => X (Real.exp p.1) p.2)
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Iθ))) (ε θ : ℝ) :
    AEStronglyMeasurable (fun t : ℝ => MmPsi ε X θ t) volume := by
  have hsk : Continuous (fun s : ℝ => sKer ε s) :=
    Work.FTS.EllSol.K5cAux.continuous_sKer ε
  have h1 : AEMeasurable (fun p : ℝ × ℝ => sKer ε (θ - p.2))
      (volume.prod (volume.restrict Iθ)) :=
    (hsk.measurable.comp (measurable_const.sub measurable_snd)).aemeasurable
  have h2 : AEMeasurable (fun p : ℝ × ℝ => sKer ε (θ + p.2))
      (volume.prod (volume.restrict Iθ)) :=
    (hsk.measurable.comp (measurable_const.add measurable_snd)).aemeasurable
  have h3 : AEMeasurable (fun p : ℝ × ℝ => sKer ε (θ + p.2 - Real.pi))
      (volume.prod (volume.restrict Iθ)) :=
    (hsk.measurable.comp
      ((measurable_const.add measurable_snd).sub measurable_const)).aemeasurable
  have hKae : AEMeasurable (fun p : ℝ × ℝ => Work.FTS.EllSol.EllPkgAux.KJ ε θ p.2)
      (volume.prod (volume.restrict Iθ)) :=
    (h1.add h2).add h3
  have h4 : AEMeasurable (fun p : ℝ × ℝ =>
      Work.FTS.EllSol.EllPkgAux.KJ ε θ p.2 * |X (Real.exp p.1) p.2|)
      (volume.prod (volume.restrict Iθ)) := hKae.mul hXmeas.abs
  have h5 := h4.aestronglyMeasurable.integral_prod_right' (ν := volume.restrict Iθ)
  simpa only [MmPsi] using h5



end Work.FTS.EllSol.EllPkgAux.MollDom
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.swapFubini =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

theorem swapFubini {k : ℝ → ℝ} {v : ℝ → ℝ → ℝ} {ε θ σ : ℝ}
    (h : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => k (σ - p.1) * Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ p.2 * v p.1 p.2)
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    (∫ t : ℝ, k (σ - t) * (∫ s in Work.Spaces.Iθ, Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s * v t s))
      = ∫ s in Work.Spaces.Iθ, Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s * (∫ t : ℝ, k (σ - t) * v t s) := by
  -- Fubini/Tonelli for the product measure `volume × (volume ↾ Iθ)`: both sides are the
  -- iterated integral of the single product integrand, so both equal its product integral.
  set F : ℝ × ℝ → ℝ :=
    fun p => k (σ - p.1) * Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ p.2 * v p.1 p.2
    with hFdef
  -- left-hand side: the `t`-integral of the `Iθ`-integral
  have hlhs : (∫ t : ℝ, k (σ - t) * (∫ s in Work.Spaces.Iθ, Work.FTS.EllSol.EllPkgAux.Kern
        (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s * v t s))
      = ∫ p, F p ∂(MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.integral_prod F h]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only []
    rw [← MeasureTheory.integral_const_mul (k (σ - t))
      (fun s => Work.FTS.EllSol.EllPkgAux.Kern (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s * v t s)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [F]
    ring
  -- right-hand side: the `Iθ`-integral of the `t`-integral
  have hrhs : (∫ s in Work.Spaces.Iθ, Work.FTS.EllSol.EllPkgAux.Kern
        (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s * (∫ t : ℝ, k (σ - t) * v t s))
      = ∫ p, F p ∂(MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.integral_prod_symm F h]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only []
    rw [← MeasureTheory.integral_const_mul (Work.FTS.EllSol.EllPkgAux.Kern
      (Work.FTS.EllSol.PkgK5.K5c.sKer ε) θ s) (fun t => k (σ - t) * v t s)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [F]
    ring
  exact hlhs.trans hrhs.symm

end Work.FTS.EllSol.EllPkgAux.MollDom
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollKdAux =====
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
set_option linter.unusedVariables false



/-- Unfolded form of the two-dimensional mollifier. -/
theorem Kd_eq (δ ε : ℝ) : Kd δ ε = fun p : ℝ × ℝ =>
    (δ * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ *
        Real.smoothTransition (1 - (p.1 / δ) ^ 2)
      * ((ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ *
        Real.smoothTransition (1 - (p.2 / ε) ^ 2)) := by
  funext p
  simp only [Kd, Work.FTS.EllSol.PkgK5.K5c.sKer, Work.FTS.EllSol.PkgK5.K5c.sBump]

/-- The two-dimensional mollifier is `C^∞`. -/
theorem Kd_contDiff (δ ε : ℝ) (n : ℕ) : ContDiff ℝ n (Kd δ ε) := by
  rw [Kd_eq δ ε]
  fun_prop

/-- The two-dimensional mollifier is compactly supported (its support lies in
`[-δ,δ] × [-ε,ε]`). -/
theorem Kd_hasCompactSupport (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    HasCompactSupport (Kd δ ε) := by
  refine HasCompactSupport.intro (K := Set.Icc (-δ) δ ×ˢ Set.Icc (-ε) ε)
    (isCompact_Icc.prod isCompact_Icc) ?_
  rintro ⟨t, s⟩ hp
  simp only [Set.mem_prod, Set.mem_Icc, not_and_or, not_le] at hp
  rcases hp with (h | h) | (h | h)
  · have ht : δ ≤ |t| := by
      have h1 : δ ≤ -t := by linarith
      exact le_trans h1 (neg_le_abs t)
    show Work.FTS.EllSol.PkgK5.K5c.sKer δ t * Work.FTS.EllSol.PkgK5.K5c.sKer ε s = 0
    rw [Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ ht, zero_mul]
  · have ht : δ ≤ |t| := by
      have h1 : δ ≤ t := le_of_lt h
      exact le_trans h1 (le_abs_self t)
    show Work.FTS.EllSol.PkgK5.K5c.sKer δ t * Work.FTS.EllSol.PkgK5.K5c.sKer ε s = 0
    rw [Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ ht, zero_mul]
  · have hs : ε ≤ |s| := by
      have h1 : ε ≤ -s := by linarith
      exact le_trans h1 (neg_le_abs s)
    show Work.FTS.EllSol.PkgK5.K5c.sKer δ t * Work.FTS.EllSol.PkgK5.K5c.sKer ε s = 0
    rw [Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε hs, mul_zero]
  · have hs : ε ≤ |s| := by
      have h1 : ε ≤ s := le_of_lt h
      exact le_trans h1 (le_abs_self s)
    show Work.FTS.EllSol.PkgK5.K5c.sKer δ t * Work.FTS.EllSol.PkgK5.K5c.sKer ε s = 0
    rw [Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε hs, mul_zero]

end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollSliceDom =====
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
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Geometric and integrability facts about the interval spanned by `π/4` and `τ` -/







/-! ## Note

The full slice-domination statement (`|G w τ| ≤ MG G w`) is *proved* in
`Submission/Work/FTS/EllSol/EllPkgAux/MollSmooth/sliceDom.lean`
(`Work.FTS.EllSol.EllPkgAux.MollSmooth.sliceDom`, which `mollAdm` imports).  The lemmas above
are the ingredients of a second, independent proof of the same statement (via the weighted
Cauchy–Schwarz `cs_minmax` and the interval-length bound `thEta_inv_integral_minmax_le`); they
are kept because they are reusable, but they are not (yet) assembled into that second proof.
-/

end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollSmooth.Hxy_quad_locallyIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllSol.PkgK5.K5c

namespace Work.FTS.EllSol.EllPkgAux.MollSmooth

set_option linter.unusedVariables false

theorem Hxy_quad_locallyIntegrable (G : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen G)
    (hdom : ∀ w : ℝ, 0 < w → ∀ τ : ℝ, τ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      |G w τ| ≤ Work.FTS.EllSol.EllPkgAux.MG G w)
    (hint : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Work.FTS.EllSol.EllPkgAux.MG G) (Set.Ioo a b)) :
    MeasureTheory.LocallyIntegrable
      (Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G)) MeasureTheory.volume := by
  -- `MG G` is nonnegative.
  have hMGnn : ∀ w : ℝ, 0 ≤ Work.FTS.EllSol.EllPkgAux.MG G w := by
    intro w
    have h1 : (0 : ℝ) ≤ |G w (Real.pi / 4)| := abs_nonneg _
    have h2 : (0 : ℝ) ≤ |Work.Spaces.pth G w (Real.pi / 4)| := abs_nonneg _
    have h3 : (0 : ℝ) ≤ Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2sl G w) := Real.sqrt_nonneg _
    simp only [Work.FTS.EllSol.EllPkgAux.MG]
    linarith
  -- The quadrant-killed datum is dominated by `MG G` on the positive half line.
  have hGq : ∀ z : ℝ, 0 < z → ∀ τ : ℝ, |Work.FTS.EllSol.EllPkgAux.Gquad G z τ|
      ≤ Work.FTS.EllSol.EllPkgAux.MG G z := by
    intro z hz τ
    by_cases hτ : τ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
    · rw [Work.FTS.EllSol.EllPkgAux.Gquad, ite_eq_left hτ]
      exact hdom z hz τ hτ
    · rw [Work.FTS.EllSol.EllPkgAux.Gquad, ite_eq_right hτ, abs_zero]
      exact hMGnn z
  -- The doubly-odd extension is dominated by `MG G` as well.
  have hQb : ∀ z : ℝ, 0 < z → ∀ s : ℝ,
      |Qext (Work.FTS.EllSol.EllPkgAux.Gquad G) z s| ≤ Work.FTS.EllSol.EllPkgAux.MG G z := by
    intro z hz s
    by_cases h1 : 0 ≤ s ∧ s ≤ Real.pi / 2
    · rw [Qext, ite_eq_left h1]
      exact hGq z hz s
    · rw [Qext, ite_eq_right h1]
      by_cases h2 : s < 0
      · rw [ite_eq_left h2, abs_neg]
        exact hGq z hz (-s)
      · rw [ite_eq_right h2, abs_neg]
        exact hGq z hz (Real.pi - s)
  -- `t ↦ MG G (exp t)` is integrable on every bounded interval `(a,b)`, by substitution.
  have hexp : ∀ a b : ℝ, a < b →
      IntegrableOn (fun t : ℝ => Work.FTS.EllSol.EllPkgAux.MG G (Real.exp t)) (Set.Ioo a b) := by
    intro a b hab
    have hiff := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
      (f := Real.exp) (f' := fun x => Real.exp x) (g := Work.FTS.EllSol.EllPkgAux.MG G)
      (a := a) (b := b)
      (by fun_prop) (fun x _ => Real.hasDerivAt_exp x) (fun x _ => (Real.exp_pos x).le)
    have hR : IntervalIntegrable (Work.FTS.EllSol.EllPkgAux.MG G) volume (Real.exp a)
        (Real.exp b) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (le_of_lt (Real.exp_lt_exp.mpr hab))).mpr
        (hint (Real.exp a) (Real.exp b) (Real.exp_pos a) (Real.exp_lt_exp.mpr hab))
    have hL : IntegrableOn
        (fun t : ℝ => Work.FTS.EllSol.EllPkgAux.MG G (Real.exp t) * Real.exp t)
        (Set.Ioo a b) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (le_of_lt hab)).mp (hiff.mpr hR)
    rw [IntegrableOn] at hL ⊢
    have h2 : Integrable
        (fun t : ℝ => (Real.exp a)⁻¹ * (Work.FTS.EllSol.EllPkgAux.MG G (Real.exp t)
          * Real.exp t)) (volume.restrict (Set.Ioo a b)) := hL.const_mul _
    refine h2.mono' ?_ ?_
    · have hcont : Continuous (fun t : ℝ => Real.exp a * (Real.exp t)⁻¹) :=
        continuous_const.mul (Real.continuous_exp.inv₀ (fun t => Real.exp_ne_zero t))
      refine (hcont.aestronglyMeasurable.mul h2.aestronglyMeasurable).congr ?_
      filter_upwards with t
      have ha : Real.exp a ≠ 0 := Real.exp_ne_zero a
      have ht : Real.exp t ≠ 0 := Real.exp_ne_zero t
      calc Real.exp a * (Real.exp t)⁻¹
            * ((Real.exp a)⁻¹ * (Work.FTS.EllSol.EllPkgAux.MG G (Real.exp t) * Real.exp t))
          = (Real.exp t)⁻¹ * Real.exp t * (Real.exp a * (Real.exp a)⁻¹)
              * Work.FTS.EllSol.EllPkgAux.MG G (Real.exp t) := by ring
        _ = Work.FTS.EllSol.EllPkgAux.MG G (Real.exp t) := by
              rw [inv_mul_cancel₀ ht, mul_inv_cancel₀ ha]; ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have hpa : 0 < Real.exp a := Real.exp_pos a
      have hlt : Real.exp a < Real.exp t := Real.exp_lt_exp.mpr ht.1
      have hge : 1 ≤ Real.exp t / Real.exp a := (one_le_div hpa).mpr hlt.le
      rw [Real.norm_of_nonneg (hMGnn _)]
      calc Work.FTS.EllSol.EllPkgAux.MG G (Real.exp t)
          = Work.FTS.EllSol.EllPkgAux.MG G (Real.exp t) * 1 := by ring
        _ ≤ Work.FTS.EllSol.EllPkgAux.MG G (Real.exp t) * (Real.exp t / Real.exp a) :=
              mul_le_mul_of_nonneg_left hge (hMGnn _)
        _ = (Real.exp a)⁻¹ * (Work.FTS.EllSol.EllPkgAux.MG G (Real.exp t) * Real.exp t) := by
              ring
  -- Local integrability of the dominating function on the plane.
  have hLI : LocallyIntegrable
      (fun p : ℝ × ℝ => Work.FTS.EllSol.EllPkgAux.MG G (Real.exp p.1)) volume := by
    intro x
    refine ⟨Set.Ioo (x.1 - 1) (x.1 + 1) ×ˢ Set.Ioo (x.2 - 1) (x.2 + 1), ?_, ?_⟩
    · exact IsOpen.mem_nhds (isOpen_Ioo.prod isOpen_Ioo)
        (mem_prod.mpr ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩)
    · have hA : Integrable
          (fun t : ℝ => Work.FTS.EllSol.EllPkgAux.MG G (Real.exp t))
          (volume.restrict (Set.Ioo (x.1 - 1) (x.1 + 1))) :=
        hexp (x.1 - 1) (x.1 + 1) (by linarith)
      have h2 := hA.comp_fst (volume.restrict (Set.Ioo (x.2 - 1) (x.2 + 1)))
      rw [Measure.prod_restrict] at h2
      rw [← Measure.volume_eq_prod ℝ ℝ] at h2
      exact h2
  -- The pointwise decomposition of the integrand into three reflected pieces.
  have hfun : ∀ p : ℝ × ℝ, Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G) p =
      Set.indicator {q : ℝ × ℝ | q.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)}
          (fun q : ℝ × ℝ => G (Real.exp q.1) q.2) p
        + Set.indicator {q : ℝ × ℝ | q.2 ∈ Set.Ioo (-(Real.pi / 2)) 0}
          (fun q : ℝ × ℝ => -(G (Real.exp q.1) (-q.2))) p
        + Set.indicator {q : ℝ × ℝ | q.2 ∈ Set.Ioo (Real.pi / 2) Real.pi}
          (fun q : ℝ × ℝ => -(G (Real.exp q.1) (Real.pi - q.2))) p := by
    intro p
    by_cases hA : p ∈ {q : ℝ × ℝ | q.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)}
    · have hAc : p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hA
      have hAs : 0 < p.2 ∧ p.2 < Real.pi / 2 := Set.mem_Ioo.mp hAc
      have h1 : 0 ≤ p.2 ∧ p.2 ≤ Real.pi / 2 := ⟨hAs.1.le, hAs.2.le⟩
      have hBn : p ∉ {q : ℝ × ℝ | q.2 ∈ Set.Ioo (-(Real.pi / 2)) 0} := fun h => by
        have hb : -(Real.pi / 2) < p.2 ∧ p.2 < 0 := Set.mem_Ioo.mp h
        linarith [hAs.1, hb.2]
      have hCn : p ∉ {q : ℝ × ℝ | q.2 ∈ Set.Ioo (Real.pi / 2) Real.pi} := fun h => by
        have hc : Real.pi / 2 < p.2 ∧ p.2 < Real.pi := Set.mem_Ioo.mp h
        linarith [hAs.2, hc.1]
      rw [Hxy, Qext, ite_eq_left h1, Work.FTS.EllSol.EllPkgAux.Gquad, ite_eq_left hAc,
        Set.indicator_of_mem hA, Set.indicator_of_notMem hBn, Set.indicator_of_notMem hCn]
      ring
    · by_cases hB : p ∈ {q : ℝ × ℝ | q.2 ∈ Set.Ioo (-(Real.pi / 2)) 0}
      · have hBs : -(Real.pi / 2) < p.2 ∧ p.2 < 0 := Set.mem_Ioo.mp hB
        have h1 : ¬ (0 ≤ p.2 ∧ p.2 ≤ Real.pi / 2) := fun h => by linarith [h.1, hBs.2]
        have hneg : -p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
          rw [Set.mem_Ioo]; exact ⟨by linarith [hBs.2], by linarith [hBs.1]⟩
        have hCn : p ∉ {q : ℝ × ℝ | q.2 ∈ Set.Ioo (Real.pi / 2) Real.pi} := fun h => by
          have hc : Real.pi / 2 < p.2 ∧ p.2 < Real.pi := Set.mem_Ioo.mp h
          linarith [hBs.2, hc.1]
        rw [Hxy, Qext, ite_eq_right h1, ite_eq_left hBs.2, Work.FTS.EllSol.EllPkgAux.Gquad, ite_eq_left hneg,
          Set.indicator_of_notMem hA, Set.indicator_of_mem hB, Set.indicator_of_notMem hCn]
        ring
      · by_cases hC : p ∈ {q : ℝ × ℝ | q.2 ∈ Set.Ioo (Real.pi / 2) Real.pi}
        · have hCs : Real.pi / 2 < p.2 ∧ p.2 < Real.pi := Set.mem_Ioo.mp hC
          have h1 : ¬ (0 ≤ p.2 ∧ p.2 ≤ Real.pi / 2) := fun h => by linarith [h.2, hCs.1]
          have hlt : ¬ p.2 < 0 := by linarith [hCs.1, Real.pi_pos]
          have hneg : Real.pi - p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
            rw [Set.mem_Ioo]; exact ⟨by linarith [hCs.2], by linarith [hCs.1]⟩
          rw [Hxy, Qext, ite_eq_right h1, ite_eq_right hlt, Work.FTS.EllSol.EllPkgAux.Gquad, ite_eq_left hneg,
            Set.indicator_of_notMem hA, Set.indicator_of_notMem hB, Set.indicator_of_mem hC]
          ring
        · have hAc : p.2 ∉ Set.Ioo (0 : ℝ) (Real.pi / 2) := hA
          have h0 : Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G) p = 0 := by
            rw [Hxy, Qext]
            by_cases h1 : 0 ≤ p.2 ∧ p.2 ≤ Real.pi / 2
            · rw [ite_eq_left h1, Work.FTS.EllSol.EllPkgAux.Gquad, ite_eq_right hAc]
            · rw [ite_eq_right h1]
              by_cases h2 : p.2 < 0
              · rw [ite_eq_left h2, Work.FTS.EllSol.EllPkgAux.Gquad, ite_eq_right (fun hm => by
                  have hmm : 0 < -p.2 ∧ -p.2 < Real.pi / 2 := Set.mem_Ioo.mp hm
                  exact hB ⟨by linarith [hmm.2], h2⟩), neg_zero]
              · rw [ite_eq_right h2, Work.FTS.EllSol.EllPkgAux.Gquad, ite_eq_right (fun hm => by
                  have hmm : 0 < Real.pi - p.2 ∧ Real.pi - p.2 < Real.pi / 2 :=
                    Set.mem_Ioo.mp hm
                  exact hC ⟨by linarith [hmm.1], by linarith [hmm.2]⟩), neg_zero]
          rw [h0, Set.indicator_of_notMem hA, Set.indicator_of_notMem hB,
            Set.indicator_of_notMem hC]
          ring
  -- Measurability of the integrand.
  have hmeasH : AEStronglyMeasurable
      (Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G)) (volume : Measure (ℝ × ℝ)) := by
    have hAmeas : MeasurableSet {q : ℝ × ℝ | q.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)} :=
      (IsOpen.preimage continuous_snd isOpen_Ioo).measurableSet
    have hBmeas : MeasurableSet {q : ℝ × ℝ | q.2 ∈ Set.Ioo (-(Real.pi / 2)) 0} :=
      (IsOpen.preimage continuous_snd isOpen_Ioo).measurableSet
    have hCmeas : MeasurableSet {q : ℝ × ℝ | q.2 ∈ Set.Ioo (Real.pi / 2) Real.pi} :=
      (IsOpen.preimage continuous_snd isOpen_Ioo).measurableSet
    have hcontA : ContinuousOn (fun q : ℝ × ℝ => G (Real.exp q.1) q.2)
        {q : ℝ × ℝ | q.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)} := by
      have hmp : MapsTo (fun q : ℝ × ℝ => (Real.exp q.1, q.2))
          {q : ℝ × ℝ | q.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)} Work.FTS.EllipticEst.Q0 := by
        intro q hq
        exact mem_prod.mpr ⟨Real.exp_pos q.1, hq⟩
      have hc := hS.continuousOn.comp (by fun_prop) hmp
      have hFeq : (fun q : ℝ × ℝ => G (Real.exp q.1) q.2)
          = (Function.uncurry G) ∘ (fun q : ℝ × ℝ => (Real.exp q.1, q.2)) := by
        funext q; rfl
      rw [hFeq]
      exact hc
    have hcontB : ContinuousOn (fun q : ℝ × ℝ => -(G (Real.exp q.1) (-q.2)))
        {q : ℝ × ℝ | q.2 ∈ Set.Ioo (-(Real.pi / 2)) 0} := by
      have hmp : MapsTo (fun q : ℝ × ℝ => (Real.exp q.1, -q.2))
          {q : ℝ × ℝ | q.2 ∈ Set.Ioo (-(Real.pi / 2)) 0} Work.FTS.EllipticEst.Q0 := by
        intro q hq
        have hq2 : q.2 ∈ Set.Ioo (-(Real.pi / 2)) 0 := hq
        rw [Set.mem_Ioo] at hq2
        have hq' : -q.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
          rw [Set.mem_Ioo]; exact ⟨by linarith [hq2.2], by linarith [hq2.1]⟩
        exact mem_prod.mpr ⟨Real.exp_pos q.1, hq'⟩
      have hc := hS.continuousOn.comp (by fun_prop) hmp
      have hFeq : (fun q : ℝ × ℝ => -(G (Real.exp q.1) (-q.2)))
          = -((Function.uncurry G) ∘ (fun q : ℝ × ℝ => (Real.exp q.1, -q.2))) := by
        funext q; rfl
      rw [hFeq]
      exact hc.neg
    have hcontC : ContinuousOn (fun q : ℝ × ℝ => -(G (Real.exp q.1) (Real.pi - q.2)))
        {q : ℝ × ℝ | q.2 ∈ Set.Ioo (Real.pi / 2) Real.pi} := by
      have hmp : MapsTo (fun q : ℝ × ℝ => (Real.exp q.1, Real.pi - q.2))
          {q : ℝ × ℝ | q.2 ∈ Set.Ioo (Real.pi / 2) Real.pi} Work.FTS.EllipticEst.Q0 := by
        intro q hq
        have hq2 : q.2 ∈ Set.Ioo (Real.pi / 2) Real.pi := hq
        rw [Set.mem_Ioo] at hq2
        have hq' : Real.pi - q.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
          rw [Set.mem_Ioo]; exact ⟨by linarith [hq2.2], by linarith [hq2.1]⟩
        exact mem_prod.mpr ⟨Real.exp_pos q.1, hq'⟩
      have hc := hS.continuousOn.comp (by fun_prop) hmp
      have hFeq : (fun q : ℝ × ℝ => -(G (Real.exp q.1) (Real.pi - q.2)))
          = -((Function.uncurry G) ∘ (fun q : ℝ × ℝ => (Real.exp q.1, Real.pi - q.2))) := by
        funext q; rfl
      rw [hFeq]
      exact hc.neg
    have hm1 : AEStronglyMeasurable
        ({q : ℝ × ℝ | q.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)}.indicator
          (fun q : ℝ × ℝ => G (Real.exp q.1) q.2)) volume :=
      (aestronglyMeasurable_indicator_iff hAmeas).mpr (hcontA.aestronglyMeasurable hAmeas)
    have hm2 : AEStronglyMeasurable
        ({q : ℝ × ℝ | q.2 ∈ Set.Ioo (-(Real.pi / 2)) 0}.indicator
          (fun q : ℝ × ℝ => -(G (Real.exp q.1) (-q.2)))) volume :=
      (aestronglyMeasurable_indicator_iff hBmeas).mpr (hcontB.aestronglyMeasurable hBmeas)
    have hm3 : AEStronglyMeasurable
        ({q : ℝ × ℝ | q.2 ∈ Set.Ioo (Real.pi / 2) Real.pi}.indicator
          (fun q : ℝ × ℝ => -(G (Real.exp q.1) (Real.pi - q.2)))) volume :=
      (aestronglyMeasurable_indicator_iff hCmeas).mpr (hcontC.aestronglyMeasurable hCmeas)
    refine ((hm1.add hm2).add hm3).congr ?_
    filter_upwards with p
    exact (hfun p).symm
  -- Domination of the integrand by the locally integrable function, and conclusion.
  have hdomH : ∀ p : ℝ × ℝ,
      |Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G) p|
        ≤ Work.FTS.EllSol.EllPkgAux.MG G (Real.exp p.1) := by
    intro p
    have hp := hQb (Real.exp p.1) (Real.exp_pos p.1) p.2
    simpa only [Hxy] using hp
  exact hLI.mono hmeasH (Eventually.of_forall (fun p => by
    simp only [Real.norm_eq_abs, abs_of_nonneg (hMGnn (Real.exp p.1))]
    exact hdomH p))

end Work.FTS.EllSol.EllPkgAux.MollSmooth
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollSmooth.MG_integrableOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollSmooth

open MeasureTheory Set Filter

theorem MG_integrableOn (G : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen G)
    (hFI : Work.FTS.EllSol.EllPkgAux.FourInts G) :
    ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Work.FTS.EllSol.EllPkgAux.MG G) (Set.Ioo a b) := by
  intro a b ha hab
  have hθ0 : (Real.pi / 4) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le ha hx.1
  -- the two interior slice values are continuous on `(0,∞)`, hence integrable on `(a,b)`
  have h_int1 : MeasureTheory.IntegrableOn (fun w => |G w (Real.pi / 4)|) (Set.Ioo a b) :=
    (((hS.curry_z hθ0).continuousOn.abs).mono hsub).integrableOn_compact isCompact_Icc
      |>.mono_set Set.Ioo_subset_Icc_self
  have h_int2 : MeasureTheory.IntegrableOn (fun w => |Work.Spaces.pth G w (Real.pi / 4)|)
      (Set.Ioo a b) :=
    (((hS.pth.curry_z hθ0).continuousOn.abs).mono hsub).integrableOn_compact isCompact_Icc
      |>.mono_set Set.Ioo_subset_Icc_self
  -- the square root of the slice functional
  have h_int3 : MeasureTheory.IntegrableOn
      (fun w => Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2sl G w)) (Set.Ioo a b) := by
    have hT : MeasureTheory.IntegrableOn (Work.EllipticEst.Core.ttIntS G) (Set.Ioo a b) :=
      hFI.2.2.1.mono_set (fun x hx => le_of_lt (lt_trans ha hx.1))
    have hwpos : ∀ z ∈ Set.Ioo a b, 0 < Work.Spaces.w z := by
      intro z hz; rw [Work.Spaces.w]; have : (0 : ℝ) < z := lt_trans ha hz.1; positivity
    -- the dominating function `(|ttIntS G ·| + 1)/2 · (b^2/(1+b)^2)`
    have hgint : MeasureTheory.IntegrableOn
        (fun z => (|Work.EllipticEst.Core.ttIntS G z| + 1) / 2 * (b ^ 2 / (1 + b) ^ 2))
        (Set.Ioo a b) := by
      have hc : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo a b) :=
        (continuousOn_const.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
      exact (((MeasureTheory.Integrable.abs hT).add hc).div_const 2).mul_const (b ^ 2 / (1 + b) ^ 2)
    -- `E2sl G = ttIntS G / w²` on `(a,b)`, so it is a.e. strongly measurable
    have hw2cont : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioo a b) := by
      have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2) = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := rfl
      rw [hfun]
      refine ContinuousOn.pow ?_ 2
      exact ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2) (continuousOn_id.pow 2)
        (fun z hz => pow_ne_zero 2 (ne_of_gt (lt_trans ha hz.1)))
    have hwit : ∀ z ∈ Set.Ioo a b,
        Work.EllipticEst.Core.ttIntS G z / (Work.Spaces.w z) ^ 2
          = Work.FTS.EllSol.EllPkgAux.E2sl G z := by
      intro z hz
      have hwz : Work.Spaces.w z ≠ 0 := ne_of_gt (hwpos z hz)
      rw [show Work.EllipticEst.Core.ttIntS G z
            = (Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.EllPkgAux.E2sl G z from rfl]
      exact mul_div_cancel_left₀ (Work.FTS.EllSol.EllPkgAux.E2sl G z) (pow_ne_zero 2 hwz)
    have hE2meas : AEStronglyMeasurable (fun w => Work.FTS.EllSol.EllPkgAux.E2sl G w)
        (volume.restrict (Set.Ioo a b)) :=
      (hT.aemeasurable.div (hw2cont.aemeasurable measurableSet_Ioo)).aestronglyMeasurable |>.congr
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo hwit)
    have hmeas : AEStronglyMeasurable
        (fun w => Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2sl G w))
        (volume.restrict (Set.Ioo a b)) :=
      (hE2meas.aemeasurable.sqrt).aestronglyMeasurable
    -- the pointwise domination
    have hdom : ∀ᵐ z ∂(volume.restrict (Set.Ioo a b)),
        ‖Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2sl G z)‖
          ≤ (|Work.EllipticEst.Core.ttIntS G z| + 1) / 2 * (b ^ 2 / (1 + b) ^ 2) := by
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun z hz => ?_)
      have hE2nn : 0 ≤ Work.FTS.EllSol.EllPkgAux.E2sl G z := by
        rw [Work.FTS.EllSol.EllPkgAux.E2sl]
        refine MeasureTheory.integral_nonneg_of_ae ?_
        refine MeasureTheory.ae_restrict_of_forall_mem (show MeasurableSet Work.Spaces.Iθ from by
          rw [Work.Spaces.Iθ]; exact measurableSet_Icc) ?_
        intro θ hθ
        exact mul_nonneg (sq_nonneg _)
          (Work.FTS.EllipticEst.thEta_nonneg (by rw [Work.Spaces.Iθ]; exact hθ))
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      have hz1 : 0 < z := lt_trans ha hz.1
      have hzb : z < b := hz.2
      have hwzp : 0 < Work.Spaces.w z := hwpos z hz
      have hnn : 0 ≤ (Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.EllPkgAux.E2sl G z :=
        mul_nonneg (sq_nonneg _) hE2nn
      -- `√(E2sl) = √|ttIntS| / w`
      have hsq : Real.sqrt (|Work.EllipticEst.Core.ttIntS G z|)
          = Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2sl G z) * Work.Spaces.w z := by
        rw [show Work.EllipticEst.Core.ttIntS G z
              = (Work.Spaces.w z) ^ 2 * Work.FTS.EllSol.EllPkgAux.E2sl G z from rfl,
          abs_of_nonneg hnn, Real.sqrt_mul (sq_nonneg (Work.Spaces.w z)), Real.sqrt_sq_eq_abs,
          abs_of_nonneg (le_of_lt hwzp)]
        ring
      have h4 : Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2sl G z)
          = Real.sqrt (|Work.EllipticEst.Core.ttIntS G z|) / Work.Spaces.w z := by
        rw [eq_div_iff (ne_of_gt hwzp)]
        simpa [mul_comm] using hsq.symm
      -- `√|t| ≤ (|t| + 1)/2`
      have hup : Real.sqrt (|Work.EllipticEst.Core.ttIntS G z|)
          ≤ (|Work.EllipticEst.Core.ttIntS G z| + 1) / 2 := by
        rw [Real.sqrt_le_iff]
        refine ⟨by positivity, ?_⟩
        nlinarith [abs_nonneg (Work.EllipticEst.Core.ttIntS G z),
          sq_nonneg (|Work.EllipticEst.Core.ttIntS G z| - 1)]
      -- `1/w z ≤ b²/(1+b)²` on `(a,b)`
      have hinvw : 1 / Work.Spaces.w z ≤ b ^ 2 / (1 + b) ^ 2 := by
        have hb1 : 0 < b := lt_trans hz1 hzb
        have hw : 1 / Work.Spaces.w z = z ^ 2 / (1 + z) ^ 2 := by
          rw [Work.Spaces.w]; field_simp
        rw [hw]
        have hsub2 : 0 ≤ b ^ 2 / (1 + b) ^ 2 - z ^ 2 / (1 + z) ^ 2 := by
          rw [show b ^ 2 / (1 + b) ^ 2 - z ^ 2 / (1 + z) ^ 2
                = (b - z) * (b + 2 * b * z + z) / ((1 + b) ^ 2 * (1 + z) ^ 2) from by
            field_simp; ring]
          exact div_nonneg (mul_nonneg (by linarith) (by nlinarith [hb1, hz1])) (by positivity)
        linarith
      rw [h4]
      calc Real.sqrt (|Work.EllipticEst.Core.ttIntS G z|) / Work.Spaces.w z
          ≤ ((|Work.EllipticEst.Core.ttIntS G z| + 1) / 2) / Work.Spaces.w z :=
            div_le_div_of_nonneg_right hup (le_of_lt hwzp)
        _ = (|Work.EllipticEst.Core.ttIntS G z| + 1) / 2 * (1 / Work.Spaces.w z) := by ring
        _ ≤ (|Work.EllipticEst.Core.ttIntS G z| + 1) / 2 * (b ^ 2 / (1 + b) ^ 2) :=
            mul_le_mul_of_nonneg_left hinvw (by positivity)
    exact hgint.mono' hmeas hdom
  show MeasureTheory.IntegrableOn (fun w => |G w (Real.pi / 4)|
      + |Work.Spaces.pth G w (Real.pi / 4)|
      + Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2sl G w)) (Set.Ioo a b)
  exact (h_int1.add h_int2).add h_int3

end Work.FTS.EllSol.EllPkgAux.MollSmooth
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollSmooth.sliceDom =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollSmooth

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **The slice is dominated by the two data values plus the weighted second-derivative
functional.**  For `G` smooth on the open quadrant and honestly slice-integrable
(`SliceHonestOpen`), and every `w > 0`, the whole angular slice `τ ↦ G w τ` on `(0, π/2)` is
bounded by `MG G w`.

The proof is the second-order Taylor formula at the interior base point `θ = π/4`,
`f τ = f (π/4) + (τ - π/4) f' (π/4) + ∫_{π/4}^{τ} (τ - t) f'' t dt`,
together with the interval Cauchy–Schwarz bound `∫ |f''| ≤ √(length) √(∫ f''²)`; the
remaining second-derivative mass is upgraded to the weighted functional `E2sl G w` because
`σ_η = sin(2θ)^{-η} ≥ 1` on `(0, π/2)`.  The numerical constants are harmless:
`|τ - π/4| ≤ π/4 < 1` and `(π/4)·√(π/4) ≤ 1`. -/
theorem sliceDom (G : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen G)
    (hH : Work.EllipticEst.Core.i0Aux.SliceHonestOpen G) :
    ∀ w : ℝ, 0 < w → ∀ τ : ℝ, τ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      |G w τ| ≤ Work.FTS.EllSol.EllPkgAux.MG G w := by
  intro w hw τ hτ
  have hτ0 : 0 < τ := hτ.1
  have hτ1 : τ < Real.pi / 2 := hτ.2
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  -- the slice at radius `w` is `C²` on the open angular interval
  have hsmo : (2 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
    simp [Work.Stability.smoothOrder]
  have hf2 : ContDiffOn ℝ 2 (fun θ : ℝ => G w θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hS.curry_θ hw).of_le hsmo
  have ha0 : (0 : ℝ) < Real.pi / 4 := by linarith
  have ha1 : Real.pi / 4 < Real.pi / 2 := by linarith
  have ha_mem : (Real.pi / 4 : ℝ) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨ha0, ha1⟩
  -- integrability of the weighted square of the second derivative
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
  -- the Taylor formula at the base point `π/4`
  have hT := slice_taylor_two hf2 ha_mem hτ
  -- the bound on the integral part
  have hTail : |∫ t in (Real.pi / 4)..τ,
        (τ - t) * deriv (deriv (fun θ : ℝ => G w θ)) t|
      ≤ (Real.pi / 4) * Real.sqrt (Real.pi / 4) *
        Real.sqrt (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
    rcases le_total (Real.pi / 4) τ with hle | hle
    · -- `π/4 ≤ τ`: apply the estimate on `[π/4, τ]`
      have hcont : ContinuousOn (fun t : ℝ => deriv (deriv (fun θ : ℝ => G w θ)) t)
          (Set.uIcc (Real.pi / 4) τ) := slice_dd_cont hf2 ha_mem hτ
      have hc : ∀ t ∈ Set.Icc (Real.pi / 4) τ, |τ - t| ≤ Real.pi / 4 := by
        intro t ht
        rw [abs_of_nonneg (by linarith [ht.2])]
        linarith [ht.1]
      exact slice_int_bound hle ha0 hτ1 (by linarith) hcont hc hHint
    · -- `τ ≤ π/4`: flip the interval
      have hcont : ContinuousOn (fun t : ℝ => deriv (deriv (fun θ : ℝ => G w θ)) t)
          (Set.uIcc τ (Real.pi / 4)) := slice_dd_cont hf2 hτ ha_mem
      have hc : ∀ t ∈ Set.Icc τ (Real.pi / 4), |τ - t| ≤ Real.pi / 4 := by
        intro t ht
        rw [abs_of_nonpos (by linarith [ht.1])]
        linarith [ht.2]
      have h := slice_int_bound hle hτ0 ha1 (by linarith) hcont hc hHint
      rw [intervalIntegral.integral_symm, abs_neg]
      exact h
  -- the final assembly
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

end Work.FTS.EllSol.EllPkgAux.MollSmooth
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollSmooth.zmoll_Gquad_eq_conv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollSmooth

set_option linter.unusedVariables false

/-- `sKer δ` is continuous. -/
private lemma sKer_continuous_moll (δ : ℝ) :
    Continuous (Work.FTS.EllSol.PkgK5.K5c.sKer δ) := by
  have h : Work.FTS.EllSol.PkgK5.K5c.sKer δ = fun t : ℝ =>
      (δ * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹ *
        Work.FTS.EllSol.PkgK5.K5c.sBump (t / δ) := by
    funext t
    rw [Work.FTS.EllSol.PkgK5.K5c.sKer]
  rw [h]
  exact continuous_const.mul
    (Work.FTS.EllSol.PkgK5.K5c.sBump_continuous.comp (continuous_id.div_const δ))

/-- `Kd δ ε` is continuous. -/
private lemma Kd_continuous_moll (δ ε : ℝ) :
    Continuous (Work.FTS.EllSol.EllPkgAux.Kd δ ε) := by
  change Continuous (fun p : ℝ × ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer δ p.1
    * Work.FTS.EllSol.PkgK5.K5c.sKer ε p.2)
  exact ((sKer_continuous_moll δ).comp continuous_fst).mul
    ((sKer_continuous_moll ε).comp continuous_snd)

/-- The `(t,s) ↦ Kd δ ε ((log z, θ) - (t,s))` translate of the two-dimensional kernel is
continuous. -/
private lemma Kd_shift_continuous_moll (δ ε z θ : ℝ) :
    Continuous (fun p : ℝ × ℝ => Work.FTS.EllSol.EllPkgAux.Kd δ ε ((Real.log z, θ) - p)) :=
  (Kd_continuous_moll δ ε).comp (continuous_const.sub continuous_id)

/-- It also has compact support: its support is contained in the box
`[log z - δ, log z + δ] × [θ - ε, θ + ε]`. -/
private lemma Kd_shift_hasCompactSupport_moll (δ ε z θ : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    HasCompactSupport (fun p : ℝ × ℝ => Work.FTS.EllSol.EllPkgAux.Kd δ ε
      ((Real.log z, θ) - p)) := by
  refine HasCompactSupport.intro
    (K := Set.Icc (Real.log z - δ) (Real.log z + δ) ×ˢ Set.Icc (θ - ε) (θ + ε))
    (isCompact_Icc.prod isCompact_Icc) ?_
  intro p hp
  by_contra h0
  apply hp
  have hne : Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - p.1) *
      Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - p.2) ≠ 0 := by
    intro h
    exact h0 (by simpa only [Work.FTS.EllSol.EllPkgAux.Kd, Prod.fst_sub, Prod.snd_sub] using h)
  have h1 : |Real.log z - p.1| < δ := by
    by_contra hle
    exact (mul_ne_zero_iff.mp hne).1
      (Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hδ (not_lt.mp hle))
  have h2 : |θ - p.2| < ε := by
    by_contra hle
    exact (mul_ne_zero_iff.mp hne).2
      (Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε (not_lt.mp hle))
  rw [abs_lt] at h1 h2
  rw [Set.mem_prod]
  exact ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, ⟨by linarith [h2.1], by linarith [h2.2]⟩⟩

theorem zmoll_Gquad_eq_conv (G : ℝ → ℝ → ℝ)
    (hloc : MeasureTheory.LocallyIntegrable
      (Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G)) MeasureTheory.volume)
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (z θ : ℝ) (hz : 0 < z) :
    Work.FTS.EllSol.PkgK5.K5c.zmoll (Work.FTS.EllSol.EllPkgAux.Gquad G) δ ε z θ
      = MeasureTheory.convolution (Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G))
          (Work.FTS.EllSol.EllPkgAux.Kd δ ε) (ContinuousLinearMap.mul ℝ ℝ)
          MeasureTheory.volume (Real.log z, θ) := by
  have hInt : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G) p
        * Work.FTS.EllSol.EllPkgAux.Kd δ ε ((Real.log z, θ) - p)) MeasureTheory.volume := by
    refine (hloc.integrable_smul_left_of_hasCompactSupport
      (g := fun p : ℝ × ℝ => Work.FTS.EllSol.EllPkgAux.Kd δ ε ((Real.log z, θ) - p))
      (Kd_shift_continuous_moll δ ε z θ)
      (Kd_shift_hasCompactSupport_moll δ ε z θ hδ hε)).congr ?_
    filter_upwards with p
    simp only [smul_eq_mul]
    ring
  have hvol : (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
      = MeasureTheory.volume.prod MeasureTheory.volume := rfl
  have hL : Work.FTS.EllSol.PkgK5.K5c.zmoll (Work.FTS.EllSol.EllPkgAux.Gquad G) δ ε z θ
      = ∫ t : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t)
          * (∫ s : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - s)
              * Work.FTS.EllSol.PkgK5.K5c.Qext (Work.FTS.EllSol.EllPkgAux.Gquad G)
                  (Real.exp t) s) := rfl
  rw [hL, MeasureTheory.convolution_mul, hvol,
    MeasureTheory.integral_prod (fun p : ℝ × ℝ =>
      Work.FTS.EllSol.EllPkgAux.Hxy (Work.FTS.EllSol.EllPkgAux.Gquad G) p
        * Work.FTS.EllSol.EllPkgAux.Kd δ ε ((Real.log z, θ) - p)) hInt]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  refine (MeasureTheory.integral_const_mul (Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t))
    (fun s : ℝ => Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - s)
      * Work.FTS.EllSol.PkgK5.K5c.Qext (Work.FTS.EllSol.EllPkgAux.Gquad G)
          (Real.exp t) s)).symm.trans ?_
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [Work.FTS.EllSol.EllPkgAux.Hxy, Work.FTS.EllSol.EllPkgAux.Kd, Prod.fst_sub,
    Prod.snd_sub]
  ring

end Work.FTS.EllSol.EllPkgAux.MollSmooth
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollSmooth.zmoll_Gquad_eq_zmoll =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollSmooth

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary facts about `Gquad` and `Qext` -/

/-- `Gquad G` agrees with `G` on the *open* quadrant. -/
lemma Gquad_eq_self_of_mem {G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.FTS.EllSol.EllPkgAux.Gquad G z θ = G z θ := by
  rw [Work.FTS.EllSol.EllPkgAux.Gquad, if_pos h]

/-- `Gquad G` agrees with `G` on the *closed* quadrant when `G` vanishes on the two boundary
lines (at `θ = 0` both `G` and `Gquad G` are `0`, and likewise at `θ = π/2`). -/
lemma Gquad_eq_self_of_mem_Icc (G : ℝ → ℝ → ℝ) (h0 : ∀ z : ℝ, G z 0 = 0)
    (hπ : ∀ z : ℝ, G z (Real.pi / 2) = 0) {z s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    Work.FTS.EllSol.EllPkgAux.Gquad G z s = G z s := by
  rcases lt_or_eq_of_le hs.1 with h | h
  · rcases lt_or_eq_of_le hs.2 with h2 | h2
    · exact Gquad_eq_self_of_mem ⟨h, h2⟩
    · rw [h2, hπ z, Work.FTS.EllSol.EllPkgAux.Gquad]
      norm_num [Set.mem_Ioo]
  · rw [← h, h0 z, Work.FTS.EllSol.EllPkgAux.Gquad]
    norm_num [Set.mem_Ioo]

/-- `Qext u z s = u z s` on the closed quadrant. -/
lemma Qext_of_mem_Icc (u : ℝ → ℝ → ℝ) (z s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    Work.FTS.EllSol.PkgK5.K5c.Qext u z s = u z s := by
  rw [Work.FTS.EllSol.PkgK5.K5c.Qext, if_pos (Set.mem_Icc.mp hs)]

/-- `Qext` reflects a negative argument `s` to `-u z (-s)`. -/
lemma Qext_of_neg (u : ℝ → ℝ → ℝ) (z s : ℝ) (hs : s < 0) :
    Work.FTS.EllSol.PkgK5.K5c.Qext u z s = -u z (-s) := by
  rw [Work.FTS.EllSol.PkgK5.K5c.Qext, if_neg (by rintro ⟨h1, _⟩; linarith), if_pos hs]

/-- `Qext` reflects an argument `s > π/2` to `-u z (π - s)`. -/
lemma Qext_of_pihalf_lt (u : ℝ → ℝ → ℝ) (z s : ℝ) (hs : Real.pi / 2 < s) :
    Work.FTS.EllSol.PkgK5.K5c.Qext u z s = -u z (Real.pi - s) := by
  rw [Work.FTS.EllSol.PkgK5.K5c.Qext, if_neg (by rintro ⟨_, h2⟩; linarith),
    if_neg (by intro h; linarith [Real.pi_pos])]

/-! ## Insensitivity of `Qext`, and hence of the angular mollification, to the cutoff -/

/-- On the window `(-π/2, π)` — the range of angular arguments that the mollification actually
probes — cutting `G` off outside the open quadrant does not change the doubly-odd extension
`Qext`, provided `G` vanishes on the two boundary lines. -/
lemma Qext_Gquad_eq_Qext (G : ℝ → ℝ → ℝ) (h0 : ∀ z : ℝ, G z 0 = 0)
    (hπ : ∀ z : ℝ, G z (Real.pi / 2) = 0) (w s : ℝ)
    (hs : s ∈ Set.Ioo (-(Real.pi / 2)) Real.pi) :
    Work.FTS.EllSol.PkgK5.K5c.Qext (Work.FTS.EllSol.EllPkgAux.Gquad G) w s
      = Work.FTS.EllSol.PkgK5.K5c.Qext G w s := by
  by_cases h1 : 0 ≤ s ∧ s ≤ Real.pi / 2
  · rw [Qext_of_mem_Icc _ w s (Set.mem_Icc.mpr h1),
      Qext_of_mem_Icc _ w s (Set.mem_Icc.mpr h1),
      Gquad_eq_self_of_mem_Icc G h0 hπ (Set.mem_Icc.mpr h1)]
  · rcases lt_or_ge s 0 with hneg | hge
    · rw [Qext_of_neg _ w s hneg, Qext_of_neg _ w s hneg,
        Gquad_eq_self_of_mem (G := G) (z := w)
          (show -s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) from ⟨by linarith, by linarith [hs.1]⟩)]
    · have hsgt : Real.pi / 2 < s := lt_of_not_ge (fun hle => h1 ⟨hge, hle⟩)
      rw [Qext_of_pihalf_lt _ w s hsgt, Qext_of_pihalf_lt _ w s hsgt,
        Gquad_eq_self_of_mem (G := G) (z := w)
          (show Real.pi - s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) from
            ⟨by linarith [hs.2], by linarith⟩)]

/-- The angular mollification is insensitive to the quadrant cutoff (for the validity window
`0 < ε ≤ 1/2` of the mollification and the strip `-1 < θ < π/2 + 1` on which it is used). -/
lemma thMoll_Gquad_eq (G : ℝ → ℝ → ℝ) (h0 : ∀ z : ℝ, G z 0 = 0)
    (hπ : ∀ z : ℝ, G z (Real.pi / 2) = 0) (ε w θ : ℝ) (hεpos : 0 < ε) (hε : ε ≤ 1 / 2)
    (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    Work.FTS.EllSol.PkgK5.K5c.thMoll (Work.FTS.EllSol.EllPkgAux.Gquad G) ε w θ
      = Work.FTS.EllSol.PkgK5.K5c.thMoll G ε w θ := by
  rw [Work.FTS.EllSol.PkgK5.K5c.thMoll, Work.FTS.EllSol.PkgK5.K5c.thMoll]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  show Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - s)
        * Work.FTS.EllSol.PkgK5.K5c.Qext (Work.FTS.EllSol.EllPkgAux.Gquad G) w s
      = Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - s)
        * Work.FTS.EllSol.PkgK5.K5c.Qext G w s
  by_cases h : |θ - s| < ε
  · have hmem : s ∈ Set.Ioo (-(Real.pi / 2)) Real.pi := by
      rw [abs_lt] at h
      constructor <;> linarith [Real.pi_gt_three, h.1, h.2, hθ.1, hθ.2, hε]
    rw [Qext_Gquad_eq_Qext G h0 hπ w s hmem]
  · have hzero : Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - s) = 0 :=
      Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hεpos (not_lt.mp h)
    rw [hzero, zero_mul, zero_mul]

/-- The double mollification is insensitive to the quadrant cutoff: no `z`-, `δ`- or
integrability hypothesis is needed, because the identity is pointwise in the outer (`t`)
variable. -/
theorem zmoll_Gquad_eq_zmoll (G : ℝ → ℝ → ℝ) (h0 : ∀ z : ℝ, G z 0 = 0)
    (hπ : ∀ z : ℝ, G z (Real.pi / 2) = 0) (δ ε : ℝ) (hεpos : 0 < ε) (hε : ε ≤ 1 / 2)
    (z θ : ℝ) (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    Work.FTS.EllSol.PkgK5.K5c.zmoll (Work.FTS.EllSol.EllPkgAux.Gquad G) δ ε z θ
      = Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε z θ := by
  rw [Work.FTS.EllSol.PkgK5.K5c.zmoll, Work.FTS.EllSol.PkgK5.K5c.zmoll]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t)
        * Work.FTS.EllSol.PkgK5.K5c.thMoll (Work.FTS.EllSol.EllPkgAux.Gquad G) ε (Real.exp t) θ
      = Work.FTS.EllSol.PkgK5.K5c.sKer δ (Real.log z - t)
        * Work.FTS.EllSol.PkgK5.K5c.thMoll G ε (Real.exp t) θ
  rw [thMoll_Gquad_eq G h0 hπ ε (Real.exp t) θ hεpos hε hθ]

end Work.FTS.EllSol.EllPkgAux.MollSmooth
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollSmooth.zmoll_theta_pihalf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollSmooth

open MeasureTheory Set Filter

open Work.FTS.EllSol.PkgK5.K5c

/-- **The angular mollification vanishes at `θ = π/2`.**  For every datum `G`, every `w`, and
every scale `ε ∈ (0, 1/2]`, the angular mollification `thMoll G ε w` of the slice
`s ↦ G w s` (through the doubly-odd extension `Qext G w`) is `0` at `θ = π/2`.

Indeed `sKer ε` is even and supported in `[-ε, ε]`, and on `(-ε, ε) \ {0}` the oddness of
`Qext` about `π/2` gives `Qext G w (π/2 - u) = -Qext G w (π/2 + u)`, so the substitution
`u ↦ π/2 - u` (which preserves Lebesgue measure) exhibits the integral as the integral of
its own negative. -/
theorem thMoll_pihalf_eq_zero (G : ℝ → ℝ → ℝ) (ε w : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    thMoll G ε w (Real.pi / 2) = 0 := by
  change (∫ s : ℝ, sKer ε (Real.pi / 2 - s) * Qext G w s) = 0
  set f : ℝ → ℝ := fun s => sKer ε (Real.pi / 2 - s) * Qext G w s with hf
  -- The pointwise oddness of the shifted integrand away from `u = 0`.
  have key : ∀ u : ℝ, u ≠ 0 → f (Real.pi / 2 - u) = -f (Real.pi / 2 + u) := by
    intro u hu0
    have hFu : f (Real.pi / 2 - u) = sKer ε u * Qext G w (Real.pi / 2 - u) := by
      simp only [hf]
      rw [show Real.pi / 2 - (Real.pi / 2 - u) = u by ring]
    have hFv : f (Real.pi / 2 + u) = sKer ε u * Qext G w (Real.pi / 2 + u) := by
      simp only [hf]
      rw [show Real.pi / 2 - (Real.pi / 2 + u) = -u by ring, sKer_even]
    rw [hFu, hFv]
    by_cases hbig : ε ≤ |u|
    · -- outside the support of the kernel both sides vanish
      rw [sKer_eq_zero_of_le_abs hε hbig]
      ring
    · have hu_lt : |u| < ε := not_le.mp hbig
      have hpos : 0 < |u| := abs_pos.mpr hu0
      have hpi2 : |u| ≤ Real.pi / 2 := by
        have h3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
        linarith
      have hQ : Qext G w (Real.pi / 2 - |u|) = -Qext G w (Real.pi / 2 + |u|) :=
        Qext_pihalf_odd G w |u| hpos hpi2
      rcases lt_or_ge 0 u with hu | hu
      · -- `u > 0`: the identity is `Qext_pihalf_odd` at `s = u`
        rw [abs_of_pos hu] at hQ
        rw [hQ]
        ring
      · -- `u < 0`: the same identity at `s = -u`, using evenness of the kernel
        have huneg : u < 0 := lt_of_le_of_ne hu hu0
        have habs : |u| = -u := abs_of_neg huneg
        have hsu : sKer ε u = sKer ε |u| := by rw [habs, sKer_even]
        rw [hsu, show Real.pi / 2 - u = Real.pi / 2 + |u| by rw [habs]; ring,
          show Real.pi / 2 + u = Real.pi / 2 - |u| by rw [habs]; ring, hQ]
        ring
  -- The shifted integrands are a.e. negatives of each other.
  have hgh : (fun u : ℝ => f (Real.pi / 2 - u)) =ᵐ[volume]
      (fun u : ℝ => -f (Real.pi / 2 + u)) := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_singleton (0 : ℝ))
    intro u hu
    simp only [Set.mem_ofPred_eq] at hu ⊢
    by_contra hne
    exact hu (key u hne)
  -- The reflection `s ↦ π/2 - s` and the translation `s ↦ π/2 + s` preserve Lebesgue measure.
  have A1 : (∫ s : ℝ, f s) = ∫ u : ℝ, f (Real.pi / 2 - u) :=
    (MeasureTheory.integral_sub_left_eq_self f volume (Real.pi / 2)).symm
  have A2 : (∫ s : ℝ, f s) = ∫ u : ℝ, f (Real.pi / 2 + u) :=
    (MeasureTheory.integral_add_left_eq_self f (Real.pi / 2)).symm
  have C : (∫ u : ℝ, f (Real.pi / 2 - u)) = -∫ u : ℝ, f (Real.pi / 2 + u) := by
    rw [MeasureTheory.integral_congr_ae hgh, MeasureTheory.integral_neg]
  linarith [A1, A2, C]

theorem zmoll_theta_pihalf (G : ℝ → ℝ → ℝ) (δ ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (z : ℝ) :
    Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε z (Real.pi / 2) = 0 := by
  have hth : ∀ w : ℝ, Work.FTS.EllSol.PkgK5.K5c.thMoll G ε w (Real.pi / 2) = 0 :=
    fun w => thMoll_pihalf_eq_zero G ε w hε hε2
  simp only [Work.FTS.EllSol.PkgK5.K5c.zmoll, hth, mul_zero]
  exact MeasureTheory.integral_zero ℝ ℝ

end Work.FTS.EllSol.EllPkgAux.MollSmooth
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollSmooth.zmoll_theta_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollSmooth

open Work.FTS.EllSol.PkgK5.K5c

/-- The integrand of the angular mollification at `θ = 0`: the even kernel `sKer ε` sampled at
`-s` against the doubly-odd extension `Qext G w`. -/
def thZero (G : ℝ → ℝ → ℝ) (ε w : ℝ) : ℝ → ℝ :=
  fun s => sKer ε (-s) * Qext G w s

/-- **The integral of an almost everywhere odd real function vanishes.** -/
theorem integral_eq_zero_of_ae_odd {g : ℝ → ℝ}
    (h : ∀ᵐ s ∂(volume : Measure ℝ), g (-s) = - g s) : ∫ s, g s = 0 := by
  have h1 : ∫ s, g s = ∫ s, - g (-s) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [h] with s hs
    rw [hs]; ring
  have h2 : ∫ s, - g (-s) = - ∫ s, g (-s) := MeasureTheory.integral_neg _
  have h3 : ∫ s, g (-s) = ∫ s, g s := MeasureTheory.integral_neg_eq_self g volume
  have h4 : ∫ s, g s = - ∫ s, g s := by
    calc ∫ s, g s = ∫ s, - g (-s) := h1
      _ = - ∫ s, g (-s) := h2
      _ = - ∫ s, g s := by rw [h3]
  linarith

/-- Almost every real number is nonzero, `volume` being atomless. -/
theorem ae_ne_zero' : ∀ᵐ s : ℝ ∂(volume : Measure ℝ), s ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  rw [show {a : ℝ | ¬ a ≠ 0} = ({0} : Set ℝ) by ext a; simp]
  exact MeasureTheory.NullSingletonClass.measure_singleton 0

/-- `Qext u z` is odd about `0` on `(-1/2, 1/2)` — the range met by the angular mollification
at scales `ε ≤ 1/2` — except at the origin. -/
theorem Qext_neg_eq_neg_of_abs_lt_half {u : ℝ → ℝ → ℝ} {z s : ℝ} (hs : s ≠ 0)
    (h : |s| < 1 / 2) : Qext u z (-s) = - Qext u z s := by
  have hpi : (1 : ℝ) / 2 < Real.pi / 2 := by linarith [Real.pi_gt_three]
  rcases lt_or_gt_of_ne hs with hslt | hsgt
  · have ht : 0 < -s := by linarith
    have htle : -s ≤ Real.pi / 2 := by
      have h1 : -s < 1 / 2 := by linarith [(abs_lt.mp h).1]
      linarith
    have h1 : Qext u z (-s) = u z (-s) := Qext_of_mem u z (-s) ⟨ht.le, htle⟩
    have h2 : Qext u z s = -u z (-s) := by
      have h3 := Qext_neg_of_pos u z (-s) ht
      rwa [neg_neg] at h3
    rw [h1, h2, neg_neg]
  · rw [Qext_neg_of_pos u z s hsgt,
      Qext_of_mem u z s ⟨hsgt.le, by linarith [(abs_lt.mp h).2]⟩]

/-- The `θ = 0` integrand of the angular mollification is odd off the origin. -/
theorem thZero_ae_odd (G : ℝ → ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (w s : ℝ) (hs : s ≠ 0) : thZero G ε w (-s) = - thZero G ε w s := by
  unfold thZero
  by_cases hsmall : |s| < ε
  · have hhalf : |s| < 1 / 2 := lt_of_lt_of_le hsmall hε2
    rw [neg_neg, sKer_even ε s, Qext_neg_eq_neg_of_abs_lt_half hs hhalf]
    ring
  · rw [not_lt] at hsmall
    have h0 : sKer ε s = 0 := sKer_eq_zero_of_le_abs hε hsmall
    have h00 : sKer ε (-s) = 0 := sKer_eq_zero_of_le_abs hε (by simpa using hsmall)
    rw [neg_neg, h0, h00]
    simp

/-- **The angular mollification vanishes at `θ = 0`.** -/
theorem thMoll_theta_zero (G : ℝ → ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (w : ℝ) : thMoll G ε w 0 = 0 := by
  have hae : ∀ᵐ s ∂(volume : Measure ℝ), thZero G ε w (-s) = - thZero G ε w s := by
    filter_upwards [ae_ne_zero'] with s hs
    exact thZero_ae_odd G hε hε2 w s hs
  have h0 : ∫ s, thZero G ε w s = 0 := integral_eq_zero_of_ae_odd hae
  have h1 : thMoll G ε w 0 = ∫ s, thZero G ε w s := by
    simp only [thMoll, thZero, zero_sub]
  rw [h1, h0]

theorem zmoll_theta_zero (G : ℝ → ℝ → ℝ) (δ ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (z : ℝ) :
    Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε z 0 = 0 := by
  simp only [Work.FTS.EllSol.PkgK5.K5c.zmoll, thMoll_theta_zero G hε hε2]
  simp

end Work.FTS.EllSol.EllPkgAux.MollSmooth
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.Qext_eq_Qcut_combination =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux

/-- **The pointwise doubly-odd extension identity.**

Writing `g := u z`, the doubly odd extension `Qext u z` of the angular slice agrees with the
three-image combination `Qcut g s - Qcut g (-s) - Qcut g (π - s)` on the window
`(-3/4, π/2 + 3/4)` that the angular mollification at scales `ε ≤ 1/2` can reach.

The three pieces are the reflections of the slice about `0` (sign `-`) and about `π/2`
(sign `-`); the endpoint values `u z 0 = 0` and `u z (π/2) = 0` are needed only at the two
exceptional angles `s = 0` and `s = π/2`, where the reflected intervals meet the base
interval `Iθ = [0, π/2]` at a single point. -/
theorem Qext_eq_Qcut_pt {u : ℝ → ℝ → ℝ} {z s : ℝ} (h0 : u z 0 = 0)
    (hp : u z (Real.pi / 2) = 0) (hs_gt : -(3 : ℝ) / 4 < s)
    (hs_lt : s < Real.pi / 2 + 3 / 4) :
    Work.FTS.EllSol.PkgK5.K5c.Qext u z s
      = Qcut (fun s : ℝ => u z s) s
        - Qcut (fun s : ℝ => u z s) (-s)
        - Qcut (fun s : ℝ => u z s) (Real.pi - s) := by
  by_cases hneg : s < 0
  · -- `s < 0`: the base interval is missed, and `Qext` evaluates the `0`-reflection.
    rw [Work.FTS.EllSol.PkgK5.K5c.Qext,
      if_neg (by intro h; exact absurd h.1 (not_le.mpr hneg)), if_pos hneg]
    rw [Qcut_of_lt_zero hneg,
      Qcut_of_mem (show -s ∈ Set.Icc (0 : ℝ) (Real.pi / 2) from
        ⟨by linarith, by linarith [hs_gt, Real.pi_gt_three]⟩),
      Qcut_of_pihalf_lt (show Real.pi / 2 < Real.pi - s by linarith [Real.pi_pos])]
    ring
  · rw [not_lt] at hneg
    by_cases hle : s ≤ Real.pi / 2
    · -- `0 ≤ s ≤ π/2`: the reflected intervals meet `Iθ` only at the endpoints.
      have hQneg : Qcut (fun s : ℝ => u z s) (-s) = 0 := by
        rw [Qcut_apply]
        split_ifs with h
        · have hs0 : s = 0 := by linarith [h.1]
          rw [hs0]
          simpa using h0
        · rfl
      have hQpi : Qcut (fun s : ℝ => u z s) (Real.pi - s) = 0 := by
        rw [Qcut_apply]
        split_ifs with h
        · have hs : s = Real.pi / 2 := by linarith [h.2]
          rw [hs, show Real.pi - Real.pi / 2 = Real.pi / 2 by ring]
          exact hp
        · rfl
      rw [Work.FTS.EllSol.PkgK5.K5c.Qext, if_pos ⟨hneg, hle⟩,
        Qcut_of_mem ⟨hneg, hle⟩, hQneg, hQpi]
      ring
    · -- `π/2 < s`: the base interval is missed, and `Qext` evaluates the `π/2`-reflection.
      rw [not_le] at hle
      rw [Work.FTS.EllSol.PkgK5.K5c.Qext,
        if_neg (by intro h; exact absurd h.2 (not_le.mpr hle)),
        if_neg (by intro h; linarith [Real.pi_pos])]
      rw [Qcut_of_pihalf_lt hle, Qcut_of_lt_zero (by linarith [hle, Real.pi_pos]),
        Qcut_of_mem (show Real.pi - s ∈ Set.Icc (0 : ℝ) (Real.pi / 2) from
          ⟨by linarith [hs_lt, Real.pi_gt_three], by linarith⟩)]
      ring

theorem Qext_eq_Qcut_combination {u : ℝ → ℝ → ℝ} {z ε θ' s : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (h0 : u z 0 = 0) (hp : u z (Real.pi / 2) = 0)
    (hθ'1 : -(1 / 4) < θ') (hθ'2 : θ' < Real.pi / 2 + 1 / 4) :
    Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ' - s) * Work.FTS.EllSol.PkgK5.K5c.Qext u z s
      = Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ' - s)
        * (Work.FTS.EllSol.EllPkgAux.Qcut (fun s : ℝ => u z s) s
            - Work.FTS.EllSol.EllPkgAux.Qcut (fun s : ℝ => u z s) (-s)
            - Work.FTS.EllSol.EllPkgAux.Qcut (fun s : ℝ => u z s) (Real.pi - s)) := by
  by_cases hker : Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ' - s) = 0
  · -- The kernel vanishes: both sides are `0`.
    rw [hker, zero_mul, zero_mul]
  · -- Otherwise the support of the bump confines `s` to `(θ' - ε, θ' + ε)`, and the
    -- pointwise identity applies because `θ' ∈ (-1/4, π/2 + 1/4)` and `ε ≤ 1/2`.
    have habs : |θ' - s| < ε :=
      not_le.mp (fun h => hker (Work.FTS.EllSol.PkgK5.K5c.sKer_eq_zero_of_le_abs hε h))
    have hs_gt : -(3 : ℝ) / 4 < s := by
      have h1 : θ' - s < ε := (abs_lt.mp habs).2
      linarith
    have hs_lt : s < Real.pi / 2 + 3 / 4 := by
      have h1 : -ε < θ' - s := (abs_lt.mp habs).1
      linarith
    rw [Qext_eq_Qcut_pt h0 hp hs_gt hs_lt]

end Work.FTS.EllSol.EllPkgAux
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.ThMollAux0 =====
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
set_option maxHeartbeats 1000000

open Work.FTS.EllSol.PkgK5.K5c

local notation "Iθ" => Work.Spaces.Iθ

/-- The bump is bounded by its normalising constant. -/
theorem abs_sKer_le_inv {ε : ℝ} (hε : 0 < ε) (t : ℝ) : |sKer ε t| ≤ (ε * sMass)⁻¹ := by
  have hD : 0 ≤ (ε * sMass)⁻¹ := inv_nonneg.mpr (mul_nonneg hε.le sMass_pos.le)
  rw [sKer, abs_mul, abs_of_nonneg hD]
  refine mul_le_of_le_one_right hD ?_
  rw [abs_le]
  exact ⟨by linarith [sBump_nonneg (t / ε)], sBump_le_one (t / ε)⟩

/-- Change of variables `x ↦ -x` for the Lebesgue integral on the line. -/
theorem integral_comp_neg_eq (f : ℝ → ℝ) : (∫ x : ℝ, f (-x)) = ∫ x : ℝ, f x := by
  have h := MeasureTheory.Measure.integral_comp_mul_left f (-1 : ℝ)
  simpa using h

/-- Multiplying by an indicator of `Iθ` turns a line integral into the set integral over `Iθ`. -/
theorem integral_mul_Qcut (f g : ℝ → ℝ) :
    (∫ s : ℝ, f s * Qcut g s) = ∫ s in Iθ, f s * g s := by
  have h : (fun s : ℝ => f s * Qcut g s)
      = (Set.Icc (0 : ℝ) (Real.pi / 2)).indicator (fun s : ℝ => f s * g s) := by
    funext s
    rw [Qcut]
    exact (Set.indicator_mul_right _ f g).symm
  rw [h, MeasureTheory.integral_indicator measurableSet_Icc]
  rfl

/-- The set integral over `Iθ` is the interval integral from `0` to `π/2`. -/
theorem setIntegral_Iθ_eq_interval (f : ℝ → ℝ) :
    (∫ s in Iθ, f s) = ∫ s in (0 : ℝ)..(Real.pi / 2), f s := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ Real.pi / 2 by positivity)]


/-! ## Integrability of a bump times an integrable function -/

/-- A bump of radius `ε` times an integrable function is integrable. -/
theorem integrable_sKer_mul_of_integrable {ε θ' : ℝ} (hε : 0 < ε) {F : ℝ → ℝ}
    (hF : Integrable F) : Integrable (fun s : ℝ => sKer ε (θ' - s) * F s) := by
  have hD : 0 ≤ (ε * sMass)⁻¹ := inv_nonneg.mpr (mul_nonneg hε.le sMass_pos.le)
  have hcont : Continuous (fun s : ℝ => sKer ε (θ' - s)) :=
    ((contDiff_sKer ε (n := 3)).continuous).comp (continuous_const.sub continuous_id)
  have hm : AEStronglyMeasurable (fun s : ℝ => sKer ε (θ' - s) * F s) volume :=
    hcont.aestronglyMeasurable.mul hF.1
  refine MeasureTheory.Integrable.mono' (g := fun s : ℝ => (ε * sMass)⁻¹ * ‖F s‖) ?_ hm ?_
  · simpa only [Real.norm_eq_abs] using hF.norm.const_mul ((ε * sMass)⁻¹)
  · filter_upwards with s
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_sKer_le_inv hε (θ' - s)) (abs_nonneg (F s))

/-! ## The angle interval bookkeeping -/

theorem measurableSet_Iθ : MeasurableSet Iθ := measurableSet_Icc

theorem pi_half_pos : (0 : ℝ) < Real.pi / 2 := by positivity

/-- Weighted integration by parts on `[0, π/2]` with interior differentiability. -/
theorem ibp_first_pi {u u' g h : ℝ → ℝ}
    (hu : ContinuousOn u (Set.Icc (0 : ℝ) (Real.pi / 2)))
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) (Real.pi / 2)))
    (hu' : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt u (u' x) x)
    (hg' : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt g (h x) x)
    (hu'int : IntervalIntegrable u' volume 0 (Real.pi / 2))
    (hhint : IntervalIntegrable h volume 0 (Real.pi / 2)) :
    (∫ x in (0 : ℝ)..(Real.pi / 2), u x * h x)
      = u (Real.pi / 2) * g (Real.pi / 2) - u 0 * g 0
        - ∫ x in (0 : ℝ)..(Real.pi / 2), u' x * g x := by
  have hle : (0 : ℝ) ≤ Real.pi / 2 := pi_half_pos.le
  have hmin : min (0 : ℝ) (Real.pi / 2) = 0 := min_eq_left hle
  have hmax : max (0 : ℝ) (Real.pi / 2) = Real.pi / 2 := max_eq_right hle
  refine intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := 0) (b := Real.pi / 2) ?_ ?_ ?_ ?_ hu'int hhint
  · simpa only [Set.uIcc_of_le hle] using hu
  · simpa only [Set.uIcc_of_le hle] using hg
  · intro x hx
    rw [hmin, hmax] at hx
    exact hu' x hx
  · intro x hx
    rw [hmin, hmax] at hx
    exact hg' x hx

end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.hasDerivAt_intervalIntegral_Kern =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

theorem hasDerivAt_intervalIntegral_Kern {ρ ρ' g : ℝ → ℝ} {C a b : ℝ}
    (hd : ∀ t : ℝ, HasDerivAt ρ (ρ' t) t) (hC : ∀ t : ℝ, |ρ' t| ≤ C)
    (hg : ContinuousOn g (Set.uIcc a b)) :
    ∀ θ : ℝ, HasDerivAt (fun θ' : ℝ => ∫ s in a..b, Work.FTS.EllSol.EllPkgAux.Kern ρ θ' s * g s)
      (∫ s in a..b, Work.FTS.EllSol.EllPkgAux.Kern ρ' θ s * g s) θ := by
  intro θ
  -- `ρ` is continuous (it is differentiable everywhere) …
  have hcontρ : Continuous ρ := continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt
  -- … and `ρ' = deriv ρ` is measurable.
  have hρ'eq : ρ' = deriv ρ := funext fun t => ((hd t).deriv).symm
  have hmeasρ' : Measurable ρ' := by rw [hρ'eq]; exact measurable_deriv ρ
  -- continuity of `s ↦ Kern ρ x s`.
  have hcontK : ∀ x : ℝ, Continuous fun s : ℝ => Kern ρ x s := by
    intro x
    have h1 : Continuous fun s : ℝ => ρ (x - s) := hcontρ.comp (continuous_const.sub continuous_id)
    have h2 : Continuous fun s : ℝ => ρ (x + s) := hcontρ.comp (continuous_const.add continuous_id)
    have h3 : Continuous fun s : ℝ => ρ (x + s - Real.pi) :=
      hcontρ.comp ((continuous_const.add continuous_id).sub continuous_const)
    have heq : (fun s : ℝ => Kern ρ x s)
        = fun s => ρ (x - s) - ρ (x + s) - ρ (x + s - Real.pi) := by
      funext s; exact Kern_apply ρ x s
    rw [heq]
    exact (h1.sub h2).sub h3
  -- measurability of `s ↦ Kern ρ' x s`.
  have hmeasK' : ∀ x : ℝ, Measurable fun s : ℝ => Kern ρ' x s := by
    intro x
    have h1 : Measurable fun s : ℝ => ρ' (x - s) :=
      hmeasρ'.comp (measurable_const.sub measurable_id)
    have h2 : Measurable fun s : ℝ => ρ' (x + s) :=
      hmeasρ'.comp (measurable_const.add measurable_id)
    have h3 : Measurable fun s : ℝ => ρ' (x + s - Real.pi) :=
      hmeasρ'.comp ((measurable_const.add measurable_id).sub measurable_const)
    have heq : (fun s : ℝ => Kern ρ' x s)
        = fun s => ρ' (x - s) - ρ' (x + s) - ρ' (x + s - Real.pi) := by
      funext s; exact Kern_apply ρ' x s
    rw [heq]
    exact (h1.sub h2).sub h3
  -- `g` is a.e. strongly measurable on `uIoc a b`, since it is continuous on `uIcc a b`.
  have hg_aem : AEMeasurable g (volume.restrict (Set.uIoc a b)) :=
    AEMeasurable.mono_set Set.uIoc_subset_uIcc (hg.aemeasurable measurableSet_uIcc)
  have hF_meas : ∀ᶠ x in 𝓝 θ, AEStronglyMeasurable (fun s : ℝ => Kern ρ x s * g s)
      (volume.restrict (Set.uIoc a b)) := by
    refine Filter.Eventually.of_forall fun x => ?_
    have hmul : ContinuousOn (fun s : ℝ => Kern ρ x s * g s) (Set.uIcc a b) :=
      ((hcontK x).continuousOn.mono (Set.subset_univ _)).mul hg
    exact AEStronglyMeasurable.mono_set Set.uIoc_subset_uIcc
      (hmul.aestronglyMeasurable measurableSet_uIcc)
  have hF_int : IntervalIntegrable (fun s : ℝ => Kern ρ θ s * g s) volume a b :=
    (((hcontK θ).continuousOn.mono (Set.subset_univ _)).mul hg).intervalIntegrable
  have hF'_meas : AEStronglyMeasurable (fun s : ℝ => Kern ρ' θ s * g s)
      (volume.restrict (Set.uIoc a b)) :=
    (((hmeasK' θ).aemeasurable).mul hg_aem).aestronglyMeasurable
  -- the uniform dominating function `t ↦ 3 C |g t|`
  have hbound : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc a b → ∀ x ∈ (Set.univ : Set ℝ),
      ‖Kern ρ' x t * g t‖ ≤ 3 * C * |g t| := by
    filter_upwards with t _ht x _hx
    have hK : |Kern ρ' x t| ≤ 3 * C := by
      rw [Kern_apply]
      have h := abs_sub (ρ' (x - t) - ρ' (x + t)) (ρ' (x + t - Real.pi))
      have h2 := abs_sub (ρ' (x - t)) (ρ' (x + t))
      have h3 := hC (x - t); have h4 := hC (x + t); have h5 := hC (x + t - Real.pi)
      linarith [abs_nonneg (ρ' (x + t - Real.pi))]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hK (abs_nonneg _)
  have hbound_int : IntervalIntegrable (fun t : ℝ => 3 * C * |g t|) volume a b :=
    (hg.abs.intervalIntegrable).const_mul (3 * C)
  have hdiff : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc a b → ∀ x ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun y : ℝ => Kern ρ y t * g t) (Kern ρ' x t * g t) x := by
    filter_upwards with t _ht x _hx
    exact (Kern_hasDerivAt hd x t).mul_const (g t)
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun y s => Kern ρ y s * g s)
    (F' := fun y s => Kern ρ' y s * g s)
    (x₀ := θ) (s := Set.univ) (a := a) (b := b) (μ := volume)
    (bound := fun t => 3 * C * |g t|)
    Filter.univ_mem hF_meas hF_int hF'_meas hbound hbound_int hdiff).2

end Work.FTS.EllSol.EllPkgAux
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.mixedPartialEq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology
open Filter

namespace Work.FTS.EllSol.EllPkgAux

/-- **Mixed partial derivative, general form.** For `F : ℝ × ℝ → ℝ` which is `C²` on an open
set `U` and `p = (x,y) ∈ U`, the derivative at `x` of the `y`-slice derivative
`x' ↦ deriv (fun y' => F (x',y')) y` equals the second Fréchet derivative of `F` at `(x,y)`
evaluated on `(1,0)` and then `(0,1)`. -/
theorem mixedPartialEq_uncurry {F : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} {x y : ℝ}
    (hU : IsOpen U) (hxy : (x, y) ∈ U) (hF : ContDiffOn ℝ 2 F U) :
    deriv (fun x' => deriv (fun y' => F (x', y')) y) x
      = (fderiv ℝ (fderiv ℝ F) (x, y) (1, 0)) (0, 1) := by
  have hUnhds : U ∈ 𝓝 (x, y) := hU.mem_nhds hxy
  -- `F` is differentiable on `U`, and the derivative is `C¹` there.
  have hFdiff : DifferentiableOn ℝ F U := hF.differentiableOn (by norm_num)
  have hdfF : ContDiffOn ℝ 1 (fderiv ℝ F) U := hF.fderiv_of_isOpen hU (by norm_num)
  have hdfFdiff : DifferentiableOn ℝ (fderiv ℝ F) U := hdfF.differentiableOn (by norm_num)
  -- the points `(x', y)` with `x'` near `x` all lie in `U`
  have hcont : ContinuousAt (fun x' : ℝ => (x', y)) x := by fun_prop
  have hmem : ∀ᶠ x' in 𝓝 x, (x', y) ∈ U := hcont.preimage_mem_nhds hUnhds
  -- the `y`-slice derivative
  have hslice : ∀ x' : ℝ, (x', y) ∈ U →
      deriv (fun y' => F (x', y')) y = (fderiv ℝ F (x', y)) (0, 1) := by
    intro x' hx'
    have hF' : HasFDerivAt F (fderiv ℝ F (x', y)) (x', y) :=
      DifferentiableOn.hasFDerivAt hFdiff (hU.mem_nhds hx')
    have hφ : HasDerivAt (fun t : ℝ => (x', t)) (0, 1) y :=
      (hasDerivAt_const y x').prodMk (hasDerivAt_id y)
    exact (hF'.comp_hasDerivAt y hφ).deriv
  have hgerm : (fun x' => deriv (fun y' => F (x', y')) y) =ᶠ[𝓝 x]
      (fun x' => (fderiv ℝ F (x', y)) (0, 1)) := by
    filter_upwards [hmem] with x' hx'
    exact hslice x' hx'
  -- the `x`-derivative of `p ↦ (fderiv ℝ F p) (0,1)` at `(x,y)`
  have hG : HasFDerivAt (fun p : ℝ × ℝ => (fderiv ℝ F p) (0, 1))
      ((ContinuousLinearMap.apply ℝ ℝ (0, 1)).comp (fderiv ℝ (fderiv ℝ F) (x, y))) (x, y) := by
    have hdF : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) (x, y)) (x, y) :=
      DifferentiableOn.hasFDerivAt hdfFdiff hUnhds
    have hev : HasFDerivAt (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0, 1))
        (ContinuousLinearMap.apply ℝ ℝ (0, 1)) (fderiv ℝ F (x, y)) :=
      (ContinuousLinearMap.apply ℝ ℝ (0, 1)).hasFDerivAt
    have h2 := hev.comp (x, y) hdF
    simpa [Function.comp_def] using h2
  have hderiv : deriv (fun x' => (fderiv ℝ F (x', y)) (0, 1)) x
      = (fderiv ℝ (fderiv ℝ F) (x, y) (1, 0)) (0, 1) := by
    have hφ : HasDerivAt (fun t : ℝ => (t, y)) (1, 0) x :=
      (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
    have h4 : HasDerivAt (fun x' => (fderiv ℝ F (x', y)) (0, 1))
        (((ContinuousLinearMap.apply ℝ ℝ (0, 1)).comp
          (fderiv ℝ (fderiv ℝ F) (x, y))) (1, 0)) x := by
      have h5 := hG.comp_hasDerivAt x hφ
      simpa [Function.comp_def] using h5
    rw [h4.deriv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  rw [Filter.EventuallyEq.deriv_eq hgerm, hderiv]

theorem mixedPartialEq {H : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} {x y : ℝ}
    (hU : IsOpen U) (hxy : (x, y) ∈ U) (hH : ContDiffOn ℝ 2 (Function.uncurry H) U) :
    deriv (fun x' => deriv (fun y' => H x' y') y) x
      = (fderiv ℝ (fderiv ℝ (Function.uncurry H)) (x, y) (1, 0)) (0, 1) :=
  mixedPartialEq_uncurry hU hxy hH

end Work.FTS.EllSol.EllPkgAux
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.mollFatouHelpers =====
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

/-- `thEta θ = sin(2θ)^{-η}` is continuous on the open interval. -/
theorem continuousOn_thEta_Ioo :
    ContinuousOn Work.FTS.EllipticEst.thEta (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * θ) ≠ 0 := fun θ hθ =>
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))
  have h := hsin.rpow_const (p := -(Work.Spaces.eta)) (fun θ hθ => Or.inl (hne θ hθ))
  change ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
    (Set.Ioo (0 : ℝ) (Real.pi / 2))
  exact h

/-- The `θ`-slice integrand of the datum is a.e.-strongly measurable: it is continuous on the
open interval, which is conull in `Iθ`. -/
theorem aeStronglyMeasurable_slice_G (G : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen G)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hdiff := (hS.pth.Dz).curry_θ hz
  have hslice : ContinuousOn (fun θ : ℝ => Work.Spaces.Dz (Work.Spaces.pth G) z θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hdiff.continuousOn
  have hsq : ContinuousOn (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hslice.pow 2
  have hprod := hsq.mul continuousOn_thEta_Ioo
  rw [restrict_Iθ_eq_restrict_Ioo]
  exact hprod.aestronglyMeasurable measurableSet_Ioo

/-- On the open angular interval the doubly-odd extension `Qext` agrees with `G`, so the
uncurried integrand `Hxyc G` is smooth there. -/
theorem contDiffOn_uncurry_Hxyc (G : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen G)
    (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry (Hxyc G))
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hmap : ContDiffOn ℝ n (fun p : ℝ × ℝ => (Real.exp p.1, p.2))
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine ContDiffOn.prodMk ?_ ?_
    · exact (Real.contDiff_exp.comp (contDiff_fst)).contDiffOn
    · exact contDiff_snd.contDiffOn
  have hmaps : Set.MapsTo (fun p : ℝ × ℝ => (Real.exp p.1, p.2))
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) Work.FTS.EllipticEst.Q0 := by
    rintro ⟨t, s⟩ ⟨-, hs⟩
    exact Work.FTS.EllipticEst.mem_Q0.mpr ⟨Real.exp_pos t, hs.1, hs.2⟩
  have hcomp := (hS.forall n).comp hmap hmaps
  refine hcomp.congr (fun p hp => ?_)
  simp only [Function.uncurry, Function.comp_apply, Hxyc]
  exact Work.FTS.EllSol.PkgK5.K5c.Qext_of_mem G (Real.exp p.1) p.2
    (Set.mem_Icc.mpr ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩)

end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.mollHconv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.FTS.EllSol.EllPkgAux

/-- **Change of variables in the double convolution.**  The reflection `x ↦ a - x` of `ℝ`
preserves Lebesgue measure, so the double iterated integral of the mollifying kernel `k`
against a datum `H` can be written with the arguments of `H` reflected.  This is the passage
between the two orders in which the two-dimensional convolution is written. -/
theorem integral_reflect_pair (k : ℝ → ℝ) (H : ℝ → ℝ → ℝ) (a b : ℝ) :
    (∫ t' : ℝ, k (a - t') * (∫ s : ℝ, k (b - s) * H t' s))
      = ∫ u : ℝ, ∫ v : ℝ, k u * k v * H (a - u) (b - v) := by
  have hinner : ∀ t' : ℝ, (∫ s : ℝ, k (b - s) * H t' s) = ∫ v : ℝ, k v * H t' (b - v) := by
    intro t'
    simpa using (MeasureTheory.integral_sub_left_eq_self
        (fun v : ℝ => k v * H t' (b - v)) MeasureTheory.volume b)
  have hstep1 : (∫ t' : ℝ, k (a - t') * (∫ s : ℝ, k (b - s) * H t' s))
      = ∫ t' : ℝ, k (a - t') * (∫ v : ℝ, k v * H t' (b - v)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t' => ?_)
    simp only [hinner t']
  rw [hstep1]
  have hstep2 : (∫ t' : ℝ, k (a - t') * (∫ v : ℝ, k v * H t' (b - v)))
      = ∫ u : ℝ, k u * (∫ v : ℝ, k v * H (a - u) (b - v)) := by
    simpa using (MeasureTheory.integral_sub_left_eq_self
        (fun u : ℝ => k u * (∫ v : ℝ, k v * H (a - u) (b - v))) MeasureTheory.volume a)
  rw [hstep2]
  have hpt : ∀ u : ℝ, k u * (∫ v : ℝ, k v * H (a - u) (b - v))
      = ∫ v : ℝ, k u * k v * H (a - u) (b - v) := by
    intro u
    rw [← MeasureTheory.integral_const_mul (k u) (fun v : ℝ => k v * H (a - u) (b - v))]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    ring
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)

theorem mollHconv (G : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen G) (hderiv : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 → deriv (fun x' => deriv (fun y' => Work.FTS.EllSol.EllPkgAux.Hxyc G x' y') θ) (Real.log z) = Work.Spaces.Dz (Work.Spaces.pth G) z θ) (hid : ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ → Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G t t)) z θ = ∫ t' : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd t (Real.log z - t') * (∫ s : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd t (θ - s) * Work.FTS.EllSol.EllPkgAux.Hxyc G t' s)) (hlim : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 → Filter.Tendsto (fun t : ℝ => ∫ u : ℝ, ∫ v : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd t u * Work.FTS.EllSol.EllPkgAux.sKerd t v * Work.FTS.EllSol.EllPkgAux.Hxyc G (Real.log z - u) (θ - v)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (deriv (fun x' => deriv (fun y' => Work.FTS.EllSol.EllPkgAux.Hxyc G x' y') θ) (Real.log z)))) : ∀ z : ℝ, 0 < z → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), Filter.Tendsto (fun n : ℕ => (Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G (Work.FTS.EllSol.EllPkgAux.tseq n) (Work.FTS.EllSol.EllPkgAux.tseq n))) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Filter.atTop (nhds ((Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)) := by
  intro z hz
  -- The endpoints of `Iθ = [0, π/2]` are null, so almost everywhere `θ` lies in the open
  -- interval where both `hlim` and `hderiv` are available.
  have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    show ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))),
      θ ∈ Set.Ioo 0 (Real.pi / 2)
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null (t := ({(0 : ℝ), Real.pi / 2} : Set ℝ)) ?_ ?_
    · intro θ hθ
      simp only [Set.mem_ofPred_eq, not_imp, Set.mem_Icc, Set.mem_Ioo, not_and_or,
        not_lt] at hθ
      obtain ⟨⟨h1, h2⟩, h3⟩ := hθ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases h3 with h3 | h3
      · exact Or.inl (le_antisymm h3 h1)
      · exact Or.inr (le_antisymm h2 h3)
    · exact Set.Finite.measure_zero (Set.Finite.insert _ (Set.finite_singleton _)) _
  filter_upwards [hae] with θ hθ
  have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  -- Along the diagonal sequence the double mollification is *exactly* the double convolution
  -- appearing in `hlim`.
  have hkey : ∀ n : ℕ,
      Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G
          (Work.FTS.EllSol.EllPkgAux.tseq n) (Work.FTS.EllSol.EllPkgAux.tseq n))) z θ
        = ∫ u : ℝ, ∫ v : ℝ,
            Work.FTS.EllSol.EllPkgAux.sKerd (Work.FTS.EllSol.EllPkgAux.tseq n) u
              * Work.FTS.EllSol.EllPkgAux.sKerd (Work.FTS.EllSol.EllPkgAux.tseq n) v
              * Work.FTS.EllSol.EllPkgAux.Hxyc G (Real.log z - u) (θ - v) := by
    intro n
    rw [hid (Work.FTS.EllSol.EllPkgAux.tseq n) (Work.FTS.EllSol.EllPkgAux.tseq_pos n)
      (Work.FTS.EllSol.EllPkgAux.tseq_le_half n) z hz θ hθIθ]
    exact integral_reflect_pair (Work.FTS.EllSol.EllPkgAux.sKerd
      (Work.FTS.EllSol.EllPkgAux.tseq n)) (Work.FTS.EllSol.EllPkgAux.Hxyc G)
      (Real.log z) θ
  have hseq : Filter.Tendsto Work.FTS.EllSol.EllPkgAux.tseq Filter.atTop
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨Work.FTS.EllSol.EllPkgAux.tendsto_tseq,
      Filter.Eventually.of_forall fun n => Work.FTS.EllSol.EllPkgAux.tseq_pos n⟩
  have hcomp := (hlim z hz θ hθ.1 hθ.2).comp hseq
  rw [hderiv z hz θ hθ.1 hθ.2] at hcomp
  have hconv : Filter.Tendsto (fun n : ℕ =>
      Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G
        (Work.FTS.EllSol.EllPkgAux.tseq n) (Work.FTS.EllSol.EllPkgAux.tseq n))) z θ)
      Filter.atTop (nhds (Work.Spaces.Dz (Work.Spaces.pth G) z θ)) :=
    Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n => (hkey n).symm) hcomp
  exact (hconv.pow 2).mul_const (Work.FTS.EllipticEst.thEta θ)

end Work.FTS.EllSol.EllPkgAux
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.mollHdom =====
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

/-! ## The zero-extended angular slice -/

/-- The angular slice of `G` at the logarithmic radial variable `t`, extended by zero off the
open angular interval `(0, π/2)`.  This is the integrand of the slice functional. -/
def sliceAbs (G : ℝ → ℝ → ℝ) (t s : ℝ) : ℝ :=
  if s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) then |G (Real.exp t) s| else 0

theorem sliceAbs_of_mem (G : ℝ → ℝ → ℝ) {t s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    sliceAbs G t s = |G (Real.exp t) s| := by
  rw [sliceAbs, ite_eq_left hs]

theorem sliceAbs_of_notMem (G : ℝ → ℝ → ℝ) {t s : ℝ}
    (hs : s ∉ Set.Ioo (0 : ℝ) (Real.pi / 2)) : sliceAbs G t s = 0 := by
  rw [sliceAbs, ite_eq_right hs]

/-! ## The main theorem -/

theorem mollHdom (G : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen G) (C : ℝ) (hC : 0 < C) (hsl : ∀ w : ℝ, 0 < w → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 → |G w θ| ≤ C * Work.FTS.EllSol.EllPkgAux.MGf G w) (hint : ∀ a b : ℝ, 0 < a → a ≤ b → MeasureTheory.IntegrableOn (Work.FTS.EllSol.EllPkgAux.MGf G) (Set.Icc a b)) : MeasureTheory.LocallyIntegrable (fun t : ℝ => ∫ s in Work.Spaces.Iθ, |Work.FTS.EllSol.EllPkgAux.Hxyc G t s|) MeasureTheory.volume := by
  -- `MGf G` is nonnegative.
  have hMGnn : ∀ w : ℝ, 0 ≤ MGf G w := by
    intro w
    have h2 : (0 : ℝ) ≤ |G w (Real.pi / 4)| := abs_nonneg _
    have h3 : (0 : ℝ) ≤ |Work.Spaces.pth G w (Real.pi / 4)| := abs_nonneg _
    have h4 : (0 : ℝ) ≤ Real.sqrt (E2s G w) := Real.sqrt_nonneg _
    simp only [MGf]
    linarith
  -- The angular interval has finite measure.
  have hFinθ : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) :=
    ⟨by rw [Measure.restrict_apply_univ, Work.Spaces.Iθ, Real.volume_Icc, sub_zero]
        exact ENNReal.ofReal_lt_top⟩
  -- `t ↦ MGf G (e^t)` is integrable on every bounded interval (substitution, `e^t` bounded
  -- below by `e^a > 0` on `(a,b)`).
  have hExp : ∀ a b : ℝ, a < b →
      IntegrableOn (fun t : ℝ => MGf G (Real.exp t)) (Set.Ioo a b) := by
    intro a b hab
    have hiff := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
      (f := Real.exp) (f' := fun x => Real.exp x) (g := MGf G) (a := a) (b := b)
      (by fun_prop) (fun x _ => Real.hasDerivAt_exp x) (fun x _ => (Real.exp_pos x).le)
    have hR : IntervalIntegrable (MGf G) volume (Real.exp a) (Real.exp b) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le
        (le_of_lt (Real.exp_lt_exp.mpr hab))).mpr
        ((hint (Real.exp a) (Real.exp b) (Real.exp_pos a)
          (le_of_lt (Real.exp_lt_exp.mpr hab))).mono_set Set.Ioo_subset_Icc_self)
    have hL : IntegrableOn (fun t : ℝ => MGf G (Real.exp t) * Real.exp t) (Set.Ioo a b) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (le_of_lt hab)).mp (hiff.mpr hR)
    rw [IntegrableOn] at hL ⊢
    have h2 : Integrable (fun t : ℝ => (Real.exp a)⁻¹ * (MGf G (Real.exp t) * Real.exp t))
        (volume.restrict (Set.Ioo a b)) := hL.const_mul _
    refine h2.mono' ?_ ?_
    · have hcont : Continuous (fun t : ℝ => Real.exp a * (Real.exp t)⁻¹) :=
        continuous_const.mul (Real.continuous_exp.inv₀ (fun t => Real.exp_ne_zero t))
      refine (hcont.aestronglyMeasurable.mul h2.aestronglyMeasurable).congr ?_
      filter_upwards with t
      have ha : Real.exp a ≠ 0 := Real.exp_ne_zero a
      have ht : Real.exp t ≠ 0 := Real.exp_ne_zero t
      calc Real.exp a * (Real.exp t)⁻¹ * ((Real.exp a)⁻¹ * (MGf G (Real.exp t) * Real.exp t))
          = (Real.exp t)⁻¹ * Real.exp t * (Real.exp a * (Real.exp a)⁻¹)
              * MGf G (Real.exp t) := by ring
        _ = MGf G (Real.exp t) := by rw [inv_mul_cancel₀ ht, mul_inv_cancel₀ ha]; ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have hpa : 0 < Real.exp a := Real.exp_pos a
      have hlt : Real.exp a < Real.exp t := Real.exp_lt_exp.mpr ht.1
      have hge : 1 ≤ Real.exp t / Real.exp a := (one_le_div hpa).mpr hlt.le
      rw [Real.norm_of_nonneg (hMGnn _)]
      calc MGf G (Real.exp t) = MGf G (Real.exp t) * 1 := by ring
        _ ≤ MGf G (Real.exp t) * (Real.exp t / Real.exp a) :=
            mul_le_mul_of_nonneg_left hge (hMGnn _)
        _ = (Real.exp a)⁻¹ * (MGf G (Real.exp t) * Real.exp t) := by ring
  -- Main argument: on a compact interval `K` the slice functional is integrable.
  intro x
  refine ⟨Set.Ioo (x - 1) (x + 1), IsOpen.mem_nhds isOpen_Ioo ⟨by linarith, by linarith⟩, ?_⟩
  -- measurability of the joint integrand
  have hmeasS : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)} :=
    (isOpen_Ioo.preimage continuous_snd).measurableSet
  have hcontS : ContinuousOn (fun p : ℝ × ℝ => |G (Real.exp p.1) p.2|)
      {p : ℝ × ℝ | p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)} := by
    have hmp : MapsTo (fun p : ℝ × ℝ => (Real.exp p.1, p.2))
        {p : ℝ × ℝ | p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)} Work.FTS.EllipticEst.Q0 := by
      intro p hp
      rw [Work.FTS.EllipticEst.mem_Q0]
      exact ⟨Real.exp_pos p.1, hp.1, hp.2⟩
    exact (hS.continuousOn.comp (by fun_prop) hmp).abs
  have hmeasF : AEStronglyMeasurable (Function.uncurry (sliceAbs G))
      ((volume.restrict (Set.Ioo (x - 1) (x + 1))).prod (volume.restrict Work.Spaces.Iθ)) := by
    have h1 : AEStronglyMeasurable
        (Set.indicator {p : ℝ × ℝ | p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)}
          (fun p : ℝ × ℝ => |G (Real.exp p.1) p.2|))
        ((volume.restrict (Set.Ioo (x - 1) (x + 1))).prod (volume.restrict Work.Spaces.Iθ)) :=
      (aestronglyMeasurable_indicator_iff hmeasS).mpr (hcontS.aestronglyMeasurable hmeasS)
    refine h1.congr ?_
    filter_upwards with p
    by_cases hp : p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
    · rw [Set.indicator_of_mem
        (show p ∈ {q : ℝ × ℝ | q.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)} from hp)]
      show |G (Real.exp p.1) p.2| = sliceAbs G p.1 p.2
      rw [sliceAbs_of_mem G hp]
    · rw [Set.indicator_of_notMem
        (show p ∉ {q : ℝ × ℝ | q.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)} from hp)]
      show (0 : ℝ) = sliceAbs G p.1 p.2
      rw [sliceAbs_of_notMem G hp]
  -- integrability of the dominating function on the product
  have hDomInt : Integrable (fun p : ℝ × ℝ => C * MGf G (Real.exp p.1))
      ((volume.restrict (Set.Ioo (x - 1) (x + 1))).prod (volume.restrict Work.Spaces.Iθ)) :=
    ((hExp (x - 1) (x + 1) (by linarith)).comp_fst
      (volume.restrict Work.Spaces.Iθ)).const_mul C
  -- the joint integrand is integrable
  have hFInt : Integrable (Function.uncurry (sliceAbs G))
      ((volume.restrict (Set.Ioo (x - 1) (x + 1))).prod (volume.restrict Work.Spaces.Iθ)) := by
    refine hDomInt.mono' hmeasF (Eventually.of_forall (fun p => ?_))
    by_cases hp : p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
    · have hval : ‖Function.uncurry (sliceAbs G) p‖ = |G (Real.exp p.1) p.2| := by
        show ‖sliceAbs G p.1 p.2‖ = |G (Real.exp p.1) p.2|
        rw [sliceAbs_of_mem G hp, Real.norm_eq_abs, abs_abs]
      rw [hval]
      exact hsl (Real.exp p.1) (Real.exp_pos p.1) p.2 hp.1 hp.2
    · have hval : ‖Function.uncurry (sliceAbs G) p‖ = 0 := by
        show ‖sliceAbs G p.1 p.2‖ = 0
        rw [sliceAbs_of_notMem G hp, norm_zero]
      rw [hval]
      exact mul_nonneg (le_of_lt hC) (hMGnn _)
  -- Fubini
  have hFub := hFInt.integral_prod_left
  refine hFub.congr (Eventually.of_forall (fun t => ?_))
  rw [restrict_Iθ_eq_restrict_Ioo]
  refine setIntegral_congr_ae measurableSet_Ioo (Eventually.of_forall (fun s hs => ?_))
  show sliceAbs G t s = |Hxyc G t s|
  rw [sliceAbs_of_mem G hs, Hxyc,
    Work.FTS.EllSol.PkgK5.K5c.Qext_of_mem G (Real.exp t) s (Set.Ioo_subset_Icc_self hs)]

end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.mollKerdMoments =====
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

/-! ### Scaling of `sKer` and of its derivative -/

/-- `sKer ε` is the `ε`-rescaling of `sKer 1`. -/
theorem mk_sKer_eq_scale (ε t : ℝ) : sKer ε t = ε⁻¹ * sKer 1 (t / ε) := by
  rw [sKer, sKer]
  simp only [one_mul, div_one]
  ring

/-- The derivative of `sKer ε` is `ε⁻²` times the rescaled derivative of `sKer 1`. -/
theorem mk_deriv_sKerd_scale (ε t : ℝ) :
    deriv (sKer ε) t = ε⁻¹ * (ε⁻¹ * deriv (sKer 1) (t / ε)) := by
  have h1 : deriv (sKer ε) t = deriv (fun s : ℝ => ε⁻¹ * sKer 1 (s / ε)) t := by
    congr 1
    funext s
    exact mk_sKer_eq_scale ε s
  rw [h1, deriv_const_mul_field]
  congr 1
  rw [show (fun s : ℝ => sKer 1 (s / ε)) = (fun s : ℝ => sKer 1 (ε⁻¹ * s)) from by
        funext s; rw [div_eq_inv_mul]]
  rw [deriv_comp_mul_left]
  simp only [smul_eq_mul]
  rw [div_eq_inv_mul]

/-! ### Change of variables `t ↦ ε t` -/




/-! ### The three L¹-norms of `sKerd ε` -/




/-! ### Continuity, compact support and integrability -/

theorem mk_continuous_sKer (ε : ℝ) : Continuous (sKer ε) := by
  have h : sKer ε = fun t : ℝ => (ε * sMass)⁻¹ * sBump (t / ε) := by
    funext t; rw [sKer]
  rw [h]
  exact continuous_const.mul (sBump_continuous.comp (continuous_id.div_const ε))

theorem mk_hasCompactSupport_sKer {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (sKer ε) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-ε) ε) isCompact_Icc ?_
  intro t ht
  rw [Function.mem_support] at ht
  have hlt : |t| < ε := by
    by_contra h
    exact ht (sKer_eq_zero_of_le_abs hε (not_lt.mp h))
  rw [abs_lt] at hlt
  exact ⟨le_of_lt hlt.1, le_of_lt hlt.2⟩

theorem mk_integrable_sKer {ε : ℝ} (hε : 0 < ε) : Integrable (sKer ε) :=
  (mk_continuous_sKer ε).integrable_of_hasCompactSupport (mk_hasCompactSupport_sKer hε)

theorem mk_integrable_deriv_sKer {ε : ℝ} (hε : 0 < ε) : Integrable (deriv (sKer ε)) :=
  (contDiff_sKer ε).continuous_deriv_one.integrable_of_hasCompactSupport
    (mk_hasCompactSupport_sKer hε).deriv

theorem mk_integrable_id_sKer {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x : ℝ => x * sKer ε x) :=
  (continuous_id.mul (mk_continuous_sKer ε)).integrable_of_hasCompactSupport
    (mk_hasCompactSupport_sKer hε).mul_left

theorem mk_integrable_id_deriv_sKer {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x : ℝ => x * deriv (sKer ε) x) :=
  (continuous_id.mul (contDiff_sKer ε).continuous_deriv_one).integrable_of_hasCompactSupport
    (mk_hasCompactSupport_sKer hε).deriv.mul_left

theorem mk_integrable_sq_deriv_sKer {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x : ℝ => x ^ 2 * deriv (sKer ε) x) := by
  have hcs : HasCompactSupport (fun x : ℝ => x * (x * deriv (sKer ε) x)) :=
    (mk_hasCompactSupport_sKer hε).deriv.mul_left.mul_left
  have hcont : Continuous (fun x : ℝ => x * (x * deriv (sKer ε) x)) :=
    continuous_id.mul (continuous_id.mul (contDiff_sKer ε).continuous_deriv_one)
  have hfun : (fun x : ℝ => x ^ 2 * deriv (sKer ε) x)
      = (fun x : ℝ => x * (x * deriv (sKer ε) x)) := by
    funext x; ring
  rw [hfun]
  exact hcont.integrable_of_hasCompactSupport hcs

/-! ### The two moment identities -/

/-- The derivative of the compactly supported mass-one kernel has zero integral. -/
theorem mk_integral_sKerd_eq_zero {ε : ℝ} (hε : 0 < ε) :
    (∫ u : ℝ, deriv (sKer ε) u) = 0 := by
  have hderiv : ∀ x : ℝ, HasDerivAt (sKer ε) (deriv (sKer ε) x) x :=
    fun x => ((contDiff_sKer ε : ContDiff ℝ 1 (sKer ε)).differentiable
      one_ne_zero).differentiableAt.hasDerivAt
  have hintd : Integrable (deriv (sKer ε)) := mk_integrable_deriv_sKer hε
  have key := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun _ : ℝ => (1 : ℝ)) (u' := fun _ : ℝ => (0 : ℝ))
    (v := sKer ε) (v' := fun x : ℝ => deriv (sKer ε) x)
    (fun x _ => hasDerivAt_const x (1 : ℝ))
    (fun x _ => hderiv x)
    (by
      rw [show (fun _ : ℝ => (1 : ℝ)) * (fun x : ℝ => deriv (sKer ε) x)
            = (fun x : ℝ => deriv (sKer ε) x) from by funext x; simp]
      exact hintd)
    (by
      rw [show (fun _ : ℝ => (0 : ℝ)) * sKer ε = (fun _ : ℝ => (0 : ℝ)) from by
            funext x; simp]
      exact integrable_zero ℝ ℝ volume)
    (by
      rw [show (fun _ : ℝ => (1 : ℝ)) * sKer ε = sKer ε from by funext x; simp]
      exact mk_integrable_sKer hε)
  simpa using key

/-- The first moment of `sKerd ε`: `∫ u * sKerd ε u = -∫ sKer ε = -1`. -/
theorem mk_integral_id_sKerd {ε : ℝ} (hε : 0 < ε) :
    (∫ u : ℝ, u * deriv (sKer ε) u) = -1 := by
  have hderiv : ∀ x : ℝ, HasDerivAt (sKer ε) (deriv (sKer ε) x) x :=
    fun x => ((contDiff_sKer ε : ContDiff ℝ 1 (sKer ε)).differentiable
      one_ne_zero).differentiableAt.hasDerivAt
  have key := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => x) (u' := fun _ : ℝ => (1 : ℝ))
    (v := sKer ε) (v' := fun x : ℝ => deriv (sKer ε) x)
    (fun x _ => hasDerivAt_id x)
    (fun x _ => hderiv x)
    (by
      rw [show (fun x : ℝ => x) * (fun x : ℝ => deriv (sKer ε) x)
            = (fun x : ℝ => x * deriv (sKer ε) x) from by funext x; simp]
      exact mk_integrable_id_deriv_sKer hε)
    (by
      rw [show (fun _ : ℝ => (1 : ℝ)) * sKer ε = sKer ε from by funext x; simp]
      exact mk_integrable_sKer hε)
    (by
      rw [show (fun x : ℝ => x) * sKer ε = (fun x : ℝ => x * sKer ε x) from by
            funext x; simp]
      exact mk_integrable_id_sKer hε)
  rw [key]
  simp [sKer_integral_eq_one hε]


end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.mollTargetDeriv =====
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

/-- The doubly-odd extension `Qext` agrees with the datum on a neighbourhood of every interior
angle, hence the two `θ`-derivatives at such an angle coincide. -/
theorem deriv_Qext_slice {G : ℝ → ℝ → ℝ} {w θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2) :
    deriv (fun y' => Work.FTS.EllSol.PkgK5.K5c.Qext G w y') θ
      = deriv (fun y' => G w y') θ := by
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) from
    ⟨hθ0, hθ1⟩)] with y hy
  exact Work.FTS.EllSol.PkgK5.K5c.Qext_of_mem G w y ⟨hy.1.le, hy.2.le⟩

theorem mollTargetDeriv (G : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen G) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) : deriv (fun x' => deriv (fun y' => Work.FTS.EllSol.EllPkgAux.Hxyc G x' y') θ) (Real.log z) = Work.Spaces.Dz (Work.Spaces.pth G) z θ := by
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  -- the inner `s`-derivative is the plain angular derivative of the datum
  have hinner : (fun x' => deriv (fun y' => Work.FTS.EllSol.EllPkgAux.Hxyc G x' y') θ)
      = fun x' => Work.Spaces.pth G (Real.exp x') θ := by
    funext x'
    exact deriv_Qext_slice (G := G) (w := Real.exp x') hθ0 hθ1
  rw [hinner]
  -- chain rule: `z`-slice of `∂_θG` composed with `Real.exp`, at `x = log z`
  have hF : HasDerivAt (fun w : ℝ => Work.Spaces.pth G w θ)
      (Work.Spaces.pz (Work.Spaces.pth G) z θ) z := hS.pth.hasDerivAt_slice hθ hz
  have hF' : HasDerivAt (fun w : ℝ => Work.Spaces.pth G w θ)
      (Work.Spaces.pz (Work.Spaces.pth G) z θ) (Real.exp (Real.log z)) := by
    rw [Real.exp_log hz]; exact hF
  have hcomp := HasDerivAt.comp (h := Real.exp) (x := Real.log z) hF'
    (Real.hasDerivAt_exp (Real.log z))
  have hderiv : deriv (fun x' => Work.Spaces.pth G (Real.exp x') θ) (Real.log z)
      = Work.Spaces.pz (Work.Spaces.pth G) z θ * Real.exp (Real.log z) := hcomp.deriv
  rw [hderiv, Real.exp_log hz]
  show Work.Spaces.pz (Work.Spaces.pth G) z θ * z = Work.Spaces.Dz (Work.Spaces.pth G) z θ
  rw [Work.Spaces.Dz]
  ring

end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.secondOrderRem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `secondOrderRem`

**The requested statement is false as written.**  The requested lemma is

```
theorem secondOrderRem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} {p : E} (hp : ContDiffAt ℝ 2 f p) :
    ∀ ε > 0, ∃ δ > 0, ∀ ξ : E, ‖ξ‖ < δ →
      ‖f (p + ξ) - f p - (fderiv ℝ f p) ξ - (1 / 2) • ((fderiv ℝ (fderiv ℝ f) p) ξ) ξ‖
        ≤ ε * ‖ξ‖ ^ 2
```

and the problem is the literal `1 / 2`.  Nothing in the statement forces the type of
`1 / 2`, so the elaborator resolves it to `ℕ` and uses the natural-number scalar action
on `F`: `1 / 2 = 0 : ℕ` and `0 • y = 0` for `y : F`.  Hence the third term of the bound
vanishes *definitionally*, and the claim above is the *first order* Peano remainder
bound

  `‖f (p + ξ) - f p - (fderiv ℝ f p) ξ‖ ≤ ε * ‖ξ‖ ^ 2`  (for `‖ξ‖ < δ`),

which is false: take `E = F = ℝ`, `f x = x ^ 2` (a `C^∞` function, so `hp` holds),
`p = 0`, `ε = 1 / 2`.  Then the claim reads `ξ ^ 2 ≤ (1 / 2) * ξ ^ 2` for every `ξ` with
`‖ξ‖ < δ`, which fails for `ξ = δ / 2`.  (Even without computing `fderiv ℝ f 0`, adding
the claims at `ξ` and `-ξ` gives `2 * ξ ^ 2 ≤ ξ ^ 2`.)

A complete, sorry-free formal refutation — including proofs that `(1 / 2) • v = 0` for
every `v : F` and that `fun x : ℝ => x ^ 2` satisfies `ContDiffAt ℝ 2 · 0` — is in
`Submission/Work/FTS/EllSol/EllPkgAux/refute_secondOrderRem.lean` (`not_conclusion`,
`hp_poly`).

The **intended** statement — the second order Taylor (Peano remainder) theorem — is the
same statement with the scalar `1 / 2` read as a real number.  It is true and is proved
below as `secondOrderRem_real`, on top of the general helper `second_order_rem_aux`
(the proof: differentiate the second-order Taylor polynomial and use the mean value
inequality on the ball `closedBall p ‖ξ‖`; the symmetry of the second derivative is used
to identify the derivative of the quadratic term).

Note for consumers: the module currently still contains the requested statement (kept
verbatim, unproved, marked FALSE); importing it and using `secondOrderRem_real` is safe,
as the `sorry` is not in the dependency cone of `secondOrderRem_real`.
-/

namespace Work.FTS.EllSol.EllPkgAux

open Filter

/-- **Taylor's theorem with Peano remainder, to second order**, with the two derivatives
passed explicitly: if `L` is the derivative of `f` at `p`, if `Q` is the second
derivative of `f` at `p` (as a continuous linear map `E →L (E →L F)`), if `Q` is
symmetric (which it is for a `C^2` function) and if `f` is differentiable near `p`,
then

`f (p + ξ) - f p - L ξ - (1 / 2 : ℝ) • ((Q ξ) ξ) = O (‖ξ‖ ^ 2)`.

This is the corrected form of the requested `secondOrderRem`. -/
theorem second_order_rem_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {p : E} {L : E →L[ℝ] F} {Q : E →L[ℝ] (E →L[ℝ] F)}
    (hL : HasFDerivAt f L p) (hQ : HasFDerivAt (fderiv ℝ f) Q p)
    (hsymm : ∀ v w : E, Q v w = Q w v)
    (hev : ∀ᶠ x in nhds p, DifferentiableAt ℝ f x) :
    ∀ ε > 0, ∃ δ > 0, ∀ ξ : E, ‖ξ‖ < δ →
      ‖f (p + ξ) - f p - L ξ - (1 / 2 : ℝ) • ((Q ξ) ξ)‖ ≤ ε * ‖ξ‖ ^ 2 := by
  intro ε hε
  have hQε : ∀ᶠ x in nhds p, ‖fderiv ℝ f x - fderiv ℝ f p - Q (x - p)‖ ≤ ε * ‖x - p‖ :=
    hQ.isLittleO.bound hε
  rcases Metric.mem_nhds_iff.1 hQε with ⟨δ₁, hδ₁pos, hδ₁⟩
  rcases Metric.mem_nhds_iff.1 hev with ⟨δ₂, hδ₂pos, hδ₂⟩
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, ?_⟩
  intro ξ hξ
  have hξ₁ : ‖ξ‖ < δ₁ := lt_of_lt_of_le hξ (min_le_left δ₁ δ₂)
  have hξ₂ : ‖ξ‖ < δ₂ := lt_of_lt_of_le hξ (min_le_right δ₁ δ₂)
  have hLfd : fderiv ℝ f p = L := hL.fderiv
  set K : E → F := fun x => f x - f p - L (x - p) - (1 / 2 : ℝ) • ((Q (x - p)) (x - p))
    with hK
  have hu : ∀ x : E, HasFDerivAt (fun y : E => y - p) (ContinuousLinearMap.id ℝ E) x := by
    intro x
    exact (hasFDerivAt_id (𝕜 := ℝ) x).sub_const p
  have hquad : ∀ x : E,
      HasFDerivAt (fun y : E => (Q (y - p)) (y - p)) ((2 : ℝ) • (Q (x - p))) x := by
    intro x
    have hcomp : HasFDerivAt (fun y : E => Q (y - p)) Q x := by
      have h := (ContinuousLinearMap.hasFDerivAt Q (x := x - p)).comp x (hu x)
      simpa [Function.comp_def] using h
    have h := hcomp.clm_apply (hu x)
    have hflip : Q.flip (x - p) = Q (x - p) := by
      ext v
      rw [ContinuousLinearMap.flip_apply]
      exact hsymm v (x - p)
    convert h using 1
    rw [ContinuousLinearMap.comp_id, hflip, two_smul]
  have hKderiv : ∀ x : E, DifferentiableAt ℝ f x →
      HasFDerivAt K (fderiv ℝ f x - L - Q (x - p)) x := by
    intro x hx
    have h1 : HasFDerivAt (fun y : E => f y - f p) (fderiv ℝ f x) x :=
      hx.hasFDerivAt.sub_const (f p)
    have h2 : HasFDerivAt (fun y : E => L (y - p)) L x := by
      have h := (ContinuousLinearMap.hasFDerivAt L (x := x - p)).comp x (hu x)
      simpa [Function.comp_def] using h
    have h3 : HasFDerivAt (fun y : E => (1 / 2 : ℝ) • ((Q (y - p)) (y - p)))
        ((1 / 2 : ℝ) • ((2 : ℝ) • (Q (x - p)))) x := (hquad x).const_smul (1 / 2 : ℝ)
    rw [hK]
    have hderiv : fderiv ℝ f x - L - (1 / 2 : ℝ) • ((2 : ℝ) • (Q (x - p)))
        = fderiv ℝ f x - L - Q (x - p) := by
      rw [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]
    rw [← hderiv]
    exact (h1.sub h2).sub h3
  have hfdiff : ∀ x ∈ Metric.closedBall p ‖ξ‖, DifferentiableAt ℝ f x := by
    intro x hx
    have hxd : ‖x - p‖ < δ₂ := by
      have h2 := Metric.mem_closedBall.1 hx
      rw [dist_eq_norm] at h2
      exact lt_of_le_of_lt h2 hξ₂
    exact hδ₂ (Metric.mem_ball.2 (by rwa [dist_eq_norm]))
  have hb : ∀ x ∈ Metric.closedBall p ‖ξ‖, ‖fderiv ℝ K x‖ ≤ ε * ‖ξ‖ := by
    intro x hx
    have hxd : ‖x - p‖ < δ₁ := by
      have h2 := Metric.mem_closedBall.1 hx
      rw [dist_eq_norm] at h2
      exact lt_of_le_of_lt h2 hξ₁
    have hb₁ : ‖fderiv ℝ f x - fderiv ℝ f p - Q (x - p)‖ ≤ ε * ‖x - p‖ :=
      hδ₁ (Metric.mem_ball.2 (by rwa [dist_eq_norm]))
    rw [(hKderiv x (hfdiff x hx)).fderiv]
    calc ‖fderiv ℝ f x - L - Q (x - p)‖
        = ‖fderiv ℝ f x - fderiv ℝ f p - Q (x - p)‖ := by rw [hLfd]
      _ ≤ ε * ‖x - p‖ := hb₁
      _ ≤ ε * ‖ξ‖ := by
            refine mul_le_mul_of_nonneg_left ?_ hε.le
            have h2 := Metric.mem_closedBall.1 hx
            rwa [dist_eq_norm] at h2
  have hKdiff : ∀ x ∈ Metric.closedBall p ‖ξ‖, DifferentiableAt ℝ K x :=
    fun x hx => (hKderiv x (hfdiff x hx)).differentiableAt
  have hpp : p ∈ Metric.closedBall p ‖ξ‖ := Metric.mem_closedBall_self (norm_nonneg ξ)
  have hpξ : p + ξ ∈ Metric.closedBall p ‖ξ‖ := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp
  have hMVT : ‖K (p + ξ) - K p‖ ≤ (ε * ‖ξ‖) * ‖ξ‖ := by
    have h := (convex_closedBall p ‖ξ‖).norm_image_sub_le_of_norm_fderiv_le
      hKdiff hb hpp hpξ
    rwa [add_sub_cancel_left] at h
  have hKp : K p = 0 := by
    rw [hK]
    change f p - f p - L (p - p) - (1 / 2 : ℝ) • ((Q (p - p)) (p - p)) = 0
    simp
  have hKξ : K (p + ξ) = f (p + ξ) - f p - L ξ - (1 / 2 : ℝ) • ((Q ξ) ξ) := by
    rw [hK]
    change f (p + ξ) - f p - L ((p + ξ) - p)
        - (1 / 2 : ℝ) • ((Q ((p + ξ) - p)) ((p + ξ) - p))
      = f (p + ξ) - f p - L ξ - (1 / 2 : ℝ) • ((Q ξ) ξ)
    rw [add_sub_cancel_left]
  calc ‖f (p + ξ) - f p - L ξ - (1 / 2 : ℝ) • ((Q ξ) ξ)‖
      = ‖K (p + ξ) - K p‖ := by rw [hKξ, hKp, sub_zero]
    _ ≤ (ε * ‖ξ‖) * ‖ξ‖ := hMVT
    _ = ε * ‖ξ‖ ^ 2 := by ring

/-- **The intended statement**: `secondOrderRem` with the scalar `1 / 2` read as a real
number.  (In the requested statement the literal `1 / 2` is read as `1 / 2 = 0 : ℕ`,
which makes the statement false; see the module comment.) -/
theorem secondOrderRem_real {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} {p : E} (hp : ContDiffAt ℝ 2 f p) :
    ∀ ε > 0, ∃ δ > 0, ∀ ξ : E, ‖ξ‖ < δ →
      ‖f (p + ξ) - f p - (fderiv ℝ f p) ξ - (1 / 2 : ℝ) • ((fderiv ℝ (fderiv ℝ f) p) ξ) ξ‖
        ≤ ε * ‖ξ‖ ^ 2 := by
  refine second_order_rem_aux (L := fderiv ℝ f p)
    (Q := fderiv ℝ (fderiv ℝ f) p) ?_ ?_ ?_ ?_
  · exact (hp.differentiableAt (by simp)).hasFDerivAt
  · exact (ContDiffAt.differentiableAt (hp.fderiv_right (m := 1) (by norm_num))
      (by simp)).hasFDerivAt
  · intro v w
    exact hp.isSymmSndFDerivAt (by simp) v w
  · exact (hp.eventually (by simp)).mono fun x hx => hx.differentiableAt (by simp)


end Work.FTS.EllSol.EllPkgAux
end
-- ===== merged: Submission.Work.FTS.EllSol.FlatFT.flatNiceSlices =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.FlatFT

open MeasureTheory Set Filter
open scoped Real Topology
open Work.Spaces

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The open strip `ℝ × (0,π/2)` on which `NiceFlat` data are smooth. -/
abbrev nfStrip : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)

theorem nfStrip_isOpen : IsOpen nfStrip := isOpen_univ.prod isOpen_Ioo

variable {g : ℝ → ℝ → ℝ}

/-! ## The uniform support in `t` -/

theorem niceFlat_supp (hg : NiceFlat g) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t θ : ℝ, M < |t| → g t θ = 0 := by
  obtain ⟨-, -, -, N, hN⟩ := hg
  exact ⟨max N 0, le_max_right _ _, fun t θ ht => hN t θ (lt_of_le_of_lt (le_max_left _ _) ht)⟩

theorem pth_eq_zero_of_forall {t θ : ℝ} (h : ∀ θ' : ℝ, g t θ' = 0) : pth g t θ = 0 := by
  simp only [pth]
  rw [show (fun θ' : ℝ => g t θ') = fun _ => (0 : ℝ) from funext h]
  simp

theorem pth_pth_eq_zero_of_forall {t θ : ℝ} (h : ∀ θ' : ℝ, pth g t θ' = 0) :
    pth (pth g) t θ = 0 := by
  simp only [pth] at h ⊢
  rw [show (fun θ' : ℝ => deriv (fun θ'' : ℝ => g t θ'') θ') = fun _ => (0 : ℝ) from funext h]
  simp

/-- The `t`-slice of a `NiceFlat` datum, as a complex-valued function, has compact support. -/
theorem niceFlat_hasCompactSupport (hg : NiceFlat g) (θ : ℝ) :
    HasCompactSupport (fun t : ℝ => (g t θ : ℂ)) := by
  obtain ⟨M, -, hM⟩ := niceFlat_supp hg
  refine HasCompactSupport.intro (K := Set.Icc (-M) M) isCompact_Icc (fun t ht => ?_)
  have hMt : M < |t| := not_le.mp fun hle => ht (abs_le.mp hle)
  simp [hM t θ hMt]

theorem niceFlat_hasCompactSupport_pth (hg : NiceFlat g) (θ : ℝ) :
    HasCompactSupport (fun t : ℝ => (pth g t θ : ℂ)) := by
  obtain ⟨M, -, hM⟩ := niceFlat_supp hg
  refine HasCompactSupport.intro (K := Set.Icc (-M) M) isCompact_Icc (fun t ht => ?_)
  have hMt : M < |t| := not_le.mp fun hle => ht (abs_le.mp hle)
  simp [pth_eq_zero_of_forall (fun θ' => hM t θ' hMt)]

theorem niceFlat_hasCompactSupport_pthpth (hg : NiceFlat g) (θ : ℝ) :
    HasCompactSupport (fun t : ℝ => (pth (pth g) t θ : ℂ)) := by
  obtain ⟨M, -, hM⟩ := niceFlat_supp hg
  refine HasCompactSupport.intro (K := Set.Icc (-M) M) isCompact_Icc (fun t ht => ?_)
  have hMt : M < |t| := not_le.mp fun hle => ht (abs_le.mp hle)
  simp [pth_pth_eq_zero_of_forall (fun θ' => pth_eq_zero_of_forall (fun θ'' => hM t θ'' hMt))]

/-! ## Smoothness of the `t`-slices -/

theorem contDiff_ofReal_comp {f : ℝ → ℝ} {n : ℕ} (h : ContDiff ℝ n f) :
    ContDiff ℝ n (fun t : ℝ => (f t : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp h

theorem niceFlat_slice_contDiff (hg : NiceFlat g) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    {n : ℕ} (hn : n ≤ 2) : ContDiff ℝ n (fun t : ℝ => g t θ) := by
  have hn' : (n : WithTop ℕ∞) ≤ (2 : WithTop ℕ∞) := by exact_mod_cast hn
  have h := (hg.1.of_le hn').comp (t := nfStrip) (f := fun t : ℝ => (t, θ)) (s := Set.univ)
    ((show ContDiff ℝ n (fun t : ℝ => (t, θ)) from by fun_prop).contDiffOn (s := Set.univ))
    (fun t _ => ⟨trivial, hθ⟩)
  exact contDiffOn_univ.1 (by simpa [Function.comp_def, Function.uncurry] using h)

theorem niceFlat_slice_pth_contDiff (hg : NiceFlat g) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) {n : ℕ} (hn : n ≤ 1) :
    ContDiff ℝ n (fun t : ℝ => pth g t θ) := by
  have h1 : ContDiffOn ℝ 1 (Function.uncurry (pth g)) nfStrip :=
    pth_contDiffOn_succ nfStrip_isOpen hg.1
  have hn' : (n : WithTop ℕ∞) ≤ (1 : WithTop ℕ∞) := by exact_mod_cast hn
  have h := (h1.of_le hn').comp (t := nfStrip) (f := fun t : ℝ => (t, θ)) (s := Set.univ)
    ((show ContDiff ℝ n (fun t : ℝ => (t, θ)) from by fun_prop).contDiffOn (s := Set.univ))
    (fun t _ => ⟨trivial, hθ⟩)
  exact contDiffOn_univ.1 (by simpa [Function.comp_def, Function.uncurry] using h)

theorem niceFlat_slice_pthpth_contDiff (hg : NiceFlat g) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContDiff ℝ 0 (fun t : ℝ => pth (pth g) t θ) := by
  have h1 : ContDiffOn ℝ 1 (Function.uncurry (pth g)) nfStrip :=
    pth_contDiffOn_succ nfStrip_isOpen hg.1
  have h2 : ContDiffOn ℝ 0 (Function.uncurry (pth (pth g))) nfStrip :=
    pth_contDiffOn_succ nfStrip_isOpen h1
  have h := h2.comp (t := nfStrip) (f := fun t : ℝ => (t, θ)) (s := Set.univ)
    ((show ContDiff ℝ 0 (fun t : ℝ => (t, θ)) from by fun_prop).contDiffOn (s := Set.univ))
    (fun t _ => ⟨trivial, hθ⟩)
  exact contDiffOn_univ.1 (by simpa [Function.comp_def, Function.uncurry] using h)

/-! ## The derivative rule for the coercions -/

theorem deriv_ofReal_comp {f : ℝ → ℝ} {x : ℝ} (hd : DifferentiableAt ℝ f x) :
    deriv (fun t : ℝ => (f t : ℂ)) x = ((deriv f x : ℝ) : ℂ) :=
  (hd.hasDerivAt.ofReal_comp).deriv

theorem normSq_ofReal' (x : ℝ) : ‖(x : ℂ)‖ ^ 2 = x ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_ofReal]
  ring

theorem slice_eq_slice1' (g : ℝ → ℝ → ℝ) (ξ θ : ℝ) :
    slice g ξ θ = slice1 (fun t : ℝ => (g t θ : ℂ)) ξ := rfl

theorem slice_eq_zero (hg : NiceFlat g) (ξ : ℝ) : slice g ξ 0 = 0 := by
  simp only [slice]
  rw [show (fun t : ℝ => (g t 0 : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * ξ * t)))
      = fun _ => (0 : ℂ) from funext fun t => by rw [hg.2.1 t, Complex.ofReal_zero, zero_mul]]
  simp

theorem slice_eq_zero_pi (hg : NiceFlat g) (ξ : ℝ) : slice g ξ (Real.pi / 2) = 0 := by
  simp only [slice]
  rw [show (fun t : ℝ => (g t (Real.pi / 2) : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * ξ * t)))
      = fun _ => (0 : ℂ) from funext fun t => by rw [hg.2.2.1 t, Complex.ofReal_zero, zero_mul]]
  simp

/-! ## The Plancherel identities at a fixed angle -/





/-- `∫_ξ ‖Φ_ξ''(θ)‖² = ∫_t (∂_θ²g(t,θ))²`. -/
theorem plancherel_slice_pthpth (hg : NiceFlat g) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ∫ ξ : ℝ, ‖deriv (fun θ' => deriv (fun θ'' => slice g ξ θ'') θ') θ‖ ^ 2
      = ∫ t : ℝ, (pth (pth g) t θ) ^ 2 := by
  have hs0 := niceFlat_slice_pthpth_contDiff hg hθ
  have hcont : Continuous (fun t : ℝ => (pth (pth g) t θ : ℂ)) :=
    (contDiff_ofReal_comp hs0).continuous
  have hsupp := niceFlat_hasCompactSupport_pthpth hg θ
  calc ∫ ξ : ℝ, ‖deriv (fun θ' => deriv (fun θ'' => slice g ξ θ'') θ') θ‖ ^ 2
      = ∫ ξ : ℝ, ‖slice1 (fun t : ℝ => (pth (pth g) t θ : ℂ)) ξ‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards with ξ
        have hev : (fun θ' => deriv (fun θ'' => slice g ξ θ'') θ') =ᶠ[𝓝 θ]
            (fun θ' => slice (pth g) ξ θ') := by
          filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
          exact (slice_hasDerivAt g hg ξ hθ').1.deriv
        rw [hev.deriv_eq, (slice_hasDerivAt g hg ξ hθ).2.deriv, slice_eq_slice1']
    _ = ∫ t : ℝ, ‖(pth (pth g) t θ : ℂ)‖ ^ 2 := plancherelSlice1 _ hcont hsupp
    _ = ∫ t : ℝ, (pth (pth g) t θ) ^ 2 :=
        integral_congr_ae (Filter.Eventually.of_forall fun t =>
          normSq_ofReal' (pth (pth g) t θ))

end

end Work.FTS.EllSol.FlatFT
end
-- ===== merged: Submission.Work.FTS.EllSol.FlatFT.plancherelDeriv2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.EllSol.FlatFT


end Work.FTS.EllSol.FlatFT
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.TraceEngine.sliceAgmonOpenCoreExplicit =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The open-class angular Agmon inequality, with the constants made explicit

`sliceAgmonOpenCoreExplicit` is the explicit-constant form of the one-dimensional weighted Agmon
estimate `Work.EllipticEst.Core.i0Aux.sliceAgmonOpenCore`:

  `(1/200) ∫_{Iθ} (f')² σ  ≤  - ∫_{Iθ} f f'' σ + 2η ∫_{Iθ} f² σ`,   `σ = thEta = sin(2θ)^{-η}`,

for `f` of class `C²` on the open interval `(0, π/2)` whose two traces vanish and whose three
weighted energies are finite.

The existential version only records the *existence* of a pair `(c, C)`; here the pair is pinned
to the values `(1/200, 2η)` that actually occur in the proof (and which are the ones the trace
engine consumes).

The argument is the one of `sliceAgmonOpenCore`: the primitive `Φ` of `SliceAgmonOpen.Defs`, the
endpoint rate `EndpointRate`, the sharp weighted Hardy inequality `SharpHardyOpenAux`, the two
"small value" lemmas `PhiGeNearZero`/`PhiLeNearPi` producing two sequences of interior points
along which `Φ` is small, the convergence of the sub-interval integrals `tendsto_subinterval`, and
finally the arithmetic lemma `SliceAgmonOpen.agFinal`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5.TraceEngine

-- (verbatim from `Work.EllipticEst.Core.i0Aux.sliceAgmonOpenCore`)
/-- The integrand of the integration-by-parts identity `Work.EllipticEst.Core.i0Aux.PhiIdentity`. -/
private def agIntegrand (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x
    + f x * deriv (deriv f) x * Work.FTS.EllipticEst.thEta x
    - 2 * Work.Spaces.eta * (f x) ^ 2 * Work.FTS.EllipticEst.thEta x
    - 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * (f x) ^ 2
        * (Real.cos (2 * x)) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))


/-- Splitting the integral of a linear combination into the combination of the integrals. -/
private theorem integral_decomp {F G H K : ℝ → ℝ} {c d : ℝ} {s : Set ℝ}
    (hF : MeasureTheory.IntegrableOn F s) (hG : MeasureTheory.IntegrableOn G s)
    (hH : MeasureTheory.IntegrableOn (fun x => c * H x) s)
    (hK : MeasureTheory.IntegrableOn (fun x => d * K x) s) :
    (∫ x in s, (F x + G x - c * H x - d * K x))
      = (∫ x in s, F x) + (∫ x in s, G x) - c * (∫ x in s, H x)
        - d * (∫ x in s, K x) := by
  have h1 : MeasureTheory.IntegrableOn (fun x => F x + G x) s := hF.add hG
  have h2 : MeasureTheory.IntegrableOn (fun x => F x + G x - c * H x) s := h1.sub hH
  have e1 : (∫ x in s, (F x + G x - c * H x - d * K x))
      = (∫ x in s, (F x + G x - c * H x)) - (∫ x in s, d * K x) :=
    MeasureTheory.integral_sub h2 hK
  have e2 : (∫ x in s, (F x + G x - c * H x))
      = (∫ x in s, (F x + G x)) - (∫ x in s, c * H x) :=
    MeasureTheory.integral_sub h1 hH
  have e3 : (∫ x in s, (F x + G x)) = (∫ x in s, F x) + (∫ x in s, G x) :=
    MeasureTheory.integral_add hF hG
  have e4 : (∫ x in s, c * H x) = c * (∫ x in s, H x) :=
    MeasureTheory.integral_const_mul c H
  have e5 : (∫ x in s, d * K x) = d * (∫ x in s, K x) :=
    MeasureTheory.integral_const_mul d K
  rw [e1, e2, e3, e4, e5]

/-- **The angular Agmon inequality of the open slice class, with explicit constants.** -/
theorem sliceAgmonOpenCoreExplicit (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (h0 : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (h1 : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hA : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hN : MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hP : MeasureTheory.IntegrableOn (fun θ : ℝ => f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) :
    (1 / 200) * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ - (∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ)
        + 2 * Work.Spaces.eta * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  -- ## the open interval
  have hmemT : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hAoo : MeasureTheory.IntegrableOn
      (fun x : ℝ => (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      (Set.Ioo 0 (Real.pi / 2)) := hA.mono_set hmemT
  have hNoo : MeasureTheory.IntegrableOn
      (fun x : ℝ => (f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      (Set.Ioo 0 (Real.pi / 2)) := hN.mono_set hmemT
  have hPoo : MeasureTheory.IntegrableOn
      (fun x : ℝ => f x * deriv (deriv f) x * Work.FTS.EllipticEst.thEta x)
      (Set.Ioo 0 (Real.pi / 2)) := hP.mono_set hmemT
  -- ## the two imported inputs
  obtain ⟨hrate0, hrate1⟩ := Work.EllipticEst.Core.i0Aux.EndpointRate hf h0 h1 hA
  obtain ⟨hHqintIθ, hHardyIθ⟩ := Work.EllipticEst.Core.i0Aux.SliceAgmonAux.sharpHardyOpenAux hf hrate0 hrate1 hA
  have hHqint : MeasureTheory.IntegrableOn
      (fun x : ℝ => (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
      (Set.Ioo 0 (Real.pi / 2)) := hHqintIθ.mono_set hmemT
  have hcos : ContinuousOn (fun x : ℝ => (Real.cos (2 * x)) ^ 2)
      (Set.Icc 0 (Real.pi / 2)) :=
    (((Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn).pow 2)
  have hJIoo_int : MeasureTheory.IntegrableOn
      (fun x : ℝ => (f x) ^ 2 * (Real.cos (2 * x)) ^ 2
        * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
      (Set.Ioo 0 (Real.pi / 2)) := by
    have h0' : MeasureTheory.IntegrableOn
        (fun x : ℝ => ((f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
          * (Real.cos (2 * x)) ^ 2)
        (Set.Ioo 0 (Real.pi / 2)) :=
      hHqint.mul_continuousOn_of_subset hcos measurableSet_Ioo isCompact_Icc
        (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
    exact h0'.congr_fun (fun x hx => by ring) measurableSet_Ioo
  have hG3int : MeasureTheory.IntegrableOn
      (fun x : ℝ => (2 * Work.Spaces.eta) * ((f x) ^ 2 * Work.FTS.EllipticEst.thEta x))
      (Set.Ioo 0 (Real.pi / 2)) := hNoo.const_mul (2 * Work.Spaces.eta)
  have hG4int : MeasureTheory.IntegrableOn
      (fun x : ℝ => (2 * Work.Spaces.eta * (1 + Work.Spaces.eta))
        * ((f x) ^ 2 * (Real.cos (2 * x)) ^ 2
          * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hJIoo_int.const_mul (2 * Work.Spaces.eta * (1 + Work.Spaces.eta))
  have hGint : MeasureTheory.IntegrableOn (agIntegrand f) (Set.Ioo 0 (Real.pi / 2)) := by
    have hsrc : MeasureTheory.IntegrableOn
        (fun x : ℝ => ((deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x
            + f x * deriv (deriv f) x * Work.FTS.EllipticEst.thEta x
            - (2 * Work.Spaces.eta) * ((f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
            - (2 * Work.Spaces.eta * (1 + Work.Spaces.eta))
                * ((f x) ^ 2 * (Real.cos (2 * x)) ^ 2
                  * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))))
        (Set.Ioo 0 (Real.pi / 2)) :=
      ((hAoo.add hPoo).sub hG3int).sub hG4int
    exact hsrc.congr_fun (fun x hx => by simp only [agIntegrand]; ring) measurableSet_Ioo
  -- ## identifying the `Ioo`-integrals with the `Iθ`-integrals
  have hAoo_eq : (∫ x in Set.Ioo 0 (Real.pi / 2),
        (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      = (∫ x in Work.Spaces.Iθ, (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x) :=
    MeasureTheory.setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Icc
  have hNoo_eq : (∫ x in Set.Ioo 0 (Real.pi / 2),
        (f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      = (∫ x in Work.Spaces.Iθ, (f x) ^ 2 * Work.FTS.EllipticEst.thEta x) :=
    MeasureTheory.setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Icc
  have hPoo_eq : (∫ x in Set.Ioo 0 (Real.pi / 2),
        f x * deriv (deriv f) x * Work.FTS.EllipticEst.thEta x)
      = (∫ x in Work.Spaces.Iθ, f x * deriv (deriv f) x * Work.FTS.EllipticEst.thEta x) :=
    MeasureTheory.setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Icc
  have hHqoo_eq : (∫ x in Set.Ioo 0 (Real.pi / 2),
        (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
      = (∫ x in Work.Spaces.Iθ,
          (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))) :=
    MeasureTheory.setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Icc
  have hAnn : 0 ≤ (∫ x in Set.Ioo 0 (Real.pi / 2),
      (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo
      (fun x hx => mul_nonneg (sq_nonneg _)
        (Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt hx.1, le_of_lt hx.2⟩))
  -- ## the two sequences of interior points where `Work.EllipticEst.Core.i0Aux.Phi` is small
  choose a ha using fun n : ℕ =>
    Work.EllipticEst.Core.i0Aux.SliceAgmonOpen.PhiGeNearZero hf hrate0 (1 / ((n : ℝ) + 1)) (1 / ((n : ℝ) + 1))
      (by positivity) (by positivity)
  choose b hb using fun n : ℕ =>
    Work.EllipticEst.Core.i0Aux.SliceAgmonOpen.PhiLeNearPi hf hrate1 (Real.pi / 2 - 1 / ((n : ℝ) + 1))
      (1 / ((n : ℝ) + 1))
      (by
        have h : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith) (by positivity)
  have ha_pos : ∀ n : ℕ, 0 < a n := fun n => (ha n).1.1
  have ha_lt : ∀ n : ℕ, a n < 1 / ((n : ℝ) + 1) := fun n => (ha n).1.2
  have ha_bd : ∀ n : ℕ, -(1 / ((n : ℝ) + 1)) ≤ Work.EllipticEst.Core.i0Aux.Phi f (a n) := fun n => (ha n).2
  have hb_gt : ∀ n : ℕ, Real.pi / 2 - 1 / ((n : ℝ) + 1) < b n := fun n => (hb n).1.1
  have hb_lt : ∀ n : ℕ, b n < Real.pi / 2 := fun n => (hb n).1.2
  have hb_bd : ∀ n : ℕ, Work.EllipticEst.Core.i0Aux.Phi f (b n) ≤ 1 / ((n : ℝ) + 1) := fun n => (hb n).2
  have hratio : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) := by
    have hnat : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)) Filter.atTop Filter.atTop :=
      tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
    have h2 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hnat
    simpa [one_div] using h2
  have ha_tend : Filter.Tendsto a Filter.atTop (nhds 0) :=
    squeeze_zero' (Eventually.of_forall (fun n => le_of_lt (ha_pos n)))
      (Eventually.of_forall (fun n => le_of_lt (ha_lt n))) hratio
  have ha_within : Filter.Tendsto a Filter.atTop (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨ha_tend, Eventually.of_forall (fun n => ha_pos n)⟩
  have hbsub : Filter.Tendsto (fun n : ℕ => Real.pi / 2 - b n) Filter.atTop (nhds 0) :=
    squeeze_zero' (Eventually.of_forall (fun n => by linarith [hb_lt n]))
      (Eventually.of_forall (fun n => by linarith [hb_gt n])) hratio
  have hb_tend : Filter.Tendsto b Filter.atTop (nhds (Real.pi / 2)) := by
    have h2 : Filter.Tendsto (fun n : ℕ => Real.pi / 2 - (Real.pi / 2 - b n))
        Filter.atTop (nhds (Real.pi / 2 - 0)) := tendsto_const_nhds.sub hbsub
    have h3 : (fun n : ℕ => Real.pi / 2 - (Real.pi / 2 - b n)) = b := by
      funext n; ring
    rw [h3] at h2
    simpa using h2
  have hb_within : Filter.Tendsto b Filter.atTop
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hb_tend, Eventually.of_forall (fun n => hb_lt n)⟩
  have hanb : ∀ n : ℕ, 1 ≤ n → a n < b n := by
    intro n hn
    have h1 := ha_lt n
    have h2 := hb_gt n
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have h4 : 2 * (1 / ((n : ℝ) + 1)) ≤ Real.pi / 2 := by
      nlinarith [hle, Real.pi_gt_three]
    linarith
  have hab : ∀ᶠ n : ℕ in Filter.atTop, a n < b n :=
    Filter.eventually_atTop.mpr ⟨1, fun n hn => hanb n hn⟩
  -- ## `Work.EllipticEst.Core.i0Aux.PhiIdentity` along the sequences
  have hPhi_eq : ∀ᶠ n : ℕ in Filter.atTop,
      (∫ x in Set.Ioo (a n) (b n), agIntegrand f x) = Work.EllipticEst.Core.i0Aux.Phi f (b n) - Work.EllipticEst.Core.i0Aux.Phi f (a n) := by
    filter_upwards [hab] with n hn
    have hh : Work.EllipticEst.Core.i0Aux.Phi f (b n) - Work.EllipticEst.Core.i0Aux.Phi f (a n)
        = ∫ x in Set.Ioo (a n) (b n), agIntegrand f x := by
      rw [Work.EllipticEst.Core.i0Aux.PhiIdentity hf (ha_pos n) (le_of_lt hn) (hb_lt n),
        intervalIntegral.integral_of_le (le_of_lt hn),
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      simp only [agIntegrand]
    exact hh.symm
  have hGtend := Work.EllipticEst.Core.i0Aux.SliceAgmonOpen.tendsto_subinterval hGint ha_within hb_within hab
  have hPhi_tend : Filter.Tendsto (fun n : ℕ => Work.EllipticEst.Core.i0Aux.Phi f (b n) - Work.EllipticEst.Core.i0Aux.Phi f (a n)) Filter.atTop
      (nhds (∫ x in Set.Ioo 0 (Real.pi / 2), agIntegrand f x)) :=
    Filter.Tendsto.congr' hPhi_eq hGtend
  have hPhi_bd : ∀ n : ℕ, Work.EllipticEst.Core.i0Aux.Phi f (b n) - Work.EllipticEst.Core.i0Aux.Phi f (a n) ≤ 2 * (1 / ((n : ℝ) + 1)) := by
    intro n; linarith [hb_bd n, ha_bd n]
  have hPhi_lim : Filter.Tendsto (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1))) Filter.atTop
      (nhds 0) := by
    have h := hratio.const_mul (2 : ℝ)
    simpa using h
  have hLraw : (∫ x in Set.Ioo 0 (Real.pi / 2), agIntegrand f x) ≤ 0 :=
    le_of_tendsto_of_tendsto hPhi_tend hPhi_lim (Eventually.of_forall hPhi_bd)
  -- ## expanding the limit integral
  have hG_decomp : (∫ x in Set.Ioo 0 (Real.pi / 2), agIntegrand f x)
      = (∫ x in Set.Ioo 0 (Real.pi / 2), (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
        + (∫ x in Set.Ioo 0 (Real.pi / 2),
            f x * deriv (deriv f) x * Work.FTS.EllipticEst.thEta x)
        - (2 * Work.Spaces.eta)
          * (∫ x in Set.Ioo 0 (Real.pi / 2),
              (f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
        - (2 * Work.Spaces.eta * (1 + Work.Spaces.eta))
          * (∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 * (Real.cos (2 * x)) ^ 2
              * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))) := by
    rw [show (∫ x in Set.Ioo 0 (Real.pi / 2), agIntegrand f x)
        = ∫ x in Set.Ioo 0 (Real.pi / 2),
            ((deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x
              + f x * deriv (deriv f) x * Work.FTS.EllipticEst.thEta x
              - (2 * Work.Spaces.eta) * ((f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
              - (2 * Work.Spaces.eta * (1 + Work.Spaces.eta))
                  * ((f x) ^ 2 * (Real.cos (2 * x)) ^ 2
                    * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))) from by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      simp only [agIntegrand]
      ring]
    exact integral_decomp hAoo hPoo hG3int hG4int
  -- ## the sharp Hardy bound on the `cos²`-weighted integral
  have hJle' : (1 + Work.Spaces.eta) ^ 2
        * (∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 * (Real.cos (2 * x)) ^ 2
            * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
      ≤ (∫ x in Set.Ioo 0 (Real.pi / 2),
          (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x) := by
    have h1 : (∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 * (Real.cos (2 * x)) ^ 2
          * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
        ≤ (∫ x in Set.Ioo 0 (Real.pi / 2),
            (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))) := by
      refine MeasureTheory.setIntegral_mono_on (hf := hJIoo_int) (hg := hHqint)
        measurableSet_Ioo ?_
      intro x hx
      have hs : 0 ≤ (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)) :=
        Real.rpow_nonneg (le_of_lt (Work.EllipticEst.Core.i0Aux.sin_two_pos hx)) _
      calc (f x) ^ 2 * (Real.cos (2 * x)) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))
          = (f x) ^ 2 * ((Real.cos (2 * x)) ^ 2
              * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))) := by ring
        _ ≤ (f x) ^ 2 * (1 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (Real.cos_sq_le_one (2 * x)) hs) (sq_nonneg _)
        _ = (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)) := by ring
    have h2 : (1 + Work.Spaces.eta) ^ 2
          * (∫ x in Set.Ioo 0 (Real.pi / 2),
              (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
        = (1 + Work.Spaces.eta) ^ 2
          * (∫ x in Work.Spaces.Iθ,
              (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))) :=
      congrArg (fun y => (1 + Work.Spaces.eta) ^ 2 * y) hHqoo_eq
    have h3 : (1 + Work.Spaces.eta) ^ 2
          * (∫ x in Work.Spaces.Iθ,
              (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
        ≤ (∫ x in Work.Spaces.Iθ, (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x) :=
      hHardyIθ
    have h4 : (∫ x in Work.Spaces.Iθ, (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
        = (∫ x in Set.Ioo 0 (Real.pi / 2),
            (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x) := hAoo_eq.symm
    calc (1 + Work.Spaces.eta) ^ 2
          * (∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 * (Real.cos (2 * x)) ^ 2
              * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
        ≤ (1 + Work.Spaces.eta) ^ 2
          * (∫ x in Set.Ioo 0 (Real.pi / 2),
              (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (1 + Work.Spaces.eta) ^ 2
          * (∫ x in Work.Spaces.Iθ,
              (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))) := h2
      _ ≤ (∫ x in Work.Spaces.Iθ, (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x) := h3
      _ = (∫ x in Set.Ioo 0 (Real.pi / 2),
            (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x) := h4
  -- ## the final arithmetic
  have hnum : (1 / 200)
        * (∫ x in Set.Ioo 0 (Real.pi / 2),
            (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      + (∫ x in Set.Ioo 0 (Real.pi / 2),
          f x * deriv (deriv f) x * Work.FTS.EllipticEst.thEta x)
      ≤ 2 * Work.Spaces.eta
        * (∫ x in Set.Ioo 0 (Real.pi / 2),
            (f x) ^ 2 * Work.FTS.EllipticEst.thEta x) :=
    Work.EllipticEst.Core.i0Aux.SliceAgmonOpen.agFinal
      (A := ∫ x in Set.Ioo 0 (Real.pi / 2),
        (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      (P := ∫ x in Set.Ioo 0 (Real.pi / 2),
        f x * deriv (deriv f) x * Work.FTS.EllipticEst.thEta x)
      (N := ∫ x in Set.Ioo 0 (Real.pi / 2),
        (f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      (J := ∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 * (Real.cos (2 * x)) ^ 2
        * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
      (eta := Work.Spaces.eta) Work.Spaces.eta_pos
      (by norm_num [Work.Spaces.eta]) hAnn
      (by linarith [hLraw, hG_decomp]) hJle'
  rw [hAoo_eq, hNoo_eq, hPoo_eq] at hnum
  linarith [hnum]

end Work.FTS.EllSol.PkgK5.TraceEngine
end
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.TraceEngine.slotBounds =====
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
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! # `TraceEngine.slotBounds`

The three slots of the trace engine: the weighted `L²`-masses of `D_z(D_z^rV)`,
`∂_θ²(D_z^rV)` and `D_z²(D_z^rV) + b·D_z(D_z^rV)` (`b z = (z-3)/(1+z)`, `|b| ≤ 3` on `Iz`)
are honest on `Iz ×ˢ Iθ` and bounded by the corresponding `ℋ^k`-norms.

The first two slots are `Work.FTS.EllSol.PkgK5.TraceEngine.slotAux_slotZ_prod` and
`slotAux_slotT_prod`; the third is the sum of the `D_z²`-slot (`slotAux_slotD2_prod`) and the
`D_z`-slot, combined by the pointwise convexity `(X+bY)² ≤ 2X² + 18Y²`
(`Work.Blocks.sq_add_b_mul_sq_le`, `Work.Blocks.abs_bcoef_le`). -/

theorem slotBounds {k : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V)
    (hdd : Work.Spaces.HkMem α k (Work.Spaces.DzIter 2 V))
    (htt : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V))
    (hd : Work.Spaces.HkMem α k (Work.Spaces.Dz V))
    (r : ℕ) (hr : r ≤ k) :
    (MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ∧ (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
          * Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
        ≤ Work.Spaces.HkSq α k (Work.Spaces.Dz V))
    ∧ (MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ∧ (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
          * Work.FTS.EllipticEst.thEta p.2
          * (Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
        ≤ Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V))
    ∧ (MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2
            + ((p.1 - 3) / (1 + p.1)) * Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ∧ (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
          * Work.FTS.EllipticEst.thEta p.2
          * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2
              + ((p.1 - 3) / (1 + p.1)) * Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
        ≤ 18 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
          + 18 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)) := by
  have hZ := slotAux_slotZ_prod (k := k) (r := r) (α := α) (V := V) hV hd hr
  have hT := slotAux_slotT_prod (k := k) (r := r) (α := α) (V := V) hV htt hr
  have hD2 := slotAux_slotD2_prod (k := k) (r := r) (α := α) (V := V) hV hdd hr
  -- the third slot: continuity of the combined integrand on the open quadrant
  have hcont3 : ContinuousOn (Function.uncurry (fun z θ : ℝ =>
      (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ
        * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) z θ
            + ((z - 3) / (1 + z)) * Work.Spaces.Dz (Work.Spaces.DzIter r V) z θ) ^ 2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hX : ContinuousOn
        (fun p : ℝ × ℝ => Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := ((hV.DzIter r).DzIter 2).continuousOn
    have hY : ContinuousOn
        (fun p : ℝ × ℝ => Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := ((hV.DzIter r).Dz).continuousOn
    have hb : ContinuousOn (fun p : ℝ × ℝ => (p.1 - 3) / (1 + p.1))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      refine ContinuousOn.div (continuousOn_fst.sub continuousOn_const)
        (continuousOn_const.add continuousOn_fst) ?_
      intro p hp
      have hp1 : (0 : ℝ) < p.1 := hp.1
      exact ne_of_gt (by linarith)
    refine (slotAux_continuousOn_w2_thEta.mul ((hX.add (hb.mul hY)).pow 2)).congr ?_
    intro p hp
    rfl
  -- the pointwise convexity
  have hpt3 : ∀ p ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
      (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2
            + ((p.1 - 3) / (1 + p.1)) * Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2
      ≤ 2 * ((Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
            * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
        + 18 * ((Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
            * (Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2) := by
    intro p hp
    obtain ⟨hz, hθ⟩ := Set.mem_prod.mp hp
    have hS : 0 ≤ Work.FTS.EllipticEst.thEta p.2 :=
      Work.EllipticEst.Core.i0Aux.thEta_nonneg_Iθ hθ
    have hWnn : 0 ≤ (Work.Spaces.w p.1) ^ 2 := sq_nonneg _
    have hb : |(p.1 - 3) / (1 + p.1)| ≤ 3 := Work.Blocks.abs_bcoef_le p.1 hz
    have hkey := Work.Blocks.sq_add_b_mul_sq_le
      (X := Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2)
      (Y := Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2)
      (b := (p.1 - 3) / (1 + p.1)) hb
    have hmul := mul_le_mul_of_nonneg_left hkey (mul_nonneg hWnn hS)
    calc (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
          * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2
              + ((p.1 - 3) / (1 + p.1)) * Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2
        = ((Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2)
          * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2
              + ((p.1 - 3) / (1 + p.1))
                * Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2 := by
          ring
      _ ≤ ((Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2)
            * (2 * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2) ^ 2
              + 18 * (Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2) := hmul
      _ = 2 * ((Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
            * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
          + 18 * ((Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
            * (Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2) := by ring
  have hdom : IntegrableOn (fun p : ℝ × ℝ => 2 * ((Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2
      * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
      + 18 * ((Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
      * (Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    (hD2.1.const_mul 2).add (hZ.1.const_mul 18)
  have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2
      * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2
          + ((p.1 - 3) / (1 + p.1)) * Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
      ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    rw [slotAux_volume_restrict_dom]
    exact Work.Spaces.aesm_of_continuousOn_Qd _ hcont3
  have hInt3 : IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2
      * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2
          + ((p.1 - 3) / (1 + p.1)) * Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.mono' hdom haesm ?_
    refine MeasureTheory.ae_restrict_of_forall_mem slotAux_measurableSet_dom (fun p hp => ?_)
    obtain ⟨hz, hθ⟩ := Set.mem_prod.mp hp
    have hnn3 : 0 ≤ (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2
            + ((p.1 - 3) / (1 + p.1)) * Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2 :=
      mul_nonneg (mul_nonneg (sq_nonneg _)
        (Work.EllipticEst.Core.i0Aux.thEta_nonneg_Iθ hθ)) (sq_nonneg _)
    rw [Real.norm_of_nonneg hnn3]
    exact hpt3 p hp
  have hC3 : (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2
      * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2
          + ((p.1 - 3) / (1 + p.1)) * Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
      ≤ 18 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
        + 18 * Work.Spaces.HkSq α k (Work.Spaces.Dz V) := by
    have hmono := MeasureTheory.setIntegral_mono_on hInt3 hdom slotAux_measurableSet_dom hpt3
    rw [MeasureTheory.integral_add (hD2.1.const_mul 2) (hZ.1.const_mul 18),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hmono
    have hA₀ : 0 ≤ Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V) :=
      Work.Spaces.HkSq_nonneg α k _
    have hB₀ : 0 ≤ Work.Spaces.HkSq α k (Work.Spaces.Dz V) :=
      Work.Spaces.HkSq_nonneg α k _
    linarith [hmono, hD2.2, hZ.2, hA₀, hB₀]
  exact ⟨⟨hZ.1, hZ.2⟩, ⟨hT.1, hT.2⟩, ⟨hInt3, hC3⟩⟩

end Work.FTS.EllSol.PkgK5.TraceEngine
end
end
-- ===== merged: Submission.Work.FTS.EllSol.ShiftFT.AtwoAux.Const =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false


/-- The arithmetic of the constants: with `K = 3 + 3·(Kd(1+2/4096))² + 196608·M²/4096⁴` one
has `3 ≤ K`, `3·(Kd/N + 2Kd/(4096N))² ≤ K/N`, and `12·N·Aphi ≤ K/N` for
`Aphi ≤ 16384·N·(M/(4096N)²)²` and `N ≥ 2`. -/
theorem uTrAtwo_const (N Kd M Aphi : ℝ) (hN : 2 ≤ N) (hKd : 0 ≤ Kd)
    (hAphi : Aphi ≤ 16384 * N * (M / (4096 * N) ^ 2) ^ 2) :
    (3 : ℝ) ≤ 3 + 3 * (Kd * (1 + 2 / 4096)) ^ 2 + 196608 * M ^ 2 / 4096 ^ 4
    ∧ 3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2 + 12 * N * Aphi
      ≤ (3 + 3 * (Kd * (1 + 2 / 4096)) ^ 2 + 196608 * M ^ 2 / 4096 ^ 4) / N := by
  have hN0 : 0 < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  set c : ℝ := Kd * (1 + 2 / 4096) with hc
  set K : ℝ := 3 + 3 * c ^ 2 + 196608 * M ^ 2 / 4096 ^ 4 with hK
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  have hM2 : 0 ≤ 196608 * M ^ 2 / 4096 ^ 4 := by positivity
  have hK3 : (3 : ℝ) ≤ K := by rw [hK]; linarith
  have hKcc : 3 * c ^ 2 + 196608 * M ^ 2 / 4096 ^ 4 ≤ K := by rw [hK]; linarith
  have hcf : Kd / N + 2 * (Kd / (4096 * N)) = c / N := by
    rw [hc]
    field_simp
    try ring
  have hAphi' : Aphi ≤ 16384 * M ^ 2 / (4096 ^ 4 * N ^ 3) := by
    refine hAphi.trans (le_of_eq ?_)
    rw [div_pow]
    field_simp
    try ring
  refine ⟨hK3, ?_⟩
  rw [hcf]
  have hB : 3 * (c / N) ^ 2 ≤ (3 * c ^ 2) / N := by
    have h1 : 3 * (c / N) ^ 2 = (3 * c ^ 2) / N ^ 2 := by ring
    rw [h1, div_le_div_iff₀ (pow_pos hN0 2) hN0]
    have h2 : 3 * c ^ 2 * N ≤ 3 * c ^ 2 * N ^ 2 := by
      have hNN : (1 : ℝ) * N ≤ N * N := by nlinarith [hN1]
      nlinarith [hc2, hN1]
    linarith [h2]
  have hC : 12 * N * Aphi ≤ (196608 * M ^ 2 / 4096 ^ 4) / N := by
    rw [le_div_iff₀ hN0]
    have hstep : 12 * N ^ 2 * Aphi ≤ 196608 * M ^ 2 / (4096 ^ 4 * N) := by
      have h1 : 12 * N ^ 2 * Aphi ≤ 12 * N ^ 2 * (16384 * M ^ 2 / (4096 ^ 4 * N ^ 3)) :=
        mul_le_mul_of_nonneg_left hAphi' (by positivity)
      have h2 : 12 * N ^ 2 * (16384 * M ^ 2 / (4096 ^ 4 * N ^ 3))
          = 196608 * M ^ 2 / (4096 ^ 4 * N) := by
        field_simp
        try ring
      linarith [h1, h2.le, h2.ge]
    have hstep2 : 196608 * M ^ 2 / (4096 ^ 4 * N) ≤ 196608 * M ^ 2 / 4096 ^ 4 := by
      have h1 : 196608 * M ^ 2 / (4096 ^ 4 * N) = (196608 * M ^ 2 / 4096 ^ 4) / N := by ring
      rw [h1]
      have h2 : (196608 * M ^ 2 / 4096 ^ 4) / N ≤ (196608 * M ^ 2 / 4096 ^ 4) / 1 :=
        div_le_div_of_nonneg_left hM2 (by norm_num) hN1
      have h3 : (196608 * M ^ 2 / 4096 ^ 4) / 1 = 196608 * M ^ 2 / 4096 ^ 4 := by ring
      linarith [h2, h3.le]
    have h4 : 12 * N * Aphi * N = 12 * N ^ 2 * Aphi := by ring
    linarith [hstep, hstep2, h4.le, h4.ge]
  have hsum : 3 * (c / N) ^ 2 + 12 * N * Aphi
      ≤ (3 * c ^ 2) / N + (196608 * M ^ 2 / 4096 ^ 4) / N := add_le_add hB hC
  have hcomb : (3 * c ^ 2) / N + (196608 * M ^ 2 / 4096 ^ 4) / N
      = (3 * c ^ 2 + 196608 * M ^ 2 / 4096 ^ 4) / N := by ring
  have hlast : (3 * c ^ 2 + 196608 * M ^ 2 / 4096 ^ 4) / N ≤ K / N :=
    div_le_div_of_nonneg_right hKcc (le_of_lt hN0)
  linarith [hsum, hcomb.le, hcomb.ge, hlast]

end

end Work.FTS.EllSol.ShiftFT
end
-- ===== merged: Submission.Work.FTS.EllSol.ShiftFT.AtwoAux.Cutoff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false


/-- `tk` is locally `1` near the points of the open interval `(-1,1)`. -/
theorem tk_eventuallyEq_one {s : ℝ} (h : |s| < 1) : Trunc.tk =ᶠ[𝓝 s] (fun _ => (1 : ℝ)) := by
  have hopen : IsOpen {u : ℝ | |u| < 1} := isOpen_lt continuous_abs continuous_const
  filter_upwards [hopen.mem_nhds h] with u hu
  exact Trunc.tk_eq_one (le_of_lt hu)

/-- `tk` is locally `0` near the points with `u ^ 2 > 2` (in particular for `2 ≤ |s|`). -/
theorem tk_eventuallyEq_zero {s : ℝ} (h : (2 : ℝ) < s ^ 2) :
    Trunc.tk =ᶠ[𝓝 s] (fun _ => (0 : ℝ)) := by
  have hopen : IsOpen {u : ℝ | (2 : ℝ) < u ^ 2} :=
    isOpen_lt continuous_const (continuous_id.pow 2)
  filter_upwards [hopen.mem_nhds h] with u hu
  unfold Trunc.tk
  exact Real.smoothTransition.zero_of_nonpos (by linarith [hu])

theorem two_lt_sq_of_two_le_abs {s : ℝ} (h : 2 ≤ |s|) : (2 : ℝ) < s ^ 2 := by
  have h2 := sq_abs s
  nlinarith [abs_nonneg s, h]

theorem deriv_tk_eq_zero_of_abs_lt_one {s : ℝ} (h : |s| < 1) : deriv Trunc.tk s = 0 := by
  rw [(tk_eventuallyEq_one h).deriv_eq, deriv_const]

theorem deriv_tk_eq_zero_of_two_lt_sq {s : ℝ} (h : (2 : ℝ) < s ^ 2) : deriv Trunc.tk s = 0 := by
  rw [(tk_eventuallyEq_zero h).deriv_eq, deriv_const]

theorem deriv_deriv_tk_eq_zero_of_abs_lt_one {s : ℝ} (h : |s| < 1) :
    deriv (deriv Trunc.tk) s = 0 := by
  have hd : deriv Trunc.tk =ᶠ[𝓝 s] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_lt continuous_abs continuous_const |>.mem_nhds h] with u hu
    exact deriv_tk_eq_zero_of_abs_lt_one hu
  rw [hd.deriv_eq, deriv_const]

theorem deriv_deriv_tk_eq_zero_of_two_lt_sq {s : ℝ} (h : (2 : ℝ) < s ^ 2) :
    deriv (deriv Trunc.tk) s = 0 := by
  have hd : deriv Trunc.tk =ᶠ[𝓝 s] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_lt continuous_const (continuous_id.pow 2) |>.mem_nhds h] with u hu
    exact deriv_tk_eq_zero_of_two_lt_sq hu
  rw [hd.deriv_eq, deriv_const]

theorem deriv_phiTr_eq (N t : ℝ) :
    deriv (phiTr N) t = deriv Trunc.tk (t / (4096 * N)) / (4096 * N) :=
  Trunc.deriv_chi_eq (4096 * N) t

theorem deriv2_phiTr_eq (N t : ℝ) :
    deriv (deriv (phiTr N)) t = deriv (deriv Trunc.tk) (t / (4096 * N)) / (4096 * N) ^ 2 :=
  Trunc.deriv2_chi_eq (4096 * N) t

theorem abs_deriv_phiTr_le (N : ℝ) {Kd : ℝ} (hKd : ∀ t : ℝ, |deriv Trunc.tk t| ≤ Kd)
    {t : ℝ} (hN : 0 < N) : |deriv (phiTr N) t| ≤ Kd / (4096 * N) :=
  Trunc.abs_deriv_chi_le hKd (by linarith) t

theorem abs_deriv2_phiTr_le (N : ℝ) {M : ℝ} (hM : ∀ t : ℝ, |deriv (deriv Trunc.tk) t| ≤ M)
    {t : ℝ} (hN : 0 < N) : |deriv (deriv (phiTr N)) t| ≤ M / (4096 * N) ^ 2 := by
  rw [deriv2_phiTr_eq, abs_div, abs_of_nonneg (sq_nonneg (4096 * N))]
  exact div_le_div_of_nonneg_right (hM _) (sq_nonneg _)

theorem deriv2_phiTr_eq_zero_of_abs_lt {N : ℝ} (hN : 0 < N) {t : ℝ}
    (h : |t| < 4096 * N) : deriv (deriv (phiTr N)) t = 0 := by
  have hpos : 0 < 4096 * N := by linarith
  rw [deriv2_phiTr_eq]
  have hlt : |t / (4096 * N)| < 1 := by
    rw [abs_div, abs_of_pos hpos, div_lt_one hpos]
    exact h
  rw [deriv_deriv_tk_eq_zero_of_abs_lt_one hlt, zero_div]

theorem deriv2_phiTr_eq_zero_of_abs_ge {N : ℝ} (hN : 0 < N) {t : ℝ}
    (h : 8192 * N ≤ |t|) : deriv (deriv (phiTr N)) t = 0 := by
  have hpos : 0 < 4096 * N := by linarith
  rw [deriv2_phiTr_eq]
  have h2 : 2 ≤ |t / (4096 * N)| := by
    rw [abs_div, abs_of_pos hpos, le_div_iff₀ hpos]
    linarith
  rw [deriv_deriv_tk_eq_zero_of_two_lt_sq (two_lt_sq_of_two_le_abs h2), zero_div]

/-- The mass bound on the second derivative of `phiTr`: its support has length `16384*N` and
the function is bounded by `M/(4096*N)^2` there. -/
theorem integral_deriv2_phiTr_sq_le (N : ℝ) {M : ℝ}
    (hM : ∀ t : ℝ, |deriv (deriv Trunc.tk) t| ≤ M) (hN : 0 < N) :
    (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2) ≤
      16384 * N * (M / (4096 * N) ^ 2) ^ 2 := by
  set A : ℝ := 8192 * N with hAdef
  have hA0 : 0 < A := by rw [hAdef]; linarith
  have hsupp : ∀ t : ℝ, t ∉ Set.Icc (-A) A → (deriv (deriv (phiTr N)) t) ^ 2 = 0 := by
    intro t ht
    have hge : A ≤ |t| := by
      by_contra hcon
      push Not at hcon
      exact ht ⟨by linarith [neg_abs_le t, hcon], by linarith [le_abs_self t, hcon]⟩
    rw [deriv2_phiTr_eq_zero_of_abs_ge hN (by rw [hAdef] at hge; exact hge)]
    ring
  have hfin : volume (Set.Icc (-A) A) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hbnd : ∀ t ∈ Set.Icc (-A) A, ‖(deriv (deriv (phiTr N)) t) ^ 2‖
      ≤ (M / (4096 * N) ^ 2) ^ 2 := by
    intro t _
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h := abs_deriv2_phiTr_le N hM (t := t) hN
    have hle : deriv (deriv (phiTr N)) t ≤ M / (4096 * N) ^ 2 := le_trans (le_abs_self _) h
    have hle' : -(M / (4096 * N) ^ 2) ≤ deriv (deriv (phiTr N)) t :=
      le_trans (neg_le_neg h) (neg_abs_le _)
    nlinarith [sq_nonneg (deriv (deriv (phiTr N)) t)]
  have hmain : (∫ t in Set.Icc (-A) A, (deriv (deriv (phiTr N)) t) ^ 2)
      ≤ (M / (4096 * N) ^ 2) ^ 2 * volume.real (Set.Icc (-A) A) := by
    have h1 := MeasureTheory.norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.mpr hfin) hbnd
    rwa [Real.norm_of_nonneg
      (MeasureTheory.integral_nonneg (fun t => sq_nonneg _))] at h1
  calc (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2)
      = ∫ t in Set.Icc (-A) A, (deriv (deriv (phiTr N)) t) ^ 2 := by
        rw [MeasureTheory.setIntegral_univ]
        exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm
    _ ≤ (M / (4096 * N) ^ 2) ^ 2 * volume.real (Set.Icc (-A) A) := hmain
    _ = 16384 * N * (M / (4096 * N) ^ 2) ^ 2 := by
        rw [Real.volume_real_Icc_of_le (by rw [hAdef]; linarith), hAdef]; ring

/-! ## The a.e. description of the strip `ℝ × Iθ` -/

theorem ae_mem_Ioo_of_Iθ :
    ∀ᵐ p ∂(volume.restrict ((Set.univ : Set ℝ) ×ˢ Work.Spaces.Iθ)),
      p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have hθ : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := Real.pi / 2)).symm
  have hprod : ((Set.univ : Set ℝ) ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
      =ᵐ[volume] ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    exact MeasureTheory.Measure.set_prod_ae_eq EventuallyEq.rfl hθ
  rw [MeasureTheory.Measure.restrict_congr_set hprod]
  rw [MeasureTheory.ae_restrict_iff' (MeasurableSet.univ.prod measurableSet_Ioo)]
  filter_upwards with p hp
  exact hp.2

theorem measurableSet_stripIθ : MeasurableSet ((Set.univ : Set ℝ) ×ˢ Work.Spaces.Iθ) :=
  MeasurableSet.univ.prod measurableSet_Icc

/-! ## The pointwise description of the shifted second slot of `uTr N b u` -/

end

end Work.FTS.EllSol.ShiftFT
end
-- ===== merged: Submission.Work.FTS.EllSol.ShiftFT.Aux2.gcIntShift =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT.Aux2

open MeasureTheory Set
open scoped Real Topology

noncomputable section

/-! ## Where `deriv (chi N)` vanishes

`chi N t = tk (t/N)` with `tk = Real.smoothTransition (2 - ·²)`, so `tk` is *identically* `0` on
a whole neighbourhood of every point with `2 ≤ |t|` (the threshold `√2` of `2 - t² ≤ 0` is
strictly below `2`, so the closed condition `2 ≤ |t|` gives an open neighbourhood).  Hence,
up to the endpoints: `deriv (chi N)` vanishes for `2N ≤ |s|`.  This is the (slightly sharper)
closed-endpoint version of `Trunc.deriv_chi_eq_zero_of_gt`, which only covers `2N < |s|`; the
endpoint case matters below because the integration interval is *closed* at `-2N`. -/

/-- `deriv tk` vanishes at every point with `2 ≤ |t|` (in fact `tk` is `0` near such a point). -/
theorem deriv_tk_eq_zero_of_two_le_abs {t : ℝ} (ht : 2 ≤ |t|) :
    deriv (Work.FTS.EllSol.Trunc.tk) t = 0 := by
  -- `2 - t² < 0`, so `tk ≡ 0` on a neighbourhood of `t`
  have hneg : 2 - t ^ 2 < 0 := by
    have h2 : (2 : ℝ) < t ^ 2 := by
      have h3 := sq_abs t
      nlinarith [abs_nonneg t, ht]
    linarith
  have hopen : IsOpen {s : ℝ | 2 - s ^ 2 < 0} :=
    isOpen_lt (f := fun s : ℝ => 2 - s ^ 2) (g := fun _ : ℝ => 0)
      (continuous_const.sub (continuous_id.pow 2)) continuous_const
  have hev : (Work.FTS.EllSol.Trunc.tk) =ᶠ[𝓝 t] fun _ : ℝ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds hneg] with s hs
    unfold Work.FTS.EllSol.Trunc.tk
    exact Real.smoothTransition.zero_of_nonpos (le_of_lt hs)
  rw [hev.deriv_eq, deriv_const]

/-- `deriv (chi N)` vanishes at every point with `2N ≤ |t|` (`N > 0`). -/
theorem deriv_chi_eq_zero_of_two_mul_le_abs {N t : ℝ} (hN : 0 < N) (ht : 2 * N ≤ |t|) :
    deriv (Work.FTS.EllSol.Trunc.chi N) t = 0 := by
  rw [Work.FTS.EllSol.Trunc.deriv_chi_eq]
  have h2 : (2 : ℝ) ≤ |t / N| := by
    rw [abs_div, abs_of_pos hN, le_div_iff₀ hN]
    linarith
  rw [deriv_tk_eq_zero_of_two_le_abs h2, zero_div]

/-- **The shifted integral does not see the lower limit, once that limit is left of `-2N`.**
Since `deriv (chi N)` is supported in `[-2N, 2N]`, the integrand
`s ↦ e^{-bs}·(chi N)'(s)·u(s,θ)` has support inside `(-2N, 2N]`; hence both the integral over
`[t, 2N]` (for `t ≤ -2N`) and the integral over `[-2N, 2N]` equal the integral of that same
integrand over all of `ℝ`. -/
theorem gcIntShift (N b : ℝ) (u : ℝ → ℝ → ℝ) (hN : 0 < N)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ t : ℝ, t ≤ -(2 * N) →
      (∫ s in t..(2 * N),
          Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ)
        = ∫ s in (-(2 * N))..(2 * N),
            Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ := by
  intro θ hθ t ht
  set f : ℝ → ℝ := fun s => Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ
    with hf
  -- the derivative of the cutoff vanishes on both outer regions
  have hz : ∀ x : ℝ, (x ≤ -(2 * N) ∨ 2 * N ≤ x) →
      deriv (Work.FTS.EllSol.Trunc.chi N) x = 0 := by
    intro x hx
    rcases hx with hx | hx
    · exact deriv_chi_eq_zero_of_two_mul_le_abs hN
        (by rw [abs_of_nonpos (by linarith)]; linarith)
    · exact deriv_chi_eq_zero_of_two_mul_le_abs hN
        (by rw [abs_of_pos (by linarith)]; linarith)
  -- hence the integrand is supported in `(-2N, 2N]`
  have hsuppBig : Function.support f ⊆ Set.Ioc (-(2 * N)) (2 * N) := by
    intro s hs
    refine ⟨?_, ?_⟩
    · by_contra h
      simp only [not_lt] at h
      exact hs (by rw [hf]; simp [hz s (Or.inl h)])
    · by_contra h
      simp only [not_le] at h
      exact hs (by rw [hf]; simp [hz s (Or.inr (le_of_lt h))])
  -- and a fortiori in `(t, 2N]` whenever `t ≤ -2N`
  have hsupp1 : Function.support f ⊆ Set.Ioc t (2 * N) := by
    intro s hs
    obtain ⟨h1, h2⟩ := hsuppBig hs
    exact ⟨by linarith, h2⟩
  have h2 : (∫ s in t..(2 * N), f s) = ∫ s, f s :=
    intervalIntegral.integral_eq_integral_of_support_subset hsupp1
  have h1 : (∫ s in (-(2 * N))..(2 * N), f s) = ∫ s, f s :=
    intervalIntegral.integral_eq_integral_of_support_subset hsuppBig
  rw [h2, h1]

end

end Work.FTS.EllSol.ShiftFT.Aux2
end
-- ===== merged: Submission.Work.FTS.EllSol.ShiftFT.Aux2.gcIntTailZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project (area `FTS.EllSol`).

# The right tail of the truncation integral vanishes

`Work.FTS.EllSol.ShiftFT.Gc N b u t θ = chi N t * u t θ
 + e^{bt} ∫_t^{2N} e^{-bs} (chi N)'(s) u s θ ds`; the integral is the primitive of the
truncation error.  Here we record the elementary fact that for `2N ≤ t` this integral
vanishes: the integrand carries the factor `deriv (chi N) s`, and `chi N s = tk (s/N)`
is identically `0` for `2N < |s|`, so its derivative vanishes on the (strict) window
`(2N, ∞)`; the interval `t..(2N)` therefore consists entirely of such points (it is a
subset of `Ioc (2N) t`, on which `2N < s` strictly).
-/

namespace Work.FTS.EllSol.ShiftFT.Aux2

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-- Off the strict window `|s| ≤ 2N` the cutoff `chi N` is locally constant `0`, hence its
derivative vanishes: `deriv (chi N) s = 0` for `2N < s`. -/
theorem deriv_chi_eq_zero_of_two_mul_lt {N s : ℝ} (hN : 0 < N) (hs : 2 * N < s) :
    deriv (Work.FTS.EllSol.Trunc.chi N) s = 0 := by
  have hmem : s ∈ {x : ℝ | 2 * N < |x|} := by
    show 2 * N < |s|
    rw [abs_of_pos (by linarith)]
    exact hs
  have hopen : IsOpen {x : ℝ | 2 * N < |x|} := isOpen_lt continuous_const continuous_abs
  have hev : Work.FTS.EllSol.Trunc.chi N =ᶠ[𝓝 s] fun _ : ℝ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds hmem] with x hx
    exact Work.FTS.EllSol.Trunc.chi_eq_zero hN (le_of_lt hx)
  rw [hev.deriv_eq, deriv_const]

set_option linter.unusedVariables false in
theorem gcIntTailZero (N b : ℝ) (u : ℝ → ℝ → ℝ) (hN : 0 < N)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ t : ℝ, 2 * N ≤ t →
      (∫ s in t..(2 * N),
          Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ) = 0 := by
  intro θ hθ t ht
  -- on `(2N, t]` the factor `deriv (chi N)` vanishes, so the whole integrand is `0`
  have hzero : ∀ s ∈ Set.Ioc (2 * N) t,
      Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ = 0 := by
    intro s hs
    rw [deriv_chi_eq_zero_of_two_mul_lt hN hs.1]
    ring
  rw [intervalIntegral.integral_of_ge ht,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hzero]
  simp

end

end Work.FTS.EllSol.ShiftFT.Aux2
end
-- ===== merged: Submission.Work.FTS.EllSol.ShiftFT.Aux2.gcJHasDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT.Aux2

open MeasureTheory Set
open scoped Topology

theorem gcJHasDeriv (N b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => ∫ y in s..(2 * N),
          Real.exp (-(b * y)) * deriv (Work.FTS.EllSol.Trunc.chi N) y * u y θ)
        (-(Real.exp (-(b * t)) * deriv (Work.FTS.EllSol.Trunc.chi N) t * u t θ)) t := by
  intro θ hθ t
  -- the `θ`-slice of `u` is continuous
  have hslice : Continuous fun y : ℝ => u y θ := by
    rw [continuous_iff_continuousAt]
    intro y
    have hpt : ContinuousAt (Function.uncurry u) (y, θ) :=
      hu.continuousOn.continuousAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨trivial, hθ⟩)
    have hmap : ContinuousAt (fun y' : ℝ => (y', θ)) y :=
      (Continuous.prodMk_left θ).continuousAt
    exact hpt.comp (f := fun y' : ℝ => (y', θ)) hmap
  have hchi : Continuous (deriv (Work.FTS.EllSol.Trunc.chi N)) :=
    (Work.FTS.EllSol.Trunc.chi_contDiff 1 N).continuous_deriv_one
  have hexp : Continuous fun y : ℝ => Real.exp (-(b * y)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id).neg
  have hcont : Continuous fun y : ℝ =>
      Real.exp (-(b * y)) * deriv (Work.FTS.EllSol.Trunc.chi N) y * u y θ :=
    (hexp.mul hchi).mul hslice
  exact intervalIntegral.integral_hasDerivAt_left
    (f := fun y : ℝ => Real.exp (-(b * y)) * deriv (Work.FTS.EllSol.Trunc.chi N) y * u y θ)
    (a := t) (b := 2 * N)
    (hcont.intervalIntegrable _ _) (hcont.stronglyMeasurableAtFilter volume (𝓝 t))
    hcont.continuousAt

end Work.FTS.EllSol.ShiftFT.Aux2
end
-- ===== merged: Submission.Work.FTS.EllSol.ShiftFT.Aux2.gcSliceData =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT.Aux2

/-- If `u` is jointly `C²` on the closed half-strip `ℝ × (0,π/2)`, then every `θ`-slice
`s ↦ u s θ` (`θ ∈ (0,π/2)`) is `C²`, hence in particular differentiable, and its `z`-derivative
`pz u · θ = ∂_z u(·,θ)` is again differentiable (the slice is `C²`, so `deriv` of the slice is
`C¹`).

The slice is obtained by composing the (smooth) map `s ↦ (s,θ)` with `Function.uncurry u`; since
the second coordinate of the image is `θ` itself (in the interval), the whole image lies in
`univ ×ˢ Ioo 0 (π/2)`. -/
theorem gcSliceData (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Differentiable ℝ (fun s : ℝ => u s θ))
    ∧ (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Differentiable ℝ (fun s : ℝ => Work.Spaces.pz u s θ)) := by
  -- every slice of `u` at `θ ∈ (0,π/2)` is globally `C²` on `ℝ`
  have hslice : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ContDiff ℝ 2 (fun s : ℝ => u s θ) := by
    intro θ hθ
    -- the parametrisation `s ↦ (s,θ)` is smooth …
    have hφ : ContDiff ℝ 2 (fun s : ℝ => (s, θ)) := by fun_prop
    -- … and takes all of `ℝ` into the half-strip
    have hmap : Set.MapsTo (fun s : ℝ => (s, θ)) Set.univ
        (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun s _ => ⟨trivial, hθ⟩
    have h2 := hu.comp (contDiffOn_univ.mpr hφ) hmap
    rw [contDiffOn_univ] at h2
    have heq : (Function.uncurry u ∘ fun s : ℝ => (s, θ)) = fun s : ℝ => u s θ := by
      funext s; rfl
    rwa [heq] at h2
  constructor
  · -- differentiability of the slice
    intro θ hθ
    exact (hslice θ hθ).differentiable (by norm_num)
  · -- differentiability of the derivative of the slice
    intro θ hθ
    have h := ContDiff.differentiable_deriv_two (hslice θ hθ)
    simpa [Work.Spaces.pz] using h

end Work.FTS.EllSol.ShiftFT.Aux2
end
-- ===== merged: Submission.Work.FTS.EllSol.ShiftFT.Aux2.marginal =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT.Aux2

open MeasureTheory Set



end Work.FTS.EllSol.ShiftFT.Aux2
end
-- ===== merged: Submission.Work.FTS.EllSol.ShiftFT.Gc_pth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-! ## Auxiliary: the `θ`-partial of a `C²` datum is continuous

This is the `n = 1` instance of the general fact that the curried partial derivative of a
function of class `C^{n+1}` on an open set is of class `C^n` there. -/

/-! ## Auxiliary: differentiation of the `θ`-slice of the integral -/


/-! ## The target -/


end

end Work.FTS.EllSol.ShiftFT
end
-- ===== merged: Submission.Work.FTS.EllSol.ShiftFT.Gc_pth_pth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT

open MeasureTheory Set Filter
open scoped Real Topology Interval

noncomputable section

set_option autoImplicit false

/-- The open angular interval `(0, π/2)`. -/
abbrev gIθ : Set ℝ := Set.Ioo 0 (Real.pi / 2)

theorem isOpen_gIθ : IsOpen gIθ := isOpen_Ioo

/-! ## Generic calculus lemmas -/

/-- On an open set, the curried `θ`-partial derivative of a function lowers the order of
smoothness by one. -/
theorem pth_contDiffOn_uncurry_fin {n : ℕ} {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (0, 1) := fun p hp =>
    Work.Spaces.pth_eq_fderiv ((h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun (p : ℝ × ℝ) => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (m := n) (by simp)
  have hcomp : ContDiffOn ℝ n
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- **Differentiation under the integral sign in the parameter, over an interval.**  If `c` is
continuous, `f` and `g` are jointly continuous on the product of `univ` with an open set `V`,
and for every `s` the slice `θ ↦ f s θ` has derivative `g s θ` at every `θ ∈ V`, then
`θ ↦ ∫_s∈[a,b] c s · f s θ` has derivative `∫_s∈[a,b] c s · g s θ₀` at `θ₀`. -/
theorem hasDerivAt_intervalIntegral_pth
    {c : ℝ → ℝ} (hc : Continuous c) {f g : ℝ → ℝ → ℝ} {V : Set ℝ} (hV : IsOpen V)
    {a b θ₀ : ℝ} (hθ₀ : θ₀ ∈ V)
    (hf : ContinuousOn (Function.uncurry f) ((Set.univ : Set ℝ) ×ˢ V))
    (hg : ContinuousOn (Function.uncurry g) ((Set.univ : Set ℝ) ×ˢ V))
    (hdiff : ∀ s θ, θ ∈ V → HasDerivAt (fun θ' => f s θ') (g s θ) θ) :
    HasDerivAt (fun θ => ∫ s in a..b, c s * f s θ) (∫ s in a..b, c s * g s θ₀) θ₀ := by
  obtain ⟨δ, hδpos, hδV⟩ := Metric.mem_nhds_iff.1 (hV.mem_nhds hθ₀)
  set K : Set ℝ := Set.Icc (θ₀ - δ / 2) (θ₀ + δ / 2) with hKdef
  set W : Set ℝ := Set.Ioo (θ₀ - δ / 2) (θ₀ + δ / 2) with hWdef
  set J : Set ℝ := Set.Icc (min a b) (max a b) with hJdef
  have hKW : K ⊆ V := by
    intro y hy
    refine hδV ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hy.1, hδpos], by linarith [hy.2, hδpos]⟩
  have hWK : W ⊆ K := Set.Ioo_subset_Icc_self
  have hJc : IsCompact J := by rw [hJdef]; exact isCompact_Icc
  have hKc : IsCompact K := by rw [hKdef]; exact isCompact_Icc
  have hIJ : Set.uIoc a b ⊆ J := by
    rw [hJdef, Set.Icc_min_max]
    exact Set.uIoc_subset_uIcc
  have hWnhds : W ∈ 𝓝 θ₀ := by
    rw [hWdef]
    exact isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  have hcontG : ContinuousOn (fun p : ℝ × ℝ => c p.1 * g p.1 p.2) (J ×ˢ K) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => c p.1) (J ×ˢ K) :=
      hc.comp_continuousOn continuousOn_fst
    have h2 : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (J ×ˢ K) :=
      hg.mono (Set.prod_mono (subset_univ J) hKW)
    exact h1.mul h2
  obtain ⟨C, hC⟩ := (hJc.prod hKc).exists_bound_of_continuousOn hcontG
  have hJF : ∀ x ∈ V, ContinuousOn (fun s => c s * f s x) J := by
    intro x hx
    have h1 : ContinuousOn (fun s : ℝ => c s) J := hc.comp_continuousOn continuousOn_id
    have h2 : ContinuousOn (fun s : ℝ => f s x) J := by
      have hmap : ContinuousOn (fun s : ℝ => (s, x)) J :=
        continuousOn_id.prodMk (continuousOn_const (s := J) (c := x))
      have hcomp := hf.comp hmap (fun s _ => ⟨trivial, hx⟩)
      simpa [Function.comp_def, Function.uncurry] using hcomp
    exact h1.mul h2
  have hJG : ∀ x ∈ V, ContinuousOn (fun s => c s * g s x) J := by
    intro x hx
    have h1 : ContinuousOn (fun s : ℝ => c s) J := hc.comp_continuousOn continuousOn_id
    have h2 : ContinuousOn (fun s : ℝ => g s x) J := by
      have hmap : ContinuousOn (fun s : ℝ => (s, x)) J :=
        continuousOn_id.prodMk (continuousOn_const (s := J) (c := x))
      have hcomp := hg.comp hmap (fun s _ => ⟨trivial, hx⟩)
      simpa [Function.comp_def, Function.uncurry] using hcomp
    exact h1.mul h2
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (𝕜 := ℝ)
    (F := fun θ s => c s * f s θ) (F' := fun θ s => c s * g s θ) (bound := fun _ => C)
    (x₀ := θ₀) (s := W) hWnhds ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hV.mem_nhds hθ₀] with x hx
    exact ((hJF x hx).mono hIJ).aestronglyMeasurable measurableSet_uIoc
  · refine ContinuousOn.intervalIntegrable ((hJF θ₀ hθ₀).mono ?_)
    rw [← Set.Icc_min_max, hJdef]
  · exact ((hJG θ₀ hθ₀).mono hIJ).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards with t ht x hx
    exact hC (t, x) ⟨hIJ ht, hWK hx⟩
  · exact intervalIntegrable_const
  · filter_upwards with t ht x hx
    exact (hdiff t x (hKW (hWK hx))).const_mul (c t)

/-! ## The angular derivatives of `Gc` -/

/-- The first angular derivative of `Gc`: differentiating the defining formula under the
integral sign.  (This is the `b`-shifted counterpart of the definition; note that the prefactor
`χ_N(t)` and `e^{bt}` do not depend on `θ`.) -/
theorem Gc_pth_aux (N b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ t : ℝ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Spaces.pth (Gc N b u) t θ
      = Work.FTS.EllSol.Trunc.chi N t * Work.Spaces.pth u t θ
        + Real.exp (b * t) * ∫ s in t..(2 * N),
            Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s
              * Work.Spaces.pth u s θ := by
  intro t θ hθ
  have hS : IsOpen ((Set.univ : Set ℝ) ×ˢ gIθ) := isOpen_univ.prod isOpen_Ioo
  have hc : Continuous
      (fun s : ℝ => Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s) :=
    (Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)).mul
      ((Work.FTS.EllSol.Trunc.chi_contDiff 2 N).continuous_deriv (by norm_num))
  have hu1 : ContDiffOn ℝ 1 (Function.uncurry u) ((Set.univ : Set ℝ) ×ˢ gIθ) :=
    hu.of_le (by norm_num)
  have hpt1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth u))
      ((Set.univ : Set ℝ) ×ˢ gIθ) := pth_contDiffOn_uncurry_fin hS (n := 1) hu
  have hd_u : ∀ s θ', θ' ∈ gIθ → HasDerivAt (fun θ'' => u s θ'') (Work.Spaces.pth u s θ') θ' := by
    intro s θ' hθ'
    have hmem : (s, θ') ∈ (Set.univ : Set ℝ) ×ˢ gIθ := ⟨trivial, hθ'⟩
    have hdiff : DifferentiableAt ℝ (Function.uncurry u) (s, θ') :=
      (hu.differentiableOn (by simp)).differentiableAt (hS.mem_nhds hmem)
    exact (Work.Spaces.differentiableAt_curry_right hdiff).hasDerivAt
  have hH1 : HasDerivAt (fun θ'' => ∫ s in t..(2 * N),
        Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ'')
      (∫ s in t..(2 * N),
        Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * Work.Spaces.pth u s θ) θ :=
    hasDerivAt_intervalIntegral_pth hc isOpen_gIθ hθ hu1.continuousOn hpt1.continuousOn hd_u
  have h1 : HasDerivAt (fun θ'' => Work.FTS.EllSol.Trunc.chi N t * u t θ'')
      (Work.FTS.EllSol.Trunc.chi N t * Work.Spaces.pth u t θ) θ :=
    (hd_u t θ hθ).const_mul _
  have h2 : HasDerivAt (fun θ'' => Real.exp (b * t) * ∫ s in t..(2 * N),
        Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ'')
      (Real.exp (b * t) * ∫ s in t..(2 * N),
        Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * Work.Spaces.pth u s θ) θ :=
    hH1.const_mul _
  rw [show Work.Spaces.pth (Gc N b u) t θ
      = deriv (fun θ'' => Gc N b u t θ'') θ from rfl]
  exact (h1.add h2).deriv

theorem Gc_pth_pth (N b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ t : ℝ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Spaces.pth (Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.Gc N b u)) t θ
      = Work.FTS.EllSol.Trunc.chi N t * Work.Spaces.pth (Work.Spaces.pth u) t θ
        + Real.exp (b * t) * ∫ s in t..(2 * N),
            Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s
              * Work.Spaces.pth (Work.Spaces.pth u) s θ := by
  intro t θ hθ
  have hS : IsOpen ((Set.univ : Set ℝ) ×ˢ gIθ) := isOpen_univ.prod isOpen_Ioo
  have hc : Continuous
      (fun s : ℝ => Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s) :=
    (Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)).mul
      ((Work.FTS.EllSol.Trunc.chi_contDiff 2 N).continuous_deriv (by norm_num))
  have hpt1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth u))
      ((Set.univ : Set ℝ) ×ˢ gIθ) := pth_contDiffOn_uncurry_fin hS (n := 1) hu
  have hpt2 : ContinuousOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth u)))
      ((Set.univ : Set ℝ) ×ˢ gIθ) :=
    (pth_contDiffOn_uncurry_fin hS (n := 0) hpt1).continuousOn
  have hd_pth : ∀ s θ', θ' ∈ gIθ →
      HasDerivAt (fun θ'' => Work.Spaces.pth u s θ'')
        (Work.Spaces.pth (Work.Spaces.pth u) s θ') θ' := by
    intro s θ' hθ'
    have hmem : (s, θ') ∈ (Set.univ : Set ℝ) ×ˢ gIθ := ⟨trivial, hθ'⟩
    have hdiff : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pth u)) (s, θ') :=
      (hpt1.differentiableOn (by simp)).differentiableAt (hS.mem_nhds hmem)
    exact (Work.Spaces.differentiableAt_curry_right hdiff).hasDerivAt
  -- the function whose derivative we compute is `θ' ↦ ∂_θ(Gc) t θ'`, given by `Gc_pth_aux`
  have heq : (fun θ' => Work.Spaces.pth (Gc N b u) t θ') =ᶠ[𝓝 θ]
      (fun θ' => Work.FTS.EllSol.Trunc.chi N t * Work.Spaces.pth u t θ'
        + Real.exp (b * t) * ∫ s in t..(2 * N),
            Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s
              * Work.Spaces.pth u s θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact Gc_pth_aux N b u hu t θ' hθ'
  have hder : deriv (fun θ' => Work.FTS.EllSol.Trunc.chi N t * Work.Spaces.pth u t θ'
        + Real.exp (b * t) * ∫ s in t..(2 * N),
            Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s
              * Work.Spaces.pth u s θ') θ
      = Work.FTS.EllSol.Trunc.chi N t * Work.Spaces.pth (Work.Spaces.pth u) t θ
        + Real.exp (b * t) * ∫ s in t..(2 * N),
            Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s
              * Work.Spaces.pth (Work.Spaces.pth u) s θ := by
    have hH2 : HasDerivAt (fun θ' => ∫ s in t..(2 * N),
          Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s
            * Work.Spaces.pth u s θ')
        (∫ s in t..(2 * N),
          Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s
            * Work.Spaces.pth (Work.Spaces.pth u) s θ) θ :=
      hasDerivAt_intervalIntegral_pth hc isOpen_gIθ hθ hpt1.continuousOn hpt2 hd_pth
    have h1 : HasDerivAt (fun θ' => Work.FTS.EllSol.Trunc.chi N t * Work.Spaces.pth u t θ')
        (Work.FTS.EllSol.Trunc.chi N t * Work.Spaces.pth (Work.Spaces.pth u) t θ) θ :=
      (hd_pth t θ hθ).const_mul _
    have h2 : HasDerivAt (fun θ' => Real.exp (b * t) * ∫ s in t..(2 * N),
          Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s
            * Work.Spaces.pth u s θ')
        (Real.exp (b * t) * ∫ s in t..(2 * N),
          Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s
            * Work.Spaces.pth (Work.Spaces.pth u) s θ) θ :=
      hH2.const_mul _
    exact (h1.add h2).deriv
  rw [show Work.Spaces.pth (Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.Gc N b u)) t θ
      = deriv (fun θ' => Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.Gc N b u) t θ') θ from rfl,
    Filter.EventuallyEq.deriv_eq heq]
  exact hder

end

end Work.FTS.EllSol.ShiftFT
end
-- ===== merged: Submission.Work.FTS.EllSol.ShiftFT.Gc_sh =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project (area `FTS.EllSol`).

# The shifted operator applied to the truncation `Gc`

`Work.FTS.EllSol.ShiftFT.Gc N b u` is the particular solution of the shifted equation
`L_b G = chi N · (L_b u)`, where `L_b u = ∂_t u - b·u` and `chi N` is the smooth cutoff of
`Work.FTS.EllSol.Trunc`.  This file verifies the defining identity in the first variable:

`∂_t (Gc N b u) - b·(Gc N b u) = chi N t · (∂_t u - b·u)`.

It is a direct instance of the fundamental theorem of calculus: with
`Gc N b u t θ = chi N t · u t θ + e^{bt} ∫_t^{2N} e^{-bs} (chi N)'(s) u s θ ds`
the derivative of the integral is `- e^{-bt} (chi N)'(t) u t θ`, whose product with the
prefactor `e^{bt}` cancels the `(chi N)'`-term produced by the product rule; what survives is
exactly `chi N t · (∂_t u - b·u)` together with the `b·e^{bt}·∫`-term which cancels against the
`b·Gc` on the left.
-/

namespace Work.FTS.EllSol.ShiftFT

open MeasureTheory Set Filter
open scoped Real Topology

theorem Gc_sh (N b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.Gc N b u) t θ
        - b * Work.FTS.EllSol.ShiftFT.Gc N b u t θ
      = Work.FTS.EllSol.Trunc.chi N t * (Work.Spaces.pz u t θ - b * u t θ) := by
  intro t θ hθ
  -- smoothness of the cutoff and its derivative
  have hchi2 : ContDiff ℝ 2 (Work.FTS.EllSol.Trunc.chi N) :=
    Work.FTS.EllSol.Trunc.chi_contDiff 2 N
  have hchiD : DifferentiableAt ℝ (Work.FTS.EllSol.Trunc.chi N) t :=
    hchi2.differentiable (by norm_num) t
  have hchic : Continuous (deriv (Work.FTS.EllSol.Trunc.chi N)) :=
    hchi2.continuous_deriv (by norm_num)
  -- the `θ`-slice of `u` is `C²` on `ℝ`, hence differentiable and continuous
  have hmap : Set.MapsTo (fun s : ℝ => (s, θ)) Set.univ
      (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun s _ => ⟨trivial, hθ⟩
  have hpair : ContDiffOn ℝ 2 (fun s : ℝ => ((s, θ) : ℝ × ℝ)) Set.univ :=
    ContDiffOn.prodMk contDiffOn_id contDiffOn_const
  have hslice : ContDiffOn ℝ 2 (fun s : ℝ => u s θ) Set.univ := by
    have h := hu.comp hpair hmap
    simpa [Function.comp_def, Function.uncurry] using h
  have hsliceDiff : DifferentiableAt ℝ (fun s : ℝ => u s θ) t :=
    (hslice.differentiableOn (by norm_num)).differentiableAt (by simp)
  have hsliceC : Continuous (fun s : ℝ => u s θ) := continuousOn_univ.mp hslice.continuousOn
  have hslice_deriv : HasDerivAt (fun s : ℝ => u s θ) (deriv (fun s : ℝ => u s θ) t) t :=
    hsliceDiff.hasDerivAt
  -- product rule for the cutoff term
  have hFd : HasDerivAt (fun s : ℝ => Work.FTS.EllSol.Trunc.chi N s * u s θ)
      (deriv (Work.FTS.EllSol.Trunc.chi N) t * u t θ
        + Work.FTS.EllSol.Trunc.chi N t * deriv (fun s : ℝ => u s θ) t) t :=
    hchiD.hasDerivAt.mul hslice_deriv
  -- the exponential prefactor
  have hexpD : HasDerivAt (fun s : ℝ => Real.exp (b * s)) (b * Real.exp (b * t)) t := by
    have h : HasDerivAt (fun s : ℝ => b * s) b t := by
      have h' := (hasDerivAt_id t).const_mul b
      simpa using h'
    simpa [mul_comm] using h.exp
  -- continuity of the integrand
  have hint_cont : Continuous (fun s : ℝ =>
      Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ) := by
    have h1 : Continuous (fun s : ℝ => Real.exp (-(b * s))) := by fun_prop
    exact (h1.mul hchic).mul hsliceC
  -- fundamental theorem of calculus for the lower limit
  have hH : HasDerivAt (fun v : ℝ => ∫ s in v..(2 * N),
        Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ)
      (-(Real.exp (-(b * t)) * deriv (Work.FTS.EllSol.Trunc.chi N) t * u t θ)) t :=
    intervalIntegral.integral_hasDerivAt_left (hint_cont.intervalIntegrable t (2 * N))
      (hint_cont.stronglyMeasurableAtFilter volume (𝓝 t)) hint_cont.continuousAt
  have hEHd : HasDerivAt (fun v : ℝ => Real.exp (b * v) * ∫ s in v..(2 * N),
        Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ)
      (b * Real.exp (b * t) * (∫ s in t..(2 * N),
          Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ)
        + Real.exp (b * t) * (-(Real.exp (-(b * t))
            * deriv (Work.FTS.EllSol.Trunc.chi N) t * u t θ))) t :=
    hexpD.mul hH
  have hsumd : HasDerivAt (fun v : ℝ => Work.FTS.EllSol.Trunc.chi N v * u v θ
        + Real.exp (b * v) * ∫ s in v..(2 * N),
          Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ)
      ((deriv (Work.FTS.EllSol.Trunc.chi N) t * u t θ
          + Work.FTS.EllSol.Trunc.chi N t * deriv (fun s : ℝ => u s θ) t)
        + (b * Real.exp (b * t) * (∫ s in t..(2 * N),
            Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ)
          + Real.exp (b * t) * (-(Real.exp (-(b * t))
              * deriv (Work.FTS.EllSol.Trunc.chi N) t * u t θ)))) t :=
    hFd.add hEHd
  have hderiv : deriv (fun v : ℝ => Gc N b u v θ) t
      = (deriv (Work.FTS.EllSol.Trunc.chi N) t * u t θ
          + Work.FTS.EllSol.Trunc.chi N t * deriv (fun s : ℝ => u s θ) t)
        + (b * Real.exp (b * t) * (∫ s in t..(2 * N),
            Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ)
          + Real.exp (b * t) * (-(Real.exp (-(b * t))
              * deriv (Work.FTS.EllSol.Trunc.chi N) t * u t θ))) := hsumd.deriv
  have hGct : Gc N b u t θ = Work.FTS.EllSol.Trunc.chi N t * u t θ
      + Real.exp (b * t) * ∫ s in t..(2 * N),
          Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ := rfl
  have hexpneg : Real.exp (b * t) * Real.exp (-(b * t)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  change deriv (fun v : ℝ => Gc N b u v θ) t - b * Gc N b u t θ
      = Work.FTS.EllSol.Trunc.chi N t * (deriv (fun s : ℝ => u s θ) t - b * u t θ)
  rw [hderiv, hGct]
  linear_combination (-(deriv (Work.FTS.EllSol.Trunc.chi N) t * u t θ)) * hexpneg

end Work.FTS.EllSol.ShiftFT
end
-- ===== merged: Submission.Work.FTS.EllSol.ShiftFT.uTrAthree.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT.uTrAthree

open MeasureTheory Set
open scoped Real Topology ENNReal

noncomputable section

set_option autoImplicit false

/-- The tail integral of the `θθ`-derivative of `Gc N b u`: the second `θ`-derivative of
`Gc N b u` equals `chi N t · ∂_θ²u t θ + tailE N b (∂_θ²u) t θ`. -/
def tailE (N b : ℝ) (f : ℝ → ℝ → ℝ) (t θ : ℝ) : ℝ :=
  Real.exp (b * t) * ∫ s in t..(2 * N),
    Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * f s θ



end

end Work.FTS.EllSol.ShiftFT.uTrAthree
end
-- ===== merged: Submission.Work.FTS.EllSol.ShiftFT.uTr_niceFlat =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.EllSol.ShiftFT.uTr_niceFlat`

`uTr N b u = phiTr N · Gc N b u` is the truncated ("nice", i.e. uniformly compactly supported in
`t`) approximant of the shifted construction of `ShiftFT/ShiftPrimDefs.lean`.  The content of the
target theorem is that for `2 ≤ N` this approximant is again a `NiceFlat` datum, i.e. jointly `C²`
on the half-strip, with the two endpoint values `0` and uniformly compact support in `t`.

Everything is elementary except the `C²`-regularity of the variable lower endpoint primitive
`(t,θ) ↦ ∫ s in t..(2N), exp (-(b*s)) * deriv (chi N) s * u s θ`, which is the content of the
`ParamIntSelf` namespace below (a self-contained proof by two-level differentiation under the
integral sign; see also the sibling modules
`Submission/Work/FTS/EllSol/ShiftFT/contDiffOn_integral_variableLower.lean` and
`contDiffOn_intervalIntegral_param_two.lean` for the same statement required of the fleet).
-/

namespace Work.FTS.EllSol.ShiftFT

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-! ## `C²`-regularity of parametric interval integrals

A self-contained proof (no import of the sibling delegated lemmas needed) that a jointly `C²` family
`K` has a `C²` parametric interval integral, both for fixed endpoints and for a variable lower
endpoint.  The route is the two-level induction on the order of differentiability:

* `contDiffOn_fderiv_slice_param'` — the slice derivative `(t,x) ↦ ∂₂K(t,x)` of a jointly `C^{n+1}`
  family is jointly `C^n`;
* `continuousOn_fderiv_slice_param'` — that slice derivative is continuous for `C¹` families;
* `continuousOn_intervalIntegral_param'` — dominated convergence for the parametric interval
  integral (general codomain);
* `hasFDerivAt_intervalIntegral_param'` — differentiation under the integral sign, from Mathlib's
  `hasFDerivAt_integral_of_dominated_of_fderiv_le''` and compactness of the tube;
* `contDiffOn_intervalIntegral_param_one'` — the `C¹` statement;
* `contDiffOn_intervalIntegral_param_two'` — the `C²` statement (with `E := X →L[ℝ] ℝ` for the
  derivative family);
* `contDiffOn_integral_variableLower'` — the variable lower endpoint version, from
  `∫ s in t..c = ∫ s in 0..c - ∫ s in 0..t` and the substitution `∫ s in 0..t = t ∫ v in 0..1, …(t*v)`. -/

namespace ParamIntSelf

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The partial derivative in the second variable of a jointly `C¹` family is the full Fréchet
derivative composed with `inr`. -/
theorem hasFDerivAt_slice_param' {K : ℝ → X → E} {u : Set ℝ} {s : Set X}
    (hu : IsOpen u) (hs : IsOpen s)
    (hK : ContDiffOn ℝ 1 (fun p : ℝ × X => K p.1 p.2) (u ×ˢ s))
    {t : ℝ} {x : X} (ht : t ∈ u) (hx : x ∈ s) :
    HasFDerivAt (fun y => K t y)
      ((fderiv ℝ (fun p : ℝ × X => K p.1 p.2) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ X)) x := by
  have hcd : ContDiffAt ℝ 1 (fun p : ℝ × X => K p.1 p.2) (t, x) :=
    (hK (t, x) ⟨ht, hx⟩).contDiffAt ((hu.prod hs).mem_nhds ⟨ht, hx⟩)
  have hfd : HasFDerivAt (fun p : ℝ × X => K p.1 p.2)
      (fderiv ℝ (fun p : ℝ × X => K p.1 p.2) (t, x)) (t, x) :=
    hcd.differentiableAt_one.hasFDerivAt
  have hpair : HasFDerivAt (fun y : X => (t, y)) (ContinuousLinearMap.inr ℝ ℝ X) x := by
    have h : HasFDerivAt (fun y : X => ContinuousLinearMap.inr ℝ ℝ X y)
        (ContinuousLinearMap.inr ℝ ℝ X) x :=
      ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.inr ℝ ℝ X)
    have h' : HasFDerivAt (fun y : X => (t, (0 : X)) + ContinuousLinearMap.inr ℝ ℝ X y)
        (ContinuousLinearMap.inr ℝ ℝ X) x := h.const_add (t, (0 : X))
    simpa using h'
  simpa only [Function.comp_def] using hfd.comp x hpair

/-- The family `(t,x) ↦ ∂₂K(t,x)` is jointly `C^n` when `K` is jointly `C^{n+1}`. -/
theorem contDiffOn_fderiv_slice_param' {K : ℝ → X → E} {u : Set ℝ} {s : Set X}
    (hu : IsOpen u) (hs : IsOpen s) (n : ℕ)
    (hK : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ENat)
      (fun p : ℝ × X => K p.1 p.2) (u ×ˢ s)) :
    ContDiffOn ℝ (n : WithTop ENat)
      (fun p : ℝ × X => fderiv ℝ (fun y => K p.1 y) p.2) (u ×ˢ s) := by
  have hK1 : ContDiffOn ℝ 1 (fun p : ℝ × X => K p.1 p.2) (u ×ˢ s) :=
    hK.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
  have h1 : ContDiffOn ℝ (n : WithTop ENat)
      (fderiv ℝ (fun p : ℝ × X => K p.1 p.2)) (u ×ˢ s) :=
    hK.fderiv_of_isOpen (hu.prod hs) (by rw [Nat.cast_add, Nat.cast_one])
  have h2 : ContDiffOn ℝ (n : WithTop ENat)
      (fun p : ℝ × X => ((ContinuousLinearMap.compL ℝ X (ℝ × X) E).flip
        (ContinuousLinearMap.inr ℝ ℝ X)) (fderiv ℝ (fun p : ℝ × X => K p.1 p.2) p)) (u ×ˢ s) :=
    (((ContinuousLinearMap.compL ℝ X (ℝ × X) E).flip
      (ContinuousLinearMap.inr ℝ ℝ X))).contDiff.comp_contDiffOn h1
  exact h2.congr fun p hp => (hasFDerivAt_slice_param' hu hs hK1 hp.1 hp.2).fderiv

/-- The slice derivative of a jointly `C¹` family is continuous on the product of the open sets. -/
theorem continuousOn_fderiv_slice_param' {K : ℝ → X → E} {u : Set ℝ} {s : Set X}
    (hu : IsOpen u) (hs : IsOpen s)
    (hK : ContDiffOn ℝ 1 (fun p : ℝ × X => K p.1 p.2) (u ×ˢ s)) :
    ContinuousOn (fun p : ℝ × X => fderiv ℝ (fun y => K p.1 y) p.2) (u ×ˢ s) := by
  have h1 : ContinuousOn (fun p : ℝ × X => fderiv ℝ (fun p : ℝ × X => K p.1 p.2) p) (u ×ˢ s) :=
    hK.continuousOn_fderiv_of_isOpen (hu.prod hs) le_rfl
  have h2 : Continuous fun L : (ℝ × X) →L[ℝ] E => L.comp (ContinuousLinearMap.inr ℝ ℝ X) :=
    (((ContinuousLinearMap.compL ℝ X (ℝ × X) E).flip
      (ContinuousLinearMap.inr ℝ ℝ X)) : ((ℝ × X) →L[ℝ] E) →L[ℝ] (X →L[ℝ] E)).continuous
  refine (h2.continuousOn.comp h1 (fun p _ => Set.mem_univ _)).congr fun p hp => ?_
  exact (hasFDerivAt_slice_param' hu hs hK hp.1 hp.2).fderiv

/-- **Continuity of a parametric interval integral** (general codomain). -/
theorem continuousOn_intervalIntegral_param' [ProperSpace X]
    {K : ℝ → X → E} {s : Set X} {u : Set ℝ} {a b : ℝ}
    (hs : IsOpen s) (hab : a ≤ b) (hsub : Set.Icc a b ⊆ u)
    (hK : ContinuousOn (fun p : ℝ × X => K p.1 p.2) (u ×ˢ s)) :
    ContinuousOn (fun x => ∫ t in a..b, K t x) s := by
  have hIoc : Set.uIoc a b ⊆ Set.Icc a b := fun t ht => by
    rw [Set.uIoc_of_le hab] at ht
    exact ⟨le_of_lt ht.1, ht.2⟩
  have hsubIoc : Set.uIoc a b ⊆ u := fun t ht => hsub (hIoc ht)
  intro x₀ hx₀
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hx₀)
  have hρ : 0 < δ / 2 := by positivity
  have hsubρ : Metric.closedBall x₀ (δ / 2) ⊆ s :=
    (Metric.closedBall_subset_ball (by linarith)).trans hδs
  have hcont : ContinuousOn (fun p : ℝ × X => K p.1 p.2)
      (Set.Icc a b ×ˢ Metric.closedBall x₀ (δ / 2)) := hK.mono (Set.prod_mono hsub hsubρ)
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc.prod (isCompact_closedBall x₀ (δ / 2))).exists_bound_of_continuousOn hcont
  have hslice : ∀ x ∈ s, ContinuousOn (fun t : ℝ => K t x) (Set.Icc a b) := by
    intro x hx
    exact hK.comp (continuous_id.prodMk continuous_const).continuousOn (fun t ht => ⟨hsub ht, hx⟩)
  refine intervalIntegral.continuousWithinAt_of_dominated_interval (bound := fun _ => C) ?_ ?_
    intervalIntegrable_const ?_
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact ((hslice x hx).mono hIoc).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds x₀ hρ)] with x hx
    refine Eventually.of_forall fun t ht => ?_
    exact hC (t, x) ⟨hIoc ht, Metric.ball_subset_closedBall hx⟩
  · refine Eventually.of_forall fun t ht => ?_
    have htu : t ∈ u := hsubIoc ht
    have ht' : (t, x₀) ∈ u ×ˢ s := ⟨htu, hx₀⟩
    exact (hK.continuousWithinAt ht').comp
      (continuousWithinAt_const.prodMk continuousWithinAt_id) (fun x hx => ⟨htu, hx⟩)

/-- **Differentiation under the integral sign**, general codomain `E`, fixed endpoints. -/
theorem hasFDerivAt_intervalIntegral_param' [ProperSpace X]
    {K : ℝ → X → E} {u : Set ℝ} {s : Set X} {a b : ℝ}
    (hs : IsOpen s) (hu : IsOpen u) (hab : a ≤ b) (hsub : Set.Icc a b ⊆ u)
    (hK : ContDiffOn ℝ 1 (fun p : ℝ × X => K p.1 p.2) (u ×ˢ s)) {x₀ : X} (hx₀ : x₀ ∈ s) :
    HasFDerivAt (fun x => ∫ t in a..b, K t x) (∫ t in a..b, fderiv ℝ (fun y => K t y) x₀) x₀ := by
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hx₀)
  have hε2 : 0 < ε / 2 := by positivity
  have hdie : Metric.closedBall x₀ (ε / 2) ⊆ s :=
    (Metric.closedBall_subset_ball (by linarith)).trans hεs
  have hcont : ContinuousOn (fun p : ℝ × X => fderiv ℝ (fun y => K p.1 y) p.2)
      (Set.Icc a b ×ˢ Metric.closedBall x₀ (ε / 2)) :=
    (continuousOn_fderiv_slice_param' hu hs hK).mono (Set.prod_mono hsub hdie)
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc.prod (isCompact_closedBall x₀ (ε / 2))).exists_bound_of_continuousOn hcont
  have hsubIoc : Set.uIoc a b ⊆ Set.Icc a b := by
    rw [Set.uIoc_of_le hab]; exact Set.Ioc_subset_Icc_self
  have hslice (x : X) (hx : x ∈ s) : ContinuousOn (fun t : ℝ => K t x) (Set.Icc a b) :=
    hK.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨hsub ht, hx⟩)
  have hslice' : ContinuousOn (fun t : ℝ => fderiv ℝ (fun y => K t y) x₀) (Set.Icc a b) :=
    (continuousOn_fderiv_slice_param' hu hs hK).comp
      (continuous_id.prodMk continuous_const).continuousOn (fun t ht => ⟨hsub ht, hx₀⟩)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le'' (μ := volume) (x₀ := x₀)
    (s := Metric.ball x₀ (ε / 2) ∩ s)
    (F := fun x t => K t x) (F' := fun x t => fderiv ℝ (fun y => K t y) x) (bound := fun _ => M)
    ?_ ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
  · exact inter_mem (Metric.ball_mem_nhds x₀ hε2) (hs.mem_nhds hx₀)
  · filter_upwards [hs.mem_nhds hx₀] with x hx
    exact ((hslice x hx).mono hsubIoc).aestronglyMeasurable measurableSet_uIoc
  · exact (hslice x₀ hx₀).intervalIntegrable_of_Icc hab
  · exact (hslice'.mono hsubIoc).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [self_mem_ae_restrict measurableSet_uIoc] with t ht
    intro x hx
    exact hM (t, x) ⟨hsubIoc ht, Metric.ball_subset_closedBall hx.1⟩
  · filter_upwards [self_mem_ae_restrict measurableSet_uIoc] with t ht
    intro x hx
    have h := hasFDerivAt_slice_param' hu hs hK (hsub (hsubIoc ht)) hx.2
    simpa only [h.fderiv] using h

/-- **`C¹` parametric interval integral**, general codomain `E`, fixed endpoints. -/
theorem contDiffOn_intervalIntegral_param_one' [ProperSpace X]
    {K : ℝ → X → E} {u : Set ℝ} {s : Set X} {a b : ℝ}
    (hu : IsOpen u) (hs : IsOpen s) (hab : a ≤ b) (hsub : Set.Icc a b ⊆ u)
    (hK : ContDiffOn ℝ 1 (fun p : ℝ × X => K p.1 p.2) (u ×ˢ s)) :
    ContDiffOn ℝ 1 (fun x => ∫ t in a..b, K t x) s := by
  have hderiv : ContinuousOn (fun x => ∫ t in a..b, fderiv ℝ (fun y => K t y) x) s :=
    continuousOn_intervalIntegral_param' hs hab hsub (continuousOn_fderiv_slice_param' hu hs hK)
  refine (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (s := s)
    (f := fun x => ∫ t in a..b, K t x) (n := (0 : WithTop ENat)) hs.uniqueDiffOn).2 ⟨?_, ?_⟩
  · intro h
    exact absurd h (by simp)
  · refine ⟨fun x => ∫ t in a..b, fderiv ℝ (fun y => K t y) x, (contDiffOn_zero).2 hderiv, ?_⟩
    intro x hx
    exact (hasFDerivAt_intervalIntegral_param' hs hu hab hsub hK hx).hasFDerivWithinAt

/-- **`C²` parametric interval integral**, fixed endpoints. -/
theorem contDiffOn_intervalIntegral_param_two' [ProperSpace X]
    {K : ℝ → X → ℝ} {u : Set ℝ} {s : Set X} {a b : ℝ}
    (hu : IsOpen u) (hs : IsOpen s) (hab : a ≤ b) (hsub : Set.Icc a b ⊆ u)
    (hK : ContDiffOn ℝ 2 (fun p : ℝ × X => K p.1 p.2) (u ×ˢ s)) :
    ContDiffOn ℝ 2 (fun x => ∫ t in a..b, K t x) s := by
  have hK1 : ContDiffOn ℝ 1 (fun p : ℝ × X => K p.1 p.2) (u ×ˢ s) := hK.of_le (by norm_num)
  have hf' : ContDiffOn ℝ 1 (fun x => ∫ t in a..b, fderiv ℝ (fun y => K t y) x) s :=
    contDiffOn_intervalIntegral_param_one' (E := X →L[ℝ] ℝ) hu hs hab hsub
      (contDiffOn_fderiv_slice_param' hu hs 1 hK)
  refine (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (s := s)
    (f := fun x => ∫ t in a..b, K t x) (n := (1 : WithTop ENat)) hs.uniqueDiffOn).2 ⟨?_, ?_⟩
  · intro h
    exact absurd h (by simp)
  · refine ⟨fun x => ∫ t in a..b, fderiv ℝ (fun y => K t y) x, hf', ?_⟩
    intro x hx
    exact (hasFDerivAt_intervalIntegral_param' hs hu hab hsub hK1 hx).hasFDerivWithinAt

/-- The slice `s ↦ F s θ` is continuous when `F` is jointly `C²` on `univ ×ˢ V` and `θ ∈ V`. -/
theorem continuous_slice_of_contDiffOn' {F : ℝ → ℝ → ℝ} {V : Set ℝ}
    (hF : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => F p.1 p.2) (Set.univ ×ˢ V))
    {θ : ℝ} (hθ : θ ∈ V) : Continuous (fun s : ℝ => F s θ) := by
  have hcont : ContinuousOn (fun s : ℝ => F s θ) Set.univ :=
    hF.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s _ => ⟨trivial, hθ⟩)
  exact continuousOn_univ.mp hcont

/-- **The variable lower endpoint primitive of a jointly `C²` family is `C²`.** -/
theorem contDiffOn_integral_variableLower' (F : ℝ → ℝ → ℝ) {V : Set ℝ} (hV : IsOpen V) (c : ℝ)
    (hF : ContDiffOn ℝ 2 (Function.uncurry F) (Set.univ ×ˢ V)) :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ => ∫ s in p.1..c, F s p.2) (Set.univ ×ˢ V) := by
  have hF' : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => F p.1 p.2) (Set.univ ×ˢ V) := hF
  -- the `θ`-only piece
  have hA : ContDiffOn ℝ 2 (fun θ : ℝ => ∫ s in (0 : ℝ)..c, F s θ) V := by
    rcases le_or_gt (0 : ℝ) c with hc | hc
    · exact contDiffOn_intervalIntegral_param_two' (X := ℝ) (K := fun s θ => F s θ)
        (u := Set.univ) (s := V) (a := 0) (b := c) isOpen_univ hV hc (fun _ _ => trivial) hF'
    · have h2 := contDiffOn_intervalIntegral_param_two' (X := ℝ) (K := fun s θ => F s θ)
        (u := Set.univ) (s := V) (a := c) (b := 0) isOpen_univ hV (le_of_lt hc)
        (fun _ _ => trivial) hF'
      have heq : (fun θ : ℝ => ∫ s in (0 : ℝ)..c, F s θ) = fun θ => -∫ s in c..0, F s θ := by
        funext θ; rw [intervalIntegral.integral_symm]
      rw [heq]
      exact h2.neg
  -- the rescaled piece
  have hB : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => ∫ v in (0 : ℝ)..1, F (p.1 * v) p.2)
      (Set.univ ×ˢ V) := by
    have hK : ContDiffOn ℝ 2 (fun q : ℝ × (ℝ × ℝ) => F (q.2.1 * q.1) q.2.2)
        (Set.univ ×ˢ (Set.univ ×ˢ V)) := by
      have hφ : ContDiffOn ℝ 2 (fun q : ℝ × (ℝ × ℝ) => (q.2.1 * q.1, q.2.2))
          (Set.univ ×ˢ (Set.univ ×ˢ V)) := by fun_prop
      exact hF'.comp hφ (fun q hq => ⟨trivial, hq.2.2⟩)
    exact contDiffOn_intervalIntegral_param_two' (X := ℝ × ℝ) (K := fun v p => F (p.1 * v) p.2)
      (u := Set.univ) (s := Set.univ ×ˢ V) (a := 0) (b := 1) isOpen_univ
      (isOpen_univ.prod hV) (by norm_num) (fun _ _ => trivial) hK
  have hAs : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => ∫ s in (0 : ℝ)..c, F s p.2)
      (Set.univ ×ˢ V) :=
    hA.comp (contDiffOn_snd (s := Set.univ ×ˢ V)) (fun p hp => hp.2)
  refine (hAs.sub (contDiffOn_fst (s := Set.univ ×ˢ V) |>.mul hB)).congr fun p hp => ?_
  obtain ⟨t, θ⟩ := p
  have hslice : Continuous (fun s : ℝ => F s θ) := continuous_slice_of_contDiffOn' hF' hp.2
  have hsub : (∫ s in (0 : ℝ)..t, F s θ) = t * ∫ v in (0 : ℝ)..1, F (t * v) θ := by
    have h := intervalIntegral.smul_integral_comp_mul_left (a := (0 : ℝ)) (b := (1 : ℝ))
      (f := fun v : ℝ => F v θ) t
    simpa [smul_eq_mul] using h.symm
  have hsplit : (∫ s in t..c, F s θ) = (∫ s in (0 : ℝ)..c, F s θ) - ∫ s in (0 : ℝ)..t, F s θ := by
    have h := intervalIntegral.integral_interval_sub_left (f := fun s : ℝ => F s θ)
      (hslice.intervalIntegrable (μ := volume) (0 : ℝ) c)
      (hslice.intervalIntegrable (μ := volume) (0 : ℝ) t)
    linarith [h]
  rw [hsplit, hsub]

end ParamIntSelf

/-! ## Auxiliary: `C^n`-regularity of `p ↦ g p.1` on a strip -/

private lemma contDiffOn_fst_comp {g : ℝ → ℝ} {n : WithTop ENat} (hg : ContDiff ℝ n g)
    (V : Set ℝ) : ContDiffOn ℝ n (fun p : ℝ × ℝ => g p.1) (Set.univ ×ˢ V) :=
  (hg.comp_contDiffOn contDiff_fst.contDiffOn).mono (Set.subset_univ _)

/-! ## The target -/

theorem uTr_niceFlat (N b : ℝ) (u : ℝ → ℝ → ℝ) (hN : 2 ≤ N)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (h0 : ∀ t : ℝ, u t 0 = 0) (h1 : ∀ t : ℝ, u t (Real.pi / 2) = 0) :
    Work.FTS.EllSol.FlatFT.NiceFlat (Work.FTS.EllSol.ShiftFT.uTr N b u) := by
  have hV : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have huf : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => u p.1 p.2)
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := hu
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ContDiffOn ℝ 2 (fun p : ℝ × ℝ => phiTr N p.1 * Gc N b u p.1 p.2)
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))
    have hphi : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => phiTr N p.1)
        (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      contDiffOn_fst_comp (phiTr_contDiff 2 N) _
    have hchi : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Trunc.chi N p.1)
        (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      contDiffOn_fst_comp (Trunc.chi_contDiff 2 N) _
    have hdchi : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => deriv (Trunc.chi N) p.1)
        (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      contDiffOn_fst_comp ((Trunc.chi_contDiff 3 N).deriv') _
    have hexp1 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.exp (-(b * p.1)))
        (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      contDiffOn_fst_comp (((contDiff_const.mul contDiff_id).neg).exp) _
    have hexp2 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.exp (b * p.1))
        (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      contDiffOn_fst_comp ((contDiff_const.mul contDiff_id).exp) _
    have hH : ContDiffOn ℝ 2
        (Function.uncurry (fun s θ => Real.exp (-(b * s)) * deriv (Trunc.chi N) s * u s θ))
        (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      show ContDiffOn ℝ 2
        (fun p : ℝ × ℝ => Real.exp (-(b * p.1)) * deriv (Trunc.chi N) p.1 * u p.1 p.2) _
      exact (hexp1.mul hdchi).mul huf
    have hInt : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
        ∫ s in p.1..(2 * N), Real.exp (-(b * s)) * deriv (Trunc.chi N) s * u s p.2)
        (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      ParamIntSelf.contDiffOn_integral_variableLower'
        (fun s θ => Real.exp (-(b * s)) * deriv (Trunc.chi N) s * u s θ) hV (2 * N) hH
    have hGc : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Gc N b u p.1 p.2)
        (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (hchi.mul huf).add (hexp2.mul hInt)
    exact hphi.mul hGc
  · intro t
    show phiTr N t * Gc N b u t 0 = 0
    have hz : Gc N b u t 0 = 0 := by
      show Trunc.chi N t * u t 0
        + Real.exp (b * t) * ∫ s in t..(2 * N),
            Real.exp (-(b * s)) * deriv (Trunc.chi N) s * u s 0 = 0
      simp [h0]
    rw [hz, mul_zero]
  · intro t
    show phiTr N t * Gc N b u t (Real.pi / 2) = 0
    have hz : Gc N b u t (Real.pi / 2) = 0 := by
      show Trunc.chi N t * u t (Real.pi / 2)
        + Real.exp (b * t) * ∫ s in t..(2 * N),
            Real.exp (-(b * s)) * deriv (Trunc.chi N) s * u s (Real.pi / 2) = 0
      simp [h1]
    rw [hz, mul_zero]
  · refine ⟨8192 * N, fun t θ ht => ?_⟩
    have hz : phiTr N t = 0 := by
      rw [phiTr_eq_chi]
      exact Trunc.chi_eq_zero (N := 4096 * N) (by linarith) (by linarith)
    show phiTr N t * Gc N b u t θ = 0
    rw [hz, zero_mul]

end

end Work.FTS.EllSol.ShiftFT
end
-- ===== merged: Submission.Work.FTS.EllSol.VopAux.TraceAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.VopAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped Real Topology
open MeasureTheory Set Filter

/-!
# Auxiliary lemmas for the angular Poincaré estimate in the weak (trace) class

Slices of `C^∞`-on-the-open-quadrant data at a fixed `z > 0`, Clairaut for `∂_θ²` and `D_z^j`
on the open quadrant, the congruence of `D_θ`-iterates of functions agreeing on the open
interval, the a.e. strong measurability of the `z`-integral of the `ℋ^k`-integrand, and the
integrability of the individual summands of the `j`-th slice group of `∂_θ² f`.
-/

/-- `Real.sqrt x ≤ max 1 x`. -/
lemma sqrt_le_max_one (x : ℝ) : Real.sqrt x ≤ max 1 x := by
  have h1 : 0 ≤ max 1 x := le_trans zero_le_one (le_max_left _ _)
  have h2 : x ≤ (max 1 x) ^ 2 := by
    calc x ≤ max 1 x := le_max_right _ _
      _ ≤ (max 1 x) * (max 1 x) := le_mul_of_one_le_left h1 (le_max_left _ _)
      _ = (max 1 x) ^ 2 := by ring
  calc Real.sqrt x ≤ Real.sqrt ((max 1 x) ^ 2) := Real.sqrt_le_sqrt h2
    _ = max 1 x := Real.sqrt_sq h1

/-- The angular weight `thEta` is continuous on the open interval. -/
lemma continuousOn_thEta : ContinuousOn Work.FTS.EllipticEst.thEta
    (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  refine hsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt ?_))
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The angular weight `thGam α` is continuous on the open interval. -/
lemma continuousOn_thGam (α : ℝ) : ContinuousOn (Work.FTS.EllipticEst.thGam α)
    (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  refine hsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt ?_))
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The `θ`-slices of a function `C^∞` on the open quadrant are `C^∞` on the open interval. -/
lemma contDiffOn_slice_of_smoothOpen {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) {z : ℝ} (hz : 0 < z) :
    ∀ n : ℕ, ContDiffOn ℝ n (fun θ => g z θ) (Set.Ioo 0 (Real.pi / 2)) :=
  fun n => contDiffOn_iff_forall_nat_le.mp (hg.curry_θ hz) n le_top

/-- **Clairaut for `∂_θ²` and `D_z^j` on the open quadrant**: the second angular derivative of
the slice `θ' ↦ D_z^j f z θ'` is the `j`-th slice of `∂_θ²f`. -/
lemma sliceV_DzIter_openQ {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (j : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ') θ
      = Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ := by
  have h1 : ∀ θ' ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.pth (Work.Spaces.DzIter j f) z θ'
        = Work.Spaces.DzIter j (Work.Spaces.pth f) z θ' :=
    fun θ' hθ' => Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0 hf.forall j
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ'.1, hθ'.2⟩)
  have h2 : ∀ θ' ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.pth (Work.Spaces.DzIter j (Work.Spaces.pth f)) z θ'
        = Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.pth f)) z θ' :=
    fun θ' hθ' => Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0 hf.pth.forall j
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ'.1, hθ'.2⟩)
  have h3 : Work.Spaces.pthIter 2 f = Work.Spaces.pth (Work.Spaces.pth f) := rfl
  rw [h3]
  have e1 : Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ') θ
      = deriv (fun θ' => Work.Spaces.pth (Work.Spaces.DzIter j f) z θ') θ := rfl
  rw [e1]
  have hev1 : (fun θ' => Work.Spaces.pth (Work.Spaces.DzIter j f) z θ')
      =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pth f) z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact h1 θ' hθ'
  rw [hev1.deriv_eq]
  have e2 : deriv (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pth f) z θ') θ
      = Work.Spaces.pth (Work.Spaces.DzIter j (Work.Spaces.pth f)) z θ := rfl
  rw [e2]
  exact h2 θ hθ

/-- The `D_θ`-iterates of two functions agreeing at every interior angle agree there. -/
lemma LopIter_congr_Ioo {u v : ℝ → ℝ}
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), u θ = v θ) :
    ∀ i : ℕ, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.LopIter i u θ = Work.FTS.EllipticEst.LopIter i v θ := by
  intro i
  induction i with
  | zero => intro θ hθ; exact h θ hθ
  | succ i ih =>
      intro θ hθ
      have heq : (fun θ' => Work.FTS.EllipticEst.LopIter i u θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.FTS.EllipticEst.LopIter i v θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih θ' hθ'
      simp only [Work.FTS.EllipticEst.LopIter_succ, Work.Spaces.Lop]
      rw [heq.deriv_eq]

/-- `L^m` of the second derivative of the `j`-th slice is the mixed derivative
`D_z^j D_θ^m (∂_θ²f)`. -/
lemma LopIter_sliceV_DzIter_eq_mixed_openQ {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (j m : ℕ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.FTS.EllipticEst.LopIter m
        (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ
      = Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ := by
  have hpth2 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 f) := by
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using hf.pth.pth
  have hfun : ∀ θ' ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.sliceV (fun θ'' => Work.Spaces.DzIter j f z θ'') θ'
        = Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ' :=
    fun θ' hθ' => sliceV_DzIter_openQ hf j hz hθ'
  rw [LopIter_congr_Ioo hfun m θ hθ]
  have hslice := Work.FTS.EllipticEst.LopIter_slice m
    (fun z θ => Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ) z
  have hval : Work.FTS.EllipticEst.LopIter m
        (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ') θ
      = Work.Spaces.DthIter m (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f)) z θ :=
    congrFun hslice θ
  rw [hval]
  exact Work.FTS.EllipticEst.DthIter_DzIter_eq_mixed_open hpth2.forall j m hz hθ

/-- The `θ`-integral of the `ℋ^k`-integrand is a.e. strongly measurable as a function of `z`. -/
lemma aesm_integral_HkIntegrand (α : ℝ) (k : ℕ) {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hX : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k g p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (hg.continuousOn_HkIntegrand α k)
  have h2 := hX.integral_prod_right' (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
  simpa using h2

/-- A slice group is integrable on `Iθ` as soon as the whole `ℋ^k`-integrand of the same
function is. -/
lemma integrableOn_sliceGroup_of_HkIntegrand {α : ℝ} {k j : ℕ} {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) {z : ℝ} (hz : 0 < z) (hj : j ≤ k)
    (hInt : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α k F z θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.sliceGroup α k j F z θ)
      Work.Spaces.Iθ := by
  refine MeasureTheory.Integrable.mono' hInt ?_ ?_
  · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sliceGroup α k j F p.1 p.2)
      (Work.FTS.EllipticEst.continuousOn_sliceGroup_Q0 hF α k j) hz
  · exact Filter.Eventually.of_forall fun θ => by
      rw [Real.norm_of_nonneg (Work.FTS.EllipticEst.sliceGroup_nonneg α k j F z θ)]
      exact Work.FTS.EllipticEst.sliceGroup_le_HkIntegrand α k j F z θ
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

/-- Integrability of the `η`-weighted square of the second derivative of the `j`-th slice. -/
lemma integrableOn_sliceV_thEta {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) {z : ℝ} (hz : 0 < z) {j : ℕ} (hj : j ≤ k)
    (hInt : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ)
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ =>
      (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
  have hwpos : 0 < Work.Spaces.w z := by
    rw [Work.Spaces.w]; exact div_pos (pow_pos (by linarith) 2) (pow_pos hz 2)
  have hwne : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hwpos)
  refine MeasureTheory.Integrable.mono'
    (hInt.const_mul ((Work.Spaces.w z) ^ 2)⁻¹) ?_ ?_
  · -- a.e. strong measurability: continuity of the slice data on the open interval
    have hsm : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' => Work.Spaces.DzIter j f z θ')
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := (hf.DzIter j).curry_θ hz
    have hd1 : ContDiffOn ℝ Work.Stability.smoothOrder
        (deriv (fun θ' => Work.Spaces.DzIter j f z θ')) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      hsm.deriv_of_isOpen isOpen_Ioo (le_of_eq Work.FTS.LocData.smoothOrder_add_one)
    have hd2 : ContDiffOn ℝ Work.Stability.smoothOrder
        (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ'))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      hd1.deriv_of_isOpen isOpen_Ioo (le_of_eq Work.FTS.LocData.smoothOrder_add_one)
    have hcont : ContinuousOn (fun θ =>
        (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ ^ 2
          * Work.FTS.EllipticEst.thEta θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (hd2.continuousOn.pow 2).mul continuousOn_thEta
    rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
    exact hcont.aestronglyMeasurable measurableSet_Ioo
  · rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
    refine ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ => ?_
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
    have hval := sliceV_DzIter_openQ hf j hz hθ
    have hw := Work.FTS.EllipticEst.w_div_sin_sq hθI z
    have hsq := Work.Spaces.sq_le_HkIntegrand_z α k (Work.Spaces.pthIter 2 f) z θ j hj
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.thEta_nonneg hθI)), hval]
    have hkey : (Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ
        = ((Work.Spaces.w z) ^ 2)⁻¹
          * ((Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
      rw [mul_pow, hw]; field_simp
    rw [hkey]
    exact mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr (sq_nonneg _))

/-- Integrability of the `γ`-weighted squares of the higher angular derivatives of the `j`-th
slice of `∂_θ²f`. -/
lemma integrableOn_sliceV_LopIter {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) {z : ℝ} (hz : 0 < z) {j m : ℕ} (hm : 1 ≤ m)
    (hmj : m + j ≤ k)
    (hInt : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ)
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ =>
      (Work.FTS.EllipticEst.LopIter m
        (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ) ^ 2
        * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ := by
  have hwpos : 0 < Work.Spaces.w z := by
    rw [Work.Spaces.w]; exact div_pos (pow_pos (by linarith) 2) (pow_pos hz 2)
  have hwne : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hwpos)
  -- integrability of the corresponding mixed summand
  have hInt2 : MeasureTheory.IntegrableOn (fun θ =>
      (Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ) ^ 2
        * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono'
      (hInt.const_mul ((Work.Spaces.w z) ^ 2)⁻¹) ?_ ?_
    · have hcont : ContinuousOn (fun θ =>
          (Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ) ^ 2
            * Work.FTS.EllipticEst.thGam α θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        ((((hf.pth.pth).mixed j m).continuousOn.comp
            (continuous_const.prodMk continuous_id).continuousOn
            (fun θ hθ => ⟨hz, hθ⟩)).pow 2).mul (continuousOn_thGam α)
      rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
      exact hcont.aestronglyMeasurable measurableSet_Ioo
    · rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
      refine ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ => ?_
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
      have hmix := Work.FTS.EllipticEst.mix_term_eq (α := α) hθI z
        (Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ)
      have hsq := Work.Spaces.sq_le_HkIntegrand_mixed α k (Work.Spaces.pthIter 2 f)
        z θ m j hm hmj
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
        (Work.FTS.EllipticEst.thGam_nonneg hθI))]
      have hkey : (Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ
          = ((Work.Spaces.w z) ^ 2)⁻¹
            * ((Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ
                * Work.Spaces.Wt α z θ) ^ 2) := by
        rw [hmix, Work.FTS.EllipticEst.sGam_eq_thGam α]; field_simp
      rw [hkey]
      exact mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr (sq_nonneg _))
  -- transport across the a.e. identification of the two functions
  refine hInt2.congr ?_
  rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
  refine ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ => ?_
  show Work.Spaces.mixed j m (Work.Spaces.pthIter 2 f) z θ ^ 2
      * Work.FTS.EllipticEst.thGam α θ
    = Work.FTS.EllipticEst.LopIter m
        (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ ^ 2
      * Work.FTS.EllipticEst.thGam α θ
  rw [LopIter_sliceV_DzIter_eq_mixed_openQ hf j m hz hθ]

/-- Integrability of the slice functional from the integrability of its summands. -/
lemma integrableOn_sliceW_of {K : ℕ} {α : ℝ} {u : ℝ → ℝ}
    (h0 : MeasureTheory.IntegrableOn
      (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hL : ∀ i ∈ Finset.Icc 1 K, MeasureTheory.IntegrableOn (fun θ =>
      (Work.FTS.EllipticEst.LopIter i u θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ)
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => sliceW K α u θ) Work.Spaces.Iθ := by
  have hsum : MeasureTheory.IntegrableOn (fun θ => ∑ i ∈ Finset.Icc 1 K,
      (Work.FTS.EllipticEst.LopIter i u θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ)
      Work.Spaces.Iθ := MeasureTheory.integrable_finsetSum _ hL
  show MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
    + ∑ i ∈ Finset.Icc 1 K,
        (Work.FTS.EllipticEst.LopIter i u θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ)
    Work.Spaces.Iθ
  exact h0.add hsum

/-- The `θ`-integral of the `j`-th slice group of `f` is `w(z)²` times the single-slice
functional of the slice `θ' ↦ D_z^j f z θ'`. -/
lemma integral_sliceGroup_eq_sliceF (α : ℝ) (k j : ℕ) (f : ℝ → ℝ → ℝ) {z : ℝ}
    (hz : 0 < z) (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => sliceW (k - j) α (fun θ' => Work.Spaces.DzIter j f z θ') θ)
      Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α k j f z θ)
      = (Work.Spaces.w z) ^ 2
          * sliceF (k - j) α (fun θ' => Work.Spaces.DzIter j f z θ') := by
  rw [sliceF, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [Work.FTS.EllipticEst.ThetaU.ae_eq_of_forall_Ioo (u := fun θ =>
      Work.FTS.EllipticEst.sliceGroup α k j f z θ)
    (v := fun θ => (Work.Spaces.w z) ^ 2
      * sliceW (k - j) α (fun θ' => Work.Spaces.DzIter j f z θ') θ)
    (fun θ hθ => sliceGroup_eq_sliceW α k j f hz hf.forall θ hθ)] with θ hθ
  exact hθ

/-- The same identity for the slice group of `∂_θ² f`, whose single-slice datum is the second
derivative of the `j`-th slice of `f`. -/
lemma integral_sliceGroup_pthIter2_eq_sliceF (α : ℝ) (k j : ℕ) (f : ℝ → ℝ → ℝ)
    {z : ℝ} (hz : 0 < z) (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => sliceW (k - j) α
        (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ)
      Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ)
      = (Work.Spaces.w z) ^ 2 * sliceF (k - j) α
          (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) := by
  rw [sliceF, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae ?_
  have hpth2 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 f) := by
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using hf.pth.pth
  filter_upwards [Work.FTS.EllipticEst.ThetaU.ae_eq_of_forall_Ioo (u := fun θ =>
      Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pthIter 2 f) z θ)
    (v := fun θ => (Work.Spaces.w z) ^ 2 * sliceW (k - j) α
      (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ)
    (fun θ hθ => by
      rw [sliceGroup_eq_sliceW α k j (Work.Spaces.pthIter 2 f) hz hpth2.forall θ hθ,
        sliceW_pthIter2_eq_sliceW_sliceV α (k - j) j f hz hf.forall θ hθ])] with θ hθ
  exact hθ

end Work.FTS.EllSol.VopAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.aeI1CwBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AngAWeak.aeI1CwBound` — the drift pairing `⟨cw · U, B⟩` in the weak class

Target: `Work.FTS.EllipticEst.AngAWeak.aeI1CwBound`.

With `U = z ∂_z u` (`AngAWeak.i1U u`) and `B = ∂_θθ u` (`AngAWeak.i1B u`), and the weight
`cw z = 2(z-1)/(1+z)` of the radial integration by parts of Step 2 (`prop:H2` of
T. M. Elgindi, Annals **194** (2021)),

  `IP (cw · U) B ≤ 2 √(IP U U) · √(IP B B)`,

where `IP g h = ∫_z ∫_θ g h w²σ`.

This is the drift-term Cauchy–Schwarz of the `I₁` computation, in the almost-everywhere class
`H2W.Ae.AeData` where only the *diagonal* honesties `HkMem α 0 (z∂_z u)` and
`HkMem α 0 (∂_θθu)` are available.

## Route

1. `AngClean.HkMem_zero_IPMem` turns the two `HkMem` hypotheses into the diagonal honesties
   `IPMem U U` and `IPMem B B`;
2. `Work.AngSecond.IPMem_cw_mul_diag` upgrades `IPMem U U` to `IPMem (cw · U) (cw · U)`
   (`|cw| ≤ 2` on `[0,∞)`);
3. the *cross* honesty `IPMem (cw · U) B` is obtained from the two diagonal honesties by the
   AM–GM polarisation `|g h| ≤ (g² + h²)/2`
   (`Work.FTS.EllipticEst.H2W.WeakAux.IPMem_of_diag_open`), which needs only the continuity of
   the two profiles on the open quadrant — supplied by `AeData.smooth` through
   `SmoothOpen` (`smoothOpen_fst_mul_pz`, `smoothOpen_pthIter_two`);
4. Cauchy–Schwarz (`AngSecond.IP_cauchy_schwarz`) then gives
   `|IP (cw·U) B| ≤ √(IP (cw·U) (cw·U)) · √(IP B B)`, and `IP (cw·U) (cw·U) ≤ 4 IP U U`
   because `cw² ≤ 4` on `[0,∞)` (`AngSecond.abs_cw_le_two`).
-/

namespace Work.FTS.EllipticEst.AngAWeak

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

/-- The open quadrant `(0,∞) × (0,π/2)`. -/
private abbrev Quad : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

/-- **The diagonal bound `IP (cw · g) (cw · g) ≤ 4 · IP g g`.**

On `[0,∞)` the weight `cw z = 2(z-1)/(1+z)` is bounded by `2` in absolute value, hence
`cw z² ≤ 4`; slicewise the integrand of `IP (cw · g) (cw · g)` is `cw z²` times that of
`IP g g`.  (The proof is the one of `AngSecond.IP_cwPhi_le`, carried out for an arbitrary `g`,
so that it applies to the weak class without a `SmoothNbhd` hypothesis.) -/
private theorem IP_cw_mul_diag_le {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.AngSecond.IPMem g g)
    (hcw : Work.FTS.EllipticEst.AngSecond.IPMem
      (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * g z θ)
      (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * g z θ)) :
    Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * g z θ)
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * g z θ)
      ≤ 4 * Work.FTS.EllipticEst.AngSecond.IP g g := by
  rw [Work.FTS.EllipticEst.AngSecond.IP, Work.FTS.EllipticEst.AngSecond.IP,
    ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_mono_on hcw.2 (hg.2.const_mul 4) measurableSet_Ici
    (fun z hz => ?_)
  have hI : (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ,
      g z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
        * Work.FTS.EllipticEst.AngSecond.sig θ := by
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
    have h1 : (0 : ℝ) ≤ g z θ * g z θ := mul_self_nonneg _
    have h2 : (0 : ℝ) ≤ g z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z :=
      mul_nonneg h1 (Work.FTS.EllipticEst.AngSecond.w2_nonneg z)
    exact mul_nonneg h2 (Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ)
  have hstep : (∫ θ in Work.Spaces.Iθ,
        (Work.FTS.EllipticEst.AngSecond.cw z * g z θ)
          * (Work.FTS.EllipticEst.AngSecond.cw z * g z θ)
          * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ)
      = Work.FTS.EllipticEst.AngSecond.cw z * Work.FTS.EllipticEst.AngSecond.cw z
        * (∫ θ in Work.Spaces.Iθ, g z θ * g z θ
            * Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ) := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
  rw [hstep]
  have hcq : Work.FTS.EllipticEst.AngSecond.cw z * Work.FTS.EllipticEst.AngSecond.cw z ≤ 4 := by
    have h := abs_le.mp (Work.AngSecond.abs_cw_le_two hz)
    nlinarith [h.1, h.2]
  exact mul_le_mul_of_nonneg_right hcq hI

/-- `cw` is continuous on `(0,∞)`. -/
private theorem continuousOn_cw_Ioi :
    ContinuousOn (fun z : ℝ => Work.FTS.EllipticEst.AngSecond.cw z) (Set.Ioi (0 : ℝ)) := by
  have h : ContinuousOn (fun z : ℝ => 2 * (z - 1) / (1 + z)) (Set.Ioi (0 : ℝ)) :=
    ContinuousOn.div
      ((continuous_const.mul (continuous_id.sub continuous_const)).continuousOn)
      ((continuous_const.add continuous_id).continuousOn)
      (fun z hz => by
        have hz' : (0 : ℝ) < z := hz
        have : (0 : ℝ) < 1 + z := by linarith
        positivity)
  simpa only [Work.FTS.EllipticEst.AngSecond.cw] using h

/-- The uncurried `(z,θ) ↦ cw z` is continuous on the open quadrant. -/
private theorem continuousOn_uncurry_cw :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AngSecond.cw p.1) Quad :=
  continuousOn_cw_Ioi.comp continuous_fst.continuousOn (fun _ hp => hp.1)

theorem aeI1CwBound {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hAe : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AngAWeak.i1U u)) :
    Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
          * Work.FTS.EllipticEst.AngAWeak.i1U u z θ)
        (Work.FTS.EllipticEst.AngAWeak.i1B u)
      ≤ 2 * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
            (Work.FTS.EllipticEst.AngAWeak.i1U u)
            (Work.FTS.EllipticEst.AngAWeak.i1U u))
          * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
              (Work.FTS.EllipticEst.AngAWeak.i1B u)
              (Work.FTS.EllipticEst.AngAWeak.i1B u)) := by
  -- ### The `SmoothOpen` smoothness of the datum on the open quadrant
  have hsm : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => hAe.smooth n)
  -- ### The three honesties
  have hUdiag : Work.FTS.EllipticEst.AngSecond.IPMem
      (Work.FTS.EllipticEst.AngAWeak.i1U u)
      (Work.FTS.EllipticEst.AngAWeak.i1U u) :=
    Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hU
  have hBdiag : Work.FTS.EllipticEst.AngSecond.IPMem
      (Work.FTS.EllipticEst.AngAWeak.i1B u)
      (Work.FTS.EllipticEst.AngAWeak.i1B u) :=
    Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hAe.memAng2
  have hCwU : Work.FTS.EllipticEst.AngSecond.IPMem
      (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
        * Work.FTS.EllipticEst.AngAWeak.i1U u z θ)
      (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
        * Work.FTS.EllipticEst.AngAWeak.i1U u z θ) :=
    Work.AngSecond.IPMem_cw_mul_diag hUdiag
  -- ### Continuity of the two profiles on the open quadrant
  have hcontB : ContinuousOn
      (Function.uncurry (Work.FTS.EllipticEst.AngAWeak.i1B u)) Quad :=
    (Work.FTS.EllipticEst.H2W.WeakAux.smoothOpen_pthIter_two hsm).continuousOn
  have hcontU : ContinuousOn
      (Function.uncurry (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
        * Work.FTS.EllipticEst.AngAWeak.i1U u z θ)) Quad :=
    continuousOn_uncurry_cw.mul
      (Work.FTS.EllipticEst.H2W.WeakAux.smoothOpen_fst_mul_pz hsm).continuousOn
  -- ### The cross honesty, by polarisation
  have hcross : Work.FTS.EllipticEst.AngSecond.IPMem
      (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
        * Work.FTS.EllipticEst.AngAWeak.i1U u z θ)
      (Work.FTS.EllipticEst.AngAWeak.i1B u) :=
    Work.FTS.EllipticEst.H2W.WeakAux.IPMem_of_diag_open hcontU hcontB hCwU hBdiag
  -- ### Cauchy–Schwarz
  have hcs : |Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
          * Work.FTS.EllipticEst.AngAWeak.i1U u z θ)
        (Work.FTS.EllipticEst.AngAWeak.i1B u)|
      ≤ Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
            (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
              * Work.FTS.EllipticEst.AngAWeak.i1U u z θ)
            (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
              * Work.FTS.EllipticEst.AngAWeak.i1U u z θ))
          * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
              (Work.FTS.EllipticEst.AngAWeak.i1B u)
              (Work.FTS.EllipticEst.AngAWeak.i1B u)) :=
    Work.FTS.EllipticEst.AngSecond.IP_cauchy_schwarz hCwU hBdiag hcross
  -- ### The diagonal comparison and the square root
  have hdiagle : Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
          * Work.FTS.EllipticEst.AngAWeak.i1U u z θ)
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
          * Work.FTS.EllipticEst.AngAWeak.i1U u z θ)
      ≤ 4 * Work.FTS.EllipticEst.AngSecond.IP
          (Work.FTS.EllipticEst.AngAWeak.i1U u)
          (Work.FTS.EllipticEst.AngAWeak.i1U u) :=
    IP_cw_mul_diag_le hUdiag hCwU
  have hsqrt : Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
          * Work.FTS.EllipticEst.AngAWeak.i1U u z θ)
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
          * Work.FTS.EllipticEst.AngAWeak.i1U u z θ))
      ≤ 2 * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
          (Work.FTS.EllipticEst.AngAWeak.i1U u)
          (Work.FTS.EllipticEst.AngAWeak.i1U u)) := by
    have h4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    calc Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
            (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
              * Work.FTS.EllipticEst.AngAWeak.i1U u z θ)
            (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
              * Work.FTS.EllipticEst.AngAWeak.i1U u z θ))
        ≤ Real.sqrt (4 * Work.FTS.EllipticEst.AngSecond.IP
            (Work.FTS.EllipticEst.AngAWeak.i1U u)
            (Work.FTS.EllipticEst.AngAWeak.i1U u)) := Real.sqrt_le_sqrt hdiagle
      _ = Real.sqrt 4 * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
            (Work.FTS.EllipticEst.AngAWeak.i1U u)
            (Work.FTS.EllipticEst.AngAWeak.i1U u)) := Real.sqrt_mul (by norm_num) _
      _ = 2 * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
            (Work.FTS.EllipticEst.AngAWeak.i1U u)
            (Work.FTS.EllipticEst.AngAWeak.i1U u)) := by rw [h4]
  -- ### Assembly
  calc Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
          * Work.FTS.EllipticEst.AngAWeak.i1U u z θ)
        (Work.FTS.EllipticEst.AngAWeak.i1B u)
      ≤ |Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
            * Work.FTS.EllipticEst.AngAWeak.i1U u z θ)
          (Work.FTS.EllipticEst.AngAWeak.i1B u)| := le_abs_self _
    _ ≤ Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
            (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
              * Work.FTS.EllipticEst.AngAWeak.i1U u z θ)
            (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z
              * Work.FTS.EllipticEst.AngAWeak.i1U u z θ))
          * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
              (Work.FTS.EllipticEst.AngAWeak.i1B u)
              (Work.FTS.EllipticEst.AngAWeak.i1B u)) := hcs
    _ ≤ (2 * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
            (Work.FTS.EllipticEst.AngAWeak.i1U u)
            (Work.FTS.EllipticEst.AngAWeak.i1U u)))
          * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
              (Work.FTS.EllipticEst.AngAWeak.i1B u)
              (Work.FTS.EllipticEst.AngAWeak.i1B u)) :=
        mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
            (Work.FTS.EllipticEst.AngAWeak.i1U u)
            (Work.FTS.EllipticEst.AngAWeak.i1U u))
          * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
              (Work.FTS.EllipticEst.AngAWeak.i1B u)
              (Work.FTS.EllipticEst.AngAWeak.i1B u)) := by ring

end

end Work.FTS.EllipticEst.AngAWeak
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.Ae.hkMem_ang1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.Ae

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# `HkMem α 0 (∂_θ(tan θ · u))` in the almost-everywhere class

The angular term `ang1 u = ∂_θ(tan θ · u)` of the level-`0` estimate is honest
(`Work.Spaces.HkMem α 0`) for every datum `AeData α u G` of the almost-everywhere class,
given the honesty of `u` and of `grad u = z ∂_z u`.

## Route

On the open quadrant the equation `bslOp α u = G` rearranges (`scaled_ang1_eq`) to

  `ang1 u = α² z²∂_zz u + G + α(5+α)(z∂_z u) + ∂_θθ u + 6u`,

and each of the five summands is honest: `α² z²∂_zz u` by `AeData.memRad2` and
`HkMem_const_mul`, `G` by `AeData.memG`, `α(5+α)(z∂_z u)` by the hypothesis on `grad u`,
`∂_θθ u` by `AeData.memAng2`, and `6u` by the hypothesis on `u`.  The five-term
Cauchy–Schwarz inequality (`Honest.HkIntegrand_zero_le_five`) turns the pointwise identity
into the domination of the level-`0` integrand of `ang1 u` by `5` times the sum of the five
integrands, and `Work.Blocks.HkMem_of_majorant_aesm` upgrades that to `HkMem` once the
integrability of the majorant (on every angular slice, and of its `z`-integral) and the a.e.
strong measurability of the target integrand are supplied.  The latter follows from the
`C^∞`-regularity of `ang1 u = ∂_θ(tan θ·u)` on the open quadrant (`SmoothOpen`).
-/

/-! ## The rearrangement of the equation -/

/-- **The equation solved for `∂_θ(tan θ · u)`** on the open quadrant. -/
private theorem scaled_ang1_eq {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) {z θ : ℝ}
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    ang1 u z θ
      = α ^ 2 * rad2 u z θ + G z θ + α * (5 + α) * grad u z θ + ang2 u z θ
        + 6 * u z θ := by
  have h2 := AeData.eq h z hz θ hθ0 hθ1
  simp only [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero, rad2, grad, ang2, ang1] at h2 ⊢
  linarith

/-- `|a + b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e|`. -/
private theorem abs_five_le (a b c d e : ℝ) :
    |a + b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
  have h1 := abs_add_le (a + b + c + d) e
  have h2 := abs_add_le (a + b + c) d
  have h3 := abs_add_le (a + b) c
  have h4 := abs_add_le a b
  have n1 : 0 ≤ |a + b + c + d| := abs_nonneg _
  have n2 : 0 ≤ |a + b + c| := abs_nonneg _
  have n3 : 0 ≤ |a + b| := abs_nonneg _
  have n4 : 0 ≤ |a| := abs_nonneg _
  have n5 : 0 ≤ |b| := abs_nonneg _
  have n6 : 0 ≤ |c| := abs_nonneg _
  have n7 : 0 ≤ |d| := abs_nonneg _
  have n8 : 0 ≤ |e| := abs_nonneg _
  linarith

/-! ## The pointwise majorant and the integrability bookkeeping -/

/-- Integrability on `Iz` of the `θ`-integral of a pointwise sum of two functions, given the
integrability of the angular slices and of the two `θ`-integrals. -/
private theorem integrableOn_integral_add {f g : ℝ → ℝ → ℝ}
    (hf : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => f z θ) Work.Spaces.Iθ)
    (hg : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => g z θ) Work.Spaces.Iθ)
    (hF : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, f z θ) Work.Spaces.Iz)
    (hG : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, g z θ) Work.Spaces.Iz) :
    IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, f z θ + g z θ) Work.Spaces.Iz := by
  refine (hF.add hG).congr ?_
  filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
    with z hz
  exact (MeasureTheory.integral_add (hf z hz) (hg z hz)).symm

/-- The pointwise majorant of the level-`0` `HkIntegrand` of `∂_θ(tan θ · u)` in the
almost-everywhere class: five times the sum of the `HkIntegrand`s of the five summands of the
rearranged equation `scaled_ang1_eq`. -/
private def Maj (α : ℝ) (G u : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  5 * (Work.Spaces.HkIntegrand α 0 (fun z θ => α ^ 2 * rad2 u z θ) z θ
    + Work.Spaces.HkIntegrand α 0 G z θ
    + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * grad u z θ) z θ
    + Work.Spaces.HkIntegrand α 0 (ang2 u) z θ
    + Work.Spaces.HkIntegrand α 0 (fun z θ => 6 * u z θ) z θ)

/-! ## The main lemma -/

theorem hkMem_ang1 (α : ℝ) (u G : ℝ → ℝ → ℝ) (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (hu : Work.Spaces.HkMem α 0 u) (hd : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)) : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.ang1 u) := by
  -- `ang1 u` is `C^∞` on the open quadrant
  have huS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall (AeData.smooth h)
  have htan : Work.FTS.EllipticEst.SmoothOpen (fun _ : ℝ => Real.tan) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl
  have htanu : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * u z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl htan huS
  have htgt : Work.FTS.EllipticEst.SmoothOpen (ang1 u) :=
    Work.FTS.EllipticEst.SmoothOpen.pth htanu
  have hcont := Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand htgt α 0
  -- the a.e. strong measurability of the integrand of `ang1 u`
  have haesmJoint : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 (ang1 u) p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  have haesmSlice : ∀ z ∈ Work.Spaces.Iz, AEStronglyMeasurable
      (fun θ => Work.Spaces.HkIntegrand α 0 (ang1 u) z θ)
      (volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · rw [show (fun θ => Work.Spaces.HkIntegrand α 0 (ang1 u) z θ) = fun θ => (0 : ℝ) from by
        funext θ
        rw [← hz0, Work.Spaces.HkIntegrand_zero_z]]
      exact aestronglyMeasurable_const
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hzpos
  have haesmOuter : AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (ang1 u) z θ)
      (volume.restrict Work.Spaces.Iz) := haesmJoint.integral_prod_right'
  -- the five summands of the rearranged equation are honest
  have hm1 : Work.Spaces.HkMem α 0 (fun z θ => α ^ 2 * rad2 u z θ) := by
    simpa only [rad2] using
      (Work.FTS.LocData.HkMem_const_mul α 0 (α ^ 2) (AeData.memRad2 h))
  have hm2 : Work.Spaces.HkMem α 0 G := AeData.memG h
  have hm3 : Work.Spaces.HkMem α 0 (fun z θ => (α * (5 + α)) * grad u z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 0 (α * (5 + α)) hd
  have hm4 : Work.Spaces.HkMem α 0 (ang2 u) := by
    simpa only [ang2] using AeData.memAng2 h
  have hm5 : Work.Spaces.HkMem α 0 (fun z θ => 6 * u z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 0 6 hu
  -- integrability of the angular slices of the majorant
  have hMslice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => Maj α G u z θ) Work.Spaces.Iθ := by
    intro z hz
    simp only [Maj]
    have h12 : Integrable (fun θ => Work.Spaces.HkIntegrand α 0
          (fun z θ => α ^ 2 * rad2 u z θ) z θ
        + Work.Spaces.HkIntegrand α 0 G z θ) (volume.restrict Work.Spaces.Iθ) :=
      (hm1.1 z hz).add (hm2.1 z hz)
    have h123 : Integrable (fun θ => (Work.Spaces.HkIntegrand α 0
          (fun z θ => α ^ 2 * rad2 u z θ) z θ
        + Work.Spaces.HkIntegrand α 0 G z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * grad u z θ) z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      h12.add (hm3.1 z hz)
    have h1234 : Integrable (fun θ => ((Work.Spaces.HkIntegrand α 0
          (fun z θ => α ^ 2 * rad2 u z θ) z θ
        + Work.Spaces.HkIntegrand α 0 G z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * grad u z θ) z θ)
        + Work.Spaces.HkIntegrand α 0 (ang2 u) z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      h123.add (hm4.1 z hz)
    have h12345 : Integrable (fun θ => (((Work.Spaces.HkIntegrand α 0
          (fun z θ => α ^ 2 * rad2 u z θ) z θ
        + Work.Spaces.HkIntegrand α 0 G z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * grad u z θ) z θ)
        + Work.Spaces.HkIntegrand α 0 (ang2 u) z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => 6 * u z θ) z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      h1234.add (hm5.1 z hz)
    exact h12345.const_mul 5
  -- integrability of the `θ`-integral of the majorant
  have hMz : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, Maj α G u z θ) Work.Spaces.Iz := by
    have hs1 : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
        (fun z θ => α ^ 2 * rad2 u z θ) z θ) Work.Spaces.Iz := hm1.2
    have hs2 : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.HkIntegrand α 0 (fun z θ => α ^ 2 * rad2 u z θ) z θ
        + Work.Spaces.HkIntegrand α 0 G z θ)) Work.Spaces.Iz :=
      integrableOn_integral_add
        (f := fun z θ => Work.Spaces.HkIntegrand α 0 (fun z θ => α ^ 2 * rad2 u z θ) z θ)
        (g := fun z θ => Work.Spaces.HkIntegrand α 0 G z θ)
        hm1.1 hm2.1 hm1.2 hm2.2
    have hs3 : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        ((Work.Spaces.HkIntegrand α 0 (fun z θ => α ^ 2 * rad2 u z θ) z θ
        + Work.Spaces.HkIntegrand α 0 G z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * grad u z θ) z θ))
        Work.Spaces.Iz :=
      integrableOn_integral_add (f := fun z θ => Work.Spaces.HkIntegrand α 0
          (fun z θ => α ^ 2 * rad2 u z θ) z θ
        + Work.Spaces.HkIntegrand α 0 G z θ)
        (g := fun z θ => Work.Spaces.HkIntegrand α 0
          (fun z θ => (α * (5 + α)) * grad u z θ) z θ)
        (fun z hz => (hm1.1 z hz).add (hm2.1 z hz)) hm3.1 hs2 hm3.2
    have hs4 : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        (((Work.Spaces.HkIntegrand α 0 (fun z θ => α ^ 2 * rad2 u z θ) z θ
        + Work.Spaces.HkIntegrand α 0 G z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * grad u z θ) z θ)
        + Work.Spaces.HkIntegrand α 0 (ang2 u) z θ)) Work.Spaces.Iz :=
      integrableOn_integral_add (f := fun z θ => (Work.Spaces.HkIntegrand α 0
          (fun z θ => α ^ 2 * rad2 u z θ) z θ
        + Work.Spaces.HkIntegrand α 0 G z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * grad u z θ) z θ)
        (g := fun z θ => Work.Spaces.HkIntegrand α 0 (ang2 u) z θ)
        (fun z hz => ((hm1.1 z hz).add (hm2.1 z hz)).add (hm3.1 z hz)) hm4.1 hs3 hm4.2
    have hs5 : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        ((((Work.Spaces.HkIntegrand α 0 (fun z θ => α ^ 2 * rad2 u z θ) z θ
        + Work.Spaces.HkIntegrand α 0 G z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * grad u z θ) z θ)
        + Work.Spaces.HkIntegrand α 0 (ang2 u) z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => 6 * u z θ) z θ)) Work.Spaces.Iz :=
      integrableOn_integral_add (f := fun z θ => ((Work.Spaces.HkIntegrand α 0
          (fun z θ => α ^ 2 * rad2 u z θ) z θ
        + Work.Spaces.HkIntegrand α 0 G z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * grad u z θ) z θ)
        + Work.Spaces.HkIntegrand α 0 (ang2 u) z θ)
        (g := fun z θ => Work.Spaces.HkIntegrand α 0 (fun z θ => 6 * u z θ) z θ)
        (fun z hz => (((hm1.1 z hz).add (hm2.1 z hz)).add (hm3.1 z hz)).add (hm4.1 z hz))
        hm5.1 hs4 hm5.2
    have hkey : (fun z => ∫ θ in Work.Spaces.Iθ, Maj α G u z θ)
        = fun z => 5 * ∫ θ in Work.Spaces.Iθ,
            ((((Work.Spaces.HkIntegrand α 0 (fun z θ => α ^ 2 * rad2 u z θ) z θ
            + Work.Spaces.HkIntegrand α 0 G z θ)
            + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * grad u z θ) z θ)
            + Work.Spaces.HkIntegrand α 0 (ang2 u) z θ)
            + Work.Spaces.HkIntegrand α 0 (fun z θ => 6 * u z θ) z θ) := by
      funext z
      simp only [Maj]
      exact MeasureTheory.integral_const_mul 5 _
    rw [hkey]
    exact hs5.const_mul 5
  -- the pointwise five-term domination
  have hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (ang1 u) z θ ≤ Maj α G u z θ := by
    have hb := Work.FTS.EllipticEst.Honest.HkIntegrand_zero_le_five (α := α) (u := ang1 u)
      (g1 := fun z θ => α ^ 2 * rad2 u z θ) (g2 := G)
      (g3 := fun z θ => (α * (5 + α)) * grad u z θ) (g4 := ang2 u)
      (g5 := fun z θ => 6 * u z θ)
      (fun z hz θ hθ0 hθ1 => by
        have heq := scaled_ang1_eq h hz hθ0 hθ1
        have e : ang1 u z θ = α ^ 2 * rad2 u z θ + G z θ + (α * (5 + α)) * grad u z θ
            + ang2 u z θ + 6 * u z θ := by
          rw [heq]
        rw [e]
        exact abs_five_le _ _ _ _ _)
    intro z hz θ hθ
    simp only [Maj]
    exact hb z hz θ hθ
  exact Work.Blocks.HkMem_of_majorant_aesm α 0 haesmSlice haesmOuter hMslice hMz hle

end

end Work.FTS.EllipticEst.H2W.Ae
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AeMixedAeMem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false

/-! ## The reduction of the target to the finiteness of the iterated `∫⁻` -/


/-! ## The reduction of the target to the `H`-slot `∂_θ²(z∂_zu)`

The mixed slot `z∂_z∂_θu` is the *first* angular derivative of the slice `θ ↦ z ∂_zu(z,θ)`; its
`σ`-honesty follows, at the *same* `z`, from the `σ`-honesty of the *second* angular derivative
`H = ∂_θ²(z∂_zu) = ∂_θ²(D_zu) = D_z(∂_θ²u)` by the one-variable Cauchy trick
(`H2W.slice_deriv_of_sq_deriv_deriv`). -/




/-! ## The `HkMem` form of the two reductions

Every consumer of the mixed slot in the tree carries the slot's honesty in the `HkMem α 0`
form (`Final/AeI1Paper_mix_fts`, `H2W/EllCore/AeI1HonestCore.lean`, `AngAWeak/aeI1Mixed.lean`,
`Cores/AeStep2Aux/i1Paper_weakMixed.lean`, …), i.e.

`HkMem α 0 (fun z θ => z * pz (pth u) z θ)`   (the mixed slot `z ∂_z∂_θu`) or
`HkMem α 0 (pthIter 2 (grad u))`              (the `H`-slot `∂_θ²(z∂_zu)`).

`HkMem α 0 f` is the honesty of `HkIntegrand α 0 f z θ = (f z θ · w z / sin(2θ)^{η/2})²`, which
equals `w(z)² σ(θ) f(z,θ)²`; since `w z ≠ 0` for `z > 0`, the *first* conjunct of `HkMem` (which
holds for **every** `z ∈ Iz`) gives the `σ`-slice honesty of `f` for every `z > 0`.  The bridges
below turn those `HkMem`-form hypotheses into the target. -/

/-- The `k = 0` `HkIntegrand` is `w(z)² · (f z θ)² · σ θ` on `Iθ`. -/
theorem HkIntegrand_zero_eq_w (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (Work.Spaces.w z) ^ 2 * ((f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  have h0 : Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    simp [Work.Spaces.HkIntegrand]
  rw [h0, Work.FTS.EllipticEst.AngSecond.sq_mul_W f hθ]
  simp only [Work.FTS.EllipticEst.AngSecond.w2, Work.FTS.EllipticEst.AngSecond.sig,
    Work.FTS.EllipticEst.sEta]
  ring





end Work.FTS.EllipticEst.H2W
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AeU2.aeU2_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AeU2

set_option autoImplicit false

/-- `Ioi 0` and `Iz = Ici 0` differ by the null singleton `{0}`, hence carry the same restriction
of Lebesgue measure. -/
lemma restrict_Ioi_eq_restrict_Iz :
    MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
      = MeasureTheory.volume.restrict Work.Spaces.Iz :=
  MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici

theorem aeU2_bound : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
    (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) →
    (∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
      ≤ ENNReal.ofReal C
        * ENNReal.ofReal (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u)) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := sliceSigmaTraceZero
  refine ⟨C₁, hC₁pos, ?_⟩
  intro α u G hA h0
  -- the two `z`-slice `∫⁻`'s that occur in the target
  set Φ : ℝ → ENNReal := fun z => ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (u z θ ^ 2 * Work.FTS.EllipticEst.sEta θ) with hΦdef
  set Ψ : ℝ → ENNReal := fun z => ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal ((deriv (fun θ' => deriv (fun θ'' => u z θ'') θ')) θ ^ 2
        * Work.FTS.EllipticEst.sEta θ) with hΨdef
  -- (1) the slicewise bound, for almost every `z`
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Φ z ≤ ENNReal.ofReal C₁ * Ψ z := by
    filter_upwards [h0, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz hzpos
    -- the slice is `C²` on the open interval
    have hsm : ContDiffOn ℝ 2 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
      Work.FTS.EllipticEst.Honest.contDiffOn_slice u hzpos (hA.smooth 2)
    -- the `σ`-weighted square of `∂_θθ u` is integrable on the slice
    have hint : MeasureTheory.IntegrableOn
        (fun θ => (deriv (fun θ' => deriv (fun θ'' => u z θ'') θ')) θ ^ 2
          * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
      have h1 := Work.FTS.EllipticEst.Honest.HkMemSliceSqSigma hA.memAng2 hzpos
      refine h1.congr_fun (fun θ _ => ?_) measurableSet_Icc
      simp only [congrFun (Work.FTS.EllipticEst.Honest.pthIter_two_eq u z) θ]
    -- the trace at `π/2` vanishes in this class
    have hL : Filter.Tendsto (fun θ => u z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
      (Work.FTS.EllipticEst.H2W.AeProof.AeSliceRightTendsto α u G hA z hzpos).1
    have hthis := hC₁ (fun θ => u z θ) hsm hint hz hL
    rwa [hΦdef, hΨdef]
  -- (2) integrate the slicewise bound in `z`
  have hmain : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Φ z)
      ≤ ENNReal.ofReal C₁
        * (∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Ψ z) := by
    calc ∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Φ z
        ≤ ∫⁻ z in Set.Ioi 0,
            ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * (ENNReal.ofReal C₁ * Ψ z) := by
          refine MeasureTheory.lintegral_mono_ae ?_
          filter_upwards [hslice] with z hz
          exact mul_le_mul_right hz _
      _ = ENNReal.ofReal C₁
            * ∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Ψ z := by
          rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal C₁) _
            ENNReal.ofReal_ne_top]
          exact MeasureTheory.lintegral_congr (fun z => by rw [mul_left_comm])
  -- (3) `Ioi 0` and `Iz` carry the same measure
  have hIoi : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Ψ z)
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Ψ z := by
    rw [restrict_Ioi_eq_restrict_Iz]
  -- (4) `Ψ` is the `θθ`-slice of `u`
  have hΨ : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Ψ z)
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal ((Work.Spaces.pthIter 2 u z θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)) := by
    refine MeasureTheory.lintegral_congr (fun z => ?_)
    simp only [hΨdef]
    congr 1
  -- (5) the double `∫⁻` is `ofReal (HkSq α 0 (∂_θθ u))`
  have hHk : ENNReal.ofReal (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u))
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal ((Work.Spaces.pthIter 2 u z θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)) :=
    ofReal_HkSq_eq_lintegral α (Work.Spaces.pthIter 2 u) hA.memAng2
  calc ∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Φ z
      ≤ ENNReal.ofReal C₁
          * (∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Ψ z) := hmain
    _ = ENNReal.ofReal C₁
          * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * Ψ z) := by
        rw [hIoi]
    _ = ENNReal.ofReal C₁
          * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
              * (∫⁻ θ in Work.Spaces.Iθ,
                  ENNReal.ofReal ((Work.Spaces.pthIter 2 u z θ) ^ 2
                    * Work.FTS.EllipticEst.sEta θ))) := by
        rw [hΨ]
    _ = ENNReal.ofReal C₁
          * ENNReal.ofReal (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u)) := by
        rw [hHk]

end Work.FTS.EllipticEst.H2W.AeU2
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AngBW.Chain.Step2Assembly =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `H2W/AngBW/Chain/Step2Assembly` — the arithmetic assembly of Step 2

The body below is a verbatim copy of the three (already proved) arithmetic theorems of
`Submission/Work/FTS/EllipticEst/remov/AeStep2Holds.lean` — `quad_solve_pos`,
`step2Ae_of_pos`, `aeStep1_of_full`, `AeI1LowerPos_of_paper` — with the two *analytic* inputs
`remov.AeStep1Full` and `remov.AeI1Paper` kept as explicit hypotheses.  The point of the copy is
to keep the import cone free of the three still-open leaf modules of `remov/`
(`AeStep1FullHolds`, `AeI1PaperHolds`, `AeI1LowerPosHolds`), so that `Step2` can be assembled
from *proved* versions of the two Props (supplied by the sibling modules
`AngBW/Chain/Step1FullProof` and `AngBW/Chain/I1PaperProof`).
-/

namespace Work.FTS.EllipticEst.H2W.AngBW

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

open Work.FTS.EllipticEst.AngSecond
open Work.FTS.EllipticEst.remov










end Work.FTS.EllipticEst.H2W.AngBW
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AngBW.Step3.Ang1Bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AngBW.S3

open Work.FTS.EllipticEst.Honest
open Work.FTS.EllipticEst.H2W.Ae

set_option autoImplicit false


set_option autoImplicit false

/-! ## The level-`0` integrand does not depend on `α`, and the two names of the angular term -/


/-- The same for the squared norm. -/
theorem HkSq_zero_alpha_eq (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq 0 0 g = Work.Spaces.HkSq α 0 g :=
  (Work.FTS.EllipticEst.Honest.HkSq_zero_eq 0 g).trans
    (Work.FTS.EllipticEst.Honest.HkSq_zero_eq α g).symm

/-- And for the honesty. -/
theorem HkMem_zero_alpha_iff (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkMem α 0 g ↔ Work.Spaces.HkMem 0 0 g := by
  simp only [Work.Spaces.HkMem, Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq]

/-- `Ae.ang1` is `Honest.uOf`: both are `∂_θ(tan θ · u)`. -/
theorem ang1_eq_uOf (u : ℝ → ℝ → ℝ) : ang1 u = Work.FTS.EllipticEst.Honest.uOf u := rfl

/-! ## The pointwise majorant for the `I₄`-quantity -/

/-- **The pointwise domination of the integrand of `POf u`.**  On the open quadrant
`POf u = uOf u - u` (`Honest.pth_tan_mul_eq_open`), and the level-`0` integrand is the square of
the weighted profile, so `(x-y)² ≤ 2x²+2y²` gives the bound; on the two boundary lines the
integrand of `POf u` vanishes and the right-hand side is nonnegative. -/
theorem HkIntegrand_POf_le (α : ℝ) (u : ℝ → ℝ → ℝ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (z θ : ℝ) (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.Honest.POf u) z θ
      ≤ 2 * (Work.Spaces.HkIntegrand α 0 u z θ
        + Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.Honest.uOf u) z θ) := by
  have hnn1 : 0 ≤ Work.Spaces.HkIntegrand α 0 u z θ :=
    Work.FTS.EllipticEst.Honest.HkIntegrand_nonneg α 0 u z θ
  have hnn2 : 0 ≤ Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.Honest.uOf u) z θ :=
    Work.FTS.EllipticEst.Honest.HkIntegrand_nonneg α 0 _ z θ
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_boundary α _ (Or.inl hz0.symm)]
    linarith
  · rcases eq_or_lt_of_le (Set.mem_Icc.mp hθ).1 with hθ0 | hθ0pos
    · rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_boundary α _ (Or.inr (Or.inl hθ0.symm))]
      linarith
    · rcases eq_or_lt_of_le (Set.mem_Icc.mp hθ).2 with hθπ | hθlt
      · rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_boundary α _ (Or.inr (Or.inr hθπ))]
        linarith
      · rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
          Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
          Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq]
        have hid := Work.FTS.EllipticEst.Honest.pth_tan_mul_eq_open hsm hzpos hθ0pos hθlt
        have hpof : Work.FTS.EllipticEst.Honest.POf u z θ
            = Work.FTS.EllipticEst.Honest.uOf u z θ - u z θ := by
          have h : Work.FTS.EllipticEst.Honest.uOf u z θ
              = u z θ + Work.FTS.EllipticEst.Honest.POf u z θ := hid
          linarith
        rw [hpof]
        nlinarith [sq_nonneg (Work.FTS.EllipticEst.Honest.uOf u z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
          + u z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))]

/-! ## Honesty of the `I₄`-quantity from the honesty of `u` and of `∂_θ(tan θ·u)` -/

/-- **`HkMem α 0 (POf u)`**, given `HkMem α 0 u` and `HkMem α 0 (∂_θ(tan θ·u))`.  The proof is
the majorant argument of `Work.Blocks.HkMem_of_majorant_aesm` with the pointwise bound
`HkIntegrand_POf_le`; the a.e. strong measurability hypotheses come from the `C^∞`-regularity
of `POf u` on the open quadrant (`Honest.smoothOpen_POf`). -/
theorem hkMem_POf_of_uOf {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hu : Work.Spaces.HkMem α 0 u)
    (hG : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.Honest.uOf u)) :
    Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.Honest.POf u) := by
  have hS : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllipticEst.Honest.POf u) :=
    Work.FTS.EllipticEst.Honest.smoothOpen_POf hsm
  refine Work.Blocks.HkMem_of_majorant_aesm α 0
    (f := Work.FTS.EllipticEst.Honest.POf u)
    (M := fun z θ => 2 * (Work.Spaces.HkIntegrand α 0 u z θ
      + Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.Honest.uOf u) z θ))
    ?_ ?_ ?_ ?_ ?_
  · -- a.e. strong measurability of every angular slice
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · rw [show (fun θ => Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.Honest.POf u) z θ)
          = fun _ : ℝ => (0 : ℝ) from by
        funext θ
        rw [← hz0]
        exact Work.FTS.EllipticEst.Honest.HkIntegrand_zero_boundary α _ (Or.inl rfl)]
      exact aestronglyMeasurable_const
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.Honest.POf u)
          p.1 p.2)
        (hS.continuousOn_HkIntegrand α 0) hzpos
  · -- a.e. strong measurability of the `θ`-integral
    have hprod : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0
          (Work.FTS.EllipticEst.Honest.POf u) p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.Spaces.aesm_of_continuousOn_Qd _ (hS.continuousOn_HkIntegrand α 0)
    exact hprod.integral_prod_right'
  · -- integrability of the majorant on every slice
    intro z hz
    exact ((hu.1 z hz).add (hG.1 z hz)).const_mul 2
  · -- integrability of the `z`-integral of the majorant
    have h2 : MeasureTheory.IntegrableOn
        (fun z => 2 * ((∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
          + (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.Honest.uOf u) z θ)))
        Work.Spaces.Iz := (hu.2.add hG.2).const_mul 2
    refine MeasureTheory.IntegrableOn.congr_fun h2 (fun z hz => ?_) measurableSet_Ici
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add (hu.1 z hz) (hG.1 z hz)]
  · -- the pointwise domination
    intro z hz θ hθ
    exact HkIntegrand_POf_le α u hsm z θ hz hθ

/-! ## The estimate -/

theorem ang1_bound : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u : ℝ → ℝ → ℝ),
    (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
    (∀ z : ℝ, u z 0 = 0) → (∀ z : ℝ, u z (Real.pi / 2) = 0) →
    Work.Spaces.HkMem α 0 u →
    Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 u) →
    Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.ang1 u) →
    Real.sqrt (Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.ang1 u))
      ≤ C * (Real.sqrt (Work.Spaces.HkSq α 0 u)
          + Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u))) := by
  obtain ⟨C₃, hC₃pos, hC₃b⟩ := Work.FTS.EllipticEst.H2W.AngBW.S3.step3PsiBar
  refine ⟨Real.sqrt 2 * (1 + C₃) + 1, ?_, ?_⟩
  · have h1 : (0 : ℝ) < 1 + C₃ := by linarith
    have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    nlinarith [mul_pos h2 h1]
  · intro α u hsm h0 hπ hu hB hG
    -- the honesty of `POf u` and the two estimates
    have hG' : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.Honest.uOf u) := by
      rwa [← ang1_eq_uOf u]
    have hPmem : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.Honest.POf u) :=
      hkMem_POf_of_uOf hsm hu hG'
    have hu0 : Work.Spaces.HkMem 0 0 u := (HkMem_zero_alpha_iff α u).mp hu
    have hB0 : Work.Spaces.HkMem 0 0 (Work.Spaces.pthIter 2 u) :=
      (HkMem_zero_alpha_iff α _).mp hB
    have hP0 : Work.Spaces.HkMem 0 0 (Work.FTS.EllipticEst.Honest.POf u) :=
      (HkMem_zero_alpha_iff α _).mp hPmem
    have hunion := Work.FTS.EllipticEst.Honest.sqrt_HkSq_uOf_le (α := α) (Ψ := u) hsm hu hPmem
    have hPbar : Real.sqrt (Work.Spaces.HkSq 0 0 (Work.FTS.EllipticEst.Honest.POf u))
        ≤ C₃ * (Real.sqrt (Work.Spaces.HkSq 0 0 u)
          + Real.sqrt (Work.Spaces.HkSq 0 0 (Work.Spaces.pthIter 2 u))) :=
      hC₃b u hsm h0 hπ hu0 hB0 hP0
    have hPbar' : Real.sqrt (Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.Honest.POf u))
        ≤ C₃ * (Real.sqrt (Work.Spaces.HkSq α 0 u)
          + Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u))) := by
      rw [HkSq_zero_alpha_eq α (Work.FTS.EllipticEst.Honest.POf u),
        HkSq_zero_alpha_eq α u, HkSq_zero_alpha_eq α (Work.Spaces.pthIter 2 u)] at hPbar
      exact hPbar
    -- the arithmetic
    have hsu : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 u) := Real.sqrt_nonneg _
    have hsb : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u)) :=
      Real.sqrt_nonneg _
    have hsp : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.Honest.POf u)) :=
      Real.sqrt_nonneg _
    have hr : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have hC₃le : C₃ ≤ 1 + C₃ := by linarith
    have hC₃0 : 0 ≤ C₃ := le_of_lt hC₃pos
    have hS : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 u)
        + Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u)) := by linarith
    have s1 : Real.sqrt 2 * (Real.sqrt (Work.Spaces.HkSq α 0 u)
          + Real.sqrt (Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.Honest.POf u)))
        ≤ Real.sqrt 2 * (Real.sqrt (Work.Spaces.HkSq α 0 u)
          + C₃ * (Real.sqrt (Work.Spaces.HkSq α 0 u)
            + Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u)))) :=
      mul_le_mul_of_nonneg_left (by linarith) hr
    have s2 : Real.sqrt 2 * (Real.sqrt (Work.Spaces.HkSq α 0 u)
          + C₃ * (Real.sqrt (Work.Spaces.HkSq α 0 u)
            + Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u))))
        ≤ Real.sqrt 2 * (1 + C₃) * (Real.sqrt (Work.Spaces.HkSq α 0 u)
            + Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u))) := by
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hr
      nlinarith [hsb]
    have s3 : Real.sqrt 2 * (1 + C₃) * (Real.sqrt (Work.Spaces.HkSq α 0 u)
          + Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u)))
        ≤ (Real.sqrt 2 * (1 + C₃) + 1) * (Real.sqrt (Work.Spaces.HkSq α 0 u)
            + Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u))) := by
      nlinarith [hS]
    rw [ang1_eq_uOf u]
    linarith [hunion, s1, s2, s3]


end Work.FTS.EllipticEst.H2W.AngBW.S3
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.WeakPureAux.towerAscent =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `WeakPureAux/towerAscent` — the level tower, and the ascent/descent of the slice bound

Let `(G, Φ)` be a pair on the open quadrant with `bslOp α Φ = G` there and `Φ` smooth, and write
`Φ_j := ∂_z^j Φ` for the radial levels.  The equation at level `0` in *slice* form is

  `Lzero1 (Φ z ·) = G z · + α²z²·Φ_2(z,·) + α(5+α)z·Φ_1(z,·)`   on `(0, π/2)`
  (`lzero1_slice_eq_of_class` below),

and differentiating it `m` times in `z` (`D_z` commutes with `bslOp α`, `TT.bslOp_DzIter_eq`)
gives the same relation with every level shifted by `m`.  Note that *no* `HkMem` hypothesis is
used: only the equation and the smoothness — so the statements below apply to the shifted data
`(D_z^m G, D_z^m Φ)` as well, which is what makes the full index descent iterative.

Combining the slice tower with the *indicial step* for `Lzero1` (a source of growth
`θ^{-(R+2)}`/`(π/2-θ)^{-(R+2)}` forces a solution of growth `θ^{-R}`/`(π/2-θ)^{-R}`, for `R > 1`,
proved as `WeakPureAux.poleBoundOfSourcePow`) gives the **ascent**:

> if the slices of `G`, `Φ_1` and `Φ_2` at a fixed `z` are all of growth `≤ t^{-(R+2)}`, then the
> slice of `Φ` at that `z` is of growth `≤ t^{-R}`  (`towerAscent_of_eq`);

and its contrapositive, the **descent**:

> if the slice of `Φ` at `z` fails to grow like `t^{-R}`, then one of the three slices `G z ·`,
> `∂_zΦ(z,·)`, `∂_z²Φ(z,·)` fails to grow like `t^{-(R+2)}`  (`towerDescent_of_eq`).

`towerAscent` / `towerDescent` are the `WeakPos0` instances (the class is only used for its
equation and smoothness fields, both of which the general versions take separately).

**Where the argument stops** (`NOTES_weakPhiPoleBound.md` §U): the descent's first alternative —
"the source `G` is to blame" — is not refutable from the class, since `HkMem α 0 G` constrains
`G`'s slice only in the weighted-`L²(sEta)` sense, which admits growth as bad as `t^{-3.5}`.
Closing the target needs the *quantitative* cascade of §K rather than the indicial step alone.
-/

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.WeakPureAux









end Work.FTS.EllipticEst.H2W.WeakPureAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.pzIterEqInvPowDzIter =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open scoped Real Topology
open Filter Set

/-!
# `∂_z^n F` in terms of `D_z^n F` for `n ≤ 3`

`D_z = z ∂_z`, so the iterated operators satisfy

* `∂_z F = z⁻¹ D_z F`,
* `∂_z² F = z⁻² (D_z² F − D_z F)`,
* `∂_z³ F = z⁻³ (D_z³ F − 3 D_z² F + 2 D_z F)`.

(These are the inverse-Sirling relations `z^n ∂_z^n = ∑_k s(n,k) D_z^k` for `n ≤ 3`, with
the signed Stirling numbers of the first kind `s(2,·) = (-1,1)`, `s(3,·) = (2,-3,1)`.)

The two `z`-expansions used in the proof are
`D_z²F = z ∂_z F + z² ∂_z²F` and `D_z³F = z ∂_z F + 3z²∂_z²F + z³∂_z³F`, both from the
product rule applied to the `z`-slices (`SmoothOpen.hasDerivAt_slice_pzIter`).
-/




end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.TIProp.Bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted bounds for the surrogate decomposition

For `f` with finite weighted energies `P = ∫ f²σ` and `E = ∫ (f'')²σ`, whose endpoint traces are
`F₀`, `F₁`, and a surrogate `ℓ = surrFun ψ F₀ F₁ L` at a scale `L` with `L⁴ = P/(16(P+E))`, this
module records:

* the weighted `L²` mass of the difference `f - ℓ` (at most `10^6 P`);
* the weighted `L²` mass of the second derivative of `f - ℓ` (at most `10^8 (Cb+1)² (P+E)`);
* the weighted `L²` mass of the first derivative of `ℓ`;
* the integrability of `(f-ℓ)²σ`, `((f-ℓ)')²σ` and `((f-ℓ)'')²σ`.
-/

namespace Work.FTS.EllipticEst.Prop.TIProp

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 4000000

local notation "σ" => Work.FTS.EllipticEst.thEta

theorem bounds {ψ : ℝ → ℝ} {Cb F₀ F₁ P E L : ℝ}
    (hψ : Work.EllipticEst.Core.i0Aux.IsBump ψ Cb)
    (hLpos : 0 < L) (hLp : L ≤ Real.pi / 4) (hPpos : 0 < P) (hEnn : 0 ≤ E)
    (hL4 : L ^ 4 = P / (16 * (P + E)))
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hF0tr : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds F₀))
    (hF1tr : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds F₁))
    (hPint : MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * σ θ) Work.Spaces.Iθ)
    (hAint : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2 * σ θ) Work.Spaces.Iθ)
    (hEint : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * σ θ)
      Work.Spaces.Iθ)
    (hPdef : P = ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * σ θ)
    (hEdef : E = ∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * σ θ) :
    ((∫ θ in Work.Spaces.Iθ,
        (fun θ : ℝ => f θ - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) θ ^ 2
          * σ θ) ≤ 10 ^ 6 * P)
    ∧ ((∫ θ in Work.Spaces.Iθ,
        (deriv (deriv (fun θ : ℝ => f θ - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ)) θ) ^ 2
          * σ θ) ≤ (2 + 2 * (10 ^ 8 * (Cb + 1) ^ 2)) * (P + E))
    ∧ ((∫ θ in Work.Spaces.Iθ,
        (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2 * σ θ)
          ≤ 10 ^ 6 * (Cb + 1) ^ 2 * (P + Real.sqrt (P * E)))
    ∧ (MeasureTheory.IntegrableOn (fun θ : ℝ =>
        (f θ - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) ^ 2 * σ θ) Work.Spaces.Iθ)
    ∧ (MeasureTheory.IntegrableOn (fun θ : ℝ =>
        (deriv (fun θ : ℝ => f θ - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) θ) ^ 2
          * σ θ) Work.Spaces.Iθ)
    ∧ (MeasureTheory.IntegrableOn (fun θ : ℝ =>
        (deriv (deriv (fun θ : ℝ => f θ - Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ)) θ) ^ 2
          * σ θ) Work.Spaces.Iθ)
    ∧ (MeasureTheory.IntegrableOn (fun θ : ℝ =>
        (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) ^ 2 * σ θ) Work.Spaces.Iθ)
    ∧ (MeasureTheory.IntegrableOn (fun θ : ℝ =>
        (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2 * σ θ)
          Work.Spaces.Iθ) := by
  have hLnn : (0 : ℝ) ≤ L := hLpos.le
  have hLlt : L < Real.pi / 2 := by linarith [hLp, Real.pi_pos]
  have hPnn : 0 ≤ P := hPpos.le
  have hsubPO : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hIooP : MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * σ θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hPint.mono_set hsubPO
  have hIooE : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * σ θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hEint.mono_set hsubPO
  have hPbound : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (f θ) ^ 2 * σ θ) ≤ P := by
    rw [hPdef]
    refine MeasureTheory.setIntegral_mono_set hPint ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
    · filter_upwards with θ hθ; exact hsubPO hθ
  have hEbound : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv (deriv f) θ) ^ 2 * σ θ) ≤ E := by
    rw [hEdef]
    refine MeasureTheory.setIntegral_mono_set hEint ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
    · filter_upwards with θ hθ; exact hsubPO hθ
  have hF0b : F₀ ^ 2 ≤ 2 * L ^ (3 + Work.Spaces.eta) * E
      + 100 * L ^ (Work.Spaces.eta - 1) * P := by
    have h := Work.EllipticEst.Core.i0Aux.TVRed.endpointParamLeftW f F₀ L hLpos hLlt hf hF0tr
      hIooE hIooP
    have h1 : 0 ≤ L ^ (3 + Work.Spaces.eta) := Real.rpow_nonneg hLnn _
    have h2 : 0 ≤ L ^ (Work.Spaces.eta - 1) := Real.rpow_nonneg hLnn _
    have h3 := mul_le_mul_of_nonneg_left hEbound h1
    have h4 := mul_le_mul_of_nonneg_left hPbound h2
    linarith
  have hF1b : F₁ ^ 2 ≤ 2 * L ^ (3 + Work.Spaces.eta) * E
      + 100 * L ^ (Work.Spaces.eta - 1) * P := by
    have h := Work.EllipticEst.Core.i0Aux.TVRed.endpointParamRightW f F₁ L hLpos hLlt hf hF1tr
      hIooE hIooP
    have h1 : 0 ≤ L ^ (3 + Work.Spaces.eta) := Real.rpow_nonneg hLnn _
    have h2 : 0 ≤ L ^ (Work.Spaces.eta - 1) := Real.rpow_nonneg hLnn _
    have h3 := mul_le_mul_of_nonneg_left hEbound h1
    have h4 := mul_le_mul_of_nonneg_left hPbound h2
    linarith
  have hF0sc : F₀ ^ 2 * L ^ (1 - Work.Spaces.eta) ≤ 200 * P :=
    endpoint_scale hLpos hPpos hPnn hEnn hL4 hF0b
  have hF1sc : F₁ ^ 2 * L ^ (1 - Work.Spaces.eta) ≤ 200 * P :=
    endpoint_scale hLpos hPpos hPnn hEnn hL4 hF1b
  -- ## the surrogate and its weighted energies
  let ℓ : ℝ → ℝ := Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L
  let g : ℝ → ℝ := fun θ : ℝ => f θ - ℓ θ
  obtain ⟨hAℓ, hEℓ, hintℓ0, hintℓ1, hintℓ2⟩ :=
    Work.FTS.EllipticEst.Prop.TIProp.surr_energy hψ hLpos hLp hPpos hEnn hL4 hF0b hF1b
  -- ## the weighted mass of `f - ℓ`
  have hL2pos : (0 : ℝ) < L / 2 := by linarith
  have hcmp : L / 2 < Real.pi / 2 - L / 2 := by linarith [hLp, Real.pi_pos]
  have hcmp2 : Real.pi / 2 - L / 2 < Real.pi / 2 := by linarith
  have hsubL : Set.Ioo (0 : ℝ) (L / 2) ⊆ Work.Spaces.Iθ :=
    fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt (by linarith [hθ.2, hLp, Real.pi_pos])⟩
  have hsubR : Set.Ioo (Real.pi / 2 - L / 2) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun θ hθ => ⟨le_of_lt (by linarith [hθ.1, hLp, Real.pi_pos]), le_of_lt hθ.2⟩
  have hmid0 : ∀ θ ∈ Set.Ioo (L / 2) (Real.pi / 2 - L / 2), ℓ θ = 0 := by
    intro θ hθ
    have h1 : ψ (θ / L) = 0 :=
      hψ.eq_zero _ (by rw [le_div_iff₀ hLpos]; linarith [hθ.1])
    have h2 : ψ ((Real.pi / 2 - θ) / L) = 0 :=
      hψ.eq_zero _ (by rw [le_div_iff₀ hLpos]; linarith [hθ.2])
    show Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ = 0
    simp only [Work.EllipticEst.Core.i0Aux.surrFun, h1, h2, mul_zero, add_zero]
  have hsurrb : ∀ θ : ℝ, (ℓ θ) ^ 2 ≤ (|F₀| + |F₁|) ^ 2 := by
    intro θ
    have h := Work.EllipticEst.Core.i0Aux.TVRed.surr_bound (F₀ := F₀) (F₁ := F₁) (L := L) hψ θ
    calc (ℓ θ) ^ 2 = |ℓ θ| ^ 2 := (sq_abs _).symm
      _ ≤ (|F₀| + |F₁|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  -- the left piece
  have hleft : (∫ θ in Set.Ioo (0 : ℝ) (L / 2), (g θ) ^ 2 * σ θ) ≤ 400000 * P := by
    have h1 : (∫ θ in Set.Ioo (0 : ℝ) (L / 2), (g θ) ^ 2 * σ θ)
        ≤ ∫ θ in Set.Ioo (0 : ℝ) (L / 2),
            2 * ((f θ) ^ 2 * σ θ) + 2 * ((ℓ θ) ^ 2 * σ θ) := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
        exact mul_nonneg (sq_nonneg _)
          (thEta_nonneg_Ioo ⟨hθ.1, by linarith [hθ.2, hLp, Real.pi_pos]⟩)
      · exact ((hPint.mono_set hsubL).const_mul 2).add ((hintℓ0.mono_set hsubL).const_mul 2)
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
        have hσ : 0 ≤ σ θ :=
          thEta_nonneg_Ioo ⟨hθ.1, by linarith [hθ.2, hLp, Real.pi_pos]⟩
        have h2 : (g θ) ^ 2 ≤ 2 * (f θ) ^ 2 + 2 * (ℓ θ) ^ 2 := by
          show (f θ - ℓ θ) ^ 2 ≤ 2 * (f θ) ^ 2 + 2 * (ℓ θ) ^ 2
          nlinarith [sq_nonneg (f θ + ℓ θ)]
        calc (g θ) ^ 2 * σ θ ≤ (2 * (f θ) ^ 2 + 2 * (ℓ θ) ^ 2) * σ θ :=
              mul_le_mul_of_nonneg_right h2 hσ
          _ = 2 * ((f θ) ^ 2 * σ θ) + 2 * ((ℓ θ) ^ 2 * σ θ) := by ring
    have h2 : (∫ θ in Set.Ioo (0 : ℝ) (L / 2),
          2 * ((f θ) ^ 2 * σ θ) + 2 * ((ℓ θ) ^ 2 * σ θ))
        ≤ 2 * P + 2 * ((|F₀| + |F₁|) ^ 2 * (200 * L ^ (1 - Work.Spaces.eta))) := by
      rw [MeasureTheory.integral_add ((hPint.mono_set hsubL).const_mul 2)
          ((hintℓ0.mono_set hsubL).const_mul 2),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      have h3 : (∫ θ in Set.Ioo (0 : ℝ) (L / 2), (f θ) ^ 2 * σ θ) ≤ P := by
        rw [hPdef]
        refine MeasureTheory.setIntegral_mono_set hPint ?_ ?_
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
          exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
        · filter_upwards with θ hθ; exact hsubL hθ
      have h4 : (∫ θ in Set.Ioo (0 : ℝ) (L / 2), (ℓ θ) ^ 2 * σ θ)
          ≤ (|F₀| + |F₁|) ^ 2 * (200 * L ^ (1 - Work.Spaces.eta)) := by
        have h5 : (∫ θ in Set.Ioo (0 : ℝ) (L / 2), (ℓ θ) ^ 2 * σ θ)
            ≤ ∫ θ in Set.Ioo (0 : ℝ) (L / 2), ((|F₀| + |F₁|) ^ 2) * σ θ := by
          refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
          · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
            exact mul_nonneg (sq_nonneg _)
              (thEta_nonneg_Ioo ⟨hθ.1, by linarith [hθ.2, hLp, Real.pi_pos]⟩)
          · exact ((Work.FTS.EllipticEst.integrableOn_thEta.1).mono_set hsubL).const_mul _
          · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
            exact mul_le_mul_of_nonneg_right (hsurrb θ)
              (thEta_nonneg_Ioo ⟨hθ.1, by linarith [hθ.2, hLp, Real.pi_pos]⟩)
        rw [MeasureTheory.integral_const_mul] at h5
        exact h5.trans
          (mul_le_mul_of_nonneg_left (thEta_tail_left_Ioo hLpos hLp) (by positivity))
      linarith [h3, h4]
    have h6 : 2 * P + 2 * ((|F₀| + |F₁|) ^ 2 * (200 * L ^ (1 - Work.Spaces.eta)))
        ≤ 400000 * P := by
      have h7 : (|F₀| + |F₁|) ^ 2 * L ^ (1 - Work.Spaces.eta)
          ≤ 2 * ((F₀ ^ 2 + F₁ ^ 2) * L ^ (1 - Work.Spaces.eta)) := by
        have h7a : (|F₀| + |F₁|) ^ 2 ≤ 2 * (F₀ ^ 2 + F₁ ^ 2) := by
          nlinarith [sq_nonneg (|F₀| - |F₁|), sq_abs F₀, sq_abs F₁]
        calc (|F₀| + |F₁|) ^ 2 * L ^ (1 - Work.Spaces.eta)
            ≤ (2 * (F₀ ^ 2 + F₁ ^ 2)) * L ^ (1 - Work.Spaces.eta) :=
              mul_le_mul_of_nonneg_right h7a (Real.rpow_nonneg hLnn _)
          _ = 2 * ((F₀ ^ 2 + F₁ ^ 2) * L ^ (1 - Work.Spaces.eta)) := by ring
      have h8 : 2 * ((F₀ ^ 2 + F₁ ^ 2) * L ^ (1 - Work.Spaces.eta)) ≤ 800 * P := by
        have h8a : (F₀ ^ 2 + F₁ ^ 2) * L ^ (1 - Work.Spaces.eta) ≤ 400 * P := by
          linarith [hF0sc, hF1sc]
        linarith
      calc 2 * P + 2 * ((|F₀| + |F₁|) ^ 2 * (200 * L ^ (1 - Work.Spaces.eta)))
          = 2 * P + 400 * ((|F₀| + |F₁|) ^ 2 * L ^ (1 - Work.Spaces.eta)) := by ring
        _ ≤ 2 * P + 400 * (800 * P) := by linarith [h7, h8]
        _ ≤ 400000 * P := by linarith [hPnn]
    linarith [h1, h2, h6]
  -- the middle piece
  have hmid : (∫ θ in Set.Ioo (L / 2) (Real.pi / 2 - L / 2), (g θ) ^ 2 * σ θ) ≤ P := by
    have h1 : (∫ θ in Set.Ioo (L / 2) (Real.pi / 2 - L / 2), (g θ) ^ 2 * σ θ)
        = ∫ θ in Set.Ioo (L / 2) (Real.pi / 2 - L / 2), (f θ) ^ 2 * σ θ := by
      refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioo
        (Filter.Eventually.of_forall ?_)
      intro θ hθ
      show (f θ - ℓ θ) ^ 2 * σ θ = (f θ) ^ 2 * σ θ
      rw [hmid0 θ hθ]; ring
    rw [h1, hPdef]
    refine MeasureTheory.setIntegral_mono_set hPint ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
    · filter_upwards with θ hθ
      exact ⟨le_of_lt (by linarith [hθ.1, hL2pos]), le_of_lt (by linarith [hθ.2, hcmp2])⟩
  -- the right piece
  have hright : (∫ θ in Set.Ioo (Real.pi / 2 - L / 2) (Real.pi / 2), (g θ) ^ 2 * σ θ)
      ≤ 400000 * P := by
    have h1 : (∫ θ in Set.Ioo (Real.pi / 2 - L / 2) (Real.pi / 2), (g θ) ^ 2 * σ θ)
        ≤ ∫ θ in Set.Ioo (Real.pi / 2 - L / 2) (Real.pi / 2),
            2 * ((f θ) ^ 2 * σ θ) + 2 * ((ℓ θ) ^ 2 * σ θ) := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
        exact mul_nonneg (sq_nonneg _)
          (thEta_nonneg_Ioo ⟨by linarith [hθ.1, hLp, Real.pi_pos], hθ.2⟩)
      · exact ((hPint.mono_set hsubR).const_mul 2).add ((hintℓ0.mono_set hsubR).const_mul 2)
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
        have hσ : 0 ≤ σ θ :=
          thEta_nonneg_Ioo ⟨by linarith [hθ.1, hLp, Real.pi_pos], hθ.2⟩
        have h2 : (g θ) ^ 2 ≤ 2 * (f θ) ^ 2 + 2 * (ℓ θ) ^ 2 := by
          show (f θ - ℓ θ) ^ 2 ≤ 2 * (f θ) ^ 2 + 2 * (ℓ θ) ^ 2
          nlinarith [sq_nonneg (f θ + ℓ θ)]
        calc (g θ) ^ 2 * σ θ ≤ (2 * (f θ) ^ 2 + 2 * (ℓ θ) ^ 2) * σ θ :=
              mul_le_mul_of_nonneg_right h2 hσ
          _ = 2 * ((f θ) ^ 2 * σ θ) + 2 * ((ℓ θ) ^ 2 * σ θ) := by ring
    have h2 : (∫ θ in Set.Ioo (Real.pi / 2 - L / 2) (Real.pi / 2),
          2 * ((f θ) ^ 2 * σ θ) + 2 * ((ℓ θ) ^ 2 * σ θ))
        ≤ 2 * P + 2 * ((|F₀| + |F₁|) ^ 2 * (200 * L ^ (1 - Work.Spaces.eta))) := by
      rw [MeasureTheory.integral_add ((hPint.mono_set hsubR).const_mul 2)
          ((hintℓ0.mono_set hsubR).const_mul 2),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      have h3 : (∫ θ in Set.Ioo (Real.pi / 2 - L / 2) (Real.pi / 2),
          (f θ) ^ 2 * σ θ) ≤ P := by
        rw [hPdef]
        refine MeasureTheory.setIntegral_mono_set hPint ?_ ?_
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
          exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
        · filter_upwards with θ hθ; exact hsubR hθ
      have h4 : (∫ θ in Set.Ioo (Real.pi / 2 - L / 2) (Real.pi / 2), (ℓ θ) ^ 2 * σ θ)
          ≤ (|F₀| + |F₁|) ^ 2 * (200 * L ^ (1 - Work.Spaces.eta)) := by
        have h5 : (∫ θ in Set.Ioo (Real.pi / 2 - L / 2) (Real.pi / 2), (ℓ θ) ^ 2 * σ θ)
            ≤ ∫ θ in Set.Ioo (Real.pi / 2 - L / 2) (Real.pi / 2),
                ((|F₀| + |F₁|) ^ 2) * σ θ := by
          refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
          · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
            exact mul_nonneg (sq_nonneg _)
              (thEta_nonneg_Ioo ⟨by linarith [hθ.1, hLp, Real.pi_pos], hθ.2⟩)
          · exact ((Work.FTS.EllipticEst.integrableOn_thEta.1).mono_set hsubR).const_mul _
          · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
            exact mul_le_mul_of_nonneg_right (hsurrb θ)
              (thEta_nonneg_Ioo ⟨by linarith [hθ.1, hLp, Real.pi_pos], hθ.2⟩)
        rw [MeasureTheory.integral_const_mul] at h5
        exact h5.trans
          (mul_le_mul_of_nonneg_left (thEta_tail_right_Ioo hLpos hLp) (by positivity))
      linarith [h3, h4]
    have h6 : 2 * P + 2 * ((|F₀| + |F₁|) ^ 2 * (200 * L ^ (1 - Work.Spaces.eta)))
        ≤ 400000 * P := by
      have h7 : (|F₀| + |F₁|) ^ 2 * L ^ (1 - Work.Spaces.eta)
          ≤ 2 * ((F₀ ^ 2 + F₁ ^ 2) * L ^ (1 - Work.Spaces.eta)) := by
        have h7a : (|F₀| + |F₁|) ^ 2 ≤ 2 * (F₀ ^ 2 + F₁ ^ 2) := by
          nlinarith [sq_nonneg (|F₀| - |F₁|), sq_abs F₀, sq_abs F₁]
        calc (|F₀| + |F₁|) ^ 2 * L ^ (1 - Work.Spaces.eta)
            ≤ (2 * (F₀ ^ 2 + F₁ ^ 2)) * L ^ (1 - Work.Spaces.eta) :=
              mul_le_mul_of_nonneg_right h7a (Real.rpow_nonneg hLnn _)
          _ = 2 * ((F₀ ^ 2 + F₁ ^ 2) * L ^ (1 - Work.Spaces.eta)) := by ring
      have h8 : 2 * ((F₀ ^ 2 + F₁ ^ 2) * L ^ (1 - Work.Spaces.eta)) ≤ 800 * P := by
        have h8a : (F₀ ^ 2 + F₁ ^ 2) * L ^ (1 - Work.Spaces.eta) ≤ 400 * P := by
          linarith [hF0sc, hF1sc]
        linarith
      calc 2 * P + 2 * ((|F₀| + |F₁|) ^ 2 * (200 * L ^ (1 - Work.Spaces.eta)))
          = 2 * P + 400 * ((|F₀| + |F₁|) ^ 2 * L ^ (1 - Work.Spaces.eta)) := by ring
        _ ≤ 2 * P + 400 * (800 * P) := by linarith [h7, h8]
        _ ≤ 400000 * P := by linarith [hPnn]
    linarith [h1, h2, h6]
  -- ## the total mass and the integrability of `(f - ℓ)²σ`
  have hgIθ : MeasureTheory.IntegrableOn (fun θ : ℝ => (g θ) ^ 2 * σ θ) Work.Spaces.Iθ :=
    Work.EllipticEst.Core.i0Aux.TVRed.tvh_integrableOn_sq_sub hPint hintℓ0
      (Work.EllipticEst.Core.i0Aux.TVRed.tvh_aesm_of_continuousOn hf.continuousOn)
      (Work.EllipticEst.Core.i0Aux.TVRed.tvh_aesm_of_continuousOn
        ((Work.EllipticEst.Core.i0Aux.TVRed.surr_smooth hψ
          (ne_of_gt hLpos)).continuous.continuousOn))
  have hIfg : MeasureTheory.IntegrableOn (fun θ : ℝ => (g θ) ^ 2 * σ θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hgIθ.mono_set hsubPO
  have hsplit3 := Work.EllipticEst.Core.i0Aux.setIntegral_Ioo_split3
    (f := fun θ : ℝ => (g θ) ^ 2 * σ θ) (a := (0 : ℝ)) (b := L / 2)
    (c := Real.pi / 2 - L / 2) (d := Real.pi / 2) hL2pos hcmp hcmp2 hIfg
  have hIθIoo : (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * σ θ)
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (g θ) ^ 2 * σ θ := by
    rw [Measure.restrict_congr_set (Work.EllipticEst.Core.i0Aux.tvc_ae_eq_Iθ_Ioo)]
  have hPg : (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * σ θ) ≤ 10 ^ 6 * P := by
    rw [hIθIoo, hsplit3]
    linarith [hleft, hmid, hright]
  -- ## the integrability of `((f - ℓ)'')²σ` and the bound for `((f-ℓ)'')²σ`
  have hg_int2 : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv g) θ) ^ 2 * σ θ)
      Work.Spaces.Iθ := by
    have hae : (fun θ : ℝ => (deriv (deriv f) θ - deriv (deriv ℓ) θ) ^ 2 * σ θ)
        =ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ : ℝ => (deriv (deriv g) θ) ^ 2 * σ θ) := by
      filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
      rw [Work.EllipticEst.Core.i0Aux.TVRed.tvh_deriv2_sub hf
        (Work.EllipticEst.Core.i0Aux.TVRed.surr_smooth hψ (ne_of_gt hLpos)) θ hθ]
    refine (Work.EllipticEst.Core.i0Aux.TVRed.tvh_integrableOn_sq_sub hEint hintℓ2
      ?_ ?_).congr hae
    · have h0 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        hf.deriv_of_isOpen isOpen_Ioo (by norm_num)
      exact Work.EllipticEst.Core.i0Aux.TVRed.tvh_aesm_of_continuousOn
        (contDiffOn_zero.1 (h0.deriv_of_isOpen isOpen_Ioo (by norm_num)))
    · have h1 : ContDiff ℝ 1 (deriv ℓ) := by
        simpa using (Work.EllipticEst.Core.i0Aux.TVRed.surr_smooth hψ
          (ne_of_gt hLpos)).deriv' (n := 1)
      exact Work.EllipticEst.Core.i0Aux.TVRed.tvh_aesm_of_continuousOn
        (contDiffOn_zero.1 ((h1.contDiffOn).deriv_of_isOpen isOpen_Ioo (by norm_num)))
  have hEg : (∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 * σ θ)
      ≤ (2 + 2 * (10 ^ 8 * (Cb + 1) ^ 2)) * (P + E) := by
    have hae : (fun θ : ℝ => (deriv (deriv g) θ) ^ 2 * σ θ)
        =ᵐ[volume.restrict Work.Spaces.Iθ]
          (fun θ : ℝ => (deriv (deriv f) θ - deriv (deriv ℓ) θ) ^ 2 * σ θ) := by
      filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
      rw [Work.EllipticEst.Core.i0Aux.TVRed.tvh_deriv2_sub hf
        (Work.EllipticEst.Core.i0Aux.TVRed.surr_smooth hψ (ne_of_gt hLpos)) θ hθ]
    rw [MeasureTheory.integral_congr_ae hae]
    have h2 : (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ - deriv (deriv ℓ) θ) ^ 2 * σ θ)
        ≤ ∫ θ in Work.Spaces.Iθ,
            2 * ((deriv (deriv f) θ) ^ 2 * σ θ) + 2 * ((deriv (deriv ℓ) θ) ^ 2 * σ θ) := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
      · exact (hEint.const_mul 2).add (hintℓ2.const_mul 2)
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        have hσ : 0 ≤ σ θ := Work.FTS.EllipticEst.thEta_nonneg hθ
        have h3 : (deriv (deriv f) θ - deriv (deriv ℓ) θ) ^ 2
            ≤ 2 * (deriv (deriv f) θ) ^ 2 + 2 * (deriv (deriv ℓ) θ) ^ 2 := by
          nlinarith [sq_nonneg (deriv (deriv f) θ + deriv (deriv ℓ) θ)]
        calc (deriv (deriv f) θ - deriv (deriv ℓ) θ) ^ 2 * σ θ
            ≤ (2 * (deriv (deriv f) θ) ^ 2 + 2 * (deriv (deriv ℓ) θ) ^ 2) * σ θ :=
              mul_le_mul_of_nonneg_right h3 hσ
          _ = 2 * ((deriv (deriv f) θ) ^ 2 * σ θ)
              + 2 * ((deriv (deriv ℓ) θ) ^ 2 * σ θ) := by ring
    rw [MeasureTheory.integral_add (hEint.const_mul 2) (hintℓ2.const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at h2
    rw [← hEdef] at h2
    have h5 : 2 * (∫ θ in Work.Spaces.Iθ, (deriv (deriv ℓ) θ) ^ 2 * σ θ)
        ≤ 2 * (10 ^ 8 * (Cb + 1) ^ 2 * (P + E)) :=
      mul_le_mul_of_nonneg_left hEℓ (by norm_num)
    have h6 : 2 * E + 2 * (10 ^ 8 * (Cb + 1) ^ 2 * (P + E))
        ≤ (2 + 2 * (10 ^ 8 * (Cb + 1) ^ 2)) * (P + E) := by
      have h7 : 2 * E ≤ 2 * (P + E) := by linarith [hEnn, hPpos.le]
      linarith [h7]
    linarith [h2, h5, h6]
  -- ## the integrability of `((f - ℓ)')²σ`
  have hg_int1 : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv g θ) ^ 2 * σ θ)
      Work.Spaces.Iθ := by
    have hae : (fun θ : ℝ => (deriv f θ - deriv ℓ θ) ^ 2 * σ θ)
        =ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ : ℝ => (deriv g θ) ^ 2 * σ θ) := by
      filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
      rw [Work.EllipticEst.Core.i0Aux.TVRed.tvh_deriv_sub hf
        (Work.EllipticEst.Core.i0Aux.TVRed.surr_smooth hψ (ne_of_gt hLpos)) θ hθ]
    refine (Work.EllipticEst.Core.i0Aux.TVRed.tvh_integrableOn_sq_sub hAint hintℓ1
      ?_ ?_).congr hae
    · exact Work.EllipticEst.Core.i0Aux.TVRed.tvh_aesm_of_continuousOn
        (hf.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num))
    · have h1 : ContDiff ℝ 1 (deriv ℓ) := by
        simpa using (Work.EllipticEst.Core.i0Aux.TVRed.surr_smooth hψ
          (ne_of_gt hLpos)).deriv' (n := 1)
      exact Work.EllipticEst.Core.i0Aux.TVRed.tvh_aesm_of_continuousOn
        (h1.continuous.continuousOn)
  exact ⟨hPg, hEg, hAℓ, hgIθ, hg_int1, hg_int2, hintℓ0, hintℓ1⟩

end Work.FTS.EllipticEst.Prop.TIProp
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.l0_second_sharp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 4000000



end Work.FTS.EllipticEst.Prop
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.AeI1CSPiece =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov


end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.H2W.PsiSlices.pzIterLevelIdentities =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The level-`1` and level-`2` slice identities of the weak class `WeakPos2`

Differentiating the elliptic equation `Work.Elliptic.bslOp α Ψ = F` once (resp. twice) in the
radial variable `z` and commuting `∂_z` with the angular operator `Lzero` (Clairaut/Schwarz)
gives, on the open quadrant,

  `Lzero1 (∂_zΨ(z,·)) = ∂_zF(z,·) + α²(2z∂_z²Ψ + z²∂_z³Ψ) + α(5+α)(∂_zΨ + z∂_z²Ψ)`

and

  `Lzero1 (∂_z²Ψ(z,·)) = ∂_z²F(z,·) + α²(2∂_z²Ψ + 4z∂_z³Ψ + z²∂_z⁴Ψ) + α(5+α)(2∂_z²Ψ + z∂_z³Ψ)`.

The first identity is the `pz`-companion of `remov.SourceBound.sliceShiftedDecomposition` (which
treats the undifferentiated equation); the second is obtained by differentiating the first, the
`z`-derivative of the `Lzero1`-slice being again a `Lzero1` of the next slice
(`remov.SourceBound.Lzero1PzComm`).

The only smoothness input is `C^∞` of `Ψ` on the open quadrant — which is the corresponding
field of `Work.FTS.EllipticEst.WeakPos2`.  Note that the source `F` is only known to agree with
`bslOp α Ψ` on the open quadrant, so its `z`-derivatives are computed from that local equality
(`Filter.EventuallyEq.deriv_eq`).  Everything rests on
`[propext, Classical.choice, Quot.sound]`.
-/
open scoped Real Topology

open MeasureTheory Set Filter

namespace Work.H2W.PsiSlices

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The `z`-derivative of the slice of `Lzero` -/

/-- **The derivative in `z` of the `θ`-slice of `Lzero`.**

For `Ψ` of class `C^∞` on the open quadrant, `z > 0` and `0 < θ < π/2`, the function
`z' ↦ Lzero Ψ z' θ` has derivative `Lzero1 (∂_zΨ(z,·))` at `z`.

The value is identified with the aid of the commutation `remov.Lzero1PzComm`
(`Lzero1 (∂_zΦ(z,·)) = ∂_z (z' ↦ Lzero1 (Φ(z',·)))`, with `Lzero1` of a slice definitionally
the slice of `Lzero`), which settles the Clairaut part; the differentiability itself is the
product rule for the three summands of `Lzero` (`∂_θ²Ψ`, `∂_θ(tan θ·Ψ)`, `Ψ`). -/
theorem hasDerivAt_Lzero_slice {Ψ : ℝ → ℝ → ℝ}
    (hsmooth : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    HasDerivAt (fun z' => Work.Elliptic.Lzero Ψ z' θ)
      (Work.FTS.EllipticEst.Lzero1 (fun θ' => Work.Spaces.pzIter 1 Ψ z θ') θ) z := by
  have hθm : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ := Work.FTS.EllipticEst.smoothOpen_of_forall hsmooth
  have htan : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl hΨ
  have hd1 : HasDerivAt (fun z' => Work.Spaces.pthIter 2 Ψ z' θ)
      (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) z := (hΨ.pth.pth).hasDerivAt_slice hθm hz
  have hd2 : HasDerivAt (fun z' => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z' θ)
      (Work.Spaces.pz (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ)) z θ) z :=
    htan.pth.hasDerivAt_slice hθm hz
  have hd3 : HasDerivAt (fun z' => Ψ z' θ) (Work.Spaces.pz Ψ z θ) z := hΨ.hasDerivAt_slice hθm hz
  have hsum : HasDerivAt (fun z' => -(Work.Spaces.pthIter 2 Ψ z' θ)
        + Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z' θ - 6 * Ψ z' θ)
      ((-(Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)
        + Work.Spaces.pz (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ)) z θ)
        - 6 * Work.Spaces.pz Ψ z θ) z :=
    (hd1.neg.add hd2).sub (hd3.const_mul 6)
  have key : Work.FTS.EllipticEst.Lzero1 (fun θ' => Work.Spaces.pzIter 1 Ψ z θ') θ
      = deriv (fun z' => Work.Elliptic.Lzero Ψ z' θ) z := by
    exact Work.FTS.EllipticEst.remov.SourceBound.Lzero1PzComm hsmooth hz hθ0 hθ1
  have hV : ((-(Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)
        + Work.Spaces.pz (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ)) z θ)
        - 6 * Work.Spaces.pz Ψ z θ)
      = deriv (fun z' => Work.Elliptic.Lzero Ψ z' θ) z := hsum.deriv.symm
  refine hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun z' => ?_)) |>.congr_deriv ?_
  · exact (Work.FTS.EllipticEst.remov.Lzero1_slice_eq Ψ z' θ).symm
  · exact hV.trans key.symm

/-! ## The level-`1` identity -/


/-! ## The level-`2` identity -/


/-! ## The requested statement -/


end Work.H2W.PsiSlices
end
-- ===== merged: Submission.Work.H2W.PsiSlices.shiftedSourcePoleBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.H2W.PsiSlices

open Work.FTS.EllipticEst.H2W
open Work.FTS.EllipticEst.H2W.WeakPureAux
open Work.FTS.EllipticEst.H2W.LzeroGrowth

set_option autoImplicit false

noncomputable section

/-! ## The shifted source mass, and the pointwise splitting of the `Dfun` density

The whole proof runs the `(Dfun, Rfun)`-Wronskian system of `Lzero1` with the *shifted* source
`g = Lzero1 u - c·u`.  The only structural change with respect to the eigen case is that the
source integral `∫ sinθcos²θ |g|` is a fixed (finite) number `shiftedMass c u` rather than a
multiple of the running `Rfun`-mass, which only shifts the constant of the resulting Grönwall
inequality. -/






/-! ## The two halves of the running bounds -/





/-! ## The left half -/






end

end Work.H2W.PsiSlices
end
