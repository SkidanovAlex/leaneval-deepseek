import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.DerivNotation
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Tactic.Have
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Coercivity.L2CoercivityTransport
import Submission.Work.Coercivity.L2CoercivityTransportEta
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.A_sq_prod_le
import Submission.Work.FTS.CoercivityStep.Step.Coercive
import Submission.Work.FTS.EllSol.Trunc.PassAux2
import Submission.Work.FTS.EllipticEst.AeI1Fts.zibp_cut
import Submission.Work.FTS.EllipticEst.AeS1.SigFirstOrderDefs
import Submission.Work.FTS.EllipticEst.Dispatch.truncRadialIbpTheta
import Submission.Work.FTS.EllipticEst.Final.ReHome.H2W_slot20_bound
import Submission.Work.FTS.EllipticEst.H2W.Ae.aeSigmaSliceLower
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeGapSlices
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.Honest.I4UpperHonest
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.TT.ESW.Tk_B_le_chain_uniform
import Submission.Work.FTS.EllipticEst.TT.truncAux
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.interpol_trunc_defs
import Submission.Work.FTS.EllipticEst.remov.SrdFork.EllWeakPos_DzIter_one_shift_fork
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.ModalSolR.PerModeBasic
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.integral_sin_two_rpow_neg
import Submission.Work.FTS.LocDataExt.Defs
import Submission.Work.FTS.LocDataExt.LocG5
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.OpenPkg.ProdOpen.Tools1d
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeDefs
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Gmaj6
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.StrongPersist.N6.Slots
import Submission.Work.FTS.StrongPersist.N6.sliceAvg_le6
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.StrongPersist.QangSq6
import Submission.Work.FTS.StrongPersist.QangSq6Full
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.T2S
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_EllLimOK.SlotJets.slotPthSliceLe
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.ExcBoundQ
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.T1Q.SlotPtQ
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H2.WPQ.hardy_slice_Aang
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.H2W.PsiSlices.shiftedSourcePoleBound
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.Scaling.vorticityDecay_rescaleDatum
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.ZcutSmoothCompact
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.Q0.weakLocQ0 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity.Q0

open MeasureTheory Set Filter

theorem weakLocQ0 {V G : Work.EllipticEst.InteriorRegularity.E2 → ℂ}
    (hSW : Work.EllipticEst.InteriorRegularity.Q0.StripWeakC V G)
    {χ : Work.EllipticEst.InteriorRegularity.E2 → ℂ}
    (hχs : ∀ n : ℕ, ContDiff ℝ n χ)
    (hχsub : tsupport χ ⊆ Work.EllipticEst.InteriorRegularity.stripE) :
    ∀ ψ : Work.EllipticEst.InteriorRegularity.E2 → ℂ, (∀ n : ℕ, ContDiff ℝ n ψ) →
      HasCompactSupport ψ → Function.support ψ ⊆ {x | χ x = 1} →
      ∫ x, (χ x * V x) * Work.EllipticEst.InteriorRegularity.Kop ψ x
        = ∫ x, (χ x * G x) * ψ x := by
  intro ψ hψs hψc hψsub
  -- `χ = 1` on the support of `ψ`, so `χ · ψ = ψ`
  have hχψ : (fun y : Work.EllipticEst.InteriorRegularity.E2 => χ y * ψ y) = ψ := by
    funext x
    by_cases hx : ψ x = 0
    · simp [hx]
    · have h1 : χ x = 1 := hψsub (Function.mem_support.mpr hx)
      simp [h1]
  have hKopEq : Work.EllipticEst.InteriorRegularity.Kop
      (fun y : Work.EllipticEst.InteriorRegularity.E2 => χ y * ψ y)
      = Work.EllipticEst.InteriorRegularity.Kop ψ := by rw [hχψ]
  -- the set `{χ = 1}` is closed and contained in `tsupport χ`
  have hclosed : IsClosed {x : Work.EllipticEst.InteriorRegularity.E2 | χ x = 1} :=
    isClosed_eq (hχs 0).continuous continuous_const
  have hts : tsupport ψ ⊆ {x : Work.EllipticEst.InteriorRegularity.E2 | χ x = 1} := by
    rw [tsupport]
    exact (closure_mono hψsub).trans (le_of_eq hclosed.closure_eq)
  have hχ1ts : {x : Work.EllipticEst.InteriorRegularity.E2 | χ x = 1} ⊆ tsupport χ :=
    fun x hx => subset_closure (by
      rw [Function.mem_support]
      rw [hx]
      exact one_ne_zero)
  have htsuppψ : tsupport ψ ⊆ Work.EllipticEst.InteriorRegularity.stripE :=
    hts.trans (hχ1ts.trans hχsub)
  -- `Kop ψ` is supported in `tsupport ψ`, hence in `{χ = 1}`
  have hKop : Function.support (Work.EllipticEst.InteriorRegularity.Kop ψ)
      ⊆ {x : Work.EllipticEst.InteriorRegularity.E2 | χ x = 1} := by
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hxn
    exact hx (Work.EllipticEst.InteriorRegularity.VT.Kop_eq_zero_of_notMem_tsupport hψs
      (fun h => hxn (hts h)))
  calc ∫ x, (χ x * V x) * Work.EllipticEst.InteriorRegularity.Kop ψ x
      = ∫ x, (χ x * Work.EllipticEst.InteriorRegularity.Kop ψ x) * V x :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    _ = ∫ x, Work.EllipticEst.InteriorRegularity.Kop ψ x * V x := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        by_cases hx : Work.EllipticEst.InteriorRegularity.Kop ψ x = 0
        · simp [hx]
        · have h1 : χ x = 1 := hKop (Function.mem_support.mpr hx)
          simp only [h1, one_mul]
    _ = ∫ x, V x * Work.EllipticEst.InteriorRegularity.Kop ψ x :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    _ = ∫ x, V x * Work.EllipticEst.InteriorRegularity.Kop
          (fun y : Work.EllipticEst.InteriorRegularity.E2 => χ y * ψ y) x := by
        rw [hKopEq]
    _ = ∫ x, G x * (fun y : Work.EllipticEst.InteriorRegularity.E2 => χ y * ψ y) x :=
        hSW (fun y : Work.EllipticEst.InteriorRegularity.E2 => χ y * ψ y)
          (fun n => by rw [hχψ]; exact hψs n) (by rw [hχψ]; exact hψc)
          (by rw [hχψ]; exact htsuppψ)
    _ = ∫ x, (χ x * G x) * ψ x :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

end Work.EllipticEst.InteriorRegularity.Q0
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.VT.LocalSmoothAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology SchwartzMap LineDeriv ContDiff

namespace Work.EllipticEst.InteriorRegularity.VT

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **The fundamental lemma with Schwartz pairings.** -/
theorem ae_eq_of_pairing {Φ V : E2 → ℂ} {x₀ : E2} {R : ℝ}
    (hΦc : ContinuousOn Φ (Metric.ball x₀ R)) (hV : Integrable V)
    (hpair : ∀ ψ : 𝓢(E2, ℂ), (∀ y, ψ y ≠ 0 → y ∈ Metric.ball x₀ R) →
      ∫ y, ψ y • Φ y = ∫ y, ψ y • V y) :
    V =ᵐ[volume.restrict (Metric.ball x₀ R)] Φ := by
  have hvan : ∀ g : E2 → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ Metric.ball x₀ R → ∫ x, g x • (Φ x - V x) = 0 := by
    intro g hgd hgc hgsub
    have hgs : ∀ n : ℕ, ContDiff ℝ n g := contDiff_infty.mp hgd
    have hgcC : HasCompactSupport (fun x : E2 => ((g x : ℝ) : ℂ)) :=
      hasCompactSupport_ofReal hgc
    have hgsC : ∀ n : ℕ, ContDiff ℝ n (fun x : E2 => ((g x : ℝ) : ℂ)) :=
      fun n => Complex.ofRealCLM.contDiff.comp (hgs n)
    set hS : 𝓢(E2, ℂ) := hgcC.toSchwartzMap (contDiff_infty.mpr hgsC) with hSdef
    have hcoef : (⇑hS : E2 → ℂ) = fun x : E2 => ((g x : ℝ) : ℂ) := by
      rw [hSdef]
      exact funext (HasCompactSupport.toSchwartzMap_toFun hgcC (contDiff_infty.mpr hgsC))
    have hsuppS : ∀ y, hS y ≠ 0 → y ∈ Metric.ball x₀ R := by
      intro y hy
      have hy1 : y ∈ Function.support (⇑hS) := hy
      rw [hcoef] at hy1
      have hy2 : y ∈ Function.support g := by
        rw [Function.mem_support] at hy1 ⊢
        intro h0
        exact hy1 (by rw [h0]; simp)
      exact hgsub (subset_closure hy2)
    have hpairS := hpair hS hsuppS
    have hAi : Integrable (fun y : E2 => g y • Φ y) :=
      integrable_smul_of_continuousOn hgc hgs
        (Metric.isOpen_ball : IsOpen (Metric.ball x₀ R)) hgsub hΦc
    have hBi : Integrable (fun y : E2 => g y • V y) := integrable_smul_of_cc hV hgc hgs
    have hkey : ∫ y, g y • Φ y = ∫ y, g y • V y := by
      have i1 : ∫ y, g y • Φ y = ∫ y, hS y • Φ y :=
        integral_congr_ae (Filter.Eventually.of_forall fun y => by
          rw [hcoef]
          exact (Complex.real_smul : g y • Φ y = ((g y : ℝ) : ℂ) * Φ y))
      have i2 : ∫ y, hS y • V y = ∫ y, g y • V y :=
        integral_congr_ae (Filter.Eventually.of_forall fun y => by
          rw [hcoef]
          exact (Complex.real_smul : g y • V y = ((g y : ℝ) : ℂ) * V y).symm)
      rw [i1, hpairS, i2]
    rw [show (fun x : E2 => g x • (Φ x - V x)) = fun x => g x • Φ x - g x • V x from by
      funext x
      simp only [Pi.sub_apply, smul_sub]]
    rw [integral_sub hAi hBi, hkey, sub_self]
  have hae := IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero Metric.isOpen_ball
    ((hΦc.locallyIntegrableOn Metric.isOpen_ball.measurableSet).sub
      (hV.locallyIntegrable.locallyIntegrableOn (Metric.ball x₀ R))) hvan
  rw [Filter.EventuallyEq]
  refine (ae_restrict_iff' Metric.isOpen_ball.measurableSet).mpr ?_
  filter_upwards [hae] with x hx hxball
  exact (sub_eq_zero.mp (hx hxball)).symm

end Work.EllipticEst.InteriorRegularity.VT
end
end
-- ===== merged: Submission.Work.FTS.Apriori.Limit.integral_mixed_mul_adjMixed =====
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
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open Work.FTS.LocData (SmoothQuad)

theorem ae_restrict_Iz_mem_Ioi :
    ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), 0 < z := by
  rw [Work.Spaces.Iz]
  rw [← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioi

theorem ae_restrict_Iθ_mem_Ioo :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (π / 2) := by
  rw [Work.Spaces.Iθ]
  rw [← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := π / 2))]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

theorem ae_mem_Qd : ∀ᵐ p ∂Qμ, p ∈ Qd := by
  have h : ∀ᵐ p ∂Qμ, p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
      (s := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))
      (measurableSet_Ioi.prod measurableSet_Ioo)).mpr
      (ae_restrict_Iz_mem_Ioi.mono (fun z hz => ae_restrict_Iθ_mem_Ioo.mono
        (fun θ hθ => ⟨hz, hθ⟩)))
  simpa [Qd] using h

/-- Integrability of a smooth function whose *closed* support is contained in that of a test
function. -/
theorem integrable_of_contDiffOn_supp {w v : ℝ → ℝ → ℝ}
    (hw : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry w) Qd) (hv : TestQ v)
    (hsupp : tsupport (Function.uncurry w) ⊆ tsupport (Function.uncurry v)) :
    Integrable (Function.uncurry w) Qμ :=
  integrable_of_continuousOn_of_support hw.continuousOn hv.2.1 hv.2.2
    ((subset_tsupport _).trans hsupp)

theorem tsupport_pz_subset {w : ℝ → ℝ → ℝ} :
    tsupport (Function.uncurry (Work.Spaces.pz w)) ⊆ tsupport (Function.uncurry w) := by
  refine (closure_mono (support_pz_subset_tsupport w)).trans ?_
  rw [IsClosed.closure_eq (isClosed_tsupport _)]

theorem tsupport_adjZ_subset {w : ℝ → ℝ → ℝ} :
    tsupport (Function.uncurry (adjZ w)) ⊆ tsupport (Function.uncurry w) := by
  refine (closure_mono (support_adjZ_subset w)).trans ?_
  rw [IsClosed.closure_eq (isClosed_tsupport _)]

theorem tsupport_pth_subset {w : ℝ → ℝ → ℝ} :
    tsupport (Function.uncurry (Work.Spaces.pth w)) ⊆ tsupport (Function.uncurry w) := by
  refine (closure_mono (support_pth_subset_tsupport w)).trans ?_
  rw [IsClosed.closure_eq (isClosed_tsupport _)]

theorem tsupport_adjTh_subset {w : ℝ → ℝ → ℝ} :
    tsupport (Function.uncurry (adjTh w)) ⊆ tsupport (Function.uncurry w) := by
  refine (closure_mono (support_adjTh_subset w)).trans ?_
  rw [IsClosed.closure_eq (isClosed_tsupport _)]

/-! ## The pointwise product rules -/

theorem pz_mul_three {u v : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry u) Qd)
    (hv : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry v) Qd)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.pz (fun z θ => z * u z θ * v z θ) z θ
      = u z θ * v z θ + z * Work.Spaces.pz u z θ * v z θ
        + z * u z θ * Work.Spaces.pz v z θ := by
  have hzu : HasDerivAt (fun z' => u z' θ) (Work.Spaces.pz u z θ) z :=
    ((Work.FTS.LocData.contDiffOn_slice_z hu hθ).differentiableOn
      Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
        (isOpen_Ioi.mem_nhds hz) |>.hasDerivAt
  have hzv : HasDerivAt (fun z' => v z' θ) (Work.Spaces.pz v z θ) z :=
    ((Work.FTS.LocData.contDiffOn_slice_z hv hθ).differentiableOn
      Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
        (isOpen_Ioi.mem_nhds hz) |>.hasDerivAt
  have hid : HasDerivAt (fun z' : ℝ => z') (1 : ℝ) z := hasDerivAt_id z
  have h3 := hid.mul hzu
  have h4 := h3.mul hzv
  have hd : HasDerivAt (fun z' => z' * u z' θ * v z' θ)
      (u z θ * v z θ + z * Work.Spaces.pz u z θ * v z θ
        + z * u z θ * Work.Spaces.pz v z θ) z := by
    convert h4 using 1
    first | (simp only [Pi.mul_apply]; ring) | ring
  rw [Work.Spaces.pz, hd.deriv]

theorem adjZ_apply {v : ℝ → ℝ → ℝ}
    (hv : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry v) Qd)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    adjZ v z θ = -(v z θ + z * Work.Spaces.pz v z θ) := by
  have hzv : HasDerivAt (fun z' => v z' θ) (Work.Spaces.pz v z θ) z :=
    ((Work.FTS.LocData.contDiffOn_slice_z hv hθ).differentiableOn
      Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
        (isOpen_Ioi.mem_nhds hz) |>.hasDerivAt
  have hid : HasDerivAt (fun z' : ℝ => z') (1 : ℝ) z := hasDerivAt_id z
  have h := hid.mul hzv
  have hd : HasDerivAt (fun z' => z' * v z' θ) (v z θ + z * Work.Spaces.pz v z θ) z := by
    convert h using 1
    first | (simp only [Pi.mul_apply]; ring) | ring
  rw [adjZ, hd.deriv]

/-! ## The elementary `z`-integration by parts -/

theorem integral_Dz_mul_adjZ {u v : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry u) Qd) (hv : TestQ v) :
    ∫ p, Work.Spaces.Dz u p.1 p.2 * v p.1 p.2 ∂Qμ
      = ∫ p, u p.1 p.2 * adjZ v p.1 p.2 ∂Qμ := by
  set W : ℝ → ℝ → ℝ := fun z θ => z * u z θ * v z θ with hWdef
  have hWsm : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry W) Qd := by
    have h1 : Function.uncurry W
        = fun p : ℝ × ℝ => p.1 * Function.uncurry u p * Function.uncurry v p := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [h1]
    exact (contDiffOn_fst.mul hu).mul hv.1
  have hWsupp : tsupport (Function.uncurry W) ⊆ tsupport (Function.uncurry v) := by
    have h1 : Function.uncurry W
        = fun p : ℝ × ℝ => p.1 * Function.uncurry u p * Function.uncurry v p := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [h1]
    exact tsupport_mul_subset_right
      (f := fun p : ℝ × ℝ => p.1 * Function.uncurry u p) (g := Function.uncurry v)
  have hWcomp : HasCompactSupport (Function.uncurry W) :=
    IsCompact.of_isClosed_subset hv.2.1 (isClosed_tsupport _) hWsupp
  have hWsub : tsupport (Function.uncurry W) ⊆ Qd := fun p hp => hv.2.2 (hWsupp hp)
  have hftc : ∫ p, Work.Spaces.pz W p.1 p.2 ∂Qμ = 0 :=
    integral_pz_eq_zero hWsm hWcomp hWsub
  have hpzW : Integrable (fun p : ℝ × ℝ => Work.Spaces.pz W p.1 p.2) Qμ :=
    integrable_of_contDiffOn_supp (w := Work.Spaces.pz W) (v := v)
      (Work.FTS.LocData.contDiffOn_pz isOpen_Qd hWsm) hv
      ((tsupport_pz_subset (w := W)).trans hWsupp)
  have huv : Integrable (fun p : ℝ × ℝ => u p.1 p.2 * v p.1 p.2) Qμ := by
    refine integrable_of_contDiffOn_supp (w := fun z θ => u z θ * v z θ) (v := v) ?_ hv ?_
    · have h1 : Function.uncurry (fun z θ => u z θ * v z θ)
          = Function.uncurry u * Function.uncurry v := by
        funext p; rcases p with ⟨z, θ⟩; rfl
      rw [h1]; exact hu.mul hv.1
    · exact tsupport_mul_subset_right (f := Function.uncurry u) (g := Function.uncurry v)
  have hzu : Integrable (fun p : ℝ × ℝ => p.1 * u p.1 p.2 * Work.Spaces.pz v p.1 p.2) Qμ := by
    refine integrable_of_contDiffOn_supp
      (w := fun z θ => z * u z θ * Work.Spaces.pz v z θ) (v := v) ?_ hv ?_
    · have h1 : Function.uncurry (fun z θ => z * u z θ * Work.Spaces.pz v z θ)
          = fun p : ℝ × ℝ => p.1 * Function.uncurry u p
              * Function.uncurry (Work.Spaces.pz v) p := by
        funext p; rcases p with ⟨z, θ⟩; rfl
      rw [h1]
      exact (contDiffOn_fst.mul hu).mul (Work.FTS.LocData.contDiffOn_pz isOpen_Qd hv.1)
    · have h1 : Function.uncurry (fun z θ => z * u z θ * Work.Spaces.pz v z θ)
          = fun p : ℝ × ℝ => p.1 * Function.uncurry u p
              * Function.uncurry (Work.Spaces.pz v) p := by
        funext p; rcases p with ⟨z, θ⟩; rfl
      rw [h1]
      exact (tsupport_mul_subset_right
        (f := fun p : ℝ × ℝ => p.1 * Function.uncurry u p)
        (g := Function.uncurry (Work.Spaces.pz v))).trans
        (tsupport_pz_subset (w := v))
  have huadj : Integrable (fun p : ℝ × ℝ => u p.1 p.2 * adjZ v p.1 p.2) Qμ := by
    refine integrable_of_contDiffOn_supp (w := fun z θ => u z θ * adjZ v z θ) (v := v) ?_ hv ?_
    · have h1 : Function.uncurry (fun z θ => u z θ * adjZ v z θ)
          = Function.uncurry u * Function.uncurry (adjZ v) := by
        funext p; rcases p with ⟨z, θ⟩; rfl
      rw [h1]; exact hu.mul (TestQ_adjZ hv).1
    · exact (tsupport_mul_subset_right (f := Function.uncurry u) (g := Function.uncurry (adjZ v))).trans
        (tsupport_adjZ_subset (w := v))
  have hkey : ∀ᵐ p ∂Qμ, Work.Spaces.Dz u p.1 p.2 * v p.1 p.2
      = u p.1 p.2 * adjZ v p.1 p.2 + Work.Spaces.pz W p.1 p.2 := by
    filter_upwards [ae_mem_Qd] with p hp
    have h1 := pz_mul_three hu hv.1 hp.1 hp.2
    have h2 := adjZ_apply hv.1 hp.1 hp.2
    rw [hWdef, h1, h2, Work.Spaces.Dz]
    ring
  rw [MeasureTheory.integral_congr_ae hkey]
  rw [show (∫ p : ℝ × ℝ, u p.1 p.2 * adjZ v p.1 p.2
        + Work.Spaces.pz W p.1 p.2 ∂Qμ)
      = (∫ p, u p.1 p.2 * adjZ v p.1 p.2 ∂Qμ)
        + ∫ p, Work.Spaces.pz W p.1 p.2 ∂Qμ
    from MeasureTheory.integral_add huadj hpzW]
  rw [hftc, add_zero]


/-! ## The `θ`-product rules -/

theorem pth_mul_three {u v : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry u) Qd)
    (hv : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry v) Qd)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.pth (fun z θ => Real.sin (2 * θ) * (u z θ * v z θ)) z θ
      = 2 * Real.cos (2 * θ) * (u z θ * v z θ)
        + Real.sin (2 * θ) * (Work.Spaces.pth u z θ * v z θ
          + u z θ * Work.Spaces.pth v z θ) := by
  have hzu : HasDerivAt (fun θ' => u z θ') (Work.Spaces.pth u z θ) θ :=
    ((Work.FTS.LocData.contDiffOn_slice_θ hu (by rw [Set.mem_Ioi]; exact hz)).differentiableOn
      Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
        (isOpen_Ioo.mem_nhds hθ) |>.hasDerivAt
  have hzv : HasDerivAt (fun θ' => v z θ') (Work.Spaces.pth v z θ) θ :=
    ((Work.FTS.LocData.contDiffOn_slice_θ hv (by rw [Set.mem_Ioi]; exact hz)).differentiableOn
      Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
        (isOpen_Ioo.mem_nhds hθ) |>.hasDerivAt
  have hsin : HasDerivAt (fun θ' => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ := by
    have h2 : HasDerivAt (fun y : ℝ => 2 * y) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul 2
    exact (Real.hasDerivAt_sin (2 * θ)).comp θ h2
  have h := hsin.mul (hzu.mul hzv)
  have hd : HasDerivAt (fun θ' => Real.sin (2 * θ') * (u z θ' * v z θ'))
      (2 * Real.cos (2 * θ) * (u z θ * v z θ)
        + Real.sin (2 * θ) * (Work.Spaces.pth u z θ * v z θ
          + u z θ * Work.Spaces.pth v z θ)) θ := by
    convert h using 1
    first | (simp only [Pi.mul_apply]; ring) | ring
  rw [Work.Spaces.pth, hd.deriv]

theorem adjTh_apply {v : ℝ → ℝ → ℝ}
    (hv : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry v) Qd)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    adjTh v z θ = -(2 * Real.cos (2 * θ) * v z θ
      + Real.sin (2 * θ) * Work.Spaces.pth v z θ) := by
  have hzv : HasDerivAt (fun θ' => v z θ') (Work.Spaces.pth v z θ) θ :=
    ((Work.FTS.LocData.contDiffOn_slice_θ hv (by rw [Set.mem_Ioi]; exact hz)).differentiableOn
      Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
        (isOpen_Ioo.mem_nhds hθ) |>.hasDerivAt
  have hsin : HasDerivAt (fun θ' => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ := by
    have h2 : HasDerivAt (fun y : ℝ => 2 * y) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul 2
    exact (Real.hasDerivAt_sin (2 * θ)).comp θ h2
  have h := hsin.mul hzv
  have hd : HasDerivAt (fun θ' => Real.sin (2 * θ') * v z θ')
      (2 * Real.cos (2 * θ) * v z θ + Real.sin (2 * θ) * Work.Spaces.pth v z θ) θ := by
    convert h using 1
    first | (simp only [Pi.mul_apply]; ring) | ring
  rw [adjTh, hd.deriv]

/-! ## The elementary `θ`-integration by parts -/

theorem integral_Dth_mul_adjTh {u v : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry u) Qd) (hv : TestQ v) :
    ∫ p, Work.Spaces.Dth u p.1 p.2 * v p.1 p.2 ∂Qμ
      = ∫ p, u p.1 p.2 * adjTh v p.1 p.2 ∂Qμ := by
  set W : ℝ → ℝ → ℝ := fun z θ => Real.sin (2 * θ) * (u z θ * v z θ) with hWdef
  have hWsm : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry W) Qd := by
    have h1 : Function.uncurry W
        = fun p : ℝ × ℝ => Real.sin (2 * p.2) * (Function.uncurry u p * Function.uncurry v p) := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [h1]
    exact ((Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn).mul
      (hu.mul hv.1)
  have hWsupp : tsupport (Function.uncurry W) ⊆ tsupport (Function.uncurry v) := by
    have h1 : Function.uncurry W
        = fun p : ℝ × ℝ => Real.sin (2 * p.2) * (Function.uncurry u p * Function.uncurry v p) := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [h1]
    refine (tsupport_mul_subset_right (f := fun p : ℝ × ℝ => Real.sin (2 * p.2))
      (g := fun p : ℝ × ℝ => Function.uncurry u p * Function.uncurry v p)).trans ?_
    exact tsupport_mul_subset_right (f := Function.uncurry u) (g := Function.uncurry v)
  have hWcomp : HasCompactSupport (Function.uncurry W) :=
    IsCompact.of_isClosed_subset hv.2.1 (isClosed_tsupport _) hWsupp
  have hWsub : tsupport (Function.uncurry W) ⊆ Qd := fun p hp => hv.2.2 (hWsupp hp)
  have hftc : ∫ p, Work.Spaces.pth W p.1 p.2 ∂Qμ = 0 :=
    integral_pth_eq_zero hWsm hWcomp hWsub
  have hpthW : Integrable (fun p : ℝ × ℝ => Work.Spaces.pth W p.1 p.2) Qμ :=
    integrable_of_contDiffOn_supp (w := Work.Spaces.pth W) (v := v)
      (Work.FTS.LocData.contDiffOn_pth isOpen_Qd hWsm) hv
      ((tsupport_pth_subset (w := W)).trans hWsupp)
  have huv : Integrable (fun p : ℝ × ℝ => Real.sin (2 * p.2) * u p.1 p.2 * Work.Spaces.pth v p.1 p.2) Qμ := by
    refine integrable_of_contDiffOn_supp
      (w := fun z θ => Real.sin (2 * θ) * u z θ * Work.Spaces.pth v z θ) (v := v) ?_ hv ?_
    · have h1 : Function.uncurry (fun z θ => Real.sin (2 * θ) * u z θ * Work.Spaces.pth v z θ)
          = fun p : ℝ × ℝ => Real.sin (2 * p.2) * Function.uncurry u p
              * Function.uncurry (Work.Spaces.pth v) p := by
        funext p; rcases p with ⟨z, θ⟩; rfl
      rw [h1]
      exact (((Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn).mul hu).mul
        (Work.FTS.LocData.contDiffOn_pth isOpen_Qd hv.1)
    · have h1 : Function.uncurry (fun z θ => Real.sin (2 * θ) * u z θ * Work.Spaces.pth v z θ)
          = fun p : ℝ × ℝ => Real.sin (2 * p.2) * Function.uncurry u p
              * Function.uncurry (Work.Spaces.pth v) p := by
        funext p; rcases p with ⟨z, θ⟩; rfl
      rw [h1]
      exact (tsupport_mul_subset_right
        (f := fun p : ℝ × ℝ => Real.sin (2 * p.2) * Function.uncurry u p)
        (g := Function.uncurry (Work.Spaces.pth v))).trans
        ((tsupport_pth_subset (w := v)))
  have huadj : Integrable (fun p : ℝ × ℝ => u p.1 p.2 * adjTh v p.1 p.2) Qμ := by
    refine integrable_of_contDiffOn_supp (w := fun z θ => u z θ * adjTh v z θ) (v := v) ?_ hv ?_
    · have h1 : Function.uncurry (fun z θ => u z θ * adjTh v z θ)
          = Function.uncurry u * Function.uncurry (adjTh v) := by
        funext p; rcases p with ⟨z, θ⟩; rfl
      rw [h1]; exact hu.mul (TestQ_adjTh hv).1
    · exact (tsupport_mul_subset_right (f := Function.uncurry u)
        (g := Function.uncurry (adjTh v))).trans (tsupport_adjTh_subset (w := v))
  have hkey : ∀ᵐ p ∂Qμ, Work.Spaces.Dth u p.1 p.2 * v p.1 p.2
      = u p.1 p.2 * adjTh v p.1 p.2 + Work.Spaces.pth W p.1 p.2 := by
    filter_upwards [ae_mem_Qd] with p hp
    have h1 := pth_mul_three hu hv.1 hp.1 hp.2
    have h2 := adjTh_apply hv.1 hp.1 hp.2
    rw [hWdef, h1, h2, Work.Spaces.Dth]
    ring
  rw [MeasureTheory.integral_congr_ae hkey]
  rw [show (∫ p : ℝ × ℝ, u p.1 p.2 * adjTh v p.1 p.2
        + Work.Spaces.pth W p.1 p.2 ∂Qμ)
      = (∫ p, u p.1 p.2 * adjTh v p.1 p.2 ∂Qμ)
        + ∫ p, Work.Spaces.pth W p.1 p.2 ∂Qμ
    from MeasureTheory.integral_add huadj hpthW]
  rw [hftc, add_zero]

/-! ## Iterating the elementary integrations by parts -/

theorem integral_DzIter_mul_adjDzIter_aux {u : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry u) Qd) (j : ℕ) :
    ∀ {v : ℝ → ℝ → ℝ}, TestQ v →
      ∫ p, Work.Spaces.DzIter j u p.1 p.2 * v p.1 p.2 ∂Qμ
        = ∫ p, u p.1 p.2 * adjDzIter j v p.1 p.2 ∂Qμ := by
  induction j with
  | zero => intro v hv; rfl
  | succ j ih =>
      intro v hv
      rw [Work.Spaces.DzIter_succ]
      rw [integral_Dz_mul_adjZ (u := Work.Spaces.DzIter j u) (v := v)
        (Work.FTS.LocData.contDiffOn_DzIter isOpen_Qd hu j) hv]
      rw [ih (TestQ_adjZ hv)]
      rfl

theorem integral_DzIter_mul_adjDzIter {u v : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry u) Qd) (hv : TestQ v)
    (j : ℕ) :
    ∫ p, Work.Spaces.DzIter j u p.1 p.2 * v p.1 p.2 ∂Qμ
      = ∫ p, u p.1 p.2 * adjDzIter j v p.1 p.2 ∂Qμ :=
  integral_DzIter_mul_adjDzIter_aux hu j hv

theorem integral_DthIter_mul_adjDthIter_aux {u : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry u) Qd) (i : ℕ) :
    ∀ {v : ℝ → ℝ → ℝ}, TestQ v →
      ∫ p, Work.Spaces.DthIter i u p.1 p.2 * v p.1 p.2 ∂Qμ
        = ∫ p, u p.1 p.2 * adjDthIter i v p.1 p.2 ∂Qμ := by
  induction i with
  | zero => intro v hv; rfl
  | succ i ih =>
      intro v hv
      rw [Work.Spaces.DthIter_succ]
      rw [integral_Dth_mul_adjTh (u := Work.Spaces.DthIter i u) (v := v)
        (Work.FTS.LocData.contDiffOn_DthIter isOpen_Qd hu i) hv]
      rw [ih (TestQ_adjTh hv)]
      rfl

theorem integral_DthIter_mul_adjDthIter {u v : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry u) Qd) (hv : TestQ v)
    (i : ℕ) :
    ∫ p, Work.Spaces.DthIter i u p.1 p.2 * v p.1 p.2 ∂Qμ
      = ∫ p, u p.1 p.2 * adjDthIter i v p.1 p.2 ∂Qμ :=
  integral_DthIter_mul_adjDthIter_aux hu i hv

/-! ## The adjointness of `mixed j i` -/


end Work.FTS.Apriori.Limit
end
end
-- ===== merged: Submission.Work.FTS.ClassC.RopGen.Trace.mollFatou =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC.RopGen.Trace

set_option autoImplicit false
set_option linter.unusedVariables false

theorem mollFatou : ∀ (G : ℝ → ℝ → ℝ), Work.FTS.EllSol.EllPkgAux.TraceClass G →
    Work.FTS.EllSol.EllPkgAux.FourInts G →
    (∀ (δ ε : ℝ), Work.FTS.EllSol.EllPkgAux.Params δ ε → MeasureTheory.IntegrableOn
      (fun z : ℝ => Work.EllipticEst.Core.mixIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z)
      Work.Spaces.Iz) →
    ∀ η : ℝ, 0 < η → ∃ δ ε : ℝ, Work.FTS.EllSol.EllPkgAux.Params δ ε ∧
      (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z)
        ≤ (∫ z in Work.Spaces.Iz,
            Work.EllipticEst.Core.mixIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z) + η := by
  intro G hT hF hint η hη
  -- the slice bound and the local integrability of the dominating function
  obtain ⟨C, hC, hslBound⟩ := Work.FTS.EllSol.EllPkgAux.mollSliceBound
  obtain ⟨hslG, hintMGG⟩ := hslBound G hT hF
  have hS : Work.FTS.EllipticEst.SmoothOpen G := hT.1
  -- the domination hypothesis of `zmollDzPth`
  have hdom := Work.FTS.EllSol.EllPkgAux.mollHdom G hS C hC hslG hintMGG
  -- the identification of the mixed derivative of the approximant
  have hid : ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G t t)) z θ
        = ∫ t' : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd t (Real.log z - t')
            * (∫ s : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd t (θ - s)
                * Work.FTS.EllSol.EllPkgAux.Hxyc G t' s) :=
    fun t ht0 ht1 =>
      Work.FTS.ClassC.RopGen.Trace.ZmollAux.zmollDzPth G hT hdom ht0 ht1 ht0 ht1
  -- the limit of the double kernel convolution
  have hderiv : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      deriv (fun x' => deriv (fun y' => Work.FTS.EllSol.EllPkgAux.Hxyc G x' y') θ) (Real.log z)
        = Work.Spaces.Dz (Work.Spaces.pth G) z θ :=
    fun z hz θ h0 h1 => Work.FTS.EllSol.EllPkgAux.mollTargetDeriv G hS hz h0 h1
  have hlim : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto
        (fun t : ℝ => ∫ u : ℝ, ∫ v : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd t u
          * Work.FTS.EllSol.EllPkgAux.sKerd t v
          * Work.FTS.EllSol.EllPkgAux.Hxyc G (Real.log z - u) (θ - v))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (deriv (fun x' => deriv (fun y' => Work.FTS.EllSol.EllPkgAux.Hxyc G x' y') θ)
          (Real.log z))) := by
    intro z hz θ h0 h1
    have hU : IsOpen ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      isOpen_univ.prod isOpen_Ioo
    have hmem : (Real.log z, θ) ∈ (Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨trivial, h0, h1⟩
    exact Work.FTS.EllSol.EllPkgAux.mollKernelLimit
      (H := Work.FTS.EllSol.EllPkgAux.Hxyc G)
      (U := (Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))
      (x := Real.log z) (y := θ) hU hmem
      (Work.FTS.EllSol.EllPkgAux.contDiffOn_uncurry_Hxyc G hS 2)
  -- pointwise convergence along the sequence
  have hconv := Work.FTS.EllSol.EllPkgAux.mollHconv G hS hderiv hid hlim
  -- honesty of the approximant's slice integrals
  have hhon : ∀ (n : ℕ) (z : ℝ), 0 < z →
      MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.pth
          (Work.FTS.EllSol.PkgK5.K5c.zmoll G (Work.FTS.EllSol.EllPkgAux.tseq n)
            (Work.FTS.EllSol.EllPkgAux.tseq n))) z θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun n z hz =>
      Work.FTS.EllSol.EllPkgAux.mollHon G hS (Work.FTS.EllSol.EllPkgAux.tseq n)
        (Work.FTS.EllSol.EllPkgAux.tseq_pos n) (Work.FTS.EllSol.EllPkgAux.tseq_le_half n) z hz
        (fun θ hθ => hid (Work.FTS.EllSol.EllPkgAux.tseq n)
          (Work.FTS.EllSol.EllPkgAux.tseq_pos n) (Work.FTS.EllSol.EllPkgAux.tseq_le_half n)
          z hz θ hθ)
  -- honesty of the datum's slice integrals
  have hhonG : ∀ z : ℝ, 0 < z →
      MeasureTheory.AEStronglyMeasurable
        (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun z hz => Work.FTS.EllSol.EllPkgAux.aeStronglyMeasurable_slice_G G hS hz
  exact Work.FTS.EllSol.EllPkgAux.mollFatouAssembly G hT hF hint hconv hhon hhonG η hη

end Work.FTS.ClassC.RopGen.Trace
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1.coer1_Lhat =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false


end Work.FTS.CoercivityFix.Coer1
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1SO.wip_Dz_self_le_SO =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1SO

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The open-class `z`-integration by parts -/

/-- The `z`-slice `z ↦ z (u(z,θ) w(z))²` of a function `C^∞` on the *open* quadrant is
differentiable at every `x > 0`, with the derivative `deriv` of itself.  This is the
`SmoothOpen` analogue of `Coer1.hasDerivAt_zw_sq_Q`. -/
theorem hasDerivAt_zw_sq_O {u : Fn} (hu : Work.FTS.EllipticEst.SmoothOpen u) {θ x : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hx : 0 < x) :
    HasDerivAt (fun z => z * (u z θ * Work.Spaces.w z) ^ 2)
      (deriv (fun z => z * (u z θ * Work.Spaces.w z) ^ 2) x) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hu_d : HasDerivAt (fun z => u z θ) (Work.Spaces.pz u x θ) x :=
    hu.hasDerivAt_slice hθ hx
  have hw_d : HasDerivAt Work.Spaces.w (-2 * (1 + x) / x ^ 3) x :=
    Work.Coercivity.hasDerivAt_w hx0
  have huW : HasDerivAt (fun z => u z θ * Work.Spaces.w z)
      (Work.Spaces.pz u x θ * Work.Spaces.w x + u x θ * (-2 * (1 + x) / x ^ 3)) x :=
    hu_d.mul hw_d
  have h := (hasDerivAt_id x).mul (huW.pow 2)
  exact h.congr_deriv h.deriv.symm

/-- **The boundary term of the `z`-integration by parts vanishes, in integral form** (open
class): for `θ` in the open interval, `∫₀^∞ ∂_z(z (u(·,θ) w)²) dz = 0`.  This is the
fundamental theorem of calculus on `(0,∞)`: the integrand is the derivative of
`z ↦ z(u w)²`, which has limit `0` both at `z = 0⁺` and at `z = ∞` by
`ZIBPO.bd0`/`ZIBPO.bdTop`. -/
theorem deriv_zw_sq_integral_O (u : Fn) (hu : ZIBPO u) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hint : MeasureTheory.IntegrableOn
      (fun z => deriv (fun z' => z' * (u z' θ * Work.Spaces.w z') ^ 2) z) (Set.Ioi 0)) :
    ∫ z in Set.Ioi (0 : ℝ), deriv (fun z' => z' * (u z' θ * Work.Spaces.w z') ^ 2) z = 0 := by
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z => z * (u z θ * Work.Spaces.w z) ^ 2)
        (deriv (fun z => z * (u z θ * Work.Spaces.w z) ^ 2) x) x :=
    fun x hx => hasDerivAt_zw_sq_O hu.smooth hθ hx
  have htop : Tendsto (fun z => z * (u z θ * Work.Spaces.w z) ^ 2) atTop (𝓝 0) :=
    hu.bdTop θ hθ
  have hcont : ContinuousWithinAt (fun z => z * (u z θ * Work.Spaces.w z) ^ 2)
      (Set.Ici (0 : ℝ)) 0 := by
    have h2 : Tendsto (fun z => z * (u z θ * Work.Spaces.w z) ^ 2) (𝓝[{(0 : ℝ)}] 0)
        (𝓝 (0 * (u 0 θ * Work.Spaces.w 0) ^ 2)) := by
      rw [nhdsWithin_singleton]
      exact tendsto_pure_nhds _ 0
    have h1 : Tendsto (fun z => z * (u z θ * Work.Spaces.w z) ^ 2) (𝓝[>] (0 : ℝ))
        (𝓝 (0 * (u 0 θ * Work.Spaces.w 0) ^ 2)) := by
      simpa using hu.bd0 θ hθ
    have h3 : Tendsto (fun z => z * (u z θ * Work.Spaces.w z) ^ 2)
        (𝓝[>] (0 : ℝ) ⊔ 𝓝[{(0 : ℝ)}] 0) (𝓝 (0 * (u 0 θ * Work.Spaces.w 0) ^ 2)) := h1.sup h2
    rw [nhdsGT_sup_nhdsWithin_singleton] at h3
    exact h3
  have key := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htop
  simpa using key

/-- **The `z`-integration by parts of §6 on a single `θ`-slice** (open class): for `θ` in the
open interval, `∫₀^∞ z ∂_z((u(z,θ) w(z))²) dz = − ∫₀^∞ (u(z,θ) w(z))² dz`. -/
theorem slice_z_deriv_integral_O (u : Fn) (hu : ZIBPO u) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hintD : MeasureTheory.IntegrableOn
      (fun z => deriv (fun z' => z' * (u z' θ * Work.Spaces.w z') ^ 2) z) (Set.Ioi 0))
    (hintS : MeasureTheory.IntegrableOn (fun z => (u z θ * Work.Spaces.w z) ^ 2) (Set.Ioi 0)) :
    ∫ z in Work.Spaces.Iz, z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z
      = -∫ z in Work.Spaces.Iz, (u z θ * Work.Spaces.w z) ^ 2 := by
  have hftc := deriv_zw_sq_integral_O u hu hθ hintD
  have hIzeq : Work.Spaces.Iz =ᵐ[(volume : Measure ℝ)] Set.Ioi 0 := by
    rw [MeasureTheory.ae_eq_set]
    refine ⟨?_, ?_⟩
    · have h : Work.Spaces.Iz \ Set.Ioi 0 = {0} := by
        ext x
        simp only [Set.mem_sdiff, Set.mem_Ioi, Set.mem_singleton_iff, Work.Spaces.Iz,
          Set.mem_Ici, not_lt]
        constructor
        · rintro ⟨h1, h2⟩; exact le_antisymm h2 h1
        · rintro rfl; exact ⟨le_refl 0, le_refl 0⟩
      rw [h, Real.volume_singleton]
    · have h : Set.Ioi (0 : ℝ) \ Work.Spaces.Iz = ∅ := by
        rw [Work.Spaces.Iz, Set.sdiff_eq_empty]
        exact Set.Ioi_subset_Ici_self
      rw [h, MeasureTheory.measure_empty]
  have hsub : ∫ z in Set.Ioi (0 : ℝ),
        (deriv (fun z' => z' * (u z' θ * Work.Spaces.w z') ^ 2) z
          - (u z θ * Work.Spaces.w z) ^ 2)
      = - ∫ z in Set.Ioi (0 : ℝ), (u z θ * Work.Spaces.w z) ^ 2 := by
    rw [MeasureTheory.integral_sub hintD hintS, hftc, zero_sub]
  have hcongr : ∫ z in Set.Ioi (0 : ℝ),
        (deriv (fun z' => z' * (u z' θ * Work.Spaces.w z') ^ 2) z
          - (u z θ * Work.Spaces.w z) ^ 2)
      = ∫ z in Set.Ioi (0 : ℝ), z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
    rw [deriv_zw_sq_O hu.smooth hz hθ]; ring
  have hL : ∫ z in Work.Spaces.Iz, z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z
      = ∫ z in Set.Ioi (0 : ℝ), z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z :=
    MeasureTheory.setIntegral_congr_set hIzeq
  have hR : ∫ z in Work.Spaces.Iz, (u z θ * Work.Spaces.w z) ^ 2
      = ∫ z in Set.Ioi (0 : ℝ), (u z θ * Work.Spaces.w z) ^ 2 :=
    MeasureTheory.setIntegral_congr_set hIzeq
  rw [hL, hR, ← hcongr, hsub]

/-! ## The `wip`-identity in the open class -/

/-- The integrand `𝓛u · u · w²σ` on the product `Iz × Iθ`. -/
def LwSO (u : Fn) (σ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  Work.Coercivity.L u p.1 p.2 * u p.1 p.2 * Work.Spaces.w p.1 ^ 2 * σ p.2

/-- The integrand `u² w²σ` on the product `Iz × Iθ`. -/
def RwSO (u : Fn) (σ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2 * σ p.2

/-- The integrand `z ∂_z((u w)²) σ` on the product `Iz × Iθ`. -/
def DwSO (u : Fn) (σ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1 * deriv (fun z' => (u z' p.2 * Work.Spaces.w z') ^ 2) p.1 * σ p.2

/-- **The paper's identity `(LW)` integrated, in the open class `SmoothOpen`**:
`⟨𝓛u, u⟩_{w²σ} = ½⟨u,u⟩_{w²σ}`.  This is the open-class copy of `Coer1.wip_L_self_Q`; the
only change is that the pointwise identity `l_self_w_sq_O` (proved from
`SmoothOpen.hasDerivAt_slice`) replaces `l_self_w_sq_Q`. -/
theorem wip_L_self_QO (u : Fn) (hu : ZIBPO u) (σ : ℝ → ℝ)
    (h1 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * Work.Spaces.w z ^ 2 * σ θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (h2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.L u z θ * u z θ * Work.Spaces.w z ^ 2 * σ θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) (Work.Coercivity.L u) u
      = (1 / 2) * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u := by
  set μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict Work.Spaces.Iz with hμ
  set ν : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict Work.Spaces.Iθ with hν
  have hmeas : μ.prod ν
      = (volume : MeasureTheory.Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    rw [hμ, hν, MeasureTheory.Measure.prod_restrict,
      ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  have hF1 : MeasureTheory.Integrable (LwSO u σ) (μ.prod ν) := by
    rw [hmeas]; exact h2
  have hF2 : MeasureTheory.Integrable (RwSO u σ) (μ.prod ν) := by
    rw [hmeas]; exact h1
  -- a.e. positivity in the radial variable
  have haepos : ∀ᵐ p ∂(μ.prod ν), 0 < p.1 := by
    have hslice : ∀ᵐ z ∂μ, 0 < z := by
      rw [hμ, MeasureTheory.ae_restrict_iff (p := fun z => 0 < z) measurableSet_Ioi,
        MeasureTheory.ae_iff]
      have hset : {z : ℝ | ¬ (z ∈ Work.Spaces.Iz → 0 < z)} = {0} := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Work.Spaces.Iz, Set.mem_Ici, not_imp]
        constructor
        · rintro ⟨h1, h2⟩; exact le_antisymm (not_lt.mp h2) h1
        · intro h; rw [h]; exact ⟨le_refl 0, lt_irrefl 0⟩
      rw [hset, Real.volume_singleton]
    have h : ∀ᵐ p ∂(μ.prod ν), p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.univ :=
      (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
        (s := Set.Ioi (0 : ℝ) ×ˢ Set.univ) (measurableSet_Ioi.prod MeasurableSet.univ)).mpr
        (hslice.mono (fun x hx => Filter.Eventually.of_forall (fun _ => by simp [hx])))
    simpa using h
  -- a.e. interiority of the angle
  have haeθ : ∀ᵐ p ∂(μ.prod ν), p.2 ∈ Set.Ioo 0 (π / 2) := by
    have h1 : ∀ᵐ θ ∂ν, θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
      rw [hν]; exact Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo
    have h : ∀ᵐ p ∂(μ.prod ν), p ∈ Set.univ ×ˢ Set.Ioo (0 : ℝ) (π / 2) :=
      (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
        (s := Set.univ ×ˢ Set.Ioo (0 : ℝ) (π / 2))
        (MeasurableSet.univ.prod measurableSet_Ioo)).mpr
        (Filter.Eventually.of_forall (fun _ => h1.mono (fun y hy => ⟨Set.mem_univ _, hy⟩)))
    simpa using h
  -- the pointwise identity `𝓛u·u·w²σ = u²w²σ + ½ z∂_z((uw)²)σ`, a.e. on the product
  have hae_id : ∀ᵐ p ∂(μ.prod ν), LwSO u σ p = RwSO u σ p + (1 / 2) * DwSO u σ p := by
    filter_upwards [haepos, haeθ] with p hp hθ
    have h := l_self_w_sq_O hu.smooth hp hθ
    dsimp only [LwSO, RwSO, DwSO]
    rw [h]; ring
  have hF3 : MeasureTheory.Integrable (DwSO u σ) (μ.prod ν) := by
    have h2' : MeasureTheory.Integrable
        (fun p => 2 * LwSO u σ p - 2 * RwSO u σ p) (μ.prod ν) :=
      (hF1.const_mul 2).sub (hF2.const_mul 2)
    refine h2'.congr ?_
    filter_upwards [hae_id] with p hp
    linarith
  have hΦval : ∫ p, LwSO u σ p ∂(μ.prod ν)
      = ∫ p, RwSO u σ p ∂(μ.prod ν) + (1 / 2) * ∫ p, DwSO u σ p ∂(μ.prod ν) := by
    rw [MeasureTheory.integral_congr_ae hae_id]
    rw [MeasureTheory.integral_add hF2 (hF3.const_mul (1 / 2)),
      MeasureTheory.integral_const_mul]
  -- the derivative term is minus the norm: Fubini in `θ`, then the slice identity
  have hDval : ∫ p, DwSO u σ p ∂(μ.prod ν) = -∫ p, RwSO u σ p ∂(μ.prod ν) := by
    have hinner : (fun θ => ∫ z, DwSO u σ (z, θ) ∂μ)
        =ᵐ[ν] (fun θ => -∫ z, RwSO u σ (z, θ) ∂μ) := by
      filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo, hu.intSq, hu.intDeriv]
        with θ hθIoo hθSq hθDer
      have h1 : (∫ z, DwSO u σ (z, θ) ∂μ)
          = (∫ z, z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z ∂μ) * σ θ := by
        dsimp only [DwSO]
        rw [MeasureTheory.integral_mul_const]
      have h2 : (∫ z, z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z ∂μ)
          = -(∫ z, (u z θ * Work.Spaces.w z) ^ 2 ∂μ) := by
        rw [show (∫ z, z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z ∂μ)
            = ∫ z in Work.Spaces.Iz,
                z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z from rfl,
          show (∫ z, (u z θ * Work.Spaces.w z) ^ 2 ∂μ)
            = ∫ z in Work.Spaces.Iz, (u z θ * Work.Spaces.w z) ^ 2 from rfl,
          slice_z_deriv_integral_O u hu hθIoo hθDer hθSq]
      have h3 : (∫ z, RwSO u σ (z, θ) ∂μ)
          = (∫ z, (u z θ * Work.Spaces.w z) ^ 2 ∂μ) * σ θ := by
        dsimp only [RwSO]
        rw [MeasureTheory.integral_mul_const]
        congr 1
        exact MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall (fun z => by ring))
      rw [h1, h2, h3]; ring
    rw [MeasureTheory.integral_prod_symm (DwSO u σ) hF3,
      MeasureTheory.integral_congr_ae hinner, MeasureTheory.integral_neg,
      ← MeasureTheory.integral_prod_symm (RwSO u σ) hF2]
  -- Fubini bridge: both `wip`s are product-measure integrals
  have hint2' : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.L u z θ * u z θ
        * (Work.Spaces.w z ^ 2 * σ θ))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine h2.congr ?_
    filter_upwards with p
    dsimp only [Function.uncurry]
    ring
  have hint' : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ
        * (Work.Spaces.w z ^ 2 * σ θ))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine h1.congr ?_
    filter_upwards with p
    dsimp only [Function.uncurry]
    ring
  have hwL : Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
        (Work.Coercivity.L u) u = ∫ p, LwSO u σ p ∂(μ.prod ν) := by
    rw [Work.Coercivity.wip_eq_integral_prod (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
      (Work.Coercivity.L u) u hint2']
    rw [hμ, hν]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    dsimp only [LwSO, Function.uncurry]
    ring
  have hwR : Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u
      = ∫ p, RwSO u σ p ∂(μ.prod ν) := by
    rw [Work.Coercivity.wip_eq_integral_prod (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u hint']
    rw [hμ, hν]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    dsimp only [RwSO, Function.uncurry]
    ring
  rw [hwL, hwR, hΦval, hDval]
  ring

/-! ## The generic `wip` lemmas (copies of `Assembly/V_bounds.lean`'s, no regularity used) -/

/-- `wip` is a congruence in both pairing arguments. -/
theorem wip_congr_pt_SO {ρ : Fn} {A A' B B' : Fn} (hA : ∀ z θ, A z θ = A' z θ)
    (hB : ∀ z θ, B z θ = B' z θ) : Work.Coercivity.wip ρ A B = Work.Coercivity.wip ρ A' B' := by
  rw [Work.Coercivity.wip, Work.Coercivity.wip]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  rw [hA z θ, hB z θ]

/-- `⟨u/(1+z), u⟩_{w²σ} ≤ ⟨u,u⟩_{w²σ}` for a nonnegative weight: the factor `1/(1+z) ≤ 1`
on `z ≥ 0`. -/
theorem wip_div_one_add_self_le_SO {ρ u : Fn} (hρ : ∀ z θ, θ ∈ Work.Spaces.Iθ → 0 ≤ ρ z θ)
    (h : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => u z θ ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hd : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      u z θ ^ 2 * ρ z θ / (1 + z))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Work.Coercivity.wip ρ (fun z θ => u z θ / (1 + z)) u ≤ Work.Coercivity.wip ρ u u := by
  have hIsum : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      u z θ / (1 + z) * u z θ * ρ z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q hd (fun z θ => by ring)
  have hIu : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      u z θ * u z θ * ρ z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q h (fun z θ => by ring)
  have e1 : Work.Coercivity.wip ρ (fun z θ => u z θ / (1 + z)) u
      = ∫ p : ℝ × ℝ, u p.1 p.2 ^ 2 * ρ p.1 p.2 / (1 + p.1)
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.Coercivity.wip_eq_integral_prod ρ (fun z θ => u z θ / (1 + z)) u hIsum]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    ring
  have e2 : Work.Coercivity.wip ρ u u
      = ∫ p : ℝ × ℝ, u p.1 p.2 ^ 2 * ρ p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.Coercivity.wip_eq_integral_prod ρ u u hIu]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    ring
  rw [e1, e2]
  have hI1 : MeasureTheory.Integrable (fun p : ℝ × ℝ => u p.1 p.2 ^ 2 * ρ p.1 p.2 / (1 + p.1))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.FTS.CoercivityFix.Coer1.iz_prod_restrict]
    exact hd
  have hI2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => u p.1 p.2 ^ 2 * ρ p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Work.FTS.CoercivityFix.Coer1.iz_prod_restrict]
    exact h
  refine MeasureTheory.integral_mono_ae hI1 hI2 ?_
  filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_prod_fst_pos,
    Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem_Ioo] with p hp1 hp2
  have hρnn : 0 ≤ ρ p.1 p.2 := hρ p.1 p.2 ⟨le_of_lt hp2.1, le_of_lt hp2.2⟩
  have hz : 0 < 1 + p.1 := by linarith [hp1]
  have hle : 1 / (1 + p.1) ≤ 1 := by
    rw [div_le_one hz]; linarith
  have hsq : 0 ≤ u p.1 p.2 ^ 2 * ρ p.1 p.2 := mul_nonneg (sq_nonneg _) hρnn
  calc u p.1 p.2 ^ 2 * ρ p.1 p.2 / (1 + p.1)
      = (u p.1 p.2 ^ 2 * ρ p.1 p.2) * (1 / (1 + p.1)) := by ring
    _ ≤ (u p.1 p.2 ^ 2 * ρ p.1 p.2) * 1 := mul_le_mul_of_nonneg_left hle hsq
    _ = u p.1 p.2 ^ 2 * ρ p.1 p.2 := mul_one _

/-! ## The `D_z`-self estimate in the open class -/

/-- **The pairing of a slot with itself is controlled by the norm.**  For `u` with the
open-class `z`-IBP hypotheses (`ZIBPO`), the honesty of `u²w²σ` and of `𝓛u·u·w²σ`, and
`σ ≥ 0` on `Iθ`, `|⟨D_z u, u⟩_{w²σ}| ≤ (5/2)⟨u, u⟩_{w²σ}`.

Indeed `⟨𝓛u, u⟩_{w²σ} = ½⟨u,u⟩_{w²σ}` and `𝓛u = u + D_z u - 2u/(1+z)`, so
`⟨D_z u, u⟩_{w²σ} = 2⟨u/(1+z), u⟩_{w²σ} - ½⟨u,u⟩_{w²σ}` with
`0 ≤ ⟨u/(1+z), u⟩_{w²σ} ≤ ⟨u,u⟩_{w²σ}`. -/
theorem wip_Dz_self_le_SO {u : Work.FTS.Galerkin.Fn}
    (hu : Work.FTS.CoercivityFix.Coer1SO.ZIBPO u)
    {σ : ℝ → ℝ} (hσ : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ σ θ)
    (h2 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      u z θ ^ 2 * Work.Spaces.w z ^ 2 * σ θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hL : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.L u z θ * u z θ * Work.Spaces.w z ^ 2 * σ θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    |Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
        (Work.Spaces.Dz u) u|
      ≤ (5 / 2) * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u := by
  have h2' : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      u z θ * u z θ * (Work.Spaces.w z ^ 2 * σ θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q h2 (fun z θ => by ring)
  have hL' : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.L u z θ * u z θ * (Work.Spaces.w z ^ 2 * σ θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q hL (fun z θ => by ring)
  have h3 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      u z θ * u z θ * (Work.Spaces.w z ^ 2 * σ θ) / (1 + z)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_div_one_add_Q h2'
  have hLu : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Coercivity.L u z θ - u z θ) * u z θ * (Work.Spaces.w z ^ 2 * σ θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine (hL'.sub h2').congr (Filter.Eventually.of_forall fun p => ?_)
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Pi.sub_apply]
    ring
  have h2u : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (2 * (u z θ / (1 + z))) * u z θ * (Work.Spaces.w z ^ 2 * σ θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine (h3.const_mul 2).congr (Filter.Eventually.of_forall fun p => ?_)
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair]
    ring
  have hself := wip_L_self_QO u hu σ h2 hL
  have e0 : Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
        (Work.Spaces.Dz u) u
      = Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
          (fun z θ => (Work.Coercivity.L u z θ - u z θ) + 2 * (u z θ / (1 + z))) u := by
    refine wip_congr_pt_SO (fun z θ => ?_) (fun z θ => rfl)
    simp only [Work.Coercivity.L, Work.Spaces.Dz]
    ring
  have e1 : Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
        (fun z θ => (Work.Coercivity.L u z θ - u z θ) + 2 * (u z θ / (1 + z))) u
      = Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
          (fun z θ => Work.Coercivity.L u z θ - u z θ) u
        + Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
          (fun z θ => 2 * (u z θ / (1 + z))) u :=
    Work.Coercivity.wip_add_left hLu h2u
  have e2 : Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
        (fun z θ => Work.Coercivity.L u z θ - u z θ) u
      = Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) (Work.Coercivity.L u) u
        - Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u :=
    Work.FTS.CoercivityFix.Coer1.wip_sub_left hL' h2'
  have e3 : Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
        (fun z θ => 2 * (u z θ / (1 + z))) u
      = 2 * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
          (fun z θ => u z θ / (1 + z)) u :=
    Work.Coercivity.wip_smul_left
  have hkey : Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
        (Work.Spaces.Dz u) u
      = 2 * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
            (fun z θ => u z θ / (1 + z)) u
        - (1 / 2) * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u := by
    rw [e0, e1, e2, e3, hself]
    ring
  have hρnn : ∀ z θ, θ ∈ Work.Spaces.Iθ → 0 ≤ (fun z θ => Work.Spaces.w z ^ 2 * σ θ) z θ :=
    fun z θ hθ => mul_nonneg (sq_nonneg _) (hσ θ hθ)
  have hA : 0 ≤ Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u :=
    Work.Coercivity.wip_self_nonneg hρnn
  have hT3nn : 0 ≤ Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
      (fun z θ => u z θ / (1 + z)) u := by
    rw [Work.Coercivity.wip]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ici (fun z hz => ?_)
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
    have hρ : 0 ≤ Work.Spaces.w z ^ 2 * σ θ := mul_nonneg (sq_nonneg _) (hσ θ hθ)
    have hz0 : (0 : ℝ) ≤ z := hz
    have h1z : 0 < 1 + z := by linarith
    have : u z θ / (1 + z) * u z θ = u z θ ^ 2 / (1 + z) := by ring
    rw [this]
    exact mul_nonneg (div_nonneg (sq_nonneg _) h1z.le) hρ
  have hT3le : Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
        (fun z θ => u z θ / (1 + z)) u
      ≤ Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u :=
    wip_div_one_add_self_le_SO hρnn
      (Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q h2 (fun z θ => by ring))
      (Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q h3 (fun z θ => by ring))
  rw [hkey]
  have habs : |2 * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
        (fun z θ => u z θ / (1 + z)) u
      - (1 / 2) * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u|
      ≤ 2 * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
          (fun z θ => u z θ / (1 + z)) u
        + (1 / 2) * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u := by
    have h := abs_sub (2 * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
          (fun z θ => u z θ / (1 + z)) u)
        ((1 / 2) * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u)
    have h1 : |2 * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
          (fun z θ => u z θ / (1 + z)) u|
        = 2 * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ)
            (fun z θ => u z θ / (1 + z)) u :=
      abs_of_nonneg (by linarith [hT3nn])
    have h2 : |(1 / 2) * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u|
        = (1 / 2) * Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * σ θ) u u :=
      abs_of_nonneg (by linarith [hA])
    rw [h1, h2] at h
    exact h
  linarith [habs, hA, hT3le]

end Work.FTS.CoercivityFix.Coer1SO
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1T.SlotsDzGam =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1T

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The comparison `EnOne u ≤ En η u` -/

/-- On the open angular interval the plain radial weight `w²` is dominated by the
`η`-weight `w²·sin(2θ)^{-η}`; integrating gives `EnOne u ≤ En η u` as soon as both
integrals are honest. -/
theorem EnOne_le_En_eta {u : Fn}
    (h1 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (h2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ =>
        u z θ ^ 2 * Work.Spaces.w z ^ 2 * Coer1.sig Work.Spaces.eta θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Coer1.EnOne u ≤ Coer1.En Work.Spaces.eta u := by
  have h2' : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2 * Coer1.sig Work.Spaces.eta p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [Coer1.iz_prod_restrict]; exact h2
  have e1 : Coer1.EnOne u = ∫ p : ℝ × ℝ, u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := Coer1.EnOne_eq_prod h1
  have e2 : Coer1.En Work.Spaces.eta u = ∫ p : ℝ × ℝ,
      u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2 * Coer1.sig Work.Spaces.eta p.2
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (MeasureTheory.integral_prod (fun p : ℝ × ℝ =>
      u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2 * Coer1.sig Work.Spaces.eta p.2) h2').symm
  rw [e1, e2]
  refine MeasureTheory.integral_mono_ae ?_ h2' ?_
  · rw [Coer1.iz_prod_restrict]; exact h1
  · filter_upwards [Coer1.ae_prod_snd_mem_Ioo] with p hp
    have hle : Work.Spaces.w p.1 ^ 2 ≤ Coer1.Rho Work.Spaces.eta p.1 p.2 :=
      Coer1.w2_le_Rho_eta p.1 p.2 hp
    have h := mul_le_mul_of_nonneg_left hle (sq_nonneg (u p.1 p.2))
    simpa only [Coer1.Rho, Coer1.sig, mul_assoc] using h

/-! ## The three comparisons needed by the ledger -/




/-! ## The arithmetic ledger -/


end Work.FTS.CoercivityFix.Coer1T
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1T.slotDz_LGammaT =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1T

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Integrals over `Iz = [0,∞)` and `(0,∞)` agree (the two sets differ by `{0}`). -/
theorem setIntegral_Iz_eq_Ioi (g : ℝ → ℝ) :
    ∫ z in Work.Spaces.Iz, g z = ∫ z in Set.Ioi (0 : ℝ), g z := by
  show (∫ z in Set.Ici (0 : ℝ), g z) = ∫ z in Set.Ioi (0 : ℝ), g z
  exact (MeasureTheory.setIntegral_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))).symm

/-- Integrability over `Iz = [0,∞)` and over `(0,∞)` agree. -/
theorem integrableOn_Iz_iff_Ioi (g : ℝ → ℝ) :
    MeasureTheory.IntegrableOn g Work.Spaces.Iz
      ↔ MeasureTheory.IntegrableOn g (Set.Ioi (0 : ℝ)) := by
  have h : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
    show MeasureTheory.volume.restrict (Set.Ici (0 : ℝ)) = _
    exact (Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))).symm
  rw [MeasureTheory.IntegrableOn, MeasureTheory.IntegrableOn, h]






/-! ## The endpoint vanishing of the profile and the angular integration by parts -/




/-! ## The bound `(C₀ f)² ≤ 64 Ef f` in the interior class -/





/-- The radial majorant `4(L₁₂dens)² + 4(L₁₂f/z)² + 16C₀²/(1+z)²` of the nonlocal deflection
`Z₃ + Z₄ + Z₇` of `D_z𝓛_Γ^T`. -/
noncomputable def ZrestBracket (f : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  4 * (Work.FM.L12dens Work.Spaces.K f z) ^ 2
    + 4 * (Work.Coercivity.L12f f z / z) ^ 2
    + 16 * (Work.Coercivity.C0 f) ^ 2 / (1 + z) ^ 2

/-- The full majorant of the squared nonlocal deflection: `ZrestBracket f z` times the `θ`-weight
`300 sin(2θ)^{-η}`. -/
noncomputable def ZrestMaj (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => 300 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ * ZrestBracket f z


/-- `z ↦ Kavg f z` is continuous on `z > 0` (it is `z · L₁₂dens`). -/
theorem continuousOn_Kavg_Ioi (f : ℝ → ℝ → ℝ) (hfH : Work.Coercivity.HardyHyp f) :
    ContinuousOn (fun z : ℝ => Work.Coercivity.Kavg f z) (Set.Ioi 0) := by
  have hL : ContinuousOn (fun z : ℝ => Work.FM.L12dens Work.Spaces.K f z) (Set.Ioi 0) :=
    fun z hz => (hfH.hcont z hz).continuousWithinAt
  refine (continuousOn_id.mul hL).congr (fun z hz => ?_)
  have hz0 : z ≠ 0 := ne_of_gt hz
  show Work.Coercivity.Kavg f z = z * Work.FM.L12dens Work.Spaces.K f z
  rw [Work.FM.L12dens_eq (K := Work.Spaces.K) (f := f) (s := z) hz0]
  simp only [Work.Coercivity.Kavg, Work.Spaces.Iθ]
  field_simp

/-- The sum `Z₃ + Z₄ + Z₇` of the three nonlocal deflections of `D_z𝓛_Γ^T` is continuous on the
open quadrant. -/
theorem continuousOn_Zrest_Q (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hfH : Work.Coercivity.HardyHyp f) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Coercivity.Z3 α f p.1 p.2
      + Work.Coercivity.Z4 α f p.1 p.2 + Work.Coercivity.Z7 α f p.1 p.2)
      Work.FTS.CoercivityFix.Coer1.Qd := by
  have hc : Work.Spaces.c α ≠ 0 := Work.Coercivity.c_ne_zero hα hα1
  have hKavg : ContinuousOn (fun p : ℝ × ℝ => Work.Coercivity.Kavg f p.1)
      Work.FTS.CoercivityFix.Coer1.Qd :=
    (continuousOn_Kavg_Ioi f hfH).comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hL12f : ContinuousOn (fun p : ℝ × ℝ => Work.Coercivity.L12f f p.1)
      Work.FTS.CoercivityFix.Coer1.Qd :=
    (Work.Coercivity.L12f_continuousOn f hfH).comp continuous_fst.continuousOn
      (fun p hp => hp.1)
  have hGam : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2)
      Work.FTS.CoercivityFix.Coer1.Qd :=
    (Work.Coercivity.continuousOn_Gam α hα).comp continuous_snd.continuousOn
      (fun p hp => ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩)
  have hden2 : ∀ p ∈ Work.FTS.CoercivityFix.Coer1.Qd,
      Work.Spaces.c α * (1 + p.1) ^ 2 ≠ 0 := fun p hp =>
    mul_ne_zero hc (ne_of_gt (by have h : (0 : ℝ) < p.1 := hp.1; positivity))
  have hden3 : ∀ p ∈ Work.FTS.CoercivityFix.Coer1.Qd,
      Work.Spaces.c α * (1 + p.1) ^ 3 ≠ 0 := fun p hp =>
    mul_ne_zero hc (ne_of_gt (by have h : (0 : ℝ) < p.1 := hp.1; positivity))
  have hden4 : ∀ p ∈ Work.FTS.CoercivityFix.Coer1.Qd, (1 + p.1) ^ 4 ≠ 0 := fun p hp =>
    ne_of_gt (by have h : (0 : ℝ) < p.1 := hp.1; positivity)
  have hZ3 : ContinuousOn (fun p : ℝ × ℝ => Work.Coercivity.Z3 α f p.1 p.2)
      Work.FTS.CoercivityFix.Coer1.Qd := by
    have hA : ContinuousOn (fun p : ℝ × ℝ =>
        2 * p.1 * Work.Spaces.Gam α p.2 / (Work.Spaces.c α * (1 + p.1) ^ 2))
        Work.FTS.CoercivityFix.Coer1.Qd :=
      (((continuous_const.mul continuous_fst).continuousOn).mul hGam).div
        ((continuous_const.mul ((continuous_const.add continuous_fst).pow 2)).continuousOn)
        hden2
    refine (hA.mul hKavg).congr (fun p hp => ?_)
    simp only [Work.Coercivity.Z3, Pi.mul_apply]
  have hZ4 : ContinuousOn (fun p : ℝ × ℝ => Work.Coercivity.Z4 α f p.1 p.2)
      Work.FTS.CoercivityFix.Coer1.Qd := by
    have hB : ContinuousOn (fun p : ℝ × ℝ => -(2 * p.1 * (1 - p.1) * Work.Spaces.Gam α p.2
        / (Work.Spaces.c α * (1 + p.1) ^ 3))) Work.FTS.CoercivityFix.Coer1.Qd :=
      ((((continuous_const.mul continuous_fst).continuousOn).mul
        (continuous_const.sub continuous_fst).continuousOn).mul hGam).div
        ((continuous_const.mul ((continuous_const.add continuous_fst).pow 3)).continuousOn)
        hden3 |>.neg
    refine (hB.mul hL12f).congr (fun p hp => ?_)
    simp only [Work.Coercivity.Z4, Pi.mul_apply]
  have hZ7 : ContinuousOn (fun p : ℝ × ℝ => Work.Coercivity.Z7 α f p.1 p.2)
      Work.FTS.CoercivityFix.Coer1.Qd := by
    have hC : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.Gam α p.2 / Work.Spaces.c α)
        * (2 * p.1 ^ 2 * (2 - p.1) / (1 + p.1) ^ 4)) Work.FTS.CoercivityFix.Coer1.Qd :=
      (hGam.div_const (Work.Spaces.c α)).mul
        ((((continuous_const.mul (continuous_fst.pow 2)).continuousOn).mul
          (continuous_const.sub continuous_fst).continuousOn).div
          (((continuous_const.add continuous_fst).pow 4).continuousOn) hden4)
    have h := hC.mul (continuousOn_const (c := Work.Coercivity.C0 f))
    refine h.congr (fun p hp => ?_)
    simp only [Work.Coercivity.Z7, Pi.mul_apply]
    ring
  exact (hZ3.add hZ4).add hZ7

/-- **Pointwise bound for the nonlocal deflection `Z₃ + Z₄ + Z₇`.**  With `D = L₁₂dens(f)`,
`L = L₁₂(f)` and `C = L₁₂(Transport f)(0)`, the three summands factor as
`Z₃ = (Γ/c)(2z/(1+z)²)(zD)`, `Z₄ = (Γ/c)(-(2z(1-z)/(1+z)³))L` and
`Z₇ = (Γ/c)C·(2z²(2-z)/(1+z)⁴)`, so that `(Z₃+Z₄+Z₇)²w²sin^{-η}` is controlled by
`3(a²+b²+c²)` with `a = 2D`, `b = -2(1-z)L/(z(1+z))`, `c = 2(2-z)C/(1+z)²`, and
`|b| ≤ 2|L|/z`, `|c| ≤ 4|C|/(1+z)`; with `(Γ/c)² ≤ 100` this gives the stated constant. -/
theorem Zrest_sq_pt (α : ℝ) (hα : 0 < α) (hα1' : α ≤ 1) {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Coercivity.Z3 α f z θ + Work.Coercivity.Z4 α f z θ + Work.Coercivity.Z7 α f z θ) ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ
      ≤ 300 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ
          * (4 * (Work.FM.L12dens Work.Spaces.K f z) ^ 2
            + 4 * (Work.Coercivity.L12f f z / z) ^ 2
            + 16 * (Work.Coercivity.C0 f) ^ 2 / (1 + z) ^ 2) := by
  have hc : Work.Spaces.c α ≠ 0 := Work.Coercivity.c_ne_zero hα hα1'
  have hz0 : z ≠ 0 := ne_of_gt hz
  have h1z : (1 : ℝ) + z ≠ 0 := by positivity
  have hG : (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2 ≤ 100 := by
    have h1 : |Work.Spaces.Gam α θ / Work.Spaces.c α| ≤ 10 :=
      Work.Coercivity.Gam_div_c_bound hα hα1' hθ
    have h2 := abs_le.mp h1
    nlinarith [abs_nonneg (Work.Spaces.Gam α θ / Work.Spaces.c α), h2.1, h2.2]
  have hsin_nn : 0 ≤ Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ := by
    rw [Work.FTS.CoercivityFix.Coer1.sig]
    exact Real.rpow_nonneg (Work.FTS.CoercivityFix.Coer1.sin_nonneg_of_mem_Iθ hθ) _
  have hKavg : Work.Coercivity.Kavg f z = z * Work.FM.L12dens Work.Spaces.K f z := by
    rw [Work.FM.L12dens_eq (K := Work.Spaces.K) (f := f) (s := z) hz0]
    simp only [Work.Coercivity.Kavg, Work.Spaces.Iθ]
    field_simp
  have hZ3 : Work.Coercivity.Z3 α f z θ
      = (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z / (1 + z) ^ 2)
          * Work.Coercivity.Kavg f z := by
    simp only [Work.Coercivity.Z3]
    field_simp
  have hZ4 : Work.Coercivity.Z4 α f z θ
      = (Work.Spaces.Gam α θ / Work.Spaces.c α) * (-(2 * z * (1 - z) / (1 + z) ^ 3))
          * Work.Coercivity.L12f f z := by
    simp only [Work.Coercivity.Z4]
    field_simp
  have hZ7 : Work.Coercivity.Z7 α f z θ
      = (Work.Spaces.Gam α θ / Work.Spaces.c α) * Work.Coercivity.C0 f
          * (2 * z ^ 2 * (2 - z) / (1 + z) ^ 4) := by
    simp only [Work.Coercivity.Z7]
  rw [hZ3, hZ4, hZ7, hKavg]
  simp only [Work.FTS.CoercivityFix.Coer1.Rho]
  have hcs : ∀ a b c : ℝ, (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    intro a b c
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
  have hstep1 : ((2 * z / (1 + z) ^ 2) * (z * Work.FM.L12dens Work.Spaces.K f z)
        + (-(2 * z * (1 - z) / (1 + z) ^ 3)) * Work.Coercivity.L12f f z
        + Work.Coercivity.C0 f * (2 * z ^ 2 * (2 - z) / (1 + z) ^ 4)) ^ 2
      ≤ 3 * (((2 * z / (1 + z) ^ 2) * (z * Work.FM.L12dens Work.Spaces.K f z)) ^ 2
        + ((-(2 * z * (1 - z) / (1 + z) ^ 3)) * Work.Coercivity.L12f f z) ^ 2
        + (Work.Coercivity.C0 f * (2 * z ^ 2 * (2 - z) / (1 + z) ^ 4)) ^ 2) :=
    hcs _ _ _
  have hstep2 : (Work.Spaces.w z) ^ 2
        * ((2 * z / (1 + z) ^ 2) * (z * Work.FM.L12dens Work.Spaces.K f z)) ^ 2
      = 4 * (Work.FM.L12dens Work.Spaces.K f z) ^ 2 := by
    rw [Work.Spaces.w]
    field_simp
    ring
  have hstep3 : (Work.Spaces.w z) ^ 2
        * ((-(2 * z * (1 - z) / (1 + z) ^ 3)) * Work.Coercivity.L12f f z) ^ 2
      ≤ 4 * (Work.Coercivity.L12f f z / z) ^ 2 := by
    have hL2 : 0 ≤ (Work.Coercivity.L12f f z) ^ 2 := sq_nonneg _
    have h1 : (1 - z) ^ 2 ≤ (1 + z) ^ 2 := by
      nlinarith [sq_nonneg ((1 : ℝ) + z - (1 - z)), hz.le, sq_nonneg (1 + z), sq_nonneg (1 - z)]
    have hnum : 4 * ((1 - z) * Work.Coercivity.L12f f z) ^ 2
        ≤ 4 * ((Work.Coercivity.L12f f z) ^ 2 * (1 + z) ^ 2) := by
      have h := mul_le_mul_of_nonneg_right h1 hL2
      nlinarith [h]
    have heq1 : (Work.Spaces.w z) ^ 2
          * ((-(2 * z * (1 - z) / (1 + z) ^ 3)) * Work.Coercivity.L12f f z) ^ 2
        = 4 * ((1 - z) * Work.Coercivity.L12f f z) ^ 2 / (z ^ 2 * (1 + z) ^ 2) := by
      rw [Work.Spaces.w]
      field_simp
      ring
    have heq2 : 4 * (Work.Coercivity.L12f f z / z) ^ 2
        = 4 * ((Work.Coercivity.L12f f z) ^ 2 * (1 + z) ^ 2) / (z ^ 2 * (1 + z) ^ 2) := by
      field_simp
    rw [heq1, heq2]
    exact div_le_div_of_nonneg_right hnum (by positivity)
  have hstep4 : (Work.Spaces.w z) ^ 2
        * (Work.Coercivity.C0 f * (2 * z ^ 2 * (2 - z) / (1 + z) ^ 4)) ^ 2
      ≤ 16 * (Work.Coercivity.C0 f) ^ 2 / (1 + z) ^ 2 := by
    have hC2 : 0 ≤ (Work.Coercivity.C0 f) ^ 2 := sq_nonneg _
    have h1 : (2 - z) ^ 2 ≤ 4 * (1 + z) ^ 2 := by
      nlinarith [hz.le, sq_nonneg (1 + z), sq_nonneg (2 - z), sq_nonneg z]
    have hnum : 4 * ((2 - z) * Work.Coercivity.C0 f) ^ 2
        ≤ 4 * (4 * (Work.Coercivity.C0 f) ^ 2 * (1 + z) ^ 2) := by
      have h := mul_le_mul_of_nonneg_right h1 hC2
      nlinarith [h]
    have heq1 : (Work.Spaces.w z) ^ 2
          * (Work.Coercivity.C0 f * (2 * z ^ 2 * (2 - z) / (1 + z) ^ 4)) ^ 2
        = 4 * ((2 - z) * Work.Coercivity.C0 f) ^ 2 / (1 + z) ^ 4 := by
      rw [Work.Spaces.w]
      field_simp
      ring
    have heq2 : 16 * (Work.Coercivity.C0 f) ^ 2 / (1 + z) ^ 2
        = 4 * (4 * (Work.Coercivity.C0 f) ^ 2 * (1 + z) ^ 2) / (1 + z) ^ 4 := by
      field_simp
      ring
    rw [heq1, heq2]
    exact div_le_div_of_nonneg_right hnum (by positivity)
  have hmid : 3 * ((Work.Spaces.w z) ^ 2
        * ((2 * z / (1 + z) ^ 2) * (z * Work.FM.L12dens Work.Spaces.K f z)) ^ 2
      + (Work.Spaces.w z) ^ 2
        * ((-(2 * z * (1 - z) / (1 + z) ^ 3)) * Work.Coercivity.L12f f z) ^ 2
      + (Work.Spaces.w z) ^ 2
        * (Work.Coercivity.C0 f * (2 * z ^ 2 * (2 - z) / (1 + z) ^ 4)) ^ 2)
      ≤ 3 * (4 * (Work.FM.L12dens Work.Spaces.K f z) ^ 2
        + 4 * (Work.Coercivity.L12f f z / z) ^ 2
        + 16 * (Work.Coercivity.C0 f) ^ 2 / (1 + z) ^ 2) := by
    linarith [hstep2, hstep3, hstep4]
  have hWnn : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  calc ((Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z / (1 + z) ^ 2)
          * (z * Work.FM.L12dens Work.Spaces.K f z)
        + (Work.Spaces.Gam α θ / Work.Spaces.c α) * (-(2 * z * (1 - z) / (1 + z) ^ 3))
          * Work.Coercivity.L12f f z
        + (Work.Spaces.Gam α θ / Work.Spaces.c α) * Work.Coercivity.C0 f
          * (2 * z ^ 2 * (2 - z) / (1 + z) ^ 4)) ^ 2
        * ((Work.Spaces.w z) ^ 2 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ)
      = (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * ((2 * z / (1 + z) ^ 2) * (z * Work.FM.L12dens Work.Spaces.K f z)
          + (-(2 * z * (1 - z) / (1 + z) ^ 3)) * Work.Coercivity.L12f f z
          + Work.Coercivity.C0 f * (2 * z ^ 2 * (2 - z) / (1 + z) ^ 4)) ^ 2
        * ((Work.Spaces.w z) ^ 2 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ) := by
        ring
    _ ≤ (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * (3 * (((2 * z / (1 + z) ^ 2) * (z * Work.FM.L12dens Work.Spaces.K f z)) ^ 2
          + ((-(2 * z * (1 - z) / (1 + z) ^ 3)) * Work.Coercivity.L12f f z) ^ 2
          + (Work.Coercivity.C0 f * (2 * z ^ 2 * (2 - z) / (1 + z) ^ 4)) ^ 2))
        * ((Work.Spaces.w z) ^ 2 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep1 (sq_nonneg _)) ?_
        exact mul_nonneg hWnn hsin_nn
    _ = (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ
        * (3 * ((Work.Spaces.w z) ^ 2
            * ((2 * z / (1 + z) ^ 2) * (z * Work.FM.L12dens Work.Spaces.K f z)) ^ 2
          + (Work.Spaces.w z) ^ 2
            * ((-(2 * z * (1 - z) / (1 + z) ^ 3)) * Work.Coercivity.L12f f z) ^ 2
          + (Work.Spaces.w z) ^ 2
            * (Work.Coercivity.C0 f * (2 * z ^ 2 * (2 - z) / (1 + z) ^ 4)) ^ 2)) := by
        ring
    _ ≤ (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ
        * (3 * (4 * (Work.FM.L12dens Work.Spaces.K f z) ^ 2
          + 4 * (Work.Coercivity.L12f f z / z) ^ 2
          + 16 * (Work.Coercivity.C0 f) ^ 2 / (1 + z) ^ 2)) := by
        refine mul_le_mul_of_nonneg_left hmid ?_
        exact mul_nonneg (sq_nonneg _) hsin_nn
    _ ≤ 100 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ
        * (3 * (4 * (Work.FM.L12dens Work.Spaces.K f z) ^ 2
          + 4 * (Work.Coercivity.L12f f z / z) ^ 2
          + 16 * (Work.Coercivity.C0 f) ^ 2 / (1 + z) ^ 2)) := by
        have h1 : (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
              * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ
            ≤ 100 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ :=
          mul_le_mul_of_nonneg_right hG hsin_nn
        have h2 : 0 ≤ 3 * (4 * (Work.FM.L12dens Work.Spaces.K f z) ^ 2
            + 4 * (Work.Coercivity.L12f f z / z) ^ 2
            + 16 * (Work.Coercivity.C0 f) ^ 2 / (1 + z) ^ 2) := by
          have h1z' : (0 : ℝ) < 1 + z := by linarith
          positivity
        exact mul_le_mul_of_nonneg_right h1 h2
    _ = 300 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ
        * (4 * (Work.FM.L12dens Work.Spaces.K f z) ^ 2
          + 4 * (Work.Coercivity.L12f f z / z) ^ 2
          + 16 * (Work.Coercivity.C0 f) ^ 2 / (1 + z) ^ 2) := by
        ring




end Work.FTS.CoercivityFix.Coer1T
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1T.slotEta_LGammaT =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Coer1T

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000


end

end Work.FTS.CoercivityFix.Coer1T
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1T.slotW_LGammaT =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1T

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Integrability of the `L₁₂`-pairings in the interior class

The analytic chapter (`Work.Coercivity`) takes the joint integrability of the pairings of
`L₁₂(f)` against `f` as *hypotheses* (the fields `intK`, `intG` of `CoerciveData`).  Here we
prove them from the interior class `RegQ α 2 f` together with `HardyHyp f`, by the
two-step Cauchy–Schwarz that is the paper's own argument: write

  `w(z)/z · L₁₂(f)(z) · (c(θ) f(z,θ)) = (L₁₂(f)(z)/z · c(θ)) · (f(z,θ) w(z))`,

a product of two `L²`-functions of the product variable — `L₁₂(f)/z` is `L²` on `Iz` by
`HardyHyp.intA`, `c` is `L²` on `Iθ` by hypothesis, and `f w` is `L²` by `hfw`. -/

/-- The product of the two restricted measures is the restriction to the quadrant. -/
theorem prod_restrict_eq :
    (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)
      = volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  rw [Measure.prod_restrict, Measure.volume_eq_prod]

/-- **The general integrability lemma of the `L₁₂`-pairings.**  For `f` satisfying the Hardy
hypotheses, with `(f w)²` jointly integrable and `f` a.e. strongly measurable, and for any
`c` with `c² ∈ L¹(Iθ)`, the product `(w/z) L₁₂(f) (c·f)` is jointly integrable on the
quadrant. -/
theorem intMul_L12_Q {f : ℝ → ℝ → ℝ} (hHH : Work.Coercivity.HardyHyp f)
    (hfw : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (f z θ * Work.Spaces.w z) ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hfaesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
    (c : ℝ → ℝ) (hc : MeasureTheory.Integrable (fun θ => (c θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ))
    (hcm : MeasureTheory.AEStronglyMeasurable c (volume.restrict Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.w z / z * Work.Coercivity.L12f f z
        * (c θ * f z θ))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  rw [MeasureTheory.IntegrableOn, ← prod_restrict_eq]
  -- ## `(L₁₂(f)/z)²` is integrable on `Iz`
  have hA : MeasureTheory.Integrable
      (fun z : ℝ => (Work.Coercivity.L12f f z / z) ^ 2) (volume.restrict Work.Spaces.Iz) := by
    have h0 := hHH.intA 1 (by norm_num : (1 : ℕ) ≤ 2)
    rw [Work.FTS.CoercivityFix.Coer1.iz_ae_restrict]
    refine h0.congr (Filter.Eventually.of_forall fun z => ?_)
    dsimp only
    rw [div_pow, Nat.cast_one, mul_one, Real.rpow_two]
  have hC : MeasureTheory.Integrable (fun θ : ℝ => (c θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ) := hc
  -- ## a.e. strong measurability of `L₁₂(f)/z`
  have hL12aesm : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => Work.Coercivity.L12f f z / z) (volume.restrict Work.Spaces.Iz) := by
    rw [Work.FTS.CoercivityFix.Coer1.iz_ae_restrict]
    exact ((Work.Coercivity.L12f_continuousOn f hHH).div continuousOn_id
      (fun z hz => ne_of_gt hz)).aestronglyMeasurable measurableSet_Ioi
  -- ## the first `L²`-factor
  have h1 : MeasureTheory.MemLp
      (fun p : ℝ × ℝ => Work.Coercivity.L12f f p.1 / p.1 * c p.2) 2
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    refine (MeasureTheory.memLp_two_iff_integrable_sq ?_).2 ?_
    · exact (hL12aesm.comp_fst).mul (hcm.comp_snd)
    · refine (Integrable.mul_prod hA hC).congr (Filter.Eventually.of_forall fun p => ?_)
      rcases p with ⟨z, θ⟩
      ring
  -- ## the second `L²`-factor: `f w`
  have hwaesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ Work.Coercivity.continuousOn_w_quad
  have hfwP : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (f p.1 p.2 * Work.Spaces.w p.1) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [prod_restrict_eq]
    exact hfw.congr (Filter.Eventually.of_forall fun p => by
      rcases p with ⟨z, θ⟩
      rfl)
  have h2 : MeasureTheory.MemLp (fun p : ℝ × ℝ => f p.1 p.2 * Work.Spaces.w p.1) 2
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq (hfaesm.mul hwaesm)).2 hfwP
  -- ## Hölder
  refine (h1.integrable_mul h2).congr (Filter.Eventually.of_forall fun p => ?_)
  rcases p with ⟨z, θ⟩
  simp only [Pi.mul_apply, Function.uncurry_apply_pair]
  ring

/-! ## The concrete integrability certificates -/







/-! ## The interior-class port of `L2Coercivity` -/


/-! ## The sharp projector bound in the interior class -/









end Work.FTS.CoercivityFix.Coer1T
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.BlocksCont_mul_factor =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open Set

namespace Work.FTS.CoercivityFix.Transfer

theorem BlocksCont_mul_factor (B R : ℝ → ℝ)
    (hB : ContDiffOn ℝ 3 B (Set.Ioo 0 (π / 2)))
    (hR : ContDiffOn ℝ 3 R (Set.Ioi 0)) :
    Work.FTS.CoercivityFix.Assembly.BlocksCont 3 (fun z θ : ℝ => B θ * R z) := by
  intro a b hab
  have hU : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) := isOpen_Ioi.prod isOpen_Ioo
  -- the separated product is `C^3` on the open quadrant
  have hF : ContDiffOn ℝ 3 (Function.uncurry (fun z θ : ℝ => B θ * R z))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have hfun : Function.uncurry (fun z θ : ℝ => B θ * R z)
        = (fun p : ℝ × ℝ => B p.2) * (fun p : ℝ × ℝ => R p.1) := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [hfun]
    refine ContDiffOn.mul ?_ ?_
    · exact hB.comp contDiffOn_snd (fun p hp => hp.2)
    · exact hR.comp contDiffOn_fst (fun p hp => hp.1)
  have ha : a ≤ 3 := by omega
  have hDth := Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DthIter_fin
    (G := fun z θ : ℝ => B θ * R z) hU hF a ha
  have hb : b ≤ 3 - a := by omega
  have hDz := Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DzIter_fin
    (G := Work.Spaces.DthIter a (fun z θ : ℝ => B θ * R z)) hU hDth b hb
  exact hDz.continuousOn

end Work.FTS.CoercivityFix.Transfer
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.ZmollTTB2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ

open Work.FTS.EllSol.PkgK5.K5c

/-- **Integrability of the dominating functional.** -/
theorem rhs_integrable (G : ℝ → ℝ → ℝ) (hsl : SliceData G)
    (hsqrt : LocallyIntegrable (fun t : ℝ => Real.sqrt (E2s G (Real.exp t))) volume)
    {δ ε : ℝ} (hδ0 : 0 < δ) (hε0 : 0 < ε) {z θ : ℝ} (hz : 0 < z) :
    Integrable (fun t : ℝ => sKer δ (Real.log z - t) *
      ∫ s in Iθ, KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|) volume := by
  have hKδ : ∀ x : ℝ, |sKer δ x| ≤ (δ * sMass)⁻¹ := fun x => by
    rw [abs_of_nonneg (sKer_nonneg hδ0 x)]
    exact Work.FTS.EllSol.K5cAux.sKer_le_inv hδ0 x
  have hKδ0 : (0 : ℝ) ≤ (δ * sMass)⁻¹ := by have := sMass_pos; positivity
  have hC0 : (0 : ℝ) ≤ 3 * (ε * sMass)⁻¹ := by have := sMass_pos; positivity
  have hpt : ∀ t : ℝ,
      ‖∫ s in Iθ, KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|‖
        ≤ (3 * (ε * sMass)⁻¹) * (Real.sqrt (Real.pi / 2)
            * Real.sqrt (E2s G (Real.exp t))) := by
    intro t
    have h1 : ‖∫ s in Iθ, KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|‖
        ≤ ∫ s in Iθ, ‖KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|‖ :=
      MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict Iθ)
        (fun s : ℝ => KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|)
    have h2 : (∫ s in Iθ, ‖KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|‖)
        ≤ ∫ s in Iθ, (3 * (ε * sMass)⁻¹)
            * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s| := by
      refine integral_mono_of_nonneg (μ := volume.restrict Iθ)
        (Filter.Eventually.of_forall fun s => abs_nonneg _)
        ((hsl.deriv2_int (Real.exp t) (Real.exp_pos t)).abs.const_mul _) ?_
      exact Filter.Eventually.of_forall fun s => by
        show ‖KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|‖
          ≤ (3 * (ε * sMass)⁻¹) * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|
        rw [Real.norm_eq_abs, abs_mul, abs_abs,
          abs_of_nonneg (Work.FTS.EllSol.EllPkgAux.KJ_nonneg hε0 θ s)]
        exact mul_le_mul_of_nonneg_right
          (Work.FTS.EllSol.EllPkgAux.KJ_le hε0 θ s) (abs_nonneg _)
    have h3 : (∫ s in Iθ, (3 * (ε * sMass)⁻¹)
          * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|)
        = (3 * (ε * sMass)⁻¹)
          * (∫ s in Iθ, |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|) :=
      MeasureTheory.integral_const_mul _ _
    have hE2 : (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 2),
          Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) θ ^ 2
          * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))) = E2s G (Real.exp t) := by
      simp only [E2s, Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta, Work.Spaces.eta]
    have h4 : (∫ s in Iθ, |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|)
        ≤ Real.sqrt (Real.pi / 2) * Real.sqrt (E2s G (Real.exp t)) := by
      have h4a := Work.FTS.EllSol.EllPkgAux.MollAux.integralAbsLeSqrtWeighted
        (h := fun s : ℝ => Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ?_
      · rw [hE2] at h4a
        exact h4a
      · simpa only [Work.FTS.EllipticEst.thEta, Work.Spaces.eta, Work.Spaces.Iθ,
          Work.Spaces.pth] using
          hsl.deriv2_weighted (Real.exp t) (Real.exp_pos t)
    calc ‖∫ s in Iθ, KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|‖
        ≤ ∫ s in Iθ, ‖KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|‖ := h1
      _ ≤ ∫ s in Iθ, (3 * (ε * sMass)⁻¹)
            * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s| := h2
      _ = (3 * (ε * sMass)⁻¹)
            * (∫ s in Iθ, |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|) := h3
      _ ≤ (3 * (ε * sMass)⁻¹) * (Real.sqrt (Real.pi / 2)
            * Real.sqrt (E2s G (Real.exp t))) := mul_le_mul_of_nonneg_left h4 hC0
  set Cst : ℝ := (δ * sMass)⁻¹ * ((3 * (ε * sMass)⁻¹) * Real.sqrt (Real.pi / 2)) with hCst
  set g : ℝ → ℝ := (Set.Icc (Real.log z - δ) (Real.log z + δ)).indicator
    (fun t : ℝ => Cst * Real.sqrt (E2s G (Real.exp t))) with hg
  have hgint : Integrable g volume := by
    refine IntegrableOn.integrable_indicator ?_ measurableSet_Icc
    exact (hsqrt.integrableOn_isCompact isCompact_Icc).const_mul Cst
  have hmem : AEStronglyMeasurable (fun t : ℝ => sKer δ (Real.log z - t) *
      ∫ s in Iθ, KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|) volume := by
    have hker : AEStronglyMeasurable (fun t : ℝ => sKer δ (Real.log z - t)) volume :=
      (((Work.FTS.EllSol.EllPkgAux.contDiff_sKer δ (n := 0)).continuous.comp
        (continuous_const.sub continuous_id))).aestronglyMeasurable
    refine hker.mul ?_
    have hX : ContinuousOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth G)))
        Work.FTS.EllipticEst.Q0 := (hsl.sm.pth.pth).continuousOn
    have hKcont : ContinuousOn (fun p : ℝ × ℝ => KJ ε θ p.2)
        (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      ((continuous_KJ ε).comp (continuous_const.prodMk continuous_snd)).continuousOn
    have hY : ContinuousOn (fun p : ℝ × ℝ =>
        KJ ε θ p.2 * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp p.1) p.2|)
        (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      refine hKcont.mul ?_
      refine ContinuousOn.abs ?_
      have hΦ : Continuous (fun p : ℝ × ℝ => (Real.exp p.1, p.2)) :=
        (Real.continuous_exp.comp continuous_fst).prodMk continuous_snd
      exact hX.comp hΦ.continuousOn (fun p hp => ⟨Real.exp_pos p.1, hp.2.1, hp.2.2⟩)
    exact aesm_param_Iθ _ hY
  have hle : ∀ᵐ t ∂volume,
      ‖sKer δ (Real.log z - t) *
        ∫ s in Iθ, KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|‖ ≤ g t := by
    refine Filter.Eventually.of_forall fun t => ?_
    by_cases ht : t ∈ Set.Icc (Real.log z - δ) (Real.log z + δ)
    · rw [hg, Set.indicator_of_mem ht, Real.norm_eq_abs, abs_mul]
      refine le_trans (mul_le_mul (hKδ _) (hpt t) (abs_nonneg _) hKδ0) (le_of_eq ?_)
      rw [hCst]; ring
    · have hzero : sKer δ (Real.log z - t) = 0 := by
        refine sKer_eq_zero_of_le_abs hδ0 ?_
        rw [Set.mem_Icc, not_and_or] at ht
        rcases ht with h | h
        · rw [not_le] at h
          rw [abs_of_pos (by linarith)]
          linarith
        · rw [not_le] at h
          rw [abs_of_neg (by linarith)]
          linarith
      rw [hg, Set.indicator_of_notMem ht, hzero, zero_mul, norm_zero]
  exact Integrable.mono' hgint hmem hle

/-! ## Integration by parts -/

theorem ibp_km {G : ℝ → ℝ → ℝ} (hsl : SliceData G) {ε w θ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hw : 0 < w) (hθ : θ ∈ Iθ) :
    (∫ s in Iθ, kmθθ ε θ s * G w s)
      = ∫ s in Iθ, km ε θ s * deriv (deriv (fun s' : ℝ => G w s')) s := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hQint : IntegrableOn (fun s : ℝ => G w s) Iθ :=
    (hsl.cont w hw).integrableOn_compact isCompact_Icc
  have hQ''int : IntegrableOn (fun s : ℝ => deriv (deriv (fun s' : ℝ => G w s')) s) Iθ :=
    hsl.deriv2_int w hw
  obtain ⟨Mq, hMq0, hMq⟩ := hsl.deriv_bdd w hw
  have hQ'aesm : AEStronglyMeasurable (fun s : ℝ => deriv (fun s' : ℝ => G w s') s)
      (volume.restrict Iθ) := aesm_slice_deriv G hsl.sm hw
  obtain ⟨Mk', hMk'0, hMk'⟩ := kms_bdd hε0
  have hpart1 : IntegrableOn (fun s : ℝ => kmθθ ε θ s * G w s) Iθ := by
    have h := hQint.mul_continuousOn (continuous_kmθθ ε θ).continuousOn isCompact_Icc
    exact h.congr_fun (fun s _ => mul_comm _ _) measurableSet_Icc
  have hpart2 : IntegrableOn (fun s : ℝ => kms ε θ s * deriv (fun s' : ℝ => G w s') s) Iθ := by
    refine Integrable.mono' (MeasureTheory.integrableOn_const (s := Iθ) (C := Mk' * Mq) ?_) ?_ ?_
    · rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    · have hm1 : AEStronglyMeasurable (fun s : ℝ => kms ε θ s) (volume.restrict Iθ) :=
        ((continuous_kms ε θ).aestronglyMeasurable).restrict
      exact AEStronglyMeasurable.mul hm1 hQ'aesm
    · rw [Work.FTS.EllSol.EllPkgAux.restrict_Iθ_eq_restrict_Ioo]
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun s hs => by
        show ‖kms ε θ s * deriv (fun s' : ℝ => G w s') s‖ ≤ Mk' * Mq
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hMk' θ s) (hMq s hs) (abs_nonneg _) hMk'0)
  have hpart4 : IntegrableOn (fun s : ℝ => km ε θ s * deriv (deriv (fun s' : ℝ => G w s')) s)
      Iθ := by
    have h := hQ''int.mul_continuousOn (continuous_km ε θ).continuousOn isCompact_Icc
    exact h.congr_fun (fun s _ => mul_comm _ _) measurableSet_Icc
  have hI1 : IntervalIntegrable (fun s : ℝ => kmθθ ε θ s * G w s) volume 0 (Real.pi / 2) :=
    intervalIntegrable_iff.mpr (integrableOn_uIoc_of_Icc (le_of_lt hpi) hpart1)
  have hI2 : IntervalIntegrable
      (fun s : ℝ => kms ε θ s * deriv (fun s' : ℝ => G w s') s) volume 0 (Real.pi / 2) :=
    intervalIntegrable_iff.mpr (integrableOn_uIoc_of_Icc (le_of_lt hpi) hpart2)
  have hI4 : IntervalIntegrable
      (fun s : ℝ => km ε θ s * deriv (deriv (fun s' : ℝ => G w s')) s) volume 0 (Real.pi / 2) :=
    intervalIntegrable_iff.mpr (integrableOn_uIoc_of_Icc (le_of_lt hpi) hpart4)
  -- Step 1: the FTC for `k' * Q`
  have hF1der : ∀ s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun s' : ℝ => kms ε θ s' * G w s')
        (kmθθ ε θ s * G w s + kms ε θ s * deriv (fun s' : ℝ => G w s') s) s :=
    fun s hs => (hasDerivAt_kms_s ε θ s).mul (slice_hasDerivAt G hsl.sm hw hs)
  have hF1int : IntervalIntegrable (fun s : ℝ =>
      kmθθ ε θ s * G w s + kms ε θ s * deriv (fun s' : ℝ => G w s') s)
      volume 0 (Real.pi / 2) := hI1.add hI2
  have ht1a : Tendsto (fun s : ℝ => kms ε θ s * G w s)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => kms ε θ s) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (𝓝 (kms ε θ 0)) :=
      (continuous_kms ε θ).tendsto 0 |>.mono_left nhdsWithin_le_nhds
    have h2 := h1.mul (hsl.tr0 w hw)
    simpa using h2
  have ht1b : Tendsto (fun s : ℝ => kms ε θ s * G w s)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => kms ε θ s)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (𝓝 (kms ε θ (Real.pi / 2))) :=
      (continuous_kms ε θ).tendsto _ |>.mono_left nhdsWithin_le_nhds
    have h2 := h1.mul (hsl.trpi w hw)
    simpa using h2
  have hFTC1 : (∫ s in (0 : ℝ)..(Real.pi / 2),
      (kmθθ ε θ s * G w s + kms ε θ s * deriv (fun s' : ℝ => G w s') s)) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hpi hF1der hF1int ht1a ht1b
    simpa using h
  -- Step 2: the FTC for `k * Q'`
  have hF2der : ∀ s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun s' : ℝ => km ε θ s' * deriv (fun s'' : ℝ => G w s'') s')
        (kms ε θ s * deriv (fun s'' : ℝ => G w s'') s
          + km ε θ s * deriv (deriv (fun s'' : ℝ => G w s'')) s) s :=
    fun s hs => (hasDerivAt_km_s ε θ s).mul (slice_hasDerivAt2 G hsl.sm hw hs)
  have hF2int : IntervalIntegrable (fun s : ℝ =>
      kms ε θ s * deriv (fun s'' : ℝ => G w s'') s
        + km ε θ s * deriv (deriv (fun s'' : ℝ => G w s'')) s) volume 0 (Real.pi / 2) :=
    hI2.add hI4
  have hkm0 : Tendsto (fun s : ℝ => km ε θ s) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => km ε θ s) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (𝓝 (km ε θ 0)) :=
      (continuous_km ε θ).tendsto 0 |>.mono_left nhdsWithin_le_nhds
    rw [km_zero_left' hε0 hε1 hθ] at h1
    exact h1
  have hkmpi : Tendsto (fun s : ℝ => km ε θ s)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => km ε θ s)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (𝓝 (km ε θ (Real.pi / 2))) :=
      (continuous_km ε θ).tendsto _ |>.mono_left nhdsWithin_le_nhds
    rw [km_zero_right hε0 hε1 hθ] at h1
    exact h1
  have ht2a : Tendsto (fun s : ℝ => km ε θ s * deriv (fun s'' : ℝ => G w s'') s)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
    refine tendsto_mul_zero (c := Mq) hkm0 ?_
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
        (show (0 : ℝ) < Real.pi / 2 by linarith [Real.pi_pos])] with s hs hys
    exact hMq s ⟨hys, hs.2⟩
  have ht2b : Tendsto (fun s : ℝ => km ε θ s * deriv (fun s'' : ℝ => G w s'') s)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (𝓝 0) := by
    refine tendsto_mul_zero (c := Mq) hkmpi ?_
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioo_mem_nhds (show (0 : ℝ) < Real.pi / 2 by linarith [Real.pi_pos])
        (show Real.pi / 2 < Real.pi by linarith [Real.pi_pos])] with s hs hys
    exact hMq s ⟨hs.1, hys⟩
  have hFTC2 : (∫ s in (0 : ℝ)..(Real.pi / 2),
      (kms ε θ s * deriv (fun s'' : ℝ => G w s'') s
        + km ε θ s * deriv (deriv (fun s'' : ℝ => G w s'')) s)) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hpi hF2der hF2int ht2a ht2b
    simpa using h
  -- combine
  have hAB : (∫ s in (0 : ℝ)..(Real.pi / 2), kmθθ ε θ s * G w s)
      + (∫ s in (0 : ℝ)..(Real.pi / 2), kms ε θ s * deriv (fun s' : ℝ => G w s') s) = 0 := by
    rw [← intervalIntegral.integral_add hI1 hI2]
    exact hFTC1
  have hBC : (∫ s in (0 : ℝ)..(Real.pi / 2), kms ε θ s * deriv (fun s' : ℝ => G w s') s)
      + (∫ s in (0 : ℝ)..(Real.pi / 2),
          km ε θ s * deriv (deriv (fun s' : ℝ => G w s')) s) = 0 := by
    rw [← intervalIntegral.integral_add hI2 hI4]
    exact hFTC2
  have hAC : (∫ s in (0 : ℝ)..(Real.pi / 2), kmθθ ε θ s * G w s)
      = ∫ s in (0 : ℝ)..(Real.pi / 2), km ε θ s * deriv (deriv (fun s' : ℝ => G w s')) s := by
    linarith
  rw [← intervalIntegral_Iθ_eq (fun s : ℝ => kmθθ ε θ s * G w s),
    ← intervalIntegral_Iθ_eq (fun s : ℝ => km ε θ s * deriv (deriv (fun s' : ℝ => G w s')) s)]
  exact hAC

end Work.FTS.EllSol.EllPkgAux.MollDom
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.window_E_le_F =====
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

/-- A constant `if` may be pulled out of a set integral. -/
private lemma integral_ite_const {c : Prop} [Decidable c] (u : ℝ → ℝ) :
    (∫ s in Work.Spaces.Iθ, (if c then u s else 0))
      = (if c then ∫ s in Work.Spaces.Iθ, u s else 0) := by
  by_cases h : c
  · rw [ite_eq_left h]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun s => ite_eq_left h))
  · rw [ite_eq_right h]
    have heq : (fun s : ℝ => (if c then u s else 0))
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] (fun _ => (0 : ℝ)) :=
      Filter.Eventually.of_forall (fun s => ite_eq_right h)
    rw [MeasureTheory.integral_congr_ae heq, MeasureTheory.integral_zero]

/-- The windowed weighted angular first derivative of `G` in the logarithmic variable. -/
private def Efun (G : ℝ → ℝ → ℝ) (δ z : ℝ) : ℝ → ℝ :=
  fun t => if |Real.log z - t| ≤ δ then
    (∫ s in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.thEta s * (Work.Spaces.pth G (Real.exp t) s) ^ 2) else 0

/-- The windowed (unweighted) angular second derivative of `G` in the logarithmic variable. -/
private def Rfun (G : ℝ → ℝ → ℝ) (δ z : ℝ) : ℝ → ℝ :=
  fun t => if |Real.log z - t| ≤ δ then
    (∫ s in Work.Spaces.Iθ,
      (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2) else 0

theorem window_E_le_F (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 0 < z →
      MeasureTheory.Integrable (fun t : ℝ => if |Real.log z - t| ≤ δ then
          (∫ s in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.thEta s * (Work.Spaces.pth G (Real.exp t) s) ^ 2) else 0) ∧
      (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
            (∫ s in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.thEta s * (Work.Spaces.pth G (Real.exp t) s) ^ 2) else 0))
        ≤ C * (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
            (∫ s in Work.Spaces.Iθ,
              (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2) else 0)) := by
  -- the uniform slicewise Poincaré constant
  obtain ⟨C₀, hC₀pos, hC₀⟩ := slice_pth_poincare_unif G hT
  refine ⟨C₀, hC₀pos, fun z hz => ?_⟩
  -- the right-hand side is integrable in `t`
  have hRint : MeasureTheory.Integrable (Rfun G δ z) :=
    window_ttIntS_plain_integrable G hT hF δ z hδ hz
  -- the left-hand side is a.e. strongly measurable in `t`
  have hLaesm : MeasureTheory.AEStronglyMeasurable (Efun G δ z) MeasureTheory.volume := by
    have hprod := thSlice_window_aesm_pth G hT δ z
    have hE : MeasureTheory.AEStronglyMeasurable
        (fun t : ℝ => ∫ s in Work.Spaces.Iθ,
          (if |Real.log z - t| ≤ δ then
            Work.FTS.EllipticEst.thEta s * (Work.Spaces.pth G (Real.exp t) s) ^ 2
            else 0)) MeasureTheory.volume := hprod.integral_prod_right'
    have hEq : (fun t : ℝ => ∫ s in Work.Spaces.Iθ,
          (if |Real.log z - t| ≤ δ then
            Work.FTS.EllipticEst.thEta s * (Work.Spaces.pth G (Real.exp t) s) ^ 2
            else 0)) = Efun G δ z := by
      funext t
      exact integral_ite_const
        (u := fun s : ℝ => Work.FTS.EllipticEst.thEta s * (Work.Spaces.pth G (Real.exp t) s) ^ 2)
    rwa [hEq] at hE
  -- the two pointwise unfoldings of the window
  have hEw : ∀ t : ℝ, |Real.log z - t| ≤ δ → Efun G δ z t = ∫ s in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.thEta s * (Work.Spaces.pth G (Real.exp t) s) ^ 2 := by
    intro t h; simp only [Efun]; exact ite_eq_left h
  have hRw : ∀ t : ℝ, |Real.log z - t| ≤ δ → Rfun G δ z t = ∫ s in Work.Spaces.Iθ,
      (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2 := by
    intro t h; simp only [Rfun]; exact ite_eq_left h
  have hEo : ∀ t : ℝ, ¬ (|Real.log z - t| ≤ δ) → Efun G δ z t = 0 := by
    intro t h; simp only [Efun]; exact ite_eq_right h
  have hRo : ∀ t : ℝ, ¬ (|Real.log z - t| ≤ δ) → Rfun G δ z t = 0 := by
    intro t h; simp only [Rfun]; exact ite_eq_right h
  -- nonnegativity of the left-hand side
  have hEnn : ∀ t : ℝ, 0 ≤ Efun G δ z t := by
    intro t
    by_cases h : |Real.log z - t| ≤ δ
    · rw [hEw t h]
      exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun s hs => mul_nonneg (Work.FTS.EllipticEst.thEta_nonneg hs) (sq_nonneg _))
    · simp only [hEo t h, le_refl]
  -- the pointwise (slicewise) Poincaré inequality
  have hle : ∀ t : ℝ, Efun G δ z t ≤ C₀ * Rfun G δ z t := by
    intro t
    by_cases h : |Real.log z - t| ≤ δ
    · rw [hEw t h, hRw t h]
      exact hC₀ (Real.exp t) (Real.exp_pos t)
    · simp only [hEo t h, hRo t h, mul_zero, le_refl]
  have hpt : ∀ t : ℝ, ‖Efun G δ z t‖ ≤ C₀ * Rfun G δ z t := by
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (hEnn t)]
    exact hle t
  -- integrability of the left-hand side
  have hLint : MeasureTheory.Integrable (Efun G δ z) :=
    MeasureTheory.Integrable.mono' (hRint.const_mul C₀) hLaesm
      (Filter.Eventually.of_forall hpt)
  refine ⟨hLint, ?_⟩
  have hmono : (∫ t, Efun G δ z t) ≤ ∫ t, C₀ * Rfun G δ z t :=
    MeasureTheory.integral_mono_ae hLint (hRint.const_mul C₀)
      (Filter.Eventually.of_forall hle)
  rw [MeasureTheory.integral_const_mul] at hmono
  exact hmono

end Work.FTS.EllSol.EllPkgAux.MollDom
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zSchur_pth_window_unif =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The window estimate for the logarithmic Schur transform of the angular derivative,
uniformly in the radius `z`.**

For a trace-class datum `G` (`TraceClass G`, `FourInts G`) and `0 < δ ≤ 1/2` there is a single
constant `C > 0` — independent of `z` — such that for every `z > 0` the weighted square of
`zSchur δ (fun w => ∂_θG(w,·)) z` against `σ_η = sin(2θ)^{-η}` is integrable on `Iθ` and is
bounded by `C` times the *windowed* angular energy

  `∫_t 1_{|log z - t| ≤ δ} ∫_{Iθ} σ_η(s) (∂_θG(e^t,s))²`.

The proof is the pointwise Cauchy–Schwarz bound `schur_sq_window_le_unif` (whose constant
`2δM² + 1` involves only a global bound `M` of the compactly supported kernel `sKerd δ`),
applied for a.e. angle `s`, followed by Fubini for the (integrable) joint integrand
`J(t,s) = 1_{|log z - t| ≤ δ} (∂_θG(e^t,s))² σ_η(s)`; the integrability of `J` uses the
slice majorant `thSliceMajorant G (e^t)` (`win_majorant_integrable`,
`pth_slice_sq_le_majorant`). -/
theorem zSchur_pth_window_unif (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn
        (fun s : ℝ => (Work.FTS.EllSol.EllPkgAux.MollDom.zSchur δ (fun w => Work.Spaces.pth G w s) z) ^ 2
          * Work.FTS.EllipticEst.thEta s) Work.Spaces.Iθ ∧
      (∫ s in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta s
          * (Work.FTS.EllSol.EllPkgAux.MollDom.zSchur δ (fun w => Work.Spaces.pth G w s) z) ^ 2)
        ≤ C * (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
            (∫ s in Work.Spaces.Iθ,
              Work.FTS.EllipticEst.thEta s * (Work.Spaces.pth G (Real.exp t) s) ^ 2) else 0)) := by
  -- ## the uniform Cauchy–Schwarz bound on the window (constant free of `z`)
  obtain ⟨A, hApos, hAbnd⟩ := schur_sq_window_le_unif δ hδ
  refine ⟨A, hApos, fun z hz => ?_⟩
  -- ## the pointwise angular majorant of the datum `G`
  have hbound_s : ∀ (t s : ℝ), s ∈ Work.Spaces.Iθ →
      (Work.Spaces.pth G (Real.exp t) s) ^ 2 * Work.FTS.EllipticEst.thEta s
        ≤ thSliceMajorant G (Real.exp t) * Work.FTS.EllipticEst.thEta s := by
    intro t s hs
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · rw [← h0, thEta_zero]
      simp
    · rcases eq_or_lt_of_le hs.2 with h2 | h2
      · rw [h2, thEta_pi_half]
        simp
      · exact mul_le_mul_of_nonneg_right
          (pth_slice_sq_le_majorant G hT (Real.exp t) (Real.exp_pos t) s ⟨h0, h2⟩)
          (Work.FTS.EllipticEst.thEta_nonneg hs)
  have hmaj : MeasureTheory.Integrable (fun t : ℝ =>
      if |Real.log z - t| ≤ δ then thSliceMajorant G (Real.exp t) else 0) MeasureTheory.volume :=
    win_majorant_integrable G hT hF δ z hδ hz
  -- ## the joint integrand on `ℝ × Iθ`
  set J : ℝ × ℝ → ℝ := fun p : ℝ × ℝ =>
    (if |Real.log z - p.1| ≤ δ then (Work.Spaces.pth G (Real.exp p.1) p.2) ^ 2 else 0)
      * Work.FTS.EllipticEst.thEta p.2 with hJ
  have hae_Iθ : ∀ᵐ p ∂((MeasureTheory.volume : Measure ℝ).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), p.2 ∈ Work.Spaces.Iθ := by
    have h : ∀ᵐ p ∂((MeasureTheory.volume : Measure ℝ).prod
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2)))),
        p ∈ Set.univ ×ˢ Set.Icc (0 : ℝ) (Real.pi / 2) := by
      refine (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
        (μ := (MeasureTheory.volume : Measure ℝ))
        (ν := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2)))
        (s := Set.univ ×ˢ Set.Icc (0 : ℝ) (Real.pi / 2))
        (MeasurableSet.univ.prod (measurableSet_Icc (a := (0 : ℝ)) (b := Real.pi / 2)))).mpr ?_
      filter_upwards with t
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact ⟨trivial, hθ⟩
    exact h.mono (fun p hp => hp.2)
  have hKint : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (if |Real.log z - p.1| ≤ δ then thSliceMajorant G (Real.exp p.1) else 0)
        * Work.FTS.EllipticEst.thEta p.2)
      ((MeasureTheory.volume : Measure ℝ).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    hmaj.mul_prod Work.FTS.EllipticEst.integrableOn_thEta.1
  have hJ_eq : (fun p : ℝ × ℝ => (if |Real.log z - p.1| ≤ δ then
        Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.pth G (Real.exp p.1) p.2) ^ 2 else 0))
      =ᵐ[((MeasureTheory.volume : Measure ℝ).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))] J := by
    rw [hJ]
    filter_upwards with p
    by_cases hp : |Real.log z - p.1| ≤ δ
    · rw [if_pos hp, if_pos hp, mul_comm]
    · rw [if_neg hp, if_neg hp, zero_mul]
  have hJ_aesm : MeasureTheory.AEStronglyMeasurable J
      ((MeasureTheory.volume : Measure ℝ).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (thSlice_window_aesm_pth G hT δ z).congr hJ_eq
  have hJint : MeasureTheory.Integrable J
      ((MeasureTheory.volume : Measure ℝ).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine hKint.mono' hJ_aesm ?_
    filter_upwards [hae_Iθ] with p hp
    show ‖(if |Real.log z - p.1| ≤ δ
        then (Work.Spaces.pth G (Real.exp p.1) p.2) ^ 2 else 0)
        * Work.FTS.EllipticEst.thEta p.2‖
      ≤ (if |Real.log z - p.1| ≤ δ then thSliceMajorant G (Real.exp p.1) else 0)
        * Work.FTS.EllipticEst.thEta p.2
    by_cases hw : |Real.log z - p.1| ≤ δ
    · rw [if_pos hw, if_pos hw,
        Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hp))]
      exact hbound_s p.1 p.2 hp
    · rw [if_neg hw, if_neg hw]
      simp
  -- ## Fubini on the product `ℝ × Iθ`
  have hprod1 : (∫ p, J p ∂((MeasureTheory.volume : Measure ℝ).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∫ t : ℝ, (∫ s : ℝ, J (t, s) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          ∂MeasureTheory.volume :=
    MeasureTheory.integral_prod J hJint
  have hprod2 : (∫ p, J p ∂((MeasureTheory.volume : Measure ℝ).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∫ s : ℝ, (∫ t : ℝ, J (t, s) ∂MeasureTheory.volume)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.integral_prod_symm J hJint
  have hslice_s : MeasureTheory.Integrable
      (fun s : ℝ => ∫ t : ℝ, J (t, s) ∂MeasureTheory.volume)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.Integrable.integral_prod_right hJint
  -- ## the `t`-slice identity: the right-hand side of the statement
  have hsliceJ : ∀ t : ℝ, (∫ s : ℝ, J (t, s) ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      = (if |Real.log z - t| ≤ δ then
          (∫ s in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta s
            * (Work.Spaces.pth G (Real.exp t) s) ^ 2) else 0) := by
    intro t
    by_cases hw : |Real.log z - t| ≤ δ
    · rw [if_pos hw]
      have heq : (fun s : ℝ => J (t, s)) = fun s : ℝ => Work.FTS.EllipticEst.thEta s
          * (Work.Spaces.pth G (Real.exp t) s) ^ 2 := by
        funext s
        show (if |Real.log z - t| ≤ δ then (Work.Spaces.pth G (Real.exp t) s) ^ 2 else 0)
            * Work.FTS.EllipticEst.thEta s
          = Work.FTS.EllipticEst.thEta s * (Work.Spaces.pth G (Real.exp t) s) ^ 2
        rw [if_pos hw, mul_comm]
      rw [heq]
    · rw [if_neg hw]
      have heq : (fun s : ℝ => J (t, s)) = fun _ : ℝ => (0 : ℝ) := by
        funext s
        show (if |Real.log z - t| ≤ δ then (Work.Spaces.pth G (Real.exp t) s) ^ 2 else 0)
            * Work.FTS.EllipticEst.thEta s = 0
        rw [if_neg hw, zero_mul]
      rw [heq, MeasureTheory.integral_zero]
  have hRHS : (∫ p, J p ∂((MeasureTheory.volume : Measure ℝ).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∫ t : ℝ, (if |Real.log z - t| ≤ δ then
          (∫ s in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta s
            * (Work.Spaces.pth G (Real.exp t) s) ^ 2) else 0) := by
    rw [hprod1]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsliceJ)
  -- ## the `s`-slice identity
  have hJsl : ∀ s : ℝ, (∫ t : ℝ, J (t, s) ∂MeasureTheory.volume)
      = Work.FTS.EllipticEst.thEta s * (∫ t : ℝ,
          if |Real.log z - t| ≤ δ then (Work.Spaces.pth G (Real.exp t) s) ^ 2 else 0) := by
    intro s
    have heq : (fun t : ℝ => J (t, s)) = fun t : ℝ =>
        (if |Real.log z - t| ≤ δ then (Work.Spaces.pth G (Real.exp t) s) ^ 2 else 0)
          * Work.FTS.EllipticEst.thEta s := by
      funext t
      rw [hJ]
    rw [heq, MeasureTheory.integral_mul_const]
    ring
  -- ## continuity of the angular-derivative slice along `t ↦ e^t`
  have hcont_slice : ∀ s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Continuous (fun t : ℝ => Work.Spaces.pth G (Real.exp t) s) := by
    intro s hs
    have hmap : Continuous (fun t : ℝ => (Real.exp t, s)) :=
      Real.continuous_exp.prodMk continuous_const
    exact (hT.1.pth).continuousOn.comp_continuous hmap (fun t => ⟨Real.exp_pos t, hs⟩)
  -- ## the uniform Cauchy–Schwarz bound for each interior angle
  have hcs : ∀ s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (zSchur δ (fun w => Work.Spaces.pth G w s) z) ^ 2
        ≤ A * (∫ t : ℝ, if |Real.log z - t| ≤ δ
            then (Work.Spaces.pth G (Real.exp t) s) ^ 2 else 0) := by
    intro s hs
    have h := hAbnd z hz (fun t : ℝ => Work.Spaces.pth G (Real.exp t) s) (hcont_slice s hs)
    simpa only [zSchur] using h
  -- ## the pointwise bound on `Iθ`
  have hfs_le : ∀ s ∈ Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta s
      * (zSchur δ (fun w => Work.Spaces.pth G w s) z) ^ 2
        ≤ A * (∫ t : ℝ, J (t, s) ∂MeasureTheory.volume) := by
    intro s hs
    rw [hJsl s]
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · rw [← h0, thEta_zero]
      simp
    · rcases eq_or_lt_of_le hs.2 with h2 | h2
      · rw [h2, thEta_pi_half]
        simp
      · calc Work.FTS.EllipticEst.thEta s * (zSchur δ (fun w => Work.Spaces.pth G w s) z) ^ 2
            ≤ Work.FTS.EllipticEst.thEta s * (A * (∫ t : ℝ, if |Real.log z - t| ≤ δ
                then (Work.Spaces.pth G (Real.exp t) s) ^ 2 else 0)) :=
              mul_le_mul_of_nonneg_left (hcs s ⟨h0, h2⟩) (Work.FTS.EllipticEst.thEta_nonneg hs)
          _ = A * (Work.FTS.EllipticEst.thEta s * (∫ t : ℝ, if |Real.log z - t| ≤ δ
                then (Work.Spaces.pth G (Real.exp t) s) ^ 2 else 0)) := by ring
  -- ## nonnegativity, integrability of the dominating function, monotonicity
  have hfs_nn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] fun s : ℝ =>
      Work.FTS.EllipticEst.thEta s * (zSchur δ (fun w => Work.Spaces.pth G w s) z) ^ 2 := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs
    exact mul_nonneg (Work.FTS.EllipticEst.thEta_nonneg hs) (sq_nonneg _)
  have hgs_int : MeasureTheory.Integrable
      (fun s : ℝ => A * (∫ t : ℝ, J (t, s) ∂MeasureTheory.volume))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hslice_s.const_mul _
  have hmono := MeasureTheory.integral_mono_of_nonneg hfs_nn hgs_int
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hfs_le)
  have hgs_eq : (∫ s : ℝ, A * (∫ t : ℝ, J (t, s) ∂MeasureTheory.volume)
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      = A * (∫ p, J p ∂((MeasureTheory.volume : Measure ℝ).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
    rw [MeasureTheory.integral_const_mul, ← hprod2]
  -- ## integrability of the weighted square (first conjunct of the statement)
  have hLHSint : MeasureTheory.Integrable (fun s : ℝ =>
      (zSchur δ (fun w => Work.Spaces.pth G w s) z) ^ 2 * Work.FTS.EllipticEst.thEta s)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine hgs_int.mono' ?_ ?_
    · exact (aesm_thEta_zSchur_pth_sq G hT δ hδ hz).congr
        (Filter.Eventually.of_forall (fun s => by ring))
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hs))]
      calc (zSchur δ (fun w => Work.Spaces.pth G w s) z) ^ 2 * Work.FTS.EllipticEst.thEta s
          = Work.FTS.EllipticEst.thEta s
              * (zSchur δ (fun w => Work.Spaces.pth G w s) z) ^ 2 := by ring
        _ ≤ A * (∫ t : ℝ, J (t, s) ∂MeasureTheory.volume) := hfs_le s hs
  refine ⟨hLHSint, ?_⟩
  calc (∫ s in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta s
        * (zSchur δ (fun w => Work.Spaces.pth G w s) z) ^ 2)
      = ∫ s : ℝ, Work.FTS.EllipticEst.thEta s
          * (zSchur δ (fun w => Work.Spaces.pth G w s) z) ^ 2
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := rfl
    _ ≤ ∫ s : ℝ, A * (∫ t : ℝ, J (t, s) ∂MeasureTheory.volume)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := hmono
    _ = A * (∫ p, J p ∂((MeasureTheory.volume : Measure ℝ).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := hgs_eq
    _ = A * (∫ t : ℝ, (if |Real.log z - t| ≤ δ then
          (∫ s in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta s
            * (Work.Spaces.pth G (Real.exp t) s) ^ 2) else 0)) := by rw [hRHS]

end Work.FTS.EllSol.EllPkgAux.MollDom
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zmoll_mixed_id =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

set_option linter.unusedVariables false

/-- **The angular derivative of the angular mollification, as a convolution with `sKerd ε`.**

For a trace-class datum `G`, a mollification scale `ε ∈ (0, 1/2]` and any bound `M` of the
derivative kernel `sKerd ε`, the `θ`-derivative of `θ' ↦ thMoll G ε w θ'` at any `θ ∈ Iθ` is the
convolution of the (doubly odd extension of the) slice `s ↦ Qext G w s` with `sKerd ε`, for
*every* radius `w > 0`; we state it for `w = eᵗ`.

This is `MollDzAux.thMoll_hasDerivAt` applied with `Q := Qext G (eᵗ)` and the slice identity
`thMoll G ε w θ' = ∫ s, sKer ε (θ' - s) * Qext G w s`. -/
theorem thMoll_pth_kernel (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    {ε M : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hM : ∀ x : ℝ, |Work.FTS.EllSol.EllPkgAux.sKerd ε x| ≤ M) :
    ∀ t : ℝ, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.pth (fun z' θ' => Work.FTS.EllSol.PkgK5.K5c.thMoll G ε z' θ') (Real.exp t) θ
        = ∫ s : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd ε (θ - s)
            * Work.FTS.EllSol.EllPkgAux.Hxyc G t s := by
  intro t θ hθ
  -- `θ ∈ Iθ` lies in the window on which the differentiation under the integral is available
  have hθw : θ ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4) := by
    obtain ⟨h1, h2⟩ := Set.mem_Icc.mp hθ
    exact ⟨by linarith, by linarith⟩
  have h := Work.FTS.EllSol.EllPkgAux.MollDzAux.thMoll_hasDerivAt
      (Q := fun s : ℝ => Work.FTS.EllSol.PkgK5.K5c.Qext G (Real.exp t) s)
      (Work.FTS.EllSol.EllPkgAux.MollDzAux.qext_continuousOn G hT (Real.exp_pos t))
      hε0 hε1 hM hθw
  simpa only [Work.Spaces.pth, Work.FTS.EllSol.PkgK5.K5c.thMoll,
    Work.FTS.EllSol.EllPkgAux.Hxyc] using h.deriv

theorem zmoll_mixed_id (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) (δ ε : ℝ)
    (hP : Work.FTS.EllSol.EllPkgAux.Params δ ε) :
    ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε)) z θ
        = ∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t)
            * (Work.Spaces.pth (fun z' θ' => Work.FTS.EllSol.PkgK5.K5c.thMoll G ε z' θ') (Real.exp t) θ) := by
  intro z hz θ hθ
  obtain ⟨hε0, hε1, hδ0, hδ1⟩ := hP
  -- ## local integrability of the angular slice functional (the domination for the outer `t`-integral)
  have hdom : MeasureTheory.LocallyIntegrable (fun t : ℝ => ∫ s in Work.Spaces.Iθ,
      |Work.FTS.EllSol.EllPkgAux.Hxyc G t s|) MeasureTheory.volume := by
    obtain ⟨C, hC, hslB⟩ := Work.FTS.EllSol.EllPkgAux.mollSliceBound
    obtain ⟨hslG, hintMGG⟩ := hslB G hT hF
    exact Work.FTS.EllSol.EllPkgAux.mollHdom G hT.1 C hC hslG hintMGG
  -- ## a bound for the derivative kernel `sKerd ε`
  obtain ⟨Mε, _hMε0, hMεb, -⟩ := Work.FTS.ClassC.RopGen.Trace.ZmollAux.exists_kernel_bound
    (Work.FTS.EllSol.EllPkgAux.MollDzAux.continuous_sKerd ε) hε0
    (fun x hx => Work.FTS.EllSol.EllPkgAux.MollDzAux.sKerd_eq_zero_of_lt_abs hε0 hx)
  -- ## the outer `D_z`, i.e. the logarithmic convolution with `sKerd δ`
  rw [Work.FTS.ClassC.RopGen.Trace.ZmollAux.zmollDzPth G hT hdom (δ := δ) (ε := ε)
    hδ0 hδ1 hε0 hε1 z hz θ hθ]
  -- ## the inner `∂_θ`, i.e. the convolution of the slice with `sKerd ε`, for every `t`
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  rw [thMoll_pth_kernel G hT hε0 hε1 hMεb t θ hθ]

end Work.FTS.EllSol.EllPkgAux.MollDom
end
end
-- ===== merged: Submission.Work.FTS.EllSol.FlatFT.Flat2DAgmonNiceBPrelim2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.FlatFT

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Vanishing of the profiles away from the `t`-support -/

theorem pth_eq_zero_of_lt_abs {ψ : ℝ → ℝ → ℝ} {M t θ : ℝ} (ht : M < |t|)
    (hψ : ∀ t' θ' : ℝ, M < |t'| → ψ t' θ' = 0) : Work.Spaces.pth ψ t θ = 0 := by
  have hz : (fun θ' : ℝ => ψ t θ') = fun _ => (0 : ℝ) := funext fun θ' => hψ t θ' ht
  simp only [Work.Spaces.pth]
  rw [hz]
  simp

theorem pth_pth_eq_zero_of_lt_abs {ψ : ℝ → ℝ → ℝ} {M t θ : ℝ} (ht : M < |t|)
    (hψ : ∀ t' θ' : ℝ, M < |t'| → ψ t' θ' = 0) :
    Work.Spaces.pth (Work.Spaces.pth ψ) t θ = 0 := by
  have hz : (fun θ' : ℝ => Work.Spaces.pth ψ t θ') = fun _ => (0 : ℝ) :=
    funext fun θ' => pth_eq_zero_of_lt_abs (ψ := ψ) ht hψ
  have hgoal : Work.Spaces.pth (Work.Spaces.pth ψ) t θ
      = deriv (fun θ' : ℝ => Work.Spaces.pth ψ t θ') θ := rfl
  rw [hgoal, hz]
  simp

theorem supp_pz {g : ℝ → ℝ → ℝ} {M : ℝ} (hM : ∀ t θ : ℝ, M < |t| → g t θ = 0) :
    ∀ t θ : ℝ, M < |t| → Work.Spaces.pz g t θ = 0 :=
  fun t θ ht => pz_eq_zero_of_lt_abs ht fun y hy => hM y θ hy

theorem supp_pth {g : ℝ → ℝ → ℝ} {M : ℝ} (hM : ∀ t θ : ℝ, M < |t| → g t θ = 0) :
    ∀ t θ : ℝ, M < |t| → Work.Spaces.pth g t θ = 0 :=
  fun t θ ht => pth_eq_zero_of_lt_abs ht hM

theorem supp_pzpz {g : ℝ → ℝ → ℝ} {M : ℝ} (hM : ∀ t θ : ℝ, M < |t| → g t θ = 0) :
    ∀ t θ : ℝ, M < |t| → Work.Spaces.pz (Work.Spaces.pz g) t θ = 0 :=
  fun t θ ht => pz_eq_zero_of_lt_abs ht fun y hy =>
    pz_eq_zero_of_lt_abs hy fun z hz => hM z θ hz


theorem supp_pthpth {g : ℝ → ℝ → ℝ} {M : ℝ} (hM : ∀ t θ : ℝ, M < |t| → g t θ = 0) :
    ∀ t θ : ℝ, M < |t| → Work.Spaces.pth (Work.Spaces.pth g) t θ = 0 :=
  fun _ θ ht => pth_pth_eq_zero_of_lt_abs ht hM

/-! ## The fixed-`θ` Plancherel data of the four slots -/




theorem plancherel_pthpth {g : ℝ → ℝ → ℝ} (hg : NiceFlat g) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    MeasureTheory.Integrable
        (fun ξ : ℝ => ‖slice (Work.Spaces.pth (Work.Spaces.pth g)) ξ θ‖ ^ 2) ∧
      (∫ ξ : ℝ, ‖slice (Work.Spaces.pth (Work.Spaces.pth g)) ξ θ‖ ^ 2)
        = ∫ t : ℝ, (Work.Spaces.pth (Work.Spaces.pth g) t θ) ^ 2 := by
  refine ⟨?_, ?_⟩
  · exact (integrable_weighted_slice1 (k := 0) (by norm_num)
      (contDiff_ofReal_comp (niceFlat_slice_pthpth_contDiff hg hθ))
      (niceFlat_hasCompactSupport_pthpth hg θ)).congr
        (Eventually.of_forall fun ξ => by
          show (2 * Real.pi * ξ) ^ (2 * 0) * ‖slice1 (fun t : ℝ =>
              ((Work.Spaces.pth (Work.Spaces.pth g) t θ : ℝ) : ℂ)) ξ‖ ^ 2
            = ‖slice (Work.Spaces.pth (Work.Spaces.pth g)) ξ θ‖ ^ 2
          rw [show (2 * Real.pi * ξ) ^ (2 * 0) = 1 by norm_num, one_mul]
          rfl)
  · have hpt : ∀ ξ : ℝ, ‖slice (Work.Spaces.pth (Work.Spaces.pth g)) ξ θ‖ ^ 2
        = ‖deriv (fun θ' => deriv (fun θ'' => slice g ξ θ'') θ') θ‖ ^ 2 := by
      intro ξ
      have hev : (fun θ' => deriv (fun θ'' => slice g ξ θ'') θ') =ᶠ[𝓝 θ]
          (fun θ' => slice (Work.Spaces.pth g) ξ θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact (slice_hasDerivAt g hg ξ hθ').1.deriv
      rw [hev.deriv_eq, (slice_hasDerivAt g hg ξ hθ).2.deriv]
    rw [integral_congr_ae (Eventually.of_forall hpt), plancherel_slice_pthpth hg hθ]

/-! ## The angular slot of a slice is finite, with an explicit energy bound -/

theorem aemeasurable_slice_sq_mul_snd {ψ : ℝ → ℝ → ℝ} {w : ℝ → ℝ}
    (hsl : ContinuousOn (fun p : ℝ × ℝ => slice ψ p.1 p.2) flStrip) (hw : Measurable w) :
    AEMeasurable (fun p : ℝ × ℝ => ‖slice ψ p.1 p.2‖ ^ 2 * w p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)) := by
  have h1 : AEMeasurable (fun p : ℝ × ℝ => ‖slice ψ p.1 p.2‖ ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)) :=
    (aemeasurable_of_continuousOn_strip
      (F := fun p : ℝ × ℝ => ‖slice ψ p.1 p.2‖) hsl.norm).pow_const 2
  have h2 : AEMeasurable (fun p : ℝ × ℝ => w p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)) :=
    (hw.comp measurable_snd).aemeasurable
  exact h1.mul h2

/-- `‖(r : ℂ)‖ = |r|`. -/
theorem norm_ofReal_eq_abs (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  have h1 : ‖(r : ℂ)‖ = |‖(r : ℂ)‖| := (abs_of_nonneg (norm_nonneg _)).symm
  rw [h1, ← Real.sqrt_sq_eq_abs (‖(r : ℂ)‖), ← Real.sqrt_sq_eq_abs r]
  congr 1
  rw [Complex.sq_norm, Complex.normSq_ofReal]
  ring

/-- The pointwise bound `‖Φ_ξ(θ)‖² ≤ 2M ∫_t φ(t,θ)²` for a profile supported in `[-M,M]`. -/
theorem slice_norm_sq_le_self {φ : ℝ → ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hcont : ContinuousOn (Function.uncurry φ) flStrip)
    (hsupp : ∀ t θ : ℝ, M < |t| → φ t θ = 0) (ξ : ℝ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ‖slice φ ξ θ‖ ^ 2 ≤ 2 * M * ∫ t : ℝ, (φ t θ) ^ 2 := by
  have hcontθ : Continuous fun t : ℝ => φ t θ := continuous_slice_of_continuousOn_strip hcont hθ
  have hsuppθ : HasCompactSupport fun t : ℝ => φ t θ := slice_hasCompactSupport hM hsupp θ
  -- step 1: `‖Φ_ξ(θ)‖ ≤ ∫_t |φ(t,θ)|`
  have hexpnorm : ∀ t : ℝ, ‖Complex.exp (-(2 * Real.pi * Complex.I * ξ * t))‖ = 1 := by
    intro t
    rw [show -(2 * Real.pi * Complex.I * ξ * t)
        = ((-(2 * Real.pi * ξ * t) : ℝ) : ℂ) * Complex.I from by
      push_cast
      ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hnorm : ‖slice φ ξ θ‖ ≤ ∫ t : ℝ, |φ t θ| := by
    have h := norm_integral_le_integral_norm (μ := MeasureTheory.volume)
      (fun t : ℝ => (φ t θ : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * ξ * t)))
    refine le_trans h (le_of_eq ?_)
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    show ‖(φ t θ : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * ξ * t))‖ = |φ t θ|
    rw [norm_mul, hexpnorm t, mul_one, norm_ofReal_eq_abs]
  -- step 2: Cauchy–Schwarz on the box `[-M,M]`
  set μ : Measure ℝ := (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc (-M) M)
    with hμ
  have hmu_univ : μ Set.univ = ENNReal.ofReal (2 * M) := by
    rw [hμ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
    congr 1
    ring
  have hmem1 : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2) μ := memLp_const 1
  have hmem2 : MemLp (fun t : ℝ => |φ t θ|) (ENNReal.ofReal 2) μ :=
    (hcontθ.abs).memLp_of_hasCompactSupport
      (hsuppθ.comp_left (g := fun x : ℝ => |x|) (by simp))
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2)
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
    (Eventually.of_forall fun _ => by norm_num)
    (Eventually.of_forall fun t => abs_nonneg _) hmem1 hmem2
  have hp1 : (∫ t : ℝ, (1 : ℝ) ^ (2 : ℝ) ∂μ) = 2 * M := by
    rw [Real.one_rpow, integral_const, Measure.real_def, hmu_univ,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul, mul_one]
  have hp2 : (∫ t : ℝ, |φ t θ| ^ (2 : ℝ) ∂μ) = ∫ t : ℝ, (φ t θ) ^ 2 := by
    have h1 : (∫ t : ℝ, |φ t θ| ^ (2 : ℝ) ∂μ) = ∫ t : ℝ, (φ t θ) ^ 2 ∂μ :=
      integral_congr_ae (Eventually.of_forall fun t => by
        show |φ t θ| ^ (2 : ℝ) = (φ t θ) ^ 2
        rw [Real.rpow_two, sq_abs])
    rw [h1, hμ, MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro t ht
    have ht' : M < |t| := not_le.mp fun hle => ht (abs_le.mp hle)
    rw [hsupp t θ ht']
    norm_num
  have hCS2 : (∫ t : ℝ, |φ t θ| ∂μ)
      ≤ (∫ t : ℝ, (1 : ℝ) ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2)
        * (∫ t : ℝ, |φ t θ| ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) := by
    rw [show (∫ t : ℝ, |φ t θ| ∂μ) = ∫ t : ℝ, 1 * |φ t θ| ∂μ from
      integral_congr_ae (Eventually.of_forall fun t => (one_mul _).symm)]
    exact hCS
  have hbound : (∫ t : ℝ, |φ t θ| ∂μ) ≤ Real.sqrt (2 * M) * Real.sqrt (∫ t : ℝ, (φ t θ) ^ 2) := by
    have h := hCS2
    rw [hp1, hp2] at h
    simpa [Real.sqrt_eq_rpow] using h
  have hfull : (∫ t : ℝ, |φ t θ| ∂μ) = ∫ t : ℝ, |φ t θ| :=
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => by
      have ht' : M < |t| := not_le.mp fun hle => ht (abs_le.mp hle)
      rw [hsupp t θ ht', abs_zero]
  rw [hfull] at hbound
  have hsq : (∫ t : ℝ, |φ t θ|) ^ 2 ≤ (2 * M) * ∫ t : ℝ, (φ t θ) ^ 2 := by
    have hnn : 0 ≤ ∫ t : ℝ, |φ t θ| := integral_nonneg fun t => abs_nonneg _
    have hmain := mul_self_le_mul_self hnn hbound
    have hsq2 : (Real.sqrt (2 * M) * Real.sqrt (∫ t : ℝ, (φ t θ) ^ 2))
        * (Real.sqrt (2 * M) * Real.sqrt (∫ t : ℝ, (φ t θ) ^ 2))
        = (2 * M) * ∫ t : ℝ, (φ t θ) ^ 2 := by
      rw [mul_mul_mul_comm, Real.mul_self_sqrt (by linarith),
        Real.mul_self_sqrt (integral_nonneg fun t => sq_nonneg _)]
    calc (∫ t : ℝ, |φ t θ|) ^ 2 = (∫ t : ℝ, |φ t θ|) * (∫ t : ℝ, |φ t θ|) := by ring
      _ ≤ (Real.sqrt (2 * M) * Real.sqrt (∫ t : ℝ, (φ t θ) ^ 2))
            * (Real.sqrt (2 * M) * Real.sqrt (∫ t : ℝ, (φ t θ) ^ 2)) := hmain
      _ = (2 * M) * ∫ t : ℝ, (φ t θ) ^ 2 := hsq2
  have hstep1 : ‖slice φ ξ θ‖ * ‖slice φ ξ θ‖
      ≤ (∫ t : ℝ, |φ t θ|) * (∫ t : ℝ, |φ t θ|) :=
    mul_self_le_mul_self (norm_nonneg _) hnorm
  calc ‖slice φ ξ θ‖ ^ 2 = ‖slice φ ξ θ‖ * ‖slice φ ξ θ‖ := by ring
    _ ≤ (∫ t : ℝ, |φ t θ|) * (∫ t : ℝ, |φ t θ|) := hstep1
    _ = (∫ t : ℝ, |φ t θ|) ^ 2 := by ring
    _ ≤ 2 * M * ∫ t : ℝ, (φ t θ) ^ 2 := hsq

theorem integrableOn_slice_sq_mul {ψ : ℝ → ℝ → ℝ} {w : ℝ → ℝ} {M ξ : ℝ} (hM : 0 ≤ M)
    (hcont : ContinuousOn (Function.uncurry ψ) flStrip)
    (hsupp : ∀ t θ : ℝ, M < |t| → ψ t θ = 0)
    (hwnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ w θ) (hwmeas : Measurable w)
    (hslice : ContinuousOn (fun θ : ℝ => slice ψ ξ θ) (Set.Ioo 0 (Real.pi / 2)))
    (henergy : MeasureTheory.IntegrableOn (fun θ : ℝ => (∫ t : ℝ, (ψ t θ) ^ 2) * w θ)
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => ‖slice ψ ξ θ‖ ^ 2 * w θ) Work.Spaces.Iθ := by
  refine MeasureTheory.Integrable.mono' (henergy.const_mul (2 * M)) ?_ ?_
  · have h1 : AEMeasurable (fun θ : ℝ => ‖slice ψ ξ θ‖ ^ 2)
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ) :=
      (aemeasurable_Iθ_of_continuousOn_Ioo hslice.norm).pow_const 2
    have h2 : AEMeasurable (fun θ : ℝ => w θ)
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ) :=
      hwmeas.aemeasurable.restrict
    exact aestronglyMeasurable_iff_aemeasurable.mpr (h1.mul h2)
  · filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    have hw0 : 0 ≤ w θ := hwnn θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hb := slice_norm_sq_le_self hM hcont hsupp ξ hθ
    calc ‖‖slice ψ ξ θ‖ ^ 2 * w θ‖ = ‖slice ψ ξ θ‖ ^ 2 * w θ :=
          Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hw0)
      _ ≤ ((2 * M) * ∫ t : ℝ, (ψ t θ) ^ 2) * w θ := mul_le_mul_of_nonneg_right hb hw0
      _ = 2 * M * ((∫ t : ℝ, (ψ t θ) ^ 2) * w θ) := by ring

theorem integrableOn_slice_sq_mul_le {ψ : ℝ → ℝ → ℝ} {w w' : ℝ → ℝ} {ξ : ℝ}
    (hwnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ w θ) (hw'nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ w' θ)
    (hle : ∀ θ ∈ Work.Spaces.Iθ, w θ ≤ w' θ)
    (hslice : ContinuousOn (fun θ : ℝ => slice ψ ξ θ) (Set.Ioo 0 (Real.pi / 2)))
    (hwmeas : Measurable w)
    (h' : MeasureTheory.IntegrableOn (fun θ : ℝ => ‖slice ψ ξ θ‖ ^ 2 * w' θ)
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => ‖slice ψ ξ θ‖ ^ 2 * w θ) Work.Spaces.Iθ := by
  refine MeasureTheory.Integrable.mono' h' ?_ ?_
  · have h1 : AEMeasurable (fun θ : ℝ => ‖slice ψ ξ θ‖ ^ 2)
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ) :=
      (aemeasurable_Iθ_of_continuousOn_Ioo hslice.norm).pow_const 2
    have h2 : AEMeasurable (fun θ : ℝ => w θ)
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ) :=
      hwmeas.aemeasurable.restrict
    exact aestronglyMeasurable_iff_aemeasurable.mpr (h1.mul h2)
  · filter_upwards [ae_mem_Iθ] with θ hθ
    have h1 : 0 ≤ ‖slice ψ ξ θ‖ ^ 2 := sq_nonneg _
    calc ‖‖slice ψ ξ θ‖ ^ 2 * w θ‖ = ‖slice ψ ξ θ‖ ^ 2 * w θ :=
          Real.norm_of_nonneg (mul_nonneg h1 (hwnn θ hθ))
      _ ≤ ‖slice ψ ξ θ‖ ^ 2 * w' θ := mul_le_mul_of_nonneg_left (hle θ hθ) h1

end

end Work.FTS.EllSol.FlatFT
end
-- ===== merged: Submission.Work.FTS.EllSol.ShiftFT.ShiftPassDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT

open MeasureTheory Set
open scoped Real Topology

noncomputable section

set_option autoImplicit false


/-- The scale sequence `Nf n = n + 2` along which the truncation parameter tends to `∞`. -/
def Nf (n : ℕ) : ℝ := (n : ℝ) + 2

/-- The heavy first-order slot `(L_b f)² σ_η`, `L_b f = ∂_t f - b f`. -/
def slotE1 (b : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (Work.Spaces.pz f p.1 p.2 - b * f p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2

/-- The heavy second-order slot `(L_b²f)² σ_η`. -/
def slotE2 (b : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (Work.Spaces.pz (Work.Spaces.pz f) p.1 p.2 - 2 * b * Work.Spaces.pz f p.1 p.2
      + b ^ 2 * f p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2

/-- The heavy angular slot `(∂_θ²f)² σ_η`. -/
def slotE3 (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (Work.Spaces.pth (Work.Spaces.pth f) p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2

/-- The light mixed slot `(∂_θL_b f)² σ_a`. -/
def slotAa (α b : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (Work.Spaces.pth (Work.Spaces.pz f) p.1 p.2 - b * Work.Spaces.pth f p.1 p.2) ^ 2
    * Work.FTS.EllSol.FlatFT.wA α p.2

@[simp] theorem slotE1_apply (b : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    slotE1 b f p = (Work.Spaces.pz f p.1 p.2 - b * f p.1 p.2) ^ 2
      * Work.FTS.EllSol.FlatFT.wE p.2 := rfl

@[simp] theorem slotE2_apply (b : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    slotE2 b f p = (Work.Spaces.pz (Work.Spaces.pz f) p.1 p.2
        - 2 * b * Work.Spaces.pz f p.1 p.2 + b ^ 2 * f p.1 p.2) ^ 2
      * Work.FTS.EllSol.FlatFT.wE p.2 := rfl

@[simp] theorem slotE3_apply (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    slotE3 f p = (Work.Spaces.pth (Work.Spaces.pth f) p.1 p.2) ^ 2
      * Work.FTS.EllSol.FlatFT.wE p.2 := rfl

@[simp] theorem slotAa_apply (α b : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    slotAa α b f p = (Work.Spaces.pth (Work.Spaces.pz f) p.1 p.2
        - b * Work.Spaces.pth f p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wA α p.2 := rfl







end

end Work.FTS.EllSol.ShiftFT
end
-- ===== merged: Submission.Work.FTS.EllSol.ShiftFT.uTrAone.GcAbsLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT.uTrAone

open MeasureTheory Set
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-- `Gc` vanishes on the far right: for `t ≥ 2N` the cutoff term is zero, and the interval
integral is zero because `(chi N)'` is supported in `[-2N,2N]`. -/
theorem gc_right_zero (N b : ℝ) (u : ℝ → ℝ → ℝ) (hN : 0 < N) {t θ : ℝ}
    (ht : 2 * N ≤ |t|) (hge : 2 * N ≤ t) :
    Work.FTS.EllSol.ShiftFT.Gc N b u t θ = 0 := by
  have hchit : Work.FTS.EllSol.Trunc.chi N t = 0 := Work.FTS.EllSol.Trunc.chi_eq_zero hN ht
  have hI : (∫ s in t..(2 * N),
      Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ) = 0 := by
    rcases eq_or_lt_of_le hge with heq | hlt
    · rw [heq, intervalIntegral.integral_same]
    · rw [intervalIntegral.integral_of_ge (le_of_lt hlt)]
      have hz : (∫ x in Set.Ioc (2 * N) t,
          Real.exp (-(b * x)) * deriv (Work.FTS.EllSol.Trunc.chi N) x * u x θ) = 0 :=
        MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero (fun x hx => by
          have hd : deriv (Work.FTS.EllSol.Trunc.chi N) x = 0 :=
            Work.FTS.EllSol.Trunc.deriv_chi_eq_zero_of_gt hN (by
              rw [abs_of_pos (by linarith [hx.1])]
              exact hx.1)
          simp [hd])
      rw [hz, neg_zero]
  show Work.FTS.EllSol.Trunc.chi N t * u t θ
      + Real.exp (b * t) * (∫ s in t..(2 * N),
          Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ) = 0
  rw [hchit, hI]
  ring

/-- The tail representation of `Gc` for `t ≤ -2N`: integrating
`s ↦ chi N s · e^{-bs} u(s,θ)` by parts over `[t,2N]` (both boundary terms vanish because
`chi N` is supported in `[-2N,2N]`) turns the defining integral into the shifted derivative
of `u` against `chi N · e^{b(t-s)}`. -/
theorem gc_tail_ibp (N b : ℝ) (u : ℝ → ℝ → ℝ) (hN : 0 < N)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {t θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hle : t ≤ -(2 * N)) :
    Work.FTS.EllSol.ShiftFT.Gc N b u t θ
      = -(∫ s in t..(2 * N), Work.FTS.EllSol.Trunc.chi N s * Real.exp (b * (t - s))
          * (Work.Spaces.pz u s θ - b * u s θ)) := by
  have hC2 : Work.FTS.EllSol.Trunc.StripC2 u := hu
  have hslice : ∀ x : ℝ, HasDerivAt (fun s : ℝ => u s θ) (Work.Spaces.pz u x θ) x :=
    fun x => Work.FTS.EllSol.Trunc.hasDerivAt_zslice hC2 hθ x
  have huC : Continuous (fun s : ℝ => u s θ) := Work.FTS.EllSol.Trunc.continuous_zslice hC2 hθ
  have hpzC : Continuous (fun s : ℝ => Work.Spaces.pz u s θ) :=
    Work.FTS.EllSol.Trunc.continuous_pz_zslice hC2 hθ
  have hLcont : Continuous (fun s : ℝ => Work.Spaces.pz u s θ - b * u s θ) :=
    hpzC.sub (continuous_const.mul huC)
  have hchit : Work.FTS.EllSol.Trunc.chi N t = 0 := by
    apply Work.FTS.EllSol.Trunc.chi_eq_zero hN
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hchi2N : Work.FTS.EllSol.Trunc.chi N (2 * N) = 0 := by
    apply Work.FTS.EllSol.Trunc.chi_eq_zero hN
    rw [abs_of_nonneg (by linarith)]
  have hIbp : (∫ x in t..(2 * N),
        deriv (Work.FTS.EllSol.Trunc.chi N) x * (Real.exp (-(b * x)) * u x θ))
      = -(∫ x in t..(2 * N), Work.FTS.EllSol.Trunc.chi N x
          * (Real.exp (-(b * x)) * (Work.Spaces.pz u x θ - b * u x θ))) := by
    have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (a := t) (b := 2 * N)
      (u := fun x : ℝ => Work.FTS.EllSol.Trunc.chi N x)
      (v := fun x : ℝ => Real.exp (-(b * x)) * u x θ)
      (u' := fun x : ℝ => deriv (Work.FTS.EllSol.Trunc.chi N) x)
      (v' := fun x : ℝ => Real.exp (-(b * x)) * (Work.Spaces.pz u x θ - b * u x θ))
      (fun x _ => ((Work.FTS.EllSol.Trunc.chi_contDiff 1 N).differentiable
        (by norm_num) x).hasDerivAt)
      (fun x _ => by
        have hx1 : HasDerivAt (fun s : ℝ => Real.exp (-(b * s)))
            (Real.exp (-(b * x)) * (-b)) x := by
          have h2 : HasDerivAt (fun s : ℝ => -(b * s)) (-b) x := by
            simpa using (hasDerivAt_id x).const_mul (-b)
          simpa using h2.exp
        have h3 := hx1.mul (hslice x)
        convert h3 using 1
        ring)
      (((Work.FTS.EllSol.Trunc.chi_contDiff 2 N).continuous_deriv
        (by norm_num)).intervalIntegrable t (2 * N))
      (((Real.continuous_exp.comp (by fun_prop :
          Continuous fun s : ℝ => -(b * s))).mul hLcont).intervalIntegrable t (2 * N))
    rw [hchi2N, hchit] at h1
    simp only [zero_mul, sub_zero, zero_sub] at h1
    linarith
  have hIeq : (∫ s in t..(2 * N),
        Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ)
      = ∫ s in t..(2 * N),
          deriv (Work.FTS.EllSol.Trunc.chi N) s * (Real.exp (-(b * s)) * u s θ) := by
    apply intervalIntegral.integral_congr
    intro s _
    ring
  show Work.FTS.EllSol.Trunc.chi N t * u t θ
      + Real.exp (b * t) * (∫ s in t..(2 * N),
          Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ)
      = -(∫ s in t..(2 * N), Work.FTS.EllSol.Trunc.chi N s * Real.exp (b * (t - s))
          * (Work.Spaces.pz u s θ - b * u s θ))
  rw [hchit, zero_mul, zero_add, hIeq, hIbp, mul_neg, ← intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  simp only []
  have he : Real.exp (b * t) * Real.exp (-(b * s)) = Real.exp (b * (t - s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [show Real.exp (b * t) * (Work.FTS.EllSol.Trunc.chi N s
        * (Real.exp (-(b * s)) * (Work.Spaces.pz u s θ - b * u s θ)))
      = Work.FTS.EllSol.Trunc.chi N s * (Real.exp (b * t) * Real.exp (-(b * s)))
        * (Work.Spaces.pz u s θ - b * u s θ) from by ring,
    he]

/-- Domination of the cutoff-weighted integral: on `[t,2N]` with `t ≤ -2N` the cutoff
vanishes below `-2N` and is `≤ 1` on `[-2N,2N]`, and the exponential factor `e^{b(t-s)}` is
`≤ 1` there because `b ≥ 0` and `t ≤ s`. -/
theorem chi_exp_abs_le (N b : ℝ) (hN : 0 < N) (hb : 0 ≤ b)
    {L : ℝ → ℝ} (hL : Continuous L) {t : ℝ} (hle : t ≤ -(2 * N)) :
    |∫ s in t..(2 * N),
        Work.FTS.EllSol.Trunc.chi N s * Real.exp (b * (t - s)) * L s|
      ≤ ∫ s in (-(2 * N))..(2 * N), |L s| := by
  have hNm : -(2 * N) ≤ 2 * N := by linarith
  have hgC : Continuous (fun s : ℝ =>
      Work.FTS.EllSol.Trunc.chi N s * Real.exp (b * (t - s)) * |L s|) :=
    (((Work.FTS.EllSol.Trunc.chi_contDiff 0 N).continuous).mul (by fun_prop :
      Continuous fun s : ℝ => Real.exp (b * (t - s)))).mul hL.abs
  have hz : (∫ s in t..(-(2 * N)),
      Work.FTS.EllSol.Trunc.chi N s * Real.exp (b * (t - s)) * |L s|) = 0 := by
    rw [← intervalIntegral.integral_zero (a := t) (b := -(2 * N))]
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [Pi.zero_apply]
    rw [Set.uIcc_of_le hle] at hx
    have hxle : x ≤ -(2 * N) := hx.2
    have hchi0 : Work.FTS.EllSol.Trunc.chi N x = 0 := by
      apply Work.FTS.EllSol.Trunc.chi_eq_zero hN
      rw [abs_of_nonpos (by linarith)]
      linarith
    rw [hchi0, zero_mul, zero_mul]
  calc |∫ s in t..(2 * N),
        Work.FTS.EllSol.Trunc.chi N s * Real.exp (b * (t - s)) * L s|
      ≤ ∫ s in t..(2 * N),
          |Work.FTS.EllSol.Trunc.chi N s * Real.exp (b * (t - s)) * L s| :=
        intervalIntegral.abs_integral_le_integral_abs (by linarith)
    _ = ∫ s in t..(2 * N),
          Work.FTS.EllSol.Trunc.chi N s * Real.exp (b * (t - s)) * |L s| := by
        apply intervalIntegral.integral_congr
        intro s _
        simp only []
        rw [abs_mul, abs_mul, abs_of_nonneg (Work.FTS.EllSol.Trunc.chi_nonneg N s),
          abs_of_pos (Real.exp_pos _)]
    _ = ∫ s in (-(2 * N))..(2 * N),
          Work.FTS.EllSol.Trunc.chi N s * Real.exp (b * (t - s)) * |L s| := by
        rw [← intervalIntegral.integral_add_adjacent_intervals
          (hgC.intervalIntegrable t (-(2 * N))) (hgC.intervalIntegrable (-(2 * N)) (2 * N)),
          hz, zero_add]
    _ ≤ ∫ s in (-(2 * N))..(2 * N), |L s| := by
        apply intervalIntegral.integral_mono_on hNm
        · exact hgC.intervalIntegrable _ _
        · exact hL.abs.intervalIntegrable _ _
        · intro x hx
          have hb0 : b * (t - x) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hb (by linarith [hx.1, hle])
          have hexp1 : Real.exp (b * (t - x)) ≤ 1 := Real.exp_le_one_iff.mpr hb0
          have hexp0 : 0 ≤ Real.exp (b * (t - x)) := Real.exp_nonneg _
          have hchi1 : Work.FTS.EllSol.Trunc.chi N x ≤ 1 :=
            Work.FTS.EllSol.Trunc.chi_le_one N x
          have hchi0 : 0 ≤ Work.FTS.EllSol.Trunc.chi N x :=
            Work.FTS.EllSol.Trunc.chi_nonneg N x
          calc Work.FTS.EllSol.Trunc.chi N x * Real.exp (b * (t - x)) * |L x|
              ≤ 1 * 1 * |L x| := by
                apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
                exact mul_le_mul hchi1 hexp1 hexp0 (by norm_num)
            _ = |L x| := by ring

theorem GcAbsLe (N b : ℝ) (u : ℝ → ℝ → ℝ) (hN : 0 < N) (hb : 0 ≤ b)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) → 2 * N ≤ |t| →
      |Work.FTS.EllSol.ShiftFT.Gc N b u t θ|
        ≤ ∫ s in (-(2 * N))..(2 * N), |Work.Spaces.pz u s θ - b * u s θ| := by
  intro t θ hθ ht
  have hC2 : Work.FTS.EllSol.Trunc.StripC2 u := hu
  have hLcont : Continuous (fun s : ℝ => Work.Spaces.pz u s θ - b * u s θ) :=
    (Work.FTS.EllSol.Trunc.continuous_pz_zslice hC2 hθ).sub
      (continuous_const.mul (Work.FTS.EllSol.Trunc.continuous_zslice hC2 hθ))
  rcases le_abs.mp ht with hge | hle'
  · rw [gc_right_zero N b u hN ht hge, abs_zero]
    exact intervalIntegral.integral_nonneg (by linarith) (fun x _ => abs_nonneg _)
  · have hle : t ≤ -(2 * N) := by linarith
    rw [gc_tail_ibp N b u hN hu hθ hle, abs_neg]
    exact chi_exp_abs_le N b hN hb hLcont hle

end

end Work.FTS.EllSol.ShiftFT.uTrAone
end
-- ===== merged: Submission.Work.FTS.EllSol.ShiftFT.uTrAone.GcAesm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT.uTrAone

open MeasureTheory Set

/-- The particular solution `Gc N b u` of the shifted equation is continuous on the open
strip `ℝ × (0,π/2)`.

`Gc N b u t θ = χ_N(t)·u(t,θ) + e^{bt} ∫_s in t..(2N), e^{-bs}·(χ_N)'(s)·u(s,θ)`.
The first summand is a product of continuous functions.  For the second we use the joint
continuity of a parameter-dependent interval integral with a *moving* limit; the integrand
`(s,θ) ↦ e^{-bs}(χ_N)'(s)u(s,θ)` is only known to be continuous on the open strip, so
`intervalIntegral.continuous_parametric_primitive_of_continuous` is applied to the subtype
`↥(univ ×ˢ Ioo 0 (π/2))`, after inverting the interval (`∫_t^{2N} = -∫_{2N}^t`) to turn the
moving lower limit into a moving upper limit. -/
theorem continuousOn_Gc_strip (N b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllSol.ShiftFT.Gc N b u p.1 p.2)
      (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  set F : ℝ → ℝ → ℝ :=
    fun s θ => Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ with hFdef
  have hucont : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2)
      (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) := hu.continuousOn
  have hFc : ContinuousOn (Function.uncurry F) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : Continuous (fun p : ℝ × ℝ => Real.exp (-(b * p.1))) := by fun_prop
    have h2 : Continuous (fun p : ℝ × ℝ => deriv (Work.FTS.EllSol.Trunc.chi N) p.1) :=
      ((Work.FTS.EllSol.Trunc.chi_contDiff 1 N).continuous_deriv (by norm_num)).comp
        continuous_fst
    have h3 := (h1.continuousOn.mul h2.continuousOn).mul hucont
    rw [hFdef]
    exact h3
  -- joint continuity of the moving-limit interval integral
  have hint : ContinuousOn (fun p : ℝ × ℝ => ∫ s in p.1..(2 * N), F s p.2)
      (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hf : Continuous (fun q : ↥((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) × ℝ =>
        F q.2 q.1.val.2) := by
      have hmaps : ∀ q : ↥((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) × ℝ,
          ((q.2, q.1.val.2) : ℝ × ℝ) ∈ Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2) :=
        fun q => ⟨trivial, q.1.property.2⟩
      have hcont : Continuous (fun q : ↥((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) × ℝ =>
          ((q.2, q.1.val.2) : ℝ × ℝ)) :=
        continuous_snd.prodMk ((continuous_snd.comp continuous_subtype_val).comp continuous_fst)
      exact hFc.comp_continuous hcont hmaps
    have h1 : Continuous (fun p : ↥((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) × ℝ =>
        ∫ t in (2 * N)..p.2, F t p.1.val.2) :=
      intervalIntegral.continuous_parametric_primitive_of_continuous
        (f := fun (x : ↥((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))) (s : ℝ) =>
          F s x.val.2) (a₀ := 2 * N) hf
    have h2 : Continuous (fun x : ↥((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) =>
        ∫ t in (2 * N)..x.val.1, F t x.val.2) :=
      h1.comp (continuous_id.prodMk (continuous_fst.comp continuous_subtype_val))
    rw [continuousOn_iff_continuous_domRestrict]
    refine h2.neg.congr (fun x => ?_)
    rw [Set.domRestrict_apply, Pi.neg_apply]
    exact (intervalIntegral.integral_symm (f := fun s : ℝ => F s x.val.2) (2 * N) x.val.1).symm
  have hprod : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllSol.Trunc.chi N p.1 * u p.1 p.2)
      (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((((Work.FTS.EllSol.Trunc.chi_contDiff 1 N).continuous).comp continuous_fst).continuousOn).mul
      hucont
  have hexp2 : ContinuousOn (fun p : ℝ × ℝ => Real.exp (b * p.1))
      (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (by fun_prop : Continuous (fun p : ℝ × ℝ => Real.exp (b * p.1))).continuousOn
  have hg : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllSol.Trunc.chi N p.1 * u p.1 p.2
      + Real.exp (b * p.1) * ∫ s in p.1..(2 * N), F s p.2)
      (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    hprod.add (hexp2.mul hint)
  refine hg.congr (fun p hp => ?_)
  simp only [hFdef, Work.FTS.EllSol.ShiftFT.Gc]

theorem GcAesm (N b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.FTS.EllSol.ShiftFT.Gc N b u p.1 p.2)
      (MeasureTheory.volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) := by
  exact Work.FTS.EllSol.Trunc.aesm_strip (continuousOn_Gc_strip N b u hu)

end Work.FTS.EllSol.ShiftFT.uTrAone
end
-- ===== merged: Submission.Work.FTS.EllSol.ShiftFT.uTr_Atwo =====
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

theorem uTr_Atwo (b : ℝ) (u : ℝ → ℝ → ℝ) (hb : 0 ≤ b)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (h0 : ∀ t : ℝ, u t 0 = 0) (h1 : ∀ t : ℝ, u t (Real.pi / 2) = 0)
    (hI : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz (Work.Spaces.pz u) p.1 p.2 - 2 * b * Work.Spaces.pz u p.1 p.2
          + b ^ 2 * u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ))
    (hJ : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2
          * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ)) :
    ∃ K : ℝ, 0 < K ∧ ∀ N ≥ (2 : ℝ),
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz (Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.uTr N b u)) p.1 p.2
          - 2 * b * Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.uTr N b u) p.1 p.2
          + b ^ 2 * Work.FTS.EllSol.ShiftFT.uTr N b u p.1 p.2) ^ 2
          * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ) ∧
      (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          (Work.Spaces.pz (Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.uTr N b u)) p.1 p.2
            - 2 * b * Work.Spaces.pz (Work.FTS.EllSol.ShiftFT.uTr N b u) p.1 p.2
            + b ^ 2 * Work.FTS.EllSol.ShiftFT.uTr N b u p.1 p.2) ^ 2
            * Work.FTS.EllSol.FlatFT.wE p.2)
        ≤ K * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
            (Work.Spaces.pz (Work.Spaces.pz u) p.1 p.2 - 2 * b * Work.Spaces.pz u p.1 p.2
              + b ^ 2 * u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
          + (K / N) * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
            (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2
              * Work.FTS.EllSol.FlatFT.wE p.2) := by
  obtain ⟨Kd, hKd0, hKd⟩ := Work.FTS.EllSol.Trunc.exists_bound_deriv_tk
  obtain ⟨M, hM0, hM⟩ := Work.FTS.EllSol.Trunc.exists_bound_deriv2_tk
  refine ⟨3 + 3 * (Kd * (1 + 2 / 4096)) ^ 2 + 196608 * M ^ 2 / 4096 ^ 4, ?_, fun N hN => ?_⟩
  · have h2 : (0 : ℝ) ≤ 3 * (Kd * (1 + 2 / 4096)) ^ 2 := by positivity
    have h3 : (0 : ℝ) ≤ 196608 * M ^ 2 / 4096 ^ 4 := by positivity
    linarith
  · have hN0 : 0 < N := by linarith
    have hI' : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (uTrAtwo_L2 b u p.1 p.2) ^ 2
        * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ) := by
      simpa only [uTrAtwo_L2] using hI
    have hJ' : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (uTrAtwo_L1 b u p.1 p.2) ^ 2
        * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ) := by
      simpa only [uTrAtwo_L1] using hJ
    obtain ⟨hK3, hcc⟩ := uTrAtwo_const N Kd M
      (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2) hN hKd0
      (integral_deriv2_phiTr_sq_le N hM hN0)
    have hI2nn : 0 ≤ ∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L2 b u p.1 p.2) ^ 2
        * Work.FTS.EllSol.FlatFT.wE p.2 :=
      MeasureTheory.setIntegral_nonneg measurableSet_stripIθ (fun p hp =>
        mul_nonneg (sq_nonneg _) (Work.FTS.EllSol.FlatFT.wE_nonneg hp.2))
    have hJnn : 0 ≤ ∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
        * Work.FTS.EllSol.FlatFT.wE p.2 :=
      MeasureTheory.setIntegral_nonneg measurableSet_stripIθ (fun p hp =>
        mul_nonneg (sq_nonneg _) (Work.FTS.EllSol.FlatFT.wE_nonneg hp.2))
    have hAphinn : 0 ≤ ∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2 :=
      MeasureTheory.integral_nonneg (fun t => sq_nonneg _)
    have hDint : MeasureTheory.IntegrableOn (uTrAtwo_D N b u Kd)
        (Set.univ ×ˢ Work.Spaces.Iθ) :=
      uTrAtwo_D_integrable N b u Kd hN0 hu hI' hJ
    have hae : (fun p : ℝ × ℝ => (uTrAtwo_L2 b (uTr N b u) p.1 p.2) ^ 2
        * Work.FTS.EllSol.FlatFT.wE p.2)
        =ᵐ[MeasureTheory.volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)]
        (fun p : ℝ × ℝ => (uTrAtwo_W N b u p) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2) := by
      filter_upwards [ae_uTr_L2_eq N b u hu] with p hp
      rw [hp]
    have hle : (fun p : ℝ × ℝ => (uTrAtwo_W N b u p) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
        ≤ᵐ[MeasureTheory.volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)]
        uTrAtwo_D N b u Kd := by
      filter_upwards [ae_mem_Ioo_of_Iθ] with p hp
      exact uTrAtwo_W_sq_le_D N b u hb hN0 hu hKd hKd0 p hp
    have hWint : MeasureTheory.Integrable (fun p : ℝ × ℝ => (uTrAtwo_W N b u p) ^ 2
        * Work.FTS.EllSol.FlatFT.wE p.2)
        (MeasureTheory.volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
      MeasureTheory.Integrable.mono' hDint (uTrAtwo_W_aesm N b u hN hu h0 h1) (by
        filter_upwards [hle, ae_restrict_mem measurableSet_stripIθ] with p hp hmem
        rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
          (Work.FTS.EllSol.FlatFT.wE_nonneg hmem.2))]
        exact hp)
    have hmain := integral_uTrAtwo_D N b u Kd hN0 hu hI' hJ
    have hwin := (Aux2.windowMarginal b N u hu hJ)
    have hWle : (∫ θ in Work.Spaces.Iθ, (∫ s in Set.Icc (-(2 * N)) (2 * N),
        (uTrAtwo_L1 b u s θ) ^ 2) * Work.FTS.EllSol.FlatFT.wE θ)
        ≤ ∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
            * Work.FTS.EllSol.FlatFT.wE p.2 :=
      hwin.2
    have hint : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (uTrAtwo_L2 b (uTr N b u) p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
        (Set.univ ×ˢ Work.Spaces.Iθ) := by
      exact hWint.congr hae.symm
    refine ⟨hint, ?_⟩
    calc (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          (uTrAtwo_L2 b (uTr N b u) p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
        = ∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
            (uTrAtwo_W N b u p) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2 :=
          MeasureTheory.integral_congr_ae hae
      _ ≤ ∫ p in Set.univ ×ˢ Work.Spaces.Iθ, uTrAtwo_D N b u Kd p :=
          MeasureTheory.integral_mono_ae hWint hDint hle
      _ = 3 * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L2 b u p.1 p.2) ^ 2
              * Work.FTS.EllSol.FlatFT.wE p.2)
            + 3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2
                * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
                    * Work.FTS.EllSol.FlatFT.wE p.2)
            + 3 * (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2)
                * (4 * N * (∫ θ in Work.Spaces.Iθ, (∫ s in Set.Icc (-(2 * N)) (2 * N),
                    (uTrAtwo_L1 b u s θ) ^ 2) * Work.FTS.EllSol.FlatFT.wE θ)) := hmain
      _ ≤ (3 + 3 * (Kd * (1 + 2 / 4096)) ^ 2 + 196608 * M ^ 2 / 4096 ^ 4)
              * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L2 b u p.1 p.2) ^ 2
                  * Work.FTS.EllSol.FlatFT.wE p.2)
            + ((3 + 3 * (Kd * (1 + 2 / 4096)) ^ 2 + 196608 * M ^ 2 / 4096 ^ 4) / N)
              * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
                  * Work.FTS.EllSol.FlatFT.wE p.2) := by
          have h1 : 3 * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L2 b u p.1 p.2) ^ 2
              * Work.FTS.EllSol.FlatFT.wE p.2)
              ≤ (3 + 3 * (Kd * (1 + 2 / 4096)) ^ 2 + 196608 * M ^ 2 / 4096 ^ 4)
                * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L2 b u p.1 p.2) ^ 2
                    * Work.FTS.EllSol.FlatFT.wE p.2) := by
            nlinarith [hI2nn, hK3]
          have h2 : 3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2
                * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
                    * Work.FTS.EllSol.FlatFT.wE p.2)
              + 3 * (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2)
                * (4 * N * (∫ θ in Work.Spaces.Iθ, (∫ s in Set.Icc (-(2 * N)) (2 * N),
                    (uTrAtwo_L1 b u s θ) ^ 2) * Work.FTS.EllSol.FlatFT.wE θ))
              ≤ ((3 + 3 * (Kd * (1 + 2 / 4096)) ^ 2 + 196608 * M ^ 2 / 4096 ^ 4) / N)
                * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
                    * Work.FTS.EllSol.FlatFT.wE p.2) := by
            have hJv : 0 ≤ ∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
                * Work.FTS.EllSol.FlatFT.wE p.2 := hJnn
            have hb : 3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2
                * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
                    * Work.FTS.EllSol.FlatFT.wE p.2)
                + 12 * N * (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2)
                  * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
                      * Work.FTS.EllSol.FlatFT.wE p.2)
                = (3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2
                    + 12 * N * (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2))
                  * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
                      * Work.FTS.EllSol.FlatFT.wE p.2) := by ring
            have hc : (3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2
                    + 12 * N * (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2))
                  * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
                      * Work.FTS.EllSol.FlatFT.wE p.2)
                ≤ ((3 + 3 * (Kd * (1 + 2 / 4096)) ^ 2 + 196608 * M ^ 2 / 4096 ^ 4) / N)
                  * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
                      * Work.FTS.EllSol.FlatFT.wE p.2) :=
              mul_le_mul_of_nonneg_right hcc hJv
            have hd : 3 * (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2)
                  * (4 * N * (∫ θ in Work.Spaces.Iθ, (∫ s in Set.Icc (-(2 * N)) (2 * N),
                      (uTrAtwo_L1 b u s θ) ^ 2) * Work.FTS.EllSol.FlatFT.wE θ))
                ≤ 12 * N * (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2)
                  * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
                      * Work.FTS.EllSol.FlatFT.wE p.2) := by
              have h4 : (∫ θ in Work.Spaces.Iθ, (∫ s in Set.Icc (-(2 * N)) (2 * N),
                  (uTrAtwo_L1 b u s θ) ^ 2) * Work.FTS.EllSol.FlatFT.wE θ)
                  ≤ (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
                      * Work.FTS.EllSol.FlatFT.wE p.2) := hWle
              have h5 : 3 * (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2)
                    * (4 * N * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
                        (uTrAtwo_L1 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2))
                  = 12 * N * (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2)
                    * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
                        * Work.FTS.EllSol.FlatFT.wE p.2) := by ring
              have h6 : 3 * (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2)
                    * (4 * N * (∫ θ in Work.Spaces.Iθ, (∫ s in Set.Icc (-(2 * N)) (2 * N),
                        (uTrAtwo_L1 b u s θ) ^ 2) * Work.FTS.EllSol.FlatFT.wE θ))
                  ≤ 3 * (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2)
                    * (4 * N * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
                        (uTrAtwo_L1 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact mul_le_mul_of_nonneg_left h4 (by positivity)
              linarith [h5.le, h5.ge, h6]
            linarith [hb.le, hb.ge, hd, hc]
          linarith [h1, h2]

end

end Work.FTS.EllSol.ShiftFT
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.IP_add_repr =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeI1Fts/IP_add_repr` — the additive representation of the `ω²σ`-pairing

The `I₁` chain of Elgindi, Annals 194 (3) 2021, splits the pairing
`IP (AA u) (BB u) + IP (cw·U u) (BB u)` into the single iterated integral

`∫_z w(z)² ∫_θ sin(2θ)^{-η} (AA·BB + cw·U·BB)`.

The pairing `AngSecond.IP g h = ∫_z ∫_θ g h w² σ` is a *totalised* (Bochner) double integral, so
the split is **not** free: adding the two iterated integrals and merging them into one requires the
joint integrability of the two integrands.  That is supplied here by
`H2W.WeakAux.prod_integrable_mul` (Fubini + the arithmetic–geometric mean inequality against the
`ℋ⁰`-integrands of `AA u`, `U u`, `BB u`), which applies verbatim because `u` is `C^∞` on the open
quadrant (`AeData.smooth`, hence `SmoothOpen u`) so that `AA u`, `BB u`, `U u` and `cw · U u` are
continuous on `(0,∞) × (0,π/2)`, and because the three hypotheses `HkMem α 0` are honest.

The `z`-pairing `cw z = 2(z-1)/(1+z)` is bounded by `2` on `[0,∞)`, so `cw · U u` is again
`ℋ⁰`-honest (`HkMem_cw_mul`).

* `IP_repr` — the representation of the pairing as a single iterated integral over
  `(0,∞) × (0,π/2)` with `w²` pulled out; it is *hypothesis-free* (interval bookkeeping on null
  sets plus `integral_const_mul`);
* `HkMem_cw_mul` — `HkMem α 0 (cw · f)` from `HkMem α 0 f`;
* `IP_add_repr` — the target.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeI1Fts

set_option autoImplicit false

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-! ## Interval bookkeeping for `IP`

(The two lemmas below are *private*: `AeI1Fts/identity.lean` declares the same two statements
publicly under the same names, and both modules are in the cone of `AeI1Fts/identity_local.lean`
once `radial_identity` imports the assembled `radial_alt`; a duplicate public declaration there
is an error.  Nothing in this development uses the public names from this file.) -/




/-! ## `ℋ⁰`-honesty of `cw · f` -/

/-- **`cw` is bounded by `2` on `Iz`.** -/
theorem abs_cw_le_two_Iz {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    |Work.FTS.EllipticEst.AngSecond.cw z| ≤ 2 :=
  Work.FTS.EllipticEst.AngSecond.abs_cw_le_two (Set.mem_Ici.mp hz)


/-! ## The additive representation -/

local notation "Qd0" => Work.FTS.EllipticEst.H2W.WeakAux.Qd0
local notation "muP" => Work.FTS.EllipticEst.H2W.WeakAux.muP


end Work.FTS.EllipticEst.AeI1Fts
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.Upsi_P_ae_Aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Auxiliaries for `Upsi_P_integrable_ae`

The pointwise identity behind the target `Work.FTS.EllipticEst.AeI1Fts.Upsi_P_integrable_ae`:
for a datum `u` smooth on the open quadrant, a `C²` function `ψ` and a point `(z,θ)` of the open
quadrant, the derivative of the slice `θ' ↦ U u z θ' * ψ θ'` is

  `deriv (U u z · * ψ) θ = V u z θ * ψ θ + U u z θ * deriv ψ θ`,

where `U u = z ∂_z u` and `V u = z ∂_z∂_θ u` (which coincides with `∂_θ (U u)` on the quadrant,
`Work.FTS.EllipticEst.AeI1Fts.slice_deriv_eq`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeI1Fts

set_option autoImplicit false



end Work.FTS.EllipticEst.AeI1Fts
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.slice_theta_ibp_cut =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular integration by parts of the `I₁` chain against the cut-off `χ_ε`

Target: `Work.FTS.EllipticEst.AeI1Fts.slice_theta_ibp_cut`.  For a datum `u` smooth on the open
quadrant, `z > 0` and `ε > 0`,

```
∫_{0<θ<π/2} σ·χ_ε·(U·Hh) = -∫ σ·χ_ε·V² + 2η·∫ σ₁·χ_ε·(U·V·cos 2θ) - ∫ σ·χ_ε'·(U·V),
```

where `U = z∂_zu`, `V = z∂_z∂_θu`, `Hh = z∂_z∂_θθu`, `σ = sin(2θ)^{-η}`,
`σ₁ = sin(2θ)^{-1-η}`, `η = 99/100` and `χ_ε = SliceMixedAux.cut ε` is the smooth two-plateau
cut-off of `SliceMixedAux.smoothCutoffIoo`.

The proof is the integration by parts of the pointwise identity
`∂_θ(U·V·σ) = V²σ + U·Hh·σ - 2η·U·V·cos(2θ)·σ₁` (`hasDerivAt_theta_ident`) against `χ_ε`:
the antiderivative `G = χ_ε·(U·V·σ)` vanishes identically near both endpoints (because `χ_ε` does),
so `∫ G' = 0`, and expanding `G' = χ_ε'·(U·V·σ) + χ_ε·(V²σ + U·Hh·σ - 2η U·V cos(2θ)σ₁)` and
splitting the integral gives the claim.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeI1Fts

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Continuity of the two angular weights on the open interval -/



/-! ## Integrability on `(0,π/2)` of a function continuous on a compact subinterval and
vanishing outside it -/


/-! ## Vanishing of the derivative of the cut-off outside its plateau band -/



/-! ## The main lemma -/


end Work.FTS.EllipticEst.AeI1Fts
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.zibp_zouter =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `zibp_zouter` — the radial integration by parts against the angular weight

`AeI1Fts.zibp_cut` proves, for every fixed `θ ∈ (0,π/2)`, the cut-off radial integration by
parts

  `∫_z χ_n w² Fp u(·,θ) = -∫_z (z χ_n') (z∂_zu)(∂_θθu) w²`,

where `χ_n = EllipticEst.cut n` is supported in `[1/(n+1), 3(n+1)]`.  The target of this module
multiplies that identity by the angular weight `σ θ · χ_ε θ` (`σ = sigE = sin(2θ)^{-η}`,
`χ_ε = SliceMixedAux.cut ε`, supported in `[ε/2, π/2 - ε/2]`), integrates over `θ ∈ (0,π/2)`
and interchanges the two integrations:

  `∫_z χ_n w² ∫_θ σ χ_ε Fp u = -∫_z (z χ_n') w² ∫_θ σ χ_ε (U u · BB u)`.

Both `θ`-integrands are supported in the compact box
`[1/(2(n+1)), 4(n+1)] ×ˢ [ε/2, π/2 - ε/2]` lying in the open quadrant, where they are
continuous (`SmoothOpen u` makes every derivative slot used by `Fp` continuous), so the swap is
`iter_swap_compact`.
-/

namespace Work.FTS.EllipticEst.AeI1Fts

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000


/-! ## Elementary continuity facts on a compact box inside the open quadrant -/





/-! ## Vanishing of the two cut-offs off their bands -/

private theorem deriv_cut_eq_zero_of_lt (n : ℕ) {z : ℝ} (hz : z < 1 / (n + 1 : ℝ)) :
    deriv (Work.FTS.EllipticEst.cut n) z = 0 := by
  have hEq : (fun y : ℝ => Work.FTS.EllipticEst.cut n y) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds hz] with y hy
    exact Work.FTS.EllipticEst.cut_apply_zero_of_le n hy.le
  simpa using hEq.deriv_eq

private theorem deriv_cut_eq_zero_of_gt (n : ℕ) {z : ℝ} (hz : 3 * (n + 1 : ℝ) < z) :
    deriv (Work.FTS.EllipticEst.cut n) z = 0 := by
  have hEq : (fun y : ℝ => Work.FTS.EllipticEst.cut n y) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    exact Work.FTS.EllipticEst.cut_apply_zero_of_ge n hy.le
  simpa using hEq.deriv_eq

/-! ## The target -/


end

end Work.FTS.EllipticEst.AeI1Fts
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.aeSigmaEnergyOwn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false
set_option maxHeartbeats 3200000

local notation "sg" => Work.FTS.EllipticEst.sEta

/-! ## The angular weight and the level-`0` integrand -/

/-- The angular weight `σ = sin(2θ)^{-η} ≥ 1` on the open interval. -/
private theorem one_le_sEta_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ sg θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hc : (-(Work.Spaces.eta) : ℝ) ≤ 0 := by rw [Work.Spaces.eta]; norm_num
  have h := Real.rpow_le_rpow_of_nonpos hs h1 hc
  rw [Real.one_rpow] at h
  simpa only [Work.FTS.EllipticEst.sEta] using h

/-- `σ` is `C²` on the open interval. -/
private theorem contDiffOn_sEta_Ioo :
    ContDiffOn ℝ 2 (fun θ : ℝ => sg θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have hsin : ContDiffOn ℝ 2 (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).contDiffOn
  have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * θ) ≠ 0 := by
    intro θ hθ
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))
  have h := hsin.rpow (contDiffOn_const (c := -(Work.Spaces.eta))) (fun θ hθ => hne θ hθ)
  simpa only [Work.FTS.EllipticEst.sEta] using h

/-- `σ` is continuous on the open interval. -/
private theorem continuousOn_sEta_Ioo :
    ContinuousOn (fun θ : ℝ => sg θ) (Set.Ioo 0 (Real.pi / 2)) :=
  contDiffOn_sEta_Ioo.continuousOn

/-- `w z ≥ 1` for `z > 0`. -/
private theorem one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (pow_pos hz 2)]
  nlinarith [hz]

/-- The level-`0` integrand is `w(z)² · f² σ`. -/
private theorem HkIntegrand_eq (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (Work.Spaces.w z) ^ 2 * ((f z θ) ^ 2 * sg θ) :=
  Work.FTS.EllipticEst.Dispatch.HkIntegrand_zero_D α f hθ

/-! ## `HkSq α 0` as the `w²`-weighted slice integral -/




/-! ## Regularity of the radial weight `w²` -/

/-- `z ↦ w z ^ 2` is `C²` on `(0,∞)`. -/
private theorem contDiffOn_w_sq_two :
    ContDiffOn ℝ 2 (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have h1 : ContDiffOn ℝ 2 (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0) := by
    refine ContDiffOn.div ?_ ?_ ?_
    · exact (contDiffOn_const.add contDiffOn_id).pow 2
    · exact contDiffOn_id.pow 2
    · intro z hz; exact pow_ne_zero 2 (ne_of_gt hz)
  have h2 := h1.pow 2
  rw [show (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      = (fun z : ℝ => ((1 + z) ^ 2 / z ^ 2)) ^ 2 by
    funext y; simp only [Pi.pow_apply]; rw [Work.Spaces.w]]
  exact h2






/-! ## The proved truncated `σ`-identity with its honesty hypotheses discharged -/

/-- `|a b| ≤ (a² + b²)/2`. -/
private theorem abs_mul_le_half {a b : ℝ} : |a * b| ≤ (1 / 2) * (a ^ 2 + b ^ 2) := by
  have h := abs_mul a b
  nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]






/-! ## The assembly: from the truncated identity to the untruncated estimate -/


/-- A weighted comparison bound: a coefficient bounded by `C w²` pairs against a nonnegative
slice mass. -/
private theorem weighted_le_of_bound {c m : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hmint : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * m z) Work.Spaces.Iz)
    (hmnn : ∀ z, 0 ≤ m z)
    (hbound : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      |c z| ≤ C * (Work.Spaces.w z) ^ 2) :
    |∫ z in Work.Spaces.Iz, c z * m z| ≤ C * (∫ z in Work.Spaces.Iz,
      (Work.Spaces.w z) ^ 2 * m z) := by
  have hstep1 : |∫ z in Work.Spaces.Iz, c z * m z|
      ≤ ∫ z in Work.Spaces.Iz, |c z * m z| := by
    simpa only [Real.norm_eq_abs] using
      MeasureTheory.norm_integral_le_integral_norm (fun z => c z * m z)
  have hint : MeasureTheory.IntegrableOn
      (fun z => C * ((Work.Spaces.w z) ^ 2 * m z)) Work.Spaces.Iz := hmint.const_mul C
  have hstep2 : (∫ z in Work.Spaces.Iz, |c z * m z|)
      ≤ ∫ z in Work.Spaces.Iz, C * ((Work.Spaces.w z) ^ 2 * m z) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => abs_nonneg _) hint ?_
    filter_upwards [hbound] with z hz
    rw [abs_mul]
    calc |c z| * |m z| ≤ (C * (Work.Spaces.w z) ^ 2) * m z :=
          mul_le_mul hz (by rw [abs_of_nonneg (hmnn z)]) (abs_nonneg _)
            (mul_nonneg hC (sq_nonneg _))
      _ = C * ((Work.Spaces.w z) ^ 2 * m z) := by ring
  have hsplit : (∫ z in Work.Spaces.Iz, C * ((Work.Spaces.w z) ^ 2 * m z))
      = C * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * m z) :=
    MeasureTheory.integral_const_mul C _
  linarith [hstep1, hstep2, hsplit]







/-! ## The final assembly -/


/-- Almost every point of `Iz` is positive. -/
private theorem ae_pos_of_mem_Iz :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
  rw [Work.Spaces.Iz, MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioi



end Work.FTS.EllipticEst.AngAWeak
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Deleg.mixedPairLimit =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Deleg

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-! ## The five limits -/

theorem tendsto_Ptr {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (hM : MixedHon u) (n : ℕ) :
    Tendsto (fun δ : ℝ => Work.FTS.EllipticEst.AeColl.Ptr u n δ)
      (𝓝[>] (0 : ℝ)) (𝓝 (Work.FTS.EllipticEst.AeColl.Pcut u n)) := by
  have hmain := psiDIntegralLimitAlt
    (c := fun z => Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z)
    (G := fun z θ => Work.FTS.EllipticEst.AeColl.sigθ θ
      * Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2)
    (aesm_cut_mul_wt n) (aesm_joint_Vz hA) (integrableOn_slice_of_MixedHon hM)
    (hdom_Vz hA hM n)
  have hval : (∫ z, (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z) *
      (∫ θ, (Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2)
        ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      ∂(volume.restrict (Set.Ioi (0 : ℝ)))) = Work.FTS.EllipticEst.AeColl.Pcut u n := by
    rw [Work.FTS.EllipticEst.AeColl.Pcut]
  rw [hval] at hmain
  refine Filter.Tendsto.congr' ?_ hmain
  refine Filter.Eventually.of_forall (fun δ => ?_)
  simp only [Work.FTS.EllipticEst.AeColl.Ptr]
  refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ _
  ring

theorem tendsto_Atr {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)) (n : ℕ) :
    Tendsto (fun δ : ℝ => Work.FTS.EllipticEst.AeColl.Atr u n δ)
      (𝓝[>] (0 : ℝ)) (𝓝 (Work.FTS.EllipticEst.AeColl.Acut u n)) := by
  have hGz : Filter.Eventually (fun z => Integrable (fun θ =>
      Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      (ae (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    exact integrableOn_sig_mul_sq_of_HkMem α hU hz
  have hmain := psiDIntegralLimitAlt
    (c := fun z => Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z)
    (G := fun z θ => Work.FTS.EllipticEst.AeColl.sigθ θ
      * Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2)
    (aesm_cut_mul_wt n) (aesm_joint_Uz hA) hGz (hdom_Uz hA hU n)
  have hval : (∫ z, (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z) *
      (∫ θ, (Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2)
        ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      ∂(volume.restrict (Set.Ioi (0 : ℝ)))) = Work.FTS.EllipticEst.AeColl.Acut u n := by
    rw [Work.FTS.EllipticEst.AeColl.Acut]
  rw [hval] at hmain
  refine Filter.Tendsto.congr' ?_ hmain
  refine Filter.Eventually.of_forall (fun δ => ?_)
  simp only [Work.FTS.EllipticEst.AeColl.Atr]
  refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ _
  ring

theorem tendsto_Dtr {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (n : ℕ) :
    Tendsto (fun δ : ℝ => Work.FTS.EllipticEst.AeColl.Dtr u n δ)
      (𝓝[>] (0 : ℝ)) (𝓝 (Work.FTS.EllipticEst.AeColl.Dcut u n)) := by
  have hGz : Filter.Eventually (fun z => Integrable (fun θ =>
      Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Az u z θ
        * Work.Spaces.pthIter 2 u z θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      (ae (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    refine integrableOn_sig_mul_mul_of_HkMem α
      (Work.FTS.EllipticEst.H2W.Ae.AeData.memRad2 hA)
      (Work.FTS.EllipticEst.H2W.Ae.AeData.memAng2 hA) hz ?_
    exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ (continuousOn_joint_AzB hA) hz
  have hmain := psiDIntegralLimitAlt
    (c := fun z => Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z)
    (G := fun z θ => Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Az u z θ
      * Work.Spaces.pthIter 2 u z θ)
    (aesm_cut_mul_wt n) (aesm_prod_of_continuousOn_Q0 (continuousOn_joint_AzB hA)) hGz
    (hdom_AzB hA n)
  have hval : (∫ z, (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z) *
      (∫ θ, (Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Az u z θ
        * Work.Spaces.pthIter 2 u z θ) ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      ∂(volume.restrict (Set.Ioi (0 : ℝ)))) = Work.FTS.EllipticEst.AeColl.Dcut u n := by
    rw [Work.FTS.EllipticEst.AeColl.Dcut]
    refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
    rw [show (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.cut n z
          * Work.FTS.EllipticEst.AeColl.wt z
          * Work.FTS.EllipticEst.AeColl.sigθ θ * (Work.FTS.EllipticEst.AeColl.Az u z θ)
          * (Work.Spaces.pthIter 2 u z θ))
        = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z)
              * (Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Az u z θ
                * Work.Spaces.pthIter 2 u z θ) from
      integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))]
    rw [MeasureTheory.integral_const_mul]
  rw [hval] at hmain
  refine Filter.Tendsto.congr' ?_ hmain
  refine Filter.Eventually.of_forall (fun δ => ?_)
  simp only [Work.FTS.EllipticEst.AeColl.Dtr]
  refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
  rw [show (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.cut n z
        * Work.FTS.EllipticEst.AeColl.wt z
        * Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.psiD δ θ
        * (Work.FTS.EllipticEst.AeColl.Az u z θ) * (Work.Spaces.pthIter 2 u z θ))
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z)
            * (Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.psiD δ θ
              * (Work.FTS.EllipticEst.AeColl.Az u z θ)
              * (Work.Spaces.pthIter 2 u z θ)) from
    integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ _
  ring

theorem tendsto_Trtr {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)) (n : ℕ) :
    Tendsto (fun δ : ℝ => Work.FTS.EllipticEst.AeColl.Trtr u n δ)
      (𝓝[>] (0 : ℝ)) (𝓝 (Work.FTS.EllipticEst.AeColl.Trcut u n)) := by
  have hGz : Filter.Eventually (fun z => Integrable (fun θ =>
      Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ
        * Work.Spaces.pthIter 2 u z θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      (ae (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    refine integrableOn_sig_mul_mul_of_HkMem α hU
      (Work.FTS.EllipticEst.H2W.Ae.AeData.memAng2 hA) hz ?_
    exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ (continuousOn_joint_UzB hA) hz
  have hmain := psiDIntegralLimitAlt
    (c := fun z => deriv (fun z' => Work.FTS.EllipticEst.cut n z'
      * Work.FTS.EllipticEst.AeColl.wt z' * z' ^ 2) z / z)
    (G := fun z θ => Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ
      * Work.Spaces.pthIter 2 u z θ)
    (aesm_trtr_coef n) (aesm_prod_of_continuousOn_Q0 (continuousOn_joint_UzB hA)) hGz
    (hdom_UzB hA hU n)
  have hval : (∫ z, (deriv (fun z' => Work.FTS.EllipticEst.cut n z'
        * Work.FTS.EllipticEst.AeColl.wt z' * z' ^ 2) z / z) *
      (∫ θ, (Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ
        * Work.Spaces.pthIter 2 u z θ) ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      ∂(volume.restrict (Set.Ioi (0 : ℝ)))) = Work.FTS.EllipticEst.AeColl.Trcut u n := by
    rw [Work.FTS.EllipticEst.AeColl.Trcut]
    refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
    rw [show (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          deriv (fun z' => Work.FTS.EllipticEst.cut n z'
            * Work.FTS.EllipticEst.AeColl.wt z' * z' ^ 2) z / z
          * Work.FTS.EllipticEst.AeColl.sigθ θ * (Work.FTS.EllipticEst.AeColl.Uz u z θ)
          * (Work.Spaces.pthIter 2 u z θ))
        = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (deriv (fun z' => Work.FTS.EllipticEst.cut n z'
              * Work.FTS.EllipticEst.AeColl.wt z' * z' ^ 2) z / z)
              * (Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ
                * Work.Spaces.pthIter 2 u z θ) from
      integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))]
    rw [MeasureTheory.integral_const_mul]
  rw [hval] at hmain
  refine Filter.Tendsto.congr' ?_ hmain
  refine Filter.Eventually.of_forall (fun δ => ?_)
  simp only [Work.FTS.EllipticEst.AeColl.Trtr]
  refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
  rw [show (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        deriv (fun z' => Work.FTS.EllipticEst.cut n z'
          * Work.FTS.EllipticEst.AeColl.wt z' * z' ^ 2) z / z
        * Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.psiD δ θ
        * (Work.FTS.EllipticEst.AeColl.Uz u z θ) * (Work.Spaces.pthIter 2 u z θ))
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (deriv (fun z' => Work.FTS.EllipticEst.cut n z'
            * Work.FTS.EllipticEst.AeColl.wt z' * z' ^ 2) z / z)
            * (Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.psiD δ θ
              * (Work.FTS.EllipticEst.AeColl.Uz u z θ)
              * (Work.Spaces.pthIter 2 u z θ)) from
    integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ _
  ring

theorem tendsto_Col {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (hM : MixedHon u) (n : ℕ) :
    Tendsto (fun δ : ℝ => Work.FTS.EllipticEst.AeColl.Col u n δ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hGnn : ∀ z θ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) → 0 ≤
      Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2 :=
    fun z θ hθ => mul_nonneg
      (le_of_lt (sigθ_pos_of_mem_Ioo hθ)) (sq_nonneg _)
  have hmain := psiDLayerLimit
    (c := fun z => Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z)
    (G := fun z θ => Work.FTS.EllipticEst.AeColl.sigθ θ
      * Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2)
    (aesm_cut_mul_wt n) (aesm_joint_Vz hA) (integrableOn_slice_of_MixedHon hM) hGnn
    (hdom_Vz hA hM n)
  refine Filter.Tendsto.congr' ?_ hmain
  refine Filter.Eventually.of_forall (fun δ => ?_)
  simp only [Work.FTS.EllipticEst.AeColl.Col]

/-! ## The assembly -/

theorem mixedPairLimit (Cw : ℝ) (hCw : 0 < Cw) :
    Work.FTS.EllipticEst.Deleg.PairLimit Cw := by
  intro α u G hA hU hM K hK _hR hpair n
  have h1 := tendsto_Ptr hA hM n
  have h2 := tendsto_Atr hA hU n
  have h3 := tendsto_Dtr hA n
  have h4 := tendsto_Trtr hA hU n
  have h5 := tendsto_Col hA hM n
  have hL : Tendsto (fun δ : ℝ => kap * Work.FTS.EllipticEst.AeColl.Ptr u n δ)
      (𝓝[>] (0 : ℝ)) (𝓝 (kap * Work.FTS.EllipticEst.AeColl.Pcut u n)) :=
    h1.const_mul kap
  have hR : Tendsto (fun δ : ℝ => Work.FTS.EllipticEst.AeColl.Dtr u n δ
        + Work.FTS.EllipticEst.AeColl.Trtr u n δ
        - 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AeColl.Atr u n δ
        + Cw * K * Work.FTS.EllipticEst.AeColl.Col u n δ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Work.FTS.EllipticEst.AeColl.Dcut u n + Work.FTS.EllipticEst.AeColl.Trcut u n
        - 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AeColl.Acut u n + Cw * K * 0)) :=
    (((h3.add h4).sub (h2.const_mul (2 * Work.Spaces.eta))).add (h5.const_mul (Cw * K)))
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), kap * Work.FTS.EllipticEst.AeColl.Ptr u n δ
      ≤ Work.FTS.EllipticEst.AeColl.Dtr u n δ + Work.FTS.EllipticEst.AeColl.Trtr u n δ
        - 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AeColl.Atr u n δ
        + Cw * K * Work.FTS.EllipticEst.AeColl.Col u n δ := by
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < Real.pi / 16 by linarith [Real.pi_pos])]
      with δ hδ
    exact hpair n δ hδ.1 (by linarith [hδ.2, Real.pi_pos])
  have hfin := le_of_tendsto_of_tendsto hL hR hev
  simpa using hfin

end

end Work.FTS.EllipticEst.Deleg
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Final.ReHome.M4_s20_honesty =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.Step5

open MeasureTheory Set Filter

/-! ## The honesty of the two dominating pieces of the top angular slot at level `2`

The datum `Ψ` of the weak class `TT.EllWeakPos α 2 F Ψ` is only required to be smooth on the
*open* quadrant, with the two `H²`-memberships of `F` and of `∂_θθΨ`; in particular the level-`2`
integrand of `∂_θθΨ` is honest.  Writing `H := ∂_θθΨ`, the `(i,j) = (2,0)` and `(1,0)` summands
of `HkIntegrand α 2 H` are the weighted squares of

  `D_θ²H = sin(2θ)· (2cos(2θ)·∂_θH + sin(2θ)·∂_θ²H)` and `D_θH = sin(2θ)·∂_θH`,

and the two quantities `F₄ = 2w²(∂_θ⁴Ψ)²σ₄` and `F₃ = 8w²(∂_θ³Ψ)²σ₂` are recovered from them by
inverting the triangular relation

  `sin(2θ)·∂_θ²H = D_θ²H / sin(2θ) - 2cos(2θ)·∂_θH`,

which costs only the numerical factor `20 = 4 + 16` (resp. `8`).  Hence both pieces are honest as
soon as `∂_θθΨ ∈ ℋ²`, which is a field of the hypothesis class.  This is the "honesty" input of
the level-`2` Step-5 estimate, and it needs no use of the equation, of the moment conditions or of
the honesty of `F`: only the `ℋ²`-field of `∂_θθΨ` (together with the a.e.-measurability of the
integrands, which is `s20Aesm`). -/

/-- **The weight identity behind the top slot.**  With `Wt α z θ = w z · sin(2θ)^{-γ/2}` and
`σ₄ = sin(2θ)^{4-γ}`,

  `2 w(z)² (∂_θ⁴Ψ z θ)² σ₄(θ) = 2 (sin(2θ)² · ∂_θ⁴Ψ z θ · Wt α z θ)²`.

The right-hand side is the square of a `(2,0)`-shaped expression, so that the two `HkIntegrand`
summands can be combined with it. -/
theorem s20F4_eq_sq (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ
      = 2 * (Real.sin (2 * θ) ^ 2 * Work.Spaces.pthIter 4 Ψ z θ
              * Work.Spaces.Wt α z θ) ^ 2 := by
  have hs : 0 ≤ Real.sin (2 * θ) := Work.Spaces.bt_sin_nonneg hθ
  have hgam4 : Work.Spaces.gam α ≠ 4 := by
    rw [Work.Spaces.gam]; intro h; linarith
  have hne : (4 : ℝ) + -(Work.Spaces.gam α) ≠ 0 := by
    intro h; exact hgam4 (by linarith)
  have hXc : Real.sin (2 * θ) ^ (4 - Work.Spaces.gam α)
      = Real.sin (2 * θ) ^ (4 : ℕ) * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) := by
    rw [show (4 : ℝ) - Work.Spaces.gam α = (4 : ℝ) + -(Work.Spaces.gam α) from by ring,
        Real.rpow_add' hs hne]
    rw [show Real.sin (2 * θ) ^ (4 : ℝ) = Real.sin (2 * θ) ^ (4 : ℕ) from
      Real.rpow_natCast _ 4]
  rw [Work.FTS.EllipticEst.H2W.s20F4, Work.FTS.EllipticEst.Mine.sig4]
  change 2 * (Work.Spaces.w z) ^ 2
      * (Work.Spaces.pthIter 4 Ψ z θ ^ 2 * (Real.sin (2 * θ) ^ (4 - Work.Spaces.gam α)))
    = 2 * (Real.sin (2 * θ) ^ 2 * Work.Spaces.pthIter 4 Ψ z θ * Work.Spaces.Wt α z θ) ^ 2
  rw [hXc, mul_pow, Work.Spaces.bt_Wt_sq α z θ hα hθ]
  ring

/-- The vanishing of `s20F4` at the two angular endpoints (`σ₄` carries the factor
`sin(2θ)^{4-γ}` and `4 - γ ≠ 0` for `γ = 1 + α/10 ≤ 5/4`). -/
theorem s20F4_eq_zero_theta_zero (α : ℝ) (hα4 : α ≤ 1 / 4) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.FTS.EllipticEst.H2W.s20F4 α Ψ z 0 = 0 := by
  have hpos : 0 < 4 - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  rw [Work.FTS.EllipticEst.H2W.s20F4, Work.FTS.EllipticEst.Mine.sig4]
  rw [show (2 : ℝ) * 0 = 0 from by ring, Real.sin_zero]
  change 2 * Work.Spaces.w z ^ 2
      * (Work.Spaces.pthIter 4 Ψ z 0 ^ 2 * (0 : ℝ) ^ (4 - Work.Spaces.gam α)) = 0
  rw [Real.zero_rpow (ne_of_gt hpos)]
  ring

/-- Vanishing of `s20F4` at `θ = π/2`. -/
theorem s20F4_eq_zero_theta_pi (α : ℝ) (hα4 : α ≤ 1 / 4) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.FTS.EllipticEst.H2W.s20F4 α Ψ z (Real.pi / 2) = 0 := by
  have hpos : 0 < 4 - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  rw [Work.FTS.EllipticEst.H2W.s20F4, Work.FTS.EllipticEst.Mine.sig4]
  rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi]
  change 2 * Work.Spaces.w z ^ 2
      * (Work.Spaces.pthIter 4 Ψ z (Real.pi / 2) ^ 2
          * (0 : ℝ) ^ (4 - Work.Spaces.gam α)) = 0
  rw [Real.zero_rpow (ne_of_gt hpos)]
  ring

/-- Vanishing of `s20F4` at `z = 0` (the radial weight `w` vanishes there). -/
theorem s20F4_eq_zero_z (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.FTS.EllipticEst.H2W.s20F4 α Ψ 0 θ = 0 := by
  rw [Work.FTS.EllipticEst.H2W.s20F4, Work.Spaces.w]
  norm_num

/-- **The pointwise domination on the open quadrant.**  With `H := ∂_θθΨ`,
`D_θ²H = sin²(2θ)∂_θ²H + 2sin(2θ)cos(2θ)∂_θH`, so `sin(2θ)∂_θ²H` is a difference of `D_θ²H/sin(2θ)`
and `2cos(2θ)∂_θH`; squaring with `(a-b)² ≤ 2a² + 2b²`, using `|cos| ≤ 1` and multiplying by
`w²sin(2θ)^{-γ}` turns `F₄` into at most `4` times the `(2,0)` summand plus `16` times the `(1,0)`
summand of `HkIntegrand α 2 H`. -/
theorem s20F4_le_of_int (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (Ψ : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ)
    (hdiff : DifferentiableAt ℝ (fun t => deriv (fun t' => Work.Spaces.pthIter 2 Ψ z t') t) θ) :
    Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ
      ≤ 20 * Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ := by
  have hmain := s20F4_eq_sq α hα hα4 Ψ z θ hθ
  have hE : Work.Spaces.mixed 0 2 (Work.Spaces.pthIter 2 Ψ) z θ * Work.Spaces.Wt α z θ
      = Real.sin (2 * θ) ^ 2 * Work.Spaces.pthIter 4 Ψ z θ * Work.Spaces.Wt α z θ
        + 2 * Real.cos (2 * θ) * (Real.sin (2 * θ) * Work.Spaces.pthIter 3 Ψ z θ
            * Work.Spaces.Wt α z θ) := by
    have h := Work.FTS.EllipticEst.H2W.DthIter_two_eq_pth (Work.Spaces.pthIter 2 Ψ) z θ hdiff
    have h2 : Work.Spaces.pthIter 2 (Work.Spaces.pthIter 2 Ψ) z θ
        = Work.Spaces.pthIter 4 Ψ z θ := rfl
    have h1 : Work.Spaces.pth (Work.Spaces.pthIter 2 Ψ) z θ
        = Work.Spaces.pthIter 3 Ψ z θ := rfl
    show Work.Spaces.DthIter 2 (Work.Spaces.pthIter 2 Ψ) z θ * Work.Spaces.Wt α z θ = _
    rw [h, h2, h1]; ring
  have hQ : Work.Spaces.mixed 0 1 (Work.Spaces.pthIter 2 Ψ) z θ * Work.Spaces.Wt α z θ
      = Real.sin (2 * θ) * Work.Spaces.pthIter 3 Ψ z θ * Work.Spaces.Wt α z θ := rfl
  have h1 := Work.Spaces.sq_le_HkIntegrand_mixed α 2 (Work.Spaces.pthIter 2 Ψ) z θ 2 0
    (by norm_num) (by norm_num)
  have h2 := Work.Spaces.sq_le_HkIntegrand_mixed α 2 (Work.Spaces.pthIter 2 Ψ) z θ 1 0
    (by norm_num) (by norm_num)
  set U : ℝ := Real.sin (2 * θ) ^ 2 * Work.Spaces.pthIter 4 Ψ z θ * Work.Spaces.Wt α z θ
    with hU
  set V : ℝ := 2 * Real.cos (2 * θ) * (Real.sin (2 * θ) * Work.Spaces.pthIter 3 Ψ z θ
    * Work.Spaces.Wt α z θ) with hV
  set Q : ℝ := Real.sin (2 * θ) * Work.Spaces.pthIter 3 Ψ z θ * Work.Spaces.Wt α z θ with hQd
  have h1' : (U + V) ^ 2 ≤ Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ := by
    rw [← hE]; exact h1
  have h2' : Q ^ 2 ≤ Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ := by
    rw [← hQ]; exact h2
  have hc2 : Real.cos (2 * θ) ^ 2 ≤ 1 := by
    nlinarith [Real.cos_sq_add_sin_sq (2 * θ), sq_nonneg (Real.sin (2 * θ))]
  have hv : V ^ 2 ≤ 4 * Q ^ 2 := by rw [hV]; nlinarith [hc2, sq_nonneg Q]
  have hu : U ^ 2 ≤ 2 * (U + V) ^ 2 + 2 * V ^ 2 := by nlinarith [sq_nonneg (U + 2 * V)]
  rw [hmain]; linarith

/-- **The pointwise domination, everywhere on `Iz × Iθ`.**  At the angular endpoints and at
`z = 0` both sides are nonnegative with `s20F4` vanishing; in the interior
`s20F4_le_of_int` applies with the differentiability of the `∂_θ²`-slice supplied by the
smoothness of `Ψ` on the open quadrant. -/
theorem s20F4_le_HkIntegrand (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) {Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ
      ≤ 20 * Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ := by
  have hnn : (0 : ℝ) ≤ 20 * Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ :=
    mul_nonneg (by norm_num) (Work.Spaces.HkIntegrand_nonneg α 2 _ z θ)
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
  · have h0 : Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ = 0 := by
      rw [← hz0]; exact s20F4_eq_zero_z α Ψ θ
    rw [h0]; exact hnn
  · rcases eq_or_lt_of_le hθ.1 with hθ0 | hθpos
    · have h0 : Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ = 0 := by
        rw [← hθ0]; exact s20F4_eq_zero_theta_zero α hα4 Ψ z
      rw [h0]; exact hnn
    · rcases eq_or_lt_of_le hθ.2 with hθ2 | hθlt
      · have h0 : Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ = 0 := by
          rw [hθ2]; exact s20F4_eq_zero_theta_pi α hα4 Ψ z
        rw [h0]; exact hnn
      · exact s20F4_le_of_int α hα hα4 Ψ ⟨le_of_lt hθpos, le_of_lt hθlt⟩
          (Work.FTS.EllipticEst.H2W.slice_diff2 hsm hzpos θ ⟨hθpos, hθlt⟩)

/-- `F₃ ≤ 8 · HkIntegrand α 2 (∂_θθΨ)`: the `(1,0)`-summand of the level-`2` integrand of
`∂_θθΨ` is exactly `w²sin(2θ)^{2-γ}(∂_θ³Ψ)²`, which is `F₃/8`. -/
theorem s20F3_le_HkIntegrand (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (Ψ : ℝ → ℝ → ℝ)
    (z : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ
      ≤ 8 * Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ := by
  rw [Work.FTS.EllipticEst.H2W.s20F3_eq α hα hα4 Ψ hθ z]
  exact mul_le_mul_of_nonneg_left
    (Work.Spaces.sq_le_HkIntegrand_mixed α 2 (Work.Spaces.pthIter 2 Ψ) z θ 1 0
      (by norm_num) (by norm_num)) (by norm_num)

/-- Nonnegativity of the step-5 piece. -/
theorem s20F4_nonneg (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ := by
  rw [Work.FTS.EllipticEst.H2W.s20F4, Work.FTS.EllipticEst.Mine.sig4]
  exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Work.Spaces.bt_sin_nonneg hθ) _))

/-- Nonnegativity of the step-4 piece. -/
theorem s20F3_nonneg (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ := by
  rw [Work.FTS.EllipticEst.H2W.s20F3, Work.FTS.EllipticEst.Mine.sig2]
  exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Work.Spaces.bt_sin_nonneg hθ) _))

theorem s20_honesty : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      (∀ z ∈ Work.Spaces.Iz,
        MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ)
          Work.Spaces.Iθ) ∧
      MeasureTheory.Integrable
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
      (∀ z ∈ Work.Spaces.Iz,
        MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ)
          Work.Spaces.Iθ) ∧
      MeasureTheory.Integrable
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  intro α F Ψ hα hα4 h
  have hsm := h.smooth
  have hmem := h.memB
  obtain ⟨haesm4, haesm3, haesm4z, haesm3z⟩ := s20Aesm α Ψ hsm
  -- the two pointwise dominations of the level-`2` integrand of `∂_θθΨ`
  have hle4 : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ
        ≤ 20 * Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ :=
    fun z hz θ hθ => s20F4_le_HkIntegrand α hα hα4 hsm hz hθ
  have hle3 : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ
        ≤ 8 * Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ :=
    fun z hz θ hθ => s20F3_le_HkIntegrand α hα hα4 Ψ z hθ
  have hnn4 : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      0 ≤ Work.FTS.EllipticEst.H2W.s20F4 α Ψ z θ :=
    fun z _ θ hθ => s20F4_nonneg α Ψ z hθ
  have hnn3 : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      0 ≤ Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ :=
    fun z _ θ hθ => s20F3_nonneg α Ψ z hθ
  -- the majorants are honest, being constant multiples of the level-`2` integrand
  have hMsl20 : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => 20 * Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ)
      Work.Spaces.Iθ :=
    fun z hz => (hmem.1 z hz).const_mul 20
  have hMsl8 : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => 8 * Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ)
      Work.Spaces.Iθ :=
    fun z hz => (hmem.1 z hz).const_mul 8
  have hMz20 : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      20 * Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ)
      Work.Spaces.Iz := by
    refine (show MeasureTheory.Integrable (fun z => 20 * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) from hmem.2.const_mul 20).congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [MeasureTheory.integral_const_mul]
  have hMz8 : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      8 * Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ)
      Work.Spaces.Iz := by
    refine (show MeasureTheory.Integrable (fun z => 8 * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) from hmem.2.const_mul 8).congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [MeasureTheory.integral_const_mul]
  obtain ⟨h4θ, h4z⟩ := integrable_of_majorant haesm4 haesm4z hMsl20 hMz20 hnn4 hle4
  obtain ⟨h3θ, h3z⟩ := integrable_of_majorant haesm3 haesm3z hMsl8 hMz8 hnn3 hle3
  exact ⟨h4θ, h4z, h3θ, h3z⟩

end Work.FTS.EllipticEst.H2W.Step5
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.ESV.MassBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.Pieces.AeGradRho

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false

/-! ## Two elementary facts -/

/-- The restriction of Lebesgue measure to `Iz = [0,∞)` is that to `(0,∞)`: the two sets differ
by the null singleton `{0}`. -/
private lemma restrict_Iz_eq_restrict_Ioi :
    (MeasureTheory.volume.restrict Work.Spaces.Iz)
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
  rw [Work.Spaces.Iz]
  exact MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ))).symm

/-- The angular weight `σ = sin(2θ)^{-η}` dominates `1` off the two endpoints. -/
private lemma one_le_sEta {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hc : (-(Work.Spaces.eta) : ℝ) ≤ 0 := by
    rw [Work.Spaces.eta]; norm_num
  have h := Real.rpow_le_rpow_of_nonpos hs h1 hc
  rw [Real.one_rpow] at h
  simpa only [Work.FTS.EllipticEst.sEta] using h

/-- `ofReal` of a nonnegative Bochner integral is dominated by the `lintegral` of its `ofReal`,
for any function (no measurability needed: a non-strongly-measurable function has integral `0`). -/
private lemma ofReal_integral_le_lintegral' {μ : MeasureTheory.Measure ℝ} {f : ℝ → ℝ}
    (hnn : ∀ θ, 0 ≤ f θ) :
    ENNReal.ofReal (∫ θ, f θ ∂μ) ≤ ∫⁻ θ, ENNReal.ofReal (f θ) ∂μ := by
  by_cases h : MeasureTheory.AEStronglyMeasurable f μ
  · rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnn) h]
    exact ENNReal.ofReal_toReal_le
  · rw [MeasureTheory.integral_undef (fun hi => h hi.aestronglyMeasurable)]
    simp

/-! ## The `HkSq α 0`-mass of `u` against the `σ`-mass -/

/-- For `u` whatsoever, `ofReal (HkSq α 0 u)` is dominated by the `σ`-weighted angular mass
of `u`. -/
private theorem ofReal_HkSq_le_sigmaMass (α : ℝ) {u : ℝ → ℝ → ℝ} :
    ENNReal.ofReal (Work.Spaces.HkSq α 0 u) ≤
      ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
  have step1 : ENNReal.ofReal (∫ z in Work.Spaces.Iz,
        ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
      ≤ ∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ) :=
    ofReal_integral_le_lintegral'
      (fun z => integral_nonneg (fun θ => Work.Spaces.HkIntegrand_nonneg α 0 u z θ))
  have step2 : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ))
      ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 u z θ) :=
    MeasureTheory.lintegral_mono
      (fun z => ofReal_integral_le_lintegral'
        (fun θ => Work.Spaces.HkIntegrand_nonneg α 0 u z θ))
  have step3 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 u z θ))
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
    refine MeasureTheory.lintegral_congr (fun z => ?_)
    have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 u z θ)
          = ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
        rw [Work.FTS.EllipticEst.H2W.AeU2.HkIntegrand_zero_eq α u hθ,
          ENNReal.ofReal_mul (sq_nonneg _)])
    rw [MeasureTheory.lintegral_congr_ae hae,
      MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ENNReal.ofReal (Work.Spaces.HkSq α 0 u)
      = ENNReal.ofReal (∫ z in Work.Spaces.Iz,
          ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ) := by
        rw [Work.Spaces.HkSq]
    _ ≤ _ := step1
    _ ≤ _ := step2
    _ = _ := step3

/-- Almost every point of `Iθ = [0,π/2]` lies in the open interval `(0,π/2)`. -/
private lemma ae_mem_Ioo_Iθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
    θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [Work.Spaces.Iθ, ← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := Real.pi / 2))]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

end

/-- **The `u`-mass bound of Step 1 of `prop:H2` in the `AeData` class**, from the paper's
`w²`-weighted radial energy inequality (★) — the statement of
`Work.FTS.EllipticEst.H2W.AeProof.AeEnergyExpl` / `Cores.Pieces.AeGradRho.ae_w2_energy` — taken
here as the hypothesis `hW2`.

Chain: (★) plus the constrained slice gap `9∫u² ≤ ∫(∂_θu)²` (a.e. in `z`) gives
`9 Mc ≤ Bc ≤ K Mc + ½ HkSq α 0 G` with `K = 13/2 + 3α² + (3/2)α(5+α) ≤ 8.7 < 9`, hence
`Bc ≤ 30·(½ HkSq α 0 G)` and `Mc` is finite; the `σ`-upgrade
`AeSigmaUpgradeU_all` bounds the `σ`-mass `Sc` by `Cσ·Bc`, and the bridge
`ofReal_HkSq_le_sigmaMass` identifies `ofReal (HkSq α 0 u)` with at most `Sc`. -/
theorem ae_mass_bound_of
    (hW2 : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      ENNReal.ofReal (α ^ 2) * (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((z * Work.Spaces.pz u z θ) ^ 2)))
        + (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)))
      ≤ ENNReal.ofReal (13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α)))
          * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)))
        + ENNReal.ofReal (1 / 2) * ENNReal.ofReal (Work.Spaces.HkSq α 0 G)) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.FTS.EllipticEst.H2W.Ae.nrm α u ≤ C * Work.FTS.EllipticEst.H2W.Ae.nrm α G := by
  obtain ⟨Cσ, hCσpos, hσup⟩ := Work.FTS.EllipticEst.H2W.AeProof.AeSigmaUpgradeU_all
  obtain ⟨C₂, hC₂pos, hC₂⟩ := Work.FTS.EllipticEst.H2W.AeU2.aeU2_bound
  refine ⟨Real.sqrt (Cσ * 30 * (1 / 2)), Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro α u G h
  -- ## the a.e. fibre data
  have hL0 := Work.FTS.EllipticEst.H2W.AeLeftClean.sliceLeftTendstoClean α u G h
  have hC := Work.FTS.EllipticEst.H2W.AeProof.ae_continuousOn_slice h hL0
  have hLπ : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
        (nhds 0) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz
    exact (Work.FTS.EllipticEst.H2W.AeProof.AeSliceRightTendsto α u G h z hz).1
  have hint : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pth u z θ) ^ 2) Work.Spaces.Iθ := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz
    exact Work.FTS.EllipticEst.AngAWeak.integrableOn_pth_sq_of_AeData_esv α u G h z hz
  -- ## the constrained slice gap, a.e. in `z`
  have hgap := Work.FTS.EllipticEst.H2W.AeProof.AeGapSlices α u G h hC hint
  -- ## the radial energy inequality
  have hEn := hW2 α u G h
  -- ## the three masses
  set Mc : ℝ≥0∞ := ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
      * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)) with hMc
  set Bc : ℝ≥0∞ := ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
      * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)) with hBc
  set Sc : ℝ≥0∞ := ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
      * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) with hSc
  -- ## the `σ`-mass is finite, and dominates `Mc`
  have hSc_fin : Sc ≤ ENNReal.ofReal C₂
      * ENNReal.ofReal (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u)) := by
    rw [hSc, restrict_Iz_eq_restrict_Ioi]
    exact hC₂ α u G h hL0
  have hSc_ne_top : Sc ≠ ⊤ := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hSc_fin
  have hMc_le_Sc : Mc ≤ Sc := by
    rw [hMc, hSc]
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z _
    refine mul_le_mul_of_nonneg_left ?_
      (bot_le : (⊥ : ℝ≥0∞) ≤ ENNReal.ofReal ((Work.Spaces.w z) ^ 2))
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    exact ENNReal.ofReal_le_ofReal (le_mul_of_one_le_right (sq_nonneg _) (one_le_sEta hθ))
  have hMc_ne_top : Mc ≠ ⊤ := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) (hMc_le_Sc.trans hSc_fin)
  -- ## the slice gap in `lintegral` form
  have hgapI : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      9 * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2))
        ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2) := by
    rw [restrict_Iz_eq_restrict_Ioi]
    filter_upwards [hgap, hC, hint] with z hzgap hzC hzint
    have hLI : MeasureTheory.IntegrableOn (fun θ => (u z θ) ^ 2) Work.Spaces.Iθ :=
      (hzC.pow 2).integrableOn_compact isCompact_Icc
    have hL : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2))
        = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2) :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hLI
        (Eventually.of_forall (fun θ => sq_nonneg _))).symm
    have hR : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2))
        = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2) :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hzint
        (Eventually.of_forall (fun θ => sq_nonneg _))).symm
    rw [hL, hR]
    calc 9 * ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)
        = ENNReal.ofReal (9 * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9),
            show ENNReal.ofReal (9 : ℝ) = (9 : ℝ≥0∞) from by norm_num]
      _ ≤ ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2) :=
          ENNReal.ofReal_le_ofReal hzgap
  have h9 : (9 : ℝ≥0∞) * Mc ≤ Bc := by
    rw [hMc, hBc]
    calc (9 : ℝ≥0∞) * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)))
        = ∫⁻ z in Work.Spaces.Iz, (9 : ℝ≥0∞)
            * (ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
              * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2))) :=
          (MeasureTheory.lintegral_const_mul' 9 _ (by norm_num)).symm
      _ = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * (9 * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2))) := by
          refine MeasureTheory.lintegral_congr (fun z => ?_)
          ring
      _ ≤ ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)) :=
          MeasureTheory.lintegral_mono_ae
            (hgapI.mono (fun z hz => mul_le_mul_of_nonneg_left hz bot_le))
  -- ## the arithmetic in `ℝ`
  obtain ⟨hα0, hα4⟩ := h.hα, h.hα4
  have hKn_nonneg : (0 : ℝ) ≤ 13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α)) := by
    nlinarith [hα0]
  have hKn87 : 13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α)) ≤ 87 / 10 := by
    nlinarith [hα0, hα4]
  have hKn_lt9 : 13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α)) < 9 := by linarith
  have hSG : (0 : ℝ) ≤ Work.Spaces.HkSq α 0 G := Work.Spaces.HkSq_nonneg α 0 G
  have hhalf : (0 : ℝ) ≤ 1 / 2 * Work.Spaces.HkSq α 0 G := by linarith
  have hRHS_ne_top : ENNReal.ofReal (13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α))) * Mc
      + ENNReal.ofReal (1 / 2) * ENNReal.ofReal (Work.Spaces.HkSq α 0 G) ≠ ⊤ :=
    (ENNReal.add_ne_top).mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hMc_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩
  have hBc_ne_top : Bc ≠ ⊤ := ne_top_of_le_ne_top hRHS_ne_top (le_trans le_add_self hEn)
  have hBcreal : Bc.toReal ≤ (13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α))) * Mc.toReal
      + 1 / 2 * Work.Spaces.HkSq α 0 G := by
    have h := ENNReal.toReal_mono hRHS_ne_top (le_trans le_add_self hEn)
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hMc_ne_top)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
      ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hKn_nonneg, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.toReal_ofReal hSG] at h
    exact h
  have h9real : 9 * Mc.toReal ≤ Bc.toReal := by
    have h := ENNReal.toReal_mono hBc_ne_top h9
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at h
    exact h
  have hhalfmul : 29 * (1 / 2 * Work.Spaces.HkSq α 0 G) * (9 - (13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α))))
      ≥ (13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α))) * (1 / 2 * Work.Spaces.HkSq α 0 G) := by
    nlinarith [hKn87, hKn_nonneg, hhalf]
  have hBc_le : Bc.toReal ≤ 30 * (1 / 2 * Work.Spaces.HkSq α 0 G) := by
    have hMr : (0 : ℝ) ≤ Mc.toReal := ENNReal.toReal_nonneg
    nlinarith [hBcreal, h9real, hKn87, hKn_nonneg, hhalf, hhalfmul, hMr]
  -- ## back to the `σ`-mass
  have hSc_real : Sc.toReal ≤ Cσ * Bc.toReal := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBc_ne_top)
      (hσup α u G h)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt hCσpos)] at h
    exact h
  have hSc_le : Sc ≤ ENNReal.ofReal (Cσ * 30 * (1 / 2)) * ENNReal.ofReal (Work.Spaces.HkSq α 0 G) := by
    rw [← ENNReal.ofReal_toReal hSc_ne_top, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [hSc_real, hBc_le, hCσpos]
  -- ## the final comparison
  have hmain : ENNReal.ofReal (Work.Spaces.HkSq α 0 u)
      ≤ ENNReal.ofReal (Cσ * 30 * (1 / 2)) * ENNReal.ofReal (Work.Spaces.HkSq α 0 G) :=
    (ofReal_HkSq_le_sigmaMass α).trans hSc_le
  have hreal : Work.Spaces.HkSq α 0 u ≤ Cσ * 30 * (1 / 2) * Work.Spaces.HkSq α 0 G := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hmain
    rw [ENNReal.toReal_ofReal (Work.Spaces.HkSq_nonneg α 0 u), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hSG] at h
    exact h
  calc Work.FTS.EllipticEst.H2W.Ae.nrm α u
      = Real.sqrt (Work.Spaces.HkSq α 0 u) := rfl
    _ ≤ Real.sqrt (Cσ * 30 * (1 / 2) * Work.Spaces.HkSq α 0 G) := Real.sqrt_le_sqrt hreal
    _ = Real.sqrt (Cσ * 30 * (1 / 2)) * Work.FTS.EllipticEst.H2W.Ae.nrm α G := by
        rw [Real.sqrt_mul (by positivity)]
        rfl

end Work.FTS.EllipticEst.Cores.Pieces.AeGradRho
end
-- ===== merged: Submission.Work.FTS.FinalV2.LocVanish =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.FinalV2.LocVanish` — the datum `locG6` vanishes at the θ-ends (curric-46 lead, 2026-10-10)

`locG6 α L β = locR α L β (z) · Γ(θ)` (`LocDataExt.locG_eq_locR_Gam`) with
`Γ α θ = (sin θ · cos² θ)^(α/3)` (`Work.Spaces.Gam`). At `θ = 0` (`sin 0 = 0`) and `θ = π/2`
(`cos (π/2) = 0`) the base is `0`, and `0 ^ (α/3) = 0` since `α/3 ≠ 0` for `α > 0`
(`Real.zero_rpow`). This supplies the hypothesis `hvan` of `StrongEps.EpsUniform_of_data` in
`Inputs'` (3) for the datum of the adapter.
-/

noncomputable section
open scoped Real

namespace Work.FTS.FinalV2

set_option autoImplicit false

theorem gam_zero_end {α : ℝ} (hα : 0 < α) : Work.Spaces.Gam α 0 = 0 := by
  simp only [Work.Spaces.Gam, Real.sin_zero, zero_mul]
  exact Real.zero_rpow (by positivity)

theorem gam_pi_div_two_end {α : ℝ} (hα : 0 < α) : Work.Spaces.Gam α (π / 2) = 0 := by
  simp only [Work.Spaces.Gam, Real.cos_pi_div_two]
  rw [show Real.sin (π / 2) * (0 : ℝ) ^ 2 = 0 by ring]
  exact Real.zero_rpow (by positivity)

/-- **The datum vanishes at both θ-ends**, for every `z`. -/
theorem locG6_vanish {α : ℝ} (hα : 0 < α) (L β : ℝ) :
    ∀ z, 0 ≤ z → Work.FTS.LocData6.locG6 α L β z 0 = 0 ∧
      Work.FTS.LocData6.locG6 α L β z (π / 2) = 0 := by
  intro z _
  rw [Work.FTS.LocData6.locG6_eq, Work.FTS.LocDataExt.locG_eq_locR_Gam]
  exact ⟨by simp only [gam_zero_end hα, mul_zero], by simp only [gam_pi_div_two_end hα, mul_zero]⟩

end Work.FTS.FinalV2
end
end
-- ===== merged: Submission.Work.FTS.GalFields.Norm.RadA4.L12f_DzdIter_sq_w_sq_integrable_four =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.Norm.RadA4

set_option autoImplicit false
set_option maxHeartbeats 1000000


end Work.FTS.GalFields.Norm.RadA4
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Row19Prep.row19_gam_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Open.Row19Prep

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000


end Work.FTS.Nonlinear.Open.Row19Prep
end
end
-- ===== merged: Submission.Work.FTS.OpenPkg.ProdOpen.prod_majorant =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.OpenPkg.ProdOpen

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Work.Spaces

theorem prod_majorant : ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.HkIntegrand α 4 (fun z θ => f z θ * g z θ) z θ
        ≤ K / (Work.Spaces.gam α - 1)
            * (Work.Spaces.HkSq α 4 f * Work.Spaces.HkIntegrand α 4 g z θ
              + Work.Spaces.HkSq α 4 g * Work.Spaces.HkIntegrand α 4 f z θ)
          + K * ((Work.Spaces.DzIter 3 f z θ * Work.Spaces.Dth g z θ) ^ 2
              + (Work.Spaces.Dth f z θ * Work.Spaces.DzIter 3 g z θ) ^ 2)
            * (Work.Spaces.Wt α z θ) ^ 2 := by
  obtain ⟨CZ, hCZpos, hZ⟩ := z_sum_bound
  obtain ⟨CM, hCMpos, hM⟩ := m_sum_bound
  refine ⟨5 * CZ + 25 * CM + 1, by positivity, ?_⟩
  intro α f g hα hα1 hF hmemF hG hmemG z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hRnn : 0 ≤ Maj α f g z θ := Maj_nonneg hα f g z θ
  have hZsum : ∑ i ∈ Finset.range 5, (DzIter i (fun z θ => f z θ * g z θ) z θ
        * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2 ≤ 5 * (CZ * Maj α f g z θ) := by
    calc ∑ i ∈ Finset.range 5, (DzIter i (fun z θ => f z θ * g z θ) z θ
          * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
        ≤ ∑ i ∈ Finset.range 5, (CZ * Maj α f g z θ) :=
          Finset.sum_le_sum (fun i hi => hZ α f g hα hα1 hF hmemF hG hmemG i
            (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) z θ hz hθ0 hθ1)
      _ = 5 * (CZ * Maj α f g z θ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
  have hMsum : ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2 else 0)
        ≤ 25 * (CM * Maj α f g z θ) := by
    have hper : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2 else 0)
        ≤ CM * Maj α f g z θ := by
      intro i hi j hj
      by_cases hc : 1 ≤ i ∧ i + j ≤ 4
      · rw [if_pos hc]
        exact hM α f g hα hα1 hF hmemF hG hmemG i j hc.1 hc.2 z θ hz hθ0 hθ1
      · rw [if_neg hc]
        exact mul_nonneg hCMpos.le hRnn
    calc ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2 else 0)
        ≤ ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, (CM * Maj α f g z θ) :=
          Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hper i hi j hj))
      _ = 25 * (CM * Maj α f g z θ) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have hcomb : 5 * (CZ * Maj α f g z θ) + 25 * (CM * Maj α f g z θ)
      ≤ (5 * CZ + 25 * CM + 1) * Maj α f g z θ := by nlinarith [hRnn]
  rw [HkIntegrand]
  refine le_trans (add_le_add hZsum hMsum) (le_trans hcomb (le_of_eq ?_))
  rw [Maj, SInv, Texc, div_eq_mul_inv]
  ring

end Work.FTS.OpenPkg.ProdOpen
end
-- ===== merged: Submission.Work.FTS.PhiStar.Assemble =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## `SmoothOpen` and `ContDiffAt` -/

/-- A `SmoothOpen` function is `C^n` at every interior point of the open quadrant. -/
theorem contDiffAt_of_smoothOpen {R : Fn} (hR : Work.FTS.EllipticEst.SmoothOpen R)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) (n : ℕ) :
    ContDiffAt ℝ n (Function.uncurry R) (z, θ) :=
  (Work.FTS.EllipticEst.SmoothOpen.forall hR n).contDiffAt
    (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
    ((Work.FTS.EllipticEst.mem_Q0).mpr ⟨hz, hθ, hθ2⟩))

/-! ## The `bslOp`-image of the model part -/

/-- **The model part of the decomposition solves the profile equation up to the remainder
source**: for the explicit radial profile `GzProfile α` and an angular model `ψ`,
`bslOp α (Model α (GzProfile α) ψ) = F_* − α²(𝒜φ)ψ` on the open quadrant.  This is the
telescoping identity `phiStar_remainder_source` instantiated at `Gz = GzProfile α`. -/
theorem bslOp_model_eq {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {ψ : ℝ → ℝ}
    (hψ : AngModel α ψ) (hGzd : ContDiffOn ℝ 2 (GzProfile α) (Set.Ioi 0))
    (z θ : ℝ) (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < π / 2) :
    Work.Elliptic.bslOp α (Model α (GzProfile α) ψ) z θ
      = Work.Construction.Fstar α z θ - RemSource α ψ z θ := by
  have hψsm : ContDiffOn ℝ 2 ψ (Set.Ioo 0 (π / 2)) := hψ.smooth.of_le (by norm_num)
  have hψeq : ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.FTS.EllipticEst.Lzero1 ψ θ = Work.FTS.VocabO.GamBar α θ := fun θ hθ => hψ.eq θ hθ
  have hGode : ∀ z, 0 < z →
      -(α ^ 2 * z ^ 2 * iteratedDeriv 2 (GzProfile α) z)
        - α * (5 + α) * z * deriv (GzProfile α) z
      = (5 * α / 4) * Work.FTS.VocabO.phiR z := fun z hz => GzProfile_ode hα hα4 z hz
  exact phiStar_remainder_source α hα ψ (GzProfile α) hψsm hψeq hGode hGzd z hz θ hθ hθ2

/-! ## The assembled solution -/

/-- **The assembled stream function.**  Given an angular model `ψ`, an explicit radial profile
`GzProfile α` and a solution `R` of `bslOp α R = RemSource α ψ` with the Dirichlet data at
`θ = 0, π/2` and decay, the sum `Φ_* = Model α (GzProfile α) ψ + R` is a solution of
`bslOp α Φ_* = F_*` in the class `IsBslSol`. -/
theorem isBslSol_of_rem {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {ψ : ℝ → ℝ} {R : Fn}
    {C : ℝ} (hψ : AngModel α ψ) (hGzd : ContDiffOn ℝ 2 (GzProfile α) (Set.Ioi 0))
    (hGzdec : Tendsto (GzProfile α) atTop (𝓝 0)) (hψbd : ∀ θ ∈ Work.Spaces.Iθ, |ψ θ| ≤ C)
    (hRs : Work.FTS.EllipticEst.SmoothOpen R)
    (hRx : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp α R z θ = RemSource α ψ z θ)
    (hR0 : ∀ z, R z 0 = 0) (hR1 : ∀ z, R z (π / 2) = 0)
    (hRdec : ∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => R z θ) atTop (𝓝 0)) :
    Work.Elliptic.IsBslSol α (Work.Construction.Fstar α)
      (fun z θ => Model α (GzProfile α) ψ z θ + R z θ) := by
  refine isBslSol_of_split (Gz := GzProfile α) (ψ := ψ) (R := R) (C := C) ?_ hRx ?_ ?_
    hψ.bdry0 hψ.bdry1 hR0 hR1 hGzdec hψbd hRdec
  · intro z hz θ hθ hθ2
    exact bslOp_model_eq hα hα4 hψ hGzd z θ hz hθ hθ2
  · intro z θ hz hθ hθ2
    refine contDiffAt_model 2 hz (hGzd.contDiffAt (isOpen_Ioi.mem_nhds hz)) ?_
    exact (hψ.smooth.of_le (by norm_num)).contDiffAt
      (isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo 0 (π / 2) from ⟨hθ, hθ2⟩))
  · intro z θ hz hθ hθ2
    exact contDiffAt_of_smoothOpen hRs hz hθ hθ2 2

/-! ## The `hGzd`-free forms

`GzProfile_smooth` (proved) discharges the differentiability hypothesis of `GzProfile`. -/

/-- The explicit radial profile is `C²` on `(0,∞)`. -/
theorem GzProfile_contDiffOn_two {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) :
    ContDiffOn ℝ 2 (GzProfile α) (Set.Ioi 0) :=
  GzProfile_smooth hα hα4 2


/-- `isBslSol_of_rem` with the differentiability of `GzProfile` discharged. -/
theorem isBslSol_of_rem' {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {ψ : ℝ → ℝ} {R : Fn}
    {C : ℝ} (hψ : AngModel α ψ) (hGzdec : Tendsto (GzProfile α) atTop (𝓝 0))
    (hψbd : ∀ θ ∈ Work.Spaces.Iθ, |ψ θ| ≤ C) (hRs : Work.FTS.EllipticEst.SmoothOpen R)
    (hRx : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 →
      Work.Elliptic.bslOp α R z θ = RemSource α ψ z θ)
    (hR0 : ∀ z, R z 0 = 0) (hR1 : ∀ z, R z (π / 2) = 0)
    (hRdec : ∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => R z θ) atTop (𝓝 0)) :
    Work.Elliptic.IsBslSol α (Work.Construction.Fstar α)
      (fun z θ => Model α (GzProfile α) ψ z θ + R z θ) :=
  isBslSol_of_rem hα hα4 hψ (GzProfile_contDiffOn_two hα hα4) hGzdec hψbd hRs hRx hR0 hR1 hRdec

end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Psi0Classes =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false

/-- The angular tail bound of `Psi0Aux/cos_sq_Gam_div_sin_bounds`. -/
def IClass (K : ℝ) : Prop :=
  0 < K ∧
  (∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ θ ∈ Set.Icc (0 : ℝ) (2 / 3),
    (∫ t in θ..(Real.pi / 2), Real.cos t ^ 2 * Work.Spaces.Gam α t / Real.sin t) ≤ K / α) ∧
  (∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ θ ∈ Set.Icc (2 / 3 : ℝ) (Real.pi / 2),
    (∫ t in θ..(Real.pi / 2), Real.cos t ^ 2 * Work.Spaces.Gam α t / Real.sin t)
      ≤ K * Real.cos θ ^ 3 * Work.Spaces.Gam α θ)

/-- The elementary `D_θ`-bounds: `|D_θ^i sin²θ| ≤ b_i sin²θ`, `|D_θ^i cos²θ| ≤ b_i cos²θ`,
`|D_θ^i cos 2θ| ≤ b_i`. -/
def ElemClass (b : ℕ → ℝ) : Prop :=
  (∀ i, 0 ≤ b i) ∧
  (∀ i ≤ 7, ∀ θ ∈ Work.Spaces.Iθ,
    |Work.Spaces.dthU^[i] (fun t : ℝ => Real.sin t ^ 2) θ| ≤ b i * Real.sin θ ^ 2) ∧
  (∀ i ≤ 7, ∀ θ ∈ Work.Spaces.Iθ,
    |Work.Spaces.dthU^[i] (fun t : ℝ => Real.cos t ^ 2) θ| ≤ b i * Real.cos θ ^ 2) ∧
  (∀ i ≤ 7, ∀ θ ∈ Work.Spaces.Iθ,
    |Work.Spaces.dthU^[i] (fun t : ℝ => Real.cos (2 * t)) θ| ≤ b i)

/-- The `D_θ`-bounds for the source `Γ̄`. -/
def HClass (cc dd : ℕ → ℝ) : Prop :=
  (∀ j, 0 ≤ cc j) ∧ (∀ j, 0 ≤ dd j) ∧
  ∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ j : ℕ, 1 ≤ j → j ≤ 5 →
  ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
    |Work.Spaces.dthU^[j] (Work.FTS.VocabO.GamBar α) θ|
      ≤ cc j * α * Work.Spaces.Gam α θ + dd j * Real.sin (2 * θ)

/-- The `Z`-class: pointwise bounds for `D_θ^j P`, `1 ≤ j ≤ 5`. -/
def ZClass (κ ell : ℕ → ℝ) : Prop :=
  (∀ j, 0 ≤ κ j) ∧ (∀ j, 0 ≤ ell j) ∧
  ∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ j : ℕ, 1 ≤ j → j ≤ 5 →
  ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
    |Work.Spaces.dthU^[j] (Pfun α) θ|
      ≤ κ j * α * (Real.sin θ ^ 2 * Real.cos θ ^ (2 * α / 3)) + ell j * Real.sin (2 * θ)

/-- The `A`-class: `|D_θ^j ψ| ≤ ν_j sin 2θ` for `0 ≤ j ≤ 6`. -/
def AClass (ν : ℕ → ℝ) : Prop :=
  (∀ j, 0 ≤ ν j) ∧
  ∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ j : ℕ, j ≤ 6 →
  ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
    |Work.Spaces.dthU^[j] (psiSol α) θ| ≤ ν j * Real.sin (2 * θ)

end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Psi0Ident =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- `D_θψ = 2cos 2θ·ψ + 4cos²θ·P` for the explicit model. -/
theorem dthU_psiSol (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.dthU (psiSol α) θ
      = 2 * Real.cos (2 * θ) * psiSol α θ + 4 * Real.cos θ ^ 2 * Pfun α θ := by
  have hS : Real.sin θ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1
    (by linarith [hθ.2, Real.pi_gt_three]))
  have hd : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ := by
    have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    have h := hlin.sin
    convert h using 1
    ring
  have hw : HasDerivAt (fun t : ℝ => Kc α + wZer α t) (Pfun α θ / (Real.sin θ) ^ 2) θ :=
    (hasDerivAt_wZer α hα hα1 hθ).const_add (Kc α)
  have hderiv : deriv (psiSol α) θ
      = 2 * Real.cos (2 * θ) * (Kc α + wZer α θ)
        + Real.sin (2 * θ) * (Pfun α θ / (Real.sin θ) ^ 2) := (hd.mul hw).deriv
  have hpsi : psiSol α θ = Real.sin (2 * θ) * (Kc α + wZer α θ) := rfl
  rw [Work.Spaces.dthU_apply, hderiv, hpsi, Real.sin_two_mul]
  field_simp
  ring

/-- **The reduced second-derivative identity**: `ψ'' = 2P − 4ψ − Γ̄`. -/
theorem psiSol_sndDeriv (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    iteratedDeriv 2 (psiSol α) θ
      = 2 * Pfun α θ - 4 * psiSol α θ - Work.FTS.VocabO.GamBar α θ := by
  have hC : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hS : Real.sin θ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1
    (by linarith [hθ.2, Real.pi_gt_three]))
  have hode := psiSol_ode α hα hα1 hθ
  have hL : Work.FTS.EllipticEst.Lzero1 (psiSol α) θ
      = -iteratedDeriv 2 (psiSol α) θ + deriv (fun t : ℝ => Real.tan t * psiSol α t) θ
        - 6 * psiSol α θ := by
    rw [Work.FTS.EllipticEst.Lzero1]
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have hdif : DifferentiableAt ℝ (psiSol α) θ :=
    (((contDiffOn_psiSol α hα hα1).differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ))
  have htan : deriv (fun t : ℝ => Real.tan t * psiSol α t) θ
      = (1 / Real.cos θ ^ 2) * psiSol α θ + Real.tan θ * deriv (psiSol α) θ := by
    have h1 : HasDerivAt Real.tan (1 / Real.cos θ ^ 2) θ := Real.hasDerivAt_tan hC
    exact (h1.mul hdif.hasDerivAt).deriv
  have hsin2 : Real.sin (2 * θ) ≠ 0 := by
    rw [Real.sin_two_mul]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hS) hC
  have hdψ : deriv (psiSol α) θ
      = (2 * Real.cos (2 * θ) * psiSol α θ + 4 * Real.cos θ ^ 2 * Pfun α θ)
        / Real.sin (2 * θ) := by
    rw [← dthU_psiSol α hα hα1 hθ, Work.Spaces.dthU_apply]
    field_simp
  rw [hL, htan, hdψ] at hode
  have htanθ : Real.tan θ = Real.sin θ / Real.cos θ := Real.tan_eq_sin_div_cos θ
  have hcos2 : Real.cos (2 * θ) = Real.cos θ ^ 2 - Real.sin θ ^ 2 := Real.cos_two_mul' θ
  have hsq : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  rw [htanθ, hcos2, Real.sin_two_mul] at hode
  have hsq' : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by linarith
  rw [hsq'] at hode
  field_simp at hode
  ring_nf at hode
  have h2 : 2 * Real.cos θ ^ 2 * iteratedDeriv 2 (psiSol α) θ
      = 2 * Real.cos θ ^ 2 * (2 * Pfun α θ - 4 * psiSol α θ
        - Work.FTS.VocabO.GamBar α θ) := by
    linarith [hode]
  exact mul_left_cancel₀ (by positivity : (2 * Real.cos θ ^ 2) ≠ 0) h2

/-- `|Kc| ≤ 250π`. -/
lemma abs_Kc_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) : |Kc α| ≤ 250 * π := by
  have hπ : (0:ℝ) ≤ π / 2 := by linarith [Real.pi_pos]
  have hcont : ContinuousOn (fun θ : ℝ => Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ)
      (Set.uIcc (0:ℝ) (π / 2)) := by
    rw [Set.uIcc_of_le hπ]
    exact continuousOn_wZer' α hα hα1
  have hint : IntervalIntegrable (fun θ : ℝ =>
      |Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ|) volume 0 (π / 2) :=
    hcont.abs.intervalIntegrable
  have h2 : IntervalIntegrable (fun θ : ℝ =>
      (500 * (π / 2)) * (Real.sin θ ^ 2 * Real.cos θ ^ 3)) volume 0 (π / 2) :=
    (by fun_prop : Continuous fun θ : ℝ =>
      (500 * (π/2)) * (Real.sin θ ^ 2 * Real.cos θ ^ 3)).intervalIntegrable _ _
  have h1 : (∫ θ in (0:ℝ)..(π / 2), |Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ|)
      ≤ 500 * (π / 2) * (∫ θ in (0:ℝ)..(π / 2), Real.sin θ ^ 2 * Real.cos θ ^ 3) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hπ hint h2 ?_
    intro θ hθ
    have hSC : 0 ≤ Real.sin θ ^ 2 * Real.cos θ ^ 3 := by
      have h1 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ.1,
        by linarith [hθ.2, Real.pi_gt_three]⟩
      have h2 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      positivity
    rw [abs_mul, abs_of_nonneg hSC]
    exact mul_le_mul_of_nonneg_left (abs_wZer_le α hα hα1 hθ) hSC |>.trans_eq (by ring)
  have h3 : (∫ θ in (0:ℝ)..(π / 2), Real.sin θ ^ 2 * Real.cos θ ^ 3) = 2 / 15 := by
    rw [integral_sin_sq_cos_cu (0:ℝ) (π/2) hπ, PsiS_zero, PsiS_pi_div_two, sub_zero]
  have h4 := intervalIntegral.abs_integral_le_integral_abs (μ := volume) (f := fun θ : ℝ =>
    Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ) hπ
  rw [h3] at h1
  have hKc : Kc α = -(15 / 2) * (∫ θ in (0:ℝ)..(π / 2),
      Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ) := rfl
  have hA : |∫ θ in (0:ℝ)..(π / 2), Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ|
      ≤ 500 * (π / 2) * (2 / 15) := h4.trans h1
  rw [hKc, abs_mul]
  have habs : |-((15:ℝ) / 2)| = 15 / 2 := by
    rw [abs_of_neg (by norm_num : -((15:ℝ) / 2) < 0)]; norm_num
  rw [habs]
  calc (15 / 2) * |∫ θ in (0:ℝ)..(π / 2), Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ|
      ≤ (15 / 2) * (500 * (π / 2) * (2 / 15)) :=
        mul_le_mul_of_nonneg_left hA (by norm_num)
    _ = 250 * π := by ring

/-- **The moment condition**: `∫_0^{π/2} ψ sinθcos²θ = 0`. -/
theorem psiSol_moment (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    (∫ θ in Work.Spaces.Iθ, psiSol α θ * Work.Elliptic.sinCos2 θ) = 0 := by
  have hπ : (0:ℝ) ≤ π / 2 := by linarith [Real.pi_pos]
  have hint1 : IntervalIntegrable (fun θ : ℝ =>
      Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ) volume 0 (π / 2) := by
    have hcont : ContinuousOn (fun θ : ℝ => Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ)
        (Set.uIcc (0:ℝ) (π / 2)) := by
      rw [Set.uIcc_of_le hπ]
      exact continuousOn_wZer' α hα hα1
    exact hcont.intervalIntegrable
  have hint2 : IntervalIntegrable (fun θ : ℝ =>
      (2 * Kc α) * (Real.sin θ ^ 2 * Real.cos θ ^ 3)) volume 0 (π / 2) :=
    (by fun_prop : Continuous fun θ : ℝ =>
      (2 * Kc α) * (Real.sin θ ^ 2 * Real.cos θ ^ 3)).intervalIntegrable _ _
  have hint3 : IntervalIntegrable (fun θ : ℝ =>
      2 * (Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ)) volume 0 (π / 2) :=
    hint1.const_mul 2
  have hpt : ∀ θ : ℝ, psiSol α θ * Work.Elliptic.sinCos2 θ
      = 2 * (Kc α + wZer α θ) * (Real.sin θ ^ 2 * Real.cos θ ^ 3) := by
    intro θ
    simp only [psiSol, Work.Elliptic.sinCos2, Real.sin_two_mul]
    ring
  have key : (∫ θ in (0:ℝ)..(π / 2), psiSol α θ * Work.Elliptic.sinCos2 θ)
      = 2 * Kc α * (∫ θ in (0:ℝ)..(π / 2), Real.sin θ ^ 2 * Real.cos θ ^ 3)
        + 2 * (∫ θ in (0:ℝ)..(π / 2), Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ) := by
    rw [intervalIntegral.integral_congr (fun θ _ => hpt θ)]
    rw [show (fun θ : ℝ => 2 * (Kc α + wZer α θ) * (Real.sin θ ^ 2 * Real.cos θ ^ 3))
        = fun θ => (2 * Kc α) * (Real.sin θ ^ 2 * Real.cos θ ^ 3)
          + 2 * (Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ) by
      funext θ; ring]
    rw [intervalIntegral.integral_add hint2 hint3, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have hval : (∫ θ in (0:ℝ)..(π / 2), Real.sin θ ^ 2 * Real.cos θ ^ 3) = 2 / 15 := by
    rw [integral_sin_sq_cos_cu (0:ℝ) (π/2) hπ, PsiS_zero, PsiS_pi_div_two, sub_zero]
  have hKc : Kc α = -(15 / 2) * (∫ θ in (0:ℝ)..(π / 2),
      Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ) := rfl
  rw [hval, hKc] at key
  have hzero : 2 * (-(15 / 2) * (∫ θ in (0:ℝ)..(π / 2),
      Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ)) * (2 / 15)
      + 2 * (∫ θ in (0:ℝ)..(π / 2), Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ) = 0 := by
    ring
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hπ, key]
  ring

end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.PsiDivS2EqPfun =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false

theorem PsiDivS2EqPfun {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {ψ : ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n ψ (Set.Ioo 0 (Real.pi / 2)))
    (hcont : ContinuousOn ψ (Set.Icc 0 (Real.pi / 2))) (h0 : ψ 0 = 0)
    (hconst : ∃ c : ℝ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Real.sin θ ^ 2 * Real.cos θ ^ 3 * deriv (fun θ' => ψ θ' / Real.sin (2 * θ')) θ
        - Work.FTS.PhiStar.Gzero α θ / 2 = c) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (fun θ' => ψ θ' / Real.sin (2 * θ')) θ
        = Work.FTS.PhiStar.Pfun α θ / Real.sin θ ^ 2 := by
  obtain ⟨c, hc⟩ := hconst
  let F : ℝ → ℝ := fun t => ψ t / Real.sin (2 * t)
  let H : ℝ → ℝ := fun t => F t + c * (Real.cos t / Real.sin t)
  let A : ℝ → ℝ := fun s => (c + Gzero α s / 2) / (Real.sin s ^ 2 * Real.cos s ^ 3)
      - c / Real.sin s ^ 2
  have hsin_pos : ∀ t ∈ Set.Ioo (0:ℝ) (Real.pi / 2), 0 < Real.sin t :=
    fun t ht => Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
  have hcos_pos : ∀ t ∈ Set.Ioo (0:ℝ) (Real.pi / 2), 0 < Real.cos t :=
    fun t ht => Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  -- `F` is smooth on the open interval
  have hsmF : ∀ n : ℕ, ContDiffOn ℝ n F (Set.Ioo 0 (Real.pi / 2)) := by
    intro n
    have hsin : ContDiffOn ℝ n (fun t : ℝ => Real.sin (2 * t)) (Set.Ioo 0 (Real.pi / 2)) := by
      fun_prop
    have hd := (hsm n).div hsin (fun t ht => by
      have h2 : 0 < Real.sin (2 * t) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos])
      exact ne_of_gt h2)
    exact hd
  have hFdiff : DifferentiableOn ℝ F (Set.Ioo 0 (Real.pi / 2)) :=
    (hsmF 1).differentiableOn (by norm_num)
  -- the first integral of the ODE gives a formula for `F'`
  have hFderiv : ∀ t ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      deriv F t = (c + Gzero α t / 2) / (Real.sin t ^ 2 * Real.cos t ^ 3) := by
    intro t ht
    have h := hc t ht
    have hne : Real.sin t ^ 2 * Real.cos t ^ 3 ≠ 0 := by
      have h1 := hsin_pos t ht
      have h2 := hcos_pos t ht
      positivity
    have h2 : Real.sin t ^ 2 * Real.cos t ^ 3 * deriv F t = c + Gzero α t / 2 := by
      linarith
    rw [eq_div_iff hne]
    linarith
  -- derivative of `H`
  have hHderiv : ∀ t ∈ Set.Ioo (0:ℝ) (Real.pi / 2), HasDerivAt H (A t) t := by
    intro t ht
    have htπ : t ∈ Set.Ioo (0:ℝ) (Real.pi / 2) := ht
    have hsin0 : 0 < Real.sin t := hsin_pos t htπ
    have hF' : HasDerivAt F ((c + Gzero α t / 2) / (Real.sin t ^ 2 * Real.cos t ^ 3)) t := by
      have h := (hFdiff.differentiableAt (isOpen_Ioo.mem_nhds htπ)).hasDerivAt
      rwa [hFderiv t htπ] at h
    have hcot' : HasDerivAt (fun s : ℝ => Real.cos s / Real.sin s) (-(1 / Real.sin t ^ 2)) t := by
      have h := (Real.hasDerivAt_cos t).div (Real.hasDerivAt_sin t) (ne_of_gt hsin0)
      have h2 : (-Real.sin t * Real.sin t - Real.cos t * Real.cos t) / Real.sin t ^ 2
          = -(1 / Real.sin t ^ 2) := by
        have h3 : -Real.sin t * Real.sin t - Real.cos t * Real.cos t = -1 := by
          nlinarith [Real.sin_sq_add_cos_sq t]
        rw [h3, neg_div]
      rwa [h2] at h
    have hsum : HasDerivAt (fun y : ℝ => F y + c * (Real.cos y / Real.sin y)) (A t) t := by
      have h1 : HasDerivAt (fun y : ℝ => F y + c * (Real.cos y / Real.sin y))
          ((c + Gzero α t / 2) / (Real.sin t ^ 2 * Real.cos t ^ 3)
            + c * (-(1 / Real.sin t ^ 2))) t := hF'.add (hcot'.const_mul c)
      rwa [show ((c + Gzero α t / 2) / (Real.sin t ^ 2 * Real.cos t ^ 3)
            + c * (-(1 / Real.sin t ^ 2))) = A t from by simp only [A]; ring] at h1
    exact hsum
  -- the mean value theorem bounds `H` near `0`
  have hHbd : ∀ t ∈ Set.Ioo (0:ℝ) (1 / 2),
      |H t| ≤ |H (1 / 2)| + (24 * |c| + 7 * Real.pi ^ 2) * (1 / 2) := by
    intro t ht
    have hC : 0 ≤ 24 * |c| + 7 * Real.pi ^ 2 := by positivity
    have hder : ∀ x ∈ Set.Icc t (1 / 2), HasDerivWithinAt H (A x) (Set.Icc t (1 / 2)) x := by
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le ht.1 hx.1
      have hx' : x ∈ Set.Ioo (0:ℝ) (Real.pi / 2) := ⟨hx0, by linarith [hx.2, Real.pi_gt_three]⟩
      exact (hHderiv x hx').hasDerivWithinAt
    have hbnd : ∀ x ∈ Set.Ico t (1 / 2), ‖A x‖ ≤ 24 * |c| + 7 * Real.pi ^ 2 := by
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le ht.1 hx.1
      have hx' : x ∈ Set.Ioo (0:ℝ) (1 / 2) := ⟨hx0, hx.2⟩
      have h := PsiDivS2Sup.derivG_reg_bound (c := c) hα hα4 hx'
      simpa only [A, Real.norm_eq_abs] using h
    have hmain := norm_image_sub_le_of_norm_deriv_le_segment' (f := H) (f' := A)
      (a := t) (b := (1 / 2 : ℝ)) hder hbnd (1 / 2) (Set.right_mem_Icc.mpr (le_of_lt ht.2))
    have h1 : |H t - H (1 / 2)| ≤ (24 * |c| + 7 * Real.pi ^ 2) * (1 / 2 - t) := by
      rw [abs_sub_comm]
      simpa only [Real.norm_eq_abs] using hmain
    have h2 : (1 / 2 - t) ≤ 1 / 2 := by linarith [ht.1]
    calc |H t| = |(H t - H (1 / 2)) + H (1 / 2)| := by ring_nf
      _ ≤ |H t - H (1 / 2)| + |H (1 / 2)| := abs_add_le _ _
      _ ≤ (24 * |c| + 7 * Real.pi ^ 2) * (1 / 2 - t) + |H (1 / 2)| := by linarith
      _ ≤ (24 * |c| + 7 * Real.pi ^ 2) * (1 / 2) + |H (1 / 2)| := by
            have := mul_le_mul_of_nonneg_left h2 hC
            linarith
      _ = |H (1 / 2)| + (24 * |c| + 7 * Real.pi ^ 2) * (1 / 2) := by ring
  -- assemble the hypothesis of the limit lemma
  have hb : ∀ t ∈ Set.Ioo (0:ℝ) (1 / 2),
      |ψ t + 2 * c * Real.cos t ^ 2|
        ≤ (|H (1 / 2)| + (24 * |c| + 7 * Real.pi ^ 2) * (1 / 2)) * Real.sin (2 * t) := by
    intro t ht
    have htπ : t ∈ Set.Ioo (0:ℝ) (Real.pi / 2) := ⟨ht.1, by linarith [ht.2, Real.pi_gt_three]⟩
    have hs0 : 0 < Real.sin (2 * t) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, Real.pi_gt_three])
    have heq : ψ t + 2 * c * Real.cos t ^ 2 = Real.sin (2 * t) * H t := by
      have hsin : Real.sin t ≠ 0 :=
        ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1])
          (by linarith [ht.2, Real.pi_gt_three]))
      have hcos : Real.cos t ≠ 0 :=
        ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], htπ.2⟩)
      simp only [H, F, Real.sin_two_mul]
      field_simp
    rw [heq, abs_mul, abs_of_pos hs0]
    calc Real.sin (2 * t) * |H t| = |H t| * Real.sin (2 * t) := by ring
      _ ≤ (|H (1 / 2)| + (24 * |c| + 7 * Real.pi ^ 2) * (1 / 2)) * Real.sin (2 * t) :=
          mul_le_mul_of_nonneg_right (hHbd t ht) (le_of_lt hs0)
  have hcont' : ContinuousWithinAt ψ (Set.Icc 0 (1 / 2)) 0 := by
    have h1 : ContinuousWithinAt ψ (Set.Icc 0 (Real.pi / 2)) 0 :=
      hcont.continuousWithinAt ⟨le_rfl, by positivity⟩
    exact h1.mono (Set.Icc_subset_Icc le_rfl (by linarith [Real.pi_gt_three]))
  have hc0 : c = 0 := PsiDivS2Sup.eq_zero_of_bound hb hcont' h0
  -- conclusion
  intro θ hθ
  show deriv F θ = Work.FTS.PhiStar.Pfun α θ / Real.sin θ ^ 2
  rw [hFderiv θ hθ, hc0, zero_add]
  have hs : Real.sin θ ≠ 0 := ne_of_gt (hsin_pos θ hθ)
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (hcos_pos θ hθ)
  simp only [Work.FTS.PhiStar.Pfun]
  field_simp

end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Wdiv_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.PhiStar.Wdiv_bound`

The function `v = ψ / sin 2θ` of the angular model is *determined up to an additive constant*:
its derivative is `P/sin²θ = (wZer α)'` (hypothesis `hp`), so `v − wZer α` is constant on the
connected interval `(0, π/2)` (`IsOpen.exists_eq_add_of_deriv_eq`).  The constant is pinned by
the moment condition `∫_{Iθ} ψ · sinθcos²θ = 0`: since `sin 2θ · sinθcos²θ ≥ 0` on `Iθ` with
`∫_{Iθ} sin 2θ · sinθcos²θ = 4/15 > 0`, the moment of `ψ = sin 2θ · v` is
`c·(4/15) + ∫_{Iθ} sin 2θ · wZer · sinθcos²θ`, so

`|c|·(4/15) = |∫ sin 2θ · wZer · sinθcos²θ| ≤ (500·(π/2))·(4/15)`,

i.e. `|c| ≤ 500·(π/2)`.  Since `|wZer α θ| ≤ 500·(π/2)` as well
(`abs_wZer_le`), the triangle inequality gives `|v θ| ≤ 500·π`.

The measure-theoretic half (the moment inequality `const_le_of_moment`) is proved in
`Submission/Work/FTS/PhiStar/const_le_of_moment.lean`.
-/

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false

theorem Wdiv_bound {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {ψ : ℝ → ℝ}
    (hmom : ∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ = 0)
    (h0 : ψ 0 = 0) (h1 : ψ (Real.pi / 2) = 0)
    (hdiff : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), DifferentiableAt ℝ (fun θ' => ψ θ' / Real.sin (2 * θ')) θ)
    (hp : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (fun θ' => ψ θ' / Real.sin (2 * θ')) θ = Work.FTS.PhiStar.Pfun α θ / Real.sin θ ^ 2) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |ψ θ / Real.sin (2 * θ)| ≤ 500 * Real.pi := by
  -- `v − wZer` is constant on the connected open interval `(0, π/2)`
  obtain ⟨c, hc⟩ := IsOpen.exists_eq_add_of_deriv_eq (s := Set.Ioo (0 : ℝ) (Real.pi / 2))
    (f := fun θ => ψ θ / Real.sin (2 * θ)) (g := wZer α) isOpen_Ioo isPreconnected_Ioo
    (fun θ hθ => (hdiff θ hθ).differentiableWithinAt)
    (fun θ hθ => (hasDerivAt_wZer α hα hα4 hθ).differentiableAt.differentiableWithinAt)
    (fun θ hθ => by rw [hp θ hθ, (hasDerivAt_wZer α hα hα4 hθ).deriv])
  -- `sin 2θ` does not vanish on the open interval
  have hsin_ne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * θ) ≠ 0 := by
    intro θ hθ
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))
  -- hence `ψ = sin 2θ · (wZer + c)` on the open interval
  have hpsi : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ψ θ = Real.sin (2 * θ) * (wZer α θ + c) := by
    intro θ hθ
    have hcθ : ψ θ / Real.sin (2 * θ) = wZer α θ + c := hc hθ
    rw [← hcθ, mul_div_cancel₀ _ (hsin_ne θ hθ)]
  -- the identification `sin 2θ · v = ψ` on `Iθ`, including the endpoints where `sin 2θ = 0`
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      Real.sin (2 * θ) * (ψ θ / Real.sin (2 * θ)) * Work.Elliptic.sinCos2 θ
        = ψ θ * Work.Elliptic.sinCos2 θ := by
    intro θ hθ
    rcases lt_or_eq_of_le hθ.1 with hpos | hzero
    · rcases lt_or_eq_of_le hθ.2 with hlt | hpi
      · rw [mul_div_cancel₀ _ (hsin_ne θ ⟨hpos, hlt⟩)]
      · rw [hpi, h1, show 2 * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi]
        ring
    · rw [← hzero, h0, show 2 * (0 : ℝ) = 0 from by ring, Real.sin_zero]
      ring
  -- so the moment condition transfers to `v`
  have hzero : ∫ θ in Work.Spaces.Iθ,
      Real.sin (2 * θ) * (ψ θ / Real.sin (2 * θ)) * Work.Elliptic.sinCos2 θ = 0 := by
    rw [setIntegral_congr_fun (s := Work.Spaces.Iθ) measurableSet_Icc hpt, hmom]
  -- the moment inequality pins the constant
  have hcle : |c| ≤ 500 * (Real.pi / 2) :=
    Work.FTS.PhiStar.const_le_of_moment
      (v := fun θ => ψ θ / Real.sin (2 * θ)) (w := wZer α) (c := c)
      (M := 500 * (Real.pi / 2))
      (fun θ hθ => by rw [hpsi θ hθ, mul_div_cancel_left₀ _ (hsin_ne θ hθ)])
      (fun θ hθ => abs_wZer_le α hα hα4 hθ)
      ((continuousOn_wZer α hα hα4).aestronglyMeasurable measurableSet_Icc)
      hzero
  intro θ hθ
  have hθI : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hcθ : ψ θ / Real.sin (2 * θ) = wZer α θ + c := hc hθ
  calc |ψ θ / Real.sin (2 * θ)| = |wZer α θ + c| := by rw [hcθ]
    _ ≤ |wZer α θ| + |c| := abs_add_le _ _
    _ ≤ 500 * (Real.pi / 2) + 500 * (Real.pi / 2) := by
        linarith [abs_wZer_le α hα hα4 hθI, hcle]
    _ = 500 * Real.pi := by ring

end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeIbp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The per-`n` integration-by-parts identity -/


/-! ## The boundary layers -/

lemma indicator_one_nonneg {A : Set ℝ} (θ : ℝ) : 0 ≤ A.indicator (fun _ => (1 : ℝ)) θ := by
  classical
  rw [Set.indicator_apply]; split_ifs <;> norm_num

lemma indicator_one_le_one {A : Set ℝ} (θ : ℝ) : A.indicator (fun _ => (1 : ℝ)) θ ≤ 1 := by
  classical
  rw [Set.indicator_apply]; split_ifs <;> norm_num

theorem layer_eq_union (n : ℕ) :
    layer n = Set.Ioo 0 (2 * delta n) ∪ Set.Ioo (π / 2 - 2 * delta n) (π / 2) := rfl

/-- The indicator of a measurable set, as a `[0,1]`-valued multiplier, preserves integrability. -/
theorem integrableOn_mul_indicator {f : ℝ → ℝ} {s A : Set ℝ} (hf : MeasureTheory.IntegrableOn f s)
    (hA : MeasurableSet A) (hf0 : ∀ x, 0 ≤ f x) :
    MeasureTheory.IntegrableOn (fun θ => f θ * A.indicator (fun _ => (1 : ℝ)) θ) s := by
  rw [MeasureTheory.IntegrableOn] at hf ⊢
  refine Integrable.mono' hf (hf.aestronglyMeasurable.mul
    (Measurable.aestronglyMeasurable (measurable_const.indicator hA))) ?_
  filter_upwards with θ
  rw [Real.norm_of_nonneg (mul_nonneg (hf0 θ)
    (indicator_one_nonneg θ))]
  calc f θ * A.indicator (fun _ => (1 : ℝ)) θ ≤ f θ * 1 :=
        mul_le_mul_of_nonneg_left (indicator_one_le_one θ) (hf0 θ)
    _ = f θ := mul_one _

/-- Integrate against the indicator of a set contained in the domain. -/
theorem setIntegral_mul_indicator {f : ℝ → ℝ} {A s : Set ℝ} (hA : MeasurableSet A)
    (hsub : A ⊆ s) :
    (∫ θ in s, f θ * A.indicator (fun _ => (1 : ℝ)) θ) = ∫ θ in A, f θ := by
  rw [show (fun θ => f θ * A.indicator (fun _ => (1 : ℝ)) θ) = A.indicator (fun θ => f θ) from by
    funext θ
    by_cases h : θ ∈ A
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, mul_one]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]]
  rw [MeasureTheory.setIntegral_indicator hA, Set.inter_eq_right.mpr hsub]

theorem layer_left_subset_Iθ {n : ℕ} (hn : 2 * delta n ≤ π / 4) :
    Set.Ioo 0 (2 * delta n) ⊆ Work.Spaces.Iθ := fun θ hθ =>
  ⟨le_of_lt hθ.1, by linarith [hθ.2, hn, Real.pi_pos]⟩

theorem layer_right_subset_Iθ {n : ℕ} (hn : 2 * delta n ≤ π / 4) :
    Set.Ioo (π / 2 - 2 * delta n) (π / 2) ⊆ Work.Spaces.Iθ := fun θ hθ =>
  ⟨by linarith [hθ.1, hn, Real.pi_pos], le_of_lt hθ.2⟩

/-- **The per-slice layer bound**: the part of `∫_θ |Φ|` sitting in the layer is controlled by
`√(sliceEnergy Φ z)·δ^{(3+η)/2}`. -/
theorem layer_slice_le {Φ : ℝ → ℝ → ℝ} {C : ℝ}
    (hΦint : ∀ z ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn (fun θ => |Φ z θ|) Work.Spaces.Iθ)
    (hC : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ δ ∈ Set.Ioc (0 : ℝ) (π / 4),
      (∫ θ in Set.Ioo 0 δ, |Φ z θ|
          ≤ C * Real.sqrt (sliceEnergy Φ z) * δ ^ ((3 + Work.Spaces.eta) / 2)) ∧
      (∫ θ in Set.Ioo (π / 2 - δ) (π / 2), |Φ z θ|
          ≤ C * Real.sqrt (sliceEnergy Φ z) * δ ^ ((3 + Work.Spaces.eta) / 2)))
    {z : ℝ} (hz : 0 < z) {n : ℕ} (hn0 : 0 < 2 * delta n)
    (hn1 : 2 * delta n ≤ π / 4) :
    (∫ θ in Work.Spaces.Iθ, |Φ z θ| * layerInd n θ)
      ≤ 2 * C * Real.sqrt (sliceEnergy Φ z) * (2 * delta n) ^ ((3 + Work.Spaces.eta) / 2) := by
  obtain ⟨hAb, hBb⟩ := hC z (Set.mem_Ioi.mpr hz) (2 * delta n) ⟨hn0, hn1⟩
  have hAmeas : MeasurableSet (Set.Ioo 0 (2 * delta n)) := measurableSet_Ioo
  have hBmeas : MeasurableSet (Set.Ioo (π / 2 - 2 * delta n) (π / 2)) := measurableSet_Ioo
  have hint := hΦint z (Set.mem_Ioi.mpr hz)
  have h1 : MeasureTheory.IntegrableOn
      (fun θ => |Φ z θ| * (Set.Ioo 0 (2 * delta n)).indicator (fun _ => (1 : ℝ)) θ)
      Work.Spaces.Iθ := integrableOn_mul_indicator hint hAmeas (fun θ => abs_nonneg _)
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => |Φ z θ| * (Set.Ioo (π / 2 - 2 * delta n) (π / 2)).indicator (fun _ => (1 : ℝ)) θ)
      Work.Spaces.Iθ := integrableOn_mul_indicator hint hBmeas (fun θ => abs_nonneg _)
  have hpt : ∀ θ : ℝ, |Φ z θ| * layerInd n θ
      ≤ |Φ z θ| * (Set.Ioo 0 (2 * delta n)).indicator (fun _ => (1 : ℝ)) θ
        + |Φ z θ| * (Set.Ioo (π / 2 - 2 * delta n) (π / 2)).indicator (fun _ => (1 : ℝ)) θ := by
    intro θ
    by_cases h : θ ∈ layer n
    · have hge : 1 ≤ (Set.Ioo 0 (2 * delta n)).indicator (fun _ => (1 : ℝ)) θ
          + (Set.Ioo (π / 2 - 2 * delta n) (π / 2)).indicator (fun _ => (1 : ℝ)) θ := by
        rw [layer_eq_union] at h
        rcases h with h | h
        · rw [Set.indicator_of_mem h]
          linarith [indicator_one_nonneg (A := Set.Ioo (π / 2 - 2 * delta n) (π / 2)) θ]
        · rw [Set.indicator_of_mem h]
          linarith [indicator_one_nonneg (A := Set.Ioo 0 (2 * delta n)) θ]
      rw [layerInd, Set.indicator_of_mem h, mul_one]
      nlinarith [abs_nonneg (Φ z θ), hge,
        indicator_one_nonneg (A := Set.Ioo 0 (2 * delta n)) θ,
        indicator_one_nonneg (A := Set.Ioo (π / 2 - 2 * delta n) (π / 2)) θ]
    · rw [layerInd, Set.indicator_of_notMem h, mul_zero]
      exact add_nonneg (mul_nonneg (abs_nonneg _) (indicator_one_nonneg _))
        (mul_nonneg (abs_nonneg _) (indicator_one_nonneg _))
  have hsum : MeasureTheory.IntegrableOn (fun θ => |Φ z θ|
      * (Set.Ioo 0 (2 * delta n)).indicator (fun _ => (1 : ℝ)) θ
      + |Φ z θ| * (Set.Ioo (π / 2 - 2 * delta n) (π / 2)).indicator (fun _ => (1 : ℝ)) θ)
      Work.Spaces.Iθ := h1.add h2
  refine (integral_mono_of_nonneg (Eventually.of_forall fun θ => mul_nonneg (abs_nonneg _)
      (indicator_one_nonneg θ)) hsum (Eventually.of_forall hpt)).trans ?_
  have hsum' : (∫ θ in Work.Spaces.Iθ, |Φ z θ|
      * (Set.Ioo 0 (2 * delta n)).indicator (fun _ => (1 : ℝ)) θ
      + |Φ z θ| * (Set.Ioo (π / 2 - 2 * delta n) (π / 2)).indicator (fun _ => (1 : ℝ)) θ)
      = (∫ θ in Set.Ioo 0 (2 * delta n), |Φ z θ|)
        + ∫ θ in Set.Ioo (π / 2 - 2 * delta n) (π / 2), |Φ z θ| := by
    rw [MeasureTheory.integral_add h1 h2,
      setIntegral_mul_indicator hAmeas (layer_left_subset_Iθ hn1),
      setIntegral_mul_indicator hBmeas (layer_right_subset_Iθ hn1)]
  rw [hsum']
  linarith


/-- `δ_n^s → 0` for every `s > 0`. -/
theorem tendsto_delta_rpow {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ => (delta n) ^ s) atTop (𝓝 0) := by
  have hcomp : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := (tendsto_rpow_neg_atTop hs).comp hcomp
  refine h.congr' ?_
  filter_upwards with n
  rw [Function.comp_apply, delta, one_div]
  exact (Real.rpow_neg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) s).trans
    (Real.inv_rpow (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) s).symm

end Work.FTS.StrongEps.EComparison
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.aesm_diff_family =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A.e. strong measurability of the difference family `V s - W`

Given a family `V s` (`s ∈ [0,δ]`) and a fixed profile `W`, all `C^∞` on the open quadrant
`Q0 = (0,∞) × (0,π/2)`, and assuming that all the mixed derivatives `D_z^jD_θ^i (V s)` are
a.e. strongly measurable in `s` at every point of the quadrant (for `i + j ≤ k`), we show

* the same for the mixed derivatives of the difference `V s - W` (subtraction on the open
  quadrant, `Work.FTS.StrongEps.EpsE4Thr.mixed_sub_of_contDiffOn_six`); and
* the joint a.e. strong measurability of the `ℋ^k`-integrand of the difference on the
  product measure `(volume.restrict (Icc 0 δ)) × (volume.restrict Iz) × (volume.restrict Iθ)`.

The second part is a Carathéodory argument (`aesm_uncurry_of_continuousOn_of_zero`): the
integrand is continuous in `(z,θ)` on the open quadrant (for `s ∈ Icc 0 δ`) and measurable
in `s` at each point of the quadrant; the target product measure is that of the restriction
to `A ×ˢ Q0`, and the points where `(z,θ)` leaves `Q0` (the coordinate axes and the lines
`θ = 0`, `θ = π/2`) are null for `(volume.restrict Iz).prod (volume.restrict Iθ)`.
-/

namespace Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits

open MeasureTheory Set Filter
open scoped Real Topology

/-! ## Two auxiliary measurability lemmas -/

/-- A finite sum (evaluated pointwise) of a.e. strongly measurable real functions is a.e.
strongly measurable.  (Local copy of the helper of `aesm_HkIntegrand_of_slots`.) -/
private lemma aesm_finsetSum_apply {ι : Type*} {s : Finset ι} {f : ι → ℝ → ℝ}
    {μ : MeasureTheory.Measure ℝ}
    (hf : ∀ i ∈ s, MeasureTheory.AEStronglyMeasurable (f i) μ) :
    MeasureTheory.AEStronglyMeasurable (fun a : ℝ => ∑ i ∈ s, f i a) μ := by
  have h := Finset.aestronglyMeasurable_sum (M := ℝ) (f := f) s hf
  refine h.congr (Filter.Eventually.of_forall fun a => ?_)
  exact Finset.sum_apply a s f

/-- `aesm_HkIntegrand_of_slots` with the measurability hypothesis required only for the slots
`j + i ≤ k` that actually occur in `HkIntegrand α k`. -/
private lemma aesm_HkIntegrand_of_slots_le {μ : MeasureTheory.Measure ℝ} {B : ℝ → ℝ → ℝ → ℝ}
    {α : ℝ} {k : ℕ} {z θ : ℝ}
    (h : ∀ j i : ℕ, j + i ≤ k →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (B s) z θ) μ) :
    MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => Work.Spaces.HkIntegrand α k (B s) z θ) μ := by
  unfold Work.Spaces.HkIntegrand
  have hA : MeasureTheory.AEStronglyMeasurable (fun s : ℝ => ∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i (B s) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) μ :=
    aesm_finsetSum_apply (fun i hi => by
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      exact ((h i 0 (by omega)).mul_const
        (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))).pow 2)
  have hB : MeasureTheory.AEStronglyMeasurable (fun s : ℝ => ∑ i ∈ Finset.range (k + 1),
      ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i (B s) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)) μ :=
    aesm_finsetSum_apply (fun i _ => aesm_finsetSum_apply (fun j _ => by
      by_cases hh : 1 ≤ i ∧ i + j ≤ k
      · have hthis : (fun s : ℝ => (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.mixed j i (B s) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
            = fun s : ℝ => (Work.Spaces.mixed j i (B s) z θ * Work.Spaces.Wt α z θ) ^ 2 :=
          funext fun s => ite_eq_left hh
        rw [hthis]
        exact (((h j i (by omega)).mul_const (Work.Spaces.Wt α z θ)).pow 2)
      · have hthis : (fun s : ℝ => (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.mixed j i (B s) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
            = fun _ : ℝ => (0 : ℝ) :=
          funext fun s => ite_eq_right hh
        rw [hthis]
        exact MeasureTheory.aestronglyMeasurable_const))
  exact hA.add hB

theorem aesm_diff_family {α : ℝ} {k : ℕ} {δ : ℝ} {V : ℝ → ℝ → ℝ → ℝ} {W : ℝ → ℝ → ℝ}
    (hle : k ≤ 6)
    (hsmV : ∀ s ∈ Set.Icc 0 δ, Work.FTS.EllipticEst.SmoothOpen (V s))
    (hsmW : Work.FTS.EllipticEst.SmoothOpen W)
    (hmeasV : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (V s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc 0 δ))) :
    (∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ => Work.Spaces.mixed j i (fun z θ => V s z θ - W z θ) z θ)
        (MeasureTheory.volume.restrict (Set.Icc 0 δ))) ∧
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => Work.Spaces.HkIntegrand α k
        (fun z θ => V p.1 z θ - W z θ) p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict (Set.Icc 0 δ)).prod
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
  classical
  set A : Set ℝ := Set.Icc 0 δ with hAdef
  have hAmeas : MeasurableSet A := by rw [hAdef]; exact measurableSet_Icc
  have haeA : ∀ᵐ s ∂(MeasureTheory.volume.restrict A), s ∈ A := by
    rw [MeasureTheory.ae_restrict_iff' hAmeas]
    exact Filter.Eventually.of_forall (fun s hs => hs)
  -- the difference of the two profiles is `C^∞` on the open quadrant
  have hsm_diff : ∀ s ∈ A, Work.FTS.EllipticEst.SmoothOpen (fun z θ => V s z θ - W z θ) := by
    intro s hs
    exact ContDiffOn.sub (hsmV s hs) hsmW
  -- **Part 1**: the mixed derivatives of the difference are a.e. strongly measurable
  have hpart1 : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ => Work.Spaces.mixed j i (fun z θ => V s z θ - W z θ) z θ)
        (MeasureTheory.volume.restrict A) := by
    intro j i hji z θ hzθ
    obtain ⟨hz0, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
    have haesm := (hmeasV j i hji z θ hzθ).sub
      (MeasureTheory.aestronglyMeasurable_const (b := Work.Spaces.mixed j i W z θ))
    refine haesm.congr ?_
    filter_upwards [haeA] with s hs
    exact (Work.FTS.StrongEps.EpsE4Thr.mixed_sub_of_contDiffOn_six (hji := by omega)
      (hz := hz0) (hθ := ⟨hθ0, hθ1⟩)
      (hA := (hsmV s hs).forall 6) (hB := hsmW.forall 6)).symm
  refine ⟨hpart1, ?_⟩
  -- pointwise (at a point of the quadrant) measurability of the `ℋ^k`-integrand
  have hpoint : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ => Work.Spaces.HkIntegrand α k
          (fun z θ => V s z θ - W z θ) z θ) (MeasureTheory.volume.restrict A) := by
    intro z θ hzθ
    exact aesm_HkIntegrand_of_slots_le (B := fun s z θ => V s z θ - W z θ)
      (fun j i hji => hpart1 j i hji z θ hzθ)
  -- the integrand, truncated to the open quadrant in `(z,θ)`
  set g₂ : ℝ → ℝ → ℝ → ℝ := fun s z θ =>
      if z ∈ Set.Ioi 0 ∧ θ ∈ Set.Ioo 0 (Real.pi / 2) then
        Work.Spaces.HkIntegrand α k (fun z θ => V s z θ - W z θ) z θ else 0 with hg₂
  have hcont₂ : ∀ s ∈ A, ContinuousOn (fun q : ℝ × ℝ => g₂ s q.1 q.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    intro s hs
    refine ((hsm_diff s hs).continuousOn_HkIntegrand α k).congr ?_
    intro q hq
    obtain ⟨hq1, hq2⟩ := Set.mem_prod.mp hq
    have hcond : q.1 ∈ Set.Ioi 0 ∧ q.2 ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hq1, hq2⟩
    simp only [hg₂]
    rw [ite_eq_left hcond]
  have hzero₂ : ∀ s ∈ A, ∀ q : ℝ × ℝ, q ∉ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) →
      g₂ s q.1 q.2 = 0 := by
    intro s _ q hq
    have hq' : ¬ (q.1 ∈ Set.Ioi 0 ∧ q.2 ∈ Set.Ioo 0 (Real.pi / 2)) := by
      simpa only [Set.mem_prod] using hq
    simp only [hg₂, ite_eq_right hq']
  have hmeas₂ : ∀ q : ℝ × ℝ, MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => g₂ s q.1 q.2) (MeasureTheory.volume.restrict A) := by
    intro q
    by_cases hq : q ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))
    · obtain ⟨hq1, hq2⟩ := Set.mem_prod.mp hq
      have hcond : q.1 ∈ Set.Ioi 0 ∧ q.2 ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hq1, hq2⟩
      have hEq : (fun s : ℝ => g₂ s q.1 q.2)
          = fun s : ℝ => Work.Spaces.HkIntegrand α k
              (fun z θ => V s z θ - W z θ) q.1 q.2 := by
        funext s
        simp only [hg₂]
        rw [ite_eq_left hcond]
      rw [hEq]
      exact hpoint q.1 q.2 hq
    · have hq' : ¬ (q.1 ∈ Set.Ioi 0 ∧ q.2 ∈ Set.Ioo 0 (Real.pi / 2)) := by
        simpa only [Set.mem_prod] using hq
      have hEq : (fun s : ℝ => g₂ s q.1 q.2) = fun _ => (0 : ℝ) := by
        funext s
        simp only [hg₂, ite_eq_right hq']
      rw [hEq]
      exact MeasureTheory.aestronglyMeasurable_const
  -- Carathéodory: joint measurability of the truncated integrand
  have hbig := Work.FTS.EpsEngine.aesm_uncurry_restricted (A := A) hAmeas
    hcont₂ hzero₂ hmeas₂
  -- the angular product measure is that of the open quadrant inside the closed box
  have hIZ : ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
      = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    rw [MeasureTheory.Measure.prod_restrict (μ := MeasureTheory.volume)
      (ν := MeasureTheory.volume) Work.Spaces.Iz Work.Spaces.Iθ]
    refine MeasureTheory.Measure.restrict_congr_set ?_
    exact MeasureTheory.Measure.set_prod_ae_eq (MeasureTheory.Ioi_ae_eq_Ici).symm
      (MeasureTheory.Ioo_ae_eq_Icc).symm
  have hν : ((MeasureTheory.volume.restrict A).prod
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ((MeasureTheory.volume : Measure ℝ).prod
          (MeasureTheory.volume.prod MeasureTheory.volume)).restrict
          (A ×ˢ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) := by
    rw [hIZ]
    rw [MeasureTheory.Measure.prod_restrict (μ := MeasureTheory.volume)
      (ν := MeasureTheory.volume.prod MeasureTheory.volume) A
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))]
  have hle : ((MeasureTheory.volume.restrict A).prod
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      ≤ (MeasureTheory.volume.restrict A).prod (MeasureTheory.volume : Measure (ℝ × ℝ)) :=
    MeasureTheory.Measure.prod_mono le_rfl
      (MeasureTheory.Measure.prod_mono MeasureTheory.Measure.restrict_le_self
        MeasureTheory.Measure.restrict_le_self)
  refine (hbig.mono_measure hle).congr ?_
  rw [hν, Filter.EventuallyEq,
    MeasureTheory.ae_restrict_iff' (hAmeas.prod (measurableSet_Ioi.prod measurableSet_Ioo))]
  exact Filter.Eventually.of_forall (fun p hp => by
    obtain ⟨_, hpQ⟩ := hp
    obtain ⟨hpQ1, hpQ2⟩ := Set.mem_prod.mp hpQ
    have hcond : p.2.1 ∈ Set.Ioi 0 ∧ p.2.2 ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hpQ1, hpQ2⟩
    simp only [hg₂]
    rw [ite_eq_left hcond])

end Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.sup_mixed_diff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits

theorem sup_mixed_diff {k : ℕ} {δ : ℝ} {V : ℝ → ℝ → ℝ → ℝ} {W : ℝ → ℝ → ℝ}
    (hle : k ≤ 6)
    (hsmV : ∀ s ∈ Set.Icc 0 δ, Work.FTS.EllipticEst.SmoothOpen (V s))
    (hsmW : Work.FTS.EllipticEst.SmoothOpen W)
    (hsupV : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc 0 δ, ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ k →
        |Work.Spaces.mixed j i (V s) q.1 q.2| ≤ C)
    (hsupW : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ k →
        |Work.Spaces.mixed j i W q.1 q.2| ≤ C) :
    ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc 0 δ, ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ k →
        |Work.Spaces.mixed j i (fun z θ => V s z θ - W z θ) q.1 q.2| ≤ C := by
  intro K hKc hKQ
  obtain ⟨CV, hCV0, hCV⟩ := hsupV K hKc hKQ
  obtain ⟨CW, hCW0, hCW⟩ := hsupW K hKc hKQ
  refine ⟨CV + CW, add_nonneg hCV0 hCW0, ?_⟩
  intro s hs q hqK j i hji
  have hqQ : q ∈ Work.FTS.EllipticEst.Q0 := hKQ hqK
  rw [Work.FTS.EllipticEst.mem_Q0] at hqQ
  obtain ⟨hz, hθ0, hθπ⟩ := hqQ
  have hji6 : j + i ≤ 6 := le_trans hji hle
  rw [Work.FTS.StrongEps.EpsE4Thr.mixed_sub_of_contDiffOn_six hji6 hz ⟨hθ0, hθπ⟩
      (Work.FTS.EllipticEst.SmoothOpen.forall (hsmV s hs) 6)
      (Work.FTS.EllipticEst.SmoothOpen.forall hsmW 6)]
  have htri : |Work.Spaces.mixed j i (V s) q.1 q.2 - Work.Spaces.mixed j i W q.1 q.2|
      ≤ |Work.Spaces.mixed j i (V s) q.1 q.2| + |Work.Spaces.mixed j i W q.1 q.2| := by
    simpa [sub_eq_add_neg] using abs_add_le (Work.Spaces.mixed j i (V s) q.1 q.2)
      (-(Work.Spaces.mixed j i W q.1 q.2))
  exact le_trans htri (add_le_add (hCV s hs q hqK j i hji) (hCW q hqK j i hji))

end Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.RadMem5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5

set_option autoImplicit false

/-- The level-`5` radial density `Σ_{i≤5} (D_z^i r)² w²`. -/
def Rint5 (r : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (5 + 1), (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2

theorem Rint5_nonneg (r : ℝ → ℝ) (z : ℝ) : 0 ≤ Rint5 r z :=
  Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The exact value of `HkSq α 5` of a radial lift. -/
theorem HkSq_rad_eq5 (α : ℝ) (r : ℝ → ℝ) :
    Work.Spaces.HkSq α 5 (fun z (_ : ℝ) => r z)
      = (∫ z in Work.Spaces.Iz, Rint5 r z)
          * Work.FTS.Nonlinear.RadialProd.Kth := by
  rw [Work.Elliptic.HkSq_rad α 5 r]
  simp only [Rint5, Work.FTS.Nonlinear.RadialProd.Kth, Work.FTS.Nonlinear.RadialProd.smE]

/-- `K_θ = ∫_θ sin(2θ)^{-η} ≤ 10⁴`. -/
theorem Kth_le_1e4 : Work.FTS.Nonlinear.RadialProd.Kth ≤ 10 ^ 4 := by
  have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
    (by linarith [Work.Spaces.eta_lt_one]) (by linarith [Work.Spaces.eta_pos])).2
  have hexp : -(Work.Spaces.eta) + 1 = (1 : ℝ) / 100 := by rw [Work.Spaces.eta]; norm_num
  rw [hexp] at h
  have h2 : (100 : ℝ) / ((1 : ℝ) / 100) = 10000 := by norm_num
  rw [h2] at h
  norm_num at h ⊢
  simpa only [Work.FTS.Nonlinear.RadialProd.Kth, Work.FTS.Nonlinear.RadialProd.smE] using h

/-- The `z`-integral of `(1/(1+z))²` over `Iz = [0,∞)` is at most `2`. -/
theorem int_inv_one_add_sq_Iz :
    (∫ z in Work.Spaces.Iz, (1 / (1 + z)) ^ 2) ≤ 2 := by
  have hbd : (∫ z in (Set.Ioi (0 : ℝ)), (1 / (1 + z)) ^ 2) ≤ 2 :=
    Work.FTS.H2.InvOneAddSq.2
  rw [MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))] at hbd
  exact hbd

/-- The `ℋ⁵`-density `Rint5 r` of a radial profile with `|D_z^i r z| ≤ C0·z²/(1+z)³` is
integrable on `Iz`, with integral at most `12·C0²`. -/
theorem Rint5_integral_le {r : ℝ → ℝ} {C0 : ℝ} (hC0 : 0 < C0)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n r (Set.Ioi 0))
    (hb : ∀ i : ℕ, i ≤ 5 → ∀ z : ℝ, 0 ≤ z →
      |Work.Elliptic.DzdIter i r z| ≤ C0 * z ^ 2 / (1 + z) ^ 3) :
    (∫ z in Work.Spaces.Iz, Rint5 r z) ≤ 12 * C0 ^ 2 := by
  -- ### the pointwise slot bound
  have hslot : ∀ (i : ℕ), i ≤ 5 → ∀ z ∈ Work.Spaces.Iz,
      (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2 ≤ (C0 / (1 + z)) ^ 2 := by
    intro i hi z hz
    have hz0 : 0 ≤ z := hz
    have habs := hb i hi z hz0
    have hsq : (Work.Elliptic.DzdIter i r z) ^ 2 ≤ (C0 * z ^ 2 / (1 + z) ^ 3) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    have hprod := mul_le_mul_of_nonneg_right hsq (sq_nonneg (Work.Spaces.w z))
    rcases eq_or_lt_of_le hz0 with hz' | hz'
    · rw [← hz']
      have hw0 : Work.Spaces.w (0 : ℝ) = 0 := by simp [Work.Spaces.w]
      rw [hw0]
      simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero, div_one]
      exact sq_nonneg C0
    · refine hprod.trans (le_of_eq ?_)
      rw [Work.Spaces.w]
      field_simp
  have hsum_le : ∀ z ∈ Work.Spaces.Iz, Rint5 r z ≤ 6 * (C0 / (1 + z)) ^ 2 := by
    intro z hz
    calc Rint5 r z
        ≤ ∑ _i ∈ Finset.range 6, (C0 / (1 + z)) ^ 2 :=
          Finset.sum_le_sum (fun i hi => hslot i (by
            have := Finset.mem_range.mp hi; omega) z hz)
      _ = 6 * (C0 / (1 + z)) ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
  -- ### integrability of the majorant
  have hmaj_int : MeasureTheory.IntegrableOn
      (fun z : ℝ => 6 * (C0 / (1 + z)) ^ 2) Work.Spaces.Iz := by
    have h1 : MeasureTheory.Integrable (fun z : ℝ =>
        (6 * C0 ^ 2) * (1 / (1 + z)) ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      Work.FTS.H2.InvOneAddSq.1.const_mul _
    have h2 : MeasureTheory.Integrable (fun z : ℝ => 6 * (C0 / (1 + z)) ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      h1.congr (Filter.Eventually.of_forall fun z => by ring)
    rw [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))] at h2
    exact h2
  -- ### the integral comparison
  have hmono : (∫ z in Work.Spaces.Iz, Rint5 r z)
      ≤ ∫ z in Work.Spaces.Iz, 6 * (C0 / (1 + z)) ^ 2 :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => Rint5_nonneg r z) hmaj_int
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
        exact hsum_le z hz)
  have hInt2 : (∫ z in Work.Spaces.Iz, 6 * (C0 / (1 + z)) ^ 2)
      = 6 * C0 ^ 2 * ∫ z in Work.Spaces.Iz, (1 / (1 + z)) ^ 2 := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    ring
  have hIz_le2 : (∫ z in Work.Spaces.Iz, (1 / (1 + z)) ^ 2) ≤ 2 := int_inv_one_add_sq_Iz
  rw [hInt2] at hmono
  have h6 : 6 * C0 ^ 2 * (∫ z in Work.Spaces.Iz, (1 / (1 + z)) ^ 2) ≤ 6 * C0 ^ 2 * 2 :=
    mul_le_mul_of_nonneg_left hIz_le2 (by positivity)
  linarith

/-- **The level-`5` radial norm bound.**  A radial profile with
`|D_z^i r z| ≤ C0·z²/(1+z)³` for `i ≤ 5` has an `ℋ⁵`-lift whose level-`5` norm is at most
`√(12·10⁴)·C0`. -/
theorem RadMem5 {r : ℝ → ℝ} {C0 : ℝ} (hC0 : 0 < C0)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n r (Set.Ioi 0))
    (hb : ∀ i : ℕ, i ≤ 5 → ∀ z : ℝ, 0 ≤ z →
      |Work.Elliptic.DzdIter i r z| ≤ C0 * z ^ 2 / (1 + z) ^ 3) :
    ∃ Cr : ℝ, 0 < Cr ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
      Work.Spaces.HkMem α 5 (fun z (_ : ℝ) => r z) ∧
      Work.Spaces.HkNorm α 5 (fun z (_ : ℝ) => r z) ≤ Cr * C0 := by
  have hRint5_le := Rint5_integral_le hC0 hsm hb
  obtain ⟨C', hC'pos, hgen⟩ := RadHkMemXn_gen (r := r) (C := C0) (k := 5) hC0 hsm hb
  refine ⟨Real.sqrt (12 * 10 ^ 4), by positivity, fun α hαI => ?_⟩
  obtain ⟨hmem, _⟩ := hgen α hαI
  refine ⟨hmem, ?_⟩
  have hKth0 : 0 ≤ Work.FTS.Nonlinear.RadialProd.Kth :=
    le_trans zero_le_one Work.FTS.Nonlinear.RadialProd.one_le_Kth
  have hKth_le : Work.FTS.Nonlinear.RadialProd.Kth ≤ 10 ^ 4 := Kth_le_1e4
  have hRint5nn : 0 ≤ ∫ z in Work.Spaces.Iz, Rint5 r z :=
    MeasureTheory.integral_nonneg fun z => Rint5_nonneg r z
  rw [show Work.Spaces.HkNorm α 5 (fun z (_ : ℝ) => r z)
      = Real.sqrt (Work.Spaces.HkSq α 5 (fun z (_ : ℝ) => r z)) from rfl, HkSq_rad_eq5]
  calc Real.sqrt ((∫ z in Work.Spaces.Iz, Rint5 r z)
        * Work.FTS.Nonlinear.RadialProd.Kth)
      ≤ Real.sqrt ((12 * C0 ^ 2) * 10 ^ 4) :=
        Real.sqrt_le_sqrt (mul_le_mul hRint5_le hKth_le hKth0 (by positivity))
    _ = Real.sqrt (12 * 10 ^ 4) * C0 := by
        rw [show (12 * C0 ^ 2) * 10 ^ 4 = (12 * 10 ^ 4) * C0 ^ 2 by ring,
          Real.sqrt_mul (by norm_num), Real.sqrt_sq hC0.le]

end Work.FTS.StrongEps.H5
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.WProd5.dzIter_w_mean_le5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.H5.WProd5

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- The squared radial slot `(D_z^d g)²` of order `d ≤ 5` is dominated by the level-`5`
integrand, on the open quadrant: `HkIntegrand α 5 g` contains the term
`(D_z^d g · w/ sin(2θ)^{η/2})²` and the multiplier is `≥ 1`
(`w z ≥ 1` and `sin(2θ)^{η/2} ≤ 1`). -/
private theorem dzIter_sq_le_HkIntegrand5 {α : ℝ} {g : ℝ → ℝ → ℝ} {d : ℕ} (hd : d ≤ 5)
    {z σ : ℝ} (hz : 0 < z) (hσ : σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.DzIter d g z σ) ^ 2 ≤ Work.Spaces.HkIntegrand α 5 g z σ := by
  have hsin : 0 < Real.sin (2 * σ) :=
    Real.sin_pos_of_mem_Ioo ⟨by linarith [hσ.1], by linarith [hσ.2, Real.pi_pos]⟩
  have hspos : 0 < (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hsin _
  have hsle : (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one hsin.le (Real.sin_le_one _) (by norm_num [Work.Spaces.eta])
  have hz2 : 0 < z ^ 2 := by positivity
  have hw : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, one_le_div hz2]
    nlinarith
  have hmul : 1 ≤ Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2) := by
    rw [one_le_div hspos]
    linarith
  calc (Work.Spaces.DzIter d g z σ) ^ 2
      ≤ (Work.Spaces.DzIter d g z σ) ^ 2
          * (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
        le_mul_of_one_le_right (sq_nonneg _) (one_le_pow₀ hmul)
    _ = (Work.Spaces.DzIter d g z σ
          * (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α 5 g z σ :=
        Work.Spaces.sq_le_HkIntegrand_z α 5 g z σ d (by omega)

/-- **The mean-term form of the radial `D_z`-slot bound at level `5`.**

The literal `4 ↦ 5` shift of the *proved* `Work.FTS.OpenPkg.WProdWin.dzIter_w_mean_le`
(`Submission/Work/FTS/OpenPkg/WProdWin/dzIter_w_mean_le.lean`), and at the same time the
`6 ↦ 5` shift of the *proved* `Work.FTS.StrongPersist.H6Rows.WProd6.dzIter_w_mean_le6`
(`Submission/Work/FTS/StrongPersist/H6Rows/wprod6/dzIter_w_mean_le6.lean`): the same proof with
`HkMem α 4 → HkMem α 5` (so `d ≤ 3 → d ≤ 4`, since the `g`-slot `mixed d 1 g` needs
`1 + d ≤ 5`), and `HkIntegrand α 4 → HkIntegrand α 5`. -/
theorem dzIter_w_mean_le5 : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (g : ℝ → ℝ → ℝ) (d : ℕ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 5 g → d ≤ 4 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
        ≤ C * ((Work.Spaces.w z) ^ 2
              * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
            + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.OpenPkg.ProdOpen.sob_theta_mean
  refine ⟨C, hCpos, ?_⟩
  intro α g d hα hα1 hF hmem hd z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hwpos : 0 < Work.Spaces.w z := Work.FTS.OpenPkg.ProdOpen.w_pos_of_pos hz
  have hwne : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 hwpos.ne'
  -- the angular slice `h = D_z^d g (z, ·)` and its weighted derivative square
  set F : ℝ → ℝ := fun σ : ℝ =>
    (deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) with hFdef
  -- ### smoothness of the slice
  have hcurry := (hF.DzIter d).curry_θ hz
  have hder : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun σ' : ℝ => Work.Spaces.DzIter d g z σ')
        (deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') x) x :=
    fun x hx => ((hcurry.differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  have hcont : ContinuousOn (deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ'))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h : ContinuousOn (fun σ : ℝ => Work.Spaces.pth (Work.Spaces.DzIter d g) z σ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := ((hF.DzIter d).pth.curry_θ hz).continuousOn
    simpa only [Work.Spaces.pth] using h
  -- ### the a.e. identification of the derivative square with the mixed slot `(d,1)`
  have haeEq : ∀ᵐ σ ∂(volume.restrict Work.Spaces.Iθ),
      F σ = (Work.Spaces.mixed d 1 g z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
    filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ hσ
    have h := Work.FTS.OpenPkg.ProdOpen.deriv_mixed_weight α hF d 0 hz hσ
    simpa only [hFdef, Nat.zero_add, Work.Spaces.mixed_zero_right] using h
  -- ### the weight identity: `(w z)² · (mixed d 1 g)² sin^{-γ} = (mixed d 1 g · W)²`
  have hkey : ∀ σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Spaces.w z) ^ 2 * ((Work.Spaces.mixed d 1 g z σ) ^ 2
          * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)))
        = (Work.Spaces.mixed d 1 g z σ * Work.Spaces.Wt α z σ) ^ 2 := by
    intro σ hσ
    have hsin := Work.FTS.OpenPkg.ProdOpen.sin_two_pos hσ
    rw [mul_pow, Work.H2.T1Q.Wt_sq_eq α z σ hsin]
    ring
  have haeW : ∀ᵐ σ ∂(volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.w z) ^ 2 * F σ
        = (Work.Spaces.mixed d 1 g z σ * Work.Spaces.Wt α z σ) ^ 2 := by
    filter_upwards [haeEq, Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ he hσ
    rw [he, hkey σ hσ]
  -- ### integrability of the two slice functions
  have hint1 : IntegrableOn (fun σ : ℝ => (Work.Spaces.DzIter d g z σ) ^ 2)
      Work.Spaces.Iθ := by
    refine Integrable.mono' (hmem.1 z hz.le)
      (Work.H2.T1Q.aesm_Iθ_of_continuousOn (hcurry.continuousOn.pow 2)) ?_
    filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ hσ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact dzIter_sq_le_HkIntegrand5 (by omega) hz hσ
  have hint2 : IntegrableOn F Work.Spaces.Iθ := by
    refine Integrable.mono' ((hmem.1 z hz.le).const_mul ((Work.Spaces.w z) ^ 2)⁻¹) ?_ ?_
    · rw [hFdef]
      refine Work.H2.T1Q.aesm_Iθ_of_continuousOn ?_
      have hbase : Continuous fun σ : ℝ => Real.sin (2 * σ) := by fun_prop
      exact (((hF.DzIter d).pth.curry_θ hz).continuousOn.pow 2).mul
        (hbase.continuousOn.rpow_const
          (fun σ hσ => Or.inl (ne_of_gt (Work.FTS.OpenPkg.ProdOpen.sin_two_pos hσ))))
    · filter_upwards [haeEq, Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ he hσ
      have hsin := Work.FTS.OpenPkg.ProdOpen.sin_two_pos hσ
      have hnn : 0 ≤ F σ := by
        rw [he]
        exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _)
      rw [Real.norm_of_nonneg hnn, he]
      have hX : (Work.Spaces.mixed d 1 g z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          = ((Work.Spaces.w z) ^ 2)⁻¹ * ((Work.Spaces.w z) ^ 2
              * ((Work.Spaces.mixed d 1 g z σ) ^ 2
                * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)))) := by
        rw [← mul_assoc, inv_mul_cancel₀ hwne, one_mul]
      rw [hX]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (sq_nonneg (Work.Spaces.w z)))
      rw [hkey σ hσ]
      exact Work.Spaces.sq_le_HkIntegrand_mixed α 5 g z σ 1 d (by norm_num) (by omega)
  -- ### the exact value of the derivative term: `(w z)² ∫ F = Aang α g d z`
  have hAang : (Work.Spaces.w z) ^ 2 * (∫ σ in Work.Spaces.Iθ, F σ)
      = Work.FTS.H2.WPQ.Aang α g d z := by
    have hstep : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * F σ)
        = (Work.Spaces.w z) ^ 2 * (∫ σ in Work.Spaces.Iθ, F σ) :=
      MeasureTheory.integral_const_mul (μ := volume.restrict Work.Spaces.Iθ) _ _
    rw [← hstep, Work.FTS.H2.WPQ.Aang]
    exact MeasureTheory.integral_congr_ae haeW
  -- ### the angular inequality and the assembly
  have hmain := hC α (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') θ hα hα1 hθ
    hder hcont hint1 hint2
  have hmain' : (Work.Spaces.DzIter d g z θ) ^ 2
      ≤ C * ((∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
          + (Work.Spaces.gam α - 1)⁻¹ * (∫ σ in Work.Spaces.Iθ, F σ)) := by
    simpa only [hFdef] using hmain
  calc (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter d g z θ) ^ 2 := by ring
    _ ≤ (Work.Spaces.w z) ^ 2 * (C * ((∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
          + (Work.Spaces.gam α - 1)⁻¹ * (∫ σ in Work.Spaces.Iθ, F σ))) :=
        mul_le_mul_of_nonneg_left hmain' (sq_nonneg _)
    _ = C * ((Work.Spaces.w z) ^ 2 * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
          + (Work.Spaces.gam α - 1)⁻¹ * ((Work.Spaces.w z) ^ 2
              * (∫ σ in Work.Spaces.Iθ, F σ))) := by ring
    _ = C * ((Work.Spaces.w z) ^ 2 * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
          + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z) := by rw [hAang]

end Work.FTS.StrongEps.H5.WProd5
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.WProd5.prod_majorant_winf5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5.WProd5

open Work.Spaces

set_option linter.unusedVariables false

/-- **The pointwise majorant of the `𝒲^{5,∞}`-priced product rule.**

The literal `6 ↦ 5` shift (`7 ↦ 6` pure slots, `49 ↦ 36` mixed slots) of the *proved*
`Work.FTS.StrongPersist.H6Rows.WProd6.prod_majorant_winf6`
(`Submission/Work/FTS/StrongPersist/H6Rows/wprod6/Majorant6.lean`), which is itself the level-six
shift of the *proved* `Work.FTS.OpenPkg.prod_majorant_winf`
(`Submission/Work/FTS/OpenPkg/wprod_field_winf.lean`).  Summing the six pure `D_z`-slots
(`hzslot`) and the at most 36 mixed slots (`hmslot`) of `HkIntegrand α 5 (f·g)`, using
`HkIntegrand α 5 g ≤ GmajW5 α g` (from `WProd5.Gmaj5`). -/
theorem prod_majorant_winf5 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hfm : Work.Spaces.WlInfMem α 5 f)
    (hgsm : Work.FTS.EllipticEst.SmoothOpen g) (hgm : Work.Spaces.HkMem α 5 g)
    {Cz Cm : ℝ} (hCz0 : 0 < Cz) (hCm0 : 0 < Cm)
    (hzslot : ∀ i : ℕ, i ≤ 5 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Cz * (Work.Spaces.WlInf α 5 f) ^ 2 * Work.Spaces.HkIntegrand α 5 g z θ)
    (hmslot : ∀ I J : ℕ, 1 ≤ I → I + J ≤ 5 → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 →
      (Work.Spaces.mixed J I (fun z θ => f z θ * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Cm * (Work.Spaces.WlInf α 5 f) ^ 2 * Work.FTS.StrongEps.H5.WProd5.GmajW5 α g z θ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 5 (fun z θ => f z θ * g z θ) z θ
        ≤ (6 * Cz + 36 * Cm) * (Work.Spaces.WlInf α 5 f) ^ 2
            * Work.FTS.StrongEps.H5.WProd5.GmajW5 α g z θ := by
  intro z hz θ hθ
  have hGnn : 0 ≤ GmajW5 α g z θ := GmajW5_nonneg hα g hθ
  have hbase : 0 ≤ (6 * Cz + 36 * Cm) * (WlInf α 5 f) ^ 2 * GmajW5 α g z θ :=
    mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) hGnn
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hzz | hzpos
  · have hz0 : z = 0 := hzz.symm
    subst hz0
    rw [HkIntegrand_zero_z]
    exact hbase
  · by_cases hθi : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
    · have hGle : HkIntegrand α 5 g z θ ≤ GmajW5 α g z θ :=
        HkIntegrand_le_GmajW5 hα g hθ
      have hsum1 : (∑ i ∈ Finset.range (5 + 1),
            (DzIter i (fun z θ => f z θ * g z θ) z θ
              * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2)
          ≤ 6 * (Cz * (WlInf α 5 f) ^ 2 * GmajW5 α g z θ) := by
        calc (∑ i ∈ Finset.range (5 + 1),
              (DzIter i (fun z θ => f z θ * g z θ) z θ
                * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2)
            ≤ ∑ _i ∈ Finset.range (5 + 1), (Cz * (WlInf α 5 f) ^ 2
                * GmajW5 α g z θ) := by
              refine Finset.sum_le_sum fun i hi => ?_
              have hi5 : i ≤ 5 := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
              refine le_trans (hzslot i hi5 z θ hzpos hθi.1 hθi.2) ?_
              exact mul_le_mul_of_nonneg_left hGle (mul_nonneg (le_of_lt hCz0) (sq_nonneg _))
          _ = 6 * (Cz * (WlInf α 5 f) ^ 2 * GmajW5 α g z θ) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
      have hsum2 : (∑ i ∈ Finset.range (5 + 1), ∑ j ∈ Finset.range (5 + 1),
            (if 1 ≤ i ∧ i + j ≤ 5 then
              (mixed j i (fun z θ => f z θ * g z θ) z θ
                * Wt α z θ) ^ 2 else 0))
          ≤ 36 * (Cm * (WlInf α 5 f) ^ 2 * GmajW5 α g z θ) := by
        calc (∑ i ∈ Finset.range (5 + 1), ∑ j ∈ Finset.range (5 + 1),
              (if 1 ≤ i ∧ i + j ≤ 5 then
                (mixed j i (fun z θ => f z θ * g z θ) z θ
                  * Wt α z θ) ^ 2 else 0))
            ≤ ∑ _i ∈ Finset.range (5 + 1), ∑ _j ∈ Finset.range (5 + 1),
                (Cm * (WlInf α 5 f) ^ 2 * GmajW5 α g z θ) := by
              refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
              by_cases hc : 1 ≤ i ∧ i + j ≤ 5
              · rw [if_pos hc]
                exact hmslot i j hc.1 hc.2 z θ hzpos hθi.1 hθi.2
              · rw [if_neg hc]
                exact mul_nonneg (mul_nonneg (le_of_lt hCm0) (sq_nonneg _)) hGnn
          _ = 36 * (Cm * (WlInf α 5 f) ^ 2 * GmajW5 α g z θ) := by
              simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      rw [HkIntegrand]
      calc (∑ i ∈ Finset.range (5 + 1),
            (DzIter i (fun z θ => f z θ * g z θ) z θ
              * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2)
          + (∑ i ∈ Finset.range (5 + 1), ∑ j ∈ Finset.range (5 + 1),
              (if 1 ≤ i ∧ i + j ≤ 5 then
                (mixed j i (fun z θ => f z θ * g z θ) z θ
                  * Wt α z θ) ^ 2 else 0))
          ≤ 6 * (Cz * (WlInf α 5 f) ^ 2 * GmajW5 α g z θ)
            + 36 * (Cm * (WlInf α 5 f) ^ 2 * GmajW5 α g z θ) :=
            add_le_add hsum1 hsum2
        _ = (6 * Cz + 36 * Cm) * (WlInf α 5 f) ^ 2 * GmajW5 α g z θ := by
            ring
    · have hsin : Real.sin (2 * θ) = 0 := sin_two_eq_zero_of_not_Ioo hθ hθi
      rw [HkIntegrand5_eq_zero_of_sin_two_eq_zero (α := α) (F := fun z θ => f z θ * g z θ)
        (by rw [gam]; linarith) hsin]
      exact hbase

end Work.FTS.StrongEps.H5.WProd5
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.WProd5.zslot_le_winf5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.H5.WProd5

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

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

/-- **The radial `D_z`-slots of the level-`5` `𝒲^{5,∞}`-priced product rule.**

The literal `4 ↦ 5` shift of the *proved* `Work.FTS.OpenPkg.WProdWin.zslot_le_winf`
(`Submission/Work/FTS/OpenPkg/WProdWin/zslot_le_winf.lean`): the same proof with
`i ≤ 4 → i ≤ 5`, `WlInfMem α 4 → WlInfMem α 5`, `HkIntegrand α 4 → HkIntegrand α 5`, and the
`f`-factor bound taken from `Pointwise5.dzIter_le_WlInf5` (`|D_z^b f| ≤ 100 |f|_{𝒲^{5,∞}}`,
`b ≤ 5`) instead of `Work.FTS.OpenPkg.DzIter_le_WlInf_open`.  The binomial-coefficient bound
`Work.Spaces.choose_sq_le_256` is stated for `n ≤ 4`; at level `5` one needs the trivial
extension to `n ≤ 5` (`C(5,2) = 10`, so `10² = 100 ≤ 256`), which can be proved locally. -/
theorem zslot_le_winf5 : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 5 f →
      Work.FTS.EllipticEst.SmoothOpen g →
      ∀ i : ℕ, i ≤ 5 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ C * (Work.Spaces.WlInf α 5 f) ^ 2 * Work.Spaces.HkIntegrand α 5 g z θ := by
  refine ⟨10 ^ 8, by norm_num, ?_⟩
  intro α f g _hα _hα1 hf hfm hg i hi z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hW : 0 ≤ Work.Spaces.WlInf α 5 f := Work.Spaces.WlInf_nonneg α 5 f hfm
  set Hv : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hHv
  -- the Leibniz expansion of `D_z^i (f·g)` in the open quadrant
  have heq := Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz i f g hf hg z θ hz hθ0 hθ1
  have hsplit : (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ * Hv) ^ 2
      = (∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
            * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2 := by
    rw [heq, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl (fun b _ => by ring)
  rw [hsplit]
  -- Cauchy-Schwarz for the finite sum
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
    (f := fun b => ((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
      * (Work.Spaces.DzIter (i - b) g z θ * Hv))
  have hcard : (((Finset.range (i + 1)).card : ℕ) : ℝ) = (i : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  -- the per-term bound: the `f`-factor costs `100 |f|_𝒲`, the binomial coefficient costs `16`
  have hper : ∀ b ∈ Finset.range (i + 1),
      (((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
          * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2
        ≤ 2560000 * (Work.Spaces.WlInf α 5 f) ^ 2
          * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by
    intro b hb
    have hbi : b ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hDf : |Work.Spaces.DzIter b f z θ| ≤ 100 * Work.Spaces.WlInf α 5 f :=
      dzIter_le_WlInf5 hf hfm (by omega) hz hθ
    have hx : (Work.Spaces.DzIter b f z θ) ^ 2
        ≤ (100 * Work.Spaces.WlInf α 5 f) ^ 2 := by
      have hB : (0 : ℝ) ≤ 100 * Work.Spaces.WlInf α 5 f := mul_nonneg (by norm_num) hW
      have h1 := (abs_le.mp hDf).1
      have h2 := (abs_le.mp hDf).2
      nlinarith [hB, h1, h2]
    have hch : ((i.choose b : ℝ)) ^ 2 ≤ 256 := choose_sq_le_256_five i b hbi hi
    calc (((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
          * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2
        = ((i.choose b : ℝ)) ^ 2 * (Work.Spaces.DzIter b f z θ) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by ring
      _ ≤ 256 * (100 * Work.Spaces.WlInf α 5 f) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by gcongr
      _ = 2560000 * (Work.Spaces.WlInf α 5 f) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by ring
  -- each surviving `g`-factor is a pure slot of `HkIntegrand α 5 g`
  have hsumsq : ∑ b ∈ Finset.range (i + 1),
        (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2
      ≤ 6 * Work.Spaces.HkIntegrand α 5 g z θ := by
    calc ∑ b ∈ Finset.range (i + 1), (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2
        ≤ ∑ _b ∈ Finset.range (i + 1), Work.Spaces.HkIntegrand α 5 g z θ :=
          Finset.sum_le_sum (fun b _ =>
            Work.Spaces.sq_le_HkIntegrand_z α 5 g z θ (i - b) (by omega))
      _ = ((i : ℝ) + 1) * Work.Spaces.HkIntegrand α 5 g z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ 6 * Work.Spaces.HkIntegrand α 5 g z θ := by
          have hnn := Work.Spaces.HkIntegrand_nonneg α 5 g z θ
          have hI2 : (i : ℝ) + 1 ≤ 6 := by exact_mod_cast (by omega : i + 1 ≤ 6)
          nlinarith
  calc (∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
            * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2
      ≤ (((Finset.range (i + 1)).card : ℕ) : ℝ) *
          ∑ b ∈ Finset.range (i + 1),
            (((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
              * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2 := hcs
    _ ≤ ((i : ℝ) + 1) * ∑ b ∈ Finset.range (i + 1),
          (2560000 * (Work.Spaces.WlInf α 5 f) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2) := by
        rw [hcard]
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hper) (by positivity)
    _ = 2560000 * (Work.Spaces.WlInf α 5 f) ^ 2 * (((i : ℝ) + 1)
          * ∑ b ∈ Finset.range (i + 1), (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ 2560000 * (Work.Spaces.WlInf α 5 f) ^ 2
          * (6 * (6 * Work.Spaces.HkIntegrand α 5 g z θ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hI2 : (i : ℝ) + 1 ≤ 6 := by exact_mod_cast (by omega : i + 1 ≤ 6)
        exact mul_le_mul hI2 hsumsq (Finset.sum_nonneg (fun b _ => sq_nonneg _)) (by norm_num)
    _ ≤ 10 ^ 8 * (Work.Spaces.WlInf α 5 f) ^ 2 * Work.Spaces.HkIntegrand α 5 g z θ := by
        have hnn := Work.Spaces.HkIntegrand_nonneg α 5 g z θ
        have h2 : 0 ≤ (Work.Spaces.WlInf α 5 f) ^ 2 := sq_nonneg _
        have hh : 2560000 * (Work.Spaces.WlInf α 5 f) ^ 2
              * (6 * (6 * Work.Spaces.HkIntegrand α 5 g z θ))
            = 92160000 * ((Work.Spaces.WlInf α 5 f) ^ 2
              * Work.Spaces.HkIntegrand α 5 g z θ) := by ring
        rw [hh, show (10 : ℝ) ^ 8 * (Work.Spaces.WlInf α 5 f) ^ 2
              * Work.Spaces.HkIntegrand α 5 g z θ
            = 10 ^ 8 * ((Work.Spaces.WlInf α 5 f) ^ 2
              * Work.Spaces.HkIntegrand α 5 g z θ) from by ring]
        exact mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg h2 hnn)

end Work.FTS.StrongEps.H5.WProd5
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.Zop_zdiv_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux

/-- **Boundedness of the `Zop`-iterates of `z ↦ z/(1+z)²` up to order six on `[0,∞)`.**

`Work.Spaces.Zop u = (z ↦ z·u'(z))` is the one-dimensional radial derivation.  The profile
`φ(z) = z/(1+z)²` is the Möbius-chart evaluation `gpoly Pphi` of `Pphi = ¼(1 - X²)`
(`Work.FTS.CoercivityFix.E2Bound.gpoly_Pphi`), and `Zop` intertwines the chart evaluation with
the polynomial map `P ↦ ½(1 - X²)·P'`; hence every iterate is a polynomial in the bounded
chart variable `(z-1)/(z+1) ∈ (-1,1)` for `z > 0`, and bounded there by the sum of the
absolute values of its coefficients.  This is exactly `zop_phi_bound`, stated on the closed
half-line: at the remaining point `z = 0` every iterate of order `≥ 1` vanishes because `Zop`
carries a factor `z`, and order `0` contributes `φ(0) = 0`. -/
theorem Zop_zdiv_bound : ∃ K : ℝ, 0 < K ∧ ∀ b ≤ 6, ∀ z : ℝ, 0 ≤ z →
    |Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z| ≤ K := by
  obtain ⟨K, hK0, hKb⟩ := Work.FTS.CoercivityFix.E2Bound.zop_phi_bound 6
  refine ⟨K + 1, by linarith, ?_⟩
  intro b hb z hz
  rcases eq_or_lt_of_le hz with hz0 | hzpos
  · -- the endpoint `z = 0`: the linear factor `z` of `Zop` kills every iterate of order `≥ 1`
    rw [← hz0]
    rcases Nat.eq_zero_or_pos b with hb0 | hbpos
    · rw [hb0, Function.iterate_zero_apply]
      have h0 : (0 : ℝ) / (1 + 0) ^ 2 = 0 := by norm_num
      rw [h0, abs_zero]
      linarith
    · rw [Work.FTS.StrongPersist.L6Aux.Zop_iterate_zero_of_pos
            (fun z : ℝ => z / (1 + z) ^ 2) hbpos, abs_zero]
      linarith
  · -- `z > 0`: the Möbius-chart bound of `zop_phi_bound`
    exact le_trans (hKb b hb z hzpos) (by linarith)

end Work.FTS.StrongPersist.H6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.wprod6.dzIter_w_mean_le6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.wprod6

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

theorem dzIter_w_mean_le6 : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (g : ℝ → ℝ → ℝ) (d : ℕ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g → d ≤ 5 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
        ≤ C * ((Work.Spaces.w z) ^ 2
              * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
            + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.OpenPkg.ProdOpen.sob_theta_mean
  refine ⟨C, hCpos, ?_⟩
  intro α g d hα hα1 hF hmem hd z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hwpos : 0 < Work.Spaces.w z := Work.FTS.OpenPkg.ProdOpen.w_pos_of_pos hz
  have hwne : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 hwpos.ne'
  -- the angular slice `h = D_z^d g (z, ·)` and its weighted derivative square
  set F : ℝ → ℝ := fun σ : ℝ =>
    (deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) with hFdef
  -- ### smoothness of the slice
  have hcurry := (hF.DzIter d).curry_θ hz
  have hder : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun σ' : ℝ => Work.Spaces.DzIter d g z σ')
        (deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') x) x :=
    fun x hx => ((hcurry.differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  have hcont : ContinuousOn (deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ'))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h : ContinuousOn (fun σ : ℝ => Work.Spaces.pth (Work.Spaces.DzIter d g) z σ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := ((hF.DzIter d).pth.curry_θ hz).continuousOn
    simpa only [Work.Spaces.pth] using h
  -- ### the a.e. identification of the derivative square with the mixed slot `(d,1)`
  have haeEq : ∀ᵐ σ ∂(volume.restrict Work.Spaces.Iθ),
      F σ = (Work.Spaces.mixed d 1 g z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
    filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ hσ
    have h := Work.FTS.OpenPkg.ProdOpen.deriv_mixed_weight α hF d 0 hz hσ
    simpa only [hFdef, Nat.zero_add, Work.Spaces.mixed_zero_right] using h
  -- ### the weight identity: `(w z)² · (mixed d 1 g)² sin^{-γ} = (mixed d 1 g · W)²`
  have hkey : ∀ σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Spaces.w z) ^ 2 * ((Work.Spaces.mixed d 1 g z σ) ^ 2
          * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)))
        = (Work.Spaces.mixed d 1 g z σ * Work.Spaces.Wt α z σ) ^ 2 := by
    intro σ hσ
    have hsin := Work.FTS.OpenPkg.ProdOpen.sin_two_pos hσ
    rw [mul_pow, Work.H2.T1Q.Wt_sq_eq α z σ hsin]
    ring
  have haeW : ∀ᵐ σ ∂(volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.w z) ^ 2 * F σ
        = (Work.Spaces.mixed d 1 g z σ * Work.Spaces.Wt α z σ) ^ 2 := by
    filter_upwards [haeEq, Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ he hσ
    rw [he, hkey σ hσ]
  -- ### integrability of the two slice functions
  have hint1 : IntegrableOn (fun σ : ℝ => (Work.Spaces.DzIter d g z σ) ^ 2)
      Work.Spaces.Iθ := by
    refine Integrable.mono' (hmem.1 z hz.le)
      (Work.H2.T1Q.aesm_Iθ_of_continuousOn (hcurry.continuousOn.pow 2)) ?_
    filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ hσ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [Work.Spaces.mixed_zero_right] using
      Work.FTS.StrongPersist.N6.mixed_sq_le_HkIntegrand6 α hα g d 0 (by omega)
        hz hσ.1 hσ.2
  have hint2 : IntegrableOn F Work.Spaces.Iθ := by
    refine Integrable.mono' ((hmem.1 z hz.le).const_mul ((Work.Spaces.w z) ^ 2)⁻¹) ?_ ?_
    · rw [hFdef]
      refine Work.H2.T1Q.aesm_Iθ_of_continuousOn ?_
      have hbase : Continuous fun σ : ℝ => Real.sin (2 * σ) := by fun_prop
      exact (((hF.DzIter d).pth.curry_θ hz).continuousOn.pow 2).mul
        (hbase.continuousOn.rpow_const
          (fun σ hσ => Or.inl (ne_of_gt (Work.FTS.OpenPkg.ProdOpen.sin_two_pos hσ))))
    · filter_upwards [haeEq, Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ he hσ
      have hsin := Work.FTS.OpenPkg.ProdOpen.sin_two_pos hσ
      have hnn : 0 ≤ F σ := by
        rw [he]
        exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _)
      rw [Real.norm_of_nonneg hnn, he]
      have hX : (Work.Spaces.mixed d 1 g z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          = ((Work.Spaces.w z) ^ 2)⁻¹ * ((Work.Spaces.w z) ^ 2
              * ((Work.Spaces.mixed d 1 g z σ) ^ 2
                * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)))) := by
        rw [← mul_assoc, inv_mul_cancel₀ hwne, one_mul]
      rw [hX]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (sq_nonneg (Work.Spaces.w z)))
      rw [hkey σ hσ]
      exact Work.Spaces.sq_le_HkIntegrand_mixed α 6 g z σ 1 d (by norm_num) (by omega)
  -- ### the exact value of the derivative term: `(w z)² ∫ F = Aang α g d z`
  have hAang : (Work.Spaces.w z) ^ 2 * (∫ σ in Work.Spaces.Iθ, F σ)
      = Work.FTS.H2.WPQ.Aang α g d z := by
    have hstep : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * F σ)
        = (Work.Spaces.w z) ^ 2 * (∫ σ in Work.Spaces.Iθ, F σ) :=
      MeasureTheory.integral_const_mul (μ := volume.restrict Work.Spaces.Iθ) _ _
    rw [← hstep, Work.FTS.H2.WPQ.Aang]
    exact MeasureTheory.integral_congr_ae haeW
  -- ### the angular inequality and the assembly
  have hmain := hC α (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') θ hα hα1 hθ
    hder hcont hint1 hint2
  have hmain' : (Work.Spaces.DzIter d g z θ) ^ 2
      ≤ C * ((∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
          + (Work.Spaces.gam α - 1)⁻¹ * (∫ σ in Work.Spaces.Iθ, F σ)) := by
    simpa only [hFdef] using hmain
  calc (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter d g z θ) ^ 2 := by ring
    _ ≤ (Work.Spaces.w z) ^ 2 * (C * ((∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
          + (Work.Spaces.gam α - 1)⁻¹ * (∫ σ in Work.Spaces.Iθ, F σ))) :=
        mul_le_mul_of_nonneg_left hmain' (sq_nonneg _)
    _ = C * ((Work.Spaces.w z) ^ 2 * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
          + (Work.Spaces.gam α - 1)⁻¹ * ((Work.Spaces.w z) ^ 2
              * (∫ σ in Work.Spaces.Iθ, F σ))) := by ring
    _ = C * ((Work.Spaces.w z) ^ 2 * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
          + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z) := by rw [hAang]

end Work.FTS.StrongPersist.H6Rows.wprod6
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Aux.bcoefPrep =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Aux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The radial half `2z²/(1+z)³` of the projector coefficient. -/
def bcoefRad (z : ℝ) : ℝ := 2 * z ^ 2 / (1 + z) ^ 3

/-- The angular half `Γ(θ)/c(α)`. -/
def gamCoefAng (α θ : ℝ) : ℝ := Work.Spaces.Gam α θ / Work.Spaces.c α

lemma bcoefRad_eq (z : ℝ) : bcoefRad z = 2 * z ^ 2 / (1 + z) ^ 3 := rfl
lemma gamCoefAng_eq (α θ : ℝ) : gamCoefAng α θ = Work.Spaces.Gam α θ / Work.Spaces.c α := rfl

/-! ## A. Smoothness on the open quadrant -/

lemma contDiffOn_gamCoefAng (α : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => gamCoefAng α θ) (Set.Ioo 0 (π / 2)) := by
  have h : (fun θ : ℝ => gamCoefAng α θ)
      = fun θ : ℝ => Work.Spaces.Gam α θ * (Work.Spaces.c α)⁻¹ := by
    funext θ; rw [gamCoefAng_eq]; ring
  rw [h]
  exact (Work.FTS.Nonlinear.Open.Row19Prep.contDiffOn_Gam α).mul contDiffOn_const

lemma contDiffOn_bcoefRad :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => bcoefRad z) (Set.Ioi 0) := by
  have h : (fun z : ℝ => bcoefRad z) = fun z : ℝ => 2 * z ^ 2 / (1 + z) ^ 3 := by
    funext z; rw [bcoefRad_eq]
  rw [h]
  refine ContDiffOn.div ?_ ?_ ?_
  · exact contDiffOn_const.mul (contDiffOn_id.pow 2)
  · exact (contDiffOn_const.add contDiffOn_id).pow 3
  · intro z hz
    have hz1 : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
    positivity

lemma smoothOpen_prod (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => gamCoefAng α θ * bcoefRad z) :=
  Work.FTS.Nonlinear.Open.Row19Prep.smoothOpen_mul
    (Work.FTS.Nonlinear.Open.Row19Prep.smoothOpen_theta_only (contDiffOn_gamCoefAng α))
    (Work.FTS.Nonlinear.Open.Row19Prep.smoothOpen_z_only contDiffOn_bcoefRad)

/-! ## B. Decomposition of the mixed operators on a product `g θ * φ z` -/

lemma DzIter_ang_rad (i : ℕ) (φ : ℝ → ℝ) (g : ℝ → ℝ) :
    Work.Spaces.DzIter i (fun z θ => g θ * φ z)
      = fun z θ => g θ * (Work.Spaces.Zop^[i] φ) z := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DzIter_succ, ih, Function.iterate_succ_apply']
      funext z θ
      show z * deriv (fun z' => g θ * (Work.Spaces.Zop^[i] φ) z') z
          = g θ * (Work.Spaces.Zop (Work.Spaces.Zop^[i] φ) z)
      simp only [Work.Spaces.Zop]
      rw [Work.Spaces.deriv_const_mul']
      ring

lemma dthU_iter_const_mul (i : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    Work.Spaces.dthU^[i] (fun θ => c * f θ) = fun θ => c * (Work.Spaces.dthU^[i] f) θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      funext θ
      simp only [Work.Spaces.dthU_apply]
      rw [Work.Spaces.deriv_const_mul']
      ring

lemma DthIter_ang_rad (i : ℕ) (φ : ℝ → ℝ) (g : ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => g θ * φ z)
      = fun z θ => (Work.Spaces.dthU^[i] g) θ * φ z := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih, Function.iterate_succ_apply']
      funext z θ
      show Real.sin (2 * θ) * deriv (fun θ' => (Work.Spaces.dthU^[i] g) θ' * φ z) θ
          = (Work.Spaces.dthU (Work.Spaces.dthU^[i] g) θ) * φ z
      simp only [Work.Spaces.dthU_apply]
      rw [Work.Spaces.deriv_mul_const']
      ring

lemma mixed_ang_rad (j i : ℕ) (φ : ℝ → ℝ) (g : ℝ → ℝ) :
    Work.Spaces.mixed j i (fun z θ => g θ * φ z)
      = fun z θ => (Work.Spaces.dthU^[i] g) θ * (Work.Spaces.Zop^[j] φ) z := by
  rw [Work.Spaces.mixed, DthIter_ang_rad]
  exact DzIter_ang_rad j φ (Work.Spaces.dthU^[i] g)

/-! ## C. The two weight-square identities -/

lemma sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

lemma div_sin_eta_sq (a : ℝ) {θ : ℝ} (hs : 0 ≤ Real.sin (2 * θ)) :
    (a / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = a ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have heta : (Work.Spaces.eta / 2) ≠ 0 := by rw [Work.Spaces.eta]; norm_num
  have heta' : -(Work.Spaces.eta) ≠ 0 := by rw [Work.Spaces.eta]; norm_num
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h, Real.zero_rpow heta, div_zero, Real.zero_rpow heta', zero_pow (by norm_num : (2:ℕ) ≠ 0)]
    ring
  · have h1 : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
        = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
      rw [← Real.rpow_mul_natCast h.le (Work.Spaces.eta / 2) 2]
      congr 1
      ring
    rw [div_eq_mul_inv, mul_pow, inv_pow, h1, Real.rpow_neg h.le (Work.Spaces.eta)]

lemma Wt_sq_of_nonneg {α z θ : ℝ} (hα : 0 < α) (hs : 0 ≤ Real.sin (2 * θ)) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hgam : Work.Spaces.gam α ≠ 0 := by
    rw [Work.Spaces.gam]; intro h; linarith
  have hgam2 : -(Work.Spaces.gam α / 2) ≠ 0 := by
    intro h
    apply hgam
    linarith
  have hgam' : -(Work.Spaces.gam α) ≠ 0 := neg_ne_zero.mpr hgam
  have hWt : Work.Spaces.Wt α z θ
      = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := rfl
  rw [hWt, mul_pow]
  congr 1
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h, Real.zero_rpow hgam2, Real.zero_rpow hgam', zero_pow (by norm_num : (2:ℕ) ≠ 0)]
  · have h1 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      rw [← Real.rpow_mul_natCast h.le (-(Work.Spaces.gam α / 2)) 2]
      congr 1
      ring
    rw [h1]

/-! ## D. Pointwise angular bounds -/

/-- `radTB` dominates all the `tBound (i-1) 0` for `i ≤ 4`. -/
def radTB : ℝ := ∑ j ∈ Finset.range 3, Work.Spaces.tBound j 0

lemma radTB_nonneg : 0 ≤ radTB :=
  Finset.sum_nonneg fun j _ => Work.Spaces.tBound_nonneg j 0

lemma tBound_le_radTB {i : ℕ} (hi1 : 1 ≤ i) (hi3 : i ≤ 3) :
    Work.Spaces.tBound (i - 1) 0 ≤ radTB :=
  Finset.single_le_sum (f := fun j : ℕ => Work.Spaces.tBound j 0)
    (fun j _ => Work.Spaces.tBound_nonneg j 0)
    (Finset.mem_range.mpr (by omega))

lemma c_pos {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) : 0 < Work.Spaces.c α := by
  have h := (Work.Spaces.c_bounds α hα hα1).1
  linarith

lemma gamCoefAng_nonneg {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ gamCoefAng α θ :=
  div_nonneg (Work.Spaces.Gam_bounds α θ hα hθ).1 (le_of_lt (c_pos hα hα1))

lemma gamCoefAng_le_ten {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Work.Spaces.Iθ) : gamCoefAng α θ ≤ 10 := by
  rw [gamCoefAng_eq, div_le_iff₀ (c_pos hα hα1)]
  have h1 : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
  have h2 : (1 : ℝ) ≤ 10 * Work.Spaces.c α := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  linarith


lemma gamCoefAng_sq_le {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Work.Spaces.Iθ) : (gamCoefAng α θ) ^ 2 ≤ 100 := by
  have h1 : gamCoefAng α θ ≤ 10 := gamCoefAng_le_ten hα hα1 hθ
  have h2 : 0 ≤ gamCoefAng α θ := gamCoefAng_nonneg hα hα1 hθ
  nlinarith

lemma gamCoefAng_sq_le_gam_sq {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (gamCoefAng α θ) ^ 2 ≤ 100 * (Work.Spaces.Gam α θ) ^ 2 := by
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hcpos : 0 < Work.Spaces.c α := c_pos hα hα1
  have hcle : 10 * (Work.Spaces.c α)⁻¹ ≤ 100 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    have h1 : (Work.Spaces.c α)⁻¹ ≤ 10 := by
      rw [inv_le_iff_one_le_mul₀ hcpos]
      linarith
    linarith
  have h1 : gamCoefAng α θ ≤ 10 * Work.Spaces.Gam α θ := by
    rw [gamCoefAng_eq, div_le_iff₀ hcpos]
    have : Work.Spaces.Gam α θ * 1 ≤ Work.Spaces.Gam α θ * (10 * Work.Spaces.c α) := by
      have h2 : (1 : ℝ) ≤ 10 * Work.Spaces.c α := by
        have h := (Work.Spaces.c_bounds α hα hα1).1; linarith
      exact mul_le_mul_of_nonneg_left h2 hG0
    linarith
  have h2 : 0 ≤ gamCoefAng α θ := gamCoefAng_nonneg hα hα1 hθ
  have h3 : 0 ≤ 10 * Work.Spaces.Gam α θ := by positivity
  nlinarith [sq_nonneg (gamCoefAng α θ), sq_nonneg (Work.Spaces.Gam α θ), mul_nonneg h2 h3]

/-- `dthU^i` of the angular coefficient is dominated by `α·radTB·(Γ/c)`. -/
lemma dthU_gamCoefAng_le {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Work.Spaces.Iθ) {i : ℕ} (hi1 : 1 ≤ i) (hi3 : i ≤ 3) :
    |Work.Spaces.dthU^[i] (fun θ => gamCoefAng α θ) θ| ≤ α * radTB * gamCoefAng α θ := by
  have hdec : (fun θ : ℝ => gamCoefAng α θ)
      = fun θ : ℝ => (Work.Spaces.c α)⁻¹ * Work.Spaces.Gam α θ := by
    funext t; rw [gamCoefAng_eq]; ring
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hcpos : 0 < Work.Spaces.c α := c_pos hα hα1
  have hbase := Work.Spaces.dthU_Gam_le i hi1 α hα hα1 θ hθ
  rw [hdec, dthU_iter_const_mul, abs_mul, abs_of_pos (inv_pos.mpr hcpos)]
  have h1 : (Work.Spaces.c α)⁻¹ * |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
      ≤ (Work.Spaces.c α)⁻¹ * (α * Work.Spaces.tBound (i - 1) 0 * Work.Spaces.Gam α θ) :=
    mul_le_mul_of_nonneg_left hbase (le_of_lt (inv_pos.mpr hcpos))
  calc (Work.Spaces.c α)⁻¹ * |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
      ≤ (Work.Spaces.c α)⁻¹ * (α * Work.Spaces.tBound (i - 1) 0 * Work.Spaces.Gam α θ) := h1
    _ = α * Work.Spaces.tBound (i - 1) 0 * (Work.Spaces.Gam α θ / Work.Spaces.c α) := by
          rw [div_eq_mul_inv]; ring
    _ ≤ α * radTB * (Work.Spaces.Gam α θ / Work.Spaces.c α) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (tBound_le_radTB hi1 hi3) (le_of_lt hα))
            (div_nonneg hG0 (le_of_lt hcpos))
    _ = α * radTB * gamCoefAng α θ := by rw [gamCoefAng_eq]

lemma dthU_gamCoefAng_sq_le {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Work.Spaces.Iθ) {i : ℕ} (hi1 : 1 ≤ i) (hi3 : i ≤ 3) :
    (Work.Spaces.dthU^[i] (fun θ => gamCoefAng α θ) θ) ^ 2
      ≤ 100 * radTB ^ 2 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2) := by
  have h1 : |Work.Spaces.dthU^[i] (fun θ => gamCoefAng α θ) θ| ≤ α * radTB * gamCoefAng α θ :=
    dthU_gamCoefAng_le hα hα1 hθ hi1 hi3
  have h2 : 0 ≤ α * radTB * gamCoefAng α θ :=
    mul_nonneg (mul_nonneg (le_of_lt hα) radTB_nonneg) (gamCoefAng_nonneg hα hα1 hθ)
  have h3 : (Work.Spaces.dthU^[i] (fun θ => gamCoefAng α θ) θ) ^ 2
      ≤ (α * radTB * gamCoefAng α θ) ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg h2]
    exact h1
  refine h3.trans ?_
  have h4 : (gamCoefAng α θ) ^ 2 ≤ 100 * (Work.Spaces.Gam α θ) ^ 2 := gamCoefAng_sq_le_gam_sq hα hα1 hθ
  have h5 : 0 ≤ (α * radTB) ^ 2 := sq_nonneg _
  calc (α * radTB * gamCoefAng α θ) ^ 2 = (α * radTB) ^ 2 * (gamCoefAng α θ) ^ 2 := by ring
    _ ≤ (α * radTB) ^ 2 * (100 * (Work.Spaces.Gam α θ) ^ 2) := mul_le_mul_of_nonneg_left h4 h5
    _ = 100 * radTB ^ 2 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2) := by ring


end Work.FTS.StrongPersist.L3Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6.m_sum_bound6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

open Work.Spaces
open Work.FTS.EllipticEst (SmoothOpen Q0 mem_Q0)
open Work.FTS.OpenPkg.ProdOpen (leibniz_open_mixed)

/-
Template (verbatim, level 4, sorry-free): `Work.FTS.OpenPkg.ProdOpen.{m_slot_bound, m_sum_bound}`
(`Submission/Work/FTS/OpenPkg/ProdOpen/m_sum_bound.lean`) — copy with `4 ↦ 6`, the low-order
threshold `2 ↦ 4`, the binomial constants `256 ↦ 4096` (`N6.binom_sq_le_4096`),
`65536 ↦ 16777216`, `(I+1)(J+1) ≤ 25 ↦ ≤ 49`, and a generous final constant.

`m_slot_bound6` (proved below) is: for `A,B` the angular/radial orders on `f` and `D,C` those on
`g` with `1 ≤ A + D` and `A+B+C+D ≤ 6`, the pair `(D_z^B D_θ^A f · D_z^C D_θ^D g · W)²` is
`≤ max CPw 1 * (SInv6 + Texc6)`, closing by
  (a) `1 ≤ D` and `A+B ≤ 4`: `PwAny6` on `f` + the `(C,D)`-slot of `g`;
  (b) `A ≥ 1` and `C+D ≤ 4`: `PwAny6` on `g` + the `(B,A)`-slot of `f`;
  (c) the two exceptional slots `(A,B,C,D) = (0,5,0,1)` and `(1,0,5,0)`, bounded by `Texc6`
      (again as in the level-4 file).

Helpers: `Work.FTS.StrongPersist.N6.{SInv6_nonneg, Texc6_nonneg, mul_inv_mul_le_SInv6_left,
mul_inv_mul_le_SInv6_right, binom_sq_le_4096, gam_sub_one_pos6}` (in `N6/ProdDefs6`);
`Work.FTS.StrongPersist.N6.PwAny6` (in `N6/PwOpen6`); the index-general Leibniz rule
`Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed`.
-/

/-- **The per-Leibniz-term bound.**  For orders `A,B` on `f` and `C,D` on `g` with
`A + D ≥ 1` and `A + B + C + D ≤ 6`,

  `(D_z^B D_θ^A f · D_z^C D_θ^D g · W)² ≤ max CPw 1 · (SInv6 + Texc6)`.

The hypothesis `1 ≤ A + D` is the slot condition `i ≥ 1` of `HkIntegrand`. -/
theorem m_slot_bound6 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f g : ℝ → ℝ → ℝ}
    (hF : SmoothOpen f) (hmemF : HkMem α 6 f) (hG : SmoothOpen g) (hmemG : HkMem α 6 g)
    {CPw : ℝ} (hCPw : 0 < CPw)
    (hPw : ∀ (u : ℝ → ℝ → ℝ), SmoothOpen u → HkMem α 6 u → ∀ b a : ℕ, a + b ≤ 4 →
      ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      (mixed b a u z θ) ^ 2 ≤ CPw / (gam α - 1) * HkSq α 6 u)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ∀ A B C D : ℕ, 1 ≤ A + D → A + B + C + D ≤ 6 →
      (mixed B A f z θ * mixed C D g z θ * Wt α z θ) ^ 2
        ≤ max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ) := by
  intro A B C D hAD htot
  have hγ : 0 < gam α - 1 := gam_sub_one_pos6 hα
  have hSl : 0 ≤ SInv6 α f g z θ := SInv6_nonneg hα f g z θ
  have hTl : 0 ≤ Texc6 α f g z θ := Texc6_nonneg α f g z θ
  have hCMpos : 0 < max CPw 1 := lt_of_lt_of_le hCPw (le_max_left _ _)
  have hPwCM : CPw ≤ max CPw 1 := le_max_left _ _
  have h1CM : (1 : ℝ) ≤ max CPw 1 := le_max_right _ _
  -- ### The three closing shapes
  have keyF : (mixed B A f z θ) ^ 2 ≤ CPw / (gam α - 1) * HkSq α 6 f →
      (mixed C D g z θ * Wt α z θ) ^ 2 ≤ HkIntegrand α 6 g z θ →
      (mixed B A f z θ * mixed C D g z θ * Wt α z θ) ^ 2
        ≤ max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ) := by
    intro hx hy
    have h1 : (mixed B A f z θ * mixed C D g z θ * Wt α z θ) ^ 2
        = (mixed B A f z θ) ^ 2 * (mixed C D g z θ * Wt α z θ) ^ 2 := by ring
    rw [h1]
    calc (mixed B A f z θ) ^ 2 * (mixed C D g z θ * Wt α z θ) ^ 2
        ≤ (CPw / (gam α - 1) * HkSq α 6 f) * HkIntegrand α 6 g z θ :=
          mul_le_mul hx hy (sq_nonneg _)
            (mul_nonneg (div_nonneg hCPw.le hγ.le) (HkSq_nonneg α 6 f))
      _ = CPw * ((gam α - 1)⁻¹ * (HkSq α 6 f * HkIntegrand α 6 g z θ)) := by
          rw [div_eq_mul_inv]; ring
      _ ≤ CPw * SInv6 α f g z θ :=
          mul_le_mul_of_nonneg_left (mul_inv_mul_le_SInv6_left hα f g z θ) hCPw.le
      _ ≤ max CPw 1 * SInv6 α f g z θ := mul_le_mul_of_nonneg_right hPwCM hSl
      _ ≤ max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hTl) hCMpos.le
  have keyG : (mixed C D g z θ) ^ 2 ≤ CPw / (gam α - 1) * HkSq α 6 g →
      (mixed B A f z θ * Wt α z θ) ^ 2 ≤ HkIntegrand α 6 f z θ →
      (mixed B A f z θ * mixed C D g z θ * Wt α z θ) ^ 2
        ≤ max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ) := by
    intro hy hx
    have h1 : (mixed B A f z θ * mixed C D g z θ * Wt α z θ) ^ 2
        = (mixed B A f z θ * Wt α z θ) ^ 2 * (mixed C D g z θ) ^ 2 := by ring
    rw [h1]
    calc (mixed B A f z θ * Wt α z θ) ^ 2 * (mixed C D g z θ) ^ 2
        ≤ HkIntegrand α 6 f z θ * (CPw / (gam α - 1) * HkSq α 6 g) :=
          mul_le_mul hx hy (sq_nonneg _) (HkIntegrand_nonneg α 6 f z θ)
      _ = CPw * ((gam α - 1)⁻¹ * (HkSq α 6 g * HkIntegrand α 6 f z θ)) := by
          rw [div_eq_mul_inv]; ring
      _ ≤ CPw * SInv6 α f g z θ :=
          mul_le_mul_of_nonneg_left (mul_inv_mul_le_SInv6_right hα f g z θ) hCPw.le
      _ ≤ max CPw 1 * SInv6 α f g z θ := mul_le_mul_of_nonneg_right hPwCM hSl
      _ ≤ max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hTl) hCMpos.le
  have keyE : (mixed B A f z θ * mixed C D g z θ * Wt α z θ) ^ 2 ≤ Texc6 α f g z θ →
      (mixed B A f z θ * mixed C D g z θ * Wt α z θ) ^ 2
        ≤ max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ) := by
    intro hxy
    calc (mixed B A f z θ * mixed C D g z θ * Wt α z θ) ^ 2 ≤ Texc6 α f g z θ := hxy
      _ = 1 * Texc6 α f g z θ := by ring
      _ ≤ max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ) :=
          mul_le_mul h1CM (le_add_of_nonneg_left hSl) hTl (by linarith)
  -- ### The case analysis
  by_cases hA1 : 1 ≤ A
  · by_cases hD1 : 1 ≤ D
    · -- both angular orders positive: `min (A+B) (C+D) ≤ 3 ≤ 4`
      by_cases hmin : A + B ≤ C + D
      · exact keyF (hPw f hF hmemF B A (by omega) z θ hz hθ)
          (sq_le_HkIntegrand_mixed α 6 g z θ D C hD1 (by omega))
      · exact keyG (hPw g hG hmemG C D (by omega) z θ hz hθ)
          (sq_le_HkIntegrand_mixed α 6 f z θ A B hA1 (by omega))
    · -- `D = 0`: the `g`-factor is a pure `D_z`-slot
      have hDe : D = 0 := by omega
      subst hDe
      by_cases hC4 : C ≤ 4
      · exact keyG (hPw g hG hmemG C 0 (by omega) z θ hz hθ)
          (sq_le_HkIntegrand_mixed α 6 f z θ A B hA1 (by omega))
      · -- exceptional: `A = 1, B = 0, C = 5, D = 0`
        have hAe : A = 1 := by omega
        have hBe : B = 0 := by omega
        have hCe : C = 5 := by omega
        refine keyE ?_
        rw [hAe, hBe, hCe]
        simp only [mixed_zero_left, mixed_zero_right, DthIter_succ, DthIter_zero]
        rw [show (Dth f z θ * DzIter 5 g z θ * Wt α z θ) ^ 2
            = (Dth f z θ * DzIter 5 g z θ) ^ 2 * (Wt α z θ) ^ 2 from by ring, Texc6]
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (sq_nonneg _)) (sq_nonneg _)
  · -- `A = 0`: the `f`-factor is a pure `D_z`-slot
    have hAe : A = 0 := by omega
    subst hAe
    have hD1 : 1 ≤ D := by omega
    by_cases hB4 : B ≤ 4
    · exact keyF (hPw f hF hmemF B 0 (by omega) z θ hz hθ)
        (sq_le_HkIntegrand_mixed α 6 g z θ D C hD1 (by omega))
    · -- exceptional: `A = 0, B = 5, C = 0, D = 1`
      have hBe : B = 5 := by omega
      have hCe : C = 0 := by omega
      have hDe : D = 1 := by omega
      refine keyE ?_
      rw [hBe, hCe, hDe]
      simp only [mixed_zero_left, mixed_zero_right, DthIter_succ, DthIter_zero]
      rw [show (DzIter 5 f z θ * Dth g z θ * Wt α z θ) ^ 2
          = (DzIter 5 f z θ * Dth g z θ) ^ 2 * (Wt α z θ) ^ 2 from by ring, Texc6]
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (sq_nonneg _)) (sq_nonneg _)

theorem m_sum_bound6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
    ∀ I J : ℕ, 1 ≤ I → I + J ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.mixed J I (fun z θ => f z θ * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ C * (Work.FTS.StrongPersist.N6.SInv6 α f g z θ
            + Work.FTS.StrongPersist.N6.Texc6 α f g z θ) := by
  obtain ⟨CPw, hCPwpos, hPwAny⟩ := PwAny6
  refine ⟨10 ^ 11 * max CPw 1, by positivity, ?_⟩
  intro α f g hα hα1 hF hmemF hG hmemG I J hI hIJ z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hPw : ∀ (u : ℝ → ℝ → ℝ), SmoothOpen u → HkMem α 6 u → ∀ b a : ℕ, a + b ≤ 4 →
      ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      (mixed b a u z θ) ^ 2 ≤ CPw / (gam α - 1) * HkSq α 6 u :=
    fun u hu hum b a hab z θ hz hθ' => hPwAny α u b a hα hα1 hu hum hab z hz θ hθ'
  have hMnn : 0 ≤ max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ) :=
    mul_nonneg (le_trans hCPwpos.le (le_max_left _ _))
      (add_nonneg (SInv6_nonneg hα f g z θ) (Texc6_nonneg α f g z θ))
  -- ### Leibniz expansion and the two Cauchy–Schwarz steps
  have hlei := leibniz_open_mixed J I f g hF hG z θ hz hθ0 hθ1
  set Y : ℕ → ℕ → ℝ := fun a b => (I.choose a : ℝ) * (J.choose b : ℝ)
    * (mixed b a f z θ * mixed (J - b) (I - a) g z θ * Wt α z θ) with hYdef
  have hYsplit : (mixed J I (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2
      = (∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b) ^ 2 := by
    have hkey : (mixed J I (fun z θ => f z θ * g z θ) z θ) * Wt α z θ
        = ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), Y a b := by
      rw [hlei, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b hb
      simp only [hYdef]; ring
    rw [hkey]
  have hper : ∀ a ∈ Finset.range (I + 1), ∀ b ∈ Finset.range (J + 1),
      (Y a b) ^ 2 ≤ 16777216 * (max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ)) := by
    intro a ha b hb
    have haI : a ≤ I := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    have hbJ : b ≤ J := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hcha : (I.choose a : ℝ) ^ 2 ≤ 4096 := binom_sq_le_4096 I a (by omega) (by omega)
    have hchb : (J.choose b : ℝ) ^ 2 ≤ 4096 := binom_sq_le_4096 J b (by omega) (by omega)
    have hch : (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2 ≤ 16777216 :=
      calc (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2 ≤ 4096 * 4096 :=
            mul_le_mul hcha hchb (by positivity) (by norm_num)
        _ = 16777216 := by norm_num
    have hslot := m_slot_bound6 hα hα1 hF hmemF hG hmemG hCPwpos hPw hz hθ a b (J - b) (I - a)
      (by omega) (by omega)
    have hY : (Y a b) ^ 2 = (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2
        * (mixed b a f z θ * mixed (J - b) (I - a) g z θ * Wt α z θ) ^ 2 := by
      rw [hYdef]; ring
    rw [hY]
    exact mul_le_mul hch hslot (sq_nonneg _) (by norm_num)
  have hcardI : (((Finset.range (I + 1)).card : ℕ) : ℝ) = (I : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hcardJ : (((Finset.range (J + 1)).card : ℕ) : ℝ) = (J : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hIJ49 : ((I : ℝ) + 1) * ((J : ℝ) + 1) ≤ 49 := by
    have hI6 : (I : ℝ) ≤ 6 := by exact_mod_cast (by omega : I ≤ 6)
    have hJ6 : (J : ℝ) ≤ 6 := by exact_mod_cast (by omega : J ≤ 6)
    nlinarith
  have hsum2 : ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2
      ≤ ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
          (16777216 * (max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ))) :=
    Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hper a ha b hb
  have hsumconst : ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
        (16777216 * (max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ)))
      = ((I : ℝ) + 1) * ((J : ℝ) + 1)
        * (16777216 * (max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ))) := by
    rw [Finset.sum_const, Finset.sum_const, Finset.card_range, Finset.card_range,
      nsmul_eq_mul, nsmul_eq_mul]
    push_cast; ring
  rw [hYsplit]
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
              (16777216 * (max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ))) :=
        mul_le_mul_of_nonneg_left hsum2 (by positivity)
    _ = (((I : ℝ) + 1) * ((J : ℝ) + 1)) ^ 2
          * (16777216 * (max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ))) := by
        rw [hsumconst]; ring_nf
    _ ≤ 2401 * (16777216 * (max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ))) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have h0 : (0 : ℝ) ≤ ((I : ℝ) + 1) * ((J : ℝ) + 1) := by positivity
        nlinarith [hIJ49, h0]
    _ = 40282095616 * (max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ)) := by ring
    _ ≤ 10 ^ 11 * (max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ)) :=
        mul_le_mul_of_nonneg_right (by norm_num) hMnn
    _ = 10 ^ 11 * max CPw 1 * (SInv6 α f g z θ + Texc6 α f g z θ) := by ring

end Work.FTS.StrongPersist.N6
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6.z_sum_bound6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.Spaces

/-
The level-six shift of `Work.FTS.OpenPkg.ProdOpen.z_sum_bound`: the proof is that proof with
`4 ↦ 6` and `3 ↦ 5`, i.e. the binomial constant `256 ↦ 4096` (`binom_sq_le_4096`), `(i+1) ≤ 5 ↦ ≤ 7`
and `6400 ↦ 200704`, using `PwAny6` in place of `PwAny` and `SInv6`/`Texc6` in place of
`SInv`/`Texc`.
-/
theorem z_sum_bound6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
    ∀ i : ℕ, i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ C * (Work.FTS.StrongPersist.N6.SInv6 α f g z θ
            + Work.FTS.StrongPersist.N6.Texc6 α f g z θ) := by
  obtain ⟨CPw, hCPwpos, hPw⟩ := PwAny6
  refine ⟨200704 * CPw, by positivity, ?_⟩
  intro α f g hα hα1 hF hFmem hG hGmem i hi z θ hz hθ0 hθ1
  change (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ * Hv6 z θ) ^ 2
      ≤ 200704 * CPw * (SInv6 α f g z θ + Texc6 α f g z θ)
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hSl : 0 ≤ SInv6 α f g z θ := SInv6_nonneg hα f g z θ
  have hTl : 0 ≤ Texc6 α f g z θ := Texc6_nonneg α f g z θ
  have hγ : 0 < gam α - 1 := gam_sub_one_pos6 hα
  have hKnn : ∀ (u : ℝ → ℝ → ℝ), 0 ≤ CPw / (gam α - 1) * HkSq α 6 u := fun u =>
    mul_nonneg (div_nonneg hCPwpos.le hγ.le) (HkSq_nonneg α 6 u)
  -- ### Step 1: Leibniz plus Cauchy–Schwarz
  have hcs : (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ * Hv6 z θ) ^ 2
      ≤ ((i + 1 : ℕ) : ℝ)
        * ∑ b ∈ Finset.range (i + 1),
            ((i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ * Hv6 z θ)) ^ 2 := by
    have hsum : Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ * Hv6 z θ
        = ∑ b ∈ Finset.range (i + 1),
            ((i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ * Hv6 z θ)) := by
      rw [Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz i f g hF hG z θ hz hθ0 hθ1,
        Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [hsum]
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
      (f := fun b => (i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ * Hv6 z θ))
    simpa using h
  -- ### Step 2: each Leibniz summand is dominated by `CPw * SInv6`
  have hterm : ∀ b ∈ Finset.range (i + 1),
      ((i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ * Hv6 z θ)) ^ 2
        ≤ 4096 * (CPw * SInv6 α f g z θ) := by
    intro b hb
    have hbi : b ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have hcb : (i.choose b : ℝ) ^ 2 ≤ 4096 := binom_sq_le_4096 i b hbi hi
    have hcore : (DzIter b f z θ * DzIter (i - b) g z θ * Hv6 z θ) ^ 2
        ≤ CPw * SInv6 α f g z θ := by
      by_cases hcase : b ≤ i - b
      · -- the `f`-factor is the one of low order `b ≤ 3`
        have hb3 : b ≤ 3 := by omega
        have hx : (DzIter b f z θ) ^ 2 ≤ CPw / (gam α - 1) * HkSq α 6 f := by
          have h := hPw α f b 0 hα hα1 hF hFmem (by omega) z hz θ hθ
          simpa only [Work.Spaces.mixed_zero_right] using h
        have hy : (DzIter (i - b) g z θ * Hv6 z θ) ^ 2 ≤ HkIntegrand α 6 g z θ := by
          have h := sq_le_HkIntegrand_z α 6 g z θ (i - b) (by omega)
          simpa only [Hv6] using h
        have h1 : (DzIter b f z θ * DzIter (i - b) g z θ * Hv6 z θ) ^ 2
            = (DzIter b f z θ) ^ 2 * (DzIter (i - b) g z θ * Hv6 z θ) ^ 2 := by ring
        rw [h1]
        refine le_trans (le_trans (mul_le_mul_of_nonneg_right hx (sq_nonneg _))
          (mul_le_mul_of_nonneg_left hy (hKnn f))) ?_
        rw [show CPw / (gam α - 1) * HkSq α 6 f * HkIntegrand α 6 g z θ
            = CPw * ((gam α - 1)⁻¹ * (HkSq α 6 f * HkIntegrand α 6 g z θ)) by
          rw [div_eq_mul_inv]; ring]
        exact mul_le_mul_of_nonneg_left (mul_inv_mul_le_SInv6_left hα f g z θ) hCPwpos.le
      · -- the `g`-factor is the one of low order `i - b ≤ 3`
        have hib3 : i - b ≤ 3 := by omega
        have hy : (DzIter (i - b) g z θ) ^ 2 ≤ CPw / (gam α - 1) * HkSq α 6 g := by
          have h := hPw α g (i - b) 0 hα hα1 hG hGmem (by omega) z hz θ hθ
          simpa only [Work.Spaces.mixed_zero_right] using h
        have hx : (DzIter b f z θ * Hv6 z θ) ^ 2 ≤ HkIntegrand α 6 f z θ := by
          have h := sq_le_HkIntegrand_z α 6 f z θ b (by omega)
          simpa only [Hv6] using h
        have h1 : (DzIter b f z θ * DzIter (i - b) g z θ * Hv6 z θ) ^ 2
            = (DzIter (i - b) g z θ) ^ 2 * (DzIter b f z θ * Hv6 z θ) ^ 2 := by ring
        rw [h1]
        refine le_trans (le_trans (mul_le_mul_of_nonneg_right hy (sq_nonneg _))
          (mul_le_mul_of_nonneg_left hx (hKnn g))) ?_
        rw [show CPw / (gam α - 1) * HkSq α 6 g * HkIntegrand α 6 f z θ
            = CPw * ((gam α - 1)⁻¹ * (HkSq α 6 g * HkIntegrand α 6 f z θ)) by
          rw [div_eq_mul_inv]; ring]
        exact mul_le_mul_of_nonneg_left (mul_inv_mul_le_SInv6_right hα f g z θ) hCPwpos.le
    have h1 : ((i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ * Hv6 z θ)) ^ 2
        = (i.choose b : ℝ) ^ 2 * (DzIter b f z θ * DzIter (i - b) g z θ * Hv6 z θ) ^ 2 := by
      ring
    rw [h1]
    exact le_trans (mul_le_mul_of_nonneg_right hcb (sq_nonneg _))
      (mul_le_mul_of_nonneg_left hcore (by norm_num))
  -- ### Step 3: sum the terms
  have hsum_bd : ∑ b ∈ Finset.range (i + 1),
      ((i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ * Hv6 z θ)) ^ 2
        ≤ ((i + 1 : ℕ) : ℝ) * (4096 * (CPw * SInv6 α f g z θ)) := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ hterm) ?_
    simp [nsmul_eq_mul]
  have hm : ((i + 1 : ℕ) : ℝ) ≤ 7 := by
    have : (i : ℝ) ≤ 6 := by exact_mod_cast hi
    push_cast
    linarith
  have hKnn' : 0 ≤ 4096 * (CPw * SInv6 α f g z θ) :=
    mul_nonneg (by norm_num) (mul_nonneg hCPwpos.le hSl)
  have hstep : ((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) * (4096 * (CPw * SInv6 α f g z θ)))
      ≤ 200704 * (CPw * SInv6 α f g z θ) := by
    have hmnn : (0 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by positivity
    have h1 : ((i + 1 : ℕ) : ℝ) * (4096 * (CPw * SInv6 α f g z θ))
        ≤ 7 * (4096 * (CPw * SInv6 α f g z θ)) := mul_le_mul_of_nonneg_right hm hKnn'
    have h2 : ((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) * (4096 * (CPw * SInv6 α f g z θ)))
        ≤ 7 * (7 * (4096 * (CPw * SInv6 α f g z θ))) :=
      mul_le_mul hm h1 (mul_nonneg hmnn hKnn') (by norm_num)
    have h3 : 7 * (7 * (4096 * (CPw * SInv6 α f g z θ)))
        = 200704 * (CPw * SInv6 α f g z θ) := by
      ring
    linarith [h2, h3]
  calc (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ * Hv6 z θ) ^ 2
      ≤ ((i + 1 : ℕ) : ℝ)
          * ∑ b ∈ Finset.range (i + 1),
              ((i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ * Hv6 z θ)) ^ 2 := hcs
    _ ≤ ((i + 1 : ℕ) : ℝ)
          * (((i + 1 : ℕ) : ℝ) * (4096 * (CPw * SInv6 α f g z θ))) :=
        mul_le_mul_of_nonneg_left hsum_bd (by positivity)
    _ ≤ 200704 * (CPw * SInv6 α f g z θ) := hstep
    _ ≤ 200704 * (CPw * (SInv6 α f g z θ + Texc6 α f g z θ)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hTl) hCPwpos.le) (by norm_num)
    _ = 200704 * CPw * (SInv6 α f g z θ + Texc6 α f g z θ) := by ring

end Work.FTS.StrongPersist.N6
end
end
-- ===== merged: Submission.Work.FTS.TransportS.T2SliceAux.sliceBoundF =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T2SliceAux

set_option autoImplicit false
set_option maxHeartbeats 1600000



end Work.FTS.TransportS.T2SliceAux
end
end
-- ===== merged: Submission.Work.FTS.TransportS.t2Aesm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.TransportS

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Continuity on the open quadrant for `SmoothOpen` data

The transport chapter works in the *open* quadrant class `SmoothOpen` (smoothness on
`z > 0`, `0 < θ < π/2`) rather than in `SmoothQuad`.  The two continuity lemmas below
transfer the `TransportS.HardDefs` cluster to that class; they are the analogues of
`Work.FTS.H2.continuousOn_mixed_Qd` and of the (private)
`Work.FTS.H2.continuousOn_H4PairInt_smoothQuad`. -/





/-! ## The main statement -/


end Work.FTS.TransportS
end
-- ===== merged: Submission.Work.FTS.TransportS.t2Hard =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# `T2Hard`: the five order-five terms of the `D_z`-transport pairing

The statement `Work.FTS.TransportS.T2Hard` bounds the "hard" part of the `D_z`-transport
pairing, `Hhard α f g` (`Submission/Work/FTS/H2/T2Defs.lean`), in the frozen (open-quadrant)
hypothesis class:

* on the `f`-side only `SmoothOpen f`, `HkMem α 4 f`, `CoefThMem 1 f` and the pointwise
  bounds `|f| ≤ Mf`, `|D_z f| ≤ Mf` on the open quadrant are used;
* on the `g`-side `SmoothQuad g`, `HkMem α 4 g`, `HkMem α 5 g`, `DecayAll 4 g` and the
  boundary traces `BdryTraces α 4 g` (from `RegQ α 4 g`) are used.

## Route

`Hhard α f g z θ = ∑_{k : Fin 5} f z θ · z · pz (Thard g k) z θ · Thard g k z θ · w² · sghard α k θ`,
and `z · pz (Thard g k) = Dz (Thard g k) = mixed (5 - k) k g`.  Hence each summand is
`f · X_k · Y_k` with

`X_k = Thard g k · w sin(2θ)^{-η_k/2}`, `Y_k = D_z(Thard g k) · w sin(2θ)^{-η_k/2}`

(`η_0 = η`, `η_k = γ` for `k ≥ 1`, see `Submission/Work/FTS/TransportS/HardDefs.lean`), so
`X_k²` is a slot of `HkIntegrand α 4 g` and `Y_k²` is a slot of `HkIntegrand α 5 g`.  The
elementary AM–GM bound `|Hhard| ≤ 5 Mf · HkIntegrand α 5 g` then makes `Hhard`
product-integrable with respect to `(volume.restrict Iz).prod (volume.restrict Iθ)`, which is
what allows the use of Fubini.

The *sharp* estimate is the radial integration by parts, performed θ-slice by θ-slice
(`Work.FTS.TransportS.slice_identity`): for a.e. `θ ∈ Iθ`,

`∫_z Hhard α f g z θ dz = -∫_z ZE α f g z θ dz`

with `ZE` the correction term of the primitive `ZG = ½ f z w² ZU`
(`Work.FTS.H2.HhardZibp`: `Hhard = ∂_z ZG - ZE`).  Fubini in the product measure turns this
into `∫_z∫_θ Hhard = -∫_z∫_θ ZE`, and the crude bound
`|ZE z θ| ≤ 2 Mf w(z)² ZU α g z θ = 2 Mf ∑_k X_k(z,θ)²` gives
`|∫_z∫_θ Hhard| ≤ 2 Mf ∑_k ∫∫ X_k² ≤ 10 Mf HkSq α 4 g`.
-/



end Work.FTS.TransportS
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXB.DzSlice_l2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXB

set_option autoImplicit false

/-! ## The joint continuity of the slot integrand on the open quadrant -/

/-- The integrand `(t,θ) ↦ (D_z f(t,θ) · w(t))²` is continuous on the open quadrant `(0,∞) ×
(0,π/2)`: `D_z f` is smooth there (`SmoothOpen.DzIter`) and the radial weight `w` is continuous
because the denominator `t²` does not vanish for `t > 0`. -/
theorem continuousOn_dzSlot {f : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f) :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter 1 f p.1 p.2 * Work.Spaces.w p.1) ^ 2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2)) := by
  have hD : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter 1 f p.1 p.2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2)) :=
    (hF.DzIter 1).continuousOn
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2)) := by
    simp only [Work.Spaces.w]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) ?_
    intro p hp
    exact pow_ne_zero 2 (ne_of_gt hp.1)
  exact (hD.mul hw).pow 2

/-- The slot integrand is almost everywhere strongly measurable for the product of the
restrictions of Lebesgue measure to `(0,∞)` and to `Iθ`; the two restrictions on the first
factor (open half-line and `Iz = [0,∞)`) agree because they differ by the null set `{0}`. -/
theorem aesm_dzSlot_prod {f : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => (Work.Spaces.DzIter 1 f p.1 p.2 * Work.Spaces.w p.1) ^ 2)
      ((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have h := Work.Spaces.aesm_of_continuousOn_Qd _
    (show ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter 1 f p.1 p.2 * Work.Spaces.w p.1) ^ 2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2)) from continuousOn_dzSlot hF)
  have hz : MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))
      = MeasureTheory.volume.restrict Work.Spaces.Iz :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))
  rw [← hz] at h
  exact h

/-! ## The pointwise domination by the `i = 1` summand of `HkIntegrand` -/

/-- For `θ ∈ (0,π/2)` the unweighted (in `θ`) radial slot `(D_z f(t,θ) · w(t))²` is dominated
by the full `ℋ⁴`-integrand at `(t,θ)`: the `i = 1` summand of `HkIntegrand` is
`(D_z f·w)² sin(2θ)^{-η}` and `sin(2θ)^{η} ≤ 1`. -/
theorem dzSlot_le_HkIntegrand {α : ℝ} {f : ℝ → ℝ → ℝ} {t θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    (Work.Spaces.DzIter 1 f t θ * Work.Spaces.w t) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f t θ := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hs : 0 ≤ Real.sin (2 * θ) := hsin.le
  have hone : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    Work.Spaces.Slots.one_le_sin_two_rpow_neg_eta hθ0 hθ1
  have hkey := Work.Spaces.sq_le_HkIntegrand_z α 4 f t θ 1 (by norm_num)
  have hsq : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
    norm_num
  have heq : (Work.Spaces.DzIter 1 f t θ
        * (Work.Spaces.w t / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.DzIter 1 f t θ) ^ 2 * (Work.Spaces.w t) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [mul_pow, div_pow, hsq, div_eq_mul_inv, ← Real.rpow_neg hs (Work.Spaces.eta)]
    ring
  calc (Work.Spaces.DzIter 1 f t θ * Work.Spaces.w t) ^ 2
      = (Work.Spaces.DzIter 1 f t θ) ^ 2 * (Work.Spaces.w t) ^ 2 := by ring
    _ ≤ (Work.Spaces.DzIter 1 f t θ) ^ 2 * (Work.Spaces.w t) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        le_mul_of_one_le_right (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hone
    _ = (Work.Spaces.DzIter 1 f t θ
          * (Work.Spaces.w t / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := heq.symm
    _ ≤ Work.Spaces.HkIntegrand α 4 f t θ := hkey

/-! ## The main statement -/

theorem DzSlice_l2 {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) :
    (∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        MeasureTheory.IntegrableOn
          (fun t => (Work.Spaces.DzIter 1 f t θ * Work.Spaces.w t) ^ 2) (Set.Ioi 0)) ∧
      MeasureTheory.AEStronglyMeasurable
        (fun θ => Real.sqrt (∫ t in Set.Ioi 0,
          (Work.Spaces.DzIter 1 f t θ * Work.Spaces.w t) ^ 2))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn
        (fun θ => (Real.sqrt (∫ t in Set.Ioi 0,
          (Work.Spaces.DzIter 1 f t θ * Work.Spaces.w t) ^ 2)) ^ 2)
        Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Real.sqrt (∫ t in Set.Ioi 0,
          (Work.Spaces.DzIter 1 f t θ * Work.Spaces.w t) ^ 2)) ^ 2)
        ≤ Work.Spaces.HkSq α 4 f := by
  -- The exchange of the two iterated integrals for the smooth open datum.
  obtain ⟨hswap, hIntHkθ, hAeIntHk⟩ := Work.FTS_RegExport.C4.HkSqSwap_C4 (hF.forall 4) hmem
  -- Joint a.e. strong measurability of the (uncurried) slot integrand.
  have hGprod := aesm_dzSlot_prod hF
  -- ... hence of the `t`-slices, a.e. in `θ`.
  have hAESMslice := hGprod.prodMk_right
  -- ... and of `θ ↦ ∫_t (D_z f · w)²`.
  have hAESMint : AEStronglyMeasurable
      (fun θ => ∫ t in Set.Ioi (0:ℝ), (Work.Spaces.DzIter 1 f t θ * Work.Spaces.w t) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h2 : AEStronglyMeasurable
        (fun p : ℝ × ℝ => (Work.Spaces.DzIter 1 f p.2 p.1 * Work.Spaces.w p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
          (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)))) := hGprod.prod_swap
    have h3 := h2.integral_prod_right'
    simpa only using h3
  -- The square root of that is a.e. strongly measurable.
  have hb := Real.continuous_sqrt.comp_aestronglyMeasurable hAESMint
  -- For a.e. `θ` we are in the open interval.
  have hae_θ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo 0 (Real.pi / 2) :=
    Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo (fun θ h0 h1 => ⟨h0, h1⟩)
  -- The two restrictions of Lebesgue measure to `Iz` and to the open half-line coincide.
  have hIz_eq : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0:ℝ)) :=
    (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))).symm
  -- The key a.e. bound: the squared `θ`-slice `L²` of the slot is dominated by the sliced
  -- `ℋ⁴`-integrand.
  have hbound : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Real.sqrt (∫ t in Set.Ioi (0:ℝ), (Work.Spaces.DzIter 1 f t θ * Work.Spaces.w t) ^ 2)) ^ 2
        ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s θ := by
    filter_upwards [hae_θ, hAeIntHk] with θ hθ hInt
    rw [Real.sq_sqrt (integral_nonneg fun t => sq_nonneg _)]
    calc ∫ t in Set.Ioi (0:ℝ), (Work.Spaces.DzIter 1 f t θ * Work.Spaces.w t) ^ 2
        = ∫ t in Work.Spaces.Iz, (Work.Spaces.DzIter 1 f t θ * Work.Spaces.w t) ^ 2 := by
          rw [hIz_eq]
      _ ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s θ :=
          integral_mono_of_nonneg (Eventually.of_forall fun t => sq_nonneg _) hInt
            (Eventually.of_forall fun t => dzSlot_le_HkIntegrand (f := f) hθ.1 hθ.2)
  refine ⟨?_, hb, ?_, ?_⟩
  · -- a.e. integrability of the `t`-slice, by domination from the sliced `HkIntegrand`
    filter_upwards [hae_θ, hAESMslice, hAeIntHk] with θ hθ hAESM hInt
    refine Integrable.mono' (hInt.mono_set ?_) hAESM ?_
    · exact Set.Ioi_subset_Ici_self
    · filter_upwards with t
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact dzSlot_le_HkIntegrand hθ.1 hθ.2
  · -- integrability of the square of the slice norm
    refine Integrable.mono' hIntHkθ (hb.pow 2) ?_
    filter_upwards [hbound] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hθ
  · -- the `L²`-bound, by monotonicity of the integral and the exchange of the two
    -- iterated integrals
    calc ∫ θ in Work.Spaces.Iθ, (Real.sqrt (∫ t in Set.Ioi (0:ℝ),
            (Work.Spaces.DzIter 1 f t θ * Work.Spaces.w t) ^ 2)) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
            Work.Spaces.HkIntegrand α 4 f s θ :=
          integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _) hIntHkθ hbound
      _ = Work.Spaces.HkSq α 4 f := hswap

end Work.FTS_RegExport.RXB
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR5L.Auxiliary.Tlim_sub_aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXR5L.Auxiliary

set_option autoImplicit false

local notation "Rwt" => Work.FTS_RegExport.RXT.L12Iter.Rwt

/-- The integral of a constant over `Iθ = [0,π/2]` is the constant times `π/2`. -/
private theorem integral_Iθ_const (c : ℝ) :
    (∫ _θ in Work.Spaces.Iθ, c) = c * (Real.pi / 2) := by
  rw [Work.Elliptic.integral_Iθ_eq_interval, intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring

/-- The angular weight `K(θ) = 3 sin θ cos²θ` is continuous on the open quadrant. -/
private theorem continuousOn_K_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2) Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.K p.2)
      = fun p : ℝ × ℝ => 3 * Real.sin p.2 * Real.cos p.2 ^ 2 := by
    funext p
    rw [Work.Spaces.K]
  rw [hfun]
  exact ((continuous_const.mul (Real.continuous_sin.comp continuous_snd)).mul
    ((Real.continuous_cos.comp continuous_snd).pow 2)).continuousOn

/-- The joint integrand `(s,θ) ↦ K(θ)·a(s,θ)/s` is continuous on the open quadrant. -/
private theorem continuousOn_integrand {a : ℝ → ℝ → ℝ}
    (hca : ContinuousOn (Function.uncurry a) Work.FTS.EllipticEst.Q0) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Function.uncurry a p / p.1)
      Work.FTS.EllipticEst.Q0 := by
  refine (continuousOn_K_Q0.mul hca).div continuous_fst.continuousOn ?_
  intro p hp
  exact ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1

/-- The pointwise domination of the angular integrand, including the two angular endpoints
(where `K` vanishes). -/
private theorem integrand_bound {a : ℝ → ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hba : ∀ s θ : ℝ, 0 < s → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |a s θ| ≤ A * (Rwt s / (1 + s)))
    {s : ℝ} (hs : 0 < s) :
    ∀ θ ∈ Work.Spaces.Iθ,
      ‖Work.Spaces.K θ * a s θ / s‖ ≤ 3 * (A * (Rwt s / (1 + s))) / s := by
  intro θ hθ
  have hC : 0 ≤ 3 * (A * (Rwt s / (1 + s))) / s := by
    have h1 : 0 ≤ A * (Rwt s / (1 + s)) :=
      mul_nonneg hA (div_nonneg (Work.FTS_RegExport.RXT.L12Iter.Rwt_nonneg hs.le) (by linarith))
    positivity
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · subst h0
    rw [Work.Spaces.K]
    simp
    exact hC
  · rcases eq_or_lt_of_le hθ.2 with h1 | h1
    · subst h1
      have hK0 : Work.Spaces.K (Real.pi / 2) = 0 := by
        rw [Work.Spaces.K, Real.cos_pi_div_two]
        norm_num
      rw [hK0, zero_mul, zero_div, norm_zero]
      exact hC
    · have h1' := hba s θ hs ⟨h0, h1⟩
      have hK : |Work.Spaces.K θ| ≤ 3 := by
        rw [← Work.Elliptic.Ktheta_eq_K]
        exact Work.FTS_RegExport.RXT.L12Iter.abs_Ktheta_le_three θ
      have hnum : |Work.Spaces.K θ| * |a s θ| ≤ 3 * (A * (Rwt s / (1 + s))) :=
        mul_le_mul hK h1' (abs_nonneg _) (by norm_num)
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hs]
      exact div_le_div_of_nonneg_right hnum hs.le

/-- **The angular slice of the datum is integrable.**  For `a` continuous on the open quadrant and
dominated by `A·Rwt·(1+·)⁻¹`, the slice `θ ↦ K(θ)·a(s,θ)/s` is integrable on `Iθ` for every
`s > 0`. -/
private theorem integrableOn_slice_of_bdd {a : ℝ → ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hca : ContinuousOn (Function.uncurry a) Work.FTS.EllipticEst.Q0)
    (hba : ∀ s θ : ℝ, 0 < s → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |a s θ| ≤ A * (Rwt s / (1 + s))) :
    ∀ s ∈ Set.Ioi (0 : ℝ),
      IntegrableOn (fun θ => Work.Spaces.K θ * a s θ / s) Work.Spaces.Iθ := by
  intro s hs
  have hs0 : 0 < s := hs
  have haesm : AEStronglyMeasurable (fun θ => Work.Spaces.K θ * a s θ / s)
      (volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Function.uncurry a p / p.1)
      (continuousOn_integrand hca) hs0
  refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const
    (3 * (A * (Rwt s / (1 + s))) / s)) haesm ?_
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  exact Eventually.of_forall (integrand_bound hA hba hs0)

/-- **The `L₁₂`-density of the datum is integrable on `(0,∞)`.** -/
private theorem integrableOn_dens_of_bdd {a : ℝ → ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hca : ContinuousOn (Function.uncurry a) Work.FTS.EllipticEst.Q0)
    (hba : ∀ s θ : ℝ, 0 < s → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |a s θ| ≤ A * (Rwt s / (1 + s))) :
    IntegrableOn (Work.Construction.L12dens a) (Set.Ioi (0 : ℝ)) := by
  -- a.e. strong measurability of the density on `(0,∞)`
  have haesmIz : AEStronglyMeasurable
      (fun z => ∫ θ, Work.Spaces.K θ * Function.uncurry a (z, θ) / z
        ∂(volume.restrict Work.Spaces.Iθ)) (volume.restrict Work.Spaces.Iz) :=
    (Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Function.uncurry a p / p.1)
      (continuousOn_integrand hca)).integral_prod_right'
  have haesm : AEStronglyMeasurable (Work.Construction.L12dens a)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    MeasureTheory.AEStronglyMeasurable.mono_set (fun z hz => (Set.mem_Ioi.mp hz).le) haesmIz
  -- the integrable majorant `3·(π/2)·A·Rwt s/s`
  obtain ⟨hint, -⟩ :=
    Work.FTS_RegExport.RXT.Sys.MajorantPieces.sqrt_div_sq_Ioi_integral_le (z := 0) le_rfl
  have hmaj : Integrable (fun s : ℝ => 3 * (Real.pi / 2) * A * (Rwt s / s))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine (hint.const_mul (3 * (Real.pi / 2) * A)).congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_
    show 3 * (Real.pi / 2) * A * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)
      = 3 * (Real.pi / 2) * A * (Rwt s / s)
    rw [Work.FTS_RegExport.RXT.L12Iter.Rwt_div s hs]
  refine MeasureTheory.Integrable.mono' hmaj haesm ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_
  have hs0 : 0 < s := hs
  have hR : 0 ≤ Rwt s := Work.FTS_RegExport.RXT.L12Iter.Rwt_nonneg hs0.le
  have hRs : 0 ≤ Rwt s / s := div_nonneg hR hs0.le
  have hs1 : (0 : ℝ) < 1 + s := by linarith
  -- the inner mean inequality
  have hmain := MeasureTheory.norm_integral_le_of_norm_le
    (μ := volume.restrict Work.Spaces.Iθ)
    (f := fun θ => Work.Spaces.K θ * a s θ / s)
    (g := fun _ : ℝ => 3 * (A * (Rwt s / (1 + s))) / s)
    (MeasureTheory.integrable_const (3 * (A * (Rwt s / (1 + s))) / s))
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => integrand_bound hA hba hs0 θ hθ))
  have hval : (∫ _θ in Work.Spaces.Iθ, 3 * (A * (Rwt s / (1 + s))) / s)
      = 3 * (A * (Rwt s / (1 + s))) / s * (Real.pi / 2) := integral_Iθ_const _
  have hdens : ‖Work.Construction.L12dens a s‖
      ≤ 3 * (A * (Rwt s / (1 + s))) / s * (Real.pi / 2) := by
    rw [Work.Construction.L12dens, Work.FM.L12dens]
    exact le_trans hmain (le_of_eq hval)
  calc ‖Work.Construction.L12dens a s‖
      ≤ 3 * (A * (Rwt s / (1 + s))) / s * (Real.pi / 2) := hdens
    _ = 3 * (Real.pi / 2) * A * (Rwt s / s) / (1 + s) := by ring
    _ ≤ 3 * (Real.pi / 2) * A * (Rwt s / s) := by
        rw [div_le_iff₀ hs1]
        have hnn : 0 ≤ 3 * (Real.pi / 2) * A * (Rwt s / s) :=
          mul_nonneg (mul_nonneg (by positivity) hA) hRs
        nlinarith [hnn, hs0]

/-- **Linearity of `L₁₂` in its profile, for continuous boundedly-dominated data.** -/
theorem L12_sub_of_bdd_proved {a b : ℝ → ℝ → ℝ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hca : ContinuousOn (Function.uncurry a) Work.FTS.EllipticEst.Q0)
    (hcb : ContinuousOn (Function.uncurry b) Work.FTS.EllipticEst.Q0)
    (hba : ∀ s θ : ℝ, 0 < s → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |a s θ| ≤ A * (Rwt s / (1 + s)))
    (hbb : ∀ s θ : ℝ, 0 < s → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |b s θ| ≤ B * (Rwt s / (1 + s))) :
    Work.Construction.L12 a 0 - Work.Construction.L12 b 0
      = Work.Construction.L12 (fun z θ => a z θ - b z θ) 0 :=
  (Work.FTS.StrongEps.EComparison.L12_sub_of_integrable (z := 0)
    (integrableOn_slice_of_bdd hA hca hba)
    (integrableOn_slice_of_bdd hB hcb hbb)
    (integrableOn_dens_of_bdd hA hca hba)
    (integrableOn_dens_of_bdd hB hcb hbb)).symm

end Work.FTS_RegExport.RXR5L.Auxiliary
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.L12dens_hasDerivAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project.

# `∂_z (L₁₂dens f) = (Qang f 1 - Qang f 0)/z²`

This module proves

  `Work.FTS_RegExport.RXT.Sys.L12FKaux.L12dens_hasDerivAt`,

the `z`-derivative of the `L₁₂`-density of a datum of the standing class
(`C⁴` on the open quadrant, `|D_z^k f| ≤ C₀ z^{3/2}/(1+z)²` for `k ≤ 2`).

Writing `A(x) = ∫_θ K(θ) f(x,θ) dθ` (so that `Qang f 0 = A` and `Qang f 1 z = z·A'(z)`,
and `L₁₂dens f = A(x)/x`), the claim is the quotient rule for `x ↦ A(x)/x`:

  `(A'(z)·z - A(z))/z² = (Qang f 1 z - Qang f 0 z)/z²`.

The differentiation under the angular integral is `hasDerivAt_integral_Itheta_K`
(sibling module), which needs bounds for `f` and `∂_z f` on the open strip
`(z/2, 2z) × (0, π/2)`; those come from the standing bound at `k = 0, 1` together with
`‖∂_z f‖ = ‖D_z f‖/x` and `x^{3/2}/(1+x)² ≤ (2z)^{3/2}`, `x^{1/2}/(1+x)² ≤ (2z)^{1/2}`
on the strip.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys.L12FKaux

set_option maxHeartbeats 800000

/-! ## Two elementary bounds on the strip `(z/2, 2z)` -/

/-- For `0 < x ≤ 2z`, `x^{3/2}/(1+x)² ≤ (2z)^{3/2}`. -/
private theorem rpow_three_halves_div_sq_le {z x : ℝ} (hz : 0 < z) (hx : 0 < x)
    (hxle : x ≤ 2 * z) :
    x ^ ((3 : ℝ) / 2) / (1 + x) ^ 2 ≤ (2 * z) ^ ((3 : ℝ) / 2) := by
  have h2z : 0 < 2 * z := by linarith
  have h1 : x ^ ((3 : ℝ) / 2) ≤ (2 * z) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow hx.le hxle (by norm_num)
  have h3 : (0 : ℝ) ≤ (2 * z) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg h2z.le _
  have h4 : (1 : ℝ) ≤ (1 + x) ^ 2 := by nlinarith [sq_nonneg x]
  have hbc : (2 * z) ^ ((3 : ℝ) / 2) ≤ (2 * z) ^ ((3 : ℝ) / 2) * (1 + x) ^ 2 := by
    simpa using mul_le_mul_of_nonneg_left h4 h3
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < (1 + x) ^ 2)]
  linarith

/-- For `0 < x ≤ 2z`, `x^{1/2}/(1+x)² ≤ (2z)^{1/2}`. -/
private theorem rpow_half_div_sq_le' {z x : ℝ} (hz : 0 < z) (hx : 0 < x)
    (hxle : x ≤ 2 * z) :
    x ^ ((1 : ℝ) / 2) / (1 + x) ^ 2 ≤ (2 * z) ^ ((1 : ℝ) / 2) := by
  have h2z : 0 < 2 * z := by linarith
  have h1 : x ^ ((1 : ℝ) / 2) ≤ (2 * z) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow hx.le hxle (by norm_num)
  have h3 : (0 : ℝ) ≤ (2 * z) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg h2z.le _
  have h4 : (1 : ℝ) ≤ (1 + x) ^ 2 := by nlinarith [sq_nonneg x]
  have hbc : (2 * z) ^ ((1 : ℝ) / 2) ≤ (2 * z) ^ ((1 : ℝ) / 2) * (1 + x) ^ 2 := by
    simpa using mul_le_mul_of_nonneg_left h4 h3
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < (1 + x) ^ 2)]
  linarith

/-! ## The main statement -/

theorem L12dens_hasDerivAt {f : ℝ → ℝ → ℝ} {C0 : ℝ} (hC0 : 0 ≤ C0)
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k f z θ| ≤ C0 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun x => Work.FM.L12dens Work.Spaces.K f x)
      ((Work.Elliptic.Qang f 1 z - Work.Elliptic.Qang f 0 z) / z ^ 2) z := by
  have hz2 : 0 < 2 * z := by linarith
  have hp : (0 : ℝ) ≤ (2 * z) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hz2.le _
  have hq : (0 : ℝ) ≤ (2 * z) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hz2.le _
  have hC : (0 : ℝ) ≤ C0 * ((2 * z) ^ ((3 : ℝ) / 2) + (2 * z) ^ ((1 : ℝ) / 2) + 1) :=
    mul_nonneg hC0 (by linarith)
  -- the two bounds on the open strip `(z/2, 2z) × (0, π/2)`
  have hb0 : ∀ x ∈ Set.Ioo (z / 2) (2 * z), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |f x θ| ≤ C0 * ((2 * z) ^ ((3 : ℝ) / 2) + (2 * z) ^ ((1 : ℝ) / 2) + 1) := by
    intro x hx θ hθ
    have hxpos : 0 < x := by linarith [hx.1, hz]
    have h := hbd 0 (by norm_num) x θ hxpos hθ.1 hθ.2
    simp only [Work.Spaces.DzIter_zero] at h
    refine le_trans h (mul_le_mul_of_nonneg_left ?_ hC0)
    linarith [rpow_three_halves_div_sq_le hz hxpos hx.2.le, hq]
  have hb1 : ∀ x ∈ Set.Ioo (z / 2) (2 * z), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |Work.Spaces.pz f x θ| ≤ C0 * ((2 * z) ^ ((3 : ℝ) / 2) + (2 * z) ^ ((1 : ℝ) / 2) + 1) := by
    intro x hx θ hθ
    have hxpos : 0 < x := by linarith [hx.1, hz]
    have hstep : |Work.Spaces.pz f x θ| ≤ C0 * (x ^ ((1 : ℝ) / 2) / (1 + x) ^ 2) := by
      have hkey : Work.Spaces.pz f x θ = Work.Spaces.DzIter 1 f x θ / x := by
        show Work.Spaces.pz f x θ = x * Work.Spaces.pz f x θ / x
        rw [mul_div_cancel_left₀ _ (ne_of_gt hxpos)]
      rw [hkey, abs_div, abs_of_pos hxpos]
      have h2 := hbd 1 (by norm_num) x θ hxpos hθ.1 hθ.2
      rw [Work.FTS_RegExport.RXT.Slots.rpow_three_halves hxpos] at h2
      calc |Work.Spaces.DzIter 1 f x θ| / x
          ≤ C0 * (x * x ^ ((1 : ℝ) / 2) / (1 + x) ^ 2) / x :=
            div_le_div_of_nonneg_right h2 hxpos.le
        _ = C0 * (x ^ ((1 : ℝ) / 2) / (1 + x) ^ 2) := by field_simp
    refine le_trans hstep (mul_le_mul_of_nonneg_left ?_ hC0)
    linarith [rpow_half_div_sq_le' hz hxpos hx.2.le, hp]
  -- differentiation under the angular integral (the sibling lemma)
  have h2' : ContDiffOn ℝ 2 (Function.uncurry f) Work.FTS.EllipticEst.Q0 :=
    h4.of_le (Nat.cast_le.mpr (by omega : 2 ≤ 4))
  have hd : HasDerivAt (Work.Elliptic.Qang f 0)
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz f z θ) z :=
    hasDerivAt_integral_Itheta_K (f := f) (z := z)
      (C := C0 * ((2 * z) ^ ((3 : ℝ) / 2) + (2 * z) ^ ((1 : ℝ) / 2) + 1))
      h2' hz hC hb1 hb0
  -- `Qang f 1 z = z · (∫_θ K ∂_z f)`, hence the integral is `Qang f 1 z / z`
  have hQ1z : Work.Elliptic.Qang f 1 z
      = z * ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz f z θ := by
    have h1 : Work.Elliptic.Qang f 1 z
        = ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.K θ * (z * Work.Spaces.pz f z θ) := rfl
    rw [h1, show (fun θ => Work.Spaces.K θ * (z * Work.Spaces.pz f z θ))
        = fun θ => z * (Work.Spaces.K θ * Work.Spaces.pz f z θ) from by
          funext θ; ring,
      MeasureTheory.integral_const_mul]
  have hQ1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz f z θ)
      = Work.Elliptic.Qang f 1 z / z := by
    rw [hQ1z, mul_div_cancel_left₀ _ (ne_of_gt hz)]
  rw [hQ1] at hd
  -- the quotient rule at the base point
  have hq : HasDerivAt (fun y => Work.Elliptic.Qang f 0 y / y)
      ((Work.Elliptic.Qang f 1 z / z * z - Work.Elliptic.Qang f 0 z * 1) / z ^ 2) z :=
    hd.div (hasDerivAt_id z) (ne_of_gt hz)
  have hder : (Work.Elliptic.Qang f 1 z / z * z - Work.Elliptic.Qang f 0 z * 1) / z ^ 2
      = (Work.Elliptic.Qang f 1 z - Work.Elliptic.Qang f 0 z) / z ^ 2 := by
    rw [div_mul_cancel₀ _ (ne_of_gt hz), mul_one]
  rw [hder] at hq
  -- the density is `Qang f 0 x / x`
  have hfun : (fun x => Work.FM.L12dens Work.Spaces.K f x)
      = fun x => Work.Elliptic.Qang f 0 x / x := by
    funext x
    exact Work.FTS_RegExport.RXT.L12Iter.L12dens_eq_Qang_zero f x
  rw [hfun]
  exact hq

end Work.FTS_RegExport.RXT.Sys.L12FKaux
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.Jets =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L12FKjet.Jets` — the `D_z`-jet identities and the linearity of `D_z^j`

Third part of the jet package of `L12_FK_jets_of_datum`: the identities

* `D_z L₁₂(F) = -Qang F 0 = -𝔽K(F)`,   `D_z² L₁₂(F) = -Qang F 1`,
* `D_z 𝔽K(F) = Qang F 1`,               `D_z² 𝔽K(F) = Qang F 2`

(where `D_z = z∂_z` and `Qang F m z = ∫_θ K(θ)D_z^mF(z,θ) dθ`), together with the linearity of
`D_z^j` (`j ≤ 2`) in the function at a point at which the function and its iterates are
differentiable, and the elementary real bound `C ≤ C⁴` for `C ≥ 1`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- `D_z L₁₂(F) = -Qang F 0` eventually (hence on all of `(0,∞)`). -/
theorem lfj_DzdIter_one_L12_eq {F : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hL : ∀ u ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z => Work.Construction.L12 F z) (-(Work.Construction.L12dens F u)) u) :
    Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 F z)
      =ᶠ[𝓝 z] fun u => -(Work.Elliptic.Qang F 0 u) := by
  filter_upwards [isOpen_Ioi.mem_nhds hz] with u hu
  have h1 : u * Work.Construction.L12dens F u = Work.Construction.FK F u :=
    Work.Construction.mul_L12dens_eq_FK (F := F) (ne_of_gt hu)
  rw [show Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 F z) u
      = u * deriv (fun z => Work.Construction.L12 F z) u from rfl, (hL u hu).deriv,
    lfj_Qang_zero_eq_FK F u, ← h1]
  ring

/-- **`D_z L₁₂(F) = -𝔽K(F)`.** -/
theorem lfj_DzdIter_one_L12 {F : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hL : HasDerivAt (fun z => Work.Construction.L12 F z)
      (-(Work.Construction.L12dens F z)) z) :
    Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 F z) z
      = - Work.Construction.FK F z := by
  have h1 : z * Work.Construction.L12dens F z = Work.Construction.FK F z :=
    Work.Construction.mul_L12dens_eq_FK (F := F) (ne_of_gt hz)
  rw [show Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 F z) z
      = z * deriv (fun z => Work.Construction.L12 F z) z from rfl, hL.deriv, ← h1]
  ring

/-- **`D_z² L₁₂(F) = -Qang F 1`.** -/
theorem lfj_DzdIter_two_L12 {F : ℝ → ℝ → ℝ} {z : ℝ}
    (h1e : Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 F z)
      =ᶠ[𝓝 z] fun u => -(Work.Elliptic.Qang F 0 u))
    (hQ0 : HasDerivAt (Work.Elliptic.Qang F 0) (Work.Elliptic.Qang F 1 z / z) z)
    (hz : 0 < z) :
    Work.Elliptic.DzdIter 2 (fun z => Work.Construction.L12 F z) z
      = -(Work.Elliptic.Qang F 1 z) := by
  have hder : deriv (Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 F z)) z
      = -(Work.Elliptic.Qang F 1 z / z) := by
    rw [h1e.deriv_eq]
    exact hQ0.neg.deriv
  show z * deriv (Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 F z)) z
      = -(Work.Elliptic.Qang F 1 z)
  rw [hder, show z * (-(Work.Elliptic.Qang F 1 z / z))
      = -(z * Work.Elliptic.Qang F 1 z / z) by ring,
    mul_div_cancel_left₀ _ (ne_of_gt hz)]

/-- `D_z 𝔽K(F) = Qang F 1` eventually. -/
theorem lfj_DzdIter_one_FK_eq {F : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hF : ∀ u ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun z => Work.Construction.FK F z)
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz F u θ * Work.Spaces.K θ) u) :
    Work.Elliptic.DzdIter 1 (fun z => Work.Construction.FK F z) =ᶠ[𝓝 z]
      Work.Elliptic.Qang F 1 := by
  filter_upwards [isOpen_Ioi.mem_nhds hz] with u hu
  rw [show Work.Elliptic.DzdIter 1 (fun z => Work.Construction.FK F z) u
      = u * deriv (fun z => Work.Construction.FK F z) u from rfl, (hF u hu).deriv,
    lfj_Qang_one_eq F u]

/-- **`D_z 𝔽K(F) = Qang F 1`.** -/
theorem lfj_DzdIter_one_FK {F : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hF : HasDerivAt (fun z => Work.Construction.FK F z)
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz F z θ * Work.Spaces.K θ) z) :
    Work.Elliptic.DzdIter 1 (fun z => Work.Construction.FK F z) z
      = Work.Elliptic.Qang F 1 z := by
  rw [show Work.Elliptic.DzdIter 1 (fun z => Work.Construction.FK F z) z
      = z * deriv (fun z => Work.Construction.FK F z) z from rfl, hF.deriv,
    lfj_Qang_one_eq F z]

/-- **`D_z² 𝔽K(F) = Qang F 2`.** -/
theorem lfj_DzdIter_two_FK {F : ℝ → ℝ → ℝ} {z : ℝ}
    (h1e : Work.Elliptic.DzdIter 1 (fun z => Work.Construction.FK F z) =ᶠ[𝓝 z]
      Work.Elliptic.Qang F 1)
    (hQ1 : HasDerivAt (Work.Elliptic.Qang F 1) (Work.Elliptic.Qang F 2 z / z) z)
    (hz : 0 < z) :
    Work.Elliptic.DzdIter 2 (fun z => Work.Construction.FK F z) z
      = Work.Elliptic.Qang F 2 z := by
  have hder : deriv (Work.Elliptic.DzdIter 1 (fun z => Work.Construction.FK F z)) z
      = Work.Elliptic.Qang F 2 z / z := by
    rw [h1e.deriv_eq, hQ1.deriv]
  show z * deriv (Work.Elliptic.DzdIter 1 (fun z => Work.Construction.FK F z)) z
      = Work.Elliptic.Qang F 2 z
  rw [hder, ← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt hz)]

/-! ## Linearity of the `D_z`-jets in the function -/

/-- `D_z^j` (`j ≤ 2`) is linear at a point at which `u`, `v` and their `D_z`-iterates are
differentiable. -/
theorem lfj_DzdIter_linear {u v : ℝ → ℝ} {a b z : ℝ}
    (hu1 : DifferentiableAt ℝ u z) (hv1 : DifferentiableAt ℝ v z)
    (hue : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ u w)
    (hve : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ v w)
    (hu2 : DifferentiableAt ℝ (Work.Elliptic.DzdIter 1 u) z)
    (hv2 : DifferentiableAt ℝ (Work.Elliptic.DzdIter 1 v) z) :
    ∀ j : ℕ, j ≤ 2 →
      Work.Elliptic.DzdIter j (fun w => a * u w + b * v w) z
        = a * Work.Elliptic.DzdIter j u z + b * Work.Elliptic.DzdIter j v z := by
  intro j hj
  interval_cases j
  · simp only [Work.Elliptic.DzdIter_zero]
  · simp only [Work.Elliptic.DzdIter_succ, Work.Elliptic.DzdIter_zero, Work.Elliptic.Dzd]
    have hsum : HasDerivAt (fun w => a * u w + b * v w)
        (a * deriv u z + b * deriv v z) z :=
      (hu1.hasDerivAt.const_mul a).add (hv1.hasDerivAt.const_mul b)
    rw [hsum.deriv]
    ring
  · have hev : Work.Elliptic.DzdIter 1 (fun w => a * u w + b * v w)
        =ᶠ[𝓝 z] fun w => a * Work.Elliptic.DzdIter 1 u w + b * Work.Elliptic.DzdIter 1 v w := by
      filter_upwards [hue, hve] with w huw hvw
      simp only [Work.Elliptic.DzdIter_succ, Work.Elliptic.DzdIter_zero, Work.Elliptic.Dzd]
      have hsum : HasDerivAt (fun w' => a * u w' + b * v w')
          (a * deriv u w + b * deriv v w) w :=
        (huw.hasDerivAt.const_mul a).add (hvw.hasDerivAt.const_mul b)
      rw [hsum.deriv]
      ring
    have hder : deriv (Work.Elliptic.DzdIter 1 (fun w => a * u w + b * v w)) z
        = a * deriv (Work.Elliptic.DzdIter 1 u) z
          + b * deriv (Work.Elliptic.DzdIter 1 v) z := by
      rw [hev.deriv_eq]
      have hsum : HasDerivAt
          (fun w => a * Work.Elliptic.DzdIter 1 u w + b * Work.Elliptic.DzdIter 1 v w)
          (a * deriv (Work.Elliptic.DzdIter 1 u) z + b * deriv (Work.Elliptic.DzdIter 1 v) z) z :=
        (hu2.hasDerivAt.const_mul a).add (hv2.hasDerivAt.const_mul b)
      exact hsum.deriv
    show z * deriv (Work.Elliptic.DzdIter 1 (fun w => a * u w + b * v w)) z
        = a * (z * deriv (Work.Elliptic.DzdIter 1 u) z)
          + b * (z * deriv (Work.Elliptic.DzdIter 1 v) z)
    rw [hder]
    ring

/-- The bound for a linear combination of two functions whose `D_z`-jets of order `≤ 2` are
bounded by `B`. -/
theorem lfj_DzdIter_lin_bound {u v : ℝ → ℝ} {a b z B : ℝ}
    (hlin : ∀ j : ℕ, j ≤ 2 →
      Work.Elliptic.DzdIter j (fun w => a * u w + b * v w) z
        = a * Work.Elliptic.DzdIter j u z + b * Work.Elliptic.DzdIter j v z)
    (hBu : ∀ j : ℕ, j ≤ 2 → |Work.Elliptic.DzdIter j u z| ≤ B)
    (hBv : ∀ j : ℕ, j ≤ 2 → |Work.Elliptic.DzdIter j v z| ≤ B) :
    ∀ j : ℕ, j ≤ 2 →
      |Work.Elliptic.DzdIter j (fun w => a * u w + b * v w) z| ≤ (|a| + |b|) * B := by
  intro j hj
  rw [hlin j hj]
  calc |a * Work.Elliptic.DzdIter j u z + b * Work.Elliptic.DzdIter j v z|
      ≤ |a * Work.Elliptic.DzdIter j u z| + |b * Work.Elliptic.DzdIter j v z| := abs_add_le _ _
    _ = |a| * |Work.Elliptic.DzdIter j u z| + |b| * |Work.Elliptic.DzdIter j v z| := by
        rw [abs_mul, abs_mul]
    _ ≤ |a| * B + |b| * B :=
        add_le_add (mul_le_mul_of_nonneg_left (hBu j hj) (abs_nonneg a))
          (mul_le_mul_of_nonneg_left (hBv j hj) (abs_nonneg b))
    _ = (|a| + |b|) * B := by ring

/-- `C ≤ C⁴` for `C ≥ 1`. -/
theorem lfj_le_pow_four {C : ℝ} (hC1 : 1 ≤ C) : C ≤ C ^ 4 := by
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have h1 : (1 : ℝ) ≤ C ^ 3 := one_le_pow₀ (n := 3) hC1
  calc C = C * 1 := by ring
    _ ≤ C * C ^ 3 := mul_le_mul_of_nonneg_left h1 hC0
    _ = C ^ 4 := by ring

/-- `|x| ≤ 18 C` upgrades to `|x| ≤ 64 C⁴` for `C ≥ 1`. -/
theorem lfj_le_const {x C : ℝ} (hC1 : 1 ≤ C) (h : |x| ≤ 18 * C) : |x| ≤ 64 * C ^ 4 := by
  have hC4 := lfj_le_pow_four hC1
  have hC0 : (0 : ℝ) ≤ C := by linarith
  nlinarith [h, hC4, hC0, hC1]

end Work.FTS_RegExport.RXT.Sys
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L12FKjet.L12` — the `L₁₂`-side of the jet package

Second half of the jet package of `L12_FK_jets_of_datum`: `∂_z L₁₂(F) = -L12dens(F)`
(`FM.hasDerivAt_L12`, whose continuity hypothesis comes from the angular-moment derivative of
`Qang F 0`), the bound `|L₁₂(F)(z)| ≤ C` from the `L¹`-control of the density, and the level one
angular moment differentiated under the `θ`-integral,
`∂_z Qang F 1 (z) = Qang F 2 z / z`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- `Work.Construction.L12dens F` is `Qang F 0` divided by the radial variable. -/
theorem lfj_FM_L12dens_eq (F : ℝ → ℝ → ℝ) :
    Work.FM.L12dens Work.Spaces.K F = fun s => Work.Elliptic.Qang F 0 s / s := by
  funext s
  rw [← Work.Elliptic.L12dens_eq_Qang_div F s]
  rfl

/-- Continuity of the `L₁₂`-density at `z`, from continuity of the level zero angular moment. -/
theorem lfj_L12dens_continuousAt {F : ℝ → ℝ → ℝ} {z : ℝ}
    (hQ0 : ContinuousAt (Work.Elliptic.Qang F 0) z) (hz : 0 < z) :
    ContinuousAt (Work.Construction.L12dens F) z := by
  have hfun : Work.Construction.L12dens F = fun s => Work.Elliptic.Qang F 0 s / s :=
    lfj_FM_L12dens_eq F
  rw [hfun]
  exact hQ0.div continuousAt_id (ne_of_gt hz)

/-- **`∂_z L₁₂(F)(z) = -L12dens(F)(z)`.** -/
theorem lfj_L12_hasDerivAt {F : ℝ → ℝ → ℝ} {z : ℝ}
    (hint : IntegrableOn (Work.Construction.L12dens F) (Set.Ioi 0))
    (hcont : ContinuousAt (Work.Construction.L12dens F) z) (hz : 0 < z) :
    HasDerivAt (fun z' => Work.Construction.L12 F z')
      (-(Work.Construction.L12dens F z)) z := by
  have hin : IntegrableOn (Work.FM.L12dens Work.Spaces.K F) (Set.Ioi 0) := hint
  have hc : ContinuousAt (Work.FM.L12dens Work.Spaces.K F) z := hcont
  simpa only [Work.Construction.L12, Work.Construction.L12dens] using
    Work.FM.hasDerivAt_L12 (K := Work.Spaces.K) (f := F) (a := 0) (ρ := z) hin hc (by linarith)

/-- **`|L₁₂(F)(z)| ≤ C`** from the `L¹`-control of the density. -/
theorem lfj_L12_abs_le {F : ℝ → ℝ → ℝ} {C z : ℝ}
    (hint : IntegrableOn (Work.Construction.L12dens F) (Set.Ioi 0))
    (hmass : (∫ s in Set.Ioi 0, |Work.Construction.L12dens F s|) ≤ C) (hz : 0 < z) :
    |Work.Construction.L12 F z| ≤ C := by
  have h1 : |∫ s in Set.Ioi z, Work.Construction.L12dens F s| ≤
      ∫ s in Set.Ioi z, |Work.Construction.L12dens F s| := by
    have h := MeasureTheory.norm_integral_le_integral_norm
      (μ := volume.restrict (Set.Ioi z)) (f := fun s => Work.Construction.L12dens F s)
    simpa only [Real.norm_eq_abs] using h
  have h2 : (∫ s in Set.Ioi z, |Work.Construction.L12dens F s|) ≤
      ∫ s in Set.Ioi 0, |Work.Construction.L12dens F s| :=
    MeasureTheory.setIntegral_mono_set hint.abs
      (Filter.Eventually.of_forall fun x => abs_nonneg _)
      (Set.Ioi_subset_Ioi hz.le).eventuallySubset
  have h3 : Work.Construction.L12 F z
      = ∫ s in Set.Ioi z, Work.Construction.L12dens F s := rfl
  rw [h3]
  linarith [h1, h2, hmass]

/-- **`∂_z Qang F 1 (z) = Qang F 2 z / z`** (the level one angular moment, differentiated). -/
theorem lfj_Qang_one_hasDerivAt {F : ℝ → ℝ → ℝ} {C z : ℝ}
    (h2 : ContDiffOn ℝ 2 (Function.uncurry F) Work.FTS.EllipticEst.Q0)
    (hb : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k F z θ| ≤ C)
    (hC : 0 ≤ C) (hz : 0 < z) :
    HasDerivAt (Work.Elliptic.Qang F 1) (Work.Elliptic.Qang F 2 z / z) z := by
  haveI : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) :=
    Work.FTS_RegExport.RXT.Slots.isFiniteMeasure_restrict_Iθ
  have hz2 : 0 < z / 2 := by linarith
  have hVmem : z ∈ Set.Ioi (z / 2) := Set.mem_Ioi.mpr (by linarith)
  have hVpos : ∀ x ∈ Set.Ioi (z / 2), 0 < x := fun x hx => lt_trans hz2 (Set.mem_Ioi.mp hx)
  have hcd1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.DzIter 1 F))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DzIter_fin Work.FTS.EllipticEst.isOpen_Q0
      (n := 2) h2 1 (by norm_num)
  have hpz1 : ContDiffOn ℝ 0
      (Function.uncurry (Work.Spaces.pz (Work.Spaces.DzIter 1 F))) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_pz_fin Work.FTS.EllipticEst.isOpen_Q0 (n := 0) hcd1
  have hKbd : ∀ θ : ℝ, |Work.Elliptic.Ktheta θ| ≤ 3 :=
    Work.FTS_RegExport.RXT.Slots.abs_Ktheta_le
  have hcg : ContinuousOn
      (Function.uncurry (fun x θ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter 1 F x θ))
      Work.FTS.EllipticEst.Q0 :=
    show ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * Work.Spaces.DzIter 1 F p.1 p.2)
      Work.FTS.EllipticEst.Q0 from lfj_continuousOn_Ktheta_jet.mul hcd1.continuousOn
  have hcg' : ContinuousOn
      (Function.uncurry (fun x θ => Work.Elliptic.Ktheta θ
        * Work.Spaces.pz (Work.Spaces.DzIter 1 F) x θ)) Work.FTS.EllipticEst.Q0 :=
    show ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
        * Work.Spaces.pz (Work.Spaces.DzIter 1 F) p.1 p.2) Work.FTS.EllipticEst.Q0 from
      lfj_continuousOn_Ktheta_jet.mul hpz1.continuousOn
  have hint : Integrable (fun θ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter 1 F z θ)
      (volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (3 * C))
      (Work.FTS_RegExport.RXT.Slots.aesm_slice_Q0 hcg hz) ?_
    rw [Work.FTS_RegExport.RXT.Slots.restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hKbd θ) (hb 1 (by norm_num) z θ hz hθ.1 hθ.2) (abs_nonneg _) (by norm_num)
  have hpzbd : ∀ x ∈ Set.Ioi (z / 2), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |Work.Spaces.pz (Work.Spaces.DzIter 1 F) x θ| ≤ 2 * C / z := by
    intro x hx θ hθ
    have hx0 : 0 < x := hVpos x hx
    have hxz : z / 2 < x := Set.mem_Ioi.mp hx
    have h := hb 2 (by norm_num) x θ hx0 hθ.1 hθ.2
    have heq : Work.Spaces.DzIter 2 F x θ
        = x * Work.Spaces.pz (Work.Spaces.DzIter 1 F) x θ := rfl
    rw [heq, abs_mul, abs_of_pos hx0] at h
    have hle : |Work.Spaces.pz (Work.Spaces.DzIter 1 F) x θ| ≤ C / x := by
      rw [le_div_iff₀ hx0]; rw [mul_comm]; exact h
    have h2' : C / x ≤ 2 * C / z := by
      have h3 : C / x ≤ C / (z / 2) := div_le_div_of_nonneg_left hC hz2 hxz.le
      have h4 : C / (z / 2) = 2 * C / z := by field_simp
      linarith [h3, le_of_eq h4]
    linarith
  have hbound : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), ∀ x ∈ Set.Ioi (z / 2),
      ‖Work.Elliptic.Ktheta θ * Work.Spaces.pz (Work.Spaces.DzIter 1 F) x θ‖
        ≤ 3 * (2 * C / z) := by
    rw [Work.FTS_RegExport.RXT.Slots.restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ x hx => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h3 := hpzbd x hx θ hθ
    exact mul_le_mul (hKbd θ) h3 (abs_nonneg _) (by norm_num)
  have hdiff : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ x ∈ Set.Ioi (z / 2),
      HasDerivAt (fun y => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter 1 F y θ)
        (Work.Elliptic.Ktheta θ * Work.Spaces.pz (Work.Spaces.DzIter 1 F) x θ) x :=
    fun θ hθ x hx =>
      (lfj_slice_hasDerivAt hcd1 (hVpos x hx) hθ.1 hθ.2).const_mul _
  have key := Work.FTS_RegExport.RXT.Slots.hasDerivAt_integral_Itheta_Q0 (V := Set.Ioi (z / 2))
    isOpen_Ioi hVmem hVpos hcg hcg' hint hbound hdiff
  have hval : (∫ θ in Work.Spaces.Iθ,
        Work.Elliptic.Ktheta θ * Work.Spaces.pz (Work.Spaces.DzIter 1 F) z θ)
      = Work.Elliptic.Qang F 2 z / z := by
    rw [lfj_Qang_succ_eq F 1 z, mul_div_cancel_left₀ _ (ne_of_gt hz)]
  rw [hval] at key
  have hfun : Work.Elliptic.Qang F 1 = fun x => ∫ θ in Work.Spaces.Iθ,
      Work.Elliptic.Ktheta θ * Work.Spaces.DzIter 1 F x θ := rfl
  rw [hfun]
  exact key

end Work.FTS_RegExport.RXT.Sys
end
end
