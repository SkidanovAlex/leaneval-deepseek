import Mathlib
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Have
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.Blocks.InterpTrunc.cut_functional_le
import Submission.Work.Blocks.InterpTrunc.zF_abs_le
import Submission.Work.Coercivity.slice_ibp_eta
import Submission.Work.Coercivity.wip_L_self
import Submission.Work.FTS.ClassCHon.CmodeDefs
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.A_sq_prod_le
import Submission.Work.FTS.EllipticEst.Alpha4.integrable_slice_pthDz_sigma
import Submission.Work.FTS.EllipticEst.H2W.Ae.TruncIdentAe
import Submission.Work.FTS.EllipticEst.H2W.PsiSlices.PsiBox
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.RPFresh.slice_z_integrable
import Submission.Work.FTS.EllipticEst.SliceAux
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.TT.ESW.Tk_B_le_chain_uniform
import Submission.Work.FTS.EllipticEst.ThetaSliceIdent
import Submission.Work.FTS.EllipticEst.ZCuts.zHardy_compact
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.Dz_slice_identities
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.CleanBase
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.GalBasis.cut.LN_slot_tendsto
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.H2.T2Qaux.SupAux
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts
import Submission.Work.FTS.PhiStar.Psi0Aux.dthU_iter_elementary_bounds_repaired
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongPersist.L3Aux.acoef_gamCoef_slots_le
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.StrongPersist.QangSq6
import Submission.Work.FTS.StrongPersist.QangSq6Full
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.H2.T1Q.SlotBoundQ
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.H2.WPQ.hardy_slice_Aang
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.H2W.PsiSlices.shiftedSourcePoleBound
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.SolutionDelivery.Scaling.Main
import Submission.Work.Spaces.HProductRule_bad_term
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
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.StabilityFar.Decay.hasDerivAt_bsK
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.Blocks.interp_truncation =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Blocks


end Work.Blocks
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.thetaInterpCore =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux

set_option autoImplicit false

open scoped Real Topology
open MeasureTheory Set Filter

theorem thetaInterpCore : ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ,
    ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
    f 0 = 0 → f (Real.pi / 2) = 0 →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ C * ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + Real.sqrt ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
              * (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))) := by
  exact @Work.EllipticEst.Core.i0Aux.thetaInterpCoreOfTraceVanishing
    (fun _ : ℝ => 0)
    Work.EllipticEst.Core.i0Aux.traceVanishingInterp
    ⟨0, 0, tendsto_const_nhds, tendsto_const_nhds⟩

end Work.EllipticEst.Core.i0Aux
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.Q0.transportWeakRRAux =====
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

/-! ## The real and imaginary parts of a complex test function -/

/-- The real part of a complex-valued function of two variables. -/
def reFun (ψ : ℝ → ℝ → ℂ) : ℝ → ℝ → ℝ := fun σ θ => (ψ σ θ).re

/-- The imaginary part of a complex-valued function of two variables. -/
def imFun (ψ : ℝ → ℝ → ℂ) : ℝ → ℝ → ℝ := fun σ θ => (ψ σ θ).im

theorem uncurry_reFun (ψ : ℝ → ℝ → ℂ) :
    Function.uncurry (reFun ψ) = fun p : ℝ × ℝ => (Function.uncurry ψ p).re := rfl

theorem uncurry_imFun (ψ : ℝ → ℝ → ℂ) :
    Function.uncurry (imFun ψ) = fun p : ℝ × ℝ => (Function.uncurry ψ p).im := rfl

theorem contDiff_uncurry_reFun {ψ : ℝ → ℝ → ℂ}
    (hψ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ)) :
    ∀ n : ℕ, ContDiff ℝ n (Function.uncurry (reFun ψ)) := by
  intro n
  rw [uncurry_reFun]
  exact Complex.reCLM.contDiff.comp (hψ n)

theorem contDiff_uncurry_imFun {ψ : ℝ → ℝ → ℂ}
    (hψ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ)) :
    ∀ n : ℕ, ContDiff ℝ n (Function.uncurry (imFun ψ)) := by
  intro n
  rw [uncurry_imFun]
  exact Complex.imCLM.contDiff.comp (hψ n)

theorem hasCompactSupport_uncurry_reFun {ψ : ℝ → ℝ → ℂ}
    (hψc : HasCompactSupport (Function.uncurry ψ)) :
    HasCompactSupport (Function.uncurry (reFun ψ)) := by
  rw [uncurry_reFun]
  exact hψc.comp_left (g := Complex.re) (by simp)

theorem hasCompactSupport_uncurry_imFun {ψ : ℝ → ℝ → ℂ}
    (hψc : HasCompactSupport (Function.uncurry ψ)) :
    HasCompactSupport (Function.uncurry (imFun ψ)) := by
  rw [uncurry_imFun]
  exact hψc.comp_left (g := Complex.im) (by simp)

theorem tsupport_uncurry_reFun_subset (ψ : ℝ → ℝ → ℂ) :
    tsupport (Function.uncurry (reFun ψ)) ⊆ tsupport (Function.uncurry ψ) := by
  have hs : Function.support (fun p : ℝ × ℝ => (Function.uncurry ψ p).re)
      ⊆ Function.support (Function.uncurry ψ) := by
    intro p hp
    have hp' : (Function.uncurry ψ p).re ≠ 0 := hp
    intro h0
    exact hp' (by simp [h0])
  rw [uncurry_reFun]
  exact closure_mono hs

theorem tsupport_uncurry_imFun_subset (ψ : ℝ → ℝ → ℂ) :
    tsupport (Function.uncurry (imFun ψ)) ⊆ tsupport (Function.uncurry ψ) := by
  have hs : Function.support (fun p : ℝ × ℝ => (Function.uncurry ψ p).im)
      ⊆ Function.support (Function.uncurry ψ) := by
    intro p hp
    have hp' : (Function.uncurry ψ p).im ≠ 0 := hp
    intro h0
    exact hp' (by simp [h0])
  rw [uncurry_imFun]
  exact closure_mono hs

/-! ## The pointwise complex identities -/

/-- `VRR · kopD` splits into its real and imaginary parts. -/
theorem VRR_mul_kopD_eq {α : ℝ} {Ψ : ℝ → ℝ → ℝ} {ψ : ℝ → ℝ → ℂ}
    (hψ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ)) (σ θ : ℝ) :
    (VRR α Ψ σ θ : ℂ) * kopD ψ σ θ
      = ((VRR α Ψ σ θ * kopDr (reFun ψ) σ θ : ℝ) : ℂ)
        + Complex.I * ((VRR α Ψ σ θ * kopDr (imFun ψ) σ θ : ℝ) : ℂ) := by
  have hre : (kopD ψ σ θ).re = kopDr (reFun ψ) σ θ := kopD_re hψ σ θ
  have him : (kopD ψ σ θ).im = kopDr (imFun ψ) σ θ := kopD_im hψ σ θ
  conv_lhs => rw [← Complex.re_add_im (kopD ψ σ θ)]
  rw [hre, him]
  simp only [Complex.ofReal_mul]
  ring

/-- `GRR · ψ` splits into its real and imaginary parts. -/
theorem GRR_mul_test_eq {α : ℝ} {F : ℝ → ℝ → ℝ} {ψ : ℝ → ℝ → ℂ} (σ θ : ℝ) :
    (GRR α F σ θ : ℂ) * ψ σ θ
      = ((GRR α F σ θ * reFun ψ σ θ : ℝ) : ℂ)
        + Complex.I * ((GRR α F σ θ * imFun ψ σ θ : ℝ) : ℂ) := by
  have hre : (ψ σ θ).re = reFun ψ σ θ := rfl
  have him : (ψ σ θ).im = imFun ψ σ θ := rfl
  conv_lhs => rw [← Complex.re_add_im (ψ σ θ)]
  rw [hre, him]
  simp only [Complex.ofReal_mul]
  ring

/-! ## The complex integrals -/

/-- The left-hand side of the transported weak formulation, split into real and imaginary
parts. -/
theorem integral_VRR_kopD {α : ℝ} (hα : 0 < α) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0)
    {ψ : ℝ → ℝ → ℂ} (hψ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ))
    (hψc : HasCompactSupport (Function.uncurry ψ))
    (hψs : tsupport (Function.uncurry ψ) ⊆ stripRR) :
    (∫ q : ℝ × ℝ, (VRR α Ψ q.1 q.2 : ℂ) * kopD ψ q.1 q.2)
      = ((∫ q : ℝ × ℝ, VRR α Ψ q.1 q.2 * kopDr (reFun ψ) q.1 q.2 : ℝ) : ℂ)
        + Complex.I * ((∫ q : ℝ × ℝ, VRR α Ψ q.1 q.2 * kopDr (imFun ψ) q.1 q.2 : ℝ) : ℂ) := by
  have hr : MeasureTheory.Integrable
      (fun q : ℝ × ℝ => VRR α Ψ q.1 q.2 * kopDr (reFun ψ) q.1 q.2) :=
    integrable_VRR_kopDr hα hΨ (contDiff_uncurry_reFun hψ)
      (hasCompactSupport_uncurry_reFun hψc) (subset_trans (tsupport_uncurry_reFun_subset ψ) hψs)
  have hi : MeasureTheory.Integrable
      (fun q : ℝ × ℝ => VRR α Ψ q.1 q.2 * kopDr (imFun ψ) q.1 q.2) :=
    integrable_VRR_kopDr hα hΨ (contDiff_uncurry_imFun hψ)
      (hasCompactSupport_uncurry_imFun hψc) (subset_trans (tsupport_uncurry_imFun_subset ψ) hψs)
  have hrC : MeasureTheory.Integrable
      (fun q : ℝ × ℝ => ((VRR α Ψ q.1 q.2 * kopDr (reFun ψ) q.1 q.2 : ℝ) : ℂ)) :=
    hr.ofReal
  have hiC : MeasureTheory.Integrable
      (fun q : ℝ × ℝ => Complex.I * ((VRR α Ψ q.1 q.2 * kopDr (imFun ψ) q.1 q.2 : ℝ) : ℂ)) :=
    hi.ofReal.const_mul Complex.I
  have hpt : (fun q : ℝ × ℝ => (VRR α Ψ q.1 q.2 : ℂ) * kopD ψ q.1 q.2)
      = fun q : ℝ × ℝ => ((VRR α Ψ q.1 q.2 * kopDr (reFun ψ) q.1 q.2 : ℝ) : ℂ)
          + Complex.I * ((VRR α Ψ q.1 q.2 * kopDr (imFun ψ) q.1 q.2 : ℝ) : ℂ) :=
    funext fun q => VRR_mul_kopD_eq hψ q.1 q.2
  rw [hpt, MeasureTheory.integral_add hrC hiC, integral_complex_ofReal,
    MeasureTheory.integral_const_mul Complex.I
      (fun q : ℝ × ℝ => ((VRR α Ψ q.1 q.2 * kopDr (imFun ψ) q.1 q.2 : ℝ) : ℂ)),
    integral_complex_ofReal]
  try rfl

/-- The right-hand side of the transported weak formulation, split into real and imaginary
parts. -/
theorem integral_GRR_test {α : ℝ} {F : ℝ → ℝ → ℝ} {ψ : ℝ → ℝ → ℂ}
    (hr : MeasureTheory.Integrable (fun q : ℝ × ℝ => GRR α F q.1 q.2 * reFun ψ q.1 q.2))
    (hi : MeasureTheory.Integrable (fun q : ℝ × ℝ => GRR α F q.1 q.2 * imFun ψ q.1 q.2)) :
    (∫ q : ℝ × ℝ, (GRR α F q.1 q.2 : ℂ) * ψ q.1 q.2)
      = ((∫ q : ℝ × ℝ, GRR α F q.1 q.2 * reFun ψ q.1 q.2 : ℝ) : ℂ)
        + Complex.I * ((∫ q : ℝ × ℝ, GRR α F q.1 q.2 * imFun ψ q.1 q.2 : ℝ) : ℂ) := by
  have hrC : MeasureTheory.Integrable
      (fun q : ℝ × ℝ => ((GRR α F q.1 q.2 * reFun ψ q.1 q.2 : ℝ) : ℂ)) :=
    hr.ofReal
  have hiC : MeasureTheory.Integrable
      (fun q : ℝ × ℝ => Complex.I * ((GRR α F q.1 q.2 * imFun ψ q.1 q.2 : ℝ) : ℂ)) :=
    hi.ofReal.const_mul Complex.I
  have hpt : (fun q : ℝ × ℝ => (GRR α F q.1 q.2 : ℂ) * ψ q.1 q.2)
      = fun q : ℝ × ℝ => ((GRR α F q.1 q.2 * reFun ψ q.1 q.2 : ℝ) : ℂ)
          + Complex.I * ((GRR α F q.1 q.2 * imFun ψ q.1 q.2 : ℝ) : ℂ) :=
    funext fun q => GRR_mul_test_eq q.1 q.2
  rw [hpt, MeasureTheory.integral_add hrC hiC, integral_complex_ofReal,
    MeasureTheory.integral_const_mul Complex.I
      (fun q : ℝ × ℝ => ((GRR α F q.1 q.2 * imFun ψ q.1 q.2 : ℝ) : ℂ)),
    integral_complex_ofReal]
  try rfl

/-- The real part of an integrable complex integrand is integrable (in the `F · reFun`-form). -/
theorem integrable_re_of_complex {F : ℝ → ℝ → ℝ} {ψ : ℝ → ℝ → ℂ}
    (h : MeasureTheory.Integrable (fun q : ℝ × ℝ => (F q.1 q.2 : ℂ) * ψ q.1 q.2)) :
    MeasureTheory.Integrable (fun q : ℝ × ℝ => F q.1 q.2 * reFun ψ q.1 q.2) := by
  have h1 : MeasureTheory.Integrable
      (fun q : ℝ × ℝ => ((F q.1 q.2 : ℂ) * ψ q.1 q.2).re) := h.re
  refine h1.congr (Filter.Eventually.of_forall fun q => ?_)
  simp only [reFun, RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

/-- The imaginary part of an integrable complex integrand is integrable. -/
theorem integrable_im_of_complex {F : ℝ → ℝ → ℝ} {ψ : ℝ → ℝ → ℂ}
    (h : MeasureTheory.Integrable (fun q : ℝ × ℝ => (F q.1 q.2 : ℂ) * ψ q.1 q.2)) :
    MeasureTheory.Integrable (fun q : ℝ × ℝ => F q.1 q.2 * imFun ψ q.1 q.2) := by
  have h1 : MeasureTheory.Integrable
      (fun q : ℝ × ℝ => ((F q.1 q.2 : ℂ) * ψ q.1 q.2).im) := h.im
  refine h1.congr (Filter.Eventually.of_forall fun q => ?_)
  simp only [imFun, RCLike.im_to_complex, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]

/-! ## The assembly -/

theorem transportWeakRR_of_pullback {α : ℝ} (hα : 0 < α) {F Ψ : ℝ → ℝ → ℝ}
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0)
    (hweak : ∀ φ : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) →
      HasCompactSupport (Function.uncurry φ) →
      tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 →
      (∫ p in Work.FTS.EllipticEst.Q0,
          Ψ p.1 p.2 * (Work.Elliptic.bslOp α φ p.1 p.2)
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
        = ∫ p in Work.FTS.EllipticEst.Q0,
            F p.1 p.2 * φ p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
    (hpull : ∀ ψ : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ)) →
      HasCompactSupport (Function.uncurry ψ) →
      tsupport (Function.uncurry ψ) ⊆ stripRR →
      ∃ φ : ℝ → ℝ → ℝ,
        (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) ∧
        HasCompactSupport (Function.uncurry φ) ∧
        tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 ∧
        (∀ z θ : ℝ, 0 < z → φ z θ = ψ ((1 / α) * Real.log z) θ) ∧
        (∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
          Work.Elliptic.bslOp α φ z θ = kopDr ψ ((1 / α) * Real.log z) θ)) :
    StripWeakRR (fun σ θ => (VRR α Ψ σ θ : ℂ)) (fun σ θ => (GRR α F σ θ : ℂ)) := by
  intro ψ hψ hψc hψs
  have hweak' : ∀ φ : ℝ → ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) →
      HasCompactSupport (Function.uncurry φ) →
      tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 →
      (∫ p in Work.FTS.EllipticEst.Q0, Lint α Ψ φ p)
        = ∫ p in Work.FTS.EllipticEst.Q0, Gint α F φ p := by
    intro φ h1 h2 h3
    simpa only [Lint, Gint] using hweak φ h1 h2 h3
  have hψr := contDiff_uncurry_reFun hψ
  have hψi := contDiff_uncurry_imFun hψ
  have hψrc := hasCompactSupport_uncurry_reFun hψc
  have hψic := hasCompactSupport_uncurry_imFun hψc
  have hψrs : tsupport (Function.uncurry (reFun ψ)) ⊆ stripRR :=
    subset_trans (tsupport_uncurry_reFun_subset ψ) hψs
  have hψis : tsupport (Function.uncurry (imFun ψ)) ⊆ stripRR :=
    subset_trans (tsupport_uncurry_imFun_subset ψ) hψs
  obtain ⟨φr, hφrsm, hφrc, hφrQ, hφrval, hφrbsl⟩ := hpull (reFun ψ) hψr hψrc hψrs
  obtain ⟨φi, hφism, hφic, hφiQ, hφival, hφibsl⟩ := hpull (imFun ψ) hψi hψic hψis
  have hTr : (∫ q : ℝ × ℝ, VRR α Ψ q.1 q.2 * kopDr (reFun ψ) q.1 q.2)
      = ∫ q : ℝ × ℝ, GRR α F q.1 q.2 * reFun ψ q.1 q.2 :=
    transport_real hα hΨ hweak' hψr hψrc hψrs hφrsm hφrc hφrQ hφrval hφrbsl
  have hTi : (∫ q : ℝ × ℝ, VRR α Ψ q.1 q.2 * kopDr (imFun ψ) q.1 q.2)
      = ∫ q : ℝ × ℝ, GRR α F q.1 q.2 * imFun ψ q.1 q.2 :=
    transport_real hα hΨ hweak' hψi hψic hψis hφism hφic hφiQ hφival hφibsl
  rw [integral_VRR_kopD hα hΨ hψ hψc hψs, hTr, hTi]
  by_cases hnd : Nondeg α Ψ
  · have hr : MeasureTheory.Integrable
        (fun q : ℝ × ℝ => GRR α F q.1 q.2 * reFun ψ q.1 q.2) :=
      (integrable_GRR_iff hα hφrval hφrQ).mpr
        (integrableOn_Gint_of_nondeg hα hΨ hweak' hnd hψr hψrc hψrs
          hφrsm hφrc hφrQ hφrval hφrbsl)
    have hi : MeasureTheory.Integrable
        (fun q : ℝ × ℝ => GRR α F q.1 q.2 * imFun ψ q.1 q.2) :=
      (integrable_GRR_iff hα hφival hφiQ).mpr
        (integrableOn_Gint_of_nondeg hα hΨ hweak' hnd hψi hψic hψis
          hφism hφic hφiQ hφival hφibsl)
    rw [integral_GRR_test hr hi]
  · have hzr : (∫ q : ℝ × ℝ, VRR α Ψ q.1 q.2 * kopDr (reFun ψ) q.1 q.2) = 0 :=
      VRR_kopDr_eq_zero_of_not_nondeg hα hΨ hnd hψr hψrc hψrs hφrsm hφrc hφrQ hφrval hφrbsl
    have hzi : (∫ q : ℝ × ℝ, VRR α Ψ q.1 q.2 * kopDr (imFun ψ) q.1 q.2) = 0 :=
      VRR_kopDr_eq_zero_of_not_nondeg hα hΨ hnd hψi hψic hψis hφism hφic hφiQ hφival hφibsl
    have hzr' : (∫ q : ℝ × ℝ, GRR α F q.1 q.2 * reFun ψ q.1 q.2) = 0 := by
      rw [← hTr]; exact hzr
    have hzi' : (∫ q : ℝ × ℝ, GRR α F q.1 q.2 * imFun ψ q.1 q.2) = 0 := by
      rw [← hTi]; exact hzi
    rw [hzr', hzi', Complex.ofReal_zero, mul_zero, add_zero]
    by_cases hint : MeasureTheory.Integrable
        (fun q : ℝ × ℝ => (GRR α F q.1 q.2 : ℂ) * ψ q.1 q.2)
    · rw [integral_GRR_test (integrable_re_of_complex hint) (integrable_im_of_complex hint),
        hzr', hzi', Complex.ofReal_zero, mul_zero, add_zero]
    · rw [MeasureTheory.integral_undef hint]

end Work.EllipticEst.InteriorRegularity.Q0
end
end
-- ===== merged: Submission.Work.FTS.Apriori.Limit.HksqCut_le_HkSq =====
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


end Work.FTS.Apriori.Limit
end
end
-- ===== merged: Submission.Work.FTS.Apriori.Limit.SupportBox =====
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

/-- A compact subset of the open quadrant `Qd = (0,∞) × (0,π/2)` is contained in a closed box
`[A,B] × [C,D]` with strictly positive `z`-bounds and with angular bounds inside `(0,π/2)`. -/
theorem exists_box_of_isCompact_subset_Qd {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hsub : K ⊆ Qd) :
    ∃ A B C D : ℝ, 0 < A ∧ A ≤ B ∧ 0 < C ∧ C ≤ D ∧ D < π / 2 ∧
      K ⊆ Set.Icc A B ×ˢ Set.Icc C D := by
  by_cases hne : K.Nonempty
  · have hKz : IsCompact (Prod.fst '' K) := hK.image continuous_fst
    have hKθ : IsCompact (Prod.snd '' K) := hK.image continuous_snd
    have hnez : (Prod.fst '' K).Nonempty := hne.image Prod.fst
    have hneθ : (Prod.snd '' K).Nonempty := hne.image Prod.snd
    refine ⟨sInf (Prod.fst '' K), sSup (Prod.fst '' K), sInf (Prod.snd '' K),
      sSup (Prod.snd '' K), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨p, hp, hp1⟩ := hKz.sInf_mem hnez
      rw [← hp1]
      exact (mem_Qd_iff.mp (hsub hp)).1
    · exact csInf_le hKz.bddBelow (hKz.sSup_mem hnez)
    · obtain ⟨p, hp, hp2⟩ := hKθ.sInf_mem hneθ
      rw [← hp2]
      exact (mem_Qd_iff.mp (hsub hp)).2.1
    · exact csInf_le hKθ.bddBelow (hKθ.sSup_mem hneθ)
    · obtain ⟨p, hp, hp2⟩ := hKθ.sSup_mem hneθ
      rw [← hp2]
      exact (mem_Qd_iff.mp (hsub hp)).2.2
    · intro p hp
      constructor
      · rw [Set.mem_Icc]
        exact ⟨csInf_le hKz.bddBelow ⟨p, hp, rfl⟩, le_csSup hKz.bddAbove ⟨p, hp, rfl⟩⟩
      · rw [Set.mem_Icc]
        exact ⟨csInf_le hKθ.bddBelow ⟨p, hp, rfl⟩, le_csSup hKθ.bddAbove ⟨p, hp, rfl⟩⟩
  · refine ⟨1, 1, 1, 1, one_pos, le_rfl, one_pos, le_rfl, ?_, ?_⟩
    · linarith [Real.pi_gt_three]
    · intro p hp
      exact absurd ⟨p, hp⟩ hne

/-- **The box of a compactly supported function vanishing off the open quadrant.**  There are
`A < B` and `C < D` with `0 < A`, `C > 0`, `D < π/2` such that `W` vanishes for `z < A`, for
`z > B`, for `θ < C` and for `θ > D` — with no restriction on the other variable. -/
theorem exists_box_vanish {W : ℝ → ℝ → ℝ}
    (hcomp : HasCompactSupport (Function.uncurry W))
    (hsub : tsupport (Function.uncurry W) ⊆ Qd) :
    ∃ A B C D : ℝ, 0 < A ∧ A < B ∧ 0 < C ∧ C < D ∧ D < π / 2 ∧
      (∀ z θ, z < A → W z θ = 0) ∧ (∀ z θ, B < z → W z θ = 0) ∧
      (∀ z θ, θ < C → W z θ = 0) ∧ (∀ z θ, D < θ → W z θ = 0) := by
  obtain ⟨A₀, B₀, C₀, D₀, hA₀, hAB₀, hC₀, hCD₀, hD₀, hbox⟩ :=
    exists_box_of_isCompact_subset_Qd hcomp hsub
  have hmem_of : ∀ z θ : ℝ, W z θ ≠ 0 →
      (z, θ) ∈ tsupport (Function.uncurry W) := fun z θ h =>
    subset_tsupport _ (by simpa [Function.mem_support, Function.uncurry] using h)
  refine ⟨A₀ / 2, B₀ + 1, C₀ / 2, (D₀ + π / 2) / 2, by linarith, by linarith, by linarith,
    by linarith, by linarith, ?_, ?_, ?_, ?_⟩
  · intro z θ hz
    by_contra h
    have h1 : (z, θ) ∈ Set.Icc A₀ B₀ ×ˢ Set.Icc C₀ D₀ := hbox (hmem_of z θ h)
    rw [Set.mem_prod, Set.mem_Icc] at h1
    linarith [h1.1.1]
  · intro z θ hz
    by_contra h
    have h1 : (z, θ) ∈ Set.Icc A₀ B₀ ×ˢ Set.Icc C₀ D₀ := hbox (hmem_of z θ h)
    rw [Set.mem_prod, Set.mem_Icc] at h1
    linarith [h1.1.2]
  · intro z θ hz
    by_contra h
    have h1 : (z, θ) ∈ Set.Icc A₀ B₀ ×ˢ Set.Icc C₀ D₀ := hbox (hmem_of z θ h)
    rw [Set.mem_prod, Set.mem_Icc] at h1
    linarith [h1.2.1]
  · intro z θ hz
    by_contra h
    have h1 : (z, θ) ∈ Set.Icc A₀ B₀ ×ˢ Set.Icc C₀ D₀ := hbox (hmem_of z θ h)
    rw [Set.mem_prod, Set.mem_Icc] at h1
    linarith [h1.2.2]

end Work.FTS.Apriori.Limit
end
end
-- ===== merged: Submission.Work.FTS.Apriori.Limit.TestQClosure =====
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

theorem isOpen_Qd : IsOpen Qd := isOpen_Ioi.prod isOpen_Ioo

/-! ## Supports of the partial derivatives -/

/-- The support of the partial `z`-derivative is contained in the closed support of the
function. -/
theorem isClosed_slice_tsupport (ψ : ℝ → ℝ → ℝ) (θ : ℝ) :
    IsClosed {z : ℝ | (z, θ) ∈ tsupport (Function.uncurry ψ)} :=
  (isClosed_tsupport (Function.uncurry ψ)).preimage (continuous_id.prodMk continuous_const)

theorem isClosed_slice_tsupport' (ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    IsClosed {θ : ℝ | (z, θ) ∈ tsupport (Function.uncurry ψ)} :=
  (isClosed_tsupport (Function.uncurry ψ)).preimage (continuous_const.prodMk continuous_id)

theorem support_pz_subset_tsupport (ψ : ℝ → ℝ → ℝ) :
    Function.support (fun p : ℝ × ℝ => Work.Spaces.pz ψ p.1 p.2)
      ⊆ tsupport (Function.uncurry ψ) := by
  intro p hp
  have hp1 : p.1 ∈ tsupport (fun z : ℝ => deriv (fun z' => ψ z' p.2) z) :=
    subset_tsupport _ (by simpa [Function.mem_support, Work.Spaces.pz] using hp)
  have h1 : tsupport (fun z : ℝ => deriv (fun z' => ψ z' p.2) z)
      ⊆ tsupport (fun z : ℝ => ψ z p.2) := tsupport_deriv_subset
  have h2 : tsupport (fun z : ℝ => ψ z p.2)
      ⊆ {z : ℝ | (z, p.2) ∈ tsupport (Function.uncurry ψ)} := by
    refine closure_minimal ?_ (isClosed_slice_tsupport ψ p.2)
    intro z hz
    exact subset_tsupport (Function.uncurry ψ) (by simpa using hz)
  exact h2 (h1 hp1)

/-- The support of the partial `θ`-derivative is contained in the closed support of the
function. -/
theorem support_pth_subset_tsupport (ψ : ℝ → ℝ → ℝ) :
    Function.support (fun p : ℝ × ℝ => Work.Spaces.pth ψ p.1 p.2)
      ⊆ tsupport (Function.uncurry ψ) := by
  intro p hp
  have hp2 : p.2 ∈ tsupport (fun θ : ℝ => deriv (fun θ' => ψ p.1 θ') θ) :=
    subset_tsupport _ (by simpa [Function.mem_support, Work.Spaces.pth] using hp)
  have h1 : tsupport (fun θ : ℝ => deriv (fun θ' => ψ p.1 θ') θ)
      ⊆ tsupport (fun θ : ℝ => ψ p.1 θ) := tsupport_deriv_subset
  have h2 : tsupport (fun θ : ℝ => ψ p.1 θ)
      ⊆ {θ : ℝ | (p.1, θ) ∈ tsupport (Function.uncurry ψ)} := by
    refine closure_minimal ?_ (isClosed_slice_tsupport' ψ p.1)
    intro θ hθ
    exact subset_tsupport (Function.uncurry ψ) (by simpa using hθ)
  exact h2 (h1 hp2)

/-! ## Supports of the adjoints -/

theorem support_adjZ_subset (ψ : ℝ → ℝ → ℝ) :
    Function.support (Function.uncurry (adjZ ψ)) ⊆ tsupport (Function.uncurry ψ) := by
  have hneg : Function.support (fun p : ℝ × ℝ =>
      -(Function.uncurry (Work.Spaces.pz (fun z θ => z * ψ z θ)) p))
      = Function.support (fun p : ℝ × ℝ =>
          Function.uncurry (Work.Spaces.pz (fun z θ => z * ψ z θ)) p) := by
    ext p
    simp only [Function.mem_support, neg_ne_zero]
  have hG : Function.uncurry (adjZ ψ)
      = fun p : ℝ × ℝ =>
          -(Function.uncurry (Work.Spaces.pz (fun z θ => z * ψ z θ)) p) := rfl
  rw [hG, hneg]
  refine (support_pz_subset_tsupport (fun z θ => z * ψ z θ)).trans ?_
  exact closure_mono (Function.support_mul_subset_right _ _)

theorem support_adjTh_subset (ψ : ℝ → ℝ → ℝ) :
    Function.support (Function.uncurry (adjTh ψ)) ⊆ tsupport (Function.uncurry ψ) := by
  have hneg : Function.support (fun p : ℝ × ℝ =>
      -(Function.uncurry (Work.Spaces.pth (fun z θ => Real.sin (2 * θ) * ψ z θ)) p))
      = Function.support (fun p : ℝ × ℝ =>
          Function.uncurry (Work.Spaces.pth (fun z θ => Real.sin (2 * θ) * ψ z θ)) p) := by
    ext p
    simp only [Function.mem_support, neg_ne_zero]
  have hG : Function.uncurry (adjTh ψ)
      = fun p : ℝ × ℝ =>
          -(Function.uncurry (Work.Spaces.pth (fun z θ => Real.sin (2 * θ) * ψ z θ)) p) := rfl
  rw [hG, hneg]
  refine (support_pth_subset_tsupport (fun z θ => Real.sin (2 * θ) * ψ z θ)).trans ?_
  exact closure_mono (Function.support_mul_subset_right _ _)

/-! ## The elementary adjoints preserve `TestQ` -/

theorem TestQ_adjZ {ψ : ℝ → ℝ → ℝ} (h : TestQ ψ) : TestQ (adjZ ψ) := by
  obtain ⟨hsm, hcomp, hsub⟩ := h
  have hG : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (fun z θ => z * ψ z θ)) Qd := by
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => p.1 * Function.uncurry ψ p) Qd :=
      (contDiffOn_fst (s := Qd)).mul hsm
    exact h1.congr (fun p _ => rfl)
  have hsupp : tsupport (Function.uncurry (adjZ ψ)) ⊆ tsupport (Function.uncurry ψ) :=
    closure_minimal (support_adjZ_subset ψ) (isClosed_tsupport (Function.uncurry ψ))
  exact ⟨(Work.FTS.LocData.contDiffOn_pz isOpen_Qd hG).neg,
    IsCompact.of_isClosed_subset hcomp (isClosed_tsupport (Function.uncurry (adjZ ψ))) hsupp,
    hsupp.trans hsub⟩

theorem TestQ_adjTh {ψ : ℝ → ℝ → ℝ} (h : TestQ ψ) : TestQ (adjTh ψ) := by
  obtain ⟨hsm, hcomp, hsub⟩ := h
  have hG : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (fun z θ => Real.sin (2 * θ) * ψ z θ)) Qd := by
    have hsin : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Qd :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin (2 * p.2) * Function.uncurry ψ p) Qd := hsin.mul hsm
    exact h1.congr (fun p _ => rfl)
  have hsupp : tsupport (Function.uncurry (adjTh ψ)) ⊆ tsupport (Function.uncurry ψ) :=
    closure_minimal (support_adjTh_subset ψ) (isClosed_tsupport (Function.uncurry ψ))
  exact ⟨(Work.FTS.LocData.contDiffOn_pth isOpen_Qd hG).neg,
    IsCompact.of_isClosed_subset hcomp (isClosed_tsupport (Function.uncurry (adjTh ψ))) hsupp,
    hsupp.trans hsub⟩

theorem TestQ_adjDzIter (j : ℕ) {ψ : ℝ → ℝ → ℝ} (h : TestQ ψ) :
    TestQ (adjDzIter j ψ) := by
  induction j generalizing ψ with
  | zero => exact h
  | succ j ih => exact ih (TestQ_adjZ h)

theorem TestQ_adjDthIter (i : ℕ) {ψ : ℝ → ℝ → ℝ} (h : TestQ ψ) :
    TestQ (adjDthIter i ψ) := by
  induction i generalizing ψ with
  | zero => exact h
  | succ i ih => exact ih (TestQ_adjTh h)

/-- `TestQ` is closed under multiplication by functions that are `C^∞` on the open quadrant,
and under the adjoints of the slot operators. -/
theorem TestQ_mul_adjMixed {ψ : ℝ → ℝ → ℝ} (hψ : TestQ ψ) :
    (∀ (g : ℝ → ℝ → ℝ),
        ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) Qd →
        TestQ (fun z θ => g z θ * ψ z θ)) ∧
      (∀ j i : ℕ, TestQ (adjMixed (j, i) ψ)) := by
  constructor
  · intro g hg
    have hsupp : Function.support (Function.uncurry (fun z θ => g z θ * ψ z θ))
        ⊆ tsupport (Function.uncurry ψ) :=
      (Function.support_mul_subset_right _ _).trans (subset_tsupport _)
    refine ⟨hg.mul hψ.1, ?_, ?_⟩
    · exact IsCompact.of_isClosed_subset hψ.2.1
        (isClosed_tsupport (Function.uncurry (fun z θ => g z θ * ψ z θ)))
        (closure_minimal hsupp (isClosed_tsupport (Function.uncurry ψ)))
    · exact (closure_minimal hsupp (isClosed_tsupport (Function.uncurry ψ))).trans hψ.2.2
  · intro j i
    exact TestQ_adjDthIter i (TestQ_adjDzIter j hψ)

end Work.FTS.Apriori.Limit
end
end
-- ===== merged: Submission.Work.FTS.Apriori.Limit.lintegral_HkIntegrand_le_iSup_HksqCut =====
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

/-! ## Elementary helpers -/





/-! ## Fatou's lemma for an exhausting family of cut-offs -/


/-! ## The target -/


end Work.FTS.Apriori.Limit
end
end
-- ===== merged: Submission.Work.FTS.Apriori.Limit.tendsto_integral_mul_of_tendstoLocUnif =====
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

/-- A `SmoothQuad` function (genuine `C^∞` on `(-1,∞) × (0,π/2)`) is continuous on the open
quadrant `Qd = (0,∞) × (0,π/2)` of the limit chapter. -/
theorem continuousOn_uncurry_of_smoothQuad {F : ℝ → ℝ → ℝ} (hF : SmoothQuad F) :
    ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) Qd := by
  refine hF.continuousOn.mono ?_
  intro p hp
  simp only [Qd, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
  exact ⟨by linarith [hp.1], hp.2.1, hp.2.2⟩



end Work.FTS.Apriori.Limit
end
end
-- ===== merged: Submission.Work.FTS.Apriori.Profile.SliceMass =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Apriori.Profile

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Work.Spaces



/-- `w` is measurable. -/
theorem measurable_w : Measurable w := by
  have hnum : Measurable (fun z : ℝ => (1 + z) ^ 2) := by
    have h : Measurable (fun z : ℝ => (1 + z) * (1 + z)) :=
      (measurable_const.add measurable_id).mul (measurable_const.add measurable_id)
    simpa [pow_two] using h
  have hden : Measurable (fun z : ℝ => z ^ 2) := by
    have h : Measurable (fun z : ℝ => z * z) := measurable_id.mul measurable_id
    simpa [pow_two] using h
  exact hnum.div hden

/-- `w z ≥ 1` for `z > 0`. -/
theorem one_le_w {z : ℝ} (hz : 0 < z) : 1 ≤ w z := by
  rw [w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
  nlinarith





end Work.FTS.Apriori.Profile
end
end
-- ===== merged: Submission.Work.FTS.ClassC.HkIntegrand_seven_le_of_bounds_Ioo =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC


end Work.FTS.ClassC
end
-- ===== merged: Submission.Work.FTS.ClassC.RopGen.Trace.ZmollAux.hxycSliceAESM =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC.RopGen.Trace.ZmollAux

open MeasureTheory Set Filter
open scoped Real Topology

set_option linter.deprecated false

/-! ## The three branches of the doubly-odd extension, as functions on the plane -/

/-- The left branch `k (θ-s) · (-G (exp t, -s))` of the slice integrand, as a function of
`p = (t, s)`. -/
private noncomputable def Sl1 (G : ℝ → ℝ → ℝ) (k : ℝ → ℝ) (θ : ℝ) : ℝ × ℝ → ℝ :=
  fun p => k (θ - p.2) * (-(Function.uncurry G (Real.exp p.1, -p.2)))

/-- The middle branch `k (θ-s) · G (exp t, s)`. -/
private noncomputable def Sl2 (G : ℝ → ℝ → ℝ) (k : ℝ → ℝ) (θ : ℝ) : ℝ × ℝ → ℝ :=
  fun p => k (θ - p.2) * Function.uncurry G (Real.exp p.1, p.2)

/-- The right branch `k (θ-s) · (-G (exp t, π-s))`. -/
private noncomputable def Sl3 (G : ℝ → ℝ → ℝ) (k : ℝ → ℝ) (θ : ℝ) : ℝ × ℝ → ℝ :=
  fun p => k (θ - p.2) * (-(Function.uncurry G (Real.exp p.1, Real.pi - p.2)))

/-- The window on the left of the origin. -/
private def SlSet (θ ε : ℝ) : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ioo (θ - ε) 0

/-- The middle window `(0, π/2)`. -/
private def SmSet (_θ _ε : ℝ) : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)

/-- The window on the right of `π/2`. -/
private def SrSet (θ ε : ℝ) : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ioo (Real.pi / 2) (θ + ε)

/-- The three-piece representative of the slice integrand.  It agrees with
`(t,s) ↦ k (θ - s) * Qext G (exp t) s` except on the null set `ℝ × {0, π/2, θ-ε, θ+ε}`. -/
private noncomputable def SliceSum (G : ℝ → ℝ → ℝ) (k : ℝ → ℝ) (θ ε : ℝ) : ℝ × ℝ → ℝ :=
  fun p => (SlSet θ ε).indicator (Sl1 G k θ) p
    + (SmSet θ ε).indicator (Sl2 G k θ) p
    + (SrSet θ ε).indicator (Sl3 G k θ) p

private lemma SliceSum_apply (G : ℝ → ℝ → ℝ) (k : ℝ → ℝ) (θ ε t s : ℝ) :
    SliceSum G k θ ε (t, s)
      = (SlSet θ ε).indicator (Sl1 G k θ) (t, s)
        + (SmSet θ ε).indicator (Sl2 G k θ) (t, s)
        + (SrSet θ ε).indicator (Sl3 G k θ) (t, s) := rfl

private lemma Sl1_apply (G : ℝ → ℝ → ℝ) (k : ℝ → ℝ) (θ : ℝ) (t s : ℝ) :
    Sl1 G k θ (t, s) = k (θ - s) * (-(Function.uncurry G (Real.exp t, -s))) := rfl

private lemma Sl2_apply (G : ℝ → ℝ → ℝ) (k : ℝ → ℝ) (θ : ℝ) (t s : ℝ) :
    Sl2 G k θ (t, s) = k (θ - s) * Function.uncurry G (Real.exp t, s) := rfl

private lemma Sl3_apply (G : ℝ → ℝ → ℝ) (k : ℝ → ℝ) (θ : ℝ) (t s : ℝ) :
    Sl3 G k θ (t, s) = k (θ - s) * (-(Function.uncurry G (Real.exp t, Real.pi - s))) := rfl

/-! ## The three branches of `Qext`, in uncurried form -/

private lemma qext_lt_zero' (G : ℝ → ℝ → ℝ) (z s : ℝ) (hs : s < 0) :
    Work.FTS.EllSol.PkgK5.K5c.Qext G z s = -(Function.uncurry G (z, -s)) := by
  rw [Work.FTS.EllSol.PkgK5.K5c.Qext, if_neg (fun h => absurd h.1 (not_le.mpr hs)), if_pos hs]
  rfl

private lemma qext_mem' (G : ℝ → ℝ → ℝ) (z s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    Work.FTS.EllSol.PkgK5.K5c.Qext G z s = Function.uncurry G (z, s) := by
  rw [Work.FTS.EllSol.PkgK5.K5c.Qext_of_mem G z s hs]
  rfl

private lemma qext_pihalf_lt' (G : ℝ → ℝ → ℝ) (z s : ℝ) (hs : Real.pi / 2 < s) :
    Work.FTS.EllSol.PkgK5.K5c.Qext G z s = -(Function.uncurry G (z, Real.pi - s)) := by
  have h0s : (0 : ℝ) < s := by linarith [Real.pi_pos]
  rw [Work.FTS.EllSol.PkgK5.K5c.Qext, if_neg (fun h => (not_le.mpr hs) h.2),
    if_neg (not_lt.mpr h0s.le)]
  rfl

/-! ## The pointwise identification, off the four exceptional angles -/

private lemma slice_eq (G : ℝ → ℝ → ℝ) {k : ℝ → ℝ} {ε θ t s : ℝ}
    (hvan : ∀ x : ℝ, ε < |x| → k x = 0)
    (hs : s ∉ ({0, Real.pi / 2, θ - ε, θ + ε} : Set ℝ)) :
    SliceSum G k θ ε (t, s) = k (θ - s) * Work.FTS.EllSol.EllPkgAux.Hxyc G t s := by
  rw [SliceSum_apply, Work.FTS.EllSol.EllPkgAux.Hxyc]
  have hmL : (t, s) ∈ SlSet θ ε ↔ s ∈ Set.Ioo (θ - ε) 0 := by
    simp only [SlSet, Set.mem_prod, Set.mem_univ, true_and]
  have hmM : (t, s) ∈ SmSet θ ε ↔ s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    simp only [SmSet, Set.mem_prod, Set.mem_univ, true_and]
  have hmR : (t, s) ∈ SrSet θ ε ↔ s ∈ Set.Ioo (Real.pi / 2) (θ + ε) := by
    simp only [SrSet, Set.mem_prod, Set.mem_univ, true_and]
  have hneL : s ≠ θ - ε := fun h => hs (by rw [h]; simp)
  have hneR : s ≠ θ + ε := fun h => hs (by rw [h]; simp)
  by_cases h1 : s ∈ Set.Ioo (θ - ε) 0
  · -- left branch
    have h2 : s ∉ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun h => by linarith [h1.2, h.1]
    have h3 : s ∉ Set.Ioo (Real.pi / 2) (θ + ε) := fun h => by
      linarith [h1.2, h.1, Real.pi_pos]
    rw [Set.indicator_of_mem (hmL.mpr h1), Set.indicator_of_notMem (fun h => h2 (hmM.mp h)),
      Set.indicator_of_notMem (fun h => h3 (hmR.mp h)), Sl1_apply,
      qext_lt_zero' G (Real.exp t) s h1.2]
    ring
  · by_cases h2 : s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
    · -- middle branch
      have h3 : s ∉ Set.Ioo (Real.pi / 2) (θ + ε) := fun h => by linarith [h2.2, h.1]
      rw [Set.indicator_of_notMem (fun h => h1 (hmL.mp h)), Set.indicator_of_mem (hmM.mpr h2),
        Set.indicator_of_notMem (fun h => h3 (hmR.mp h)), Sl2_apply,
        qext_mem' G (Real.exp t) s ⟨h2.1.le, h2.2.le⟩]
      ring
    · by_cases h3 : s ∈ Set.Ioo (Real.pi / 2) (θ + ε)
      · -- right branch
        rw [Set.indicator_of_notMem (fun h => h1 (hmL.mp h)),
          Set.indicator_of_notMem (fun h => h2 (hmM.mp h)),
          Set.indicator_of_mem (hmR.mpr h3), Sl3_apply, qext_pihalf_lt' G (Real.exp t) s h3.1]
        ring
      · -- outside the window: `k (θ - s) = 0` and all three indicators vanish
        have hnot : ¬ (θ - ε < s ∧ s < θ + ε) := by
          rintro ⟨hlt, hgt⟩
          rcases lt_trichotomy s 0 with h | h | h
          · exact h1 ⟨hlt, h⟩
          · exact hs (by rw [h]; simp)
          · rcases lt_trichotomy s (Real.pi / 2) with h' | h' | h'
            · exact h2 ⟨h, h'⟩
            · exact hs (by rw [h']; simp)
            · exact h3 ⟨h', hgt⟩
        rw [not_and_or, not_lt, not_lt] at hnot
        have hk0 : k (θ - s) = 0 := by
          apply hvan
          rcases hnot with h | h
          · have hlt : s < θ - ε := lt_of_le_of_ne h hneL
            calc ε < θ - s := by linarith
              _ ≤ |θ - s| := le_abs_self _
          · have hlt : θ + ε < s := lt_of_le_of_ne h (Ne.symm hneR)
            calc ε < s - θ := by linarith
              _ ≤ |s - θ| := le_abs_self _
              _ = |θ - s| := abs_sub_comm _ _
        rw [Set.indicator_of_notMem (fun h => h1 (hmL.mp h)),
          Set.indicator_of_notMem (fun h => h2 (hmM.mp h)),
          Set.indicator_of_notMem (fun h => h3 (hmR.mp h)), hk0, zero_mul]
        ring

/-! ## Joint measurability of the three-piece representative -/

private lemma aesm_sliceSum (G : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen G)
    {k : ℝ → ℝ} (hk : Continuous k) {ε θ : ℝ}
    (ha : -(Real.pi / 2) < θ - ε) (hb : θ + ε < Real.pi) :
    AEStronglyMeasurable (SliceSum G k θ ε) (volume.prod volume) := by
  have hcont : ContinuousOn (Function.uncurry G) Work.FTS.EllipticEst.Q0 := hS.continuousOn
  have hK : ContinuousOn (fun p : ℝ × ℝ => k (θ - p.2)) (SlSet θ ε) :=
    (by fun_prop : Continuous fun p : ℝ × ℝ => k (θ - p.2)).continuousOn
  have hg1 : ContinuousOn (fun p : ℝ × ℝ => Function.uncurry G (Real.exp p.1, -p.2))
      (SlSet θ ε) := by
    refine ContinuousOn.comp hcont ?_ ?_
    · fun_prop
    · intro p hp
      simp only [SlSet, Set.mem_prod, Set.mem_univ, true_and, Set.mem_Ioo] at hp
      rw [Work.FTS.EllipticEst.Q0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
      exact ⟨Real.exp_pos p.1, by linarith [hp.2], by linarith [ha, hp.1]⟩
  have hc1 : ContinuousOn (Sl1 G k θ) (SlSet θ ε) := hK.mul hg1.neg
  have hg2 : ContinuousOn (fun p : ℝ × ℝ => Function.uncurry G (Real.exp p.1, p.2))
      (SmSet θ ε) := by
    refine ContinuousOn.comp hcont ?_ ?_
    · fun_prop
    · intro p hp
      simp only [SmSet, Set.mem_prod, Set.mem_univ, true_and, Set.mem_Ioo] at hp
      rw [Work.FTS.EllipticEst.Q0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
      exact ⟨Real.exp_pos p.1, hp.1, hp.2⟩
  have hK2 : ContinuousOn (fun p : ℝ × ℝ => k (θ - p.2)) (SmSet θ ε) :=
    (by fun_prop : Continuous fun p : ℝ × ℝ => k (θ - p.2)).continuousOn
  have hc2 : ContinuousOn (Sl2 G k θ) (SmSet θ ε) := hK2.mul hg2
  have hg3 : ContinuousOn (fun p : ℝ × ℝ => Function.uncurry G (Real.exp p.1, Real.pi - p.2))
      (SrSet θ ε) := by
    refine ContinuousOn.comp hcont ?_ ?_
    · fun_prop
    · intro p hp
      simp only [SrSet, Set.mem_prod, Set.mem_univ, true_and, Set.mem_Ioo] at hp
      rw [Work.FTS.EllipticEst.Q0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
      exact ⟨Real.exp_pos p.1, by linarith [hb, hp.2], by linarith [hp.1]⟩
  have hK3 : ContinuousOn (fun p : ℝ × ℝ => k (θ - p.2)) (SrSet θ ε) :=
    (by fun_prop : Continuous fun p : ℝ × ℝ => k (θ - p.2)).continuousOn
  have hc3 : ContinuousOn (Sl3 G k θ) (SrSet θ ε) := hK3.mul hg3.neg
  have hLm : MeasurableSet (SlSet θ ε) := by
    rw [SlSet]; exact MeasurableSet.univ.prod isOpen_Ioo.measurableSet
  have hMm : MeasurableSet (SmSet θ ε) := by
    rw [SmSet]; exact MeasurableSet.univ.prod isOpen_Ioo.measurableSet
  have hRm : MeasurableSet (SrSet θ ε) := by
    rw [SrSet]; exact MeasurableSet.univ.prod isOpen_Ioo.measurableSet
  have h1 : AEStronglyMeasurable ((SlSet θ ε).indicator (Sl1 G k θ)) (volume.prod volume) :=
    (aestronglyMeasurable_indicator_iff hLm).mpr (hc1.aestronglyMeasurable hLm)
  have h2 : AEStronglyMeasurable ((SmSet θ ε).indicator (Sl2 G k θ)) (volume.prod volume) :=
    (aestronglyMeasurable_indicator_iff hMm).mpr (hc2.aestronglyMeasurable hMm)
  have h3 : AEStronglyMeasurable ((SrSet θ ε).indicator (Sl3 G k θ)) (volume.prod volume) :=
    (aestronglyMeasurable_indicator_iff hRm).mpr (hc3.aestronglyMeasurable hRm)
  have h12 := h1.add h2
  exact h12.add h3

theorem hxycSliceAESM (G : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen G)
    {k : ℝ → ℝ} (hk : Continuous k) {ε θ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hvan : ∀ x : ℝ, ε < |x| → k x = 0)
    (hθ : θ ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4)) :
    MeasureTheory.AEStronglyMeasurable (fun t : ℝ => ∫ s : ℝ, k (θ - s) *
      Work.FTS.EllSol.EllPkgAux.Hxyc G t s) MeasureTheory.volume := by
  -- the window `(θ - ε, θ + ε)` lies in `(-π/2, π)`
  have ha : -(Real.pi / 2) < θ - ε := by linarith [hθ.1, hε1, Real.pi_gt_three]
  have hb : θ + ε < Real.pi := by linarith [hθ.2, hε1, Real.pi_gt_three]
  have hΨ : AEStronglyMeasurable (SliceSum G k θ ε) (volume.prod volume) :=
    aesm_sliceSum G hS hk ha hb
  have hInt : AEStronglyMeasurable (fun t : ℝ => ∫ s : ℝ, SliceSum G k θ ε (t, s)) volume :=
    hΨ.integral_prod_right'
  refine hInt.congr (Filter.Eventually.of_forall fun t => ?_)
  -- for every `t`, the two integrands agree a.e. in `s` (they can only differ on a finite set)
  have hae : (fun s : ℝ => SliceSum G k θ ε (t, s)) =ᵐ[volume]
      (fun s : ℝ => k (θ - s) * Work.FTS.EllSol.EllPkgAux.Hxyc G t s) := by
    filter_upwards [((by simp : ({0, Real.pi / 2, θ - ε, θ + ε} : Set ℝ).Countable).ae_notMem
      volume)] with s hs
    exact slice_eq G hvan hs
  exact MeasureTheory.integral_congr_ae hae

end Work.FTS.ClassC.RopGen.Trace.ZmollAux
end
-- ===== merged: Submission.Work.FTS.ClassC.RopGen.Trace.ZmollAux.hxycSliceLocIntHonest =====
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
set_option linter.unusedVariables false

open Work.FTS.EllSol.EllPkgAux

/-! ## The kernel slice against the globally measurable branch function -/

/-- **Branch agreement of the two integrands.**  For a kernel `k` supported in `(-ε, ε)` with
`ε ≤ 1/2`, a modulus `θ ∈ (-1/4, π/2 + 1/4)` and any `t'`, the integrands
`s ↦ k (θ - s) · Hxyc G t' s` and `s ↦ k (θ - s) · Hm G (t', s)` agree off the null set
`{0, π/2}`: whenever `k (θ - s) ≠ 0` the argument `θ - s` lies in `(-ε, ε)`, which forces every
argument at which `Kq G` is evaluated (namely `s`, `-s` for `s < 0` and `π - s` for
`s > π/2`) into the open quadrant, where `Kq G` is the datum and the branches of `Qext`
reproduce the three cases of `Hm G`. -/
theorem kernel_mul_Hxyc_eq_Hm (G : ℝ → ℝ → ℝ) {k : ℝ → ℝ} {ε θ : ℝ}
    (hε1 : ε ≤ 1 / 2) (hvan : ∀ x : ℝ, ε < |x| → k x = 0)
    (hθ : θ ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4)) (t' : ℝ) :
    (fun s : ℝ => k (θ - s) * Hxyc G t' s)
      =ᵐ[volume] (fun s : ℝ => k (θ - s) * Hm G (t', s)) := by
  have key : ∀ s : ℝ, s ≠ 0 → s ≠ Real.pi / 2 →
      k (θ - s) * Hxyc G t' s = k (θ - s) * Hm G (t', s) := by
    intro s hs0 hspi
    by_cases hk : k (θ - s) = 0
    · rw [hk, zero_mul, zero_mul]
    · have hwin : |θ - s| ≤ ε := by
        by_contra hlt
        exact hk (hvan _ (lt_of_not_ge hlt))
      have hb : -ε ≤ θ - s ∧ θ - s ≤ ε := abs_le.mp hwin
      have hpt : Hxyc G t' s = Hm G (t', s) := by
        rcases lt_trichotomy s 0 with hs | hs | hs
        · -- `s < 0`: the reflected argument `-s` is in `(0, π/2)`
          have hmem : 0 < -s ∧ -s < Real.pi / 2 :=
            ⟨by linarith, by linarith [hb.2, hε1, hθ.1, Real.pi_gt_three]⟩
          have hKq : Kq G (Real.exp t', -s) = G (Real.exp t') (-s) := by
            unfold Kq
            rw [if_pos ⟨Real.exp_pos t', hmem.1, hmem.2⟩]
          unfold Hxyc Hm
          rw [if_pos hs, Qext_of_neg G (Real.exp t') s hs, hKq]
        · exact absurd hs hs0
        · by_cases hsle : s ≤ Real.pi / 2
          · -- the middle branch: `0 < s < π/2`
            have hmem : 0 < s ∧ s < Real.pi / 2 := ⟨hs, lt_of_le_of_ne hsle hspi⟩
            have hKq : Kq G (Real.exp t', s) = G (Real.exp t') s := by
              unfold Kq
              rw [if_pos ⟨Real.exp_pos t', hmem.1, hmem.2⟩]
            unfold Hxyc Hm
            rw [if_neg (not_lt.mpr (le_of_lt hs)), if_pos hsle,
              Work.FTS.EllSol.PkgK5.K5c.Qext_of_mem G (Real.exp t') s ⟨le_of_lt hs, hsle⟩, hKq]
          · -- `s > π/2`: the reflected argument `π - s` is in `(0, π/2)`
            have hmem : 0 < Real.pi - s ∧ Real.pi - s < Real.pi / 2 :=
              ⟨by linarith [hb.1, hθ.2, hε1, Real.pi_gt_three], by linarith⟩
            have hKq : Kq G (Real.exp t', Real.pi - s) = G (Real.exp t') (Real.pi - s) := by
              unfold Kq
              rw [if_pos ⟨Real.exp_pos t', hmem.1, hmem.2⟩]
            unfold Hxyc Hm
            rw [if_neg (not_lt.mpr (le_of_lt hs)), if_neg hsle,
              Qext_of_pihalf_lt G (Real.exp t') s (not_le.mp hsle), hKq]
      rw [hpt]
  refine MeasureTheory.ae_iff.mpr ?_
  refine measure_mono_null ?_ (Set.Finite.measure_zero
    ((Set.finite_singleton (Real.pi / 2)).insert 0) volume)
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  by_contra hcon
  push_neg at hcon
  exact hs (key s hcon.1 hcon.2)

/-! ## A.e. strong measurability of the sliced integral -/

/-- **A.e. strong measurability of the sliced angular mollification.**  The `s`-integrand with the
doubly odd extension is replaced by the globally measurable branch function `Hm G`
(`measurable_Hm`), the parameter integral is measurable by Fubini
(`MeasureTheory.AEStronglyMeasurable.integral_prod_right'`), and the two parameter integrals are
identified pointwise through `kernel_mul_Hxyc_eq_Hm`. -/
theorem aesm_slice_kernel (G : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen G)
    {k : ℝ → ℝ} (hk : Continuous k) {ε θ : ℝ} (hε1 : ε ≤ 1 / 2)
    (hvan : ∀ x : ℝ, ε < |x| → k x = 0)
    (hθ : θ ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4)) :
    MeasureTheory.AEStronglyMeasurable (fun t : ℝ => ∫ s : ℝ, k (θ - s) *
      Work.FTS.EllSol.EllPkgAux.Hxyc G t s) MeasureTheory.volume := by
  have hjoint : Measurable (fun p : ℝ × ℝ => k (θ - p.2) * Hm G p) :=
    (hk.measurable.comp (continuous_const.sub continuous_snd).measurable).mul
      (measurable_Hm G hS)
  have h1 : MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => ∫ s : ℝ, k (θ - s) * Hm G (t, s))
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (ν := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      hjoint.aestronglyMeasurable
  refine h1.congr (Filter.Eventually.of_forall fun t => ?_)
  exact (integral_congr_ae (kernel_mul_Hxyc_eq_Hm G hε1 hvan hθ t)).symm

/-! ## The target -/

theorem hxycSliceLocIntHonest (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hdom : MeasureTheory.LocallyIntegrable (fun t : ℝ => ∫ s in Work.Spaces.Iθ,
      |Work.FTS.EllSol.EllPkgAux.Hxyc G t s|) MeasureTheory.volume)
    {k : ℝ → ℝ} (hk : Continuous k) {ε M θ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hM0 : 0 ≤ M) (hM : ∀ x : ℝ, |k x| ≤ M) (hvan : ∀ x : ℝ, ε < |x| → k x = 0)
    (hθ : θ ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4)) :
    MeasureTheory.LocallyIntegrable (fun t : ℝ => ∫ s : ℝ, k (θ - s) *
      Work.FTS.EllSol.EllPkgAux.Hxyc G t s) MeasureTheory.volume := by
  have hS : Work.FTS.EllipticEst.SmoothOpen G := hT.1
  -- ## Measurability of the sliced integral
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => ∫ s : ℝ, k (θ - s) * Work.FTS.EllSol.EllPkgAux.Hxyc G t s)
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    aesm_slice_kernel G hS hk hε1 hvan hθ
  -- ## The pointwise domination by the honest slice norm
  have hbound : ∀ t : ℝ, |∫ s : ℝ, k (θ - s) * Work.FTS.EllSol.EllPkgAux.Hxyc G t s|
      ≤ 3 * M * ∫ s in Work.Spaces.Iθ, |Work.FTS.EllSol.EllPkgAux.Hxyc G t s| := by
    intro t
    have h := kernelSliceBound G (Real.exp t)
      (Work.FTS.EllSol.EllPkgAux.MollDzAux.qext_continuousOn G hT (Real.exp_pos t))
      hk hε0 hε1 hM0 hM hvan hθ
    simpa only [Work.FTS.EllSol.EllPkgAux.Hxyc] using h
  -- ## Local integrability of the dominating function (a constant multiple of the slice norm)
  refine (hdom.smul (3 * M)).mono hmeas (Filter.Eventually.of_forall fun t => ?_)
  have hnn : (0 : ℝ) ≤ 3 * M * ∫ s in Work.Spaces.Iθ,
      |Work.FTS.EllSol.EllPkgAux.Hxyc G t s| :=
    mul_nonneg (by linarith [hM0]) (integral_nonneg (fun s => abs_nonneg _))
  change ‖∫ s : ℝ, k (θ - s) * Work.FTS.EllSol.EllPkgAux.Hxyc G t s‖
    ≤ ‖(3 * M) • (∫ s in Work.Spaces.Iθ, |Work.FTS.EllSol.EllPkgAux.Hxyc G t s|)‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul, abs_of_nonneg hnn]
  exact hbound t

end Work.FTS.ClassC.RopGen.Trace.ZmollAux
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Assembly.H1IP_core_Q =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `H1IP_core_Q`: the four algebraic clauses of the `ℋ¹` inner product on `RegQ α 1`

The inner product

  `H1IP α f g = 10·(D_zf,D_zg)_{w²/sin^η} + 10¹⁰·(f,g)_{w²/sin^η} + 10¹⁷·(f,g)_{w²}
                 + 10²¹·(D_θf,D_θg)_{w²/sin^γ}`

is a sum of four weight pairings `wip ρ A B = ∫_z ∫_θ A·B·ρ`.  The Bochner integral is
total, so `wip` is not additive for *arbitrary* profiles (the junk value `0` of a
non-integrable integrand destroys the identity — `Work.Coercivity.H1IP_add_fails`); but for
profiles of the class `RegQ α 1` (genuine `C^∞` on the open quadrant, `HkMem α 1`, and the
integration-by-parts boundary traces) every pairing integrand is *honest*, because it is
dominated by the (integrable) `ℋ¹`-integrand of the two arguments and is a.e. strongly
measurable (continuity on the open quadrant).  Hence:

* `H1IP` is additive and homogeneous in its first argument on `RegQ α 1` (the four
  `PairHonest` lemmas below, followed by `H1IP_add_Q`);
* `H1IP` is symmetric for **all** profiles (`H1IP_comm`: the integrands are literally equal
  pointwise, so no honesty is needed);
* the diagonal is nonnegative for **all** profiles (`H1IP_nonneg`).

This is the `RegQ` (interior, non-analytic) replacement of the analytic-class additivity
proved in `Work.Coercivity.H1IP_isHkIP`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Symmetry of `wip` and of `H1IP` -/

theorem wip_comm (ρ A B : ℝ → ℝ → ℝ) :
    Work.Coercivity.wip ρ A B = Work.Coercivity.wip ρ B A := by
  simp only [Work.Coercivity.wip]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  ring

theorem H1IP_comm (α : ℝ) (f g : ℝ → ℝ → ℝ) :
    Work.Coercivity.H1IP α f g = Work.Coercivity.H1IP α g f := by
  simp only [Work.Coercivity.H1IP, wip_comm]

/-! ## The open quadrant, and continuity of the blocks -/

/-- The open quadrant `(0,∞) × (0,π/2)`, definitionally `Work.Construction.Qd`. -/
abbrev Qo : Set (ℝ × ℝ) := Work.Construction.Qd

theorem Qo_subset_quadU : Qo ⊆ Work.Spaces.quadU :=
  Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0)) subset_rfl

theorem continuousOn_w_Qo : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Qo := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
    funext p; rfl
  rw [hfun]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt (Set.mem_Ioi.mp hp.1)))

theorem continuousOn_sinpow_Qo (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Qo := by
  have hsin : Continuous (fun p : ℝ × ℝ => Real.sin (2 * p.2)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_snd)
  refine hsin.continuousOn.rpow_const ?_
  intro p hp
  have h1 : 0 < p.2 := (Set.mem_Ioo.mp hp.2).1
  have h2 : p.2 < π / 2 := (Set.mem_Ioo.mp hp.2).2
  exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])))

theorem continuousOn_lamEta : ContinuousOn (Function.uncurry Work.Coercivity.lamEta) Qo := by
  have hfun : Function.uncurry Work.Coercivity.lamEta
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-Work.Spaces.eta) := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  exact (continuousOn_w_Qo.pow 2).mul (continuousOn_sinpow_Qo _)

theorem continuousOn_lamGam (α : ℝ) :
    ContinuousOn (Function.uncurry (Work.Coercivity.lamGam α)) Qo := by
  have hfun : Function.uncurry (Work.Coercivity.lamGam α)
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α)) := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  exact (continuousOn_w_Qo.pow 2).mul (continuousOn_sinpow_Qo _)

theorem continuousOn_lamW : ContinuousOn (Function.uncurry Work.Coercivity.lamW) Qo := by
  have hfun : Function.uncurry Work.Coercivity.lamW = fun p : ℝ × ℝ => Work.Spaces.w p.1 ^ 2 := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  exact continuousOn_w_Qo.pow 2

theorem continuousOn_smoothQuad {f : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad f) :
    ContinuousOn (Function.uncurry f) Qo :=
  h.continuousOn.mono Qo_subset_quadU

theorem continuousOn_Dz_smoothQuad {f : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad f) :
    ContinuousOn (Function.uncurry (Work.Spaces.Dz f)) Qo :=
  ((Work.FTS.LocData.contDiffOn_Dz Work.Spaces.isOpen_quadU h).continuousOn).mono Qo_subset_quadU

theorem continuousOn_Dth_smoothQuad {f : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad f) :
    ContinuousOn (Function.uncurry (Work.Spaces.Dth f)) Qo :=
  ((Work.FTS.LocData.contDiffOn_Dth Work.Spaces.isOpen_quadU h).continuousOn).mono Qo_subset_quadU

/-! ## Domination of the pairing integrands by the `ℋ¹`-integrand -/

/-- The elementary AM–GM bound `|a|·|b| ≤ (a² + b²)/2`. -/
theorem abs_mul_abs_le_half (a b : ℝ) : |a| * |b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h := two_mul_le_add_sq |a| |b|
  rw [sq_abs, sq_abs] at h
  linarith

/-- For `0 < t ≤ 1` and any `a`, dividing by `t` does not decrease the square. -/
theorem sq_le_div_sq {a t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) : a ^ 2 ≤ (a / t) ^ 2 := by
  have ht2 : 0 < t ^ 2 := pow_pos ht0 2
  have ht2le : t ^ 2 ≤ 1 := by nlinarith [ht0, ht1]
  rw [div_pow, le_div_iff₀ ht2]
  simpa using mul_le_mul_of_nonneg_left ht2le (sq_nonneg a)

/-- The `D_z⁰`-block `Xeta f = f·w/√(sin 2θ^η)` is dominated by the `ℋ¹`-integrand. -/
theorem sq_Xeta_le_HkIntegrand (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (Work.Coercivity.Xeta f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 1 f z θ := by
  have h := Work.Spaces.sq_le_HkIntegrand_z α 1 f z θ 0 (by norm_num)
  simpa only [Work.Coercivity.Xeta, Work.Coercivity.U0, Work.Spaces.DzIter_zero] using h

/-- The `D_z¹`-block `XetaDz f = D_zf·w/√(sin 2θ^η)` is dominated by the `ℋ¹`-integrand. -/
theorem sq_XetaDz_le_HkIntegrand (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (Work.Coercivity.XetaDz f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 1 f z θ := by
  have h := Work.Spaces.sq_le_HkIntegrand_z α 1 f z θ 1 (by norm_num)
  simpa only [Work.Coercivity.XetaDz, Work.Coercivity.U1, Work.Spaces.DzIter_succ,
    Work.Spaces.DzIter_zero] using h

/-- The `D_θ`-block `XgamDth α f = D_θf·W` is dominated by the `ℋ¹`-integrand. -/
theorem sq_XgamDth_le_HkIntegrand (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (Work.Coercivity.XgamDth α f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 1 f z θ := by
  have h := Work.Spaces.sq_le_HkIntegrand_mixed α 1 f z θ 1 0 (by norm_num) (by norm_num)
  simpa only [Work.Coercivity.XgamDth, Work.Coercivity.U2, Work.Spaces.mixed_zero_left,
    Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero] using h

/-- The plain `w²`-block `Xw f = f·w` is dominated by the `ℋ¹`-integrand **off the two
(null) endpoints** `θ = 0`, `θ = π/2`: there the `D_z⁰`-summand of the integrand is
`Xw f / √(sin 2θ^η)` and `0 < sin 2θ ≤ 1`. -/
theorem sq_Xw_le_HkIntegrand_ae (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Work.Coercivity.Xw f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 1 f z θ := by
  have hmeas : MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  rw [← hmeas]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have ht0 : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hs0 _
  have ht1 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 := by
    calc (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        ≤ (1 : ℝ) ^ (Work.Spaces.eta / 2) := Real.rpow_le_rpow (le_of_lt hs0) hs1
          (div_nonneg (le_of_lt Work.Spaces.eta_pos) (by norm_num))
      _ = 1 := by simp
  have hkey : (f z θ * Work.Spaces.w z) ^ 2
      ≤ ((f z θ * Work.Spaces.w z) / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
    sq_le_div_sq ht0 ht1
  have hterm : (Work.Coercivity.Xw f z θ) ^ 2
      ≤ (Work.Spaces.DzIter 0 f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    simp only [Work.Coercivity.Xw, Work.Spaces.DzIter_zero]
    rw [← mul_div_assoc]
    exact hkey
  exact le_trans hterm (Work.Spaces.sq_le_HkIntegrand_z α 1 f z θ 0 (by norm_num))

/-- Honesty of the "average" domination `(HkIntegrand α 1 a + HkIntegrand α 1 b)/2` used for
all four pairings: it is the arithmetic mean of two integrable functions. -/
theorem I2Mem_HkPairDom (α : ℝ) {a b : ℝ → ℝ → ℝ} (ha : Work.Spaces.HkMem α 1 a)
    (hb : Work.Spaces.HkMem α 1 b) :
    Work.Coercivity.I2Mem (fun z θ => (Work.Spaces.HkIntegrand α 1 a z θ
      + Work.Spaces.HkIntegrand α 1 b z θ) / 2) := by
  refine ⟨fun z hz => (ha.1 z hz |>.add (hb.1 z hz)).div_const 2, ?_⟩
  refine (ha.2.div_const 2 |>.add (hb.2.div_const 2)).congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
  simp only [Pi.add_apply]
  rw [MeasureTheory.integral_div, MeasureTheory.integral_add (ha.1 z hz) (hb.1 z hz)]
  ring

/-- **Domination criterion for honesty.**  If an integrand `F` is continuous on the open
quadrant, vanishes on the slice `z = 0`, and is dominated (a.e. in `θ`) by an honest
integrand `D`, then its iterated integral over the quadrant is honest. -/
theorem I2Mem_of_dominated {F D : ℝ → ℝ → ℝ}
    (hD : Work.Coercivity.I2Mem D)
    (hFc : ContinuousOn (Function.uncurry F) Qo)
    (hF0 : ∀ θ, F 0 θ = 0)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |F z θ| ≤ D z θ) :
    Work.Coercivity.I2Mem F := by
  have haesm : MeasureTheory.AEStronglyMeasurable (Function.uncurry F)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hFc
  refine ⟨fun z hz => ?_, ?_⟩
  · rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hpos
    · subst h0
      have hz0 : (fun θ : ℝ => F 0 θ) = fun _ : ℝ => (0 : ℝ) := by
        funext θ; exact hF0 θ
      rw [hz0]
      exact MeasureTheory.integrableOn_zero
    · exact MeasureTheory.Integrable.mono' (hD.1 z hz)
        (Work.Spaces.aesm_slice_of_continuousOn_Qd _ hFc hpos)
        (by filter_upwards [hle z hz] with θ hθ; rwa [Real.norm_eq_abs])
  · refine MeasureTheory.Integrable.mono' hD.2 haesm.integral_prod_right' ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [Real.norm_eq_abs]
    calc |∫ θ in Work.Spaces.Iθ, F z θ| ≤ ∫ θ in Work.Spaces.Iθ, |F z θ| := by
          simpa only [Real.norm_eq_abs] using
            (MeasureTheory.norm_integral_le_integral_norm (fun θ : ℝ => F z θ)
              (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ))
      _ ≤ ∫ θ in Work.Spaces.Iθ, D z θ :=
          MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall
            (fun θ => abs_nonneg _)) (hD.1 z hz) (hle z hz)

/-! ## The four honest pairings of `H1IP` -/

theorem PairHonest_eta_Q (α : ℝ) {a b : ℝ → ℝ → ℝ}
    (hqa : Work.FTS.LocData.SmoothQuad a) (hqb : Work.FTS.LocData.SmoothQuad b)
    (hma : Work.Spaces.HkMem α 1 a) (hmb : Work.Spaces.HkMem α 1 b) :
    Work.Coercivity.PairHonest Work.Coercivity.lamEta a b := by
  refine I2Mem_of_dominated (I2Mem_HkPairDom α hma hmb) ?_ ?_ ?_
  · have hfun : Function.uncurry (fun z θ => a z θ * b z θ * Work.Coercivity.lamEta z θ)
        = fun p : ℝ × ℝ => Function.uncurry a p * Function.uncurry b p
            * Function.uncurry Work.Coercivity.lamEta p := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [hfun]
    exact ((continuousOn_smoothQuad hqa).mul (continuousOn_smoothQuad hqb)).mul continuousOn_lamEta
  · intro θ
    simp [Work.Coercivity.lamEta, Work.Spaces.w]
  · intro z _
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [← Work.Coercivity.Xeta_mul_eq a b z θ hθ]
    calc |Work.Coercivity.Xeta a z θ * Work.Coercivity.Xeta b z θ|
        = |Work.Coercivity.Xeta a z θ| * |Work.Coercivity.Xeta b z θ| := abs_mul _ _
      _ ≤ ((Work.Coercivity.Xeta a z θ) ^ 2 + (Work.Coercivity.Xeta b z θ) ^ 2) / 2 :=
          abs_mul_abs_le_half _ _
      _ ≤ (Work.Spaces.HkIntegrand α 1 a z θ + Work.Spaces.HkIntegrand α 1 b z θ) / 2 := by
          have h1 := sq_Xeta_le_HkIntegrand α a z θ
          have h2 := sq_Xeta_le_HkIntegrand α b z θ
          linarith

theorem PairHonest_etaDz_Q (α : ℝ) {a b : ℝ → ℝ → ℝ}
    (hqa : Work.FTS.LocData.SmoothQuad a) (hqb : Work.FTS.LocData.SmoothQuad b)
    (hma : Work.Spaces.HkMem α 1 a) (hmb : Work.Spaces.HkMem α 1 b) :
    Work.Coercivity.PairHonest Work.Coercivity.lamEta
      (Work.Spaces.Dz a) (Work.Spaces.Dz b) := by
  refine I2Mem_of_dominated (I2Mem_HkPairDom α hma hmb) ?_ ?_ ?_
  · have hfun : Function.uncurry (fun z θ =>
        Work.Spaces.Dz a z θ * Work.Spaces.Dz b z θ * Work.Coercivity.lamEta z θ)
        = fun p : ℝ × ℝ => Function.uncurry (Work.Spaces.Dz a) p
            * Function.uncurry (Work.Spaces.Dz b) p
            * Function.uncurry Work.Coercivity.lamEta p := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [hfun]
    exact ((continuousOn_Dz_smoothQuad hqa).mul (continuousOn_Dz_smoothQuad hqb)).mul
      continuousOn_lamEta
  · intro θ
    simp [Work.Coercivity.lamEta, Work.Spaces.w]
  · intro z _
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [← Work.Coercivity.XetaDz_mul_eq a b z θ hθ]
    calc |Work.Coercivity.XetaDz a z θ * Work.Coercivity.XetaDz b z θ|
        = |Work.Coercivity.XetaDz a z θ| * |Work.Coercivity.XetaDz b z θ| := abs_mul _ _
      _ ≤ ((Work.Coercivity.XetaDz a z θ) ^ 2 + (Work.Coercivity.XetaDz b z θ) ^ 2) / 2 :=
          abs_mul_abs_le_half _ _
      _ ≤ (Work.Spaces.HkIntegrand α 1 a z θ + Work.Spaces.HkIntegrand α 1 b z θ) / 2 := by
          have h1 := sq_XetaDz_le_HkIntegrand α a z θ
          have h2 := sq_XetaDz_le_HkIntegrand α b z θ
          linarith

theorem PairHonest_gam_Q (α : ℝ) {a b : ℝ → ℝ → ℝ}
    (hqa : Work.FTS.LocData.SmoothQuad a) (hqb : Work.FTS.LocData.SmoothQuad b)
    (hma : Work.Spaces.HkMem α 1 a) (hmb : Work.Spaces.HkMem α 1 b) :
    Work.Coercivity.PairHonest (Work.Coercivity.lamGam α)
      (Work.Spaces.Dth a) (Work.Spaces.Dth b) := by
  refine I2Mem_of_dominated (I2Mem_HkPairDom α hma hmb) ?_ ?_ ?_
  · have hfun : Function.uncurry (fun z θ =>
        Work.Spaces.Dth a z θ * Work.Spaces.Dth b z θ * Work.Coercivity.lamGam α z θ)
        = fun p : ℝ × ℝ => Function.uncurry (Work.Spaces.Dth a) p
            * Function.uncurry (Work.Spaces.Dth b) p
            * Function.uncurry (Work.Coercivity.lamGam α) p := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [hfun]
    exact ((continuousOn_Dth_smoothQuad hqa).mul (continuousOn_Dth_smoothQuad hqb)).mul
      (continuousOn_lamGam α)
  · intro θ
    simp [Work.Coercivity.lamGam, Work.Spaces.w]
  · intro z _
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [← Work.Coercivity.XgamDth_mul_eq α a b z θ hθ]
    calc |Work.Coercivity.XgamDth α a z θ * Work.Coercivity.XgamDth α b z θ|
        = |Work.Coercivity.XgamDth α a z θ| * |Work.Coercivity.XgamDth α b z θ| := abs_mul _ _
      _ ≤ ((Work.Coercivity.XgamDth α a z θ) ^ 2
            + (Work.Coercivity.XgamDth α b z θ) ^ 2) / 2 := abs_mul_abs_le_half _ _
      _ ≤ (Work.Spaces.HkIntegrand α 1 a z θ + Work.Spaces.HkIntegrand α 1 b z θ) / 2 := by
          have h1 := sq_XgamDth_le_HkIntegrand α a z θ
          have h2 := sq_XgamDth_le_HkIntegrand α b z θ
          linarith

theorem PairHonest_w_Q (α : ℝ) {a b : ℝ → ℝ → ℝ}
    (hqa : Work.FTS.LocData.SmoothQuad a) (hqb : Work.FTS.LocData.SmoothQuad b)
    (hma : Work.Spaces.HkMem α 1 a) (hmb : Work.Spaces.HkMem α 1 b) :
    Work.Coercivity.PairHonest Work.Coercivity.lamW a b := by
  refine I2Mem_of_dominated (I2Mem_HkPairDom α hma hmb) ?_ ?_ ?_
  · have hfun : Function.uncurry (fun z θ => a z θ * b z θ * Work.Coercivity.lamW z θ)
        = fun p : ℝ × ℝ => Function.uncurry a p * Function.uncurry b p
            * Function.uncurry Work.Coercivity.lamW p := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [hfun]
    exact ((continuousOn_smoothQuad hqa).mul (continuousOn_smoothQuad hqb)).mul continuousOn_lamW
  · intro θ
    simp [Work.Coercivity.lamW, Work.Spaces.w]
  · intro z _
    filter_upwards [sq_Xw_le_HkIntegrand_ae α a z, sq_Xw_le_HkIntegrand_ae α b z]
      with θ h1 h2
    have hXw : Work.Coercivity.Xw a z θ * Work.Coercivity.Xw b z θ
        = a z θ * b z θ * Work.Coercivity.lamW z θ := by
      simp only [Work.Coercivity.Xw, Work.Coercivity.lamW]; ring
    rw [← hXw]
    calc |Work.Coercivity.Xw a z θ * Work.Coercivity.Xw b z θ|
        = |Work.Coercivity.Xw a z θ| * |Work.Coercivity.Xw b z θ| := abs_mul _ _
      _ ≤ ((Work.Coercivity.Xw a z θ) ^ 2 + (Work.Coercivity.Xw b z θ) ^ 2) / 2 :=
          abs_mul_abs_le_half _ _
      _ ≤ (Work.Spaces.HkIntegrand α 1 a z θ + Work.Spaces.HkIntegrand α 1 b z θ) / 2 := by
          linarith

/-! ## Derivative linearity on the open quadrant -/

theorem Dz_add_Qo {a₁ a₂ : ℝ → ℝ → ℝ} (h1 : Work.FTS.LocData.SmoothQuad a₁)
    (h2 : Work.FTS.LocData.SmoothQuad a₂) :
    ∀ z θ, (z, θ) ∈ Qo →
      Work.Spaces.Dz (a₁ + a₂) z θ = Work.Spaces.Dz a₁ z θ + Work.Spaces.Dz a₂ z θ := by
  intro z θ hzθ
  have hz : z ∈ Set.Ioi (-1 : ℝ) := Set.mem_Ioi.mpr (by linarith [Set.mem_Ioi.mp hzθ.1])
  have hθ : θ ∈ Set.Ioo 0 (π / 2) := hzθ.2
  have hd : ∀ a : ℝ → ℝ → ℝ, Work.FTS.LocData.SmoothQuad a →
      DifferentiableAt ℝ (fun z' => a z' θ) z := fun a ha =>
    (Work.FTS.LocData.SmoothQuad.differentiableAt_slice_mixed ha 0 0 hz hθ)
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [show (fun z' => (a₁ + a₂) z' θ) = (fun z' => a₁ z' θ) + (fun z' => a₂ z' θ) from rfl,
    deriv_add (hd a₁ h1) (hd a₂ h2)]
  ring

theorem Dth_add_Qo {a₁ a₂ : ℝ → ℝ → ℝ} (h1 : Work.FTS.LocData.SmoothQuad a₁)
    (h2 : Work.FTS.LocData.SmoothQuad a₂) :
    ∀ z θ, (z, θ) ∈ Qo →
      Work.Spaces.Dth (a₁ + a₂) z θ = Work.Spaces.Dth a₁ z θ + Work.Spaces.Dth a₂ z θ := by
  intro z θ hzθ
  have hz : z ∈ Set.Ioi (-1 : ℝ) := Set.mem_Ioi.mpr (by linarith [Set.mem_Ioi.mp hzθ.1])
  have hθ : θ ∈ Set.Ioo 0 (π / 2) := hzθ.2
  have hd : ∀ a : ℝ → ℝ → ℝ, Work.FTS.LocData.SmoothQuad a →
      DifferentiableAt ℝ (fun θ' => a z θ') θ := fun a ha =>
    (Work.FTS.LocData.SmoothQuad.differentiableAt_slice_DthIter ha 0 hz hθ)
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [show (fun θ' => (a₁ + a₂) z θ') = (fun θ' => a₁ z θ') + (fun θ' => a₂ z θ') from rfl,
    deriv_add (hd a₁ h1) (hd a₂ h2)]
  ring

/-! ## Additivity of `H1IP` on `RegQ α 1` -/

theorem H1IP_add_Q (α : ℝ) {a₁ a₂ b : ℝ → ℝ → ℝ}
    (h1 : Work.FTS.Nonlin.RegQ α 1 a₁) (h2 : Work.FTS.Nonlin.RegQ α 1 a₂)
    (hb : Work.FTS.Nonlin.RegQ α 1 b) :
    Work.Coercivity.H1IP α (a₁ + a₂) b
      = Work.Coercivity.H1IP α a₁ b + Work.Coercivity.H1IP α a₂ b := by
  simp only [Work.FTS.Nonlin.RegQ] at h1 h2 hb
  obtain ⟨hq1, hm1, _⟩ := h1
  obtain ⟨hq2, hm2, _⟩ := h2
  obtain ⟨hqb, hmb, _⟩ := hb
  have hA : Work.Coercivity.wip Work.Coercivity.lamEta (Work.Spaces.Dz (a₁ + a₂))
        (Work.Spaces.Dz b)
      = Work.Coercivity.wip Work.Coercivity.lamEta (Work.Spaces.Dz a₁) (Work.Spaces.Dz b)
        + Work.Coercivity.wip Work.Coercivity.lamEta (Work.Spaces.Dz a₂) (Work.Spaces.Dz b) := by
    rw [Work.FTS.CoercivityFix.StepAssembly.wip_congr_Qd (A := Work.Spaces.Dz (a₁ + a₂))
      (A' := Work.Spaces.Dz a₁ + Work.Spaces.Dz a₂)
      (fun z θ hzθ => Dz_add_Qo hq1 hq2 z θ hzθ)]
    exact Work.Coercivity.wip_add_of_PairHonest Work.Coercivity.lamEta (Work.Spaces.Dz a₁)
      (Work.Spaces.Dz a₂) (Work.Spaces.Dz b)
      (PairHonest_etaDz_Q α hq1 hqb hm1 hmb) (PairHonest_etaDz_Q α hq2 hqb hm2 hmb)
  have hB : Work.Coercivity.wip Work.Coercivity.lamEta (a₁ + a₂) b
      = Work.Coercivity.wip Work.Coercivity.lamEta a₁ b
        + Work.Coercivity.wip Work.Coercivity.lamEta a₂ b :=
    Work.Coercivity.wip_add_of_PairHonest Work.Coercivity.lamEta a₁ a₂ b
      (PairHonest_eta_Q α hq1 hqb hm1 hmb) (PairHonest_eta_Q α hq2 hqb hm2 hmb)
  have hC : Work.Coercivity.wip Work.Coercivity.lamW (a₁ + a₂) b
      = Work.Coercivity.wip Work.Coercivity.lamW a₁ b
        + Work.Coercivity.wip Work.Coercivity.lamW a₂ b :=
    Work.Coercivity.wip_add_of_PairHonest Work.Coercivity.lamW a₁ a₂ b
      (PairHonest_w_Q α hq1 hqb hm1 hmb) (PairHonest_w_Q α hq2 hqb hm2 hmb)
  have hD : Work.Coercivity.wip (Work.Coercivity.lamGam α) (Work.Spaces.Dth (a₁ + a₂))
        (Work.Spaces.Dth b)
      = Work.Coercivity.wip (Work.Coercivity.lamGam α) (Work.Spaces.Dth a₁)
          (Work.Spaces.Dth b)
        + Work.Coercivity.wip (Work.Coercivity.lamGam α) (Work.Spaces.Dth a₂)
          (Work.Spaces.Dth b) := by
    rw [Work.FTS.CoercivityFix.StepAssembly.wip_congr_Qd (A := Work.Spaces.Dth (a₁ + a₂))
      (A' := Work.Spaces.Dth a₁ + Work.Spaces.Dth a₂)
      (fun z θ hzθ => Dth_add_Qo hq1 hq2 z θ hzθ)]
    exact Work.Coercivity.wip_add_of_PairHonest (Work.Coercivity.lamGam α) (Work.Spaces.Dth a₁)
      (Work.Spaces.Dth a₂) (Work.Spaces.Dth b)
      (PairHonest_gam_Q α hq1 hqb hm1 hmb) (PairHonest_gam_Q α hq2 hqb hm2 hmb)
  have hEtaW : (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      = Work.Coercivity.lamEta := rfl
  have hGamW : (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = Work.Coercivity.lamGam α := rfl
  have hWtW : (fun z _ => Work.Spaces.w z ^ 2) = Work.Coercivity.lamW := rfl
  simp only [Work.Coercivity.H1IP]
  rw [hEtaW, hGamW, hWtW, hA, hB, hC, hD]
  ring

theorem H1IP_core_Q (α : ℝ) (hα : 0 < α) :
    (∀ f₁ f₂ g : ℝ → ℝ → ℝ, Work.FTS.Nonlin.RegQ α 1 f₁ → Work.FTS.Nonlin.RegQ α 1 f₂ →
      Work.FTS.Nonlin.RegQ α 1 g →
      Work.Coercivity.H1IP α (f₁ + f₂) g
        = Work.Coercivity.H1IP α f₁ g + Work.Coercivity.H1IP α f₂ g) ∧
    (∀ (c : ℝ) (f g : ℝ → ℝ → ℝ), Work.FTS.Nonlin.RegQ α 1 f → Work.FTS.Nonlin.RegQ α 1 g →
      Work.Coercivity.H1IP α (fun z θ => c * f z θ) g
        = c * Work.Coercivity.H1IP α f g) ∧
    (∀ f g : ℝ → ℝ → ℝ, Work.Coercivity.H1IP α f g = Work.Coercivity.H1IP α g f) ∧
    (∀ f : ℝ → ℝ → ℝ, 0 ≤ Work.Coercivity.H1IP α f f) :=
  ⟨fun f₁ f₂ g h₁ h₂ hg => H1IP_add_Q α h₁ h₂ hg,
   fun c f g _ _ => Work.Coercivity.H1IP_homog α c f g,
   fun f g => H1IP_comm α f g,
   fun f => Work.Coercivity.H1IP_nonneg α f⟩

end Work.FTS.CoercivityFix.Assembly
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Assembly.exists_coerAdm_pos =====
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

set_option autoImplicit false

/-! ## The angular jet bound, for every `α > 0`

The delivered `Work.FTS.LocData.DthIter_Gam_abs_le` and `Work.FTS.LocDataExt.DthIter_Gam_abs_le5`
carry the hypothesis `α ≤ 1` (they bound the polynomials `Qp j α` on `[-1,1]` by numerical
constants valid only there).  The non-vacuity statement is for **every** `α > 0`, so we redo the
bound with an `α`-dependent constant: `Tfun j α` is continuous on the compact `Iθ`, hence
bounded, and `Work.Spaces.dthU_iter_Gam_abs_bound` (which has no restriction on `α`) turns a
bound on `Tfun (i-1) α` into `|D_θ^i Γ| ≤ C·Γ`. -/



/-! ## The radial weighted bound -/


/-! ## Integrability of the angular majorant, for every `α > 0` -/



/-! ## The witness is `L₁₂`-orthogonal -/


/-! ## The boundary traces of the witness -/


/-! ## The separable `ℋ^k`-majorant of the witness, and its `ℋ^k`-membership -/




/-! ## Strict positivity of the `ℋ⁴`-functional of the witness -/


/-! ## The witness lies in `CoerAdm` -/



end Work.FTS.CoercivityFix.Assembly
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1.Assembly =====
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

/-- The four coercivity estimates of `Lhat` imply the level-1 coercivity, together with the
identification of the `ℋ¹`-energy and the domination of the plain `D_θ`-energy by the
`γ`-weighted one. -/
theorem assembly (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {f : Fn}
    (hHk : Work.Spaces.HkSq α 1 f
      = En Work.Spaces.eta (Work.Spaces.Dz f) + En Work.Spaces.eta f
        + En (Work.Spaces.gam α) (Work.Spaces.Dth f))
    (hW : Work.Coercivity.EDthW f ≤ En (Work.Spaces.gam α) (Work.Spaces.Dth f))
    (hA : (47 / 100) * En Work.Spaces.eta (Work.Spaces.Dz f)
      - (En Work.Spaces.eta f + 4 * En (Work.Spaces.gam α) (Work.Spaces.Dth f)
          + (1 / 8) * En Work.Spaces.eta (Work.Spaces.Dz f))
      ≤ Work.Coercivity.wip (Rho Work.Spaces.eta) (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f))
          (Work.Spaces.Dz f))
    (hB : (47 / 100) * En Work.Spaces.eta f
      ≤ Work.Coercivity.wip (Rho Work.Spaces.eta) (Work.FTS.CoercivityFix.Lhat f) f)
    (hC : (1 / 8) * EnOne f - 6 * Work.Coercivity.EDthW f
      ≤ Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) (Work.FTS.CoercivityFix.Lhat f) f)
    (hD : (17 / 40) * En (Work.Spaces.gam α) (Work.Spaces.Dth f)
      ≤ Work.Coercivity.wip (Rho (Work.Spaces.gam α))
          (Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dth f)) :
    2 * Work.Spaces.HkSq α 1 f
      ≤ Work.Coercivity.H1IP α (Work.FTS.CoercivityFix.Lhat f) f := by
  -- ## the `H1IP` is the sum of the four pairings
  have hH1 : Work.Coercivity.H1IP α (Work.FTS.CoercivityFix.Lhat f) f
      = 10 * Work.Coercivity.wip (Rho Work.Spaces.eta)
            (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dz f)
        + (10 : ℝ) ^ 10 * Work.Coercivity.wip (Rho Work.Spaces.eta)
            (Work.FTS.CoercivityFix.Lhat f) f
        + (10 : ℝ) ^ 17 * Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
            (Work.FTS.CoercivityFix.Lhat f) f
        + (10 : ℝ) ^ 21 * Work.Coercivity.wip (Rho (Work.Spaces.gam α))
            (Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dth f) := by
    rw [Work.Coercivity.H1IP]
    rfl
  rw [hH1, hHk]
  -- ## the three energies as squares of their square roots
  set X := Real.sqrt (En Work.Spaces.eta (Work.Spaces.Dz f)) with hXdef
  set Y := Real.sqrt (En Work.Spaces.eta f) with hYdef
  set Z := Real.sqrt (En (Work.Spaces.gam α) (Work.Spaces.Dth f)) with hZdef
  have hXn : 0 ≤ En Work.Spaces.eta (Work.Spaces.Dz f) := En_nonneg _ _
  have hYn : 0 ≤ En Work.Spaces.eta f := En_nonneg _ _
  have hZn : 0 ≤ En (Work.Spaces.gam α) (Work.Spaces.Dth f) := En_nonneg _ _
  have hX2 : X ^ 2 = En Work.Spaces.eta (Work.Spaces.Dz f) := Real.sq_sqrt hXn
  have hY2 : Y ^ 2 = En Work.Spaces.eta f := Real.sq_sqrt hYn
  have hZ2 : Z ^ 2 = En (Work.Spaces.gam α) (Work.Spaces.Dth f) := Real.sq_sqrt hZn
  have hXn' : 0 ≤ X := Real.sqrt_nonneg _
  have hYn' : 0 ≤ Y := Real.sqrt_nonneg _
  -- ## the scaled estimates
  have hA' : (47 / 10) * X ^ 2 - (10 * Y ^ 2 + 40 * Z ^ 2 + (5 / 4) * X ^ 2)
      ≤ 10 * Work.Coercivity.wip
      (Rho Work.Spaces.eta) (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dz f) := by
    have h := mul_le_mul_of_nonneg_left hA (show (0 : ℝ) ≤ 10 by norm_num)
    rw [← hX2, ← hY2, ← hZ2] at h
    linarith [h]
  have hB' : (47 / 100) * (10 : ℝ) ^ 10 * Y ^ 2 ≤ (10 : ℝ) ^ 10 * Work.Coercivity.wip
      (Rho Work.Spaces.eta) (Work.FTS.CoercivityFix.Lhat f) f := by
    have h := mul_le_mul_of_nonneg_left hB (show (0 : ℝ) ≤ (10 : ℝ) ^ 10 by norm_num)
    rw [hY2]
    linarith [h]
  have hC' : (1 / 8) * (10 : ℝ) ^ 17 * EnOne f - 6 * (10 : ℝ) ^ 17 * Work.Coercivity.EDthW f
      ≤ (10 : ℝ) ^ 17 * Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
          (Work.FTS.CoercivityFix.Lhat f) f := by
    have h := mul_le_mul_of_nonneg_left hC (show (0 : ℝ) ≤ (10 : ℝ) ^ 17 by norm_num)
    linarith [h]
  have hD' : (17 / 40) * (10 : ℝ) ^ 21 * Z ^ 2 ≤ (10 : ℝ) ^ 21 * Work.Coercivity.wip
      (Rho (Work.Spaces.gam α)) (Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f))
        (Work.Spaces.Dth f) := by
    have h := mul_le_mul_of_nonneg_left hD (show (0 : ℝ) ≤ (10 : ℝ) ^ 21 by norm_num)
    rw [hZ2]
    linarith [h]
  -- ## the two AM–GM steps

  have hWc : (6 : ℝ) * (10 : ℝ) ^ 17 * Work.Coercivity.EDthW f
      ≤ 6 * (10 : ℝ) ^ 17 * Z ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hW (show (0 : ℝ) ≤ 6 * (10 : ℝ) ^ 17 by norm_num)
    linarith [h, hZ2]
  -- ## conclusion
  have hfin : 2 * X ^ 2 + 2 * Y ^ 2 + 2 * Z ^ 2
      ≤ 10 * Work.Coercivity.wip (Rho Work.Spaces.eta)
            (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dz f)
        + (10 : ℝ) ^ 10 * Work.Coercivity.wip (Rho Work.Spaces.eta)
            (Work.FTS.CoercivityFix.Lhat f) f
        + (10 : ℝ) ^ 17 * Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
            (Work.FTS.CoercivityFix.Lhat f) f
        + (10 : ℝ) ^ 21 * Work.Coercivity.wip (Rho (Work.Spaces.gam α))
            (Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dth f) := by
    have hEn : 0 ≤ EnOne f := EnOne_nonneg f
    nlinarith [hA', hB', hC', hD', hWc, hEn]
  rw [hX2, hY2, hZ2] at hfin
  linarith [hfin]

end Work.FTS.CoercivityFix.Coer1
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1.HkSqOne =====
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
set_option maxHeartbeats 1600000

/-- The open quadrant on which the `ℋ¹`-weights are continuous. -/
abbrev Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

/-- The piece `u ↦ u · w/sin(2θ)^{η/2}` is continuous on the open quadrant. -/
theorem continuousOn_wdiv : ContinuousOn (fun p : ℝ × ℝ =>
    Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) Qd := by
  have hsinpos : ∀ p ∈ Qd, 0 < Real.sin (2 * p.2) :=
    fun p hp =>
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Qd := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  have hsinpow : ContinuousOn (fun p : ℝ × ℝ =>
      (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) Qd :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn)
      |>.rpow_const (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  exact hw.div hsinpow (fun p hp => ne_of_gt (Real.rpow_pos_of_pos (hsinpos p hp) _))





/-- Domination of a square of a continuous function by the `ℋ^k`-integrand gives the honesty
of its iterated integral. -/
theorem i2Mem_sq_of_le (α : ℝ) (k : ℕ) {f A : Fn} (hm : Work.Spaces.HkMem α k f)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => (A p.1 p.2) ^ 2) Qd)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (A z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k f z θ) :
    Work.Coercivity.I2Mem (fun z θ => (A z θ) ^ 2) := by
  constructor
  · intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      refine MeasureTheory.IntegrableOn.congr_fun integrableOn_zero (fun θ hθ => ?_)
        measurableSet_Icc
      have h1 := hle 0 (le_refl (0 : ℝ)) θ hθ
      rw [Work.Spaces.HkIntegrand_zero_z] at h1
      exact (le_antisymm h1 (sq_nonneg _)).symm
    · have hsl : ContinuousOn (fun θ : ℝ => (A z θ) ^ 2) (Set.Ioo 0 (π / 2)) :=
        hcont.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun θ hθ => ⟨hz0, hθ⟩)
      have haesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (A z θ) ^ 2)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
        have h1 : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (A z θ) ^ 2)
            (MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2))) :=
          hsl.aestronglyMeasurable measurableSet_Ioo
        have hset : MeasureTheory.volume.restrict Work.Spaces.Iθ
            = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
          (MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm
        rwa [hset]
      refine MeasureTheory.Integrable.mono' (hm.1 z hz) haesm ?_
      filter_upwards [MeasureTheory.ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hle z hz θ hθ
  · have hjoint : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => (A p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.Spaces.aesm_of_continuousOn_Qd _ hcont
    refine MeasureTheory.Integrable.mono' hm.2 hjoint.integral_prod_right' ?_
    filter_upwards [MeasureTheory.ae_restrict_mem
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg _)
      (hm.1 z hz)
      (MeasureTheory.ae_restrict_of_forall_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) fun θ hθ => hle z hz θ hθ)


end Work.FTS.CoercivityFix.Coer1
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1.thetaIBP =====
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
set_option maxHeartbeats 1600000




/-- The `cos(2θ)·sin(2θ)^{-β}·v²` slice is integrable as soon as the `w²·sin(2θ)^{-β}·v²`
slice is (the constant `w(z)² ≠ 0` can be divided out and `cos(2·)` is bounded on the compact
interval `Iθ`). -/
theorem cos_sin_integrable_Q (β : ℝ) (v : Fn) {z : ℝ} (hz : 0 < z)
    (hC : MeasureTheory.IntegrableOn (fun θ => Rho β z θ * (v z θ) ^ 2) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
      (fun θ => Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-β) * (v z θ) ^ 2)
      Work.Spaces.Iθ := by
  have hw : Work.Spaces.w z ≠ 0 := by
    unfold Work.Spaces.w
    positivity
  have hg : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin (2 * θ)) ^ (-β) * (v z θ) ^ 2) Work.Spaces.Iθ := by
    rw [MeasureTheory.IntegrableOn] at hC ⊢
    have hrw : (fun θ => Rho β z θ * (v z θ) ^ 2)
        = fun θ => (Work.Spaces.w z) ^ 2 *
            ((Real.sin (2 * θ)) ^ (-β) * (v z θ) ^ 2) := by
      funext θ
      simp only [Rho, sig]
      ring
    rw [hrw] at hC
    exact (MeasureTheory.integrable_const_mul_iff
      (isUnit_iff_ne_zero.mpr (pow_ne_zero 2 hw)) _).mp hC
  have hcont : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) Work.Spaces.Iθ :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
  have hh := MeasureTheory.IntegrableOn.continuousOn_mul hcont hg isCompact_Icc
  simpa [mul_assoc] using hh


end Work.FTS.CoercivityFix.Coer1
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1.zIBP =====
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
set_option maxHeartbeats 1600000

/-! ## The slice derivative of a `SmoothQuad` function -/





/-! ## The `wip`-identity -/





end Work.FTS.CoercivityFix.Coer1
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1SO.Defs =====
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
set_option linter.unusedVariables false

/-! ## The open-class `z`-integration-by-parts package -/

/-- **The `z`-integration-by-parts hypotheses in the open class.**  This is
`Work.FTS.CoercivityFix.Coer1.ZIBP` with the smoothness field weakened from the analytic
`SmoothQuad` to the honest `SmoothOpen` (`C^∞` on the open quadrant `(0,∞) × (0,π/2)`, the
class carried by `RegQo`).

Every consumer of `ZIBP` in the `z`-IBP of §6 uses the smoothness only through the
differentiability of the `z`-slices at `z > 0` and the chain rule there, both of which
`SmoothOpen` supplies; the boundary limits are asked on the open angular interval and the two
one-dimensional integrals only a.e. in the angle, exactly as before. -/
structure ZIBPO (u : Fn) : Prop where
  /-- the datum is `C^∞` on the open quadrant -/
  smooth : Work.FTS.EllipticEst.SmoothOpen u
  /-- the boundary term `z (u w)²` vanishes at `z = 0⁺` -/
  bd0 : ∀ θ ∈ Set.Ioo 0 (π / 2),
    Filter.Tendsto (fun z => z * (u z θ * Work.Spaces.w z) ^ 2) (𝓝[>] 0) (𝓝 0)
  /-- the boundary term `z (u w)²` vanishes at `z = ∞` -/
  bdTop : ∀ θ ∈ Set.Ioo 0 (π / 2),
    Filter.Tendsto (fun z => z * (u z θ * Work.Spaces.w z) ^ 2) Filter.atTop (𝓝 0)
  /-- a.e. in the angle, `(u w)²` is `z`-integrable -/
  intSq : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
    MeasureTheory.IntegrableOn (fun z => (u z θ * Work.Spaces.w z) ^ 2) (Set.Ioi 0)
  /-- a.e. in the angle, the derivative of the boundary term is `z`-integrable -/
  intDeriv : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
    MeasureTheory.IntegrableOn
      (fun z => deriv (fun z' => z' * (u z' θ * Work.Spaces.w z') ^ 2) z) (Set.Ioi 0)

/-! ## The fragment of `IntPkg` consumed by the base estimate of the `D_z`-clause -/

/-- **The integrability fragment of the `D_z`-clause at level 2, in the open class.**  This
carries exactly the certificates that `H1IP α (D_z f) f ≤ 10²²·|f|²_{ℋ¹}` consumes (see the
frozen proof in `Assembly/V_bounds.lean`): the squared `D_z`-blocks at levels `0, 1` in the
`η`-weight, the squared `f`-, `D_z f`- and `D_θ f`-blocks in the plain radial weight, the
`D_θ f`-block in the `γ`-weight, the four `𝓛`-pairings, and the a.e. commutation
`D_z D_θ f = D_θ D_z f` used to identify the last pairing. -/
structure IP2O (α : ℝ) (f : Fn) : Prop where
  /-- `(D_z f)²·ρ_η` is jointly integrable -/
  sqDzEta_one : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ =>
      (Work.Spaces.Dz f z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- `f²·ρ_η` is jointly integrable -/
  sqDzEta_zero : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ =>
      f z θ ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- `f²·w²` is jointly integrable -/
  sqDzOne_zero : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => f z θ ^ 2 * Work.Spaces.w z ^ 2))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- `(D_z f)²·w²` is jointly integrable -/
  sqDzOne_one : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => (Work.Spaces.Dz f z θ) ^ 2 * Work.Spaces.w z ^ 2))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- `(D_θ f)²·w²` is jointly integrable -/
  sqDthOne : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => (Work.Spaces.Dth f z θ) ^ 2 * Work.Spaces.w z ^ 2))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- `(D_θ f)²·ρ_γ` is jointly integrable -/
  sqDthGam : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ =>
      (Work.Spaces.Dth f z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `𝓛`-pairing of `f` with the `η`-weight is jointly integrable -/
  intL_f_eta : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ =>
      Work.Coercivity.L f z θ * f z θ * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `𝓛`-pairing of `D_z f` with the `η`-weight is jointly integrable -/
  intL_Dz_eta : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Coercivity.L (Work.Spaces.Dz f) z θ
      * Work.Spaces.Dz f z θ * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `𝓛`-pairing of `f` with the plain radial weight is jointly integrable -/
  intL_f_one : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ =>
      Work.Coercivity.L f z θ * f z θ * Work.Spaces.w z ^ 2))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `𝓛`-pairing of `D_z f` with the plain radial weight is jointly integrable -/
  intL_Dz_one : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Coercivity.L (Work.Spaces.Dz f) z θ
      * Work.Spaces.Dz f z θ * Work.Spaces.w z ^ 2))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `𝓛`-pairing of `D_θ f` with the plain radial weight is jointly integrable -/
  intL_Dth_one : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Coercivity.L (Work.Spaces.Dth f) z θ
      * Work.Spaces.Dth f z θ * Work.Spaces.w z ^ 2))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- the `𝓛`-pairing of `D_θ f` with the `γ`-weight is jointly integrable -/
  intL_Dth_gam : MeasureTheory.IntegrableOn
    (Function.uncurry (fun z θ => Work.Coercivity.L (Work.Spaces.Dth f) z θ
      * Work.Spaces.Dth f z θ * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ))
    (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
  /-- `D_z` and `D_θ` commute almost everywhere on the quadrant -/
  dzDthComm : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.Dz (Work.Spaces.Dth f) z θ = Work.Spaces.Dth (Work.Spaces.Dz f) z θ

end Work.FTS.CoercivityFix.Coer1SO
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1T.hardyHyp_of_coerAdm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Coer1T


end Work.FTS.CoercivityFix.Coer1T
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.E2Bound.E2hat_HkIntegrand_le_uniform =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.E2Bound

open scoped Real Topology

set_option autoImplicit false

/-! # The `ℋⁿ`-bound for the `D_z`-commutator defect `Ê₂`

`Work.FTS.CoercivityFix.E2hat f = (2zf + 3z·D_θf)/(1+z)² = 2·φ·f + 3·φ·D_θf` with
`φ(z) = z/(1+z)²`.  This file proves the *pointwise* slot bound

`HkIntegrand α n (Ê₂ f) z θ ≤ C · (HkIntegrand α n f z θ + HkIntegrand α n (D_θ f) z θ)`

with `C` depending only on `n` (in fact `C = 18·κ_n·(1+K_n)² + 1`, where `κ_n` is the
multiplier constant of `HkIntegrand_zmul_le` and `K_n` the uniform bound on the `D_z`-iterates
of `φ`), on the open quadrant `z > 0`, `0 < θ < π/2`.

The three ingredients, all independent of each other:

* `HkIntegrand_zmul_le`: for a multiplier `a = a(z)` whose `D_z`-iterates up to order `n` are
  bounded by `K` on `(0,∞)`, `HkIntegrand α n (a·f) ≤ C(n)·(1+K)²·HkIntegrand α n f`
  (the Leibniz bookkeeping);
* `zop_phi_bound`: the specific bound for `φ(z) = z/(1+z)²`;
* the subadditivity `HkIntegrand_add_le` / homogeneity `HkIntegrand_const_mul` of the
  integrand, which split `Ê₂ f = 2·(φ·f) + 3·(φ·D_θ f)` and scale the two pieces.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

/-! ## The `z`-only multiplier `φ(z) = z/(1+z)²` -/

/-- `φ(z) = z/(1+z)²` is `C^∞` on `(-1,∞)`. -/
theorem contDiffOn_zDiv : ContDiffOn ℝ Work.Stability.smoothOrder
    (fun z : ℝ => z / (1 + z) ^ 2) (Set.Ioi (-1)) := by
  refine ContDiffOn.div (by fun_prop) (by fun_prop) ?_
  intro z hz
  simp only [Set.mem_Ioi] at hz
  exact pow_ne_zero 2 (by linarith)

/-- A function of `z` alone, `C^∞` on `(-1,∞)`, is `SmoothQuad` as a function of `(z,θ)`. -/
theorem smoothQuad_of_zOnly {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ Work.Stability.smoothOrder a (Set.Ioi (-1))) :
    Work.FTS.LocData.SmoothQuad (fun z _ : ℝ => a z) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (fun z _ : ℝ => a z))
    (Set.Ioi (-1) ×ˢ Set.Ioo 0 (Real.pi / 2))
  have h : Function.uncurry (fun z _ : ℝ => a z) = fun p : ℝ × ℝ => a p.1 := rfl
  rw [h]
  exact ha.comp contDiffOn_fst (fun p hp => hp.1)

/-- `φ(z) = z/(1+z)²` is `SmoothQuad`. -/
theorem smoothQuad_zDiv : Work.FTS.LocData.SmoothQuad (fun z _ : ℝ => z / (1 + z) ^ 2) :=
  smoothQuad_of_zOnly contDiffOn_zDiv

/-! ## The explicit form of the defect -/

/-- **The defect as a `z`-multiplier.**  `Ê₂ f = 2·φ·f + 3·φ·D_θf` with `φ(z) = z/(1+z)²`. -/
theorem E2hat_eq_zmul (f : ℝ → ℝ → ℝ) :
    Work.FTS.CoercivityFix.E2hat f
      = fun z θ => 2 * ((z / (1 + z) ^ 2) * f z θ)
          + 3 * ((z / (1 + z) ^ 2) * Work.Spaces.Dth f z θ) := by
  funext z θ
  rw [Work.FTS.CoercivityFix.E2hat_eq]
  field_simp


end Work.FTS.CoercivityFix.E2Bound
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.QuadPorts.RegQ_dth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.CoercivityFix.QuadPorts

/-- `D_θ` raises the angular order of the mixed derivatives by one:
`D_z^j D_θ^i (D_θ f) = D_z^j D_θ^{i+1} f`. -/
theorem mixed_Dth_shift (j i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (Work.Spaces.Dth f) = Work.Spaces.mixed j (i + 1) f := by
  simp only [Work.Spaces.mixed]
  have h : Work.Spaces.Dth f = Work.Spaces.DthIter 1 f := rfl
  rw [h, Work.Spaces.DthIter_add_right]

/-- `D_θ` preserves `C^∞`-smoothness on the open quadrant. -/
theorem smoothQuad_Dth {f : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f) :
    Work.FTS.LocData.SmoothQuad (Work.Spaces.Dth f) := by
  have h := hf.DthIter 1
  rwa [show Work.Spaces.DthIter 1 f = Work.Spaces.Dth f from rfl] at h

theorem RegQ_dth (α : ℝ) (hα : 0 < α) {n : ℕ} {f : ℝ → ℝ → ℝ}
    (h : Work.FTS.Nonlin.RegQ α (n + 1) f) :
    Work.FTS.Nonlin.RegQ α n (Work.Spaces.Dth f) := by
  obtain ⟨hsm, hmem, hbd⟩ := h
  have hsm' : Work.FTS.LocData.SmoothQuad (Work.Spaces.Dth f) := smoothQuad_Dth hsm
  refine ⟨hsm', ?_, ?_⟩
  · -- the `ℋⁿ`-membership, by domination of the integrands
    refine Work.FTS.LocData.HkMem_of_majorant α n
      (f := Work.Spaces.Dth f)
      (M := fun z θ => Work.Spaces.HkIntegrand α (n + 1) f z θ) ?_ ?_ ?_ ?_
    · exact Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α n (Work.Spaces.Dth f) hsm'
    · exact hmem.1
    · exact hmem.2
    · intro z hz θ hθ
      exact Work.Coercivity.HkIntegrand_Dth_le α hα n f z θ hz hθ
  · -- the boundary traces, by the reindexing of the mixed derivatives
    intro a b hab
    have key : ∀ z θ, Work.Spaces.mixed b a (Work.Spaces.Dth f) z θ
        = Work.Spaces.mixed b (a + 1) f z θ := fun z θ => by rw [mixed_Dth_shift]
    simpa only [key] using hbd (a + 1) b (by omega)

end Work.FTS.CoercivityFix.QuadPorts
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.HardyOne =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer.E1Parts


end Work.FTS.CoercivityFix.Transfer.E1Parts
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E2norm.L12f_Transport_zero_sq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer.E2norm

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-!
# `(L₁₂(Transport f)(0))² ≤ 16·|D_θ f|²_{ℋⁿ}`

The `L₁₂`-zero-mode `C0 f = L₁₂(Transport f)(0)` — the constant of the projector term of
`𝓛_Γ^T` — is controlled by the *angular* derivative `D_θ f` alone, uniformly in `α ∈ (0,1]`
and in `n ≤ 3`.  The proof is a single Cauchy–Schwarz on the product measure
`(volume|Iz) ⊗ (volume|Iθ)`:

`C0 f = ∫∫ 3 K(θ) D_θ f(z,θ)/(z(1+z)) dθ dz = ∫∫ A·B`, with

`A(z,θ) = 3 K(θ)·z/(1+z)³·sin(2θ)^{η/2}`,  `B(z,θ) = D_θ f(z,θ)·w(z)/sin(2θ)^{η/2}`,

whose squares are integrable (`A²` is a product of two explicitly bounded factors and
`B² = HkIntegrand α 0 (D_θ f)` is exactly a summand of the `ℋⁿ` integrand).  The constant
`16` is the crude product of the two one-dimensional bounds
`∫_z (z/(1+z)³)² ≤ 1/16` and `∫_θ 9 K(θ)² sin(2θ)^η ≤ 162`.

The three numerical/structural inputs are proved in the sibling modules `C0_eq_density`
(the unfolding of `C0`), `A_sq_prod_le` and `B_sq_prod_eq_HkSq`.
-/

/-- The angular factor `3 K(θ)·z/(1+z)³·sin(2θ)^{η/2}` of the Cauchy–Schwarz weight. -/
private noncomputable def cwA (p : ℝ × ℝ) : ℝ :=
  3 * Work.Spaces.K p.2 * (p.1 / (1 + p.1) ^ 3)
    * (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)

/-- The `D_θ f`-factor of the Cauchy–Schwarz weight.  Its square is exactly
`HkIntegrand α 0 (D_θ f)`. -/
private noncomputable def cwB (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  Work.Spaces.Dth f p.1 p.2
    * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))

/-- The product measure `(volume|Iz) ⊗ (volume|Iθ)`. -/
private noncomputable def cwμ : Measure (ℝ × ℝ) :=
  (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)

/-! ## Elementary facts about the two weights -/

/-- `Iθ` agrees a.e. with its interior, so angular identities need only hold on
`(0, π/2)`. -/
private theorem Iθ_restrict_congr : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
  (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm

/-- `cwA` is measurable (it is a product of measurable functions; the `sin(2θ)^{η/2}`
factor is measurable because `x ↦ x^{η/2}` is continuous, `η/2 > 0`). -/
private theorem cwA_measurable : Measurable cwA := by
  have hK : Measurable (fun p : ℝ × ℝ => Work.Spaces.K p.2) := by
    apply Continuous.measurable
    show Continuous fun p : ℝ × ℝ => 3 * Real.sin p.2 * Real.cos p.2 ^ 2
    fun_prop
  have hrat : Measurable (fun p : ℝ × ℝ => p.1 / (1 + p.1) ^ 3) :=
    measurable_fst.div ((measurable_const.add measurable_fst).pow_const 3)
  have hrpow : Measurable (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) :=
    (Real.continuous_rpow_const (by norm_num [Work.Spaces.eta])).measurable.comp
      ((by fun_prop : Continuous fun p : ℝ × ℝ => Real.sin (2 * p.2)).measurable)
  exact ((hK.const_mul 3).mul hrat).mul hrpow

/-- `cwB f` is a.e. strongly measurable on the product measure as soon as `f` is smooth on
the open quadrant. -/
private theorem cwB_aesm {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f) :
    AEStronglyMeasurable (cwB f) cwμ := by
  have hDth : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    (hsm.DthIter 1).continuousOn.mono (fun p hp => by
      refine ⟨?_, ?_⟩
      · have h1 : (0 : ℝ) < p.1 := hp.1
        show (-1 : ℝ) < p.1
        linarith
      · exact hp.2)
  have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2) cwμ :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hDth
  have h2 : Measurable (fun p : ℝ × ℝ =>
      Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) := by
    have hw : Measurable (fun p : ℝ × ℝ => Work.Spaces.w p.1) := by
      show Measurable fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2
      exact ((measurable_const.add measurable_fst).pow_const 2).div
        (measurable_fst.pow_const 2)
    have hrpow : Measurable (fun p : ℝ × ℝ =>
        (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) :=
      (Real.continuous_rpow_const (by norm_num [Work.Spaces.eta])).measurable.comp
        ((by fun_prop : Continuous fun p : ℝ × ℝ => Real.sin (2 * p.2)).measurable)
    exact hw.div hrpow
  exact h1.mul h2.aestronglyMeasurable

/-- The pointwise identity underlying the Cauchy–Schwarz decomposition (for `z > 0` and
`θ` in the interior of `Iθ`). -/
private theorem cwA_mul_cwB {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    3 * Work.Spaces.K θ * Work.Spaces.Dth f z θ / (z * (1 + z))
      = cwA (z, θ) * cwB f (z, θ) := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsne : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hs _)
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hz1 : (1 : ℝ) + z ≠ 0 := by positivity
  simp only [cwA, cwB, Work.Spaces.w]
  field_simp

/-! ## The Cauchy–Schwarz bound -/


/-! ## The target -/


end Work.FTS.CoercivityFix.Transfer.E2norm
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.hasDerivAt_radA =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer

open Work.FTS.Galerkin (Fn)

/-- `ampA α` is differentiable at every `z > 0`.  If `c α = 0` the function is identically
`0` (division by the vanishing denominator); otherwise the denominator `c·(1+z)²` is nonzero
at `z > 0`. -/
lemma differentiableAt_ampA (α : ℝ) {z : ℝ} (hz : 0 < z) :
    DifferentiableAt ℝ (ampA α) z := by
  by_cases hc : Work.Spaces.c α = 0
  · have h0 : ampA α = fun _ : ℝ => 0 := by funext w; simp [ampA, hc]
    rw [h0]; exact differentiableAt_const 0
  · have hnum : DifferentiableAt ℝ (fun w : ℝ => 2 * w) z :=
      (differentiableAt_const (2 : ℝ)).mul differentiableAt_id
    have hden : DifferentiableAt ℝ (fun w : ℝ => Work.Spaces.c α * (1 + w) ^ 2) z :=
      (((differentiableAt_const (1 : ℝ)).add differentiableAt_id).pow 2).const_mul
        (Work.Spaces.c α)
    have hne : Work.Spaces.c α * (1 + z) ^ 2 ≠ 0 := by
      refine mul_ne_zero hc (pow_ne_zero 2 ?_)
      linarith
    exact hnum.div hden hne

/-- The derivative form of `differentiableAt_ampA`. -/
lemma hasDerivAt_ampA (α : ℝ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (ampA α) (deriv (ampA α) z) z :=
  (differentiableAt_ampA α hz).hasDerivAt

/-- `ampB α` is differentiable at every `z > 0`. -/
lemma differentiableAt_ampB (α : ℝ) {z : ℝ} (hz : 0 < z) :
    DifferentiableAt ℝ (ampB α) z := by
  have hden : DifferentiableAt ℝ (fun w : ℝ => (1 + w) ^ 3) z :=
    ((differentiableAt_const (1 : ℝ)).add differentiableAt_id).pow 3
  have hnum : DifferentiableAt ℝ (fun w : ℝ => 2 * w ^ 2) z :=
    (differentiableAt_const (2 : ℝ)).mul (differentiableAt_id.pow 2)
  have hne : (1 + z) ^ 3 ≠ 0 := by
    refine pow_ne_zero 3 ?_
    linarith
  exact hnum.div hden hne

/-- The derivative form of `differentiableAt_ampB`. -/
lemma hasDerivAt_ampB (α : ℝ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (ampB α) (deriv (ampB α) z) z :=
  (differentiableAt_ampB α hz).hasDerivAt

/-- The composite `z ↦ radA α f z` is differentiable at `z > 0`, with derivative the explicit
expression appearing in `hasDerivAt_radA`.  This is just the product/negation calculus on
`ampA`, `ampB` and `L₁₂ f`. -/
lemma hasDerivAt_radA_aux (α : ℝ) (f : Fn) (hfH : Work.Coercivity.HardyHyp f) {z : ℝ}
    (hz : 0 < z) :
    HasDerivAt (radA α f)
      (-(deriv (ampA α) z) * Work.Coercivity.L12f f z
        + (-ampA α z) * deriv (Work.Coercivity.L12f f) z
        + (deriv (ampB α) z / Work.Spaces.c α)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) z := by
  have hA : HasDerivAt (ampA α) (deriv (ampA α) z) z := hasDerivAt_ampA α hz
  have hB : HasDerivAt (ampB α) (deriv (ampB α) z) z := hasDerivAt_ampB α hz
  have hL : HasDerivAt (Work.Coercivity.L12f f)
      (-(Work.FM.L12dens Work.Spaces.K f z)) z :=
    Work.FM.hasDerivAt_L12 (K := Work.Spaces.K) (f := f) (a := 0) hfH.hint (hfH.hcont z hz) hz
  have hLd : HasDerivAt (Work.Coercivity.L12f f)
      (deriv (Work.Coercivity.L12f f) z) z := hL.differentiableAt.hasDerivAt
  have h1 : HasDerivAt (fun w => -ampA α w * Work.Coercivity.L12f f w)
      (-(deriv (ampA α) z) * Work.Coercivity.L12f f z
        + (-ampA α z) * deriv (Work.Coercivity.L12f f) z) z := hA.neg.mul hLd
  have h2 : HasDerivAt
      (fun w => (ampB α w / Work.Spaces.c α)
        * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)
      ((deriv (ampB α) z / Work.Spaces.c α)
        * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) z :=
    (hB.div_const (Work.Spaces.c α)).mul_const
      (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)
  have h : HasDerivAt
      (fun w => -ampA α w * Work.Coercivity.L12f f w
        + (ampB α w / Work.Spaces.c α) * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0)
      (-(deriv (ampA α) z) * Work.Coercivity.L12f f z
        + (-ampA α z) * deriv (Work.Coercivity.L12f f) z
        + (deriv (ampB α) z / Work.Spaces.c α)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) z := h1.add h2
  exact h

/-- **The derivative of the radial profile `radA` is `radS` divided by `z`.**
For `f` with the Hardy hypotheses and `z > 0`,
`deriv (radA α f) z = radS α f z / z`.

Consequently `D_z (Corr α f) = Γ(θ)·radS α f z`, the `D_z`-defect of the transfer. -/
theorem hasDerivAt_radA (α : ℝ) (f : ℝ → ℝ → ℝ) (hfH : Work.Coercivity.HardyHyp f) {z : ℝ}
    (hz : 0 < z) :
    HasDerivAt (Work.FTS.CoercivityFix.Transfer.radA α f)
      (Work.FTS.CoercivityFix.Transfer.radS α f z / z) z := by
  have h := hasDerivAt_radA_aux α f hfH hz
  have hd : DifferentiableAt ℝ (radA α f) z := h.differentiableAt
  have hderiv : deriv (radA α f) z
      = -(deriv (ampA α) z) * Work.Coercivity.L12f f z
        + (-ampA α z) * deriv (Work.Coercivity.L12f f) z
        + (deriv (ampB α) z / Work.Spaces.c α)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 := h.deriv
  have hval : radS α f z / z
      = -(deriv (ampA α) z) * Work.Coercivity.L12f f z
        + (-ampA α z) * deriv (Work.Coercivity.L12f f) z
        + (deriv (ampB α) z / Work.Spaces.c α)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 := by
    rw [div_eq_iff (ne_of_gt hz)]
    simp only [radS, dAmpA, dAmpB]
    ring
  have hd' : HasDerivAt (radA α f) (deriv (radA α f) z) z := hd.hasDerivAt
  rw [hderiv] at hd'
  rwa [← hval] at hd'

end Work.FTS.CoercivityFix.Transfer
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.KJDdG =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllSol.PkgK5.K5c
open Work.Spaces (Dz)
open Work.EllipticEst.Core

local notation "Iθ" => Work.Spaces.Iθ
local notation "thEta" => Work.FTS.EllipticEst.thEta

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-- The log-kernel `t ↦ sKer δ (log z - t)` is integrable (compact support). -/
theorem sKer_sub_integrable {δ z : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hz : 0 < z) :
    Integrable (fun t : ℝ => sKer δ (Real.log z - t)) volume := by
  have hcont : Continuous (fun t : ℝ => sKer δ (Real.log z - t)) :=
    (Work.FTS.EllSol.EllPkgAux.contDiff_sKer δ (n := 1)).continuous.comp
      (continuous_const.sub continuous_id)
  have hzero : ∀ t ∉ Set.Icc (Real.log z - 1) (Real.log z + 1),
      sKer δ (Real.log z - t) = 0 := by
    intro t ht
    refine sKer_eq_zero_of_le_abs hδ ?_
    rw [Set.mem_Icc, not_and_or] at ht
    rcases ht with h | h
    · have h1 : t < Real.log z - 1 := not_le.mp h
      rw [abs_of_pos (by linarith)]
      linarith
    · have h1 : Real.log z + 1 < t := not_le.mp h
      rw [abs_of_neg (by linarith)]
      linarith
  have h1 : Integrable (Set.indicator (Set.Icc (Real.log z - 1) (Real.log z + 1))
      (fun t : ℝ => sKer δ (Real.log z - t))) volume :=
    (hcont.continuousOn.integrableOn_compact isCompact_Icc).integrable_indicator
      measurableSet_Icc
  refine h1.congr (Filter.Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ Set.Icc (Real.log z - 1) (Real.log z + 1)
  · rw [Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem ht]
    exact (hzero t ht).symm

/-- The `σ_η`-weighted angular slice of `D_z²G` is integrable. -/
theorem ddG_slice_integrable {G : ℝ → ℝ → ℝ} (hT : TraceClass G) {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun s : ℝ => (Dz (Dz G) u s) ^ 2 * thEta s) Iθ := by
  have hhon : Work.EllipticEst.Core.i0Aux.SliceHonestOpen G := hT.2.2.2.2.2.2.2
  have h2 : IntegrableOn (fun s : ℝ => (Dz (Dz G) u s) ^ 2 * (Work.Spaces.w u) ^ 2
      * thEta s) Iθ := hhon.2.1 u hu
  refine MeasureTheory.Integrable.mono' h2 ?_ ?_
  · have ha : AEStronglyMeasurable (fun s : ℝ => Dz (Dz G) u s) (volume.restrict Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd
        (Function.uncurry (fun u s : ℝ => Dz (Dz G) u s)) (hT.1.Dz.Dz).continuousOn hu
    have hσ : AEStronglyMeasurable (fun s : ℝ => thEta s) (volume.restrict Iθ) :=
      Work.FTS.EllipticEst.integrableOn_thEta.1.aestronglyMeasurable
    exact (ha.pow 2).mul hσ
  · filter_upwards [MeasureTheory.ae_restrict_mem
      (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)] with s hs
    have hσ0 : 0 ≤ thEta s := Work.FTS.EllipticEst.thEta_nonneg hs
    have hw1 : (1 : ℝ) ≤ (Work.Spaces.w u) ^ 2 := one_le_w_sq hu
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hσ0)]
    exact mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right (sq_nonneg _) hw1) hσ0

/-- The pointwise `KJ`-slice bound for the second radial derivative. -/
theorem ddG_KJ_bound {G : ℝ → ℝ → ℝ} (hT : TraceClass G) {ε θ t : ℝ} (hε : 0 < ε) :
    (∫ s in Iθ, KJ ε θ s * |Dz (Dz G) (Real.exp t) s|)
      ≤ (3 * (ε * sMass)⁻¹ / 2) * ((∫ s in Iθ,
          (Dz (Dz G) (Real.exp t) s) ^ 2 * thEta s) + Real.pi / 2) :=
  slice_abs_le (Real.exp_pos t) hε (ddG_slice_integrable hT (Real.exp_pos t))
    (Work.Spaces.aesm_slice_of_continuousOn_Qd
      (Function.uncurry (fun u s : ℝ => Dz (Dz G) u s)) (hT.1.Dz.Dz).continuousOn
      (Real.exp_pos t))

/-- A.e. strong measurability in `t` of the `KJ`-slice of `D_z²G`. -/
theorem ddG_KJ_aesm {G : ℝ → ℝ → ℝ} (hT : TraceClass G) (ε θ : ℝ) :
    AEStronglyMeasurable (fun t : ℝ => ∫ s in Iθ, KJ ε θ s * |Dz (Dz G) (Real.exp t) s|)
      volume := by
  have hXsm : ContinuousOn (Function.uncurry (fun u s : ℝ => Dz (Dz G) u s))
      Work.FTS.EllipticEst.Q0 := (hT.1.Dz.Dz).continuousOn
  exact MmPsi_aesm (aeStronglyMeasurable_exp hXsm).aemeasurable ε θ

/-- **The angular `KJ`-slice of the second radial derivative of a trace-class datum, tested
against the logarithmic mollification kernel, is integrable in the logarithmic radial
variable.** -/
theorem KJ_ddG_integrable_mine {G : ℝ → ℝ → ℝ} (hT : TraceClass G) (hF : FourInts G)
    {δ ε θ z : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hz : 0 < z) :
    Integrable (fun t : ℝ => sKer δ (Real.log z - t)
      * (∫ s in Iθ, KJ ε θ s * |Dz (Dz G) (Real.exp t) s|)) volume := by
  have hdd : IntegrableOn (fun u : ℝ => (Work.Spaces.w u) ^ 2
      * (∫ s in Iθ, (Dz (Dz G) u s) ^ 2 * thEta s)) Work.Spaces.Iz := by
    simpa only [Work.EllipticEst.Core.ddIntS] using hF.2.1
  have hkerint : Integrable (fun t : ℝ => sKer δ (Real.log z - t)
      * (∫ s in Iθ, (Dz (Dz G) (Real.exp t) s) ^ 2 * thEta s)) volume :=
    integrable_sKer_slice (hT.1.Dz.Dz).continuousOn hδ hz hdd
  have hsKerint : Integrable (fun t : ℝ => sKer δ (Real.log z - t)) volume :=
    sKer_sub_integrable hδ hδ1 hz
  have hg : Integrable (fun t : ℝ => sKer δ (Real.log z - t)
      * ((3 * (ε * sMass)⁻¹ / 2) * ((∫ s in Iθ,
          (Dz (Dz G) (Real.exp t) s) ^ 2 * thEta s) + Real.pi / 2))) volume := by
    refine ((hkerint.const_mul (3 * (ε * sMass)⁻¹ / 2)).add
      (hsKerint.const_mul (3 * (ε * sMass)⁻¹ / 2 * (Real.pi / 2)))).congr
      (Filter.Eventually.of_forall fun t => by
        simp only [Pi.add_apply]
        ring)
  have hmeas : AEStronglyMeasurable (fun t : ℝ => sKer δ (Real.log z - t)
      * (∫ s in Iθ, KJ ε θ s * |Dz (Dz G) (Real.exp t) s|)) volume := by
    have hsK : Continuous (fun t : ℝ => sKer δ (Real.log z - t)) :=
      (Work.FTS.EllSol.EllPkgAux.contDiff_sKer δ (n := 1)).continuous.comp
        (continuous_const.sub continuous_id)
    refine (hsK.aestronglyMeasurable.mul (ddG_KJ_aesm hT ε θ)).congr
      (Filter.Eventually.of_forall fun t => rfl)
  refine MeasureTheory.Integrable.mono' hg hmeas ?_
  filter_upwards with t
  have hnn : (0 : ℝ) ≤ ∫ s in Iθ, KJ ε θ s * |Dz (Dz G) (Real.exp t) s| :=
    MeasureTheory.setIntegral_nonneg (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
      (fun s _ => mul_nonneg (Work.FTS.EllSol.EllPkgAux.KJ_nonneg hε θ s) (abs_nonneg _))
  rw [Real.norm_of_nonneg (mul_nonneg (sKer_nonneg hδ _) hnn)]
  exact mul_le_mul_of_nonneg_left (ddG_KJ_bound hT hε) (sKer_nonneg hδ _)

end Work.FTS.EllSol.EllPkgAux.MollDom
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.ddG_sliceL1_bound =====
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

/-- **The `L¹`-bound for the angular slices of `D_z²G`.**

`TraceClass G` carries, as its last component, `SliceHonestOpen G`, whose *second* conjunct is
exactly the honesty of the `D_z(D_zG)`-slice with the full weight `(w z)² sin(2θ)^{-η}`:

  `IntegrableOn (fun θ => (D_z(D_z G) z θ)² * (w z)² * thEta θ) Iθ`  for `z > 0`.

Dividing the constant weight `(w z)² > 0` off and rewriting `thEta θ = sin(2θ)^{-99/100}` puts
this in the shape required by the weighted Cauchy–Schwarz inequality
`Work.FTS.EllSol.EllPkgAux.MollAux.integralAbsLeSqrtWeighted`, which bounds
`∫_{Iθ} |D_z²G|` by `√(π/2) · √(∫_{Iθ} (D_z²G)² thEta)`.  Since `1 ≤ (w z)²` for `z > 0`, the
weighted square integral is dominated by `ddIntS G z`, and `√a ≤ 1 + a` turns the square root
into the affine bound `1 + ddIntS G z`.  The constant `4` absorbs `√(π/2) < 2`.

The first conjunct is the radial local integrability of `1 + ddIntS G z`, which is exactly the
`ddIntS`-component of `FourInts G`, restricted to `[a,b] ⊆ [0,∞)`. -/
theorem ddG_sliceL1_bound {G : ℝ → ℝ → ℝ} (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) :
    ∃ C : ℝ, 0 < C ∧
      (∀ a b : ℝ, 0 < a → a ≤ b → MeasureTheory.IntegrableOn
        (fun w => C * (1 + Work.EllipticEst.Core.ddIntS G w)) (Set.Icc a b)) ∧
      (∀ w : ℝ, 0 < w → ∫ s in Work.Spaces.Iθ,
        |Work.Spaces.Dz (Work.Spaces.Dz G) w s| ≤ C * (1 + Work.EllipticEst.Core.ddIntS G w)) := by
  obtain ⟨-, -, -, -, -, -, -, hhon⟩ := hT
  refine ⟨4, by norm_num, ?_, ?_⟩
  · -- ## local integrability of `4 * (1 + ddIntS G)`
    intro a b ha hab
    have hsub : Set.Icc a b ⊆ Work.Spaces.Iz := fun w hw => le_trans ha.le hw.1
    have hd : MeasureTheory.IntegrableOn
        (fun z : ℝ => Work.EllipticEst.Core.ddIntS G z) (Set.Icc a b) :=
      (hF.2.1).mono_set hsub
    have h1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b) :=
      MeasureTheory.integrableOn_const (s := Set.Icc a b)
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
    change MeasureTheory.Integrable
      (fun w : ℝ => 4 * (1 + Work.EllipticEst.Core.ddIntS G w))
      (volume.restrict (Set.Icc a b))
    exact (h1.add hd).const_mul 4
  · -- ## the `L¹`-bound for the slice of `D_z²G`
    intro w hw
    have hW2pos : 0 < (Work.Spaces.w w) ^ 2 := pow_pos (Work.FTS.EllSol.EllPkgAux.w_pos hw) 2
    have hW2ne : (Work.Spaces.w w) ^ 2 ≠ 0 := ne_of_gt hW2pos
    -- honesty of the `D_z²G`-slice, with the radial weight stripped off
    have hdd : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
      have h0 := (hhon.2.1 w hw).const_mul (((Work.Spaces.w w) ^ 2)⁻¹)
      refine h0.congr (Filter.Eventually.of_forall (fun θ => ?_))
      show ((Work.Spaces.w w) ^ 2)⁻¹
          * ((Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2 * (Work.Spaces.w w) ^ 2
              * Work.FTS.EllipticEst.thEta θ)
        = (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
      rw [show (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2 * (Work.Spaces.w w) ^ 2
            * Work.FTS.EllipticEst.thEta θ
          = (Work.Spaces.w w) ^ 2
              * ((Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ) from by ring]
      rw [← mul_assoc, inv_mul_cancel₀ hW2ne, one_mul]
    -- the same integrability with the weight written out
    have hdd2 : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))) (Set.Icc 0 (Real.pi / 2)) := by
      rw [Work.Spaces.Iθ] at hdd
      exact hdd.congr (Filter.Eventually.of_forall (fun θ => by
        show (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
          = (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))
        simp only [Work.FTS.EllipticEst.thEta, Work.Spaces.eta]))
    -- the weighted Cauchy–Schwarz bound
    have hAbs := Work.FTS.EllSol.EllPkgAux.MollAux.integralAbsLeSqrtWeighted
      (h := fun s : ℝ => Work.Spaces.Dz (Work.Spaces.Dz G) w s) hdd2
    have hSnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
      refine MeasureTheory.setIntegral_nonneg (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc) ?_
      intro θ hθ
      exact mul_nonneg (sq_nonneg _) (Work.FTS.EllSol.EllPkgAux.thEta_nonneg_of_mem_Iθ hθ)
    have hddIntS_eq : Work.EllipticEst.Core.ddIntS G w
        = (Work.Spaces.w w) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ) := rfl
    have hSle : (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ Work.EllipticEst.Core.ddIntS G w := by
      rw [hddIntS_eq]
      exact le_mul_of_one_le_left hSnn (Work.FTS.EllSol.EllPkgAux.one_le_w_sq hw)
    -- the two forms of the weight
    have haux : (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 2),
          (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
        = ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
      rw [Work.Spaces.Iθ]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
      intro θ _
      simp only [Work.FTS.EllipticEst.thEta, Work.Spaces.eta]
    have hs : Real.sqrt (Real.pi / 2) ≤ 4 := by
      have h2 : Real.sqrt (Real.pi / 2) ≤ 2 := by
        calc Real.sqrt (Real.pi / 2) ≤ Real.sqrt ((2 : ℝ) ^ 2) :=
              Real.sqrt_le_sqrt (by linarith [Real.pi_lt_four])
          _ = 2 := Real.sqrt_sq (by norm_num)
      linarith
    calc (∫ s in Work.Spaces.Iθ, |Work.Spaces.Dz (Work.Spaces.Dz G) w s|)
        ≤ Real.sqrt (Real.pi / 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ) := by
          show (∫ s in Set.Icc (0 : ℝ) (Real.pi / 2),
              |Work.Spaces.Dz (Work.Spaces.Dz G) w s|) ≤ _
          rw [← haux]
          exact hAbs
      _ ≤ Real.sqrt (Real.pi / 2) * (1 + Work.EllipticEst.Core.ddIntS G w) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
          calc Real.sqrt (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2
                  * Work.FTS.EllipticEst.thEta θ)
              ≤ 1 + (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2
                    * Work.FTS.EllipticEst.thEta θ) :=
                Work.FTS.EllSol.EllPkgAux.sqrt_le_one_add_self hSnn
            _ ≤ 1 + Work.EllipticEst.Core.ddIntS G w := by linarith
      _ ≤ 4 * (1 + Work.EllipticEst.Core.ddIntS G w) :=
          mul_le_mul_of_nonneg_right hs (by linarith)

end Work.FTS.EllSol.EllPkgAux.MollDom
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.ibp_kern_first_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

/-- The "open" (trace-class) version of `ibp_kern_first`: the derivative `H` of the slice `G`
is only assumed *interval integrable* (`H` need not be continuous, and no a.e. identification
with `deriv G` is used).  The integration by parts is carried out directly on `0..π/2` with the
given `H`, exactly as in `ibp_first_pi`. -/
theorem ibp_kern_first_open {ρ ρ' G H : ℝ → ℝ} {θ : ℝ}
    (hρ : ∀ t : ℝ, HasDerivAt ρ (ρ' t) t) (hρ'c : Continuous ρ')
    (hGc : ContinuousOn G Work.Spaces.Iθ)
    (hHG : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt G (H x) x)
    (hG0 : G 0 = 0) (hGp : G (Real.pi / 2) = 0)
    (hHint : IntervalIntegrable H MeasureTheory.volume 0 (Real.pi / 2)) :
    (∫ s in Work.Spaces.Iθ, Work.FTS.EllSol.EllPkgAux.Kern ρ' θ s * G s)
      = ∫ s in Work.Spaces.Iθ,
          (ρ (θ - s) + ρ (θ + s) + ρ (θ + s - Real.pi)) * H s := by
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  -- `ρ` is continuous, being differentiable everywhere
  have hρc : Continuous ρ := continuous_iff_continuousAt.mpr fun t => (hρ t).continuousAt
  -- the primitive of `Kern ρ' θ` in the `s` variable
  set ψ : ℝ → ℝ := fun s => -(ρ (θ - s) + ρ (θ + s) + ρ (θ + s - Real.pi)) with hψ
  have hψc : Continuous ψ := by
    rw [hψ]
    exact (((hρc.comp (continuous_const.sub continuous_id)).add
      (hρc.comp (continuous_const.add continuous_id))).add
      (hρc.comp ((continuous_const.add continuous_id).sub continuous_const))).neg
  have hKc : Continuous (fun s : ℝ => Work.FTS.EllSol.EllPkgAux.Kern ρ' θ s) := by
    have h1 : Continuous (fun s : ℝ => ρ' (θ - s)) :=
      hρ'c.comp (continuous_const.sub continuous_id)
    have h2 : Continuous (fun s : ℝ => ρ' (θ + s)) :=
      hρ'c.comp (continuous_const.add continuous_id)
    have h3 : Continuous (fun s : ℝ => ρ' (θ + s - Real.pi)) :=
      hρ'c.comp ((continuous_const.add continuous_id).sub continuous_const)
    exact (h1.sub h2).sub h3
  -- `∂_s ψ = Kern ρ' θ` on the open interval
  have hψ_deriv : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt ψ (Work.FTS.EllSol.EllPkgAux.Kern ρ' θ x) x := by
    intro x _
    have h1 : HasDerivAt (fun s : ℝ => ρ (θ - s)) (-(ρ' (θ - x))) x :=
      HasDerivAt.comp_const_sub θ x (hρ (θ - x))
    have h2 : HasDerivAt (fun s : ℝ => ρ (θ + s)) (ρ' (θ + x)) x :=
      HasDerivAt.comp_const_add θ x (hρ (θ + x))
    have h3 : HasDerivAt (fun s : ℝ => ρ (θ + s - Real.pi)) (ρ' (θ + x - Real.pi)) x := by
      have h := HasDerivAt.comp_const_add (θ - Real.pi) x (hρ ((θ - Real.pi) + x))
      have hfun : (fun s : ℝ => ρ ((θ - Real.pi) + s))
          = fun s : ℝ => ρ (θ + s - Real.pi) := by
        funext s; rw [show (θ - Real.pi) + s = θ + s - Real.pi by ring]
      have hval : ρ' ((θ - Real.pi) + x) = ρ' (θ + x - Real.pi) := by
        rw [show (θ - Real.pi) + x = θ + x - Real.pi by ring]
      rw [hfun, hval] at h
      exact h
    have hd := ((h1.add h2).add h3).neg
    rw [hψ]
    convert hd using 1
    rw [Work.FTS.EllSol.EllPkgAux.Kern]
    ring
  have hIb := Work.FTS.EllSol.EllPkgAux.ibp_first_pi
    (u := ψ) (u' := fun s : ℝ => Work.FTS.EllSol.EllPkgAux.Kern ρ' θ s) (g := G) (h := H)
    hψc.continuousOn hGc hψ_deriv hHG (hKc.intervalIntegrable 0 (Real.pi / 2)) hHint
  -- both sides as interval integrals over `0..π/2`
  rw [Work.FTS.EllSol.EllPkgAux.setIntegral_Iθ_eq_interval,
    Work.FTS.EllSol.EllPkgAux.setIntegral_Iθ_eq_interval]
  -- the boundary terms vanish by `G 0 = G (π/2) = 0`
  have hkey : (∫ x in (0 : ℝ)..(Real.pi / 2),
        Work.FTS.EllSol.EllPkgAux.Kern ρ' θ x * G x)
      = -∫ x in (0 : ℝ)..(Real.pi / 2), ψ x * H x := by
    have h := hIb
    rw [hGp, hG0] at h
    have h' : (∫ x in (0 : ℝ)..(Real.pi / 2), ψ x * H x)
        = -∫ x in (0 : ℝ)..(Real.pi / 2),
            Work.FTS.EllSol.EllPkgAux.Kern ρ' θ x * G x := by
      simpa using h
    linarith
  rw [hkey, ← intervalIntegral.integral_neg]
  have hpt : ∀ x : ℝ, -(ψ x * H x)
      = (ρ (θ - x) + ρ (θ + x) + ρ (θ + x - Real.pi)) * H x := by
    intro x
    simp only [hψ]
    ring
  exact intervalIntegral.integral_congr (fun x _ => hpt x)

end Work.FTS.EllSol.EllPkgAux.MollDom
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.localIntegrable_sqrtE2s =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1000000

/-- **Pointwise estimate for the `u`-integrand.**  For `u ≥ exp p`,
`√(E2s G u)/u ≤ exp(-p)·(1 + ttIntS G u)`: the factor `1/u ≤ exp(-p)` is bounded on the range of
`exp` over `[p, ∞)`, and `√(E2s) ≤ 1 + ttIntS` is the honest `H⁰`-bound on the slice energy. -/
theorem sqrt_E2s_div_le (G : ℝ → ℝ → ℝ) {p u : ℝ} (hu : Real.exp p ≤ u) :
    Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G u) / u
      ≤ Real.exp (-p) * (1 + Work.EllipticEst.Core.ttIntS G u) := by
  have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos p) hu
  have hC : (1 : ℝ) / u ≤ Real.exp (-p) := by
    simpa [one_div, Real.exp_neg] using one_div_le_one_div_of_le (Real.exp_pos p) hu
  calc Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G u) / u
      = Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G u) * (1 / u) := by
        rw [div_eq_mul_inv, one_div]
    _ ≤ Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G u) * Real.exp (-p) :=
        mul_le_mul_of_nonneg_left hC (Real.sqrt_nonneg _)
    _ = Real.exp (-p) * Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G u) := by ring
    _ ≤ Real.exp (-p) * (1 + Work.EllipticEst.Core.ttIntS G u) :=
        mul_le_mul_of_nonneg_left (Work.FTS.EllSol.EllPkgAux.sqrt_e2s_le_one_add_ttIntS G hu0)
          (Real.exp_pos (-p)).le

/-- **Integrability on a compact logarithmic window.**  For any `p q : ℝ`, the function
`t ↦ √(E2s G (exp t))` is integrable on `Icc p q`. -/
theorem integrableOn_sqrt_E2s_exp (G : ℝ → ℝ → ℝ)
    (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) (p q : ℝ) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G (Real.exp t)))
      (Set.Icc p q) MeasureTheory.volume := by
  -- the honest `H⁰`-mass `ttIntS G` is integrable on the `u`-window
  have h1 : MeasureTheory.IntegrableOn (fun u : ℝ => Work.EllipticEst.Core.ttIntS G u)
      (Set.Icc (Real.exp p) (Real.exp q)) MeasureTheory.volume :=
    hF.2.2.1.mono_set (fun u hu => by
      show (0 : ℝ) ≤ u
      exact le_trans (Real.exp_pos p).le hu.1)
  have h2 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ))
      (Set.Icc (Real.exp p) (Real.exp q)) MeasureTheory.volume :=
    MeasureTheory.integrableOn_const (C := (1 : ℝ)) (by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  -- the two pieces of the dominating function, and their sum
  have hA : MeasureTheory.IntegrableOn (fun u : ℝ => Real.exp (-p) * (1 : ℝ))
      (Set.Icc (Real.exp p) (Real.exp q)) MeasureTheory.volume :=
    h2.const_mul (Real.exp (-p))
  have hB : MeasureTheory.IntegrableOn
      (fun u : ℝ => Real.exp (-p) * Work.EllipticEst.Core.ttIntS G u)
      (Set.Icc (Real.exp p) (Real.exp q)) MeasureTheory.volume :=
    h1.const_mul (Real.exp (-p))
  have hdom := hA.add hB
  -- measurability of `u ↦ √(E2s G u)/u` on the `u`-window
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun u : ℝ => Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G u) / u)
      (MeasureTheory.volume.restrict (Set.Icc (Real.exp p) (Real.exp q))) :=
    (Real.continuous_sqrt.comp_aestronglyMeasurable
        (Work.FTS.EllSol.EllPkgAux.MollAux.aesmE2s (G := G) (a := Real.exp p)
          (b := Real.exp q) hT.1 (Real.exp_pos p))).div₀
      measurable_id.aestronglyMeasurable
  -- the pointwise domination on the `u`-window
  have hle : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Set.Icc (Real.exp p) (Real.exp q))),
      ‖Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G u) / u‖
        ≤ Real.exp (-p) * 1 + Real.exp (-p) * Work.EllipticEst.Core.ttIntS G u := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun u hu => ?_)
    have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos p) hu.1
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) hu0.le)]
    have h := sqrt_E2s_div_le G hu.1
    have e : Real.exp (-p) * (1 + Work.EllipticEst.Core.ttIntS G u)
        = Real.exp (-p) * 1 + Real.exp (-p) * Work.EllipticEst.Core.ttIntS G u := by ring
    rwa [e] at h
  have hint : MeasureTheory.IntegrableOn
      (fun u : ℝ => Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G u) / u)
      (Set.Icc (Real.exp p) (Real.exp q)) MeasureTheory.volume :=
    MeasureTheory.Integrable.mono' hdom hmeas hle
  -- the change of variables `u = exp t` on `[p,q]`
  have hkey := MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
    (F := ℝ) (f := Real.exp) (f' := Real.exp) (s := Set.Icc p q)
    (g := fun u : ℝ => Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G u) / u)
    measurableSet_Icc (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn
  rw [Real.image_exp_Icc] at hkey
  have hout := hkey.mp hint
  -- the `exp`-factors cancel
  refine hout.congr_fun (fun x _ => ?_) measurableSet_Icc
  dsimp only
  rw [abs_of_pos (Real.exp_pos x), smul_eq_mul, div_eq_mul_inv]
  have hx : Real.exp x ≠ 0 := Real.exp_ne_zero x
  calc Real.exp x * (Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G (Real.exp x)) * (Real.exp x)⁻¹)
      = Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G (Real.exp x))
          * (Real.exp x * (Real.exp x)⁻¹) := by ring
    _ = Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G (Real.exp x)) * 1 := by
        rw [mul_inv_cancel₀ hx]
    _ = Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G (Real.exp x)) := by ring

theorem localIntegrable_sqrtE2s (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) :
    MeasureTheory.LocallyIntegrable
      (fun t : ℝ => Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G (Real.exp t)))
      MeasureTheory.volume := by
  intro x
  exact ⟨Set.Icc (x - 1) (x + 1),
    mem_of_superset (Ioo_mem_nhds (by linarith) (by linarith)) Ioo_subset_Icc_self,
    integrableOn_sqrt_E2s_exp G hT hF (x - 1) (x + 1)⟩

end Work.FTS.EllSol.EllPkgAux.MollDom
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.sliceL1_bound =====
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

/-- The integral of a constant over the angular interval. -/
theorem integral_Iθ_const (c : ℝ) : ∫ s in Work.Spaces.Iθ, c = c * (Real.pi / 2) := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ Real.pi / 2 by positivity)]
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  ring

/-- The `L¹`-bound for the angular slices of a trace-class datum: the slice of `G`, and the
slice of `D_zG`, are dominated by the local (`L¹` in `w`) functions `MGf G` and
`1 + dIntS G` respectively.  Both are ``honest'' integrals (the slice integrands are
integrable by the honesty component `SliceHonestOpen` of `TraceClass`), and the constant is
the one of `mollSliceBound` inflated by the length `π/2 ≤ 3` of the angular interval and by
the Cauchy–Schwarz factor `√(π/2) ≤ 2`. -/
theorem sliceL1_bound {G : ℝ → ℝ → ℝ} (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) :
    ∃ C : ℝ, 0 < C ∧
      (∀ a b : ℝ, 0 < a → a ≤ b → MeasureTheory.IntegrableOn (fun w => C * Work.FTS.EllSol.EllPkgAux.MGf G w) (Set.Icc a b)) ∧
      (∀ w : ℝ, 0 < w → ∫ s in Work.Spaces.Iθ, |G w s| ≤ C * Work.FTS.EllSol.EllPkgAux.MGf G w) ∧
      (∀ a b : ℝ, 0 < a → a ≤ b → MeasureTheory.IntegrableOn
        (fun w => C * (1 + Work.EllipticEst.Core.dIntS G w)) (Set.Icc a b)) ∧
      (∀ w : ℝ, 0 < w → ∫ s in Work.Spaces.Iθ, |Work.Spaces.Dz G w s| ≤ C * (1 + Work.EllipticEst.Core.dIntS G w)) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.FTS.EllSol.EllPkgAux.mollSliceBound
  obtain ⟨hsl, hintMG⟩ := hC₀ G hT hF
  obtain ⟨-, -, -, -, -, -, -, hhon⟩ := hT
  refine ⟨3 * C₀ + 3, by linarith, ?_, ?_, ?_, ?_⟩
  · -- ## local integrability of `C * MGf G`
    intro a b ha hab
    change MeasureTheory.Integrable
      (fun w : ℝ => (3 * C₀ + 3) * Work.FTS.EllSol.EllPkgAux.MGf G w)
      (volume.restrict (Set.Icc a b))
    exact (hintMG a b ha hab).const_mul (3 * C₀ + 3)
  · -- ## the `L¹`-bound for the slice of `G`
    intro w hw
    have hMGnn : 0 ≤ Work.FTS.EllSol.EllPkgAux.MGf G w := by
      have h2 : (0 : ℝ) ≤ |G w (Real.pi / 4)| := abs_nonneg _
      have h3 : (0 : ℝ) ≤ |Work.Spaces.pth G w (Real.pi / 4)| := abs_nonneg _
      have h4 : (0 : ℝ) ≤ Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G w) := Real.sqrt_nonneg _
      simp only [Work.FTS.EllSol.EllPkgAux.MGf]
      linarith
    have hone_int : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
      MeasureTheory.integrableOn_const (s := Work.Spaces.Iθ)
        (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
    have hconst_int : MeasureTheory.IntegrableOn
        (fun _ : ℝ => C₀ * Work.FTS.EllSol.EllPkgAux.MGf G w) Work.Spaces.Iθ := by
      change MeasureTheory.Integrable
        (fun _ : ℝ => C₀ * Work.FTS.EllSol.EllPkgAux.MGf G w) (volume.restrict Work.Spaces.Iθ)
      simpa only [mul_one] using
        hone_int.const_mul (C₀ * Work.FTS.EllSol.EllPkgAux.MGf G w)
    have hmono : (∫ s in Work.Spaces.Iθ, |G w s|)
        ≤ ∫ s in Work.Spaces.Iθ, C₀ * Work.FTS.EllSol.EllPkgAux.MGf G w :=
      MeasureTheory.integral_mono_of_nonneg (μ := volume.restrict Work.Spaces.Iθ)
        (f := fun s : ℝ => |G w s|)
        (g := fun _ : ℝ => C₀ * Work.FTS.EllSol.EllPkgAux.MGf G w)
        (Filter.Eventually.of_forall (fun s => abs_nonneg _)) hconst_int
        (by
          filter_upwards [Work.FTS.EllSol.EllPkgAux.ae_mem_Ioo_Iθ] with s hs
          exact hsl w hw s hs.1 hs.2)
    have hstep : (C₀ * Work.FTS.EllSol.EllPkgAux.MGf G w) * (Real.pi / 2)
        ≤ (C₀ * Work.FTS.EllSol.EllPkgAux.MGf G w) * 3 := by
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (le_of_lt hC₀pos) hMGnn)
      linarith [Real.pi_lt_four]
    have hstep2 : (C₀ * Work.FTS.EllSol.EllPkgAux.MGf G w) * 3
        ≤ (3 * C₀ + 3) * Work.FTS.EllSol.EllPkgAux.MGf G w := by
      nlinarith [hC₀pos, hMGnn]
    calc (∫ s in Work.Spaces.Iθ, |G w s|)
        ≤ ∫ s in Work.Spaces.Iθ, C₀ * Work.FTS.EllSol.EllPkgAux.MGf G w := hmono
      _ = (C₀ * Work.FTS.EllSol.EllPkgAux.MGf G w) * (Real.pi / 2) := integral_Iθ_const _
      _ ≤ (C₀ * Work.FTS.EllSol.EllPkgAux.MGf G w) * 3 := hstep
      _ ≤ (3 * C₀ + 3) * Work.FTS.EllSol.EllPkgAux.MGf G w := hstep2
  · -- ## local integrability of `C * (1 + dIntS G)`
    intro a b ha hab
    have hsub : Set.Icc a b ⊆ Work.Spaces.Iz := fun w hw => le_trans ha.le hw.1
    have hd : MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.dIntS G z)
        (Set.Icc a b) := (hF.2.2.2).mono_set hsub
    have h1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b) :=
      MeasureTheory.integrableOn_const (s := Set.Icc a b)
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
    change MeasureTheory.Integrable
      (fun w : ℝ => (3 * C₀ + 3) * (1 + Work.EllipticEst.Core.dIntS G w))
      (volume.restrict (Set.Icc a b))
    exact (h1.add hd).const_mul (3 * C₀ + 3)
  · -- ## the `L¹`-bound for the slice of `D_zG`
    intro w hw
    have hW2pos : 0 < (Work.Spaces.w w) ^ 2 := pow_pos (Work.FTS.EllSol.EllPkgAux.w_pos hw) 2
    have hW2ne : (Work.Spaces.w w) ^ 2 ≠ 0 := ne_of_gt hW2pos
    -- honesty of the `D_zG`-slice, with the radial weight stripped off
    have hDz : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.Dz G w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        Work.Spaces.Iθ := by
      have h0 := (hhon.2.2 w hw).const_mul (((Work.Spaces.w w) ^ 2)⁻¹)
      refine h0.congr (Filter.Eventually.of_forall (fun θ => ?_))
      show ((Work.Spaces.w w) ^ 2)⁻¹ * ((Work.Spaces.Dz G w θ) ^ 2 * (Work.Spaces.w w) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
        = (Work.Spaces.Dz G w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
      rw [show (Work.Spaces.Dz G w θ) ^ 2 * (Work.Spaces.w w) ^ 2
            * Work.FTS.EllipticEst.thEta θ
          = (Work.Spaces.w w) ^ 2 * ((Work.Spaces.Dz G w θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ) from by ring]
      rw [← mul_assoc, inv_mul_cancel₀ hW2ne, one_mul]
    -- the same integrability with the weight written out
    have hDz2 : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.Dz G w θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
        (Set.Icc 0 (Real.pi / 2)) := by
      rw [Work.Spaces.Iθ] at hDz
      exact hDz.congr (Filter.Eventually.of_forall (fun θ => by
        show (Work.Spaces.Dz G w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
          = (Work.Spaces.Dz G w θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))
        simp only [Work.FTS.EllipticEst.thEta, Work.Spaces.eta]))
    -- the weighted Cauchy–Schwarz bound
    have hAbs := Work.FTS.EllSol.EllPkgAux.MollAux.integralAbsLeSqrtWeighted
      (h := fun s : ℝ => Work.Spaces.Dz G w s) hDz2
    have hSnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.Dz G w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
      refine MeasureTheory.setIntegral_nonneg (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc) ?_
      intro θ hθ
      exact mul_nonneg (sq_nonneg _) (Work.FTS.EllSol.EllPkgAux.thEta_nonneg_of_mem_Iθ hθ)
    have hdIntS_eq : Work.EllipticEst.Core.dIntS G w
        = (Work.Spaces.w w) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dz G w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := rfl
    have hDnn : 0 ≤ Work.EllipticEst.Core.dIntS G w := by
      rw [hdIntS_eq]
      exact mul_nonneg (le_of_lt hW2pos) hSnn
    have hSle : (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dz G w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ Work.EllipticEst.Core.dIntS G w := by
      rw [hdIntS_eq]
      exact le_mul_of_one_le_left hSnn (Work.FTS.EllSol.EllPkgAux.one_le_w_sq hw)
    -- the two forms of the weight
    have haux : (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 2),
          (Work.Spaces.Dz G w θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
        = ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dz G w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
      rw [Work.Spaces.Iθ]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
      intro θ _
      simp only [Work.FTS.EllipticEst.thEta, Work.Spaces.eta]
    have hs : Real.sqrt (Real.pi / 2) ≤ 3 * C₀ + 3 := by
      have h2 : Real.sqrt (Real.pi / 2) ≤ 2 := by
        calc Real.sqrt (Real.pi / 2) ≤ Real.sqrt ((2 : ℝ) ^ 2) :=
              Real.sqrt_le_sqrt (by linarith [Real.pi_lt_four])
          _ = 2 := Real.sqrt_sq (by norm_num)
      linarith
    calc (∫ s in Work.Spaces.Iθ, |Work.Spaces.Dz G w s|)
        ≤ Real.sqrt (Real.pi / 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dz G w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
          show (∫ s in Set.Icc (0 : ℝ) (Real.pi / 2), |Work.Spaces.Dz G w s|) ≤ _
          rw [← haux]
          exact hAbs
      _ ≤ Real.sqrt (Real.pi / 2) * (1 + Work.EllipticEst.Core.dIntS G w) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
          calc Real.sqrt (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.Dz G w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
              ≤ 1 + (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.Dz G w θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) :=
                Work.FTS.EllSol.EllPkgAux.sqrt_le_one_add_self hSnn
            _ ≤ 1 + Work.EllipticEst.Core.dIntS G w := by linarith
      _ ≤ (3 * C₀ + 3) * (1 + Work.EllipticEst.Core.dIntS G w) :=
          mul_le_mul_of_nonneg_right hs (by linarith)

end Work.FTS.EllSol.EllPkgAux.MollDom
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.mollDzPthConv =====
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

/-! ## Change of variables in the double convolution, with two different kernels -/


/-! ## The quadrant cutoff is invisible to the angular derivative kernel -/


/-! ## The mixed derivative identity -/


end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.mollFatouAssembly =====
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

theorem mollFatouAssembly (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G) (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) (hint : ∀ δ ε : ℝ, Work.FTS.EllSol.EllPkgAux.Params δ ε → MeasureTheory.IntegrableOn (fun z : ℝ => Work.EllipticEst.Core.mixIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z) Work.Spaces.Iz) (hconv : ∀ z : ℝ, 0 < z → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), Filter.Tendsto (fun n : ℕ => (Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G (Work.FTS.EllSol.EllPkgAux.tseq n) (Work.FTS.EllSol.EllPkgAux.tseq n))) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Filter.atTop (nhds ((Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))) (hhon : ∀ (n : ℕ) (z : ℝ), 0 < z → MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G (Work.FTS.EllSol.EllPkgAux.tseq n) (Work.FTS.EllSol.EllPkgAux.tseq n))) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ)) (hhonG : ∀ z : ℝ, 0 < z → MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ)) : ∀ η : ℝ, 0 < η → ∃ δ ε : ℝ, Work.FTS.EllSol.EllPkgAux.Params δ ε ∧ (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z) ≤ (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z) + η := by
  have hhonest : ∀ (n : ℕ) (z : ℝ), 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.pth
        (Work.FTS.EllSol.PkgK5.K5c.zmoll G (tseq n) (tseq n))) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
    intro n z hz
    exact Work.FTS.EllSol.EllPkgAux.MollMFA.zmollSliceHonest G (tseq n) (tseq n)
      (MollAssem.mollAdmMFA G hT hF (tseq n) (tseq n) (params_tseq n)) z hz
  exact MollAssem.mollFatouCore G hT hF hint hconv hhon hhonest

end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.mollKernelAux =====
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

set_option maxHeartbeats 1000000

lemma sKerd_scale_int {t : ℝ} (ht : 0 < t)
    (hsc : ∀ t : ℝ, 0 < t → ∀ u : ℝ, sKerd t u = (1 / t ^ 2) * sKerd 1 (u / t)) (Φ : ℝ → ℝ) :
    (∫ u : ℝ, sKerd t u * Φ u) = (1 / t) * ∫ w : ℝ, sKerd 1 w * Φ (t * w) := by
  have h1 : ∀ u : ℝ, sKerd t u * Φ u
      = (1 / t ^ 2) * (sKerd 1 (t⁻¹ * u) * Φ (t * (t⁻¹ * u))) := by
    intro u
    have hdiv : u / t = t⁻¹ * u := by rw [div_eq_inv_mul]
    have htu : t * (t⁻¹ * u) = u := by field_simp
    rw [hsc t ht u, hdiv, htu]
    ring
  have h2 : (∫ u : ℝ, (1 / t ^ 2) * (sKerd 1 (t⁻¹ * u) * Φ (t * (t⁻¹ * u))))
      = (1 / t ^ 2) * (∫ u : ℝ, sKerd 1 (t⁻¹ * u) * Φ (t * (t⁻¹ * u))) := by
    rw [MeasureTheory.integral_const_mul]
  have h3 : (∫ u : ℝ, sKerd 1 (t⁻¹ * u) * Φ (t * (t⁻¹ * u)))
      = |(t⁻¹)⁻¹| • ∫ w : ℝ, sKerd 1 w * Φ (t * w) :=
    MeasureTheory.Measure.integral_comp_mul_left (fun w : ℝ => sKerd 1 w * Φ (t * w)) (t⁻¹)
  have h4 : (1 / t ^ 2) * (|(t⁻¹)⁻¹| • ∫ w : ℝ, sKerd 1 w * Φ (t * w))
      = (1 / t) * ∫ w : ℝ, sKerd 1 w * Φ (t * w) := by
    rw [inv_inv, abs_of_pos ht, smul_eq_mul]
    have : t * t⁻¹ ^ 2 = t⁻¹ := by rw [sq, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt ht), one_mul]
    rw [show (1 / t ^ 2) * (t * ∫ w : ℝ, sKerd 1 w * Φ (t * w)) = t * t⁻¹ ^ 2 * (∫ w : ℝ, sKerd 1 w * Φ (t * w)) by
          rw [div_eq_mul_inv, inv_pow]; ring, this, one_div]
  calc (∫ u : ℝ, sKerd t u * Φ u)
      = ∫ u : ℝ, (1 / t ^ 2) * (sKerd 1 (t⁻¹ * u) * Φ (t * (t⁻¹ * u))) :=
        integral_congr_ae (Eventually.of_forall h1)
    _ = (1 / t ^ 2) * (∫ u : ℝ, sKerd 1 (t⁻¹ * u) * Φ (t * (t⁻¹ * u))) := h2
    _ = (1 / t ^ 2) * (|(t⁻¹)⁻¹| • ∫ w : ℝ, sKerd 1 w * Φ (t * w)) := by rw [h3]
    _ = (1 / t) * ∫ w : ℝ, sKerd 1 w * Φ (t * w) := h4

/-- `z ∉ [-1,1]` implies `1 ≤ |z|`. -/
lemma one_le_abs_of_notMem_Icc {z : ℝ} (hz : z ∉ Set.Icc (-1:ℝ) 1) : 1 ≤ |z| := by
  rw [Set.mem_Icc] at hz
  by_cases h : z < -1
  · rw [abs_of_nonpos (by linarith)]; linarith
  · have h2 : 1 < z := by
      by_contra hc
      exact hz ⟨by linarith, by linarith⟩
    rw [abs_of_pos (by linarith)]; linarith


lemma mollKernel_aux
    {F : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} {x y : ℝ} (hU : IsOpen U) (hxy : (x, y) ∈ U)
    (hF : ContDiffOn ℝ 2 F U) :
    Tendsto (fun t : ℝ => ∫ u : ℝ, sKerd t u * (∫ v : ℝ, sKerd t v * F (x-u, y-v)))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((fderiv ℝ (fderiv ℝ F) (x,y) (1,0)) (0,1))) := by
  obtain ⟨hηcont, hηcpt, hηvan, hη0, hη1, hηI, hηI1, hηI2, hηscale⟩ := sKerdFacts
  set p : ℝ × ℝ := (x, y) with hp
  have hpU : U ∈ 𝓝 p := by rw [hp]; exact hU.mem_nhds hxy
  have hF2 : ContDiffAt ℝ 2 F p := hF.contDiffAt hpU
  have hsym : IsSymmSndFDerivAt ℝ F p := hF2.isSymmSndFDerivAt (by simp)
  have hFcontU : ContinuousOn F U := hF.continuousOn
  obtain ⟨r, hr0, hru⟩ : ∃ r : ℝ, 0 < r ∧ Metric.ball p r ⊆ U := Metric.mem_nhds_iff.mp hpU
  set c1 : ℝ := (fderiv ℝ F p) ((1:ℝ),(0:ℝ)) with hc1
  set c2 : ℝ := (fderiv ℝ F p) ((0:ℝ),(1:ℝ)) with hc2
  set Aa : ℝ := ((fderiv ℝ (fderiv ℝ F) p) ((1:ℝ),(0:ℝ))) ((1:ℝ),(0:ℝ)) with hAa
  set Bb : ℝ := ((fderiv ℝ (fderiv ℝ F) p) ((1:ℝ),(0:ℝ))) ((0:ℝ),(1:ℝ)) with hBb
  set Dd : ℝ := ((fderiv ℝ (fderiv ℝ F) p) ((0:ℝ),(1:ℝ))) ((0:ℝ),(1:ℝ)) with hDd
  set M0 : ℝ := ∫ u : ℝ, sKerd 1 u with hM0
  set M1 : ℝ := ∫ u : ℝ, u * sKerd 1 u with hM1
  set M2 : ℝ := ∫ u : ℝ, u ^ 2 * sKerd 1 u with hM2
  have hM0v : M0 = 0 := hM0.trans hη0
  have hM1v : M1 = -1 := hM1.trans hη1
  set A0 : ℝ := ∫ w : ℝ, |sKerd 1 w| with hA0
  set A2 : ℝ := ∫ w : ℝ, w ^ 2 * |sKerd 1 w| with hA2
  have hA0int : Integrable (fun w : ℝ => |sKerd 1 w|) := hηI.abs
  have hA2int : Integrable (fun w : ℝ => w ^ 2 * |sKerd 1 w|) := by
    refine hηI2.abs.congr ?_
    filter_upwards with u
    rw [abs_mul, abs_of_nonneg (sq_nonneg u)]
  have hA0nn : 0 ≤ A0 := integral_nonneg fun w => abs_nonneg (sKerd 1 w)
  have hA2nn : 0 ≤ A2 := integral_nonneg fun w => mul_nonneg (sq_nonneg w) (abs_nonneg (sKerd 1 w))
  have poly_intble : ∀ (α β γ : ℝ), Integrable (fun z : ℝ => sKerd 1 z * (α + β * z + γ * z^2)) := by
    intro α β γ
    have h1 : Integrable (fun z : ℝ => α * sKerd 1 z) := hηI.const_mul α
    have h2 : Integrable (fun z : ℝ => β * (z * sKerd 1 z)) := hηI1.const_mul β
    have h3 : Integrable (fun z : ℝ => γ * (z^2 * sKerd 1 z)) := hηI2.const_mul γ
    have h := h1.add (h2.add h3)
    refine h.congr ?_
    filter_upwards with z
    simp only [Pi.add_apply]
    ring
  have poly_int : ∀ (α β γ : ℝ),
      (∫ z : ℝ, sKerd 1 z * (α + β * z + γ * z^2)) = α * M0 + β * M1 + γ * M2 := by
    intro α β γ
    have h1 : Integrable (fun z : ℝ => α * sKerd 1 z) := hηI.const_mul α
    have h2 : Integrable (fun z : ℝ => β * (z * sKerd 1 z)) := hηI1.const_mul β
    have h3 : Integrable (fun z : ℝ => γ * (z^2 * sKerd 1 z)) := hηI2.const_mul γ
    have hfunc : (∫ z : ℝ, sKerd 1 z * (α + β * z + γ * z^2))
        = ∫ z : ℝ, α * sKerd 1 z + (β * (z * sKerd 1 z) + γ * (z^2 * sKerd 1 z)) := by
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      ring
    have hstep2 : (∫ z : ℝ, α * sKerd 1 z + (β * (z * sKerd 1 z) + γ * (z^2 * sKerd 1 z)))
        = (∫ z : ℝ, α * sKerd 1 z)
          + (∫ z : ℝ, β * (z * sKerd 1 z) + γ * (z^2 * sKerd 1 z)) := by
      simpa using MeasureTheory.integral_add h1 (h2.add h3)
    have hstep3 : (∫ z : ℝ, β * (z * sKerd 1 z) + γ * (z^2 * sKerd 1 z))
        = (∫ z : ℝ, β * (z * sKerd 1 z)) + (∫ z : ℝ, γ * (z^2 * sKerd 1 z)) := by
      simpa using MeasureTheory.integral_add h2 h3
    have hsum : (∫ z : ℝ, sKerd 1 z * (α + β * z + γ * z^2))
        = (∫ z : ℝ, α * sKerd 1 z)
          + ((∫ z : ℝ, β * (z * sKerd 1 z)) + (∫ z : ℝ, γ * (z^2 * sKerd 1 z))) := by
      rw [hfunc, hstep2, hstep3]
    rw [hsum, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul, ← hM0, ← hM1, ← hM2]
    ring
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  set Kc : ℝ := 4 * A0 * A2 + 1 with hKc
  have hKcpos : 0 < Kc := by
    rw [hKc]
    have : 0 ≤ 4 * A0 * A2 := by positivity
    linarith
  set εt : ℝ := ε / (2 * Kc) with hεt
  have hεtpos : 0 < εt := by rw [hεt]; positivity
  obtain ⟨δ0, hδ0pos, hδ0⟩ := secondOrderRem_real (f := F) hF2 εt hεtpos
  refine ⟨min r δ0, lt_min hr0 hδ0pos, ?_⟩
  intro t ht htdist
  have ht0 : 0 < t := ht
  have htmin : t < min r δ0 := by rwa [Real.dist_eq, sub_zero, abs_of_pos ht0] at htdist
  have htr : t < r := lt_of_lt_of_le htmin (min_le_left _ _)
  have htδ : t < δ0 := lt_of_lt_of_le htmin (min_le_right _ _)
  have habs1 : ∀ w : ℝ, sKerd 1 w ≠ 0 → |w| < 1 := fun w hw => not_le.mp fun h => hw (hηvan w h)
  -- Taylor polynomial and remainder
  obtain ⟨Tayl, hTayl⟩ : ∃ T : ℝ → ℝ → ℝ, T = fun w z => F p + (-(t*w))*c1 + (-(t*z))*c2
      + (1/2)*(t^2*w^2*Aa + 2*t^2*w*z*Bb + t^2*z^2*Dd) := ⟨_, rfl⟩
  obtain ⟨Rm, hRm⟩ : ∃ R : ℝ → ℝ → ℝ, R = fun w z => F (x - t*w, y - t*z) - Tayl w z := ⟨_, rfl⟩
  -- expansions
  have hlin (w z : ℝ) : (fderiv ℝ F p) (-(t*w), -(t*z)) = (-(t*w))*c1 + (-(t*z))*c2 := by
    have hξe : (-(t*w), -(t*z)) = (-(t*w)) • ((1:ℝ),(0:ℝ)) + (-(t*z)) • ((0:ℝ),(1:ℝ)) := by
      ext <;> simp
    rw [hξe, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← hc1, ← hc2]
  have hquad (w z : ℝ) : ((fderiv ℝ (fderiv ℝ F) p) (-(t*w), -(t*z))) (-(t*w), -(t*z))
      = t^2*w^2*Aa + 2*(t^2*w*z*Bb) + t^2*z^2*Dd := by
    have hexp : ((fderiv ℝ (fderiv ℝ F) p) (-(t*w), -(t*z))) (-(t*w), -(t*z))
        = t^2*w^2 * (((fderiv ℝ (fderiv ℝ F) p) ((1:ℝ),(0:ℝ))) ((1:ℝ),(0:ℝ)))
          + t^2*w*z * (((fderiv ℝ (fderiv ℝ F) p) ((1:ℝ),(0:ℝ))) ((0:ℝ),(1:ℝ)))
          + t^2*z*w * (((fderiv ℝ (fderiv ℝ F) p) ((0:ℝ),(1:ℝ))) ((1:ℝ),(0:ℝ)))
          + t^2*z^2 * (((fderiv ℝ (fderiv ℝ F) p) ((0:ℝ),(1:ℝ))) ((0:ℝ),(1:ℝ))) := by
      have hξe : (-(t*w), -(t*z)) = (-(t*w)) • ((1:ℝ),(0:ℝ)) + (-(t*z)) • ((0:ℝ),(1:ℝ)) := by
        ext <;> simp
      simp only [hξe, map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
      ring_nf
    rw [hexp, hsym.eq ((0:ℝ),(1:ℝ)) ((1:ℝ),(0:ℝ)), ← hAa, ← hBb, ← hDd]
    ring
  have hTay_eq (w z : ℝ) : Rm w z = F (x - t*w, y - t*z) - F p
      - ((-(t*w))*c1 + (-(t*z))*c2)
      - (1/2)*(t^2*w^2*Aa + 2*(t^2*w*z*Bb) + t^2*z^2*Dd) := by
    simp only [hRm, hTayl]; ring
  have hξnorm (w z : ℝ) : ‖((-(t*w), -(t*z)) : ℝ × ℝ)‖^2 ≤ (2 * t^2) * (w^2 + z^2) := by
    rw [Prod.norm_def]
    simp only [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos ht0]
    have h1 : max (t*|w|) (t*|z|) ≤ t * (|w| + |z|) := by
      rw [max_le_iff]
      constructor <;> nlinarith [abs_nonneg w, abs_nonneg z, ht0.le]
    have h1nn : 0 ≤ max (t*|w|) (t*|z|) :=
      le_trans (by positivity) (le_max_left _ _)
    have h3 : (|w| + |z|)^2 ≤ 2 * (w^2 + z^2) := by
      nlinarith [sq_nonneg (|w| - |z|), sq_abs w, sq_abs z, abs_nonneg w, abs_nonneg z]
    have h2 : (t * (|w| + |z|))^2 ≤ 2 * t^2 * (w^2 + z^2) := by
      have h := mul_le_mul_of_nonneg_left h3 (sq_nonneg t)
      nlinarith [h]
    calc (max (t*|w|) (t*|z|))^2 ≤ (t * (|w| + |z|))^2 := by
          simpa [sq] using mul_self_le_mul_self h1nn h1
      _ ≤ 2 * t^2 * (w^2 + z^2) := h2
  have hRmb : ∀ w z : ℝ, |w| < 1 → |z| < 1 → |Rm w z| ≤ (2 * εt * t^2) * (w^2 + z^2) := by
    intro w z hw hz
    have hξ : ‖((-(t*w), -(t*z)) : ℝ × ℝ)‖ < δ0 := by
      rw [Prod.norm_def]
      simp only [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos ht0]
      rw [max_lt_iff]
      constructor
      · have h := mul_lt_mul_of_pos_left hw ht0
        rw [mul_one] at h
        linarith
      · have h := mul_lt_mul_of_pos_left hz ht0
        rw [mul_one] at h
        linarith
    have hkey := hδ0 (-(t*w), -(t*z)) hξ
    have hpt : p + (-(t*w), -(t*z)) = (x - t*w, y - t*z) := by
      rw [hp]; ext <;> simp [sub_eq_add_neg]
    rw [hpt, hlin w z, hquad w z] at hkey
    have hnn : ‖((-(t*w), -(t*z)) : ℝ × ℝ)‖^2 ≤ (2 * t^2) * (w^2 + z^2) := hξnorm w z
    have hfin : ‖F (x - t*w, y - t*z) - F p - ((-(t*w))*c1 + (-(t*z))*c2)
        - (1/2)*(t^2*w^2*Aa + 2*(t^2*w*z*Bb) + t^2*z^2*Dd)‖
        ≤ (2 * εt * t^2) * (w^2 + z^2) := by
      have h1 : εt * ‖((-(t*w), -(t*z)) : ℝ × ℝ)‖^2 ≤ εt * ((2 * t^2) * (w^2 + z^2)) :=
        mul_le_mul_of_nonneg_left hnn hεtpos.le
      rw [show (2 * εt * t^2) * (w^2 + z^2) = εt * (2 * t^2 * (w^2 + z^2)) by ring]
      exact hkey.trans h1
    rw [hTay_eq w z, ← Real.norm_eq_abs]
    exact hfin
  -- integrability of the Taylor part (inner) and its integral
  have hTint (w : ℝ) : Integrable (fun z : ℝ => sKerd 1 z * Tayl w z) := by
    have h := poly_intble (F p + (-(t*w))*c1 + (1/2)*(t^2*w^2*Aa))
      ((-(t))*c2 + (1/2)*(2*t^2*w*Bb)) ((1/2)*(t^2*Dd))
    refine h.congr ?_
    filter_upwards with z
    simp only [hTayl]
    ring
  have hTayl_eval (w : ℝ) :
      (∫ z : ℝ, sKerd 1 z * Tayl w z) = t*c2 - t^2*w*Bb + (1/2)*t^2*Dd*M2 := by
    have h := poly_int (F p + (-(t*w))*c1 + (1/2)*(t^2*w^2*Aa))
      ((-(t))*c2 + (1/2)*(2*t^2*w*Bb)) ((1/2)*(t^2*Dd))
    have heq : (fun z : ℝ => sKerd 1 z * Tayl w z)
        = fun z : ℝ => sKerd 1 z * ((F p + (-(t*w))*c1 + (1/2)*(t^2*w^2*Aa))
            + ((-(t))*c2 + (1/2)*(2*t^2*w*Bb)) * z + ((1/2)*(t^2*Dd)) * z^2) := by
      funext z; simp only [hTayl]; ring
    rw [heq, h, hM0v, hM1v]
    ring
  -- continuity of the `F`-pullback on the box
  have hbox_cont (w : ℝ) (hw : |w| < 1) :
      ContinuousOn (fun z : ℝ => F (x - t*w, y - t*z)) (Set.Icc (-1:ℝ) 1) := by
    have himg : Set.MapsTo (fun z : ℝ => ((x - t*w), (y - t*z))) (Set.Icc (-1:ℝ) 1) (Metric.ball p r) := by
      intro z hz
      have hzw : |z| ≤ 1 := abs_le.mpr hz
      rw [Metric.mem_ball, dist_eq_norm, Prod.norm_def, hp]
      simp only [Prod.fst_sub, Prod.snd_sub, sub_self, sub_zero, Real.norm_eq_abs]
      rw [max_lt_iff]
      constructor
      · rw [show x - t*w - x = -(t*w) by ring, abs_neg, abs_mul, abs_of_pos ht0]
        have h := mul_lt_mul_of_pos_left hw ht0
        rw [mul_one] at h
        linarith
      · rw [show y - t*z - y = -(t*z) by ring, abs_neg, abs_mul, abs_of_pos ht0]
        nlinarith [abs_nonneg z, ht0, htr]
    have hmap : ContinuousOn (fun z : ℝ => ((x - t*w), (y - t*z))) (Set.Icc (-1:ℝ) 1) := by fun_prop
    have h2 := (hFcontU.mono hru).comp hmap himg
    simpa [Function.comp_def] using h2
  -- integrability of the remainder against η
  have hRint (w : ℝ) (hw : |w| < 1) : Integrable (fun z : ℝ => sKerd 1 z * Rm w z) := by
    have hdom : Integrable (fun z : ℝ => |sKerd 1 z| * ((2 * εt * t^2) * (w^2 + z^2))) := by
      have heq : (fun z : ℝ => |sKerd 1 z| * ((2 * εt * t^2) * (w^2 + z^2)))
          = fun z : ℝ => ((2 * εt * t^2) * w^2) * |sKerd 1 z| + (2 * εt * t^2) * (z^2 * |sKerd 1 z|) := by
        funext z; ring
      rw [heq]
      exact (hA0int.const_mul _).add (hA2int.const_mul _)
    refine Integrable.mono' hdom ?_ ?_
    · have hcontOn' : ContinuousOn (fun z : ℝ => sKerd 1 z * (F (x - t*w, y - t*z) - Tayl w z))
          (Set.Icc (-1:ℝ) 1) :=
        hηcont.continuousOn.mul ((hbox_cont w hw).sub (by simp only [hTayl]; fun_prop))
      have hcontOn : ContinuousOn (fun z : ℝ => sKerd 1 z * Rm w z) (Set.Icc (-1:ℝ) 1) := by
        have hEq : (fun z : ℝ => sKerd 1 z * Rm w z)
            = fun z : ℝ => sKerd 1 z * (F (x - t*w, y - t*z) - Tayl w z) := by
          funext z; simp only [hRm]
        rw [hEq]; exact hcontOn'
      have h1 : AEStronglyMeasurable
          (Set.indicator (Set.Icc (-1:ℝ) 1) (fun z : ℝ => sKerd 1 z * Rm w z)) volume :=
        (aestronglyMeasurable_indicator_iff measurableSet_Icc).mpr
          (hcontOn.aestronglyMeasurable (μ := volume) measurableSet_Icc)
      refine h1.congr ?_
      filter_upwards with z
      by_cases hz : z ∈ Set.Icc (-1:ℝ) 1
      · rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz, hηvan z (one_le_abs_of_notMem_Icc hz), zero_mul]
    · filter_upwards with z
      by_cases hz : |z| < 1
      · rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hRmb w z hw hz) (abs_nonneg _)
      · rw [hηvan z (not_lt.mp hz), zero_mul, norm_zero]
        exact mul_nonneg (abs_nonneg _) (by positivity)
  -- inner decomposition and the inner bound
  have hinner_eq (w : ℝ) (hw : |w| < 1) :
      (∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z))
        = (∫ z : ℝ, sKerd 1 z * Tayl w z) + (∫ z : ℝ, sKerd 1 z * Rm w z) := by
    have hpt : (∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z))
        = ∫ z : ℝ, sKerd 1 z * Tayl w z + sKerd 1 z * Rm w z := by
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [hRm]; ring
    rw [hpt]
    simpa using MeasureTheory.integral_add (hTint w) (hRint w hw)
  have hRmIn (w : ℝ) (hw : |w| < 1) :
      ‖∫ z : ℝ, sKerd 1 z * Rm w z‖ ≤ (2 * εt * t^2) * (A0 * w^2 + A2) := by
    have hdom : Integrable (fun z : ℝ => |sKerd 1 z| * ((2 * εt * t^2) * (w^2 + z^2))) := by
      have heq : (fun z : ℝ => |sKerd 1 z| * ((2 * εt * t^2) * (w^2 + z^2)))
          = fun z : ℝ => ((2 * εt * t^2) * w^2) * |sKerd 1 z| + (2 * εt * t^2) * (z^2 * |sKerd 1 z|) := by
        funext z; ring
      rw [heq]
      exact (hA0int.const_mul _).add (hA2int.const_mul _)
    calc ‖∫ z : ℝ, sKerd 1 z * Rm w z‖
        ≤ ∫ z : ℝ, ‖sKerd 1 z * Rm w z‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ z : ℝ, |sKerd 1 z| * ((2 * εt * t^2) * (w^2 + z^2)) := by
          refine MeasureTheory.integral_mono_of_nonneg ?_ hdom ?_
          · filter_upwards with z; exact norm_nonneg _
          · filter_upwards with z
            by_cases hz : |z| < 1
            · rw [norm_mul, Real.norm_eq_abs]
              exact mul_le_mul_of_nonneg_left (hRmb w z hw hz) (abs_nonneg _)
            · rw [hηvan z (not_lt.mp hz), zero_mul, norm_zero]
              exact mul_nonneg (abs_nonneg _) (by positivity)
      _ = (2 * εt * t^2) * (A0 * w^2 + A2) := by
          rw [show (fun z : ℝ => |sKerd 1 z| * ((2 * εt * t^2) * (w^2 + z^2)))
              = fun z : ℝ => ((2 * εt * t^2) * w^2) * |sKerd 1 z| + (2 * εt * t^2) * (z^2 * |sKerd 1 z|) from by
                funext z; ring]
          rw [MeasureTheory.integral_add (hA0int.const_mul _) (hA2int.const_mul _),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, ← hA0, ← hA2]
          ring
  -- continuity on the square, measurability of the pair function
  have hsq_cont : ContinuousOn (fun q : ℝ × ℝ => F (x - t*q.1, y - t*q.2))
      (Set.Icc (-1:ℝ) 1 ×ˢ Set.Icc (-1:ℝ) 1) := by
    have himg : Set.MapsTo (fun q : ℝ × ℝ => ((x - t*q.1), (y - t*q.2)))
        (Set.Icc (-1:ℝ) 1 ×ˢ Set.Icc (-1:ℝ) 1) (Metric.ball p r) := by
      intro q hq
      rw [Set.mem_prod] at hq
      rw [Metric.mem_ball, dist_eq_norm, Prod.norm_def, hp]
      simp only [Prod.fst_sub, Prod.snd_sub, sub_self, sub_zero, Real.norm_eq_abs]
      rw [max_lt_iff]
      constructor
      · rw [show x - t*q.1 - x = -(t*q.1) by ring, abs_neg, abs_mul, abs_of_pos ht0]
        have hq1 : |q.1| ≤ 1 := abs_le.mpr hq.1
        nlinarith [abs_nonneg q.1, ht0, htr]
      · rw [show y - t*q.2 - y = -(t*q.2) by ring, abs_neg, abs_mul, abs_of_pos ht0]
        have hq2 : |q.2| ≤ 1 := abs_le.mpr hq.2
        nlinarith [abs_nonneg q.2, ht0, htr]
    have hmap : ContinuousOn (fun q : ℝ × ℝ => ((x - t*q.1), (y - t*q.2)))
        (Set.Icc (-1:ℝ) 1 ×ˢ Set.Icc (-1:ℝ) 1) := by fun_prop
    have h2 := (hFcontU.mono hru).comp hmap himg
    simpa [Function.comp_def] using h2
  have hpair_meas : AEStronglyMeasurable
      (fun q : ℝ × ℝ => sKerd 1 q.1 * (sKerd 1 q.2 * Rm q.1 q.2)) (volume.prod volume) := by
    have hcont : ContinuousOn (fun q : ℝ × ℝ => sKerd 1 q.1 * (sKerd 1 q.2 * Rm q.1 q.2))
        (Set.Icc (-1:ℝ) 1 ×ˢ Set.Icc (-1:ℝ) 1) := by
      refine ContinuousOn.mul ((hηcont.comp continuous_fst).continuousOn) ?_
      refine ContinuousOn.mul ((hηcont.comp continuous_snd).continuousOn) ?_
      have hRmq : (fun q : ℝ × ℝ => Rm q.1 q.2)
          = fun q : ℝ × ℝ => F (x - t*q.1, y - t*q.2) - Tayl q.1 q.2 := by
        funext q; simp only [hRm]
      rw [hRmq]
      exact hsq_cont.sub (by simp only [hTayl]; fun_prop)
    have h1 : AEStronglyMeasurable
        (Set.indicator (Set.Icc (-1:ℝ) 1 ×ˢ Set.Icc (-1:ℝ) 1)
          (fun q : ℝ × ℝ => sKerd 1 q.1 * (sKerd 1 q.2 * Rm q.1 q.2))) (volume.prod volume) :=
      (aestronglyMeasurable_indicator_iff (measurableSet_Icc.prod measurableSet_Icc)).mpr
        (hcont.aestronglyMeasurable (μ := volume.prod volume) (measurableSet_Icc.prod measurableSet_Icc))
    refine h1.congr ?_
    filter_upwards with q
    by_cases hq : q ∈ Set.Icc (-1:ℝ) 1 ×ˢ Set.Icc (-1:ℝ) 1
    · rw [Set.indicator_of_mem hq]
    · rw [Set.indicator_of_notMem hq]
      rw [Set.mem_prod] at hq
      by_cases hq1 : q.1 ∈ Set.Icc (-1:ℝ) 1
      · have hq2 : q.2 ∉ Set.Icc (-1:ℝ) 1 := fun hc => hq ⟨hq1, hc⟩
        have h1 : 1 ≤ |q.2| := one_le_abs_of_notMem_Icc hq2
        rw [hηvan q.2 h1]; ring
      · have h1 : 1 ≤ |q.1| := one_le_abs_of_notMem_Icc hq1
        rw [hηvan q.1 h1, zero_mul]
  -- integrability at the outer level
  have hTaylwint : Integrable (fun w : ℝ => sKerd 1 w * (t*c2 - t^2*w*Bb + (1/2)*t^2*Dd*M2)) := by
    have h := poly_intble (t*c2 + (1/2)*t^2*Dd*M2) (-(t^2*Bb)) 0
    have h' : Integrable (fun w : ℝ => sKerd 1 w * (t*c2 + (1/2)*t^2*Dd*M2 + -(t^2*Bb) * w)) := by
      simpa using h
    refine h'.congr ?_
    filter_upwards with w; ring
  have constD : Integrable (fun w : ℝ => |sKerd 1 w| * ((2 * εt * t^2) * (A0 * w^2 + A2))) := by
    have heq : (fun w : ℝ => |sKerd 1 w| * ((2 * εt * t^2) * (A0 * w^2 + A2)))
        = fun w : ℝ => ((2 * εt * t^2) * A0) * (w^2 * |sKerd 1 w|)
            + ((2 * εt * t^2) * A2) * |sKerd 1 w| := by
      funext w; ring
    rw [heq]
    exact (hA2int.const_mul _).add (hA0int.const_mul _)
  have hRwint : Integrable (fun w : ℝ => sKerd 1 w * (∫ z : ℝ, sKerd 1 z * Rm w z)) := by
    refine Integrable.mono' constD ?_ ?_
    · have hpi := hpair_meas.integral_prod_right' (μ := volume) (ν := volume)
      refine hpi.congr ?_
      filter_upwards with w
      rw [MeasureTheory.integral_const_mul]
    · filter_upwards with w
      by_cases hw : |w| < 1
      · rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hRmIn w hw) (abs_nonneg _)
      · rw [hηvan w (not_lt.mp hw), zero_mul, norm_zero]
        exact mul_nonneg (abs_nonneg _) (by positivity)
  have heval : (∫ w : ℝ, sKerd 1 w * (t*c2 - t^2*w*Bb + (1/2)*t^2*Dd*M2)) = t^2*Bb := by
    have h := poly_int (t*c2 + (1/2)*t^2*Dd*M2) (-(t^2*Bb)) 0
    have h' : (∫ w : ℝ, sKerd 1 w * (t*c2 + (1/2)*t^2*Dd*M2 + -(t^2*Bb) * w))
        = (t*c2 + (1/2)*t^2*Dd*M2) * M0 + (-(t^2*Bb)) * M1 := by
      simpa using h
    have heq : (fun w : ℝ => sKerd 1 w * (t*c2 - t^2*w*Bb + (1/2)*t^2*Dd*M2))
        = fun w : ℝ => sKerd 1 w * (t*c2 + (1/2)*t^2*Dd*M2 + -(t^2*Bb) * w) := by
      funext w; ring
    rw [heq, h', hM0v, hM1v]
    ring
  -- the decomposition
  have hdec : (∫ w : ℝ, sKerd 1 w * (∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z)))
      = t^2 * Bb + (∫ w : ℝ, sKerd 1 w * (∫ z : ℝ, sKerd 1 z * Rm w z)) := by
    have hpt : ∀ w : ℝ, sKerd 1 w * (∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z))
        = sKerd 1 w * (t*c2 - t^2*w*Bb + (1/2)*t^2*Dd*M2)
          + sKerd 1 w * (∫ z : ℝ, sKerd 1 z * Rm w z) := by
      intro w
      by_cases hw : |w| < 1
      · rw [hinner_eq w hw, hTayl_eval w]; ring
      · rw [hηvan w (not_lt.mp hw)]; ring
    have hmid : (∫ w : ℝ, sKerd 1 w * (∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z)))
        = ∫ w : ℝ, (sKerd 1 w * (t*c2 - t^2*w*Bb + (1/2)*t^2*Dd*M2)
            + sKerd 1 w * (∫ z : ℝ, sKerd 1 z * Rm w z)) :=
      MeasureTheory.integral_congr_ae (μ := volume) (Eventually.of_forall hpt)
    have hsplit : (∫ w : ℝ, (sKerd 1 w * (t*c2 - t^2*w*Bb + (1/2)*t^2*Dd*M2)
            + sKerd 1 w * (∫ z : ℝ, sKerd 1 z * Rm w z)))
        = (∫ w : ℝ, sKerd 1 w * (t*c2 - t^2*w*Bb + (1/2)*t^2*Dd*M2))
          + (∫ w : ℝ, sKerd 1 w * (∫ z : ℝ, sKerd 1 z * Rm w z)) := by
      simpa using MeasureTheory.integral_add hTaylwint hRwint
    rw [hmid, hsplit, heval]
  -- the outer bound
  have hRwbd : ‖∫ w : ℝ, sKerd 1 w * (∫ z : ℝ, sKerd 1 z * Rm w z)‖
      ≤ (2 * εt * t^2) * (2 * (A0 * A2)) := by
    calc ‖∫ w : ℝ, sKerd 1 w * (∫ z : ℝ, sKerd 1 z * Rm w z)‖
        ≤ ∫ w : ℝ, ‖sKerd 1 w * (∫ z : ℝ, sKerd 1 z * Rm w z)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ w : ℝ, |sKerd 1 w| * ((2 * εt * t^2) * (A0 * w^2 + A2)) := by
          refine MeasureTheory.integral_mono_of_nonneg ?_ constD ?_
          · filter_upwards with w; exact norm_nonneg _
          · filter_upwards with w
            by_cases hw : |w| < 1
            · rw [norm_mul, Real.norm_eq_abs]
              exact mul_le_mul_of_nonneg_left (hRmIn w hw) (abs_nonneg _)
            · rw [hηvan w (not_lt.mp hw), zero_mul, norm_zero]
              exact mul_nonneg (abs_nonneg _) (by positivity)
      _ = (2 * εt * t^2) * (2 * (A0 * A2)) := by
          rw [show (fun w : ℝ => |sKerd 1 w| * ((2 * εt * t^2) * (A0 * w^2 + A2)))
              = fun w : ℝ => ((2 * εt * t^2) * A0) * (w^2 * |sKerd 1 w|)
                  + ((2 * εt * t^2) * A2) * |sKerd 1 w| from by funext w; ring]
          rw [MeasureTheory.integral_add (hA2int.const_mul _) (hA0int.const_mul _),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, ← hA0, ← hA2]
          ring
  -- the scaling identity
  have hI1 : (∫ u : ℝ, sKerd t u * (∫ v : ℝ, sKerd t v * F (x-u, y-v)))
      = (1 / t^2) * ∫ w : ℝ, sKerd 1 w * (∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z)) := by
    have hs1 : (∫ u : ℝ, sKerd t u * (∫ v : ℝ, sKerd t v * F (x-u, y-v)))
        = (1/t) * ∫ w : ℝ, sKerd 1 w * (∫ v : ℝ, sKerd t v * F (x - t*w, y - v)) := by
      simpa using sKerd_scale_int ht0 hηscale (fun u => ∫ v : ℝ, sKerd t v * F (x-u, y-v))
    rw [hs1]
    have h2 : (∫ w : ℝ, sKerd 1 w * (∫ v : ℝ, sKerd t v * F (x - t*w, y - v)))
        = ∫ w : ℝ, sKerd 1 w * ((1/t) * ∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z)) := by
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      have hs2 : (∫ v : ℝ, sKerd t v * F (x - t*w, y - v))
          = (1/t) * ∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z) := by
        simpa using sKerd_scale_int ht0 hηscale (fun v => F (x - t*w, y - v))
      show sKerd 1 w * (∫ v : ℝ, sKerd t v * F (x - t*w, y - v))
        = sKerd 1 w * ((1/t) * ∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z))
      rw [hs2]
    rw [h2]
    have h2' : (∫ w : ℝ, sKerd 1 w * ((1/t) * ∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z)))
        = ∫ w : ℝ, (1/t) * (sKerd 1 w * (∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z))) := by
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      show sKerd 1 w * ((1/t) * (∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z)))
        = (1/t) * (sKerd 1 w * (∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z)))
      ring
    rw [h2']
    have h3 : (∫ w : ℝ, (1/t) * (sKerd 1 w * (∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z))))
        = (1/t) * ∫ w : ℝ, sKerd 1 w * (∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z)) := by
      simpa using MeasureTheory.integral_const_mul (1/t)
        (fun w : ℝ => sKerd 1 w * (∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z)))
    rw [h3]
    have hcomb : (1/t) * ((1/t) * ∫ w : ℝ, sKerd 1 w * (∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z)))
        = (1/t^2) * ∫ w : ℝ, sKerd 1 w * (∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z)) := by
      field_simp
    exact hcomb
  -- conclusion
  rw [hI1, hdec]
  have hfin : (1/t^2) * (t^2*Bb + (∫ w : ℝ, sKerd 1 w * (∫ z : ℝ, sKerd 1 z * Rm w z)))
      = Bb + (1/t^2) * (∫ w : ℝ, sKerd 1 w * (∫ z : ℝ, sKerd 1 z * Rm w z)) := by
    field_simp
  rw [hfin, dist_eq_norm, add_sub_cancel_left, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / t^2)]
  have hb : (1/t^2) * ‖∫ w : ℝ, sKerd 1 w * (∫ z : ℝ, sKerd 1 z * Rm w z)‖
      ≤ (1/t^2) * ((2 * εt * t^2) * (2 * (A0 * A2))) :=
    mul_le_mul_of_nonneg_left hRwbd (by positivity)
  have hA0A2 : 0 ≤ A0 * A2 := mul_nonneg hA0nn hA2nn
  refine lt_of_le_of_lt hb ?_
  have heq2 : (1/t^2) * ((2 * εt * t^2) * (2 * (A0 * A2))) = 4 * εt * (A0 * A2) := by
    field_simp
    ring
  rw [heq2]
  have hlt : 4 * (A0 * A2) / (2 * (4 * A0 * A2 + 1)) < 1 := by
    rw [div_lt_one (by linarith : (0:ℝ) < 2 * (4 * A0 * A2 + 1))]
    linarith
  have hkey : 4 * (ε / (2 * (4 * A0 * A2 + 1))) * (A0 * A2)
      = ε * (4 * (A0 * A2) / (2 * (4 * A0 * A2 + 1))) := by ring
  rw [hεt, hKc, hkey]
  calc ε * (4 * (A0 * A2) / (2 * (4 * A0 * A2 + 1))) < ε * 1 := mul_lt_mul_of_pos_left hlt hε
    _ = ε := by ring



end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.thMollTransfer2 =====
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

/-! ## Boundedness of the derivatives of the bump -/

/-- Change of variables `x ↦ c - x` on the line. -/
theorem integral_comp_sub_eq (F : ℝ → ℝ) (c : ℝ) : (∫ x : ℝ, F (c - x)) = ∫ x : ℝ, F x := by
  calc (∫ x : ℝ, F (c - x))
      = ∫ x : ℝ, (fun y : ℝ => F (-y)) (x - c) := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        show F (c - x) = F (-(x - c))
        rw [show -(x - c) = c - x by ring]
    _ = ∫ y : ℝ, F (-y) := MeasureTheory.integral_sub_right_eq_self (fun y : ℝ => F (-y)) c
    _ = ∫ y : ℝ, F y := integral_comp_neg_eq F

theorem hasDerivAt_sKer (ε : ℝ) (t : ℝ) : HasDerivAt (sKer ε) (deriv (sKer ε) t) t :=
  ((contDiff_sKer ε (n := 1)).differentiable (by norm_num)).differentiableAt.hasDerivAt

theorem continuous_deriv_sKer (ε : ℝ) : Continuous (deriv (sKer ε)) :=
  (contDiff_sKer ε (n := 2)).continuous_deriv (by norm_num)





/-- The first derivative of the bump vanishes off its support. -/
theorem deriv_sKer_eq_zero_of_lt_abs {ε t : ℝ} (hε : 0 < ε) (h : ε < |t|) :
    deriv (sKer ε) t = 0 := by
  have hev : sKer ε =ᶠ[𝓝 t] fun _ : ℝ => (0 : ℝ) := by
    rcases lt_or_ge (0 : ℝ) t with hpos | hnonpos
    · have htε : ε < t := by rwa [abs_of_pos hpos] at h
      filter_upwards [isOpen_Ioi.mem_nhds htε] with u hu
      have hu' : ε ≤ |u| := by
        rw [abs_of_pos (lt_trans hε hu)]
        exact le_of_lt hu
      exact sKer_eq_zero_of_le_abs hε hu'
    · have htε : t < -ε := by
        rw [abs_of_nonpos hnonpos] at h; linarith
      filter_upwards [isOpen_Iio.mem_nhds htε] with u hu
      have hu2 : u < -ε := hu
      have hu0 : u < 0 := by linarith
      have hu' : ε ≤ |u| := by
        rw [abs_of_neg hu0]; linarith
      exact sKer_eq_zero_of_le_abs hε hu'
  rw [Filter.EventuallyEq.deriv_eq hev]
  simp


/-- A continuous function vanishing off `[-ε, ε]` is bounded. -/
theorem exists_bound_of_vanishes_off {f : ℝ → ℝ} (hcont : Continuous f) {ε : ℝ}
    (hv : ∀ t : ℝ, ε < |t| → f t = 0) : ∃ C : ℝ, ∀ t : ℝ, |f t| ≤ C := by
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn (s := Set.Icc (-ε) ε)
    isCompact_Icc hcont.continuousOn
  refine ⟨max C 0, fun t => ?_⟩
  by_cases h : |t| ≤ ε
  · refine le_trans ?_ (le_max_left _ _)
    have ht : t ∈ Set.Icc (-ε) ε := by
      rw [Set.mem_Icc]
      exact abs_le.mp h
    simpa only [Real.norm_eq_abs] using hC t ht
  · rw [hv t (not_le.mp h), abs_zero]
    exact le_max_right _ _

theorem exists_bound_deriv_sKer {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ t : ℝ, |deriv (sKer ε) t| ≤ C :=
  exists_bound_of_vanishes_off (continuous_deriv_sKer ε)
    (fun t ht => deriv_sKer_eq_zero_of_lt_abs (t := t) hε ht)


/-! ## The fold of the angular mollification -/

/-- **The fold**: the whole-line convolution defining `thMoll` sees the slice only through the
three images of the doubly odd extension, i.e. through `Kern (sKer ε) θ'`. -/
theorem thMoll_fold {u : ℝ → ℝ → ℝ} {ε z θ' : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (h0 : u z 0 = 0) (hp : u z (Real.pi / 2) = 0)
    (hgc : ContinuousOn (fun s : ℝ => u z s) Iθ)
    (hθ'1 : -(1 / 4) < θ') (hθ'2 : θ' < Real.pi / 2 + 1 / 4) :
    thMoll u ε z θ' = ∫ s in Iθ, Kern (sKer ε) θ' s * u z s := by
  set g : ℝ → ℝ := fun s => u z s with hg
  have hGint : Integrable (Qcut g) := by
    have hgI : IntegrableOn g Iθ := by
      rw [hg]
      exact hgc.integrableOn_compact isCompact_Icc
    exact hgI.integrable_indicator measurableSet_Icc
  have hGneg : Integrable (fun s : ℝ => Qcut g (-s)) := hGint.comp_neg
  have hGpi : Integrable (fun s : ℝ => Qcut g (Real.pi - s)) := by
    have h2 := hGneg.comp_sub_right Real.pi
    refine h2.congr (Filter.Eventually.of_forall fun s => ?_)
    show Qcut g (-(s - Real.pi)) = Qcut g (Real.pi - s)
    rw [show -(s - Real.pi) = Real.pi - s by ring]
  have hI1 : Integrable (fun s : ℝ => sKer ε (θ' - s) * Qcut g s) :=
    integrable_sKer_mul_of_integrable hε hGint
  have hI2 : Integrable (fun s : ℝ => sKer ε (θ' - s) * Qcut g (-s)) :=
    integrable_sKer_mul_of_integrable hε hGneg
  have hI3 : Integrable (fun s : ℝ => sKer ε (θ' - s) * Qcut g (Real.pi - s)) :=
    integrable_sKer_mul_of_integrable hε hGpi
  -- the pointwise identity
  have hpt : ∀ s : ℝ, sKer ε (θ' - s) * Qext u z s
      = sKer ε (θ' - s) * (Qcut g s - Qcut g (-s) - Qcut g (Real.pi - s)) := by
    intro s
    rw [hg]
    exact Qext_eq_Qcut_combination hε hε1 h0 hp hθ'1 hθ'2
  -- the two change of variables
  have hsub2 : (∫ s : ℝ, sKer ε (θ' - s) * Qcut g (-s))
      = ∫ s : ℝ, sKer ε (θ' + s) * Qcut g s := by
    have hconv : (∫ s : ℝ, sKer ε (θ' - s) * Qcut g (-s))
        = ∫ s : ℝ, (fun u : ℝ => sKer ε (θ' + u) * Qcut g u) (-s) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      simp only [sub_eq_add_neg]
    rw [hconv, integral_comp_neg_eq (fun u : ℝ => sKer ε (θ' + u) * Qcut g u)]
  have hsub3 : (∫ s : ℝ, sKer ε (θ' - s) * Qcut g (Real.pi - s))
      = ∫ s : ℝ, sKer ε (θ' + s - Real.pi) * Qcut g s := by
    have hconv : (∫ s : ℝ, sKer ε (θ' - s) * Qcut g (Real.pi - s))
        = ∫ s : ℝ, (fun u : ℝ => sKer ε (θ' + u - Real.pi) * Qcut g u) (Real.pi - s) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      show sKer ε (θ' - s) * Qcut g (Real.pi - s)
        = sKer ε (θ' + (Real.pi - s) - Real.pi) * Qcut g (Real.pi - s)
      rw [show θ' + (Real.pi - s) - Real.pi = θ' - s by ring]
    rw [hconv, integral_comp_sub_eq (fun u : ℝ => sKer ε (θ' + u - Real.pi) * Qcut g u) Real.pi]
  -- integrability of the reflected pieces
  have hJ2 : Integrable (fun s : ℝ => sKer ε (θ' + s) * Qcut g s) := by
    have h := integrable_sKer_mul_of_integrable (ε := ε) (θ' := -θ') hε hGint
    refine h.congr (Filter.Eventually.of_forall fun s => ?_)
    show sKer ε (-θ' - s) * Qcut g s = sKer ε (θ' + s) * Qcut g s
    rw [show -θ' - s = -(θ' + s) by ring, sKer_even]
  have hJ3 : Integrable (fun s : ℝ => sKer ε (θ' + s - Real.pi) * Qcut g s) := by
    have h := integrable_sKer_mul_of_integrable (ε := ε) (θ' := Real.pi - θ') hε hGint
    refine h.congr (Filter.Eventually.of_forall fun s => ?_)
    show sKer ε ((Real.pi - θ') - s) * Qcut g s = sKer ε (θ' + s - Real.pi) * Qcut g s
    rw [show (Real.pi - θ') - s = -(θ' + s - Real.pi) by ring, sKer_even]
  -- assemble
  calc thMoll u ε z θ' = ∫ s : ℝ, sKer ε (θ' - s) * Qext u z s := rfl
    _ = ∫ s : ℝ, sKer ε (θ' - s) * (Qcut g s - Qcut g (-s) - Qcut g (Real.pi - s)) :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (∫ s : ℝ, sKer ε (θ' - s) * Qcut g s) - (∫ s : ℝ, sKer ε (θ' - s) * Qcut g (-s))
          - (∫ s : ℝ, sKer ε (θ' - s) * Qcut g (Real.pi - s)) := by
        have h1 : (∫ s : ℝ, sKer ε (θ' - s) * (Qcut g s - Qcut g (-s) - Qcut g (Real.pi - s)))
            = ∫ s : ℝ, (sKer ε (θ' - s) * Qcut g s - sKer ε (θ' - s) * Qcut g (-s)
                - sKer ε (θ' - s) * Qcut g (Real.pi - s)) := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
          ring
        rw [h1]
        rw [MeasureTheory.integral_sub
          (f := fun s : ℝ => sKer ε (θ' - s) * Qcut g s - sKer ε (θ' - s) * Qcut g (-s))
          (g := fun s : ℝ => sKer ε (θ' - s) * Qcut g (Real.pi - s)) (hI1.sub hI2) hI3]
        rw [MeasureTheory.integral_sub
          (f := fun s : ℝ => sKer ε (θ' - s) * Qcut g s)
          (g := fun s : ℝ => sKer ε (θ' - s) * Qcut g (-s)) hI1 hI2]
    _ = (∫ s : ℝ, sKer ε (θ' - s) * Qcut g s) - (∫ s : ℝ, sKer ε (θ' + s) * Qcut g s)
          - (∫ s : ℝ, sKer ε (θ' + s - Real.pi) * Qcut g s) := by rw [hsub2, hsub3]
    _ = ∫ s : ℝ, Kern (sKer ε) θ' s * Qcut g s := by
        rw [← MeasureTheory.integral_sub
          (f := fun s : ℝ => sKer ε (θ' - s) * Qcut g s)
          (g := fun s : ℝ => sKer ε (θ' + s) * Qcut g s) hI1 hJ2]
        rw [← MeasureTheory.integral_sub
          (f := fun s : ℝ => sKer ε (θ' - s) * Qcut g s - sKer ε (θ' + s) * Qcut g s)
          (g := fun s : ℝ => sKer ε (θ' + s - Real.pi) * Qcut g s) (hI1.sub hJ2) hJ3]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
        show sKer ε (θ' - s) * Qcut g s - sKer ε (θ' + s) * Qcut g s
              - sKer ε (θ' + s - Real.pi) * Qcut g s
            = (sKer ε (θ' - s) - sKer ε (θ' + s) - sKer ε (θ' + s - Real.pi)) * Qcut g s
        ring
    _ = ∫ s in Iθ, Kern (sKer ε) θ' s * u z s := by
        show (∫ s : ℝ, Kern (sKer ε) θ' s * Qcut g s)
          = ∫ s in Iθ, Kern (sKer ε) θ' s * g s
        exact integral_mul_Qcut (fun s : ℝ => Kern (sKer ε) θ' s) g


end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgGo =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The three fields that come from the class -/

theorem EllResid_at_zero {α : ℝ} {g Ψ : Fn} (h : EllClassO α g Ψ) (z : ℝ) :
    Work.Elliptic.EllResid α g Ψ z 0 = 0 := by
  rw [Work.Elliptic.EllResid]
  simp [h.sol.2.1 z]

theorem EllResid_at_pi_half {α : ℝ} {g Ψ : Fn} (h : EllClassO α g Ψ) (z : ℝ) :
    Work.Elliptic.EllResid α g Ψ z (π / 2) = 0 := by
  rw [Work.Elliptic.EllResid]
  simp only [show (2 : ℝ) * (π / 2) = π by ring, Real.sin_pi]
  simp [h.sol.2.2.1 z]

/-- `∂_z` of a function vanishing identically on an angular boundary vanishes there. -/
theorem pz_eq_zero_of_forall_eq_zero {f : Fn} {θ₀ : ℝ} (h : ∀ z, f z θ₀ = 0) (z : ℝ) :
    Work.Spaces.pz f z θ₀ = 0 := by
  have hfun : (fun z' : ℝ => f z' θ₀) = fun _ => (0 : ℝ) := funext h
  simp only [Work.Spaces.pz, hfun]
  exact deriv_const z (0 : ℝ)


/-! ## The assembly of item (d) -/


end Work.FTS.EllSol
end
end
-- ===== merged: Submission.Work.FTS.EllSol.FlatFT.niceFlatSliceL2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.FlatFT

theorem niceFlatSliceL2 (g : ℝ → ℝ → ℝ) (hg : Work.FTS.EllSol.FlatFT.NiceFlat g) {θ₁ : ℝ}
    (hθ₁ : θ₁ ∈ Set.Ioo 0 (Real.pi / 2)) :
    MeasureTheory.Integrable (fun z : ℝ => (g z θ₁) ^ 2) ∧
      MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.pth g z θ₁) ^ 2) := by
  obtain ⟨hsm, h0, hπ, N, hN⟩ := hg
  have hU : IsOpen ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    isOpen_univ.prod isOpen_Ioo
  -- a point outside `[-N,N]` satisfies `N < |z|`, where `g` vanishes identically
  have hmem : ∀ z : ℝ, z ∉ Set.Icc (-N) N → N < |z| := by
    intro z hz
    exact not_le.mp (fun h => hz (abs_le.mp h))
  -- the `z`-slices of `g` and of `∂_θ g` at the fixed interior angle `θ₁` are continuous
  have hslice_cont : Continuous (fun z : ℝ => g z θ₁) := by
    have h1 : ContDiffOn ℝ 2 (fun z : ℝ => (z, θ₁)) Set.univ := by fun_prop
    have h2 := hsm.comp h1 (fun z _ => ⟨trivial, hθ₁⟩)
    have h3 : ContDiffOn ℝ 2 (fun z : ℝ => g z θ₁) Set.univ := by
      simpa [Function.comp_def, Function.uncurry] using h2
    simpa [continuousOn_univ] using h3.continuousOn
  have hpth_cont : Continuous (fun z : ℝ => Work.Spaces.pth g z θ₁) := by
    have hfd : ContinuousOn
        (fun p : ℝ × ℝ =>
          fderivWithin ℝ (Function.uncurry g) ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) p)
        ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      hsm.continuousOn_fderivWithin hU.uniqueDiffOn (by norm_num)
    have hcomp : Continuous
        ((fun p : ℝ × ℝ =>
            fderivWithin ℝ (Function.uncurry g) ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) p)
          ∘ (fun z : ℝ => (z, θ₁))) :=
      hfd.comp_continuous (by fun_prop) (fun z => ⟨trivial, hθ₁⟩)
    have hcl : Continuous (fun z : ℝ =>
        fderivWithin ℝ (Function.uncurry g) ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))
          (z, θ₁) (0, 1)) :=
      hcomp.clm_apply continuous_const
    refine hcl.congr (fun z => ?_)
    have hd : DifferentiableAt ℝ (Function.uncurry g) (z, θ₁) :=
      (hsm.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds ⟨trivial, hθ₁⟩)
    rw [fderivWithin_of_isOpen hU ⟨trivial, hθ₁⟩]
    exact (Work.Spaces.pth_eq_fderiv hd).symm
  -- both slices are supported in `[-N,N]`
  refine ⟨?_, ?_⟩
  · exact ((hslice_cont.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (K := Set.Icc (-N) N) isCompact_Icc
        (fun z hz => by simp [hN z θ₁ (hmem z hz)]))
  · exact ((hpth_cont.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (K := Set.Icc (-N) N) isCompact_Icc
        (fun z hz => by
          simp [Work.Spaces.pth, show (fun θ' : ℝ => g z θ') = fun _ : ℝ => (0 : ℝ) from
            funext (fun θ' => hN z θ' (hmem z hz))]))

end Work.FTS.EllSol.FlatFT
end
-- ===== merged: Submission.Work.FTS.EllSol.FlatFT.shiftPlancherel1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.FlatFT

open MeasureTheory
open scoped Real

namespace Work.FTS.EllSol.FlatFT

/-- The squared modulus of the *shifted* Fourier multiplier `2πIξ - b`: the two summands `-b`
and `2πξ·I` of `2πIξ - b` are orthogonal, so there is no cross term,
`‖(2πIξ - b)F‖² = ((2πξ)² + b²)·‖F‖²`. -/
private theorem norm_sq_mul_shift (F : ℂ) (b ξ : ℝ) :
    ‖(2 * Real.pi * Complex.I * ξ - (b : ℂ)) * F‖ ^ 2
      = ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖F‖ ^ 2 := by
  rw [norm_mul, mul_pow]
  congr 1
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hre : (2 * Real.pi * Complex.I * ξ - (b : ℂ)).re = -b := by simp
  have him : (2 * Real.pi * Complex.I * ξ - (b : ℂ)).im = 2 * Real.pi * ξ := by simp
  rw [hre, him]
  ring

/-- Linearity of the `t`-Fourier slice `slice1` in its argument, for a difference of a constant
multiple: `slice1 (f - c·g) ξ = slice1 f ξ - c·slice1 g ξ`.  All the integrals involved are
absolutely convergent because `f` and `g` are continuous with compact support while the
exponential factor has modulus one. -/
private theorem slice1_sub_const_mul' (f g : ℝ → ℂ) (c : ℂ) (hf : Continuous f)
    (hfs : HasCompactSupport f) (hg : Continuous g) (hgs : HasCompactSupport g) (ξ : ℝ) :
    slice1 (fun t => f t - c * g t) ξ = slice1 f ξ - c * slice1 g ξ := by
  set κ : ℝ → ℂ := fun t => Complex.exp (-(2 * Real.pi * Complex.I * ξ * t)) with hκ
  have hκc : Continuous κ := by rw [hκ]; fun_prop
  have hfs' : HasCompactSupport (fun t => f t * κ t) :=
    hfs.mono (fun t ht => by
      intro h0
      exact ht (by simp [h0]))
  have hgs' : HasCompactSupport (fun t => g t * κ t) :=
    hgs.mono (fun t ht => by
      intro h0
      exact ht (by simp [h0]))
  have h1 : Integrable (fun t => f t * κ t) :=
    (hf.mul hκc).integrable_of_hasCompactSupport hfs'
  have h2 : Integrable (fun t => g t * κ t) :=
    (hg.mul hκc).integrable_of_hasCompactSupport hgs'
  have h3 : Integrable (fun t => c * (g t * κ t)) := h2.const_mul c
  calc slice1 (fun t => f t - c * g t) ξ
      = ∫ t, (f t - c * g t) * κ t := rfl
    _ = ∫ t, (f t * κ t - c * (g t * κ t)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        ring
    _ = (∫ t, f t * κ t) - ∫ t, c * (g t * κ t) := integral_sub h1 h3
    _ = (∫ t, f t * κ t) - c * ∫ t, g t * κ t := by rw [integral_const_mul]
    _ = slice1 f ξ - c * slice1 g ξ := rfl

/-- Shifted first-order Plancherel for the `t`-Fourier slice.  All helper lemmas in the file
should be `private` (the file's public interface is this one theorem). -/
theorem shiftPlancherel1 {h : ℝ → ℂ} (hh : ContDiff ℝ 1 h) (hs : HasCompactSupport h) (b : ℝ) :
    MeasureTheory.Integrable
      (fun ξ : ℝ => ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖slice1 h ξ‖ ^ 2) ∧
    (∫ ξ : ℝ, ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖slice1 h ξ‖ ^ 2
      = ∫ t : ℝ, ‖deriv h t - b * h t‖ ^ 2) := by
  -- The shifted profile `g = h' - b·h` is continuous with compact support, and its Fourier
  -- slice is `(2πIξ - b)·slice1 h ξ`, whose squared modulus is `((2πξ)² + b²)‖slice1 h ξ‖²`.
  have hb : HasCompactSupport (fun t : ℝ => (b : ℂ) * h t) :=
    hs.mono (fun t ht => by
      intro h0
      exact ht (by simp [h0]))
  have gcont : Continuous (fun t : ℝ => deriv h t - (b : ℂ) * h t) :=
    hh.continuous_deriv_one.sub (hh.continuous.const_mul b)
  have gsupp : HasCompactSupport (fun t : ℝ => deriv h t - (b : ℂ) * h t) :=
    hs.deriv.sub hb
  have key : ∀ ξ : ℝ, ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖slice1 h ξ‖ ^ 2
      = ‖slice1 (fun t : ℝ => deriv h t - (b : ℂ) * h t) ξ‖ ^ 2 := by
    intro ξ
    rw [slice1_sub_const_mul' (deriv h) h (b : ℂ) hh.continuous_deriv_one hs.deriv
      hh.continuous hs ξ, slice1_deriv h hh hs ξ, ← sub_mul, norm_sq_mul_shift]
  constructor
  · exact (integrable_normSq_slice1 gcont gsupp).congr
      (Filter.Eventually.of_forall fun ξ => (key ξ).symm)
  · calc ∫ ξ : ℝ, ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖slice1 h ξ‖ ^ 2
        = ∫ ξ : ℝ, ‖slice1 (fun t : ℝ => deriv h t - (b : ℂ) * h t) ξ‖ ^ 2 :=
          integral_congr_ae (Filter.Eventually.of_forall key)
      _ = ∫ t : ℝ, ‖deriv h t - (b : ℂ) * h t‖ ^ 2 :=
          plancherelSlice1 (fun t : ℝ => deriv h t - (b : ℂ) * h t) gcont gsupp

end Work.FTS.EllSol.FlatFT

/-- Shifted first-order Plancherel for the `t`-Fourier slice, under the name requested for this
module (the statement above sits inside a doubly-opened `Work.FTS.EllSol.FlatFT` namespace, this
is the same theorem with the usual fully-qualified name). -/
theorem shiftPlancherel1 {h : ℝ → ℂ} (hh : ContDiff ℝ 1 h) (hs : HasCompactSupport h) (b : ℝ) :
    MeasureTheory.Integrable
      (fun ξ : ℝ => ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖slice1 h ξ‖ ^ 2) ∧
    (∫ ξ : ℝ, ((2 * Real.pi * ξ) ^ 2 + b ^ 2) * ‖slice1 h ξ‖ ^ 2
      = ∫ t : ℝ, ‖deriv h t - b * h t‖ ^ 2) :=
  Work.FTS.EllSol.FlatFT.Work.FTS.EllSol.FlatFT.shiftPlancherel1 hh hs b

end Work.FTS.EllSol.FlatFT
end
-- ===== merged: Submission.Work.FTS.EllSol.FlatFT.sliceFunBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The slice bound `∫ g²σ ≤ (2(π/2)∫(∂_θg)²σ + 2g(θ₁)²)·∫σ`

For a function `g` of class `C²` on the open strip `ℝ × (0,π/2)` and a point
`θ₁ ∈ (0,π/2)` the θ-slice `θ ↦ g z θ` is controlled by its derivative:

  `∫_{Iθ} (g z θ)² sin(2θ)^{-η} ≤ (2(π/2)∫_{Iθ}(∂_θg z θ)² sin(2θ)^{-η} + 2(g z θ₁)²)·∫_{Iθ}sin(2θ)^{-η}`

`(η = 99/100)`, provided the derivative slot is finite.  This is the zeroth-order member of the
chain `sliceFunBound → slicePthBound → …` and the `θ`-companion of the `z`-slice bounds of
`Submission/Work/FTS/EllSol/FlatFT/`.

The proof is the elementary "fundamental theorem of calculus + Cauchy–Schwarz" step, with the
*point* `θ₁` as the reference value:

* `g z θ - g z θ₁ = ∫_{θ₁}^{θ} ∂_θg z` (FTC on the open interval, where the slice is `C²`);
* hence `|g z θ - g z θ₁| ≤ ∫_{Iθ}|∂_θg z| =: S`, because `[θ₁,θ]` lies in `Iθ`;
* `S² ≤ (π/2)∫_{Iθ}(∂_θg z)² ≤ (π/2)∫_{Iθ}(∂_θg z)²sin(2θ)^{-η}` by Cauchy–Schwarz on `Iθ`
  (`Work.Blocks.IMC.cs_integral_mul_le`) and `sin(2θ)^{-η} ≥ 1` on the open interval;
* `(x+y)² ≤ 2x² + 2y²` and `|θ - θ₁| ≤ π/2` produce the stated constants.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

namespace Work.FTS.EllSol.FlatFT

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

/-- **Weighted Cauchy–Schwarz on the angular interval.**  For a function of class `C²` on
`(0,π/2)` whose weighted derivative slot is finite, the total mass of `|∂_θf|` is finite and

  `(∫_{Iθ} |∂_θf|)² ≤ (π/2) · ∫_{Iθ} (∂_θf)² sin(2θ)^{-η}`.

(`η = 99/100`; the weight is `≥ 1` on the open interval, so the weighted slot dominates the
plain one, and Cauchy–Schwarz on `Iθ` costs exactly the length `π/2`.) -/
private lemma sliceCS_deriv (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun t : ℝ => |deriv f t|) Work.Spaces.Iθ ∧
      (∫ t in Work.Spaces.Iθ, |deriv f t|) ^ 2
        ≤ (Real.pi / 2) * ∫ t in Work.Spaces.Iθ, (deriv f t) ^ 2
            * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)) := by
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := by rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  -- the weight is `≥ 1` off the two endpoints
  have hone_le : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    intro θ hθ
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have h := Real.rpow_le_rpow_of_nonpos (z := -(Work.Spaces.eta)) hsin
      (Real.sin_le_one (2 * θ)) (by norm_num [Work.Spaces.eta])
    rwa [Real.one_rpow] at h
  have hcont : ContinuousOn (fun t => deriv f t) (Set.Ioo 0 (Real.pi / 2)) :=
    (hf.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).continuousOn
  -- the plain squared-derivative slot is finite
  have hP2 : IntegrableOn (fun t : ℝ => (deriv f t) ^ 2) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' hint
      (Work.FTS.EllSol.aesm_of_continuousOn_Ioo (hcont.pow 2)) ?_
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    show ‖(deriv f θ) ^ 2‖ ≤ (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact le_mul_of_one_le_right (sq_nonneg _) (hone_le θ hθ)
  -- and so is the absolute first-derivative slot, by `|x| ≤ x² + 1/4`
  have habs : IntegrableOn (fun t : ℝ => |deriv f t|) Work.Spaces.Iθ := by
    have hconst : IntegrableOn (fun _ : ℝ => (1/4 : ℝ)) Work.Spaces.Iθ :=
      MeasureTheory.integrableOn_const
        (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
    refine MeasureTheory.Integrable.mono' (hP2.add hconst)
      (Work.FTS.EllSol.aesm_of_continuousOn_Ioo (hcont.abs)) ?_
    refine Eventually.of_forall (fun θ => ?_)
    have := Work.FTS.EllSol.abs_le_sq_add_quarter (deriv f θ)
    simpa only [Pi.add_apply, Real.norm_eq_abs, abs_abs] using this
  refine ⟨habs, ?_⟩
  have hSnn : 0 ≤ ∫ t in Work.Spaces.Iθ, |deriv f t| :=
    MeasureTheory.setIntegral_nonneg hIθ_meas (fun t _ => abs_nonneg _)
  have hXnn : 0 ≤ ∫ t in Work.Spaces.Iθ, (deriv f t) ^ 2 :=
    MeasureTheory.setIntegral_nonneg hIθ_meas (fun t _ => sq_nonneg _)
  have hvol : (∫ _ in Work.Spaces.Iθ, (1:ℝ)) = Real.pi / 2 := by
    have hvol : volume.real Work.Spaces.Iθ = Real.pi / 2 := by
      rw [MeasureTheory.measureReal_def, Work.Spaces.Iθ, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
      ring
    rw [MeasureTheory.setIntegral_const, hvol]; simp
  -- Cauchy–Schwarz: `(∫|f'|)² ≤ (∫(f')²)(∫1)`
  have hcs := Work.Blocks.IMC.cs_integral_mul_le (volume.restrict Work.Spaces.Iθ)
    (f := fun t : ℝ => |deriv f t|) (g := fun _ : ℝ => (1:ℝ))
    (habs.aestronglyMeasurable) aestronglyMeasurable_const
    (by simpa only [sq_abs, MeasureTheory.IntegrableOn] using hP2)
    (by simpa using (integrable_const (1:ℝ) :
      Integrable (fun _ : ℝ => (1:ℝ)) (volume.restrict Work.Spaces.Iθ)))
  simp only [mul_one] at hcs
  have h1 : (∫ x in Work.Spaces.Iθ, |deriv f x| ^ 2)
      = (∫ x in Work.Spaces.Iθ, (deriv f x) ^ 2) :=
    MeasureTheory.setIntegral_congr_fun hIθ_meas (fun x _ => sq_abs (deriv f x))
  rw [h1] at hcs
  simp only [one_pow] at hcs
  have hkey : (∫ t in Work.Spaces.Iθ, |deriv f t|) ^ 2 ≤
      (∫ t in Work.Spaces.Iθ, (deriv f t) ^ 2) * (Real.pi / 2) := by
    calc (∫ t in Work.Spaces.Iθ, |deriv f t|) ^ 2
        ≤ (Real.sqrt (∫ t in Work.Spaces.Iθ, (deriv f t)^2) * Real.sqrt (Real.pi/2)) ^ 2 :=
          pow_le_pow_left₀ hSnn (by simpa only [abs_of_nonneg hSnn, hvol] using hcs) 2
      _ = (∫ t in Work.Spaces.Iθ, (deriv f t)^2) * (Real.pi/2) := by
          rw [mul_pow, Real.sq_sqrt hXnn, Real.sq_sqrt (by linarith [Real.pi_pos])]
  -- the weight is `≥ 1` on the open interval, so it can be inserted
  have hle : ∫ t in Work.Spaces.Iθ, (deriv f t) ^ 2 ≤
      ∫ t in Work.Spaces.Iθ, (deriv f t) ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)) := by
    refine MeasureTheory.integral_mono_ae hP2 hint
      (Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_))
    show (deriv f θ) ^ 2 ≤ (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    exact le_mul_of_one_le_right (sq_nonneg _) (hone_le θ hθ)
  calc (∫ t in Work.Spaces.Iθ, |deriv f t|) ^ 2
      ≤ (∫ t in Work.Spaces.Iθ, (deriv f t) ^ 2) * (Real.pi / 2) := hkey
    _ ≤ (∫ t in Work.Spaces.Iθ, (deriv f t) ^ 2
          * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta))) * (Real.pi / 2) :=
        mul_le_mul_of_nonneg_right hle (by linarith [Real.pi_pos])
    _ = (Real.pi / 2) * ∫ t in Work.Spaces.Iθ, (deriv f t) ^ 2
          * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)) := by ring

/-- **The fundamental-theorem-of-calculus slice bound.**  For a function of class `C¹` on
`(0,π/2)` with finite `L¹`-mass of `|∂_θf|`,

  `|f θ - f θ₁| ≤ ∫_{Iθ} |∂_θf|`  for all `θ, θ₁ ∈ (0,π/2)`.

The two cases `θ₁ ≤ θ` and `θ ≤ θ₁` are handled by the FTC
`intervalIntegral.integral_deriv_of_contDiffOn_Icc` on `Icc`, followed by monotonicity of the
set integral (the interval `[θ,θ₁]` is contained in `Iθ`). -/
private lemma sliceFTC_le (f : ℝ → ℝ) (hf : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn (fun t : ℝ => |deriv f t|) Work.Spaces.Iθ)
    {θ₁ θ : ℝ} (hθ₁ : θ₁ ∈ Set.Ioo 0 (Real.pi / 2)) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |f θ - f θ₁| ≤ ∫ t in Work.Spaces.Iθ, |deriv f t| := by
  rcases le_total θ₁ θ with hle | hle
  · have hcd : ContDiffOn ℝ 1 f (Set.Icc θ₁ θ) :=
      hf.mono (fun x hx => ⟨by linarith [hx.1, hθ₁.1], by linarith [hx.2, hθ.2]⟩)
    have hftc : ∫ t in θ₁..θ, deriv f t = f θ - f θ₁ :=
      intervalIntegral.integral_deriv_of_contDiffOn_Icc hcd hle
    have hmono : ∫ t in θ₁..θ, |deriv f t| ≤ ∫ t in Work.Spaces.Iθ, |deriv f t| := by
      rw [intervalIntegral.integral_of_le hle]
      refine MeasureTheory.setIntegral_mono_set hint (Eventually.of_forall (fun x => abs_nonneg _))
        (Eventually.of_forall ?_)
      intro x hx
      rw [Set.mem_Ioc] at hx
      exact ⟨by linarith [hx.1, hθ₁.1], by linarith [hx.2, hθ.2]⟩
    calc |f θ - f θ₁| = |∫ t in θ₁..θ, deriv f t| := by rw [hftc]
      _ ≤ ∫ t in θ₁..θ, |deriv f t| := intervalIntegral.abs_integral_le_integral_abs hle
      _ ≤ ∫ t in Work.Spaces.Iθ, |deriv f t| := hmono
  · have hcd : ContDiffOn ℝ 1 f (Set.Icc θ θ₁) :=
      hf.mono (fun x hx => ⟨by linarith [hx.1, hθ.1], by linarith [hx.2, hθ₁.2]⟩)
    have hftc : ∫ t in θ..θ₁, deriv f t = f θ₁ - f θ :=
      intervalIntegral.integral_deriv_of_contDiffOn_Icc hcd hle
    have hmono : ∫ t in θ..θ₁, |deriv f t| ≤ ∫ t in Work.Spaces.Iθ, |deriv f t| := by
      rw [intervalIntegral.integral_of_le hle]
      refine MeasureTheory.setIntegral_mono_set hint (Eventually.of_forall (fun x => abs_nonneg _))
        (Eventually.of_forall ?_)
      intro x hx
      rw [Set.mem_Ioc] at hx
      exact ⟨by linarith [hx.1, hθ.1], by linarith [hx.2, hθ₁.2]⟩
    have h2 : |f θ - f θ₁| = |∫ t in θ..θ₁, deriv f t| := by
      rw [hftc, abs_sub_comm]
    calc |f θ - f θ₁| = |∫ t in θ..θ₁, deriv f t| := h2
      _ ≤ ∫ t in θ..θ₁, |deriv f t| := intervalIntegral.abs_integral_le_integral_abs hle
      _ ≤ ∫ t in Work.Spaces.Iθ, |deriv f t| := hmono

theorem sliceFunBound (g : ℝ → ℝ → ℝ)
    (hg : ContDiffOn ℝ 2 (Function.uncurry g) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z θ₁ : ℝ} (hθ₁ : θ₁ ∈ Set.Ioo 0 (Real.pi / 2))
    (hint : MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.pth g z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (g z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        ≤ (2 * (Real.pi / 2) * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pth g z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            + 2 * (g z θ₁) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := by rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  -- the `θ`-slice at `z` is `C²` on the open angular interval
  have hf2 : ContDiffOn ℝ 2 (fun θ : ℝ => g z θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have hcurve : ContDiffOn ℝ 2 (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
    have h := hg.comp hcurve (fun θ hθ => ⟨Set.mem_univ z, hθ⟩)
    simpa [Function.comp_def, Function.uncurry] using h
  have hf1 : ContDiffOn ℝ 1 (fun θ : ℝ => g z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    hf2.of_le (m := 1) (by norm_num)
  -- the mass of `|∂_θg|` is finite, and its square is dominated by the weighted derivative slot
  obtain ⟨habs, hS2⟩ := sliceCS_deriv (fun θ : ℝ => g z θ) hf2 hint
  let A : ℝ := ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth g z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
  let B : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
  let S : ℝ := ∫ t in Work.Spaces.Iθ, |deriv (fun θ : ℝ => g z θ) t|
  have hS2' : S ^ 2 ≤ (Real.pi / 2) * A := hS2
  have hσnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    fun θ hθ => Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc (x := 2 * θ)
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _
  have hA_nonneg : 0 ≤ A :=
    MeasureTheory.setIntegral_nonneg hIθ_meas
      (fun θ hθ => mul_nonneg (sq_nonneg _) (hσnn θ hθ))
  -- the pointwise bound, on the open interval
  have hpoint : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        ≤ (2 * (Real.pi / 2) * A + 2 * (g z θ₁) ^ 2)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    intro θ hθ
    have hbd : (g z θ) ^ 2 ≤ 2 * (Real.pi / 2) * A + 2 * (g z θ₁) ^ 2 := by
      have hd : |g z θ - g z θ₁| ≤ S := sliceFTC_le (fun θ : ℝ => g z θ) hf1 habs hθ₁ hθ
      have h1 : (g z θ) ^ 2 ≤ (|g z θ₁| + S) ^ 2 := by
        have hbase : |g z θ| ≤ |g z θ₁| + S := by
          calc |g z θ| = |g z θ₁ + (g z θ - g z θ₁)| := by
                rw [show g z θ₁ + (g z θ - g z θ₁) = g z θ from by ring]
            _ ≤ |g z θ₁| + |g z θ - g z θ₁| := abs_add_le _ _
            _ ≤ |g z θ₁| + S := add_le_add (le_refl _) hd
        calc (g z θ) ^ 2 = |g z θ| ^ 2 := (sq_abs _).symm
          _ ≤ (|g z θ₁| + S) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hbase 2
      have h2 : (|g z θ₁| + S) ^ 2 ≤ 2 * (g z θ₁) ^ 2 + 2 * S ^ 2 := by
        nlinarith [two_mul_le_add_sq |g z θ₁| S, sq_abs (g z θ₁)]
      have h3 : 2 * S ^ 2 ≤ 2 * (Real.pi / 2) * A := by
        calc 2 * S ^ 2 ≤ 2 * ((Real.pi / 2) * A) := mul_le_mul_of_nonneg_left hS2' (by norm_num)
          _ = 2 * (Real.pi / 2) * A := by ring
      calc (g z θ) ^ 2 ≤ 2 * (g z θ₁) ^ 2 + 2 * S ^ 2 := le_trans h1 h2
        _ ≤ 2 * (g z θ₁) ^ 2 + 2 * (Real.pi / 2) * A := add_le_add (le_refl _) h3
        _ = 2 * (Real.pi / 2) * A + 2 * (g z θ₁) ^ 2 := by ring
    exact mul_le_mul_of_nonneg_right hbd (hσnn θ ⟨hθ.1.le, hθ.2.le⟩)
  -- integrability of the majorant
  have hσ_int : MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by norm_num [Work.Spaces.eta])
      (by norm_num [Work.Spaces.eta])).1
  have hK_int : MeasureTheory.IntegrableOn (fun θ : ℝ => (2 * (Real.pi / 2) * A + 2 * (g z θ₁) ^ 2)
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    MeasureTheory.Integrable.const_mul hσ_int (2 * (Real.pi / 2) * A + 2 * (g z θ₁) ^ 2)
  -- the integrand itself
  have hF_int : MeasureTheory.IntegrableOn (fun θ : ℝ => (g z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
    have hcontσ : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (Set.Ioo 0 (Real.pi / 2)) :=
      ContinuousOn.rpow_const
        (Real.continuous_sin.comp_continuousOn (continuousOn_const.mul continuousOn_id))
        (fun x hx => Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1])
          (by linarith [hx.2, Real.pi_pos]))))
    refine MeasureTheory.Integrable.mono' hK_int
      (Work.FTS.EllSol.aesm_of_continuousOn_Ioo ((hf1.continuousOn.pow 2).mul hcontσ)) ?_
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    have hp := hpoint θ hθ
    have hnn : 0 ≤ (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      mul_nonneg (sq_nonneg _) (hσnn θ ⟨hθ.1.le, hθ.2.le⟩)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hp
  refine ⟨hF_int, ?_⟩
  have hineq : ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ ∫ θ in Work.Spaces.Iθ, (2 * (Real.pi / 2) * A + 2 * (g z θ₁) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    MeasureTheory.integral_mono_ae hF_int hK_int
      (Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => hpoint θ hθ))
  calc ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ ∫ θ in Work.Spaces.Iθ, (2 * (Real.pi / 2) * A + 2 * (g z θ₁) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := hineq
    _ = (2 * (Real.pi / 2) * A + 2 * (g z θ₁) ^ 2) * B := by
        rw [MeasureTheory.integral_const_mul]
    _ = (2 * (Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth g z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            + 2 * (g z θ₁) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := rfl

end

end Work.FTS.EllSol.FlatFT
end
-- ===== merged: Submission.Work.FTS.EllSol.FlatFT.slicePthBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.FlatFT

open MeasureTheory Set Filter
open scoped Real Topology

/-! ## The slice bound -/

theorem slicePthBound (g : ℝ → ℝ → ℝ)
    (hg : ContDiffOn ℝ 2 (Function.uncurry g) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z θ₁ : ℝ} (hθ₁ : θ₁ ∈ Set.Ioo 0 (Real.pi / 2))
    (hint : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.pth (Work.Spaces.pth g) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.pth g z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth g z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        ≤ (2 * (Real.pi / 2) * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pth (Work.Spaces.pth g) z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            + 2 * (Work.Spaces.pth g z θ₁) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  -- The angular slice `F θ = g z θ` of the datum.
  set F : ℝ → ℝ := fun θ => g z θ with hF
  -- the weight is nonnegative on `Iθ`
  have hθI : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  -- ### smoothness of the slice
  have hF2 : ContDiffOn ℝ 2 F (Set.Ioo 0 (Real.pi / 2)) := by
    have hmap : ContDiffOn ℝ 2 (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
    have h := hg.comp hmap (fun θ hθ => ⟨Set.mem_univ θ, hθ⟩)
    simpa [hF, Function.comp_def, Function.uncurry] using h
  have hF1 : ContDiffOn ℝ 1 (deriv F) (Set.Ioo 0 (Real.pi / 2)) :=
    hF2.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  have hF0 : ContinuousOn (deriv (deriv F)) (Set.Ioo 0 (Real.pi / 2)) :=
    (hF1.deriv_of_isOpen isOpen_Ioo (m := 0) (by norm_num)).continuousOn
  -- ### the fundamental theorem of calculus on subintervals of `(0,π/2)`
  have hftc2 : ∀ {a b : ℝ}, a ∈ Set.Ioo 0 (Real.pi / 2) → b ∈ Set.Ioo 0 (Real.pi / 2) →
      a ≤ b → ∫ t in a..b, deriv (deriv F) t = deriv F b - deriv F a := by
    intro a b ha hb hab
    have hcd : ContDiffOn ℝ 1 (deriv F) (Set.Icc a b) :=
      hF1.mono (fun x hx => ⟨by linarith [hx.1, ha.1], by linarith [hx.2, hb.2]⟩)
    exact intervalIntegral.integral_deriv_of_contDiffOn_Icc hcd hab
  -- ### the mass of the second angular derivative
  set M : ℝ := ∫ t in Work.Spaces.Iθ,
      (deriv (deriv F) t) ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)) with hM
  have hMnn : 0 ≤ M := by
    rw [hM]
    refine MeasureTheory.setIntegral_nonneg (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc) ?_
    intro t ht
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hθI t ht) _)
  have hintF : MeasureTheory.IntegrableOn (fun t : ℝ =>
      (deriv (deriv F) t) ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ := by
    simpa only [Work.Spaces.pth, hF] using hint
  -- ### the pointwise bound on the slice
  have hpoint : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (deriv F θ) ^ 2 ≤ 2 * (Real.pi / 2) * M + 2 * (deriv F θ₁) ^ 2 := by
    intro θ hθ
    have hA : 0 ≤ (Real.pi / 2) * M := mul_nonneg (by positivity) hMnn
    have hdiff : |deriv F θ - deriv F θ₁| ≤ Real.sqrt ((Real.pi / 2) * M) := by
      rcases le_total θ₁ θ with hle | hle
      · have hftc := hftc2 hθ₁ hθ hle
        have hcs := sliceCSMass (u := fun t => deriv (deriv F) t) hθ₁ hθ hF0 hintF
        rw [hftc] at hcs
        have hcs' : (deriv F θ - deriv F θ₁) ^ 2 ≤ (Real.pi / 2) * M := hcs
        rw [← Real.sq_sqrt hA] at hcs'
        have := sq_le_sq.mp hcs'
        rwa [abs_of_nonneg (Real.sqrt_nonneg _)] at this
      · have hftc := hftc2 hθ hθ₁ hle
        have hcs := sliceCSMass (u := fun t => deriv (deriv F) t) hθ hθ₁ hF0 hintF
        rw [hftc] at hcs
        have hsq : (deriv F θ - deriv F θ₁) ^ 2 = (deriv F θ₁ - deriv F θ) ^ 2 := by ring
        have hcs' : (deriv F θ - deriv F θ₁) ^ 2 ≤ (Real.pi / 2) * M := by
          rw [hsq]; exact hcs
        rw [← Real.sq_sqrt hA] at hcs'
        have := sq_le_sq.mp hcs'
        rwa [abs_of_nonneg (Real.sqrt_nonneg _)] at this
    have hxsq : (deriv F θ - deriv F θ₁) ^ 2 ≤ (Real.pi / 2) * M := by
      calc (deriv F θ - deriv F θ₁) ^ 2 = |deriv F θ - deriv F θ₁| ^ 2 := by rw [sq_abs]
        _ ≤ (Real.sqrt ((Real.pi / 2) * M)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hdiff 2
        _ = (Real.pi / 2) * M := Real.sq_sqrt hA
    have h1 : (deriv F θ) ^ 2 ≤ 2 * (deriv F θ₁) ^ 2 + 2 * (deriv F θ - deriv F θ₁) ^ 2 := by
      nlinarith [sq_nonneg (deriv F θ - 2 * deriv F θ₁)]
    have h2 : 2 * (deriv F θ - deriv F θ₁) ^ 2 ≤ 2 * ((Real.pi / 2) * M) := by linarith
    linarith
  -- ### integration of the pointwise bound
  have hC : 0 ≤ 2 * (Real.pi / 2) * M + 2 * (deriv F θ₁) ^ 2 := by
    have h1 : 0 ≤ 2 * (Real.pi / 2) * M := mul_nonneg (by positivity) hMnn
    have h2 : 0 ≤ (deriv F θ₁) ^ 2 := sq_nonneg _
    linarith
  have hgm : MeasureTheory.AEStronglyMeasurable (deriv F)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.EllSol.aesm_of_continuousOn_Ioo hF1.continuousOn
  obtain ⟨hint', hineq⟩ :=
    sliceIntegralPointwise (u := fun t => deriv F t)
      (C := 2 * (Real.pi / 2) * M + 2 * (deriv F θ₁) ^ 2) hC hgm
      (fun θ hθ => hpoint θ hθ)
  refine ⟨?_, ?_⟩
  · simpa only [Work.Spaces.pth, hF] using hint'
  · simpa only [Work.Spaces.pth, hF, hM] using hineq

end Work.FTS.EllSol.FlatFT
end
-- ===== merged: Submission.Work.FTS.EllSol.Hamel =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Module

namespace Work.FTS.EllSol

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

variable {α : ℝ} {P : Fn → Fn → Prop}

/-- **The Hamel-basis assembly (item (e)).** -/
theorem exists_linear_selector
    (hG0 : Work.FTS.Nonlin.GalClass α (0 : Fn))
    (hGlin : ∀ g g' : Fn, ∀ c : ℝ, Work.FTS.Nonlin.GalClass α g →
      Work.FTS.Nonlin.GalClass α g' → Work.FTS.Nonlin.GalClass α (g + c • g'))
    (hP0 : P 0 0)
    (hPlin : ∀ g g' Ψ Ψ' : Fn, ∀ c : ℝ, Work.FTS.Nonlin.GalClass α g →
      Work.FTS.Nonlin.GalClass α g' → P g Ψ → P g' Ψ' → P (g + c • g') (Ψ + c • Ψ'))
    (hex : ∀ g, Work.FTS.Nonlin.GalClass α g → ∃ Ψ, P g Ψ) :
    ∃ EllSol : Fn →ₗ[ℝ] Fn,
      ∀ g, Work.FTS.Nonlin.GalClass α g → P g (EllSol g) := by
  classical
  -- the submodule spanned by the Galerkin class
  let S : Submodule ℝ Fn := Submodule.span ℝ {g : Fn | Work.FTS.Nonlin.GalClass α g}
  -- every element of `S` is in the class
  have hGS : ∀ x : Fn, x ∈ S → Work.FTS.Nonlin.GalClass α x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => exact hG0
    | add a b _ _ ha hb => simpa using hGlin a b 1 ha hb
    | smul c a _ ha => simpa using hGlin 0 a c hG0 ha
  -- a Hamel basis of `S` and the values of the linear map on it
  let b : Basis (Module.Basis.ofVectorSpaceIndex ℝ S) ℝ S := Basis.ofVectorSpace ℝ S
  let σ : S →ₗ[ℝ] Fn := Submodule.subtype S
  have hσb : ∀ i, σ (b i) = ((b i : S) : Fn) := fun i => rfl
  have hb : ∀ i, Work.FTS.Nonlin.GalClass α (σ (b i)) := fun i => hGS _ (b i).2
  let solB : Module.Basis.ofVectorSpaceIndex ℝ S → Fn :=
    fun i => Classical.choose (hex _ (hb i))
  have hsolB : ∀ i, P (σ (b i)) (solB i) := fun i => Classical.choose_spec (hex _ (hb i))
  let f : S →ₗ[ℝ] Fn := b.constr ℝ solB
  -- evaluating the two `Finsupp` sums at an inserted index
  have hsumS : ∀ (i : Module.Basis.ofVectorSpaceIndex ℝ S) (bb : ℝ)
      (c' : Module.Basis.ofVectorSpaceIndex ℝ S →₀ ℝ),
      ((Finsupp.single i bb + c').sum fun j a => a • b j : S)
        = bb • b i + c'.sum (fun j a => a • b j) := by
    intro i bb c'
    rw [Finsupp.sum_add_index' (fun j => by simp) (fun j x y => by simp [add_smul]),
      Finsupp.sum_single_index (by simp)]
  have hsumF : ∀ (i : Module.Basis.ofVectorSpaceIndex ℝ S) (bb : ℝ)
      (c' : Module.Basis.ofVectorSpaceIndex ℝ S →₀ ℝ),
      (Finsupp.single i bb + c').sum (fun j a => a • solB j)
        = bb • solB i + c'.sum (fun j a => a • solB j) := by
    intro i bb c'
    rw [Finsupp.sum_add_index' (fun j => by simp) (fun j x y => by simp [add_smul]),
      Finsupp.sum_single_index (by simp)]
  -- the key induction: on the support of the representation
  have key : ∀ c : Module.Basis.ofVectorSpaceIndex ℝ S →₀ ℝ,
      Work.FTS.Nonlin.GalClass α (σ (c.sum fun i a => a • b i)) →
      P (σ (c.sum fun i a => a • b i)) (c.sum fun i a => a • solB i) := by
    intro c
    induction c using Finsupp.induction with
    | zero =>
      intro _
      simpa using hP0
    | single_add i bb c' _ _ ih =>
      intro hGwhole
      -- the whole sum, split at the inserted index
      have hsplit : σ ((Finsupp.single i bb + c').sum fun j a => a • b j)
          = bb • σ (b i) + σ (c'.sum fun j a => a • b j) := by
        rw [hsumS i bb c', map_add, map_smul]
      -- the class of the two pieces
      have hG1 : Work.FTS.Nonlin.GalClass α (bb • σ (b i)) := by
        have h := hGlin 0 (σ (b i)) bb hG0 (hb i)
        simpa using h
      have hGtail : σ (c'.sum fun j a => a • b j)
          = σ ((Finsupp.single i bb + c').sum fun j a => a • b j) - bb • σ (b i) := by
        rw [hsplit]; abel
      have hG2 : Work.FTS.Nonlin.GalClass α (σ (c'.sum fun j a => a • b j)) := by
        have h := hGlin _ _ (-1) hGwhole hG1
        have h' : Work.FTS.Nonlin.GalClass α
            (σ ((Finsupp.single i bb + c').sum fun j a => a • b j) - bb • σ (b i)) := by
          simpa only [sub_eq_add_neg, neg_smul, one_smul] using h
        simpa only [hGtail] using h'
      have hIH := ih hG2
      have hP1 : P (bb • σ (b i)) (bb • solB i) := by
        simpa using hPlin 0 (σ (b i)) 0 (solB i) bb hG0 (hb i) hP0 (hsolB i)
      have hres0 := hPlin (bb • σ (b i)) (σ (c'.sum fun j a => a • b j))
        (bb • solB i) (c'.sum fun j a => a • solB j) 1 hG1 hG2 hP1 hIH
      have hres : P (bb • σ (b i) + σ (c'.sum fun j a => a • b j))
          (bb • solB i + c'.sum fun j a => a • solB j) := by
        simpa only [one_smul] using hres0
      rw [hsplit, hsumF i bb c']
      exact hres
  -- every element of `S` carries a solution
  have keyS : ∀ x : S, Work.FTS.Nonlin.GalClass α (σ x) → P (σ x) (f x) := by
    intro x hx
    have hsum : ((b.repr x).sum fun i a => a • b i : S) = x := by
      rw [← Finsupp.linearCombination_apply]
      exact Basis.linearCombination_repr b x
    have hrepr : σ ((b.repr x).sum fun i a => a • b i) = σ x := congrArg σ hsum
    have hfx : f x = (b.repr x).sum (fun i a => a • solB i) := by
      show (b.constr ℝ solB) x = _
      rw [Basis.constr_apply]
    rw [hfx, ← hrepr]
    exact key (b.repr x) (by rw [hrepr]; exact hx)
  -- extend `f` to all of `Fn`
  obtain ⟨EllSol, hEll⟩ := LinearMap.exists_extend f
  refine ⟨EllSol, ?_⟩
  intro g hg
  have hgS : g ∈ S := Submodule.subset_span hg
  have h1 : EllSol g = f ⟨g, hgS⟩ := by
    have := congr_fun (congr_arg DFunLike.coe hEll) (⟨g, hgS⟩ : S)
    simpa [LinearMap.comp_apply] using this
  rw [h1]
  exact keyS ⟨g, hgS⟩ (by change Work.FTS.Nonlin.GalClass α g; exact hg)

end Work.FTS.EllSol
end
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.i0TraceMoll.PsiAux.pthSliceLeE2s =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.PkgK5.i0TraceMoll.PsiAux

open MeasureTheory Set Filter

theorem pthSliceLeE2s (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G) :
    ∀ w : ℝ, 0 < w → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.pth G w θ| ≤ |Work.Spaces.pth G w (Real.pi / 4)|
        + Real.sqrt (Real.pi / 2)
          * Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G w) := by
  intro w hw θ hθ0 hθ1
  obtain ⟨hsm, -, -, -, -, -, -, hhon⟩ := hT
  have hπ4pos : 0 < Real.pi / 4 := by linarith [Real.pi_pos]
  have hπ4lt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  -- The `θ`-slice `t ↦ G w t` is `C²` on the open interval `(0, π/2)`.
  have hC2 : ContDiffOn ℝ 2 (fun t : ℝ => G w t) (Set.Ioo 0 (Real.pi / 2)) :=
    (hsm.curry_θ hw).of_le (by simp [Work.Stability.smoothOrder])
  -- Integrability of the weighted square of the second angular derivative.
  have hE2 : MeasureTheory.IntegrableOn
      (fun t : ℝ => (Work.Spaces.pth (Work.Spaces.pth G) w t) ^ 2
        * Work.FTS.EllipticEst.thEta t) Work.Spaces.Iθ :=
    Work.FTS.EllSol.EllPkgAux.integrableOn_second_deriv hhon hw
  have hE2' : MeasureTheory.IntegrableOn
      (fun t : ℝ => (Work.Spaces.pth (Work.Spaces.pth G) w t) ^ 2
        * (Real.sin (2 * t)) ^ (-(99 / 100 : ℝ))) (Set.Icc 0 (Real.pi / 2)) := by
    simpa only [Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta, Work.Spaces.eta] using hE2
  have hE2s_eq : Work.FTS.EllSol.EllPkgAux.E2s G w
      = ∫ t in Set.Icc (0 : ℝ) (Real.pi / 2),
          (Work.Spaces.pth (Work.Spaces.pth G) w t) ^ 2 * (Real.sin (2 * t)) ^ (-(99 / 100 : ℝ)) := by
    simp only [Work.FTS.EllSol.EllPkgAux.E2s, Work.Spaces.Iθ,
      Work.FTS.EllipticEst.thEta, Work.Spaces.eta]
  -- Weighted Cauchy–Schwarz for the slice of `∂_θ²G`.
  have hCS : (∫ t in Work.Spaces.Iθ, |Work.Spaces.pth (Work.Spaces.pth G) w t|)
      ≤ Real.sqrt (Real.pi / 2) * Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G w) := by
    have h := Work.FTS.EllSol.EllPkgAux.MollAux.integralAbsLeSqrtWeighted
      (h := fun t : ℝ => Work.Spaces.pth (Work.Spaces.pth G) w t) hE2'
    rw [← hE2s_eq] at h
    simpa only [Work.Spaces.Iθ] using h
  -- Integrability of `|∂_θ²G|` on the full interval.
  have habs : MeasureTheory.IntegrableOn
      (fun t : ℝ => |Work.Spaces.pth (Work.Spaces.pth G) w t|) Work.Spaces.Iθ :=
    Work.FTS.EllSol.EllPkgAux.integrableOn_abs_second_deriv hsm hhon hw
  -- Monotonicity of the integral over a subinterval of `[0, π/2]`.
  have hsubI : ∀ {c d : ℝ}, c ≤ d → 0 < c → d < Real.pi / 2 →
      (∫ t in c..d, |Work.Spaces.pth (Work.Spaces.pth G) w t|)
        ≤ ∫ t in Work.Spaces.Iθ, |Work.Spaces.pth (Work.Spaces.pth G) w t| := by
    intro c d hcd hc hd
    rw [intervalIntegral.integral_of_le hcd]
    refine MeasureTheory.setIntegral_mono_set habs
      (Filter.Eventually.of_forall (fun t => abs_nonneg _)) ?_
    filter_upwards with t ht using
      ⟨le_of_lt (lt_trans hc ht.1), le_of_lt (lt_of_le_of_lt ht.2 hd)⟩
  rcases lt_trichotomy θ (Real.pi / 4) with hlt | heq | hgt
  · -- ## Case `θ < π/4`
    have hftc : Work.Spaces.pth G w (Real.pi / 4) - Work.Spaces.pth G w θ
        = ∫ x in θ..(Real.pi / 4), Work.Spaces.pth (Work.Spaces.pth G) w x :=
      Work.FTS.EllSol.c2_deriv_sub_eq_intervalIntegral (h := fun t : ℝ => G w t)
        (ε := Real.pi / 2) hC2 hθ0 hlt.le hπ4lt
    have hdiff : Work.Spaces.pth G w θ - Work.Spaces.pth G w (Real.pi / 4)
        = -(∫ x in θ..(Real.pi / 4), Work.Spaces.pth (Work.Spaces.pth G) w x) := by
      rw [← hftc]; ring
    have h1 : |Work.Spaces.pth G w θ|
        ≤ |Work.Spaces.pth G w (Real.pi / 4)|
          + |Work.Spaces.pth G w θ - Work.Spaces.pth G w (Real.pi / 4)| := by
      have h := abs_add_le (Work.Spaces.pth G w (Real.pi / 4))
        (Work.Spaces.pth G w θ - Work.Spaces.pth G w (Real.pi / 4))
      rwa [show Work.Spaces.pth G w (Real.pi / 4)
            + (Work.Spaces.pth G w θ - Work.Spaces.pth G w (Real.pi / 4))
          = Work.Spaces.pth G w θ from by ring] at h
    refine h1.trans ?_
    rw [hdiff, abs_neg]
    exact add_le_add_right ((intervalIntegral.abs_integral_le_integral_abs hlt.le).trans
      ((hsubI hlt.le hθ0 hπ4lt).trans hCS)) _
  · -- ## Case `θ = π/4`
    subst heq
    refine le_add_of_nonneg_right ?_
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · -- ## Case `π/4 < θ`
    have hftc : Work.Spaces.pth G w θ - Work.Spaces.pth G w (Real.pi / 4)
        = ∫ x in (Real.pi / 4)..θ, Work.Spaces.pth (Work.Spaces.pth G) w x :=
      Work.FTS.EllSol.c2_deriv_sub_eq_intervalIntegral (h := fun t : ℝ => G w t)
        (ε := Real.pi / 2) hC2 hπ4pos hgt.le hθ1
    have h1 : |Work.Spaces.pth G w θ|
        ≤ |Work.Spaces.pth G w (Real.pi / 4)|
          + |Work.Spaces.pth G w θ - Work.Spaces.pth G w (Real.pi / 4)| := by
      have h := abs_add_le (Work.Spaces.pth G w (Real.pi / 4))
        (Work.Spaces.pth G w θ - Work.Spaces.pth G w (Real.pi / 4))
      rwa [show Work.Spaces.pth G w (Real.pi / 4)
            + (Work.Spaces.pth G w θ - Work.Spaces.pth G w (Real.pi / 4))
          = Work.Spaces.pth G w θ from by ring] at h
    refine h1.trans ?_
    rw [hftc]
    exact add_le_add_right ((intervalIntegral.abs_integral_le_integral_abs hgt.le).trans
      ((hsubI hgt.le hπ4pos hθ1).trans hCS)) _

end Work.FTS.EllSol.PkgK5.i0TraceMoll.PsiAux
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.i0TraceMoll.PsiAuxExp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5.i0TraceMoll

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The kernel: boundedness and support -/



/-! ## Integrability of the slice domination in the logarithmic variable -/

/-- **`t ↦ MGf G (e^t)` is integrable on bounded intervals**, from the local integrability of
`MGf G` on compact subintervals of `(0,∞)`.  The substitution rule for `t ↦ e^t` (whose
derivative is bounded below by `e^a > 0` on `(a,b)`) converts the interval `(a,b)` into
`(e^a, e^b)`. -/
theorem integrableOn_MGf_exp (G : ℝ → ℝ → ℝ)
    (hint : ∀ a b : ℝ, 0 < a → a ≤ b →
      MeasureTheory.IntegrableOn (Work.FTS.EllSol.EllPkgAux.MGf G) (Set.Icc a b))
    {a b : ℝ} (hab : a < b) :
    MeasureTheory.IntegrableOn (fun t : ℝ => Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t))
      (Set.Ioo a b) := by
  have hiff := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (f := Real.exp) (f' := fun x => Real.exp x) (g := Work.FTS.EllSol.EllPkgAux.MGf G)
    (a := a) (b := b)
    (by fun_prop) (fun x _ => Real.hasDerivAt_exp x) (fun x _ => (Real.exp_pos x).le)
  have hR : IntervalIntegrable (Work.FTS.EllSol.EllPkgAux.MGf G) volume (Real.exp a)
      (Real.exp b) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le
      (le_of_lt (Real.exp_lt_exp.mpr hab))).mpr
      ((hint (Real.exp a) (Real.exp b) (Real.exp_pos a)
        (le_of_lt (Real.exp_lt_exp.mpr hab))).mono_set Set.Ioo_subset_Icc_self)
  have hL : IntegrableOn (fun t : ℝ => Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t) * Real.exp t)
      (Set.Ioo a b) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (le_of_lt hab)).mp (hiff.mpr hR)
  have hMGnn : ∀ w : ℝ, 0 ≤ Work.FTS.EllSol.EllPkgAux.MGf G w := by
    intro w
    have h2 : (0 : ℝ) ≤ |G w (Real.pi / 4)| := abs_nonneg _
    have h3 : (0 : ℝ) ≤ |Work.Spaces.pth G w (Real.pi / 4)| := abs_nonneg _
    have h4 : (0 : ℝ) ≤ Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G w) := Real.sqrt_nonneg _
    simp only [Work.FTS.EllSol.EllPkgAux.MGf]
    linarith
  rw [IntegrableOn] at hL ⊢
  have h2 : Integrable (fun t : ℝ =>
      (Real.exp a)⁻¹ * (Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t) * Real.exp t))
      (volume.restrict (Set.Ioo a b)) := hL.const_mul _
  refine h2.mono' ?_ ?_
  · have hcont : Continuous (fun t : ℝ => Real.exp a * (Real.exp t)⁻¹) :=
      continuous_const.mul (Real.continuous_exp.inv₀ (fun t => Real.exp_ne_zero t))
    refine (hcont.aestronglyMeasurable.mul h2.aestronglyMeasurable).congr ?_
    filter_upwards with t
    have ha : Real.exp a ≠ 0 := Real.exp_ne_zero a
    have ht : Real.exp t ≠ 0 := Real.exp_ne_zero t
    calc Real.exp a * (Real.exp t)⁻¹ * ((Real.exp a)⁻¹ * (Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t) * Real.exp t))
        = (Real.exp t)⁻¹ * Real.exp t * (Real.exp a * (Real.exp a)⁻¹)
            * Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t) := by ring
      _ = Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t) := by
          rw [inv_mul_cancel₀ ht, mul_inv_cancel₀ ha]; ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hpa : 0 < Real.exp a := Real.exp_pos a
    have hlt : Real.exp a < Real.exp t := Real.exp_lt_exp.mpr ht.1
    have hge : 1 ≤ Real.exp t / Real.exp a := (one_le_div hpa).mpr hlt.le
    rw [Real.norm_of_nonneg (hMGnn _)]
    calc Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t)
        = Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t) * 1 := by ring
      _ ≤ Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t) * (Real.exp t / Real.exp a) :=
          mul_le_mul_of_nonneg_left hge (hMGnn _)
      _ = (Real.exp a)⁻¹ * (Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t) * Real.exp t) := by ring

/-- The `TraceClass`/`FourInts` form of `integrableOn_MGf_exp`, via `mollSliceBound`. -/
theorem integrableOn_MGf_exp_of_trace (G : ℝ → ℝ → ℝ)
    (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G) (hF : Work.FTS.EllSol.EllPkgAux.FourInts G)
    {a b : ℝ} (hab : a < b) :
    MeasureTheory.IntegrableOn (fun t : ℝ => Work.FTS.EllSol.EllPkgAux.MGf G (Real.exp t))
      (Set.Ioo a b) := by
  obtain ⟨C, hC, hbound⟩ := Work.FTS.EllSol.EllPkgAux.mollSliceBound
  exact integrableOn_MGf_exp G (fun _ _ ha hab' => (hbound G hT hF).2 _ _ ha hab') hab

end Work.FTS.EllSol.PkgK5.i0TraceMoll
end
end
-- ===== merged: Submission.Work.FTS.EllSol.ShiftFT.AtwoAux.Defs =====
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


/-- `L_b u = ∂_t u - b·u`. -/
def uTrAtwo_L1 (b : ℝ) (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t θ => Work.Spaces.pz u t θ - b * u t θ

/-- `L_b² u = ∂_t² u - 2b·∂_t u + b²·u`. -/
def uTrAtwo_L2 (b : ℝ) (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t θ => Work.Spaces.pz (Work.Spaces.pz u) t θ - 2 * b * Work.Spaces.pz u t θ
    + b ^ 2 * u t θ

/-- The pointwise expression for `L_b² (phiTr N · Gc N b u)` on the strip, obtained from the
two derivative identities of `Aux2.gcDeriv`. -/
def uTrAtwo_W (N b : ℝ) (u : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  phiTr N p.1 * Work.FTS.EllSol.Trunc.chi N p.1 * uTrAtwo_L2 b u p.1 p.2
    + (phiTr N p.1 * deriv (Work.FTS.EllSol.Trunc.chi N) p.1
        + 2 * deriv (phiTr N) p.1 * Work.FTS.EllSol.Trunc.chi N p.1) * uTrAtwo_L1 b u p.1 p.2
    + deriv (deriv (phiTr N)) p.1 * Gc N b u p.1 p.2

/-- The pointwise identity `L_b² (uTr N b u) = W` on the open strip. -/
theorem uTr_L2_eq (N b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ t θ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      uTrAtwo_L2 b (uTr N b u) t θ = uTrAtwo_W N b u (t, θ) := by
  intro t θ hθ
  have hd1 : Differentiable ℝ (fun s => Gc N b u s θ) := (Aux2.gcDeriv N b u hu).2.2.1 θ hθ
  have hd2 : Differentiable ℝ (fun s => Work.Spaces.pz (Gc N b u) s θ) :=
    (Aux2.gcDeriv N b u hu).2.2.2 θ hθ
  have hphi : Differentiable ℝ (phiTr N) := (phiTr_contDiff 1 N).differentiable (by norm_num)
  have hphi1 : Differentiable ℝ (deriv (phiTr N)) :=
    (phiTr_contDiff 2 N).differentiable_deriv_two
  have key : Work.Spaces.pz (Work.Spaces.pz (uTr N b u)) t θ
      = deriv (deriv (phiTr N)) t * Gc N b u t θ
        + 2 * deriv (phiTr N) t * Work.Spaces.pz (Gc N b u) t θ
        + phiTr N t * Work.Spaces.pz (Work.Spaces.pz (Gc N b u)) t θ :=
    Work.FTS.EllSol.Trunc.pz_pz_mul_slice (phiTr N) (Gc N b u) t θ hphi hphi1 hd1 hd2
  have key1 : Work.Spaces.pz (uTr N b u) t θ
      = deriv (phiTr N) t * Gc N b u t θ + phiTr N t * Work.Spaces.pz (Gc N b u) t θ :=
    Work.FTS.EllSol.Trunc.pz_mul_slice (phiTr N) (Gc N b u) t θ (hphi t) (hd1 t)
  rw [uTrAtwo_L2, uTrAtwo_W, uTrAtwo_L1, key, key1,
    (Aux2.gcDeriv N b u hu).1 t θ hθ, (Aux2.gcDeriv N b u hu).2.1 t θ hθ]
  simp only [uTrAtwo_L2, uTr]
  ring


/-- The a.e. version of `uTr_L2_eq` on the strip `ℝ × Iθ`. -/
theorem ae_uTr_L2_eq (N b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    (fun p : ℝ × ℝ => uTrAtwo_L2 b (uTr N b u) p.1 p.2)
      =ᵐ[volume.restrict ((Set.univ : Set ℝ) ×ˢ Work.Spaces.Iθ)]
      (fun p : ℝ × ℝ => uTrAtwo_W N b u p) := by
  filter_upwards [ae_mem_Ioo_of_Iθ] with p hp
  exact uTr_L2_eq N b u hu p.1 p.2 hp

end

end Work.FTS.EllSol.ShiftFT
end
-- ===== merged: Submission.Work.FTS.EllSol.ShiftFT.Aux2.gcTail =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project (area `FTS.EllSol`).

# The tail behaviour of the backward particular solution `Gc`

`Gc N b u` is the backward particular solution of the shifted equation
`L_b G = chi N · (L_b u)`, written in `ShiftPrimDefs` as

`Gc N b u t θ = chi N t · u t θ + e^{bt} ∫_t^{2N} e^{-bs} (chi N)'(s) u s θ ds`.

This file proves the three assertions needed about its behaviour *off* the truncation window:

* for `t ≤ -2N` it agrees with the *improper integral* form
  `Gc N b u t θ = -∫_{-2N}^{2N} e^{b(t-s)} chi N s (∂_t u - b u)(s,θ) ds`
  (the two right-tail pieces of the primitive identity are recombined by an integration by
  parts, the boundary terms vanishing because `chi N (±2N) = 0`);
* consequently `(Gc N b u t θ)^2 ≤ 4N ∫_{-2N}^{2N} (∂_t u - b u)(s,θ)^2 ds` for `t ≤ -2N`
  (Cauchy–Schwarz, using `0 ≤ b` to bound `e^{b(t-s)} ≤ 1` on the window);
* for `2N ≤ t` it vanishes identically (`(chi N)' = 0` on `[2N,∞)`).

The analytic pieces of this (the integration by parts and the Cauchy–Schwarz inequality for
interval integrals) are proved in the sibling modules `gcIBP`, `gcIntShift`, `gcIntTailZero`
and `sqIntegralAbsLe`.
-/

namespace Work.FTS.EllSol.ShiftFT.Aux2

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-! ## Elementary support facts for the cutoff -/




/-! ## Slice regularity from the joint `C²` hypothesis -/

/-- The `θ`-slice of `u` is `C²` on all of `ℝ` for `θ` in the open angular interval. -/
theorem contDiff_slice_of_uncurry {u : ℝ → ℝ → ℝ} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContDiff ℝ 2 (fun s : ℝ => u s θ) := by
  have hmap : Set.MapsTo (fun s : ℝ => ((s, θ) : ℝ × ℝ)) Set.univ
      (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun s _ => ⟨trivial, hθ⟩
  have hpair : ContDiffOn ℝ 2 (fun s : ℝ => ((s, θ) : ℝ × ℝ)) Set.univ :=
    ContDiffOn.prodMk contDiffOn_id contDiffOn_const
  have hslice : ContDiffOn ℝ 2 (fun s : ℝ => u s θ) Set.univ := by
    have h := hu.comp hpair hmap
    simpa [Function.comp_def, Function.uncurry] using h
  exact contDiffOn_univ.mp hslice

/-- The `t`-derivative of the `θ`-slice of `u` is continuous. -/
theorem continuous_pz_slice_of_uncurry {u : ℝ → ℝ → ℝ} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    Continuous (fun s : ℝ => Work.Spaces.pz u s θ) :=
  (contDiff_slice_of_uncurry hθ hu).continuous_deriv (by norm_num)

/-! ## The target -/

theorem gcTail (N b : ℝ) (u : ℝ → ℝ → ℝ) (hb : 0 ≤ b) (hN : 0 < N)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    (∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) → t ≤ -(2 * N) →
      Work.FTS.EllSol.ShiftFT.Gc N b u t θ
        = -(∫ s in (-(2 * N))..(2 * N),
            Real.exp (b * (t - s)) * Work.FTS.EllSol.Trunc.chi N s
              * (Work.Spaces.pz u s θ - b * u s θ)))
    ∧ (∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) → t ≤ -(2 * N) →
      (Work.FTS.EllSol.ShiftFT.Gc N b u t θ) ^ 2
        ≤ 4 * N * ∫ s in (-(2 * N))..(2 * N), (Work.Spaces.pz u s θ - b * u s θ) ^ 2)
    ∧ (∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) → 2 * N ≤ t →
      Work.FTS.EllSol.ShiftFT.Gc N b u t θ = 0) := by
  have hchi_cont : Continuous (Work.FTS.EllSol.Trunc.chi N) :=
    (Work.FTS.EllSol.Trunc.chi_contDiff 2 N).continuous
  have htail : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) → t ≤ -(2 * N) →
      Work.FTS.EllSol.ShiftFT.Gc N b u t θ
        = -(∫ s in (-(2 * N))..(2 * N),
            Real.exp (b * (t - s)) * Work.FTS.EllSol.Trunc.chi N s
              * (Work.Spaces.pz u s θ - b * u s θ)) := by
    intro t θ hθ ht
    have hχt : Work.FTS.EllSol.Trunc.chi N t = 0 := by
      refine Work.FTS.EllSol.Trunc.chi_eq_zero hN ?_
      rw [abs_of_nonpos (by linarith)]
      linarith
    have hunfold : Work.FTS.EllSol.ShiftFT.Gc N b u t θ
        = Work.FTS.EllSol.Trunc.chi N t * u t θ
          + Real.exp (b * t) * ∫ s in t..(2 * N),
              Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ := rfl
    rw [hunfold, hχt, zero_mul, zero_add, gcIntShift N b u hN hu θ hθ t ht]
    rw [gcIBP N b u hN hu θ hθ t]
    ring
  have hzero : ∀ t θ, θ ∈ Set.Ioo 0 (Real.pi / 2) → 2 * N ≤ t →
      Work.FTS.EllSol.ShiftFT.Gc N b u t θ = 0 := by
    intro t θ hθ ht
    have hχt : Work.FTS.EllSol.Trunc.chi N t = 0 := by
      refine Work.FTS.EllSol.Trunc.chi_eq_zero hN ?_
      rw [abs_of_nonneg (by linarith)]
      linarith
    have hunfold : Work.FTS.EllSol.ShiftFT.Gc N b u t θ
        = Work.FTS.EllSol.Trunc.chi N t * u t θ
          + Real.exp (b * t) * ∫ s in t..(2 * N),
              Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ := rfl
    rw [hunfold, hχt, zero_mul, zero_add, gcIntTailZero N b u hN hu θ hθ t ht, mul_zero]
  refine ⟨htail, ?_, hzero⟩
  intro t θ hθ ht
  have hu_cont : Continuous (fun s : ℝ => u s θ) := (contDiff_slice_of_uncurry hθ hu).continuous
  have hpz_cont : Continuous (fun s : ℝ => Work.Spaces.pz u s θ) :=
    continuous_pz_slice_of_uncurry hθ hu
  have hv_cont : Continuous (fun s : ℝ => Work.Spaces.pz u s θ - b * u s θ) :=
    hpz_cont.sub (hu_cont.const_mul b)
  have hexp_cont : Continuous (fun s : ℝ => Real.exp (b * (t - s))) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))
  have hJabs_le : ∀ s : ℝ,
      |Real.exp (b * (t - s)) * Work.FTS.EllSol.Trunc.chi N s
          * (Work.Spaces.pz u s θ - b * u s θ)|
        ≤ |Work.Spaces.pz u s θ - b * u s θ| := by
    intro s
    by_cases hχ : Work.FTS.EllSol.Trunc.chi N s = 0
    · rw [hχ, mul_zero, zero_mul, abs_zero]
      exact abs_nonneg _
    · have hts : t ≤ s := by
        by_contra hcon
        have hcon' : s < t := lt_of_not_ge hcon
        have hst : s < -(2 * N) := lt_of_lt_of_le hcon' ht
        have habs : |s| = -s := abs_of_neg (by linarith)
        exact hχ (Work.FTS.EllSol.Trunc.chi_eq_zero hN (by rw [habs]; linarith))
      have hexp1 : Real.exp (b * (t - s)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact mul_nonpos_of_nonneg_of_nonpos hb (by linarith)
      have hexp0 : 0 ≤ Real.exp (b * (t - s)) := Real.exp_nonneg _
      have hχ0 : 0 ≤ Work.FTS.EllSol.Trunc.chi N s := Work.FTS.EllSol.Trunc.chi_nonneg _ _
      have hχ1 : Work.FTS.EllSol.Trunc.chi N s ≤ 1 := Work.FTS.EllSol.Trunc.chi_le_one _ _
      calc |Real.exp (b * (t - s)) * Work.FTS.EllSol.Trunc.chi N s
              * (Work.Spaces.pz u s θ - b * u s θ)|
          = Real.exp (b * (t - s)) * Work.FTS.EllSol.Trunc.chi N s
              * |Work.Spaces.pz u s θ - b * u s θ| := by
            rw [abs_mul, abs_of_nonneg (mul_nonneg hexp0 hχ0)]
        _ ≤ 1 * |Work.Spaces.pz u s θ - b * u s θ| :=
            mul_le_mul_of_nonneg_right (mul_le_one₀ hexp1 hχ0 hχ1) (abs_nonneg _)
        _ = |Work.Spaces.pz u s θ - b * u s θ| := one_mul _
  have hstep1 : |Work.FTS.EllSol.ShiftFT.Gc N b u t θ|
      ≤ ∫ s in (-(2 * N))..(2 * N), |Work.Spaces.pz u s θ - b * u s θ| := by
    rw [htail t θ hθ ht, abs_neg]
    refine le_trans (intervalIntegral.abs_integral_le_integral_abs
      (f := fun s => Real.exp (b * (t - s)) * Work.FTS.EllSol.Trunc.chi N s
        * (Work.Spaces.pz u s θ - b * u s θ)) (by linarith)) ?_
    refine intervalIntegral.integral_mono (by linarith) ?_ ?_ (fun s => hJabs_le s)
    · exact ((hexp_cont.mul hchi_cont).mul hv_cont).abs.intervalIntegrable _ _
    · exact hv_cont.abs.intervalIntegrable _ _
  have hCS : (∫ s in (-(2 * N))..(2 * N), |Work.Spaces.pz u s θ - b * u s θ|) ^ 2
      ≤ 4 * N * ∫ s in (-(2 * N))..(2 * N), (Work.Spaces.pz u s θ - b * u s θ) ^ 2 := by
    have h := sqIntegralAbsLe (-(2 * N)) (2 * N) (by linarith)
      (fun s : ℝ => Work.Spaces.pz u s θ - b * u s θ) hv_cont
    convert h using 1
    ring
  have hsq : |Work.FTS.EllSol.ShiftFT.Gc N b u t θ| ^ 2
      ≤ (∫ s in (-(2 * N))..(2 * N), |Work.Spaces.pz u s θ - b * u s θ|) ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg (Work.FTS.EllSol.ShiftFT.Gc N b u t θ)) hstep1
    simpa [sq] using h
  calc (Work.FTS.EllSol.ShiftFT.Gc N b u t θ) ^ 2
      = |Work.FTS.EllSol.ShiftFT.Gc N b u t θ| ^ 2 := (sq_abs _).symm
    _ ≤ (∫ s in (-(2 * N))..(2 * N), |Work.Spaces.pz u s θ - b * u s θ|) ^ 2 := hsq
    _ ≤ 4 * N * ∫ s in (-(2 * N))..(2 * N), (Work.Spaces.pz u s θ - b * u s θ) ^ 2 := hCS

end

end Work.FTS.EllSol.ShiftFT.Aux2
end
-- ===== merged: Submission.Work.FTS.EllSol.ropBasic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- `sin 2θ` does not vanish on the open quadrant. -/
theorem sin_two_ne_zero_of_mem_Q0 {p : ℝ × ℝ} (hp : p ∈ Work.FTS.EllipticEst.Q0) :
    Real.sin (2 * p.2) ≠ 0 := by
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))

/-- Sums of functions `C^∞` on the open quadrant are `C^∞` on the open quadrant. -/
theorem SmoothOpen_add_local {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall fun n => ?_
  have h1 : Function.uncurry (fun z θ => f z θ + g z θ)
      = (Function.uncurry f) + (Function.uncurry g) := by funext p; rfl
  rw [h1]
  exact (Work.FTS.EllipticEst.SmoothOpen.forall hf n).add
    (Work.FTS.EllipticEst.SmoothOpen.forall hg n)

/-- Multiplication of a function `C^∞` on the open quadrant by the bounded smooth angular profile
`sin²θ` keeps it `C^∞` there. -/
theorem SmoothOpen_mul_sin_sq_local {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.sin θ ^ 2 * f z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => Real.sin θ ^ 2 * f z θ)) Work.FTS.EllipticEst.Q0
  rw [show Function.uncurry (fun z θ => Real.sin θ ^ 2 * f z θ)
      = fun p : ℝ × ℝ => Real.sin p.2 ^ 2 * f p.1 p.2 from rfl]
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin p.2 ^ 2) Work.FTS.EllipticEst.Q0 :=
    ((contDiffOn_snd (𝕜 := ℝ) (s := Work.FTS.EllipticEst.Q0)).sin).pow 2
  exact h1.mul hf




/-- **`Ξ = ellShift - Ḡ·sin 2θ`**: the exact algebraic identity relating the residual of
Theorem `RemovingL12` to the straightened unknown `V = ellShift α g Ψ = Ψ + Gsing α g·sin 2θ`
and the lower singular term `Ḡ = Gbar α g`. -/
theorem EllResid_eq_ellShift_sub_Gbar_point (α : ℝ) (g Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.EllResid α g Ψ z θ
      = (Ψ z θ + Work.Elliptic.Gsing α g z * Real.sin (2 * θ))
        - Work.Elliptic.Gbar α g z * Real.sin (2 * θ) := by
  rw [Work.Elliptic.EllResid, Work.Elliptic.Gsing, Work.Elliptic.Gstar]
  ring

end Work.FTS.EllSol
end
end
-- ===== merged: Submission.Work.FTS.EllSol.ropIdentity =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false


end Work.FTS.EllSol
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Blocks.HkNorm_Dz_amgm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.EllipticEst.DzAmgm

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The angular weights as squares -/

theorem angZ_sq {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : (angZ θ) ^ 2 = sEta θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  rw [angZ, sEta, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hs]
  norm_num

theorem angM_sq (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : (angM α θ) ^ 2 = sGam α θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  rw [angM, sGam, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hs]
  norm_num

/-! ## The termwise Agmon estimate (adapted from `DzAmgm.Scratch`) -/

/-- **Termwise AM–GM, pure summands.**  Applying `TermAMGMLintegral` with `V = D_z^m f`,
`wth = angZ` and rewriting `D_z (D_z^m f) = D_z^{m+1} f`,
`z²∂_z²(D_z^m f) = D_z^m (z²∂_z²f)` (`ZsqPz2Comm`) gives the termwise estimate for `TZ`. -/
theorem TZ_termwise (C1 : ℝ) (hC1 : 0 < C1)
    (hgen : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2)))) :
    ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (f : ℝ → ℝ → ℝ), SmoothOpen f → ∀ (m : ℕ),
      ENNReal.ofReal (α ^ 2) * TZ f (m + 1)
        ≤ ENNReal.ofReal (C1 ^ 2) *
            (ENNReal.ofReal (α ^ 4) * TZ (zsqPz2 f) m + TZ f m) := by
  intro α hα hα1 f hf m
  have hang : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ angZ θ := fun θ hθ =>
    angZ_nonneg_of_mem (by rw [Work.Spaces.Iθ]; exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have h := hgen α hα hα1 (Work.Spaces.DzIter m f) angZ (hf.DzIter m) hang
  -- the first factor of the left-hand integrand
  have hL : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.Dz (Work.Spaces.DzIter m f) z θ * Work.Spaces.w z
          * angZ θ) ^ 2))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.DzIter (m + 1) f z θ * Work.Spaces.w z * angZ θ) ^ 2) := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    rw [Work.Spaces.DzIter_succ]
  -- the second-derivative factor of the right-hand side
  have hR2 : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z θ
          * Work.Spaces.w z * angZ θ) ^ 2))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.DzIter m (zsqPz2 f) z θ * Work.Spaces.w z * angZ θ) ^ 2) := by
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    have hcomm := AgmonSlice.zsq_pzIter2_mixed_open f ((smoothOpen_iff_forall f).mp hf) m 0 hz hθ
    have h1 : z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z θ
        = Work.Spaces.DzIter m (zsqPz2 f) z θ := hcomm
    rw [h1]
  rw [hL, hR2] at h
  rw [lintegral_open_eq_prod] at h
  rw [lintegral_open_eq_prod] at h
  rw [lintegral_open_eq_prod] at h
  exact h

/-- **Termwise AM–GM, mixed summands.**  Applying `TermAMGMLintegral` with
`V = D_z^j D_θ^i f`, `wth = angM α` and rewriting `D_z (D_z^j D_θ^i f) = D_z^{j+1} D_θ^i f`,
`z²∂_z²(D_z^j D_θ^i f) = D_z^j D_θ^i (z²∂_z²f)` (`ZsqPz2Comm`) gives the termwise estimate. -/
theorem TM_termwise (C1 : ℝ) (hC1 : 0 < C1)
    (hgen : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2)))) :
    ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (f : ℝ → ℝ → ℝ), SmoothOpen f → ∀ (i j : ℕ),
      ENNReal.ofReal (α ^ 2) * TM α f i (j + 1)
        ≤ ENNReal.ofReal (C1 ^ 2) *
            (ENNReal.ofReal (α ^ 4) * TM α (zsqPz2 f) i j + TM α f i j) := by
  intro α hα hα1 f hf i j
  have hang : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ angM α θ := fun θ hθ =>
    angM_nonneg_of_mem (by rw [Work.Spaces.Iθ]; exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have h := hgen α hα hα1 (Work.Spaces.mixed j i f) (angM α) (hf.mixed j i) hang
  have hL : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.Dz (Work.Spaces.mixed j i f) z θ * Work.Spaces.w z
          * angM α θ) ^ 2))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.mixed (j + 1) i f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    have hdz : Work.Spaces.Dz (Work.Spaces.mixed j i f)
        = Work.Spaces.mixed (j + 1) i f := by
      simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ]
    rw [hdz]
    exact mixed_ofReal_eq α f i (j + 1) z θ
  have hR2 : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.mixed j i f) z θ
          * Work.Spaces.w z * angM α θ) ^ 2))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.mixed j i (zsqPz2 f) z θ * Work.Spaces.Wt α z θ) ^ 2) := by
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    refine lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    have hcomm := AgmonSlice.zsq_pzIter2_mixed_open f ((smoothOpen_iff_forall f).mp hf) j i hz hθ
    have h1 : z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.mixed j i f) z θ
        = Work.Spaces.mixed j i (zsqPz2 f) z θ := hcomm
    rw [h1, mixed_ofReal_eq α (zsqPz2 f) i j z θ]
  have hR3 : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.mixed j i f z θ * Work.Spaces.w z * angM α θ) ^ 2))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    refine lintegral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact mixed_ofReal_eq α f i j z θ
  rw [hL, hR2, hR3] at h
  rw [lintegral_open_eq_prod] at h
  rw [lintegral_open_eq_prod] at h
  rw [lintegral_open_eq_prod] at h
  exact h



/-! ## The `LkSq` inequality -/

/-- **The `θ`-integrated radial interpolation for `D_z f`, at the level of the honest
`lintegral`s.** -/
theorem LkSq_Dz_le (C1 : ℝ) (hC1 : 0 < C1)
    (hgen : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2)))) :
    ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (k : ℕ) (f : ℝ → ℝ → ℝ),
      (∀ (a : ℕ) (z θ : ℝ), (z, θ) ∈ Q0 →
        Work.Spaces.DthIter a (Work.Spaces.Dz f) z θ
          = Work.Spaces.Dz (Work.Spaces.DthIter a f) z θ) →
      SmoothOpen f →
      ENNReal.ofReal (α ^ 2) * LkSq α k (Work.Spaces.Dz f)
        ≤ ENNReal.ofReal (C1 ^ 2) *
            (ENNReal.ofReal (α ^ 4) * LkSq α k (zsqPz2 f) + LkSq α k f) := by
  intro α hα hα1 k f hcomm hf
  have hDz : SmoothOpen (Work.Spaces.Dz f) := hf.Dz
  have hQ : SmoothOpen (zsqPz2 f) := SmoothOpen_zsqPz2 f hf
  have hdec : LkSq α k (Work.Spaces.Dz f)
      = (∑ i ∈ Finset.range (k + 1), TZ f (i + 1))
        + ∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α f p.1 (p.2 + 1) else 0) := by
    rw [LkSq_eq_sum α k (Work.Spaces.Dz f) hDz]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => TZ_Dz f i
    · refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hc : 1 ≤ p.1 ∧ p.1 + p.2 ≤ k
      · rw [if_pos hc, if_pos hc, TM_Dz_of_comm α f hcomm p.1 p.2]
      · rw [if_neg hc, if_neg hc]
  have hdecQ : LkSq α k (zsqPz2 f)
      = (∑ i ∈ Finset.range (k + 1), TZ (zsqPz2 f) i)
        + ∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α (zsqPz2 f) p.1 p.2 else 0) :=
    LkSq_eq_sum α k (zsqPz2 f) hQ
  have hdecf : LkSq α k f
      = (∑ i ∈ Finset.range (k + 1), TZ f i)
        + ∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α f p.1 p.2 else 0) :=
    LkSq_eq_sum α k f hf
  -- the termwise bounds
  have hT : ∀ i ∈ Finset.range (k + 1), ENNReal.ofReal (α ^ 2) * TZ f (i + 1)
      ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * TZ (zsqPz2 f) i + TZ f i) :=
    fun i _ => TZ_termwise C1 hC1 hgen α hα hα1 f hf i
  have hM : ∀ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
      (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then ENNReal.ofReal (α ^ 2) * TM α f p.1 (p.2 + 1) else 0)
        ≤ ENNReal.ofReal (C1 ^ 2) *
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then
              ENNReal.ofReal (α ^ 4) * TM α (zsqPz2 f) p.1 p.2 + TM α f p.1 p.2 else 0) := by
    intro p _
    by_cases hc : 1 ≤ p.1 ∧ p.1 + p.2 ≤ k
    · rw [if_pos hc, if_pos hc]
      exact TM_termwise C1 hC1 hgen α hα hα1 f hf p.1 p.2
    · rw [if_neg hc, if_neg hc, mul_zero]
  -- the two sums
  have hS1le : ENNReal.ofReal (α ^ 2) * (∑ i ∈ Finset.range (k + 1), TZ f (i + 1))
      ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∑ i ∈ Finset.range (k + 1), TZ (zsqPz2 f) i)
            + (∑ i ∈ Finset.range (k + 1), TZ f i)) := by
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum hT) (le_of_eq ?_)
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.mul_sum]
  have hS2le : ENNReal.ofReal (α ^ 2)
        * (∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α f p.1 (p.2 + 1) else 0))
      ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4)
              * (∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
                  (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α (zsqPz2 f) p.1 p.2 else 0))
            + (∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
                  (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α f p.1 p.2 else 0))) := by
    rw [Finset.mul_sum]
    have hstep : (∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
          ENNReal.ofReal (α ^ 2) *
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then TM α f p.1 (p.2 + 1) else 0))
        = ∑ p ∈ (Finset.range (k + 1)) ×ˢ (Finset.range (k + 1)),
            (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k
              then ENNReal.ofReal (α ^ 2) * TM α f p.1 (p.2 + 1) else 0) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hc : 1 ≤ p.1 ∧ p.1 + p.2 ≤ k
      · rw [if_pos hc, if_pos hc]
      · rw [if_neg hc, if_neg hc, mul_zero]
    rw [hstep]
    refine le_trans (Finset.sum_le_sum hM) (le_of_eq ?_)
    have hflat : ∀ p : ℕ × ℕ,
        ENNReal.ofReal (C1 ^ 2) * (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then
            ENNReal.ofReal (α ^ 4) * TM α (zsqPz2 f) p.1 p.2 + TM α f p.1 p.2 else 0)
          = (if 1 ≤ p.1 ∧ p.1 + p.2 ≤ k then ENNReal.ofReal (C1 ^ 2) *
                (ENNReal.ofReal (α ^ 4) * TM α (zsqPz2 f) p.1 p.2 + TM α f p.1 p.2)
              else 0) := by
      intro p; by_cases hc : 1 ≤ p.1 ∧ p.1 + p.2 ≤ k <;> simp [hc]
    rw [Finset.sum_congr rfl (fun p _ => hflat p)]
    rw [sum_ite_mul_split (k := k) (ENNReal.ofReal (C1 ^ 2)) (ENNReal.ofReal (α ^ 4))
      (fun p => TM α (zsqPz2 f) p.1 p.2) (fun p => TM α f p.1 p.2)]
    rw [mul_add]
    ring
  -- combine
  rw [hdec, mul_add]
  refine le_trans (add_le_add hS1le hS2le) (le_of_eq ?_)
  rw [hdecQ, hdecf]
  ring

/-- Finiteness of `LkSq (D_z f)` from the `LkSq` inequality. -/
theorem LkSq_Dz_lt_top (C1 : ℝ) (hC1 : 0 < C1)
    (hgen : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2))))
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f)
    (hmf : Work.Spaces.HkMem α k f) (hmQ : Work.Spaces.HkMem α k (zsqPz2 f)) :
    LkSq α k (Work.Spaces.Dz f) < ⊤ := by
  have hQfin : LkSq α k (zsqPz2 f) < ⊤ := LkSq_lt_top α k _ (SmoothOpen_zsqPz2 f hf) hmQ
  have hffin : LkSq α k f < ⊤ := LkSq_lt_top α k f hf hmf
  have h := LkSq_Dz_le C1 hC1 hgen α hα hα1 k f (comm_hyp f hf) hf
  have hfin : ENNReal.ofReal (C1 ^ 2) *
      (ENNReal.ofReal (α ^ 4) * LkSq α k (zsqPz2 f) + LkSq α k f) < ⊤ := by
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hQfin, hffin⟩
  have hlt : ENNReal.ofReal (α ^ 2) * LkSq α k (Work.Spaces.Dz f) < ⊤ := lt_of_le_of_lt h hfin
  have hpos : ENNReal.ofReal (α ^ 2) ≠ 0 := by
    simpa using (ENNReal.ofReal_pos.mpr (by positivity : (0 : ℝ) < α ^ 2)).ne'
  rcases ENNReal.mul_lt_top_iff.mp hlt with ⟨-, h2⟩ | h0 | h0
  · exact h2
  · exact absurd h0 hpos
  · exact lt_top_iff_ne_top.mpr (by simp [h0])

/-- **The norm inequality**, given the honesty of `D_z f`. -/
theorem HkNorm_Dz_le_of (C1 : ℝ) (hC1 : 0 < C1)
    (hgen : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ∫⁻ z in Set.Ioi (0 : ℝ),
              ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2))))
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f)
    (hmf : Work.Spaces.HkMem α k f) (hmQ : Work.Spaces.HkMem α k (zsqPz2 f))
    (hmDz : Work.Spaces.HkMem α k (Work.Spaces.Dz f)) :
    α * Work.Spaces.HkNorm α k (Work.Spaces.Dz f)
      ≤ C1 * (Work.Spaces.HkNorm α k f + α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f)) := by
  have hDzSm : SmoothOpen (Work.Spaces.Dz f) := hf.Dz
  have hQSm : SmoothOpen (zsqPz2 f) := SmoothOpen_zsqPz2 f hf
  have hDzfin := LkSq_Dz_lt_top C1 hC1 hgen α hα hα1 k f hf hmf hmQ
  have hQfin : LkSq α k (zsqPz2 f) < ⊤ := LkSq_lt_top α k _ hQSm hmQ
  have hffin : LkSq α k f < ⊤ := LkSq_lt_top α k f hf hmf
  -- (★) in terms of `HkSq`
  have h := LkSq_Dz_le C1 hC1 hgen α hα hα1 k f (comm_hyp f hf) hf
  rw [LkSq_eq_ofReal_HkSq α k (Work.Spaces.Dz f) hDzSm hmDz,
    LkSq_eq_ofReal_HkSq α k (zsqPz2 f) hQSm hmQ,
    LkSq_eq_ofReal_HkSq α k f hf hmf] at h
  have hnn : 0 ≤ Work.Spaces.HkSq α k (Work.Spaces.Dz f) :=
    Work.Spaces.HkSq_nonneg α k _
  have hnnQ : 0 ≤ Work.Spaces.HkSq α k (zsqPz2 f) := Work.Spaces.HkSq_nonneg α k _
  have hnnf : 0 ≤ Work.Spaces.HkSq α k f := Work.Spaces.HkSq_nonneg α k f
  have hL : ENNReal.ofReal (α ^ 2) * ENNReal.ofReal (Work.Spaces.HkSq α k (Work.Spaces.Dz f))
      = ENNReal.ofReal (α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz f)) := by
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ α ^ 2)]
  have hR : ENNReal.ofReal (C1 ^ 2) * (ENNReal.ofReal (α ^ 4) *
        ENNReal.ofReal (Work.Spaces.HkSq α k (zsqPz2 f)) + ENNReal.ofReal (Work.Spaces.HkSq α k f))
      = ENNReal.ofReal (C1 ^ 2 * (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f)
          + Work.Spaces.HkSq α k f)) := by
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ C1 ^ 2),
      ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f)) hnnf,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ α ^ 4)]
  rw [hL, hR] at h
  have hsq : α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz f)
      ≤ C1 ^ 2 * (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  -- take square roots
  have hsqrt : α * Real.sqrt (Work.Spaces.HkSq α k (Work.Spaces.Dz f))
      ≤ C1 * Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f) := by
    have h1 : α * Real.sqrt (Work.Spaces.HkSq α k (Work.Spaces.Dz f))
        = Real.sqrt (α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz f)) := by
      rw [Real.sqrt_mul (sq_nonneg α), Real.sqrt_sq hα.le]
    have h2 : C1 * Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f)
        = Real.sqrt (C1 ^ 2 * (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f)
            + Work.Spaces.HkSq α k f)) := by
      rw [Real.sqrt_mul (sq_nonneg C1), Real.sqrt_sq hC1.le]
    rw [h1, h2]
    exact Real.sqrt_le_sqrt hsq
  have hf1 : Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f))
      = α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f) := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ α ^ 4), Work.Spaces.HkNorm,
      show Real.sqrt (α ^ 4) = α ^ 2 by
        rw [show α ^ 4 = (α ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity : (0 : ℝ) ≤ α ^ 2)]]
  have hadd : Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f)
      ≤ α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f) + Work.Spaces.HkNorm α k f := by
    calc Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f)
        ≤ Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f))
          + Real.sqrt (Work.Spaces.HkSq α k f) :=
          sqrt_add_le_sqrt _ _ (by positivity) (Work.Spaces.HkSq_nonneg α k f)
      _ = α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f) + Work.Spaces.HkNorm α k f := by
          rw [hf1]
          rfl
  calc α * Real.sqrt (Work.Spaces.HkSq α k (Work.Spaces.Dz f))
      ≤ C1 * Real.sqrt (α ^ 4 * Work.Spaces.HkSq α k (zsqPz2 f) + Work.Spaces.HkSq α k f) := hsqrt
    _ ≤ C1 * (α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f) + Work.Spaces.HkNorm α k f) :=
        mul_le_mul_of_nonneg_left hadd (le_of_lt hC1)
    _ = C1 * (Work.Spaces.HkNorm α k f + α ^ 2 * Work.Spaces.HkNorm α k (zsqPz2 f)) := by ring


/-! ## The honesty certificate `HkMem α k (D_z f)` -/

section Cert

/-- `D_z` commutes with the iterates `D_z^m` on the left: `D_z^m (D_z f) = D_z (D_z^m f)`. -/
theorem DzIter_Dz_eq (m : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter m (Work.Spaces.Dz f) = Work.Spaces.Dz (Work.Spaces.DzIter m f) := by
  have h1 : Work.Spaces.Dz f = Work.Spaces.DzIter 1 f := rfl
  rw [h1, ← Work.Spaces.DzIter_add_right m 1 f,
    show m + 1 = 1 + m from by omega, Work.Spaces.DzIter_add_right 1 m f]
  rfl

theorem angw_zero (α : ℝ) (θ : ℝ) : angw α 0 θ = sEta θ := by simp [angw]

theorem angw_pos (α : ℝ) {i : ℕ} (hi : 1 ≤ i) (θ : ℝ) : angw α i θ = sGam α θ := by
  simp only [angw]
  rw [if_neg (by omega)]

theorem measurable_angZ : Measurable angZ := by
  have h : angZ = fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) := rfl
  rw [h]; fun_prop

theorem measurable_angM (α : ℝ) : Measurable (angM α) := by
  have h : angM α = fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := rfl
  rw [h]; fun_prop

/-- A single block of the `ℋ^k`-integrand is dominated by the whole integrand. -/
theorem hblk_le_HkIntegrand (α : ℝ) (k : ℕ) (φ : ℝ → ℝ → ℝ) (i m : ℕ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : hblk α k φ (i, m) z θ ≤ Work.Spaces.HkIntegrand α k φ z θ := by
  by_cases h : i + m ≤ k
  · rw [HkIntegrand_eq_hblk α k φ hθ]
    refine le_trans (Finset.single_le_sum (s := Finset.range (k + 1))
      (f := fun m' => hblk α k φ (i, m') z θ)
      (fun m' _ => hblk_nonneg α k φ (i, m') z θ hθ) (a := m)
      (Finset.mem_range.mpr (by omega))) ?_
    exact Finset.single_le_sum (s := Finset.range (k + 1))
      (f := fun i' => ∑ m' ∈ Finset.range (k + 1), hblk α k φ (i', m') z θ)
      (fun i' _ => Finset.sum_nonneg (fun m' _ => hblk_nonneg α k φ (i', m') z θ hθ)) (a := i)
      (Finset.mem_range.mpr (by omega))
  · rw [hblk_eq_zero α k φ (i, m) z θ h]
    exact Work.Spaces.HkIntegrand_nonneg α k φ z θ

/-- The `θ`-slice integral of a single block of the `ℋ^k`-integrand is finite, as soon as the
integrand is honest. -/
theorem hblk_Iθ_lt_top (α : ℝ) (k : ℕ) (φ : ℝ → ℝ → ℝ) (hφ : SmoothOpen φ)
    (hm : Work.Spaces.HkMem α k φ) (i m : ℕ) {z : ℝ} (hz : 0 < z) :
    ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (hblk α k φ (i, m) z θ) < ⊤ := by
  have hInt : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k φ z θ) Work.Spaces.Iθ :=
    hm.1 z (le_of_lt hz)
  have haesm : AEStronglyMeasurable (fun θ => Work.Spaces.HkIntegrand α k φ z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd _ (hφ.continuousOn_HkIntegrand α k) hz
  have hbnd : ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k φ z θ) < ⊤ :=
    lt_top_iff_ne_top.mpr ((MeasureTheory.lintegral_ofReal_ne_top_iff_integrable haesm
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k φ z θ)).mpr hInt)
  exact lt_of_le_of_lt (lintegral_mono_ae (by
    filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from
      measurableSet_Icc)] with θ hθ
    exact ENNReal.ofReal_le_ofReal (hblk_le_HkIntegrand α k φ i m hθ))) hbnd

/-- **The `z`-slice of `D_z V`, against a general angular weight, is finite.**  This is the
`D_z`-form of the slice lemma `SliceZDeriv_finite`. -/
theorem sliceDz_lintegral_lt_top (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ)
    (hwth : ∀ θ, 0 ≤ wth θ) (hwthmeas : Measurable wth)
    (hsm : ContDiffOn ℝ 2 (Function.uncurry V) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hG : ∀ z ∈ Set.Ioi (0 : ℝ),
      ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ENNReal.ofReal ((V z θ * wth θ) ^ 2) < ⊤)
    (hB : ∀ z ∈ Set.Ioi (0 : ℝ), ∃ δ : ℝ, 0 < δ ∧
      ∫⁻ z' in Set.Ioo z (z + δ), ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal ((Work.Spaces.pzIter 2 V z' θ * wth θ) ^ 2) < ⊤)
    {z : ℝ} (hz : 0 < z) :
    ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2) < ⊤ := by
  have h1 := SliceZDeriv_finite V wth hwth hwthmeas hsm hG hB hz
  rw [lintegral_Iθ_eq_Ioo]
  have hEq : ∀ θ : ℝ, ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2)
      = ENNReal.ofReal ((z * Work.Spaces.w z) ^ 2)
        * ENNReal.ofReal ((Work.Spaces.pz V z θ * wth θ) ^ 2) := by
    intro θ
    have hpt : (Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2
        = (z * Work.Spaces.w z) ^ 2 * (Work.Spaces.pz V z θ * wth θ) ^ 2 := by
      simp only [Work.Spaces.Dz]
      ring
    rw [hpt, ENNReal.ofReal_mul (by positivity)]
  rw [lintegral_congr_ae (Filter.Eventually.of_forall hEq)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h1

/-- The raw shape of the open-quadrant smoothness hypothesis. -/
theorem smooth_raw {φ : ℝ → ℝ → ℝ} (h : SmoothOpen φ) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  fun n => (smoothOpen_iff_forall φ).mp h n

/-- The second radial derivative of `f`, as a `SmoothOpen` function. -/
theorem smooth_zsqPz2 (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f) :
    SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) := by
  have h1 : (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) = zsqPz2 f := rfl
  rw [h1]; exact SmoothOpen_zsqPz2 f hf

/-- The global `z`-`θ` `lintegral` of the `ℋ^k`-integrand of `z²∂_z²f` is finite. -/
theorem global_zsqPz2_lt_top (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f)
    (hmQ : Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ)) :
    (∫⁻ z' in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z' θ)) < ⊤ := by
  have hQSm : SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) := smooth_zsqPz2 f hf
  have h := LkSq_lt_top α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) hQSm hmQ
  rw [LkSq] at h
  rw [MeasureTheory.lintegral_lintegral_swap
    ((aesm_HkIntegrand_prod α k _ hQSm).prod_swap)] at h
  exact h

/-- **The block of the `ℋ^k`-integrand of `D_z f` at `(0,m)` has finite `θ`-slice integral.** -/
theorem hblk_pure_lt_top (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f)
    (hmf : Work.Spaces.HkMem α k f)
    (hmQ : Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ))
    {m : ℕ} (hm : m ≤ k) {z : ℝ} (hz : 0 < z) :
    ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (hblk α k (Work.Spaces.Dz f) (0, m) z θ) < ⊤ := by
  have hcongr : (fun θ => ENNReal.ofReal (hblk α k (Work.Spaces.Dz f) (0, m) z θ))
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => ENNReal.ofReal ((Work.Spaces.Dz (Work.Spaces.DzIter m f) z θ
        * Work.Spaces.w z * |angZ θ|) ^ 2)) := by
    filter_upwards [ae_mem_Ioo_theta] with θ hθ
    rw [hblk_eq α k (Work.Spaces.Dz f) (0, m) z θ (by omega), angw_zero]
    simp only [hblkR, Work.Spaces.DthIter_zero]
    rw [DzIter_Dz_eq]
    simp only [mul_pow, sq_abs, angZ_sq ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩] <;> ring_nf
  rw [lintegral_congr_ae hcongr]
  have hG : ∀ z' ∈ Set.Ioi (0 : ℝ),
      ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal ((Work.Spaces.DzIter m f z' θ * |angZ θ|) ^ 2) < ⊤ := by
    intro z' hz'
    have hpt : ∀ θ ∈ Work.Spaces.Iθ, hblk α k f (0, m) z' θ
        = (Work.Spaces.w z') ^ 2 * ((Work.Spaces.DzIter m f z' θ * |angZ θ|) ^ 2) := by
      intro θ hθ
      rw [hblk_eq α k f (0, m) z' θ (by omega), angw_zero]
      simp only [hblkR, Work.Spaces.DthIter_zero]
      simp only [mul_pow, sq_abs, angZ_sq hθ] <;> ring_nf
    have hrel : (fun θ => ENNReal.ofReal (hblk α k f (0, m) z' θ))
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ => ENNReal.ofReal ((Work.Spaces.w z') ^ 2)
          * ENNReal.ofReal ((Work.Spaces.DzIter m f z' θ * |angZ θ|) ^ 2)) := by
      filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from
        measurableSet_Icc)] with θ hθ
      rw [hpt θ hθ, ENNReal.ofReal_mul (by positivity)]
    have h4 : ENNReal.ofReal ((Work.Spaces.w z') ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((Work.Spaces.DzIter m f z' θ * |angZ θ|) ^ 2)) < ⊤ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne, lintegral_congr_ae hrel.symm]
      exact hblk_Iθ_lt_top α k f hf hmf 0 m hz'
    have hpos : ENNReal.ofReal ((Work.Spaces.w z') ^ 2) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      have hthis : (0 : ℝ) < ((1 + z') ^ 2 / z' ^ 2) ^ 2 := by
        have hz'pos : (0 : ℝ) < z' := hz'
        positivity
      simpa only [Work.Spaces.w] using hthis
    rcases ENNReal.mul_lt_top_iff.mp h4 with ⟨-, h⟩ | h0 | h0
    · rwa [lintegral_Iθ_eq_Ioo] at h
    · exact absurd h0 hpos
    · rw [← lintegral_Iθ_eq_Ioo, h0]; exact ENNReal.zero_lt_top
  have hB : ∀ z' ∈ Set.Ioi (0 : ℝ), ∃ δ : ℝ, 0 < δ ∧
      ∫⁻ z'' in Set.Ioo z' (z' + δ), ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal ((Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z'' θ
          * |angZ θ|) ^ 2) < ⊤ := by
    intro z' hz'
    refine ⟨1, one_pos, ?_⟩
    have hglob := global_zsqPz2_lt_top α k f hf hmQ
    have hstep : (∫⁻ z'' in Set.Ioo z' (z' + 1), ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          ENNReal.ofReal ((Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z'' θ
            * |angZ θ|) ^ 2))
        ≤ (∫⁻ z'' in Set.Ioo z' (z' + 1), ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z'' θ)) := by
      refine lintegral_mono_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet (Set.Ioo z' (z' + 1)) from
        measurableSet_Ioo)] with z'' hz''
      have hz''0 : 0 < z'' := lt_trans hz' hz''.1
      refine le_trans ?_ (lintegral_mono_ae (by
        filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from
          measurableSet_Icc)] with θ hθ
        exact ENNReal.ofReal_le_ofReal (hblk_le_HkIntegrand α k
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) 0 m hθ)))
      rw [← lintegral_Iθ_eq_Ioo]
      refine lintegral_mono_ae ?_
      filter_upwards [ae_mem_Ioo_theta] with θ hθ
      have hcom := AgmonSlice.zsq_pzIter2_mixed_open f (smooth_raw hf) m 0 hz''0 hθ
      have hcom' : Work.Spaces.DzIter m (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z'' θ
          = z'' ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z'' θ := by
        simpa only [Work.Spaces.mixed, Work.Spaces.DthIter_zero] using hcom.symm
      have hval2 : hblk α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) (0, m) z'' θ
          = (1 + z'') ^ 4
            * (Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z'' θ * angZ θ) ^ 2 := by
        rw [hblk_eq α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) (0, m) z'' θ (by omega),
          angw_zero]
        simp only [hblkR, Work.Spaces.DthIter_zero]
        rw [hcom']
        simp only [mul_pow, angZ_sq ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩]
        have hzne : z'' ≠ 0 := ne_of_gt hz''0
        rw [Work.Spaces.w]
        field_simp
      rw [hval2]
      have hsq : ENNReal.ofReal ((Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z'' θ
            * |angZ θ|) ^ 2)
          = ENNReal.ofReal ((Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z'' θ
              * angZ θ) ^ 2) := by
        congr 1
        simp only [mul_pow, sq_abs]
      rw [hsq]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : (1 : ℝ) ≤ (1 + z'') ^ 4 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + z'')
      have h2 : (0 : ℝ) ≤ (Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z'' θ * angZ θ) ^ 2 :=
        sq_nonneg _
      simpa using mul_le_mul_of_nonneg_right h1 h2
    have hdom : (∫⁻ z'' in Set.Ioo z' (z' + 1), ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z'' θ))
        ≤ (∫⁻ z'' in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z'' θ)) :=
      MeasureTheory.lintegral_mono_set
        (fun z'' hz'' => show z'' ∈ Work.Spaces.Iz from
          le_of_lt (lt_trans (show (0 : ℝ) < z' from hz') hz''.1))
    exact lt_of_le_of_lt (le_trans hstep hdom) hglob
  exact sliceDz_lintegral_lt_top (Work.Spaces.DzIter m f) (fun θ => |angZ θ|)
    (fun θ => abs_nonneg _) measurable_angZ.abs
    (show ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.DzIter m f))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) from (hf.DzIter m).forall 2) hG hB hz

theorem hblk_mixed_lt_top (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f)
    (hmf : Work.Spaces.HkMem α k f)
    (hmQ : Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ))
    {i m : ℕ} (hi : 1 ≤ i) (him : i + m ≤ k) {z : ℝ} (hz : 0 < z) :
    ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (hblk α k (Work.Spaces.Dz f) (i, m) z θ) < ⊤ := by
  have hcongr : (fun θ => ENNReal.ofReal (hblk α k (Work.Spaces.Dz f) (i, m) z θ))
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => ENNReal.ofReal ((Work.Spaces.Dz (Work.Spaces.mixed m i f) z θ
        * Work.Spaces.w z * |angM α θ|) ^ 2)) := by
    filter_upwards [ae_mem_Ioo_theta] with θ hθ
    have hcom : Work.Spaces.DzIter m (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
        = Work.Spaces.Dz (Work.Spaces.mixed m i f) z θ := by
      rw [show Work.Spaces.DzIter m (Work.Spaces.DthIter i (Work.Spaces.Dz f))
          = Work.Spaces.mixed m i (Work.Spaces.Dz f) from rfl,
        show Work.Spaces.mixed m i (Work.Spaces.Dz f)
          = Work.Spaces.mixed m i (Work.Spaces.DzIter 1 f) from rfl,
        AgmonSlice.mixed_DzIter_open f hf m i 1 z θ hz hθ.1 hθ.2]
      rfl
    rw [hblk_eq α k (Work.Spaces.Dz f) (i, m) z θ (by omega), angw_pos α hi]
    simp only [hblkR]
    rw [hcom]
    simp only [mul_pow, sq_abs, angM_sq α ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩] <;> ring_nf
  rw [lintegral_congr_ae hcongr]
  have hG : ∀ z' ∈ Set.Ioi (0 : ℝ),
      ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal ((Work.Spaces.mixed m i f z' θ * |angM α θ|) ^ 2) < ⊤ := by
    intro z' hz'
    have hpt : ∀ θ ∈ Work.Spaces.Iθ, hblk α k f (i, m) z' θ
        = (Work.Spaces.w z') ^ 2 * ((Work.Spaces.mixed m i f z' θ * |angM α θ|) ^ 2) := by
      intro θ hθ
      rw [hblk_eq α k f (i, m) z' θ (by omega), angw_pos α hi]
      simp only [hblkR]
      simp only [Work.Spaces.mixed, mul_pow, sq_abs, angM_sq α hθ] <;> ring_nf
    have hrel : (fun θ => ENNReal.ofReal (hblk α k f (i, m) z' θ))
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ => ENNReal.ofReal ((Work.Spaces.w z') ^ 2)
          * ENNReal.ofReal ((Work.Spaces.mixed m i f z' θ * |angM α θ|) ^ 2)) := by
      filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from
        measurableSet_Icc)] with θ hθ
      rw [hpt θ hθ, ENNReal.ofReal_mul (by positivity)]
    have h4 : ENNReal.ofReal ((Work.Spaces.w z') ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal ((Work.Spaces.mixed m i f z' θ * |angM α θ|) ^ 2)) < ⊤ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne, lintegral_congr_ae hrel.symm]
      exact hblk_Iθ_lt_top α k f hf hmf i m hz'
    have hpos : ENNReal.ofReal ((Work.Spaces.w z') ^ 2) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      have hthis : (0 : ℝ) < ((1 + z') ^ 2 / z' ^ 2) ^ 2 := by
        have hz'pos : (0 : ℝ) < z' := hz'
        positivity
      simpa only [Work.Spaces.w] using hthis
    rcases ENNReal.mul_lt_top_iff.mp h4 with ⟨-, h⟩ | h0 | h0
    · rwa [lintegral_Iθ_eq_Ioo] at h
    · exact absurd h0 hpos
    · rw [← lintegral_Iθ_eq_Ioo, h0]; exact ENNReal.zero_lt_top
  have hB : ∀ z' ∈ Set.Ioi (0 : ℝ), ∃ δ : ℝ, 0 < δ ∧
      ∫⁻ z'' in Set.Ioo z' (z' + δ), ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal ((Work.Spaces.pzIter 2 (Work.Spaces.mixed m i f) z'' θ
          * |angM α θ|) ^ 2) < ⊤ := by
    intro z' hz'
    refine ⟨1, one_pos, ?_⟩
    have hglob := global_zsqPz2_lt_top α k f hf hmQ
    have hstep : (∫⁻ z'' in Set.Ioo z' (z' + 1), ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          ENNReal.ofReal ((Work.Spaces.pzIter 2 (Work.Spaces.mixed m i f) z'' θ
            * |angM α θ|) ^ 2))
        ≤ (∫⁻ z'' in Set.Ioo z' (z' + 1), ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z'' θ)) := by
      refine lintegral_mono_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet (Set.Ioo z' (z' + 1)) from
        measurableSet_Ioo)] with z'' hz''
      have hz''0 : 0 < z'' := lt_trans hz' hz''.1
      refine le_trans ?_ (lintegral_mono_ae (by
        filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from
          measurableSet_Icc)] with θ hθ
        exact ENNReal.ofReal_le_ofReal (hblk_le_HkIntegrand α k
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) i m hθ)))
      rw [← lintegral_Iθ_eq_Ioo]
      refine lintegral_mono_ae ?_
      filter_upwards [ae_mem_Ioo_theta] with θ hθ
      have hcomA := AgmonSlice.zsq_pzIter2_mixed_open f (smooth_raw hf) m i hz''0 hθ
      have hcom' : Work.Spaces.DzIter m (Work.Spaces.DthIter i
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ)) z'' θ
          = z'' ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.mixed m i f) z'' θ := by
        simpa only [Work.Spaces.mixed] using hcomA.symm
      have hval2 : hblk α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) (i, m) z'' θ
          = (1 + z'') ^ 4
            * (Work.Spaces.pzIter 2 (Work.Spaces.mixed m i f) z'' θ * angM α θ) ^ 2 := by
        rw [hblk_eq α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) (i, m) z'' θ (by omega),
          angw_pos α hi]
        simp only [hblkR]
        rw [hcom']
        simp only [mul_pow, angM_sq α ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩]
        have hzne : z'' ≠ 0 := ne_of_gt hz''0
        rw [Work.Spaces.w]
        field_simp
      rw [hval2]
      have hsq : ENNReal.ofReal ((Work.Spaces.pzIter 2 (Work.Spaces.mixed m i f) z'' θ
            * |angM α θ|) ^ 2)
          = ENNReal.ofReal ((Work.Spaces.pzIter 2 (Work.Spaces.mixed m i f) z'' θ
              * angM α θ) ^ 2) := by
        congr 1
        simp only [mul_pow, sq_abs]
      rw [hsq]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : (1 : ℝ) ≤ (1 + z'') ^ 4 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + z'')
      have h2 : (0 : ℝ) ≤ (Work.Spaces.pzIter 2 (Work.Spaces.mixed m i f) z'' θ * angM α θ) ^ 2 :=
        sq_nonneg _
      simpa using mul_le_mul_of_nonneg_right h1 h2
    have hdom : (∫⁻ z'' in Set.Ioo z' (z' + 1), ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z'' θ))
        ≤ (∫⁻ z'' in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z'' θ)) :=
      MeasureTheory.lintegral_mono_set
        (fun z'' hz'' => show z'' ∈ Work.Spaces.Iz from
          le_of_lt (lt_trans (show (0 : ℝ) < z' from hz') hz''.1))
    exact lt_of_le_of_lt (le_trans hstep hdom) hglob
  exact sliceDz_lintegral_lt_top (Work.Spaces.mixed m i f) (fun θ => |angM α θ|)
    (fun θ => abs_nonneg _) (measurable_angM α).abs
    (show ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.mixed m i f))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) from (hf.mixed m i).forall 2) hG hB hz

/-- **The pointwise-in-`z` honesty of `HkIntegrand α k (D_z f)`.** -/
theorem HkMem_Dz_slices (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (hf : SmoothOpen f)
    (hmf : Work.Spaces.HkMem α k f)
    (hmQ : Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ)) :
    ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k (Work.Spaces.Dz f) z θ)
        Work.Spaces.Iθ := by
  intro z hz
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
  · subst h0
    have h : (fun θ => Work.Spaces.HkIntegrand α k (Work.Spaces.Dz f) 0 θ)
        = fun _ => (0 : ℝ) := by
      funext θ; exact Work.Coercivity.HkIntegrand_zero_left α k (Work.Spaces.Dz f) θ
    rw [h]; exact integrableOn_zero
  · have hDzSm : SmoothOpen (Work.Spaces.Dz f) := hf.Dz
    have haesm : AEStronglyMeasurable
        (fun θ => Work.Spaces.HkIntegrand α k (Work.Spaces.Dz f) z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd _ (hDzSm.continuousOn_HkIntegrand α k) hz0
    have hfin : (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Work.Spaces.Dz f) z θ)) < ⊤ := by
      have hpt : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Work.Spaces.Dz f) z θ)
            = ∑ i ∈ Finset.range (k + 1), ∑ m ∈ Finset.range (k + 1),
                ENNReal.ofReal (hblk α k (Work.Spaces.Dz f) (i, m) z θ) := by
        filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from
          measurableSet_Icc)] with θ hθ
        rw [HkIntegrand_eq_hblk α k (Work.Spaces.Dz f) hθ]
        rw [ENNReal.ofReal_sum_of_nonneg
          (fun i _ => Finset.sum_nonneg (fun m _ =>
            hblk_nonneg α k (Work.Spaces.Dz f) (i, m) z θ hθ))]
        exact Finset.sum_congr rfl fun i _ =>
          ENNReal.ofReal_sum_of_nonneg
            (fun m _ => hblk_nonneg α k (Work.Spaces.Dz f) (i, m) z θ hθ)
      have haesm_blk : ∀ i m : ℕ, AEMeasurable
          (fun θ => ENNReal.ofReal (hblk α k (Work.Spaces.Dz f) (i, m) z θ))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := fun i m =>
        ((Work.Spaces.aesm_slice_of_continuousOn_Qd _
          (continuousOn_hblk_Q0 α k (Work.Spaces.Dz f) (smooth_raw hDzSm) i m) hz0).aemeasurable).ennreal_ofReal
      rw [lintegral_congr_ae hpt]
      have houter := MeasureTheory.lintegral_finsetSum' (s := Finset.range (k + 1))
        (f := fun i a => ∑ m ∈ Finset.range (k + 1),
          ENNReal.ofReal (hblk α k (Work.Spaces.Dz f) (i, m) z a))
        (fun i _ => (Finset.aemeasurable_sum (Finset.range (k + 1))
          (fun m _ => haesm_blk i m)).congr
          (Filter.Eventually.of_forall fun a => by simp only [Finset.sum_apply]))
      rw [houter]
      refine ENNReal.sum_lt_top.mpr (fun i hi => ?_)
      have hinner := MeasureTheory.lintegral_finsetSum' (s := Finset.range (k + 1))
        (f := fun m a => ENNReal.ofReal (hblk α k (Work.Spaces.Dz f) (i, m) z a))
        (fun m _ => haesm_blk i m)
      rw [hinner]
      refine ENNReal.sum_lt_top.mpr (fun m hm => ?_)
      by_cases him : i + m ≤ k
      · rcases eq_or_ne i 0 with h | h
        · subst h
          exact hblk_pure_lt_top α k f hf hmf hmQ (by omega) hz0
        · exact hblk_mixed_lt_top α k f hf hmf hmQ (by omega) him hz0
      · have hzero : (fun θ => ENNReal.ofReal (hblk α k (Work.Spaces.Dz f) (i, m) z θ))
            = fun _ => (0 : ℝ≥0∞) := by
          funext θ
          rw [hblk_eq_zero α k (Work.Spaces.Dz f) (i, m) z θ him]
          simp
        rw [hzero, lintegral_zero]
        exact ENNReal.zero_lt_top


    refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable haesm
      (Filter.Eventually.of_forall fun θ =>
        Work.Spaces.HkIntegrand_nonneg α k (Work.Spaces.Dz f) z θ)).mp ?_
    exact lt_top_iff_ne_top.mp hfin

end Cert


/-! ## The last bridges -/

/-- The second `HkMem` conjunct of `g`, from the finiteness of `LkSq α k g`. -/
theorem integrableOn_sliceIntegral_of_LkSq_lt_top (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ)
    (hg : SmoothOpen g) (h : LkSq α k g < ⊤) :
    IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
      Work.Spaces.Iz := by
  have hprod : AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k g p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    aesm_HkIntegrand_prod α k g hg
  have hswap : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ)) < ⊤ := by
    rw [LkSq] at h
    rwa [MeasureTheory.lintegral_lintegral_swap (hprod.prod_swap)] at h
  have hA : AEMeasurable (fun z => ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hprod.lintegral_prod_right'
  have hintA : Integrable (fun z => (∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ)).toReal)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    MeasureTheory.integrable_toReal_of_lintegral_ne_top hA (ne_of_lt hswap)
  have hpos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), (0 : ℝ) < z := by
    rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioi
  refine hintA.congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from
    measurableSet_Ici), hpos] with z hz hzpos
  exact (MeasureTheory.integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)
    (Work.Spaces.aesm_slice_of_continuousOn_Qd _ (hg.continuousOn_HkIntegrand α k) hzpos)).symm

/-- The `θ`-integrated Agmon interface, assembled from the one-dimensional estimate. -/
theorem hgen_of_agmon : ∃ C : ℝ, 0 < C ∧
    (∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), SmoothOpen V →
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) * (MeasureTheory.lintegral
          (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))
          (fun θ => MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
            (fun z => ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))))
        ≤ ENNReal.ofReal (C ^ 2) *
            (ENNReal.ofReal (α ^ 4) * (MeasureTheory.lintegral
                (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))
                (fun θ => MeasureTheory.lintegral
                  (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                  (fun z => ENNReal.ofReal
                    ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))))
              + (MeasureTheory.lintegral
                  (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))
                  (fun θ => MeasureTheory.lintegral
                    (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                    (fun z => ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2)))))) := by
  obtain ⟨C, hC, h1D⟩ := DzAgmon1D_lintegral
  refine ⟨C, hC, ?_⟩
  intro α hα hα1 V wth hV hwth
  exact TermAgmon C hC h1D α V wth hα hα1 hV hwth

/-- **Agmon--Nirenberg (interpolation) for `D_z = z∂_z` in the weighted `H^k`-norm.**  For `f` smooth on the open quadrant and in `H^k` (with `z²∂_zzf` also in `H^k`, i.e. the honesty of its integrands),

`α · |D_z f|_{ℋ^k} ≤ C (|f|_{ℋ^k} + α² |z²∂_zzf|_{ℋ^k})`   for `0 < α ≤ 1`,

and `D_z f ∈ H^k`.  This is the elementary interpolation converting the single `z`-derivative occurring in the modulation operators into the second one, which is what the elliptic equation controls; the weight `w(z) = (1+z)²/z²` is what makes the boundary term at `z = 0` disappear.

ROUTE.  Slicewise in `z`: for `g = f(z,·)` and `h = z²∂_zzf(z,·)` (so `D_z f(z,·) = z ∂_z(f(z,·))`), the pointwise AMGM `α|a| ≤ C(|a| + α²|b|)`-type bound is applied to the *pair* `(a,b) = (D_z f, z²∂_zzf)` after the identity `z·D_z(z∂_zf) = z²∂_zzf + D_zf`; the cleanest route is the weighted AMGM in `z` (`Work.FTS.EllipticEst.zAMGM_Hk_le`, `Work.FTS.EllipticEst.zAMGM_weighted`, both axiom-clean) applied to the `ℋ^k`-integrands: for every `z > 0`,

`α² (D_zf z θ)² ≤ 2(f z θ)² + 2α⁴ (z²∂_zzf z θ)²`  is false pointwise, so instead use the `z`-integration by parts: `∫_0^∞ z^2 w(z)^2 (∂_z f)^2 dz = -2∫ z^2 w ∂_z w f ∂_z f dz - 2∫ z w^2 f ∂_z f dz` (the boundary terms vanish because `f` is smooth on the quadrant and `w` is integrable at `0` and `∞`), followed by `2|ab| ≤ εa² + b²/ε`; this is the standard weighted Agmon–Nirenberg argument of `Work.FTS.EllipticEst.zAMGM_weighted`.  The `HkMem` hypotheses make the integrals honest and give `HkMem(D_z f)`. -/
theorem HkNorm_Dz_amgm (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
      Work.Spaces.HkMem α k f →
      Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz f) ∧
        α * Work.Spaces.HkNorm α k (Work.Spaces.Dz f)
          ≤ C * (Work.Spaces.HkNorm α k f
              + α ^ 2 * Work.Spaces.HkNorm α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ)) := by
  obtain ⟨C, hC, hgen⟩ := hgen_of_agmon
  refine ⟨C, hC, ?_⟩
  intro α f hα hα1 hf hmf hmQ
  have hF : SmoothOpen f := smoothOpen_of_forall hf
  have hmQ' : Work.Spaces.HkMem α k (zsqPz2 f) := hmQ
  have hmDz : Work.Spaces.HkMem α k (Work.Spaces.Dz f) :=
    ⟨HkMem_Dz_slices α k f hF hmf hmQ',
      integrableOn_sliceIntegral_of_LkSq_lt_top α k (Work.Spaces.Dz f) hF.Dz
        (LkSq_Dz_lt_top C hC hgen α hα hα1 k f hF hmf hmQ')⟩
  exact ⟨hmDz, HkNorm_Dz_le_of C hC hgen α hα hα1 k f hF hmf hmQ' hmDz⟩

end Work.FTS.EllipticEst.Blocks
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.aeUHk_mem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux

/-- **The level-`0` `ℋ`-honesty of the solution in the a.e. class.**  For every `AeData α u G`,
i.e. for every `u` solving `bslOp α u = G` on the open quadrant with the two a.e. moment
conditions (plus `HkMem` of `G`, of `z²∂_zz u` and of `∂_θθ u`), one has `HkMem α 0 u`.

The mathematics is the a.e. slicewise second-order Poincaré inequality
`∫_θ u(z,θ)²σ θ ≤ C ∫_θ (∂_θθ u)(z,θ)²σ θ` (`σ = sin(2θ)^{-η}`), valid for a.e. `z > 0`: the
two moment conditions kill the affine mode invisible to `∂_θθ`, and the endpoint behaviour of
the slices at `θ → π/2` removes the rest.  That slice bound is `H2W.Ae.aesliceU_of`, fed with
the two-derivative weighted Hardy inequality `H2W.Ae.ZeroHardy.sliceZeroLimitHardy` and
`H2W.Ae.AeSliceRightTendsto`; it is then integrated in `z` against `HkMem`-honesty of `u`'s
slices.

The proof is the one of `Work.FTS.EllipticEst.H2W.Ae.hkMem_u`; we cite the definitionally
identical, self-contained clean-cone copy `Work.FTS.EllipticEst.H2W.AngBW.S3.hkMem_u`
(module `H2W/AngBW/Step3/HkMemU.lean`), whose import cone avoids
`Honest.firstOrderHonest` — the one module of the canonical `H2W/Ae/hkMem_u.lean` cone that is
currently unbuildable (its environment carries the declaration
`Work.FTS.EllipticEst.Honest.contDiffOn_slice` from both `Honest.HonDifQuotBound` and
`Honest.HonSliceRightTendsto`). -/
theorem aeUHk_mem : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G → Work.Spaces.HkMem α 0 u :=
  fun α u G h => Work.FTS.EllipticEst.H2W.AngBW.S3.hkMem_u α u G h

end Work.FTS.EllipticEst.Cores.AeStep2Aux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.ShiftOfTwoLe =====
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
set_option maxHeartbeats 800000

/-- **The assembly of the shift, given the two moment conditions.**

This is `ShiftOfTwoLe` with the two analytic inputs (`F_*(D_z F) = 0` and `F_*(D_z Ψ) = 0`)
supplied as explicit hypotheses; the target `ShiftOfTwoLe` below instantiates them with the
sibling modules.  The `k ≥ 1` version suffices here. -/
theorem shiftOfTwoLe_of_moments {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    (hmomF : ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F) z = 0)
    (hmomΨ : ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z = 0) :
    Work.FTS.EllipticEst.TT.EllWeakPos α (k - 1)
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) := by
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.TT.EllWeakPos.smoothOpen h
  -- the source coincides with `bslOp α Ψ` on the open quadrant, hence is smooth there
  have hSF : Work.FTS.EllipticEst.SmoothOpen F :=
    Work.FTS.EllipticEst.AeMom.Repair.SmoothOpen_of_bslOp_eq hSΨ
      (fun z θ hz hθ hlt => h.1 z hz θ hθ hlt)
  -- `∂_θ²Ψ` is smooth on the open quadrant as well
  have hSpth2 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := by
    have h1 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pth Ψ) :=
      Work.FTS.EllipticEst.SmoothOpen.pth hSΨ
    have h2 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pth (Work.Spaces.pth Ψ)) :=
      Work.FTS.EllipticEst.SmoothOpen.pth h1
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the equation: `bslOp` commutes with `D_z`
    exact Work.FTS.EllipticEst.TT.bslOp_DzIter_eq α F Ψ 1 h.smooth h.1
  · -- the Dirichlet datum at `θ = 0`
    exact Work.FTS.EllipticEst.TT.DzIter_zero_at_zero Ψ 1 h.zero
  · -- the Dirichlet datum at `θ = π/2`
    exact Work.FTS.EllipticEst.TT.DzIter_zero_at_pi_half Ψ 1 h.pi_half
  · -- the source moment condition
    exact hmomF
  · -- the solution moment condition
    exact hmomΨ
  · -- smoothness on the open quadrant is preserved by `D_z`
    intro n
    exact (Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.DzIter 1 Ψ)).mp
      (Work.FTS.EllipticEst.TT.EllWeakPos.smoothOpen_DzIter h 1) n
  · -- `D_z F ∈ ℋ^{k-1}`
    have hmem : Work.Spaces.HkMem α (k - 1) (Work.Spaces.Dz F) :=
      Work.FTS.EllipticEst.AeMom.Repair.HkMem_Dz_shift hk hSF h.memF
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using hmem
  · -- `z² ∂_zz(D_z Ψ) ∈ ℋ^{k-1}`
    have hG : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
      Work.FTS.EllipticEst.AeMom.Repair.SmoothOpen.zsq_mul
        (Work.FTS.EllipticEst.SmoothOpen.pzIter hSΨ 2)
    have hmem : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.Dz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
      Work.FTS.EllipticEst.AeMom.Repair.HkMem_Dz_shift hk hG h.memA
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) hmem ?_
    intro z hz θ hθ
    exact (Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm Ψ hSΨ 1 0
      (show ((z, θ) : ℝ × ℝ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)
        from ⟨hz, hθ⟩)).symm
  · -- `∂_θθ(D_z Ψ) ∈ ℋ^{k-1}`
    have hmem : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)) :=
      Work.FTS.EllipticEst.AeMom.Repair.HkMem_Dz_shift hk hSpth2 h.memB
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) hmem ?_
    intro z hz θ hθ
    exact Work.FTS.EllipticEst.AeMom.Repair.Dz_pthIter_two_comm hSΨ z θ hz hθ.1 hθ.2
  · -- `z ∂_z ∂_θθ(D_z Ψ) ∈ ℋ^{k-1}`
    have hGs : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) :=
      Work.FTS.EllipticEst.SmoothOpen.Dz hSpth2
    have hmem : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.Dz (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)) :=
      Work.FTS.EllipticEst.AeMom.Repair.HkMem_Dz_shift hk hGs h.memZPth2
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) hmem ?_
    intro z hz θ hθ
    have hEqOn : Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)))
        (Function.uncurry (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      rintro ⟨z', θ'⟩ ⟨hz', hθ'⟩
      exact Work.FTS.EllipticEst.AeMom.Repair.Dz_pthIter_two_comm hSΨ z' θ' hz' hθ'.1 hθ'.2
    have hpe : Work.Spaces.pz (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) z θ
        = Work.Spaces.pz (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ :=
      Work.Spaces.pz_congr_of_isOpen (isOpen_Ioi.prod isOpen_Ioo) hEqOn.symm ⟨hz, hθ⟩
    rw [hpe]
    rfl

/-- **The radially differentiated data are again of the weak class, one level down** (Elgindi,
the induction step of `prop:Hk`). -/
theorem ShiftOfTwoLe {α : ℝ} {k : ℕ} (hk : 2 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    Work.FTS.EllipticEst.TT.EllWeakPos α (k - 1)
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) :=
  shiftOfTwoLe_of_moments (by omega) h
    (Work.FTS.EllipticEst.remov.Fstar_DzIter_one_F_ge_two hk h)
    (Work.FTS.EllipticEst.remov.Fstar_DzIter_one_Psi (by omega) h)

end Work.FTS.EllipticEst.Cores
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.HkMem_zero_slices =====
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
set_option maxHeartbeats 1000000

/-! ## Helper A : `∂_θ^n` commutes with multiplication by the first variable -/

/-! ## Helper B : Clairaut for `∂_z` against `∂_θ²` -/

/-! ## Helper C : `∂_θ²` commutes with `D_z` -/

/-! ## Helper D : the requested commutation of `∂_θ²` with `D_z^j` -/

/-! ## Helper E : `bslOp α Ψ` is `C^∞` on the open quadrant for `Ψ` merely `C^∞` there -/

/-! ## Helper F : the source of the weak class is `C^∞` on the open quadrant -/

/-! ## The target lemma -/

end Work.FTS.EllipticEst.H2W
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.PsiSlices.ReductionsB =====
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

/-! ## The `D_z`-shifted propagations

The same argument applies verbatim to every `D_z`-shift of the datum: `(D_z^j F, D_z^j Ψ)` solves
the same equation on the open quadrant (`TT.bslOp_DzIter_eq`), and the shifted source slice is
`sinθcos²θ`-integrable for `j ≤ 2` (`DzIter_source_sigmaIntegrable`, from `lzeroSliceFiber` and
the triangular relation `D_z^j = ∑ z^i ∂_z^i`). -/




/-! ## The assembly: the target reduces to the *source honesty* of the first two levels

Combining the one-variable bridge with the level identities (`H2W.PsiSlices.pzIterLevelIdentities`)
and the source-side slices (`lzeroSliceFiber`) gives the exact reduction

  `pzIterSliceIntegrable`  ⟸  for a.e. `z`, `Lzero1(∂_zΨ(z,·))` and `Lzero1(∂_z²Ψ(z,·))` are
  `sinθcos²θ`-integrable,

where the hypothesis is the *datum-side endpoint rigidity* of the weak class (the chapter's
documented bottleneck): the level-`m` identity has a `γ_m·∂_z^mΨ` term, so the regress of the
`z`-levels can only be closed by controlling the sources themselves.  Everything else is proved
here. -/


end
end Work.FTS.EllipticEst.H2W.PsiSlices
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.aSliceHonest =====
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
set_option maxHeartbeats 1000000

/-! ## `∂_θ`-iterates of a function smooth on the open quadrant -/

/-! ## Clairaut at the level of the iterated plain derivatives -/

/-! ## The pointwise identity for the slice of `z²∂_z²Ψ` -/

/-! ## Honesty of a slice from `ℋ⁰`-membership -/

/-! ## The target -/

end Work.FTS.EllipticEst.H2W
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.pzIterBoxIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `H2W.pzIterBoxIntegrable` — slice and box integrability of the first four `z`-slices

Target: for a datum `(F, Ψ)` of the weak class `Work.FTS.EllipticEst.WeakPos2 α F Ψ`
(`0 < α ≤ 1/4`), for almost every `z₀ > 0` there is `ε > 0` with `ε < z₀` such that

* for every `j ≤ 3` and every `z` in `(z₀ - ε, z₀ + ε)` the angular slice
  `θ ↦ ∂_z^jΨ(z,θ)·sinθcos²θ` is integrable on `Iθ = [0, π/2]`;
* for every `j ≤ 3` the function `(s,θ) ↦ |∂_z^jΨ(s,θ)|·sinθcos²θ` is integrable on the
  product `(z₀ - ε, z₀ + ε] × Iθ`.

## What is proved here, and what is delegated

### STATUS (this stretch): the target is the chapter's bottleneck node, and its conclusion is
### available from any of the *documented* inputs below

The target's statement is **not** derivable from `WeakPos2` by any argument available in the
tree: `WeakPos2` carries no honesty for the left-hand-side slots of `Ψ` (`∂_z^jΨ·sinθcos²θ`,
`j ≤ 3` *are* the quantities the target asserts to be honest), the source-tower
`Lzero1(∂_z^mΨ) = ∂_z^mF + α²z²∂_z^{m+2}Ψ + …` has no base case because `HkMem α 2 F` stops at
level `2`, and all of the chapter's weak-class estimates are inequalities between *totalised*
(junk-tolerant) integrals.  The detailed analysis, the precedents (the verdict recorded for the
whole node family is *"mis-stated: the hypothesis list is too weak"*, never *"mathematically
false"*), the source theorem's own hypotheses (the paper's `prop:L2` uses *the unique `L²`
solution* and `R²Ψ → 0` at `R = 0`) and the dead ends are in
`Submission/Work/FTS/EllipticEst/H2W/NOTES_pzIterBoxIntegrable_state2.md` and
`.../WeakPureAux/NOTES_cascade.md`.

What IS available (all proved in this file or in the tree, all axiom-clean) is the target's
conclusion from each of the following inputs, on top of `WeakPos2 α F Ψ`:

| input | consumer lemma |
|---|---|
| `HkMem α 0 (∂_θθ(∂_z^jΨ))`, `j ≤ 3` | `H2W/pzIterBoxIntegrable_of_slots` |
| locally uniform bound on `∫_θ (∂_θ(pzIter m Ψ)(z,·))² sin(2θ)^{-η}`, `m ≤ 3` | `pzIterBoxIntegrable_of_locGradBound` |
| locally uniform bound on `∫_θ (∂_θθ(pzIter m Ψ)(z,·))² sin(2θ)^{-η}`, `m ≤ 3` | `pzIterBoxIntegrable_of_locSecBound` |
| locally uniform pole bound `|∂_z^jΨ| ≤ C(θ⁻¹+(π/2-θ)⁻¹)` | `pzIterBoxIntegrable_of_poleBoundDatum` |
| `SliceSourceMassBound Ψ` | `pzIterBoxIntegrable_of_sourceMass` |
| `SliceMassExternal α F Ψ` (ψ-mass form of the paper's `R²Ψ → 0`) | `pzIterBoxIntegrable_of_externalMass` |
| unweighted `L²`-honesty of `∂_θθ(∂_z^jΨ)`, `j ≤ 3` (per `z` and on the box) | `pzIterBoxIntegrable_of_secDerivSq` (module `H2W/pzIterBoxIntegrableOfSecDerivSq`) |
| the single slot `HkMem α 3 (pthIter 2 Ψ)` | `pzIterBoxIntegrable_of_hkMem3` (same module) |

### The reductions proved in this file

Four reductions are proved, of strictly decreasing strength in their input (the first is the
sharpest and is the one the project should consume):

* **`pzIterBoxIntegrable_of_growth`** — from the *locally uniform angular growth (pole) bound*
  `|∂_z^jΨ(z,θ)| ≤ C·(θ⁻¹ + (π/2-θ)⁻¹)` on a neighbourhood of a.e. `z₀` (with a single `C`).  The
  elementary bound `(θ⁻¹ + (π/2-θ)⁻¹)·sinθcos²θ ≤ 1 + π/2` turns the growth bound into the
  *uniform* bound `|∂_z^jΨ·sinθcos²θ| ≤ C(1+π/2)` on the whole box, the box has finite measure, so
  `Integrable.of_bound` gives both conclusions.
* **`pzIterBoxIntegrable_of_locBound`** — from the strictly weaker input that the *`θ`-integrals*
  `∫⁻_θ |∂_z^jΨ(z,θ)|·|sinθcos²θ|` (`j ≤ 3`) are *locally uniformly bounded* on a neighbourhood of
  a.e. `z₀`.  This is the weakest local-uniformity statement that implies the target: the pole
  bound gives it (integrating `C(θ⁻¹+(π/2-θ)⁻¹)` against `sinθcos²θ` gives `C(1+π/2)`), while the
  *`θ`-pointwise* information is discarded.  The pointwise conjunct comes from `M < ⊤` via
  `hasFiniteIntegral_iff_norm`; the box conjunct from Tonelli (`lintegral_prod`) and the finiteness
  of the measure of the box.
* **`pzIterBoxIntegrable_of_sourceMass`** — from a locally uniform bound on the **source mass**
  `∫_{Iθ} (sinθcos²θ·|Lzero1(∂_z^mΨ)(z,·)| + |∂_z^mΨ(z,π/4)| + |∂_θ∂_z^mΨ(z,π/4)|)`, `m ≤ 3` (the
  project's `SliceSourceMassBound` shape).  This is proved through the new node
  `poleBound_of_sourceMass`, which applies the *proved quantitative* one-variable theorem
  `H2W.LocC.lzeroGrowthQuantL1Self` (`H2W/LocC/LzeroQuantSelf.lean`, axiom-clean) slice by slice —
  the universal constant is what makes the pole bound uniform in `z`.
* **`integrableOn_abs_mul_sinCos2_of_sq_secondDeriv`** (the *bridge*) — a `C²` function on
  `(0,π/2)` with square-integrable second derivative is bounded, hence `sinθcos²θ`-integrable.
  This is the link from the *left-hand-side honesty slots* of the paper's elliptic estimates
  (`HkMem α 0 (∂_θθ·)`, `HkMem α 0 (z²∂_zz·)`) to the slice honesty.

The intended assembly of the target is then the delegated node
`H2W/pzIterBoxIntegrable_of_slots` (`Submission/.../H2W/pzIterBoxIntegrable_of_slots.lean`):

  `HkMem α 0 (∂_θθ(∂_z^jΨ))` for every `j ≤ 3`  **⟹**  the target,

via the bridge.  Indeed `HkMem α 0 g` has a *pointwise-in-`z`* first conjunct, so for every
`z > 0` one has `∫_θ (∂_θθ(∂_z^jΨ)(z,θ))² dθ < ∞` (drop the weight `w²/sin^η ≥ 1`), the bridge
gives `∫_θ |∂_z^jΨ(z,θ)|·sinθcos²θ dθ < ∞` for *every* `z > 0` (so the first conjunct of the
target holds on the whole neighbourhood), and the box conjunct follows from Tonelli together
with the bound `|u θ| ≤ |u(π/4)| + (π/2)(|u'(π/4)| + ∫_θ|u''|)` that the bridge produces:
`|∂_z^jΨ(s,π/4)|` and `|∂_θ∂_z^jΨ(s,π/4)|` are continuous in `s` (hence locally integrable), and
`∫_θ|∂_θ²∂_z^jΨ(s,θ)|dθ ≤ √Q(s)·√(∫sin^η)/w(s)` with `Q(s) = HkIntegrand α 0 (∂_θ²∂_z^jΨ) s`
globally `L¹` by the second conjunct of `HkMem`, so that Cauchy–Schwarz on a finite `s`-interval
makes `s ↦ ∫_θ|∂_z^jΨ(s,θ)|·sinθcos²θ dθ` locally integrable.  (This corrects an earlier remark
of this module: the local uniformity needed for the box conjunct *is* supplied by the
`HkMem`-honesty of the `θθ`-slots, because `HkMem` controls the global `z`-integral; what is
*not* sufficient is a merely a.e.-in-`z` growth bound — see below.)

## Why a local uniformity is needed at all, and where it comes from

`∫_θ |f(θ)|·sinθcos²θ` is finite for any `f` with `|f(θ)| = O((π/2-θ)^(-3+δ))`, so the purely
*a.e.-in-`z`* bound `|∂_z^jΨ(z,θ)| ≤ C(z)(θ⁻¹ + (π/2-θ)⁻¹)` — the shape of the project's
`SliceGrowth` — gives the pointwise slice integrability for a.e. `z`, but *not* the box
statement: the constant `C(z)` may be finite a.e. and yet have infinite integral on every
neighbourhood of a.e. `z₀` (`1/|z - z₀|` is the model example: finite everywhere, l.s.c., but not
locally integrable), and then the box integral of `|∂_z^jΨ|·sinθcos²θ` need not be finite.  Even
more, a *lower semicontinuous, everywhere finite* function can be locally unbounded
(`f z = 1/|z|` for `z ≠ 0`, `f 0 = 0`), so the *closedness* of the set `{z : the slice of ∂_z^jΨ
is not integrable}` (which does follow from Fatou) only yields the *pointwise* conjunct, not the
box conjunct.  Hence the target genuinely needs a locally uniform input; what the analysis above
adds is that the *global `z`-integral* half of `HkMem` supplies it, so the honest slots
`HkMem α 0 (∂_θθ(∂_z^jΨ))` (the left-hand-side honesty of the paper's elliptic estimates) are
enough, and the two reductions below isolate the weakest *self-contained* local-uniformity
inputs (the pole bound, and the local boundedness of the `θ`-integrals).
-/

namespace Work.FTS.EllipticEst.H2W

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-! ## Elementary facts about the angular profile `sinθcos²θ` -/




/-- `θ ↦ sinθcos²θ` is continuous. -/
private theorem continuous_sinCos2_fts : Continuous Work.Elliptic.sinCos2 := by
  unfold Work.Elliptic.sinCos2
  fun_prop


/-! ## Two integrability criteria (bounded functions on finite-measure sets) -/




/-! ## The elementary bridge: `L²`-control of `∂_θ²u` implies `sinθcos²θ`-honesty

The following lemma is the *link* between the left-hand-side honesty slots of the paper's
elliptic estimates (`HkMem α 0 (∂_θθu)`, `HkMem α 0 (z²∂_zzu)`) and the `sinθcos²θ`-integrability
of the angular slices: a `C²` function on the open interval whose second derivative is
square-integrable is *bounded*, by two applications of the one-dimensional fundamental theorem
of calculus (each losing the factor `π/2`, from Cauchy–Schwarz on the integral of `|u''|`). -/


/-! ## The reduction: the growth bound implies the box statement -/


/-! ## The reduction: a locally uniform `L¹_θ`-bound on the slices

This is the *weakest* local-uniformity input that implies the target: not the pointwise-in-`θ`
pole bound of `pzIterBoxIntegrable_of_growth`, but only the local *boundedness in `z` of the
`θ`-integral* of the slices.  The first lemma below records that the pole bound implies it
(so the reduction of this section strictly generalises the previous one). -/



/-! ## The pole bound from a locally uniform source-mass bound

The chapter's bottleneck in `L¹`-mass form is the locally uniform bound on the *source mass*
`∫_{Iθ} sinθcos²θ·|Lzero1(∂_z^mΨ)(z,·)|`, together with the (free, by continuity) bound on the
`π/4`-data of the slices.  The two lemmas below show that this input is *sufficient*: the proved
quantitative one-variable theorem `LocC.lzeroGrowthQuantL1Self`
(`Submission/Work/FTS/EllipticEst/H2W/LocC/LzeroQuantSelf.lean`, axiom-clean) bounds every slice by
`C·(mass + data at π/4)·(θ⁻¹ + (π/2-θ)⁻¹)` with a *universal* `C`, so a single uniform bound on
the mass and the data gives the pole bound with a single constant.  Consequently the target
reduces to the source-mass bound (`pzIterBoxIntegrable_of_sourceMass`). -/



/-! ## The per-datum form of the reduction, and the paper's missing hypothesis

`WeakPos2` is the *weak* class (see `PropH2Base.lean`): the equation on the open quadrant, the
Dirichlet data as *values*, the decay `z → ∞`, the two moment conditions, `C^∞` on the open
quadrant, and the honesty of the **source** only (`HkMem α 2 F`).  It carries **no** honesty for
the left-hand-side slots of `Ψ`, and those are exactly the quantities the target asserts to be
honest.  The paper's Proposition `prop:L2` does not work in this class either: it concerns *the
unique `L²` solution* of `(PolarBSL)` with `R²Ψ → 0` at `R = 0`, and its Step 1 uses precisely
that condition to conclude `Ψ_★ ≡ 0`.

The two lemmas below record the conditional forms of the target that *are* usable:

* `pzIterBoxIntegrable_of_poleBoundDatum` — the target's conclusion for a *fixed* datum from a
  locally uniform pole bound for that datum (the conclusion of the tree's
  `pzIterSliceGrowth3Loc` chain, in its `pzIterSliceGrowth3Loc_of_massBound` /
  `pzIterSliceGrowth3LocC` reductions);
* `pzIterBoxIntegrable_of_externalMass` — the target's conclusion from the paper's missing
  hypothesis `SliceMassExternal α F Ψ` (the ψ-weighted slice-mass form of the paper's
  `R²Ψ → 0` at `R = 0`, `H2W/SliceMassExternal.lean`), through the proved tree lemmas
  `sliceSourceMassBound_of_external` and `pzIterSliceGrowth3Loc_of_massBound`. -/



/-! ### The two weakest sufficient inputs available in the tree

The tree's `H2W/SliceB/pzSecGrowthLoc.lean` reduces the locally uniform pole bound to a locally
uniform bound on the *honest angular slots* of the four slices `pzIter m Ψ` (`m ≤ 3`): the second
derivative slot (`LocSecBound`) or even just the first (`LocGradBound`).  Composed with
`pzIterBoxIntegrable_of_poleBoundDatum` this gives the target's conclusion from those inputs. -/



/-! ## The target -/


end

end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.ESW.low_order_split =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT.ESW

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

/-!
# `low_order_split`

The two low-order angular terms `∫∫ w²(∂_θΨ)²` and `∫∫ w²Ψ²` of a datum of the weak class
`TT.EllWeakPos α k F Ψ` are *separately* controlled by the `η`-weighted second angular
derivative `∫∫ w² (∂_θθΨ)² sin(2θ)^{-η}` — the form of the estimate consumed by
`ESW.Assembly` (whereas `TT.ESW.low_order_le` gives the bound for the *sum* of the two
integrands).

The proof is slicewise.  For `z > 0` the slice `u = Ψ z ·` satisfies the hypotheses of
`TT.ESW.slice_deriv_bound` and `TT.ESW.slice_value_bound` (`TT.ESW.slice_class_facts`,
`TT.ESW.exists_interior_zero_of_moment` + Rolle for the interior critical point, and the
right-endpoint limit `TT.ESW.slice_tendsto_pi_half`), so that with `E(z) = ∫_θ (∂_θθΨ z θ)²`,

  `∫_θ (∂_θΨ z θ)² ≤ (π/2)² E(z)`,   `∫_θ Ψ(z,θ)² ≤ (π/2)⁴ E(z)`,

and `E(z) ≤ ∫_θ (∂_θθΨ z θ)² σ(θ)` because `σ ≥ 1`.  Multiplying by `w(z)² ≥ 0` and
integrating the two pointwise bounds against the integrable RHS
(`TT.ESW.integrable_w_sq_thetaEnergy`) gives the two separate inequalities, with constants
`(π/2)²` and `(π/2)⁴` whose sum is `< 20`.
-/

/-- **The split form of the one-dimensional low-order slice bound.**  A `C²` function on
`(0, π/2)` with vanishing angular moment, right endpoint limit `0` and finite `η`-weighted
second derivative satisfies the two low-order bounds separately, with the constants `(π/2)²`
and `(π/2)⁴`. -/
theorem slice_split_low_order {u : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hπ : Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hval : u (Real.pi / 2) = 0)
    (hint : IntegrableOn (fun θ => u θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hmom : (∫ θ in Work.Spaces.Iθ, u θ * Work.Elliptic.sinCos2 θ) = 0)
    (h2 : IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
        ≤ (Real.pi / 2) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) ∧
    (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)
        ≤ (Real.pi / 2) ^ 4 * (∫ θ in Work.Spaces.Iθ,
            (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  obtain ⟨θ₁, hθ₁, hzero⟩ := exists_interior_zero_of_moment hsm.continuousOn hint hmom
  have hcontIcc : ContinuousOn u (Set.Icc θ₁ (Real.pi / 2)) :=
    continuousOn_Icc_of_tendsto hsm.continuousOn hπ hval hθ₁
  obtain ⟨θ₀, hθ₀, hcrit⟩ :=
    exists_deriv_eq_zero hθ₁.2 hcontIcc (by rw [hzero, hval])
  have hd := slice_deriv_bound hsm ⟨lt_trans hθ₁.1 hθ₀.1, hθ₀.2⟩ hcrit h2
  have hv := slice_value_bound hsm hθ₁ hzero hd
  set E : ℝ := ∫ s in Work.Spaces.Iθ, (deriv (fun t => deriv u t) s) ^ 2 with hE
  set J : ℝ := ∫ s in Work.Spaces.Iθ,
    (deriv (fun t => deriv u t) s) ^ 2 * Work.FTS.EllipticEst.sEta s with hJ
  have hEJ : E ≤ J := by
    rw [hE, hJ]
    refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun s => sq_nonneg _) h2 ?_
    exact Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo fun θ hθ => by
      have h1 := Work.FTS.EllipticEst.Honest.one_le_sEta hθ
      nlinarith [sq_nonneg (deriv (fun t => deriv u t) θ)]
  have hvol : (volume : Measure ℝ).real Work.Spaces.Iθ = Real.pi / 2 := by
    rw [MeasureTheory.measureReal_def, Work.Spaces.Iθ, Real.volume_Icc, sub_zero,
      ENNReal.toReal_ofReal (by positivity)]
  have hdb : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv u θ) ^ 2 ≤ (Real.pi / 2) * E :=
    fun θ hθ => by rw [hE]; exact hd θ hθ
  have hvb : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (u θ) ^ 2 ≤ (Real.pi / 2) ^ 3 * E :=
    fun θ hθ => by rw [hE]; exact hv θ hθ
  have hb1 : (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2) ≤ (Real.pi / 2) ^ 2 * E := by
    have hmono : (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, ((Real.pi / 2) * E) :=
      MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _)
        (MeasureTheory.integrable_const ((Real.pi / 2) * E))
        (Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo hdb)
    have hconst : (∫ θ in Work.Spaces.Iθ, ((Real.pi / 2) * E))
        = (Real.pi / 2) * E * (Real.pi / 2) := by
      rw [MeasureTheory.setIntegral_const, hvol, smul_eq_mul]
      ring
    calc (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
        ≤ (Real.pi / 2) * E * (Real.pi / 2) := by rw [← hconst]; exact hmono
      _ = (Real.pi / 2) ^ 2 * E := by ring
  have hb0 : (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) ≤ (Real.pi / 2) ^ 4 * E := by
    have hmono : (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, ((Real.pi / 2) ^ 3 * E) :=
      MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _)
        (MeasureTheory.integrable_const ((Real.pi / 2) ^ 3 * E))
        (Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo hvb)
    have hconst : (∫ θ in Work.Spaces.Iθ, ((Real.pi / 2) ^ 3 * E))
        = (Real.pi / 2) ^ 3 * E * (Real.pi / 2) := by
      rw [MeasureTheory.setIntegral_const, hvol, smul_eq_mul]
      ring
    calc (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)
        ≤ (Real.pi / 2) ^ 3 * E * (Real.pi / 2) := by rw [← hconst]; exact hmono
      _ = (Real.pi / 2) ^ 4 * E := by ring
  constructor
  · calc (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
        ≤ (Real.pi / 2) ^ 2 * E := hb1
      _ ≤ (Real.pi / 2) ^ 2 * J := mul_le_mul_of_nonneg_left hEJ (by positivity)
      _ = (Real.pi / 2) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by rw [hJ]
  · calc (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)
        ≤ (Real.pi / 2) ^ 4 * E := hb0
      _ ≤ (Real.pi / 2) ^ 4 * J := mul_le_mul_of_nonneg_left hEJ (by positivity)
      _ = (Real.pi / 2) ^ 4 * (∫ θ in Work.Spaces.Iθ,
            (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by rw [hJ]

theorem low_order_split {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hwk : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2))
      + (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
      ≤ 20 * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ)) := by
  set Jw : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) with hJw
  have hJint : IntegrableOn Jw Work.Spaces.Iz := by
    rw [hJw]
    exact integrable_w_sq_thetaEnergy hwk
  -- the two pointwise bounds
  have hpt1 : ∀ z ∈ Work.Spaces.Iz,
      (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
        ≤ (Real.pi / 2) ^ 2 * Jw z := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · rw [← h0, hJw]
      simp [Work.Spaces.w]
    · obtain ⟨hsm2, hB2, hint, hmom, hval⟩ := slice_class_facts hwk hz0
      obtain ⟨hs1, -⟩ :=
        slice_split_low_order hsm2 (slice_tendsto_pi_half hwk hz0) hval hint hmom hB2
      have e1 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
          = ∫ θ in Work.Spaces.Iθ, (deriv (fun t => Ψ z t) θ) ^ 2 := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
        simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
      have e2 : Jw z = (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) := by
        have h : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ)
            = ∫ θ in Work.Spaces.Iθ,
                (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2
                  * Work.FTS.EllipticEst.sEta θ := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
          simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
        simp only [hJw, h]
      rw [e1, e2]
      have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      calc (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (deriv (fun t => Ψ z t) θ) ^ 2)
          ≤ (Work.Spaces.w z) ^ 2 * ((Real.pi / 2) ^ 2 *
              (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)) := mul_le_mul_of_nonneg_left hs1 hw2
        _ = (Real.pi / 2) ^ 2 * ((Work.Spaces.w z) ^ 2 *
              (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)) := by ring
  have hpt0 : ∀ z ∈ Work.Spaces.Iz,
      (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
        ≤ (Real.pi / 2) ^ 4 * Jw z := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · rw [← h0, hJw]
      simp [Work.Spaces.w]
    · obtain ⟨hsm2, hB2, hint, hmom, hval⟩ := slice_class_facts hwk hz0
      obtain ⟨-, hs0⟩ :=
        slice_split_low_order hsm2 (slice_tendsto_pi_half hwk hz0) hval hint hmom hB2
      have e2 : Jw z = (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) := by
        have h : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ)
            = ∫ θ in Work.Spaces.Iθ,
                (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2
                  * Work.FTS.EllipticEst.sEta θ := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
          simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
        simp only [hJw, h]
      rw [e2]
      have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      calc (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
          ≤ (Work.Spaces.w z) ^ 2 * ((Real.pi / 2) ^ 4 *
              (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)) := mul_le_mul_of_nonneg_left hs0 hw2
        _ = (Real.pi / 2) ^ 4 * ((Work.Spaces.w z) ^ 2 *
              (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)) := by ring
  -- integrate the two pointwise bounds
  have hInt1 : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2))
      ≤ (Real.pi / 2) ^ 2 * (∫ z in Work.Spaces.Iz, Jw z) := by
    have h := MeasureTheory.integral_mono_of_nonneg
      (f := fun z => (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2))
      (g := fun z => (Real.pi / 2) ^ 2 * Jw z)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z _ =>
        mul_nonneg (sq_nonneg _) (MeasureTheory.integral_nonneg fun θ => sq_nonneg _))
      (hJint.const_mul ((Real.pi / 2) ^ 2))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hpt1)
    rwa [MeasureTheory.integral_const_mul] at h
  have hInt0 : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
      ≤ (Real.pi / 2) ^ 4 * (∫ z in Work.Spaces.Iz, Jw z) := by
    have h := MeasureTheory.integral_mono_of_nonneg
      (f := fun z => (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
      (g := fun z => (Real.pi / 2) ^ 4 * Jw z)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z _ =>
        mul_nonneg (sq_nonneg _) (MeasureTheory.integral_nonneg fun θ => sq_nonneg _))
      (hJint.const_mul ((Real.pi / 2) ^ 4))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hpt0)
    rwa [MeasureTheory.integral_const_mul] at h
  -- the arithmetic
  have hJnn : 0 ≤ ∫ z in Work.Spaces.Iz, Jw z := by
    rw [hJw]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ici fun z _ => ?_
    exact mul_nonneg (sq_nonneg _)
      (MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ =>
        mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.Honest.sEta_nonneg hθ))
  have hpi : (Real.pi / 2) ^ 2 + (Real.pi / 2) ^ 4 ≤ 20 := by
    have h1 : Real.pi / 2 < 2 := by linarith [Real.pi_lt_four]
    have h2 : (0 : ℝ) < Real.pi / 2 := by positivity
    have h3 : (Real.pi / 2) ^ 2 < 4 := by nlinarith [h1, h2]
    have h4 : (Real.pi / 2) ^ 4 < 16 := by nlinarith [h3, sq_nonneg (Real.pi / 2)]
    linarith
  calc (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2))
      + (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
      ≤ (Real.pi / 2) ^ 2 * (∫ z in Work.Spaces.Iz, Jw z)
        + (Real.pi / 2) ^ 4 * (∫ z in Work.Spaces.Iz, Jw z) := add_le_add hInt1 hInt0
    _ = ((Real.pi / 2) ^ 2 + (Real.pi / 2) ^ 4) * (∫ z in Work.Spaces.Iz, Jw z) := by ring
    _ ≤ 20 * (∫ z in Work.Spaces.Iz, Jw z) := mul_le_mul_of_nonneg_right hpi hJnn
    _ = 20 * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ)) := by rw [hJw]

end

end Work.FTS.EllipticEst.TT.ESW
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.gammaHonesty =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

open MeasureTheory Set Filter

/-- **The pointwise identification of the target integrand with the `(1,1)`-slot of `A`.**
For `θ ∈ Iθ` the integrand `(D_z∂_θA)²·w²·sin(2θ)^{2-γ}` of the target equals the square of the
weighted slot `mixed 1 1 A · Wt α`.  (`Wt α = w · sin(2θ)^{-γ/2}`, so
`(mixed 1 1 A · Wt α)² = (D_z∂_θA · w · sin(2θ)^{1-γ/2})² = (D_z∂_θA)²·w²·sin(2θ)^{2-γ}`.) -/
theorem gammaHonesty_integrand_eq_slot11 (α : ℝ) (A : ℝ → ℝ → ℝ)
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Dz (Work.Spaces.pth A) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      = (Work.Spaces.mixed 1 1 A z θ * Work.Spaces.Wt α z θ) ^ 2 := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  have h1 : (Real.sin (2 * θ) ^ ((2 - Work.Spaces.gam α) / 2)) ^ (2 : ℕ)
      = Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α) := by
    rw [rpow_sq_eq hs]
    ring
  rw [slot11_sq_eq α A hα hα4 hθ, ← h1]
  ring

theorem gammaHonesty {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Aof Ψ)) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iz := by
  -- `Ψ` and `A = z²∂_z²Ψ` are `C^∞` on the open quadrant, and `A` is honest in `ℋ²`.
  have hΨsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hAsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllipticEst.H2W.Aof Ψ) :=
    Work.FTS.EllipticEst.H2W.AeDataAofAux.smoothOpen_zsq_mul (hΨsm.pzIter 2)
  have hmemA : Work.Spaces.HkMem α 2 (Work.FTS.EllipticEst.H2W.Aof Ψ) := h.memA
  -- the weighted `(1,1)`-slot is continuous on the open quadrant …
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.mixed 1 1 (Work.FTS.EllipticEst.H2W.Aof Ψ) p.1 p.2
        * Work.Spaces.Wt α p.1 p.2) ^ 2) Work.FTS.EllipticEst.Q0 :=
    (((hAsm.mixed 1 1).continuousOn).mul (Work.FTS.EllipticEst.continuousOn_Wt_Q0 α)).pow 2
  -- … and its iterated integral is honest, being a summand of the `ℋ²`-integrand of `A`.
  have hI2 : Work.Coercivity.I2Mem (fun z θ =>
      (Work.Spaces.mixed 1 1 (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ
        * Work.Spaces.Wt α z θ) ^ 2) :=
    Work.FTS.EllipticEst.H2W.i2Mem_sq_of_le (f := Work.FTS.EllipticEst.H2W.Aof Ψ) hmemA hcont
      (fun z hz θ hθ =>
        Work.Spaces.sq_le_HkIntegrand_mixed α 2 (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ 1 1
          le_rfl (by norm_num))
  -- the target function is the outer integral of the slot, pointwise.
  have hcongr : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Aof Ψ)) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      = fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed 1 1 (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 := by
    funext z
    exact MeasureTheory.setIntegral_congr_fun
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
      (fun θ hθ => gammaHonesty_integrand_eq_slot11 α (Work.FTS.EllipticEst.H2W.Aof Ψ)
        hα hα4 hθ)
  rw [hcongr]
  exact hI2.2

end Work.FTS.EllipticEst.TT
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.psiDerivSq_upper =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT


end Work.FTS.EllipticEst.TT
end
-- ===== merged: Submission.Work.FTS.EllipticEst.UopHk.EllResid_slice_data =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Slice data for the residual `EllResid α F Ψ` in the interior class `EllHypQ`

`Work.Elliptic.EllResid α F Ψ = Ψ - (1/(4α)) sin 2θ · L₁₂(F)` is a `C^∞` function of `θ` minus a
*radial* factor `κ(z) = -(1/(4α)) L₁₂(F)(z)` times the *angular* factor `sin 2θ`.  In the
interior class `EllHypQ` the radial factor is only known to be `C^k` on `(0,∞)`, so the residual
is *not* `C^∞` on the open quadrant; nevertheless every slice `θ ↦ D_z^j (EllResid α F Ψ) z θ`
with `j ≤ k` is `C^∞` on `(0,π/2)` (the `θ`-smoothness comes from `Ψ` alone), continuous on the
closed `Iθ` and vanishes at both endpoints.  All four pointwise identities relating the
`θ`-derivatives of the slice to the mixed operators `D_z^j D_θ^i (∂_θ^r …)` follow from the same
decomposition, the `Ψ`-half being Clairaut on the open quadrant and the radial ⊗ angular half
being an unconditional computation.

Everything here is `sorry`-free.
-/

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

noncomputable section

namespace Work.FTS.EllipticEst.UopHk

/-! ## Additivity of the operators along a sum -/




/-- The plain angular derivative is additive at a point where both slices are differentiable. -/
theorem pth_add_of_diff (f g : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hf : DifferentiableAt ℝ (fun θ' => f z θ') θ)
    (hg : DifferentiableAt ℝ (fun θ' => g z θ') θ) :
    Work.Spaces.pth (f + g) z θ = Work.Spaces.pth f z θ + Work.Spaces.pth g z θ := by
  simp only [Work.Spaces.pth, Pi.add_apply]
  rw [show deriv (fun θ' => f z θ' + g z θ') θ
      = deriv ((fun θ' => f z θ') + fun θ' => g z θ') θ from rfl]
  rw [deriv_add hf hg]


/-! ## The iterated radial operator on a one-variable function -/



/-! ## The boundary limits of the slices of a `RegQ` datum -/


/-! ## The angular profiles `sin 2θ`, `2cos 2θ`, `-4 sin 2θ` -/

theorem hasDerivAt_sin_two (θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
  simpa [Function.comp_def, mul_comm] using
    (Real.hasDerivAt_sin (2 * θ)).comp θ
      ((hasDerivAt_const (x := θ) (c := (2 : ℝ))).mul (hasDerivAt_id θ))

theorem deriv_sin_two (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ = 2 * Real.cos (2 * θ) :=
  (hasDerivAt_sin_two θ).deriv

theorem deriv_two_cos_two (θ : ℝ) :
    deriv (fun θ' : ℝ => 2 * Real.cos (2 * θ')) θ = -(4 * Real.sin (2 * θ)) := by
  have h1 : HasDerivAt (fun θ' : ℝ => Real.cos (2 * θ')) (-(2 * Real.sin (2 * θ))) θ := by
    simpa [Function.comp_def, mul_comm, mul_assoc] using
      (Real.hasDerivAt_cos (2 * θ)).comp θ
        ((hasDerivAt_const (x := θ) (c := (2 : ℝ))).mul (hasDerivAt_id θ))
  have h2 := h1.const_mul (2 : ℝ)
  rw [h2.deriv]
  ring

/-! ## The singular part of the residual as a radial ⊗ angular product -/














/-! ## The second `θ`-derivative of a slice, on an arbitrary open set -/


/-! ## Continuity on the closed angular interval from the open interval and the two limits -/



/-! ## The iterates of the one-variable angular operator `Lop` -/





/-! ## The residual vanishes on the two angular boundaries -/


/-! ## The decomposition of the radial derivatives of the residual -/





/-! ## The `D_θ`-iterates of the singular part as radial ⊗ angular products -/














end Work.FTS.EllipticEst.UopHk
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.TopCoreB.SlotRec =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TopCoreB/SlotRec`: the pointwise `∂_θ`-slot recursions

Two purely pointwise inequalities comparing the *plain* angular derivatives `∂_θ^mf` (with
their natural weights `sin(2θ)^{2m-γ}` resp. `sin(2θ)^{2m-4-γ}`) to the *`D_θ`-slots*
`D_θ^tf` (with the weight `sin(2θ)^{-γ}` of the `ℋ^k`-norm).

* `slotRecStep` / `slotRecAll` — the *unshifted* recursion
  `(∂_θ^mf)²·σ^{2m-γ} ≤ C_m Σ_{t≤m} (D_θ^tf)²·σ^{-γ}`,
  used for the *source* functions (`F`, `z²∂_zzΨ`, `D_z(∂_θθΨ)`), whose natural weight in the
  `ℋ^k`-norm is the slot weight `σ^{-γ}`.
* `slotRecShiftAll` — the *shifted* recursion
  `(∂_θ^mf)²·σ^{2m-4-γ} ≤ C_m Σ_{i<m-1} (D_θ^i(∂_θθf))²·σ^{-γ}`,
  used for `Ψ` itself: its low slots are not controlled by the hypotheses, but its second
  derivative `B = ∂_θθΨ` is.

Both are proved by strong induction on `m` from the *reverse expansions*
`Work.FTS.EllipticEst.remov.reverse_expansion_2d` (resp. `..._top`) of
`remov/DthIter_expansion`, via the pointwise algebra `slotRecStep` (resp.
`Baux.PthSlotPointwise`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.TopCoreB

set_option autoImplicit false
set_option linter.unusedSimpArgs false

theorem sin_two_pos_of_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- Nonnegativity of the `D_θ`-slot integrand at an interior angle. -/
theorem slotTerm_nonneg (γ : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (g : ℝ) : 0 ≤ g ^ 2 * (Real.sin (2 * θ)) ^ (-γ) :=
  mul_nonneg (sq_nonneg _) (le_of_lt (Real.rpow_pos_of_pos (sin_two_pos_of_Ioo hθ) _))



end Work.FTS.EllipticEst.remov.TopCoreB

namespace Work.FTS.EllipticEst.remov.TopCoreB


end Work.FTS.EllipticEst.remov.TopCoreB
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.Theta_Fstar_ops =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology

namespace Work.FTS.EpsEngine

/-- The three closed forms of the singular part `Theta α F_*` of the star profile, at the level of
the operators `Rop`, `Uop`, `Vop` of `Work.Construction`, on the open quadrant:
`Rop α (Theta α F_*) = 1/(1+z) − α sin²θ z/(1+z)²`,
`Vop (Theta α F_*) = c2m θ/(1+z)`,
`Uop α (Theta α F_*)/sin 2θ = −3/(2(1+z)) + α z/(2(1+z)²)`.
The values at `z = 0` are `1`, `c2m θ` and `−3/2` respectively.

They follow from `Work.FTS_RegExport.RXT.SysAux.Theta_ops`
(`-2·Rop α (Theta α F) = -L₁₂(F)/α + sin²θ·𝔽K(F)`, `2α·Vop (Theta α F) = L₁₂(F)·c2m θ`,
`2·Uop α (Theta α F) = -(3/(2α))sin2θ L₁₂(F) + (1/2)sin2θ·𝔽K(F)`) at `F = F_*`, together with
`Work.Construction.L12_Fstar_eq` (`L₁₂(F_*) z = 2α/(1+z)`) and
`Work.FTS.Nonlinear.FstarPkg.FK_Fstar` (`𝔽K(F_*) z = α·(2z/(1+z)²)`). -/
theorem Theta_Fstar_ops {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Rop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ
        = 1 / (1 + z) - α * (Real.sin θ) ^ 2 * z / (1 + z) ^ 2) ∧
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Vop (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ
        = Work.Construction.c2m θ / (1 + z)) ∧
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Construction.Uop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ
          / Work.Construction.s2 θ
        = -(3 / (2 * (1 + z))) + α * z / (2 * (1 + z) ^ 2)) := by
  -- The index-raising identity `z ∂_z L₁₂(F_*) = -𝔽K(F_*)` required by `Theta_ops`.  Since
  -- `L₁₂(F_*)` is *exactly* `2α/(1+z)` on `[0,∞)`, its derivative there is elementary.
  have hL12d : ∀ z : ℝ, 0 < z →
      z * deriv (fun z' => Work.Construction.L12 (Work.Construction.Fstar α) z') z
        = -Work.Construction.FK (Work.Construction.Fstar α) z := by
    intro z hz
    have heq : (fun z' : ℝ => Work.Construction.L12 (Work.Construction.Fstar α) z')
        =ᶠ[𝓝 z] (fun z' : ℝ => 2 * α / (1 + z')) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      exact Work.Construction.L12_Fstar_eq hα hα1 (le_of_lt hz')
    rw [heq.deriv_eq]
    have hd : HasDerivAt (fun z' : ℝ => (1 + z')⁻¹) (-((1 + z) ^ 2)⁻¹) z := by
      have h1 : HasDerivAt (fun z' : ℝ => 1 + z') 1 z := by
        simpa using (hasDerivAt_id z).const_add (1 : ℝ)
      have h2 := h1.inv (by positivity : (1 : ℝ) + z ≠ 0)
      convert h2 using 1
      ring
    have hderiv : deriv (fun z' : ℝ => 2 * α / (1 + z')) z = -2 * α / (1 + z) ^ 2 := by
      rw [show (fun z' : ℝ => 2 * α / (1 + z')) = fun z' => 2 * α * (1 + z')⁻¹ from by
        funext z'; ring]
      rw [deriv_const_mul_field, hd.deriv]
      ring
    rw [hderiv, Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα hα1]
    field_simp
  have hmain := Work.FTS_RegExport.RXT.SysAux.Theta_ops (αG := α) hα hL12d
  refine ⟨?_, ?_, ?_⟩
  · -- `Rop`: `-2·Rop(Θ) = -L₁₂(F_*)/α + sin²θ·𝔽K(F_*) = -2(1/(1+z) - α sin²θ z/(1+z)²)`.
    intro z θ hz hθ hθ2
    have h := (hmain z θ hz hθ hθ2).2.2
    rw [Work.Construction.L12_Fstar_eq hα hα1 (le_of_lt hz),
        Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα hα1] at h
    have hαne : α ≠ 0 := ne_of_gt hα
    have h1z : (1 : ℝ) + z ≠ 0 := by positivity
    have key : -(2 * α / (1 + z)) / α + (Real.sin θ) ^ 2 * (α * (2 * z / (1 + z) ^ 2))
        = -2 * (1 / (1 + z) - α * (Real.sin θ) ^ 2 * z / (1 + z) ^ 2) := by
      field_simp
      ring
    rw [key] at h
    linarith
  · -- `Vop`: `2α·Vop(Θ) = c2m θ·L₁₂(F_*) = 2α·(c2m θ/(1+z))`.
    intro z θ hz hθ hθ2
    have h := (hmain z θ hz hθ hθ2).1
    rw [Work.Construction.L12_Fstar_eq hα hα1 (le_of_lt hz)] at h
    have key : Work.Construction.c2m θ * (2 * α / (1 + z))
        = 2 * α * (Work.Construction.c2m θ / (1 + z)) := by ring
    rw [key] at h
    exact mul_left_cancel₀ (by positivity : (2 : ℝ) * α ≠ 0) h
  · -- `Uop`: `2·Uop(Θ) = 2 sin 2θ·(-3/(2(1+z)) + α z/(2(1+z)²))`; divide by `sin 2θ > 0`.
    intro z θ hz hθ hθ2
    have h := (hmain z θ hz hθ hθ2).2.1
    rw [Work.Construction.L12_Fstar_eq hα hα1 (le_of_lt hz),
        Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα hα1] at h
    have hαne : α ≠ 0 := ne_of_gt hα
    have h1z : (1 : ℝ) + z ≠ 0 := by positivity
    have key : -(3 / (2 * α)) * Real.sin (2 * θ) * (2 * α / (1 + z))
          + (1 / 2) * Real.sin (2 * θ) * (α * (2 * z / (1 + z) ^ 2))
        = 2 * Real.sin (2 * θ) * (-(3 / (2 * (1 + z))) + α * z / (2 * (1 + z) ^ 2)) := by
      field_simp
    rw [key] at h
    have hsin : Real.sin (2 * θ) ≠ 0 := by
      apply ne_of_gt
      apply Real.sin_pos_of_pos_of_lt_pi
      · linarith
      · linarith [Real.pi_pos]
    have hU : Work.Construction.Uop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ
        = Real.sin (2 * θ) * (-(3 / (2 * (1 + z))) + α * z / (2 * (1 + z) ^ 2)) := by
      linarith
    rw [hU, Work.Construction.s2]
    rw [div_eq_iff hsin]
    ring

end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS.GalBasis.ApproxCC.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.ApproxCC

set_option autoImplicit false

/-- **The plain mixed derivative** `∂_z^a ∂_θ^b g`, in the arrangement "the `θ`-derivative is
taken on the `z`-slice, and the `z`-derivative is taken afterwards":
`plainMixed a b g z θ = ∂_z^a (z' ↦ ∂_θ^b (θ' ↦ g z' θ') θ) (z)`.

Note that this is *not* the same expression as the `D`-operator iterate `Work.Spaces.mixed`,
but the two are related by the bounded-coefficient expansions `D_z^a = Σ c_i(z) ∂_z^i` and
`D_θ^b = Σ d_j(θ) ∂_θ^j` valid on a box `[A,B] × [C,D]` with `0 < A` (see
`ApproxCC/Basic.lean`). -/
def plainMixed (a b : ℕ) (g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => iteratedDeriv a (fun z' => iteratedDeriv b (fun θ' => g z' θ') θ) z

@[simp] theorem plainMixed_zero_left (b : ℕ) (g : ℝ → ℝ → ℝ) :
    plainMixed 0 b g = fun z θ => iteratedDeriv b (fun θ' => g z θ') θ := rfl

@[simp] theorem plainMixed_zero_right (a : ℕ) (g : ℝ → ℝ → ℝ) :
    plainMixed a 0 g = fun z θ => iteratedDeriv a (fun z' => g z' θ) z := by
  funext z θ
  simp [plainMixed]




end Work.FTS.GalBasis.ApproxCC
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.c0_pos =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis
open Work.FTS.Galerkin (Fn galFun)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 400000

/-! ## Elementary facts about the far bump `Gfar` -/














/-! ## The angular weight `K` on `[0, π/2]` -/




/-! ## The angular slice of `Gfar` and the radial density `c0F` -/









/-! ## Measurability and integrability of `c0F` -/




/-! ## Positivity of `c0` -/


end Work.FTS.GalBasis
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc_closure =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis

open Work.FTS.Galerkin (Fn galFun)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 400000

/-! ## The zero function -/

/-- The zero profile is a test function: it is `C^∞` and vanishes off any box. -/
theorem Ccφ.zero : Ccφ (fun _ _ : ℝ => (0 : ℝ)) := by
  refine ⟨1, 2, 1 / 10, by norm_num, by norm_num, by norm_num, by linarith [Real.pi_gt_three],
    ?_, 11 / 10, 19 / 10, 1 / 8, by norm_num, by norm_num, by norm_num, by norm_num,
    by linarith [Real.pi_gt_three], ?_⟩
  · rw [show Function.uncurry (fun _ _ : ℝ => (0 : ℝ)) = fun _ : ℝ × ℝ => (0 : ℝ) from rfl]
    exact contDiff_const
  · intro z θ _
    rfl

/-! ## Closure under addition -/

/-- `Ccφ` is closed under addition: the two support boxes are replaced by their pointwise
enclosure (min of the lower ends, max of the upper ends). -/
theorem Ccφ.add {f g : Fn} (hf : Ccφ f) (hg : Ccφ g) :
    Ccφ (fun z θ => f z θ + g z θ) := by
  obtain ⟨a₁, b₁, δ₁, ha₁, hab₁, hδ₁, hδπ₁, hd₁, a₁', b₁', δ₁', haa₁, hab₁', hbb₁, hδδ₁,
    hδδπ₁, hs₁⟩ := hf
  obtain ⟨a₂, b₂, δ₂, ha₂, hab₂, hδ₂, hδπ₂, hd₂, a₂', b₂', δ₂', haa₂, hab₂', hbb₂, hδδ₂,
    hδδπ₂, hs₂⟩ := hg
  refine ⟨min a₁ a₂, max b₁ b₂, min δ₁ δ₂, lt_min ha₁ ha₂, ?_, lt_min hδ₁ hδ₂,
    lt_of_le_of_lt (min_le_left _ _) hδπ₁, ?_,
    min a₁' a₂', max b₁' b₂', min δ₁' δ₂', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (lt_of_le_of_lt (min_le_left _ _) hab₁) (le_max_left _ _)
  · rw [show Function.uncurry (fun z θ : ℝ => f z θ + g z θ)
        = fun p : ℝ × ℝ => Function.uncurry f p + Function.uncurry g p from rfl]
    exact hd₁.add hd₂
  · exact lt_min (lt_of_le_of_lt (min_le_left _ _) haa₁) (lt_of_le_of_lt (min_le_right _ _) haa₂)
  · exact lt_of_lt_of_le (lt_of_le_of_lt (min_le_left _ _) hab₁') (le_max_left _ _)
  · exact max_lt (lt_of_lt_of_le hbb₁ (le_max_left _ _)) (lt_of_lt_of_le hbb₂ (le_max_right _ _))
  · exact lt_min (lt_of_le_of_lt (min_le_left _ _) hδδ₁) (lt_of_le_of_lt (min_le_right _ _) hδδ₂)
  · have h1 : δ₁' < π / 4 := by linarith
    have h3 : min δ₁' δ₂' < π / 4 := lt_of_le_of_lt (min_le_left _ _) h1
    linarith
  · intro z θ hz
    have hf' : SuppIn f (min a₁' a₂') (max b₁' b₂') (min δ₁' δ₂') :=
      hs₁.mono (min_le_left _ _) (le_max_left _ _) (min_le_left _ _)
        (by linarith [min_le_left δ₁' δ₂'])
    have hg' : SuppIn g (min a₁' a₂') (max b₁' b₂') (min δ₁' δ₂') :=
      hs₂.mono (min_le_right _ _) (le_max_right _ _) (min_le_right _ _)
        (by linarith [min_le_right δ₁' δ₂'])
    simp [hf' z θ hz, hg' z θ hz]

/-! ## Closure under subtraction -/

/-- `Ccφ` is closed under subtraction (same box argument as for addition). -/
theorem Ccφ.sub {f g : Fn} (hf : Ccφ f) (hg : Ccφ g) :
    Ccφ (fun z θ => f z θ - g z θ) := by
  obtain ⟨a₁, b₁, δ₁, ha₁, hab₁, hδ₁, hδπ₁, hd₁, a₁', b₁', δ₁', haa₁, hab₁', hbb₁, hδδ₁,
    hδδπ₁, hs₁⟩ := hf
  obtain ⟨a₂, b₂, δ₂, ha₂, hab₂, hδ₂, hδπ₂, hd₂, a₂', b₂', δ₂', haa₂, hab₂', hbb₂, hδδ₂,
    hδδπ₂, hs₂⟩ := hg
  refine ⟨min a₁ a₂, max b₁ b₂, min δ₁ δ₂, lt_min ha₁ ha₂, ?_, lt_min hδ₁ hδ₂,
    lt_of_le_of_lt (min_le_left _ _) hδπ₁, ?_,
    min a₁' a₂', max b₁' b₂', min δ₁' δ₂', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (lt_of_le_of_lt (min_le_left _ _) hab₁) (le_max_left _ _)
  · rw [show Function.uncurry (fun z θ : ℝ => f z θ - g z θ)
        = fun p : ℝ × ℝ => Function.uncurry f p - Function.uncurry g p from rfl]
    exact hd₁.sub hd₂
  · exact lt_min (lt_of_le_of_lt (min_le_left _ _) haa₁) (lt_of_le_of_lt (min_le_right _ _) haa₂)
  · exact lt_of_lt_of_le (lt_of_le_of_lt (min_le_left _ _) hab₁') (le_max_left _ _)
  · exact max_lt (lt_of_lt_of_le hbb₁ (le_max_left _ _)) (lt_of_lt_of_le hbb₂ (le_max_right _ _))
  · exact lt_min (lt_of_le_of_lt (min_le_left _ _) hδδ₁) (lt_of_le_of_lt (min_le_right _ _) hδδ₂)
  · have h1 : δ₁' < π / 4 := by linarith
    have h3 : min δ₁' δ₂' < π / 4 := lt_of_le_of_lt (min_le_left _ _) h1
    linarith
  · intro z θ hz
    have hf' : SuppIn f (min a₁' a₂') (max b₁' b₂') (min δ₁' δ₂') :=
      hs₁.mono (min_le_left _ _) (le_max_left _ _) (min_le_left _ _)
        (by linarith [min_le_left δ₁' δ₂'])
    have hg' : SuppIn g (min a₁' a₂') (max b₁' b₂') (min δ₁' δ₂') :=
      hs₂.mono (min_le_right _ _) (le_max_right _ _) (min_le_right _ _)
        (by linarith [min_le_right δ₁' δ₂'])
    simp [hf' z θ hz, hg' z θ hz]

/-! ## Closure under scalar multiplication -/

/-- `Ccφ` is closed under scalar multiplication: the box of `f` also supports `c * f`
(because `c * 0 = 0`), so no enlargement is needed. -/
theorem Ccφ.smul (c : ℝ) {f : Fn} (hf : Ccφ f) : Ccφ (fun z θ => c * f z θ) := by
  obtain ⟨a, b, δ, ha, hab, hδ, hδπ, hd, a', b', δ', haa, hab', hbb, hδδ, hδδπ, hs⟩ := hf
  refine ⟨a, b, δ, ha, hab, hδ, hδπ, ?_, a', b', δ', haa, hab', hbb, hδδ, hδδπ, ?_⟩
  · rw [show Function.uncurry (fun z θ : ℝ => c * f z θ)
        = fun p : ℝ × ℝ => c * Function.uncurry f p from rfl]
    simpa using hd.const_smul c
  · intro z θ hz
    show c * f z θ = 0
    rw [hs z θ hz, mul_zero]

/-! ## Closure under finite linear combinations -/

/-- `Ccφ` is closed under an arbitrary finite linear combination: induction over the `Finset`
of indices, using the empty combination (the zero function), addition and scalar
multiplication. -/
theorem Ccφ.finset_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (F : ι → Fn)
    (h : ∀ i ∈ s, Ccφ (F i)) : Ccφ (fun z θ => ∑ i ∈ s, c i * F i z θ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact Ccφ.zero
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact Ccφ.add (Ccφ.smul (c a) (h a (Finset.mem_insert_self a s)))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- `galFun φ c = ∑_{k : Fin n} c k · φ k` is a test function whenever all the `φ k` are. -/
theorem Ccφ.galFun {n : ℕ} (φ : ℕ → Fn) (c : Fin n → ℝ) (h : ∀ k : Fin n, Ccφ (φ k)) :
    Ccφ (galFun φ c) := by
  show Ccφ (fun z θ => ∑ k : Fin n, c k * φ (k : ℕ) z θ)
  exact Ccφ.finset_sum Finset.univ c (fun k => φ (k : ℕ)) (fun k _ => h k)

/-! ## The target -/


end Work.FTS.GalBasis
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.exists_poly_approx_c4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter Polynomial Finset

namespace Work.FTS.GalBasis

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The iterated derivatives of a finite combination of powers of `(x - a)` -/


/-! ## Uniform approximation of a continuous function on `[a,b]` by a polynomial in `x - a`

This is the Stone–Weierstrass theorem for the algebra of polynomial functions:  on the
compact set `Icc 0 (b - a)` the polynomial functions are dense in `C(Icc 0 (b-a), ℝ)`, and we
apply this to `y ↦ g (y + a)`. -/


/-! ## The approximation theorem -/


end Work.FTS.GalBasis
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.l12_linear_cc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis

open Work.FTS.Galerkin (Fn galFun)

set_option autoImplicit false
set_option maxHeartbeats 400000

/-! ## Integrability of the slice and of the density of a `Ccφ` test function -/




/-! ## The linearity identities -/


end Work.FTS.GalBasis
end
end
-- ===== merged: Submission.Work.FTS.H2.PhiStarE5.Decay =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.PhiStarE5

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllipticEst (SmoothOpen Q0 mem_Q0 smoothOpen_of_forall)

set_option autoImplicit false
noncomputable section

/-! ## 6. Transferring the pointwise decay to the smooth representative

Given a weak solution `Ψ` of `bslOp α Ψ = F` (with the decay along every ray) and a `C^∞`
function `Φ` agreeing with `Ψ` a.e. on the open quadrant (its smooth representative), the decay
of `Ψ` transfers to `Φ`.  The point is that a.e.-equality on the quadrant gives, by Fubini,
a.e.-equality of the `θ`-slices; if the slices of `Ψ` are continuous (for a.e. `z`) and those of
`Φ` always are, the slices agree *everywhere*, hence so do the rays, and continuity in `z` plus
the decay of `Ψ` along the ray gives the decay of `Φ`.  (`a.e.`-equality alone would not
determine the values on a single ray.) -/

/-- **Fubini for a.e. equality**: a.e.-equality of two functions on a product of measures gives
a.e.-equality of the sections, for a.e. first coordinate. -/
theorem ae_slice_eq_of_ae_eq {Φ Ψ : ℝ → ℝ → ℝ}
    (h : (fun p : ℝ × ℝ => Φ p.1 p.2)
        =ᵐ[volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))]
        (fun p : ℝ × ℝ => Ψ p.1 p.2)) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      (fun θ => Φ z θ) =ᵐ[volume.restrict (Set.Ioo 0 (π / 2))] (fun θ => Ψ z θ) := by
  have hmeas : (volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))
      = ((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
        ((volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2))) := by
    rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.volume_eq_prod]
  rw [hmeas] at h
  exact MeasureTheory.Measure.ae_ae_eq_of_ae_eq_uncurry h

/-- Two functions that are continuous on an open set and agree a.e. there agree everywhere. -/
theorem eqOn_of_ae_eq_of_continuousOn {f g : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (h : f =ᵐ[volume.restrict s] g) : ∀ x ∈ s, f x = g x := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨x, hxs, hxne⟩ := hcon
  have hUopen : IsOpen {y : ℝ | y ∈ s ∧ f y ≠ g y} := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨hys, hyne⟩ := hy
    have hf' : ContinuousAt f y := (hf.continuousWithinAt hys).continuousAt (hs.mem_nhds hys)
    have hg' : ContinuousAt g y := (hg.continuousWithinAt hys).continuousAt (hs.mem_nhds hys)
    have hcont : ContinuousAt (fun y => f y - g y) y := hf'.sub hg'
    have hne : f y - g y ≠ 0 := sub_ne_zero.mpr hyne
    have hnb : (fun y => f y - g y) ⁻¹' ({0}ᶜ) ∈ 𝓝 y :=
      hcont.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hne)
    refine Filter.inter_mem (hs.mem_nhds hys) ?_
    refine Filter.mem_of_superset hnb ?_
    intro y' hy'
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hy' ⊢
    exact sub_ne_zero.mp hy'
  have hUne : ({y : ℝ | y ∈ s ∧ f y ≠ g y}).Nonempty := ⟨x, hxs, hxne⟩
  have hpos : 0 < volume {y : ℝ | y ∈ s ∧ f y ≠ g y} :=
    IsOpen.measure_pos volume hUopen hUne
  have hnull : volume {y : ℝ | y ∈ s ∧ f y ≠ g y} = 0 := by
    have h' : ∀ᵐ y ∂(volume : Measure ℝ), y ∈ s → f y = g y := by
      rw [← MeasureTheory.ae_restrict_iff' hs.measurableSet]; exact h
    have hz := MeasureTheory.ae_iff.mp h'
    have hset : {y : ℝ | y ∈ s ∧ f y ≠ g y}
        = {y : ℝ | ¬(y ∈ s → f y = g y)} := by
      ext y
      simp only [Set.mem_ofPred_eq, not_imp]
    rw [hset]
    exact hz
  exact absurd hnull (ne_of_gt hpos)

/-- **The slices of the smooth representative agree with those of the weak solution
everywhere**, for a.e. `z`. -/
theorem ae_slice_eq_all {Φ Ψ : ℝ → ℝ → ℝ} (hΦ : SmoothOpen Φ)
    (hslice : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ => Ψ z θ) (Set.Ioo 0 (π / 2)))
    (hae : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      (fun θ => Φ z θ) =ᵐ[volume.restrict (Set.Ioo 0 (π / 2))] (fun θ => Ψ z θ)) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), ∀ θ ∈ Set.Ioo 0 (π / 2), Φ z θ = Ψ z θ := by
  filter_upwards [hslice, hae, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with
    z hslicez haez hzpos
  have hcΦ : ContinuousOn (fun θ => Φ z θ) (Set.Ioo 0 (π / 2)) := by
    have h0 : ContDiffOn ℝ 0 (Function.uncurry Φ) Q0 := SmoothOpen.forall hΦ 0
    have h1 : ContDiffOn ℝ 0 (fun θ : ℝ => Φ z θ) (Set.Ioo 0 (π / 2)) :=
      h0.comp ((contDiffOn_const (c := z)).prodMk contDiffOn_id)
        (fun θ hθ => mem_Q0.mpr ⟨hzpos, hθ.1, hθ.2⟩)
    exact h1.continuousOn
  exact eqOn_of_ae_eq_of_continuousOn isOpen_Ioo hcΦ hslicez haez

/-- A function that agrees a.e. (on `(0,∞)`) with a function tending to `0` at infinity and is
continuous on `(0,∞)` tends to `0` at infinity. -/
theorem tendsto_of_ae_eq_of_tendsto {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioi 0)) (hg : Tendsto g atTop (𝓝 0))
    (h : f =ᵐ[volume.restrict (Set.Ioi 0)] g) :
    Tendsto f atTop (𝓝 0) := by
  by_contra hc
  rw [Metric.tendsto_atTop] at hc hg
  push_neg at hc
  obtain ⟨ε, hε, hfreq⟩ := hc
  obtain ⟨R, hR⟩ := hg (ε / 2) (by linarith)
  -- the null set where `f` and `g` differ
  set S : Set ℝ := {y : ℝ | y ∈ Set.Ioi 0 ∧ f y ≠ g y} with hSdef
  have hSnull : volume S = 0 := by
    have h'' : ∀ᵐ y ∂(volume : Measure ℝ), y ∈ Set.Ioi 0 → f y = g y := by
      rw [← MeasureTheory.ae_restrict_iff' measurableSet_Ioi]; exact h
    have hz := MeasureTheory.ae_iff.mp h''
    have hset : S = {y : ℝ | ¬(y ∈ Set.Ioi 0 → f y = g y)} := by
      ext y
      simp only [hSdef, Set.mem_ofPred_eq, not_imp]
    rw [hset]
    exact hz
  -- the set where `f` is large is open on `(0,∞)`
  have hAopen : IsOpen ({t : ℝ | ε / 2 < |f t|} ∩ Set.Ioi 0) := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨hyA, hy0⟩ := hy
    have hcont : ContinuousAt f y :=
      (hf.continuousWithinAt hy0).continuousAt (isOpen_Ioi.mem_nhds hy0)
    have hnb : {y' : ℝ | ε / 2 < |f y'|} ∈ 𝓝 y := by
      have h1 : Set.Ioi (ε / 2) ∈ 𝓝 (|f y|) := isOpen_Ioi.mem_nhds hyA
      have h2 : ContinuousAt (fun y' => |f y'|) y := hcont.abs
      exact h2.preimage_mem_nhds h1
    exact Filter.inter_mem hnb (isOpen_Ioi.mem_nhds hy0)
  have hAunb : ∀ N : ℝ, ∃ y, y > N ∧ ε / 2 < |f y| ∧ y ∈ Set.Ioi 0 := by
    intro N
    obtain ⟨y, hyN, hyε⟩ := hfreq (max N 0 + 1)
    have hdist : dist (f y) 0 = |f y| := by rw [Real.dist_eq, sub_zero]
    rw [hdist] at hyε
    exact ⟨y, by linarith [le_max_left N 0], by linarith,
      by simp only [Set.mem_Ioi]; linarith [le_max_right N 0]⟩
  -- an open neighbourhood of some large point, hence not contained in the null set
  obtain ⟨y, hyU, hyeq⟩ : ∃ y ∈ (({t : ℝ | ε / 2 < |f t|} ∩ Set.Ioi 0) ∩ Set.Ioi (max R 0)),
      f y = g y := by
    by_contra hcon
    push_neg at hcon
    have hsub : (({t : ℝ | ε / 2 < |f t|} ∩ Set.Ioi 0) ∩ Set.Ioi (max R 0)) ⊆ S := by
      intro y hy
      exact ⟨hy.1.2, hcon y hy⟩
    obtain ⟨y₀, hy₀1, hy₀2, hy₀3⟩ := hAunb (max R 0)
    have hne : ((({t : ℝ | ε / 2 < |f t|} ∩ Set.Ioi 0) ∩ Set.Ioi (max R 0))).Nonempty :=
      ⟨y₀, ⟨⟨hy₀2, hy₀3⟩, hy₀1⟩⟩
    have hpos : 0 < volume
        (({t : ℝ | ε / 2 < |f t|} ∩ Set.Ioi 0) ∩ Set.Ioi (max R 0)) :=
      IsOpen.measure_pos volume (hAopen.inter isOpen_Ioi) hne
    have hle : volume (({t : ℝ | ε / 2 < |f t|} ∩ Set.Ioi 0) ∩ Set.Ioi (max R 0)) ≤ 0 := by
      rw [← hSnull]; exact measure_mono hsub
    exact absurd hle (not_le.mpr hpos)
  have hgt : y > R := by
    have := hyU.2; simp only [Set.mem_Ioi] at this; linarith [le_max_left R 0]
  have hlarge : ε / 2 < |f y| := hyU.1.1
  have hsmall : |g y| < ε / 2 := by
    have := hR y (le_of_lt hgt)
    rwa [Real.dist_eq, sub_zero] at this
  rw [hyeq] at hlarge
  linarith

/-- **The decay of the smooth representative.** -/
theorem smoothRep_decay {Φ Ψ : ℝ → ℝ → ℝ} (hΦ : SmoothOpen Φ)
    (hae : (fun p : ℝ × ℝ => Φ p.1 p.2)
      =ᵐ[volume.restrict Q0] (fun p : ℝ × ℝ => Ψ p.1 p.2))
    (hslice : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ => Ψ z θ) (Set.Ioo 0 (π / 2)))
    (hdec : ∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => Ψ z θ) atTop (𝓝 0)) :
    ∀ θ ∈ Set.Ioo 0 (π / 2), Tendsto (fun z => Φ z θ) atTop (𝓝 0) := by
  have h1 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      (fun θ => Φ z θ) =ᵐ[volume.restrict (Set.Ioo 0 (π / 2))] (fun θ => Ψ z θ) :=
    ae_slice_eq_of_ae_eq hae
  have h2 := ae_slice_eq_all hΦ hslice h1
  intro θ hθ
  have h3 : (fun z => Φ z θ) =ᵐ[volume.restrict (Set.Ioi 0)] (fun z => Ψ z θ) :=
    h2.mono (fun z hz => hz θ hθ)
  have hcΦ : ContinuousOn (fun z => Φ z θ) (Set.Ioi 0) := by
    have h0 : ContDiffOn ℝ 0 (Function.uncurry Φ) Q0 := SmoothOpen.forall hΦ 0
    have h1' : ContDiffOn ℝ 0 (fun z : ℝ => Φ z θ) (Set.Ioi 0) :=
      h0.comp (contDiffOn_id.prodMk (contDiffOn_const (c := θ)))
        (fun z hz => mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)
    exact h1'.continuousOn
  exact tendsto_of_ae_eq_of_tendsto hcΦ (hdec θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) h3

end

end Work.FTS.H2.PhiStarE5
end
-- ===== merged: Submission.Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn_of_continuousOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.MeridianDyn.Bridge.Pieces

/-! ## The angular slice of `K · f / s`, with only *continuity* on the open quadrant

This is the honest-hypothesis version of `sliceK_integrableOn`: the smoothness input is
reduced from `Work.FTS.EllipticEst.SmoothOpen f` (`C^∞` on the open quadrant) to mere
`ContinuousOn (Function.uncurry f) Q0`.

`Work.Spaces.K θ = 3 sin θ cos²θ` is bounded by `3` everywhere, and for `s > 0` the weight
`w s ≥ 1` while `sin(2θ)^{η/2} ≤ 1` on `Iθ`, so on the angular interval the `i = 0` term of
`HkIntegrand α 4 f` dominates `(f s θ)²` (`Work.Spaces.sq_le_HkIntegrand_z`).  With
`HkMem α 4 f` this gives the square-integrability of the slice; the slice itself is then `L¹`
because `Iθ` has finite measure, and `K θ · f s θ / s` is a bounded (`≤ 3/s`) multiple of it.

Continuity on the *open* quadrant is used only through the a.e. strong measurability of the
slice (`Work.Spaces.aesm_slice_of_continuousOn_Qd`); the two endpoints `θ = 0, π/2` are null
and the `z = 0` slice is excluded by the hypothesis `0 < s`. -/

/-- `|K θ| ≤ 3` for every `θ`. -/
private theorem abs_K_le_three (θ : ℝ) : |Work.Spaces.K θ| ≤ 3 := by
  have hsin : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
  have hcos : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
  rw [Work.Spaces.K, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
    abs_of_nonneg (sq_nonneg (Real.cos θ))]
  nlinarith [abs_nonneg (Real.sin θ)]

/-- `θ ↦ K θ` is continuous. -/
private theorem continuous_K : Continuous Work.Spaces.K := by
  have h : Work.Spaces.K = fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2 := by
    funext θ; rfl
  rw [h]
  exact (continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2)

/-- The angular slice `θ ↦ (f s θ)²` of an `HkMem α 4` datum with *continuity on the open
quadrant* is integrable on `Iθ` for `s > 0`.  This is the analogue of the helper inside
`Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn` (equivalently
`Work.FTS.H2.l12q_slice_sq_integrableOn`) with the hypothesis `SmoothOpen f` weakened to
`ContinuousOn (Function.uncurry f) Q0`. -/
private theorem slice_sq_integrableOn {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hC : ContinuousOn (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f s θ) ^ 2) Work.Spaces.Iθ := by
  -- the squared slice is a.e. strongly measurable (continuity on the open quadrant)
  have hquad : ContinuousOn (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have h1 : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := hC
    have h2 : ContinuousOn (fun p : ℝ × ℝ => (Function.uncurry f p) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := h1.pow 2
    simpa only [Function.uncurry] using h2
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (f s θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2) hquad hs
  -- domination by the `i = 0` term of `HkIntegrand`
  have hsI : s ∈ Work.Spaces.Iz := le_of_lt hs
  refine (hmem.1 s hsI).mono' haesm ?_
  -- the pointwise bound only fails on the two null endpoints
  have hcongr : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := π / 2)).symm
  rw [hcongr]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hsle : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one (le_of_lt hs0) hs1 (by have := Work.Spaces.eta_pos; linarith)
  have hspos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
    Real.rpow_pos_of_pos hs0 _
  have hw1 : 1 ≤ Work.Spaces.w s := by
    rw [Work.Spaces.w, one_le_div (by positivity)]
    nlinarith [hs]
  have hkey : 1 ≤ Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
    rw [one_le_div hspos]
    exact le_trans hsle hw1
  have hW2 : 1 ≤ (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
    have h := mul_le_mul hkey hkey (zero_le_one) (le_trans zero_le_one hkey)
    simpa only [one_mul, pow_two] using h
  have hpt : (f s θ) ^ 2 ≤ (f s θ * (Work.Spaces.w s
      / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    calc (f s θ) ^ 2 = (f s θ) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (f s θ) ^ 2
            * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
          mul_le_mul_of_nonneg_left hW2 (sq_nonneg _)
      _ = (f s θ * (Work.Spaces.w s
            / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := (mul_pow _ _ 2).symm
  calc ‖(f s θ) ^ 2‖ = (f s θ) ^ 2 := Real.norm_of_nonneg (sq_nonneg _)
    _ ≤ (f s θ * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := hpt
    _ = (Work.Spaces.DzIter 0 f s θ * (Work.Spaces.w s
          / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := rfl
    _ ≤ Work.Spaces.HkIntegrand α 4 f s θ :=
        Work.Spaces.sq_le_HkIntegrand_z α 4 f s θ 0 (by norm_num)

/-- The slice `θ ↦ K θ · f s θ / s` is integrable on `Iθ` for `s > 0`, assuming only that
`f` is continuous on the open quadrant and lies in `ℋ⁴`. -/
theorem sliceK_integrableOn_of_continuousOn {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hC : ContinuousOn (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) :
    ∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * f s θ / s) Work.Spaces.Iθ := by
  intro s hs
  -- the slice square and its measurability
  have hsq := slice_sq_integrableOn hC hmem hs
  have hfm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => f s θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry f) hC hs
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (Work.Spaces.K θ / s) * f s θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    ((continuous_K.div_const s).aestronglyMeasurable).mul hfm
  -- the integrable majorant `(3/(2s))·(f² + 1)`
  have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const
      (by rw [Work.Spaces.Iθ]; exact ne_of_lt measure_Icc_lt_top) (by simp)
  have hmaj : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (3 / (2 * s)) * ((f s θ) ^ 2 + 1)) Work.Spaces.Iθ :=
    (hsq.add hconst).const_mul _
  -- the pointwise bound `|K θ|·|f s θ|/s ≤ (3/(2s))·(f² + 1)`
  have hbd : ∀ θ : ℝ, ‖(Work.Spaces.K θ / s) * f s θ‖
      ≤ (3 / (2 * s)) * ((f s θ) ^ 2 + 1) := by
    intro θ
    have hK := abs_K_le_three θ
    have key : 2 * |f s θ| ≤ (f s θ) ^ 2 + 1 := by
      nlinarith [sq_nonneg (|f s θ| - 1), sq_abs (f s θ)]
    have hc : 0 ≤ 3 / (2 * s) := div_nonneg (by norm_num) (by linarith)
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hs]
    calc |Work.Spaces.K θ| / s * |f s θ|
        ≤ 3 / s * |f s θ| :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hK (le_of_lt hs))
            (abs_nonneg _)
      _ = (3 / (2 * s)) * (2 * |f s θ|) := by field_simp
      _ ≤ (3 / (2 * s)) * ((f s θ) ^ 2 + 1) := mul_le_mul_of_nonneg_left key hc
  have hint : MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.K θ / s) * f s θ)
      Work.Spaces.Iθ := by
    refine hmaj.mono' haesm ?_
    exact Filter.Eventually.of_forall hbd
  -- reassociate `K θ / s * f s θ` into `K θ * f s θ / s`
  refine hint.congr_fun (fun θ _ => ?_) ?_
  · ring
  · rw [Work.Spaces.Iθ]; exact measurableSet_Icc

end Work.FTS.MeridianDyn.Bridge.Pieces
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.WtoH_Mixed_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.NonlinRows

open Work.Spaces

noncomputable section

set_option autoImplicit false

/-! ## Elementary absolute-value bookkeeping

(Copied from `Submission/Work/FTS/H2/Q/WtoH_Mixed_Q.lean`, where the same three helpers are
`private`; they are class-agnostic.) -/

/-- Comparison of powers: `|z^k X| ≤ |(z+1)^k X|` for `z ≥ 0`. -/
private lemma abs_mul_pow_le_succ (z X : ℝ) (hz : 0 ≤ z) (k : ℕ) :
    |z ^ k * X| ≤ |(z + 1) ^ k * X| := by
  rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hz k),
    abs_of_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ z + 1) k)]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hz (by linarith) k) (abs_nonneg X)

/-- Triangle inequality for three weighted terms. -/
private lemma abs_comb3_le {Cst : ℝ} (hCst : 0 ≤ Cst) {a b c : ℝ} (ha : |a| ≤ Cst)
    (hb : |b| ≤ Cst) (hc : |c| ≤ Cst) {A B D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    |A * a + B * b + D * c| ≤ (A + B + D) * Cst := by
  have h1 : |A * a| ≤ A * Cst := by
    rw [abs_mul, abs_of_nonneg hA]
    exact mul_le_mul_of_nonneg_left ha hA
  have h2 : |B * b| ≤ B * Cst := by
    rw [abs_mul, abs_of_nonneg hB]
    exact mul_le_mul_of_nonneg_left hb hB
  have h3 : |D * c| ≤ D * Cst := by
    rw [abs_mul, abs_of_nonneg hD]
    exact mul_le_mul_of_nonneg_left hc hD
  have htri : |A * a + B * b + D * c| ≤ |A * a| + |B * b| + |D * c| := by
    calc |A * a + B * b + D * c| ≤ |A * a + B * b| + |D * c| := abs_add_le _ _
      _ ≤ (|A * a| + |B * b|) + |D * c| := by linarith [abs_add_le (A * a) (B * b)]
      _ = |A * a| + |B * b| + |D * c| := by ring
  calc |A * a + B * b + D * c| ≤ |A * a| + |B * b| + |D * c| := htri
    _ ≤ A * Cst + B * Cst + D * Cst := by linarith
    _ = (A + B + D) * Cst := by ring

/-- If `|(z+1)^{j+3} K j| ≤ 6000 M Φ` for `j ≤ l ≤ 3`, `z > 0`, `M, Φ ≥ 0`, then the
weighted expression `((z+1)³ z^l/z²)·(z²K_l + 2l z K_{l-1} + l(l-1)K_{l-2})` is
`≤ 200000 M Φ`. -/
private theorem arith_aux {z : ℝ} (hz : 0 < z) {M Φ : ℝ} (hM : 0 ≤ M) (hΦ : 0 ≤ Φ)
    (l : ℕ) (hl : l ≤ 3) (K : ℕ → ℝ)
    (hK : ∀ j ≤ l, |(z + 1) ^ (j + 3) * K j| ≤ 6000 * (M * Φ)) :
    |(z + 1) ^ 3 * z ^ l / z ^ 2 * (z ^ 2 * K l + (2 * (l : ℝ)) * z * K (l - 1)
        + ((l : ℝ) * ((l : ℝ) - 1)) * K (l - 2))| ≤ 200000 * (M * Φ) := by
  have hMΦ : 0 ≤ M * Φ := mul_nonneg hM hΦ
  have hz0 : (0 : ℝ) ≤ z := le_of_lt hz
  have hterm : ∀ j ≤ l, |z ^ j * ((z + 1) ^ 3 * K j)| ≤ 6000 * (M * Φ) := by
    intro j hj
    refine le_trans (abs_mul_pow_le_succ z ((z + 1) ^ 3 * K j) hz0 j) ?_
    have h2 : (z + 1) ^ j * ((z + 1) ^ 3 * K j) = (z + 1) ^ (j + 3) * K j := by
      rw [← mul_assoc, ← pow_add]
    rw [h2]
    exact hK j hj
  interval_cases l
  · -- l = 0
    have hid : (z + 1) ^ 3 * z ^ 0 / z ^ 2
          * (z ^ 2 * K 0 + (2 * ((0 : ℕ) : ℝ)) * z * K (0 - 1)
              + (((0 : ℕ) : ℝ) * (((0 : ℕ) : ℝ) - 1)) * K (0 - 2))
        = 1 * (z ^ 0 * ((z + 1) ^ 3 * K 0))
          + (2 * ((0 : ℕ) : ℝ)) * (z ^ 0 * ((z + 1) ^ 3 * K 0))
          + (((0 : ℕ) : ℝ) * (((0 : ℕ) : ℝ) - 1)) * (z ^ 0 * ((z + 1) ^ 3 * K 0)) := by
      have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
      push_cast
      norm_num1
      field_simp <;> ring
    rw [hid]
    refine le_trans (abs_comb3_le (by nlinarith [hMΦ]) (hterm 0 (by norm_num))
      (hterm 0 (by norm_num)) (hterm 0 (by norm_num)) (by norm_num) (by norm_num)
      (by norm_num)) ?_
    norm_num1
    nlinarith [hMΦ]
  · -- l = 1
    have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
    have hid : (z + 1) ^ 3 * z ^ 1 / z ^ 2
          * (z ^ 2 * K 1 + (2 * ((1 : ℕ) : ℝ)) * z * K (1 - 1)
              + (((1 : ℕ) : ℝ) * (((1 : ℕ) : ℝ) - 1)) * K (1 - 2))
        = 1 * (z ^ 1 * ((z + 1) ^ 3 * K 1))
          + (2 * ((1 : ℕ) : ℝ)) * (z ^ (1 - 1) * ((z + 1) ^ 3 * K (1 - 1)))
          + (((1 : ℕ) : ℝ) * (((1 : ℕ) : ℝ) - 1))
              * (z ^ (1 - 2) * ((z + 1) ^ 3 * K (1 - 2))) := by
      push_cast
      norm_num1
      field_simp <;> ring
    rw [hid]
    refine le_trans (abs_comb3_le (by nlinarith [hMΦ]) (hterm 1 (by norm_num))
      (hterm 0 (by norm_num)) (hterm 0 (by norm_num)) (by norm_num) (by norm_num)
      (by norm_num)) ?_
    norm_num1
    nlinarith [hMΦ]
  · -- l = 2
    have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
    have hid : (z + 1) ^ 3 * z ^ 2 / z ^ 2
          * (z ^ 2 * K 2 + (2 * ((2 : ℕ) : ℝ)) * z * K (2 - 1)
              + (((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) - 1)) * K (2 - 2))
        = 1 * (z ^ 2 * ((z + 1) ^ 3 * K 2))
          + (2 * ((2 : ℕ) : ℝ)) * (z ^ (2 - 1) * ((z + 1) ^ 3 * K (2 - 1)))
          + (((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) - 1))
              * (z ^ (2 - 2) * ((z + 1) ^ 3 * K (2 - 2))) := by
      push_cast
      norm_num1
      field_simp <;> ring
    rw [hid]
    refine le_trans (abs_comb3_le (by nlinarith [hMΦ]) (hterm 2 (by norm_num))
      (hterm 1 (by norm_num)) (hterm 0 (by norm_num)) (by norm_num) (by norm_num)
      (by norm_num)) ?_
    norm_num1
    nlinarith [hMΦ]
  · -- l = 3
    have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
    have hid : (z + 1) ^ 3 * z ^ 3 / z ^ 2
          * (z ^ 2 * K 3 + (2 * ((3 : ℕ) : ℝ)) * z * K (3 - 1)
              + (((3 : ℕ) : ℝ) * (((3 : ℕ) : ℝ) - 1)) * K (3 - 2))
        = 1 * (z ^ 3 * ((z + 1) ^ 3 * K 3))
          + (2 * ((3 : ℕ) : ℝ)) * (z ^ (3 - 1) * ((z + 1) ^ 3 * K (3 - 1)))
          + (((3 : ℕ) : ℝ) * (((3 : ℕ) : ℝ) - 1))
              * (z ^ (3 - 2) * ((z + 1) ^ 3 * K (3 - 2))) := by
      push_cast
      norm_num1
      field_simp <;> ring
    rw [hid]
    refine le_trans (abs_comb3_le (by nlinarith [hMΦ]) (hterm 3 (by norm_num))
      (hterm 2 (by norm_num)) (hterm 1 (by norm_num)) (by norm_num) (by norm_num)
      (by norm_num)) ?_
    norm_num1
    nlinarith [hMΦ]

/- Port of `Work.FTS.H2.Q.WtoH_Mixed_Q` from `SmoothQuad` to the *open*-quadrant class
`Work.FTS.EllipticEst.SmoothOpen` (the class of the primed interfaces), companion of
`Work.FTS.NonlinRows.WtoH_Radial_O`. -/
theorem WtoH_Mixed_O {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ)) :
    ∀ (i l : ℕ), 1 ≤ i → l + i ≤ 4 → ∀ (z : ℝ), 0 < z → ∀ (θ : ℝ), θ ∈ Set.Ioo 0 (π / 2) →
      |(1 + z) * Work.Spaces.w z * z ^ l
          * Work.Spaces.pzIter l (Work.Spaces.DthIter i f) z θ|
        ≤ 200000 * (Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
  intro i l hi hli z hz θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hrad : 0 ≤ Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) := by
    rw [Work.Spaces.WlInf]
    exact add_nonneg (Work.Spaces.wlZSum_nonneg α 4 _ hmem)
      (Work.Spaces.wlThSum_nonneg α 4 _ hmem)
  have hang : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hs0 _)
  have hGev : ∀ z' : ℝ, 0 < z' → ∀ θ' : ℝ,
      Work.Spaces.DthIter i (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) z' θ'
        = (z' + 1) ^ 3 * Work.Spaces.DthIter i (Work.Elliptic.divZ2 f) z' θ' :=
    fun z' hz' θ' => Work.Elliptic.WtoH_Mixed_g_eq i (ne_of_gt hz')
  have hK : ∀ j ≤ l, |(z + 1) ^ (j + 3)
      * Work.Spaces.pzIter j (Work.Spaces.DthIter i (Work.Elliptic.divZ2 f)) z θ|
      ≤ 6000 * (Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
    tri_aux_O hα hsm hmem hi hli hz hθ hGev
  have hexp := expand_aux_O (f := f) hsm i l (by omega) hz hθ
  have hw : (1 + z) * Work.Spaces.w z * z ^ l = (z + 1) ^ 3 * z ^ l / z ^ 2 := by
    rw [Work.Spaces.w]
    have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
    field_simp <;> ring
  rw [hw, hexp]
  exact arith_aux hz hrad hang l (by omega)
    (fun j => Work.Spaces.pzIter j (Work.Spaces.DthIter i (Work.Elliptic.divZ2 f)) z θ) hK

end

end Work.FTS.NonlinRows
end
-- ===== merged: Submission.Work.FTS.NonlinRows.WtoH_Radial_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

-- NOTE (porting trap).  The statement below is written with the notation `π`, and the `Real`
-- scope must be open for it to mean `Real.pi`: without the `open scoped Real` line the
-- identifier `π` is *not* the constant `Real.pi` — under `autoImplicit = false` (the setting of
-- this lakefile) it is an unknown identifier, and under the default options it would be
-- auto-bound as a free variable, either way not the intended `θ ∈ (0, π/2)`.  Every sibling file
-- opens the scope; the same line is added here.  The statement itself is unchanged.
open scoped Real

namespace Work.FTS.NonlinRows

open Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 1600000

/- Port of `Work.FTS.H2.Q.WtoH_Radial_Q` from the class `SmoothQuad` (C^∞ through z = 0) to the
*open*-quadrant class `Work.FTS.EllipticEst.SmoothOpen` (C^∞ on (0,∞) × (0,π/2) only), which is
the class in which the primed interfaces `N4Norm'`/`StarPkgo` are stated.  Needed by the primed
rows 10, 11, 15, 19 (`Submission/Work/FTS/NonlinRows/`), whose pieces have the shape
`2 ℛ(Φ̃_*)·F_*`: with `f := ℛ(Φ̃_*)·z/(1+z)²` one has `(z+1)³/z²·f = ((z+1)/z)·ℛ(Φ̃_*)` — the
weighted coefficient carried by `StarPkg.R` / to be restored in `StarPkgo`. -/
theorem WtoH_Radial_O {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ)) :
    ∀ (m : ℕ), m ≤ 4 → ∀ (z : ℝ), 0 < z → ∀ (θ : ℝ), θ ∈ Set.Ioo 0 (π / 2) →
      |(1 + z) * Work.Spaces.w z * z ^ m * Work.Spaces.pzIter m f z θ|
        ≤ 200000 * Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) := by
  -- This is the proof of `Work.FTS.H2.Q.WtoH_Radial_Q`, with its two class-dependent inputs
  -- replaced by the open-quadrant counterparts of `WtoH_OpenAux.lean`
  -- (`contDiffAt_divZ2_zslice_O`, `pzIter_divZ2_expansion_aux_O`).  The class-agnostic pieces
  -- (`tri_bound_sm`, `radial_arith`, `g_divZ2_eq`, `WlInf_z_bound`) are reused unchanged: the
  -- conclusion is a pointwise bound at `θ ∈ (0,π/2)`, where the `C^∞`-on-the-open-quadrant
  -- hypothesis provides all the smoothness that the argument uses.
  intro m hm z hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  let G : ℝ → ℝ → ℝ := fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ
  have hmemG : Work.Spaces.WlInfMem α 4 G := hmem
  have hΛ : 0 ≤ Work.Spaces.WlInf α 4 G := by
    rw [Work.Spaces.WlInf]
    exact add_nonneg (Work.Spaces.wlZSum_nonneg α 4 G hmemG)
      (Work.Spaces.wlThSum_nonneg α 4 G hmemG)
  have hG : G = fun z θ => (z + 1) ^ 3 * Work.Elliptic.divZ2 f z θ :=
    Work.Elliptic.g_divZ2_eq f
  have hκ : ContDiffAt ℝ Work.Stability.smoothOrder
      (fun z' => Work.Elliptic.divZ2 f z' θ) z :=
    contDiffAt_divZ2_zslice_O hsm hθ z hz
  have htri : ∀ j ≤ m,
      |(1 + z) ^ (j + 3) * Work.Spaces.pzIter j (Work.Elliptic.divZ2 f) z θ|
        ≤ 6000 * Work.Spaces.WlInf α 4 G := by
    have h := Work.FTS.H2.Q.tri_bound_sm (G := G) (κ := Work.Elliptic.divZ2 f) hG hm hz hκ
      (fun j hj => Work.Spaces.WlInf_z_bound α 4 G hmemG j (by omega) z θ (le_of_lt hz) hθI)
    intro j hj
    have h' := h j hj
    rw [show (1 : ℝ) + z = z + 1 by ring]
    exact h'
  have hA := pzIter_divZ2_expansion_aux_O hsm hm hz hθ
  rw [hA]
  exact Work.Elliptic.radial_arith (Λ := Work.Spaces.WlInf α 4 G) hm hz hΛ
    (fun j => Work.Spaces.pzIter j (Work.Elliptic.divZ2 f) z θ) htri

end Work.FTS.NonlinRows
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.smoothOpen_radA =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/- Open-quadrant infrastructure for the primed star rows (`N1ss = 2ℛ(Φ̃_*)F_*`, row 11, and
row 10's `2ℛ(Φ̃_*)g`): the radial factor `radA = ℛ(Φ̃_*)·z/(1+z)²` of `N1ss = (2Bv(θ))·radA` is
`C^∞` on the open quadrant from `StarPkgo.smooth`, and the weighted factor relevant to
`StarPkg.R`/`StarPkgo.R` is `(z+1)³/z²·radA = ((z+1)/z)·ℛ(Φ̃_*)`.

This is the `SmoothOpen` counterpart of the pair `smoothQuad_radA` / `weighted_eq_Rv` of
`Submission/Work/FTS/Nonlinear/Pieces/RNPV2/row11.lean` (`SmoothQuad` class).  The smoothness part
uses `L12 (Fstar α) z = 2α/(1+z)` (`FstarPkg/L12_Fstar_eq_of_gt_neg_one`, hence `0 < α ≤ 1`), so
that `Theta α (Fstar α) = sin(2θ)/(2(1+z))` is smooth on the open quadrant, and the identity part is
the pointwise `field_simp`/`ring` computation of `weighted_eq_Rv`. -/

/-! ## The two auxiliary `SmoothOpen` facts

The open-quadrant analogues of `smoothQuad_Theta_Fstar` and `smoothQuad_Rop` of
`Submission/Work/FTS/Nonlinear/Pieces/RNP/N1ss_smoothQuad.lean` (which are stated for the
*analytic* class `LocData.SmoothQuad`, unusable here since `SmoothOpen` is only `C^∞` on the
open quadrant). -/

/-- **`Θ_*(α) = Θ α (F_*)` is `C^∞` on the open quadrant.**  By the profile identity
`L₁₂(F_*)(z) = 2α/(1+z)` (valid for every `z > -1`, hence on `Q0`) it is the explicit function
`(z,θ) ↦ sin(2θ)/(2(1+z))`, smooth on `Q0` because `1 + z > 0` there. -/
theorem smoothOpen_Theta_Fstar {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Theta α (Work.Construction.Fstar α)) := by
  have hsmooth : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => Real.sin (2 * θ) / (2 * (1 + z))) := by
    change ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin (2 * p.2) / (2 * (1 + p.1)))
      Work.FTS.EllipticEst.Q0
    have hnum : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
    have hden : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => 2 * (1 + p.1)) Work.FTS.EllipticEst.Q0 :=
      contDiffOn_const.mul (contDiffOn_const.add contDiffOn_fst)
    have hne : ∀ p ∈ Work.FTS.EllipticEst.Q0, 2 * (1 + p.1) ≠ 0 := by
      intro p hp
      have hp1 : (0 : ℝ) < 1 + p.1 := by
        have := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
        linarith
      positivity
    exact hnum.div hden hne
  refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl hsmooth ?_
  intro z θ hz0 hθ0 hθ1
  have hz : -1 < z := by linarith
  have hα0 : α ≠ 0 := ne_of_gt hα
  have h1z : (1 + z : ℝ) ≠ 0 := by positivity
  show Real.sin (2 * θ) / (2 * (1 + z))
      = Work.Construction.Theta α (Work.Construction.Fstar α) z θ
  simp only [Work.Construction.Theta, Work.Construction.s2]
  rw [Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one hα hα1 hz]
  field_simp
  ring

/-- **The operator `ℛ` preserves `C^∞`-smoothness on the open quadrant.**  The only point to
check is that the division by `cos θ` is legitimate there (`cos θ > 0` for `0 < θ < π/2`); all
the remaining factors are `sin θ`, `cos θ`, `z`, the datum `Ψ` and its two first derivatives
(`SmoothOpen.pz`, `SmoothOpen.pth`). -/
theorem smoothOpen_Rop {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Rop α Ψ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (Work.Construction.Rop α Ψ)) Work.FTS.EllipticEst.Q0
  have hΨ' : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry Ψ)
      Work.FTS.EllipticEst.Q0 := hΨ
  have hpz : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pz Ψ)) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.SmoothOpen.pz hΨ
  have hpth : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pth Ψ)) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.SmoothOpen.pth hΨ
  have hsin : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin p.2) Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_sin.comp contDiff_snd).contDiffOn
  have hcos : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.cos p.2) Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_cos.comp contDiff_snd).contDiffOn
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => 2 * Real.sin p.2 * Function.uncurry Ψ p) Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_const.mul hsin).mul hΨ'
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => α * Real.sin p.2 * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p)
      Work.FTS.EllipticEst.Q0 :=
    ((contDiffOn_const.mul hsin).mul contDiffOn_fst).mul hpz
  have h3 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.cos p.2 * Function.uncurry (Work.Spaces.pth Ψ) p)
      Work.FTS.EllipticEst.Q0 :=
    hcos.mul hpth
  have hnum : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => 2 * Real.sin p.2 * Function.uncurry Ψ p
        + α * Real.sin p.2 * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p
        + Real.cos p.2 * Function.uncurry (Work.Spaces.pth Ψ) p) Work.FTS.EllipticEst.Q0 :=
    (h1.add h2).add h3
  have hne : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.cos p.2 ≠ 0 := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)
  refine (hnum.div hcos hne).congr ?_
  intro p _
  obtain ⟨z, θ⟩ := p
  rfl

/-- **`Φ̃_* = Φ_* - Θ_*(α)` is `C^∞` on the open quadrant**, from `StarPkgo.smooth` and
`smoothOpen_Theta_Fstar`. -/
theorem smoothOpen_PhiTs {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) := by
  have hTheta : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Theta α (Work.Construction.Fstar α)) :=
    smoothOpen_Theta_Fstar hα hα1
  have hmain : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => Φs z θ - Work.Construction.Theta α (Work.Construction.Fstar α) z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl hs.smooth hTheta
  refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl (f := fun z θ : ℝ =>
    Φs z θ - Work.Construction.Theta α (Work.Construction.Fstar α) z θ) hmain ?_
  intro z θ _ _ _
  rfl

/-- The rational factor `z/(1+z)²` of `radA` is `C^∞` on the open quadrant. -/
theorem smoothOpen_rat_z :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (1 + z) ^ 2) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (fun p : ℝ × ℝ => p.1 / (1 + p.1) ^ 2) Work.FTS.EllipticEst.Q0
  have hnum : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1)
      Work.FTS.EllipticEst.Q0 := contDiffOn_fst
  have hden : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => (1 + p.1) ^ 2) Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_const.add contDiffOn_fst).pow 2
  have hne : ∀ p ∈ Work.FTS.EllipticEst.Q0, (1 + p.1) ^ 2 ≠ 0 := by
    intro p hp
    have hp1 : (0 : ℝ) < 1 + p.1 := by
      have := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
      linarith
    positivity
  exact hnum.div hden hne

theorem smoothOpen_radA {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
        Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ * z / (1 + z) ^ 2) ∧
    (fun z θ => (z + 1) ^ 3 / z ^ 2
        * (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ * z / (1 + z) ^ 2))
      = (fun z θ => (z + 1) / z
          * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) := by
  constructor
  · have hPhi : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) :=
      smoothOpen_PhiTs hα hα1 hs
    have hRop : Work.FTS.EllipticEst.SmoothOpen
        (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) := smoothOpen_Rop hPhi
    have hrat : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (1 + z) ^ 2) :=
      smoothOpen_rat_z
    have hprod : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ : ℝ => Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
          * (z / (1 + z) ^ 2)) :=
      Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hRop hrat
    refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl (f := fun z θ : ℝ =>
      Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ * (z / (1 + z) ^ 2)) hprod ?_
    intro z θ _ _ _
    rw [mul_div_assoc']
  · funext z θ
    show (z + 1) ^ 3 / z ^ 2
          * (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ * z / (1 + z) ^ 2)
        = (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
    rcases eq_or_ne z 0 with rfl | hz
    · norm_num
    · rcases eq_or_ne (1 + z) 0 with h1 | h1
      · have hz1 : z = -1 := by linarith
        rw [hz1]
        norm_num
      · field_simp
        ring

end Work.FTS.NonlinRows
end
-- ===== merged: Submission.Work.FTS.NonlinRows.sqm_pz_DthIter_mul_le_4_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows

set_option autoImplicit false

/- Open-quadrant port of `Work.FTS.H2.sqm_pz_DthIter_mul_le_4` (`SmoothQuad` → `SmoothOpen`),
with the domain restricted to `z > 0` (the only points where `SmoothOpen` supplies the slices'
differentiability: `SmoothQuad`-style smoothness at `z = 0` is *not* available, and both the
Leibniz identity and the bound are stated at interior `z` only).  Needed by the primed rows
10/11/15/19 (`Submission/Work/FTS/NonlinRows/`) to pass the pointwise `𝒲`-type bounds of the two
factors of `2ℛ(Φ̃_*)F_*` to their product.  The `SmoothQuad` hypothesis of the source is used only
through the `z`-slices (`SmoothOpen.curry_z`), so the port is a verbatim re-run; `257` is the
constant of `Work.Spaces.one_add_choose_double_sum_le`. -/

/-! ## The mixed Leibniz calculus of `∂_z^k D_θ^j` in the open quadrant

The `SmoothOpen` (`C^∞` on the open quadrant `z > 0`, `0 < θ < π/2`) counterpart of the
`SmoothQuad` block of `Submission/Work/FTS/H2/prodW_interior_bound.lean`.  The only difference is
that no smoothness at `z = 0` is available, so every statement is made at `z > 0`; the proofs are
verbatim re-runs, with `SmoothOpen.curry_z`/`SmoothOpen.curry_θ` and
`Work.FTS.LocData.DthIter_mul_smoothQuad` in place of their `SmoothQuad` counterparts. -/

/-- The `z`-slices of the `D_θ`-iterates of a `SmoothOpen` function are `C^∞` at every `z > 0`,
for `θ ∈ (0,π/2)`. -/
theorem sqo_dthIter_zslice_contDiffAt {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2))
    {z : ℝ} (hz : 0 < z) (a : ℕ) :
    ContDiffAt ℝ Work.Stability.smoothOrder (fun z' => Work.Spaces.DthIter a f z' θ) z :=
  ((hf.DthIter a).curry_z hθ).contDiffAt (isOpen_Ioi.mem_nhds hz)

/-- At a fixed angle `θ ∈ (0,π/2)` the `D_θ`-Leibniz expansion of a product agrees with
`D_θ^j (f g)` on a neighbourhood of every `z > 0`. -/
theorem sqo_DthIter_mul_zslice_eventuallyEq (j : ℕ) (f g : ℝ → ℝ → ℝ)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (fun z' => Work.Spaces.DthIter j (fun z θ => f z θ * g z θ) z' θ)
      =ᶠ[𝓝 z] (fun z' => ∑ a ∈ Finset.range (j + 1),
        (j.choose a : ℝ)
          * (Work.Spaces.DthIter a f z' θ * Work.Spaces.DthIter (j - a) g z' θ)) := by
  filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
  exact Work.FTS.LocData.DthIter_mul_smoothQuad j f g hθ (hf.curry_θ hz') (hg.curry_θ hz')

/-- **The mixed Leibniz identity in the open class**: for `SmoothOpen` functions `f, g`, every
`z > 0` and `θ ∈ (0,π/2)`,
`∂_z^k D_θ^j (f g) = ∑_{a≤j} ∑_{c≤k} C(j,a) C(k,c) ∂_z^c D_θ^a f · ∂_z^{k-c} D_θ^{j-a} g`. -/
theorem sqo_pz_DthIter_mul_eq (k j : ℕ) (f g : ℝ → ℝ → ℝ)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun z θ => f z θ * g z θ)) z θ
        = ∑ a ∈ Finset.range (j + 1), ∑ c ∈ Finset.range (k + 1),
            ((j.choose a : ℝ) * (k.choose c : ℝ))
              * (Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ
                  * Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ) := by
  intro z hz θ hθ
  have hslice : ∀ (h : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen h → ∀ a : ℕ,
      ContDiffAt ℝ Work.Stability.smoothOrder (fun z' => Work.Spaces.DthIter a h z' θ) z :=
    fun h hh a => sqo_dthIter_zslice_contDiffAt hh hθ hz a
  have hleib := sqo_DthIter_mul_zslice_eventuallyEq j f g hf hg hz hθ
  rw [Work.Spaces.pzIter_eq_iteratedDeriv k _ z θ, Filter.EventuallyEq.iteratedDeriv_eq k hleib]
  have hsum := Work.Spaces.iteratedDeriv_sum_const_mul (s := Finset.range (j + 1))
    (c := fun a => (j.choose a : ℝ))
    (F := fun a z' => Work.Spaces.DthIter a f z' θ * Work.Spaces.DthIter (j - a) g z' θ) k z
    (fun a _ => ((hslice f hf a).mul (hslice g hg (j - a))).of_le
      (by rw [Work.Stability.smoothOrder]; simp))
  rw [hsum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hfun : (fun z' => Work.Spaces.DthIter a f z' θ * Work.Spaces.DthIter (j - a) g z' θ)
      = (fun z' => Work.Spaces.DthIter a f z' θ)
        * (fun z' => Work.Spaces.DthIter (j - a) g z' θ) := by
    funext z'; rfl
  rw [hfun]
  have hmul := iteratedDeriv_mul (f := fun z' => Work.Spaces.DthIter a f z' θ)
    (g := fun z' => Work.Spaces.DthIter (j - a) g z' θ) (x := z) (n := k)
    ((hslice f hf a).of_le (by rw [Work.Stability.smoothOrder]; simp))
    ((hslice g hg (j - a)).of_le (by rw [Work.Stability.smoothOrder]; simp))
  rw [hmul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Work.Spaces.pzIter_eq_iteratedDeriv c (Work.Spaces.DthIter a f) z θ,
    ← Work.Spaces.pzIter_eq_iteratedDeriv (k - c) (Work.Spaces.DthIter (j - a) g) z θ]
  ring

/-- **The Leibniz bound in the open class**, with the explicit constant `257` of
`Work.Spaces.one_add_choose_double_sum_le` (the `SmoothOpen` counterpart of
`Work.FTS.H2.sqm_pz_DthIter_mul_le_4`): for `SmoothOpen` functions `f, g`, every `z > 0`, every
`θ ∈ (0,π/2)` and `k, j ≤ 4`,
`|∂_z^k D_θ^j (f g)| ≤ 257 ∑_{c≤k} ∑_{a≤j} |∂_z^c D_θ^a f| · |∂_z^{k-c} D_θ^{j-a} g|`. -/
theorem sqm_pz_DthIter_mul_le_4_open (k j : ℕ) (hk : k ≤ 4) (hj : j ≤ 4) (f g : ℝ → ℝ → ℝ)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun z θ => f z θ * g z θ)) z θ| ≤
        (257 : ℝ) * ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
          |Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ| *
            |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ| := by
  intro z hz θ hθ
  rw [sqo_pz_DthIter_mul_eq k j f g hf hg z hz θ hθ]
  have h1 := Work.Spaces.abs_binom_double_sum_le k j
    (fun a c => Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ)
    (fun a c => Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ)
  have hT : (0 : ℝ) ≤ ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
      |Work.Spaces.pzIter c (Work.Spaces.DthIter a f) z θ| *
        |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) g) z θ| :=
    Finset.sum_nonneg fun c _ =>
      Finset.sum_nonneg fun a _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  exact h1.trans (mul_le_mul_of_nonneg_right
    (Work.Spaces.one_add_choose_double_sum_le k j hk hj) hT)

end Work.FTS.NonlinRows
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.Bv_WlInf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP

set_option autoImplicit false

/-! ## `Bv` as a scalar multiple of `Γ` -/

/-- `Bv α` is the constant multiple `2α/c(α)` of `Γ(α,·)`. -/
lemma Bv_eq_const_mul (α : ℝ) :
    Bv α = fun θ => (2 * α / Work.Spaces.c α) * Work.Spaces.Gam α θ := by
  funext θ
  simp only [Bv]
  ring

/-! ## Functions of `θ` alone: their radial derivatives vanish, their angular
derivatives are the univariate iterates of `dthU` -/

/-- The `(m+1)`-st iterated `z`-derivative of a function of `θ` alone vanishes. -/
lemma pzIter_z_indep_succ_zero (g : ℝ → ℝ) (m : ℕ) :
    Work.Spaces.pzIter (m + 1) (fun _ (θ : ℝ) => g θ) = fun _ _ => (0 : ℝ) := by
  induction m with
  | zero => ext z θ; simp [Work.Spaces.pz, deriv_const]
  | succ m ih =>
      rw [Work.Spaces.pzIter_succ, ih]
      ext z θ
      simp [Work.Spaces.pz, deriv_const]

/-- The `k`-th iterated `z`-derivative of a function of `θ` alone vanishes for `k ≠ 0`. -/
lemma pzIter_z_indep_ne_zero (g : ℝ → ℝ) (k : ℕ) (hk : k ≠ 0) :
    Work.Spaces.pzIter k (fun _ (θ : ℝ) => g θ) = fun _ _ => (0 : ℝ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  exact pzIter_z_indep_succ_zero g m

/-- The iterated `D_θ`-derivative of a function of `θ` alone is the corresponding iterate
of the univariate operator `dthU`. -/
lemma DthIter_z_indep (g : ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter j (fun _ (θ' : ℝ) => g θ') z θ = Work.Spaces.dthU^[j] g θ := by
  have h := Work.Spaces.DthIter_decomp j g (fun _ : ℝ => (1 : ℝ)) z θ
  simpa using h

/-! ## The two pointwise estimates for `Bv α` -/

/-- `|Bv α θ| ≤ 20 α` on `Iθ`, for `0 < α ≤ 1`. -/
lemma Bv_abs_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Bv α θ| ≤ 20 * α := by
  have hc := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hfac : 2 * α / Work.Spaces.c α ≤ 20 * α := by
    rw [div_le_iff₀ hcpos]
    nlinarith [hc, hα]
  have hfac0 : 0 ≤ 2 * α / Work.Spaces.c α := by positivity
  have hG := (Work.Spaces.Gam_bounds α θ hα hθ).2
  have hG0 := (Work.Spaces.Gam_bounds α θ hα hθ).1
  rw [show Bv α θ = (2 * α / Work.Spaces.c α) * Work.Spaces.Gam α θ from
        congrFun (Bv_eq_const_mul α) θ,
      abs_mul, abs_of_nonneg hfac0, abs_of_nonneg hG0]
  calc (2 * α / Work.Spaces.c α) * Work.Spaces.Gam α θ
      ≤ (2 * α / Work.Spaces.c α) * 1 := mul_le_mul_of_nonneg_left hG hfac0
    _ ≤ 20 * α := by rw [mul_one]; exact hfac

/-- The angular `𝒲^{4,∞}`-estimate for `Bv α`: for `1 ≤ j` and `θ ∈ Iθ`,
`|D_θ^j (Bv α)(θ) · sin(2θ)^{-α/5}/(α+sin 2θ)| ≤ 20 α · tBound (j-1) 0`. -/
lemma Bv_dthIter_weight_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (j : ℕ) (hj : 1 ≤ j)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.dthU^[j] (fun t => Bv α t) θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
      ≤ 20 * α * Work.Spaces.tBound (j - 1) 0 := by
  have hc := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hfac : 2 * α / Work.Spaces.c α ≤ 20 * α := by
    rw [div_le_iff₀ hcpos]
    nlinarith [hc, hα]
  have hfac0 : 0 ≤ 2 * α / Work.Spaces.c α := by positivity
  -- the signs of the angular factors
  have hs2 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) := Real.rpow_nonneg hs2 _
  have hd : 0 < α + Real.sin (2 * θ) := by linarith
  -- pull the constant factor `2α/c(α)` out of the iterated `dthU`
  have hA : Work.Spaces.dthU^[j] (fun t => Bv α t) θ
      = (2 * α / Work.Spaces.c α)
          * Work.Spaces.dthU^[j] (fun t => Work.Spaces.Gam α t) θ := by
    have h : (fun t => Bv α t)
        = fun t => (2 * α / Work.Spaces.c α) * Work.Spaces.Gam α t := by
      funext t
      exact congrFun (Bv_eq_const_mul α) t
    rw [h, Work.Spaces.dthU_iter_const_mul]
  have hGle := Work.Spaces.dthU_Gam_le j hj α hα hα1 θ hθ
  have hGw := Work.Spaces.Gam_mul_weight_le α θ hα hθ
  have hT0 := Work.Spaces.tBound_nonneg (j - 1) 0
  -- `α Γ(θ) sin(2θ)^{-α/5} ≤ α + sin(2θ)`
  have hGamW : α * Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5))
      ≤ α + Real.sin (2 * θ) := by
    have := (div_le_iff₀ hd).mp hGw
    simpa using this
  rw [hA, abs_div, abs_mul]
  rw [abs_mul, abs_of_nonneg hfac0, abs_of_nonneg hs0, abs_of_nonneg (le_of_lt hd)]
  rw [div_le_iff₀ hd]
  calc (2 * α / Work.Spaces.c α)
        * |Work.Spaces.dthU^[j] (fun t => Work.Spaces.Gam α t) θ|
        * (Real.sin (2 * θ)) ^ (-(α / 5))
      ≤ (2 * α / Work.Spaces.c α)
        * (α * Work.Spaces.tBound (j - 1) 0 * Work.Spaces.Gam α θ)
        * (Real.sin (2 * θ)) ^ (-(α / 5)) := by
        apply mul_le_mul_of_nonneg_right _ hs0
        exact mul_le_mul_of_nonneg_left hGle hfac0
    _ = (2 * α / Work.Spaces.c α) * Work.Spaces.tBound (j - 1) 0
        * (α * Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5))) := by ring
    _ ≤ (2 * α / Work.Spaces.c α) * Work.Spaces.tBound (j - 1) 0
        * (α + Real.sin (2 * θ)) :=
        mul_le_mul_of_nonneg_left hGamW (mul_nonneg hfac0 hT0)
    _ ≤ (20 * α) * Work.Spaces.tBound (j - 1) 0 * (α + Real.sin (2 * θ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfac hT0) (le_of_lt hd)
    _ = (20 * α * Work.Spaces.tBound (j - 1) 0) * (α + Real.sin (2 * θ)) := by ring

/-! ## From pointwise estimates to the `𝒲^{4,∞}`-norm, for a function of `θ` alone -/


/-! ## The target -/


end Work.FTS.Nonlinear.Pieces.RNP
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.N1ss_smoothQuad =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP

/-! ## The two ingredients: `ℛ` preserves `C^∞`, and `Θ α (F_*)` is `C^∞` -/

/-- **The operator `ℛ` preserves `C^∞`-smoothness on the open quadrant.**  The only point to
check is that the division by `cos θ` is legitimate there: on `quadU = (z > -1) × (0 < θ < π/2)`
the angle lies in `(0, π/2)`, where `cos` is strictly positive.  All the remaining factors are
the smooth functions `sin θ`, `cos θ`, `z`, the datum `Ψ` itself, and its two first derivatives
(`contDiffOn_pz`, `contDiffOn_pth`). -/
theorem smoothQuad_Rop {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.LocData.SmoothQuad Ψ) :
    Work.FTS.LocData.SmoothQuad (Work.Construction.Rop α Ψ) := by
  have hpz : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pz Ψ)) Work.Spaces.quadU :=
    Work.FTS.LocData.contDiffOn_pz Work.Spaces.isOpen_quadU hΨ
  have hpth : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pth Ψ)) Work.Spaces.quadU :=
    Work.FTS.LocData.contDiffOn_pth Work.Spaces.isOpen_quadU hΨ
  have hsin : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin p.2) Work.Spaces.quadU :=
    (Real.contDiff_sin.comp contDiff_snd).contDiffOn
  have hcos : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.cos p.2) Work.Spaces.quadU :=
    (Real.contDiff_cos.comp contDiff_snd).contDiffOn
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => 2 * Real.sin p.2 * Function.uncurry Ψ p) Work.Spaces.quadU :=
    (contDiffOn_const.mul hsin).mul hΨ
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => α * Real.sin p.2 * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p)
      Work.Spaces.quadU :=
    ((contDiffOn_const.mul hsin).mul contDiffOn_fst).mul hpz
  have h3 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.cos p.2 * Function.uncurry (Work.Spaces.pth Ψ) p)
      Work.Spaces.quadU :=
    hcos.mul hpth
  have hnum : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => 2 * Real.sin p.2 * Function.uncurry Ψ p
        + α * Real.sin p.2 * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p
        + Real.cos p.2 * Function.uncurry (Work.Spaces.pth Ψ) p) Work.Spaces.quadU :=
    (h1.add h2).add h3
  have hne : ∀ p ∈ Work.Spaces.quadU, Real.cos p.2 ≠ 0 := by
    intro p hp
    have hpos : 0 < Real.cos p.2 :=
      Real.cos_pos_of_mem_Ioo
        ⟨by linarith [(Set.mem_Ioo.mp hp.2).1, Real.pi_pos], (Set.mem_Ioo.mp hp.2).2⟩
    exact ne_of_gt hpos
  refine (hnum.div hcos hne).congr ?_
  intro p _
  obtain ⟨z, θ⟩ := p
  rfl

/-- **`Θ_*(α) = Θ α (F_*)` is `C^∞` on the open quadrant.**  By the profile identity
`L₁₂(F_*)(z) = 2α/(1+z)` (valid for every `z > -1`) it is the explicit function
`(z, θ) ↦ sin(2θ)/(2(1+z))`, which is smooth there because the denominator `2(1+z)` is
positive. -/
theorem smoothQuad_Theta_Fstar {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.LocData.SmoothQuad (Work.Construction.Theta α (Work.Construction.Fstar α)) := by
  have hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin (2 * p.2) / (2 * (1 + p.1))) Work.Spaces.quadU := by
    have hnum : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.Spaces.quadU :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
    have hden : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => 2 * (1 + p.1)) Work.Spaces.quadU :=
      contDiffOn_const.mul (contDiffOn_const.add contDiffOn_fst)
    have hne : ∀ p ∈ Work.Spaces.quadU, 2 * (1 + p.1) ≠ 0 := by
      intro p hp
      have hp1 : (0 : ℝ) < 1 + p.1 := by
        have := Set.mem_Ioi.mp hp.1; linarith
      positivity
    exact hnum.div hden hne
  refine hsmooth.congr ?_
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hz : -1 < z := Set.mem_Ioi.mp hp.1
  simp only [Function.uncurry, Work.Construction.Theta, Work.Construction.s2]
  rw [Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one hα hα1 hz]
  field_simp
  ring

/-! ## The target -/


end Work.FTS.Nonlinear.Pieces.RNP
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.Rv_smooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP

set_option autoImplicit false








end Work.FTS.Nonlinear.Pieces.RNP
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.pth_Fstar_lower =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux


end Work.FTS.Nonlinear.Pieces.RNP.row15aux
end
-- ===== merged: Submission.Work.FTS.OpenPkg.WtohWin.wtoh_mixed_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.OpenPkg.WtohWin

/-! # Elgindi's mixed-derivative `WtoH` estimate in the open-quadrant class

This is the verbatim port of `Work.FTS.H2.Q.WtoH_Mixed_Q` (stated for the class
`Work.FTS.LocData.SmoothQuad`, i.e. `C^∞` *through* `z = 0`) to the *open*-quadrant class
`Work.FTS.EllipticEst.SmoothOpen` (`C^∞` on `(0,∞) × (0,π/2)` only), which is the class in
which the primed interfaces `N4Norm'`/`StarPkgo` live.

The two class-dependent inputs are supplied by `Submission/Work/FTS/NonlinRows/WtoH_OpenAux.lean`:

* `contDiffAt_DthIter_divZ2_zslice_O` (the `z`-slices of the `D_θ`-iterates of `divZ2 f = f/z²`
  are `C^∞` at every `z > 0`);
* `expand_aux_O` (the Leibniz expansion `∂_z^l D_θ^i f = z² ∂_z^l κ + 2l z ∂_z^{l-1}κ
  + l(l-1) ∂_z^{l-2}κ`, with `κ = D_θ^i (divZ2 f)`);
* `tri_aux_O` (the `𝒲^{4,∞}`-bound on `(z+1)^{j+3} ∂_z^j (D_θ^i (divZ2 f))`).

The arithmetic bookkeeping (`abs_mul_pow_le_succ`, `abs_comb3_le`, `arith_aux`) is
class-agnostic and is the same as in `WtoH_Mixed_Q` (`arith_aux` is `private` there, so it is
repeated here). -/

/-! ## Elementary absolute-value bookkeeping -/

/-- Comparison of powers: `|z^k X| ≤ |(z+1)^k X|` for `z ≥ 0`. -/
private lemma abs_mul_pow_le_succ (z X : ℝ) (hz : 0 ≤ z) (k : ℕ) :
    |z ^ k * X| ≤ |(z + 1) ^ k * X| := by
  rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hz k),
    abs_of_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ z + 1) k)]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hz (by linarith) k) (abs_nonneg X)

/-- Triangle inequality for three weighted terms. -/
private lemma abs_comb3_le {Cst : ℝ} (hCst : 0 ≤ Cst) {a b c : ℝ} (ha : |a| ≤ Cst)
    (hb : |b| ≤ Cst) (hc : |c| ≤ Cst) {A B D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    |A * a + B * b + D * c| ≤ (A + B + D) * Cst := by
  have h1 : |A * a| ≤ A * Cst := by
    rw [abs_mul, abs_of_nonneg hA]
    exact mul_le_mul_of_nonneg_left ha hA
  have h2 : |B * b| ≤ B * Cst := by
    rw [abs_mul, abs_of_nonneg hB]
    exact mul_le_mul_of_nonneg_left hb hB
  have h3 : |D * c| ≤ D * Cst := by
    rw [abs_mul, abs_of_nonneg hD]
    exact mul_le_mul_of_nonneg_left hc hD
  have htri : |A * a + B * b + D * c| ≤ |A * a| + |B * b| + |D * c| := by
    calc |A * a + B * b + D * c| ≤ |A * a + B * b| + |D * c| := abs_add_le _ _
      _ ≤ (|A * a| + |B * b|) + |D * c| := by linarith [abs_add_le (A * a) (B * b)]
      _ = |A * a| + |B * b| + |D * c| := by ring
  calc |A * a + B * b + D * c| ≤ |A * a| + |B * b| + |D * c| := htri
    _ ≤ A * Cst + B * Cst + D * Cst := by linarith
    _ = (A + B + D) * Cst := by ring

/-! ## The elementary weighted estimate -/

/-- If `|(z+1)^{j+3} K j| ≤ 6000 M Φ` for `j ≤ l ≤ 3`, `z > 0`, `M, Φ ≥ 0`, then the
weighted expression `((z+1)³ z^l/z²)·(z²K_l + 2l z K_{l-1} + l(l-1)K_{l-2})` is
`≤ 200000 M Φ`. -/
private theorem arith_aux {z : ℝ} (hz : 0 < z) {M Φ : ℝ} (hM : 0 ≤ M) (hΦ : 0 ≤ Φ)
    (l : ℕ) (hl : l ≤ 3) (K : ℕ → ℝ)
    (hK : ∀ j ≤ l, |(z + 1) ^ (j + 3) * K j| ≤ 6000 * (M * Φ)) :
    |(z + 1) ^ 3 * z ^ l / z ^ 2 * (z ^ 2 * K l + (2 * (l : ℝ)) * z * K (l - 1)
        + ((l : ℝ) * ((l : ℝ) - 1)) * K (l - 2))| ≤ 200000 * (M * Φ) := by
  have hMΦ : 0 ≤ M * Φ := mul_nonneg hM hΦ
  have hz0 : (0 : ℝ) ≤ z := le_of_lt hz
  have hterm : ∀ j ≤ l, |z ^ j * ((z + 1) ^ 3 * K j)| ≤ 6000 * (M * Φ) := by
    intro j hj
    refine le_trans (abs_mul_pow_le_succ z ((z + 1) ^ 3 * K j) hz0 j) ?_
    have h2 : (z + 1) ^ j * ((z + 1) ^ 3 * K j) = (z + 1) ^ (j + 3) * K j := by
      rw [← mul_assoc, ← pow_add]
    rw [h2]
    exact hK j hj
  interval_cases l
  · -- l = 0
    have hid : (z + 1) ^ 3 * z ^ 0 / z ^ 2
          * (z ^ 2 * K 0 + (2 * ((0 : ℕ) : ℝ)) * z * K (0 - 1)
              + (((0 : ℕ) : ℝ) * (((0 : ℕ) : ℝ) - 1)) * K (0 - 2))
        = 1 * (z ^ 0 * ((z + 1) ^ 3 * K 0))
          + (2 * ((0 : ℕ) : ℝ)) * (z ^ 0 * ((z + 1) ^ 3 * K 0))
          + (((0 : ℕ) : ℝ) * (((0 : ℕ) : ℝ) - 1)) * (z ^ 0 * ((z + 1) ^ 3 * K 0)) := by
      have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
      push_cast
      norm_num1
      field_simp <;> ring
    rw [hid]
    refine le_trans (abs_comb3_le (by nlinarith [hMΦ]) (hterm 0 (by norm_num))
      (hterm 0 (by norm_num)) (hterm 0 (by norm_num)) (by norm_num) (by norm_num)
      (by norm_num)) ?_
    norm_num1
    nlinarith [hMΦ]
  · -- l = 1
    have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
    have hid : (z + 1) ^ 3 * z ^ 1 / z ^ 2
          * (z ^ 2 * K 1 + (2 * ((1 : ℕ) : ℝ)) * z * K (1 - 1)
              + (((1 : ℕ) : ℝ) * (((1 : ℕ) : ℝ) - 1)) * K (1 - 2))
        = 1 * (z ^ 1 * ((z + 1) ^ 3 * K 1))
          + (2 * ((1 : ℕ) : ℝ)) * (z ^ (1 - 1) * ((z + 1) ^ 3 * K (1 - 1)))
          + (((1 : ℕ) : ℝ) * (((1 : ℕ) : ℝ) - 1))
              * (z ^ (1 - 2) * ((z + 1) ^ 3 * K (1 - 2))) := by
      push_cast
      norm_num1
      field_simp <;> ring
    rw [hid]
    refine le_trans (abs_comb3_le (by nlinarith [hMΦ]) (hterm 1 (by norm_num))
      (hterm 0 (by norm_num)) (hterm 0 (by norm_num)) (by norm_num) (by norm_num)
      (by norm_num)) ?_
    norm_num1
    nlinarith [hMΦ]
  · -- l = 2
    have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
    have hid : (z + 1) ^ 3 * z ^ 2 / z ^ 2
          * (z ^ 2 * K 2 + (2 * ((2 : ℕ) : ℝ)) * z * K (2 - 1)
              + (((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) - 1)) * K (2 - 2))
        = 1 * (z ^ 2 * ((z + 1) ^ 3 * K 2))
          + (2 * ((2 : ℕ) : ℝ)) * (z ^ (2 - 1) * ((z + 1) ^ 3 * K (2 - 1)))
          + (((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) - 1))
              * (z ^ (2 - 2) * ((z + 1) ^ 3 * K (2 - 2))) := by
      push_cast
      norm_num1
      field_simp <;> ring
    rw [hid]
    refine le_trans (abs_comb3_le (by nlinarith [hMΦ]) (hterm 2 (by norm_num))
      (hterm 1 (by norm_num)) (hterm 0 (by norm_num)) (by norm_num) (by norm_num)
      (by norm_num)) ?_
    norm_num1
    nlinarith [hMΦ]
  · -- l = 3
    have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
    have hid : (z + 1) ^ 3 * z ^ 3 / z ^ 2
          * (z ^ 2 * K 3 + (2 * ((3 : ℕ) : ℝ)) * z * K (3 - 1)
              + (((3 : ℕ) : ℝ) * (((3 : ℕ) : ℝ) - 1)) * K (3 - 2))
        = 1 * (z ^ 3 * ((z + 1) ^ 3 * K 3))
          + (2 * ((3 : ℕ) : ℝ)) * (z ^ (3 - 1) * ((z + 1) ^ 3 * K (3 - 1)))
          + (((3 : ℕ) : ℝ) * (((3 : ℕ) : ℝ) - 1))
              * (z ^ (3 - 2) * ((z + 1) ^ 3 * K (3 - 2))) := by
      push_cast
      norm_num1
      field_simp <;> ring
    rw [hid]
    refine le_trans (abs_comb3_le (by nlinarith [hMΦ]) (hterm 3 (by norm_num))
      (hterm 2 (by norm_num)) (hterm 1 (by norm_num)) (by norm_num) (by norm_num)
      (by norm_num)) ?_
    norm_num1
    nlinarith [hMΦ]

/-! ## The transfer -/

theorem wtoh_mixed_open {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ)) :
    ∀ (i l : ℕ), 1 ≤ i → l + i ≤ 4 → ∀ (z : ℝ), 0 < z → ∀ (θ : ℝ), θ ∈ Set.Ioo 0 (π / 2) →
      |(1 + z) * Work.Spaces.w z * z ^ l * Work.Spaces.pzIter l (Work.Spaces.DthIter i f) z θ|
        ≤ 200000 * (Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
  intro i l hi hli z hz θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hrad : 0 ≤ Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) := by
    rw [Work.Spaces.WlInf]
    exact add_nonneg (Work.Spaces.wlZSum_nonneg α 4 _ hmem)
      (Work.Spaces.wlThSum_nonneg α 4 _ hmem)
  have hang : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hs0 _)
  have hGev : ∀ z' : ℝ, 0 < z' → ∀ θ' : ℝ,
      Work.Spaces.DthIter i (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) z' θ'
        = (z' + 1) ^ 3 * Work.Spaces.DthIter i (Work.Elliptic.divZ2 f) z' θ' :=
    fun z' hz' θ' => Work.Elliptic.WtoH_Mixed_g_eq i (ne_of_gt hz')
  have hK : ∀ j ≤ l, |(z + 1) ^ (j + 3)
      * Work.Spaces.pzIter j (Work.Spaces.DthIter i (Work.Elliptic.divZ2 f)) z θ|
      ≤ 6000 * (Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
    Work.FTS.NonlinRows.tri_aux_O hα hsm hmem hi hli hz hθ hGev
  have hexp := Work.FTS.NonlinRows.expand_aux_O (f := f) hsm i l (by omega) hz hθ
  have hw : (1 + z) * Work.Spaces.w z * z ^ l = (z + 1) ^ 3 * z ^ l / z ^ 2 := by
    rw [Work.Spaces.w]
    have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz)
    field_simp <;> ring
  rw [hw, hexp]
  exact arith_aux hz hrad hang l (by omega)
    (fun j => Work.Spaces.pzIter j (Work.Spaces.DthIter i (Work.Elliptic.divZ2 f)) z θ) hK

end Work.FTS.OpenPkg.WtohWin
end
-- ===== merged: Submission.Work.FTS.OpenPkg.WtohWin.wtoh_radial_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg.WtohWin

set_option autoImplicit false

/-! # Elgindi's radial `WtoH` estimate in the open-quadrant class

This is the verbatim port of `Work.FTS.H2.Q.WtoH_Radial_Q` (which is stated for the class
`Work.FTS.LocData.SmoothQuad`, i.e. `C^∞` *through* `z = 0`) to the *open*-quadrant class
`Work.FTS.EllipticEst.SmoothOpen` (`C^∞` on `(0,∞) × (0,π/2)` only), which is the class in
which the primed interfaces `N4Norm'`/`StarPkgo` live.

The two class-dependent inputs are supplied by `Submission/Work/FTS/NonlinRows/WtoH_OpenAux.lean`:

* `contDiffAt_divZ2_zslice_O` (the `z`-slices of `divZ2 f = f/z²` are `C^∞` at every `z > 0`);
* `pzIter_divZ2_expansion_aux_O` (the Leibniz expansion `∂_z^m f = z² ∂_z^m κ + 2m z ∂_z^{m-1}κ
  + m(m-1) ∂_z^{m-2}κ`), proved from `pzIter_sq_mul_sm` of `H2/Q/Base.lean`, which is
  class-agnostic.

The triangular estimate `tri_bound_sm` and the elementary arithmetic `radial_arith` are also
class-agnostic and are reused unchanged. -/
theorem wtoh_radial_open {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ)) :
    ∀ (m : ℕ), m ≤ 4 → ∀ (z : ℝ), 0 < z → ∀ (θ : ℝ), θ ∈ Set.Ioo 0 (π / 2) →
      |(1 + z) * Work.Spaces.w z * z ^ m * Work.Spaces.pzIter m f z θ|
        ≤ 200000 * Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) := by
  intro m hm z hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  let G : ℝ → ℝ → ℝ := fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ
  have hmemG : Work.Spaces.WlInfMem α 4 G := hmem
  have hΛ : 0 ≤ Work.Spaces.WlInf α 4 G := by
    rw [Work.Spaces.WlInf]
    exact add_nonneg (Work.Spaces.wlZSum_nonneg α 4 G hmemG)
      (Work.Spaces.wlThSum_nonneg α 4 G hmemG)
  have hG : G = fun z θ => (z + 1) ^ 3 * Work.Elliptic.divZ2 f z θ :=
    Work.Elliptic.g_divZ2_eq f
  have hκ : ContDiffAt ℝ Work.Stability.smoothOrder
      (fun z' => Work.Elliptic.divZ2 f z' θ) z :=
    Work.FTS.NonlinRows.contDiffAt_divZ2_zslice_O hsm hθ z hz
  have htri : ∀ j ≤ m,
      |(1 + z) ^ (j + 3) * Work.Spaces.pzIter j (Work.Elliptic.divZ2 f) z θ|
        ≤ 6000 * Work.Spaces.WlInf α 4 G := by
    have h := Work.FTS.H2.Q.tri_bound_sm (G := G) (κ := Work.Elliptic.divZ2 f) hG hm hz hκ
      (fun j hj => Work.Spaces.WlInf_z_bound α 4 G hmemG j (by omega) z θ (le_of_lt hz) hθI)
    intro j hj
    have h' := h j hj
    rw [show (1 : ℝ) + z = z + 1 by ring]
    exact h'
  have hA := Work.FTS.NonlinRows.pzIter_divZ2_expansion_aux_O hsm hm hz hθ
  rw [hA]
  exact Work.Elliptic.radial_arith (Λ := Work.Spaces.WlInf α 4 G) hm hz hΛ
    (fun j => Work.Spaces.pzIter j (Work.Elliptic.divZ2 f) z θ) htri

end Work.FTS.OpenPkg.WtohWin
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.LopAuxBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Uniform bounds for the first seven iterates of `Lop` on `Γ̄` and on `6 sin² − 4 cos²`

`Work.Spaces.Lop u θ = sin (2θ) · u'(θ)` is the one-dimensional operator induced by
`D_θ = sin(2θ) ∂_θ`; it is *definitionally* the same function as `Work.Spaces.dthU`.  The
lemma proved here produces a single nonnegative sequence `K` bounding, on the open quadrant
`(0, π/2)` and for all `j ≤ 6`,

* the iterates `Lop^[j] Γ̄_α` of the angular source `Γ̄_α = Γ_α/c_α − (5/4) sin 2θ`,
  *uniformly in `α ∈ (0, 1/4]`*, and
* the iterates `Lop^[j] (6 sin² − 4 cos²)` of a fixed smooth test function
  (the angular part of the `Φ_*`-profile).

## Route

* **The fixed function.**  `h(θ) = 6 sin²θ − 4 cos²θ` is `C^∞`, and `Lop` preserves
  `C^∞`, so every iterate is continuous on the compact interval `[0, π/2]`; compactness
  (`IsCompact.exists_bound_of_continuousOn`) produces a bound, chosen with `Classical.choose`.
* **The `α`-family.**  For `j ≤ 5` the already-proved `Psi0Aux.GamBar_dthU_le` gives
  `|D_θ^j Γ̄| ≤ cc j · α · Γ + dd j · sin 2θ`, and `α ≤ 1/4`, `Γ ≤ 1`, `sin 2θ ≤ 1` turn
  this into `cc j/4 + dd j`; for `j = 0` it gives the constant `K` of that lemma; the
  remaining value `j = 6` is handled by the exact decomposition `D_θ^6 Γ̄ = (1/c) dGam 6 −
  (5/4) Giter 6` on the open quadrant (`Psi0Aux.GamBar_iter_EqOn`), together with
  `|dGam α 6| ≤ α · tBound 5 0 · Γ` and `|Giter 6| ≤ 1095801216 · sin 2θ`
  (`dthU_iter_Tfun_le`, `dthUiter_sin2_iter`).
-/

namespace Work.FTS.PhiStar

theorem LopAuxBounds : ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
    (∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ j ≤ 6, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |(Work.Spaces.Lop^[j]) (Work.FTS.VocabO.GamBar α) θ| ≤ K j) ∧
    (∀ j ≤ 6, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |(Work.Spaces.Lop^[j]) (fun θ => 6 * Real.sin θ ^ 2 - 4 * Real.cos θ ^ 2) θ| ≤ K j) := by
  -- `Lop` and `dthU` have the same body; we work throughout with `dthU` (the vocabulary in
  -- which the auxiliary estimates are stated) and convert back at the very end.
  have hmain : ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
      (∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ j ≤ 6, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |(Work.Spaces.dthU^[j]) (Work.FTS.VocabO.GamBar α) θ| ≤ K j) ∧
      (∀ j ≤ 6, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |(Work.Spaces.dthU^[j]) (fun θ => 6 * Real.sin θ ^ 2 - 4 * Real.cos θ ^ 2) θ| ≤ K j) := by
    -- ## The fixed test function `h = 6 sin² − 4 cos²`, by compactness
    have hsm2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun θ : ℝ => 6 * Real.sin θ ^ 2 - 4 * Real.cos θ ^ 2) := by fun_prop
    have key2 : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          |(Work.Spaces.dthU^[j]) (fun θ => 6 * Real.sin θ ^ 2 - 4 * Real.cos θ ^ 2) θ| ≤ C := by
      intro j
      have hcont : ContinuousOn
          ((Work.Spaces.dthU^[j]) (fun θ : ℝ => 6 * Real.sin θ ^ 2 - 4 * Real.cos θ ^ 2))
          (Set.Icc (0 : ℝ) (Real.pi / 2)) :=
        ((Work.Spaces.dthU_iter_smooth hsm2 j).continuous).continuousOn
      obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hcont
      refine ⟨max C 0, le_max_right _ _, fun θ hθ => ?_⟩
      have h := hC θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      rw [Real.norm_eq_abs] at h
      exact le_trans h (le_max_left _ _)
    choose B2 hB2_0 hB2 using key2
    -- ## The family `Γ̄_α`
    obtain ⟨⟨KG, hKGpos, hKG⟩, cc, dd, hcc0, hdd0, hccdd⟩ :=
      Work.FTS.PhiStar.Psi0Aux.GamBar_dthU_le
    -- the constant for the sixth iterate
    set C6 : ℝ := 10 * (1 / 4 * Work.Spaces.tBound 5 0) + 5 / 4 * 1095801216 with hC6def
    -- ### the range `1 ≤ j ≤ 5`
    have hstep : ∀ j : ℕ, 1 ≤ j → j ≤ 5 → ∀ α : ℝ, 0 < α → α ≤ 1 / 4 →
        ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |(Work.Spaces.dthU^[j]) (Work.FTS.VocabO.GamBar α) θ| ≤ cc j / 4 + dd j := by
      intro j hj1 hj5 α hα hα1 θ hθ
      have h := hccdd α hα hα1 j hj1 hj5 θ hθ
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hG := Work.Spaces.Gam_bounds α θ hα hθI
      have hsin2le : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
      have h1 : cc j * α * Work.Spaces.Gam α θ ≤ cc j / 4 := by
        have hαG : α * Work.Spaces.Gam α θ ≤ 1 / 4 := by
          have h' := mul_le_mul hα1 hG.2 hG.1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
          linarith [h']
        have h'' := mul_le_mul_of_nonneg_left hαG (hcc0 j)
        nlinarith [h'']
      have h2 : dd j * Real.sin (2 * θ) ≤ dd j := by
        have h'' := mul_le_mul_of_nonneg_left hsin2le (hdd0 j)
        nlinarith [h'']
      linarith [h, h1, h2]
    -- ### the sixth iterate
    have hstep6 : ∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |(Work.Spaces.dthU^[6]) (Work.FTS.VocabO.GamBar α) θ| ≤ C6 := by
      intro α hα hα1 θ hθ
      have heq := Work.FTS.PhiStar.Psi0Aux.GamBar_iter_EqOn α hα 6 hθ
      rw [heq, Work.FTS.PhiStar.Psi0Aux.Fbar_apply]
      have hc := (Work.Spaces.c_bounds α hα (by linarith)).1
      have hcpos : 0 < Work.Spaces.c α := by linarith
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hG := Work.Spaces.Gam_bounds α θ hα hθI
      have ht0 : 0 ≤ Work.Spaces.tBound 5 0 := Work.Spaces.tBound_nonneg 5 0
      have hT : |Work.Spaces.Tfun 5 α θ| ≤ Work.Spaces.tBound 5 0 := by
        simpa using Work.Spaces.dthU_iter_Tfun_le 5 α hα (by linarith) θ hθI 0
      have hdG : |Work.FTS.PhiStar.Psi0Aux.dGam α 6 θ| ≤ 1 / 4 * Work.Spaces.tBound 5 0 := by
        have hd : Work.FTS.PhiStar.Psi0Aux.dGam α 6 θ
            = α * Work.Spaces.Tfun 5 α θ * Work.Spaces.Gam α θ := rfl
        rw [hd, abs_mul, abs_mul, abs_of_pos hα, abs_of_nonneg hG.1]
        calc α * |Work.Spaces.Tfun 5 α θ| * Work.Spaces.Gam α θ
            = α * (|Work.Spaces.Tfun 5 α θ| * Work.Spaces.Gam α θ) := by ring
          _ ≤ (1 / 4) * (Work.Spaces.tBound 5 0 * 1) :=
              mul_le_mul hα1 (mul_le_mul hT hG.2 hG.1 ht0)
                (mul_nonneg (abs_nonneg _) hG.1) (by norm_num)
          _ = 1 / 4 * Work.Spaces.tBound 5 0 := by ring
      have hcle : 1 / Work.Spaces.c α ≤ 10 := by
        rw [div_le_iff₀ hcpos]; linarith
      have hA : |(1 / Work.Spaces.c α) * Work.FTS.PhiStar.Psi0Aux.dGam α 6 θ|
          ≤ 10 * (1 / 4 * Work.Spaces.tBound 5 0) := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / Work.Spaces.c α)]
        calc (1 / Work.Spaces.c α) * |Work.FTS.PhiStar.Psi0Aux.dGam α 6 θ|
            ≤ 10 * |Work.FTS.PhiStar.Psi0Aux.dGam α 6 θ| :=
              mul_le_mul_of_nonneg_right hcle (abs_nonneg _)
          _ ≤ 10 * (1 / 4 * Work.Spaces.tBound 5 0) := mul_le_mul_of_nonneg_left hdG (by norm_num)
      have hG6 : |Work.FTS.PhiStar.Psi0Aux.Giter 6 θ| ≤ 1095801216 := by
        have hP : |(Work.FTS.PhiStar.Psi0Aux.dthUiterPW 6).eval (Real.cos θ ^ 2)|
            ≤ 1095801216 := by
          rw [Work.FTS.PhiStar.Psi0Aux.dthUiterPW_eval]
          exact le_trans (Work.FTS.PhiStar.Psi0Aux.dthUiter_abs_sum_pow_le _ _ _
            (sq_nonneg _) (Real.cos_sq_le_one θ))
            (Work.FTS.PhiStar.Psi0Aux.dthUiterPWcoef_sum_le 6 (by norm_num))
        have hiter := Work.FTS.PhiStar.Psi0Aux.dthUiter_sin2_iter 6 (by norm_num) θ
        show |Work.Spaces.dthU^[6] (fun t : ℝ => Real.sin (2 * t)) θ| ≤ 1095801216
        rw [hiter, abs_mul]
        calc |Real.sin (2 * θ)|
              * |(Work.FTS.PhiStar.Psi0Aux.dthUiterPW 6).eval (Real.cos θ ^ 2)|
            ≤ 1 * 1095801216 :=
              mul_le_mul (Real.abs_sin_le_one _) hP (abs_nonneg _) (by norm_num)
          _ = 1095801216 := by norm_num
      have hB : |(5 / 4) * Work.FTS.PhiStar.Psi0Aux.Giter 6 θ| ≤ (5 / 4) * 1095801216 := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 4)]
        exact mul_le_mul_of_nonneg_left hG6 (by norm_num)
      calc |1 / Work.Spaces.c α * Work.FTS.PhiStar.Psi0Aux.dGam α 6 θ
              - 5 / 4 * Work.FTS.PhiStar.Psi0Aux.Giter 6 θ|
          = |1 / Work.Spaces.c α * Work.FTS.PhiStar.Psi0Aux.dGam α 6 θ
              + -(5 / 4 * Work.FTS.PhiStar.Psi0Aux.Giter 6 θ)| := by ring_nf
        _ ≤ |1 / Work.Spaces.c α * Work.FTS.PhiStar.Psi0Aux.dGam α 6 θ|
              + |-(5 / 4 * Work.FTS.PhiStar.Psi0Aux.Giter 6 θ)| := abs_add_le _ _
        _ = |1 / Work.Spaces.c α * Work.FTS.PhiStar.Psi0Aux.dGam α 6 θ|
              + |5 / 4 * Work.FTS.PhiStar.Psi0Aux.Giter 6 θ| := by rw [abs_neg]
        _ ≤ C6 := by rw [hC6def]; linarith [hA, hB]
    -- ## assembling the sequence
    let K : ℕ → ℝ := fun j => max (max (max KG C6) (cc j / 4 + dd j)) (B2 j)
    have hK0 : ∀ j, 0 ≤ K j := by
      intro j
      simp only [K]
      exact le_trans (le_trans (le_trans (le_of_lt hKGpos) (le_max_left _ _)) (le_max_left _ _))
        (le_max_left _ _)
    have hKGle : ∀ j, KG ≤ K j := by
      intro j; simp only [K]
      exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
    have hC6le : ∀ j, C6 ≤ K j := by
      intro j; simp only [K]
      exact le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
    have hccddle : ∀ j, cc j / 4 + dd j ≤ K j := by
      intro j; simp only [K]
      exact le_trans (le_max_right _ _) (le_max_left _ _)
    have hB2le : ∀ j, B2 j ≤ K j := by
      intro j; simp only [K]; exact le_max_right _ _
    refine ⟨K, hK0, ?_, ?_⟩
    · intro α hα hα1 j hj θ hθ
      by_cases h0 : j = 0
      · subst h0
        exact le_trans (hKG α hα hα1 θ hθ) (hKGle 0)
      · by_cases h6 : j = 6
        · subst h6
          exact le_trans (hstep6 α hα hα1 θ hθ) (hC6le 6)
        · have hj1 : 1 ≤ j := by omega
          have hj5 : j ≤ 5 := by omega
          exact le_trans (hstep j hj1 hj5 α hα hα1 θ hθ) (hccddle j)
    · intro j hj θ hθ
      exact le_trans (hB2 j θ hθ) (hB2le j)
  exact hmain

end Work.FTS.PhiStar
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.BmodeBase =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

local notation "Iθ" => Work.Spaces.Iθ
local notation "Idm" => Work.FTS.EllipticEst.Lzero1
local notation "eF" => Work.FTS.PhiStar.Gegenbauer.eFam
local notation "GB" => Work.FTS.VocabO.GamBar
local notation "λm" => Work.FTS.PhiStar.Gegenbauer.lam

theorem measurableSet_Iθ : MeasurableSet Iθ := measurableSet_Icc

theorem isFiniteMeasure_Iθ : IsFiniteMeasure (volume.restrict Iθ) := by
  rw [show Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl,
    MeasureTheory.isFiniteMeasure_restrict, Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

theorem integrableOn_Iθ_of_bound {f : ℝ → ℝ}
    (hm : AEStronglyMeasurable f (volume.restrict Iθ)) {C : ℝ}
    (hC : ∀ θ ∈ Iθ, |f θ| ≤ C) : IntegrableOn f Iθ := by
  haveI : IsFiniteMeasure (volume.restrict Iθ) := isFiniteMeasure_Iθ
  have hb : ∀ᵐ θ ∂(volume.restrict Iθ), ‖f θ‖ ≤ C := by
    rw [ae_restrict_iff' measurableSet_Iθ]
    exact Eventually.of_forall fun θ hθ => by rw [Real.norm_eq_abs]; exact hC θ hθ
  exact Integrable.of_bound hm C hb

theorem iota_eq (F : ℝ → ℝ) :
    (∫ θ in (0 : ℝ)..(Real.pi / 2), F θ) = ∫ θ in Iθ, F θ := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (f := F) (by positivity : (0 : ℝ) ≤ Real.pi / 2)]

theorem integral_nonneg_Iθ {g : ℝ → ℝ} (hg : ∀ θ, 0 ≤ g θ) : 0 ≤ ∫ θ in Iθ, g θ := by
  rw [← iota_eq]
  exact intervalIntegral.integral_nonneg_of_forall (by positivity) hg

theorem eF_zero (m : ℕ) : eF m 0 = 0 := by
  rw [Work.FTS.PhiStar.Gegenbauer.eFam]
  simp [Work.FTS.PhiStar.Gegenbauer.gC_odd_zero m]

theorem eF_pi (m : ℕ) : eF m (Real.pi / 2) = 0 := by
  rw [Work.FTS.PhiStar.Gegenbauer.eFam]
  simp

theorem contDiff_eF (m : ℕ) : ContDiff ℝ 2 (eF m) := by
  rw [show eF m = fun θ => Real.cos θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)
    from rfl]
  exact (Real.contDiff_cos.mul
    ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).comp Real.contDiff_sin)).of_le
      (by norm_num)

theorem Gam_abs_le_one {α : ℝ} (hα : 0 ≤ α) {θ : ℝ} (hθ : θ ∈ Iθ) :
    |Work.Spaces.Gam α θ| ≤ 1 := by
  show |(Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)| ≤ 1
  have hsin : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hb0 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := mul_nonneg hsin (sq_nonneg _)
  have hb1 : Real.sin θ * Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [hsin, Real.sin_le_one θ, sq_nonneg (Real.cos θ), Real.sin_sq_add_cos_sq θ]
  rw [abs_of_nonneg (Real.rpow_nonneg hb0 _)]
  exact Real.rpow_le_one hb0 hb1 (by positivity)

theorem GamBar_abs_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Iθ) :
    |GB α θ| ≤ 45 / 4 := by
  show |Work.Spaces.Gam α θ / Work.Spaces.c α - 5 / 4 * Real.sin (2 * θ)| ≤ 45 / 4
  have hGam : |Work.Spaces.Gam α θ| ≤ 1 := Gam_abs_le_one (by positivity) hθ
  have hca : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := lt_of_lt_of_le (by norm_num) hca
  have h1 : |Work.Spaces.Gam α θ / Work.Spaces.c α| ≤ 10 := by
    rw [abs_div, abs_of_pos hcpos, div_le_iff₀ hcpos]
    nlinarith [hGam, hca]
  have h2 : |(5 / 4) * Real.sin (2 * θ)| ≤ 5 / 4 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 4)]
    have := (abs_le.mpr (Real.sin_mem_Icc (2 * θ)) : |Real.sin (2 * θ)| ≤ 1)
    linarith
  calc |Work.Spaces.Gam α θ / Work.Spaces.c α - 5 / 4 * Real.sin (2 * θ)|
      ≤ |Work.Spaces.Gam α θ / Work.Spaces.c α| + |5 / 4 * Real.sin (2 * θ)| := abs_sub _ _
    _ ≤ 10 + 5 / 4 := add_le_add h1 h2
    _ = 45 / 4 := by norm_num

theorem Gam_zero {α : ℝ} (hα : 0 < α) : Work.Spaces.Gam α 0 = 0 := by
  show (Real.sin (0 : ℝ) * Real.cos (0 : ℝ) ^ 2) ^ (α / 3) = 0
  rw [show Real.sin (0 : ℝ) * Real.cos (0 : ℝ) ^ 2 = 0 from by simp,
    Real.zero_rpow (by positivity : α / 3 ≠ 0)]


theorem GamBar_zero {α : ℝ} (hα : 0 < α) : GB α 0 = 0 := by
  show Work.Spaces.Gam α 0 / Work.Spaces.c α - 5 / 4 * Real.sin (2 * 0) = 0
  rw [Gam_zero hα]
  simp


theorem continuousOn_GamBar (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ContinuousOn (fun θ => GB α θ) Iθ := by
  have hcne : Work.Spaces.c α ≠ 0 := by
    have := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  show ContinuousOn (fun θ => Work.Spaces.Gam α θ / Work.Spaces.c α
    - 5 / 4 * Real.sin (2 * θ)) Iθ
  refine ContinuousOn.sub ?_ ?_
  · refine ContinuousOn.div ?_ continuousOn_const (fun θ _ => hcne)
    · show ContinuousOn (fun θ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)) Iθ
      exact ((Real.continuous_rpow_const (by positivity : (0 : ℝ) ≤ α / 3)).comp
        (Real.continuous_sin.mul (Real.continuous_cos.pow 2))).continuousOn
  · exact (continuous_const.mul (Real.continuous_sin.comp
      (continuous_const.mul continuous_id))).continuousOn

theorem sq_integral_mul_le (f g : ℝ → ℝ)
    (hf : IntegrableOn (fun θ => f θ ^ 2) Iθ)
    (hfg : IntegrableOn (fun θ => f θ * g θ) Iθ)
    (hg : IntegrableOn (fun θ => g θ ^ 2) Iθ) :
    (∫ θ in Iθ, f θ * g θ) ^ 2 ≤ (∫ θ in Iθ, f θ ^ 2) * (∫ θ in Iθ, g θ ^ 2) := by
  set A : ℝ := ∫ θ in Iθ, f θ ^ 2 with hA
  set B : ℝ := ∫ θ in Iθ, f θ * g θ with hB
  set C : ℝ := ∫ θ in Iθ, g θ ^ 2 with hC
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact integral_nonneg_Iθ (fun θ => sq_nonneg (f θ))
  have hC0 : 0 ≤ C := by
    rw [hC]
    exact integral_nonneg_Iθ (fun θ => sq_nonneg (g θ))
  have hquad : ∀ t : ℝ, 0 ≤ A - 2 * t * B + t ^ 2 * C := by
    intro t
    have hsub : IntegrableOn (fun θ => f θ ^ 2 - 2 * t * (f θ * g θ)) Iθ :=
      hf.sub (hfg.const_mul (2 * t))
    have hfull : IntegrableOn
        (fun θ => f θ ^ 2 - 2 * t * (f θ * g θ) + t ^ 2 * g θ ^ 2) Iθ :=
      hsub.add (hg.const_mul (t ^ 2))
    have hcongr : (∫ θ in Iθ, (f θ - t * g θ) ^ 2)
        = ∫ θ in Iθ, (f θ ^ 2 - 2 * t * (f θ * g θ) + t ^ 2 * g θ ^ 2) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Iθ (fun θ _ => ?_)
      ring
    have hval : (∫ θ in Iθ, (f θ ^ 2 - 2 * t * (f θ * g θ) + t ^ 2 * g θ ^ 2))
        = A - 2 * t * B + t ^ 2 * C := by
      have e1 : (∫ θ in Iθ, (f θ ^ 2 - 2 * t * (f θ * g θ) + t ^ 2 * g θ ^ 2))
          = (∫ θ in Iθ, (f θ ^ 2 - 2 * t * (f θ * g θ))) + (∫ θ in Iθ, t ^ 2 * g θ ^ 2) :=
        integral_add hsub (hg.const_mul (t ^ 2))
      have e2 : (∫ θ in Iθ, (f θ ^ 2 - 2 * t * (f θ * g θ)))
          = (∫ θ in Iθ, f θ ^ 2) - (∫ θ in Iθ, 2 * t * (f θ * g θ)) :=
        integral_sub hf (hfg.const_mul (2 * t))
      have e3 : (∫ θ in Iθ, 2 * t * (f θ * g θ)) = 2 * t * (∫ θ in Iθ, f θ * g θ) :=
        integral_const_mul (2 * t) (fun θ => f θ * g θ)
      have e4 : (∫ θ in Iθ, t ^ 2 * g θ ^ 2) = t ^ 2 * (∫ θ in Iθ, g θ ^ 2) :=
        integral_const_mul (t ^ 2) (fun θ => g θ ^ 2)
      rw [e1, e2, e3, e4, ← hA, ← hB, ← hC]
    have hnonneg : (∫ θ in Iθ, (f θ - t * g θ) ^ 2) = A - 2 * t * B + t ^ 2 * C :=
      hcongr.trans hval
    rw [← hnonneg]
    exact integral_nonneg_Iθ (fun θ => by
      have h : (f θ - t * g θ) ^ 2 = f θ ^ 2 - 2 * t * (f θ * g θ) + t ^ 2 * g θ ^ 2 := by ring
      rw [h]; nlinarith [sq_nonneg (f θ - t * g θ)])
  rcases eq_or_lt_of_le hC0 with h | h
  · have hB0 : B = 0 := by
      by_contra hBne
      have hmul : (A + 1) / B * B = A + 1 := div_mul_cancel₀ _ hBne
      have h2 : 2 * ((A + 1) / B) * B = 2 * (A + 1) := by
        rw [show 2 * ((A + 1) / B) * B = 2 * (((A + 1) / B) * B) from by ring, hmul]
      have ht := hquad ((A + 1) / B)
      rw [← h] at ht
      rw [h2] at ht
      simp only [mul_zero, add_zero] at ht
      nlinarith [ht, hA0]
    rw [hB0, ← h]
    norm_num
  · have hCpos : 0 < C := h
    have hx : 2 * (B / C) * B = 2 * (B ^ 2 / C) := by
      rw [show 2 * (B / C) * B = 2 * ((B / C) * B) from by ring]
      congr 1
      field_simp
    have hy : (B / C) ^ 2 * C = B ^ 2 / C := by
      field_simp
    have ht := hquad (B / C)
    rw [hx, hy] at ht
    have ht' : B ^ 2 / C ≤ A := by linarith [ht]
    rw [div_le_iff₀ hCpos] at ht'
    exact ht'

theorem deriv_eq_zero_of_eventuallyEq_zero {v : ℝ → ℝ} {θ : ℝ}
    (h : v =ᶠ[𝓝 θ] (fun _ : ℝ => 0)) : deriv v θ = 0 := by
  have hh : deriv (fun _ : ℝ => (0 : ℝ)) θ = deriv v θ := Filter.EventuallyEq.deriv_eq h.symm
  rw [deriv_const] at hh
  exact hh.symm

theorem Lzero1_eq_zero_of_eventuallyEq_zero {v : ℝ → ℝ} {θ : ℝ}
    (h : v =ᶠ[𝓝 θ] (fun _ : ℝ => 0)) : Idm v θ = 0 := by
  obtain ⟨U, hUsub, hUopen, hθU⟩ := mem_nhds_iff.mp h
  have hU : U ∈ 𝓝 θ := hUopen.mem_nhds hθU
  have hvθ : v θ = 0 := h.self_of_nhds
  have hdv : deriv v =ᶠ[𝓝 θ] (fun _ : ℝ => 0) := by
    filter_upwards [hU] with t ht
    exact deriv_eq_zero_of_eventuallyEq_zero
      (by filter_upwards [hUopen.mem_nhds ht] with s hs; exact hUsub hs)
  have hd2 : deriv (fun t => deriv v t) θ = 0 := by
    have hh : deriv (fun t => deriv v t) θ = deriv (fun _ : ℝ => (0 : ℝ)) θ :=
      Filter.EventuallyEq.deriv_eq hdv
    rw [deriv_const] at hh
    exact hh
  have hd3 : deriv (fun t => Real.tan t * v t) θ = 0 :=
    deriv_eq_zero_of_eventuallyEq_zero (by
      filter_upwards [hU] with t ht
      have h1 : v t = 0 := hUsub ht
      simp [h1])
  simp only [Work.FTS.EllipticEst.Lzero1]
  rw [hd2, hd3, hvθ]
  ring

theorem lzero1_mul_eq {χ e : ℝ → ℝ} (hχ : ContDiff ℝ 2 χ) (he : ContDiff ℝ 2 e)
    {θ : ℝ} (hcos : Real.cos θ ≠ 0) :
    Idm (fun t => χ t * e t) θ
      = χ θ * Idm e θ
        + (-(deriv (deriv χ) θ * e θ) - 2 * (deriv χ θ * deriv e θ)
            + Real.tan θ * deriv χ θ * e θ) := by
  have hdχ : ∀ t, HasDerivAt χ (deriv χ t) t := fun t =>
    ((hχ.contDiffAt (x := t)).differentiableAt (by norm_num)).hasDerivAt
  have hde : ∀ t, HasDerivAt e (deriv e t) t := fun t =>
    ((he.contDiffAt (x := t)).differentiableAt (by norm_num)).hasDerivAt
  have hdχ' : ∀ t, HasDerivAt (deriv χ) (deriv (deriv χ) t) t := fun t =>
    (((hχ.contDiffAt (x := t)).derivWithin (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasDerivAt
  have hde' : ∀ t, HasDerivAt (deriv e) (deriv (deriv e) t) t := fun t =>
    (((he.contDiffAt (x := t)).derivWithin (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasDerivAt
  have hχe : deriv (fun t => χ t * e t) = fun t => χ t * deriv e t + deriv χ t * e t := by
    funext t
    have h : deriv (fun s => χ s * e s) t = deriv χ t * e t + χ t * deriv e t :=
      ((hdχ t).mul (hde t)).deriv
    rw [h]; ring
  have hA : deriv (fun t => deriv (fun s => χ s * e s) t) θ
      = deriv (deriv χ) θ * e θ + 2 * (deriv χ θ * deriv e θ) + χ θ * deriv (deriv e) θ := by
    rw [hχe]
    have h1 : HasDerivAt (fun t => χ t * deriv e t)
        (deriv χ θ * deriv e θ + χ θ * deriv (deriv e) θ) θ := (hdχ θ).mul (hde' θ)
    have h2 : HasDerivAt (fun t => deriv χ t * e t)
        (deriv (deriv χ) θ * e θ + deriv χ θ * deriv e θ) θ := (hdχ' θ).mul (hde θ)
    have hfun : (fun t => χ t * deriv e t + deriv χ t * e t)
        = (fun t => χ t * deriv e t) + (fun t => deriv χ t * e t) := by
      funext t
      simp
    rw [hfun]
    have h := (h1.add h2).deriv
    rw [h]
    ring
  have hB : deriv (fun t => Real.tan t * (χ t * e t)) θ
      = 1 / Real.cos θ ^ 2 * (χ θ * e θ)
        + Real.tan θ * (χ θ * deriv e θ + deriv χ θ * e θ) := by
    have h : deriv (fun t => Real.tan t * (χ t * e t)) θ
        = 1 / Real.cos θ ^ 2 * (χ θ * e θ)
          + Real.tan θ * (deriv χ θ * e θ + χ θ * deriv e θ) :=
      ((Real.hasDerivAt_tan hcos).mul ((hdχ θ).mul (hde θ))).deriv
    rw [h]; ring
  have hC : deriv (fun t => Real.tan t * e t) θ
      = 1 / Real.cos θ ^ 2 * e θ + Real.tan θ * deriv e θ := by
    have h : deriv (fun t => Real.tan t * e t) θ
        = 1 / Real.cos θ ^ 2 * e θ + Real.tan θ * deriv e θ :=
      ((Real.hasDerivAt_tan hcos).mul (hde θ)).deriv
    exact h
  have hD : deriv (fun t => deriv e t) θ = deriv (deriv e) θ := rfl
  simp only [Work.FTS.EllipticEst.Lzero1]
  rw [hA, hB, hC, hD]
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  ring

theorem ibp_Iθ {u v : ℝ → ℝ} {c d : ℝ} (hc : 0 < c) (hcd : c < d) (hd : d < Real.pi / 2)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hv : ContDiffOn ℝ 2 v (Set.Ioo 0 (Real.pi / 2)))
    (hv0 : ∀ θ, θ ∉ Set.Icc c d → v θ = 0) :
    ∫ θ in Iθ, (u θ * Idm v θ - Idm u θ * v θ) * Real.cos θ = 0 := by
  have h := Work.EllipticEst.ModalSolution.angular_ibp_zero hc hcd hd hu hv hv0
  have hsub : Set.Icc c d ⊆ Iθ := fun θ hθ =>
    ⟨le_of_lt (lt_of_lt_of_le hc hθ.1), le_of_lt (lt_of_le_of_lt hθ.2 hd)⟩
  have hstep : (∫ θ in Iθ, (u θ * Idm v θ - Idm u θ * v θ) * Real.cos θ)
      = ∫ θ in Set.Icc c d, (u θ * Idm v θ - Idm u θ * v θ) * Real.cos θ := by
    refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      measurableSet_Iθ hsub (fun θ hθ => ?_)
    have hvz : v θ = 0 := hv0 θ hθ.2
    have hLz : Idm v θ = 0 := by
      rcases lt_or_ge θ c with hlt | hge
      · refine Lzero1_eq_zero_of_eventuallyEq_zero ?_
        filter_upwards [isOpen_Iio.mem_nhds hlt] with t ht
        exact hv0 t (fun hmem => absurd hmem.1 (not_le.mpr ht))
      · have hgt : d < θ := by
          by_contra hcon
          exact hθ.2 ⟨hge, le_of_not_gt hcon⟩
        refine Lzero1_eq_zero_of_eventuallyEq_zero ?_
        filter_upwards [isOpen_Ioi.mem_nhds hgt] with t ht
        exact hv0 t (fun hmem => absurd hmem.2 (not_le.mpr ht))
    rw [hvz, hLz]
    ring
  rw [hstep]
  exact h

theorem tan_mul_cos_eq (a θ : ℝ) (h : Real.cos θ ≠ 0) :
    Real.tan θ * a * Real.cos θ = Real.sin θ * a := by
  rw [Real.tan_eq_sin_div_cos]
  field_simp

theorem abs_tan_mul_cos_le (a θ : ℝ) : |Real.tan θ * a * Real.cos θ| ≤ |a| := by
  rcases eq_or_ne (Real.cos θ) 0 with h | h
  · rw [h, mul_zero, abs_zero]
    exact abs_nonneg a
  · rw [tan_mul_cos_eq a θ h, abs_mul]
    have h1 : |Real.sin θ| ≤ 1 := abs_le.mpr (Real.sin_mem_Icc θ)
    calc |Real.sin θ| * |a| ≤ 1 * |a| := mul_le_mul_of_nonneg_right h1 (abs_nonneg a)
      _ = |a| := one_mul _

end Work.FTS.PhiStar.Series
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Deleg.hasDerivAtPhiAseries =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series.Deleg

/-- The `n`-th summand of `phiAseries α k`, differentiated: the derivative is the `n`-th summand
of `phiAseries α (k+1)`.  The point is that
`(d/dz) (1+z)^{m} = m (1+z)^{m-1}` and `∏_{i<k+1}(m-i) = (∏_{i<k}(m-i)) · (m-k)`. -/
private lemma hasDerivAt_phiAterm (α : ℝ) (k n : ℕ) {z : ℝ} (hz : z ≠ -1) :
    HasDerivAt (fun w : ℝ => phiAcoef α n * (∏ i ∈ Finset.range k, ((-(n : ℝ) - 1) - i))
        * (1 + w) ^ (-(n : ℤ) - 1 - (k : ℤ)))
      (phiAcoef α n * (∏ i ∈ Finset.range (k + 1), ((-(n : ℝ) - 1) - i))
        * (1 + z) ^ (-(n : ℤ) - 1 - (((k + 1 : ℕ)) : ℤ))) z := by
  have h1z : (1 : ℝ) + z ≠ 0 := by
    intro h
    exact hz (by linarith)
  -- the pure power `(1+w)^m`, `m = -n-1-k`
  have hb : HasDerivAt (fun w : ℝ => ((1 : ℝ) + w) ^ (-(n : ℤ) - 1 - (k : ℤ)))
      (((-(n : ℤ) - 1 - (k : ℤ) : ℤ) : ℝ) * (1 + z) ^ ((-(n : ℤ) - 1 - (k : ℤ)) - 1)) z := by
    have h := (hasDerivAt_zpow (-(n : ℤ) - 1 - (k : ℤ)) ((1 : ℝ) + z) (Or.inl h1z)).comp z
      ((hasDerivAt_id z).const_add 1)
    simpa [Function.comp_def] using h
  have hprod :=
    HasDerivAt.const_mul (phiAcoef α n * (∏ i ∈ Finset.range k, ((-(n : ℝ) - 1) - i))) hb
  refine hprod.congr_deriv ?_
  rw [show (-(n : ℤ) - 1 - (((k + 1 : ℕ)) : ℤ)) = (-(n : ℤ) - 1 - (k : ℤ)) - 1 from by
        push_cast; ring,
      Finset.prod_range_succ]
  have hcast : ((-(n : ℤ) - 1 - (k : ℤ) : ℤ) : ℝ) = (-(n : ℝ) - 1) - (k : ℝ) := by
    push_cast; ring
  rw [hcast]
  ring

theorem hasDerivAtPhiAseries (α : ℝ) (k : ℕ) {z : ℝ} (hz : z ≠ -1) :
    HasDerivAt (Work.FTS.PhiStar.Series.Deleg.phiAseries α k)
      (Work.FTS.PhiStar.Series.Deleg.phiAseries α (k + 1) z) z := by
  change HasDerivAt (fun w : ℝ => ∑ n ∈ Finset.range 4,
      phiAcoef α n * (∏ i ∈ Finset.range k, ((-(n : ℝ) - 1) - i))
        * (1 + w) ^ (-(n : ℤ) - 1 - (k : ℤ)))
    (∑ n ∈ Finset.range 4,
      phiAcoef α n * (∏ i ∈ Finset.range (k + 1), ((-(n : ℝ) - 1) - i))
        * (1 + z) ^ (-(n : ℤ) - 1 - (((k + 1 : ℕ)) : ℤ))) z
  exact HasDerivAt.fun_sum (u := Finset.range 4) (fun n _ => hasDerivAt_phiAterm α k n hz)

end Work.FTS.PhiStar.Series.Deleg
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Deleg.phiAtermBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series.Deleg

theorem phiAtermBound (α : ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5) (n k : ℕ) (hn : n < 4) (hk : k ≤ 22)
    {z : ℝ} (hz : 0 < z) :
    |Work.FTS.PhiStar.Series.Deleg.phiAcoef α n
        * (∏ i ∈ Finset.range k, ((-(n : ℝ) - 1) - i))
        * (1 + z) ^ (-(n : ℤ) - 1 - (k : ℤ))| ≤ 30 * 26 ^ 22 := by
  -- `|phiAcoef α n| ≤ 30` for `n < 4`, `0 < α ≤ 1/5`
  have hcoef : |phiAcoef α n| ≤ 30 := by
    interval_cases n <;> simp only [phiAcoef] <;>
      rw [abs_le] <;> constructor <;> linarith
  -- the falling-factorial product is bounded by `26^22`
  have hprod : |∏ i ∈ Finset.range k, ((-(n : ℝ) - 1) - i)| ≤ 26 ^ 22 := by
    rw [Finset.abs_prod]
    have hle : ∀ i ∈ Finset.range k, |(-(n : ℝ) - 1) - i| ≤ (26 : ℝ) := by
      intro i hi
      have hi' : i < k := Finset.mem_range.mp hi
      have hn3 : (n : ℝ) ≤ 3 := by
        have : n ≤ 3 := by omega
        exact_mod_cast this
      have hi21 : (i : ℝ) ≤ 21 := by
        have : i ≤ 21 := by omega
        exact_mod_cast this
      rw [abs_le]
      constructor <;> linarith
    calc ∏ i ∈ Finset.range k, |(-(n : ℝ) - 1) - i|
        ≤ ∏ _i ∈ Finset.range k, (26 : ℝ) :=
          Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) hle
      _ = (26 : ℝ) ^ k := by rw [Finset.prod_const, Finset.card_range]
      _ ≤ (26 : ℝ) ^ 22 := pow_le_pow_right₀ (by norm_num) hk
  -- `1 + z > 1` and the exponent is a nonpositive integer, so the power is `≤ 1`
  have hpow : |(1 + z) ^ (-(n : ℤ) - 1 - (k : ℤ))| ≤ 1 := by
    have hbase : (1 : ℝ) < 1 + z := by linarith
    have hbase' : (0 : ℝ) ≤ 1 + z := by linarith
    have hexp : (-(n : ℤ) - 1 - (k : ℤ)) ≤ 0 := by omega
    rw [abs_of_nonneg (zpow_nonneg hbase' _)]
    exact (zpow_le_one_iff_right₀ hbase).mpr hexp
  calc
    |phiAcoef α n
        * (∏ i ∈ Finset.range k, ((-(n : ℝ) - 1) - i))
        * (1 + z) ^ (-(n : ℤ) - 1 - (k : ℤ))|
        = |phiAcoef α n|
            * |∏ i ∈ Finset.range k, ((-(n : ℝ) - 1) - i)|
            * |(1 + z) ^ (-(n : ℤ) - 1 - (k : ℤ))| := by rw [abs_mul, abs_mul]
    _ ≤ 30 * 26 ^ 22 * 1 := by
        have h1 : |phiAcoef α n|
              * |∏ i ∈ Finset.range k, ((-(n : ℝ) - 1) - i)| ≤ 30 * 26 ^ 22 :=
          mul_le_mul hcoef hprod (abs_nonneg _) (by norm_num)
        exact mul_le_mul h1 hpow (abs_nonneg _) (by positivity)
    _ = 30 * 26 ^ 22 := by ring

end Work.FTS.PhiStar.Series.Deleg
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Weil.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series.Weil

set_option autoImplicit false

/-- The mode series of the remainder source: the function whose `C^∞`-regularity on `Q0` is
conjunct 1 of `psiSeries_solves_rem`. -/
abbrev R (α : ℝ) (ψ : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.FTS.PhiStar.Series.psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z θ

/-- The `m`-th mode term of `R α ψ`. -/
abbrev trm (α : ℝ) (ψ : ℝ → ℝ) (m : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.FTS.PhiStar.Series.acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z
    * Work.FTS.PhiStar.Gegenbauer.eFam m θ

/-- The weight of the weak formulation of `bslOp α` on the quadrant,
`z^{(5-α)/α}·cos θ` (the weight that puts `bslOp α` into divergence form). -/
def wgt (α : ℝ) (p : ℝ × ℝ) : ℝ := p.1 ^ ((5 - α) / α) * Real.cos p.2

/-- The truncated source: the `N`-th partial sum of `Σ_m cmode m (RemSource α ψ) · e_m`. -/
abbrev csrc (α : ℝ) (ψ : ℝ → ℝ) (N : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => ∑ m ∈ Finset.range (N + 1),
    Work.FTS.PhiStar.Series.cmode m (Work.FTS.PhiStar.RemSource α ψ) z
      * Work.FTS.PhiStar.Gegenbauer.eFam m θ

/-- A closed box `[a,b] × [c,d]` of the quadrant. -/
def box (a b c d : ℝ) : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc c d

@[simp] theorem R_apply (α : ℝ) (ψ : ℝ → ℝ) (z θ : ℝ) :
    R α ψ z θ = Work.FTS.PhiStar.Series.psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z θ := rfl

@[simp] theorem trm_apply (α : ℝ) (ψ : ℝ → ℝ) (m : ℕ) (z θ : ℝ) :
    trm α ψ m z θ = Work.FTS.PhiStar.Series.acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z
      * Work.FTS.PhiStar.Gegenbauer.eFam m θ := rfl

@[simp] theorem wgt_apply (α : ℝ) (p : ℝ × ℝ) :
    wgt α p = p.1 ^ ((5 - α) / α) * Real.cos p.2 := rfl

@[simp] theorem csrc_apply (α : ℝ) (ψ : ℝ → ℝ) (N : ℕ) (z θ : ℝ) :
    csrc α ψ N z θ = ∑ m ∈ Finset.range (N + 1),
      Work.FTS.PhiStar.Series.cmode m (Work.FTS.PhiStar.RemSource α ψ) z
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ := rfl

theorem mem_box {a b c d : ℝ} {p : ℝ × ℝ} :
    p ∈ box a b c d ↔ p.1 ∈ Set.Icc a b ∧ p.2 ∈ Set.Icc c d := Iff.rfl

/-- A box with `0 < a`, `a ≤ b`, `0 < c`, `c ≤ d < π/2` lies in the open quadrant. -/
theorem box_subset_Q0 {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d)
    (hd : d < π / 2) : box a b c d ⊆ Work.FTS.EllipticEst.Q0 := by
  intro p hp
  obtain ⟨h1, h2⟩ := mem_box.mp hp
  exact Work.FTS.EllipticEst.mem_Q0.mpr ⟨lt_of_lt_of_le ha h1.1, lt_of_lt_of_le hc h2.1,
    lt_of_le_of_lt h2.2 hd⟩


end Work.FTS.PhiStar.Series.Weil
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.Dth_Lhat_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.LhatCalc

set_option autoImplicit false
set_option maxHeartbeats 800000

open DthAux

/-- **`D_θ` commutes exactly with `𝓛̂ = 𝓛 − Transport` on the open class**:
`D_θ(𝓛̂ f) = 𝓛̂(D_θ f)` for every `C^∞` datum on the open quadrant and every interior point
`z > 0`, `0 < θ < π/2`. -/
theorem Dth_Lhat_open {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f) z θ := by
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩
  have hcd : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f)
      Work.FTS.EllipticEst.Q0 := hf
  have hcf : ContDiffAt ℝ Work.Stability.smoothOrder (Function.uncurry f) (z, θ) :=
    hcd.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
  have hfθ : DifferentiableAt ℝ (fun θ' => f z θ') θ :=
    Work.Spaces.differentiableAt_curry_right (hcf.differentiableAt smoothOrder_ne_zero)
  have hpz_sm : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pz f)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_uncurry_pz_sm Work.FTS.EllipticEst.isOpen_Q0 hcd
  have hpzθ : DifferentiableAt ℝ (fun θ' => Work.Spaces.pz f z θ') θ :=
    Work.Spaces.differentiableAt_curry_right
      ((hpz_sm.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)).differentiableAt
        smoothOrder_ne_zero)
  have hpth_sm : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pth f)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_uncurry_pth_sm Work.FTS.EllipticEst.isOpen_Q0 hcd
  have hpthθ : DifferentiableAt ℝ (fun θ' => Work.Spaces.pth f z θ') θ :=
    Work.Spaces.differentiableAt_curry_right
      ((hpth_sm.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)).differentiableAt
        smoothOrder_ne_zero)
  have dL : DifferentiableAt ℝ (fun θ' => Work.Coercivity.L f z θ') θ := by
    rw [show (fun θ' => Work.Coercivity.L f z θ')
        = (fun θ' => f z θ' + z * Work.Spaces.pz f z θ' - (2 / (1 + z)) * f z θ') from by
      funext θ'; simp only [Work.Coercivity.L, Work.Spaces.Dz]; ring]
    exact (hfθ.add (hpzθ.const_mul z)).sub (hfθ.const_mul (2 / (1 + z)))
  have hDθ : DifferentiableAt ℝ (fun θ' => Work.Spaces.Dth f z θ') θ := by
    rw [show (fun θ' => Work.Spaces.Dth f z θ')
        = (fun θ' => Real.sin (2 * θ') * Work.Spaces.pth f z θ') from by
      funext θ'; simp only [Work.Spaces.Dth]]
    exact ((hasDerivAt_sin_two θ).differentiableAt).mul hpthθ
  have dTr : DifferentiableAt ℝ (fun θ' => Work.Coercivity.Transport f z θ') θ := by
    rw [show (fun θ' => Work.Coercivity.Transport f z θ')
        = (fun θ' => (3 / (1 + z)) * Work.Spaces.Dth f z θ') from by
      funext θ'; simp only [Work.Coercivity.Transport]; ring]
    exact hDθ.const_mul (3 / (1 + z))
  have hpth : Work.Spaces.pth (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.Spaces.pth (Work.Coercivity.L f) z θ
        - Work.Spaces.pth (Work.Coercivity.Transport f) z θ := by
    show deriv (fun θ' => Work.FTS.CoercivityFix.Lhat f z θ') θ = _
    rw [show (fun θ' => Work.FTS.CoercivityFix.Lhat f z θ')
        = ((fun θ' => Work.Coercivity.L f z θ')
            - fun θ' => Work.Coercivity.Transport f z θ') from by
      funext θ'; simp only [Work.FTS.CoercivityFix.Lhat, Pi.sub_apply]]
    rw [deriv_sub dL dTr]
    rfl
  rw [show Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.FTS.CoercivityFix.Lhat f) z θ from rfl]
  rw [hpth]
  rw [Work.FTS.CoercivityFix.Lhat_eq (Work.Spaces.Dth f) z θ]
  rw [pth_L_of_smooth Work.FTS.EllipticEst.isOpen_Q0 hcd hmem,
    Work.Coercivity.pth_Transport]
  rw [show Work.Spaces.Dz (Work.Spaces.Dth f) z θ
      = z * Work.Spaces.pz (Work.Spaces.Dth f) z θ from rfl]
  rw [Work.Coercivity.pz_Dth_val]
  rw [show Work.Spaces.Dth (Work.Spaces.Dth f) z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.Dth f) z θ from rfl]
  rw [show Work.Spaces.Dth f z θ = Real.sin (2 * θ) * Work.Spaces.pth f z θ from rfl]
  rw [pth_Dth_eq (g := f) hpthθ]
  ring

end Work.FTS.CoercivityFix.LhatCalc
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsWp.FK_fstar_add_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular moment of `F_* + f` is bounded by `B + 1` when `FK f` is bounded by `B`

`FK F z = ∫_θ F(z,θ)·K(θ) dθ` is the angular moment `(F,K)_{L²_θ}(z)` of the paper
(`Work.Construction.FK`).  Here we show that adding the fundamental profile `F_*` to a
perturbation `f` whose angular moment is bounded by `B` only increases the bound by the
(explicit) constant `sup_z |FK F_* z| ≤ 1`.

The mathematics is the linearity of `FK` in its argument together with the computation
`FK F_* = α·2z/(1+z)²` (`Work.FTS.Nonlinear.FstarPkg.FK_Fstar`):

* on `Iθ = [0,π/2]`, `(F_* + f)·K = F_*·K + f·K` pointwise, so the integrand splits;
* the profile part `F_*·K = (α·F_*(z)/c(α))·(Γ·K)` is a constant multiple of the continuous
  function `Γ·K`, hence integrable on the compact `Iθ`;
* if the sum of the two integrands is integrable, `MeasureTheory.integral_add` splits the
  integral and the triangle inequality plus `FK_Fstar` bound the profile contribution by
  `1` and the `f`-contribution by `B`;
* if it is not integrable, the Bochner integral is `0` (`MeasureTheory.integral_undef`) and
  the claim reduces to `0 ≤ B + 1`.

The bound on the profile is sharp: `|α·2z/(1+z)²| ≤ 1` for `0 < α ≤ 1` and `z ≥ 0`, since
`0 ≤ 2z/(1+z)² ≤ 1` (`2z ≤ (1+z)² = 1 + 2z + z²`).
-/

namespace Work.FTS.StrongEps.EpsWp

open MeasureTheory

theorem FK_fstar_add_bound {α : ℝ} {f : ℝ → ℝ → ℝ} {B : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hB : 0 ≤ B)
    (hfk : ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Construction.FK f z| ≤ B) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Construction.FK (fun z θ => Work.Construction.Fstar α z θ + f z θ) z| ≤ B + 1 := by
  intro z hz
  have hz0 : 0 ≤ z := le_of_lt hz
  -- the profile part and the perturbation part of the integrand of `FK (F_* + f) z`
  set a : ℝ → ℝ := fun θ => Work.Construction.Fstar α z θ * Work.Spaces.K θ with ha
  set cl : ℝ → ℝ := fun θ => f z θ * Work.Spaces.K θ with hcl
  -- `Γ·K` is continuous on the compact `Iθ`, hence integrable
  have hGamK : IntegrableOn (fun θ : ℝ => Work.Spaces.Gam α θ * Work.Spaces.K θ)
      Work.Spaces.Iθ := by
    have hbase : ContinuousOn (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) Work.Spaces.Iθ :=
      (Real.continuous_sin.continuousOn).mul ((Real.continuous_cos.continuousOn).pow 2)
    have hGam : ContinuousOn (fun θ : ℝ => Work.Spaces.Gam α θ) Work.Spaces.Iθ := by
      show ContinuousOn (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)) Work.Spaces.Iθ
      exact hbase.rpow_const (fun θ _ => Or.inr (div_nonneg hα.le (by norm_num)))
    have hK : ContinuousOn (fun θ : ℝ => Work.Spaces.K θ) Work.Spaces.Iθ := by
      show ContinuousOn (fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2) Work.Spaces.Iθ
      fun_prop
    exact (hGam.mul hK).integrableOn_Icc
  -- hence so is the profile part `F_*·K`, a constant multiple of `Γ·K`
  have ha_eq : a = fun θ => (α * Work.FM.Fstar z / Work.Spaces.c α)
      * (Work.Spaces.Gam α θ * Work.Spaces.K θ) := by
    funext θ
    simp only [ha, Work.Construction.Fstar]
    ring
  have hAint : Integrable a (volume.restrict Work.Spaces.Iθ) := by
    rw [ha_eq]
    exact hGamK.const_mul _
  -- the integrand of `FK (F_* + f) z` is `a + cl` on `Iθ`
  have hgoal : Work.Construction.FK (fun z θ => Work.Construction.Fstar α z θ + f z θ) z
      = ∫ θ in Work.Spaces.Iθ, (a θ + cl θ) := by
    rw [Work.Construction.FK]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    simp only [ha, hcl]
    ring
  rw [hgoal]
  by_cases hint : Integrable (fun θ => a θ + cl θ) (volume.restrict Work.Spaces.Iθ)
  · -- integrable case: split the integral, bound the two pieces separately
    have hclInt : Integrable cl (volume.restrict Work.Spaces.Iθ) := by
      refine (hint.sub hAint).congr ?_
      filter_upwards with θ
      simp only [Pi.sub_apply]
      ring
    rw [MeasureTheory.integral_add hAint hclInt]
    have hAval : ∫ θ in Work.Spaces.Iθ, a θ = α * (2 * z / (1 + z) ^ 2) := by
      rw [ha]
      exact Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα hα1
    have hCval : ∫ θ in Work.Spaces.Iθ, cl θ = Work.Construction.FK f z := by
      rw [hcl]
      rfl
    rw [hAval, hCval]
    -- `|α·2z/(1+z)²| ≤ 1`
    have hden : 0 < (1 + z) ^ 2 := pow_pos (by linarith [hz0]) 2
    have ht0 : 0 ≤ 2 * z / (1 + z) ^ 2 := div_nonneg (by linarith [hz0]) hden.le
    have ht1 : 2 * z / (1 + z) ^ 2 ≤ 1 := by
      rw [div_le_one hden]
      nlinarith [sq_nonneg z]
    have hboundα : |α * (2 * z / (1 + z) ^ 2)| ≤ 1 := by
      rw [abs_of_nonneg (mul_nonneg hα.le ht0)]
      simpa using mul_le_mul hα1 ht1 ht0 zero_le_one
    calc |α * (2 * z / (1 + z) ^ 2) + Work.Construction.FK f z|
        ≤ |α * (2 * z / (1 + z) ^ 2)| + |Work.Construction.FK f z| := abs_add_le _ _
      _ ≤ 1 + B := add_le_add hboundα (hfk z hz)
      _ = B + 1 := by ring
  · -- non-integrable case: the Bochner integral is `0`
    rw [MeasureTheory.integral_undef hint]
    simp only [abs_zero]
    linarith

end Work.FTS.StrongEps.EpsWp
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsZero.L12_Dz_zero_of_slices =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongEps.EpsZero

theorem L12_Dz_zero_of_slices {f : ℝ → ℝ → ℝ}
    (hdiff : ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun s => f s θ) (Work.Spaces.pz f z θ) z)
    (hcont0 : ∀ θ ∈ Work.Spaces.Iθ, ContinuousOn (fun s => f s θ) (Set.Ici 0))
    (hdec : ∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun s => f s θ) Filter.atTop (nhds 0))
    (hvan : ∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0)
    (hint : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)) :
    Work.Construction.L12 (Work.Spaces.Dz f) 0 = 0 := by
  -- The angular density of `D_z f` is the `K`-average of `∂_z f`, for `s ≠ 0`.
  have hdens : ∀ s ∈ Set.Ioi (0 : ℝ),
      Work.Construction.L12dens (Work.Spaces.Dz f) s
        = ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz f s θ := by
    intro s hs
    have hsne : s ≠ 0 := ne_of_gt hs
    have hpt : ∀ θ : ℝ, Work.Spaces.K θ * Work.Spaces.Dz f s θ / s
        = Work.Spaces.K θ * Work.Spaces.pz f s θ := by
      intro θ
      simp only [Work.Spaces.Dz]
      rw [mul_div_assoc, mul_div_cancel_left₀ _ hsne]
    simp only [Work.Construction.L12dens, Work.FM.L12dens]
    exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => hpt θ)
  -- `L₁₂(D_z f)(0)` as the iterated integral `∫_s ∫_θ K(θ) ∂_z f(s,θ)`.
  have hstep : Work.Construction.L12 (Work.Spaces.Dz f) 0
      = ∫ s in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.K θ * Work.Spaces.pz f s θ := by
    rw [show Work.Construction.L12 (Work.Spaces.Dz f) 0
        = ∫ s in Set.Ioi (0 : ℝ), Work.Construction.L12dens (Work.Spaces.Dz f) s from rfl]
    exact setIntegral_congr_fun measurableSet_Ioi hdens
  have hsIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  -- Fubini: swap the two integrations (legitimate by `hint`).
  have hswap : (∫ s in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.K θ * Work.Spaces.pz f s θ)
      = ∫ θ in Work.Spaces.Iθ, ∫ s in Set.Ioi (0 : ℝ),
          Work.Spaces.K θ * Work.Spaces.pz f s θ := by
    refine integral_integral_swap (μ := volume.restrict (Set.Ioi (0 : ℝ)))
      (ν := volume.restrict Work.Spaces.Iθ)
      (f := fun s θ => Work.Spaces.K θ * Work.Spaces.pz f s θ) ?_
    rw [MeasureTheory.Measure.prod_restrict]
    exact hint
  -- For almost every `θ` the radial integral vanishes, by the FTC.
  have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ∫ s in Set.Ioi (0 : ℝ), Work.Spaces.K θ * Work.Spaces.pz f s θ = 0 := by
    -- Fubini also gives the a.e. radial integrability of the slices, the FTC's integrability
    -- hypothesis.
    have hslice : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        MeasureTheory.IntegrableOn (fun s => Work.Spaces.K θ * Work.Spaces.pz f s θ)
          (Set.Ioi 0) := by
      have hprod : MeasureTheory.Integrable
          (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2)
          ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict Work.Spaces.Iθ)) := by
        rw [MeasureTheory.Measure.prod_restrict]
        exact hint
      exact hprod.prod_left_ae
    filter_upwards [hslice, MeasureTheory.self_mem_ae_restrict (μ := volume) hsIθ]
      with θ hsl hmem
    have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun s => Work.Spaces.K θ * f s θ)
        (Work.Spaces.K θ * Work.Spaces.pz f x θ) x :=
      fun x hx => (hdiff θ hmem x hx).const_mul _
    have hcw : ContinuousWithinAt (fun s => Work.Spaces.K θ * f s θ) (Set.Ici 0) 0 :=
      ((hcont0 θ hmem).continuousWithinAt (by simp : (0 : ℝ) ∈ Set.Ici 0)).const_mul _
    have hlim : Filter.Tendsto (fun s => Work.Spaces.K θ * f s θ) Filter.atTop (nhds (0 : ℝ)) := by
      simpa using (hdec θ hmem).const_mul (Work.Spaces.K θ)
    have hftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcw hderiv hsl hlim
    rw [hvan θ hmem] at hftc
    simpa using hftc
  rw [hstep, hswap]
  calc ∫ θ in Work.Spaces.Iθ, (∫ s in Set.Ioi (0 : ℝ),
        Work.Spaces.K θ * Work.Spaces.pz f s θ)
      = ∫ θ in Work.Spaces.Iθ, (0 : ℝ) := integral_congr_ae hae
    _ = 0 := integral_zero ℝ ℝ

end Work.FTS.StrongEps.EpsZero
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.Atoms.QangSq5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5.Atoms

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Null-set bookkeeping (the two ends of `Iz`, the two angular endpoints) -/

private theorem Iz_ae_eq_Ioi : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
  (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm

private theorem Iθ_ae_eq_Ioo : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
  (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm

/-- `w²` is continuous on `(0,∞)`. -/
private theorem continuousOn_w_sq :
    ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) := by
  have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      = fun z : ℝ => (((1 + z) ^ 2 / z ^ 2) ^ 2) := by
    funext z; rw [Work.Spaces.w]
  rw [hfun]
  exact (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
    (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))).pow 2

/-! ## The weighted slot, with the full weight `w²`, at level `5` -/


/-! ## A.e. strong measurability of the angular moment -/

/-- `z ↦ Qang g i z` is a.e. strongly measurable on `Iz` (no integrability needed): it is the
`θ`-integral of the jointly continuous `(z,θ) ↦ Kθ(θ)·D_z^i g z θ` on the open quadrant
(`AEStronglyMeasurable.integral_prod_right'`). -/
private theorem aesm_Qang (i : ℕ) {g : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen g) :
    AEStronglyMeasurable (fun z : ℝ => Work.Elliptic.Qang g i z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have h := (Work.Spaces.aesm_of_continuousOn_Qd
    (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * Work.Spaces.DzIter i g p.1 p.2)
    (Work.FTS.OpenPkg.QangOpen.continuousOn_Ktheta_DzIter_open hO i)).integral_prod_right'
  simpa only [Work.Elliptic.Qang] using h

/-! ## The level-five bound -/


end Work.FTS.StrongEps.H5.Atoms
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.L12.LocUnifAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.L12

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Auxiliary objects -/

/-- The radial marginal `s ↦ ∫_θ HkIntegrand α 0 D s θ` of the `ℋ⁰`-integrand. -/
def radMarg (α : ℝ) (D : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 D s θ


lemma HkSq_zero_eq (α : ℝ) (D : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 D = ∫ s in Work.Spaces.Iz, radMarg α D s := by
  simp only [Work.Spaces.HkSq, radMarg]





/-! ## Elementary estimates for `Wlam` -/




/-! ## The choice lemmas -/




end Work.FTS.StrongEps.L12
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.L12.WlamSqIoi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.L12

open scoped Real Topology
open MeasureTheory Set Filter


end Work.FTS.StrongEps.L12
end
-- ===== merged: Submission.Work.FTS.StrongLWP.Sobolev.HkIntegrand_mixed_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongLWP.Sobolev

set_option autoImplicit false

/-! ## Congruence of the iterates of `D_z` on the open quadrant

`D_z = z ∂_z` is local, so two functions that agree on the open quadrant have the same
`D_z`-iterates there. -/

private lemma DzIter_congr_quadU {F G : ℝ → ℝ → ℝ}
    (h : EqOn (Function.uncurry F) (Function.uncurry G) Work.Spaces.quadU) (b : ℕ) :
    EqOn (Function.uncurry (Work.Spaces.DzIter b F))
      (Function.uncurry (Work.Spaces.DzIter b G)) Work.Spaces.quadU := by
  have hV : IsOpen Work.Spaces.quadU := Work.Spaces.isOpen_quadU
  induction b with
  | zero => exact h
  | succ n ih =>
      intro y hy
      have hpz : Work.Spaces.pz (Work.Spaces.DzIter n F) y.1 y.2
          = Work.Spaces.pz (Work.Spaces.DzIter n G) y.1 y.2 :=
        Work.Spaces.pz_congr_of_isOpen hV ih hy
      show y.1 * Work.Spaces.pz (Work.Spaces.DzIter n F) y.1 y.2
          = y.1 * Work.Spaces.pz (Work.Spaces.DzIter n G) y.1 y.2
      rw [hpz]

/-! ## `D_z` commutes with the iterates of `D_θ` on the open quadrant -/

/-- `D_z (D_θ^a g) = D_θ^a (D_z g)` on the open quadrant, for a profile that is `C^∞` (in the
genuine smooth order `Work.Stability.smoothOrder`) there.  This is
`Work.Spaces.DzDthIterCommOn` with the finite-order smooth class `SmoothQuad` in place of the
analytic order `⊤`. -/
private theorem Dz_DthIter_comm_quadU {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) Work.Spaces.quadU)
    (a : ℕ) :
    EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter a g)))
      (Function.uncurry (Work.Spaces.DthIter a (Work.Spaces.Dz g))) Work.Spaces.quadU := by
  have hV : IsOpen Work.Spaces.quadU := Work.Spaces.isOpen_quadU
  have h2le : (2 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
    rw [Work.Stability.smoothOrder]; exact WithTop.coe_le_coe.mpr le_top
  induction a with
  | zero => intro y hy; rfl
  | succ i ih =>
      intro y hy
      have hsmD : ContDiffOn ℝ Work.Stability.smoothOrder
          (Function.uncurry (Work.Spaces.DthIter i g)) Work.Spaces.quadU :=
        Work.FTS.LocData.contDiffOn_DthIter hV hg i
      have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DthIter i g)) y :=
        (ContDiffOn.of_le hsmD h2le).contDiffAt (hV.mem_nhds hy)
      have hcomm : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i g)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DthIter i g)) y.1 y.2 :=
        Work.Spaces.Dz_Dth_comm (f := Work.Spaces.DthIter i g) hcd
      show Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i g)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.Dz g)) y.1 y.2
      rw [hcomm]
      show Real.sin (2 * y.2) * Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DthIter i g)) y.1 y.2
          = Real.sin (2 * y.2)
            * Work.Spaces.pth (Work.Spaces.DthIter i (Work.Spaces.Dz g)) y.1 y.2
      rw [Work.Spaces.pth_congr_of_isOpen hV ih hy]

/-- `D_z^j (D_θ^a X) = D_θ^a (D_z^j X)` on the open quadrant, for a profile that is `C^∞`
there. -/
private theorem DzIter_DthIter_comm_quadU {X : ℝ → ℝ → ℝ}
    (hX : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry X) Work.Spaces.quadU)
    (a j : ℕ) :
    EqOn (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.DthIter a X)))
      (Function.uncurry (Work.Spaces.DthIter a (Work.Spaces.DzIter j X))) Work.Spaces.quadU := by
  have hV : IsOpen Work.Spaces.quadU := Work.Spaces.isOpen_quadU
  induction j with
  | zero => intro y hy; rfl
  | succ j ih =>
      intro y hy
      have hDzSm : ContDiffOn ℝ Work.Stability.smoothOrder
          (Function.uncurry (Work.Spaces.DzIter j X)) Work.Spaces.quadU :=
        Work.FTS.LocData.contDiffOn_DzIter hV hX j
      have hstep : Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.DthIter a X)) y.1 y.2
          = Work.Spaces.Dz (Work.Spaces.DthIter a (Work.Spaces.DzIter j X)) y.1 y.2 := by
        have hpz := Work.Spaces.pz_congr_of_isOpen hV ih hy
        show y.1 * Work.Spaces.pz (Work.Spaces.DzIter j (Work.Spaces.DthIter a X)) y.1 y.2
            = y.1 * Work.Spaces.pz (Work.Spaces.DthIter a (Work.Spaces.DzIter j X)) y.1 y.2
        rw [hpz]
      show Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.DthIter a X)) y.1 y.2
          = Work.Spaces.DthIter a (Work.Spaces.DzIter (j + 1) X) y.1 y.2
      rw [hstep]
      exact Dz_DthIter_comm_quadU hDzSm a hy

/-! ## The mixed derivatives of a mixed derivative -/

/-- `D_z^bD_θ^a (D_z^jD_θ^if) = D_z^{b+j}D_θ^{a+i}f` at every point of the open quadrant,
for a `SmoothQuad` datum. -/
private theorem mixed_mixed_quadU {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Work.Spaces.quadU)
    (b a j i : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    Work.Spaces.mixed b a (Work.Spaces.mixed j i f) z θ
      = Work.Spaces.mixed (b + j) (a + i) f z θ := by
  have hV : IsOpen Work.Spaces.quadU := Work.Spaces.isOpen_quadU
  have hy : (z, θ) ∈ Work.Spaces.quadU := by
    simp only [Work.Spaces.quadU, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
    exact ⟨by linarith, hθ0, hθ1⟩
  have hX : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.DthIter i f)) Work.Spaces.quadU :=
    Work.FTS.LocData.contDiffOn_DthIter hV hf i
  have hcommEq : EqOn
      (Function.uncurry
        (Work.Spaces.DthIter a (Work.Spaces.DzIter j (Work.Spaces.DthIter i f))))
      (Function.uncurry
        (Work.Spaces.DzIter j (Work.Spaces.DthIter a (Work.Spaces.DthIter i f))))
      Work.Spaces.quadU := (DzIter_DthIter_comm_quadU hX a j).symm
  have h1 : Work.Spaces.DzIter b
        (Work.Spaces.DthIter a (Work.Spaces.DzIter j (Work.Spaces.DthIter i f))) z θ
      = Work.Spaces.DzIter b
        (Work.Spaces.DzIter j (Work.Spaces.DthIter a (Work.Spaces.DthIter i f))) z θ :=
    (DzIter_congr_quadU hcommEq b) hy
  simp only [Work.Spaces.mixed]
  rw [h1, ← Work.Spaces.DzIter_add_right b j (Work.Spaces.DthIter a (Work.Spaces.DthIter i f)),
    Work.Spaces.DthIter_add_right a i f]

/-! ## Vanishing of the integrand on the angular boundary -/

/-- At `sin(2θ) = 0` the `ℋ^k`-integrand vanishes for every `f`: the `1/sin(2θ)^{η/2}` of the
first sum and the `Wt = w·sin(2θ)^{-γ/2}` of the second are both `0`. -/
private lemma HkIntegrand_eq_zero_of_sin (α : ℝ) (hα : 0 < α) (k : ℕ) (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hs : Real.sin (2 * θ) = 0) : Work.Spaces.HkIntegrand α k f z θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  have hsin : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
    rw [hs, Real.zero_rpow (by norm_num [Work.Spaces.eta])]
  have hgam : 0 < Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hWt : Work.Spaces.Wt α z θ = 0 := by
    rw [Work.Spaces.Wt, Work.Spaces.wTheta, hs,
      Real.zero_rpow (neg_ne_zero.mpr (ne_of_gt (div_pos hgam (by norm_num)))), mul_zero]
  have h1 : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hsin, div_zero, mul_zero, zero_pow (by norm_num)]
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hc
    · rw [hWt, mul_zero, zero_pow (by norm_num)]
    · rfl
  rw [h1, h2, add_zero]

/-! ## The pointwise domination -/

theorem HkIntegrand_mixed_le {α : ℝ} (hα : 0 < α) {k j i : ℕ} (f : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.LocData.SmoothQuad f) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k (Work.Spaces.mixed j i f) z θ
      ≤ Work.Spaces.HkIntegrand α (i + j + k) f z θ := by
  have hθ0le : 0 ≤ θ := hθ.1
  have hθ1le : θ ≤ π / 2 := hθ.2
  by_cases hsin : Real.sin (2 * θ) = 0
  · rw [HkIntegrand_eq_zero_of_sin α hα k (Work.Spaces.mixed j i f) hsin,
      HkIntegrand_eq_zero_of_sin α hα (i + j + k) f hsin]
  · have hθ0 : 0 < θ := by
      rcases eq_or_lt_of_le hθ0le with h | h
      · exact absurd (by rw [← h]; simp) hsin
      · exact h
    have hθ1 : θ < π / 2 := by
      rcases lt_or_eq_of_le hθ1le with h | h
      · exact h
      · exact absurd (by rw [h]; rw [show 2 * (π / 2) = π by ring, Real.sin_pi]) hsin
    have hzIz : z ∈ Work.Spaces.Iz := by
      rw [Work.Spaces.Iz, Set.mem_Ici]; exact le_of_lt hz
    set H : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hH
    set W : ℝ := Work.Spaces.Wt α z θ with hW
    have hHW : H ^ 2 ≤ W ^ 2 := by
      rw [hH, hW]; exact Work.Spaces.H_le_Wt α hα z θ hzIz hθ
    -- The `(D_θ`-order, `D_z`-order)`-indexed building block of the two integrands.
    set T : ℕ × ℕ → ℝ := fun x =>
      if x.1 = 0 then (Work.Spaces.DzIter x.2 f z θ * H) ^ 2
      else (Work.Spaces.mixed x.2 x.1 f z θ * W) ^ 2 with hT
    have hTnn : ∀ x, 0 ≤ T x := by
      rintro ⟨x1, x2⟩; simp only [hT]; split <;> exact sq_nonneg _
    -- The index sets of the two sums of the right-hand side.
    set R1 : Finset (ℕ × ℕ) := (Finset.range (i + j + k + 1)).image (fun q => ((0 : ℕ), q))
      with hR1def
    set R2 : Finset (ℕ × ℕ) :=
      ((Finset.range (i + j + k + 1)) ×ˢ (Finset.range (i + j + k + 1))).filter
        (fun x : ℕ × ℕ => 1 ≤ x.1 ∧ x.1 + x.2 ≤ i + j + k) with hR2def
    -- The index sets of the two sums of the left-hand side, shifted into the right-hand side.
    set S1 : Finset (ℕ × ℕ) := (Finset.range (k + 1)).image (fun a => (i, a + j)) with hS1def
    set S2 : Finset (ℕ × ℕ) :=
      (((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))).filter
        (fun x : ℕ × ℕ => 1 ≤ x.1 ∧ x.1 + x.2 ≤ k)).image
          (fun x : ℕ × ℕ => (x.1 + i, x.2 + j)) with hS2def
    have hR1 : (∑ x ∈ R1, T x)
        = ∑ q ∈ Finset.range (i + j + k + 1), (Work.Spaces.DzIter q f z θ * H) ^ 2 := by
      rw [hR1def]
      have hinj : Set.InjOn (fun q : ℕ => ((0 : ℕ), q))
          (↑(Finset.range (i + j + k + 1)) : Set ℕ) := by
        intro x _ y _ h; simpa using h
      rw [Finset.sum_image (f := T) hinj]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      simp only [hT]; simp
    have hR2 : (∑ x ∈ R2, T x)
        = ∑ p ∈ Finset.range (i + j + k + 1), ∑ q ∈ Finset.range (i + j + k + 1),
            (if 1 ≤ p ∧ p + q ≤ i + j + k
              then (Work.Spaces.mixed q p f z θ * W) ^ 2 else 0) := by
      rw [hR2def, Finset.sum_filter, Finset.sum_product]
      refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
      simp only [hT]
      by_cases hc : 1 ≤ p ∧ p + q ≤ i + j + k
      · rw [if_pos hc, if_pos hc, if_neg (by omega : ¬ p = 0)]
      · rw [if_neg hc, if_neg hc]
    have hLHSunfold : Work.Spaces.HkIntegrand α k (Work.Spaces.mixed j i f) z θ
        = (∑ a ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter a (Work.Spaces.mixed j i f) z θ * H) ^ 2)
          + ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1),
              (if 1 ≤ a ∧ a + b ≤ k
                then (Work.Spaces.mixed b a (Work.Spaces.mixed j i f) z θ * W) ^ 2 else 0) := by
      simp [Work.Spaces.HkIntegrand, ← hH, ← hW]
    have hRHSunfold : Work.Spaces.HkIntegrand α (i + j + k) f z θ
        = (∑ q ∈ Finset.range (i + j + k + 1), (Work.Spaces.DzIter q f z θ * H) ^ 2)
          + ∑ p ∈ Finset.range (i + j + k + 1), ∑ q ∈ Finset.range (i + j + k + 1),
              (if 1 ≤ p ∧ p + q ≤ i + j + k
                then (Work.Spaces.mixed q p f z θ * W) ^ 2 else 0) := by
      simp [Work.Spaces.HkIntegrand, ← hH, ← hW]
    -- The first sum of the left-hand side sits on `S1`.
    have hS1 : (∑ a ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter a (Work.Spaces.mixed j i f) z θ * H) ^ 2)
        ≤ ∑ x ∈ S1, T x := by
      rw [hS1def]
      have hinj : Set.InjOn (fun a : ℕ => (i, a + j)) (↑(Finset.range (k + 1)) : Set ℕ) := by
        intro x _ y _ h; simpa using h
      rw [Finset.sum_image (f := T) hinj]
      refine Finset.sum_le_sum (fun a _ => ?_)
      simp only [hT]
      by_cases hi : i = 0
      · subst hi
        rw [if_pos rfl, Work.Spaces.mixed_zero_right, ← Work.Spaces.DzIter_add_right a j f]
      · rw [if_neg (by omega : ¬ i = 0)]
        have hDz : Work.Spaces.DzIter a (Work.Spaces.mixed j i f)
            = Work.Spaces.mixed (a + j) i f := by
          simp only [Work.Spaces.mixed]; rw [Work.Spaces.DzIter_add_right]
        rw [hDz]
        nlinarith [hHW, sq_nonneg (Work.Spaces.mixed (a + j) i f z θ)]
    -- The second sum of the left-hand side equals the sum on `S2`.
    have hS2 : (∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1),
          (if 1 ≤ a ∧ a + b ≤ k
            then (Work.Spaces.mixed b a (Work.Spaces.mixed j i f) z θ * W) ^ 2 else 0))
        = ∑ x ∈ S2, T x := by
      rw [hS2def]
      have hinj : Set.InjOn (fun x : ℕ × ℕ => (x.1 + i, x.2 + j))
          (↑(((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))).filter
            (fun x : ℕ × ℕ => 1 ≤ x.1 ∧ x.1 + x.2 ≤ k)) : Set (ℕ × ℕ)) := by
        intro x _ y _ h
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Nat.add_right_cancel h.1) (Nat.add_right_cancel h.2)
      rw [Finset.sum_image (f := T) hinj, Finset.sum_filter, Finset.sum_product]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      dsimp only
      by_cases hc : 1 ≤ a ∧ a + b ≤ k
      · rw [if_pos hc, if_pos hc]
        simp only [hT]
        rw [if_neg (by omega : ¬ a + i = 0)]
        rw [mixed_mixed_quadU hsm b a j i hz hθ0 hθ1]
      · rw [if_neg hc, if_neg hc]
    have hdisjS : Disjoint S1 S2 := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [hS1def, Finset.mem_image] at hx1
      obtain ⟨a, _, rfl⟩ := hx1
      rw [hS2def, Finset.mem_image] at hx2
      obtain ⟨y, hy, hxy⟩ := hx2
      rw [Finset.mem_filter] at hy
      simp only [Prod.mk.injEq] at hxy
      have hy1 : 1 ≤ y.1 := hy.2.1
      omega
    have hdisjR : Disjoint R1 R2 := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [hR1def, Finset.mem_image] at hx1
      obtain ⟨q, _, rfl⟩ := hx1
      rw [hR2def, Finset.mem_filter] at hx2
      have h := hx2.2.1
      simp only at h
      omega
    have hsub : S1 ∪ S2 ⊆ R1 ∪ R2 := by
      intro x hx
      rw [Finset.mem_union] at hx ⊢
      rcases hx with hx | hx
      · rw [hS1def, Finset.mem_image] at hx
        obtain ⟨a, ha, rfl⟩ := hx
        rw [Finset.mem_range] at ha
        by_cases hi : i = 0
        · left
          rw [hR1def, Finset.mem_image]
          exact ⟨a + j, by rw [Finset.mem_range]; omega, by simp [hi]⟩
        · right
          rw [hR2def, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
          dsimp only
          exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
      · rw [hS2def, Finset.mem_image] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hy
        right
        rw [hR2def, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
        dsimp only
        exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
    rw [hLHSunfold, hRHSunfold, ← hR1, ← hR2]
    calc _ ≤ (∑ x ∈ S1, T x) + (∑ x ∈ S2, T x) := add_le_add hS1 (le_of_eq hS2)
      _ = ∑ x ∈ S1 ∪ S2, T x := (Finset.sum_union hdisjS).symm
      _ ≤ ∑ x ∈ R1 ∪ R2, T x :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hTnn x)
      _ = (∑ x ∈ R1, T x) + (∑ x ∈ R2, T x) := Finset.sum_union hdisjR

end Work.FTS.StrongLWP.Sobolev
end
end
-- ===== merged: Submission.Work.FTS.StrongLWP.Sobolev.supAbs_mixed_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongLWP.Sobolev

set_option autoImplicit false

/-! ## `VanishTheta` is preserved by mixed `D`-derivatives -/




/-! ## The `H^k`-integrand of a mixed derivative at a lower level

The two shifts: adding one `∂_θ` (with the `D_θ`-weight) raises the level of the integrand
by one, and likewise for `∂_z` (with the `D_z`-weight, the reindexing being the commutation
`D_z D_θ = D_θ D_z`). -/






/-! ## Integration of the pointwise domination -/



/-! ## The target lemma -/


end Work.FTS.StrongLWP.Sobolev
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.Fstar_W6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `F_*`-package at order `6`: `Fstar_W6`

The profile `F_*(z,θ) = α (Γ(θ)/c) · 2z/(1+z)²` of `Work.Construction.Fstar` satisfies

  `F_* ∈ 𝒲^{6,∞}`  and  `|F_*|_{𝒲^{6,∞}} ≤ C α`,  `C` universal, for every `0 < α ≤ 1`.

The level-`4` version of this statement is `Work.FTS.Nonlinear.FstarPkg.Fstar_W`.  Nothing in
that proof used the bound `4`: the two pointwise estimates

* `Fstar_z_bound`     : `|(1+z)^k ∂_z^k F_*| ≤ 20 α · k!(k+1)`,
* `Fstar_mixed_bound` : `|(1+z)^k ∂_z^kD_θ^j F_* · sin(2θ)^{-α/5}/(α+sin 2θ)| ≤ 20 α · (tBound (j-1) 0) · k!(k+1)`

are proved for *arbitrary* `k : ℕ` and `j ≥ 1` (the only constraint is `1 ≤ j`), and the
`z`-factor `h = z/(1+z)²` as well as the angular factor `Γ` are both smooth for all orders.
So the whole `𝒲^{6,∞}`-bound follows by re-running the assembly with `4 ↦ 6` and the universal
constant `KB6` in place of `KB`.

The structure of the file is therefore:

* `KB6` and `KB6_nonneg` — the universal constant multiplying `20 α`;
* `WlInf_Fstar_le6` — the norm bound `|F_*|_{𝒲^{6,∞}} ≤ 20 α · KB6`;
* `WlInfMem_Fstar6` — membership, every `SupFinite` predicate witnessed by the same bounds;
* `Fstar_W6` — the requested statement.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

set_option autoImplicit false

/-! ## The universal constant -/

/-- The universal constant `KB6` multiplying `20 α`: the sum of all the (α-independent)
pointwise bounds of the summands of `𝒲^{6,∞}(F_*)`.  Same shape as `FstarPkg.KB`, with
`range 5 ↦ range 7` and `k + j ≤ 4 ↦ k + j ≤ 6`. -/
noncomputable def KB6 : ℝ :=
  (∑ k ∈ Finset.range 7, (k.factorial : ℝ) * (k + 1))
    + ∑ j ∈ Finset.range 7, ∑ k ∈ Finset.range 7,
        (if 1 ≤ j ∧ k + j ≤ 6 then
          Work.Spaces.tBound (j - 1) 0 * ((k.factorial : ℝ) * (k + 1)) else 0)

lemma KB6_nonneg : 0 ≤ KB6 := by
  rw [KB6]
  refine add_nonneg (Finset.sum_nonneg fun k _ => by positivity) ?_
  refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => ?_
  split_ifs with h
  · exact mul_nonneg (Work.Spaces.tBound_nonneg _ _) (by positivity)
  · norm_num

/-! ## The `𝒲^{6,∞}`-norm bound -/

/-- The `𝒲^{6,∞}`-norm of `F_*` is at most `20 α · KB6`. -/
lemma WlInf_Fstar_le6 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.WlInf α 6 (Work.Construction.Fstar α) ≤ 20 * α * KB6 := by
  have hKB : 20 * α * KB6 =
      (∑ k ∈ Finset.range 7, 20 * α * ((k.factorial : ℝ) * (k + 1)))
        + ∑ j ∈ Finset.range 7, ∑ k ∈ Finset.range 7,
            (20 * α * (if 1 ≤ j ∧ k + j ≤ 6 then
              Work.Spaces.tBound (j - 1) 0 * ((k.factorial : ℝ) * (k + 1)) else 0)) := by
    rw [KB6, mul_add]
    congr 1
    · rw [Finset.mul_sum]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
  rw [Work.Spaces.WlInf, hKB]
  apply add_le_add
  · refine Finset.sum_le_sum fun k hk => ?_
    refine Work.Spaces.supAbs_le fun z hz θ hθ => ?_
    exact Work.FTS.Nonlinear.FstarPkg.Fstar_z_bound α hα hα1 k z θ hz hθ
  · apply Finset.sum_le_sum
    intro j hj
    apply Finset.sum_le_sum
    intro k hk
    split_ifs with hcond
    · refine Work.Spaces.supAbs_le fun z hz θ hθ => ?_
      exact Work.FTS.Nonlinear.FstarPkg.Fstar_mixed_bound α hα hα1 j k hcond.1 z θ hz hθ
    · simp

/-! ## Membership in `𝒲^{6,∞}` -/

/-- `F_* ∈ 𝒲^{6,∞}` for `0 < α ≤ 1`.  Every `SupFinite` predicate is witnessed by the explicit
bound of `Fstar_z_bound` / `Fstar_mixed_bound`. -/
lemma WlInfMem_Fstar6 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Spaces.WlInfMem α 6 (Work.Construction.Fstar α) := by
  constructor
  · intro k hk
    refine ⟨20 * α * ((k.factorial : ℝ) * (k + 1)), fun y hy => ?_⟩
    rcases hy with ⟨z, hz, θ, hθ, rfl⟩
    exact Work.FTS.Nonlinear.FstarPkg.Fstar_z_bound α hα hα1 k z θ hz hθ
  · intro j hj k hk hj1 hjk
    refine ⟨20 * α * (Work.Spaces.tBound (j - 1) 0 * ((k.factorial : ℝ) * (k + 1))),
      fun y hy => ?_⟩
    rcases hy with ⟨z, hz, θ, hθ, rfl⟩
    exact Work.FTS.Nonlinear.FstarPkg.Fstar_mixed_bound α hα hα1 j k hj1 z θ hz hθ

/-! ## The requested statement -/

theorem Fstar_W6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    Work.Spaces.WlInfMem α 6 (Work.Construction.Fstar α) ∧
    Work.Spaces.WlInf α 6 (Work.Construction.Fstar α) ≤ C * α := by
  refine ⟨20 * KB6 + 1, by linarith [KB6_nonneg], fun α hα hα1 =>
    ⟨WlInfMem_Fstar6 α hα hα1, ?_⟩⟩
  refine le_trans (WlInf_Fstar_le6 α hα hα1) ?_
  nlinarith [KB6_nonneg, hα]

end Work.FTS.StrongPersist
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.LhatCommOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Aux

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.CoercivityFix.LhatCalc.DthAux

/-! ## The `D_θ`-commutator on an arbitrary open set -/

/-- **`D_θ` commutes exactly with `𝓛̂ = 𝓛 − Transport`** for a datum which is `C^∞` on an
arbitrary open set `V ∋ (z,θ)` (in particular on the open quadrant `(0,∞) × (0,π/2)` of the
strong-persistence estimates).  There is no commutator term, no nonlocal contribution and no
zero-mode hypothesis: this is `LhatCalc.Dth_Lhat` with the fixed quadrant replaced by `V`. -/
theorem Dth_Lhat_of_open {f : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hcd : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) V) {z θ : ℝ}
    (hmem : (z, θ) ∈ V) :
    Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f) z θ := by
  have hcf : ContDiffAt ℝ Work.Stability.smoothOrder (Function.uncurry f) (z, θ) :=
    hcd.contDiffAt (hV.mem_nhds hmem)
  have hfθ : DifferentiableAt ℝ (fun θ' => f z θ') θ :=
    Work.Spaces.differentiableAt_curry_right (hcf.differentiableAt smoothOrder_ne_zero)
  have hpz_sm : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pz f)) V := contDiffOn_uncurry_pz_sm hV hcd
  have hpzθ : DifferentiableAt ℝ (fun θ' => Work.Spaces.pz f z θ') θ :=
    Work.Spaces.differentiableAt_curry_right
      ((hpz_sm.contDiffAt (hV.mem_nhds hmem)).differentiableAt smoothOrder_ne_zero)
  have hpth_sm : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pth f)) V := contDiffOn_uncurry_pth_sm hV hcd
  have hpthθ : DifferentiableAt ℝ (fun θ' => Work.Spaces.pth f z θ') θ :=
    Work.Spaces.differentiableAt_curry_right
      ((hpth_sm.contDiffAt (hV.mem_nhds hmem)).differentiableAt smoothOrder_ne_zero)
  have dL : DifferentiableAt ℝ (fun θ' => Work.Coercivity.L f z θ') θ := by
    rw [show (fun θ' => Work.Coercivity.L f z θ')
        = (fun θ' => f z θ' + z * Work.Spaces.pz f z θ' - (2 / (1 + z)) * f z θ') from by
      funext θ'; simp only [Work.Coercivity.L, Work.Spaces.Dz]; ring]
    exact (hfθ.add (hpzθ.const_mul z)).sub (hfθ.const_mul (2 / (1 + z)))
  have hDθ : DifferentiableAt ℝ (fun θ' => Work.Spaces.Dth f z θ') θ := by
    rw [show (fun θ' => Work.Spaces.Dth f z θ')
        = (fun θ' => Real.sin (2 * θ') * Work.Spaces.pth f z θ') from by
      funext θ'; simp only [Work.Spaces.Dth]]
    exact ((hasDerivAt_sin_two θ).differentiableAt).mul hpthθ
  have dTr : DifferentiableAt ℝ (fun θ' => Work.Coercivity.Transport f z θ') θ := by
    rw [show (fun θ' => Work.Coercivity.Transport f z θ')
        = (fun θ' => (3 / (1 + z)) * Work.Spaces.Dth f z θ') from by
      funext θ'; simp only [Work.Coercivity.Transport]; ring]
    exact hDθ.const_mul (3 / (1 + z))
  have hpth : Work.Spaces.pth (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.Spaces.pth (Work.Coercivity.L f) z θ
        - Work.Spaces.pth (Work.Coercivity.Transport f) z θ := by
    show deriv (fun θ' => Work.FTS.CoercivityFix.Lhat f z θ') θ = _
    rw [show (fun θ' => Work.FTS.CoercivityFix.Lhat f z θ')
        = ((fun θ' => Work.Coercivity.L f z θ')
            - fun θ' => Work.Coercivity.Transport f z θ') from by
      funext θ'; simp only [Work.FTS.CoercivityFix.Lhat, Pi.sub_apply]]
    rw [deriv_sub dL dTr]
    rfl
  rw [show Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.FTS.CoercivityFix.Lhat f) z θ from rfl]
  rw [hpth]
  rw [Work.FTS.CoercivityFix.Lhat_eq (Work.Spaces.Dth f) z θ]
  rw [pth_L_of_smooth hV hcd hmem, Work.Coercivity.pth_Transport]
  rw [show Work.Spaces.Dz (Work.Spaces.Dth f) z θ
      = z * Work.Spaces.pz (Work.Spaces.Dth f) z θ from rfl]
  rw [Work.Coercivity.pz_Dth_val]
  rw [show Work.Spaces.Dth (Work.Spaces.Dth f) z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.Dth f) z θ from rfl]
  rw [show Work.Spaces.Dth f z θ = Real.sin (2 * θ) * Work.Spaces.pth f z θ from rfl]
  rw [pth_Dth_eq (g := f) hpthθ]
  ring

/-! ## The smoothness of the partials at a point of `V` -/

section Slices

variable {f : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}

/-- The `z`-slices of `f` are differentiable at a point of the open set `V`. -/
private lemma diff_z_self (hV : IsOpen V)
    (hcd : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) V) {z θ : ℝ}
    (hmem : (z, θ) ∈ V) : DifferentiableAt ℝ (fun z' => f z' θ) z :=
  Work.Spaces.differentiableAt_curry_left
    ((hcd.contDiffAt (hV.mem_nhds hmem)).differentiableAt smoothOrder_ne_zero)

/-- The `z`-slices of `∂_z f` are differentiable at a point of the open set `V`. -/
private lemma diff_z_pz (hV : IsOpen V)
    (hcd : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) V) {z θ : ℝ}
    (hmem : (z, θ) ∈ V) : DifferentiableAt ℝ (fun z' => Work.Spaces.pz f z' θ) z :=
  Work.Spaces.differentiableAt_curry_left
    (((contDiffOn_uncurry_pz_sm hV hcd).contDiffAt (hV.mem_nhds hmem)).differentiableAt
      smoothOrder_ne_zero)

/-- The `θ`-slices of `∂_z f` are differentiable at a point of the open set `V`. -/
private lemma diff_th_pz (hV : IsOpen V)
    (hcd : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) V) {z θ : ℝ}
    (hmem : (z, θ) ∈ V) : DifferentiableAt ℝ (fun θ' => Work.Spaces.pz f z θ') θ :=
  Work.Spaces.differentiableAt_curry_right
    (((contDiffOn_uncurry_pz_sm hV hcd).contDiffAt (hV.mem_nhds hmem)).differentiableAt
      smoothOrder_ne_zero)

/-- The `z`-slices of `∂_θ f` are differentiable at a point of the open set `V`. -/
private lemma diff_z_pth (hV : IsOpen V)
    (hcd : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) V) {z θ : ℝ}
    (hmem : (z, θ) ∈ V) : DifferentiableAt ℝ (fun z' => Work.Spaces.pth f z' θ) z :=
  Work.Spaces.differentiableAt_curry_left
    (((contDiffOn_uncurry_pth_sm hV hcd).contDiffAt (hV.mem_nhds hmem)).differentiableAt
      smoothOrder_ne_zero)

end Slices

/-! ## The plain `z`-derivatives of the pieces -/

private lemma deriv_z_self {f : ℝ → ℝ → ℝ} {z θ : ℝ} :
    deriv (fun z' => f z' θ) z = Work.Spaces.pz f z θ := rfl

private lemma deriv_z_mul_pz {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hpzz : DifferentiableAt ℝ (fun z' => Work.Spaces.pz f z' θ) z) :
    deriv (fun z' : ℝ => z' * Work.Spaces.pz f z' θ) z
      = Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ := by
  have hh := (hasDerivAt_id z).mul hpzz.hasDerivAt
  have h2 : deriv (fun z' : ℝ => z' * Work.Spaces.pz f z' θ) z
      = deriv (id * fun z' : ℝ => Work.Spaces.pz f z' θ) z := rfl
  rw [h2, hh.deriv]
  simp only [id_eq, one_mul]
  rfl

private lemma deriv_z_two_div {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hfz : DifferentiableAt ℝ (fun z' => f z' θ) z) :
    deriv (fun z' : ℝ => 2 * f z' θ / (1 + z')) z
      = 2 * Work.Spaces.pz f z θ / (1 + z) - 2 * f z θ / (1 + z) ^ 2 := by
  have hden : (1 + z : ℝ) ≠ 0 := by positivity
  have hh := (hfz.hasDerivAt.const_mul (2 : ℝ)).div
    ((hasDerivAt_const (x := z) (1 : ℝ)).add (hasDerivAt_id z)) (by simpa using hden)
  have h2 : deriv (fun z' : ℝ => 2 * f z' θ / (1 + z')) z
      = deriv ((fun y : ℝ => 2 * f y θ) / ((fun _ : ℝ => (1 : ℝ)) + (id : ℝ → ℝ))) z := rfl
  rw [h2, hh.deriv]
  simp only [Pi.add_apply, id_eq, zero_add]
  rw [deriv_z_self]
  field_simp
  try ring_nf

private lemma deriv_z_three_div {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hpthz : DifferentiableAt ℝ (fun z' => Work.Spaces.pth f z' θ) z) :
    deriv (fun z' : ℝ => 3 * (Real.sin (2 * θ) * Work.Spaces.pth f z' θ) / (1 + z')) z
      = 3 * (Real.sin (2 * θ) * Work.Spaces.pz (Work.Spaces.pth f) z θ) / (1 + z)
        - 3 * (Real.sin (2 * θ) * Work.Spaces.pth f z θ) / (1 + z) ^ 2 := by
  have hden : (1 + z : ℝ) ≠ 0 := by positivity
  have hh := (((hasDerivAt_const (x := z) (Real.sin (2 * θ))).mul hpthz.hasDerivAt).const_mul
    (3 : ℝ)).div ((hasDerivAt_const (x := z) (1 : ℝ)).add (hasDerivAt_id z))
    (by simpa using hden)
  have h2 : deriv (fun z' : ℝ => 3 * (Real.sin (2 * θ) * Work.Spaces.pth f z' θ) / (1 + z')) z
      = deriv ((fun y : ℝ => (fun _ : ℝ => (3 : ℝ)) y
            * ((fun _ : ℝ => Real.sin (2 * θ)) * fun z' => Work.Spaces.pth f z' θ) y)
          / ((fun _ : ℝ => (1 : ℝ)) + (id : ℝ → ℝ))) z := rfl
  rw [h2, hh.deriv]
  simp only [Pi.add_apply, Pi.mul_apply, id_eq, zero_add, zero_mul]
  rw [show deriv (fun z' => Work.Spaces.pth f z' θ) z
      = Work.Spaces.pz (Work.Spaces.pth f) z θ from rfl]
  field_simp
  try ring_nf

private lemma deriv_z_Dz {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hpzz : DifferentiableAt ℝ (fun z' => Work.Spaces.pz f z' θ) z) :
    deriv (fun z' => Work.Spaces.Dz f z' θ) z
      = Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ := by
  have hh := (hasDerivAt_id z).mul hpzz.hasDerivAt
  have h1 : (fun z' => Work.Spaces.Dz f z' θ)
      = (id * fun z' : ℝ => Work.Spaces.pz f z' θ) := by
    funext z'; rfl
  rw [h1, hh.deriv]
  simp only [id_eq, one_mul]
  rfl

private lemma deriv_th_Dz {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hpzθ : DifferentiableAt ℝ (fun θ' => Work.Spaces.pz f z θ') θ) :
    deriv (fun θ' => Work.Spaces.Dz f z θ') θ = z * Work.Spaces.pth (Work.Spaces.pz f) z θ := by
  have hh := (hasDerivAt_const (x := θ) z).mul hpzθ.hasDerivAt
  have h1 : (fun θ' => Work.Spaces.Dz f z θ')
      = ((fun _ : ℝ => z) * fun θ' => Work.Spaces.pz f z θ') := by
    funext θ'; rfl
  rw [h1, hh.deriv]
  simp only [zero_mul, zero_add]
  rfl

/-! ## The `z`-derivatives of the slices of `𝓛 f` and of `Transport f` -/

private lemma pz_L_eq {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hfz : DifferentiableAt ℝ (fun z' => f z' θ) z)
    (hpzz : DifferentiableAt ℝ (fun z' => Work.Spaces.pz f z' θ) z) :
    Work.Spaces.pz (Work.Coercivity.L f) z θ
      = Work.Spaces.pz f z θ + (Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ)
        - 2 * Work.Spaces.pz f z θ / (1 + z) + 2 * f z θ / (1 + z) ^ 2 := by
  show deriv (fun z' => Work.Coercivity.L f z' θ) z = _
  have hden : (1 + z : ℝ) ≠ 0 := by positivity
  have hid : DifferentiableAt ℝ (id * fun z' : ℝ => Work.Spaces.pz f z' θ) z :=
    differentiableAt_id.mul hpzz
  have hq : DifferentiableAt ℝ
      ((fun y : ℝ => 2 * f y θ) / ((fun _ : ℝ => (1 : ℝ)) + (id : ℝ → ℝ))) z :=
    (hfz.const_mul 2).div ((differentiableAt_const _).add differentiableAt_id)
      (by simpa using hden)
  have h1 : (fun z' => Work.Coercivity.L f z' θ)
      = (((fun z' : ℝ => f z' θ) + (id * fun z' : ℝ => Work.Spaces.pz f z' θ))
          - ((fun y : ℝ => 2 * f y θ) / ((fun _ : ℝ => (1 : ℝ)) + (id : ℝ → ℝ)))) := by
    funext z'; rfl
  rw [h1, deriv_sub (hfz.add hid) hq, deriv_add hfz hid]
  rw [show deriv (id * fun z' : ℝ => Work.Spaces.pz f z' θ) z
      = deriv (fun z' : ℝ => z' * Work.Spaces.pz f z' θ) z from rfl]
  rw [show deriv ((fun y : ℝ => 2 * f y θ) / ((fun _ : ℝ => (1 : ℝ)) + (id : ℝ → ℝ))) z
      = deriv (fun z' : ℝ => 2 * f z' θ / (1 + z')) z from rfl]
  rw [deriv_z_mul_pz hpzz, deriv_z_two_div hz hfz, deriv_z_self]
  ring

private lemma pz_Transport_eq {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hpthz : DifferentiableAt ℝ (fun z' => Work.Spaces.pth f z' θ) z) :
    Work.Spaces.pz (Work.Coercivity.Transport f) z θ
      = 3 * (Real.sin (2 * θ) * Work.Spaces.pz (Work.Spaces.pth f) z θ) / (1 + z)
        - 3 * (Real.sin (2 * θ) * Work.Spaces.pth f z θ) / (1 + z) ^ 2 := by
  show deriv (fun z' => Work.Coercivity.Transport f z' θ) z = _
  have h1 : (fun z' => Work.Coercivity.Transport f z' θ)
      = (fun z' : ℝ => 3 * (Real.sin (2 * θ) * Work.Spaces.pth f z' θ) / (1 + z')) := by
    funext z'; rfl
  rw [h1, deriv_z_three_div hz hpthz]

private lemma diff_slice_L {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hfz : DifferentiableAt ℝ (fun z' => f z' θ) z)
    (hpzz : DifferentiableAt ℝ (fun z' => Work.Spaces.pz f z' θ) z) :
    DifferentiableAt ℝ (fun z' => Work.Coercivity.L f z' θ) z := by
  have hden : (1 + z : ℝ) ≠ 0 := by positivity
  rw [show (fun z' => Work.Coercivity.L f z' θ)
      = (fun z' => f z' θ + z' * Work.Spaces.pz f z' θ - 2 * f z' θ / (1 + z')) from by
    funext z'; rfl]
  exact (hfz.add (differentiableAt_id.mul hpzz)).sub
    ((hfz.const_mul 2).div ((differentiableAt_const _).add differentiableAt_id)
      (by simpa using hden))

private lemma diff_slice_Transport {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hpthz : DifferentiableAt ℝ (fun z' => Work.Spaces.pth f z' θ) z) :
    DifferentiableAt ℝ (fun z' => Work.Coercivity.Transport f z' θ) z := by
  have hden : (1 + z : ℝ) ≠ 0 := by positivity
  rw [show (fun z' => Work.Coercivity.Transport f z' θ)
      = (fun z' => 3 * (Real.sin (2 * θ) * Work.Spaces.pth f z' θ) / (1 + z')) from by
    funext z'; rfl]
  exact (((differentiableAt_const (c := Real.sin (2 * θ))).mul hpthz).const_mul 3).div
    ((differentiableAt_const (c := (1 : ℝ))).add differentiableAt_id) (by simpa using hden)

/-! ## The `D_z`-commutator on an arbitrary open set -/

/-- **The `D_z`-commutator of the clean operator** `𝓛̂ = 𝓛 − Transport` for a datum which is
`C^∞` on an arbitrary open set `V ∋ (z,θ)`:

  `D_z(𝓛̂ f) = 𝓛̂(D_z f) + Ê₂ f`,   `Ê₂ f = (2zf + 3z D_θ f)/(1+z)²`.

This is `LhatCalc.Dz_Lhat` with the fixed quadrant `quadU = (-1,∞) × (0,π/2)` replaced by the
variable open set `V`; the hypothesis `0 < z` is only there because `𝓛` divides by `1+z`. -/
theorem Dz_Lhat_of_open {f : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hcd : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) V) {z θ : ℝ}
    (hmem : (z, θ) ∈ V) (hz : 0 < z) :
    Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
        + Work.FTS.CoercivityFix.E2hat f z θ := by
  have hden : (1 + z : ℝ) ≠ 0 := by positivity
  have hfz := diff_z_self hV hcd hmem
  have hpzz := diff_z_pz hV hcd hmem
  have hpzθ := diff_th_pz hV hcd hmem
  have hpthz := diff_z_pth hV hcd hmem
  have hLz := diff_slice_L (θ := θ) hz hfz hpzz
  have hTz := diff_slice_Transport (θ := θ) hz hpthz
  -- the plain `z`-derivatives of the two summands of `𝓛̂`
  have hpzL := pz_L_eq (θ := θ) hz hfz hpzz
  have hpzT := pz_Transport_eq (θ := θ) hz hpthz
  have hpzLhat : Work.Spaces.pz (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.Spaces.pz (Work.Coercivity.L f) z θ
        - Work.Spaces.pz (Work.Coercivity.Transport f) z θ := by
    show deriv (fun z' => Work.FTS.CoercivityFix.Lhat f z' θ) z = _
    have h1 : (fun z' => Work.FTS.CoercivityFix.Lhat f z' θ)
        = ((fun z' => Work.Coercivity.L f z' θ)
            - fun z' => Work.Coercivity.Transport f z' θ) := by
      funext z'; rfl
    rw [h1, deriv_sub hLz hTz]
    rfl
  have hLHS : Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
      = z * (Work.Spaces.pz (Work.Coercivity.L f) z θ
          - Work.Spaces.pz (Work.Coercivity.Transport f) z θ) := by
    show z * deriv (fun z' => Work.FTS.CoercivityFix.Lhat f z' θ) z = _
    rw [show deriv (fun z' => Work.FTS.CoercivityFix.Lhat f z' θ) z
        = Work.Spaces.pz (Work.FTS.CoercivityFix.Lhat f) z θ from rfl, hpzLhat]
  -- the right-hand side
  have hDzDz : Work.Spaces.Dz (Work.Spaces.Dz f) z θ
      = z * (Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ) := by
    show z * deriv (fun z' => Work.Spaces.Dz f z' θ) z = _
    rw [deriv_z_Dz hpzz]
  have hDthDz : Work.Spaces.Dth (Work.Spaces.Dz f) z θ
      = Real.sin (2 * θ) * (z * Work.Spaces.pth (Work.Spaces.pz f) z θ) := by
    show Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.Dz f z θ') θ = _
    rw [deriv_th_Dz hpzθ]
  have hRHS : Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
        + Work.FTS.CoercivityFix.E2hat f z θ
      = (z * Work.Spaces.pz f z θ
          + z * (Work.Spaces.pz f z θ + z * Work.Spaces.pz (Work.Spaces.pz f) z θ)
          - 2 * (z * Work.Spaces.pz f z θ) / (1 + z)
          - 3 * (Real.sin (2 * θ) * (z * Work.Spaces.pth (Work.Spaces.pz f) z θ)) / (1 + z))
        + (2 * z * f z θ + 3 * z * (Real.sin (2 * θ) * Work.Spaces.pth f z θ)) / (1 + z) ^ 2 := by
    rw [Work.FTS.CoercivityFix.Lhat_eq (Work.Spaces.Dz f), Work.FTS.CoercivityFix.E2hat_eq]
    rw [hDzDz, hDthDz]
    rw [show Work.Spaces.Dz f z θ = z * Work.Spaces.pz f z θ from rfl,
      show Work.Spaces.Dth f z θ = Real.sin (2 * θ) * Work.Spaces.pth f z θ from rfl]
  -- Clairaut's theorem finishes the identification `∂_θ∂_z f = ∂_z∂_θ f`
  have hcd2 : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ) :=
    (hcd.contDiffAt (hV.mem_nhds hmem)).of_le (by simp [Work.Stability.smoothOrder])
  have hcl := Work.Spaces.pz_pth_comm hcd2
  rw [hLHS, hRHS, hpzL, hpzT, hcl]
  field_simp
  try ring_nf

/-! ## The requested statement -/

/-- **Both commutator identities of `𝓛̂` on the open quadrant `Qd = (0,∞) × (0,π/2)`**: for a
datum `h` that is `C^∞` on the open quadrant `(0,∞) × (0,π/2)` (the class
`Work.FTS.EllipticEst.SmoothOpen`) and every interior point `(z,θ) ∈ Qd`,

* `D_θ(𝓛̂ h) = 𝓛̂(D_θ h)`,
* `D_z(𝓛̂ h) = 𝓛̂(D_z h) + Ê₂ h`. -/
theorem LhatCommOpen {h : ℝ → ℝ → ℝ} (hs : Work.FTS.EllipticEst.SmoothOpen h) :
    (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat h) z θ
        = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth h) z θ) ∧
    (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat h) z θ
        = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz h) z θ
          + Work.FTS.CoercivityFix.E2hat h z θ) := by
  have hs' : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry h)
      (Work.FTS.EllipticEst.Q0) := hs
  refine ⟨fun z θ hzθ => Dth_Lhat_of_open Work.FTS.EllipticEst.isOpen_Q0 hs' hzθ,
    fun z θ hzθ => Dz_Lhat_of_open Work.FTS.EllipticEst.isOpen_Q0 hs' hzθ ?_⟩
  have h := hzθ
  rw [Work.Construction.Qd, Set.mem_prod, Set.mem_Ioi] at h
  exact h.1

end Work.FTS.StrongPersist.H6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.l12ContDiffOnOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T5bAux

/-- `L₁₂(f)` is `C¹` on `(0,∞)` for a datum smooth on the open quadrant with
`HkMem α 7 f`.  In fact `UopHk.contDiffOn_L12_k` gives `C⁷`; only order one is needed, so
the statement is weakened with `ContDiffOn.of_le`.  The construction-area operator
`Work.Construction.L12` is the elliptic-area operator `Work.Elliptic.L12`
(`Work.FTS.H2.constructionL12_eq_ellipticL12`). -/
theorem l12ContDiffOnOpen : ∀ α ∈ Set.Ioc 0 1, ∀ f : ℝ → ℝ → ℝ,
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 7 f →
    ContDiffOn ℝ 1 (fun z => Work.Construction.L12 f z) (Set.Ioi 0) := by
  intro α hα f hF hmem
  have h := Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 7 f hα.1 hα.2 hF hmem
    (by norm_num)
  rw [Work.FTS.H2.constructionL12_eq_ellipticL12 f]
  exact h.of_le (by norm_num)

end Work.FTS.StrongPersist.H6Pair6Aux.T5bAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.vSliceAux.sliceZAgmon =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.vSliceAux

theorem sliceZAgmon : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ),
    0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
    Work.FTS.EllipticEst.SmoothOpen f →
    MeasureTheory.IntegrableOn (fun s => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed 0 1 f s θ) ^ 2 * (Work.Spaces.w s) ^ 2) Work.Spaces.Iz →
    MeasureTheory.IntegrableOn (fun s => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed 1 1 f s θ) ^ 2 * (Work.Spaces.w s) ^ 2) Work.Spaces.Iz →
    (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed 0 1 f z θ) ^ 2
      ≤ 2 * ∫ s in Work.Spaces.Iz, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed 1 1 f s θ) ^ 2 * (Work.Spaces.w s) ^ 2 := by
  intro α f z θ hz hθ hF hin0 hin1
  -- `sin(2θ) > 0`, so the angular weight `c := sin(2θ)^{-γ}` is a positive constant
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  set c := (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) with hcdef
  have hc : 0 < c := Real.rpow_pos_of_pos hsin _
  have hcne : c ≠ 0 := ne_of_gt hc
  -- the two integrability hypotheses, with the constant `c` factored out
  have hA : MeasureTheory.IntegrableOn
      (fun x => (Work.Spaces.mixed 0 1 f x θ) ^ 2 * (Work.Spaces.w x) ^ 2) Work.Spaces.Iz := by
    have h0 : MeasureTheory.IntegrableOn
        (fun x => c * ((Work.Spaces.mixed 0 1 f x θ) ^ 2 * (Work.Spaces.w x) ^ 2))
        Work.Spaces.Iz := by
      refine hin0.congr_fun ?_ measurableSet_Ici
      intro x hx; ring
    have h1 : MeasureTheory.IntegrableOn
        (fun x => c⁻¹ * (c * ((Work.Spaces.mixed 0 1 f x θ) ^ 2 * (Work.Spaces.w x) ^ 2)))
        Work.Spaces.Iz := h0.const_mul c⁻¹
    refine h1.congr_fun ?_ measurableSet_Ici
    intro x hx
    show c⁻¹ * (c * (Work.Spaces.mixed 0 1 f x θ ^ 2 * Work.Spaces.w x ^ 2))
      = Work.Spaces.mixed 0 1 f x θ ^ 2 * Work.Spaces.w x ^ 2
    rw [← mul_assoc, inv_mul_cancel₀ hcne, one_mul]
  have hB : MeasureTheory.IntegrableOn
      (fun x => (x * Work.Spaces.pz (Work.Spaces.DthIter 1 f) x θ * Work.Spaces.w x) ^ 2)
      Work.Spaces.Iz := by
    have h0 : MeasureTheory.IntegrableOn
        (fun x => c * ((Work.Spaces.mixed 1 1 f x θ) ^ 2 * (Work.Spaces.w x) ^ 2))
        Work.Spaces.Iz := by
      refine hin1.congr_fun ?_ measurableSet_Ici
      intro x hx; ring
    have h1 : MeasureTheory.IntegrableOn
        (fun x => c⁻¹ * (c * ((Work.Spaces.mixed 1 1 f x θ) ^ 2 * (Work.Spaces.w x) ^ 2)))
        Work.Spaces.Iz := h0.const_mul c⁻¹
    refine h1.congr_fun ?_ measurableSet_Ici
    intro x hx
    show c⁻¹ * (c * (Work.Spaces.mixed 1 1 f x θ ^ 2 * Work.Spaces.w x ^ 2))
      = (x * Work.Spaces.pz (Work.Spaces.DthIter 1 f) x θ * Work.Spaces.w x) ^ 2
    rw [← mul_assoc, inv_mul_cancel₀ hcne, one_mul]
    rw [show x * Work.Spaces.pz (Work.Spaces.DthIter 1 f) x θ
        = Work.Spaces.mixed 1 1 f x θ from rfl, mul_pow]
  -- the radial Hardy bound on the single angular slice `x ↦ D_θ f (x,θ)`
  have hmain := Work.FTS.StrongPersist.N6Trans.SixAux.zslice6_hardy
    (h := fun x => Work.Spaces.mixed 0 1 f x θ)
    (h' := fun x => Work.Spaces.pz (Work.Spaces.DthIter 1 f) x θ)
    hz (fun x hx => (hF.DthIter 1).hasDerivAt_slice hθ hx)
    (((hF.DthIter 1).curry_z hθ).continuousOn)
    ((((hF.DthIter 1).pz).curry_z hθ).continuousOn) hA hB
  have hIntEq : (∫ x in Work.Spaces.Iz,
        (x * Work.Spaces.pz (Work.Spaces.DthIter 1 f) x θ * Work.Spaces.w x) ^ 2)
      = ∫ x in Work.Spaces.Iz,
          (Work.Spaces.mixed 1 1 f x θ) ^ 2 * (Work.Spaces.w x) ^ 2 := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun x hx => ?_)
    rw [show x * Work.Spaces.pz (Work.Spaces.DthIter 1 f) x θ
        = Work.Spaces.mixed 1 1 f x θ from rfl, mul_pow]
  rw [hIntEq] at hmain
  have hsplit : (∫ s in Work.Spaces.Iz,
        (c * (Work.Spaces.mixed 1 1 f s θ) ^ 2) * (Work.Spaces.w s) ^ 2)
      = c * ∫ s in Work.Spaces.Iz,
          (Work.Spaces.mixed 1 1 f s θ) ^ 2 * (Work.Spaces.w s) ^ 2 := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun x hx => by ring)
  calc c * (Work.Spaces.mixed 0 1 f z θ) ^ 2
      ≤ c * (2 * ∫ s in Work.Spaces.Iz,
          (Work.Spaces.mixed 1 1 f s θ) ^ 2 * (Work.Spaces.w s) ^ 2) :=
        mul_le_mul_of_nonneg_left hmain (le_of_lt hc)
    _ = 2 * ∫ s in Work.Spaces.Iz,
          (c * (Work.Spaces.mixed 1 1 f s θ) ^ 2) * (Work.Spaces.w s) ^ 2 := by
        rw [hsplit]; ring

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.vSliceAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.vSliceAux.slotRadialIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `vSliceAux/slotRadialIntegrable`: the two mixed slots are radially integrable

The `ℋ⁴`-integrand of Elgindi's weighted space is the finite sum of the squares of the
weighted derivatives `D_z^i f · w/ sin(2θ)^{η/2}` and `D_z^j D_θ^i f · W` (`i ≥ 1`), where
`W = w · sin(2θ)^{-γ/2}`.  Hence *each* of its summands is integrable wherever the whole
`HkIntegrand` is, being a nonnegative summand of it.

This file records the two slots needed by the angular Agmon/Poincaré inequality on the
`θ`-slice, namely `(i, j) = (1, 0)` and `(1, 1)`: for every interior angle `θ`,
`IntegrableOn (fun s => HkIntegrand α 4 f s θ) Iz` implies

  `IntegrableOn (fun s => sin(2θ)^{-γ} · (D_z^j D_θ f s θ)² · w(s)²) Iz`,   `j ≤ 3`,

since on the open interval the `(i,j) = (1,j)` summand of the integrand is *exactly*
`sin(2θ)^{-γ} · (D_z^j D_θ f)² · w²` (`sq_rpow_neg` undoes the half exponent of `wTheta`).
The a.e. strong measurability of that radial slice comes from the joint continuity of
`(z, θ) ↦ D_z^j D_θ f · W` on the open quadrant (`SmoothOpen` supplies it, and only `z > 0`,
`0 < θ < π/2` are needed; the missing point `z = 0` is null).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.vSliceAux

set_option autoImplicit false

/-! ## Elementary facts about the weights -/

/-- `(s^{-γ/2})² = s^{-γ}` for `s > 0`: the half exponent of `wTheta` is undone by squaring. -/
private lemma sq_rpow_neg (s γ : ℝ) (hs : 0 < s) : (s ^ (-(γ / 2))) ^ 2 = s ^ (-γ) := by
  rw [← Real.rpow_two, ← Real.rpow_mul (le_of_lt hs)]
  congr 1
  ring

/-- The weight `W = w · sin(2θ)^{-γ/2}` is continuous on the open quadrant (both `z > 0` and
`θ ∈ (0,π/2)` are needed: `w` is finite at `z > 0` and `sin(2θ) > 0` at interior angles). -/
private lemma continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      Work.FTS.EllipticEst.Q0 := by
    have hfun2 : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun2]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2)
      (fun p hp => pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1))
  exact hw.mul
    (((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp))))

/-- The `z`-slice at a fixed interior angle of a function continuous on the open quadrant
`Q0 = (0,∞) × (0,π/2)` is a.e. strongly measurable for `volume.restrict Iz` (the omitted
point is `z = 0`, a null set). -/
private lemma aesm_zslice_of_continuousOn_Q0 (G : ℝ × ℝ → ℝ)
    (hG : ContinuousOn G Work.FTS.EllipticEst.Q0) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    AEStronglyMeasurable (fun z : ℝ => G (z, θ)) (volume.restrict Work.Spaces.Iz) := by
  have hIz : (volume.restrict Work.Spaces.Iz : Measure ℝ) = volume.restrict (Set.Ioi (0 : ℝ)) :=
    (MeasureTheory.Measure.restrict_congr_set
      (show Set.Ioi (0 : ℝ) =ᵐ[volume] Work.Spaces.Iz
        from MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ)))).symm
  rw [hIz]
  exact (hG.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun z hz => ⟨hz, hθ⟩)).aestronglyMeasurable measurableSet_Ioi

/-- On the open interval the squared weighted mixed slot is `sin(2θ)^{-γ} · (D_z^j D_θ^i f)² · w²`:
this is the `(i,j)`-summand of `HkIntegrand` written with the angular weight separated off. -/
private lemma slot_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (j i : ℕ) (θ : ℝ)
    (hs : 0 < Real.sin (2 * θ)) (z : ℝ) :
    (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, mul_pow,
    sq_rpow_neg (Real.sin (2 * θ)) (Work.Spaces.gam α) hs]
  ring

/-! ## The single mixed slot -/

/-- **A single mixed slot of `HkIntegrand α 4` is radially integrable.**  If the `θ`-slice of
the `ℋ⁴`-integrand is integrable on `Iz`, then so is the `(i,j)`-slot
`sin(2θ)^{-γ} · (D_z^j D_θ^i f)² · w²` for every `i ≥ 1`, `i + j ≤ 4`. -/
private lemma slot_integrable {α : ℝ} {f : ℝ → ℝ → ℝ} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hF : Work.FTS.EllipticEst.SmoothOpen f)
    (hint : MeasureTheory.IntegrableOn
      (fun s => Work.Spaces.HkIntegrand α 4 f s θ) Work.Spaces.Iz)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    MeasureTheory.IntegrableOn (fun s => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.mixed j i f s θ) ^ 2 * (Work.Spaces.w s) ^ 2) Work.Spaces.Iz := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  -- identify the slot with the `(i,j)`-summand of the integrand
  have hEq : (fun s : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed j i f s θ) ^ 2 * (Work.Spaces.w s) ^ 2)
      = fun s : ℝ => (Work.Spaces.mixed j i f s θ * Work.Spaces.Wt α s θ) ^ 2 := by
    funext s
    exact (slot_eq α f j i θ hs s).symm
  rw [hEq]
  refine MeasureTheory.Integrable.mono' hint
    ((aesm_zslice_of_continuousOn_Q0 _
      (((hF.mixed j i).continuousOn).mul (continuousOn_Wt_Q0 α)) hθ).pow 2) ?_
  filter_upwards with s
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 f s θ i j hi hij

/-! ## The requested statement -/

theorem slotRadialIntegrable : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (θ : ℝ),
    θ ∈ Set.Ioo 0 (Real.pi / 2) →
    Work.FTS.EllipticEst.SmoothOpen f →
    MeasureTheory.IntegrableOn (fun s => Work.Spaces.HkIntegrand α 4 f s θ) Work.Spaces.Iz →
      MeasureTheory.IntegrableOn (fun s => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed 0 1 f s θ) ^ 2 * (Work.Spaces.w s) ^ 2) Work.Spaces.Iz ∧
      MeasureTheory.IntegrableOn (fun s => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed 1 1 f s θ) ^ 2 * (Work.Spaces.w s) ^ 2) Work.Spaces.Iz := by
  intro α f θ hθ hF hint
  exact ⟨slot_integrable hθ hF hint 0 1 le_rfl (by norm_num),
    slot_integrable hθ hF hint 1 1 le_rfl (by norm_num)⟩

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.vSliceAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.HardSlotAux.SlotIntegrableHonest =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `SlotIntegrableHonest` — the `θ`-integrability of a single `ℋ⁴`-slot

The hard slots of the `N6` transport analysis are the functions

  `θ ↦ (D_z^b D_θ^a g z θ)² · sin(2θ)^{-q}`,   `a + b = 4`,

with the exponent `q ∈ {0, η, γ}` (`η = 99/100`, `γ = 1 + α/10`).  This file shows that each of
them is integrable on `Iθ = [0, π/2]` at every `z > 0`, for a datum `g` which is `C^∞` on the
*open* quadrant (`Work.FTS.EllipticEst.SmoothOpen`) and lies in `ℋ⁴` (`Work.Spaces.HkMem α 4 g`).

The mathematical content is one line: every one of these slots is a summand of the (integrable)
`ℋ⁴`-integrand `Work.Spaces.HkIntegrand α 4 g z ·`, with the angular weight `sin(2θ)^{-γ}`
being the *strongest* one (`sin(2θ)^{-η} ≤ sin(2θ)^{-γ}` and `1 ≤ sin(2θ)^{-η}` on `Iθ` since
`sin(2θ) ≤ 1` and `η < 1 < γ`).  The `η`-slot `(D_z⁴g)² sin(2θ)^{-η}` is the light-weighted
summand `Work.FTS.EllipticEst.integrableOn_zSummand` of `OpenQDefs`.

The whole business is therefore bookkeeping of the two weights; the only smoothness input used is
the *continuity on the open quadrant* needed for a.e. strong measurability of the slots (the
`SmoothQuad` version of these facts lives in `Work.FTS.H2.HQ.Glue` / `Work.H2.T1Q.SlotBoundQ`,
which we cannot use since our datum is only smooth on `Ioi 0`, not on `Ioi (-1)`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.HardSlotAux

set_option maxHeartbeats 800000

/-- The restriction of Lebesgue measure to `Iθ = [0, π/2]` agrees with the restriction to the
open interval `(0, π/2)`: the two endpoints are null. -/
theorem restrict_Iθ_eq_restrict_Ioo :
    volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
  (MeasureTheory.Measure.restrict_congr_set (by
    show Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Work.Spaces.Iθ
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Ioo_ae_eq_Icc)).symm

/-- `sin(2θ)` is positive on the open interval. -/
theorem sin_two_pos_of_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- **Monotonicity of the slot weight.**  On the open interval the map
`p ↦ sin(2θ)^{-p}` is decreasing (the base lies in `(0,1)`), so a smaller exponent gives a
smaller weight: this is what makes the `η`- and `0`-slots dominated by the `γ`-slots. -/
theorem rpow_sin_two_neg_le {q γ : ℝ} (hq : q ≤ γ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Real.sin (2 * θ)) ^ (-q) ≤ (Real.sin (2 * θ)) ^ (-γ) :=
  Real.rpow_le_rpow_of_exponent_ge (sin_two_pos_of_Ioo hθ) (Real.sin_le_one _) (by linarith)

/-- The two endpoints of `Iθ` are null for the restricted measure. -/
theorem ae_restrict_Iθ_of_forall_mem_Ioo {p : ℝ → Prop}
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), p θ) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), p θ := by
  have h1 : ∀ᵐ θ ∂(volume.restrict (Set.Ioo (0 : ℝ) (π / 2))), p θ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo h
  rwa [← restrict_Iθ_eq_restrict_Ioo] at h1

/-- The `θ`-slice of a function which is `C^∞` on the open quadrant is continuous on the open
angular interval. -/
theorem continuousOn_slice_of_smoothOpen {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ : ℝ => g z θ) (Set.Ioo (0 : ℝ) (π / 2)) :=
  hg.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun θ hθ => ⟨hz, hθ⟩)

/-- The slot weight `θ ↦ sin(2θ)^p` is continuous on the open angular interval. -/
theorem continuousOn_sin_two_rpow (p : ℝ) :
    ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) (Set.Ioo (0 : ℝ) (π / 2)) :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
    (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos_of_Ioo hθ)))

theorem continuousOn_Wt_slice (α z : ℝ) :
    ContinuousOn (fun θ : ℝ => Work.Spaces.Wt α z θ) (Set.Ioo (0 : ℝ) (π / 2)) := by
  have hfun : (fun θ : ℝ => Work.Spaces.Wt α z θ)
      = fun θ : ℝ => Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) :=
    funext fun _ => rfl
  rw [hfun]
  exact continuousOn_const.mul (continuousOn_sin_two_rpow _)


end Work.FTS.StrongPersist.N6Trans.HardSlotAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.hardyZQ_mixed_slice_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The radial Hardy inequality for the angular slices of the open class

For `f` of class `C^∞` on the *open* quadrant (`Work.FTS.EllipticEst.SmoothOpen f`) with
`Work.Spaces.DecayAll 4 f`, and for every interior angle `σ ∈ (0, π/2)`,

  `(D_z^b D_θ^a f(z,σ))² ≤ ∫_0^∞ (D_z^{b+1} D_θ^a f(s,σ))² w(s)² ds`   for every `z > 0`.

This is the interior (open-quadrant) radial Hardy inequality: apply
`Work.FTS.H2.HQ.HardyZQ` to the `z`-slice `v s := D_z^b D_θ^a f(s,σ)`, whose `z`-derivative is
`∂_z v s = ∂_z (D_z^b D_θ^a f)(s,σ)` and whose `D_z`-derivative is
`s ∂_z v s = D_z^{b+1} D_θ^a f(s,σ)`, exactly the integrand of the target.  The three
hypotheses of `HardyZQ` are the slice smoothness (`SmoothOpen f`), the decay of the slice at
`+∞` (the `DecayMixed`-half of `DecayAll 4 f`, using `a + b ≤ 4`) and the integrability
hypothesis `hint` (transported along the definitional identity above).
-/

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongPersist.N6Trans.OpenTwins

theorem hardyZQ_mixed_slice_open (f : ℝ → ℝ → ℝ)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hdec : Work.Spaces.DecayAll 4 f)
    (b a : ℕ) (hab : a + b ≤ 4) {σ : ℝ} (hσ : σ ∈ Set.Ioo (0 : ℝ) (π / 2))
    (hint : MeasureTheory.IntegrableOn
      (fun s => (Work.Spaces.mixed (b + 1) a f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
      Work.Spaces.Iz) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      (Work.Spaces.mixed b a f z σ) ^ 2
        ≤ ∫ s in Work.Spaces.Iz,
            (Work.Spaces.mixed (b + 1) a f s σ) ^ 2 * (Work.Spaces.w s) ^ 2 := by
  intro z hz
  -- the slice `s ↦ D_z^b D_θ^a f s σ` is `C¹` on `(0,∞)`
  have hslicecont : ContDiffOn ℝ 1 (fun s : ℝ => Work.Spaces.mixed b a f s σ)
      (Set.Ioi (0 : ℝ)) :=
    ((hf.mixed b a).curry_z hσ).of_le (by simp [Work.Stability.smoothOrder])
  -- the slice decays at `+∞`
  have hdecs : Tendsto (fun s : ℝ => Work.Spaces.mixed b a f s σ) atTop (nhds 0) :=
    hdec.2 a b hab σ ⟨le_of_lt hσ.1, le_of_lt hσ.2⟩
  -- integrability of `(s ∂_s v)² w²`, which is `hint` up to unfolding `D_z`
  have hints : MeasureTheory.IntegrableOn
      (fun s => (s * deriv (fun s' : ℝ => Work.Spaces.mixed b a f s' σ) s) ^ 2
        * (Work.Spaces.w s) ^ 2) Work.Spaces.Iz := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
      Work.Spaces.Dz, Work.Spaces.pz, mul_comm, mul_left_comm, mul_assoc] using hint
  have h := Work.FTS.H2.HQ.HardyZQ (fun s : ℝ => Work.Spaces.mixed b a f s σ)
    hslicecont hdecs hints z hz
  simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
    Work.Spaces.Dz, Work.Spaces.pz, mul_comm, mul_left_comm, mul_assoc] using h

end Work.FTS.StrongPersist.N6Trans.OpenTwins
end
-- ===== merged: Submission.Work.FTS.StrongPersist.c2m_L12Fstar_W6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The radial pointwise bound, at every order `k` -/

/-- The weighted `z`-derivative bound for the explicit function `c2m(θ)·2α/(1+z)`:
`|(z+1)^k ∂_z^k (c2m(θ)·2α/(1+z))| ≤ 4 α k!` for `z ≥ 0`, **every** `k : ℕ` and every
`α > 0`.  (The level-four statement `FstarPkg.c2mInv_points` carried the extra hypotheses
`α ≤ 1` and `k ≤ 4`; its proof used neither.) -/
theorem c2mSix_inv_points (α z θ : ℝ) (hα : 0 < α) (hz : 0 ≤ z) (k : ℕ) :
    |(z + 1) ^ k * Work.Spaces.pzIter k
        (fun z θ => Work.Construction.c2m θ * (2 * α / (1 + z))) z θ|
      ≤ 4 * α * (k.factorial : ℝ) := by
  have hz1 : -1 < z := by linarith
  have hα2 : (0 : ℝ) ≤ 2 * α := by linarith
  have hc2m : |Work.Construction.c2m θ| ≤ 2 :=
    Work.FTS.Nonlinear.FstarPkg.abs_c2m_le_two θ
  rw [Work.FTS.Nonlinear.FstarPkg.pzIter_c2m_inv α k z θ hz1]
  rw [show (z + 1) ^ k *
        (Work.Construction.c2m θ * (2 * α * Work.FTS.Nonlinear.FstarPkg.nInvClosed k z))
      = Work.Construction.c2m θ *
        (2 * α * ((z + 1) ^ k * Work.FTS.Nonlinear.FstarPkg.nInvClosed k z)) by ring]
  rw [abs_mul, abs_mul, abs_of_nonneg hα2]
  calc |Work.Construction.c2m θ| *
        (2 * α * |(z + 1) ^ k * Work.FTS.Nonlinear.FstarPkg.nInvClosed k z|)
      ≤ 2 * (2 * α * (k.factorial : ℝ)) := by
        apply mul_le_mul hc2m
        · exact mul_le_mul_of_nonneg_left
            (Work.FTS.Nonlinear.FstarPkg.nInvClosed_weighted k z hz) hα2
        · exact mul_nonneg hα2 (abs_nonneg _)
        · norm_num
    _ = 4 * α * (k.factorial : ℝ) := by ring

/-! ## The mixed pointwise bound at order six -/

/-- The mixed weighted bound for the explicit function `c2m(θ)·2α/(1+z)` at order six:
`(z+1)^k ∂_z^k D_θ^j (c2m(θ)·2α/(1+z)) · sin(2θ)^{-α/5}/(α+sin 2θ)` is bounded by `C α`,
uniformly for `0 < α ≤ 1`, `z ≥ 0`, `θ ∈ Iθ`, `1 ≤ j ≤ 6`, `k ≤ 6`. -/
theorem c2mSix_inv_mixed :
    ∃ C : ℝ, 0 < C ∧ ∀ (α z θ : ℝ), 0 < α → α ≤ 1 → 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      ∀ (j k : ℕ), 1 ≤ j → j ≤ 6 → k ≤ 6 →
      |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j
          (fun z θ => Work.Construction.c2m θ * (2 * α / (1 + z)))) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ C * α := by
  obtain ⟨C0, hC0pos, hC0⟩ := dthU_c2m_bound6
  refine ⟨max C0 1 * 1440, ?_, ?_⟩
  · have h : (0 : ℝ) < max C0 1 := lt_max_of_lt_right one_pos
    positivity
  intro α z θ hα hα1 hz hθ j k hj1 hj6 hk
  set s : ℝ := Real.sin (2 * θ) with hs
  set B : ℝ → ℝ := fun z => 2 * α / (1 + z) with hB
  set g : ℝ → ℝ := (Work.Spaces.dthU^[j] Work.Construction.c2m) with hg
  have hDth : Work.Spaces.DthIter j (fun z θ => Work.Construction.c2m θ * (2 * α / (1 + z)))
      = fun z θ => g θ * B z := by
    funext z θ
    exact Work.Spaces.DthIter_decomp j Work.Construction.c2m B z θ
  rw [hDth]
  rw [Work.Spaces.pzIter_decomp k g B z θ]
  have hs0 : 0 ≤ s := by
    rw [hs]
    exact Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [(Set.mem_Icc.mp hθ).1], by linarith [(Set.mem_Icc.mp hθ).2, Real.pi_pos]⟩
  have hs1 : s ≤ 1 := by rw [hs]; exact Real.sin_le_one _
  have hA : |g θ| ≤ max C0 1 * s ^ 2 := by
    rw [hg]
    exact le_trans (hC0 j hj1 hj6 θ)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg s))
  have hBnd : |(z + 1) ^ k * deriv^[k] B z| ≤ 2 * α * (k.factorial : ℝ) := by
    rw [hB]
    exact Work.FTS.Nonlinear.FstarPkg.c2mInv_radial α hα k z hz
  have hXnn : 0 ≤ s ^ (-(α / 5)) / (α + s) :=
    div_nonneg (Real.rpow_nonneg hs0 _) (by linarith)
  have hW : s ^ 2 * (s ^ (-(α / 5)) / (α + s)) ≤ 1 := by
    have := Work.FTS.Nonlinear.FstarPkg.sinWeight_le_one α s hα hα1 hs0 hs1
    rwa [mul_div_assoc] at this
  have hfact : (k.factorial : ℝ) ≤ 720 := by
    interval_cases k <;> norm_num
  rw [mul_div_assoc]
  rw [show (z + 1) ^ k * (g θ * deriv^[k] B z)
      = g θ * ((z + 1) ^ k * deriv^[k] B z) by ring]
  rw [abs_mul, abs_mul, abs_of_nonneg hXnn]
  have h1 : |g θ| * |(z + 1) ^ k * deriv^[k] B z| * (s ^ (-(α / 5)) / (α + s))
      ≤ (max C0 1 * s ^ 2) * (2 * α * (k.factorial : ℝ))
        * (s ^ (-(α / 5)) / (α + s)) := by
    apply mul_le_mul_of_nonneg_right _ hXnn
    exact mul_le_mul hA hBnd (abs_nonneg _) (by positivity)
  refine le_trans h1 ?_
  have h2 : (max C0 1 * s ^ 2) * (2 * α * (k.factorial : ℝ)) * (s ^ (-(α / 5)) / (α + s))
      = 2 * (max C0 1) * α * (k.factorial : ℝ)
        * (s ^ 2 * (s ^ (-(α / 5)) / (α + s))) := by ring
  rw [h2]
  have h3 : 2 * (max C0 1) * α * (k.factorial : ℝ) * (s ^ 2 * (s ^ (-(α / 5)) / (α + s)))
      ≤ 2 * (max C0 1) * α * (k.factorial : ℝ) * 1 := by
    apply mul_le_mul_of_nonneg_left hW
    have h : (0 : ℝ) < max C0 1 := lt_max_of_lt_right one_pos
    positivity
  have h4 : 2 * (max C0 1) * α * (k.factorial : ℝ) * 1 ≤ 2 * (max C0 1) * α * 720 := by
    have hnn : 0 ≤ 2 * (max C0 1) * α := by
      have h : (0 : ℝ) < max C0 1 := lt_max_of_lt_right one_pos
      positivity
    have := mul_le_mul_of_nonneg_left hfact hnn
    simpa using this
  have h5 : 2 * (max C0 1) * α * 720 = (max C0 1 * 1440) * α := by ring
  linarith [h3, h4, h5]

/-! ## The transfer of the two bounds to `c2m · L₁₂(F_*)` -/



/-! ## The universal constant and the sum arithmetic -/

/-- The universal constant of the level-six estimate, given the constant `K` of the mixed
pointwise bound: the `z`-sum `∑_{k<7} 4·k!` plus the 49 mixed summands (each `≤ K α`). -/
noncomputable def c2mSixCW (K : ℝ) : ℝ :=
  (∑ k ∈ Finset.range 7, 4 * (k.factorial : ℝ)) + 49 * K + 1

theorem c2mSixCW_pos (K : ℝ) (hK : 0 < K) : 0 < c2mSixCW K := by
  have h1 : 0 ≤ ∑ k ∈ Finset.range 7, 4 * (k.factorial : ℝ) :=
    Finset.sum_nonneg fun k _ => by positivity
  have h2 : 0 < 49 * K := by linarith
  rw [c2mSixCW]
  linarith

/-- The double sum of a constant over `range 7 × range 7` is `49 c`. -/
theorem c2mSix_sum_const_mul (c : ℝ) :
    (∑ _j ∈ Finset.range 7, ∑ _k ∈ Finset.range 7, c) = 49 * c := by
  simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- The `z`-sum, with the constant `α` pulled out. -/
theorem c2mSix_sum_fact_mul (α : ℝ) :
    (∑ k ∈ Finset.range 7, 4 * α * (k.factorial : ℝ))
      = (∑ k ∈ Finset.range 7, 4 * (k.factorial : ℝ)) * α := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ## The two halves of the `𝒲^{6,∞}`-bound -/



/-! ## The requested statement -/


end Work.FTS.StrongPersist
end
end
-- ===== merged: Submission.Work.FTS_LocDatum3a.FM_jet8safe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_LocDatum3a

set_option autoImplicit false

/- The auxiliary lemmas of the jet bound, in their own namespace so that the *local* copy of
`Gker` cannot be confused with the (unimportable) `Work.FTS.LocData.Gker`. -/
namespace LocFM8s

set_option maxHeartbeats 1600000

/-! ## The local closed forms of the iterated derivatives -/

/-- **The closed form of the `k`-th derivative of the profile** `F_* (z) = 2z/(1+z)²`:

  `Gk k z = 2·(-1)^k·k!·(z - k)/(1+z)^(k+2)`.

For `k = 0` this is `F_*` itself; in general `deriv^[k] F_* = Gk k` off `z = -1`.  This is a
*local* copy of `Work.FTS.LocData.Gker`, which lives in the unimportable `FstarAux`. -/
noncomputable def Gk (k : ℕ) (z : ℝ) : ℝ :=
  2 * (-1 : ℝ) ^ k * (k.factorial : ℝ) * (z - k) / (1 + z) ^ (k + 2)

@[simp] theorem Gk_apply (k : ℕ) (z : ℝ) :
    Gk k z = 2 * (-1 : ℝ) ^ k * (k.factorial : ℝ) * (z - k) / (1 + z) ^ (k + 2) := rfl

/-- `Gk 0` is the profile itself. -/
theorem Gk_zero (z : ℝ) : Gk 0 z = Work.FM.Fstar z := by
  simp only [Gk_apply, Work.FM.Fstar]
  norm_num

/-- **The one-step recursion `deriv (Gk k) = Gk (k+1)` off the pole `z = -1`**, by the
quotient/product rule on `(2·(-1)^k·k!·(z-k)) / (1+z)^(k+2)`. -/
theorem hasDerivAt_Gk (k : ℕ) (z : ℝ) (hz : 1 + z ≠ 0) :
    HasDerivAt (Gk k) (Gk (k + 1) z) z := by
  -- derivative of the numerator `2·(-1)^k·k!·(w - k)`
  have hnum : HasDerivAt (fun w : ℝ => 2 * (-1:ℝ)^k * (k.factorial:ℝ) * (w - k))
      (2 * (-1:ℝ)^k * (k.factorial:ℝ)) z := by
    have h : HasDerivAt (fun w : ℝ => w - (k:ℝ)) 1 z := by
      simpa using (hasDerivAt_id z).sub_const (k:ℝ)
    have h2 := h.const_mul (2 * (-1:ℝ)^k * (k.factorial:ℝ))
    simpa using h2
  -- derivative of the denominator `(1 + w)^(k+2)`
  have hden2 : HasDerivAt (fun w : ℝ => (1 + w) ^ (k + 2))
      (((k+2 : ℕ) : ℝ) * (1+z)^(k+1)) z := by
    have h : HasDerivAt (fun w : ℝ => 1 + w) 1 z := by
      simpa using (hasDerivAt_id z).const_add 1
    have h2 := h.pow (k+2)
    rw [show (fun w : ℝ => (1 + w) ^ (k + 2)) = (fun w : ℝ => 1 + w) ^ (k+2) from by
          funext w; simp [Pi.pow_apply]]
    simpa using h2
  have hden : (1+z)^(k+2) ≠ 0 := pow_ne_zero _ hz
  have hdiv := hnum.div hden2 hden
  -- the value produced by the quotient rule is `Gk (k+1) z`
  have hval : (2 * (-1:ℝ)^k * (k.factorial:ℝ) * (1+z)^(k+2)
        - 2 * (-1:ℝ)^k * (k.factorial:ℝ) * (z - k) * (((k+2:ℕ):ℝ) * (1+z)^(k+1)))
        / ((1+z)^(k+2))^2 = Gk (k+1) z := by
    rw [Gk_apply]
    rw [show (k+1)+2 = k+3 by omega]
    -- rewrite every power of `1 + z` through `(1+z)^(k+1)`
    have h1 : (1 + z) ^ (k + 2) = (1 + z) ^ (k + 1) * (1 + z) := by
      rw [show k + 2 = (k+1) + 1 by omega, pow_succ]
    have h2 : (1 + z) ^ (k + 3) = (1 + z) ^ (k + 1) * (1 + z) ^ 2 := by
      rw [show k + 3 = (k+1) + 2 by omega, pow_add]
    have h3 : ((1 + z) ^ (k + 2)) ^ 2 = ((1 + z) ^ (k + 1)) ^ 2 * (1 + z) ^ 2 := by
      rw [h1, mul_pow]
    rw [h3, h1, h2]
    have hu : (1+z)^(k+1) ≠ 0 := pow_ne_zero _ hz
    have ht : (1+z) ≠ 0 := hz
    field_simp
    rw [show (-1:ℝ)^(k+1) = -(-1)^k by rw [pow_succ]; ring]
    rw [show ((k+1).factorial : ℝ) = ((k:ℝ)+1) * (k.factorial:ℝ) by
          rw [Nat.factorial_succ]; push_cast; ring]
    push_cast
    ring
  exact hdiv.congr_deriv hval

/-! ## The `θ`-variable is a dummy -/

/-- For a function of `z` alone, every `D_z`-iterate is independent of `θ`. -/
theorem DzIter_zonly_theta_indep (Φ : ℝ → ℝ) (b : ℕ) (z θ θ' : ℝ) :
    Work.Spaces.DzIter b (fun z _ => Φ z) z θ = Work.Spaces.DzIter b (fun z _ => Φ z) z θ' := by
  induction b generalizing z with
  | zero => rfl
  | succ b ih =>
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [show (fun z' => Work.Spaces.DzIter b (fun z _ => Φ z) z' θ)
          = (fun z' => Work.Spaces.DzIter b (fun z _ => Φ z) z' θ') from
        funext fun z' => ih z']

/-- The iterated plain derivative of a function of `z` alone, as a `pzIter`. -/
theorem pzIter_zonly_eq_deriv_iter (Φ : ℝ → ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter k (fun z _ => Φ z) z θ = deriv^[k] Φ z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      simp only [Work.Spaces.pzIter_succ, Work.Spaces.pz]
      congr 1
      funext z'
      exact ih z'

/-! ## The closed forms of the iterated derivatives -/

/-- **The `k`-th plain derivative of the profile is `Gk k`**: the one-step recursion
`deriv (Gk k) = Gk (k+1)` started at `Gk 0 = F_*`. -/
theorem deriv_iter_Fstar_eq_Gk :
    ∀ k : ℕ, ∀ z ∈ Set.Ioi (-1),
      deriv^[k] (fun z => Work.FM.Fstar z) z = Gk k z := by
  intro k
  induction k with
  | zero => intro z _; exact (Gk_zero z).symm
  | succ k ih =>
      intro z hz
      have hlt : (-1 : ℝ) < z := hz
      have hev : (fun w => deriv^[k] (fun z => Work.FM.Fstar z) w)
          =ᶠ[𝓝 z] Gk k := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
        exact ih w hw
      rw [Function.iterate_succ_apply', Filter.EventuallyEq.deriv_eq hev]
      exact (hasDerivAt_Gk k z (by linarith)).deriv

/-- The `pzIter` of the profile is the closed form `Gk`. -/
theorem pzIter_Fstar_eq_Gk (k : ℕ) {z : ℝ} (hz : z ∈ Set.Ioi (-1)) (θ : ℝ) :
    Work.Spaces.pzIter k (fun z _ => Work.FM.Fstar z) z θ = Gk k z := by
  rw [pzIter_zonly_eq_deriv_iter]
  exact deriv_iter_Fstar_eq_Gk k z hz

/-- The `z`-slices of the profile are smooth on `(-1,∞)` (the only pole of `2z/(1+z)²` is
`z = -1`).  This is the smoothness hypothesis of `DzIter_eq_sum_scoef`. -/
theorem contDiffOn_Fstar : ContDiffOn ℝ ⊤ (fun z : ℝ => Work.FM.Fstar z) (Set.Ioi (-1)) := by
  have hnum : ContDiffOn ℝ ⊤ (fun z : ℝ => 2 * z) (Set.Ioi (-1)) :=
    contDiffOn_const.mul contDiffOn_id
  have hden : ContDiffOn ℝ ⊤ (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi (-1)) :=
    (contDiffOn_const.add contDiffOn_id).pow 2
  have hne : ∀ z : ℝ, z ∈ Set.Ioi (-1) → (1 + z) ^ 2 ≠ 0 := by
    intro z hz
    have hlt : (-1 : ℝ) < z := hz
    exact pow_ne_zero 2 (by linarith)
  refine (hnum.div hden hne).congr ?_
  intro z _
  simp only [Pi.div_apply, Work.FM.Fstar]

/-! ## The far-field decay of the closed forms -/

/-- **The far-field decay of `z^k·Gk k z`, at every order `k`.**  For `z ≥ 1` and all `k`,

  `|z^k · Gk k z| ≤ 2·k!·(k+1)/z`.

Since `Gk k z = 2(-1)^k k!(z-k)/(1+z)^(k+2)` and `(1+z)^(k+2) ≥ z^(k+2)`, while
`|z - k| ≤ (k+1)z` for `z ≥ 1`, this is immediate arithmetic. -/
theorem abs_zpow_mul_Gk_le_all (k : ℕ) {z : ℝ} (hz : 1 ≤ z) :
    |z ^ k * Gk k z| ≤ 2 * (k.factorial : ℝ) * ((k : ℝ) + 1) / z := by
  have hz0 : (0 : ℝ) < z := by linarith
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  have hfac : (0 : ℝ) ≤ (k.factorial : ℝ) := by positivity
  have hzpow : (0 : ℝ) ≤ z ^ k := pow_nonneg hz0.le k
  have hden : (0 : ℝ) < (1 + z) ^ (k + 2) := pow_pos hz1 _
  have hkR : |z - (k : ℝ)| ≤ ((k : ℝ) + 1) * z := by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rw [abs_le]
    constructor <;> nlinarith [hz]
  have hsign : z ^ k * Gk k z =
      (-1 : ℝ) ^ k * (2 * (k.factorial : ℝ) * z ^ k * (z - (k : ℝ)) / (1 + z) ^ (k + 2)) := by
    rw [Gk_apply]
    ring
  rw [hsign, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [abs_div, abs_of_pos hden, abs_mul, abs_mul, abs_mul, abs_of_nonneg hfac,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hzpow]
  have step1 : 2 * (k.factorial : ℝ) * z ^ k * |z - (k : ℝ)| / (1 + z) ^ (k + 2)
      ≤ 2 * (k.factorial : ℝ) * z ^ k * (((k : ℝ) + 1) * z) / (1 + z) ^ (k + 2) := by
    gcongr
  have step2 : 2 * (k.factorial : ℝ) * z ^ k * (((k : ℝ) + 1) * z) / (1 + z) ^ (k + 2)
      ≤ 2 * (k.factorial : ℝ) * ((k : ℝ) + 1) / z := by
    rw [div_le_div_iff₀ hden hz0]
    have h1 : 2 * (k.factorial : ℝ) * z ^ k * (((k : ℝ) + 1) * z) * z
        = 2 * (k.factorial : ℝ) * ((k : ℝ) + 1) * z ^ (k + 2) := by
      rw [pow_add]
      ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz0.le (by linarith) (k + 2))
      (by positivity)
  linarith

/-! ## The far-field bound for every `D_z`-iterate of the profile -/

/-- **The far-field bound for every `D_z`-iterate of the profile.**  For `z ≥ 1` and every
order `b`,

  `|D_z^b F_*(z)| ≤ bell b · 2·b!·(b+1)/z`.

This is `DzIter_eq_sum_scoef` (`D_z^b φ = ∑_{k≤b} S(b,k) z^k ∂_z^k φ`), the identification
`∂_z^k φ = Gk k` of `pzIter_Fstar_eq_Gk`, and the coefficient bound of
`abs_sum_scoef_mul_le` applied to `abs_zpow_mul_Gk_le_all`. -/
theorem DzIter_Fstar_le (b : ℕ) {z : ℝ} (hz : 1 ≤ z) (θ : ℝ) :
    |Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z θ|
      ≤ (Work.Spaces.bell b : ℝ) * (2 * (b.factorial : ℝ) * ((b : ℝ) + 1) / z) := by
  have hzmem : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
  have hsm : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ ⊤
      (fun z => (fun z _ => Work.FM.Fstar z) z θ) (Set.Ioi (-1)) :=
    fun θ _ => contDiffOn_Fstar
  have h0I : (0 : ℝ) ∈ Work.Spaces.Iθ := by
    simp only [Work.Spaces.Iθ, Set.mem_Icc]; exact ⟨le_rfl, by positivity⟩
  rw [DzIter_zonly_theta_indep (fun z => Work.FM.Fstar z) b z θ 0]
  rw [Work.Spaces.DzIter_eq_sum_scoef hsm b z hzmem 0 h0I]
  refine Work.Spaces.abs_sum_scoef_mul_le b (2 * (b.factorial : ℝ) * ((b : ℝ) + 1) / z)
    (fun k => z ^ k * Work.Spaces.pzIter k (fun z _ => Work.FM.Fstar z) z 0) ?_
  intro k hk
  rw [pzIter_Fstar_eq_Gk k hzmem 0]
  refine (abs_zpow_mul_Gk_le_all k hz).trans ?_
  have hkfac : (k.factorial : ℝ) ≤ (b.factorial : ℝ) := by exact_mod_cast Nat.factorial_le hk
  have hk1 : (k : ℝ) + 1 ≤ (b : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hk
  gcongr

/-! ## The Bell numbers of the rows `j ≤ 8` -/

/-- The Bell numbers of the rows `j ≤ 8` are at most `9000` (`B_8 = 4140`). -/
theorem bell_le_eight (j : ℕ) (hj : j ≤ 8) : Work.Spaces.bell j ≤ 9000 := by
  interval_cases j <;> decide

end LocFM8s

/-- **The `D_z`-jets of the fundamental-model profile decay like `1/z`, up to order `8`.** -/
theorem FM_jet8safe :
    ∃ CF : ℝ, 0 < CF ∧ ∀ j : ℕ, j ≤ 8 → ∀ z : ℝ, 1 ≤ z → ∀ θ : ℝ,
      |Work.Spaces.DzIter j (fun z _ => Work.FM.Fstar z) z θ| ≤ CF / z := by
  refine ⟨6531840000, by norm_num, fun j hj z hz θ => ?_⟩
  have hzpos : (0 : ℝ) < z := by linarith
  refine (LocFM8s.DzIter_Fstar_le j hz θ).trans ?_
  have hbell : (Work.Spaces.bell j : ℝ) ≤ 9000 := by
    exact_mod_cast LocFM8s.bell_le_eight j hj
  have hfac : ((j.factorial : ℕ) : ℝ) ≤ 40320 := by
    have h := Nat.factorial_le hj
    have h8 : (Nat.factorial 8 : ℕ) = 40320 := by decide
    rw [h8] at h
    exact_mod_cast h
  have hj1 : (j : ℝ) + 1 ≤ 9 := by
    have h : j + 1 ≤ 8 + 1 := Nat.succ_le_succ hj
    have hR : ((j + 1 : ℕ) : ℝ) ≤ ((8 + 1 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at hR
    linarith
  have hfac0 : (0 : ℝ) ≤ ((j.factorial : ℕ) : ℝ) := by positivity
  have hj10 : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
  have hnum : 2 * ((j.factorial : ℕ) : ℝ) * ((j : ℝ) + 1) ≤ 725760 := by
    have h1 : ((j.factorial : ℕ) : ℝ) * ((j : ℝ) + 1) ≤ 40320 * 9 :=
      mul_le_mul hfac hj1 hj10 (by norm_num)
    nlinarith [h1]
  have hB : 2 * ((j.factorial : ℕ) : ℝ) * ((j : ℝ) + 1) / z ≤ 725760 / z :=
    div_le_div_of_nonneg_right hnum hzpos.le
  have hBnn : 0 ≤ 2 * ((j.factorial : ℕ) : ℝ) * ((j : ℝ) + 1) / z := by positivity
  calc (Work.Spaces.bell j : ℝ) * (2 * ((j.factorial : ℕ) : ℝ) * ((j : ℝ) + 1) / z)
      ≤ 9000 * (725760 / z) := mul_le_mul hbell hB hBnn (by norm_num)
    _ = 6531840000 / z := by ring

end Work.FTS_LocDatum3a
end
end
-- ===== merged: Submission.Work.FTS_RegExport.C4.hardyTheta_slice_C1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.C4.hardyTheta_slice_C1`

The angular Hardy inequality of Elgindi's §H2 in the **`C¹` slice form**: fix `z > 0` and
suppose that the one-variable `θ`-slice `θ ↦ g z θ` is `C¹` on `(0,π/2)`, that its derivative
`θ ↦ ∂_θ g(z,θ)` is `C¹` there, that the slice tends to `0` as `θ → 0⁺`, and that the weighted
angular energy `(∂_θ g(z,σ))² sin(2σ)^{2-γ}` is integrable on `Iθ = [0,π/2]`.  Then

  `g(z,θ)² ≤ (100/(γ-1)) ∫_{Iθ} (∂_θ g(z,σ))² sin(2σ)^{2-γ} dσ`   for every `0 < θ < π/2`,

where `γ = Work.Spaces.gam α = 1 + α/10`.

The classical proof (the fundamental theorem of calculus on `[ε,θ]`, the weighted
Cauchy–Schwarz `Work.Spaces.hardyZ_interval_integral_mul_le_sqrt` for the two factors
`∂_θ g · sin(2·)^{(2-γ)/2}` and `sin(2·)^{(γ-2)/2}`, the quantitative bound
`Work.Spaces.sin_two_rpow` for the singular weight, and finally the limit `ε → 0⁺` using the
boundary hypothesis) uses **only** the continuity and differentiability of the two
one-variable slices on the open interval — never anything stronger than `C¹`.  That is why
this form of the statement holds; the general one-variable form is isolated below as
`hardyTheta_slice_C1_aux` and the theorem is its instantiation at `u = fun θ => g z θ`.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.C4

set_option maxHeartbeats 800000

/-! ## Elementary angular facts -/

/-- `sin (2θ) ≥ 0` on the closed angular interval `Iθ = [0,π/2]`. -/
private lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin (2θ) > 0` for `0 < θ < π/2`. -/
private lemma sin_two_pos_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- Monotonicity of the interval integral against the set integral over `Iθ`: for `0 < a ≤ b`
and `b < π/2` the interval `[a,b]` sits inside `Iθ`, so the integral of a nonnegative
integrable function over `[a,b]` is at most its integral over `Iθ`. -/
private lemma interval_integral_le_setIntegral_Iθ {F : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hb : b < π / 2) (hint : MeasureTheory.IntegrableOn F Work.Spaces.Iθ)
    (hnn : ∀ x ∈ Work.Spaces.Iθ, 0 ≤ F x) :
    (∫ x in a..b, F x) ≤ ∫ x in Work.Spaces.Iθ, F x := by
  rw [intervalIntegral.integral_of_le hab]
  refine setIntegral_mono_set hint (ae_restrict_of_forall_mem measurableSet_Icc hnn) ?_
  exact Eventually.of_forall fun x hx =>
    ⟨le_of_lt (lt_trans ha hx.1), le_of_lt (lt_of_le_of_lt hx.2 hb)⟩

/-! ## The Hardy inequality for a single `C¹` slice -/

/-- **The angular Hardy inequality for a single one-variable function, `C¹` form.**

For `u` of class `C¹` on `(0,π/2)` whose derivative `deriv u` is continuous on `(0,π/2)`
(here assumed `C¹`), with `u θ → 0` as `θ → 0⁺` and `(deriv u)² sin(2·)^{2-γ}` integrable
on `Iθ`,

  `u(θ)² ≤ (100/(γ-1)) ∫_Iθ (deriv u)² sin(2σ)^{2-γ} dσ`   for every `0 < θ < π/2`.

Proof: for `0 < ε < θ` the fundamental theorem of calculus on `[ε,θ]` gives
`u θ - u ε = ∫_ε^θ deriv u`; Cauchy–Schwarz with the two factors
`deriv u · sin(2·)^{(2-γ)/2}` and `sin(2·)^{(γ-2)/2}`, together with the quantitative bound
`Work.Spaces.sin_two_rpow` for the singular weight, gives the estimate with `u ε` on the left;
the limit `ε → 0⁺` (hypothesis `h0`) finishes. -/
private lemma hardyTheta_slice_C1_aux {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {u : ℝ → ℝ}
    (hslice : ContDiffOn ℝ 1 u (Set.Ioo 0 (π / 2)))
    (hdth : ContDiffOn ℝ 1 (deriv u) (Set.Ioo 0 (π / 2)))
    (h0 : Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hint : MeasureTheory.IntegrableOn (fun σ => (deriv u σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ) :
    ∀ θ ∈ Set.Ioo 0 (π / 2), (u θ) ^ 2 ≤
      (100 / (Work.Spaces.gam α - 1)) * ∫ σ in Work.Spaces.Iθ,
        (deriv u σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) := by
  have hγ1 : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hp1 : -1 < Work.Spaces.gam α - 2 := by rw [Work.Spaces.gam]; linarith
  have hp0 : Work.Spaces.gam α - 2 ≤ 0 := by rw [Work.Spaces.gam]; linarith
  have hne0 : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  intro θ hθ
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ < π / 2 := hθ.2
  set A : ℝ := ∫ σ in Work.Spaces.Iθ, (deriv u σ) ^ 2
    * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) with hAdef
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    exact setIntegral_nonneg measurableSet_Icc fun σ hσ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hσ) _)
  have hKnn : 0 ≤ 100 / (Work.Spaces.gam α - 1) := div_nonneg (by norm_num) hγ1.le
  -- the bound at every `ε ∈ (0,θ)`
  have hkey : ∀ ε ∈ Set.Ioo 0 θ,
      (u θ - u ε) ^ 2 ≤ (100 / (Work.Spaces.gam α - 1)) * A := by
    intro ε hε
    have hεθ : ε ≤ θ := le_of_lt hε.2
    have hsub : Set.uIcc ε θ ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
      intro x hx
      rw [Set.uIcc_of_le hεθ] at hx
      exact ⟨lt_of_lt_of_le hε.1 hx.1, lt_of_le_of_lt hx.2 hθ1⟩
    have hsubI : Set.Icc ε θ ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
      rw [← Set.uIcc_of_le hεθ]; exact hsub
    have hcontθ : ContinuousOn u (Set.Icc ε θ) := hslice.continuousOn.mono hsubI
    have hpthcont : ContinuousOn (deriv u) (Set.uIcc ε θ) := hdth.continuousOn.mono hsub
    have hderiv : ∀ x ∈ Set.Ioo ε θ, HasDerivAt u (deriv u x) x := by
      intro x hx
      have hx' : x ∈ Set.Ioo (0 : ℝ) (π / 2) :=
        ⟨lt_trans hε.1 hx.1, lt_of_lt_of_le hx.2 hθ1.le⟩
      exact ((hslice.differentiableOn hne0).differentiableAt
        (isOpen_Ioo.mem_nhds hx')).hasDerivAt
    have hintε : IntervalIntegrable (deriv u) volume ε θ := hpthcont.intervalIntegrable
    have hFTC : ∫ s in ε..θ, deriv u s = u θ - u ε :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hεθ hcontθ hderiv hintε
    have hsincont : ∀ c : ℝ,
        ContinuousOn (fun s : ℝ => (Real.sin (2 * s)) ^ c) (Set.uIcc ε θ) := fun c =>
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
        (fun s hs => Or.inl (ne_of_gt (sin_two_pos_Ioo (hsub hs))))
    have hcs := Work.Spaces.hardyZ_interval_integral_mul_le_sqrt ε θ hεθ
      (hpthcont.mul (hsincont ((2 - Work.Spaces.gam α) / 2)))
      (hsincont ((Work.Spaces.gam α - 2) / 2))
    have hcongr : ∫ s in ε..θ,
          (deriv u s * (Real.sin (2 * s)) ^ ((2 - Work.Spaces.gam α) / 2))
            * (Real.sin (2 * s)) ^ ((Work.Spaces.gam α - 2) / 2)
        = ∫ s in ε..θ, deriv u s := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      have hs' := hsub hs
      have hsin : 0 < Real.sin (2 * s) := sin_two_pos_Ioo hs'
      have h1 : (Real.sin (2 * s)) ^ ((2 - Work.Spaces.gam α) / 2)
          * (Real.sin (2 * s)) ^ ((Work.Spaces.gam α - 2) / 2) = 1 := by
        rw [← Real.rpow_add hsin,
          show (2 - Work.Spaces.gam α) / 2 + (Work.Spaces.gam α - 2) / 2 = 0 by ring,
          Real.rpow_zero]
      rw [mul_assoc, h1, mul_one]
    have hAint : ∫ s in ε..θ,
          (deriv u s * (Real.sin (2 * s)) ^ ((2 - Work.Spaces.gam α) / 2)) ^ 2 ≤ A := by
      have hEq : ∫ s in ε..θ,
            (deriv u s * (Real.sin (2 * s)) ^ ((2 - Work.Spaces.gam α) / 2)) ^ 2
          = ∫ s in ε..θ, (deriv u s) ^ 2 * (Real.sin (2 * s)) ^ (2 - Work.Spaces.gam α) := by
        refine intervalIntegral.integral_congr fun s hs => ?_
        have hs' := hsub hs
        have h1 : ((Real.sin (2 * s)) ^ ((2 - Work.Spaces.gam α) / 2)) ^ 2
            = (Real.sin (2 * s)) ^ (2 - Work.Spaces.gam α) := by
          rw [pow_two, ← Real.rpow_add (sin_two_pos_Ioo hs')]
          congr 1
          ring
        rw [mul_pow, h1]
      rw [hEq, hAdef]
      exact interval_integral_le_setIntegral_Iθ hε.1 hεθ hθ1 hint fun x hx =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hx) _)
    have hBint : ∫ s in ε..θ, ((Real.sin (2 * s)) ^ ((Work.Spaces.gam α - 2) / 2)) ^ 2
        ≤ 100 / (Work.Spaces.gam α - 1) := by
      have hEq : ∫ s in ε..θ, ((Real.sin (2 * s)) ^ ((Work.Spaces.gam α - 2) / 2)) ^ 2
          = ∫ s in ε..θ, (Real.sin (2 * s)) ^ (Work.Spaces.gam α - 2) := by
        refine intervalIntegral.integral_congr fun s hs => ?_
        rw [pow_two, ← Real.rpow_add (sin_two_pos_Ioo (hsub hs))]
        congr 1
        ring
      rw [hEq]
      refine le_trans (interval_integral_le_setIntegral_Iθ hε.1 hεθ hθ1
        (Work.Spaces.sin_two_rpow (Work.Spaces.gam α - 2) hp1 hp0).1
        (fun x hx => Real.rpow_nonneg (sin_two_nonneg_Iθ hx) _)) ?_
      have h2 := (Work.Spaces.sin_two_rpow (Work.Spaces.gam α - 2) hp1 hp0).2
      rwa [show (Work.Spaces.gam α - 2) + 1 = Work.Spaces.gam α - 1 by ring] at h2
    have hstep : |u θ - u ε| ≤ Real.sqrt A * Real.sqrt (100 / (Work.Spaces.gam α - 1)) := by
      rw [← hFTC, ← hcongr]
      exact le_trans hcs (mul_le_mul (Real.sqrt_le_sqrt hAint) (Real.sqrt_le_sqrt hBint)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have hsq : (u θ - u ε) ^ 2
        ≤ (Real.sqrt A * Real.sqrt (100 / (Work.Spaces.gam α - 1))) ^ 2 :=
      sq_le_sq' (by linarith [neg_abs_le (u θ - u ε), hstep])
        (le_trans (le_abs_self _) hstep)
    calc (u θ - u ε) ^ 2
        ≤ (Real.sqrt A * Real.sqrt (100 / (Work.Spaces.gam α - 1))) ^ 2 := hsq
      _ = A * (100 / (Work.Spaces.gam α - 1)) := by
            rw [mul_pow, Real.sq_sqrt hAnn, Real.sq_sqrt hKnn]
      _ = (100 / (Work.Spaces.gam α - 1)) * A := by ring
  -- pass to the limit `ε → 0⁺`
  have hlim : Tendsto (fun ε => (u θ - u ε) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 ((u θ) ^ 2)) := by
    have h1 : Tendsto (fun ε => u θ - u ε) (𝓝[>] (0 : ℝ)) (𝓝 (u θ - 0)) :=
      tendsto_const_nhds.sub h0
    simpa using h1.pow 2
  refine le_of_tendsto hlim ?_
  rw [eventually_nhdsWithin_iff]
  filter_upwards [isOpen_Iio.mem_nhds hθ0] with ε hε hε0
  exact hkey ε ⟨hε0, hε⟩

/-! ## The requested `C¹`-slice statement -/

theorem hardyTheta_slice_C1 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ} {z : ℝ}
    (hz : 0 < z)
    (hslice : ContDiffOn ℝ 1 (fun θ => g z θ) (Set.Ioo 0 (Real.pi / 2)))
    (hpth : ContDiffOn ℝ 1 (fun θ => Work.Spaces.pth g z θ) (Set.Ioo 0 (Real.pi / 2)))
    (h0 : Filter.Tendsto (fun θ => g z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hint : MeasureTheory.IntegrableOn (fun σ => (Work.Spaces.pth g z σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (g z θ) ^ 2 ≤
      (100 / (Work.Spaces.gam α - 1)) * ∫ σ in Work.Spaces.Iθ,
        (Work.Spaces.pth g z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) := by
  intro θ hθ
  exact hardyTheta_slice_C1_aux hα hα1 hslice hpth h0 hint θ hθ

end Work.FTS_RegExport.C4
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXB.SupGen.thetaHardyGen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology MeasureTheory
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXB.SupGen

set_option maxHeartbeats 800000

/-- `sin (2θ) ≥ 0` on the closed angular interval `Iθ = [0,π/2]`. -/
private lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem thetaHardyGen {α : ℝ} (hα : 0 < α) (K : ℝ) (hK0 : 0 ≤ K) (g : ℝ → ℝ → ℝ) (z : ℝ)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hz : 0 < z)
    (h0 : Filter.Tendsto (fun θ => g z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hint : MeasureTheory.IntegrableOn (fun σ => (Work.Spaces.pth g z σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ)
    (hSint : MeasureTheory.IntegrableOn
      (fun σ => (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2)) Work.Spaces.Iθ)
    (hSval : ∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2) ≤ K) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (g z θ) ^ 2 ≤
      K * ∫ σ in Work.Spaces.Iθ,
        (Work.Spaces.pth g z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) := by
  have hne0 : Work.Stability.smoothOrder ≠ 0 := Work.FTS.LocData.smoothOrder_ne_zero
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' => g z θ')
      (Set.Ioo 0 (π / 2)) := hg.curry_θ hz
  have hdth : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' => Work.Spaces.pth g z θ')
      (Set.Ioo 0 (π / 2)) := hg.pth.curry_θ hz
  intro θ hθ
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ < π / 2 := hθ.2
  set A : ℝ := ∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth g z σ) ^ 2
    * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) with hAdef
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    exact setIntegral_nonneg measurableSet_Icc fun σ hσ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hσ) _)
  -- the bound at every `ε ∈ (0,θ)`
  have hkey : ∀ ε ∈ Set.Ioo 0 θ, (g z θ - g z ε) ^ 2 ≤ K * A := by
    intro ε hε
    have hεθ : ε ≤ θ := le_of_lt hε.2
    have hsub : Set.uIcc ε θ ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
      intro x hx
      rw [Set.uIcc_of_le hεθ] at hx
      exact ⟨lt_of_lt_of_le hε.1 hx.1, lt_of_le_of_lt hx.2 hθ1⟩
    have hsubI : Set.Icc ε θ ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
      rw [← Set.uIcc_of_le hεθ]; exact hsub
    have hcontθ : ContinuousOn (fun θ' => g z θ') (Set.Icc ε θ) :=
      hslice.continuousOn.mono hsubI
    have hpthcont : ContinuousOn (fun s => Work.Spaces.pth g z s) (Set.uIcc ε θ) :=
      hdth.continuousOn.mono hsub
    have hderiv : ∀ x ∈ Set.Ioo ε θ,
        HasDerivAt (fun θ' => g z θ') (Work.Spaces.pth g z x) x := by
      intro x hx
      have hx' : x ∈ Set.Ioo (0 : ℝ) (π / 2) :=
        ⟨lt_trans hε.1 hx.1, lt_of_lt_of_le hx.2 hθ1.le⟩
      exact ((hslice.differentiableOn hne0).differentiableAt
        (isOpen_Ioo.mem_nhds hx')).hasDerivAt
    have hintε : IntervalIntegrable (fun s => Work.Spaces.pth g z s) volume ε θ :=
      hpthcont.intervalIntegrable
    have hFTC : ∫ s in ε..θ, Work.Spaces.pth g z s = g z θ - g z ε :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hεθ hcontθ hderiv hintε
    have hsincont : ∀ c : ℝ,
        ContinuousOn (fun s : ℝ => (Real.sin (2 * s)) ^ c) (Set.uIcc ε θ) := fun c =>
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
        (fun s hs => Or.inl (ne_of_gt (Work.FTS.H2.sin_two_pos_of_mem_Ioo (hsub hs))))
    have hcs := Work.Spaces.hardyZ_interval_integral_mul_le_sqrt ε θ hεθ
      (hpthcont.mul (hsincont ((2 - Work.Spaces.gam α) / 2)))
      (hsincont ((Work.Spaces.gam α - 2) / 2))
    have hcongr : ∫ s in ε..θ,
          (Work.Spaces.pth g z s * (Real.sin (2 * s)) ^ ((2 - Work.Spaces.gam α) / 2))
            * (Real.sin (2 * s)) ^ ((Work.Spaces.gam α - 2) / 2)
        = ∫ s in ε..θ, Work.Spaces.pth g z s := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      have hs' := hsub hs
      have hsin : 0 < Real.sin (2 * s) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hs'
      have h1 : (Real.sin (2 * s)) ^ ((2 - Work.Spaces.gam α) / 2)
          * (Real.sin (2 * s)) ^ ((Work.Spaces.gam α - 2) / 2) = 1 := by
        rw [← Real.rpow_add hsin,
          show (2 - Work.Spaces.gam α) / 2 + (Work.Spaces.gam α - 2) / 2 = 0 by ring,
          Real.rpow_zero]
      rw [mul_assoc, h1, mul_one]
    have hAint : ∫ s in ε..θ,
          (Work.Spaces.pth g z s * (Real.sin (2 * s)) ^ ((2 - Work.Spaces.gam α) / 2)) ^ 2
        ≤ A := by
      have hEq : ∫ s in ε..θ,
            (Work.Spaces.pth g z s * (Real.sin (2 * s)) ^ ((2 - Work.Spaces.gam α) / 2)) ^ 2
          = ∫ s in ε..θ, (Work.Spaces.pth g z s) ^ 2
              * (Real.sin (2 * s)) ^ (2 - Work.Spaces.gam α) := by
        refine intervalIntegral.integral_congr fun s hs => ?_
        have hs' := hsub hs
        have h1 : ((Real.sin (2 * s)) ^ ((2 - Work.Spaces.gam α) / 2)) ^ 2
            = (Real.sin (2 * s)) ^ (2 - Work.Spaces.gam α) := by
          rw [pow_two, ← Real.rpow_add (Work.FTS.H2.sin_two_pos_of_mem_Ioo hs')]
          congr 1
          ring
        rw [mul_pow, h1]
      rw [hEq, hAdef]
      exact Work.FTS.H2.interval_integral_le_setIntegral_Iθ hε.1 hεθ hθ1 hint fun x hx =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ hx) _)
    have hBint : ∫ s in ε..θ, ((Real.sin (2 * s)) ^ ((Work.Spaces.gam α - 2) / 2)) ^ 2
        ≤ K := by
      have hEq : ∫ s in ε..θ, ((Real.sin (2 * s)) ^ ((Work.Spaces.gam α - 2) / 2)) ^ 2
          = ∫ s in ε..θ, (Real.sin (2 * s)) ^ (Work.Spaces.gam α - 2) := by
        refine intervalIntegral.integral_congr fun s hs => ?_
        rw [pow_two, ← Real.rpow_add (Work.FTS.H2.sin_two_pos_of_mem_Ioo (hsub hs))]
        congr 1
        ring
      rw [hEq]
      exact le_trans (Work.FTS.H2.interval_integral_le_setIntegral_Iθ hε.1 hεθ hθ1 hSint
        fun x hx => Real.rpow_nonneg (sin_two_nonneg_Iθ hx) _) hSval
    have hstep : |g z θ - g z ε| ≤ Real.sqrt A * Real.sqrt K := by
      rw [← hFTC, ← hcongr]
      exact le_trans hcs (mul_le_mul (Real.sqrt_le_sqrt hAint) (Real.sqrt_le_sqrt hBint)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have hsq : (g z θ - g z ε) ^ 2 ≤ (Real.sqrt A * Real.sqrt K) ^ 2 :=
      sq_le_sq' (by linarith [neg_abs_le (g z θ - g z ε), hstep])
        (le_trans (le_abs_self _) hstep)
    calc (g z θ - g z ε) ^ 2
        ≤ (Real.sqrt A * Real.sqrt K) ^ 2 := hsq
      _ = A * K := by rw [mul_pow, Real.sq_sqrt hAnn, Real.sq_sqrt hK0]
      _ = K * A := by ring
  -- pass to the limit `ε → 0⁺`
  have hlim : Tendsto (fun ε => (g z θ - g z ε) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 ((g z θ) ^ 2)) := by
    have h1 : Tendsto (fun ε => g z θ - g z ε) (𝓝[>] (0 : ℝ)) (𝓝 (g z θ - 0)) :=
      tendsto_const_nhds.sub h0
    simpa using h1.pow 2
  refine le_of_tendsto hlim ?_
  rw [eventually_nhdsWithin_iff]
  filter_upwards [isOpen_Iio.mem_nhds hθ0] with ε hε hε0
  exact hkey ε ⟨hε0, hε⟩

end Work.FTS_RegExport.RXB.SupGen
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Slots.v2_Mine =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Slots

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The jet of `L₁₂` -/

/-- The `j`-th `D_z`-jet of `L₁₂ f`: the value `L₁₂ f` for `j = 0` and `-Qang f (j-1)`
for `j ≥ 1`.  This is the value produced by the angular-moment identity. -/
def L12jet (f : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) : ℝ :=
  match j with
  | 0 => Work.Construction.L12 f z
  | (k + 1) => -Work.Elliptic.Qang f k z

@[simp] theorem L12jet_zero (f : ℝ → ℝ → ℝ) (z : ℝ) :
    L12jet f 0 z = Work.Construction.L12 f z := rfl

@[simp] theorem L12jet_succ (f : ℝ → ℝ → ℝ) (k : ℕ) (z : ℝ) :
    L12jet f (k + 1) z = -Work.Elliptic.Qang f k z := rfl

/-! ## Transfer of the pointwise bound to the limit -/

/-- The pointwise bound passes to the limit. -/
theorem JetBnd.of_tendsto {C0 : ℝ} {F : ℕ → ℝ → ℝ → ℝ} {G : ℝ → ℝ → ℝ}
    (hbnd : ∀ n : ℕ, JetBnd C0 (F n))
    (hconv : ∀ (b a : ℕ), a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed b a (F n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed b a G z θ))) :
    JetBnd C0 G := by
  intro b a hab z θ hz h0 h1
  exact le_of_tendsto (hconv b a hab z θ hz h0 h1).abs
    (Filter.Eventually.of_forall (fun n => hbnd n b a hab z θ hz h0 h1))

/-! ## The a.e. bound on the angular slices -/

/-- A.e. on `Iθ`, `‖K(θ)·D_z^k f(z,θ)‖ ≤ 3·C₀·z^{3/2}/(1+z)²` for `k ≤ 2`. -/
theorem JetBnd.abs_Ktheta_mul_DzIter_le_ae {C0 : ℝ} {f : ℝ → ℝ → ℝ} (hb : JetBnd C0 f)
    {k : ℕ} (hk : k ≤ 2) {z : ℝ} (hz : 0 < z) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ‖Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k f z θ‖
        ≤ 3 * (C0 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)) := by
  rw [restrict_Iθ_eq_restrict_Ioo]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  refine le_trans (mul_le_mul (abs_Ktheta_le θ) (hb k 0 (by omega) z θ hz hθ.1 hθ.2)
    (abs_nonneg _) (by norm_num)) (le_of_eq (by ring))

/-! ## Slice derivatives of the `D_z`-iterates -/

/-- For `f` of class `C⁴` on the open quadrant and `k ≤ 3`, the radial slice of `D_z^k f`
has derivative `pz (D_z^k f)` at every point of the open quadrant. -/
theorem DzIter_slice_hasDerivAt_pz {f : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0) {k : ℕ} (hk : k ≤ 3)
    {z θ : ℝ} (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    HasDerivAt (fun x => Work.Spaces.DzIter k f x θ)
      (Work.Spaces.pz (Work.Spaces.DzIter k f) z θ) z := by
  have hcd := Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DzIter_fin
    Work.FTS.EllipticEst.isOpen_Q0 hF k (Nat.le_trans hk (by norm_num))
  have hcd1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.DzIter k f))
      Work.FTS.EllipticEst.Q0 :=
    hcd.of_le (Nat.cast_le.mpr (by omega : 1 ≤ 4 - k))
  have hslice : ContDiffOn ℝ 1 (fun x => Work.Spaces.DzIter k f x θ) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_slice_z_fin hcd1 ⟨h0, h1⟩
  have hdiff : DifferentiableAt ℝ (fun x => Work.Spaces.DzIter k f x θ) z :=
    (hslice.differentiableOn one_ne_zero).differentiableAt (isOpen_Ioi.mem_nhds hz)
  exact hdiff.hasDerivAt

/-- `D_z^k f` is `C¹` on the open quadrant as soon as `f` is `C⁴` there and `k ≤ 3`. -/
theorem contDiffOn_one_DzIter_jet {f : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0) {k : ℕ} (hk : k ≤ 3) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.DzIter k f)) Work.FTS.EllipticEst.Q0 :=
  (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DzIter_fin Work.FTS.EllipticEst.isOpen_Q0 hF k
    (Nat.le_trans hk (by norm_num))).of_le (Nat.cast_le.mpr (by omega : 1 ≤ 4 - k))

/-- `K(θ)` is continuous on the open quadrant. -/
theorem continuousOn_Ktheta_jet :
    ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2) Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2)
      = fun p : ℝ × ℝ => 3 * Real.sin p.2 * Real.cos p.2 ^ 2 := by
    funext p; rw [Work.Elliptic.Ktheta]
  rw [hfun]
  exact ((continuous_const.mul (Real.continuous_sin.comp continuous_snd)).mul
    ((Real.continuous_cos.comp continuous_snd).pow 2)).continuousOn


/-! ## The moment identities -/

/-- `Qang f (k+1) z = z · ∫_θ K(θ)·∂_z(D_z^k f)(z,θ) dθ`, by linearity of the `θ`-integral. -/
theorem Qang_succ_eq (f : ℝ → ℝ → ℝ) (k : ℕ) (z : ℝ) :
    Work.Elliptic.Qang f (k + 1) z
      = z * ∫ θ in Work.Spaces.Iθ,
          Work.Elliptic.Ktheta θ * Work.Spaces.pz (Work.Spaces.DzIter k f) z θ := by
  have h1 : Work.Elliptic.Qang f (k + 1) z
      = ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ
          * (z * Work.Spaces.pz (Work.Spaces.DzIter k f) z θ) := rfl
  rw [h1, show (fun θ => Work.Elliptic.Ktheta θ
        * (z * Work.Spaces.pz (Work.Spaces.DzIter k f) z θ))
      = fun θ => z * (Work.Elliptic.Ktheta θ
          * Work.Spaces.pz (Work.Spaces.DzIter k f) z θ) from by funext θ; ring,
    MeasureTheory.integral_const_mul]

/-- The divided form of `Qang_succ_eq`. -/
theorem Qang_succ_div (f : ℝ → ℝ → ℝ) (k : ℕ) {z : ℝ} (hz : z ≠ 0) :
    (∫ θ in Work.Spaces.Iθ,
        Work.Elliptic.Ktheta θ * Work.Spaces.pz (Work.Spaces.DzIter k f) z θ)
      = Work.Elliptic.Qang f (k + 1) z / z := by
  rw [Qang_succ_eq f k z, mul_div_cancel_left₀ _ hz]

/-! ## The derivative of `L₁₂` -/

/-- `∂_z L₁₂(f) = -(Qang f 0 z / z)`: the `k = 0` base case of the tower. -/
theorem Construction_L12_hasDerivAt_jet {C0 : ℝ} {f : ℝ → ℝ → ℝ} (hC0 : 0 ≤ C0)
    (hb : JetBnd C0 f)
    (hcont : ContinuousOn (fun s => Work.Elliptic.L12dens f s) (Set.Ioi 0))
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun σ => Work.Construction.L12 f σ) (-(Work.Elliptic.Qang f 0 z / z)) z := by
  have hint : IntegrableOn (fun s => Work.Elliptic.L12dens f s) (Set.Ioi (z / 2)) :=
    hb.dens_integrable hC0 hcont (by linarith)
  have hint' : IntegrableOn (Work.FM.L12dens Work.Spaces.K f) (Set.Ioi (z / 2)) := hint
  have hcontAt : ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z :=
    (hcont.continuousAt (isOpen_Ioi.mem_nhds hz))
  have key := Work.FM.hasDerivAt_L12_of_integrable (K := Work.Spaces.K) (f := f)
    (a := z / 2) (ρ := z) hint' (fun s hs => hcont.continuousAt
      (isOpen_Ioi.mem_nhds (by linarith : (0 : ℝ) < s))) (by linarith)
  have hden : Work.FM.L12dens Work.Spaces.K f z = Work.Elliptic.Qang f 0 z / z :=
    Work.Elliptic.L12dens_eq_Qang_div f z
  rw [hden] at key
  simpa only [Work.Construction.L12] using key

/-! ## The two `Qang`-derivatives and the two dominated-convergence statements -/

/-- The elliptic density is the fundamental-model density for `K = K(θ) = 3 sin θ cos²θ`. -/
theorem L12dens_eq_fm (f : ℝ → ℝ → ℝ) :
    Work.Elliptic.L12dens f = Work.FM.L12dens Work.Spaces.K f := rfl

/-- `∂_z (Qang f 0)(z) = Qang f 1 z / z`. -/
theorem QangZeroDeriv_jet {C0 : ℝ} {f : ℝ → ℝ → ℝ} (hC0 : 0 ≤ C0)
    (hF : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0) (hb : JetBnd C0 f)
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt (Work.Elliptic.Qang f 0) (Work.Elliptic.Qang f 1 z / z) z := by
  haveI : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) := isFiniteMeasure_restrict_Iθ
  have hz2 : 0 < z / 2 := by linarith
  have hVmem : z ∈ Set.Ioi (z / 2) := Set.mem_Ioi.mpr (by linarith)
  have hVpos : ∀ x ∈ Set.Ioi (z / 2), 0 < x :=
    fun x hx => lt_trans hz2 (Set.mem_Ioi.mp hx)
  have hcf : ContinuousOn (Function.uncurry (fun x θ => Work.Elliptic.Ktheta θ * f x θ))
      Work.FTS.EllipticEst.Q0 :=
    show ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * f p.1 p.2)
      Work.FTS.EllipticEst.Q0 from
      continuousOn_Ktheta_jet.mul (show ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
        Work.FTS.EllipticEst.Q0 from hF.continuousOn)
  have hcpz : ContinuousOn
      (Function.uncurry (fun x θ => Work.Elliptic.Ktheta θ * Work.Spaces.pz f x θ))
      Work.FTS.EllipticEst.Q0 :=
    show ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * Work.Spaces.pz f p.1 p.2)
      Work.FTS.EllipticEst.Q0 from
      continuousOn_Ktheta_jet.mul
        (show ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz f p.1 p.2)
          Work.FTS.EllipticEst.Q0 from
          (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_pz_fin Work.FTS.EllipticEst.isOpen_Q0
            (n := 3) hF).continuousOn)
  have hint : Integrable (fun θ => Work.Elliptic.Ktheta θ * f z θ)
      (volume.restrict Work.Spaces.Iθ) :=
    Integrable.mono' (integrable_const (3 * (C0 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))))
      (aesm_slice_Q0 hcf hz) (hb.abs_Ktheta_mul_DzIter_le_ae (k := 0) (by norm_num) hz)
  have hbound : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), ∀ x ∈ Set.Ioi (z / 2),
      ‖Work.Elliptic.Ktheta θ * Work.Spaces.pz f x θ‖
        ≤ 3 * C0 * ((z / 2) ^ (-(3 : ℝ) / 2) + 1) := by
    rw [restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ x hx => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    refine le_trans (mul_le_mul (abs_Ktheta_le θ)
      (le_trans (hb.pz_DzIter_le (k := 0) (by norm_num) (hVpos x hx) hθ.1 hθ.2)
        (mul_le_mul_of_nonneg_left (rpow_half_div_sq_le hz2 (le_of_lt (Set.mem_Ioi.mp hx))) hC0))
      (abs_nonneg _) (by norm_num)) (le_of_eq (by ring))
  have hdiff : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ x ∈ Set.Ioi (z / 2),
      HasDerivAt (fun y => Work.Elliptic.Ktheta θ * f y θ)
        (Work.Elliptic.Ktheta θ * Work.Spaces.pz f x θ) x :=
    fun θ hθ x hx =>
      (DzIter_slice_hasDerivAt_pz hF (k := 0) (by norm_num) (hVpos x hx) hθ.1 hθ.2).const_mul _
  have key := hasDerivAt_integral_Itheta_Q0 (V := Set.Ioi (z / 2)) isOpen_Ioi hVmem hVpos
    hcf hcpz hint hbound hdiff
  have hval : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * Work.Spaces.pz f z θ)
      = Work.Elliptic.Qang f 1 z / z := Qang_succ_div f 0 (ne_of_gt hz)
  rw [hval] at key
  exact key

/-- `∂_z (Qang f 1)(z) = Qang f 2 z / z`. -/
theorem QangOneDeriv_jet {C0 : ℝ} {f : ℝ → ℝ → ℝ} (hC0 : 0 ≤ C0)
    (hF : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0) (hb : JetBnd C0 f)
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt (Work.Elliptic.Qang f 1) (Work.Elliptic.Qang f 2 z / z) z := by
  haveI : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) := isFiniteMeasure_restrict_Iθ
  have hz2 : 0 < z / 2 := by linarith
  have hVmem : z ∈ Set.Ioi (z / 2) := Set.mem_Ioi.mpr (by linarith)
  have hVpos : ∀ x ∈ Set.Ioi (z / 2), 0 < x :=
    fun x hx => lt_trans hz2 (Set.mem_Ioi.mp hx)
  have hcd3 : ContDiffOn ℝ 3 (Function.uncurry (Work.Spaces.DzIter 1 f))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DzIter_fin Work.FTS.EllipticEst.isOpen_Q0 hF 1
      (by norm_num)
  have hcd2 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pz (Work.Spaces.DzIter 1 f)))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_pz_fin Work.FTS.EllipticEst.isOpen_Q0 (n := 2) hcd3
  have hcg : ContinuousOn
      (Function.uncurry (fun x θ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter 1 f x θ))
      Work.FTS.EllipticEst.Q0 :=
    show ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
        * Work.Spaces.DzIter 1 f p.1 p.2) Work.FTS.EllipticEst.Q0 from
      continuousOn_Ktheta_jet.mul (show ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.DzIter 1 f p.1 p.2) Work.FTS.EllipticEst.Q0 from hcd3.continuousOn)
  have hcg' : ContinuousOn
      (Function.uncurry (fun x θ => Work.Elliptic.Ktheta θ
        * Work.Spaces.pz (Work.Spaces.DzIter 1 f) x θ)) Work.FTS.EllipticEst.Q0 :=
    show ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2
        * Work.Spaces.pz (Work.Spaces.DzIter 1 f) p.1 p.2) Work.FTS.EllipticEst.Q0 from
      continuousOn_Ktheta_jet.mul (show ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.pz (Work.Spaces.DzIter 1 f) p.1 p.2) Work.FTS.EllipticEst.Q0 from
        hcd2.continuousOn)
  have hint : Integrable (fun θ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter 1 f z θ)
      (volume.restrict Work.Spaces.Iθ) :=
    Integrable.mono' (integrable_const (3 * (C0 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2))))
      (aesm_slice_Q0 hcg hz) (hb.abs_Ktheta_mul_DzIter_le_ae (k := 1) (by norm_num) hz)
  have hbound : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), ∀ x ∈ Set.Ioi (z / 2),
      ‖Work.Elliptic.Ktheta θ * Work.Spaces.pz (Work.Spaces.DzIter 1 f) x θ‖
        ≤ 3 * C0 * ((z / 2) ^ (-(3 : ℝ) / 2) + 1) := by
    rw [restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ x hx => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    refine le_trans (mul_le_mul (abs_Ktheta_le θ)
      (le_trans (hb.pz_DzIter_le (k := 1) (by norm_num) (hVpos x hx) hθ.1 hθ.2)
        (mul_le_mul_of_nonneg_left (rpow_half_div_sq_le hz2 (le_of_lt (Set.mem_Ioi.mp hx))) hC0))
      (abs_nonneg _) (by norm_num)) (le_of_eq (by ring))
  have hdiff : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ x ∈ Set.Ioi (z / 2),
      HasDerivAt (fun y => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter 1 f y θ)
        (Work.Elliptic.Ktheta θ * Work.Spaces.pz (Work.Spaces.DzIter 1 f) x θ) x :=
    fun θ hθ x hx =>
      (DzIter_slice_hasDerivAt_pz hF (k := 1) (by norm_num) (hVpos x hx) hθ.1 hθ.2).const_mul _
  have key := hasDerivAt_integral_Itheta_Q0 (V := Set.Ioi (z / 2)) isOpen_Ioi hVmem hVpos
    hcg hcg' hint hbound hdiff
  have hval : (∫ θ in Work.Spaces.Iθ,
        Work.Elliptic.Ktheta θ * Work.Spaces.pz (Work.Spaces.DzIter 1 f) z θ)
      = Work.Elliptic.Qang f 2 z / z := Qang_succ_div f 1 (ne_of_gt hz)
  rw [hval] at key
  exact key

/-- Dominated convergence in `θ`: `Qang (F n) k z → Qang G k z` for `k ≤ 2`. -/
theorem QangTendsto_conv {C0 : ℝ} {Fs : ℕ → ℝ → ℝ → ℝ} {Gl : ℝ → ℝ → ℝ} (hC0 : 0 ≤ C0)
    (hF : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry (Fs n)) Work.FTS.EllipticEst.Q0)
    (hbnd : ∀ n : ℕ, JetBnd C0 (Fs n)) (hbndG : JetBnd C0 Gl)
    (hconv : ∀ (b a : ℕ), a + b ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed b a (Fs n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed b a Gl z θ)))
    {k : ℕ} (hk : k ≤ 2) {z : ℝ} (hz : 0 < z) :
    Filter.Tendsto (fun n : ℕ => Work.Elliptic.Qang (Fs n) k z) Filter.atTop
      (nhds (Work.Elliptic.Qang Gl k z)) := by
  haveI : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) := isFiniteMeasure_restrict_Iθ
  have hk3 : k ≤ 3 := by omega
  have hmeasn : ∀ n : ℕ, AEStronglyMeasurable
      (fun θ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k (Fs n) z θ)
      (volume.restrict Work.Spaces.Iθ) :=
    fun n => aesm_slice_Q0
      (show ContinuousOn (Function.uncurry (fun x θ => Work.Elliptic.Ktheta θ
          * Work.Spaces.DzIter k (Fs n) x θ)) Work.FTS.EllipticEst.Q0 from
        continuousOn_Ktheta_jet.mul (show ContinuousOn (fun p : ℝ × ℝ =>
          Work.Spaces.DzIter k (Fs n) p.1 p.2) Work.FTS.EllipticEst.Q0 from
          (contDiffOn_one_DzIter_jet (hF n) hk3).continuousOn)) hz
  have hboundn : ∀ n : ℕ, ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ‖Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k (Fs n) z θ‖
        ≤ 3 * (C0 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)) :=
    fun n => (hbnd n).abs_Ktheta_mul_DzIter_le_ae hk hz
  have hlimit : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      Filter.Tendsto (fun n : ℕ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k (Fs n) z θ)
        Filter.atTop (nhds (Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k Gl z θ)) := by
    rw [restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    exact (hconv k 0 (by omega) z θ hz hθ.1 hθ.2).const_mul _
  have key := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict Work.Spaces.Iθ)
    (F := fun (n : ℕ) (θ : ℝ) => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k (Fs n) z θ)
    (f := fun θ : ℝ => Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k Gl z θ)
    (fun _ => 3 * (C0 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)))
    hmeasn (integrable_const _) hboundn hlimit
  simpa only [Work.Elliptic.Qang] using key

/-- Dominated convergence in the radial variable: `L₁₂ (F n) z → L₁₂ G z`. -/
theorem L12Tendsto_dens {C0 z : ℝ} {Fs : ℕ → ℝ → ℝ → ℝ} {Gl : ℝ → ℝ → ℝ} (hC0 : 0 ≤ C0)
    (hbnd : ∀ n : ℕ, JetBnd C0 (Fs n))
    (hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun s => Work.Elliptic.L12dens (Fs n) s) (volume.restrict (Set.Ioi z)))
    (hconv : ∀ s : ℝ, 0 < s → Filter.Tendsto (fun n : ℕ => Work.Elliptic.L12dens (Fs n) s)
      Filter.atTop (nhds (Work.Elliptic.L12dens Gl s)))
    (hz : 0 < z) :
    Filter.Tendsto (fun n : ℕ => Work.Construction.L12 (Fs n) z) Filter.atTop
      (nhds (Work.Construction.L12 Gl z)) := by
  have hmaj : Integrable (fun s : ℝ => 6 * C0 * s ^ (-(3 : ℝ) / 2))
      (volume.restrict (Set.Ioi z)) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3 : ℝ) / 2) < -1) hz).const_mul _
  have hboundn : ∀ n : ℕ, ∀ᵐ s ∂(volume.restrict (Set.Ioi z)),
      ‖Work.Elliptic.L12dens (Fs n) s‖ ≤ 6 * C0 * s ^ (-(3 : ℝ) / 2) := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hbnd n).dens_bound hC0 (lt_of_lt_of_le hz (le_of_lt hs))
  have hlimit : ∀ᵐ s ∂(volume.restrict (Set.Ioi z)),
      Filter.Tendsto (fun n : ℕ => Work.Elliptic.L12dens (Fs n) s) Filter.atTop
        (nhds (Work.Elliptic.L12dens Gl s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hconv s (lt_of_lt_of_le hz (le_of_lt hs))
  have key := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Set.Ioi z))
    (F := fun (n : ℕ) (s : ℝ) => Work.Elliptic.L12dens (Fs n) s)
    (f := fun s : ℝ => Work.Elliptic.L12dens Gl s)
    (fun s => 6 * C0 * s ^ (-(3 : ℝ) / 2)) hmeas hmaj hboundn hlimit
  simpa only [Work.Construction.L12, Work.FM.L12, L12dens_eq_fm] using key

/-! ## The angular-moment tower -/

/-- **The tower.**  Given, for every `w > 0`, the three derivative formulas
`∂_z Qang f 0 = Qang f 1 / z`, `∂_z Qang f 1 = Qang f 2 / z` and `∂_z L₁₂ f = -Qang f 0 / z`,
the `D_z`-jets of `L₁₂ f` up to order three are the `L12jet`s. -/
theorem dzdIter_L12_jet {C0 : ℝ} {f : ℝ → ℝ → ℝ} (hC0 : 0 ≤ C0)
    (hF : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0) (hb : JetBnd C0 f)
    (hQ0 : ∀ w : ℝ, 0 < w →
      HasDerivAt (Work.Elliptic.Qang f 0) (Work.Elliptic.Qang f 1 w / w) w)
    (hQ1 : ∀ w : ℝ, 0 < w →
      HasDerivAt (Work.Elliptic.Qang f 1) (Work.Elliptic.Qang f 2 w / w) w)
    (hL : ∀ w : ℝ, 0 < w →
      HasDerivAt (fun σ => Work.Construction.L12 f σ) (-(Work.Elliptic.Qang f 0 w / w)) w)
    {j : ℕ} (hj : j ≤ 3) {z : ℝ} (hz : 0 < z) :
    Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 f z) z = L12jet f j z := by
  have h1 : ∀ w : ℝ, 0 < w →
      Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 f z) w
        = -Work.Elliptic.Qang f 0 w := by
    intro w hw
    show w * deriv (fun z => Work.Construction.L12 f z) w = -Work.Elliptic.Qang f 0 w
    rw [(hL w hw).deriv, mul_neg, ← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt hw)]
  have h2 : ∀ w : ℝ, 0 < w →
      Work.Elliptic.DzdIter 2 (fun z => Work.Construction.L12 f z) w
        = -Work.Elliptic.Qang f 1 w := by
    intro w hw
    have heq : Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 f z)
        =ᶠ[𝓝 w] fun u => -Work.Elliptic.Qang f 0 u := by
      filter_upwards [isOpen_Ioi.mem_nhds hw] with u hu
      exact h1 u hu
    have hd : deriv (Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 f z)) w
        = -(Work.Elliptic.Qang f 1 w / w) := by
      rw [heq.deriv_eq]
      exact (hQ0 w hw).neg.deriv
    show w * deriv (Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 f z)) w
        = -Work.Elliptic.Qang f 1 w
    rw [hd, mul_neg, ← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt hw)]
  have h3 : ∀ w : ℝ, 0 < w →
      Work.Elliptic.DzdIter 3 (fun z => Work.Construction.L12 f z) w
        = -Work.Elliptic.Qang f 2 w := by
    intro w hw
    have heq : Work.Elliptic.DzdIter 2 (fun z => Work.Construction.L12 f z)
        =ᶠ[𝓝 w] fun u => -Work.Elliptic.Qang f 1 u := by
      filter_upwards [isOpen_Ioi.mem_nhds hw] with u hu
      exact h2 u hu
    have hd : deriv (Work.Elliptic.DzdIter 2 (fun z => Work.Construction.L12 f z)) w
        = -(Work.Elliptic.Qang f 2 w / w) := by
      rw [heq.deriv_eq]
      exact (hQ1 w hw).neg.deriv
    show w * deriv (Work.Elliptic.DzdIter 2 (fun z => Work.Construction.L12 f z)) w
        = -Work.Elliptic.Qang f 2 w
    rw [hd, mul_neg, ← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt hw)]
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hj' with rfl | rfl | rfl | rfl
  · simp
  · exact h1 z hz
  · exact h2 z hz
  · exact h3 z hz

end Work.FTS_RegExport.RXT.Slots
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB4.DzEpartEq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `z`-derivative of the `U`-slot of the elliptic part, at a point

`Uop α Ψ = -3Ψ - α z ∂_z Ψ` and `PhiTil α F Φ = Φ - (1/(4α)) sin 2θ · L₁₂(F)`, so on the open
quadrant the `z`-derivative of the `U`-slot `Uop α (PhiTil α F Φ)/sin 2θ` splits into the mixed
jets of `Φ` and the angular moments of `F`:

`D_z (Uop α (PhiTil α F Φ)/sin 2θ)(z,θ)`
  `= (-3 D_zΦ - α D_z²Φ)/sin 2θ - (3/(4α)) Qang F 0 z - (1/4) Qang F 1 z`,

using the tower `z ∂_z L₁₂(F) = -Qang F 0` and `z ∂_z (Qang F 0) = Qang F 1`.
-/

noncomputable section

namespace Work.FTS_StreamBdry.SB4

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

theorem Dz_Epart_eq {α : ℝ} (hα : α ≠ 0) {F Φ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hΦ : ContDiffOn ℝ 2 (Function.uncurry Φ) Work.FTS.EllipticEst.Q0)
    (hL : ∀ z' ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z'' => Work.Construction.L12 F z'') (-(Work.Elliptic.Qang F 0 z' / z')) z')
    (hQ : HasDerivAt (Work.Elliptic.Qang F 0) (Work.Elliptic.Qang F 1 z / z) z) :
    Work.Spaces.Dz (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z θ
        / Work.Construction.s2 θ) z θ
      = (-3 * Work.Spaces.mixed 1 0 Φ z θ - α * Work.Spaces.mixed 2 0 Φ z θ)
          / Work.Construction.s2 θ
        - (3 / (4 * α)) * Work.Elliptic.Qang F 0 z - (1 / 4) * Work.Elliptic.Qang F 1 z := by
  have hSpos : 0 < Work.Construction.s2 θ := by
    rw [Work.Construction.s2]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hSne : Work.Construction.s2 θ ≠ 0 := ne_of_gt hSpos
  -- `z`-slices of `Φ` and of its `z`-partial
  have hsliceΦ : ContDiffOn ℝ 2 (fun z' => Φ z' θ) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_slice_z_fin hΦ hθ
  have hpzΦc : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz Φ)) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_pz_fin Work.FTS.EllipticEst.isOpen_Q0 hΦ
  have hslicepzΦ : ContDiffOn ℝ 1 (fun z' => Work.Spaces.pz Φ z' θ) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_slice_z_fin hpzΦc hθ
  have hdΦ : DifferentiableAt ℝ (fun z' => Φ z' θ) z :=
    (hsliceΦ.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hdpzΦ : DifferentiableAt ℝ (fun z' => Work.Spaces.pz Φ z' θ) z :=
    (hslicepzΦ.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  -- the `z`-derivative data of `L₁₂(F)` and of `Qang F 0`
  have hLd : ∀ z' ∈ Set.Ioi (0 : ℝ),
      deriv (fun z'' => Work.Construction.L12 F z'') z'
        = -(Work.Elliptic.Qang F 0 z' / z') := fun z' hz' => (hL z' hz').deriv
  have hLdiff : ∀ z' ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun z'' => Work.Construction.L12 F z'') z' :=
    fun z' hz' => (hL z' hz').differentiableAt
  have hevDerivL : (deriv (fun z'' => Work.Construction.L12 F z''))
      =ᶠ[𝓝 z] fun z' => -(Work.Elliptic.Qang F 0 z' / z') := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact hLd z' hz'
  have hdDerivL : DifferentiableAt ℝ (deriv (fun z'' => Work.Construction.L12 F z'')) z :=
    (hQ.differentiableAt.div differentiableAt_id (ne_of_gt hz)).neg.congr_of_eventuallyEq hevDerivL
  have hevZL : (fun z' => z' * deriv (fun z'' => Work.Construction.L12 F z'') z')
      =ᶠ[𝓝 z] fun z' => -(Work.Elliptic.Qang F 0 z') := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    have hz'ne : z' ≠ 0 := ne_of_gt hz'
    rw [hLd z' hz', mul_neg, neg_inj]
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hz'ne]
  have hder2L : deriv (fun z' => z' * deriv (fun z'' => Work.Construction.L12 F z'') z') z
      = -(Work.Elliptic.Qang F 1 z / z) := by
    rw [hevZL.deriv_eq]
    exact hQ.neg.deriv
  -- the splitting of the `z`-derivative of `PhiTil`
  have hpzΨ : ∀ z' ∈ Set.Ioi (0 : ℝ),
      Work.Spaces.pz (Work.Construction.PhiTil α F Φ) z' θ
        = Work.Spaces.pz Φ z' θ
          - ((1 / (4 * α)) * Work.Construction.s2 θ)
              * deriv (fun z'' => Work.Construction.L12 F z'') z' := by
    intro z' hz'
    have h1 : DifferentiableAt ℝ (fun u => Φ u θ) z' :=
      (hsliceΦ.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hz')
    have h2 : DifferentiableAt ℝ (fun u => Work.Construction.L12 F u) z' := hLdiff z' hz'
    have hfun : (fun u => Work.Construction.PhiTil α F Φ u θ)
        = (fun u => Φ u θ)
          - (fun u => ((1 / (4 * α)) * Work.Construction.s2 θ) * Work.Construction.L12 F u) := by
      funext u
      simp only [Pi.sub_apply, Work.Construction.PhiTil, Work.Construction.Theta]
    have hA : deriv (fun u => Φ u θ) z' = Work.Spaces.pz Φ z' θ := rfl
    have hB : deriv (fun u => ((1 / (4 * α)) * Work.Construction.s2 θ) * Work.Construction.L12 F u) z'
        = ((1 / (4 * α)) * Work.Construction.s2 θ)
            * deriv (fun z'' => Work.Construction.L12 F z'') z' :=
      deriv_const_mul _ h2
    rw [Work.Spaces.pz, hfun, deriv_sub h1 (h2.const_mul _), hA, hB]
  have hdΨ : DifferentiableAt ℝ (fun z' => Work.Construction.PhiTil α F Φ z' θ) z := by
    have hfun : (fun z' => Work.Construction.PhiTil α F Φ z' θ)
        = (fun z' => Φ z' θ)
          - (fun z' => ((1 / (4 * α)) * Work.Construction.s2 θ)
              * Work.Construction.L12 F z') := by
      funext u
      simp only [Pi.sub_apply, Work.Construction.PhiTil, Work.Construction.Theta]
    rw [hfun]
    exact hdΦ.sub ((hLdiff z hz).const_mul _)
  have hderΨ : deriv (fun z' => Work.Construction.PhiTil α F Φ z' θ) z
      = Work.Spaces.pz Φ z θ
        - ((1 / (4 * α)) * Work.Construction.s2 θ)
            * deriv (fun z'' => Work.Construction.L12 F z'') z :=
    hpzΨ z hz
  -- the second-order splitting
  have hev2 : (fun z' => z' * Work.Spaces.pz (Work.Construction.PhiTil α F Φ) z' θ)
      =ᶠ[𝓝 z] fun z' => z' * Work.Spaces.pz Φ z' θ
        - ((1 / (4 * α)) * Work.Construction.s2 θ)
            * (z' * deriv (fun z'' => Work.Construction.L12 F z'') z') := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    rw [hpzΨ z' hz']
    ring
  have hd2Ψ : DifferentiableAt ℝ
      (fun z' => z' * Work.Spaces.pz (Work.Construction.PhiTil α F Φ) z' θ) z :=
    ((differentiableAt_id.mul hdpzΦ).sub
      (((differentiableAt_id.mul hdDerivL).const_mul
        ((1 / (4 * α)) * Work.Construction.s2 θ)))).congr_of_eventuallyEq hev2
  have hder2Ψ : deriv (fun z' => z' * Work.Spaces.pz (Work.Construction.PhiTil α F Φ) z' θ) z
      = Work.Spaces.pz (Work.Spaces.Dz Φ) z θ
        - ((1 / (4 * α)) * Work.Construction.s2 θ)
            * deriv (fun z' => z' * deriv (fun z'' => Work.Construction.L12 F z'') z') z := by
    rw [hev2.deriv_eq]
    have hdA : DifferentiableAt ℝ (fun z' => z' * Work.Spaces.pz Φ z' θ) z :=
      differentiableAt_id.mul hdpzΦ
    have hdC : DifferentiableAt ℝ
        (fun z' => z' * deriv (fun z'' => Work.Construction.L12 F z'') z') z :=
      differentiableAt_id.mul hdDerivL
    have hdD : DifferentiableAt ℝ (fun z' => ((1 / (4 * α)) * Work.Construction.s2 θ)
        * (z' * deriv (fun z'' => Work.Construction.L12 F z'') z')) z := hdC.const_mul _
    have hsub : deriv (fun z' => z' * Work.Spaces.pz Φ z' θ
          - ((1 / (4 * α)) * Work.Construction.s2 θ)
              * (z' * deriv (fun z'' => Work.Construction.L12 F z'') z')) z
        = deriv (fun z' => z' * Work.Spaces.pz Φ z' θ) z
          - deriv (fun z' => ((1 / (4 * α)) * Work.Construction.s2 θ)
              * (z' * deriv (fun z'' => Work.Construction.L12 F z'') z')) z :=
      (hdA.hasDerivAt.sub hdD.hasDerivAt).deriv
    have hpzA : deriv (fun z' => z' * Work.Spaces.pz Φ z' θ) z
        = Work.Spaces.pz (Work.Spaces.Dz Φ) z θ := rfl
    have hB : deriv (fun z' => ((1 / (4 * α)) * Work.Construction.s2 θ)
          * (z' * deriv (fun z'' => Work.Construction.L12 F z'') z')) z
        = ((1 / (4 * α)) * Work.Construction.s2 θ)
            * deriv (fun z' => z' * deriv (fun z'' => Work.Construction.L12 F z'') z') z :=
      deriv_const_mul _ hdC
    rw [hsub, hpzA, hB]
  -- the `D_z`-derivative of the `U`-slot
  have hUslot : Work.Spaces.Dz (fun z θ => Work.Construction.Uop α
        (Work.Construction.PhiTil α F Φ) z θ / Work.Construction.s2 θ) z θ
      = z * deriv (fun z' => Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z' θ) z
          / Work.Construction.s2 θ := by
    simp only [Work.Spaces.Dz, Work.Spaces.pz, deriv_div_const]
    ring
  have hUop : deriv (fun z' => Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z' θ) z
      = -3 * deriv (fun z' => Work.Construction.PhiTil α F Φ z' θ) z
        - α * deriv (fun z' => z' * Work.Spaces.pz (Work.Construction.PhiTil α F Φ) z' θ) z := by
    have hfun : (fun z' => Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z' θ)
        = fun z' => -3 * Work.Construction.PhiTil α F Φ z' θ
            - α * (z' * Work.Spaces.pz (Work.Construction.PhiTil α F Φ) z' θ) := by
      funext z'
      simp only [Work.Construction.Uop]
      ring
    have hA : deriv (fun z' => -3 * Work.Construction.PhiTil α F Φ z' θ) z
        = -3 * deriv (fun z' => Work.Construction.PhiTil α F Φ z' θ) z :=
      deriv_const_mul (-3) hdΨ
    have hB : deriv (fun z' => α * (z' * Work.Spaces.pz (Work.Construction.PhiTil α F Φ) z' θ)) z
        = α * deriv (fun z' => z' * Work.Spaces.pz (Work.Construction.PhiTil α F Φ) z' θ) z :=
      deriv_const_mul α hd2Ψ
    rw [hfun]
    rw [show (fun z' => -3 * Work.Construction.PhiTil α F Φ z' θ
          - α * (z' * Work.Spaces.pz (Work.Construction.PhiTil α F Φ) z' θ))
        = (fun z' => -3 * Work.Construction.PhiTil α F Φ z' θ)
          - (fun z' => α * (z' * Work.Spaces.pz (Work.Construction.PhiTil α F Φ) z' θ))
        from rfl]
    rw [deriv_sub (hdΨ.const_mul (-3)) (hd2Ψ.const_mul α), hA, hB]
  -- the two `z`-normalisations
  have hpzA : Work.Spaces.pz Φ z θ = Work.Spaces.mixed 1 0 Φ z θ / z := by
    show Work.Spaces.pz Φ z θ = (z * Work.Spaces.pz Φ z θ) / z
    rw [mul_comm, mul_div_cancel_right₀ _ (ne_of_gt hz)]
  have hpzB : Work.Spaces.pz (Work.Spaces.Dz Φ) z θ = Work.Spaces.mixed 2 0 Φ z θ / z := by
    show Work.Spaces.pz (Work.Spaces.Dz Φ) z θ = (z * Work.Spaces.pz (Work.Spaces.Dz Φ) z θ) / z
    rw [mul_comm, mul_div_cancel_right₀ _ (ne_of_gt hz)]
  rw [hUslot, hUop, hderΨ, hder2Ψ, hder2L, hLd z hz, hpzA, hpzB]
  field_simp
  ring

end Work.FTS_StreamBdry.SB4
end
end
