import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
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
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Distribution.DerivNotation
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Tactic.Have
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.MinImports
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.CoercivityFix.PsiMul.PsiZop
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.A_sq_prod_le
import Submission.Work.FTS.EllipticEst.AeS1.SigFirstOrderDefs
import Submission.Work.FTS.EllipticEst.H2W.Ae.TruncIdentAe
import Submission.Work.FTS.EllipticEst.H2W.Ae.aeSigmaSliceLower
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeGapSlices
import Submission.Work.FTS.EllipticEst.H2W.ESV.easySlotsAssembly
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.Honest.I4UpperHonest
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.TT.ESW.Tk_B_le_chain_uniform
import Submission.Work.FTS.EllipticEst.TT.psiDerivSq_lower
import Submission.Work.FTS.EllipticEst.ZCuts.zHardy_compact
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.remov.SrdFork.EllWeakPos_DzIter_one_shift_fork
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.EllipticEst.remov.wsMomentId
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.integral_sin_two_rpow_neg
import Submission.Work.FTS.LocDataExt.Final
import Submission.Work.FTS.LocDataExt.LocG5
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.Nonlinear.N4Fields.wang_field_smoothInt
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.OpenPkg.ProdOpen.Tools1d
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.FTS.OpenPkg.l12_open_bundle
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeDefs
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6.HkN_sepF_le
import Submission.Work.FTS.StrongPersist.N6.Slots
import Submission.Work.FTS.StrongPersist.N6.sliceAvg_le6
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.StrongPersist.QangSq6
import Submission.Work.FTS.StrongPersist.QangSq6Full
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS.TransportS.SupDzWeighted.supDz_weighted_avg_le
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.H2.T1Q.QDefs
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.H2.T1Q.SlotPtQ
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H2.T1Q.T1EasyContQ
import Submission.Work.H2.WPQ.hardy_slice_Aang
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.H2W.PsiSlices.shiftedSourcePoleBound
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.aesm_HkIntegrand_quad
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.continuousOn_HkIntegrand_Qd
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.sup_mixed_le_H4
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.VT.Assembly =====
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

theorem Kop_eq_zero_of_notMem_tsupport {ψ : E2 → ℂ} (hψs : ∀ n : ℕ, ContDiff ℝ n ψ) {x : E2}
    (hx : x ∉ tsupport ψ) : Kop ψ x = 0 := by
  have hd0 : d0 ψ x = 0 := d0_eq_zero_of_notMem_tsupport hψs hx
  have hd1 : d1 ψ x = 0 := d1_eq_zero_of_notMem_tsupport hψs hx
  have hd0' : d0 (d0 ψ) x = 0 :=
    d0_eq_zero_of_notMem_tsupport (fun k => contDiff_d0 hψs k)
      (fun h => hx ((tsupport_d0_subset hψs) h))
  have hd1' : d1 (d1 ψ) x = 0 :=
    d1_eq_zero_of_notMem_tsupport (fun k => contDiff_d1 hψs k)
      (fun h => hx ((tsupport_d1_subset hψs) h))
  have hψ0 : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx
  simp only [Kop, hd0, hd1, hd0', hd1', hψ0, mul_zero, add_zero, sub_zero, zero_add, neg_zero]


/-- A compactly supported function times a function continuous on an open set containing its
support is integrable. -/
theorem integrable_mul_of_continuousOn {g Φ : E2 → ℂ} (hgc : HasCompactSupport g)
    (hgs : ∀ n : ℕ, ContDiff ℝ n g) {U : Set E2} (hU : IsOpen U) (hsub : tsupport g ⊆ U)
    (hΦ : ContinuousOn Φ U) : Integrable (fun x => g x * Φ x) := by
  have hOn : IntegrableOn (fun x => g x * Φ x) (tsupport g) :=
    (integrable_of_smooth_compact hgc hgs).integrableOn.mul_continuousOn
      (hΦ.mono hsub) hgc
  have hsupp : Function.support (fun x => g x * Φ x) ⊆ tsupport g := by
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hxg
    rw [image_eq_zero_of_notMem_tsupport hxg, zero_mul] at hx
    exact hx rfl
  have hind : Integrable ((tsupport g).indicator (fun x => g x * Φ x)) :=
    (integrable_indicator_iff (show IsCompact (tsupport g) from hgc).measurableSet).mpr hOn
  rwa [indicator_eq_self.mpr hsupp] at hind


theorem tsupport_ofReal_subset {c : E2 → ℝ} :
    tsupport (fun x : E2 => ((c x : ℝ) : ℂ)) ⊆ tsupport c := by
  rw [tsupport, tsupport]
  refine closure_mono ?_
  intro x hx
  rw [Function.mem_support] at hx ⊢
  intro h0
  exact hx (by rw [h0]; simp)

theorem hasCompactSupport_ofReal {c : E2 → ℝ} (hc : HasCompactSupport c) :
    HasCompactSupport (fun x : E2 => ((c x : ℝ) : ℂ)) :=
  IsCompact.of_isClosed_subset (show IsCompact (tsupport c) from hc) (isClosed_tsupport _)
    tsupport_ofReal_subset

/-- A compactly supported smooth *real* function times a function continuous on an open set
containing its support is integrable. -/
theorem integrable_smul_of_continuousOn {c : E2 → ℝ} (hcc : HasCompactSupport c)
    (hcs : ∀ n : ℕ, ContDiff ℝ n c) {Φ : E2 → ℂ} {U : Set E2} (hU : IsOpen U)
    (hsub : tsupport c ⊆ U) (hΦ : ContinuousOn Φ U) :
    Integrable (fun x => c x • Φ x) := by
  have hcs' : ∀ n : ℕ, ContDiff ℝ n (fun x : E2 => ((c x : ℝ) : ℂ)) :=
    fun n => Complex.ofRealCLM.contDiff.comp (hcs n)
  refine (integrable_mul_of_continuousOn (hasCompactSupport_ofReal hcc) hcs' hU
    (tsupport_ofReal_subset.trans hsub) hΦ).congr
    (Filter.Eventually.of_forall fun x => ?_)
  exact (Complex.real_smul : c x • Φ x = ((c x : ℝ) : ℂ) * Φ x).symm

/-- A compactly supported smooth *real* function times an integrable function is integrable. -/
theorem integrable_smul_of_cc {V : E2 → ℂ} (hV : Integrable V) {c : E2 → ℝ}
    (hcc : HasCompactSupport c) (hcs : ∀ n : ℕ, ContDiff ℝ n c) :
    Integrable (fun x => c x • V x) := by
  have hcs' : ∀ n : ℕ, ContDiff ℝ n (fun x : E2 => ((c x : ℝ) : ℂ)) :=
    fun n => Complex.ofRealCLM.contDiff.comp (hcs n)
  refine (integrable_mul_of_cc hV (hasCompactSupport_ofReal hcc) hcs').congr
    (Filter.Eventually.of_forall fun x => ?_)
  exact (Complex.real_smul : c x • V x = ((c x : ℝ) : ℂ) * V x).symm

end Work.EllipticEst.InteriorRegularity.VT
end
end
-- ===== merged: Submission.Work.FTS.Apriori.Limit.integral_pth_eq_zero =====
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

theorem integral_pth_eq_zero {W : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry W) Qd)
    (hcomp : HasCompactSupport (Function.uncurry W)) (hsub : tsupport (Function.uncurry W) ⊆ Qd) :
    ∫ p, Work.Spaces.pth W p.1 p.2 ∂Qμ = 0 := by
  obtain ⟨A, B, C, D, hA, hAB, hC, hCD, hD, hvA, hvB, hvC, hvD⟩ := exists_box_vanish hcomp hsub
  have hC' : 0 < C / 2 := by linarith
  have hC'C : C / 2 < C := by linarith
  have hCD' : C / 2 ≤ (D + π / 2) / 2 := by linarith
  have hDD' : D < (D + π / 2) / 2 := by linarith
  have hD' : (D + π / 2) / 2 < π / 2 := by linarith
  have hint : Integrable (Function.uncurry (Work.Spaces.pth W)) Qμ :=
    integrable_of_continuousOn_of_support
      ((Work.FTS.LocData.contDiffOn_pth isOpen_Qd hsm).continuousOn)
      hcomp hsub (support_pth_subset_tsupport W)
  change ∫ p : ℝ × ℝ, Function.uncurry (Work.Spaces.pth W) p ∂Qμ = 0
  rw [Qμ]
  rw [MeasureTheory.integral_prod _ hint]
  have h0 : (fun z : ℝ => ∫ θ, Function.uncurry (Work.Spaces.pth W) (z, θ)
        ∂(volume.restrict Work.Spaces.Iθ)) = fun _ => (0 : ℝ) := by
    funext z
    show (∫ θ in Work.Spaces.Iθ, Work.Spaces.pth W z θ) = 0
    rw [Work.Spaces.Iθ]
    by_cases hz : 0 < z
    · have hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => W z θ)
          (Set.Ioo 0 (π / 2)) :=
        Work.FTS.LocData.contDiffOn_slice_θ hsm (by rw [Set.mem_Ioi]; exact hz)
      have hpthslice : ContDiffOn ℝ Work.Stability.smoothOrder
          (fun θ => Work.Spaces.pth W z θ) (Set.Ioo 0 (π / 2)) :=
        Work.FTS.LocData.contDiffOn_slice_θ
          (Work.FTS.LocData.contDiffOn_pth isOpen_Qd hsm) (by rw [Set.mem_Ioi]; exact hz)
      have hset : ∫ θ in Set.Icc (0 : ℝ) (π / 2), Work.Spaces.pth W z θ
          = ∫ θ in Set.Icc (C / 2) ((D + π / 2) / 2), Work.Spaces.pth W z θ := by
        refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc
          (Set.Icc_subset_Icc (by linarith) (by linarith)) (fun θ hθ => ?_)
        have hlt_or : θ < C / 2 ∨ (D + π / 2) / 2 < θ := by
          by_contra hcon
          push_neg at hcon
          exact hθ.2 (Set.mem_Icc.mpr hcon)
        rcases hlt_or with hlt | hgt
        · exact pth_eq_zero_of_forall_theta_lt hvC z θ (by linarith)
        · exact pth_eq_zero_of_forall_theta_gt hvD z θ (by linarith)
      rw [hset, MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hCD']
      have hcont : ContinuousOn (fun θ => W z θ) (Set.Icc (C / 2) ((D + π / 2) / 2)) :=
        hslice.continuousOn.mono (fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2]⟩)
      have hcont' : ContinuousOn (fun θ => Work.Spaces.pth W z θ)
          (Set.Icc (C / 2) ((D + π / 2) / 2)) :=
        hpthslice.continuousOn.mono (fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2]⟩)
      have hderiv : ∀ x ∈ Set.Ioo (C / 2) ((D + π / 2) / 2),
          HasDerivAt (fun θ => W z θ) (Work.Spaces.pth W z x) x := by
        intro x hx
        have hxmem : x ∈ Set.Ioo (0 : ℝ) (π / 2) :=
          ⟨by linarith [hx.1], by linarith [hx.2]⟩
        exact ((hslice.differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
          (isOpen_Ioo.mem_nhds hxmem)).hasDerivAt
      have hint' : IntervalIntegrable (fun θ => Work.Spaces.pth W z θ) volume (C / 2)
          ((D + π / 2) / 2) := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [Set.uIcc_of_le hCD']
        exact hcont'
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hCD' hcont hderiv hint',
        hvD z ((D + π / 2) / 2) hDD', hvC z (C / 2) hC'C]
      ring
    · have hz0 : ∀ θ, W z θ = 0 := by
        intro θ
        by_contra h
        have hmem : (z, θ) ∈ tsupport (Function.uncurry W) :=
          subset_tsupport _ (by simpa [Function.mem_support, Function.uncurry] using h)
        exact hz (mem_Qd_iff.mp (hsub hmem)).1
      rw [show (fun θ => Work.Spaces.pth W z θ) = fun _ => (0 : ℝ) from
        funext (fun θ => by simp [Work.Spaces.pth, funext hz0])]
      simp
  rw [h0, MeasureTheory.integral_zero]

end Work.FTS.Apriori.Limit
end
end
-- ===== merged: Submission.Work.FTS.Apriori.Limit.integral_pz_eq_zero =====
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

theorem integral_pz_eq_zero {W : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry W) Qd)
    (hcomp : HasCompactSupport (Function.uncurry W)) (hsub : tsupport (Function.uncurry W) ⊆ Qd) :
    ∫ p, Work.Spaces.pz W p.1 p.2 ∂Qμ = 0 := by
  obtain ⟨A, B, C, D, hA, hAB, hC, hCD, hD, hvA, hvB, hvC, hvD⟩ := exists_box_vanish hcomp hsub
  have hA' : 0 < A / 2 := by linarith
  have hA'A : A / 2 < A := by linarith
  have hBB' : B < B + 1 := by linarith
  have hA'B' : A / 2 ≤ B + 1 := by linarith
  have hint : Integrable (Function.uncurry (Work.Spaces.pz W)) Qμ :=
    integrable_of_continuousOn_of_support ((Work.FTS.LocData.contDiffOn_pz isOpen_Qd hsm).continuousOn)
      hcomp hsub (support_pz_subset_tsupport W)
  change ∫ p : ℝ × ℝ, Function.uncurry (Work.Spaces.pz W) p ∂Qμ = 0
  rw [Qμ]
  rw [MeasureTheory.integral_prod_symm _ hint]
  have h0 : (fun θ : ℝ => ∫ z, Function.uncurry (Work.Spaces.pz W) (z, θ) ∂(volume.restrict Work.Spaces.Iz)) = fun _ => (0 : ℝ) := by
    funext θ
    show (∫ z, Work.Spaces.pz W z θ ∂(volume.restrict Work.Spaces.Iz)) = 0
    by_cases hθ : θ ∈ Set.Ioo 0 (π / 2)
    · have hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => W z θ) (Set.Ioi 0) :=
        Work.FTS.LocData.contDiffOn_slice_z hsm hθ
      have hpzslice : ContDiffOn ℝ Work.Stability.smoothOrder
          (fun z => Work.Spaces.pz W z θ) (Set.Ioi 0) :=
        Work.FTS.LocData.contDiffOn_slice_z (Work.FTS.LocData.contDiffOn_pz isOpen_Qd hsm) hθ
      have hIz : ∫ z, Work.Spaces.pz W z θ ∂(volume.restrict Work.Spaces.Iz)
          = ∫ z in Set.Ioi (0 : ℝ), Work.Spaces.pz W z θ := by
        rw [Work.Spaces.Iz]
        rw [← MeasureTheory.Measure.restrict_congr_set
          (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
      rw [hIz]
      have hset : ∫ z in Set.Ioi (0 : ℝ), Work.Spaces.pz W z θ
          = ∫ z in Set.Icc (A / 2) (B + 1), Work.Spaces.pz W z θ := by
        refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
          (fun z hz => lt_of_lt_of_le hA' hz.1) (fun z hz => ?_)
        rw [Set.mem_sdiff, Set.mem_Icc, not_and_or] at hz
        rcases hz with ⟨hzpos, hz | hz⟩
        · exact pz_eq_zero_of_forall_lt hvA z θ (by linarith)
        · exact pz_eq_zero_of_forall_gt hvB z θ (by linarith)
      rw [hset, MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hA'B']
      have hcont : ContinuousOn (fun z => W z θ) (Set.Icc (A / 2) (B + 1)) :=
        hslice.continuousOn.mono (fun z hz => lt_of_lt_of_le hA' hz.1)
      have hcont' : ContinuousOn (fun z => Work.Spaces.pz W z θ)
          (Set.Icc (A / 2) (B + 1)) :=
        hpzslice.continuousOn.mono (fun z hz => lt_of_lt_of_le hA' hz.1)
      have hderiv : ∀ x ∈ Set.Ioo (A / 2) (B + 1),
          HasDerivAt (fun z => W z θ) (Work.Spaces.pz W x θ) x := by
        intro x hx
        have hx0 : x ∈ Set.Ioi (0 : ℝ) := by
          rw [Set.mem_Ioi]; linarith [hx.1]
        exact ((hslice.differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
          (isOpen_Ioi.mem_nhds hx0)).hasDerivAt
      have hint' : IntervalIntegrable (fun z => Work.Spaces.pz W z θ) volume (A / 2) (B + 1) := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [Set.uIcc_of_le hA'B']
        exact hcont'
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hA'B' hcont hderiv hint',
        hvB (B + 1) θ hBB', hvA (A / 2) θ hA'A]
      ring
    · have hz0 : ∀ z, W z θ = 0 := by
        intro z
        by_contra h
        have hmem : (z, θ) ∈ tsupport (Function.uncurry W) :=
          subset_tsupport _ (by simpa [Function.mem_support, Function.uncurry] using h)
        exact hθ (mem_Qd_iff.mp (hsub hmem)).2
      rw [show (fun z => Work.Spaces.pz W z θ) = fun _ => (0 : ℝ) from
        funext (fun z => by simp [Work.Spaces.pz, funext hz0])]
      simp
  rw [h0, MeasureTheory.integral_zero]

end Work.FTS.Apriori.Limit
end
end
-- ===== merged: Submission.Work.FTS.Apriori.Profile.linf_H2_quad =====
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




end Work.FTS.Apriori.Profile
end
end
-- ===== merged: Submission.Work.FTS.ClassC.RopGen.Trace.ZmollAux.zmollDzPth =====
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

open Work.FTS.EllSol.PkgK5.K5c (Qext thMoll zmoll sKer)
open Work.FTS.EllSol.EllPkgAux (sKerd Hxyc)

/-- **The mixed derivative of the double mollification.** -/
theorem zmollDzPth (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hdom : MeasureTheory.LocallyIntegrable (fun t : ℝ => ∫ s in Work.Spaces.Iθ,
      |Hxyc G t s|) MeasureTheory.volume)
    {δ ε : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      Work.Spaces.Dz (Work.Spaces.pth (zmoll G δ ε)) z θ
        = ∫ t : ℝ, sKerd δ (Real.log z - t)
            * (∫ s : ℝ, sKerd ε (θ - s) * Hxyc G t s) := by
  intro z hz θ hθ
  have hS : Work.FTS.EllipticEst.SmoothOpen G := hT.1
  have hθw : θ ∈ Set.Ioo (-(1 / 4) : ℝ) (Real.pi / 2 + 1 / 4) := by
    obtain ⟨h1, h2⟩ := Set.mem_Icc.mp hθ
    exact ⟨by linarith, by linarith⟩
  -- the angular derivative slice is locally integrable
  obtain ⟨Mε, hMε0, hMεb, hMεv⟩ := exists_kernel_bound
    (Work.FTS.EllSol.EllPkgAux.MollDzAux.continuous_sKerd ε) hε0
    (fun x hx => Work.FTS.EllSol.EllPkgAux.MollDzAux.sKerd_eq_zero_of_lt_abs hε0 hx)
  have hli : MeasureTheory.LocallyIntegrable (fun t : ℝ => ∫ s : ℝ,
      sKerd ε (θ - s) * Hxyc G t s) MeasureTheory.volume :=
    hxycSliceLocIntHonest G hT hdom
      (Work.FTS.EllSol.EllPkgAux.MollDzAux.continuous_sKerd ε) hε0 hε1 hMε0 hMεb hMεv hθw
  -- the angular derivative, for every positive radius
  have hA : ∀ z' : ℝ, 0 < z' → Work.Spaces.pth (zmoll G δ ε) z' θ
      = ∫ t : ℝ, sKer δ (Real.log z' - t)
          * (∫ s : ℝ, sKerd ε (θ - s) * Hxyc G t s) :=
    fun z' hz' => zmollPthEq G hT hdom hδ0 hδ1 hε0 hε1 hz' hθ
  have hcongr : (fun z' : ℝ => Work.Spaces.pth (zmoll G δ ε) z' θ)
      =ᶠ[𝓝 z] (fun z' : ℝ => ∫ t : ℝ, sKer δ (Real.log z' - t)
          * (∫ s : ℝ, sKerd ε (θ - s) * Hxyc G t s)) :=
    Filter.Eventually.mono (Ioi_mem_nhds hz) (fun z' hz' => hA z' hz')
  calc Work.Spaces.Dz (Work.Spaces.pth (zmoll G δ ε)) z θ
      = z * deriv (fun z' : ℝ => Work.Spaces.pth (zmoll G δ ε) z' θ) z := rfl
    _ = z * deriv (fun z' : ℝ => ∫ t : ℝ, sKer δ (Real.log z' - t)
          * (∫ s : ℝ, sKerd ε (θ - s) * Hxyc G t s)) z := by
        rw [Filter.EventuallyEq.deriv_eq hcongr]
    _ = ∫ t : ℝ, sKerd δ (Real.log z - t)
          * (∫ s : ℝ, sKerd ε (θ - s) * Hxyc G t s) :=
        logConvDeriv (fun t : ℝ => ∫ s : ℝ, sKerd ε (θ - s) * Hxyc G t s) hli hδ0 z hz

end Work.FTS.ClassC.RopGen.Trace.ZmollAux
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Assembly.Comm2_succ =====
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

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Locality and linearity of the two derivatives on the open quadrant

The open quadrant `Qd = (0,∞) × (0,π/2)` is `Work.Construction.Qd`, definitionally
`Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2)`.  Both facts are *pointwise on `Qd`*, which is exactly the
form in which the `congr` clause of `Comm2` is stated. -/

/-- Two functions that agree on the open quadrant have the same `D_θ` there:
the derivative is local and `Qd` is open in the `θ`-variable. -/
private lemma Dth_congr_Qd {f f' : Fn}
    (h : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dth f z θ = Work.Spaces.Dth f' z θ := by
  intro z θ hzθ
  have hz : z ∈ Set.Ioi (0 : ℝ) := hzθ.1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hzθ.2
  have heq : (fun θ' : ℝ => f z θ') =ᶠ[𝓝 θ] (fun θ' : ℝ => f' z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact h z θ' ⟨hz, hθ'⟩
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [heq.deriv_eq]

/-- Two functions that agree on the open quadrant have the same `D_z` there. -/
private lemma Dz_congr_Qd {f f' : Fn}
    (h : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dz f z θ = Work.Spaces.Dz f' z θ := by
  intro z θ hzθ
  have hz : z ∈ Set.Ioi (0 : ℝ) := hzθ.1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hzθ.2
  have heq : (fun z' : ℝ => f z' θ) =ᶠ[𝓝 z] (fun z' : ℝ => f' z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact h z' θ ⟨hz', hθ⟩
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [heq.deriv_eq]

/-- `D_θ` is additive on the open quadrant, for `SmoothQuad` functions. -/
private lemma Dth_add_Qd {f₁ f₂ : Fn} (h₁ : Work.FTS.LocData.SmoothQuad f₁)
    (h₂ : Work.FTS.LocData.SmoothQuad f₂) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dth (f₁ + f₂) z θ = Work.Spaces.Dth f₁ z θ + Work.Spaces.Dth f₂ z θ := by
  intro z θ hzθ
  have hz : z ∈ Set.Ioi (-1 : ℝ) := Set.mem_Ioi.mpr (by linarith [Set.mem_Ioi.mp hzθ.1])
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hzθ.2
  have hd : ∀ f : Fn, Work.FTS.LocData.SmoothQuad f →
      DifferentiableAt ℝ (fun θ' => f z θ') θ :=
    fun f hf => hf.differentiableAt_slice_DthIter 0 hz hθ
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [show (fun θ' => (f₁ + f₂) z θ') = (fun θ' => f₁ z θ') + (fun θ' => f₂ z θ') from rfl,
    deriv_add (hd f₁ h₁) (hd f₂ h₂)]
  ring

/-- `D_z` is additive on the open quadrant, for `SmoothQuad` functions. -/
private lemma Dz_add_Qd {f₁ f₂ : Fn} (h₁ : Work.FTS.LocData.SmoothQuad f₁)
    (h₂ : Work.FTS.LocData.SmoothQuad f₂) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dz (f₁ + f₂) z θ = Work.Spaces.Dz f₁ z θ + Work.Spaces.Dz f₂ z θ := by
  intro z θ hzθ
  have hz : z ∈ Set.Ioi (-1 : ℝ) := Set.mem_Ioi.mpr (by linarith [Set.mem_Ioi.mp hzθ.1])
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hzθ.2
  have hd : ∀ f : Fn, Work.FTS.LocData.SmoothQuad f →
      DifferentiableAt ℝ (fun z' => f z' θ) z :=
    fun f hf => hf.differentiableAt_slice_mixed 0 0 hz hθ
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [show (fun z' => (f₁ + f₂) z' θ) = (fun z' => f₁ z' θ) + (fun z' => f₂ z' θ) from rfl,
    deriv_add (hd f₁ h₁) (hd f₂ h₂)]
  ring

/-! ## The induction step of the package -/

/-- **`Comm2` climbs one level under the paper's recursion `HkIPStep c₁ c₂`.**  The two
commutator clauses are inherited verbatim (they mention neither the level `n` nor the inner
product), and the congruence/additivity clauses are transported through the two
derivative-locality / derivative-linearity facts above. -/
theorem Comm2_succ (α : ℝ) (hα : 0 < α) (n : ℕ) {IP : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ}
    {c₁ c₂ : ℝ} (hc : Work.FTS.CoercivityFix.Assembly.Comm2 α n IP) :
    Work.FTS.CoercivityFix.Assembly.Comm2 α (n + 1)
      (Work.Coercivity.HkIPStep c₁ c₂ IP) := by
  refine ⟨?congr, ?add, hc.dthC, hc.dzC⟩
  case congr =>
    intro f f' g hfg
    have e0 := hc.congr f f' g hfg
    have e1 := hc.congr (Work.Spaces.Dth f) (Work.Spaces.Dth f') (Work.Spaces.Dth g)
      (Dth_congr_Qd hfg)
    have e2 := hc.congr (Work.Spaces.Dz f) (Work.Spaces.Dz f') (Work.Spaces.Dz g)
      (Dz_congr_Qd hfg)
    simp only [Work.Coercivity.HkIPStep, e0, e1, e2]
  case add =>
    intro f₁ f₂ g hf₁ hf₂ hg
    have h₁ : Work.FTS.Nonlin.RegQ α n f₁ :=
      Work.FTS.GalerkinFix.RegQ.regQ_mono hf₁ (Nat.le_succ n)
    have h₂ : Work.FTS.Nonlin.RegQ α n f₂ :=
      Work.FTS.GalerkinFix.RegQ.regQ_mono hf₂ (Nat.le_succ n)
    have h₃ : Work.FTS.Nonlin.RegQ α n g :=
      Work.FTS.GalerkinFix.RegQ.regQ_mono hg (Nat.le_succ n)
    have e0 := hc.add f₁ f₂ g h₁ h₂ h₃
    have e1 : IP (Work.Spaces.Dth (f₁ + f₂)) (Work.Spaces.Dth g)
        = IP (Work.Spaces.Dth f₁) (Work.Spaces.Dth g)
          + IP (Work.Spaces.Dth f₂) (Work.Spaces.Dth g) := by
      rw [hc.congr (Work.Spaces.Dth (f₁ + f₂))
        (Work.Spaces.Dth f₁ + Work.Spaces.Dth f₂) (Work.Spaces.Dth g)
        (fun z θ hzθ => Dth_add_Qd hf₁.1 hf₂.1 z θ hzθ)]
      exact hc.add (Work.Spaces.Dth f₁) (Work.Spaces.Dth f₂) (Work.Spaces.Dth g)
        (Work.FTS.CoercivityFix.QuadPorts.RegQ_dth α hα hf₁)
        (Work.FTS.CoercivityFix.QuadPorts.RegQ_dth α hα hf₂)
        (Work.FTS.CoercivityFix.QuadPorts.RegQ_dth α hα hg)
    have e2 : IP (Work.Spaces.Dz (f₁ + f₂)) (Work.Spaces.Dz g)
        = IP (Work.Spaces.Dz f₁) (Work.Spaces.Dz g)
          + IP (Work.Spaces.Dz f₂) (Work.Spaces.Dz g) := by
      rw [hc.congr (Work.Spaces.Dz (f₁ + f₂))
        (Work.Spaces.Dz f₁ + Work.Spaces.Dz f₂) (Work.Spaces.Dz g)
        (fun z θ hzθ => Dz_add_Qd hf₁.1 hf₂.1 z θ hzθ)]
      exact hc.add (Work.Spaces.Dz f₁) (Work.Spaces.Dz f₂) (Work.Spaces.Dz g)
        (Work.FTS.CoercivityFix.QuadPorts.RegQ_dz α hf₁)
        (Work.FTS.CoercivityFix.QuadPorts.RegQ_dz α hf₂)
        (Work.FTS.CoercivityFix.QuadPorts.RegQ_dz α hg)
    simp only [Work.Coercivity.HkIPStep, e0, e1, e2]
    ring

end Work.FTS.CoercivityFix.Assembly
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Assembly.E2hat_HkSq_le_uniform =====
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
set_option maxHeartbeats 1600000

/-! ## The two blocks of the `ℋⁿ`-integrand -/

/-- The pure (`D_z`-only) block of the `ℋⁿ`-integrand: without the angular weight
`Wt α` this block is *independent of `α`*. -/
private def zblk (n : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    (Work.Spaces.DzIter i g z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2

/-- The mixed block of the `ℋⁿ`-integrand, **without** the angular weight: the sum of the
squares of the genuinely mixed derivatives `D_z^jD_θ^i g`, `1 ≤ i`, `i + j ≤ n`. -/
private def mblk (n : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
    (if 1 ≤ i ∧ i + j ≤ n then (Work.Spaces.mixed j i g z θ) ^ 2 else 0)

private lemma zblk_nonneg (n : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) : 0 ≤ zblk n g z θ :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

private lemma mblk_nonneg (n : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) : 0 ≤ mblk n g z θ :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by split_ifs <;> positivity

/-- **The exact identity** expressing `HkIntegrand` through the two blocks: the angular
weight `Wt α z θ` is constant in the summation indices of the mixed block, hence it can be
pulled out of the sum of squares. -/
private lemma HkIntegrand_eq_zblk_add (α : ℝ) (n : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α n g z θ
      = zblk n g z θ + (Work.Spaces.Wt α z θ) ^ 2 * mblk n g z θ := by
  have hpt : ∀ i j : ℕ,
      (if 1 ≤ i ∧ i + j ≤ n
        then (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
      = (Work.Spaces.Wt α z θ) ^ 2
        * (if 1 ≤ i ∧ i + j ≤ n then (Work.Spaces.mixed j i g z θ) ^ 2 else 0) := by
    intro i j
    by_cases hc : 1 ≤ i ∧ i + j ≤ n
    · rw [if_pos hc, if_pos hc]; ring
    · rw [if_neg hc, if_neg hc]; ring
  have hkey : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        (if 1 ≤ i ∧ i + j ≤ n
          then (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      = (Work.Spaces.Wt α z θ) ^ 2 * mblk n g z θ := by
    simp only [mblk]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => hpt i j
  simp only [Work.Spaces.HkIntegrand, zblk]
  rw [hkey]

/-- At `z = 0` the radial weight `w 0 = 0` kills every summand of the integrand. -/
private lemma HkIntegrand_zero_z (α : ℝ) (n : ℕ) (g : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α n g 0 θ = 0 := by
  rw [HkIntegrand_eq_zblk_add]
  have hw : Work.Spaces.w 0 = 0 := by simp [Work.Spaces.w]
  have hz : zblk n g 0 θ = 0 := by
    simp only [zblk, hw, zero_div, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      Finset.sum_const_zero]
  have hW : Work.Spaces.Wt α 0 θ = 0 := by simp [Work.Spaces.Wt, Work.Spaces.w]
  rw [hz, hW]
  ring

/-! ## Extracting single slots -/

/-- Each pure summand of `zblk` is at most the whole of `zblk`. -/
private lemma zslot_le (n : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) {r : ℕ} (hr : r ≤ n) :
    (Work.Spaces.DzIter r g z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ zblk n g z θ :=
  Finset.single_le_sum
    (s := Finset.range (n + 1))
    (f := fun i => (Work.Spaces.DzIter i g z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))

/-- Each mixed summand of `mblk` is at most the whole of `mblk`. -/
private lemma mslot_le (n : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) {a b : ℕ}
    (ha : 1 ≤ a) (hab : a + b ≤ n) :
    (Work.Spaces.mixed b a g z θ) ^ 2 ≤ mblk n g z θ := by
  have han : a ≤ n := le_trans (Nat.le_add_right a b) hab
  have hbn : b ≤ n := le_trans (Nat.le_add_left b a) hab
  have h1 : (Work.Spaces.mixed b a g z θ) ^ 2
      ≤ ∑ j ∈ Finset.range (n + 1),
          (if 1 ≤ a ∧ a + j ≤ n then (Work.Spaces.mixed j a g z θ) ^ 2 else 0) := by
    have h := Finset.single_le_sum
      (s := Finset.range (n + 1))
      (f := fun j => (if 1 ≤ a ∧ a + j ≤ n
        then (Work.Spaces.mixed j a g z θ) ^ 2 else 0))
      (fun j _ => by split_ifs <;> positivity)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hbn))
    rwa [if_pos ⟨ha, hab⟩] at h
  have h2 : (∑ j ∈ Finset.range (n + 1),
        (if 1 ≤ a ∧ a + j ≤ n then (Work.Spaces.mixed j a g z θ) ^ 2 else 0))
      ≤ mblk n g z θ := by
    simp only [mblk]
    exact Finset.single_le_sum
      (s := Finset.range (n + 1))
      (f := fun i => ∑ j ∈ Finset.range (n + 1),
        (if 1 ≤ i ∧ i + j ≤ n then (Work.Spaces.mixed j i g z θ) ^ 2 else 0))
      (fun i _ => Finset.sum_nonneg fun j _ => by split_ifs <;> positivity)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le han))
  exact le_trans h1 h2

/-- The binomial coefficients of order `≤ n` have square at most `4ⁿ`. -/
private lemma choose_sq_le_four_pow (n i b : ℕ) (hi : i ≤ n) :
    (((i.choose b : ℕ)) : ℝ) ^ 2 ≤ (4 : ℝ) ^ n := by
  have h1 : i.choose b ≤ 2 ^ i := Nat.choose_le_two_pow i b
  have h2 : (((i.choose b : ℕ)) : ℝ) ≤ (2 : ℝ) ^ i := by exact_mod_cast h1
  have h3 : (2 : ℝ) ^ i ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hi
  have h4 : (((i.choose b : ℕ) : ℝ)) ^ 2 ≤ ((2 : ℝ) ^ i) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2 2
  have h5 : ((2 : ℝ) ^ i) ^ 2 = (4 : ℝ) ^ i := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
    ring
  have h6 : (4 : ℝ) ^ i ≤ (4 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hi
  linarith [h4, h6, h5.le]

/-! ## The α-free multiplier estimate for the pure block -/

/-- `mixed_zmul` at `i = 0`: the Leibniz rule for `D_z^j` acting on `φ(z)·g`. -/
private lemma DzIter_zmul_eq (j : ℕ) (a : ℝ → ℝ) (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hz : z ∈ Set.Ioi (-1)) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (ha : Work.FTS.LocData.SmoothQuad (fun z θ : ℝ => a z))
    (hg : Work.FTS.LocData.SmoothQuad g) :
    Work.Spaces.DzIter j (fun z θ : ℝ => a z * g z θ) z θ
      = ∑ b ∈ Finset.range (j + 1), (((j.choose b : ℕ)) : ℝ)
          * (Work.Spaces.Zop^[b] a z * Work.Spaces.DzIter (j - b) g z θ) := by
  have h := Work.FTS.CoercivityFix.E2Bound.mixed_zmul j 0 a g hz hθ ha hg
  simpa only [Work.Spaces.mixed_zero_right] using h

/-- **The pure block of `φ·g` is dominated by the pure block of `g`**, with a constant
depending only on `n` (and not on `α`, `z`, `θ`). -/
private theorem zblk_zmul_le (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ → ℝ), Work.FTS.LocData.SmoothQuad f →
      ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        zblk n (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ ≤ C * zblk n f z θ := by
  obtain ⟨K, _hKnn, hKbd⟩ :=
    Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_phiZ_bound n
  refine ⟨((n : ℝ) + 1) ^ 4 * (4 : ℝ) ^ n * K ^ 2 + 1, by positivity, ?_⟩
  intro f hf z hz θ hθ
  have hzpos : (0 : ℝ) < z := Set.mem_Ioi.mp hz
  have hz1 : z ∈ Set.Ioi (-1 : ℝ) := Set.mem_Ioi.mpr (by linarith)
  have hphi : Work.FTS.LocData.SmoothQuad (fun z θ : ℝ => z / (1 + z) ^ 2) :=
    Work.FTS.CoercivityFix.E2Bound.smoothQuad_zDiv
  have hZnn : 0 ≤ zblk n f z θ := zblk_nonneg n f z θ
  have hper : ∀ i ∈ Finset.range (n + 1),
      (Work.Spaces.DzIter i (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ ((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n * K ^ 2 * zblk n f z θ := by
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hDz := DzIter_zmul_eq i (fun z : ℝ => z / (1 + z) ^ 2) f hz1 hθ hphi hf
    -- insert the radial weight and reassociate
    have hsplit : Work.Spaces.DzIter i (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
        = ∑ b ∈ Finset.range (i + 1), (((i.choose b : ℕ)) : ℝ)
            * (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z
              * (Work.Spaces.DzIter (i - b) f z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) := by
      rw [hDz, Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [hsplit]
    -- Cauchy–Schwarz on the binomial sum
    have hcs : (∑ b ∈ Finset.range (i + 1), (((i.choose b : ℕ)) : ℝ)
          * (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2
        ≤ ((i : ℝ) + 1) * ∑ b ∈ Finset.range (i + 1), ((((i.choose b : ℕ)) : ℝ)
          * (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2 := by
      have h0 := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
        (f := fun b => (((i.choose b : ℕ)) : ℝ)
          * (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))))
      have hcard : (((Finset.range (i + 1)).card : ℕ) : ℝ) = (i : ℝ) + 1 := by
        rw [Finset.card_range]; push_cast; ring
      simpa only [hcard] using h0
    refine le_trans hcs ?_
    have hterm : ∀ b ∈ Finset.range (i + 1),
        ((((i.choose b : ℕ)) : ℝ)
          * (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2
        ≤ (4 : ℝ) ^ n * K ^ 2
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      intro b hb
      have hbn : b ≤ n :=
        le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)) hin
      have hZb : |Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z| ≤ K :=
        hKbd b hbn z hz
      have hZb2 : (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z) ^ 2 ≤ K ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hZb 2
      have hcb := choose_sq_le_four_pow n i b hin
      calc ((((i.choose b : ℕ)) : ℝ)
            * (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z
              * (Work.Spaces.DzIter (i - b) f z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2
          = (((i.choose b : ℕ)) : ℝ) ^ 2
              * (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z) ^ 2
              * (Work.Spaces.DzIter (i - b) f z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
            ring
        _ ≤ (4 : ℝ) ^ n * K ^ 2
              * (Work.Spaces.DzIter (i - b) f z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
            exact mul_le_mul hcb hZb2 (sq_nonneg _) (by positivity)
    have hslot : ∀ b ∈ Finset.range (i + 1),
        (Work.Spaces.DzIter (i - b) f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ zblk n f z θ :=
      fun b hb => zslot_le n f z θ (r := i - b) (by
        have hb' : b ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
        omega)
    have hsum : (∑ b ∈ Finset.range (i + 1), ((((i.choose b : ℕ)) : ℝ)
          * (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z
            * (Work.Spaces.DzIter (i - b) f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2)
        ≤ ∑ _b ∈ Finset.range (i + 1), ((4 : ℝ) ^ n * K ^ 2 * zblk n f z θ) :=
      Finset.sum_le_sum fun b hb => le_trans (hterm b hb)
        (mul_le_mul_of_nonneg_left (hslot b hb) (by positivity))
    refine le_trans (mul_le_mul_of_nonneg_left hsum (by positivity)) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    have hi1 : (i : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have := Nat.succ_le_succ hin
      exact_mod_cast this
    have hA : (0 : ℝ) ≤ (4 : ℝ) ^ n * K ^ 2 * zblk n f z θ :=
      mul_nonneg (by positivity) hZnn
    calc ((i : ℝ) + 1) * (((i : ℝ) + 1) * ((4 : ℝ) ^ n * K ^ 2 * zblk n f z θ))
        = ((i : ℝ) + 1) ^ 2 * ((4 : ℝ) ^ n * K ^ 2 * zblk n f z θ) := by ring
      _ ≤ ((n : ℝ) + 1) ^ 2 * ((4 : ℝ) ^ n * K ^ 2 * zblk n f z θ) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hi1 2) hA
      _ = ((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n * K ^ 2 * zblk n f z θ := by ring
  calc zblk n (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ
      = ∑ i ∈ Finset.range (n + 1),
          (Work.Spaces.DzIter i (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := rfl
    _ ≤ ∑ _i ∈ Finset.range (n + 1),
          (((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n * K ^ 2 * zblk n f z θ) :=
        Finset.sum_le_sum hper
    _ = ((n : ℝ) + 1) * (((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n * K ^ 2 * zblk n f z θ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ (((n : ℝ) + 1) ^ 4 * (4 : ℝ) ^ n * K ^ 2 + 1) * zblk n f z θ := by
        have hA : (0 : ℝ) ≤ (4 : ℝ) ^ n * K ^ 2 * zblk n f z θ :=
          mul_nonneg (by positivity) hZnn
        have hn1 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have hfac : (((n : ℝ) + 1) ^ 4 * (4 : ℝ) ^ n * K ^ 2 + 1) * zblk n f z θ
            - ((n : ℝ) + 1) * (((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n * K ^ 2 * zblk n f z θ)
            = ((n : ℝ) + 1) ^ 3 * (n : ℝ) * (4 : ℝ) ^ n * K ^ 2 * zblk n f z θ
              + zblk n f z θ := by ring
        have hlead : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 * (n : ℝ) * (4 : ℝ) ^ n := by positivity
        have hnn : 0 ≤ ((n : ℝ) + 1) ^ 3 * (n : ℝ) * (4 : ℝ) ^ n * K ^ 2 * zblk n f z θ :=
          mul_nonneg (mul_nonneg hlead (sq_nonneg K)) hZnn
        linarith [hfac, hnn, hZnn]

/-! ## The α-free multiplier estimate for the mixed block -/

/-- **The mixed block of `φ·g` is dominated by the mixed block of `g`**, with a constant
depending only on `n`.  Here the Leibniz rule `mixed_zmul` is applied directly: the
`z`-only factor `φ` is differentiated only in `z`, so each term of the expansion is a slot
of the mixed block of `g`. -/
private theorem mblk_zmul_le (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ → ℝ), Work.FTS.LocData.SmoothQuad f →
      ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        mblk n (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ ≤ C * mblk n f z θ := by
  obtain ⟨K, _hKnn, hKbd⟩ :=
    Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_phiZ_bound n
  refine ⟨((n : ℝ) + 1) ^ 4 * (4 : ℝ) ^ n * K ^ 2 + 1, by positivity, ?_⟩
  intro f hf z hz θ hθ
  have hzpos : (0 : ℝ) < z := Set.mem_Ioi.mp hz
  have hz1 : z ∈ Set.Ioi (-1 : ℝ) := Set.mem_Ioi.mpr (by linarith)
  have hphi : Work.FTS.LocData.SmoothQuad (fun z θ : ℝ => z / (1 + z) ^ 2) :=
    Work.FTS.CoercivityFix.E2Bound.smoothQuad_zDiv
  have hMnn : 0 ≤ mblk n f z θ := mblk_nonneg n f z θ
  have hper : ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (n + 1),
      (if 1 ≤ i ∧ i + j ≤ n
        then (Work.Spaces.mixed j i (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ) ^ 2
        else 0)
      ≤ ((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n * K ^ 2 * mblk n f z θ := by
    intro i hi j hj
    by_cases hc : 1 ≤ i ∧ i + j ≤ n
    · rw [if_pos hc]
      obtain ⟨hi1, hij⟩ := hc
      have hin : i ≤ n := by omega
      have hjn : j ≤ n := by omega
      have hlei := Work.FTS.CoercivityFix.E2Bound.mixed_zmul j i
        (fun z : ℝ => z / (1 + z) ^ 2) f hz1 hθ hphi hf
      rw [hlei]
      have hcs : (∑ b ∈ Finset.range (j + 1), (((j.choose b : ℕ)) : ℝ)
            * (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z
              * Work.Spaces.mixed (j - b) i f z θ)) ^ 2
          ≤ ((j : ℝ) + 1) * ∑ b ∈ Finset.range (j + 1), ((((j.choose b : ℕ)) : ℝ)
            * (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z
              * Work.Spaces.mixed (j - b) i f z θ)) ^ 2 := by
        have h0 := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1))
          (f := fun b => (((j.choose b : ℕ)) : ℝ)
            * (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z
              * Work.Spaces.mixed (j - b) i f z θ))
        have hcard : (((Finset.range (j + 1)).card : ℕ) : ℝ) = (j : ℝ) + 1 := by
          rw [Finset.card_range]; push_cast; ring
        simpa only [hcard] using h0
      refine le_trans hcs ?_
      have hterm : ∀ b ∈ Finset.range (j + 1),
          ((((j.choose b : ℕ)) : ℝ)
            * (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z
              * Work.Spaces.mixed (j - b) i f z θ)) ^ 2
          ≤ (4 : ℝ) ^ n * K ^ 2 * (Work.Spaces.mixed (j - b) i f z θ) ^ 2 := by
        intro b hb
        have hbn : b ≤ n :=
          le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)) hjn
        have hZb : |Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z| ≤ K :=
          hKbd b hbn z hz
        have hZb2 : (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z) ^ 2 ≤ K ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hZb 2
        have hcb := choose_sq_le_four_pow n j b hjn
        calc ((((j.choose b : ℕ)) : ℝ)
              * (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z
                * Work.Spaces.mixed (j - b) i f z θ)) ^ 2
            = (((j.choose b : ℕ)) : ℝ) ^ 2
                * (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z) ^ 2
                * (Work.Spaces.mixed (j - b) i f z θ) ^ 2 := by ring
          _ ≤ (4 : ℝ) ^ n * K ^ 2 * (Work.Spaces.mixed (j - b) i f z θ) ^ 2 := by
              apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
              exact mul_le_mul hcb hZb2 (sq_nonneg _) (by positivity)
      have hslot : ∀ b ∈ Finset.range (j + 1),
          (Work.Spaces.mixed (j - b) i f z θ) ^ 2 ≤ mblk n f z θ :=
        fun b hb => mslot_le n f z θ hi1 (by
          have hb' : b ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
          omega)
      have hsum : (∑ b ∈ Finset.range (j + 1), ((((j.choose b : ℕ)) : ℝ)
            * (Work.Spaces.Zop^[b] (fun z : ℝ => z / (1 + z) ^ 2) z
              * Work.Spaces.mixed (j - b) i f z θ)) ^ 2)
          ≤ ∑ _b ∈ Finset.range (j + 1), ((4 : ℝ) ^ n * K ^ 2 * mblk n f z θ) :=
        Finset.sum_le_sum fun b hb => le_trans (hterm b hb)
          (mul_le_mul_of_nonneg_left (hslot b hb) (by positivity))
      refine le_trans (mul_le_mul_of_nonneg_left hsum (by positivity)) ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      have hj1 : (j : ℝ) + 1 ≤ (n : ℝ) + 1 := by
        have := Nat.succ_le_succ hjn
        exact_mod_cast this
      have hA : (0 : ℝ) ≤ (4 : ℝ) ^ n * K ^ 2 * mblk n f z θ :=
        mul_nonneg (by positivity) hMnn
      calc ((j : ℝ) + 1) * (((j : ℝ) + 1) * ((4 : ℝ) ^ n * K ^ 2 * mblk n f z θ))
          = ((j : ℝ) + 1) ^ 2 * ((4 : ℝ) ^ n * K ^ 2 * mblk n f z θ) := by ring
        _ ≤ ((n : ℝ) + 1) ^ 2 * ((4 : ℝ) ^ n * K ^ 2 * mblk n f z θ) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hj1 2) hA
        _ = ((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n * K ^ 2 * mblk n f z θ := by ring
    · rw [if_neg hc]
      positivity
  calc mblk n (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ
      = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          (if 1 ≤ i ∧ i + j ≤ n
            then (Work.Spaces.mixed j i (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ) ^ 2
            else 0) := rfl
    _ ≤ ∑ _i ∈ Finset.range (n + 1), ∑ _j ∈ Finset.range (n + 1),
          (((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n * K ^ 2 * mblk n f z θ) :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hper i hi j hj
    _ = ((n : ℝ) + 1)
          * (((n : ℝ) + 1) * (((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n * K ^ 2 * mblk n f z θ)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ (((n : ℝ) + 1) ^ 4 * (4 : ℝ) ^ n * K ^ 2 + 1) * mblk n f z θ := by
        have hfac : (((n : ℝ) + 1) ^ 4 * (4 : ℝ) ^ n * K ^ 2 + 1) * mblk n f z θ
            - ((n : ℝ) + 1)
              * (((n : ℝ) + 1) * (((n : ℝ) + 1) ^ 2 * (4 : ℝ) ^ n * K ^ 2 * mblk n f z θ))
            = mblk n f z θ := by ring
        linarith [hfac, hMnn]

/-! ## The α-free multiplier estimate for `φ` -/

/-- **Multiplication by `φ(z) = z/(1+z)²` does not increase the `ℋⁿ`-integrand**, with a
constant uniform in `α`.  The two blocks are estimated separately, each with its own weight;
both estimates are `α`-free because the weight `Wt α z θ` is constant in the summation
indices and factors out. -/
private theorem HkIntegrand_phi_mul_le (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), Work.FTS.LocData.SmoothQuad f →
      ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        Work.Spaces.HkIntegrand α n (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ
          ≤ C * Work.Spaces.HkIntegrand α n f z θ := by
  obtain ⟨Kp, _hKppos, hKp⟩ := zblk_zmul_le n
  obtain ⟨Km, _hKmpos, hKm⟩ := mblk_zmul_le n
  refine ⟨max Kp Km + 1, by positivity, ?_⟩
  intro α f hf z hz θ hθ
  have h1 := hKp f hf z hz θ hθ
  have h2 := hKm f hf z hz θ hθ
  rw [HkIntegrand_eq_zblk_add α n (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ,
    HkIntegrand_eq_zblk_add α n f z θ]
  have hZp : 0 ≤ zblk n f z θ := zblk_nonneg n f z θ
  have hMp : 0 ≤ mblk n f z θ := mblk_nonneg n f z θ
  have hW : 0 ≤ (Work.Spaces.Wt α z θ) ^ 2 := sq_nonneg _
  have hKpm : Kp ≤ max Kp Km + 1 := by
    have := le_max_left Kp Km
    linarith
  have hKmm : Km ≤ max Kp Km + 1 := by
    have := le_max_right Kp Km
    linarith
  have hs1 : zblk n (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ
      ≤ (max Kp Km + 1) * zblk n f z θ :=
    le_trans h1 (mul_le_mul_of_nonneg_right hKpm hZp)
  have hs3 : (Work.Spaces.Wt α z θ) ^ 2
        * mblk n (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ
      ≤ (Work.Spaces.Wt α z θ) ^ 2 * (Km * mblk n f z θ) :=
    mul_le_mul_of_nonneg_left h2 hW
  have hs4 : (Work.Spaces.Wt α z θ) ^ 2 * (Km * mblk n f z θ)
      ≤ (max Kp Km + 1) * ((Work.Spaces.Wt α z θ) ^ 2 * mblk n f z θ) := by
    have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKmm hMp) hW
    linarith [h]
  linarith [hs1, hs3, hs4]

/-! ## The pointwise defect estimate, uniform in `α` -/

/-- **The `ℋⁿ`-slot bound for the `D_z`-commutator defect, with a constant independent of
`α`.**  Splitting `Ê₂ f = 2·(φ·f) + 3·(φ·D_θf)` with the subadditivity and homogeneity of
the integrand reduces the claim to the α-free multiplier estimate for `φ`. -/
private theorem E2hat_HkIntegrand_le_uniform_pt (n : ℕ) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), Work.FTS.LocData.SmoothQuad f →
      ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.E2hat f) z θ
          ≤ Cn * (Work.Spaces.HkIntegrand α n f z θ
              + Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ) := by
  obtain ⟨C, hCpos, hC⟩ := HkIntegrand_phi_mul_le n
  refine ⟨18 * C, by positivity, ?_⟩
  intro α f hf z hz θ hθ
  have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hDth : Work.FTS.LocData.SmoothQuad (Work.Spaces.Dth f) := by
    simpa using Work.FTS.LocData.SmoothQuad.DthIter hf 1
  have hphi : Work.FTS.LocData.SmoothQuad (fun z θ : ℝ => z / (1 + z) ^ 2) :=
    Work.FTS.CoercivityFix.E2Bound.smoothQuad_zDiv
  have hA : Work.FTS.LocData.SmoothQuad
      (fun z θ : ℝ => 2 * ((z / (1 + z) ^ 2) * f z θ)) :=
    Work.FTS.LocData.smoothQuad_const_mul 2 (Work.FTS.LocData.smoothQuad_mul hphi hf)
  have hB : Work.FTS.LocData.SmoothQuad
      (fun z θ : ℝ => 3 * ((z / (1 + z) ^ 2) * (Work.Spaces.Dth f) z θ)) :=
    Work.FTS.LocData.smoothQuad_const_mul 3 (Work.FTS.LocData.smoothQuad_mul hphi hDth)
  rw [Work.FTS.CoercivityFix.E2Bound.E2hat_eq_zmul f]
  have h1 := Work.FTS.LocData.HkIntegrand_add_le α n hA hB hzIz hθIθ
  have h1' : Work.Spaces.HkIntegrand α n
        (fun z θ : ℝ => 2 * ((z / (1 + z) ^ 2) * f z θ)
          + 3 * ((z / (1 + z) ^ 2) * (Work.Spaces.Dth f) z θ)) z θ
      ≤ 2 * Work.Spaces.HkIntegrand α n
          (fun z θ : ℝ => 2 * ((z / (1 + z) ^ 2) * f z θ)) z θ
        + 2 * Work.Spaces.HkIntegrand α n
            (fun z θ : ℝ => 3 * ((z / (1 + z) ^ 2) * (Work.Spaces.Dth f) z θ)) z θ := by
    simpa only [Pi.add_apply] using h1
  have h2 := Work.FTS.LocData.HkIntegrand_const_mul α n 2
    (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ
  have h3 := Work.FTS.LocData.HkIntegrand_const_mul α n 3
    (fun z θ : ℝ => (z / (1 + z) ^ 2) * (Work.Spaces.Dth f) z θ) z θ
  have h2' : Work.Spaces.HkIntegrand α n
        (fun z θ : ℝ => 2 * ((z / (1 + z) ^ 2) * f z θ)) z θ
      = 4 * Work.Spaces.HkIntegrand α n
          (fun z θ : ℝ => (z / (1 + z) ^ 2) * f z θ) z θ := by
    rw [h2]; norm_num
  have h3' : Work.Spaces.HkIntegrand α n
        (fun z θ : ℝ => 3 * ((z / (1 + z) ^ 2) * (Work.Spaces.Dth f) z θ)) z θ
      = 9 * Work.Spaces.HkIntegrand α n
          (fun z θ : ℝ => (z / (1 + z) ^ 2) * (Work.Spaces.Dth f) z θ) z θ := by
    rw [h3]; norm_num
  have h4 := hC α f hf z hz θ hθ
  have h5 := hC α (Work.Spaces.Dth f) hDth z hz θ hθ
  have hX : 0 ≤ Work.Spaces.HkIntegrand α n f z θ :=
    Work.Spaces.HkIntegrand_nonneg α n f z θ
  have hY : 0 ≤ Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ :=
    Work.Spaces.HkIntegrand_nonneg α n (Work.Spaces.Dth f) z θ
  have hCX : 0 ≤ C * Work.Spaces.HkIntegrand α n f z θ := mul_nonneg hCpos.le hX
  have hCY : 0 ≤ C * Work.Spaces.HkIntegrand α n (Work.Spaces.Dth f) z θ :=
    mul_nonneg hCpos.le hY
  nlinarith [h1', h2', h3', h4, h5, hX, hY, hCX, hCY]

/-! ## The iterated-integral assembly -/

/-- `Iθ = [0,π/2]` and `(0,π/2)` differ by a null set. -/
private lemma restrict_Iθ_eq_Ioo :
    (volume : Measure ℝ).restrict Work.Spaces.Iθ
      = (volume : Measure ℝ).restrict (Set.Ioo 0 (π / 2)) :=
  (MeasureTheory.restrict_Ioo_eq_restrict_Icc (μ := (volume : Measure ℝ)) (a := 0)
    (b := π / 2)).symm


end Work.FTS.CoercivityFix.Assembly
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Assembly.H1IP_cs_Q =====
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
set_option maxHeartbeats 1000000

/-! ## The triangle inequality for four terms -/

private theorem abs_add_four (a b c d : ℝ) :
    |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 : |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
  have h2 : |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
  have h3 : |a + b| ≤ |a| + |b| := abs_add_le _ _
  linarith

/-! ## The main theorem -/


end Work.FTS.CoercivityFix.Assembly
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Assembly.Lhat_RegQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Assembly

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! # `RegQ` is closed under multiplication by a radial factor with bounded `Zop`-iterates

The interior class `Work.FTS.Nonlin.RegQ α k g = SmoothQuad g ∧ HkMem α k g ∧ BdryTraces α k g`
(`Submission/Work/FTS/Vocab.lean`) is the class in which the whole a-priori chapter is stated.
Multiplication by a function `ψ = ψ(z)` of `z` alone is not a differential operator, but it is
controlled by the two facts proved in `FTS/CoercivityFix/PsiMul/`:

* `HkMem_psi_mul`: `HkMem α k g → HkMem α k (ψ·g)`, via the pointwise multiplier estimate
  `Work.FTS.CoercivityFix.E2Bound.SlotMul.HkIntegrand_zmul_uniform`
  (`HkIntegrand α k (ψ·g) ≤ C·(1+K)²·HkIntegrand α k g` on the open quadrant) and the
  majorant criterion `Work.FTS.LocData.HkMem_of_majorant`;
* `BdryTraces_psi_mul`: `BdryTraces α k g → BdryTraces α k (ψ·g)`, via the Leibniz expansion
  `Work.FTS.CoercivityFix.E2Bound.mixed_zmul` of `D_z^b D_θ^a (ψ·g)` and the squeeze theorem.

Both hypotheses are on the `Zop`-iterates `Zop^[c] ψ = (z ∂_z)^c ψ`, `c ≤ k`, which are required
to be bounded on `(0,∞)` by a common `K`.  Smoothness of `ψ` on `(-1,∞)` gives `SmoothQuad`, and
`SmoothQuad` is closed under multiplication.

For the concrete factor `ψ(z) = 1/(1+z)` used by `Lhat = 𝓛 − Transport = f + D_z f − 2f/(1+z)
− 3 D_θ f/(1+z)`, the bound is `Work.FTS.CoercivityFix.PsiMul.zop_psi_bound` (proved by the
Möbius-chart/polynomial argument of `E2Bound.zop_phi_bound`) and the smoothness is
`Work.FTS.CoercivityFix.PsiMul.contDiffOn_psi`.

Everything rests on `[propext, Classical.choice, Quot.sound]`. -/




/-! ## The target: `Lhat` is a `RegQ`-port -/


end

end Work.FTS.CoercivityFix.Assembly
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Assembly.coer_clause_succ =====
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

open Work.FTS.Nonlin (RegQ)
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false



end Work.FTS.CoercivityFix.Assembly
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1.Estimates =====
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

/-! ## Tools -/

theorem ae_restrict_Iz_pos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
  rw [MeasureTheory.ae_restrict_iff (p := fun z => 0 < z) measurableSet_Ioi,
    MeasureTheory.ae_iff]
  have hset : {z : ℝ | ¬ (z ∈ Work.Spaces.Iz → 0 < z)} = {0} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Work.Spaces.Iz, Set.mem_Ici, not_imp]
    constructor
    · rintro ⟨h1, h2⟩; exact le_antisymm (not_lt.mp h2) h1
    · intro h; rw [h]; exact ⟨le_refl 0, lt_irrefl 0⟩
  rw [hset, Real.volume_singleton]

/-- The `wip` of a difference splits, under the two integrability certificates. -/
theorem wip_sub_left {ρ A B C : Fn}
    (hA : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => A z θ * C z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hB : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => B z θ * C z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Work.Coercivity.wip ρ (fun z θ => A z θ - B z θ) C
      = Work.Coercivity.wip ρ A C - Work.Coercivity.wip ρ B C := by
  have hA' : MeasureTheory.Integrable (fun p : ℝ × ℝ => A p.1 p.2 * C p.1 p.2 * ρ p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [iz_prod_restrict]; exact hA
  have hB' : MeasureTheory.Integrable (fun p : ℝ × ℝ => B p.1 p.2 * C p.1 p.2 * ρ p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [iz_prod_restrict]; exact hB
  have hAB : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (A z θ - B z θ) * C z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    rw [MeasureTheory.IntegrableOn, ← iz_prod_restrict]
    refine (hA'.sub hB').congr (Filter.Eventually.of_forall (fun p => ?_))
    rcases p with ⟨z, θ⟩
    simp only [Pi.sub_apply, Function.uncurry_apply_pair]
    ring
  rw [Work.Coercivity.wip_eq_integral_prod ρ (fun z θ => A z θ - B z θ) C hAB,
    Work.Coercivity.wip_eq_integral_prod ρ A C hA,
    Work.Coercivity.wip_eq_integral_prod ρ B C hB]
  rw [show (∫ p, (A p.1 p.2 - B p.1 p.2) * C p.1 p.2 * ρ p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∫ p, (A p.1 p.2 * C p.1 p.2 * ρ p.1 p.2 - B p.1 p.2 * C p.1 p.2 * ρ p.1 p.2)
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) from
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => by
      rcases p with ⟨z, θ⟩; ring))]
  rw [MeasureTheory.integral_sub hA' hB']


/-- The `γ`-weight is at least `1` on the open angular interval. -/
theorem one_le_sig_gam (α : ℝ) (hα : 0 < α) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    1 ≤ sig (Work.Spaces.gam α) θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hgam : 0 < Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have h := Real.rpow_le_rpow_of_exponent_ge hs hs1 (show -(Work.Spaces.gam α) ≤ -(0 : ℝ) by
    linarith)
  rw [sig]
  simpa using h

/-- `EDthW u ≤ En (gam α) (D_θ u)`. -/
theorem EDthW_le_En_gam (α : ℝ) (hα : 0 < α) (u : Fn)
    (h1 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.Dth u z θ) ^ 2 * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (h2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.Dth u z θ) ^ 2 * Work.Spaces.w z ^ 2
        * sig (Work.Spaces.gam α) θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Work.Coercivity.EDthW u ≤ En (Work.Spaces.gam α) (Work.Spaces.Dth u) := by
  have h1' : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.Dth u p.1 p.2 * Work.Spaces.Dth u p.1 p.2
        * Work.Spaces.w p.1 ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [iz_prod_restrict]
    refine (h1.const_mul 1).congr (Filter.Eventually.of_forall (fun p => ?_))
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, one_mul]
    ring
  have h2' : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.Dth u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2
        * sig (Work.Spaces.gam α) p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [iz_prod_restrict]; exact h2
  have e1 : Work.Coercivity.EDthW u = ∫ p : ℝ × ℝ,
      Work.Spaces.Dth u p.1 p.2 * Work.Spaces.Dth u p.1 p.2 * Work.Spaces.w p.1 ^ 2
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (MeasureTheory.integral_prod (fun p : ℝ × ℝ =>
      Work.Spaces.Dth u p.1 p.2 * Work.Spaces.Dth u p.1 p.2 * Work.Spaces.w p.1 ^ 2) h1').symm
  have e2 : En (Work.Spaces.gam α) (Work.Spaces.Dth u) = ∫ p : ℝ × ℝ,
      Work.Spaces.Dth u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2 * sig (Work.Spaces.gam α) p.2
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (MeasureTheory.integral_prod (fun p : ℝ × ℝ =>
      Work.Spaces.Dth u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2 * sig (Work.Spaces.gam α) p.2)
      h2').symm
  rw [e1, e2]
  refine MeasureTheory.integral_mono_ae h1' h2' ?_
  filter_upwards [ae_prod_snd_mem measurableSet_Ioo ae_restrict_Iθ_mem_Ioo] with p hp
  have hgnn : (0:ℝ) ≤ sig (Work.Spaces.gam α) p.2 :=
    Real.rpow_nonneg (sin_nonneg_of_mem_Iθ ⟨le_of_lt hp.1, le_of_lt hp.2⟩) _
  calc Work.Spaces.Dth u p.1 p.2 * Work.Spaces.Dth u p.1 p.2 * Work.Spaces.w p.1 ^ 2
      = Work.Spaces.Dth u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2 := by ring
    _ ≤ Work.Spaces.Dth u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2 * sig (Work.Spaces.gam α) p.2 :=
        le_mul_of_one_le_right (mul_nonneg (sq_nonneg _) (sq_nonneg _))
          (one_le_sig_gam α hα hp)


/-! ## The angular boundary limits

`BdryTraces` gives the one-sided angular limits of `sin(2θ)^{1-γ}·(D_z^bD_θ^a f)²`; the
`η`-exponent version follows from `sin(2θ)^{1-η} = sin(2θ)^{γ-η}·sin(2θ)^{1-γ}` and
`sin(2θ)^{γ-η} → 0`. -/

theorem tendsto_sin_rpow_gam_sub_eta_right (α : ℝ) (hα : 0 < α) :
    Filter.Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - Work.Spaces.eta))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
  Work.FTS.H2.tendsto_sin_rpow_zero_right _
    (by linarith [Work.Spaces.eta_lt_one, (by rw [Work.Spaces.gam]; linarith :
      (1 : ℝ) < Work.Spaces.gam α)])

theorem tendsto_sin_rpow_gam_sub_eta_left (α : ℝ) (hα : 0 < α) :
    Filter.Tendsto (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - Work.Spaces.eta))
      (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0) :=
  Work.FTS.H2.tendsto_sin_rpow_zero_left _
    (by linarith [Work.Spaces.eta_lt_one, (by rw [Work.Spaces.gam]; linarith :
      (1 : ℝ) < Work.Spaces.gam α)])

/-- The `η`-exponent angular limits follow from the `γ`-exponent ones. -/
theorem hvan_eta_of_gam (α : ℝ) (hα : 0 < α) {a b : ℕ} {f : Fn}
    (hγ : ∀ z, 0 < z → Filter.Tendsto
      (fun θ => (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed b a f z θ) ^ 2) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hγ2 : ∀ z, 0 < z → Filter.Tendsto
      (fun θ => (Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed b a f z θ) ^ 2) (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0)) :
    (∀ z, 0 < z → Filter.Tendsto
        (fun θ => (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta)
          * (Work.Spaces.mixed b a f z θ) ^ 2) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
      ∧ ∀ z, 0 < z → Filter.Tendsto
        (fun θ => (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta)
          * (Work.Spaces.mixed b a f z θ) ^ 2) (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0) := by
  have hgη : Work.Spaces.gam α - Work.Spaces.eta = 1 - Work.Spaces.eta - (1 - Work.Spaces.gam α) := by
    ring
  constructor
  · intro z hz
    have hprod := (tendsto_sin_rpow_gam_sub_eta_right α hα).mul (hγ z hz)
    have hprod0 : Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - Work.Spaces.eta)
        * ((Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a f z θ) ^ 2)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      simpa using hprod
    refine hprod0.congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds (by positivity : (0:ℝ) < π / 2))]
      with θ hθ hθπ
    have hθ0 : (0 : ℝ) < θ := hθ
    have hθπ' : θ < π / 2 := hθπ
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hexp : Work.Spaces.gam α - Work.Spaces.eta + (1 - Work.Spaces.gam α)
        = 1 - Work.Spaces.eta := by ring
    rw [← mul_assoc, ← Real.rpow_add hs, hexp]
  · intro z hz
    have hprod := (tendsto_sin_rpow_gam_sub_eta_left α hα).mul (hγ2 z hz)
    have hprod0 : Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - Work.Spaces.eta)
        * ((Real.sin (2 * θ)) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a f z θ) ^ 2)) (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0) := by
      simpa using hprod
    refine hprod0.congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Ioi_mem_nhds (by positivity : (0:ℝ) < π / 2))] with θ hθ hθ0
    have hθπ' : θ < π / 2 := hθ
    have hθ0' : (0 : ℝ) < θ := hθ0
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hexp : Work.Spaces.gam α - Work.Spaces.eta + (1 - Work.Spaces.gam α)
        = 1 - Work.Spaces.eta := by ring
    rw [← mul_assoc, ← Real.rpow_add hs, hexp]

/-! ## The weighted energies as product-measure integrals -/

theorem En_eq_prod {β : ℝ} {u : Fn}
    (h : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * Work.Spaces.w z ^ 2 * sig β θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    En β u = ∫ p : ℝ × ℝ, u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2 * sig β p.2
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  rw [En]
  refine (MeasureTheory.integral_prod
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (fun p : ℝ × ℝ => u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2 * sig β p.2) ?_).symm
  rw [iz_prod_restrict]; exact h

theorem EnOne_eq_prod {u : Fn}
    (h : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    EnOne u = ∫ p : ℝ × ℝ, u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  rw [EnOne]
  refine (MeasureTheory.integral_prod
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (fun p : ℝ × ℝ => u p.1 p.2 ^ 2 * Work.Spaces.w p.1 ^ 2) ?_).symm
  rw [iz_prod_restrict]; exact h

theorem EDthW_eq_prod {u : Fn}
    (h : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth u z θ * Work.Spaces.Dth u z θ
        * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Work.Coercivity.EDthW u = ∫ p : ℝ × ℝ,
      Work.Spaces.Dth u p.1 p.2 * Work.Spaces.Dth u p.1 p.2 * Work.Spaces.w p.1 ^ 2
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  rw [Work.Coercivity.EDthW, Work.Coercivity.wip]
  refine (MeasureTheory.integral_prod
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (fun p : ℝ × ℝ => Work.Spaces.Dth u p.1 p.2 * Work.Spaces.Dth u p.1 p.2
      * Work.Spaces.w p.1 ^ 2) ?_).symm
  rw [iz_prod_restrict]; exact h

/-! ## Shape conversions for the `wip`-form integrands -/

theorem to_h1 {β : ℝ} {u : Fn}
    (h : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * Rho β z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * Work.Spaces.w z ^ 2 * sig β θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  refine h.congr (MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Ici.prod measurableSet_Icc) (fun p hpp => ?_))
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair, Rho, sig]
  ring

theorem to_h2 {β : ℝ} {u : Fn}
    (h : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.L u z θ * u z θ * Rho β z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.L u z θ * u z θ
        * Work.Spaces.w z ^ 2 * sig β θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  refine h.congr (MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Ici.prod measurableSet_Icc) (fun p hpp => ?_))
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair, Rho, sig]
  ring

theorem to_tr_hint {β : ℝ} {u : Fn}
    (h : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth u z θ * u z θ * Rho β z θ / (1 + z)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-β) * Work.Spaces.Dth u z θ * u z θ
        / (1 + z))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  refine h.congr (MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Ici.prod measurableSet_Icc) (fun p hpp => ?_))
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair, Rho, sig]
  ring

theorem to_tr_hint2 {β : ℝ} {u : Fn}
    (h : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * Rho β z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-β) * (u z θ) ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  refine h.congr (MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Ici.prod measurableSet_Icc) (fun p hpp => ?_))
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair, Rho, sig]
  ring

/-! ## The four estimates -/



/-! ## Toolbox for the two remaining estimates

The two estimates `est_A` and `est_C` rest on two more scalar inequalities:

* `est_C` needs the transport pairing in the *plain* radial weight to be dominated by
  `(3/8)E_1(u) + 6·|D_θu·w|²`, which is the pointwise Young inequality
  `3ab/(1+z) ≤ 6a² + (3/8)b²` integrated;
* `est_A` needs the `D_z`-commutator defect `Ê₂f` to be dominated by
  `|f|²_{η} + 4|D_θf|²_{γ} + (1/8)|D_zf|²_{η}`, which is the pointwise bound
  `|Ê₂u| ≤ (2|u| + 3|D_θu|)/4` combined with two more Young inequalities.
-/

/-- `IntegrableOn` transports across a pointwise identification of the integrands. -/
theorem integrableOn_congr_fun_Q {A B : Fn}
    (h : MeasureTheory.IntegrableOn (Function.uncurry A) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (heq : ∀ z θ, A z θ = B z θ) :
    MeasureTheory.IntegrableOn (Function.uncurry B) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  refine h.congr (MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Ici.prod measurableSet_Icc) (fun p _ => ?_))
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair]
  exact heq z θ

/-- The weighted energy `En` with the integrand in the `Rho`-form. -/
theorem En_eq_prod_Rho {β : ℝ} {u : Fn}
    (h : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => u z θ ^ 2 * Rho β z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    En β u = ∫ p : ℝ × ℝ, u p.1 p.2 ^ 2 * Rho β p.1 p.2
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  rw [En_eq_prod (to_h1 h)]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => by
    rcases p with ⟨z, θ⟩
    simp only [Rho]
    ring))

/-! ### The two Young inequalities

`(1/2)|a||b| ≤ a² + b²/16` and `(3/4)|a||b| ≤ 3a² + (3/64)b²`, both with the sharp
discriminant-zero constants. -/

theorem amgm_half_abs (a b : ℝ) : (1 / 2) * |a| * |b| ≤ a ^ 2 + (1 / 16) * b ^ 2 := by
  have h : (0 : ℝ) ≤ (|a| - |b| / 4) ^ 2 := sq_nonneg _
  have e : (|a| - |b| / 4) ^ 2 = a ^ 2 - |a| * |b| / 2 + b ^ 2 / 16 := by
    rw [sub_sq, sq_abs, div_pow, sq_abs]
    ring
  rw [e] at h
  nlinarith [h]

theorem amgm_three_quarter_abs (a b : ℝ) :
    (3 / 4) * |a| * |b| ≤ 3 * a ^ 2 + (3 / 64) * b ^ 2 := by
  have h : (0 : ℝ) ≤ (|a| - |b| / 8) ^ 2 := sq_nonneg _
  have e : (|a| - |b| / 8) ^ 2 = a ^ 2 - |a| * |b| / 4 + b ^ 2 / 64 := by
    rw [sub_sq, sq_abs, div_pow, sq_abs]
    ring
  rw [e] at h
  nlinarith [h]

/-- Young for the transport term: `3ab/(1+z) ≤ 6a² + (3/8)b²` for `z ≥ 0`. -/
theorem transport_young (a b : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    3 * a / (1 + z) * b ≤ 6 * a ^ 2 + (3 / 8) * b ^ 2 := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  rcases le_total 0 (a * b) with hab | hab
  · have h1 : 3 * a / (1 + z) * b ≤ 3 * (a * b) := by
      rw [show 3 * a / (1 + z) * b = 3 * (a * b) / (1 + z) by ring]
      rw [div_le_iff₀ hz1]
      nlinarith
    have h2 : 3 * (a * b) ≤ 6 * a ^ 2 + (3 / 8) * b ^ 2 := by
      nlinarith [sq_nonneg (4 * a - b)]
    linarith
  · have h1 : 3 * a / (1 + z) * b ≤ 0 := by
      rw [show 3 * a / (1 + z) * b = 3 * (a * b) / (1 + z) by ring]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hz1)
    have h2 : (0 : ℝ) ≤ 6 * a ^ 2 + (3 / 8) * b ^ 2 := by positivity
    linarith

/-- The pointwise transport estimate with the plain radial weight. -/
theorem transport_pt_w2 {u : Fn} {z θ : ℝ} (hz : 0 ≤ z) :
    Work.Coercivity.Transport u z θ * u z θ * Work.Spaces.w z ^ 2
      ≤ 6 * ((Work.Spaces.Dth u z θ) ^ 2 * Work.Spaces.w z ^ 2)
        + (3 / 8) * ((u z θ) ^ 2 * Work.Spaces.w z ^ 2) := by
  have h2 := mul_le_mul_of_nonneg_right
    (transport_young (Work.Spaces.Dth u z θ) (u z θ) hz) (sq_nonneg (Work.Spaces.w z))
  simp only [Work.Coercivity.Transport]
  nlinarith [h2]

/-- The transport pairing in the plain radial weight. -/
theorem transport_w2_bound {u : Fn}
    (hT : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.Transport u z θ * u z θ * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hD : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Spaces.Dth u z θ * Work.Spaces.Dth u z θ * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hU : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (u z θ) ^ 2 * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) (Work.Coercivity.Transport u) u
      ≤ (3 / 8) * EnOne u + 6 * Work.Coercivity.EDthW u := by
  have hpr : (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      = (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := iz_prod_restrict
  have hT' : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.Coercivity.Transport u p.1 p.2 * u p.1 p.2 * Work.Spaces.w p.1 ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [hpr]; exact hT
  have hD' : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.Spaces.Dth u p.1 p.2 * Work.Spaces.Dth u p.1 p.2 * Work.Spaces.w p.1 ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [hpr]; exact hD
  have hU' : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (u p.1 p.2) ^ 2 * Work.Spaces.w p.1 ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [hpr]; exact hU
  have hA : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      6 * ((Work.Spaces.Dth u p.1 p.2) ^ 2 * Work.Spaces.w p.1 ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (hD'.const_mul 6).congr (Filter.Eventually.of_forall (fun p => by
      rcases p with ⟨z, θ⟩; ring))
  have hB : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (3 / 8) * ((u p.1 p.2) ^ 2 * Work.Spaces.w p.1 ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (hU'.const_mul (3 / 8)).congr (Filter.Eventually.of_forall (fun p => by
      rcases p with ⟨z, θ⟩; ring))
  have hS : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      6 * ((Work.Spaces.Dth u p.1 p.2) ^ 2 * Work.Spaces.w p.1 ^ 2)
        + (3 / 8) * ((u p.1 p.2) ^ 2 * Work.Spaces.w p.1 ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := hA.add hB
  have hpoint : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      Work.Coercivity.Transport u p.1 p.2 * u p.1 p.2 * Work.Spaces.w p.1 ^ 2
        ≤ 6 * ((Work.Spaces.Dth u p.1 p.2) ^ 2 * Work.Spaces.w p.1 ^ 2)
          + (3 / 8) * ((u p.1 p.2) ^ 2 * Work.Spaces.w p.1 ^ 2) := by
    filter_upwards [ae_prod_fst_mem (s := Set.Ici (0 : ℝ)) measurableSet_Ici
      (MeasureTheory.ae_restrict_mem measurableSet_Ici)] with p hp
    rcases p with ⟨z, θ⟩
    simp only [Set.mem_Ici] at hp
    exact transport_pt_w2 hp
  calc Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
        (Work.Coercivity.Transport u) u
      = ∫ p : ℝ × ℝ, Work.Coercivity.Transport u p.1 p.2 * u p.1 p.2
          * Work.Spaces.w p.1 ^ 2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
        Work.Coercivity.wip_eq_integral_prod (fun z _ => Work.Spaces.w z ^ 2)
          (Work.Coercivity.Transport u) u hT
    _ ≤ ∫ p : ℝ × ℝ, (6 * ((Work.Spaces.Dth u p.1 p.2) ^ 2 * Work.Spaces.w p.1 ^ 2)
          + (3 / 8) * ((u p.1 p.2) ^ 2 * Work.Spaces.w p.1 ^ 2))
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
        MeasureTheory.integral_mono_ae hT' hS hpoint
    _ = 6 * (∫ p : ℝ × ℝ, Work.Spaces.Dth u p.1 p.2 * Work.Spaces.Dth u p.1 p.2
            * Work.Spaces.w p.1 ^ 2
            ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
        + (3 / 8) * (∫ p : ℝ × ℝ, (u p.1 p.2) ^ 2 * Work.Spaces.w p.1 ^ 2
            ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
        have e1 : (∫ p : ℝ × ℝ,
              (Work.Spaces.Dth u p.1 p.2) ^ 2 * Work.Spaces.w p.1 ^ 2
              ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
                (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
            = ∫ p : ℝ × ℝ, Work.Spaces.Dth u p.1 p.2 * Work.Spaces.Dth u p.1 p.2
                * Work.Spaces.w p.1 ^ 2
                ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
                  (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => by
            rcases p with ⟨z, θ⟩; ring))
        rw [MeasureTheory.integral_add
            (f := fun p : ℝ × ℝ => 6 * ((Work.Spaces.Dth u p.1 p.2) ^ 2
              * Work.Spaces.w p.1 ^ 2))
            (g := fun p : ℝ × ℝ => (3 / 8) * ((u p.1 p.2) ^ 2 * Work.Spaces.w p.1 ^ 2))
            hA hB,
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, e1]
    _ = (3 / 8) * EnOne u + 6 * Work.Coercivity.EDthW u := by
        rw [EDthW_eq_prod hD, EnOne_eq_prod hU]
        ring

/-- **The `ê₂`-pairing defect bound.** -/
theorem E2hat_pt {α : ℝ} (u g : Fn) (hα : 0 < α) {z θ : ℝ} (hz : 0 ≤ z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    -(u z θ ^ 2 * Rho Work.Spaces.eta z θ
        + 4 * ((Work.Spaces.Dth u z θ) ^ 2 * Rho (Work.Spaces.gam α) z θ)
        + (7 / 64) * (g z θ ^ 2 * Rho Work.Spaces.eta z θ))
      ≤ Work.FTS.CoercivityFix.E2hat u z θ * g z θ * Rho Work.Spaces.eta z θ := by
  have habs : |Work.FTS.CoercivityFix.E2hat u z θ|
      ≤ (2 * |u z θ| + 3 * |Work.Spaces.Dth u z θ|) / 4 :=
    Work.FTS.CoercivityFix.E2hat_abs_le u (z := z) (θ := θ) hz
  have hρ : 0 ≤ Rho Work.Spaces.eta z θ := Rho_nonneg _ _ _ hθ
  have hρ' : Rho Work.Spaces.eta z θ ≤ Rho (Work.Spaces.gam α) z θ :=
    Rho_eta_le_Rho_gam α hα z θ hθ
  have hA := amgm_half_abs (u z θ) (g z θ)
  have hB := amgm_three_quarter_abs (Work.Spaces.Dth u z θ) (g z θ)
  have h3ρ : (3 : ℝ) * Rho Work.Spaces.eta z θ ≤ 4 * Rho (Work.Spaces.gam α) z θ := by
    nlinarith [hρ, hρ']
  have hAρ := mul_le_mul_of_nonneg_right hA hρ
  have hBρ := mul_le_mul_of_nonneg_right hB hρ
  have h3B := mul_le_mul_of_nonneg_left h3ρ (sq_nonneg (Work.Spaces.Dth u z θ))
  have h1 : |Work.FTS.CoercivityFix.E2hat u z θ| * |g z θ| * Rho Work.Spaces.eta z θ
      ≤ ((1 / 2) * |u z θ| + (3 / 4) * |Work.Spaces.Dth u z θ|) * |g z θ|
        * Rho Work.Spaces.eta z θ := by
    have h := mul_le_mul_of_nonneg_right habs (abs_nonneg (g z θ))
    have h2 := mul_le_mul_of_nonneg_right h hρ
    linarith [h2]
  have h2 : ((1 / 2) * |u z θ| + (3 / 4) * |Work.Spaces.Dth u z θ|) * |g z θ|
        * Rho Work.Spaces.eta z θ
      ≤ u z θ ^ 2 * Rho Work.Spaces.eta z θ
        + 4 * ((Work.Spaces.Dth u z θ) ^ 2 * Rho (Work.Spaces.gam α) z θ)
        + (7 / 64) * (g z θ ^ 2 * Rho Work.Spaces.eta z θ) := by
    nlinarith [hAρ, hBρ, h3B]
  have h3 : -|Work.FTS.CoercivityFix.E2hat u z θ * g z θ * Rho Work.Spaces.eta z θ|
      ≤ Work.FTS.CoercivityFix.E2hat u z θ * g z θ * Rho Work.Spaces.eta z θ :=
    neg_abs_le _
  have h4 : |Work.FTS.CoercivityFix.E2hat u z θ * g z θ * Rho Work.Spaces.eta z θ|
      = |Work.FTS.CoercivityFix.E2hat u z θ| * |g z θ| * Rho Work.Spaces.eta z θ := by
    rw [abs_mul, abs_mul, abs_of_nonneg hρ]
  linarith [h1, h2, h3, h4]

/-- **The `ê₂`-pairing defect is bounded below.** -/
theorem E2hat_wip_lower (α : ℝ) (hα : 0 < α) {u g : Fn}
    (hE : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.FTS.CoercivityFix.E2hat u z θ * g z θ * Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hU : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (u z θ) ^ 2 * Rho Work.Spaces.eta z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hDγ : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Spaces.Dth u z θ) ^ 2 * Rho (Work.Spaces.gam α) z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hG : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (g z θ) ^ 2 * Rho Work.Spaces.eta z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    -(En Work.Spaces.eta u + 4 * En (Work.Spaces.gam α) (Work.Spaces.Dth u)
        + (1 / 8) * En Work.Spaces.eta g)
      ≤ Work.Coercivity.wip (Rho Work.Spaces.eta) (Work.FTS.CoercivityFix.E2hat u) g := by
  have hpr : (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      = (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := iz_prod_restrict
  have hE' : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.FTS.CoercivityFix.E2hat u p.1 p.2 * g p.1 p.2 * Rho Work.Spaces.eta p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [hpr]; exact hE
  have hU' : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (u p.1 p.2) ^ 2 * Rho Work.Spaces.eta p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [hpr]; exact hU
  have hDγ' : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.Dth u p.1 p.2) ^ 2 * Rho (Work.Spaces.gam α) p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [hpr]; exact hDγ
  have hG' : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (g p.1 p.2) ^ 2 * Rho Work.Spaces.eta p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [hpr]; exact hG
  have hF : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      u p.1 p.2 ^ 2 * Rho Work.Spaces.eta p.1 p.2
        + 4 * ((Work.Spaces.Dth u p.1 p.2) ^ 2 * Rho (Work.Spaces.gam α) p.1 p.2)
        + (7 / 64) * (g p.1 p.2 ^ 2 * Rho Work.Spaces.eta p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (hU'.add (hDγ'.const_mul 4)).add (hG'.const_mul (7 / 64))
  have hpoint : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      -(u p.1 p.2 ^ 2 * Rho Work.Spaces.eta p.1 p.2
        + 4 * ((Work.Spaces.Dth u p.1 p.2) ^ 2 * Rho (Work.Spaces.gam α) p.1 p.2)
        + (7 / 64) * (g p.1 p.2 ^ 2 * Rho Work.Spaces.eta p.1 p.2))
        ≤ Work.FTS.CoercivityFix.E2hat u p.1 p.2 * g p.1 p.2 * Rho Work.Spaces.eta p.1 p.2 := by
    filter_upwards [ae_prod_fst_mem (s := Set.Ici (0 : ℝ)) measurableSet_Ici
      (MeasureTheory.ae_restrict_mem measurableSet_Ici),
      ae_prod_snd_mem measurableSet_Icc (MeasureTheory.ae_restrict_mem measurableSet_Icc)]
      with p hz hθ
    rcases p with ⟨z, θ⟩
    simp only [Set.mem_Ici] at hz
    exact E2hat_pt u g hα hz hθ
  have hFval : (∫ p : ℝ × ℝ, (u p.1 p.2 ^ 2 * Rho Work.Spaces.eta p.1 p.2
        + 4 * ((Work.Spaces.Dth u p.1 p.2) ^ 2 * Rho (Work.Spaces.gam α) p.1 p.2)
        + (7 / 64) * (g p.1 p.2 ^ 2 * Rho Work.Spaces.eta p.1 p.2))
      ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = En Work.Spaces.eta u + 4 * En (Work.Spaces.gam α) (Work.Spaces.Dth u)
        + (7 / 64) * En Work.Spaces.eta g := by
    have eF1 : (∫ p : ℝ × ℝ, u p.1 p.2 ^ 2 * Rho Work.Spaces.eta p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))) = En Work.Spaces.eta u :=
      (En_eq_prod_Rho hU).symm
    have eF2 : (∫ p : ℝ × ℝ, (Work.Spaces.Dth u p.1 p.2) ^ 2
          * Rho (Work.Spaces.gam α) p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
        = En (Work.Spaces.gam α) (Work.Spaces.Dth u) :=
      (En_eq_prod_Rho hDγ).symm
    have eF3 : (∫ p : ℝ × ℝ, g p.1 p.2 ^ 2 * Rho Work.Spaces.eta p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))) = En Work.Spaces.eta g :=
      (En_eq_prod_Rho hG).symm
    rw [MeasureTheory.integral_add
          (f := fun p : ℝ × ℝ => u p.1 p.2 ^ 2 * Rho Work.Spaces.eta p.1 p.2
            + 4 * ((Work.Spaces.Dth u p.1 p.2) ^ 2 * Rho (Work.Spaces.gam α) p.1 p.2))
          (g := fun p : ℝ × ℝ => (7 / 64) * (g p.1 p.2 ^ 2 * Rho Work.Spaces.eta p.1 p.2))
          (hU'.add (hDγ'.const_mul 4)) (hG'.const_mul (7 / 64)),
        MeasureTheory.integral_add
          (f := fun p : ℝ × ℝ => u p.1 p.2 ^ 2 * Rho Work.Spaces.eta p.1 p.2)
          (g := fun p : ℝ × ℝ => 4 * ((Work.Spaces.Dth u p.1 p.2) ^ 2
            * Rho (Work.Spaces.gam α) p.1 p.2))
          hU' (hDγ'.const_mul 4),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        eF1, eF2, eF3]
  have hmain : -(En Work.Spaces.eta u + 4 * En (Work.Spaces.gam α) (Work.Spaces.Dth u)
        + (7 / 64) * En Work.Spaces.eta g)
      ≤ Work.Coercivity.wip (Rho Work.Spaces.eta) (Work.FTS.CoercivityFix.E2hat u) g := by
    rw [Work.Coercivity.wip_eq_integral_prod (Rho Work.Spaces.eta)
      (Work.FTS.CoercivityFix.E2hat u) g hE]
    rw [← hFval]
    rw [← MeasureTheory.integral_neg]
    exact MeasureTheory.integral_mono_ae hF.neg hE' hpoint
  have h7 : (7 / 64) * En Work.Spaces.eta g ≤ (1 / 8) * En Work.Spaces.eta g := by
    have hg := En_nonneg Work.Spaces.eta g
    linarith
  linarith [hmain, h7]

/-! ## The two remaining estimates -/



end Work.FTS.CoercivityFix.Coer1
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1SO.IP2O_of =====
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
set_option maxHeartbeats 1600000

/-! ## Continuity of the weighted blocks on the open quadrant -/

/-- `SmoothOpen` gives `C²` at every point of the open quadrant. -/
theorem contDiffAt_two_O {f : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContDiffAt ℝ 2 (Function.uncurry f) (z, θ) :=
  (hs.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
    (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩))

/-- The full angular weight `Wt α = w·sin(2θ)^{-γ/2}` is continuous on the open quadrant. -/
theorem continuousOn_Wt_O (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.EllipticEst.Q0 := by
    have hfun2 : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
    rw [hfun2]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    exact pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  refine hw.mul ?_
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, h0, h1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))

/-- The square of a weighted `D_z`-summand is continuous on the open quadrant. -/
theorem continuousOn_block_z_O {f : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f) (i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.DzIter i f p.1 p.2
        * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.FTS.EllipticEst.Q0 :=
  (((hs.DzIter i).continuousOn).mul Work.FTS.EllipticEst.continuousOn_wdivsin_Q0).pow 2

/-- The square of a weighted mixed summand is continuous on the open quadrant. -/
theorem continuousOn_block_m_O {f : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f) (α : ℝ)
    (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      Work.FTS.EllipticEst.Q0 :=
  (((hs.mixed j i).continuousOn.mul (continuousOn_Wt_O α))).pow 2

/-! ## The weighted squares -/

/-- The squared `D_z`-blocks with the `η`-weight. -/
theorem sq_DzEta_O (α : ℝ) {f : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f)
    (hm : Work.Spaces.HkMem α 2 f) (i : ℕ) (hi : i ≤ 2) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ =>
        (Work.Spaces.DzIter i f z θ) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have h := Work.FTS.CoercivityFix.Coer1.joint_of_le_HkIntegrand α 2 hm
    (continuousOn_block_z_O hs i)
    (fun z _ θ _ => Work.Spaces.sq_le_HkIntegrand_z α 2 f z θ i hi)
  refine h.congr (MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => ?_))
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair] at hp ⊢
  rw [mul_pow, Work.FTS.CoercivityFix.Coer1.sig_div_sq_Iθ Work.Spaces.eta
    (by rw [Work.Spaces.eta]; norm_num) z θ hp.2]
  rfl

/-- The squared mixed blocks with the `γ`-weight. -/
theorem sq_MixedGam_O (α : ℝ) (hα : 0 < α) {f : Fn}
    (hs : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 2 f)
    (i j : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 2) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.mixed j i f z θ) ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have h := Work.FTS.CoercivityFix.Coer1.joint_of_le_HkIntegrand α 2 hm
    (continuousOn_block_m_O hs α j i)
    (fun z _ θ _ => Work.Spaces.sq_le_HkIntegrand_mixed α 2 f z θ i j hi hij)
  refine h.congr (MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => ?_))
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair] at hp ⊢
  rw [mul_pow, Work.FTS.CoercivityFix.Coer1.Wt_sq_self_Iθ α z θ hα hp.2]
  rfl

/-- The squared `D_z`-blocks with the plain radial weight. -/
theorem sq_DzOne_O (α : ℝ) {f : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f)
    (hm : Work.Spaces.HkMem α 2 f) (i : ℕ) (hi : i ≤ 2) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.DzIter i f z θ) ^ 2 * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have h := sq_DzEta_O α hs hm i hi
  refine Work.FTS.CoercivityFix.Coer1.integrableOn_of_le_Q
    ((hs.DzIter i).continuousOn.pow 2 |>.mul Work.FTS.CoercivityFix.Coer1.continuousOn_w2)
    h ?_
  refine (Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem measurableSet_Ioo
    Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo).mono (fun p hp => ?_)
  rcases p with ⟨z, θ⟩
  rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left (Work.FTS.CoercivityFix.Coer1.w2_le_Rho_eta z θ hp)
    (sq_nonneg (Work.Spaces.DzIter i f z θ))

/-- The squared mixed blocks with the plain radial weight. -/
theorem sq_MixedOne_O (α : ℝ) (hα : 0 < α) {f : Fn}
    (hs : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 2 f)
    (i j : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 2) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.mixed j i f z θ) ^ 2 * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have h := sq_MixedGam_O α hα hs hm i j hi hij
  refine Work.FTS.CoercivityFix.Coer1.integrableOn_of_le_Q
    ((hs.mixed j i).continuousOn.pow 2 |>.mul Work.FTS.CoercivityFix.Coer1.continuousOn_w2)
    h ?_
  refine (Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem measurableSet_Ioo
    Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo).mono (fun p hp => ?_)
  rcases p with ⟨z, θ⟩
  rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left
    (Work.FTS.CoercivityFix.Coer1.w2_le_Rho_gam α hα z θ hp)
    (sq_nonneg (Work.Spaces.mixed j i f z θ))

/-! ## The `𝓛`-pairings -/

/-- The `𝓛`-pairing `𝓛u·u·ρ` is integrable as soon as `u²ρ` and `(D_zu)²ρ` are.  The open-class
version of `Work.FTS.CoercivityFix.Coer1.intL_of`. -/
theorem intL_of_O {u : Fn} {ρ : Fn} (hu : Work.FTS.EllipticEst.SmoothOpen u)
    (hρc : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) Work.FTS.EllipticEst.Q0)
    (hρnn : ∀ z θ, θ ∈ Work.Spaces.Iθ → 0 ≤ ρ z θ)
    (hsq : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => u z θ ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hdz : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.Dz u z θ) ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.L u z θ * u z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have hcross : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dz u z θ * u z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_mul_of_sq_Q
      (((hu.mixed 1 0).continuousOn.mul hu.continuousOn).mul hρc) hρnn hdz hsq
  have h1 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      u z θ ^ 2 * ρ z θ + Work.Spaces.Dz u z θ * u z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_add_Q hsq hcross
  have h3 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (u z θ ^ 2 * ρ z θ) / (1 + z))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_div_one_add_Q hsq
  have h4 := h3.const_mul (-2)
  have h5 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (u z θ ^ 2 * ρ z θ + Work.Spaces.Dz u z θ * u z θ * ρ z θ)
        + (-2) * ((u z θ ^ 2 * ρ z θ) / (1 + z)))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_add_Q h1 h4
  refine h5.congr (MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => ?_))
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair, Work.Coercivity.L]
  ring

/-! ## The a.e. commutation of `D_z` and `D_θ` -/

/-- `D_z` and `D_θ` commute a.e. on the quadrant, for `SmoothOpen f` (Clairaut at every interior
point). -/
theorem ae_DzDth_comm_O {f : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.Dz (Work.Spaces.Dth f) z θ = Work.Spaces.Dth (Work.Spaces.Dz f) z θ := by
  have hzpos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
    rw [Work.FTS.CoercivityFix.Coer1.iz_ae_restrict]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioi
  filter_upwards [hzpos] with z hz
  filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo] with θ hθ
  exact Work.Spaces.Dz_Dth_comm (contDiffAt_two_O hs hz hθ)

/-! ## The bundle -/

theorem IP2O_of (α : ℝ) (hα : 0 < α) {f : Work.FTS.Galerkin.Fn}
    (hs : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 2 f) :
    Work.FTS.CoercivityFix.Coer1SO.IP2O α f := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `sqDzEta_one`
    exact sq_DzEta_O α hs hm 1 (by norm_num)
  · -- `sqDzEta_zero`
    exact sq_DzEta_O α hs hm 0 (by norm_num)
  · -- `sqDzOne_zero`
    exact sq_DzOne_O α hs hm 0 (by norm_num)
  · -- `sqDzOne_one`
    exact sq_DzOne_O α hs hm 1 (by norm_num)
  · -- `sqDthOne`
    exact sq_MixedOne_O α hα hs hm 1 0 (by norm_num) (by norm_num)
  · -- `sqDthGam`
    exact sq_MixedGam_O α hα hs hm 1 0 (by norm_num) (by norm_num)
  · -- `intL_f_eta`
    exact intL_of_O hs (Work.FTS.CoercivityFix.Coer1.continuousOn_Rho Work.Spaces.eta)
      (Work.FTS.CoercivityFix.Coer1.Rho_nonneg Work.Spaces.eta)
      (sq_DzEta_O α hs hm 0 (by norm_num)) (sq_DzEta_O α hs hm 1 (by norm_num))
  · -- `intL_Dz_eta`
    exact intL_of_O hs.Dz (Work.FTS.CoercivityFix.Coer1.continuousOn_Rho Work.Spaces.eta)
      (Work.FTS.CoercivityFix.Coer1.Rho_nonneg Work.Spaces.eta)
      (sq_DzEta_O α hs hm 1 (by norm_num)) (sq_DzEta_O α hs hm 2 (by norm_num))
  · -- `intL_f_one`
    exact intL_of_O hs Work.FTS.CoercivityFix.Coer1.continuousOn_w2
      Work.FTS.CoercivityFix.Coer1.w2_nonneg
      (sq_DzOne_O α hs hm 0 (by norm_num)) (sq_DzOne_O α hs hm 1 (by norm_num))
  · -- `intL_Dz_one`
    exact intL_of_O hs.Dz Work.FTS.CoercivityFix.Coer1.continuousOn_w2
      Work.FTS.CoercivityFix.Coer1.w2_nonneg
      (sq_DzOne_O α hs hm 1 (by norm_num)) (sq_DzOne_O α hs hm 2 (by norm_num))
  · -- `intL_Dth_one`
    exact intL_of_O hs.Dth Work.FTS.CoercivityFix.Coer1.continuousOn_w2
      Work.FTS.CoercivityFix.Coer1.w2_nonneg
      (sq_MixedOne_O α hα hs hm 1 0 (by norm_num) (by norm_num))
      (sq_MixedOne_O α hα hs hm 1 1 (by norm_num) (by norm_num))
  · -- `intL_Dth_gam`
    exact intL_of_O hs.Dth (Work.FTS.CoercivityFix.Coer1.continuousOn_Rho
        (Work.Spaces.gam α))
      (Work.FTS.CoercivityFix.Coer1.Rho_nonneg (Work.Spaces.gam α))
      (sq_MixedGam_O α hα hs hm 1 0 (by norm_num) (by norm_num))
      (sq_MixedGam_O α hα hs hm 1 1 (by norm_num) (by norm_num))
  · -- `dzDthComm`
    exact ae_DzDth_comm_O hs

end Work.FTS.CoercivityFix.Coer1SO
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1SO.zibpO_of =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Coer1SO

open scoped Real Topology
open MeasureTheory Filter

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The pointwise identities in the open class -/

/-- `𝓛u·u·w² = (u w)² + ½ z ∂_z((u w)²)` on the open quadrant, for `SmoothOpen u`. -/
theorem l_self_w_sq_O {u : Fn} (hu : Work.FTS.EllipticEst.SmoothOpen u) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Coercivity.L u z θ * u z θ * Work.Spaces.w z ^ 2
      = (u z θ * Work.Spaces.w z) ^ 2
        + (1 / 2) * (z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z) := by
  have hd : DifferentiableAt ℝ (fun z' => u z' θ) z :=
    ((hu.curry_z hθ).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
      (isOpen_Ioi.mem_nhds hz)
  have hf : HasDerivAt (fun z' => u z' θ) (Work.Spaces.pz u z θ) z := hd.hasDerivAt
  have hLw : Work.Coercivity.L u z θ * Work.Spaces.w z
      = u z θ * Work.Spaces.w z
        + z * Work.Spaces.pz (fun z θ => u z θ * Work.Spaces.w z) z θ :=
    Work.Coercivity.L_mul_w_deriv hz hf
  have hgw : DifferentiableAt ℝ (fun z' => u z' θ * Work.Spaces.w z') z :=
    (hf.mul (Work.Coercivity.hasDerivAt_w (ne_of_gt hz))).differentiableAt
  have hgsq : deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z
      = 2 * (u z θ * Work.Spaces.w z)
          * Work.Spaces.pz (fun z θ => u z θ * Work.Spaces.w z) z θ := by
    have h1 := (hgw.hasDerivAt).pow 2
    have h2 : deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z
        = 2 * (u z θ * Work.Spaces.w z) ^ (2 - 1)
            * deriv (fun z' => u z' θ * Work.Spaces.w z') z := h1.deriv
    rw [h2]
    simp only [Nat.reduceSub, pow_one]
    rfl
  have hkey : Work.Coercivity.L u z θ * u z θ * Work.Spaces.w z ^ 2
      = (Work.Coercivity.L u z θ * Work.Spaces.w z) * (u z θ * Work.Spaces.w z) := by
    ring
  rw [hkey, hLw, hgsq]
  ring

/-- `∂_z(z (u w)²) = (u w)² + z ∂_z((u w)²)` on the open quadrant, for `SmoothOpen u`. -/
theorem deriv_zw_sq_O {u : Fn} (hu : Work.FTS.EllipticEst.SmoothOpen u) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    deriv (fun z' => z' * (u z' θ * Work.Spaces.w z') ^ 2) z
      = (u z θ * Work.Spaces.w z) ^ 2
        + z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z := by
  have hd : DifferentiableAt ℝ (fun z' => u z' θ) z :=
    ((hu.curry_z hθ).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
      (isOpen_Ioi.mem_nhds hz)
  have hw : DifferentiableAt ℝ (Work.Spaces.w) z :=
    (Work.Coercivity.hasDerivAt_w (ne_of_gt hz)).differentiableAt
  have hg : DifferentiableAt ℝ (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z :=
    (hd.mul hw).pow 2
  have hmain : deriv (fun z' => z' * (u z' θ * Work.Spaces.w z') ^ 2) z
      = 1 * (u z θ * Work.Spaces.w z) ^ 2
        + z * deriv (fun z' => (u z' θ * Work.Spaces.w z') ^ 2) z :=
    HasDerivAt.deriv ((hasDerivAt_id z).mul hg.hasDerivAt)
  rw [hmain]; ring

/-- The form of `deriv_zw_sq_O` that identifies the derivative with the `𝓛`-pairing:
`∂_z(z (u w)²) = 2 (𝓛u·u·w²) − (u w)²`. -/
theorem deriv_zw_sq_eq_O {u : Fn} (hu : Work.FTS.EllipticEst.SmoothOpen u) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    deriv (fun z' => z' * (u z' θ * Work.Spaces.w z') ^ 2) z
      = 2 * (Work.Coercivity.L u z θ * u z θ * Work.Spaces.w z ^ 2)
        - (u z θ * Work.Spaces.w z) ^ 2 := by
  have h1 := deriv_zw_sq_O hu hz hθ
  have h2 := l_self_w_sq_O hu hz hθ
  linarith [h1, h2]

/-! ## The package -/

theorem zibpO_of {u : Work.FTS.Galerkin.Fn} (hs : Work.FTS.EllipticEst.SmoothOpen u)
    (hbd0 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Filter.Tendsto (fun z => z * (u z θ * Work.Spaces.w z) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hbdT : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Filter.Tendsto (fun z => z * (u z θ * Work.Spaces.w z) ^ 2) Filter.atTop (nhds 0))
    (hSq : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (u z θ * Work.Spaces.w z) ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hL : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.L u z θ * u z θ * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    Work.FTS.CoercivityFix.Coer1SO.ZIBPO u := by
  refine ⟨hs, hbd0, hbdT, ?_, ?_⟩
  · refine (Work.FTS.CoercivityFix.Coer1.ae_slice_of_integrableOn hSq).mono (fun θ hθ => ?_)
    rw [MeasureTheory.IntegrableOn, ← Work.FTS.CoercivityFix.Coer1.iz_ae_restrict]
    exact hθ
  · refine (((Work.FTS.CoercivityFix.Coer1.ae_slice_of_integrableOn hL).and
      (Work.FTS.CoercivityFix.Coer1.ae_slice_of_integrableOn hSq)).and
      Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo).mono (fun θ hθ => ?_)
    obtain ⟨⟨hLθ, hSqθ⟩, hθIoo⟩ := hθ
    have h1 : MeasureTheory.IntegrableOn
        (fun z => Work.Coercivity.L u z θ * u z θ * Work.Spaces.w z ^ 2) (Set.Ioi 0) := by
      rw [MeasureTheory.IntegrableOn, ← Work.FTS.CoercivityFix.Coer1.iz_ae_restrict]
      exact hLθ
    have h2 : MeasureTheory.IntegrableOn
        (fun z => (u z θ * Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
      rw [MeasureTheory.IntegrableOn, ← Work.FTS.CoercivityFix.Coer1.iz_ae_restrict]
      exact hSqθ
    have h3 := (h1.const_mul 2).sub h2
    refine MeasureTheory.IntegrableOn.congr_fun h3 (fun z hz => ?_) measurableSet_Ioi
    exact (deriv_zw_sq_eq_O hs hz hθIoo).symm

end Work.FTS.CoercivityFix.Coer1SO
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1T.aesm_T2G_Q =====
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

/-!
# A.e. strong measurability of the `T₂`-integrand in the interior class `SmoothQuad`

The integrand `T2 α f z θ * D_θ f z θ * thetaW α z θ` of the `T₂`-pairing is a product of a
measurable function of `(z,θ)` (the angular data `D_θΓ`, the radial coefficient
`2z/(c(1+z)²)`, the weight `thetaW α = w²·sin(2θ)^{-γ}`), a function of `z` alone
(`L₁₂(f)`, continuous on `(0,∞)` by `HardyHyp`) and `D_θ f`, which is continuous on the open
quadrant for data of class `SmoothQuad` (genuine `C^∞`, not analyticity).

This is the interior-class port of the private lemma `aesm_T2G` of
`Submission/Work/Coercivity/wip_T2_ge.lean`, where the smoothness hypothesis is the analytic
class `Work.Spaces.SmoothNbhd f`; that hypothesis is incompatible with a cut-off (see the
`SmoothQuad` discussion in `Work.FTS.LocData.Defs`), so the port is needed on the route.
-/


/-- A function of `z` alone which is continuous on `(0,∞)` is a.e. strongly measurable on the
quadrant; applied to `L₁₂(f)`, which is continuous on `(0,∞)` under `HardyHyp`. -/
theorem aesm_of_continuousOn_Ioi {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Ioi 0)) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => g p.1)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _ (hg.comp continuous_fst.continuousOn (fun _ hp => hp.1))


end Work.FTS.CoercivityFix.Coer1T
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1T.intDth_Lhat_gam =====
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



end Work.FTS.CoercivityFix.Coer1T
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.DzSelf.H1IP_Dz_self =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.DzSelf

open Work.FTS.Galerkin (Fn)
open Work.FTS.CoercivityFix.Coer1 (En Rho wip_Rho_self)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The product of the two restricted measures on the quadrant
`[0,∞) × [0,π/2]`, i.e. Lebesgue measure restricted to `Iz ×ˢ Iθ`. -/
abbrev PM : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
    (MeasureTheory.volume.restrict Work.Spaces.Iθ)

/-! ## Two elementary tools -/

/-- The triangle inequality for four real terms. -/
theorem abs_add_four (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 : |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
  have h2 : |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
  have h3 : |a + b| ≤ |a| + |b| := abs_add_le _ _
  linarith

/-! ## The weighted AM–GM bound for `wip` -/

/-- **Weighted AM–GM (Cauchy–Schwarz) for `wip`.**  If `0 ≤ ρ ≤ ρ'` almost everywhere on
the quadrant, and the three products `u²ρ'`, `v²ρ'`, `uvρ` are integrable, then

  `|wip ρ u v| ≤ (wip ρ' u u + wip ρ' v v) / 2 = (|u|²_{ρ'} + |v|²_{ρ'}) / 2`.

The proof is the pointwise bound `|uv|ρ ≤ (u² + v²)ρ/2 ≤ (u² + v²)ρ'/2`, integrated with
Fubini (`Work.Coercivity.wip_eq_integral_prod`). -/
theorem wip_abs_le_half {ρ ρ' u v : Fn}
    (hρnn : ∀ᵐ p ∂PM, 0 ≤ ρ p.1 p.2)
    (hle : ∀ᵐ p ∂PM, ρ p.1 p.2 ≤ ρ' p.1 p.2)
    (hu : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * u z θ * ρ' z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hv : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => v z θ * v z θ * ρ' z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (huv : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ * v z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    |Work.Coercivity.wip ρ u v|
      ≤ (Work.Coercivity.wip ρ' u u + Work.Coercivity.wip ρ' v v) / 2 := by
  -- Move the three integrability certificates to the product measure.
  have huP : Integrable (fun p : ℝ × ℝ => u p.1 p.2 * u p.1 p.2 * ρ' p.1 p.2) PM := by
    rw [MeasureTheory.IntegrableOn, ← Coer1.iz_prod_restrict] at hu
    exact hu
  have hvP : Integrable (fun p : ℝ × ℝ => v p.1 p.2 * v p.1 p.2 * ρ' p.1 p.2) PM := by
    rw [MeasureTheory.IntegrableOn, ← Coer1.iz_prod_restrict] at hv
    exact hv
  have huvP : Integrable (fun p : ℝ × ℝ => u p.1 p.2 * v p.1 p.2 * ρ p.1 p.2) PM := by
    rw [MeasureTheory.IntegrableOn, ← Coer1.iz_prod_restrict] at huv
    exact huv
  -- The majorant `(u²ρ' + v²ρ')/2` is integrable.
  have hmaj : Integrable (fun p : ℝ × ℝ =>
      (u p.1 p.2 * u p.1 p.2 * ρ' p.1 p.2 + v p.1 p.2 * v p.1 p.2 * ρ' p.1 p.2) / 2) PM :=
    (huP.add hvP).div_const 2
  -- The pointwise bound (a.e.).
  have hbound : ∀ᵐ p ∂PM, |u p.1 p.2 * v p.1 p.2 * ρ p.1 p.2|
      ≤ (u p.1 p.2 * u p.1 p.2 * ρ' p.1 p.2 + v p.1 p.2 * v p.1 p.2 * ρ' p.1 p.2) / 2 := by
    filter_upwards [hρnn, hle] with p hρ hρle
    have hρ' : 0 ≤ ρ' p.1 p.2 := le_trans hρ hρle
    calc |u p.1 p.2 * v p.1 p.2 * ρ p.1 p.2|
        = |u p.1 p.2 * v p.1 p.2| * ρ p.1 p.2 := by
          rw [abs_mul, abs_of_nonneg hρ]
      _ ≤ |u p.1 p.2 * v p.1 p.2| * ρ' p.1 p.2 :=
          mul_le_mul_of_nonneg_left hρle (abs_nonneg _)
      _ ≤ (u p.1 p.2 ^ 2 * ρ' p.1 p.2 + v p.1 p.2 ^ 2 * ρ' p.1 p.2) / 2 := by
          have h := Coer1.two_abs_mul_le (u p.1 p.2) (v p.1 p.2) (ρ' p.1 p.2) hρ'
          linarith
      _ = (u p.1 p.2 * u p.1 p.2 * ρ' p.1 p.2 + v p.1 p.2 * v p.1 p.2 * ρ' p.1 p.2) / 2 := by
          ring
  rw [Work.Coercivity.wip_eq_integral_prod ρ u v huv,
    Work.Coercivity.wip_eq_integral_prod ρ' u u hu,
    Work.Coercivity.wip_eq_integral_prod ρ' v v hv]
  calc |∫ p, u p.1 p.2 * v p.1 p.2 * ρ p.1 p.2 ∂PM|
      ≤ ∫ p, |u p.1 p.2 * v p.1 p.2 * ρ p.1 p.2| ∂PM :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ p, (u p.1 p.2 * u p.1 p.2 * ρ' p.1 p.2
          + v p.1 p.2 * v p.1 p.2 * ρ' p.1 p.2) / 2 ∂PM :=
        MeasureTheory.integral_mono_ae huvP.abs hmaj hbound
    _ = (∫ p, u p.1 p.2 * u p.1 p.2 * ρ' p.1 p.2 ∂PM
          + ∫ p, v p.1 p.2 * v p.1 p.2 * ρ' p.1 p.2 ∂PM) / 2 := by
        rw [MeasureTheory.integral_div, MeasureTheory.integral_add huP hvP]

/-! ## The `En`-energies as product-measure integrals -/


/-! ## The `En`-energies against the `ℋ⁴`-norm square -/





/-! ## The main estimate -/


end Work.FTS.CoercivityFix.DzSelf
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E1Norm.GaugeMass =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E1Norm

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- The gauge integrand is continuous on the open interval (every factor is: `Γ²` is a real
power of the positive function `sin θ cos²θ`, `(sin²2θ + α)²` is a polynomial, and
`sin(2θ)^{-γ}` is a real power of the positive `sin(2θ)`). -/
private theorem continuousOn_gauge_integrand (α : ℝ) :
    ContinuousOn (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2 * ((Real.sin (2 * θ)) ^ 2 + α) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) (Set.Ioo (0 : ℝ) (π / 2)) := by
  have hbase : ContinuousOn (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) (Set.Ioo (0 : ℝ) (π / 2)) :=
    (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn
  have hΓ : ContinuousOn (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3))
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    hbase.rpow_const (fun θ hθ => Or.inl (by
      have h1 : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
      have h2 : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      positivity))
  have hΓ2 : ContinuousOn (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2) (Set.Ioo (0 : ℝ) (π / 2)) := by
    refine (hΓ.mul hΓ).congr (fun θ _ => ?_)
    simp only [Pi.mul_apply]
    rw [show Work.Spaces.Gam α θ = (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) from rfl, pow_two]
  have hpoly : ContinuousOn (fun θ : ℝ => ((Real.sin (2 * θ)) ^ 2 + α) ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    (by fun_prop : Continuous fun θ : ℝ => ((Real.sin (2 * θ)) ^ 2 + α) ^ 2).continuousOn
  have hsm : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (Set.Ioo (0 : ℝ) (π / 2)) := by
    have hsin2 : Continuous fun θ : ℝ => Real.sin (2 * θ) :=
      Real.continuous_sin.comp (by fun_prop)
    refine hsin2.continuousOn.rpow_const (fun θ hθ => Or.inl ?_)
    have h1 : (0 : ℝ) < 2 * θ := by linarith [hθ.1]
    have h2 : 2 * θ < Real.pi := by linarith [hθ.2, Real.pi_pos]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h1 h2)
  exact (hΓ2.mul hpoly).mul hsm

/-- The pointwise domination of the gauge integrand by the two explicit profile pieces. -/
theorem gauge_pt (α θ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.Gam α θ) ^ 2 * ((Real.sin (2 * θ)) ^ 2 + α) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ 2 * (Real.sin (2 * θ)) ^ (4 + 2 * α / 3 - Work.Spaces.gam α)
        + 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsnn : (0 : ℝ) ≤ Real.sin (2 * θ) := le_of_lt hs
  have hGam : (Work.Spaces.Gam α θ) ^ 2 ≤ (Real.sin (2 * θ)) ^ (2 * α / 3) := by
    rw [Work.FTS.CoercivityFix.Transfer.E1Parts.Gam_sq_eq α θ hθ]
    refine Real.rpow_le_rpow ?_ (Work.FTS.CoercivityFix.Transfer.E1Parts.sin_cos_sq_le_sin_two θ hθ)
      (by linarith)
    have h1 : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have h2 : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    positivity
  have hpoly : ((Real.sin (2 * θ)) ^ 2 + α) ^ 2
      ≤ 2 * (Real.sin (2 * θ)) ^ 4 + 2 * α ^ 2 := by
    nlinarith [sq_nonneg ((Real.sin (2 * θ)) ^ 2 - α)]
  have hprod : (Work.Spaces.Gam α θ) ^ 2 * ((Real.sin (2 * θ)) ^ 2 + α) ^ 2
      ≤ (Real.sin (2 * θ)) ^ (2 * α / 3) * (2 * (Real.sin (2 * θ)) ^ 4 + 2 * α ^ 2) :=
    mul_le_mul hGam hpoly (sq_nonneg _) (Real.rpow_nonneg hsnn _)
  have hsmnn : (0 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hsnn _
  have h1 : (Work.Spaces.Gam α θ) ^ 2 * ((Real.sin (2 * θ)) ^ 2 + α) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ (Real.sin (2 * θ)) ^ (2 * α / 3)
        * (2 * (Real.sin (2 * θ)) ^ 4 + 2 * α ^ 2) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    mul_le_mul_of_nonneg_right hprod hsmnn
  have hA : (Real.sin (2 * θ)) ^ (2 * α / 3) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      = (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) := by
    rw [← Real.rpow_add hs]; ring_nf
  have h4 : (Real.sin (2 * θ)) ^ 4 = (Real.sin (2 * θ)) ^ (4 : ℝ) :=
    (Real.rpow_natCast _ 4).symm
  have hB : (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) * (Real.sin (2 * θ)) ^ (4 : ℝ)
      = (Real.sin (2 * θ)) ^ (4 + 2 * α / 3 - Work.Spaces.gam α) := by
    rw [← Real.rpow_add hs]; ring_nf
  refine le_trans h1 (le_of_eq ?_)
  calc (Real.sin (2 * θ)) ^ (2 * α / 3) * (2 * (Real.sin (2 * θ)) ^ 4 + 2 * α ^ 2)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      = 2 * ((Real.sin (2 * θ)) ^ (2 * α / 3) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Real.sin (2 * θ)) ^ 4)
        + 2 * α ^ 2 * ((Real.sin (2 * θ)) ^ (2 * α / 3)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
    _ = 2 * ((Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) * (Real.sin (2 * θ)) ^ 4)
        + 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) := by rw [hA]
    _ = 2 * ((Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) * (Real.sin (2 * θ)) ^ (4 : ℝ))
        + 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) := by rw [h4]
    _ = 2 * (Real.sin (2 * θ)) ^ (4 + 2 * α / 3 - Work.Spaces.gam α)
        + 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) := by rw [hB]

/-- **The angular mass of the gauge profile is bounded by an `α`-independent constant.**  For
`0 < α ≤ 1` the integrand `Γ(θ)²(sin²2θ + α)²·sin(2θ)^{-γ}` is integrable on `Iθ` and its
integral is at most `1000`. -/
theorem gauge_mass (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2
        * ((Real.sin (2 * θ)) ^ 2 + α) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ) ^ 2 * ((Real.sin (2 * θ)) ^ 2 + α) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) ≤ 1000 := by
  have hIoo : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Work.Spaces.Iθ := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl]
    exact MeasureTheory.Ioo_ae_eq_Icc
  have hsin : ∀ θ ∈ Work.Spaces.Iθ, (0 : ℝ) ≤ Real.sin (2 * θ) :=
    fun θ hθ => Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
  -- ## integrability of the two profile pieces
  have hp1 : -1 < 2 * α / 3 - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hp2 : 2 * α / 3 - Work.Spaces.gam α ≤ 0 := by rw [Work.Spaces.gam]; linarith
  obtain ⟨hsm_int, hsm_bd⟩ := Work.Spaces.sin_two_rpow (2 * α / 3 - Work.Spaces.gam α) hp1 hp2
  have hq0 : (0 : ℝ) ≤ 4 + 2 * α / 3 - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hq_cont : Continuous fun θ : ℝ => (Real.sin (2 * θ)) ^ (4 + 2 * α / 3 - Work.Spaces.gam α) :=
    (Real.continuous_rpow_const hq0).comp
      (Real.continuous_sin.comp (by fun_prop))
  have hq_int : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (4 + 2 * α / 3 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.integrableOn_const (μ := volume) (s := Work.Spaces.Iθ) (C := (1 : ℝ)) ?_)
      hq_cont.aestronglyMeasurable ?_
    · rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      have hs0 : (0 : ℝ) ≤ Real.sin (2 * θ) :=
        Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hs0 _)]
      exact Real.rpow_le_one hs0 (Real.sin_le_one _) hq0
  have hDint : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      2 * (Real.sin (2 * θ)) ^ (4 + 2 * α / 3 - Work.Spaces.gam α)
        + 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)) Work.Spaces.Iθ :=
    (hq_int.const_mul 2).add (hsm_int.const_mul (2 * α ^ 2))
  -- ## the bound on the integral of the profile
  have hone := Work.Spaces.sin_two_rpow 0 (by norm_num) (le_refl 0)
  have hq_bd : (∫ θ in Work.Spaces.Iθ,
      (Real.sin (2 * θ)) ^ (4 + 2 * α / 3 - Work.Spaces.gam α)) ≤ 100 := by
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => Real.rpow_nonneg (hsin θ hθ) _))
      hone.1
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
        have h1 : (Real.sin (2 * θ)) ^ (4 + 2 * α / 3 - Work.Spaces.gam α) ≤ 1 :=
          Real.rpow_le_one (hsin θ hθ) (Real.sin_le_one _) hq0
        simpa using h1))
    have hone' : (∫ θ in Set.Icc (0 : ℝ) (π / 2), (Real.sin (2 * θ)) ^ (0 : ℝ)) ≤ 100 := by
      have h := hone.2
      have h100 : (100 : ℝ) / (0 + 1) = 100 := by norm_num
      rw [h100] at h
      simpa only [Work.Spaces.Iθ] using h
    exact le_trans hmono hone'
  have hsm_bd' : (∫ θ in Work.Spaces.Iθ,
      (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)) ≤ 3000 / (17 * α) := by
    have h17 : 2 * α / 3 - Work.Spaces.gam α + 1 = 17 * α / 30 := by
      rw [Work.Spaces.gam]; ring
    refine le_trans hsm_bd ?_
    rw [h17]
    exact le_of_eq (by field_simp; ring)
  have hDbd : (∫ θ in Work.Spaces.Iθ,
      2 * (Real.sin (2 * θ)) ^ (4 + 2 * α / 3 - Work.Spaces.gam α)
        + 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)) ≤ 1000 := by
    rw [MeasureTheory.integral_add (hq_int.const_mul 2) (hsm_int.const_mul (2 * α ^ 2)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have h3a : 2 * (∫ θ in Work.Spaces.Iθ,
        (Real.sin (2 * θ)) ^ (4 + 2 * α / 3 - Work.Spaces.gam α)) ≤ 2 * 100 :=
      mul_le_mul_of_nonneg_left hq_bd (by norm_num)
    have h3b : 2 * α ^ 2 * (∫ θ in Work.Spaces.Iθ,
        (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α)) ≤ 2 * α ^ 2 * (3000 / (17 * α)) :=
      mul_le_mul_of_nonneg_left hsm_bd' (by positivity)
    have h2 : 2 * α ^ 2 * (3000 / (17 * α)) ≤ 400 := by
      rw [show 2 * α ^ 2 * (3000 / (17 * α)) = 6000 * α / 17 by field_simp; ring]
      nlinarith [hα1]
    linarith [h3a, h3b, h2]
  -- ## the a.e. pointwise bound and the measurability
  have hpt : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.Gam α θ) ^ 2 * ((Real.sin (2 * θ)) ^ 2 + α) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ 2 * (Real.sin (2 * θ)) ^ (4 + 2 * α / 3 - Work.Spaces.gam α)
          + 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) := by
    have h1 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2))),
        (Work.Spaces.Gam α θ) ^ 2 * ((Real.sin (2 * θ)) ^ 2 + α) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          ≤ 2 * (Real.sin (2 * θ)) ^ (4 + 2 * α / 3 - Work.Spaces.gam α)
            + 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
        (fun θ hθ => gauge_pt α θ hα hα1 hθ)
    rwa [MeasureTheory.Measure.restrict_congr_set hIoo] at h1
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2
      * ((Real.sin (2 * θ)) ^ 2 + α) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h1 : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2
        * ((Real.sin (2 * θ)) ^ 2 + α) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) :=
      (continuousOn_gauge_integrand α).aestronglyMeasurable measurableSet_Ioo
    rwa [MeasureTheory.Measure.restrict_congr_set hIoo] at h1
  have hpt_norm : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖(Work.Spaces.Gam α θ) ^ 2 * ((Real.sin (2 * θ)) ^ 2 + α) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))‖
        ≤ 2 * (Real.sin (2 * θ)) ^ (4 + 2 * α / 3 - Work.Spaces.gam α)
          + 2 * α ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 3 - Work.Spaces.gam α) := by
    filter_upwards [hpt, MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ h1 h2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Real.rpow_nonneg (hsin θ h2) _))]
    exact h1
  refine ⟨MeasureTheory.Integrable.mono' hDint haesm hpt_norm, ?_⟩
  refine le_trans (MeasureTheory.integral_mono_of_nonneg
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
      mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Real.rpow_nonneg (hsin θ hθ) _)))
    hDint hpt) hDbd

end Work.FTS.CoercivityFix.Transfer.E1Norm
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E1Norm.Lop_iter_LopGam_Gamma_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `α`-gain in the angular iterate bound for `Lop^i (Lop (Gam α))`

`Γ = Gam α = (sinθ cos²θ)^{α/3}` has `Lop (Gam α) = (α/3)(6cos²θ - 4)·Γ`, so for `1 ≤ k`
the iterate `Lop^[k] (Gam α)` equals `Γ θ` times the explicit polynomial coefficient
`(2α/3)·Aang (k-1)(cos²θ, α)` (`E1Parts.Lop_iter_Gam_succ`).  The `Construction` bounds give
`|Aang j x α| ≤ 10^7(α + 4x(1-x)) ≤ 2·10^7` on `[0,1]` for `j ≤ 3`, so the explicit factor `α`
in the coefficient survives:

`|Lop^[i] (Lop (Gam α)) θ| ≤ (4/3)·10^7·α·Γ θ ≤ 10^8·α·Γ θ`   (`i ≤ 3`, `θ ∈ Iθ`).

At the endpoints `θ = 0, π/2` both sides vanish because `sin(2θ) = 0` kills the innermost
`Lop`.  This is the pointwise input of the `E1`-transfer estimate: the angular profile
`D_θΓ` enters `E1 = D_θΓ · radA` with a *full* power of `α`.
-/

open scoped Real

namespace Work.FTS.CoercivityFix.Transfer.E1Norm

/-- `Lop^[i] (Lop f) = Lop^[i+1] f`. -/
lemma Lop_iter_Lop_eq (f : ℝ → ℝ) (i : ℕ) :
    (Work.Spaces.Lop^[i] (Work.Spaces.Lop f)) = (Work.Spaces.Lop^[i + 1] f) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]

/-- `|Aang i x α| ≤ 2·10^7` for `i ≤ 3`, `x ∈ [0,1]`, `0 < α ≤ 1`. -/
lemma Aang_abs_le_const (i : ℕ) (hi : i ≤ 3) (x α : ℝ) (hx : x ∈ Set.Icc 0 1)
    (hα : 0 < α) (hα1 : α ≤ 1) :
    |Work.Construction.Aang i x α| ≤ 2 * 10 ^ 7 := by
  have hx4 : 4 * x * (1 - x) ≤ 1 := by nlinarith [sq_nonneg (2 * x - 1)]
  interval_cases i
  · rw [Work.Construction.Aang_zero]
    rw [abs_le]
    constructor <;> nlinarith [hx.1, hx.2]
  · have h := Work.Construction.glop_Aang_bound_one x α hx hα hα1
    nlinarith [h, hx4, hα, hα1]
  · have h := Work.Construction.glop_Aang_bound_two x α hx hα hα1
    nlinarith [h, hx4, hα, hα1]
  · have h := Work.Construction.glop_Aang_bound_three x α hx hα hα1
    nlinarith [h, hx4, hα, hα1]

theorem Lop_iter_LopGam_Gamma_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      ∀ i : ℕ, i ≤ 3 → ∀ θ ∈ Work.Spaces.Iθ,
        |(Work.Spaces.Lop^[i] (Work.Spaces.Lop (Work.Spaces.Gam α))) θ|
          ≤ K * α * Work.Spaces.Gam α θ := by
  refine ⟨10 ^ 8, by norm_num, ?_⟩
  intro α hα hα1 i hi θ hθ
  rw [Lop_iter_Lop_eq (Work.Spaces.Gam α) i]
  -- the two endpoints of `Iθ`: `sin (2θ) = 0` makes the innermost `Lop` vanish
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · subst h0
    have hzero : (Work.Spaces.Lop^[i + 1] (Work.Spaces.Gam α)) 0 = 0 := by
      rw [Function.iterate_succ_apply']
      simp only [Work.Spaces.Lop]
      rw [show Real.sin (2 * (0 : ℝ)) = 0 by norm_num, zero_mul]
    rw [hzero, show Work.Spaces.Gam α 0 = (Real.sin 0 * Real.cos 0 ^ 2) ^ (α / 3) from rfl,
      show Real.sin 0 * Real.cos 0 ^ 2 = (0 : ℝ) by norm_num,
      Real.zero_rpow (by positivity : α / 3 ≠ 0), mul_zero]
    norm_num
  rcases eq_or_lt_of_le hθ.2 with h1 | h1
  · subst h1
    have hzero : (Work.Spaces.Lop^[i + 1] (Work.Spaces.Gam α)) (π / 2) = 0 := by
      rw [Function.iterate_succ_apply']
      simp only [Work.Spaces.Lop]
      rw [show Real.sin (2 * (π / 2)) = 0 by
        rw [show 2 * (π / 2) = π by ring, Real.sin_pi], zero_mul]
    rw [hzero, show Work.Spaces.Gam α (π / 2)
        = (Real.sin (π / 2) * Real.cos (π / 2) ^ 2) ^ (α / 3) from rfl,
      show Real.sin (π / 2) * Real.cos (π / 2) ^ 2 = (0 : ℝ) by norm_num,
      Real.zero_rpow (by positivity : α / 3 ≠ 0), mul_zero]
    norm_num
  · -- interior point: use the explicit polynomial form of the iterate
    have hθ' : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨h0, h1⟩
    rw [Work.FTS.CoercivityFix.Transfer.E1Parts.Lop_iter_Gam_succ α hα i
      (le_trans hi (by norm_num : (3 : ℕ) ≤ 4)) θ hθ']
    have hGam0 : 0 ≤ Work.Spaces.Gam α θ := by
      rw [show Work.Spaces.Gam α θ = (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) from rfl]
      exact Real.rpow_nonneg (mul_nonneg
        (le_of_lt (Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [h1, Real.pi_pos])))
        (sq_nonneg _)) _
    have hA : |Work.Construction.Aang i (Real.cos θ ^ 2) α| ≤ 2 * 10 ^ 7 :=
      Aang_abs_le_const i hi (Real.cos θ ^ 2) α
        ⟨sq_nonneg _, Real.cos_sq_le_one θ⟩ hα hα1
    have hcoef : |2 * α / 3 * Work.Construction.Aang i (Real.cos θ ^ 2) α|
        ≤ 10 ^ 8 * α := by
      rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * α / 3)]
      nlinarith [hA, hα]
    rw [abs_mul, abs_of_nonneg hGam0]
    calc Work.Spaces.Gam α θ * |2 * α / 3 * Work.Construction.Aang i (Real.cos θ ^ 2) α|
        ≤ Work.Spaces.Gam α θ * (10 ^ 8 * α) :=
          mul_le_mul_of_nonneg_left hcoef hGam0
      _ = 10 ^ 8 * α * Work.Spaces.Gam α θ := by ring

end Work.FTS.CoercivityFix.Transfer.E1Norm
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E1Norm.Lop_iter_LopGam_gauge_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `α`-gain in the angular iterate bound for `Lop^i (Lop (Gam α))`, with the gauge factor

`Γ = Gam α = (sinθ cos²θ)^{α/3}` has `Lop (Gam α) = (α/3)(6cos²θ - 4)·Γ`, so for `1 ≤ k` the
iterate `Lop^[k] (Gam α)` equals `Γ θ` times the explicit polynomial coefficient
`(2α/3)·Aang (k-1)(cos²θ, α)` (`E1Parts.Lop_iter_Gam_succ`).  The `Construction` bounds give,
for `1 ≤ j ≤ 3` and `x = cos²θ ∈ [0,1]`,

`|Aang j x α| ≤ 10^7·(α + 4x(1-x)) = 10^7·(α + sin(2θ)²)`,

which is *not* just an absolute constant: it carries the gauge factor `sin(2θ)² + α` that
vanishes at both ends of `Iθ`, exactly where `Γ` degenerates.  Consequently, for `1 ≤ i ≤ 3`
and `θ ∈ Iθ`,

`|Lop^[i] (Lop (Gam α)) θ| ≤ 10^7·α·Γ(θ)·(sin(2θ)² + α)`,

the gauge version of the `E1`-transfer pointwise input.  The hypothesis `1 ≤ i` is essential:
the excluded case `i = 0` involves `Aang 0 = 3x - 2`, which is `≠ 0` at `x = 1` (i.e. at
`θ = 0`), where the gauge factor degenerates to `α`.

At the endpoints `θ = 0, π/2` both sides vanish because the outermost `Lop` carries the factor
`sin(2θ) = 0`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real

namespace Work.FTS.CoercivityFix.Transfer.E1Norm

/-- `Lop^[i] (Lop f) = Lop^[i+1] f`. -/
lemma Lop_iter_Lop_eq_gauge (f : ℝ → ℝ) (i : ℕ) :
    (Work.Spaces.Lop^[i] (Work.Spaces.Lop f)) = (Work.Spaces.Lop^[i + 1] f) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]

/-- `Lop^[n] f` vanishes at `θ = 0` for `n ≥ 1` (the outermost `Lop` carries `sin(2·0) = 0`). -/
lemma Lop_iter_apply_zero (f : ℝ → ℝ) : ∀ n : ℕ, 0 < n → (Work.Spaces.Lop^[n] f) 0 = 0 := by
  intro n hn
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [Function.iterate_succ_apply']
  simp only [Work.Spaces.Lop]
  rw [show Real.sin (2 * (0 : ℝ)) = 0 by norm_num, zero_mul]

/-- `Lop^[n] f` vanishes at `θ = π/2` for `n ≥ 1`. -/
lemma Lop_iter_apply_pi_half (f : ℝ → ℝ) : ∀ n : ℕ, 0 < n →
    (Work.Spaces.Lop^[n] f) (π / 2) = 0 := by
  intro n hn
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [Function.iterate_succ_apply']
  simp only [Work.Spaces.Lop]
  rw [show Real.sin (2 * (π / 2)) = 0 by
    rw [show 2 * (π / 2) = π by ring, Real.sin_pi], zero_mul]

/-- `sin(2θ)² = 4 cos²θ (1 - cos²θ)`. -/
lemma sin_two_sq_eq (θ : ℝ) :
    Real.sin (2 * θ) ^ 2 = 4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2) := by
  rw [Real.sin_two_mul]
  have h := Real.sin_sq θ
  nlinarith [h]

/-- The interior pointwise bound: for `1 ≤ i ≤ 3` and `θ ∈ (0, π/2)`. -/
lemma Lop_iter_LopGam_gauge_bound_interior (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (i : ℕ)
    (hi1 : 1 ≤ i) (hi3 : i ≤ 3) (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    |(Work.Spaces.Lop^[i] (Work.Spaces.Lop (Work.Spaces.Gam α))) θ|
      ≤ 10 ^ 7 * α * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α) := by
  have hGam := Work.Spaces.Gam_bounds α θ hα ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hx : Real.cos θ ^ 2 ∈ Set.Icc (0 : ℝ) 1 := ⟨sq_nonneg _, Real.cos_sq_le_one θ⟩
  rw [Lop_iter_Lop_eq_gauge,
    Work.FTS.CoercivityFix.Transfer.E1Parts.Lop_iter_Gam_succ α hα i (by omega) θ hθ,
    abs_mul, abs_of_nonneg hGam.1]
  -- the polynomial coefficient bound, with the gauge factor
  have hA : |Work.Construction.Aang i (Real.cos θ ^ 2) α|
      ≤ 10 ^ 7 * (α + 4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2)) := by
    interval_cases i
    · exact Work.Construction.glop_Aang_bound_one _ _ hx hα hα1
    · exact Work.Construction.glop_Aang_bound_two _ _ hx hα hα1
    · exact Work.Construction.glop_Aang_bound_three _ _ hx hα hα1
  have hcoef : |2 * α / 3 * Work.Construction.Aang i (Real.cos θ ^ 2) α|
      ≤ 10 ^ 7 * α * (α + 4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2)) := by
    have h23 : (0 : ℝ) ≤ 2 * α / 3 := by linarith
    have hM : 0 ≤ α + 4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2) := by
      nlinarith [hx.1, hx.2, hα]
    have hle : 2 * α / 3 ≤ α := by linarith
    calc |2 * α / 3 * Work.Construction.Aang i (Real.cos θ ^ 2) α|
        = 2 * α / 3 * |Work.Construction.Aang i (Real.cos θ ^ 2) α| := by
          rw [abs_mul, abs_of_nonneg h23]
      _ ≤ 2 * α / 3 * (10 ^ 7 * (α + 4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2))) :=
          mul_le_mul_of_nonneg_left hA h23
      _ ≤ α * (10 ^ 7 * (α + 4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2))) :=
          mul_le_mul_of_nonneg_right hle (mul_nonneg (by norm_num) hM)
      _ = 10 ^ 7 * α * (α + 4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2)) := by ring
  rw [sin_two_sq_eq θ]
  calc Work.Spaces.Gam α θ
        * |2 * α / 3 * Work.Construction.Aang i (Real.cos θ ^ 2) α|
      ≤ Work.Spaces.Gam α θ
          * (10 ^ 7 * α * (α + 4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2))) :=
        mul_le_mul_of_nonneg_left hcoef hGam.1
    _ = 10 ^ 7 * α * Work.Spaces.Gam α θ * (4 * Real.cos θ ^ 2 * (1 - Real.cos θ ^ 2) + α) := by
        ring

theorem Lop_iter_LopGam_gauge_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ i : ℕ, 1 ≤ i → i ≤ 3 →
      ∀ θ ∈ Work.Spaces.Iθ,
        |(Work.Spaces.Lop^[i] (Work.Spaces.Lop (Work.Spaces.Gam α))) θ|
          ≤ K * α * Work.Spaces.Gam α θ * ((Real.sin (2 * θ)) ^ 2 + α) := by
  refine ⟨10 ^ 7, by norm_num, ?_⟩
  intro α hα hα1 i hi1 hi3 θ hθ
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · -- `θ = 0`: both sides vanish
    subst h0
    rw [Lop_iter_Lop_eq_gauge, Lop_iter_apply_zero (Work.Spaces.Gam α) (i + 1) (by omega),
      abs_zero]
    have hG := Work.Spaces.Gam_bounds α 0 hα ⟨le_refl 0, by positivity⟩
    have hs : 0 ≤ Real.sin (2 * 0) ^ 2 + α := by
      have := sq_nonneg (Real.sin (2 * 0)); linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hα)) hG.1) hs
  rcases eq_or_lt_of_le hθ.2 with h1 | h1
  · -- `θ = π/2`: both sides vanish
    subst h1
    rw [Lop_iter_Lop_eq_gauge, Lop_iter_apply_pi_half (Work.Spaces.Gam α) (i + 1) (by omega),
      abs_zero]
    have hG := Work.Spaces.Gam_bounds α (π / 2) hα ⟨by positivity, le_refl _⟩
    have hs : 0 ≤ Real.sin (2 * (π / 2)) ^ 2 + α := by
      have := sq_nonneg (Real.sin (2 * (π / 2))); linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hα)) hG.1) hs
  · exact Lop_iter_LopGam_gauge_bound_interior α hα hα1 i hi1 hi3 θ ⟨h0, h1⟩

end Work.FTS.CoercivityFix.Transfer.E1Norm
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAPieces =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E1Parts

set_option autoImplicit false
set_option maxHeartbeats 1000000






/-- The explicit expression to which the integrand of `radA` is equal on `(0,∞)`. -/
noncomputable def Efun (α : ℝ) (f : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) : ℝ :=
  (-(∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
        * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z)
        * (if j - b = 0 then Work.Coercivity.L12f f z
            else - Work.Elliptic.Qang f (j - b - 1) z))
      + (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
        * (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z))
    * (-(∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
        * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z)
        * (if j - b = 0 then Work.Coercivity.L12f f z
            else - Work.Elliptic.Qang f (j - b - 1) z))
      + (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
        * (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z))
    * (Work.Spaces.w z * Work.Spaces.w z)

/-- The bracket of `Efun`, exposed for the estimates. -/
noncomputable def Big (α : ℝ) (f : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) : ℝ :=
  -(∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
      * (Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z)
      * (if j - b = 0 then Work.Coercivity.L12f f z
          else - Work.Elliptic.Qang f (j - b - 1) z))
    + (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α)
      * (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z)



/-- The majorant of `Efun`. -/
noncomputable def Maj (α : ℝ) (f : ℝ → ℝ → ℝ) (j : ℕ) (K : ℝ) (z : ℝ) : ℝ :=
  2 * ((K * 2 ^ j) ^ 2 * ((j : ℝ) + 1))
      * (∑ c ∈ Finset.range (j + 1),
          (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
    + 2 * ((Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2)
      * ((Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
          * (Work.Spaces.w z) ^ 2)


end Work.FTS.CoercivityFix.Transfer.E1Parts
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.H1IP_cs_of_mem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

/-! ## The triangle inequality for four terms -/

private theorem abs_add_four (a b c d : ℝ) :
    |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 : |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
  have h2 : |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
  have h3 : |a + b| ≤ |a| + |b| := abs_add_le _ _
  linarith

/-! ## The junk-free Cauchy–Schwarz bound for a pairing of two blocks -/

/-- **Cauchy–Schwarz for a block pairing.**  If the two functions `X`, `Y` are dominated
(a.e. in `θ`, on each radial slice) by the square roots of the `ℋ¹`-integrands of `f`
resp. `g`, then the iterated integral of the product `X·Y` is bounded by the product of
the two `ℋ¹`-norms.  No measurability or integrability of `X`, `Y` themselves is assumed:
all estimates are performed in `ℝ≥0∞`, and the dominating integrands
`HkIntegrand α 1 f`, `HkIntegrand α 1 g` are honest by `HkMem α 1`. -/
private theorem abs_pairing_le (α : ℝ) {X Y f g : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α 1 f) (hg : Work.Spaces.HkMem α 1 g)
    (hX : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (X z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 1 f z θ)
    (hY : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (Y z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 1 g z θ) :
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, X z θ * Y z θ|
      ≤ Real.sqrt (Work.Spaces.HkSq α 1 f) * Real.sqrt (Work.Spaces.HkSq α 1 g) := by
  have hSfnn : ∀ z θ, 0 ≤ Work.Spaces.HkIntegrand α 1 f z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α 1 f z θ
  have hSgnn : ∀ z θ, 0 ≤ Work.Spaces.HkIntegrand α 1 g z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α 1 g z θ
  -- Pointwise (a.e. in `θ`) domination of the pairing integrand by the two square roots.
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      ‖X z θ * Y z θ‖ₑ
        ≤ ENNReal.ofReal (Real.sqrt (Work.Spaces.HkIntegrand α 1 f z θ))
          * ENNReal.ofReal (Real.sqrt (Work.Spaces.HkIntegrand α 1 g z θ)) := by
    intro z hz
    filter_upwards [hX z hz, hY z hz] with θ hx hy
    have hx' : |X z θ| ≤ Real.sqrt (Work.Spaces.HkIntegrand α 1 f z θ) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hx
    have hy' : |Y z θ| ≤ Real.sqrt (Work.Spaces.HkIntegrand α 1 g z θ) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hy
    rw [enorm_mul, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
    refine mul_le_mul' ?_ ?_
    · exact (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)).mpr hx'
    · exact (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg _)).mpr hy'
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  -- Cauchy–Schwarz on each angular slice.
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Real.sqrt (Work.Spaces.HkIntegrand α 1 f z θ))
            * ENNReal.ofReal (Real.sqrt (Work.Spaces.HkIntegrand α 1 g z θ)))
        ≤ ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ))
          * ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 g z θ)) := by
    intro z hz
    have hmeasf : AEMeasurable
        (fun θ => ENNReal.ofReal (Real.sqrt (Work.Spaces.HkIntegrand α 1 f z θ)))
        (volume.restrict Work.Spaces.Iθ) :=
      ((hf.1 z hz).aestronglyMeasurable.aemeasurable.sqrt).ennreal_ofReal
    have hmeasg : AEMeasurable
        (fun θ => ENNReal.ofReal (Real.sqrt (Work.Spaces.HkIntegrand α 1 g z θ)))
        (volume.restrict Work.Spaces.Iθ) :=
      ((hg.1 z hz).aestronglyMeasurable.aemeasurable.sqrt).ennreal_ofReal
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict Work.Spaces.Iθ) hpq hmeasf hmeasg
    have hf2 : (∫⁻ θ in Work.Spaces.Iθ,
          (ENNReal.ofReal (Real.sqrt (Work.Spaces.HkIntegrand α 1 f z θ))) ^ (2 : ℝ))
        = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ) := by
      have hcongr : (fun θ =>
            (ENNReal.ofReal (Real.sqrt (Work.Spaces.HkIntegrand α 1 f z θ))) ^ (2 : ℝ))
          = fun θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 1 f z θ) := by
        funext θ
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ (2 : ℝ)),
          Real.rpow_two, Real.sq_sqrt (hSfnn z θ)]
      rw [hcongr,
        ← ofReal_integral_eq_lintegral_ofReal (hf.1 z hz) (ae_of_all _ (fun θ => hSfnn z θ))]
    have hg2 : (∫⁻ θ in Work.Spaces.Iθ,
          (ENNReal.ofReal (Real.sqrt (Work.Spaces.HkIntegrand α 1 g z θ))) ^ (2 : ℝ))
        = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 g z θ) := by
      have hcongr : (fun θ =>
            (ENNReal.ofReal (Real.sqrt (Work.Spaces.HkIntegrand α 1 g z θ))) ^ (2 : ℝ))
          = fun θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 1 g z θ) := by
        funext θ
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ (2 : ℝ)),
          Real.rpow_two, Real.sq_sqrt (hSgnn z θ)]
      rw [hcongr,
        ← ofReal_integral_eq_lintegral_ofReal (hg.1 z hz) (ae_of_all _ (fun θ => hSgnn z θ))]
    have hf3 : (ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ)) ^ (1 / 2 : ℝ)
        = ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (integral_nonneg (hSfnn z)) (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ)),
        ← Real.sqrt_eq_rpow]
    have hg3 : (ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 g z θ)) ^ (1 / 2 : ℝ)
        = ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 g z θ)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (integral_nonneg (hSgnn z)) (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ)),
        ← Real.sqrt_eq_rpow]
    calc (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Real.sqrt (Work.Spaces.HkIntegrand α 1 f z θ))
            * ENNReal.ofReal (Real.sqrt (Work.Spaces.HkIntegrand α 1 g z θ)))
        ≤ (∫⁻ θ in Work.Spaces.Iθ,
              (ENNReal.ofReal (Real.sqrt (Work.Spaces.HkIntegrand α 1 f z θ))) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
            * (∫⁻ θ in Work.Spaces.Iθ,
              (ENNReal.ofReal (Real.sqrt (Work.Spaces.HkIntegrand α 1 g z θ))) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hH
      _ = ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ))
            * ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 g z θ)) := by
          rw [hf2, hg2, hf3, hg3]
  have hfz_int : Integrable (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ)
      (volume.restrict Work.Spaces.Iz) := hf.2
  have hgz_int : Integrable (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 g z θ)
      (volume.restrict Work.Spaces.Iz) := hg.2
  have hfz_nn : ∀ z, 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ :=
    fun z => integral_nonneg (fun θ => hSfnn z θ)
  have hgz_nn : ∀ z, 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 g z θ :=
    fun z => integral_nonneg (fun θ => hSgnn z θ)
  have hzmeas1 : AEMeasurable
      (fun z => ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ)))
      (volume.restrict Work.Spaces.Iz) :=
    (hfz_int.aestronglyMeasurable.aemeasurable.sqrt).ennreal_ofReal
  have hzmeas2 : AEMeasurable
      (fun z => ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 g z θ)))
      (volume.restrict Work.Spaces.Iz) :=
    (hgz_int.aestronglyMeasurable.aemeasurable.sqrt).ennreal_ofReal
  -- Cauchy–Schwarz in `z`.
  have hzH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict Work.Spaces.Iz) hpq hzmeas1 hzmeas2
  have hz2 : (∫⁻ z in Work.Spaces.Iz,
        (ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ))) ^ (2 : ℝ))
      = ENNReal.ofReal (Work.Spaces.HkSq α 1 f) := by
    have hcongr : (fun z =>
          (ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ))) ^ (2 : ℝ))
        = fun z => ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ) := by
      funext z
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ (2 : ℝ)),
        Real.rpow_two, Real.sq_sqrt (hfz_nn z)]
    rw [hcongr, ← ofReal_integral_eq_lintegral_ofReal hfz_int (ae_of_all _ hfz_nn)]
    rfl
  have hz2g : (∫⁻ z in Work.Spaces.Iz,
        (ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 g z θ))) ^ (2 : ℝ))
      = ENNReal.ofReal (Work.Spaces.HkSq α 1 g) := by
    have hcongr : (fun z =>
          (ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 g z θ))) ^ (2 : ℝ))
        = fun z => ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 g z θ) := by
      funext z
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ (2 : ℝ)),
        Real.rpow_two, Real.sq_sqrt (hgz_nn z)]
    rw [hcongr, ← ofReal_integral_eq_lintegral_ofReal hgz_int (ae_of_all _ hgz_nn)]
    rfl
  have hz3 : (ENNReal.ofReal (Work.Spaces.HkSq α 1 f)) ^ (1 / 2 : ℝ)
      = ENNReal.ofReal (Real.sqrt (Work.Spaces.HkSq α 1 f)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Work.Spaces.HkSq_nonneg α 1 f)
        (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ)),
      ← Real.sqrt_eq_rpow]
  have hz3g : (ENNReal.ofReal (Work.Spaces.HkSq α 1 g)) ^ (1 / 2 : ℝ)
      = ENNReal.ofReal (Real.sqrt (Work.Spaces.HkSq α 1 g)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Work.Spaces.HkSq_nonneg α 1 g)
        (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ)),
      ← Real.sqrt_eq_rpow]
  have hzH' : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ))
          * ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 g z θ)))
      ≤ ENNReal.ofReal (Real.sqrt (Work.Spaces.HkSq α 1 f))
          * ENNReal.ofReal (Real.sqrt (Work.Spaces.HkSq α 1 g)) := by
    calc (∫⁻ z in Work.Spaces.Iz,
          ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ))
            * ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 g z θ)))
        ≤ (∫⁻ z in Work.Spaces.Iz,
              (ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α 1 f z θ))) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
            * (∫⁻ z in Work.Spaces.Iz,
              (ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α 1 g z θ))) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hzH
      _ = ENNReal.ofReal (Real.sqrt (Work.Spaces.HkSq α 1 f))
            * ENNReal.ofReal (Real.sqrt (Work.Spaces.HkSq α 1 g)) := by
          rw [hz2, hz2g, hz3, hz3g]
  have hchain : ‖∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, X z θ * Y z θ)‖ₑ
      ≤ ENNReal.ofReal (Real.sqrt (Work.Spaces.HkSq α 1 f))
          * ENNReal.ofReal (Real.sqrt (Work.Spaces.HkSq α 1 g)) := by
    calc ‖∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, X z θ * Y z θ)‖ₑ
        ≤ ∫⁻ z in Work.Spaces.Iz, ‖∫ θ in Work.Spaces.Iθ, X z θ * Y z θ‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ‖X z θ * Y z θ‖ₑ :=
          lintegral_mono fun z => enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Real.sqrt (Work.Spaces.HkIntegrand α 1 f z θ))
              * ENNReal.ofReal (Real.sqrt (Work.Spaces.HkIntegrand α 1 g z θ)) := by
          refine lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_)
          exact lintegral_mono_ae (hpt z hz)
      _ ≤ ∫⁻ z in Work.Spaces.Iz,
            ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 f z θ))
              * ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 1 g z θ)) := by
          refine lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_)
          exact hslice z hz
      _ ≤ ENNReal.ofReal (Real.sqrt (Work.Spaces.HkSq α 1 f))
            * ENNReal.ofReal (Real.sqrt (Work.Spaces.HkSq α 1 g)) := hzH'
  rw [Real.enorm_eq_ofReal_abs,
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg (Work.Spaces.HkSq α 1 f))] at hchain
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp hchain

/-! ## The four pairings of `H1IP` -/

/-- **Cauchy–Schwarz for `H1IP` at level `1`, with the constant `10 ^ 22` pinned.**  The
statement is the membership-based bound of the paper's `ℋ¹` pairing; the constant is *independent
of `α` (and even of `0 < α` beyond the hypotheses), which is what makes the transfer
induction's constants uniform in `α` (`Transfer/CSQ_one_unif.lean`). -/
theorem H1IP_cs_of_mem (α : ℝ) (hα : 0 < α) (f g : ℝ → ℝ → ℝ)
    (hf : Work.Spaces.HkMem α 1 f) (hg : Work.Spaces.HkMem α 1 g) :
    |Work.Coercivity.H1IP α f g|
      ≤ (10 : ℝ) ^ 22 * Work.Spaces.HkNorm α 1 f * Work.Spaces.HkNorm α 1 g := by
  set Y : ℝ := Work.Spaces.HkNorm α 1 f * Work.Spaces.HkNorm α 1 g with hY
  have hYnn : 0 ≤ Y := by
    rw [hY]
    exact mul_nonneg (Work.Spaces.HkNorm_nonneg α 1 f) (Work.Spaces.HkNorm_nonneg α 1 g)
  -- ## Term 1: the `D_z`-pairing with weight `w²·sin(2θ)^{-η}`
  have hT1 :
      |Work.Coercivity.wip Work.Coercivity.lamEta (Work.Spaces.Dz f) (Work.Spaces.Dz g)| ≤ Y := by
    rw [hY]
    have hwip : Work.Coercivity.wip Work.Coercivity.lamEta (Work.Spaces.Dz f)
        (Work.Spaces.Dz g)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Coercivity.XetaDz f z θ * Work.Coercivity.XetaDz g z θ := by
      simp only [Work.Coercivity.wip]
      refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
      refine setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      exact (Work.Coercivity.XetaDz_mul_eq f g z θ hθ).symm
    rw [hwip]
    exact abs_pairing_le α hf hg
      (fun z _ => Eventually.of_forall
        (fun θ => Work.FTS.CoercivityFix.Assembly.sq_XetaDz_le_HkIntegrand α f z θ))
      (fun z _ => Eventually.of_forall
        (fun θ => Work.FTS.CoercivityFix.Assembly.sq_XetaDz_le_HkIntegrand α g z θ))
  -- ## Term 2: the `L²`-pairing with weight `w²·sin(2θ)^{-η}`
  have hT2 : |Work.Coercivity.wip Work.Coercivity.lamEta f g| ≤ Y := by
    rw [hY]
    have hwip : Work.Coercivity.wip Work.Coercivity.lamEta f g
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Coercivity.Xeta f z θ * Work.Coercivity.Xeta g z θ := by
      simp only [Work.Coercivity.wip]
      refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
      refine setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      exact (Work.Coercivity.Xeta_mul_eq f g z θ hθ).symm
    rw [hwip]
    exact abs_pairing_le α hf hg
      (fun z _ => Eventually.of_forall
        (fun θ => Work.FTS.CoercivityFix.Assembly.sq_Xeta_le_HkIntegrand α f z θ))
      (fun z _ => Eventually.of_forall
        (fun θ => Work.FTS.CoercivityFix.Assembly.sq_Xeta_le_HkIntegrand α g z θ))
  -- ## Term 3: the plain `w²`-pairing
  have hT3 : |Work.Coercivity.wip Work.Coercivity.lamW f g| ≤ Y := by
    rw [hY]
    have hwip : Work.Coercivity.wip Work.Coercivity.lamW f g
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Coercivity.Xw f z θ * Work.Coercivity.Xw g z θ := by
      simp only [Work.Coercivity.wip]
      refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
      refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
      simp only [Work.Coercivity.Xw, Work.Coercivity.lamW]
      ring
    rw [hwip]
    exact abs_pairing_le α hf hg
      (fun z _ => Work.FTS.CoercivityFix.Assembly.sq_Xw_le_HkIntegrand_ae α f z)
      (fun z _ => Work.FTS.CoercivityFix.Assembly.sq_Xw_le_HkIntegrand_ae α g z)
  -- ## Term 4: the `D_θ`-pairing with weight `w²·sin(2θ)^{-γ}`
  have hT4 :
      |Work.Coercivity.wip (Work.Coercivity.lamGam α) (Work.Spaces.Dth f)
        (Work.Spaces.Dth g)| ≤ Y := by
    rw [hY]
    have hwip : Work.Coercivity.wip (Work.Coercivity.lamGam α) (Work.Spaces.Dth f)
        (Work.Spaces.Dth g)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Coercivity.XgamDth α f z θ * Work.Coercivity.XgamDth α g z θ := by
      simp only [Work.Coercivity.wip]
      refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
      refine setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      exact (Work.Coercivity.XgamDth_mul_eq α f g z θ hθ).symm
    rw [hwip]
    exact abs_pairing_le α hf hg
      (fun z _ => Eventually.of_forall
        (fun θ => Work.FTS.CoercivityFix.Assembly.sq_XgamDth_le_HkIntegrand α f z θ))
      (fun z _ => Eventually.of_forall
        (fun θ => Work.FTS.CoercivityFix.Assembly.sq_XgamDth_le_HkIntegrand α g z θ))
  -- ## The triangle inequality for the four terms of `H1IP`
  have h10 : (0 : ℝ) ≤ 10 := by norm_num
  have habs : |Work.Coercivity.H1IP α f g|
      ≤ 10 * |Work.Coercivity.wip Work.Coercivity.lamEta (Work.Spaces.Dz f) (Work.Spaces.Dz g)|
        + 10 ^ 10 * |Work.Coercivity.wip Work.Coercivity.lamEta f g|
        + 10 ^ 17 * |Work.Coercivity.wip Work.Coercivity.lamW f g|
        + 10 ^ 21 * |Work.Coercivity.wip (Work.Coercivity.lamGam α) (Work.Spaces.Dth f)
            (Work.Spaces.Dth g)| := by
    have h := abs_add_four
      ((10 : ℝ) * Work.Coercivity.wip Work.Coercivity.lamEta (Work.Spaces.Dz f)
        (Work.Spaces.Dz g))
      ((10 : ℝ) ^ 10 * Work.Coercivity.wip Work.Coercivity.lamEta f g)
      ((10 : ℝ) ^ 17 * Work.Coercivity.wip Work.Coercivity.lamW f g)
      ((10 : ℝ) ^ 21 * Work.Coercivity.wip (Work.Coercivity.lamGam α) (Work.Spaces.Dth f)
        (Work.Spaces.Dth g))
    simp only [Work.Coercivity.H1IP]
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg h10,
      abs_of_nonneg (pow_nonneg h10 10), abs_of_nonneg (pow_nonneg h10 17),
      abs_of_nonneg (pow_nonneg h10 21)] at h
    exact h
  have hT1' : 10 * |Work.Coercivity.wip Work.Coercivity.lamEta (Work.Spaces.Dz f)
      (Work.Spaces.Dz g)| ≤ 10 * Y := mul_le_mul_of_nonneg_left hT1 h10
  have hT2' : 10 ^ 10 * |Work.Coercivity.wip Work.Coercivity.lamEta f g| ≤ 10 ^ 10 * Y :=
    mul_le_mul_of_nonneg_left hT2 (pow_nonneg h10 10)
  have hT3' : 10 ^ 17 * |Work.Coercivity.wip Work.Coercivity.lamW f g| ≤ 10 ^ 17 * Y :=
    mul_le_mul_of_nonneg_left hT3 (pow_nonneg h10 17)
  have hT4' : 10 ^ 21 * |Work.Coercivity.wip (Work.Coercivity.lamGam α) (Work.Spaces.Dth f)
      (Work.Spaces.Dth g)| ≤ 10 ^ 21 * Y :=
    mul_le_mul_of_nonneg_left hT4 (pow_nonneg h10 21)
  have hsum : |Work.Coercivity.H1IP α f g|
      ≤ 10 * Y + 10 ^ 10 * Y + 10 ^ 17 * Y + 10 ^ 21 * Y :=
    le_trans habs (add_le_add (add_le_add (add_le_add hT1' hT2') hT3') hT4')
  calc |Work.Coercivity.H1IP α f g|
      ≤ 10 * Y + 10 ^ 10 * Y + 10 ^ 17 * Y + 10 ^ 21 * Y := hsum
    _ = ((10 : ℝ) + 10 ^ 10 + 10 ^ 17 + 10 ^ 21) * Y := by ring
    _ ≤ (10 : ℝ) ^ 22 * Y := mul_le_mul_of_nonneg_right (by norm_num) hYnn
    _ = (10 : ℝ) ^ 22 * Work.Spaces.HkNorm α 1 f * Work.Spaces.HkNorm α 1 g := by
        rw [hY]
        ring

end

end Work.FTS.CoercivityFix.Transfer
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.ZmollTTB1 =====
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

/-! ## Differentiation under the logarithmic mollification -/

/-- **Differentiation under the logarithmic mollification.** -/
theorem conv_t_step (J J' : ℝ → ℝ → ℝ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {Cj : ℝ → ℝ} (hCj : LocallyIntegrable Cj volume) {σ : ℝ}
    (hJmem : ∀ x : ℝ, AEStronglyMeasurable (fun t : ℝ => J x t) volume)
    (hJ'mem : ∀ x : ℝ, AEStronglyMeasurable (fun t : ℝ => J' x t) volume)
    (hJint : ∀ x : ℝ, ∀ p q : ℝ, IntegrableOn (fun t : ℝ => J x t) (Set.Icc p q))
    (hJdiff : ∀ t x : ℝ, HasDerivAt (fun x' : ℝ => J x' t) (J' x t) x)
    (hJbound : ∀ x t : ℝ, ‖J' x t‖ ≤ Cj t)
    (θ : ℝ) :
    HasDerivAt (fun x : ℝ => ∫ t : ℝ, sKer δ (σ - t) * J x t)
      (∫ t : ℝ, sKer δ (σ - t) * J' θ t) θ := by
  have hKδ0 : (0 : ℝ) ≤ (δ * sMass)⁻¹ := by
    have := sMass_pos; positivity
  have hKδ : ∀ x : ℝ, |sKer δ x| ≤ (δ * sMass)⁻¹ := fun x => by
    rw [abs_of_nonneg (sKer_nonneg hδ0 x)]
    exact Work.FTS.EllSol.K5cAux.sKer_le_inv hδ0 x
  have hkercont : Continuous (fun t : ℝ => sKer δ (σ - t)) :=
    (Work.FTS.EllSol.EllPkgAux.contDiff_sKer δ (n := 0)).continuous.comp
      (continuous_const.sub continuous_id)
  have hvan : ∀ x : ℝ, δ < |x| → sKer δ x = 0 :=
    fun x hx => sKer_eq_zero_of_le_abs hδ0 (le_of_lt hx)
  set a : ℝ := σ - 1 with ha
  set b : ℝ := σ + 1 with hb
  have hab : a ≤ b := by rw [ha, hb]; linarith
  have haσ : a ≤ σ - δ := by rw [ha]; linarith
  have hbσ : σ + δ ≤ b := by rw [hb]; linarith
  have hF_meas : ∀ᶠ x in 𝓝 θ, AEStronglyMeasurable
      (fun t : ℝ => sKer δ (σ - t) * J x t) (volume.restrict (Set.uIoc a b)) :=
    Filter.Eventually.of_forall fun x => (hkercont.aestronglyMeasurable.mul (hJmem x)).restrict
  have hF'_meas : AEStronglyMeasurable (fun t : ℝ => sKer δ (σ - t) * J' θ t)
      (volume.restrict (Set.uIoc a b)) :=
    (hkercont.aestronglyMeasurable.mul (hJ'mem θ)).restrict
  have hF_int : IntervalIntegrable (fun t : ℝ => sKer δ (σ - t) * J θ t) volume a b := by
    have h1 : IntegrableOn (fun t : ℝ => J θ t * sKer δ (σ - t)) (Set.Icc a b) :=
      (hJint θ a b).mul_continuousOn hkercont.continuousOn isCompact_Icc
    have h2 : IntegrableOn (fun t : ℝ => sKer δ (σ - t) * J θ t) (Set.Icc a b) :=
      h1.congr_fun (fun t _ => mul_comm _ _) measurableSet_Icc
    exact intervalIntegrable_iff.mpr (integrableOn_uIoc_of_Icc hab h2)
  have hbound_ae : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b → ∀ x ∈ (Set.univ : Set ℝ),
      ‖sKer δ (σ - t) * J' x t‖ ≤ (δ * sMass)⁻¹ * Cj t := by
    refine Filter.Eventually.of_forall fun t _ x _ => ?_
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |sKer δ (σ - t)| ≤ (δ * sMass)⁻¹ := hKδ _
    have h2 : |J' x t| ≤ Cj t := by
      simpa only [Real.norm_eq_abs] using hJbound x t
    exact mul_le_mul h1 h2 (abs_nonneg _) hKδ0
  have hCj_int : IntervalIntegrable (fun t : ℝ => (δ * sMass)⁻¹ * Cj t) volume a b := by
    have h1 : IntegrableOn (fun t : ℝ => Cj t) (Set.Icc a b) :=
      hCj.integrableOn_isCompact isCompact_Icc
    exact intervalIntegrable_iff.mpr (integrableOn_uIoc_of_Icc hab (h1.const_mul _))
  have hdiff : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b → ∀ x ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun y : ℝ => sKer δ (σ - t) * J y t) (sKer δ (σ - t) * J' x t) x :=
    Filter.Eventually.of_forall fun t _ x _ => (hJdiff t x).const_mul _
  obtain ⟨-, hmain⟩ := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := a) (b := b) (bound := fun t : ℝ => (δ * sMass)⁻¹ * Cj t)
    (F := fun x t : ℝ => sKer δ (σ - t) * J x t)
    (F' := fun x t : ℝ => sKer δ (σ - t) * J' x t)
    (x₀ := θ) (s := Set.univ) Filter.univ_mem hF_meas hF_int hF'_meas hbound_ae hCj_int hdiff
  have hleft : (fun x : ℝ => ∫ t in a..b, sKer δ (σ - t) * J x t)
      = fun x : ℝ => ∫ t : ℝ, sKer δ (σ - t) * J x t :=
    funext fun x => (full_eq_interval_zmoll (sKer δ) (fun t => J x t) (le_of_lt hδ0) hvan haσ hbσ).symm
  have hright : (∫ t in a..b, sKer δ (σ - t) * J' θ t)
      = ∫ t : ℝ, sKer δ (σ - t) * J' θ t :=
    (full_eq_interval_zmoll (sKer δ) (fun t => J' θ t) (le_of_lt hδ0) hvan haσ hbσ).symm
  rw [hleft, hright] at hmain
  exact hmain

/-! ## The slice data supplied by `TraceClass` -/

structure SliceData (G : ℝ → ℝ → ℝ) : Prop where
  sm : Work.FTS.EllipticEst.SmoothOpen G
  val0 : ∀ w : ℝ, G w 0 = 0
  valpi : ∀ w : ℝ, G w (Real.pi / 2) = 0
  tr0 : ∀ w : ℝ, 0 < w → Tendsto (fun s : ℝ => G w s) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0)
  trpi : ∀ w : ℝ, 0 < w →
    Tendsto (fun s : ℝ => G w s) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (𝓝 0)
  cont : ∀ w : ℝ, 0 < w → ContinuousOn (fun s : ℝ => G w s) Iθ
  deriv_bdd : ∀ w : ℝ, 0 < w → ∃ M : ℝ, 0 ≤ M ∧
    ∀ s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun s' : ℝ => G w s') s| ≤ M
  deriv2_int : ∀ w : ℝ, 0 < w →
    IntegrableOn (fun s : ℝ => deriv (deriv (fun s' : ℝ => G w s')) s) Iθ
  deriv2_weighted : ∀ w : ℝ, 0 < w →
    IntegrableOn (fun s : ℝ => (deriv (deriv (fun s' : ℝ => G w s')) s) ^ 2
      * Work.FTS.EllipticEst.thEta s) Iθ

theorem slice_hasDerivAt (G : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen G)
    {w s : ℝ} (hw : 0 < w) (hs : s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (fun s' : ℝ => G w s') (deriv (fun s' : ℝ => G w s') s) s := by
  have h : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => G w θ)
      (Set.Ioo 0 (Real.pi / 2)) := hsm.curry_θ hw
  exact ((h.differentiableOn (by simp [Work.Stability.smoothOrder])).differentiableAt
    (isOpen_Ioo.mem_nhds hs)).hasDerivAt

theorem slice_hasDerivAt2 (G : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen G)
    {w s : ℝ} (hw : 0 < w) (hs : s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (fun s' : ℝ => deriv (fun s'' : ℝ => G w s'') s')
      (deriv (deriv (fun s'' : ℝ => G w s'')) s) s := by
  have h : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Work.Spaces.pth G w θ)
      (Set.Ioo 0 (Real.pi / 2)) := hsm.pth.curry_θ hw
  have h2 := ((h.differentiableOn (by simp [Work.Stability.smoothOrder])).differentiableAt
    (isOpen_Ioo.mem_nhds hs)).hasDerivAt
  simpa only [Work.Spaces.pth] using h2

theorem aesm_slice_deriv (G : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen G)
    {w : ℝ} (hw : 0 < w) :
    AEStronglyMeasurable (fun s : ℝ => deriv (fun s' : ℝ => G w s') s)
      (volume.restrict Iθ) := by
  have h : ContinuousOn (fun s : ℝ => deriv (fun s' : ℝ => G w s') s)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    simpa only [Work.Spaces.pth] using (hsm.pth.curry_θ hw).continuousOn
  have h2 := h.aestronglyMeasurable (μ := volume) measurableSet_Ioo
  rwa [← Work.FTS.EllSol.EllPkgAux.restrict_Iθ_eq_restrict_Ioo] at h2

/-! ## The three folded integrals -/

def JA (G : ℝ → ℝ → ℝ) (ε : ℝ) (x t : ℝ) : ℝ := ∫ s in Iθ, km ε x s * G (Real.exp t) s

def JB (G : ℝ → ℝ → ℝ) (ε : ℝ) (x t : ℝ) : ℝ := ∫ s in Iθ, kmθ ε x s * G (Real.exp t) s

def JC (G : ℝ → ℝ → ℝ) (ε : ℝ) (x t : ℝ) : ℝ := ∫ s in Iθ, kmθθ ε x s * G (Real.exp t) s

theorem aesm_JA (G : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen G) (ε x : ℝ) :
    AEStronglyMeasurable (fun t : ℝ => JA G ε x t) volume := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => km ε x p.2) (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((continuous_km ε x).comp (continuous_snd : Continuous (fun p : ℝ × ℝ => p.2))).continuousOn
  have hΦ : Continuous (fun p : ℝ × ℝ => (Real.exp p.1, p.2)) :=
    (Real.continuous_exp.comp continuous_fst).prodMk continuous_snd
  have h2 : ContinuousOn (fun p : ℝ × ℝ => G (Real.exp p.1) p.2)
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hsm.continuousOn.comp hΦ.continuousOn (fun p hp => ⟨Real.exp_pos p.1, hp.2.1, hp.2.2⟩)
  exact aesm_param_Iθ (fun p : ℝ × ℝ => km ε x p.2 * G (Real.exp p.1) p.2) (h1.mul h2)

theorem aesm_JB (G : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen G) (ε x : ℝ) :
    AEStronglyMeasurable (fun t : ℝ => JB G ε x t) volume := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => kmθ ε x p.2) (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((continuous_kmθ ε x).comp (continuous_snd : Continuous (fun p : ℝ × ℝ => p.2))).continuousOn
  have hΦ : Continuous (fun p : ℝ × ℝ => (Real.exp p.1, p.2)) :=
    (Real.continuous_exp.comp continuous_fst).prodMk continuous_snd
  have h2 : ContinuousOn (fun p : ℝ × ℝ => G (Real.exp p.1) p.2)
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hsm.continuousOn.comp hΦ.continuousOn (fun p hp => ⟨Real.exp_pos p.1, hp.2.1, hp.2.2⟩)
  exact aesm_param_Iθ (fun p : ℝ × ℝ => kmθ ε x p.2 * G (Real.exp p.1) p.2) (h1.mul h2)

theorem aesm_JC (G : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen G) (ε x : ℝ) :
    AEStronglyMeasurable (fun t : ℝ => JC G ε x t) volume := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => kmθθ ε x p.2) (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((continuous_kmθθ ε x).comp (continuous_snd : Continuous (fun p : ℝ × ℝ => p.2))).continuousOn
  have hΦ : Continuous (fun p : ℝ × ℝ => (Real.exp p.1, p.2)) :=
    (Real.continuous_exp.comp continuous_fst).prodMk continuous_snd
  have h2 : ContinuousOn (fun p : ℝ × ℝ => G (Real.exp p.1) p.2)
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hsm.continuousOn.comp hΦ.continuousOn (fun p hp => ⟨Real.exp_pos p.1, hp.2.1, hp.2.2⟩)
  exact aesm_param_Iθ (fun p : ℝ × ℝ => kmθθ ε x p.2 * G (Real.exp p.1) p.2) (h1.mul h2)

/-! ## Bounds for the folded integrals -/

/-- The slice functional `t ↦ ∫_{Iθ} |G (eᵗ) s| ds`. -/
def SNg (G : ℝ → ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in Iθ, |G (Real.exp t) s|

/-- A kernel bounded by `C` gives a folded integral bounded by `C · SNg`. -/
theorem abs_fold_le (G : ℝ → ℝ → ℝ) (hsl : SliceData G) {K : ℝ → ℝ → ℝ} {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ x s : ℝ, |K x s| ≤ C) (x t : ℝ) :
    |∫ s in Iθ, K x s * G (Real.exp t) s| ≤ C * SNg G t := by
  have h1 : |∫ s in Iθ, K x s * G (Real.exp t) s|
      ≤ ∫ s in Iθ, |K x s * G (Real.exp t) s| :=
    MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict Iθ)
      (fun s : ℝ => K x s * G (Real.exp t) s)
  have hint : IntegrableOn (fun s : ℝ => C * |G (Real.exp t) s|) Iθ :=
    ((hsl.cont (Real.exp t) (Real.exp_pos t)).abs.integrableOn_compact isCompact_Icc).const_mul C
  have h2 : (∫ s in Iθ, |K x s * G (Real.exp t) s|)
      ≤ ∫ s in Iθ, C * |G (Real.exp t) s| := by
    refine integral_mono_of_nonneg (μ := volume.restrict Iθ)
      (Filter.Eventually.of_forall fun s => abs_nonneg _) hint ?_
    exact Filter.Eventually.of_forall fun s => by
      show |K x s * G (Real.exp t) s| ≤ C * |G (Real.exp t) s|
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hC x s) (abs_nonneg _)
  calc |∫ s in Iθ, K x s * G (Real.exp t) s|
      ≤ ∫ s in Iθ, |K x s * G (Real.exp t) s| := h1
    _ ≤ ∫ s in Iθ, C * |G (Real.exp t) s| := h2
    _ = C * SNg G t := by rw [SNg]; exact MeasureTheory.integral_const_mul _ _

/-- Integrability of the slice functional `∫_{Iθ} KJ ε θ s |∂_θ²G (eᵗ) s| ds`. -/
theorem integrableOn_KJ_pth2 (G : ℝ → ℝ → ℝ) (hsl : SliceData G) {ε : ℝ} (hε0 : 0 < ε)
    (θ t : ℝ) :
    IntegrableOn (fun s : ℝ => KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|) Iθ := by
  have hC0 : (0 : ℝ) ≤ 3 * (ε * sMass)⁻¹ := by have := sMass_pos; positivity
  have hbnd : IntegrableOn
      (fun s : ℝ => (3 * (ε * sMass)⁻¹) * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|) Iθ :=
    (hsl.deriv2_int (Real.exp t) (Real.exp_pos t)).abs.const_mul _
  have hQ''aesm : AEStronglyMeasurable
      (fun s : ℝ => Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) (volume.restrict Iθ) :=
    (hsl.deriv2_int (Real.exp t) (Real.exp_pos t)).aestronglyMeasurable
  have hQ''abs : AEStronglyMeasurable
      (fun s : ℝ => |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|) (volume.restrict Iθ) := by
    simpa only [Real.norm_eq_abs] using hQ''aesm.norm
  have hKaesm : AEStronglyMeasurable (fun s : ℝ => KJ ε θ s) (volume.restrict Iθ) :=
    ((continuous_KJ ε).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  refine Integrable.mono' hbnd (AEStronglyMeasurable.mul hKaesm hQ''abs) ?_
  · exact Filter.Eventually.of_forall fun s => by
      show ‖KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|‖
        ≤ (3 * (ε * sMass)⁻¹) * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|
      rw [Real.norm_eq_abs, abs_mul, abs_abs,
        abs_of_nonneg (Work.FTS.EllSol.EllPkgAux.KJ_nonneg hε0 θ s)]
      exact mul_le_mul_of_nonneg_right
        (Work.FTS.EllSol.EllPkgAux.KJ_le hε0 θ s) (abs_nonneg _)

/-- The pointwise domination of the inner `s`-integral by the `KJ`-functional. -/
theorem abs_inner_le_KJ (G : ℝ → ℝ → ℝ) (hsl : SliceData G) {ε : ℝ} (hε0 : 0 < ε) (θ t : ℝ) :
    |∫ s in Iθ, km ε θ s * Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|
      ≤ ∫ s in Iθ, KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s| := by
  have h1 : |∫ s in Iθ, km ε θ s * Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|
      ≤ ∫ s in Iθ, |km ε θ s * Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s| :=
    MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict Iθ)
      (fun s : ℝ => km ε θ s * Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s)
  have h2 : (∫ s in Iθ, |km ε θ s * Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|)
      ≤ ∫ s in Iθ, KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s| := by
    refine integral_mono_of_nonneg (μ := volume.restrict Iθ)
      (Filter.Eventually.of_forall fun s => abs_nonneg _)
      (integrableOn_KJ_pth2 G hsl hε0 θ t) ?_
    exact Filter.Eventually.of_forall fun s => by
      show |km ε θ s * Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|
        ≤ KJ ε θ s * |Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s|
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_km_le_KJ hε0 θ s) (abs_nonneg _)
  linarith [h1, h2]

end Work.FTS.EllSol.EllPkgAux.MollDom
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.schur_sq_window_le_unif =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set

namespace Work.FTS.EllSol.EllPkgAux.MollDom

/-- **The logarithmic Schur bound on the window, uniformly in `z`.**

There is a *single* constant `A > 0` — independent of `z`, namely `2 δ M² + 1` where `M` is a
global bound for the continuous, compactly supported kernel `sKerd δ = deriv (sKer δ)` — such
that for every `z > 0` and every continuous `y`

  `(∫ t, sKerd δ (log z - t) · y t)² ≤ A ∫ t, 1_{|log z - t| ≤ δ} y t²`.

The kernel vanishes off the window `S = [log z - δ, log z + δ]`, where it is bounded by `M`, so
`∫_S (sKerd δ (log z - ·))² ≤ M² |S| = 2 δ M²`; Cauchy–Schwarz on the window
(`zSchur_sq_le_window`) gives the claim with a constant free of `z`. This is the uniform
version of `schur_sq_window_le`, whose constant `1 + ∫_S (sKerd δ (log z - ·))²` is a priori
`z`-dependent (it is in fact independent of `z` by translation invariance with respect to the
logarithmic variable, but it is the kernel bound that makes this explicit and uniform). -/
theorem schur_sq_window_le_unif (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ z : ℝ, 0 < z → ∀ y : ℝ → ℝ, Continuous y →
      (∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) * y t) ^ 2
        ≤ A * (∫ t : ℝ, if |Real.log z - t| ≤ δ then (y t) ^ 2 else 0) := by
  -- A global bound on the kernel `sKerd δ`, together with its support.
  obtain ⟨M, hMnn, hk, hvan⟩ := exists_sKerd_bound hδ
  refine ⟨2 * δ * M ^ 2 + 1, by nlinarith [sq_nonneg M], ?_⟩
  intro z hz y hy
  -- The window on which the kernel lives.
  set S : Set ℝ := Set.Icc (Real.log z - δ) (Real.log z + δ) with hSdef
  have hSmeas : MeasurableSet S := by rw [hSdef]; exact measurableSet_Icc
  have hScomp : IsCompact S := by rw [hSdef]; exact isCompact_Icc
  have hmem : ∀ t : ℝ, t ∈ S ↔ |Real.log z - t| ≤ δ := by
    intro t
    rw [hSdef, Set.mem_Icc, abs_le]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
  -- The windowed square of `y`, written as an indicator over `S`.
  have hsquares : (fun t : ℝ => if |Real.log z - t| ≤ δ then (y t) ^ 2 else 0)
      = S.indicator (fun t : ℝ => (y t) ^ 2) := by
    funext t
    rw [Set.indicator_apply]
    by_cases ht : t ∈ S
    · rw [ite_eq_left ((hmem t).mp ht), ite_eq_left ht]
    · rw [ite_eq_right (fun hc => ht ((hmem t).mpr hc)), ite_eq_right ht]
  have hysq_int : MeasureTheory.Integrable
      (fun t : ℝ => if |Real.log z - t| ≤ δ then (y t) ^ 2 else 0) := by
    rw [hsquares]
    exact ((hy.pow 2).continuousOn.integrableOn_compact hScomp).integrable_indicator hSmeas
  -- The windowed datum, written as an indicator over `S`, is a.e.-strongly measurable.
  have hsingle : (fun t : ℝ => if |Real.log z - t| ≤ δ then y t else 0) = S.indicator y := by
    funext t
    rw [Set.indicator_apply]
    by_cases ht : t ∈ S
    · rw [ite_eq_left ((hmem t).mp ht), ite_eq_left ht]
    · rw [ite_eq_right (fun hc => ht ((hmem t).mpr hc)), ite_eq_right ht]
  have hy_aesm : MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => if |Real.log z - t| ≤ δ then y t else 0) MeasureTheory.volume := by
    rw [hsingle]
    exact (hy.stronglyMeasurable.indicator hSmeas).aestronglyMeasurable
  -- The uniform Cauchy–Schwarz bound on the window.
  have hmain := zSchur_sq_le_window (δ := δ) (z := z) (M := M) hδ hMnn hk hvan hz
    hysq_int hy_aesm
  have hWnn : 0 ≤ ∫ t : ℝ, if |Real.log z - t| ≤ δ then (y t) ^ 2 else 0 := by
    refine integral_nonneg (fun t => ?_)
    split_ifs with h
    · exact sq_nonneg _
    · exact le_refl 0
  calc (∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) * y t) ^ 2
      ≤ 2 * δ * M ^ 2 * (∫ t : ℝ, if |Real.log z - t| ≤ δ then (y t) ^ 2 else 0) := hmain
    _ ≤ (2 * δ * M ^ 2 + 1) * (∫ t : ℝ, if |Real.log z - t| ≤ δ then (y t) ^ 2 else 0) :=
        mul_le_mul_of_nonneg_right (by linarith) hWnn

end Work.FTS.EllSol.EllPkgAux.MollDom
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.thMoll_pth_fold =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The `θ`-derivative of the angular mollification of a trace-class datum.**

Writing `ρ = sKer ε` for the normalised bump and

  `Kern ρ θ s = ρ (θ - s) - ρ (θ + s) - ρ (θ + s - π)`

for the three images of the doubly odd extension (see `ThMollDefs`), the fold identity
`thMoll G ε w θ = ∫_{s ∈ Iθ} Kern ρ θ s · G w s` may be differentiated under the integral
sign and then integrated by parts on `0..π/2`; the two endpoint terms `G w 0 · ψ 0` and
`G w (π/2) · ψ (π/2)` vanish because a trace-class datum vanishes at both endpoints, and the
three reflected pieces swap sign.  This gives

  `∂_θ (thMoll G ε w) θ = ∫_{s ∈ Iθ} (ρ(θ-s) + ρ(θ+s) + ρ(θ+s-π)) · ∂_θG(w,s) ds`

on the whole closed interval `Iθ = [0, π/2]`.  Only the *interval* integrability of
`s ↦ ∂_θG(w,s)` is needed — its continuity at the endpoints is not available from `TraceClass`
(which says nothing about the datum at `θ < 0`) and is not required. -/
theorem thMoll_pth_fold (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    ∀ w : ℝ, 0 < w → ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.pth (fun z θ' => Work.FTS.EllSol.PkgK5.K5c.thMoll G ε z θ') w θ
        = ∫ s in Work.Spaces.Iθ,
            (Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - s) + Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s)
              + Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s - Real.pi)) * Work.Spaces.pth G w s := by
  intro w hw θ hθ
  -- the two endpoint *values* of the datum, and its `C^∞`-regularity on the open quadrant
  have hsm : Work.FTS.EllipticEst.SmoothOpen G := hT.1
  have hG0 : ∀ z : ℝ, G z 0 = 0 := hT.2.1
  have hGp : ∀ z : ℝ, G z (Real.pi / 2) = 0 := hT.2.2.1
  -- the `θ`-slice `s ↦ G w s` is differentiable on the open interval, with derivative `pth`
  have hHG : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun s : ℝ => G w s) (Work.Spaces.pth G w x) x := by
    intro x hx
    have hd : DifferentiableAt ℝ (fun s : ℝ => G w s) x :=
      ((hsm.curry_θ hw).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
        (isOpen_Ioo.mem_nhds hx)
    simpa only [Work.Spaces.pth] using hd.hasDerivAt
  -- differentiating the fold under the integral sign
  have hderiv := hasDerivAt_thMoll_fold G hT hε hε1 hw θ hθ
  -- integrating the folded kernel by parts
  have hIBP := ibp_kern_first_open (ρ := Work.FTS.EllSol.PkgK5.K5c.sKer ε)
    (ρ' := deriv (Work.FTS.EllSol.PkgK5.K5c.sKer ε)) (G := fun s : ℝ => G w s)
    (H := fun s : ℝ => Work.Spaces.pth G w s) (θ := θ)
    (fun t : ℝ => Work.FTS.EllSol.EllPkgAux.hasDerivAt_sKer ε t)
    (Work.FTS.EllSol.EllPkgAux.continuous_deriv_sKer ε)
    (slice_continuousOn G hT hw) hHG (hG0 w) (hGp w)
    (intervalIntegrable_pth_slice G hT hw)
  show deriv (fun θ' : ℝ => Work.FTS.EllSol.PkgK5.K5c.thMoll G ε w θ') θ
      = ∫ s in Work.Spaces.Iθ,
          (Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - s) + Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s)
            + Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + s - Real.pi)) * Work.Spaces.pth G w s
  rw [hderiv.deriv]
  exact hIBP

end Work.FTS.EllSol.EllPkgAux.MollDom
end
-- ===== merged: Submission.Work.FTS.EllSol.FlatFT.Flat2DAgmonNiceBPrelim1 =====
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

/-! ## Elementary facts about the measure on `ℝ × ℝ` and the interval `Iθ` -/

theorem measurableSet_Iθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc

/-- The product measure on `ℝ × ℝ` restricted to `univ ×ˢ Iθ` is the product of Lebesgue
measure with the restriction of Lebesgue measure to `Iθ`. -/
theorem volume_restrict_univ_prod_Iθ :
    ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))).restrict
        (Set.univ ×ˢ Work.Spaces.Iθ)
      = (MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ) := by
  rw [show (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
      = (MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) from rfl,
    ← MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.restrict_univ]

theorem ae_mem_Iθ :
    ∀ᵐ θ ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ),
      θ ∈ Work.Spaces.Iθ :=
  MeasureTheory.ae_restrict_mem measurableSet_Iθ

/-! ## The general Tonelli/Plancherel identification

Given a "profile" `φ` and the `t`-profile `ψ` that produces the matching `t`-slot, a weight
`W` in `ξ` and a weight `w` in `θ`, the iterated (`ξ`-outer) integral of `W(ξ) · J(ξ)`,
with `J(ξ) = ∫_θ ‖Φ_ξ(θ)‖² w(θ)`, equals the product-measure integral of `ψ(t,θ)² w(θ)`. -/
theorem lintegral_slice_plancherel (φ ψ : ℝ → ℝ → ℝ) (W w : ℝ → ℝ)
    (hWnn : ∀ ξ, 0 ≤ W ξ) (hwnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ w θ)
    (hJint : ∀ ξ, MeasureTheory.IntegrableOn (fun θ : ℝ => ‖slice φ ξ θ‖ ^ 2 * w θ)
      Work.Spaces.Iθ)
    (hφint : ∀ᵐ θ ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ),
      MeasureTheory.Integrable (fun t : ℝ => (ψ t θ) ^ 2))
    (hplanch : ∀ᵐ θ ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ),
      MeasureTheory.Integrable (fun ξ : ℝ => W ξ * ‖slice φ ξ θ‖ ^ 2) ∧
      (∫ ξ : ℝ, W ξ * ‖slice φ ξ θ‖ ^ 2) = ∫ t : ℝ, (ψ t θ) ^ 2)
    (hm1 : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (W p.1) *
        ENNReal.ofReal (‖slice φ p.1 p.2‖ ^ 2 * w p.2))
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)))
    (hm2 : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal ((ψ p.1 p.2) ^ 2 * w p.2))
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ))) :
    (∫⁻ ξ, ENNReal.ofReal (W ξ * ∫ θ in Work.Spaces.Iθ, ‖slice φ ξ θ‖ ^ 2 * w θ))
      = ∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ,
          ENNReal.ofReal ((ψ p.1 p.2) ^ 2 * w p.2) := by
  have hnn1 : ∀ ξ, 0 ≤ᵐ[((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
      Work.Spaces.Iθ)] (fun θ : ℝ => ‖slice φ ξ θ‖ ^ 2 * w θ) := fun ξ =>
    ae_mem_Iθ.mono fun θ hθ => mul_nonneg (sq_nonneg _) (hwnn θ hθ)
  have step1 : ∀ ξ, ENNReal.ofReal (W ξ * ∫ θ in Work.Spaces.Iθ, ‖slice φ ξ θ‖ ^ 2 * w θ)
      = ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (W ξ) * ENNReal.ofReal (‖slice φ ξ θ‖ ^ 2 * w θ) := by
    intro ξ
    rw [ENNReal.ofReal_mul (hWnn ξ),
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hJint ξ) (hnn1 ξ),
      ← lintegral_const_mul' (ENNReal.ofReal (W ξ)) _ ENNReal.ofReal_ne_top]
  have step2 : ∀ θ : ℝ, (∫⁻ ξ, ENNReal.ofReal (W ξ) *
        ENNReal.ofReal (‖slice φ ξ θ‖ ^ 2 * w θ))
      = ENNReal.ofReal (w θ) * ∫⁻ ξ, ENNReal.ofReal (W ξ * ‖slice φ ξ θ‖ ^ 2) := by
    intro θ
    have hpt : ∀ ξ : ℝ, ENNReal.ofReal (W ξ) * ENNReal.ofReal (‖slice φ ξ θ‖ ^ 2 * w θ)
        = ENNReal.ofReal (w θ) * ENNReal.ofReal (W ξ * ‖slice φ ξ θ‖ ^ 2) := by
      intro ξ
      rw [ENNReal.ofReal_mul (sq_nonneg (‖slice φ ξ θ‖)), ← mul_assoc,
        ← ENNReal.ofReal_mul (hWnn ξ)]
      exact mul_comm _ _
    rw [lintegral_congr hpt,
      lintegral_const_mul' (ENNReal.ofReal (w θ)) _ ENNReal.ofReal_ne_top]
  have step3 : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (w θ) *
        ∫⁻ ξ, ENNReal.ofReal (W ξ * ‖slice φ ξ θ‖ ^ 2))
      = ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (w θ) * ENNReal.ofReal (∫ t : ℝ, (ψ t θ) ^ 2) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hplanch] with θ hθ
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hθ.1
      (Eventually.of_forall fun ξ => mul_nonneg (hWnn ξ) (sq_nonneg _)), hθ.2]
  have step4 : (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (w θ) * ENNReal.ofReal (∫ t : ℝ, (ψ t θ) ^ 2))
      = ∫⁻ θ in Work.Spaces.Iθ,
          ∫⁻ t, ENNReal.ofReal (w θ) * ENNReal.ofReal ((ψ t θ) ^ 2) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hφint] with θ hθ
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hθ
      (Eventually.of_forall fun t => sq_nonneg _),
      ← lintegral_const_mul' (ENNReal.ofReal (w θ)) _ ENNReal.ofReal_ne_top]
  have step5 : (∫⁻ θ in Work.Spaces.Iθ,
        ∫⁻ t, ENNReal.ofReal (w θ) * ENNReal.ofReal ((ψ t θ) ^ 2))
      = ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ t, ENNReal.ofReal ((ψ t θ) ^ 2 * w θ) := by
    refine lintegral_congr fun θ => lintegral_congr fun t => ?_
    rw [ENNReal.ofReal_mul (sq_nonneg ((ψ t θ) : ℝ)), mul_comm]
  have step6 : (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ t, ENNReal.ofReal ((ψ t θ) ^ 2 * w θ))
      = ∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ,
          ENNReal.ofReal ((ψ p.1 p.2) ^ 2 * w p.2) := by
    rw [volume_restrict_univ_prod_Iθ]
    exact (MeasureTheory.lintegral_prod_symm
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (ν := (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)
      (fun p : ℝ × ℝ => ENNReal.ofReal ((ψ p.1 p.2) ^ 2 * w p.2)) hm2).symm
  calc (∫⁻ ξ, ENNReal.ofReal (W ξ * ∫ θ in Work.Spaces.Iθ, ‖slice φ ξ θ‖ ^ 2 * w θ))
      = ∫⁻ ξ, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (W ξ) *
          ENNReal.ofReal (‖slice φ ξ θ‖ ^ 2 * w θ) := lintegral_congr step1
    _ = ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ ξ, ENNReal.ofReal (W ξ) *
          ENNReal.ofReal (‖slice φ ξ θ‖ ^ 2 * w θ) :=
        MeasureTheory.lintegral_lintegral_swap
          (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
          (ν := (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ) hm1
    _ = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (w θ) *
          ∫⁻ ξ, ENNReal.ofReal (W ξ * ‖slice φ ξ θ‖ ^ 2) := lintegral_congr step2
    _ = ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (w θ) * ENNReal.ofReal (∫ t : ℝ, (ψ t θ) ^ 2) := step3
    _ = ∫⁻ θ in Work.Spaces.Iθ,
          ∫⁻ t, ENNReal.ofReal (w θ) * ENNReal.ofReal ((ψ t θ) ^ 2) := step4
    _ = ∫⁻ θ in Work.Spaces.Iθ, ∫⁻ t, ENNReal.ofReal ((ψ t θ) ^ 2 * w θ) := step5
    _ = ∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ,
          ENNReal.ofReal ((ψ p.1 p.2) ^ 2 * w p.2) := step6

/-! ## Angular weights, measurability and slices of `NiceFlat` data -/

/-- The open strip `ℝ × (0,π/2)` on which `NiceFlat` data are smooth. -/
abbrev flStrip : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)

theorem flStrip_isOpen : IsOpen flStrip := isOpen_univ.prod isOpen_Ioo

theorem mem_flStrip {t θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : (t, θ) ∈ flStrip :=
  ⟨trivial, hθ⟩

/-- `∀ᵐ θ ∂(volume.restrict Iθ)`, `θ` lies in the *open* interval. -/
theorem ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  have hcongr : Set.Ioo (0 : ℝ) (Real.pi / 2)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] Work.Spaces.Iθ :=
    MeasureTheory.Ioo_ae_eq_Icc
  rw [← MeasureTheory.Measure.restrict_congr_set hcongr]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- A function vanishing outside the `M`-ball has zero derivative on `{M < |x|}`. -/
theorem deriv_eq_zero_of_lt_abs {f : ℝ → ℝ} {M x : ℝ} (hx : M < |x|)
    (hf : ∀ y : ℝ, M < |y| → f y = 0) : deriv f x = 0 := by
  have hopen : IsOpen {y : ℝ | M < |y|} := isOpen_lt continuous_const continuous_abs
  have hev : f =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact hf y hy
  rw [hev.deriv_eq]
  simp

theorem pz_eq_zero_of_lt_abs {ψ : ℝ → ℝ → ℝ} {θ M t : ℝ} (ht : M < |t|)
    (hψ : ∀ y : ℝ, M < |y| → ψ y θ = 0) : Work.Spaces.pz ψ t θ = 0 :=
  deriv_eq_zero_of_lt_abs ht fun y hy => hψ y hy

theorem measurable_wE : Measurable wE := by
  unfold wE
  exact (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow measurable_const

theorem measurable_wA (α : ℝ) : Measurable (wA α) := by
  unfold wA
  exact (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow measurable_const



/-- `AEMeasurable` for a function continuous on the open interval, with respect to the measure
`volume` restricted to the closed `Iθ`. -/
theorem aemeasurable_Iθ_of_continuousOn_Ioo {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioo 0 (Real.pi / 2))) :
    AEMeasurable f ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ) := by
  have h : AEMeasurable f
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioo 0 (Real.pi / 2))) :=
    hf.aemeasurable measurableSet_Ioo
  have hcongr : Set.Ioo (0 : ℝ) (Real.pi / 2)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] Work.Spaces.Iθ :=
    MeasureTheory.Ioo_ae_eq_Icc
  rwa [MeasureTheory.Measure.restrict_congr_set hcongr] at h

/-- The `t`-slice of a function continuous on the strip is continuous. -/
theorem continuous_slice_of_continuousOn_strip {ψ : ℝ → ℝ → ℝ}
    (hψ : ContinuousOn (Function.uncurry ψ) flStrip) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Continuous fun t : ℝ => ψ t θ := by
  simpa [Function.comp_def, Function.uncurry] using
    hψ.comp_continuous (continuous_id.prodMk continuous_const) fun t => mem_flStrip hθ

/-- The `t`-slice of a function with uniformly compact `t`-support has compact support. -/
theorem slice_hasCompactSupport {ψ : ℝ → ℝ → ℝ} {M : ℝ} (_hM : 0 ≤ M)
    (hsupp : ∀ t θ : ℝ, M < |t| → ψ t θ = 0) (θ : ℝ) :
    HasCompactSupport fun t : ℝ => ψ t θ :=
  HasCompactSupport.intro (K := Set.Icc (-M) M) isCompact_Icc fun t ht => by
    have ht' : M < |t| := not_le.mp fun hle => ht (abs_le.mp hle)
    rw [hsupp t θ ht']


/-- `t ↦ f(t)²` is integrable for `f` continuous with compact support. -/
theorem integrable_sq_of_continuous_hasCompactSupport {f : ℝ → ℝ} (hf : Continuous f)
    (hs : HasCompactSupport f) : MeasureTheory.Integrable fun t : ℝ => f t ^ 2 := by
  have hsupp : HasCompactSupport (fun t : ℝ => f t ^ 2) :=
    hs.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num)
  exact (hf.pow 2).integrable_of_hasCompactSupport hsupp

/-- For `ψ` continuous on the strip with uniformly compact `t`-support, the `t`-slice of `ψ²`
is integrable. -/
theorem integrable_sq_slice {ψ : ℝ → ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hcont : ContinuousOn (Function.uncurry ψ) flStrip)
    (hsupp : ∀ t θ : ℝ, M < |t| → ψ t θ = 0) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    MeasureTheory.Integrable fun t : ℝ => (ψ t θ) ^ 2 :=
  integrable_sq_of_continuous_hasCompactSupport
    (continuous_slice_of_continuousOn_strip hcont hθ) (slice_hasCompactSupport hM hsupp θ)

/-- Joint measurability of `(t,θ) ↦ ψ(t,θ)² w(θ)`, as an `ℝ≥0∞`-valued function. -/
theorem aemeasurable_ofReal_sq_mul_snd {ψ : ℝ → ℝ → ℝ} {w : ℝ → ℝ}
    (hψ : ContinuousOn (Function.uncurry ψ) flStrip) (hw : Measurable w) :
    AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal ((ψ p.1 p.2) ^ 2 * w p.2))
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)) := by
  have h1 : AEMeasurable (fun p : ℝ × ℝ => ψ p.1 p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)) :=
    aemeasurable_of_continuousOn_strip hψ
  have h2 : AEMeasurable (fun p : ℝ × ℝ => (ψ p.1 p.2) ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)) :=
    h1.pow_const 2
  have h3 : AEMeasurable (fun p : ℝ × ℝ => w p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)) :=
    (hw.comp measurable_snd).aemeasurable
  exact ENNReal.measurable_ofReal.comp_aemeasurable (h2.mul h3)

/-- Joint measurability of `(ξ,θ) ↦ ofReal(W(ξ)) · ofReal(‖Φ_ξ(θ)‖² w(θ))`. -/
theorem aemeasurable_ofReal_weight_mul {ψ : ℝ → ℝ → ℝ} {W w : ℝ → ℝ}
    (hsl : ContinuousOn (fun p : ℝ × ℝ => slice ψ p.1 p.2) flStrip)
    (hW : Measurable W) (hw : Measurable w) :
    AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (W p.1) *
        ENNReal.ofReal (‖slice ψ p.1 p.2‖ ^ 2 * w p.2))
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)) := by
  have hslice : AEMeasurable (fun p : ℝ × ℝ => ‖slice ψ p.1 p.2‖ ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)) :=
    ((aemeasurable_of_continuousOn_strip
      (F := fun p : ℝ × ℝ => ‖slice ψ p.1 p.2‖) hsl.norm)).pow_const 2
  have hWs : AEMeasurable (fun p : ℝ × ℝ => W p.1)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)) :=
    (hW.comp measurable_fst).aemeasurable
  have hws : AEMeasurable (fun p : ℝ × ℝ => w p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ)) :=
    (hw.comp measurable_snd).aemeasurable
  exact (ENNReal.measurable_ofReal.comp_aemeasurable hWs).mul
    (ENNReal.measurable_ofReal.comp_aemeasurable (hslice.mul hws))

end

end Work.FTS.EllSol.FlatFT
end
-- ===== merged: Submission.Work.FTS.EllSol.Shift2Flat.uTrAthreeE =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

noncomputable section

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Real Topology ENNReal

/-- The `ofReal` of a function continuous on the strip is a.e. strongly measurable.
(Local copy of the same-named lemma of `FlatFT/flatNiceAssembly.lean`, under a *fresh* name so
that modules importing both `FlatFT` and this file do not clash.) -/
theorem aesm_prod_of_continuousOnE {Phi : ℝ × ℝ → ℝ}
    (hPhi : ContinuousOn Phi ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (Phi p))
      ((volume : Measure ℝ).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hmeas : MeasurableSet ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  have hcont : ContinuousOn (fun p : ℝ × ℝ => ENNReal.ofReal (Phi p))
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ENNReal.continuous_ofReal.comp_continuousOn hPhi
  have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (Phi p))
      ((volume.prod volume).restrict ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))) :=
    hcont.aestronglyMeasurable hmeas
  have h2 : (volume.prod volume).restrict ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))
      = volume.prod (volume.restrict Work.Spaces.Iθ) := by
    rw [← Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      Set.univ (Set.Ioo 0 (Real.pi / 2)), Measure.restrict_univ]
    rw [Work.Spaces.Iθ,
      Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)))]
  rw [h2] at h1
  exact h1.aemeasurable


/-! ## Elementary auxiliary facts

These are the little facts about the cutoffs used by the assembly; they do not depend on any of
the three delegated lemmas. -/

/-- The derivative of the cutoff at scale `N` vanishes for `2N ≤ |s|`. -/
theorem deriv_chi_eq_zero_of_two_mul_le {N s : ℝ} (hN : 0 < N) (hs : 2 * N ≤ |s|) :
    deriv (Trunc.chi N) s = 0 := by
  have hev : Trunc.chi N =ᶠ[𝓝 s] (fun _ : ℝ => (0 : ℝ)) := by
    rcases eq_or_lt_of_le hs with heq | hlt
    · -- `|s| = 2N`: the basic cutoff vanishes on a neighbourhood of `±2`
      have hsq : s ^ 2 = (2 * N) ^ 2 := by rw [← sq_abs, ← heq]
      have h4 : (s / N) ^ 2 = 4 := by
        rw [div_pow, hsq]
        field_simp
        ring
      have hneg : (2 : ℝ) - (s / N) ^ 2 < 0 := by rw [h4]; norm_num
      have hopen : IsOpen {y : ℝ | 2 - y ^ 2 < 0} :=
        isOpen_lt (continuous_const.sub (continuous_id.pow 2)) continuous_const
      have hc : Continuous fun t : ℝ => t / N := continuous_id.div_const N
      filter_upwards [hopen.preimage hc |>.mem_nhds hneg] with t ht
      show Real.smoothTransition (2 - (t / N) ^ 2) = 0
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt ht)
    · -- `2N < |s|`
      have hopen : IsOpen {t : ℝ | 2 * N < |t|} := isOpen_lt continuous_const continuous_abs
      filter_upwards [hopen.mem_nhds hlt] with t ht
      exact Trunc.chi_eq_zero hN (le_of_lt ht)
  rw [hev.deriv_eq, deriv_const]

/-- `tailE` vanishes for `t ≥ 2N`. -/
theorem tailE_eq_zero_of_le {N b : ℝ} (hN : 0 < N) (f : ℝ → ℝ → ℝ) {t θ : ℝ}
    (ht : 2 * N ≤ t) : uTrAthree.tailE N b f t θ = 0 := by
  have hzero : ∀ s ∈ Set.Ioc (2 * N) t,
      Real.exp (-(b * s)) * deriv (Trunc.chi N) s * f s θ = 0 := by
    intro s hs
    have hs2 : 2 * N ≤ s := le_of_lt hs.1
    have habs : 2 * N ≤ |s| := by rw [abs_of_nonneg (by linarith)]; exact hs2
    rw [deriv_chi_eq_zero_of_two_mul_le hN habs, mul_zero, zero_mul]
  have h2 : (∫ x in Set.Ioc (2 * N) t,
      Real.exp (-(b * x)) * deriv (Trunc.chi N) x * f x θ) = 0 := by
    rw [show (∫ x in Set.Ioc (2 * N) t,
          Real.exp (-(b * x)) * deriv (Trunc.chi N) x * f x θ)
        = ∫ x in Set.Ioc (2 * N) t, (0 : ℝ) from
      setIntegral_congr_fun measurableSet_Ioc fun x hx => hzero x hx]
    simp
  rw [uTrAthree.tailE, intervalIntegral.integral_of_ge ht, h2, neg_zero, mul_zero]

/-- The elementary pointwise inequality behind the two-term domination of `∂_θ²(uTr)`: it keeps
the factor `A²` on the tail term, so that the `phiTr²` of the truncation stays available. -/
theorem key_ineq {A B X Y w : ℝ} (hA : A ^ 2 ≤ 1) (hB : B ^ 2 ≤ 1) (hw : 0 ≤ w) :
    (A * (B * X + Y)) ^ 2 * w ≤ 2 * (X ^ 2 * w) + 2 * (A ^ 2 * (Y ^ 2 * w)) := by
  have h2 : (B * X + Y) ^ 2 ≤ 2 * (B * X) ^ 2 + 2 * Y ^ 2 := by
    nlinarith [sq_nonneg (B * X - Y)]
  have h3 : (B * X) ^ 2 ≤ X ^ 2 := by nlinarith [sq_nonneg X, hB]
  have h4 : (B * X + Y) ^ 2 ≤ 2 * X ^ 2 + 2 * Y ^ 2 := by linarith
  have hA0 : 0 ≤ A ^ 2 := sq_nonneg A
  have hY0 : 0 ≤ Y ^ 2 := sq_nonneg Y
  have hX0 : 0 ≤ X ^ 2 := sq_nonneg X
  nlinarith [mul_nonneg (mul_nonneg hA0 hY0) hw, mul_nonneg hX0 hw, mul_nonneg hA0 hw,
    sq_nonneg (A * (B * X + Y))]

/-! ## The per-`θ` bound for the tail integral -/

/-- The per-`θ` (one-dimensional) bound for the tail integral. -/
theorem tail_per_theta {N b c : ℝ} (hN : 2 ≤ N) (hb : 0 ≤ b) (hc0 : 0 ≤ c)
    (hc : ∀ s, |deriv (Trunc.chi N) s| ≤ c / N) (hNpos : 0 < N)
    (f : ℝ → ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (∫⁻ t, ENNReal.ofReal (phiTr N t ^ 2 * uTrAthree.tailE N b f t θ ^ 2))
        * ENNReal.ofReal (FlatFT.wE θ)
      ≤ ENNReal.ofReal (40000 * c ^ 2)
        * (ENNReal.ofReal (FlatFT.wE θ)
            * ∫⁻ s in Set.Icc (-(2 * N)) (2 * N), ENNReal.ofReal (f s θ ^ 2)) := by
  have hk0 : ∀ s, 2 * N ≤ |s| → deriv (Trunc.chi N) s = 0 :=
    fun s hs => deriv_chi_eq_zero_of_two_mul_le hNpos hs
  -- restrict the `t`-integral to `[-8192N, 2N]`
  have hstep : ∫⁻ t, ENNReal.ofReal (phiTr N t ^ 2 * uTrAthree.tailE N b f t θ ^ 2)
      ≤ ∫⁻ t in Set.Icc (-(8192 * N)) (2 * N),
          ENNReal.ofReal (uTrAthree.tailE N b f t θ ^ 2) := by
    have hpt : ∀ t : ℝ, ENNReal.ofReal (phiTr N t ^ 2 * uTrAthree.tailE N b f t θ ^ 2)
        ≤ (Set.Icc (-(8192 * N)) (2 * N)).indicator
            (fun t => ENNReal.ofReal (uTrAthree.tailE N b f t θ ^ 2)) t := by
      intro t
      by_cases ht : t ∈ Set.Icc (-(8192 * N)) (2 * N)
      · rw [Set.indicator_of_mem ht,
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ phiTr N t ^ 2)]
        calc ENNReal.ofReal (phiTr N t ^ 2) * ENNReal.ofReal (uTrAthree.tailE N b f t θ ^ 2)
            ≤ 1 * ENNReal.ofReal (uTrAthree.tailE N b f t θ ^ 2) := by
              gcongr
              rw [ENNReal.ofReal_le_one]
              have h1 := phiTr_nonneg N t
              have h2 := phiTr_le_one N t
              nlinarith
          _ = ENNReal.ofReal (uTrAthree.tailE N b f t θ ^ 2) := one_mul _
      · rw [Set.indicator_of_notMem ht]
        have hz : phiTr N t ^ 2 * uTrAthree.tailE N b f t θ ^ 2 = 0 := by
          have hcases : t < -(8192 * N) ∨ 2 * N < t := by
            by_contra hcon
            rw [not_or] at hcon
            exact ht ⟨le_of_not_gt hcon.1, le_of_not_gt hcon.2⟩
          rcases hcases with hlt | hgt
          · have hz2 : phiTr N t = 0 :=
              phiTr_eq_zero hNpos (by rw [abs_of_nonpos (by linarith [hlt])]; linarith)
            rw [hz2]; ring
          · rw [tailE_eq_zero_of_le hNpos f (le_of_lt hgt)]; ring
        rw [hz, ENNReal.ofReal_zero]
    rw [← lintegral_indicator measurableSet_Icc]
    exact lintegral_mono hpt
  -- the one-dimensional estimate
  have hone : ∫⁻ t in Set.Icc (-(8192 * N)) (2 * N),
        ENNReal.ofReal (uTrAthree.tailE N b f t θ ^ 2)
      ≤ ENNReal.ofReal (40000 * c ^ 2)
        * ∫⁻ s in Set.Icc (-(2 * N)) (2 * N), ENNReal.ofReal (f s θ ^ 2) := by
    have h := Work.FTS.EllSol.ShiftFT.uTrAthree.TailOneD N b c hN hb hc0 (fun s => deriv (Trunc.chi N) s) hc hk0
      (fun s => f s θ)
    simpa [uTrAthree.tailE] using h
  have hmid : (∫⁻ t, ENNReal.ofReal (phiTr N t ^ 2 * uTrAthree.tailE N b f t θ ^ 2))
      ≤ ENNReal.ofReal (40000 * c ^ 2)
        * ∫⁻ s in Set.Icc (-(2 * N)) (2 * N), ENNReal.ofReal (f s θ ^ 2) :=
    le_trans hstep hone
  calc (∫⁻ t, ENNReal.ofReal (phiTr N t ^ 2 * uTrAthree.tailE N b f t θ ^ 2))
        * ENNReal.ofReal (FlatFT.wE θ)
      ≤ (ENNReal.ofReal (40000 * c ^ 2)
          * ∫⁻ s in Set.Icc (-(2 * N)) (2 * N), ENNReal.ofReal (f s θ ^ 2))
          * ENNReal.ofReal (FlatFT.wE θ) := by gcongr
    _ = ENNReal.ofReal (40000 * c ^ 2)
          * (ENNReal.ofReal (FlatFT.wE θ)
              * ∫⁻ s in Set.Icc (-(2 * N)) (2 * N), ENNReal.ofReal (f s θ ^ 2)) := by ring

/-! ## The main estimate -/

theorem uTr_Athree (b : ℝ) (u : ℝ → ℝ → ℝ) (hb : 0 ≤ b)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (h0 : ∀ t : ℝ, u t 0 = 0) (h1 : ∀ t : ℝ, u t (Real.pi / 2) = 0)
    (hI : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pth (Work.Spaces.pth u) p.1 p.2) ^ 2
          * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ)) :
    ∃ K : ℝ, 0 < K ∧ ∀ N ≥ (2 : ℝ),
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pth (Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.uTr N b u)) p.1 p.2) ^ 2
          * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ) ∧
      (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.uTr N b u)) p.1 p.2) ^ 2
            * Work.FTS.EllSol.FlatFT.wE p.2)
        ≤ K * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
            (Work.Spaces.pth (Work.Spaces.pth u) p.1 p.2) ^ 2
              * Work.FTS.EllSol.FlatFT.wE p.2) := by
  obtain ⟨c, hc0, hcK⟩ := Work.FTS.EllSol.Trunc.exists_bound_deriv_tk
  refine ⟨2 + 80000 * c ^ 2, by positivity, ?_⟩
  intro N hN
  have hNpos : 0 < N := by linarith
  have hcN : ∀ s : ℝ, |deriv (Trunc.chi N) s| ≤ c / N :=
    fun s => Trunc.abs_deriv_chi_le hcK hNpos s
  -- abbreviations for the two functions occurring in the two slots
  set F : ℝ → ℝ → ℝ := Work.Spaces.pth (Work.Spaces.pth u) with hFdef
  set TE : ℝ → ℝ → ℝ := uTrAthree.tailE N b F with hTEdef
  set Fe : ℝ × ℝ → ℝ :=
    fun p => phiTr N p.1 ^ 2 * (TE p.1 p.2 ^ 2 * FlatFT.wE p.2) with hFedef
  -- the measure identity: the half-strip is the line times the angular measure
  have hmeas : ((volume : Measure (ℝ × ℝ))).restrict (Set.univ ×ˢ Work.Spaces.Iθ)
      = (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  -- the `u`-slot, and the a.e. positivity of the weight
  have hI' : IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2 * FlatFT.wE p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ) := hI
  have hθIoo : ∀ᵐ θ ∂((volume : Measure ℝ).restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rw [Work.Spaces.Iθ]
    rw [ae_restrict_iff' measurableSet_Icc]
    refine (MeasureTheory.ae_iff).mpr ?_
    refine MeasureTheory.measure_mono_null ?_
      (Set.Finite.measure_zero ((Set.finite_singleton (Real.pi / 2)).insert (0 : ℝ)) volume)
    intro θ hθ
    simp only [Set.mem_setOf_eq, not_imp] at hθ
    obtain ⟨h1, h2⟩ := hθ
    rw [Set.mem_Icc] at h1
    rw [Set.mem_Ioo] at h2
    push_neg at h2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    by_cases h : θ ≤ 0
    · left; linarith
    · right; push_neg at h; linarith [h2 h, h1.2]
  have haeIoo : ∀ᵐ p ∂(volume.restrict ((Set.univ : Set ℝ) ×ˢ Work.Spaces.Iθ)),
      p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rw [hmeas]
    rw [Measure.ae_prod_iff_ae_ae (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ).restrict Work.Spaces.Iθ)
      (p := fun z : ℝ × ℝ => z.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
      (show MeasurableSet {z : ℝ × ℝ | z.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)} from by
        have hset : ({z : ℝ × ℝ | z.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)})
            = Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
          ext z; simp
        rw [hset]
        exact MeasurableSet.univ.prod measurableSet_Ioo)]
    filter_upwards with t
    exact hθIoo
  have hw : ∀ᵐ p ∂(volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)), 0 ≤ FlatFT.wE p.2 :=
    haeIoo.mono fun p hp => FlatFT.wE_nonneg (Set.Ioo_subset_Icc_self hp)
  have hFf_nn : 0 ≤ᵐ[volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)]
      (fun p : ℝ × ℝ => F p.1 p.2 ^ 2 * FlatFT.wE p.2) :=
    hw.mono fun p hp => mul_nonneg (sq_nonneg _) hp
  have hFe_nn : 0 ≤ᵐ[volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)] Fe :=
    hw.mono fun p hp => by
      rw [hFedef]
      exact mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) hp)
  -- the pointwise formula for `∂_θ²(uTr)`
  have hpoint : ∀ t : ℝ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Spaces.pth (Work.Spaces.pth (uTr N b u)) t θ
        = phiTr N t * (Trunc.chi N t * F t θ + TE t θ) := by
    intro t θ hθ
    rw [hTEdef, hFdef]
    exact Work.FTS.EllSol.ShiftFT.uTrAthree.UTrPthPth N b u hu t θ hθ
  -- continuity on the open strip
  have hFcont : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    rw [hFdef]
    exact Work.FTS.EllSol.Trunc.continuousOn_uncurry_pth_pth hu
  have hTEcont : ContinuousOn (fun p : ℝ × ℝ => TE p.1 p.2) ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    rw [hTEdef, hFdef]
    exact Work.FTS.EllSol.ShiftFT.uTrAthree.TailECont (Work.Spaces.pth (Work.Spaces.pth u)) N b
      (Work.FTS.EllSol.Trunc.continuousOn_uncurry_pth_pth hu)
  have hwEcont : ContinuousOn (fun p : ℝ × ℝ => FlatFT.wE p.2) ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllSol.Trunc.continuousOn_wE_comp
  have hchicont : ContinuousOn (fun p : ℝ × ℝ => Trunc.chi N p.1) ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((Trunc.chi_contDiff 0 N).continuous.comp continuous_fst).continuousOn
  have hphicont : ContinuousOn (fun p : ℝ × ℝ => phiTr N p.1) ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((phiTr_contDiff 0 N).continuous.comp continuous_fst).continuousOn
  have hFecont : ContinuousOn (fun p : ℝ × ℝ => Fe p) ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    rw [hFedef]
    exact (hphicont.pow 2).mul ((hTEcont.pow 2).mul hwEcont)
  have hRcont : ContinuousOn (fun p : ℝ × ℝ =>
      (phiTr N p.1 * (Trunc.chi N p.1 * F p.1 p.2 + TE p.1 p.2)) ^ 2 * FlatFT.wE p.2)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((hphicont.mul ((hchicont.mul hFcont).add hTEcont)).pow 2).mul hwEcont
  -- the a.e. equality replacing `∂_θ²(uTr)` by its explicit expression
  have haeeq : (fun p : ℝ × ℝ =>
        (Work.Spaces.pth (Work.Spaces.pth (uTr N b u)) p.1 p.2) ^ 2 * FlatFT.wE p.2)
      =ᵐ[volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)]
      (fun p : ℝ × ℝ =>
        (phiTr N p.1 * (Trunc.chi N p.1 * F p.1 p.2 + TE p.1 p.2)) ^ 2 * FlatFT.wE p.2) :=
    haeIoo.mono fun p hp => by
      show (Work.Spaces.pth (Work.Spaces.pth (uTr N b u)) p.1 p.2) ^ 2 * FlatFT.wE p.2
        = (phiTr N p.1 * (Trunc.chi N p.1 * F p.1 p.2 + TE p.1 p.2)) ^ 2 * FlatFT.wE p.2
      rw [hpoint p.1 p.2 hp]
  have hFu_aesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (Work.Spaces.pth (Work.Spaces.pth (uTr N b u)) p.1 p.2) ^ 2 * FlatFT.wE p.2)
      (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
    (Work.FTS.EllSol.Trunc.aesm_strip hRcont).congr haeeq.symm
  have hFe_aesm : AEStronglyMeasurable Fe (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
    Work.FTS.EllSol.Trunc.aesm_strip hFecont
  -- the pointwise real bound and its `ℝ≥0∞` counterpart
  have hpt_real : ∀ p : ℝ × ℝ, p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      (Work.Spaces.pth (Work.Spaces.pth (uTr N b u)) p.1 p.2) ^ 2 * FlatFT.wE p.2
        ≤ 2 * (F p.1 p.2 ^ 2 * FlatFT.wE p.2) + 2 * Fe p := by
    intro p hp
    have hw' : 0 ≤ FlatFT.wE p.2 := FlatFT.wE_nonneg (Set.Ioo_subset_Icc_self hp)
    have hA : (phiTr N p.1) ^ 2 ≤ 1 := by
      have h1 := phiTr_nonneg N p.1
      have h2 := phiTr_le_one N p.1
      nlinarith
    have hB : (Trunc.chi N p.1) ^ 2 ≤ 1 := by
      have h1 := Trunc.chi_nonneg N p.1
      have h2 := Trunc.chi_le_one N p.1
      nlinarith
    have key := key_ineq (A := phiTr N p.1) (B := Trunc.chi N p.1) (X := F p.1 p.2)
      (Y := TE p.1 p.2) (w := FlatFT.wE p.2) hA hB hw'
    rw [hpoint p.1 p.2 hp]
    rw [hFedef]
    exact key
  have hreal_pt := haeIoo.mono hpt_real
  have hFu_nn : 0 ≤ᵐ[volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)]
      (fun p : ℝ × ℝ =>
        (Work.Spaces.pth (Work.Spaces.pth (uTr N b u)) p.1 p.2) ^ 2 * FlatFT.wE p.2) :=
    hw.mono fun p hp => mul_nonneg (sq_nonneg _) hp
  have hptAE : ∀ᵐ p ∂(volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)),
      ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.pth (uTr N b u)) p.1 p.2) ^ 2
          * FlatFT.wE p.2)
        ≤ 2 * ENNReal.ofReal (F p.1 p.2 ^ 2 * FlatFT.wE p.2) + 2 * ENNReal.ofReal (Fe p) := by
    refine haeIoo.mono fun p hp => ?_
    have hw' : 0 ≤ FlatFT.wE p.2 := FlatFT.wE_nonneg (Set.Ioo_subset_Icc_self hp)
    have hFnn : 0 ≤ F p.1 p.2 ^ 2 * FlatFT.wE p.2 := mul_nonneg (sq_nonneg _) hw'
    have hFenn : 0 ≤ Fe p := by
      rw [hFedef]
      exact mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) hw')
    calc ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.pth (uTr N b u)) p.1 p.2) ^ 2
          * FlatFT.wE p.2)
        ≤ ENNReal.ofReal (2 * (F p.1 p.2 ^ 2 * FlatFT.wE p.2) + 2 * Fe p) :=
          ENNReal.ofReal_le_ofReal (hpt_real p hp)
      _ = 2 * ENNReal.ofReal (F p.1 p.2 ^ 2 * FlatFT.wE p.2) + 2 * ENNReal.ofReal (Fe p) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
  -- the per-`θ` bound and its `θ`-integration (Tonelli)
  have hAEm : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (Fe p))
      (volume.prod ((volume : Measure ℝ).restrict Work.Spaces.Iθ)) :=
    aesm_prod_of_continuousOnE hFecont
  have hper : ∀ᵐ θ ∂((volume : Measure ℝ).restrict Work.Spaces.Iθ),
      (∫⁻ t : ℝ, ENNReal.ofReal (Fe (t, θ)))
        ≤ ENNReal.ofReal (40000 * c ^ 2)
            * (ENNReal.ofReal (FlatFT.wE θ)
                * ∫⁻ s in Set.Icc (-(2 * N)) (2 * N), ENNReal.ofReal (F s θ ^ 2)) := by
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    rw [show (fun t : ℝ => ENNReal.ofReal (Fe (t, θ)))
        = fun t : ℝ => ENNReal.ofReal (phiTr N t ^ 2 * TE t θ ^ 2)
            * ENNReal.ofReal (FlatFT.wE θ) from by
      funext t
      show ENNReal.ofReal (phiTr N t ^ 2 * (TE t θ ^ 2 * FlatFT.wE θ))
        = ENNReal.ofReal (phiTr N t ^ 2 * TE t θ ^ 2) * ENNReal.ofReal (FlatFT.wE θ)
      rw [← mul_assoc, ENNReal.ofReal_mul (by positivity)]]
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    exact tail_per_theta hN hb hc0 hcN hNpos F hθ
  -- the `Fe`-slot is bounded by the `u`-slot
  have hFeInf : (∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal (Fe p))
      ≤ ENNReal.ofReal (40000 * c ^ 2)
        * ∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ,
            ENNReal.ofReal (F p.1 p.2 ^ 2 * FlatFT.wE p.2) := by
    have hFfae : AEMeasurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal (F p.1 p.2 ^ 2 * FlatFT.wE p.2))
        (volume.prod ((volume : Measure ℝ).restrict Work.Spaces.Iθ)) := by
      have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2 ^ 2 * FlatFT.wE p.2)
          (volume.prod ((volume : Measure ℝ).restrict Work.Spaces.Iθ)) := by
        rw [← hmeas]
        exact hI'.1
      exact ENNReal.measurable_ofReal.comp_aemeasurable h1.aemeasurable
    rw [hmeas]
    rw [lintegral_prod_symm (μ := (volume : Measure ℝ))
        (ν := (volume : Measure ℝ).restrict Work.Spaces.Iθ) _ hAEm]
    rw [lintegral_prod_symm (μ := (volume : Measure ℝ))
        (ν := (volume : Measure ℝ).restrict Work.Spaces.Iθ) _ hFfae]
    have hinner : ∀ θ : ℝ,
        (∫⁻ s : ℝ, ENNReal.ofReal (F s θ ^ 2 * FlatFT.wE θ))
          = (∫⁻ s : ℝ, ENNReal.ofReal (F s θ ^ 2)) * ENNReal.ofReal (FlatFT.wE θ) := by
      intro θ
      rw [show (fun s : ℝ => ENNReal.ofReal (F s θ ^ 2 * FlatFT.wE θ))
          = fun s : ℝ => ENNReal.ofReal (F s θ ^ 2) * ENNReal.ofReal (FlatFT.wE θ) from by
        funext s
        rw [ENNReal.ofReal_mul (sq_nonneg _)]]
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    refine le_trans (lintegral_mono_ae hper) ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    gcongr
    rw [hinner]
    rw [mul_comm (ENNReal.ofReal (FlatFT.wE _))]
    gcongr
    exact MeasureTheory.Measure.restrict_le_self
  -- pass to the real-valued integrals
  have hFf_fin : (∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ,
        ENNReal.ofReal (F p.1 p.2 ^ 2 * FlatFT.wE p.2)) < ∞ :=
    (hasFiniteIntegral_iff_ofReal hFf_nn).mp hI'.2
  have hFe_lt : (∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal (Fe p)) < ∞ :=
    lt_of_le_of_lt hFeInf (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFf_fin)
  have hFe_int : Integrable Fe (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
    (lintegral_ofReal_ne_top_iff_integrable hFe_aesm hFe_nn).mp hFe_lt.ne
  have hFf_lin : (∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ,
        ENNReal.ofReal (F p.1 p.2 ^ 2 * FlatFT.wE p.2))
      = ENNReal.ofReal (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          F p.1 p.2 ^ 2 * FlatFT.wE p.2) :=
    (ofReal_integral_eq_lintegral_ofReal hI' hFf_nn).symm
  have hFe_lin : (∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal (Fe p))
      = ENNReal.ofReal (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, Fe p) :=
    (ofReal_integral_eq_lintegral_ofReal hFe_int hFe_nn).symm
  have hFe_real : (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, Fe p)
      ≤ 40000 * c ^ 2 * ∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          F p.1 p.2 ^ 2 * FlatFT.wE p.2 := by
    have h1 : ENNReal.ofReal (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, Fe p)
        ≤ ENNReal.ofReal (40000 * c ^ 2 * ∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
            F p.1 p.2 ^ 2 * FlatFT.wE p.2) := by
      rw [← hFe_lin, ENNReal.ofReal_mul (by positivity), ← hFf_lin]
      exact hFeInf
    have hnn2 : 0 ≤ 40000 * c ^ 2 * ∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
        F p.1 p.2 ^ 2 * FlatFT.wE p.2 :=
      mul_nonneg (by positivity) (integral_nonneg_of_ae hFf_nn)
    exact (ENNReal.ofReal_le_ofReal_iff hnn2).mp h1
  -- the `Fu`-slot
  have hsum_int : Integrable (fun p : ℝ × ℝ =>
      2 * (F p.1 p.2 ^ 2 * FlatFT.wE p.2) + 2 * Fe p)
      (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) := by
    have h1 : Integrable (fun p : ℝ × ℝ => 2 * (F p.1 p.2 ^ 2 * FlatFT.wE p.2))
        (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) := hI'.const_mul 2
    have h2 : Integrable (fun p : ℝ × ℝ => 2 * Fe p)
        (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) := hFe_int.const_mul 2
    exact h1.add h2
  have hFu_int : Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.pth (Work.Spaces.pth (uTr N b u)) p.1 p.2) ^ 2 * FlatFT.wE p.2)
      (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
    Integrable.mono' hsum_int hFu_aesm
      ((hFu_nn.and hreal_pt).mono fun p hp => by
        rw [Real.norm_eq_abs, abs_of_nonneg hp.1]
        exact hp.2)
  refine ⟨hFu_int, ?_⟩
  have hmono : (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
        (Work.Spaces.pth (Work.Spaces.pth (uTr N b u)) p.1 p.2) ^ 2 * FlatFT.wE p.2)
      ≤ ∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          (2 * (F p.1 p.2 ^ 2 * FlatFT.wE p.2) + 2 * Fe p) :=
    integral_mono_ae hFu_int hsum_int hreal_pt
  have hsplit : (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
        (2 * (F p.1 p.2 ^ 2 * FlatFT.wE p.2) + 2 * Fe p))
      = 2 * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, F p.1 p.2 ^ 2 * FlatFT.wE p.2)
        + 2 * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, Fe p) := by
    rw [integral_add (hI'.const_mul 2) (hFe_int.const_mul 2),
      integral_const_mul, integral_const_mul]
  rw [hsplit] at hmono
  calc (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
        (Work.Spaces.pth (Work.Spaces.pth (uTr N b u)) p.1 p.2) ^ 2 * FlatFT.wE p.2)
      ≤ 2 * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, F p.1 p.2 ^ 2 * FlatFT.wE p.2)
        + 2 * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, Fe p) := hmono
    _ ≤ 2 * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, F p.1 p.2 ^ 2 * FlatFT.wE p.2)
        + 2 * (40000 * c ^ 2 * ∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
            F p.1 p.2 ^ 2 * FlatFT.wE p.2) := by linarith [hFe_real]
    _ = (2 + 80000 * c ^ 2) * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          F p.1 p.2 ^ 2 * FlatFT.wE p.2) := by ring

end

end Work.FTS.EllSol.ShiftFT
end
-- ===== merged: Submission.Work.FTS.EllSol.ShiftFT.AtwoAux.Aesm =====
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

/-- The pointwise expression `W` is a.e. strongly measurable on the half-strip: by the a.e.
identity `uTr_L2_eq` it agrees with the shifted second slot of the truncated datum `uTr N b u`,
which is `C²` on the open strip by `uTr_niceFlat`. -/
theorem uTrAtwo_W_aesm (N b : ℝ) (u : ℝ → ℝ → ℝ) (hN : 2 ≤ N)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (h0 : ∀ t : ℝ, u t 0 = 0) (h1 : ∀ t : ℝ, u t (Real.pi / 2) = 0) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
        (uTrAtwo_W N b u p) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
      (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) := by
  have hnf : Work.FTS.EllSol.FlatFT.NiceFlat (uTr N b u) := uTr_niceFlat N b u hN hu h0 h1
  have hC2 : ContDiffOn ℝ 2 (Function.uncurry (uTr N b u))
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := hnf.1
  have hV : IsOpen ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    isOpen_univ.prod isOpen_Ioo
  have hpz : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz (uTr N b u)))
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Work.FTS.EllSol.Trunc.contDiffOn_uncurry_pz_succ hV 1 hC2
  have hpzpz : ContDiffOn ℝ 0 (Function.uncurry (Work.Spaces.pz (Work.Spaces.pz (uTr N b u))))
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Work.FTS.EllSol.Trunc.contDiffOn_uncurry_pz_succ hV 0 hpz
  have haesm_L2T : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (uTrAtwo_L2 b (uTr N b u) p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
      (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) := by
    have hA : AEStronglyMeasurable
        (fun p : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.pz (uTr N b u)) p.1 p.2)
        (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
      Work.FTS.EllSol.Trunc.aesm_strip hpzpz.continuousOn
    have hB : AEStronglyMeasurable
        (fun p : ℝ × ℝ => Work.Spaces.pz (uTr N b u) p.1 p.2)
        (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
      Work.FTS.EllSol.Trunc.aesm_strip hpz.continuousOn
    have hC : AEStronglyMeasurable (fun p : ℝ × ℝ => uTr N b u p.1 p.2)
        (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
      Work.FTS.EllSol.Trunc.aesm_strip hC2.continuousOn
    have hwE : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.FTS.EllSol.FlatFT.wE p.2)
        (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
      Work.FTS.EllSol.Trunc.aesm_strip Work.FTS.EllSol.Trunc.continuousOn_wE_comp
    change AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (Work.Spaces.pz (Work.Spaces.pz (uTr N b u)) p.1 p.2
        - 2 * b * Work.Spaces.pz (uTr N b u) p.1 p.2
        + b ^ 2 * uTr N b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
      (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ))
    have hmain : AEMeasurable (fun p : ℝ × ℝ =>
        (Work.Spaces.pz (Work.Spaces.pz (uTr N b u)) p.1 p.2
          - 2 * b * Work.Spaces.pz (uTr N b u) p.1 p.2
          + b ^ 2 * uTr N b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
        (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
      (((hA.aemeasurable.sub ((hB.aemeasurable).const_mul (2 * b))).add
        ((hC.aemeasurable).const_mul (b ^ 2))).pow_const 2).mul hwE.aemeasurable
    exact hmain.aestronglyMeasurable
  refine haesm_L2T.congr ?_
  filter_upwards [ae_uTr_L2_eq N b u hu] with p hp
  rw [hp]

end

end Work.FTS.EllSol.ShiftFT
end
-- ===== merged: Submission.Work.FTS.EllSol.ShiftFT.AtwoAux.Integrable =====
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


/-- Integrability of the square of the second derivative of `phiTr` (it is continuous and
compactly supported, with support inside `[-8192N, 8192N]`). -/
theorem integrable_deriv2_phiTr_sq (N : ℝ) (hN : 0 < N) :
    Integrable (fun t : ℝ => (deriv (deriv (phiTr N)) t) ^ 2) volume := by
  set A : ℝ := 8192 * N with hAdef
  have hsupp : ∀ t : ℝ, t ∉ Set.Icc (-A) A → (deriv (deriv (phiTr N)) t) ^ 2 = 0 := by
    intro t ht
    have hge : A ≤ |t| := by
      by_contra hcon
      push Not at hcon
      exact ht ⟨by linarith [neg_abs_le t, hcon], by linarith [le_abs_self t, hcon]⟩
    rw [deriv2_phiTr_eq_zero_of_abs_ge hN (by rw [hAdef] at hge; exact hge)]
    ring
  have hcont : Continuous (fun t : ℝ => (deriv (deriv (phiTr N)) t) ^ 2) :=
    (((phiTr_contDiff 2 N).deriv').continuous_deriv_one).pow 2
  have hOn : IntegrableOn (fun t : ℝ => (deriv (deriv (phiTr N)) t) ^ 2) (Set.Icc (-A) A) :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hind : Integrable ((Set.Icc (-A) A).indicator
      (fun t : ℝ => (deriv (deriv (phiTr N)) t) ^ 2)) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr hOn
  refine hind.congr ?_
  filter_upwards with t
  by_cases ht : t ∈ Set.Icc (-A) A
  · rw [Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem ht, hsupp t ht]

/-- Integrability of the first summand of `D`. -/
theorem uTrAtwo_D1_integrable (N b : ℝ) (u : ℝ → ℝ → ℝ)
    (hI : IntegrableOn (fun p : ℝ × ℝ => (uTrAtwo_L2 b u p.1 p.2) ^ 2
      * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ)) :
    IntegrableOn (fun p : ℝ × ℝ => 3 * ((uTrAtwo_L2 b u p.1 p.2) ^ 2
      * Work.FTS.EllSol.FlatFT.wE p.2)) (Set.univ ×ˢ Work.Spaces.Iθ) :=
  hI.const_mul 3

/-- Integrability of the second summand of `D`. -/
theorem uTrAtwo_D2_integrable (N b : ℝ) (u : ℝ → ℝ → ℝ) (Kd : ℝ)
    (hJ : IntegrableOn (fun p : ℝ × ℝ => (uTrAtwo_L1 b u p.1 p.2) ^ 2
      * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ)) :
    IntegrableOn (fun p : ℝ × ℝ => 3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2
      * ((uTrAtwo_L1 b u p.1 p.2) ^ 2
        * Work.FTS.EllSol.FlatFT.wE p.2)) (Set.univ ×ˢ Work.Spaces.Iθ) :=
  hJ.const_mul _

/-- Integrability of the third summand of `D`. -/
theorem uTrAtwo_D3_integrable (N b : ℝ) (u : ℝ → ℝ → ℝ) (hN : 0 < N)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hJ : IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2
          * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ)) :
    IntegrableOn (fun p : ℝ × ℝ => 3 * (deriv (deriv (phiTr N)) p.1) ^ 2
      * (4 * N * ((∫ s in Set.Icc (-(2 * N)) (2 * N), (uTrAtwo_L1 b u s p.2) ^ 2)
          * Work.FTS.EllSol.FlatFT.wE p.2))) (Set.univ ×ˢ Work.Spaces.Iθ) := by
  have hwin := (Aux2.windowMarginal b N u hu hJ).1
  have hBw : Integrable (fun θ : ℝ => 4 * N * ((∫ s in Set.Icc (-(2 * N)) (2 * N),
      (uTrAtwo_L1 b u s θ) ^ 2) * Work.FTS.EllSol.FlatFT.wE θ))
      (volume.restrict Work.Spaces.Iθ) :=
    hwin.const_mul (4 * N)
  have hprod : Integrable (fun p : ℝ × ℝ => (3 * (deriv (deriv (phiTr N)) p.1) ^ 2)
      * (4 * N * ((∫ s in Set.Icc (-(2 * N)) (2 * N), (uTrAtwo_L1 b u s p.2) ^ 2)
          * Work.FTS.EllSol.FlatFT.wE p.2)))
      (volume.prod (volume.restrict Work.Spaces.Iθ)) :=
    Integrable.mul_prod ((integrable_deriv2_phiTr_sq N hN).const_mul 3) hBw
  rwa [IntegrableOn, uTrAtwo_prodRestrict_Iθ]

/-- Integrability of the dominating function. -/
theorem uTrAtwo_D_integrable (N b : ℝ) (u : ℝ → ℝ → ℝ) (Kd : ℝ) (hN : 0 < N)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hI : IntegrableOn (fun p : ℝ × ℝ => (uTrAtwo_L2 b u p.1 p.2) ^ 2
      * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ))
    (hJ : IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2
          * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ)) :
    IntegrableOn (uTrAtwo_D N b u Kd) (Set.univ ×ˢ Work.Spaces.Iθ) := by
  have hJ' : IntegrableOn (fun p : ℝ × ℝ => (uTrAtwo_L1 b u p.1 p.2) ^ 2
      * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ) := by
    simpa only [uTrAtwo_L1] using hJ
  have h1 := uTrAtwo_D1_integrable N b u hI
  have h2 := uTrAtwo_D2_integrable N b u Kd hJ'
  have h3 := uTrAtwo_D3_integrable N b u hN hu hJ
  change IntegrableOn (fun p : ℝ × ℝ =>
      3 * ((uTrAtwo_L2 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
      + 3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2
          * ((uTrAtwo_L1 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
      + 3 * (deriv (deriv (phiTr N)) p.1) ^ 2
          * (4 * N * ((∫ s in Set.Icc (-(2 * N)) (2 * N), (uTrAtwo_L1 b u s p.2) ^ 2)
              * Work.FTS.EllSol.FlatFT.wE p.2))) (Set.univ ×ˢ Work.Spaces.Iθ)
  exact (h1.add h2).add h3

/-- The value of the integral of the dominating function `D`. -/
theorem integral_uTrAtwo_D (N b : ℝ) (u : ℝ → ℝ → ℝ) (Kd : ℝ) (hN : 0 < N)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hI : IntegrableOn (fun p : ℝ × ℝ => (uTrAtwo_L2 b u p.1 p.2) ^ 2
      * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ))
    (hJ : IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2
          * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ)) :
    (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, uTrAtwo_D N b u Kd p)
      = 3 * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L2 b u p.1 p.2) ^ 2
              * Work.FTS.EllSol.FlatFT.wE p.2)
        + 3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2
            * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
                * Work.FTS.EllSol.FlatFT.wE p.2)
        + 3 * (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2)
            * (4 * N * (∫ θ in Work.Spaces.Iθ,
                (∫ s in Set.Icc (-(2 * N)) (2 * N), (uTrAtwo_L1 b u s θ) ^ 2)
                  * Work.FTS.EllSol.FlatFT.wE θ)) := by
  have hJ' : IntegrableOn (fun p : ℝ × ℝ => (uTrAtwo_L1 b u p.1 p.2) ^ 2
      * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ) := by
    simpa only [uTrAtwo_L1] using hJ
  have h1 := uTrAtwo_D1_integrable N b u hI
  have h2 := uTrAtwo_D2_integrable N b u Kd hJ'
  have h3 := uTrAtwo_D3_integrable N b u hN hu hJ
  have e1 : (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, 3 * ((uTrAtwo_L2 b u p.1 p.2) ^ 2
      * Work.FTS.EllSol.FlatFT.wE p.2))
      = 3 * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L2 b u p.1 p.2) ^ 2
          * Work.FTS.EllSol.FlatFT.wE p.2) :=
    MeasureTheory.integral_const_mul 3 _
  have e2 : (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
        3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2
          * ((uTrAtwo_L1 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2))
      = 3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2
          * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (uTrAtwo_L1 b u p.1 p.2) ^ 2
              * Work.FTS.EllSol.FlatFT.wE p.2) :=
    MeasureTheory.integral_const_mul _ _
  have e3 : (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, 3 * (deriv (deriv (phiTr N)) p.1) ^ 2
      * (4 * N * ((∫ s in Set.Icc (-(2 * N)) (2 * N), (uTrAtwo_L1 b u s p.2) ^ 2)
          * Work.FTS.EllSol.FlatFT.wE p.2)))
      = 3 * (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2)
          * (4 * N * (∫ θ in Work.Spaces.Iθ,
              (∫ s in Set.Icc (-(2 * N)) (2 * N), (uTrAtwo_L1 b u s θ) ^ 2)
                * Work.FTS.EllSol.FlatFT.wE θ)) := by
    rw [Work.FTS.EllSol.Trunc.setIntegral_univ_prod_Iθ_eq_iterated
      (f := fun t θ => 3 * (deriv (deriv (phiTr N)) t) ^ 2
        * (4 * N * ((∫ s in Set.Icc (-(2 * N)) (2 * N), (uTrAtwo_L1 b u s θ) ^ 2)
            * Work.FTS.EllSol.FlatFT.wE θ))) h3]
    have hinner : ∀ t : ℝ, (∫ θ in Work.Spaces.Iθ,
        (3 * (deriv (deriv (phiTr N)) t) ^ 2)
          * (4 * N * ((∫ s in Set.Icc (-(2 * N)) (2 * N), (uTrAtwo_L1 b u s θ) ^ 2)
              * Work.FTS.EllSol.FlatFT.wE θ)))
        = (3 * (deriv (deriv (phiTr N)) t) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, 4 * N * ((∫ s in Set.Icc (-(2 * N)) (2 * N),
                (uTrAtwo_L1 b u s θ) ^ 2) * Work.FTS.EllSol.FlatFT.wE θ)) :=
      fun t => MeasureTheory.integral_const_mul _ _
    simp only [hinner]
    rw [MeasureTheory.integral_mul_const]
    have h1 : (∫ t in Set.univ, 3 * (deriv (deriv (phiTr N)) t) ^ 2)
        = 3 * (∫ t in Set.univ, (deriv (deriv (phiTr N)) t) ^ 2) :=
      MeasureTheory.integral_const_mul 3 _
    have h2 : (∫ θ in Work.Spaces.Iθ, 4 * N * ((∫ s in Set.Icc (-(2 * N)) (2 * N),
        (uTrAtwo_L1 b u s θ) ^ 2) * Work.FTS.EllSol.FlatFT.wE θ))
        = 4 * N * (∫ θ in Work.Spaces.Iθ, (∫ s in Set.Icc (-(2 * N)) (2 * N),
            (uTrAtwo_L1 b u s θ) ^ 2) * Work.FTS.EllSol.FlatFT.wE θ) :=
      MeasureTheory.integral_const_mul _ _
    rw [h1, h2]
    try ring
  change (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
      3 * ((uTrAtwo_L2 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
      + 3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2
          * ((uTrAtwo_L1 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
      + 3 * (deriv (deriv (phiTr N)) p.1) ^ 2
          * (4 * N * ((∫ s in Set.Icc (-(2 * N)) (2 * N), (uTrAtwo_L1 b u s p.2) ^ 2)
              * Work.FTS.EllSol.FlatFT.wE p.2))) = _
  have step1 : (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
        (3 * ((uTrAtwo_L2 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
          + 3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2
              * ((uTrAtwo_L1 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2))
        + 3 * (deriv (deriv (phiTr N)) p.1) ^ 2
            * (4 * N * ((∫ s in Set.Icc (-(2 * N)) (2 * N), (uTrAtwo_L1 b u s p.2) ^ 2)
                * Work.FTS.EllSol.FlatFT.wE p.2)))
      = (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          3 * ((uTrAtwo_L2 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
            + 3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2
                * ((uTrAtwo_L1 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2))
        + ∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
            3 * (deriv (deriv (phiTr N)) p.1) ^ 2
              * (4 * N * ((∫ s in Set.Icc (-(2 * N)) (2 * N), (uTrAtwo_L1 b u s p.2) ^ 2)
                  * Work.FTS.EllSol.FlatFT.wE p.2)) :=
    MeasureTheory.integral_add (h1.add h2) h3
  have step2 : (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
        3 * ((uTrAtwo_L2 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
          + 3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2
              * ((uTrAtwo_L1 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2))
      = (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          3 * ((uTrAtwo_L2 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2))
        + ∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
            3 * (Kd / N + 2 * (Kd / (4096 * N))) ^ 2
              * ((uTrAtwo_L1 b u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2) :=
    MeasureTheory.integral_add h1 h2
  rw [step1, step2, e1, e2, e3]

end

end Work.FTS.EllSol.ShiftFT
end
-- ===== merged: Submission.Work.FTS.EllSol.Trunc.curlAgmon =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.Trunc

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

local notation "σ" => Work.FTS.EllipticEst.thEta
local notation "Iθ" => Work.Spaces.Iθ
local notation "J" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-- A function continuous on the *open* interval is a.e.-strongly-measurable for the restriction
of Lebesgue measure to the closed interval `Iθ = [0, π/2]` (the two sets differ by the null set
`{0, π/2}`). -/
private theorem aesm_restrict_Iθ_of_continuousOn {f : ℝ → ℝ} (h : ContinuousOn f J) :
    AEStronglyMeasurable f ((volume : Measure ℝ).restrict Iθ) := by
  have h1 : AEStronglyMeasurable f ((volume : Measure ℝ).restrict J) :=
    h.aestronglyMeasurable measurableSet_Ioo
  rw [MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)))] at h1
  exact h1

/-- Integrability on `Iθ` from a pointwise bound valid on the open interval. -/
private theorem integrableOn_Iθ_of_abs_le {f g : ℝ → ℝ} (hg : IntegrableOn g Iθ)
    (hf : AEStronglyMeasurable f ((volume : Measure ℝ).restrict Iθ))
    (hle : ∀ θ ∈ J, |f θ| ≤ |g θ|) : IntegrableOn f Iθ := by
  refine (hg.abs).mono' hf ?_
  filter_upwards [Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo hle] with θ hθ
  simpa [Real.norm_eq_abs] using hθ

theorem curlAgmon : ∃ C : ℝ, 0 < C ∧ ∀ F : ℝ → ℂ, ContDiffOn ℝ 2 F (Set.Ioo 0 (Real.pi / 2)) → F 0 = 0 → F (Real.pi / 2) = 0 → MeasureTheory.IntegrableOn (fun θ : ℝ => ‖F θ‖ ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ → MeasureTheory.IntegrableOn (fun θ : ℝ => ‖deriv F θ‖ ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ → MeasureTheory.IntegrableOn (fun θ : ℝ => ‖deriv (deriv F) θ‖ ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ → (∫ θ in Work.Spaces.Iθ, ‖deriv F θ‖ ^ 2 * Work.FTS.EllipticEst.thEta θ) ≤ C * ((∫ θ in Work.Spaces.Iθ, ‖F θ‖ ^ 2 * Work.FTS.EllipticEst.thEta θ) + Real.sqrt ((∫ θ in Work.Spaces.Iθ, ‖F θ‖ ^ 2 * Work.FTS.EllipticEst.thEta θ) * (∫ θ in Work.Spaces.Iθ, ‖deriv (deriv F) θ‖ ^ 2 * Work.FTS.EllipticEst.thEta θ))) := by
  obtain ⟨C, hCpos, hC⟩ := Work.EllipticEst.Core.i0Aux.thetaInterpCore
  refine ⟨C, hCpos, ?_⟩
  intro F hF hF0 hFπ hP hQ hE
  -- the two real projections
  set U : ℝ → ℝ := fun θ => (F θ).re with hU
  set W : ℝ → ℝ := fun θ => (F θ).im with hW
  -- ## differentiability on the open interval
  have hdiff : ∀ θ ∈ J, DifferentiableAt ℝ F θ := fun θ hθ =>
    (hF.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  -- ## the derivative identities (projections commute with `deriv`)
  have hdU : ∀ θ ∈ J, deriv U θ = (deriv F θ).re := by
    intro θ hθ
    rw [hU]
    exact deriv_re_eq (hdiff θ hθ)
  have hdW : ∀ θ ∈ J, deriv W θ = (deriv F θ).im := by
    intro θ hθ
    rw [hW]
    exact deriv_im_eq (hdiff θ hθ)
  have hddU : ∀ θ ∈ J, deriv (deriv U) θ = (deriv (deriv F) θ).re := by
    intro θ hθ
    rw [hU]
    exact deriv_deriv_re_eq isOpen_Ioo hθ hF
  have hddW : ∀ θ ∈ J, deriv (deriv W) θ = (deriv (deriv F) θ).im := by
    intro θ hθ
    rw [hW]
    exact deriv_deriv_im_eq isOpen_Ioo hθ hF
  -- ## the pointwise splitting of the squared norm
  have hnorm : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    intro z
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hpt0 : ∀ θ ∈ J, ‖F θ‖ ^ 2 * σ θ = (U θ) ^ 2 * σ θ + (W θ) ^ 2 * σ θ := by
    intro θ _
    have h1 : U θ = (F θ).re := by rw [hU]
    have h2 : W θ = (F θ).im := by rw [hW]
    rw [hnorm (F θ), h1, h2]
    ring
  have hpt1 : ∀ θ ∈ J,
      ‖deriv F θ‖ ^ 2 * σ θ = (deriv U θ) ^ 2 * σ θ + (deriv W θ) ^ 2 * σ θ := by
    intro θ hθ
    have h1 : deriv U θ = (deriv F θ).re := hdU θ hθ
    have h2 : deriv W θ = (deriv F θ).im := hdW θ hθ
    rw [hnorm (deriv F θ), h1, h2]
    ring
  have hpt2 : ∀ θ ∈ J, ‖deriv (deriv F) θ‖ ^ 2 * σ θ
      = (deriv (deriv U) θ) ^ 2 * σ θ + (deriv (deriv W) θ) ^ 2 * σ θ := by
    intro θ hθ
    have h1 : deriv (deriv U) θ = (deriv (deriv F) θ).re := hddU θ hθ
    have h2 : deriv (deriv W) θ = (deriv (deriv F) θ).im := hddW θ hθ
    rw [hnorm (deriv (deriv F) θ), h1, h2]
    ring
  -- ## regularity of the projections and of their derivatives
  have hUcd : ContDiffOn ℝ 2 U J := by rw [hU]; exact contDiffOn_re hF
  have hWcd : ContDiffOn ℝ 2 W J := by rw [hW]; exact contDiffOn_im hF
  have hdUcd : ContDiffOn ℝ 1 (deriv U) J :=
    hUcd.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  have hdWcd : ContDiffOn ℝ 1 (deriv W) J :=
    hWcd.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  have hddUcd : ContDiffOn ℝ 0 (deriv (deriv U)) J :=
    hdUcd.deriv_of_isOpen isOpen_Ioo (m := 0) (by norm_num)
  have hddWcd : ContDiffOn ℝ 0 (deriv (deriv W)) J :=
    hdWcd.deriv_of_isOpen isOpen_Ioo (m := 0) (by norm_num)
  have haesm_U : AEStronglyMeasurable U ((volume : Measure ℝ).restrict Iθ) :=
    aesm_restrict_Iθ_of_continuousOn hUcd.continuousOn
  have haesm_W : AEStronglyMeasurable W ((volume : Measure ℝ).restrict Iθ) :=
    aesm_restrict_Iθ_of_continuousOn hWcd.continuousOn
  have haesm_dU : AEStronglyMeasurable (deriv U) ((volume : Measure ℝ).restrict Iθ) :=
    aesm_restrict_Iθ_of_continuousOn hdUcd.continuousOn
  have haesm_dW : AEStronglyMeasurable (deriv W) ((volume : Measure ℝ).restrict Iθ) :=
    aesm_restrict_Iθ_of_continuousOn hdWcd.continuousOn
  have haesm_ddU : AEStronglyMeasurable (deriv (deriv U)) ((volume : Measure ℝ).restrict Iθ) :=
    aesm_restrict_Iθ_of_continuousOn hddUcd.continuousOn
  have haesm_ddW : AEStronglyMeasurable (deriv (deriv W)) ((volume : Measure ℝ).restrict Iθ) :=
    aesm_restrict_Iθ_of_continuousOn hddWcd.continuousOn
  have hσmeas : Measurable σ := by
    unfold Work.FTS.EllipticEst.thEta
    exact (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow measurable_const
  have hσaesm : AEStronglyMeasurable (fun θ : ℝ => σ θ) ((volume : Measure ℝ).restrict Iθ) :=
    hσmeas.aemeasurable.restrict.aestronglyMeasurable
  -- ## the two projections, each with its own three weighted slots
  have hU0 : U 0 = 0 := by rw [hU]; simp [hF0]
  have hUπ : U (Real.pi / 2) = 0 := by rw [hU]; simp [hFπ]
  have hW0 : W 0 = 0 := by rw [hW]; simp [hF0]
  have hWπ : W (Real.pi / 2) = 0 := by rw [hW]; simp [hFπ]
  have hPU : IntegrableOn (fun θ => (U θ) ^ 2 * σ θ) Iθ :=
    integrableOn_Iθ_of_abs_le hP ((haesm_U.pow 2).mul hσaesm) (fun θ _ => by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (U θ)),
        abs_of_nonneg (sq_nonneg ‖F θ‖)]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg (σ θ))
      have h1 : U θ = (F θ).re := by rw [hU]
      rw [hnorm (F θ), h1]
      nlinarith [sq_nonneg (F θ).im])
  have hPW : IntegrableOn (fun θ => (W θ) ^ 2 * σ θ) Iθ :=
    integrableOn_Iθ_of_abs_le hP ((haesm_W.pow 2).mul hσaesm) (fun θ _ => by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (W θ)),
        abs_of_nonneg (sq_nonneg ‖F θ‖)]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg (σ θ))
      have h1 : W θ = (F θ).im := by rw [hW]
      rw [hnorm (F θ), h1]
      nlinarith [sq_nonneg (F θ).re])
  have hQU : IntegrableOn (fun θ => (deriv U θ) ^ 2 * σ θ) Iθ :=
    integrableOn_Iθ_of_abs_le hQ ((haesm_dU.pow 2).mul hσaesm) (fun θ hθ => by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (deriv U θ)),
        abs_of_nonneg (sq_nonneg ‖deriv F θ‖)]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg (σ θ))
      have h1 : deriv U θ = (deriv F θ).re := hdU θ hθ
      rw [hnorm (deriv F θ), h1]
      nlinarith [sq_nonneg (deriv F θ).im])
  have hQW : IntegrableOn (fun θ => (deriv W θ) ^ 2 * σ θ) Iθ :=
    integrableOn_Iθ_of_abs_le hQ ((haesm_dW.pow 2).mul hσaesm) (fun θ hθ => by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (deriv W θ)),
        abs_of_nonneg (sq_nonneg ‖deriv F θ‖)]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg (σ θ))
      have h1 : deriv W θ = (deriv F θ).im := hdW θ hθ
      rw [hnorm (deriv F θ), h1]
      nlinarith [sq_nonneg (deriv F θ).re])
  have hEU : IntegrableOn (fun θ => (deriv (deriv U) θ) ^ 2 * σ θ) Iθ :=
    integrableOn_Iθ_of_abs_le hE ((haesm_ddU.pow 2).mul hσaesm) (fun θ hθ => by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (deriv (deriv U) θ)),
        abs_of_nonneg (sq_nonneg ‖deriv (deriv F) θ‖)]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg (σ θ))
      have h1 : deriv (deriv U) θ = (deriv (deriv F) θ).re := hddU θ hθ
      rw [hnorm (deriv (deriv F) θ), h1]
      nlinarith [sq_nonneg (deriv (deriv F) θ).im])
  have hEW : IntegrableOn (fun θ => (deriv (deriv W) θ) ^ 2 * σ θ) Iθ :=
    integrableOn_Iθ_of_abs_le hE ((haesm_ddW.pow 2).mul hσaesm) (fun θ hθ => by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (deriv (deriv W) θ)),
        abs_of_nonneg (sq_nonneg ‖deriv (deriv F) θ‖)]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg (σ θ))
      have h1 : deriv (deriv W) θ = (deriv (deriv F) θ).im := hddW θ hθ
      rw [hnorm (deriv (deriv F) θ), h1]
      nlinarith [sq_nonneg (deriv (deriv F) θ).re])
  -- ## the real inequality, for each projection
  have hCU := hC U hUcd hU0 hUπ hPU hQU hEU
  have hCW := hC W hWcd hW0 hWπ hPW hQW hEW
  -- ## the three slot integrals split into their two projections
  have hsplit0 : (∫ θ in Iθ, (U θ) ^ 2 * σ θ) + (∫ θ in Iθ, (W θ) ^ 2 * σ θ)
      = ∫ θ in Iθ, ‖F θ‖ ^ 2 * σ θ := by
    rw [← MeasureTheory.integral_add hPU hPW]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo hpt0] with θ hθ
    exact hθ.symm
  have hsplit1 : (∫ θ in Iθ, (deriv U θ) ^ 2 * σ θ) + (∫ θ in Iθ, (deriv W θ) ^ 2 * σ θ)
      = ∫ θ in Iθ, ‖deriv F θ‖ ^ 2 * σ θ := by
    rw [← MeasureTheory.integral_add hQU hQW]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo hpt1] with θ hθ
    exact hθ.symm
  have hsplit2 : (∫ θ in Iθ, (deriv (deriv U) θ) ^ 2 * σ θ)
        + (∫ θ in Iθ, (deriv (deriv W) θ) ^ 2 * σ θ)
      = ∫ θ in Iθ, ‖deriv (deriv F) θ‖ ^ 2 * σ θ := by
    rw [← MeasureTheory.integral_add hEU hEW]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo hpt2] with θ hθ
    exact hθ.symm
  -- ## nonnegativity of the four quadratic slots
  have hσnn : ∀ θ ∈ Iθ, 0 ≤ σ θ := fun θ hθ => Work.FTS.EllipticEst.thEta_nonneg hθ
  have hPUnn : 0 ≤ ∫ θ in Iθ, (U θ) ^ 2 * σ θ :=
    setIntegral_nonneg measurableSet_Icc (fun θ hθ => mul_nonneg (sq_nonneg _) (hσnn θ hθ))
  have hPWnn : 0 ≤ ∫ θ in Iθ, (W θ) ^ 2 * σ θ :=
    setIntegral_nonneg measurableSet_Icc (fun θ hθ => mul_nonneg (sq_nonneg _) (hσnn θ hθ))
  have hEUnn : 0 ≤ ∫ θ in Iθ, (deriv (deriv U) θ) ^ 2 * σ θ :=
    setIntegral_nonneg measurableSet_Icc (fun θ hθ => mul_nonneg (sq_nonneg _) (hσnn θ hθ))
  have hEWnn : 0 ≤ ∫ θ in Iθ, (deriv (deriv W) θ) ^ 2 * σ θ :=
    setIntegral_nonneg measurableSet_Icc (fun θ hθ => mul_nonneg (sq_nonneg _) (hσnn θ hθ))
  -- ## assembly
  have hcs : Real.sqrt ((∫ θ in Iθ, (U θ) ^ 2 * σ θ)
          * (∫ θ in Iθ, (deriv (deriv U) θ) ^ 2 * σ θ))
        + Real.sqrt ((∫ θ in Iθ, (W θ) ^ 2 * σ θ)
          * (∫ θ in Iθ, (deriv (deriv W) θ) ^ 2 * σ θ))
      ≤ Real.sqrt (((∫ θ in Iθ, (U θ) ^ 2 * σ θ) + (∫ θ in Iθ, (W θ) ^ 2 * σ θ))
          * ((∫ θ in Iθ, (deriv (deriv U) θ) ^ 2 * σ θ)
            + (∫ θ in Iθ, (deriv (deriv W) θ) ^ 2 * σ θ))) :=
    sqrt_add_le hPUnn hEUnn hPWnn hEWnn
  calc (∫ θ in Iθ, ‖deriv F θ‖ ^ 2 * σ θ)
      = (∫ θ in Iθ, (deriv U θ) ^ 2 * σ θ) + (∫ θ in Iθ, (deriv W θ) ^ 2 * σ θ) :=
        hsplit1.symm
    _ ≤ C * ((∫ θ in Iθ, (U θ) ^ 2 * σ θ)
            + Real.sqrt ((∫ θ in Iθ, (U θ) ^ 2 * σ θ)
                * (∫ θ in Iθ, (deriv (deriv U) θ) ^ 2 * σ θ)))
          + C * ((∫ θ in Iθ, (W θ) ^ 2 * σ θ)
            + Real.sqrt ((∫ θ in Iθ, (W θ) ^ 2 * σ θ)
                * (∫ θ in Iθ, (deriv (deriv W) θ) ^ 2 * σ θ))) := add_le_add hCU hCW
    _ = C * (((∫ θ in Iθ, (U θ) ^ 2 * σ θ) + (∫ θ in Iθ, (W θ) ^ 2 * σ θ))
            + (Real.sqrt ((∫ θ in Iθ, (U θ) ^ 2 * σ θ)
                  * (∫ θ in Iθ, (deriv (deriv U) θ) ^ 2 * σ θ))
                + Real.sqrt ((∫ θ in Iθ, (W θ) ^ 2 * σ θ)
                  * (∫ θ in Iθ, (deriv (deriv W) θ) ^ 2 * σ θ)))) := by ring
    _ ≤ C * (((∫ θ in Iθ, (U θ) ^ 2 * σ θ) + (∫ θ in Iθ, (W θ) ^ 2 * σ θ))
            + Real.sqrt (((∫ θ in Iθ, (U θ) ^ 2 * σ θ) + (∫ θ in Iθ, (W θ) ^ 2 * σ θ))
                * ((∫ θ in Iθ, (deriv (deriv U) θ) ^ 2 * σ θ)
                  + (∫ θ in Iθ, (deriv (deriv W) θ) ^ 2 * σ θ)))) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hcs) (le_of_lt hCpos)
    _ = C * ((∫ θ in Iθ, ‖F θ‖ ^ 2 * σ θ)
            + Real.sqrt ((∫ θ in Iθ, ‖F θ‖ ^ 2 * σ θ)
                * (∫ θ in Iθ, ‖deriv (deriv F) θ‖ ^ 2 * σ θ))) := by
        rw [hsplit0, hsplit2]

end

end Work.FTS.EllSol.Trunc
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.identity_defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeI1Fts

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-! ## The slots as operators -/






/-! ## `SmoothOpen` for the slots -/


theorem SmoothOpen.pthIter {F : ℝ → ℝ → ℝ} (hF : SmoothOpen F) (i : ℕ) :
    SmoothOpen (Work.Spaces.pthIter i F) := by
  induction i with
  | zero => simpa using hF
  | succ i ih =>
      rw [Work.Spaces.pthIter_succ]
      exact SmoothOpen.pth ih

theorem smoothOpen_U {u : ℝ → ℝ → ℝ} (hS : SmoothOpen u) : SmoothOpen (U u) :=
  hS.Dz










/-! ## Slice derivatives (Clairaut) -/

theorem contDiffAt_uncurry {u : ℝ → ℝ → ℝ} (hS : SmoothOpen u) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Iθo) (n : ℕ) : ContDiffAt ℝ n (Function.uncurry u) (z, θ) :=
  (hS.forall n).contDiffAt
    (isOpen_Q0.mem_nhds (mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩))



theorem smoothOrder_le_one : (1 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
  rw [Work.Stability.smoothOrder]
  exact WithTop.coe_le_coe.mpr le_top

/-- The `θ`-slice of `U u` is `C^∞` on the open interval. -/
theorem contDiffOn_slice_U {u : ℝ → ℝ → ℝ} (hS : SmoothOpen u) {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => U u z θ) Iθo :=
  (smoothOpen_U hS).curry_θ hz


theorem contDiffOn_slice_U_one {u : ℝ → ℝ → ℝ} (hS : SmoothOpen u) {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ 1 (fun θ => U u z θ) Iθo :=
  (contDiffOn_slice_U hS hz).of_le smoothOrder_le_one


/-! ## The angular weights -/





/-! ## The pointwise `θ`-identity -/



/-! ## The `ℋ⁰`-integrand on `Iθ` and joint integrability -/

/-- On `Iθ`, the level-`0` integrand is `w(z)²·(f(z,θ)²·σ(θ))`. -/
theorem hk_zero_eq (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (Work.Spaces.w z) ^ 2 * ((f z θ) ^ 2 * sigE θ) :=
  Work.FTS.EllipticEst.Dispatch.HkIntegrand_zero_D α f hθ



/-! ## The iterated integral over the open quadrant

`II g = ∫_z ∫_θ g` over `(0,∞) × (0,π/2)`, the form in which the target `identity` is
stated.  Everything below is expressed through `II` so that the assembly does not have to
manipulate the two integrations separately. -/

/-- `II g = ∫_{z>0} ∫_{0<θ<π/2} g z θ`. -/
def II (g : ℝ → ℝ → ℝ) : ℝ := ∫ z in Set.Ioi 0, ∫ θ in Iθo, g z θ




/-- The product measure `dz dθ` on `(0,∞) × (0,π/2)`. -/
abbrev nuQ : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict (Set.Ioi 0)).prod
    (MeasureTheory.volume.restrict Iθo)




end Work.FTS.EllipticEst.AeI1Fts
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Deleg.mixedHdom =====
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

/-- The `θ`-integral of `|σ θ · V z θ²|` equals the `θ`-integral of `σ θ · V z θ²` (the
integrand is nonnegative on `(0,π/2)`). -/
private theorem abs_setIntegral_eq_of_nonneg {V : ℝ → ℝ} (hV : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
    0 ≤ Work.FTS.EllipticEst.AeColl.sigθ θ * V θ) (z : ℝ) :
    (∫ θ, |Work.FTS.EllipticEst.AeColl.sigθ θ * V θ|
        ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ * V θ := by
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
  rw [abs_of_nonneg (hV θ hθ)]

/-- **Domination for the `V`-slot** (`Ptr`, `Col`). -/
theorem hdom_Vz {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hM : MixedHon u) (n : ℕ) :
    Integrable (fun z => |Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z| *
      ∫ θ, |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2|
        ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hdom0 : Integrable (fun z => Work.FTS.EllipticEst.AeColl.wtB n
      * ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2
          * Work.FTS.EllipticEst.AeColl.sigθ θ) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    integrableOn_marginal_Vz_of_MixedHon hM n
  have hmarg : AEStronglyMeasurable (fun z => ∫ θ,
      |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2|
        ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    aesm_marginal (aesm_abs (aesm_joint_Vz hA))
  refine Integrable.mono' hdom0 ((aesm_abs (aesm_cut_mul_wt n)).mul hmarg) ?_
  filter_upwards [hM.1, ae_restrict_mem measurableSet_Ioi] with z hzint hz
  have hIθ : Integrable (fun θ => Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2
      * Work.FTS.EllipticEst.AeColl.sigθ θ) (volume.restrict Work.Spaces.Iθ) := hzint
  have hnnθ : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ =>
      Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2 * Work.FTS.EllipticEst.AeColl.sigθ θ) :=
    ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (sigθ_nonneg_of_mem_Iθ hθ))
  have hmono : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2 * Work.FTS.EllipticEst.AeColl.sigθ θ)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2
        * Work.FTS.EllipticEst.AeColl.sigθ θ :=
    setIntegral_mono_set hIθ hnnθ (Filter.Eventually.of_forall (fun θ hθ =>
      show θ ∈ Work.Spaces.Iθ from ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩))
  have hIabs : |∫ θ, |Work.FTS.EllipticEst.AeColl.sigθ θ
        * Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2|
        ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))|
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ
        * Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2 := by
    rw [abs_of_nonneg (integral_nonneg (fun θ => abs_nonneg _))]
    exact abs_setIntegral_eq_of_nonneg (fun θ hθ => mul_nonneg
      (sigθ_nonneg_of_mem_Iθ (show θ ∈ Work.Spaces.Iθ from ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩))
      (sq_nonneg _)) z
  have hnnI : 0 ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2 :=
    setIntegral_nonneg measurableSet_Ioo (fun θ hθ => mul_nonneg
      (sigθ_nonneg_of_mem_Iθ (show θ ∈ Work.Spaces.Iθ from ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩))
      (sq_nonneg _))
  rw [Real.norm_eq_abs, abs_mul, abs_abs, hIabs]
  calc |Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z|
        * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ
            * Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2)
      ≤ Work.FTS.EllipticEst.AeColl.wtB n
          * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ
              * Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2) :=
        mul_le_mul_of_nonneg_right (Work.FTS.EllipticEst.AeColl.cut_mul_wt_bdd n z) hnnI
    _ = Work.FTS.EllipticEst.AeColl.wtB n
          * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2
                * Work.FTS.EllipticEst.AeColl.sigθ θ) := by
        congr 1
        refine integral_congr_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ _
        ring
    _ ≤ Work.FTS.EllipticEst.AeColl.wtB n
          * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2
              * Work.FTS.EllipticEst.AeColl.sigθ θ) :=
        mul_le_mul_of_nonneg_left hmono (wtB_nonneg n)

/-- **Domination for the `U`-slot** (`Atr`). -/
theorem hdom_Uz {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)) (n : ℕ) :
    Integrable (fun z => |Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z| *
      ∫ θ, |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2|
        ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hdom0 : Integrable (fun z => Work.FTS.EllipticEst.AeColl.wtB n
      * ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2
          * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (integrableOn_marginal_Ioi_of_HkMem α hU).const_mul _
  have hmarg : AEStronglyMeasurable (fun z => ∫ θ,
      |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2|
        ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    aesm_marginal (aesm_abs (aesm_joint_Uz hA))
  refine Integrable.mono' hdom0 ((aesm_abs (aesm_cut_mul_wt n)).mul hmarg) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  have hIθ : Integrable (fun θ => Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2
      * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)
      (volume.restrict Work.Spaces.Iθ) :=
    integrableOn_sig_sq_wt_of_HkMem α hU (mem_Iz_of_pos hz)
  have hIθ' : Integrable (fun θ => Work.FTS.EllipticEst.AeColl.sigθ θ
      * Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2) (volume.restrict Work.Spaces.Iθ) :=
    integrableOn_sig_mul_sq_Iθ_of_HkMem α hU hz
  have hIabs : |∫ θ, |Work.FTS.EllipticEst.AeColl.sigθ θ
        * Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2|
        ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))|
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ
        * Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2 := by
    rw [abs_of_nonneg (integral_nonneg (fun θ => abs_nonneg _))]
    exact abs_setIntegral_eq_of_nonneg (fun θ hθ => mul_nonneg
      (sigθ_nonneg_of_mem_Iθ (show θ ∈ Work.Spaces.Iθ from ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩))
      (sq_nonneg _)) z
  have hnnI : 0 ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2 :=
    setIntegral_nonneg measurableSet_Ioo (fun θ hθ => mul_nonneg
      (sigθ_nonneg_of_mem_Iθ (show θ ∈ Work.Spaces.Iθ from ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩))
      (sq_nonneg _))
  -- the pointwise comparison `σ U² ≤ U² wt σ` on the open interval
  have hpt : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ
        * Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2)
      ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2
          * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ := by
    refine integral_mono_of_nonneg ?_ (MeasureTheory.IntegrableOn.mono_set hIθ (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)) ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact mul_nonneg
        (sigθ_nonneg_of_mem_Iθ (show θ ∈ Work.Spaces.Iθ from ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩))
        (sq_nonneg _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hs0 := sigθ_nonneg_of_mem_Iθ
        (show θ ∈ Work.Spaces.Iθ from ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
      have hw1 := one_le_wt_of_pos hz
      have h1 : Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2
          ≤ Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z := by
        simpa using mul_le_mul_of_nonneg_left hw1
          (sq_nonneg (Work.FTS.EllipticEst.AeColl.Uz u z θ))
      calc Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2
          = Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2
              * Work.FTS.EllipticEst.AeColl.sigθ θ := by ring
        _ ≤ (Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z)
              * Work.FTS.EllipticEst.AeColl.sigθ θ := mul_le_mul_of_nonneg_right h1 hs0
        _ = Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
              * Work.FTS.EllipticEst.AeColl.sigθ θ := by ring
  have hmono : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
          * Work.FTS.EllipticEst.AeColl.sigθ θ)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2
        * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ :=
    setIntegral_mono_set hIθ (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
      mul_nonneg (mul_nonneg (sq_nonneg _) (wt_nonneg z)) (sigθ_nonneg_of_mem_Iθ hθ)))
      (Filter.Eventually.of_forall (fun θ hθ =>
        show θ ∈ Work.Spaces.Iθ from ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩))
  rw [Real.norm_eq_abs, abs_mul, abs_abs, hIabs]
  calc |Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z|
        * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ
            * Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2)
      ≤ Work.FTS.EllipticEst.AeColl.wtB n
          * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.AeColl.sigθ θ
              * Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2) :=
        mul_le_mul_of_nonneg_right (Work.FTS.EllipticEst.AeColl.cut_mul_wt_bdd n z) hnnI
    _ ≤ Work.FTS.EllipticEst.AeColl.wtB n
          * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2
              * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ) :=
        mul_le_mul_of_nonneg_left (le_trans hpt hmono) (wtB_nonneg n)

/-- **Domination for the mixed radial/angular slot** (`Dtr`). -/
theorem hdom_AzB {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (n : ℕ) :
    Integrable (fun z => |Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z| *
      ∫ θ, |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Az u z θ
        * Work.Spaces.pthIter 2 u z θ|
        ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hAz : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.AeColl.Az u z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
        * Work.FTS.EllipticEst.AeColl.sigθ θ) (Set.Ioi (0 : ℝ)) :=
    integrableOn_marginal_Ioi_of_HkMem α (Work.FTS.EllipticEst.H2W.Ae.AeData.memRad2 hA)
  have hB : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.pthIter 2 u z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
        * Work.FTS.EllipticEst.AeColl.sigθ θ) (Set.Ioi (0 : ℝ)) :=
    integrableOn_marginal_Ioi_of_HkMem α (Work.FTS.EllipticEst.H2W.Ae.AeData.memAng2 hA)
  have hdom0 : Integrable (fun z => Work.FTS.EllipticEst.AeColl.wtB n *
      ((∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.Az u z θ ^ 2
            * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)
        + (∫ θ in Work.Spaces.Iθ, Work.Spaces.pthIter 2 u z θ ^ 2
            * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (hAz.add hB).const_mul _
  have hmarg : AEStronglyMeasurable (fun z => ∫ θ,
      |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Az u z θ
        * Work.Spaces.pthIter 2 u z θ|
        ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    aesm_marginal (aesm_abs (aesm_prod_of_continuousOn_Q0 (continuousOn_joint_AzB hA)))
  refine Integrable.mono' hdom0 ((aesm_abs (aesm_cut_mul_wt n)).mul hmarg) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  have hIabs : |∫ θ, |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Az u z θ
        * Work.Spaces.pthIter 2 u z θ|
        ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))|
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), |Work.FTS.EllipticEst.AeColl.sigθ θ
        * Work.FTS.EllipticEst.AeColl.Az u z θ * Work.Spaces.pthIter 2 u z θ| := by
    rw [abs_of_nonneg (integral_nonneg (fun θ => abs_nonneg _))]
  have hnnI : 0 ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Az u z θ
        * Work.Spaces.pthIter 2 u z θ| :=
    setIntegral_nonneg measurableSet_Ioo (fun θ _ => abs_nonneg _)
  rw [Real.norm_eq_abs, abs_mul, abs_abs]
  calc |Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z|
        * |∫ θ, |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Az u z θ
            * Work.Spaces.pthIter 2 u z θ|
            ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))|
      = |Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AeColl.wt z|
          * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Az u z θ
                * Work.Spaces.pthIter 2 u z θ|) := by rw [hIabs]
    _ ≤ Work.FTS.EllipticEst.AeColl.wtB n
          * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Az u z θ
                * Work.Spaces.pthIter 2 u z θ|) :=
        mul_le_mul_of_nonneg_right (Work.FTS.EllipticEst.AeColl.cut_mul_wt_bdd n z) hnnI
    _ ≤ Work.FTS.EllipticEst.AeColl.wtB n *
          ((∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.Az u z θ ^ 2
              * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.pthIter 2 u z θ ^ 2
              * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)) :=
        mul_le_mul_of_nonneg_left
          (abs_mixed_slice_le α (Work.FTS.EllipticEst.H2W.Ae.AeData.memRad2 hA)
            (Work.FTS.EllipticEst.H2W.Ae.AeData.memAng2 hA) hz) (wtB_nonneg n)

/-- **Domination for the transfer slot** (`Trtr`). -/
theorem hdom_UzB {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)) (n : ℕ) :
    Integrable (fun z => |deriv (fun z' => Work.FTS.EllipticEst.cut n z'
        * Work.FTS.EllipticEst.AeColl.wt z' * z' ^ 2) z / z| *
      ∫ θ, |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ
        * Work.Spaces.pthIter 2 u z θ|
        ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  obtain ⟨C, hCpos, hCbd⟩ := trtr_coef_bound n
  have hU' : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
        * Work.FTS.EllipticEst.AeColl.sigθ θ) (Set.Ioi (0 : ℝ)) :=
    integrableOn_marginal_Ioi_of_HkMem α hU
  have hB : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.pthIter 2 u z θ ^ 2 * Work.FTS.EllipticEst.AeColl.wt z
        * Work.FTS.EllipticEst.AeColl.sigθ θ) (Set.Ioi (0 : ℝ)) :=
    integrableOn_marginal_Ioi_of_HkMem α (Work.FTS.EllipticEst.H2W.Ae.AeData.memAng2 hA)
  have hdom0 : Integrable (fun z => C *
      ((∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2
            * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)
        + (∫ θ in Work.Spaces.Iθ, Work.Spaces.pthIter 2 u z θ ^ 2
            * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (hU'.add hB).const_mul _
  have hmarg : AEStronglyMeasurable (fun z => ∫ θ,
      |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ
        * Work.Spaces.pthIter 2 u z θ|
        ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    aesm_marginal (aesm_abs (aesm_prod_of_continuousOn_Q0 (continuousOn_joint_UzB hA)))
  refine Integrable.mono' hdom0 ((aesm_abs (aesm_trtr_coef n)).mul hmarg) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  have hIabs : |∫ θ, |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ
        * Work.Spaces.pthIter 2 u z θ|
        ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))|
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), |Work.FTS.EllipticEst.AeColl.sigθ θ
        * Work.FTS.EllipticEst.AeColl.Uz u z θ * Work.Spaces.pthIter 2 u z θ| := by
    rw [abs_of_nonneg (integral_nonneg (fun θ => abs_nonneg _))]
  have hnnI : 0 ≤ ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ
        * Work.Spaces.pthIter 2 u z θ| :=
    setIntegral_nonneg measurableSet_Ioo (fun θ _ => abs_nonneg _)
  rw [Real.norm_eq_abs, abs_mul, abs_abs, hIabs]
  calc |deriv (fun z' => Work.FTS.EllipticEst.cut n z' * Work.FTS.EllipticEst.AeColl.wt z'
          * z' ^ 2) z / z|
        * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ
              * Work.Spaces.pthIter 2 u z θ|)
      ≤ (C * Work.FTS.EllipticEst.AeColl.wt z)
          * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ
                * Work.Spaces.pthIter 2 u z θ|) :=
        mul_le_mul_of_nonneg_right (hCbd z hz) hnnI
    _ = C * (Work.FTS.EllipticEst.AeColl.wt z
          * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              |Work.FTS.EllipticEst.AeColl.sigθ θ * Work.FTS.EllipticEst.AeColl.Uz u z θ
                * Work.Spaces.pthIter 2 u z θ|)) := by ring
    _ ≤ C * ((∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.Uz u z θ ^ 2
              * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)
            + (∫ θ in Work.Spaces.Iθ, Work.Spaces.pthIter 2 u z θ ^ 2
              * Work.FTS.EllipticEst.AeColl.wt z * Work.FTS.EllipticEst.AeColl.sigθ θ)) :=
        mul_le_mul_of_nonneg_left
          (abs_mixed_slice_wt_le α hU (Work.FTS.EllipticEst.H2W.Ae.AeData.memAng2 hA) hz)
          (le_of_lt hCpos)

end

end Work.FTS.EllipticEst.Deleg
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Dispatch.step3AeD =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Dispatch

/-- **The reduction of Step 3 to its four inputs.**  From

* `hu` — `HkMem α 0 u`,
* `hd` — `HkMem α 0 (z∂_zu)`,
* `ha` — `HkMem α 0 (∂_θ(tan θ·u))`,
* `hb` — the `I₄`-estimate `‖∂_θ(tan θ·u)‖_ρ ≤ CU(‖u‖_ρ + ‖∂_θθu‖_ρ)`,

one obtains the target estimate with the explicit constant `√5 (11 + CU)`.  This is the
Dispatch-cone form of the assembly: the analytic inputs are exactly the four lemmas listed in
the module docstring. -/
theorem step3AeD_of_pieces (CU : ℝ) (hCU : 0 < CU)
    (hu : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.HkMem α 0 u)
    (hd : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u))
    (ha : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.ang1 u))
    (hb : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Real.sqrt (Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.ang1 u))
        ≤ CU * (Real.sqrt (Work.Spaces.HkSq α 0 u)
            + Real.sqrt (Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.ang2 u)))) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
        Work.FTS.EllipticEst.H2W.Ae.nrm α
            (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))
          ≤ C * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
            + α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u)
            + Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.ang2 u)
            + Work.FTS.EllipticEst.H2W.Ae.nrm α u) :=
  Work.FTS.EllipticEst.H2W.AngBW.S3.step3Ae_of_pieces CU hCU hu hd ha hb

/-- **The `HkMem` honesty of `∂_θ(tan θ·u)` in the Dispatch cone**: from the honesty of `u` and
of `z∂_zu` (which are the two Dispatch inputs `Dispatch.hkMem_uM` and
`Dispatch.hkMem_gradUD`), the rearrangement of the equation and the five-term Cauchy–Schwarz
domination give `HkMem α 0 (ang1 u)`. -/
theorem hkMem_ang1D (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.ang1 u) :=
  Work.FTS.EllipticEst.H2W.Ae.hkMem_ang1 α u G h (hkMem_uM α u G h) (hkMem_gradUD α u G h)

/-- **The `I₄`-estimate in the Dispatch cone**: with the honesty inputs supplied by
`hkMem_uM`, `AeData.memAng2` and `hkMem_ang1D`, the `I₄`-estimate of `H2W.AngBW.S3.ang1_bound`
applies to every `AeData` datum. -/
theorem ang1_boundD : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Real.sqrt (Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.ang1 u))
        ≤ C * (Real.sqrt (Work.Spaces.HkSq α 0 u)
            + Real.sqrt (Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.ang2 u))) := by
  obtain ⟨C, hC, hCb⟩ := Work.FTS.EllipticEst.H2W.AngBW.S3.ang1_bound
  exact ⟨C, hC, fun α u G h => hCb α u (Work.FTS.EllipticEst.H2W.Ae.AeData.smooth h)
    (Work.FTS.EllipticEst.H2W.Ae.AeData.dirZero h) (Work.FTS.EllipticEst.H2W.Ae.AeData.dirPi h)
    (hkMem_uM α u G h) (Work.FTS.EllipticEst.H2W.Ae.AeData.memAng2 h) (hkMem_ang1D α u G h)⟩

theorem step3AeD : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.FTS.EllipticEst.H2W.Ae.nrm α (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))
        ≤ C * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
          + α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u)
          + Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.ang2 u)
          + Work.FTS.EllipticEst.H2W.Ae.nrm α u) := by
  obtain ⟨CU, hCU, hCUb⟩ := ang1_boundD
  refine step3AeD_of_pieces CU hCU
    (fun α u G h => hkMem_uM α u G h)
    (fun α u G h => hkMem_gradUD α u G h)
    (fun α u G h => hkMem_ang1D α u G h) ?_
  intro α u G h
  exact hCUb α u G h

end Work.FTS.EllipticEst.Dispatch
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Final.Rep.H2W.Step5.s20Aesm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Final.Rep.H2W.Step5.s20_Fslot =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.ESV.aeUHkAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AngAWeak/aeUHkAux` — auxiliary lemmas for `AngAWeak/aeUHk`

Sorry-free helpers for the level-`0` `ρ`-mass estimate in the a.e. class `AeData`
(see `AngAWeak/NOTES_aeUHk.md`):

* `HkIntegrand_zero_eq_w_esv` — the level-`0` integrand on `Iθ`;
* `hkMemU_slices` — the first conjunct of `HkMem α 0 u`, from `aeSliceBdd`;
* `integrableOn_pth_sq_of_AeData_esv` — `(∂_θu z ·)² ∈ L¹(Iθ)` for every `z > 0`;
* `YslicePlain`, `Uslice` — the two slice energies.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false

/-- On `Iθ` the level-`0` `HkIntegrand` is the single weighted square `g² w² σ`. -/
theorem HkIntegrand_zero_eq_w_esv (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  have hkey : Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    simp [Work.Spaces.HkIntegrand]
  rw [hkey]
  exact Work.FTS.EllipticEst.mul_w_sin_rpow_sq (g z θ) (Work.Spaces.w z) hθ




/-- **The `θ`-derivative of a slice is square-integrable for every `z > 0`.**  From
`HkMem α 0 (∂_θθu)` the slice lemma `slice_bdd_of_sq_mul_sEta` bounds `u z θ` and `∂_θu z θ` on
the open interval, whence `(∂_θu z ·)²` is integrable on `Iθ`. -/
theorem integrableOn_pth_sq_of_AeData_esv (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    ∀ z : ℝ, 0 < z →
      IntegrableOn (fun θ => (Work.Spaces.pth u z θ) ^ 2) Work.Spaces.Iθ := by
  intro z hz
  have hslice : ContDiffOn ℝ 2 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have hmap : Set.MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun θ hθ => ⟨hz, hθ⟩
    exact ((h.smooth 2).comp (by fun_prop) hmap)
  have hint : IntegrableOn
      (fun θ : ℝ => (deriv (fun t : ℝ => deriv (fun θ' : ℝ => u z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
    have h1 := h.memAng2.1 z hzI
    have h2 : IntegrableOn
        (fun θ => (Work.Spaces.pthIter 2 u z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
      h1.congr_fun (fun θ hθ => HkIntegrand_zero_eq_w_esv α (Work.Spaces.pthIter 2 u) z hθ)
        measurableSet_Icc
    have hw' : Work.Spaces.w z ≠ 0 := by
      rw [Work.Spaces.w]
      exact div_ne_zero (pow_ne_zero _ (by linarith)) (pow_ne_zero _ (ne_of_gt hz))
    have h3 := h2.mul_const ((Work.Spaces.w z) ^ 2)⁻¹
    refine h3.congr (Filter.Eventually.of_forall (fun θ => ?_))
    show ((Work.Spaces.pthIter 2 u z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.sEta θ) * ((Work.Spaces.w z) ^ 2)⁻¹
        = (deriv (fun t : ℝ => deriv (fun θ' : ℝ => u z θ') t) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ
    have hpth2 : Work.Spaces.pthIter 2 u z θ
        = deriv (fun t : ℝ => deriv (fun θ' : ℝ => u z θ') t) θ := by
      simp only [show (2 : ℕ) = 1 + 1 from rfl, Work.Spaces.pthIter_succ,
        Work.Spaces.pthIter_zero, Work.Spaces.pth]
    rw [hpth2]
    field_simp
  obtain ⟨C, hC0, hC⟩ :=
    Work.FTS.EllipticEst.Honest.slice_bdd_of_sq_mul_sEta hslice hint
  -- `Iθ` and the open interval differ by the null set `{0, π/2}`: integrate there.
  have hpair : volume ({(0 : ℝ), Real.pi / 2} : Set ℝ) = 0 :=
    Set.Finite.measure_zero (by simp) volume
  have hpairab : ∀ᵐ x : ℝ, x ∉ ({(0 : ℝ), Real.pi / 2} : Set ℝ) := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hpair
  have hst : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    filter_upwards [hpairab] with x hx
    refine propext ⟨?_, ?_⟩
    · intro h
      rw [Work.Spaces.Iθ, Set.mem_Icc] at h
      rw [Set.mem_Ioo]
      exact ⟨lt_of_le_of_ne h.1 (fun hc => hx (Or.inl hc.symm)),
             lt_of_le_of_ne h.2 (fun hc => hx (Or.inr hc))⟩
    · intro h
      rw [Work.Spaces.Iθ, Set.mem_Icc]
      rw [Set.mem_Ioo] at h
      exact ⟨le_of_lt h.1, le_of_lt h.2⟩
  have hms : volume.restrict Work.Spaces.Iθ
      = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Measure.restrict_congr_set hst
  rw [IntegrableOn, hms]
  refine IntegrableOn.of_bound (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top)
    ((measurable_deriv (fun θ' : ℝ => u z θ')).pow_const 2).aestronglyMeasurable
    (C ^ 2) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  have hb := (hC θ hθ).2
  rw [Real.norm_of_nonneg (sq_nonneg _), show Work.Spaces.pth u z θ
    = deriv (fun θ' : ℝ => u z θ') θ from rfl, ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) hb 2
end Work.FTS.EllipticEst.AngAWeak
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.ESV.easySlotsAe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project.

# `H2W/easySlotsAe` — the reduction of `easySlots` to the level-`0` estimate in the `AeData` class

The target `Work.FTS.EllipticEst.H2W.easySlots` is

```
α⁴ (|D_θ A · Wt|²_{L²} + |D_θ² A · Wt|²_{L²}) ≤ C |F|²_{ℋ²},     A = z²∂_z²Ψ,
```

for every datum of the weak class `TT.EllWeakPos α 2 F Ψ` and `0 < α ≤ 1/4`.

## What this file proves

* `AeData_DzIter` — the `j`-th radial derivative (`j ≤ 2`) of a datum of the weak class
  `EllWeakPos α 2` *is* a datum of the almost-everywhere class `Ae.AeData` of the level-`0`
  estimate: the equation is `TT.bslOp_DzIter_eq`, the Dirichlet data `TT.DzIter_zero_at_*`, the
  smoothness `SmoothOpen.DzIter`, the three `HkMem`-certificates `HkMem_zero_slices`, the
  `Ψ`-moments `Fstar_DzIter_le_Psi` (pointwise), and the `F`-moments
  `remov.Fstar_DzIter_one_F_ge_two` (`j = 1`, pointwise) resp. `Fstar_DzIter_two_F_ae`
  (`j = 2`, almost everywhere — the *pointwise* statement at `j = 2` is not derivable from the
  class, see `H2W/Fstar_DzIter_two_F.lean`).

* `easySlots_slot_bounds` — given the level-`0` estimate in the class `Ae.AeData`
  (`hL0`, the conclusion of `Ae.Assembly.level0Ae_of`), the two quantities of the reduction
  `α⁴·HkSq α 0 A` and `α⁴·HkSq α 0 (∂_θ²A)` are bounded by `HkSq α 2 F`.

* `easySlots_of_level0Ae` — the target, from `hL0` and the (proved, `easySlotsAssembly`) slicewise
  assembly `esl_lhs_bound`.

## Why not the route through the `A`-datum

The earlier reduction in `H2W/easySlotsAssembly` consumed the level-`0` estimate for the
*`A`-datum* `u = A = z²∂_z²Ψ` with the source `G = z²∂_z²F`, i.e.

  `α⁴ HkSq α 0 A + HkSq α 0 (∂_θ²A) ≤ C HkSq α 0 (z²∂_z²F)`.                      (L0A)

That statement is *not* a consequence of the weak class: its right-hand side misses the angular
slots of the source.  In the exactly solvable family `Ψ = ψ(z)φ(θ)`, `Lzero φ = μ φ`, with source
`F = χ(z)φ(θ)` (so `ψ` solves `μψ − α²ψ'' − α(5+α)ψ' = χ`), both sides factor, and (L0A) becomes

  `(α⁴ + B_θ/A_θ) · ∫(z²ψ'')²w² ≤ C · ∫(z²χ'')²w²`,   `B_θ = ∫φ''²σ`, `A_θ = ∫φ²σ`,

in which the angular factor `B_θ/A_θ` on the left has no counterpart on the right; the `θ`-slots
of `F` that would supply it live in `HkSq α 2 F`, not in `HkSq α 0 (z²∂_z²F)`.  The reduction
below therefore uses the *radially shifted* data `(D_z^j F, D_z^j Ψ)`, whose sources do carry
them.
-/

namespace Work.FTS.EllipticEst.H2W

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary integrand facts -/

/-- The level-`0` `HkIntegrand` is the square of the single weighted slot. -/
theorem hkIntegrand_zero_eq_Wg (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.pzIter_zero, Finset.range_one,
    Finset.sum_singleton]
  norm_num

/-- **Subadditivity of `HkSq α 0`** in the junk-tolerant form: for honest `a`, `b`,
`HkSq α 0 (a - b) ≤ 2 HkSq α 0 a + 2 HkSq α 0 b`.  The pointwise input is the algebraic
`(x - y)² ≤ 2x² + 2y²` applied to `x = a·Wg`, `y = b·Wg`; the honesty of `a` and `b` makes the
majorant an honest integral, so no case distinction is needed. -/
theorem HkSq_zero_sub_le (α : ℝ) (a b : ℝ → ℝ → ℝ)
    (ha : Work.Spaces.HkMem α 0 a) (hb : Work.Spaces.HkMem α 0 b) :
    Work.Spaces.HkSq α 0 (fun z θ => a z θ - b z θ)
      ≤ 2 * Work.Spaces.HkSq α 0 a + 2 * Work.Spaces.HkSq α 0 b := by
  have hpt : ∀ z θ, Work.Spaces.HkIntegrand α 0 (fun z θ => a z θ - b z θ) z θ
      ≤ 2 * Work.Spaces.HkIntegrand α 0 a z θ + 2 * Work.Spaces.HkIntegrand α 0 b z θ := by
    intro z θ
    rw [hkIntegrand_zero_eq_Wg, hkIntegrand_zero_eq_Wg, hkIntegrand_zero_eq_Wg]
    have h : ((a z θ - b z θ) * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
        = ((a z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)))
            - (b z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)))) ^ 2 := by
      ring
    rw [h]
    nlinarith [sq_nonneg ((a z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)))
      + (b z θ * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))))]
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (fun z θ => a z θ - b z θ) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, (2 * Work.Spaces.HkIntegrand α 0 a z θ
            + 2 * Work.Spaces.HkIntegrand α 0 b z θ) := by
    intro z hz
    refine MeasureTheory.integral_mono_of_nonneg (μ := volume.restrict Work.Spaces.Iθ)
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)
      (((ha.1 z hz).const_mul 2).add ((hb.1 z hz).const_mul 2))
      (Eventually.of_forall fun θ => hpt z θ)
  have hmajz : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, (2 * Work.Spaces.HkIntegrand α 0 a z θ
        + 2 * Work.Spaces.HkIntegrand α 0 b z θ)) Work.Spaces.Iz := by
    have h : MeasureTheory.IntegrableOn (fun z =>
        2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 a z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 b z θ))
        Work.Spaces.Iz := (ha.2.const_mul 2).add (hb.2.const_mul 2)
    refine h.congr_fun (fun z hz => ?_) measurableSet_Ici
    exact ((MeasureTheory.integral_add ((ha.1 z hz).const_mul 2)
      ((hb.1 z hz).const_mul 2)).trans
        (by rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul])).symm
  have hval : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (2 * Work.Spaces.HkIntegrand α 0 a z θ + 2 * Work.Spaces.HkIntegrand α 0 b z θ))
      = 2 * Work.Spaces.HkSq α 0 a + 2 * Work.Spaces.HkSq α 0 b := by
    rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
    rw [show (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (2 * Work.Spaces.HkIntegrand α 0 a z θ + 2 * Work.Spaces.HkIntegrand α 0 b z θ))
        = ∫ z in Work.Spaces.Iz,
            (2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 a z θ)
              + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 b z θ)) from
      setIntegral_congr_fun measurableSet_Ici (fun z hz => by
        rw [MeasureTheory.integral_add ((ha.1 z hz).const_mul 2) ((hb.1 z hz).const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul])]
    rw [MeasureTheory.integral_add (ha.2.const_mul 2) (hb.2.const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  refine (MeasureTheory.integral_mono_of_nonneg (μ := volume.restrict Work.Spaces.Iz)
    (Eventually.of_forall fun z => setIntegral_nonneg measurableSet_Icc
      (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ))
    hmajz (ae_restrict_of_forall_mem measurableSet_Ici hslice)).trans (le_of_eq hval)

/-- **The Clairaut identity for the twisted datum.**  On the open quadrant, the iterated angular
second derivative of `A = z²∂_z²Ψ` is the twisted datum of the angular second derivative,
`∂_θ²(z²∂_z²Ψ) = z²∂_z²(∂_θ²Ψ)`. -/
theorem pthIter_two_zsq_eq_rad2 (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      = Work.FTS.EllipticEst.H2W.Ae.rad2 (Work.Spaces.pthIter 2 Ψ) z θ := by
  -- `∂_θ² (z² · g) = z² · ∂_θ² g` at a point
  have hmul : ∀ (g : ℝ → ℝ → ℝ),
      Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * g z θ) z θ
        = z ^ 2 * Work.Spaces.pthIter 2 g z θ := by
    intro g
    have h1 : (fun z θ => z ^ 2 * g z θ) = (fun z θ => z * (z * g z θ)) := by
      funext z θ; ring
    rw [h1, pthIter_const_mul_fst 2 (fun z θ => z * g z θ),
      pthIter_const_mul_fst 2 g]
    ring
  rw [hmul (Work.Spaces.pzIter 2 Ψ)]
  -- `pzIter 2 (pthIter 2 Ψ) = pthIter 2 (pzIter 2 Ψ)` on the quadrant
  have hV : (z, θ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := ⟨hz, hθ⟩
  have hcc : Work.Spaces.pzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ
      = Work.Spaces.pthIter 2 (Work.Spaces.pzIter 2 Ψ) z θ := by
    have h1 : Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ
        = Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) z θ :=
      pz_pthIter_two_eqOn hΨ hV
    have h2 : Work.Spaces.pz (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ)) z θ
        = Work.Spaces.pthIter 2 (Work.Spaces.pzIter 2 Ψ) z θ :=
      pz_pthIter_two_eqOn hΨ.pz hV
    have h3 : Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ)) z θ
        = Work.Spaces.pz (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ)) z θ :=
      Work.Spaces.pz_congr_of_isOpen (isOpen_Ioi.prod isOpen_Ioo)
        (fun p hp => pz_pthIter_two_eqOn hΨ hp) hV
    show Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ)) z θ = _
    rw [h3, h2]
  rw [← hcc]
  rfl

/-! ## The almost-everywhere class for the radially shifted data -/


/-! ## The two slots from the level-`0` estimate -/


/-! ## The target -/


/-! ## The reduction to `Ae.Step1` and `Ae.Step2` alone

`Step3` of `Ae.Assembly` is *not* needed: the two quantities of the reduction are bounded by
`HkSq α 2 F` using the first-order radial estimate (`Step1`, applied to the base datum and to its
first radial derivative) together with the angular estimate (`Step2`) applied to the base and the
once/twice radially shifted data. -/




end

end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.PsiSlices.Reductions =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.PsiSlices.SlotReduction =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `H2W.PsiSlices.slotReduction` — the target, reduced to the *slot* honesty of the slices

The target of this directory (`Work.FTS.EllipticEst.H2W.PsiSlices.pzIterSliceIntegrable`) is: for a
datum of the weak class `WeakPos2 α F Ψ` and a.e. `z > 0`, the slices `∂_z^mΨ(z,·)`, `m ≤ 4`, are
integrable against `sinθcos²θ` on `Iθ`.

This module records the sharpest available *reduction* of it: **the target follows from the
"slot" honesty of the slices**, namely

* `HkMem α 0 (∂_θ²(∂_z^jΨ))` for `j ≤ 2` (the second angular derivative of the first three
  slices — `aeSliceHonestOfSlots` converts these into the slices themselves, using
  `Honest.slice_bdd_of_sq_mul_sEta`: `∫(u'')²σ < ∞ ⟹ u, u'` bounded, `σ = sin(2θ)^{-η}`), and
* `HkMem α 0 (z²∂_z³Ψ)`, `HkMem α 0 (z²∂_z⁴Ψ)` (the `z²`-weighted square of the two top slices,
  which the AM–GM `abs_mul_sinCos2_le_weighted` absorbs into `sinθcos²θ`).

See `NOTES_pzIterSliceIntegrable_addendum4.md` §4–§6 for why *these* are the slots the whole
chapter funnels into (the moment chain `Endpt/moment_chain_pz` and `H2W.psiMomentChainWeak` need
`HkMem α 0 (z∂_zΨ)`, `HkMem α 0 (z²∂_z²Ψ)`; `aeSliceHonestOfSlots` needs the θ-slots), and §5 for
the new commutation identity `bslOp α (D_θ^iΨ) = D_θ^iF − [D_θ^i, Lzero]Ψ` which is the only
structural handle on them.
-/

namespace Work.FTS.EllipticEst.H2W.PsiSlices

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-! ## Elementary angular facts -/






/-! ## The AM–GM absorption of the angular weight into the `η`-weighted square -/


/-! ## The reduction of the target -/


end

end Work.FTS.EllipticEst.H2W.PsiSlices
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.Rtilde.SourceLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop.Rtilde

open scoped Real Topology


-- The angular source slot of the induction step of Elgindi's `prop:Hk` (verbatim copy of the
-- statement of `Submission/Work/FTS/EllipticEst/TT/ESW/source_le.lean`, which is `sorry`).
-- `Gsl α F Ψ = F + α²·Asl Ψ + α(5+α)·D_zΨ` is the angular source of the sliced equation
-- (`ESW.Defs.slice_source_eq`, PROVED), so the integrand splits pointwise into the three pieces
-- `∂_θ^k F`, `α²∂_θ^k(Asl Ψ)` and `α(5+α)∂_θ^k(D_z Ψ)`.  The F-piece is
-- `Work.FTS.EllipticEst.TT.ESW.srcF` (PROVED), the `Asl`-piece is
-- `Work.FTS.EllipticEst.remov.A_top_slot_bound` (PROVED: `α²√(Tk α k A) ≤ C|F|_k`) together with
-- `Work.FTS.EllipticEst.remov.HkSq_step_le` (PROVED), and the `D_zΨ`-piece is the triangular
-- comparison `Work.FTS.EllipticEst.TT.ESW.reverse_expansion_sq` (PROVED) with the η-weighted
-- `D_θ`-slots of `D_z(Bsl Ψ) = D_zB` supplied by hypothesis (2).  See the module docstring of
-- `TT/ESW/source_le.lean` for the exact route.

end Work.FTS.EllipticEst.Prop.Rtilde
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.ESW.source_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT.ESW

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# `source_le`

The top plain angular slot of the source `Gsl α F Ψ = F + α²·Asl Ψ + α(5+α)·D_zΨ` of the
sliced equation is dominated by `C·HkSq α k F`, for `k ≥ 3`, `0 < α ≤ 1/4`, under the two
level-`(k-1)` bounds on `(Asl Ψ, Bsl Ψ)` and on `(Asl (D_zΨ), Bsl (D_zΨ))`.

## Proof

The source `Gsl α F Ψ` is the function `Work.FTS.EllipticEst.Mine.Gsrc α F Ψ` (they are equal
by `gsrc_eq_gsl` below, both being
`(z,θ) ↦ F z θ + α²·(z²∂_z²Ψ z θ) + α(5+α)·(z∂_zΨ z θ)`), and the two hypotheses of the
statement are literally `Cores.Pieces.H1 D α k F Ψ` and `Cores.Pieces.H2 D α k F Ψ`.  The
top-slot bound asked for is therefore exactly

  `Work.FTS.EllipticEst.Cores.Pieces.topSrcSlot D hD k hk`

(a proved, axiom-clean lemma of that module: it splits `∂_θ^k(Gsrc α F Ψ)` into the three
summands `∂_θ^k F`, `α²∂_θ^k(z²∂_z²Ψ)`, `α(5+α)∂_θ^k(D_zΨ)`, bounds the first by the slots of
`HkSq α k F`, the second by hypothesis `H1` at levels `≤ k-1` together with the top `D_θ^k`-slot
`A_top_slot_bound`, and the third by hypothesis `H2` through `∂_θθ(D_zΨ)`), and the proof below
is the reduction of the statement to it.

The auxiliary module `ESW.SourceAux` contains the lemmas that were developed for the direct
route (the `F`-piece `srcF`, the smoothness of `F`/`D_zΨ`/`z²∂_z²Ψ`/`∂_θ²Ψ` on the open
quadrant, the pointwise/integrated top-slot bounds `slot_top_le_HkIntegrand` /
`slot_top_integral_le`, and the triangular comparison `reverse_expansion_sq`); they are
independent of this reduction.
-/



end

end Work.FTS.EllipticEst.TT.ESW
end
-- ===== merged: Submission.Work.FTS.EpsEngine.SixMixed =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The per-`z` bound for a mixed slot of the level-`6` integrand.** -/
theorem mixed_slot_perz_le8 :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ {f : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 8 f →
      ∀ (i j : ℕ), 1 ≤ i → i + j ≤ 6 → ∀ {z : ℝ}, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ C * (1 + (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α 8 f := by
  obtain ⟨CB, hCBpos, hCB⟩ := sliceAng_le8
  refine ⟨CB, hCBpos, ?_⟩
  intro α hα f hF hmem i j hi hij z hz
  obtain ⟨hα0, hα1⟩ := hα
  have hcongr :
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
        = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed j i f z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← MeasureTheory.integral_const_mul]
    refine Work.FTS.EllipticEst.setIntegral_Iθ_congr_of_forall_Ioo (fun θ hθ => ?_)
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    rw [mul_pow, Work.H2.T1Q.Wt_sq_eq α z θ hs]
    ring
  rw [hcongr]
  have hb := hCB α f j i hα0 hα1 hF hmem hi (by omega) z hz
  have hHk := Work.Spaces.HkSq_nonneg α 8 f
  calc (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed j i f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ (Work.Spaces.w z) ^ 2 * (CB * Work.Spaces.HkSq α 8 f) :=
        mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ ≤ CB * (1 + (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α 8 f := by
        nlinarith [hCBpos, hHk, sq_nonneg (Work.Spaces.w z)]

end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.GalApprox.poly2_aux1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ContDiff BigOperators
open Set Filter

namespace Work.FTS.GalBasis.GalApprox

set_option autoImplicit false
set_option maxHeartbeats 1600000


/-! ## Bridge lemmas between `pzIter`/`pthIter` and `iteratedDeriv` -/

/-- `pthIter i f z θ` is the `i`-th iterated derivative of the `θ`-slice. -/
theorem pthIter_eq_iteratedDeriv (j : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter j f z θ = iteratedDeriv j (fun θ' => f z θ') θ := by
  rw [iteratedDeriv_eq_iterate]
  induction j generalizing θ with
  | zero => rfl
  | succ n ih =>
      simp only [Work.Spaces.pthIter_succ, Work.Spaces.pth]
      have h : (fun θ' => Work.Spaces.pthIter n f z θ') = deriv^[n] (fun θ' => f z θ') := by
        funext θ'; exact ih θ'
      rw [h, Function.iterate_succ_apply']

/-! ## Iterated derivatives of `x ↦ x ^ n` and the falling factorial -/



/-! ## Separable functions: iterated derivatives of `z ↦ f z * h θ` -/







/-! ## The shifted monomial: mixed iterated derivatives -/


/-! ## Linearities on slices -/





/-! ## A finite sum of shifted monomials -/



/-! ## Linearity of the iterated partials over addition and subtraction -/

theorem pzIter_add {i : ℕ} {X Y : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hX : ContDiffAt ℝ i (fun z' => X z' θ) z)
    (hY : ContDiffAt ℝ i (fun z' => Y z' θ) z) :
    Work.Spaces.pzIter i (fun z θ => X z θ + Y z θ) z θ
      = Work.Spaces.pzIter i X z θ + Work.Spaces.pzIter i Y z θ := by
  rw [Work.Spaces.pzIter_eq_iteratedDeriv, Work.Spaces.pzIter_eq_iteratedDeriv,
    Work.Spaces.pzIter_eq_iteratedDeriv]
  have h : (fun z' => X z' θ + Y z' θ) = (fun z' => X z' θ) + (fun z' => Y z' θ) := rfl
  rw [h, iteratedDeriv_add hX hY]


theorem pthIter_add {i : ℕ} {X Y : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hX : ContDiffAt ℝ i (fun θ' => X z θ') θ)
    (hY : ContDiffAt ℝ i (fun θ' => Y z θ') θ) :
    Work.Spaces.pthIter i (fun z θ => X z θ + Y z θ) z θ
      = Work.Spaces.pthIter i X z θ + Work.Spaces.pthIter i Y z θ := by
  rw [pthIter_eq_iteratedDeriv, pthIter_eq_iteratedDeriv, pthIter_eq_iteratedDeriv]
  have h : (fun θ' => X z θ' + Y z θ') = (fun θ' => X z θ') + (fun θ' => Y z θ') := rfl
  rw [h, iteratedDeriv_add hX hY]


/-! ## Smoothness of a finite sum of shifted monomials -/





/-! ## Uniform approximation by shifted monomial sums -/




/-! ## Linearity of the iterated partials over `Finset` sums -/




/-! ## Evaluation of the θ-derivatives of the two pieces of `Q` -/






/-! ## The class of shifted monomial sums -/
















end Work.FTS.GalBasis.GalApprox
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.chi_facts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cc

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The `D`-iterates of constants and of pointwise-zero functions

These are the two elementary facts behind the passage from `ψ N` to the complement
`χ = 1 - ψ N`: a constant has vanishing iterated `D`-derivatives as soon as the order is
positive (the outermost operator carries a `z` or a `sin 2θ` factor in front of a
derivative of a constant), and the iterates of a function which vanishes identically
vanish identically. -/








/-- Congruence of the mixed operators for two functions agreeing on the open quadrant. -/
private lemma mixed_congr_Q0 {F G : ℝ → ℝ → ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → F z θ = G z θ) (j i : ℕ)
    {z θ : ℝ} (hz : 0 < z) (h1 : 0 < θ) (h2 : θ < π / 2) :
    Work.Spaces.mixed j i F z θ = Work.Spaces.mixed j i G z θ := by
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, h1, h2⟩
  refine Work.FTS.GalBasis.mixed_congr_of_eventuallyEq j i ?_
  filter_upwards [Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp] with p hp'
  obtain ⟨hz', h1', h2'⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp'
  exact h p.1 p.2 hz' h1' h2'

/-! ## The three clauses -/




end Work.FTS.GalBasis.cc
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.AuxAngRad.angRad_majorant_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows.AuxAngRad

/-- The light angular weight `σ = sin(2θ)^{-η}` is integrable on the closed angular interval
`Iθ` (the exponent `η = 99/100` lies in `(0,1)`). -/
theorem integrableOn_smE :
    MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.Nonlinear.RadialProd.smE θ)
      Work.Spaces.Iθ := by
  simpa only [Work.FTS.Nonlinear.RadialProd.smE] using
    (Work.FTS.LocData.integral_sin_two_rpow_neg Work.Spaces.eta Work.Spaces.eta_pos
      Work.Spaces.eta_lt_one).1

theorem angRad_majorant_integrable {α : ℝ} {r G : ℝ → ℝ} {B0 B1 : ℝ}
    (hGint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ)
    (hrmem : Work.Spaces.HkMem α 4 (fun z _ => r z)) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.FTS.Nonlinear.RadialProd.Rint r z
          * (B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
              + 4 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ))
        Work.Spaces.Iθ)
      ∧ MeasureTheory.IntegrableOn
        (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          Work.FTS.Nonlinear.RadialProd.Rint r z
            * (B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
                + 4 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ))
        Work.Spaces.Iz := by
  -- the angular majorant is integrable: it is a combination of the integrable `σ = smE`
  -- and the (hypothesised integrable) `G² · smG α`.
  have h2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => 4 * B1 ^ 2 * (G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ))
      Work.Spaces.Iθ := hGint.const_mul _
  have h2' : MeasureTheory.IntegrableOn
      (fun θ : ℝ => 4 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
      Work.Spaces.Iθ :=
    h2.congr_fun (fun θ _ => by ring) measurableSet_Icc
  have hg : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
        + 4 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
      Work.Spaces.Iθ := (integrableOn_smE.const_mul _).add h2'
  refine ⟨fun z _ => ?_, ?_⟩
  · -- the `θ`-integrand is a constant (`Rint r z`) multiple of the angular majorant
    exact hg.const_mul (Work.FTS.Nonlinear.RadialProd.Rint r z)
  · -- `∫_θ Rint r z · (…) = Rint r z · ∫_θ (…)`, and `Rint r` is integrable for an `ℋ⁴`
    -- radial datum
    have hRint := Work.FTS.NonlinRows.AuxAngRad.integrableOn_Rint_of_HkMem hrmem
    have hK : MeasureTheory.IntegrableOn
        (fun z : ℝ => Work.FTS.Nonlinear.RadialProd.Rint r z
          * (∫ θ in Work.Spaces.Iθ,
              (B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
                + 4 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)))
        Work.Spaces.Iz := hRint.mul_const _
    refine hK.congr_fun (fun z _ => ?_) measurableSet_Ici
    rw [MeasureTheory.integral_const_mul]

end Work.FTS.NonlinRows.AuxAngRad
end
-- ===== merged: Submission.Work.FTS.NonlinRows.sin_mul_mixed_pth_le =====
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
set_option maxHeartbeats 2000000

/-! ## The constant of the `σ`-gain -/

/-- The constant `C_r` of the estimate `sin(2θ)·|D_z^jD_θ^r(∂_θG)| ≤ C_r·Σ_{1≤m≤r+1}|…|`:

`C_0 = 1` (the case `r = 0` is the exact identity `sin(2θ)·∂_θG = D_θG`), and for `1 ≤ r ≤ 4`
the recursion `C_r = 1 + Σ_{a<r} C(r,a+1)·A_{a+1}·C_{r-a-1}`, with `A_k = Asin k` the
constants of `|D_θ^k(sin 2·)| ≤ A_k·sin(2θ)`.  The values are
`C_1 = 3`, `C_2 = 17`, `C_3 = 187`, `C_4 = 2865`. -/
def B4 : ℕ → ℝ
  | 0 => 1
  | 1 => 3
  | 2 => 17
  | 3 => 187
  | _ => 2865

theorem B4_pos (n : ℕ) : 0 < B4 n := by
  rcases n with _ | _ | _ | _ | _ <;> norm_num [B4]

theorem B4_nonneg (n : ℕ) : 0 ≤ B4 n := (B4_pos n).le




/-! ## The commutator expansion

The pointwise input of the induction below — the expansion of `D_z^jD_θ^{i+1}G` in terms of
`∂_θG`, for `G` of class `SmoothOpen` — is proved in the sibling module
`Submission.Work.FTS.NonlinRows.mixed_succ_expansion_open` (namespace `Work.FTS.NonlinRows`)
as `mixed_succ_expansion_open`:

  `D_z^jD_θ^{i+1}G = sin(2θ)·D_z^jD_θ^i(∂_θG)
      + Σ_{r<i} C(i,r+1)·L^{r+1}(sin 2·)(θ)·D_z^jD_θ^{i-1-r}(∂_θG)`. -/

/-! ## The `σ`-gain, by induction on the number of angular slots -/


/-! ## The target -/


end Work.FTS.NonlinRows
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Row19Prep.gam_aux =====
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


/-- `TB = Σ_{j<5} tBound j 0`, a uniform bound for `tBound (a-1) 0`, `a ≤ 4`. -/
def TB : ℝ := ∑ j ∈ Finset.range 5, Work.Spaces.tBound j 0





/-! ## Smoothness helpers -/

theorem smoothOpen_theta_only {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ Work.Stability.smoothOrder a (Set.Ioo 0 (π / 2))) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ) :=
  ha.comp contDiffOn_snd (fun p hp => hp.2)

theorem smoothOpen_z_only {r : ℝ → ℝ}
    (hr : ContDiffOn ℝ Work.Stability.smoothOrder r (Set.Ioi 0)) :
    Work.FTS.EllipticEst.SmoothOpen (fun (z : ℝ) _ => r z) :=
  hr.comp contDiffOn_fst (fun p hp => hp.1)

theorem smoothOpen_mul {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) := by
  have h : Function.uncurry (fun z θ : ℝ => f z θ * g z θ)
      = Function.uncurry f * Function.uncurry g := rfl
  rw [Work.FTS.EllipticEst.SmoothOpen]
  rw [h]
  exact hf.mul hg

/-- `Γ(θ) = (sinθcos²θ)^{α/3}` is `C^∞` on the open interval `(0,π/2)`. -/
theorem contDiffOn_Gam (α : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Work.Spaces.Gam α θ)
      (Set.Ioo 0 (π / 2)) := by
  have hsin : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.sin θ)
      (Set.Ioo 0 (π / 2)) := Real.contDiff_sin.contDiffOn
  have hcos : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.cos θ)
      (Set.Ioo 0 (π / 2)) := Real.contDiff_cos.contDiffOn
  have hbase : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) (Set.Ioo 0 (π / 2)) := hsin.mul (hcos.pow 2)
  have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), Real.sin θ * Real.cos θ ^ 2 ≠ 0 := by
    intro θ hθ
    have h1 : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have h2 : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    positivity
  have h := hbase.rpow (contDiffOn_const (c := α / 3)) hne
  refine h.congr (fun θ hθ => ?_)
  simp only [Work.Spaces.Gam]


/-! ## `θ`-only / `z`-only calculus -/

/-- For a `θ`-only function, `D_θ^j` is the `dthU`-iterate. -/
theorem DthIter_theta_only (g : ℝ → ℝ) (j : ℕ) :
    Work.Spaces.DthIter j (fun _ (θ : ℝ) => g θ) = fun _ θ => Work.Spaces.dthU^[j] g θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DthIter_succ, ih]
      funext z θ
      show Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.dthU^[j] g θ') θ
        = Work.Spaces.dthU^[j + 1] g θ
      rw [Function.iterate_succ_apply' Work.Spaces.dthU j g, Work.Spaces.dthU]

theorem pzIter_zero_fun (k : ℕ) :
    Work.Spaces.pzIter k (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => (0 : ℝ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.pzIter_succ, ih]
      funext z θ
      simp only [Work.Spaces.pz, deriv_const]

theorem WlInf_nonneg (α : ℝ) (l : ℕ) (f : ℝ → ℝ → ℝ) (hmem : Work.Spaces.WlInfMem α l f) :
    0 ≤ Work.Spaces.WlInf α l f := by
  rw [Work.Spaces.WlInf]
  exact add_nonneg (Work.Spaces.wlZSum_nonneg α l f hmem) (Work.Spaces.wlThSum_nonneg α l f hmem)

/-! ## The `z`-only Leibniz bound for `A·H₂`

The `D_θ`-derivatives all land on `A`; the terms where one falls on the `z`-only `H₂` vanish. -/


end Work.FTS.Nonlinear.Open.Row19Prep
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.dthU_pow_Gam_sharp =====
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
set_option linter.unusedVariables false

/-! ## The base case of the induction -/

/-- `Hyp 1`: all `dthU`-iterates of `Tfun 1 α` of order `≤ 3` are `O(α + sin 2θ)`. -/
lemma Hyp_one : Hyp 1 := by
  intro α θ hα hα1 hθ k hk
  have hk3 : k ≤ 3 := by omega
  have hk4 : k ≤ 4 := by omega
  have h0 : (fun t : ℝ => Work.Spaces.Tfun 0 α t) = Work.Spaces.qfun := by
    funext t; rw [Work.Spaces.Tfun_zero]
  have hT : Work.Spaces.Tfun 1 α = Work.Spaces.dthU Work.Spaces.qfun
      + (fun θ => α * Work.Spaces.qfun θ) * Work.Spaces.qfun := by
    funext t
    rw [Work.Spaces.Tfun_succ, h0, Work.Spaces.Tfun_zero]
    simp only [Work.Spaces.dthU_apply, Pi.add_apply, Pi.mul_apply]
  have hf : ContDiff ℝ (⊤ : ℕ∞) (Work.Spaces.dthU Work.Spaces.qfun) :=
    Work.Spaces.dthU_smooth Work.Spaces.qfun_smooth
  have hfα : ContDiff ℝ (⊤ : ℕ∞) (fun θ => α * Work.Spaces.qfun θ) :=
    contDiff_const.mul Work.Spaces.qfun_smooth
  have hg : ContDiff ℝ (⊤ : ℕ∞)
      ((fun θ => α * Work.Spaces.qfun θ) * Work.Spaces.qfun) :=
    hfα.mul Work.Spaces.qfun_smooth
  have hval : Work.Spaces.dthU^[k] (Work.Spaces.Tfun 1 α) θ
      = Work.Spaces.dthU^[k + 1] Work.Spaces.qfun θ
        + ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)
            * (Work.Spaces.dthU^[i] (fun θ => α * Work.Spaces.qfun θ) θ
              * Work.Spaces.dthU^[k - i] Work.Spaces.qfun θ) := by
    rw [hT, Work.Spaces.dthU_iter_add k _ _ hf hg,
      Work.Spaces.dthU_iter_comp k Work.Spaces.qfun]
    simp only [Pi.add_apply]
    rw [dthU_iter_mul_apply k (fun θ => α * Work.Spaces.qfun θ) Work.Spaces.qfun hfα
      Work.Spaces.qfun_smooth θ]
  rw [hval]
  have hs := sinTwo_mem_Icc hθ
  have hαs : 0 ≤ α + Real.sin (2 * θ) := by linarith [hα, hs.1]
  have hA : |Work.Spaces.dthU^[k + 1] Work.Spaces.qfun θ|
      ≤ 1000 * (α + Real.sin (2 * θ)) := by
    have h1 := dthU_qfun_le_sin (i := k + 1) (by omega) (by omega) hθ
    have h2 : Real.sin (2 * θ) ≤ α + Real.sin (2 * θ) := by linarith [hα]
    linarith [h1, h2]
  have hQ : ∀ m : ℕ, m ≤ k → |Work.Spaces.dthU^[m] Work.Spaces.qfun θ| ≤ 1000 :=
    fun m hm => qfun_iter_abs_le (by omega) hθ
  have hB := alpha_qfun_leibniz_abs_le k hk4 hα hθ (Q := Work.Spaces.qfun) (KX := 1000) hQ
  have hkey : 1000 * (α + Real.sin (2 * θ)) + 16000 * α * 1000
      ≤ 17001000 * (α + Real.sin (2 * θ)) := by
    have h2 : 16000 * α * 1000 ≤ 16000 * 1000 * (α + Real.sin (2 * θ)) := by
      have h0 : (0 : ℝ) ≤ 16000 * 1000 := by norm_num
      calc 16000 * α * 1000 = (16000 * 1000) * α := by ring
        _ ≤ (16000 * 1000) * (α + Real.sin (2 * θ)) :=
              mul_le_mul_of_nonneg_left (by linarith [hα, hs.1]) h0
    linarith [h2]
  have hfin : (17001000 : ℝ) * (α + Real.sin (2 * θ))
      ≤ KB 1 * (α + Real.sin (2 * θ)) :=
    mul_le_mul_of_nonneg_right KB_one_ge hαs
  calc |Work.Spaces.dthU^[k + 1] Work.Spaces.qfun θ
        + ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)
            * (Work.Spaces.dthU^[i] (fun θ => α * Work.Spaces.qfun θ) θ
              * Work.Spaces.dthU^[k - i] Work.Spaces.qfun θ)|
      ≤ |Work.Spaces.dthU^[k + 1] Work.Spaces.qfun θ|
        + |∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)
            * (Work.Spaces.dthU^[i] (fun θ => α * Work.Spaces.qfun θ) θ
              * Work.Spaces.dthU^[k - i] Work.Spaces.qfun θ)| := abs_add_le _ _
    _ ≤ 1000 * (α + Real.sin (2 * θ)) + 16000 * α * 1000 := add_le_add hA hB
    _ ≤ KB 1 * (α + Real.sin (2 * θ)) := le_trans hkey hfin

/-! ## The induction step -/

/-- `Hyp j → Hyp (j+1)` for `1 ≤ j ≤ 3`: differentiate the recursion
`Tfun (j+1) α = dthU (Tfun j α) + α qfun Tfun j α` `k` times and apply the Leibniz rule. -/
lemma Hyp_succ (j : ℕ) (hj1 : 1 ≤ j) (hj3 : j ≤ 3) (h : Hyp j) : Hyp (j + 1) := by
  intro α θ hα hα1 hθ k hk
  have hk3 : k ≤ 3 := by omega
  have hk4 : k ≤ 4 := by omega
  have hk1 : k + 1 ≤ 4 - j := by omega
  have hT : Work.Spaces.Tfun (j + 1) α = Work.Spaces.dthU (Work.Spaces.Tfun j α)
      + (fun θ => α * Work.Spaces.qfun θ) * Work.Spaces.Tfun j α := by
    funext t
    rw [Work.Spaces.Tfun_succ]
    simp only [Work.Spaces.dthU_apply, Pi.add_apply, Pi.mul_apply]
  have hf : ContDiff ℝ (⊤ : ℕ∞) (Work.Spaces.dthU (Work.Spaces.Tfun j α)) :=
    Work.Spaces.dthU_smooth (Work.Spaces.Tfun_smooth j α)
  have hfα : ContDiff ℝ (⊤ : ℕ∞) (fun θ => α * Work.Spaces.qfun θ) :=
    contDiff_const.mul Work.Spaces.qfun_smooth
  have hg : ContDiff ℝ (⊤ : ℕ∞)
      ((fun θ => α * Work.Spaces.qfun θ) * Work.Spaces.Tfun j α) :=
    hfα.mul (Work.Spaces.Tfun_smooth j α)
  have hval : Work.Spaces.dthU^[k] (Work.Spaces.Tfun (j + 1) α) θ
      = Work.Spaces.dthU^[k + 1] (Work.Spaces.Tfun j α) θ
        + ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)
            * (Work.Spaces.dthU^[i] (fun θ => α * Work.Spaces.qfun θ) θ
              * Work.Spaces.dthU^[k - i] (Work.Spaces.Tfun j α) θ) := by
    rw [hT, Work.Spaces.dthU_iter_add k _ _ hf hg,
      Work.Spaces.dthU_iter_comp k (Work.Spaces.Tfun j α)]
    simp only [Pi.add_apply]
    rw [dthU_iter_mul_apply k (fun θ => α * Work.Spaces.qfun θ) (Work.Spaces.Tfun j α) hfα
      (Work.Spaces.Tfun_smooth j α) θ]
  rw [hval]
  have hs := sinTwo_mem_Icc hθ
  have hαs : 0 ≤ α + Real.sin (2 * θ) := by linarith [hα, hs.1]
  have hKBj : 0 ≤ KB j := (KB_pos j).le
  have hA : |Work.Spaces.dthU^[k + 1] (Work.Spaces.Tfun j α) θ|
      ≤ KB j * (α + Real.sin (2 * θ)) := h α θ hα hα1 hθ (k + 1) hk1
  have hQ : ∀ m : ℕ, m ≤ k → |Work.Spaces.dthU^[m] (Work.Spaces.Tfun j α) θ|
      ≤ KB j * (α + Real.sin (2 * θ)) := fun m hm => h α θ hα hα1 hθ m (by omega)
  have hB := alpha_qfun_leibniz_abs_le k hk4 hα hθ
    (Q := Work.Spaces.Tfun j α) (KX := KB j * (α + Real.sin (2 * θ))) hQ
  have hkey : KB j * (α + Real.sin (2 * θ))
        + 16000 * α * (KB j * (α + Real.sin (2 * θ)))
      ≤ 16001 * (KB j * (α + Real.sin (2 * θ))) := by
    have h2 : 16000 * α * (KB j * (α + Real.sin (2 * θ)))
        ≤ 16000 * (KB j * (α + Real.sin (2 * θ))) := by
      have h0 : (0 : ℝ) ≤ 16000 * (KB j * (α + Real.sin (2 * θ))) := by positivity
      calc 16000 * α * (KB j * (α + Real.sin (2 * θ)))
          = (16000 * (KB j * (α + Real.sin (2 * θ)))) * α := by ring
        _ ≤ (16000 * (KB j * (α + Real.sin (2 * θ)))) * 1 :=
              mul_le_mul_of_nonneg_left hα1 h0
        _ = 16000 * (KB j * (α + Real.sin (2 * θ))) := by ring
    linarith [h2]
  have hfin : (16001 : ℝ) * (KB j * (α + Real.sin (2 * θ)))
      ≤ KB (j + 1) * (α + Real.sin (2 * θ)) := by
    rw [KB_succ]
    have hmul : 0 ≤ KB j * (α + Real.sin (2 * θ)) := mul_nonneg hKBj hαs
    nlinarith [hmul]
  calc |Work.Spaces.dthU^[k + 1] (Work.Spaces.Tfun j α) θ
        + ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)
            * (Work.Spaces.dthU^[i] (fun θ => α * Work.Spaces.qfun θ) θ
              * Work.Spaces.dthU^[k - i] (Work.Spaces.Tfun j α) θ)|
      ≤ |Work.Spaces.dthU^[k + 1] (Work.Spaces.Tfun j α) θ|
        + |∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)
            * (Work.Spaces.dthU^[i] (fun θ => α * Work.Spaces.qfun θ) θ
              * Work.Spaces.dthU^[k - i] (Work.Spaces.Tfun j α) θ)| := abs_add_le _ _
    _ ≤ KB j * (α + Real.sin (2 * θ)) + 16000 * α * (KB j * (α + Real.sin (2 * θ))) :=
        add_le_add hA hB
    _ ≤ KB (j + 1) * (α + Real.sin (2 * θ)) := le_trans hkey hfin

/-! ## The target lemma -/

theorem dthU_pow_Gam_sharp :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ θ ∈ Work.Spaces.Iθ, ∀ m : ℕ,
      2 ≤ m → m ≤ 5 →
      |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
        ≤ C * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) := by
  refine ⟨KB 4, KB_pos 4, ?_⟩
  intro α hα hα1 θ hθ m hm2 hm5
  have h1 : Hyp 1 := Hyp_one
  have h2 : Hyp 2 := Hyp_succ 1 le_rfl (by norm_num) h1
  have h3 : Hyp 3 := Hyp_succ 2 (by norm_num) (by norm_num) h2
  have h4 : Hyp 4 := Hyp_succ 3 (by norm_num) (by norm_num) h3
  have hm1 : 1 ≤ m - 1 := by omega
  have hm1' : 1 ≤ m := by omega
  have hmle : m - 1 ≤ 4 := by omega
  have hsel : Hyp (m - 1) := by
    have hmc : m - 1 = 1 ∨ m - 1 = 2 ∨ m - 1 = 3 ∨ m - 1 = 4 := by omega
    rcases hmc with hmc | hmc | hmc | hmc <;> rw [hmc]
    exacts [h1, h2, h3, h4]
  have hGam0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hs := sinTwo_mem_Icc hθ
  rcases lt_or_eq_of_le hθ.1 with hθ0 | hθ0
  · rcases lt_or_eq_of_le hθ.2 with hθ1 | hθ1
    · -- interior of `Iθ`: use the jet identity and `Hyp (m-1)`
      have hid := Work.Spaces.dthU_iter_Gam (m - 1) α hα
        (show θ ∈ Set.Ioo 0 (Real.pi / 2) from ⟨hθ0, hθ1⟩)
      rw [show m - 1 + 1 = m from by omega] at hid
      have hT : |Work.Spaces.Tfun (m - 1) α θ|
          ≤ KB (m - 1) * (α + Real.sin (2 * θ)) := hsel α θ hα hα1 hθ 0 (by omega)
      have hKB : KB (m - 1) ≤ KB 4 := KB_mono hmle
      have hαs : 0 ≤ α + Real.sin (2 * θ) := by linarith [hα, hs.1]
      have hb : |α * Work.Spaces.Tfun (m - 1) α θ * Work.Spaces.Gam α θ|
          = α * |Work.Spaces.Tfun (m - 1) α θ| * Work.Spaces.Gam α θ := by
        rw [abs_mul, abs_mul, abs_of_pos hα, abs_of_nonneg hGam0]
      rw [hid, hb]
      have hmul : α * (KB (m - 1) * (α + Real.sin (2 * θ)))
          ≤ α * (KB 4 * (α + Real.sin (2 * θ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKB hαs) hα.le
      calc α * |Work.Spaces.Tfun (m - 1) α θ| * Work.Spaces.Gam α θ
          ≤ α * (KB (m - 1) * (α + Real.sin (2 * θ))) * Work.Spaces.Gam α θ := by
            apply mul_le_mul_of_nonneg_right _ hGam0
            exact mul_le_mul_of_nonneg_left hT hα.le
        _ ≤ KB 4 * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) := by
            calc α * (KB (m - 1) * (α + Real.sin (2 * θ))) * Work.Spaces.Gam α θ
                ≤ (α * (KB 4 * (α + Real.sin (2 * θ)))) * Work.Spaces.Gam α θ :=
                  mul_le_mul_of_nonneg_right hmul hGam0
              _ = KB 4 * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) := by ring
    · -- `θ = π/2`
      subst hθ1
      rw [Work.Spaces.dthU_iter_eq_zero_of_sin_eq_zero' (fun t => Work.Spaces.Gam α t) hm1'
            (by rw [show 2 * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi]), abs_zero]
      have hsin : 0 ≤ Real.sin (2 * (Real.pi / 2)) := by
        rw [show 2 * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi]
      exact mul_nonneg (mul_nonneg (mul_nonneg (KB_pos 4).le hα.le) hGam0)
        (by linarith [hα, hsin])
  · -- `θ = 0`
    subst hθ0
    rw [Work.Spaces.dthU_iter_eq_zero_of_sin_eq_zero' (fun t => Work.Spaces.Gam α t) hm1'
          (by simp only [mul_zero, Real.sin_zero]), abs_zero]
    have hsin : 0 ≤ Real.sin (2 * (0 : ℝ)) := by simp only [mul_zero, Real.sin_zero, le_refl]
    exact mul_nonneg (mul_nonneg (mul_nonneg (KB_pos 4).le hα.le) hGam0)
      (by linarith [hα, hsin])

end Work.FTS.Nonlinear.Pieces.RNP
end
end
-- ===== merged: Submission.Work.FTS.OpenPkg.ProdOpen.m_sum_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg.ProdOpen

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Work.Spaces
open Work.FTS.EllipticEst (SmoothOpen Q0 mem_Q0)

/-- `n.choose k ≤ 2^n ≤ 16` for `n ≤ 4`, hence `(n.choose k : ℝ)² ≤ 256`. -/
theorem binom_sq_le_256 (n k : ℕ) (hkn : k ≤ n) (hn : n ≤ 4) :
    (n.choose k : ℝ) ^ 2 ≤ 256 := by
  have h1 : n.choose k ≤ 2 ^ n := by
    have h := Finset.single_le_sum (f := fun j => n.choose j) (fun j _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hkn))
    rwa [Nat.sum_range_choose] at h
  have h2 : n.choose k ≤ 16 := by
    calc n.choose k ≤ 2 ^ n := h1
      _ ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) hn
      _ = 16 := by norm_num
  have h3 : (n.choose k : ℝ) ≤ 16 := by exact_mod_cast h2
  have h4 : (0 : ℝ) ≤ (n.choose k : ℝ) := by positivity
  nlinarith [h3, h4]

/-- **The per-Leibniz-term bound.**  For orders `A,B` on `f` and `C,D` on `g` with
`A + D ≥ 1` and `A + B + C + D ≤ 4`,

  `(D_z^B D_θ^A f · D_z^C D_θ^D g · W)² ≤ max CPw 1 · (SInv + Texc)`.

The hypothesis `1 ≤ A + D` is the slot condition `i ≥ 1` of `HkIntegrand`. -/
theorem m_slot_bound {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f g : ℝ → ℝ → ℝ}
    (hF : SmoothOpen f) (hmemF : HkMem α 4 f) (hG : SmoothOpen g) (hmemG : HkMem α 4 g)
    {CPw : ℝ} (hCPw : 0 < CPw)
    (hPw : ∀ (u : ℝ → ℝ → ℝ), SmoothOpen u → HkMem α 4 u → ∀ b a : ℕ, a + b ≤ 2 →
      ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      (mixed b a u z θ) ^ 2 ≤ CPw / (gam α - 1) * HkSq α 4 u)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ∀ A B C D : ℕ, 1 ≤ A + D → A + B + C + D ≤ 4 →
      (mixed B A f z θ * mixed C D g z θ * Wt α z θ) ^ 2
        ≤ max CPw 1 * (SInv α f g z θ + Texc α f g z θ) := by
  intro A B C D hAD htot
  have hγ : 0 < gam α - 1 := gam_sub_one_pos hα
  have hSl : 0 ≤ SInv α f g z θ := SInv_nonneg hα f g z θ
  have hTl : 0 ≤ Texc α f g z θ := Texc_nonneg α f g z θ
  have hCMpos : 0 < max CPw 1 := lt_of_lt_of_le hCPw (le_max_left _ _)
  have hPwCM : CPw ≤ max CPw 1 := le_max_left _ _
  have h1CM : (1 : ℝ) ≤ max CPw 1 := le_max_right _ _
  -- ### The three closing shapes
  have keyF : (mixed B A f z θ) ^ 2 ≤ CPw / (gam α - 1) * HkSq α 4 f →
      (mixed C D g z θ * Wt α z θ) ^ 2 ≤ HkIntegrand α 4 g z θ →
      (mixed B A f z θ * mixed C D g z θ * Wt α z θ) ^ 2
        ≤ max CPw 1 * (SInv α f g z θ + Texc α f g z θ) := by
    intro hx hy
    have h1 : (mixed B A f z θ * mixed C D g z θ * Wt α z θ) ^ 2
        = (mixed B A f z θ) ^ 2 * (mixed C D g z θ * Wt α z θ) ^ 2 := by ring
    rw [h1]
    calc (mixed B A f z θ) ^ 2 * (mixed C D g z θ * Wt α z θ) ^ 2
        ≤ (CPw / (gam α - 1) * HkSq α 4 f) * HkIntegrand α 4 g z θ :=
          mul_le_mul hx hy (sq_nonneg _)
            (mul_nonneg (div_nonneg hCPw.le hγ.le) (HkSq_nonneg α 4 f))
      _ = CPw * ((gam α - 1)⁻¹ * (HkSq α 4 f * HkIntegrand α 4 g z θ)) := by
          rw [div_eq_mul_inv]; ring
      _ ≤ CPw * SInv α f g z θ :=
          mul_le_mul_of_nonneg_left (mul_inv_mul_le_SInv_left hα f g z θ) hCPw.le
      _ ≤ max CPw 1 * SInv α f g z θ := mul_le_mul_of_nonneg_right hPwCM hSl
      _ ≤ max CPw 1 * (SInv α f g z θ + Texc α f g z θ) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hTl) hCMpos.le
  have keyG : (mixed C D g z θ) ^ 2 ≤ CPw / (gam α - 1) * HkSq α 4 g →
      (mixed B A f z θ * Wt α z θ) ^ 2 ≤ HkIntegrand α 4 f z θ →
      (mixed B A f z θ * mixed C D g z θ * Wt α z θ) ^ 2
        ≤ max CPw 1 * (SInv α f g z θ + Texc α f g z θ) := by
    intro hy hx
    have h1 : (mixed B A f z θ * mixed C D g z θ * Wt α z θ) ^ 2
        = (mixed B A f z θ * Wt α z θ) ^ 2 * (mixed C D g z θ) ^ 2 := by ring
    rw [h1]
    calc (mixed B A f z θ * Wt α z θ) ^ 2 * (mixed C D g z θ) ^ 2
        ≤ HkIntegrand α 4 f z θ * (CPw / (gam α - 1) * HkSq α 4 g) :=
          mul_le_mul hx hy (sq_nonneg _) (HkIntegrand_nonneg α 4 f z θ)
      _ = CPw * ((gam α - 1)⁻¹ * (HkSq α 4 g * HkIntegrand α 4 f z θ)) := by
          rw [div_eq_mul_inv]; ring
      _ ≤ CPw * SInv α f g z θ :=
          mul_le_mul_of_nonneg_left (mul_inv_mul_le_SInv_right hα f g z θ) hCPw.le
      _ ≤ max CPw 1 * SInv α f g z θ := mul_le_mul_of_nonneg_right hPwCM hSl
      _ ≤ max CPw 1 * (SInv α f g z θ + Texc α f g z θ) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hTl) hCMpos.le
  have keyE : (mixed B A f z θ * mixed C D g z θ * Wt α z θ) ^ 2 ≤ Texc α f g z θ →
      (mixed B A f z θ * mixed C D g z θ * Wt α z θ) ^ 2
        ≤ max CPw 1 * (SInv α f g z θ + Texc α f g z θ) := by
    intro hxy
    calc (mixed B A f z θ * mixed C D g z θ * Wt α z θ) ^ 2 ≤ Texc α f g z θ := hxy
      _ = 1 * Texc α f g z θ := by ring
      _ ≤ max CPw 1 * (SInv α f g z θ + Texc α f g z θ) :=
          mul_le_mul h1CM (le_add_of_nonneg_left hSl) hTl (by linarith)
  -- ### The case analysis
  by_cases hA1 : 1 ≤ A
  · by_cases hD1 : 1 ≤ D
    · -- both angular orders positive: `min (A+B) (C+D) ≤ 2`
      by_cases hmin : A + B ≤ C + D
      · exact keyF (hPw f hF hmemF B A (by omega) z θ hz hθ)
          (sq_le_HkIntegrand_mixed α 4 g z θ D C hD1 (by omega))
      · exact keyG (hPw g hG hmemG C D (by omega) z θ hz hθ)
          (sq_le_HkIntegrand_mixed α 4 f z θ A B hA1 (by omega))
    · -- `D = 0`: the `g`-factor is a pure `D_z`-slot
      have hDe : D = 0 := by omega
      subst hDe
      by_cases hC2 : C ≤ 2
      · exact keyG (hPw g hG hmemG C 0 (by omega) z θ hz hθ)
          (sq_le_HkIntegrand_mixed α 4 f z θ A B hA1 (by omega))
      · -- exceptional: `A = 1, B = 0, C = 3, D = 0`
        have hAe : A = 1 := by omega
        have hBe : B = 0 := by omega
        have hCe : C = 3 := by omega
        refine keyE ?_
        rw [hAe, hBe, hCe]
        simp only [mixed_zero_left, mixed_zero_right, DthIter_succ, DthIter_zero]
        rw [show (Dth f z θ * DzIter 3 g z θ * Wt α z θ) ^ 2
            = (Dth f z θ * DzIter 3 g z θ) ^ 2 * (Wt α z θ) ^ 2 from by ring, Texc]
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (sq_nonneg _)) (sq_nonneg _)
  · -- `A = 0`: the `f`-factor is a pure `D_z`-slot
    have hAe : A = 0 := by omega
    subst hAe
    have hD1 : 1 ≤ D := by omega
    by_cases hB2 : B ≤ 2
    · exact keyF (hPw f hF hmemF B 0 (by omega) z θ hz hθ)
        (sq_le_HkIntegrand_mixed α 4 g z θ D C hD1 (by omega))
    · -- exceptional: `A = 0, B = 3, C = 0, D = 1`
      have hBe : B = 3 := by omega
      have hCe : C = 0 := by omega
      have hDe : D = 1 := by omega
      refine keyE ?_
      rw [hBe, hCe, hDe]
      simp only [mixed_zero_left, mixed_zero_right, DthIter_succ, DthIter_zero]
      rw [show (DzIter 3 f z θ * Dth g z θ * Wt α z θ) ^ 2
          = (DzIter 3 f z θ * Dth g z θ) ^ 2 * (Wt α z θ) ^ 2 from by ring, Texc]
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (sq_nonneg _)) (sq_nonneg _)

/-- **The mixed slots of `HkIntegrand α 4 (f·g)` are bounded by the majorant.** -/
theorem m_sum_bound : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    SmoothOpen f → HkMem α 4 f → SmoothOpen g → HkMem α 4 g →
    ∀ I J : ℕ, 1 ≤ I → I + J ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (mixed J I (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2
        ≤ C * (SInv α f g z θ + Texc α f g z θ) := by
  obtain ⟨CPw, hCPwpos, hPwAny⟩ := PwAny
  refine ⟨10 ^ 8 * max CPw 1, by positivity, ?_⟩
  intro α f g hα hα1 hF hmemF hG hmemG I J hI hIJ z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hPw : ∀ (u : ℝ → ℝ → ℝ), SmoothOpen u → HkMem α 4 u → ∀ b a : ℕ, a + b ≤ 2 →
      ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      (mixed b a u z θ) ^ 2 ≤ CPw / (gam α - 1) * HkSq α 4 u :=
    fun u hu hum b a hab z θ hz hθ' => hPwAny α u b a hα hα1 hu hum hab z hz θ hθ'
  have hMnn : 0 ≤ max CPw 1 * (SInv α f g z θ + Texc α f g z θ) :=
    mul_nonneg (le_trans hCPwpos.le (le_max_left _ _))
      (add_nonneg (SInv_nonneg hα f g z θ) (Texc_nonneg α f g z θ))
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
      (Y a b) ^ 2 ≤ 65536 * (max CPw 1 * (SInv α f g z θ + Texc α f g z θ)) := by
    intro a ha b hb
    have haI : a ≤ I := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    have hbJ : b ≤ J := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hcha : (I.choose a : ℝ) ^ 2 ≤ 256 := binom_sq_le_256 I a (by omega) (by omega)
    have hchb : (J.choose b : ℝ) ^ 2 ≤ 256 := binom_sq_le_256 J b (by omega) (by omega)
    have hch : (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2 ≤ 65536 :=
      calc (I.choose a : ℝ) ^ 2 * (J.choose b : ℝ) ^ 2 ≤ 256 * 256 :=
            mul_le_mul hcha hchb (by positivity) (by norm_num)
        _ = 65536 := by norm_num
    have hslot := m_slot_bound hα hα1 hF hmemF hG hmemG hCPwpos hPw hz hθ a b (J - b) (I - a)
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
  have hIJ25 : ((I : ℝ) + 1) * ((J : ℝ) + 1) ≤ 25 := by
    have hI4 : (I : ℝ) ≤ 4 := by exact_mod_cast (by omega : I ≤ 4)
    have hJ4 : (J : ℝ) ≤ 4 := by exact_mod_cast (by omega : J ≤ 4)
    nlinarith
  have hsum2 : ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1), (Y a b) ^ 2
      ≤ ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
          (65536 * (max CPw 1 * (SInv α f g z θ + Texc α f g z θ))) :=
    Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hper a ha b hb
  have hsumconst : ∑ a ∈ Finset.range (I + 1), ∑ b ∈ Finset.range (J + 1),
        (65536 * (max CPw 1 * (SInv α f g z θ + Texc α f g z θ)))
      = ((I : ℝ) + 1) * ((J : ℝ) + 1)
        * (65536 * (max CPw 1 * (SInv α f g z θ + Texc α f g z θ))) := by
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
              (65536 * (max CPw 1 * (SInv α f g z θ + Texc α f g z θ))) :=
        mul_le_mul_of_nonneg_left hsum2 (by positivity)
    _ = (((I : ℝ) + 1) * ((J : ℝ) + 1)) ^ 2
          * (65536 * (max CPw 1 * (SInv α f g z θ + Texc α f g z θ))) := by
        rw [hsumconst]; ring_nf
    _ ≤ 625 * (65536 * (max CPw 1 * (SInv α f g z θ + Texc α f g z θ))) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have h0 : (0 : ℝ) ≤ ((I : ℝ) + 1) * ((J : ℝ) + 1) := by positivity
        nlinarith [hIJ25, h0]
    _ = 40960000 * (max CPw 1 * (SInv α f g z θ + Texc α f g z θ)) := by ring
    _ ≤ 10 ^ 8 * (max CPw 1 * (SInv α f g z θ + Texc α f g z θ)) :=
        mul_le_mul_of_nonneg_right (by norm_num) hMnn
    _ = 10 ^ 8 * max CPw 1 * (SInv α f g z θ + Texc α f g z θ) := by ring

end Work.FTS.OpenPkg.ProdOpen
end
end
-- ===== merged: Submission.Work.FTS.OpenPkg.ProdOpen.z_sum_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg.ProdOpen

set_option maxHeartbeats 1600000

open Work.Spaces

/-
IMPORTANT: do NOT import `Submission.Work.FTS.OpenPkg.ProdOpen.prod_majorant` (that module
contains a `sorry`); prove this from scratch.

Route.  `Hv z θ = w z / sin(2θ)^{η/2}` and `SInv`, `Texc` are in
`Submission/Work/FTS/OpenPkg/ProdOpen/ProdDefs.lean`.  Write `fg := fun z θ => f z θ * g z θ`.
1. `leibniz_open_Dz i f g hF hG z θ hz hθ0 hθ1` expands `DzIter i fg z θ` as a binomial sum;
   multiply by `Hv z θ`, use `Finset.sum_mul`, and Cauchy–Schwarz
   (`sq_sum_le_card_mul_sum_sq`) to get
   `(DzIter i fg z θ * Hv z θ)^2 ≤ (i+1) * ∑_{b ≤ i} (C(i,b))^2 * (DzIter b f * DzIter (i-b) g * Hv)^2`.
2. For each `b`, `b + (i-b) = i ≤ 4`, so `min b (i-b) ≤ 2`.  Put `x := DzIter b f z θ`,
   `y := DzIter (i-b) g z θ`, `ρ := Hv z θ`.
   * if `b ≤ i - b` (so `b ≤ 2`): `PwAny` (in `PwOpen.lean`) applied with `(b,a) = (b,0)` gives
     `x² ≤ CPw/(gam α - 1) * HkSq α 4 f` (note `mixed b 0 f = DzIter b f`), and
     `Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ (i-b) (by omega)` gives `(y*ρ)² ≤ HkIntegrand α 4 g z θ`;
   * if `i - b ≤ b`: symmetrically `PwAny` on `g` and `sq_le_HkIntegrand_z` on `f`.
   In both cases `(x*y*ρ)² = x² * (y*ρ)² ≤ CPw * SInv α f g z θ` (use
   `Work.FTS.OpenPkg.ProdOpen.mul_inv_mul_le_SInv_left/right` and the nonnegativity lemmas).
3. `(C(i,b) : ℝ)^2 ≤ 256` for `i ≤ 4` (bound `i.choose b ≤ 2^i ≤ 16`), and `∑_{b ≤ i} 1 = i+1 ≤ 5`,
   so `C := 6400 * CPw` works: the term in step 1 is `≤ (i+1) * 5 * 256 * CPw * Maj`, and
   `(i+1) * 5 * 256 ≤ 5*5*256 = 6400`; finally `CPw * SInv ≤ CPw * (SInv + Texc)`.
-/
theorem z_sum_bound : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
    ∀ i : ℕ, i ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ C * (Work.FTS.OpenPkg.ProdOpen.SInv α f g z θ
            + Work.FTS.OpenPkg.ProdOpen.Texc α f g z θ) := by
  obtain ⟨CPw, hCPwpos, hPw⟩ := PwAny
  refine ⟨6400 * CPw, by positivity, ?_⟩
  intro α f g hα hα1 hF hFmem hG hGmem i hi z θ hz hθ0 hθ1
  change (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ * Hv z θ) ^ 2
      ≤ 6400 * CPw * (SInv α f g z θ + Texc α f g z θ)
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hSl : 0 ≤ SInv α f g z θ := SInv_nonneg hα f g z θ
  have hTl : 0 ≤ Texc α f g z θ := Texc_nonneg α f g z θ
  have hγ : 0 < gam α - 1 := gam_sub_one_pos hα
  have hKnn : ∀ (u : ℝ → ℝ → ℝ), 0 ≤ CPw / (gam α - 1) * HkSq α 4 u := fun u =>
    mul_nonneg (div_nonneg hCPwpos.le hγ.le) (HkSq_nonneg α 4 u)
  -- ### Step 1: Leibniz plus Cauchy–Schwarz
  have hcs : (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ * Hv z θ) ^ 2
      ≤ ((i + 1 : ℕ) : ℝ)
        * ∑ b ∈ Finset.range (i + 1),
            ((i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ * Hv z θ)) ^ 2 := by
    have hsum : Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ * Hv z θ
        = ∑ b ∈ Finset.range (i + 1),
            ((i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ * Hv z θ)) := by
      rw [leibniz_open_Dz i f g hF hG z θ hz hθ0 hθ1, Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [hsum]
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
      (f := fun b => (i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ * Hv z θ))
    simpa using h
  -- ### Step 2: each Leibniz summand is dominated by `CPw * SInv`
  have hterm : ∀ b ∈ Finset.range (i + 1),
      ((i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ * Hv z θ)) ^ 2
        ≤ 256 * (CPw * SInv α f g z θ) := by
    intro b hb
    have hbi : b ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have hcb : (i.choose b : ℝ) ^ 2 ≤ 256 := by
      have h16 : i.choose b ≤ 16 := by
        calc i.choose b ≤ 2 ^ i := Nat.choose_le_two_pow i b
          _ ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) hi
          _ = 16 := by norm_num
      have h16' : (i.choose b : ℝ) ≤ 16 := by exact_mod_cast h16
      have hnn : (0 : ℝ) ≤ (i.choose b : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hcore : (DzIter b f z θ * DzIter (i - b) g z θ * Hv z θ) ^ 2
        ≤ CPw * SInv α f g z θ := by
      by_cases hcase : b ≤ i - b
      · -- the `f`-factor is the one of low order `b ≤ 2`
        have hb2 : b ≤ 2 := by omega
        have hx : (DzIter b f z θ) ^ 2 ≤ CPw / (gam α - 1) * HkSq α 4 f := by
          have h := hPw α f b 0 hα hα1 hF hFmem (by omega) z hz θ hθ
          simpa only [Work.Spaces.mixed_zero_right] using h
        have hy : (DzIter (i - b) g z θ * Hv z θ) ^ 2 ≤ HkIntegrand α 4 g z θ := by
          have h := sq_le_HkIntegrand_z α 4 g z θ (i - b) (by omega)
          simpa only [Hv] using h
        have h1 : (DzIter b f z θ * DzIter (i - b) g z θ * Hv z θ) ^ 2
            = (DzIter b f z θ) ^ 2 * (DzIter (i - b) g z θ * Hv z θ) ^ 2 := by ring
        rw [h1]
        refine le_trans (le_trans (mul_le_mul_of_nonneg_right hx (sq_nonneg _))
          (mul_le_mul_of_nonneg_left hy (hKnn f))) ?_
        rw [show CPw / (gam α - 1) * HkSq α 4 f * HkIntegrand α 4 g z θ
            = CPw * ((gam α - 1)⁻¹ * (HkSq α 4 f * HkIntegrand α 4 g z θ)) by
          rw [div_eq_mul_inv]; ring]
        exact mul_le_mul_of_nonneg_left (mul_inv_mul_le_SInv_left hα f g z θ) hCPwpos.le
      · -- the `g`-factor is the one of low order `i - b ≤ 2`
        have hib2 : i - b ≤ 2 := by omega
        have hy : (DzIter (i - b) g z θ) ^ 2 ≤ CPw / (gam α - 1) * HkSq α 4 g := by
          have h := hPw α g (i - b) 0 hα hα1 hG hGmem (by omega) z hz θ hθ
          simpa only [Work.Spaces.mixed_zero_right] using h
        have hx : (DzIter b f z θ * Hv z θ) ^ 2 ≤ HkIntegrand α 4 f z θ := by
          have h := sq_le_HkIntegrand_z α 4 f z θ b (by omega)
          simpa only [Hv] using h
        have h1 : (DzIter b f z θ * DzIter (i - b) g z θ * Hv z θ) ^ 2
            = (DzIter (i - b) g z θ) ^ 2 * (DzIter b f z θ * Hv z θ) ^ 2 := by ring
        rw [h1]
        refine le_trans (le_trans (mul_le_mul_of_nonneg_right hy (sq_nonneg _))
          (mul_le_mul_of_nonneg_left hx (hKnn g))) ?_
        rw [show CPw / (gam α - 1) * HkSq α 4 g * HkIntegrand α 4 f z θ
            = CPw * ((gam α - 1)⁻¹ * (HkSq α 4 g * HkIntegrand α 4 f z θ)) by
          rw [div_eq_mul_inv]; ring]
        exact mul_le_mul_of_nonneg_left (mul_inv_mul_le_SInv_right hα f g z θ) hCPwpos.le
    have h1 : ((i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ * Hv z θ)) ^ 2
        = (i.choose b : ℝ) ^ 2 * (DzIter b f z θ * DzIter (i - b) g z θ * Hv z θ) ^ 2 := by
      ring
    rw [h1]
    exact le_trans (mul_le_mul_of_nonneg_right hcb (sq_nonneg _))
      (mul_le_mul_of_nonneg_left hcore (by norm_num))
  -- ### Step 3: sum the terms
  have hsum_bd : ∑ b ∈ Finset.range (i + 1),
      ((i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ * Hv z θ)) ^ 2
        ≤ ((i + 1 : ℕ) : ℝ) * (256 * (CPw * SInv α f g z θ)) := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ hterm) ?_
    simp [nsmul_eq_mul]
  have hm : ((i + 1 : ℕ) : ℝ) ≤ 5 := by
    have : (i : ℝ) ≤ 4 := by exact_mod_cast hi
    push_cast
    linarith
  have hKnn' : 0 ≤ 256 * (CPw * SInv α f g z θ) :=
    mul_nonneg (by norm_num) (mul_nonneg hCPwpos.le hSl)
  have hstep : ((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) * (256 * (CPw * SInv α f g z θ)))
      ≤ 6400 * (CPw * SInv α f g z θ) := by
    have hmnn : (0 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by positivity
    have h1 : ((i + 1 : ℕ) : ℝ) * (256 * (CPw * SInv α f g z θ))
        ≤ 5 * (256 * (CPw * SInv α f g z θ)) := mul_le_mul_of_nonneg_right hm hKnn'
    have h2 : ((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) * (256 * (CPw * SInv α f g z θ)))
        ≤ 5 * (5 * (256 * (CPw * SInv α f g z θ))) :=
      mul_le_mul hm h1 (mul_nonneg hmnn hKnn') (by norm_num)
    have h3 : 5 * (5 * (256 * (CPw * SInv α f g z θ))) = 6400 * (CPw * SInv α f g z θ) := by
      ring
    linarith [h2, h3]
  calc (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ * Hv z θ) ^ 2
      ≤ ((i + 1 : ℕ) : ℝ)
          * ∑ b ∈ Finset.range (i + 1),
              ((i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ * Hv z θ)) ^ 2 := hcs
    _ ≤ ((i + 1 : ℕ) : ℝ)
          * (((i + 1 : ℕ) : ℝ) * (256 * (CPw * SInv α f g z θ))) :=
        mul_le_mul_of_nonneg_left hsum_bd (by positivity)
    _ ≤ 6400 * (CPw * SInv α f g z θ) := hstep
    _ ≤ 6400 * (CPw * (SInv α f g z θ + Texc α f g z θ)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hTl) hCPwpos.le) (by norm_num)
    _ = 6400 * CPw * (SInv α f g z θ + Texc α f g z θ) := by ring

end Work.FTS.OpenPkg.ProdOpen
end
end
-- ===== merged: Submission.Work.FTS.OpenPkg.WProdWin.dzIter_w_mean_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.OpenPkg.WProdWin

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

theorem dzIter_w_mean_le : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (g : ℝ → ℝ → ℝ) (d : ℕ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g → d ≤ 3 →
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
      Work.H2.T1Q.mixed_sq_le_HkIntegrand α hα g d 0 (by omega) hz hσ.1 hσ.2
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
      exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z σ 1 d (by norm_num) (by omega)
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

end Work.FTS.OpenPkg.WProdWin
end
-- ===== merged: Submission.Work.FTS.OpenPkg.WProdWin.zslot_le_winf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-
# `zslot_le_winf` — the radial `D_z`-slots of the `𝒲^{4,∞}`-priced product rule

For `f` of class `Work.FTS.EllipticEst.SmoothOpen` (`C^∞` on the *open* quadrant) and of class
`𝒲^{4,∞}` (`Work.Spaces.WlInfMem α 4 f`), and for an arbitrary `SmoothOpen` `g`, every pure
radial slot of the product `f·g` is dominated pointwise by the `𝒲^{4,∞}`-norm of the
coefficient times the `ℋ⁴`-integrand of `g`:

`(D_z^i (f·g)(z,θ) · w(z)/sin(2θ)^{η/2})² ≤ C |f|²_{𝒲^{4,∞}} · HkIntegrand α 4 g z θ`,  `i ≤ 4`,

with a universal constant `C` (here `10^8`), at every *interior* point `z > 0`, `0 < θ < π/2`.

This is the open-quadrant instance of `Work.Spaces.z_term_le` (which is stated for the
`SmoothInt`/`SmoothNbhd` classes, i.e. with smoothness through the boundary `z = 0` and the
angular endpoints).  The proof is the same:

* expand `D_z^i (f·g)` with the Leibniz rule for `D_z = z∂_z` in the open quadrant
  (`Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz`, which needs only `SmoothOpen f`, `SmoothOpen g`
  at `z > 0`, `0 < θ < π/2`);
* bound the square of the finite sum by `card • Σ (·)²` (`sq_sum_le_card_mul_sum_sq`);
* bound each `f`-factor by `100 |f|_𝒲` (`Work.FTS.OpenPkg.DzIter_le_WlInf_open`) and each
  `g`-factor by the corresponding slot of `HkIntegrand α 4 g`
  (`Work.Spaces.sq_le_HkIntegrand_z`, which needs no hypothesis at all since `HkIntegrand` is a
  sum of squares).

Note that `g` is *not* required to lie in `ℋ⁴`: the `g`-side only appears through the
(nonnegative, always finite) integrand `HkIntegrand α 4 g`, which is exactly what the consumer
of this slot bounds by the `ℋ⁴`-norm.
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.FTS.OpenPkg.WProdWin

/-- **The radial `D_z`-slot bound.**  Every pure `D_z`-slot `i ≤ 4` of the product `f·g`
(weighted as in `HkIntegrand`) is dominated by `10^8 |f|²_{𝒲^{4,∞}} HkIntegrand α 4 g z θ` at
interior points, for `f` of class `SmoothOpen` ∩ `𝒲^{4,∞}` and `g` merely `SmoothOpen`. -/
theorem zslot_le_winf : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 4 f →
      Work.FTS.EllipticEst.SmoothOpen g →
      ∀ i : ℕ, i ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ C * (Work.Spaces.WlInf α 4 f) ^ 2 * Work.Spaces.HkIntegrand α 4 g z θ := by
  refine ⟨10 ^ 8, by norm_num, ?_⟩
  intro α f g _hα _hα1 hf hfm hg i hi z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hW : 0 ≤ Work.Spaces.WlInf α 4 f := Work.Spaces.WlInf_nonneg α 4 f hfm
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
        ≤ 2560000 * (Work.Spaces.WlInf α 4 f) ^ 2
          * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by
    intro b hb
    have hbi : b ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hDf : |Work.Spaces.DzIter b f z θ| ≤ 100 * Work.Spaces.WlInf α 4 f :=
      Work.FTS.OpenPkg.DzIter_le_WlInf_open hf hfm (by omega) hz hθ
    have hx : (Work.Spaces.DzIter b f z θ) ^ 2
        ≤ (100 * Work.Spaces.WlInf α 4 f) ^ 2 := by
      have hB : (0 : ℝ) ≤ 100 * Work.Spaces.WlInf α 4 f := mul_nonneg (by norm_num) hW
      have h1 := (abs_le.mp hDf).1
      have h2 := (abs_le.mp hDf).2
      nlinarith [hB, h1, h2]
    have hch : ((i.choose b : ℝ)) ^ 2 ≤ 256 := Work.Spaces.choose_sq_le_256 i b hbi hi
    calc (((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
          * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2
        = ((i.choose b : ℝ)) ^ 2 * (Work.Spaces.DzIter b f z θ) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by ring
      _ ≤ 256 * (100 * Work.Spaces.WlInf α 4 f) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by gcongr
      _ = 2560000 * (Work.Spaces.WlInf α 4 f) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by ring
  -- each surviving `g`-factor is a pure slot of `HkIntegrand α 4 g`
  have hsumsq : ∑ b ∈ Finset.range (i + 1),
        (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2
      ≤ 5 * Work.Spaces.HkIntegrand α 4 g z θ := by
    calc ∑ b ∈ Finset.range (i + 1), (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2
        ≤ ∑ _b ∈ Finset.range (i + 1), Work.Spaces.HkIntegrand α 4 g z θ :=
          Finset.sum_le_sum (fun b _ =>
            Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ (i - b) (by omega))
      _ = ((i : ℝ) + 1) * Work.Spaces.HkIntegrand α 4 g z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ 5 * Work.Spaces.HkIntegrand α 4 g z θ := by
          have hnn := Work.Spaces.HkIntegrand_nonneg α 4 g z θ
          have hI2 : (i : ℝ) + 1 ≤ 5 := by exact_mod_cast (by omega : i + 1 ≤ 5)
          nlinarith
  calc (∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
            * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2
      ≤ (((Finset.range (i + 1)).card : ℕ) : ℝ) *
          ∑ b ∈ Finset.range (i + 1),
            (((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
              * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2 := hcs
    _ ≤ ((i : ℝ) + 1) * ∑ b ∈ Finset.range (i + 1),
          (2560000 * (Work.Spaces.WlInf α 4 f) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2) := by
        rw [hcard]
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hper) (by positivity)
    _ = 2560000 * (Work.Spaces.WlInf α 4 f) ^ 2 * (((i : ℝ) + 1)
          * ∑ b ∈ Finset.range (i + 1), (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ 2560000 * (Work.Spaces.WlInf α 4 f) ^ 2
          * (5 * (5 * Work.Spaces.HkIntegrand α 4 g z θ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hI2 : (i : ℝ) + 1 ≤ 5 := by exact_mod_cast (by omega : i + 1 ≤ 5)
        exact mul_le_mul hI2 hsumsq (Finset.sum_nonneg (fun b _ => sq_nonneg _)) (by norm_num)
    _ ≤ 10 ^ 8 * (Work.Spaces.WlInf α 4 f) ^ 2 * Work.Spaces.HkIntegrand α 4 g z θ := by
        have hnn := Work.Spaces.HkIntegrand_nonneg α 4 g z θ
        have h2 : 0 ≤ (Work.Spaces.WlInf α 4 f) ^ 2 := sq_nonneg _
        have hh : 2560000 * (Work.Spaces.WlInf α 4 f) ^ 2
              * (5 * (5 * Work.Spaces.HkIntegrand α 4 g z θ))
            = 64000000 * ((Work.Spaces.WlInf α 4 f) ^ 2
              * Work.Spaces.HkIntegrand α 4 g z θ) := by ring
        rw [hh, show (10 : ℝ) ^ 8 * (Work.Spaces.WlInf α 4 f) ^ 2
              * Work.Spaces.HkIntegrand α 4 g z θ
            = 10 ^ 8 * ((Work.Spaces.WlInf α 4 f) ^ 2
              * Work.Spaces.HkIntegrand α 4 g z θ) from by ring]
        exact mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg h2 hnn)

end Work.FTS.OpenPkg.WProdWin
end
-- ===== merged: Submission.Work.FTS.PhiStar.Psi0Est.Gzero_rpow_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Psi0Est

open scoped Real
open MeasureTheory Set Filter

/-! ## Auxiliary pointwise facts about `Γ̄` near `0`

`G₀(θ) = −∫_0^θ sin t cos²t Γ̄(t) dt` (`Gzero_eq_neg`), so a two-sided power bound for `G₀`
at `θ = 0` follows pointwise from a bound on the integrand.  The integrand is
`|sin t cos²t Γ̄(t)| ≤ |sin t| cos²t (|Γ(t)|/c + (5/4)|sin 2t|)`, and the only non-elementary
ingredient is the estimate `|Γ(t)| = |(sin t cos²t)^{α/3}| ≤ |t|^{α/3}`, which must hold for
`t < 0` as well: there `Real.rpow` of the negative base `sin t cos²t` is
`exp(log|t|·(α/3))·cos((α/3)π)`, whose modulus is `≤ |t|^{α/3}`. -/

/-- The modulus of `Real.rpow x y` for a *negative* base `x` is at most `(-x)^y`:
`x^y = exp(log x · y) cos(yπ)` and `log x = log (-x)` (`Real.log_neg_eq_log`), so
`|x^y| ≤ exp(log(-x)·y) = (-x)^y`. -/
lemma abs_rpow_le_rpow_neg {x y : ℝ} (hx : x < 0) : |x ^ y| ≤ (-x) ^ y := by
  rw [Real.rpow_def_of_neg hx, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  have h1 : Real.exp (Real.log x * y) = (-x) ^ y := by
    rw [Real.rpow_def_of_pos (neg_pos.mpr hx), Real.log_neg_eq_log]
  rw [h1]
  exact mul_le_of_le_one_right (le_of_lt (Real.rpow_pos_of_pos (neg_pos.mpr hx) y))
    (Real.abs_cos_le_one _)

/-- `|Γ(θ)| = |(sin θ cos²θ)^{α/3}| ≤ |θ|^{α/3}` — two-sided, i.e. also for `θ < 0` where the
base `sin θ cos²θ` is negative. -/
lemma abs_Gam_le_abs_rpow (α : ℝ) (hα : 0 ≤ α) (t : ℝ) :
    |Work.Spaces.Gam α t| ≤ |t| ^ (α / 3) := by
  rw [Work.Spaces.Gam]
  set b : ℝ := Real.sin t * Real.cos t ^ 2 with hb
  have hle : |b| ≤ |t| := by
    have h1 : |b| = |Real.sin t| * Real.cos t ^ 2 := by
      rw [hb, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.cos t ^ 2)]
    rw [h1]
    calc |Real.sin t| * Real.cos t ^ 2 ≤ |Real.sin t| * 1 :=
          mul_le_mul_of_nonneg_left (Real.cos_sq_le_one t) (abs_nonneg _)
      _ = |Real.sin t| := mul_one _
      _ ≤ |t| := Real.abs_sin_le_abs
  rcases lt_or_ge b 0 with hb0 | hb0
  · have h1 : |b ^ (α/3)| ≤ (-b) ^ (α/3) := abs_rpow_le_rpow_neg hb0
    have h2 : (-b) ≤ |t| := by rw [← abs_of_neg hb0]; exact hle
    have h3 : (-b) ^ (α/3) ≤ |t| ^ (α/3) :=
      Real.rpow_le_rpow (le_of_lt (neg_pos.mpr hb0)) h2 (by linarith : (0:ℝ) ≤ α/3)
    linarith
  · have hle' : b ≤ |t| := by rwa [abs_of_nonneg hb0] at hle
    have h1 : |b ^ (α/3)| = b ^ (α/3) := abs_of_nonneg (Real.rpow_nonneg hb0 _)
    rw [h1]
    exact Real.rpow_le_rpow hb0 hle' (by linarith : (0:ℝ) ≤ α/3)

/-- **The pointwise two-sided bound**: for `|t| ≤ 1/2`,
`|sin t cos²t Γ̄(t)| ≤ 13 |t|^{1+α/3}`.

Indeed `|Γ̄(t)| ≤ |Γ(t)|/c + (5/4)|sin 2t| ≤ 10|t|^{α/3} + (5/2)|t|` (using `1/c ≤ 10` and
`|sin 2t| ≤ 2|t|`), hence `|sin t cos²t Γ̄(t)| ≤ |t|(10|t|^{α/3} + (5/2)|t|)
= 10|t|^{1+α/3} + (5/2)|t|²` and `|t|² ≤ |t|^{1+α/3}` because `α/3 ≤ 1` and `|t| ≤ 1`. -/
lemma abs_sin_cos_sq_GamBar_le_rpow (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1/4) {t : ℝ}
    (ht : |t| ≤ 1/2) :
    |Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t| ≤ 13 * |t| ^ (1 + α / 3) := by
  have hα0 : 0 ≤ α := le_of_lt hα
  have hc := (Work.Spaces.c_bounds α hα (by linarith)).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hc10 : 1 / Work.Spaces.c α ≤ 10 := by rw [div_le_iff₀ hcpos]; linarith
  have hΓ : |Work.Spaces.Gam α t| ≤ |t| ^ (α / 3) := abs_Gam_le_abs_rpow α hα0 t
  have h1 : |Work.Spaces.Gam α t / Work.Spaces.c α| ≤ 10 * |t| ^ (α / 3) := by
    rw [abs_div, abs_of_pos hcpos, div_eq_mul_one_div]
    calc |Work.Spaces.Gam α t| * (1 / Work.Spaces.c α) ≤ |t| ^ (α/3) * 10 :=
          mul_le_mul hΓ hc10 (by positivity) (by positivity)
      _ = 10 * |t| ^ (α/3) := by ring
  have hsin2 : |Real.sin (2 * t)| ≤ 2 * |t| := by
    have h := Real.abs_sin_le_abs (x := 2 * t)
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)] at h
    linarith
  have hGb : |Work.FTS.VocabO.GamBar α t| ≤ 10 * |t| ^ (α/3) + (5/2) * |t| := by
    rw [Work.FTS.VocabO.GamBar]
    have hsplit : |Work.Spaces.Gam α t / Work.Spaces.c α - 5/4 * Real.sin (2*t)|
        ≤ |Work.Spaces.Gam α t / Work.Spaces.c α| + |(5:ℝ)/4 * Real.sin (2*t)| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (Work.Spaces.Gam α t / Work.Spaces.c α) (-(5/4 * Real.sin (2*t)))
    have h2 : |(5:ℝ)/4 * Real.sin (2*t)| ≤ (5/2) * |t| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 5/4)]
      linarith
    linarith
  rw [abs_mul]
  have hbase : |Real.sin t * Real.cos t ^ 2| ≤ |t| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.cos t ^ 2)]
    calc |Real.sin t| * Real.cos t ^ 2 ≤ |Real.sin t| * 1 :=
          mul_le_mul_of_nonneg_left (Real.cos_sq_le_one t) (abs_nonneg _)
      _ = |Real.sin t| := mul_one _
      _ ≤ |t| := Real.abs_sin_le_abs
  have hmul1 : |t| * |t| ^ (α/3) = |t| ^ (1 + α/3) := by
    rw [Real.rpow_add' (abs_nonneg t) (by positivity : (1:ℝ) + α/3 ≠ 0), Real.rpow_one]
  have hsq : |t| * |t| ≤ |t| ^ (1 + α/3) := by
    rcases eq_or_lt_of_le (abs_nonneg t) with h | h
    · rw [← h, mul_zero, Real.zero_rpow (by positivity : (1:ℝ) + α/3 ≠ 0)]
    · conv_lhs => rw [← Real.rpow_one |t|, ← Real.rpow_add' (le_of_lt h) (by norm_num : (1:ℝ)+1 ≠ 0)]
      exact Real.rpow_le_rpow_of_exponent_ge h (by linarith [ht]) (by linarith)
  calc |Real.sin t * Real.cos t ^ 2| * |Work.FTS.VocabO.GamBar α t|
      ≤ |t| * (10 * |t|^(α/3) + (5/2) * |t|) := mul_le_mul hbase hGb (abs_nonneg _) (abs_nonneg _)
    _ = 10 * (|t| * |t|^(α/3)) + (5/2) * (|t| * |t|) := by ring
    _ ≤ 10 * |t|^(1+α/3) + (5/2) * |t|^(1+α/3) := by linarith [hmul1, hsq]
    _ = (25/2) * |t|^(1+α/3) := by ring
    _ ≤ 13 * |t|^(1+α/3) := by
        have hpos : 0 ≤ |t| ^ (1 + α/3) := Real.rpow_nonneg (abs_nonneg t) _
        linarith

/-- The source integrand `sin t cos²t Γ̄(t)` is continuous on the closed interval `[-1,1]`
(hence in particular on the *negative* range `[-1/2,0]`, which is all we need).  Continuity of
`Γ(t) = (sin t cos²t)^{α/3}` off the positive range uses `ContinuousOn.rpow_const`, whose side
condition `x ≠ 0 ∨ 0 ≤ p` holds because `p = α/3 ≥ 0`. -/
lemma continuousOn_sin_cos_sq_GamBar_Icc (α : ℝ) (hα : 0 ≤ α) :
    ContinuousOn (fun t : ℝ => Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t)
      (Set.Icc (-1) 1) := by
  have hGam : ContinuousOn (fun t : ℝ => Work.Spaces.Gam α t) (Set.Icc (-1:ℝ) 1) := by
    change ContinuousOn (fun t : ℝ => (Real.sin t * Real.cos t ^ 2) ^ (α / 3)) (Set.Icc (-1:ℝ) 1)
    exact ((Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn).rpow_const
      (fun t _ => Or.inr (by linarith))
  have hGb : ContinuousOn (fun t : ℝ => Work.FTS.VocabO.GamBar α t) (Set.Icc (-1:ℝ) 1) := by
    change ContinuousOn (fun t : ℝ => (Real.sin t * Real.cos t ^ 2) ^ (α / 3) / Work.Spaces.c α
      - (5 / 4) * Real.sin (2 * t)) (Set.Icc (-1:ℝ) 1)
    exact (hGam.div_const _).sub (by fun_prop)
  exact (by fun_prop : ContinuousOn (fun t : ℝ => Real.sin t * Real.cos t ^ 2)
    (Set.Icc (-1:ℝ) 1)).mul hGb

/-- **Two-sided form of `Gzero_eq_neg`**: for `|θ| ≤ 1/2`,
`G₀(θ) = −∫_0^θ sin t cos²t Γ̄(t) dt`.

For `θ ≥ 0` this is `Gzero_eq_neg`.  For `θ < 0` use the additivity of the interval integral
through `0`: `∫_θ^{π/2} = ∫_θ^0 + ∫_0^{π/2}`, and `∫_0^{π/2} sin t cos²t Γ̄(t) dt = G₀(0) = 0`
(the moment condition `Gzero_zero`), while `∫_θ^0 = −∫_0^θ`. -/
lemma Gzero_eq_neg_of_abs_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1/4) {θ : ℝ}
    (hθ : |θ| ≤ 1/2) :
    Work.FTS.PhiStar.Gzero α θ
      = -∫ t in 0..θ, Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t := by
  have hθ1 : θ ≤ 1/2 := (abs_le.mp hθ).2
  have hθm : -(1/2) ≤ θ := (abs_le.mp hθ).1
  rcases lt_or_ge θ 0 with hθneg | hθnn
  · have hcont : ContinuousOn (fun t : ℝ => Real.sin t * Real.cos t ^ 2 *
        Work.FTS.VocabO.GamBar α t) (Set.Icc (-(1/2)) 0) :=
      (continuousOn_sin_cos_sq_GamBar_Icc α (le_of_lt hα)).mono (by
        intro t ht
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    have hsub : Set.uIcc θ 0 ⊆ Set.Icc (-(1/2)) 0 := by
      intro t ht
      rw [Set.uIcc_of_le (le_of_lt hθneg)] at ht
      exact ⟨le_trans hθm ht.1, ht.2⟩
    have hint1 : IntervalIntegrable (fun t : ℝ => Real.sin t * Real.cos t ^ 2 *
        Work.FTS.VocabO.GamBar α t) volume θ 0 := (hcont.mono hsub).intervalIntegrable
    have hint2 : IntervalIntegrable (fun t : ℝ => Real.sin t * Real.cos t ^ 2 *
        Work.FTS.VocabO.GamBar α t) volume 0 (π / 2) :=
      intervalIntegrable_GamBar α (le_of_lt hα) le_rfl le_rfl (by linarith [Real.pi_pos])
    have hadd := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
    have hzero : ∫ t in 0..(π / 2), Real.sin t * Real.cos t ^ 2 *
        Work.FTS.VocabO.GamBar α t = 0 := by
      have h := Gzero_zero α hα hα1
      simpa only [Work.FTS.PhiStar.Gzero] using h
    have hG : Work.FTS.PhiStar.Gzero α θ = ∫ t in θ..0, Real.sin t * Real.cos t ^ 2 *
        Work.FTS.VocabO.GamBar α t := by
      rw [Work.FTS.PhiStar.Gzero, ← hadd, hzero, add_zero]
    rw [hG, intervalIntegral.integral_symm (f := fun t => Real.sin t * Real.cos t ^ 2 *
      Work.FTS.VocabO.GamBar α t) 0 θ]
  · exact Gzero_eq_neg α hα hα1 θ
      ⟨hθnn, by have := Real.pi_gt_three; linarith⟩

/-- Two-sided power bound for `G₀` near the left endpoint of `Iθ`: `|G₀(θ)| ≤ C|θ|^{2+α/3}`
for `|θ| ≤ 1/2`.

This is the quantitative form of `G₀(θ) = -∫_0^θ sin t cos²t Γ̄(t) dt` (`Gzero_eq_neg`, with
`Gzero α 0 = 0` the moment condition `Gzero_zero`): the integrand is
`|sin t cos²t Γ̄(t)| ≤ |t|(|t|^{α/3}/c + (5/2)|t|) ≤ C|t|^{1+α/3}` for `|t| ≤ 1/2`, using
`|sin t| ≤ |t|`, `|cos t| ≤ 1`, `|Γ(t)| = |(sin t cos²t)^{α/3}| ≤ |t|^{α/3}` (for `t < 0` as
well: `Real.rpow` of a negative base is `exp(log|x|·y)·cos(yπ)`, whose modulus is
`≤ |x|^y`) and `1/c ≤ 10` (`Spaces.c_bounds`); integrating gives `C|θ|^{2+α/3}`, since
`|θ|³ ≤ C'|θ|^{2+α/3}` for `|θ| ≤ 1/2`.  The estimate improves the existing
`Gzero_abs_le_sq` (`|G₀ θ| ≤ 7θ²` for `θ ∈ [0,1]`, one-sided) by the factor `|θ|^{α/3}`, and
it is two-sided (for `θ < 0` use the additivity of the interval integral through `0`). -/
theorem Gzero_rpow_zero (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ, |θ| ≤ 1 / 2 →
      |Work.FTS.PhiStar.Gzero α θ| ≤ C * |θ| ^ (2 + α / 3) := by
  refine ⟨20, by norm_num, fun θ hθ => ?_⟩
  have hp : (0:ℝ) ≤ 1 + α/3 := by linarith
  have hθ1 : θ ≤ 1/2 := (abs_le.mp hθ).2
  have hθm : -(1/2) ≤ θ := (abs_le.mp hθ).1
  have hpt : ∀ t : ℝ, |t| ≤ 1/2 → |Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t|
      ≤ 13 * |t| ^ (1 + α/3) := fun t ht => abs_sin_cos_sq_GamBar_le_rpow α hα hα1 ht
  rcases lt_or_ge θ 0 with hθneg | hθnn
  · -- `θ < 0`: integrate the two-sided pointwise bound from `θ` to `0`
    have hsub : Set.uIcc θ 0 ⊆ Set.Icc (-1) 1 := by
      intro t ht
      rw [Set.uIcc_of_le (le_of_lt hθneg)] at ht
      exact ⟨by linarith [ht.1, hθm], by linarith [ht.2]⟩
    have hintf : IntervalIntegrable (fun t : ℝ => Real.sin t * Real.cos t ^ 2 *
        Work.FTS.VocabO.GamBar α t) volume θ 0 :=
      ((continuousOn_sin_cos_sq_GamBar_Icc α (le_of_lt hα)).mono hsub).intervalIntegrable
    have hintg : IntervalIntegrable (fun t : ℝ => 13 * |t| ^ (1 + α/3)) volume θ 0 := by
      have hcon : Continuous fun t : ℝ => 13 * |t| ^ (1 + α/3) :=
        continuous_const.mul ((Real.continuous_rpow_const hp).comp continuous_abs)
      exact hcon.intervalIntegrable _ _
    have hintc : IntervalIntegrable (fun _ : ℝ => 13 * |θ| ^ (1 + α/3)) volume θ 0 :=
      continuous_const.intervalIntegrable _ _
    have hGl : Work.FTS.PhiStar.Gzero α θ = ∫ t in θ..0, Real.sin t * Real.cos t ^ 2 *
        Work.FTS.VocabO.GamBar α t := by
      rw [Gzero_eq_neg_of_abs_le α hα hα1 hθ, ← intervalIntegral.integral_symm
        (f := fun t => Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t) 0 θ]
    calc |Work.FTS.PhiStar.Gzero α θ|
        = |∫ t in θ..0, Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t| := by
          rw [hGl]
      _ ≤ ∫ t in θ..0, |Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t| :=
          intervalIntegral.abs_integral_le_integral_abs (le_of_lt hθneg)
      _ ≤ ∫ t in θ..0, 13 * |t| ^ (1 + α/3) := by
          refine intervalIntegral.integral_mono_on (le_of_lt hθneg) hintf.abs hintg
            (fun t ht => ?_)
          have habs : |t| ≤ |θ| := by
            rw [abs_of_neg hθneg]
            exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2, hθneg]⟩
          exact hpt t (by linarith [habs, hθ])
      _ ≤ ∫ t in θ..0, 13 * |θ| ^ (1 + α/3) := by
          refine intervalIntegral.integral_mono_on (le_of_lt hθneg) hintg hintc
            (fun t ht => ?_)
          have habs : |t| ≤ |θ| := by
            rw [abs_of_neg hθneg]
            exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2, hθneg]⟩
          have h := Real.rpow_le_rpow (abs_nonneg t) habs hp
          linarith
      _ = 13 * |θ| ^ (1 + α/3) * |θ| := by
          rw [intervalIntegral.integral_const, smul_eq_mul, abs_of_neg hθneg]; ring
      _ = 13 * |θ| ^ (2 + α/3) := by
          rw [show (2:ℝ) + α/3 = 1 + (1 + α/3) by ring,
            Real.rpow_add' (abs_nonneg θ) (by positivity : (1:ℝ) + (1 + α/3) ≠ 0),
            Real.rpow_one]
          ring
      _ ≤ 20 * |θ| ^ (2 + α/3) := by
          have : (0:ℝ) ≤ |θ| ^ (2 + α/3) := Real.rpow_nonneg (abs_nonneg θ) _
          linarith
  · -- `θ ≥ 0`: `Gzero_eq_neg` plus the one-sided pointwise bound
    have hsub : Set.uIcc 0 θ ⊆ Set.Icc (-1) 1 := by
      intro t ht
      rw [Set.uIcc_of_le hθnn] at ht
      exact ⟨by linarith [ht.1], by linarith [ht.2, hθ1]⟩
    have hintf : IntervalIntegrable (fun t : ℝ => Real.sin t * Real.cos t ^ 2 *
        Work.FTS.VocabO.GamBar α t) volume 0 θ :=
      ((continuousOn_sin_cos_sq_GamBar_Icc α (le_of_lt hα)).mono hsub).intervalIntegrable
    have hintg : IntervalIntegrable (fun t : ℝ => 13 * t ^ (1 + α/3)) volume 0 θ :=
      (continuous_const.mul (Real.continuous_rpow_const hp)).intervalIntegrable _ _
    have hintc : IntervalIntegrable (fun _ : ℝ => 13 * θ ^ (1 + α/3)) volume 0 θ :=
      continuous_const.intervalIntegrable _ _
    calc |Work.FTS.PhiStar.Gzero α θ|
        = |∫ t in 0..θ, Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t| := by
          rw [Gzero_eq_neg_of_abs_le α hα hα1 hθ, abs_neg]
      _ ≤ ∫ t in 0..θ, |Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t| :=
          intervalIntegral.abs_integral_le_integral_abs hθnn
      _ ≤ ∫ t in 0..θ, 13 * t ^ (1 + α/3) := by
          refine intervalIntegral.integral_mono_on hθnn hintf.abs hintg (fun t ht => ?_)
          have ht' : |t| ≤ 1/2 := by rw [abs_of_nonneg ht.1]; linarith [ht.2, hθ1]
          have h := hpt t ht'
          rwa [abs_of_nonneg ht.1] at h
      _ ≤ ∫ t in 0..θ, 13 * θ ^ (1 + α/3) := by
          refine intervalIntegral.integral_mono_on hθnn hintg hintc (fun t ht => ?_)
          have h := Real.rpow_le_rpow ht.1 ht.2 hp
          linarith
      _ = 13 * θ ^ (1 + α/3) * θ := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      _ = 13 * |θ| ^ (2 + α/3) := by
          rw [abs_of_nonneg hθnn, show (2:ℝ) + α/3 = 1 + (1 + α/3) by ring,
            Real.rpow_add' hθnn (by positivity : (1:ℝ) + (1 + α/3) ≠ 0), Real.rpow_one]
          ring
      _ ≤ 20 * |θ| ^ (2 + α/3) := by
          have : (0:ℝ) ≤ |θ| ^ (2 + α/3) := Real.rpow_nonneg (abs_nonneg θ) _
          linarith

end Work.FTS.PhiStar.Psi0Est
end
-- ===== merged: Submission.Work.FTS.PhiStar.Psi0Ode =====
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

/-! ## Global continuity of the source integrands -/

/-- The integrand `S C² Γ` of `Ψ_Γ` is continuous on all of `ℝ` (for `α ≥ 0`). -/
lemma continuous_sin_cos_sq_Gam' (α : ℝ) (hα : 0 ≤ α) :
    Continuous fun t : ℝ => Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α t :=
  (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).mul
    (((Real.continuous_sin.mul (Real.continuous_cos.pow 2))).rpow_const
      (fun _ => Or.inr (by positivity)))

/-- The source integrand `S C² Γ̄` is continuous on all of `ℝ` (for `α ≥ 0`). -/
lemma continuous_sin_cos_sq_GamBar' (α : ℝ) (hα : 0 ≤ α) :
    Continuous fun t : ℝ => Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t := by
  have h1 := continuous_sin_cos_sq_Gam' α hα
  rw [show (fun t : ℝ => Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t)
      = fun t => (Real.sin t * Real.cos t ^ 2 * Work.Spaces.Gam α t) / Work.Spaces.c α
        - (5 / 2) * (Real.sin t ^ 2 * Real.cos t ^ 3) by
    funext t; rw [Work.FTS.VocabO.GamBar, Real.sin_two_mul]; ring]
  exact (h1.div_const _).sub (by fun_prop)

/-- `G₀` is continuous on all of `ℝ`. -/
lemma continuous_Gzero (α : ℝ) (hα : 0 ≤ α) : Continuous (Gzero α) := by
  have hF := continuous_sin_cos_sq_GamBar' α hα
  have hpr : Continuous fun θ : ℝ =>
      ∫ t in (0:ℝ)..θ, Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t := by
    rw [continuous_iff_continuousAt]
    intro θ
    exact (intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable 0 θ)
      (Continuous.stronglyMeasurableAtFilter hF volume (𝓝 θ)) hF.continuousAt).continuousAt
  have hfun : Gzero α = fun θ => (∫ t in (0:ℝ)..(π / 2),
      Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t)
      - ∫ t in (0:ℝ)..θ, Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t := by
    funext θ
    simp only [Gzero]
    have h1 : IntervalIntegrable (fun t : ℝ =>
        Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t) volume 0 θ :=
      hF.intervalIntegrable 0 θ
    have h2 : IntervalIntegrable (fun t : ℝ =>
        Real.sin t * Real.cos t ^ 2 * Work.FTS.VocabO.GamBar α t) volume θ (π / 2) :=
      hF.intervalIntegrable θ (π / 2)
    have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
    linarith [hadd]
  rw [hfun]
  exact continuous_const.sub hpr

lemma measurable_Gzero (α : ℝ) (hα : 0 ≤ α) : Measurable (Gzero α) :=
  (continuous_Gzero α hα).measurable

lemma measurable_Pfun (α : ℝ) (hα : 0 ≤ α) : Measurable (Pfun α) :=
  (measurable_Gzero α hα).div (by fun_prop : Measurable fun t : ℝ => 2 * Real.cos t ^ 3)

/-! ## `w₀ = ∫_0^θ P/sin²` -/

/-- `w₀(α,θ) = ∫_0^θ P(t)/sin²t dt`. -/
def wZer (α : ℝ) (θ : ℝ) : ℝ := ∫ t in (0:ℝ)..θ, Pfun α t / (Real.sin t) ^ 2

/-- `P/sin²` is integrable on `[0,π/2]` (for `0 < α ≤ 1/4`). -/
lemma integrableOn_Pfun_div (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    MeasureTheory.IntegrableOn (fun t : ℝ => Pfun α t / (Real.sin t) ^ 2)
      (Set.uIcc (0:ℝ) (π / 2)) volume := by
  refine MeasureTheory.IntegrableOn.of_bound (by simp) ?_ 500 ?_
  · exact (Measurable.div (measurable_Pfun α (le_of_lt hα)) (by fun_prop :
      Measurable fun t : ℝ => (Real.sin t) ^ 2)).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIcc] with t ht
    rw [Real.norm_eq_abs]
    have ht' : t ∈ Set.Icc (0:ℝ) (π / 2) := by
      rwa [Set.uIcc_of_le (by linarith [Real.pi_pos])] at ht
    exact Pfun_div_sin_sq_le α hα hα1 ht'

/-- `P/sin²` is interval-integrable on `[0,θ]` for `θ ≤ π/2`. -/
lemma intervalIntegrable_Pfun_div (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ π / 2) :
    IntervalIntegrable (fun t : ℝ => Pfun α t / (Real.sin t) ^ 2) volume 0 θ := by
  rw [intervalIntegrable_iff]
  refine (integrableOn_Pfun_div α hα hα1).mono_set (fun t ht => ?_)
  rw [Set.uIoc_of_le hθ0] at ht
  rw [Set.uIcc_of_le (by linarith [Real.pi_pos] : (0:ℝ) ≤ π / 2)]
  exact ⟨le_of_lt ht.1, le_trans ht.2 hθ1⟩

/-- `w₀` is continuous on `[0,π/2]`. -/
lemma continuousOn_wZer (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    ContinuousOn (wZer α) (Set.Icc 0 (π / 2)) := by
  have hint := integrableOn_Pfun_div α hα hα1
  have h := intervalIntegral.continuousOn_primitive_interval (a := (0:ℝ)) (b := π / 2) hint
  rw [Set.uIcc_of_le (by linarith [Real.pi_pos] : (0:ℝ) ≤ π / 2)] at h
  show ContinuousOn (fun x : ℝ => ∫ t in (0:ℝ)..x, Pfun α t / (Real.sin t) ^ 2)
    (Set.Icc 0 (π / 2))
  exact h

/-- `w₀` is bounded by `500·(π/2)` on `[0,π/2]`. -/
lemma abs_wZer_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 (π / 2)) : |wZer α θ| ≤ 500 * (π / 2) := by
  rw [wZer]
  refine le_trans (intervalIntegral.abs_integral_le_integral_abs hθ.1) ?_
  have h1 : IntervalIntegrable (fun t : ℝ => |Pfun α t / (Real.sin t) ^ 2|) volume 0 θ :=
    (intervalIntegrable_Pfun_div α hα hα1 hθ.1 hθ.2).abs
  have h2 : IntervalIntegrable (fun _ : ℝ => (500 : ℝ)) volume 0 θ := intervalIntegrable_const
  have hm := intervalIntegral.integral_mono_on hθ.1 h1 h2 (fun t ht =>
    Pfun_div_sin_sq_le α hα hα1 ⟨ht.1, le_trans ht.2 hθ.2⟩)
  have hv : (∫ _ in (0:ℝ)..θ, (500 : ℝ)) = 500 * θ := by
    rw [intervalIntegral.integral_const]; ring
  rw [hv] at hm
  linarith [hm, hθ.2, Real.pi_pos]

/-- **The derivative of `w₀`**: `w₀' = P/sin²θ`. -/
theorem hasDerivAt_wZer (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (wZer α) (Pfun α θ / (Real.sin θ) ^ 2) θ := by
  have hint := intervalIntegrable_Pfun_div α hα hα1 (le_of_lt hθ.1) (le_of_lt hθ.2)
  have hcont : ContinuousOn (fun t : ℝ => Pfun α t / (Real.sin t) ^ 2)
      (Set.Ioo 0 (π / 2)) := by
    refine ((continuous_Gzero α (le_of_lt hα)).continuousOn.div
      (by fun_prop : ContinuousOn (fun t : ℝ => 2 * Real.cos t ^ 3) _) ?_).div
      (by fun_prop : ContinuousOn (fun t : ℝ => (Real.sin t) ^ 2) _) ?_
    · intro t ht
      have hc : 0 < Real.cos t :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
      exact ne_of_gt (by positivity)
    · intro t ht
      have hs : 0 < Real.sin t :=
        Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_gt_three])
      exact ne_of_gt (by positivity)
  have hcat : ContinuousAt (fun t : ℝ => Pfun α t / (Real.sin t) ^ 2) θ :=
    hcont.continuousAt (isOpen_Ioo.mem_nhds hθ)
  have hmeas : StronglyMeasurableAtFilter (fun t : ℝ => Pfun α t / (Real.sin t) ^ 2)
      (𝓝 θ) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hcont θ hθ
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas hcat

/-- The derivative of `P/sin²` at an interior point. -/
theorem hasDerivAt_Pfun_div (α : ℝ) (hα : 0 ≤ α) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun t : ℝ => Pfun α t / (Real.sin t) ^ 2)
      (deriv (Pfun α) θ / (Real.sin θ) ^ 2
        - Pfun α θ * (2 * Real.sin θ * Real.cos θ) / (Real.sin θ) ^ 4) θ := by
  have hS : Real.sin θ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1
    (by linarith [hθ.2, Real.pi_gt_three]))
  have hden : HasDerivAt (fun t : ℝ => (Real.sin t) ^ 2) (2 * Real.sin θ * Real.cos θ) θ := by
    have h := (Real.hasDerivAt_sin θ).pow 2
    rw [show ((fun t : ℝ => Real.sin t) ^ 2) = fun t : ℝ => Real.sin t ^ 2 from by
      funext t; rw [Pi.pow_apply]] at h
    simpa using h
  have hnum : HasDerivAt (Pfun α) (deriv (Pfun α) θ) θ :=
    (hasDerivAt_Pfun α hα hθ).differentiableAt.hasDerivAt
  have hq := hnum.div hden (pow_ne_zero 2 hS)
  have hfun : (fun t : ℝ => Pfun α t / (Real.sin t) ^ 2)
      = (Pfun α / fun t : ℝ => (Real.sin t) ^ 2) := rfl
  rw [hfun]
  convert hq using 1
  field_simp

/-! ## `Kc` and `psiSol` -/

/-- The constant fixing the moment: `Kc = −(15/2)∫_0^{π/2} sin²θ cos³θ w₀(θ)dθ`. -/
def Kc (α : ℝ) : ℝ := -(15 / 2) * ∫ θ in (0:ℝ)..(π / 2),
  Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ

/-- **The explicit angular model**: `ψ(θ) = sin 2θ · (Kc + w₀(θ))`. -/
def psiSol (α : ℝ) : ℝ → ℝ := fun θ => Real.sin (2 * θ) * (Kc α + wZer α θ)

lemma continuousOn_wZer' (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    ContinuousOn (fun θ => Real.sin θ ^ 2 * Real.cos θ ^ 3 * wZer α θ)
      (Set.Icc 0 (π / 2)) :=
  (by fun_prop : ContinuousOn (fun θ : ℝ => Real.sin θ ^ 2 * Real.cos θ ^ 3)
    (Set.Icc 0 (π / 2))).mul (continuousOn_wZer α hα hα1)

/-- `psiSol 0 = 0`. -/
lemma psiSol_zero (α : ℝ) : psiSol α 0 = 0 := by
  simp [psiSol]

/-- `psiSol (π/2) = 0`. -/
lemma psiSol_pi_div_two (α : ℝ) : psiSol α (π / 2) = 0 := by
  rw [psiSol, show 2 * (π / 2) = π from by ring, Real.sin_pi]
  ring

/-- `psiSol` is continuous on `[0,π/2]`. -/
lemma continuousOn_psiSol (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    ContinuousOn (psiSol α) (Set.Icc 0 (π / 2)) :=
  (by fun_prop : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Icc 0 (π / 2))).mul
    (continuousOn_const.add (continuousOn_wZer α hα hα1))

/-- `psiSol` is `C^∞` on `(0,π/2)`. -/
lemma contDiffOn_psiSol (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    ContDiffOn ℝ (∞ : ℕ∞ω) (psiSol α) (Set.Ioo 0 (π / 2)) := by
  have hw : ContDiffOn ℝ (∞ : ℕ∞ω) (wZer α) (Set.Ioo 0 (π / 2)) := by
    have hP : ContDiffOn ℝ (∞ : ℕ∞ω) (fun t : ℝ => Pfun α t / (Real.sin t) ^ 2)
        (Set.Ioo 0 (π / 2)) := by
      refine (contDiffOn_Pfun α (le_of_lt hα)).div (by fun_prop) ?_
      intro t ht
      exact pow_ne_zero 2 (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ht.1
        (by linarith [ht.2, Real.pi_gt_three])))
    rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo]
    exact ⟨fun t ht => (hasDerivAt_wZer α hα hα1 ht).differentiableAt.differentiableWithinAt,
      hP.congr (fun t ht => (hasDerivAt_wZer α hα hα1 ht).deriv)⟩
  exact (by fun_prop : ContDiffOn ℝ (∞ : ℕ∞ω) (fun θ : ℝ => Real.sin (2 * θ))
    (Set.Ioo 0 (π / 2))).mul (contDiffOn_const.add hw)

/-! ## The model equation -/

/-- **The angular model equation**: `Lzero1 ψ = Γ̄` on `(0,π/2)`. -/
theorem psiSol_ode (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.FTS.EllipticEst.Lzero1 (psiSol α) θ = Work.FTS.VocabO.GamBar α θ := by
  have hS : Real.sin θ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1
    (by linarith [hθ.2, Real.pi_gt_three]))
  have hC : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  set w : ℝ → ℝ := fun t => Kc α + wZer α t with hw
  have hd1 : DifferentiableOn ℝ (fun t : ℝ => 2 * w t) (Set.Ioo 0 (π / 2)) := fun t ht =>
    ((hasDerivAt_wZer α hα hα1 ht).const_add (Kc α)).const_mul 2
      |>.differentiableAt.differentiableWithinAt
  have hd2 : DifferentiableOn ℝ (fun t : ℝ => deriv (fun s : ℝ => 2 * w s) t)
      (Set.Ioo 0 (π / 2)) := by
    intro t ht
    have heq : deriv (fun s : ℝ => 2 * w s) = fun s => 2 * deriv w s := by
      funext s; rw [Work.Spaces.deriv_const_mul']
    rw [heq]
    have h2 : DifferentiableAt ℝ (fun s : ℝ => 2 * (Pfun α s / (Real.sin s) ^ 2)) t :=
      ((hasDerivAt_Pfun_div α (le_of_lt hα) ht).const_mul 2).differentiableAt
    have hev : (fun s : ℝ => 2 * deriv w s)
        =ᶠ[𝓝 t] fun s => 2 * (Pfun α s / (Real.sin s) ^ 2) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      rw [(hasDerivAt_wZer α hα hα1 hs).const_add (Kc α) |>.deriv]
    exact (h2.congr_of_eventuallyEq hev).differentiableWithinAt
  have hsub := Work.FTS.H2.StarPkg.LzeroSubst.lzero_sin_cos_mul (fun _ t : ℝ => 2 * w t)
    (z := 0) (θ := θ) hθ hd1 hd2
  have hpth : ∀ t ∈ Set.Ioo (0:ℝ) (π / 2),
      Work.Spaces.pth (fun _ s : ℝ => 2 * w s) 0 t = 2 * (Pfun α t / (Real.sin t) ^ 2) := by
    intro t ht
    rw [Work.Spaces.pth, Work.Spaces.deriv_const_mul']
    exact congrArg (fun x => 2 * x) ((hasDerivAt_wZer α hα hα1 ht).const_add (Kc α) |>.deriv)
  have hpth2 : Work.Spaces.pthIter 2 (fun _ s : ℝ => 2 * w s) 0 θ
      = 2 * (deriv (Pfun α) θ / (Real.sin θ) ^ 2
        - Pfun α θ * (2 * Real.sin θ * Real.cos θ) / (Real.sin θ) ^ 4) := by
    show deriv (fun t : ℝ => Work.Spaces.pth (fun _ s : ℝ => 2 * w s) 0 t) θ = _
    have hev : (fun t : ℝ => Work.Spaces.pth (fun _ s : ℝ => 2 * w s) 0 t)
        =ᶠ[𝓝 θ] fun t => 2 * (Pfun α t / (Real.sin t) ^ 2) := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
      exact hpth t ht
    rw [hev.deriv_eq, Work.Spaces.deriv_const_mul']
    exact congrArg (fun x => 2 * x) (hasDerivAt_Pfun_div α (le_of_lt hα) hθ).deriv
  have hfun : (fun x t : ℝ => psiSol α t)
      = fun z t : ℝ => Real.sin t * Real.cos t * (2 * w t) := by
    funext x t
    rw [psiSol, hw, Real.sin_two_mul]; ring
  rw [Work.FTS.EllipticEst.Lzero1_eq_Lzero]
  simp only []
  rw [hfun, hsub, hpth θ hθ, hpth2, (hasDerivAt_Pfun α (le_of_lt hα) hθ).deriv]
  field_simp
  ring

end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeMain =====
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

/-! ## The facts supplied by the two delegated modules -/

/-- **The `ℋ⁶`-weighted consequences of `hHk`** (verbatim the conclusion of
`Work.FTS.StrongEps.EComparison.SlotsZeroModeL2`). -/
def L2Facts (α : ℝ) (Φ : ℝ → ℝ → ℝ) : Prop :=
  (∀ m : ℕ,
    MeasureTheory.LocallyIntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) (Set.Ioi 0) ∧
    MeasureTheory.IntegrableOn (fun z => (∫ θ in Work.Spaces.Iθ,
      Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2 * z ^ (-4 : ℝ))
      (Set.Ioi 0)) ∧
  (∀ z ∈ Set.Ioi (0 : ℝ),
    MeasureTheory.IntegrableOn (fun θ => |Φ z θ|) Work.Spaces.Iθ) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ z ∈ Set.Ioi (0 : ℝ),
    ∫ θ in Work.Spaces.Iθ, |Φ z θ| ≤ C * Real.sqrt (sliceEnergy Φ z)) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ z ∈ Set.Ioi (0 : ℝ), ∀ δ ∈ Set.Ioc (0 : ℝ) (π / 4),
    (∫ θ in Set.Ioo 0 δ, |Φ z θ|
        ≤ C * Real.sqrt (sliceEnergy Φ z) * δ ^ ((3 + Work.Spaces.eta) / 2)) ∧
    (∫ θ in Set.Ioo (π / 2 - δ) (π / 2), |Φ z θ|
        ≤ C * Real.sqrt (sliceEnergy Φ z) * δ ^ ((3 + Work.Spaces.eta) / 2))) ∧
  (∀ a b : ℝ, 0 < a → a ≤ b →
    MeasureTheory.IntegrableOn (fun z => Real.sqrt (sliceEnergy Φ z)) (Set.Icc a b)) ∧
  (∀ a b : ℝ, 0 < a → a ≤ b →
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Φ z θ ^ 2 * rootWeight θ) (Set.Icc a b)) ∧
  (∀ a b : ℝ, 0 < a → a ≤ b →
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, |Φ z θ|) (Set.Icc a b))

/-- **The facts about the shrinking cut-off** (verbatim the conclusion of
`Work.FTS.StrongEps.EComparison.SlotsZeroCutoff`). -/
def CutFacts (m : ℕ) : Prop :=
  (∀ n k : ℕ, ContDiff ℝ k (angCut n)) ∧
  (∀ n : ℕ, tsupport (angCut n) ⊆ Set.Icc (delta n) (π / 2 - delta n)) ∧
  (∀ θ : ℝ, 0 < θ → θ < π / 2 → ∀ᶠ n in atTop, angCut n θ = 1) ∧
  (∀ n : ℕ, ∀ θ : ℝ, 0 ≤ angCut n θ ∧ angCut n θ ≤ 1) ∧
  (∀ n : ℕ, 0 < delta n) ∧
  Tendsto delta atTop (𝓝 0) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ θ : ℝ, 0 < θ → θ < π / 2 →
    |Work.FTS.EllipticEst.Lzero1 (fun t => angCut n t * Work.FTS.PhiStar.Gegenbauer.eFam m t) θ
        - angCut n θ * Work.FTS.EllipticEst.Lzero1 (Work.FTS.PhiStar.Gegenbauer.eFam m) θ|
      ≤ C / delta n * layerInd n θ)

/-! ## Elementary accessors of the cut-off data -/

lemma CutFacts.delta_pos {m : ℕ} (h : CutFacts m) (n : ℕ) : 0 < delta n := h.2.2.2.2.1 n

lemma CutFacts.tsupport_subset {m : ℕ} (h : CutFacts m) (n : ℕ) :
    tsupport (angCut n) ⊆ Set.Icc (delta n) (π / 2 - delta n) := h.2.1 n

lemma CutFacts.bounds {m : ℕ} (h : CutFacts m) (n : ℕ) (θ : ℝ) :
    0 ≤ angCut n θ ∧ angCut n θ ≤ 1 := h.2.2.2.1 n θ




/-- `angCut n = 1` off the layer. -/
lemma CutFacts.eq_one_off_layer {m : ℕ} (h : CutFacts m) (n : ℕ) {θ : ℝ}
    (hθ1 : 2 * delta n ≤ θ) (hθ2 : θ ≤ π / 2 - 2 * delta n) : angCut n θ = 1 := by
  have hd := h.delta_pos n
  have h1 : (1 : ℝ) ≤ θ / delta n - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hd]; linarith
  have h2 : (1 : ℝ) ≤ (π / 2 - θ) / delta n - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hd]; linarith
  simp only [angCut, Real.smoothTransition.one_of_one_le h1,
    Real.smoothTransition.one_of_one_le h2, mul_one]

/-! ## Localisation of a compactly supported radial function -/

/-- A compactly supported function on `(0,∞)` is supported in an interval `[a,b] ⊆ (0,∞)`. -/
theorem exists_Icc_of_tsupport_subset {ρ : ℝ → ℝ} (hρc : HasCompactSupport ρ)
    (hρs : tsupport ρ ⊆ Set.Ioi 0) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ tsupport ρ ⊆ Set.Icc a b := by
  rcases eq_empty_or_nonempty (tsupport ρ) with h | h
  · exact ⟨1, 1, by norm_num, le_rfl, by rw [h]; exact Set.empty_subset _⟩
  · obtain ⟨x, hx, hmin⟩ := hρc.isCompact.exists_isMinOn h continuous_id.continuousOn
    obtain ⟨y, hy, hmax⟩ := hρc.isCompact.exists_isMaxOn h continuous_id.continuousOn
    exact ⟨x, y, hρs hx, (isMinOn_iff.mp hmin) y hy,
      fun z hz => ⟨(isMinOn_iff.mp hmin) z hz, (isMaxOn_iff.mp hmax) z hz⟩⟩

/-- Integrability on the open quadrant of a function which is continuous on a compact box
contained in `Q0` and vanishes outside it. -/
theorem integrableOn_Q0_of_box {f : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d) (hd : d < π / 2)
    (hvan : ∀ p : ℝ × ℝ, p ∉ Set.Icc a b ×ˢ Set.Icc c d → f p = 0)
    (hcont : ContinuousOn f (Set.Icc a b ×ˢ Set.Icc c d)) :
    MeasureTheory.IntegrableOn f Work.FTS.EllipticEst.Q0 := by
  have hKsub : Set.Icc a b ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 := fun p hp =>
    Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨lt_of_lt_of_le ha hp.1.1, lt_of_lt_of_le hc hp.2.1, lt_of_le_of_lt hp.2.2 hd⟩
  have hKcomp : IsCompact (Set.Icc a b ×ˢ Set.Icc c d) := isCompact_Icc.prod isCompact_Icc
  have hKint : IntegrableOn f (Set.Icc a b ×ˢ Set.Icc c d) :=
    hcont.integrableOn_compact hKcomp
  have hsupp : Function.support f ⊆ Set.Icc a b ×ˢ Set.Icc c d := fun p hp =>
    by_contra fun h => hp (hvan p h)
  exact (hKint.mono_set (Set.inter_subset_right.trans hsupp)).of_inter_support
    Work.FTS.EllipticEst.isOpen_Q0.measurableSet

/-! ## `bslOp` of a smooth function is continuous on the open quadrant -/

theorem continuousOn_bslOp_of_smoothOpen {α : ℝ} {ψ : ℝ → ℝ → ℝ}
    (hψ : Work.FTS.EllipticEst.SmoothOpen ψ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.bslOp α ψ p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 ψ p.1 p.2)
      Work.FTS.EllipticEst.Q0 := (hψ.pzIter 2).continuousOn
  have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz ψ p.1 p.2)
      Work.FTS.EllipticEst.Q0 := (hψ.pz).continuousOn
  have h3 : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Lzero ψ p.1 p.2)
      Work.FTS.EllipticEst.Q0 := Work.EllipticEst.ModalSolution.continuousOn_Lzero hψ
  have hz : ContinuousOn (fun p : ℝ × ℝ => p.1) Work.FTS.EllipticEst.Q0 := continuousOn_fst
  have h4 : ContinuousOn (fun p : ℝ × ℝ => -(α ^ 2 * p.1 ^ 2)) Work.FTS.EllipticEst.Q0 :=
    (continuousOn_const.mul (hz.pow 2)).neg
  have h5 : ContinuousOn (fun p : ℝ × ℝ => α * (5 + α) * p.1) Work.FTS.EllipticEst.Q0 :=
    continuousOn_const.mul hz
  have hmain : ContinuousOn (fun p : ℝ × ℝ =>
      -(α ^ 2 * p.1 ^ 2) * Work.Spaces.pzIter 2 ψ p.1 p.2
        - (α * (5 + α) * p.1) * Work.Spaces.pz ψ p.1 p.2
        + Work.Elliptic.Lzero ψ p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    ((h4.mul h1).sub (h5.mul h2)).add h3
  simpa only [Work.Elliptic.bslOp_apply] using hmain

theorem continuousOn_weight (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => bslWeight α p) Work.FTS.EllipticEst.Q0 := by
  refine ContinuousOn.mul ?_ ?_
  · exact continuousOn_fst.rpow_const
      (fun p hp => Or.inl (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1))
  · exact (Real.continuous_cos.comp continuous_snd).continuousOn

/-! ## The cut-off test functions -/

/-- The cut-off test function `ρ(z)·(χ_n(θ)·e_m(θ))`. -/
def modeTest (m : ℕ) (ρ : ℝ → ℝ) (n : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => ρ z * (angCut n θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ)

@[simp] lemma modeTest_apply (m n : ℕ) (ρ : ℝ → ℝ) (z θ : ℝ) :
    modeTest m ρ n z θ = ρ z * (angCut n θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ) := rfl

lemma modeTest_uncurry (m n : ℕ) (ρ : ℝ → ℝ) :
    Function.uncurry (modeTest m ρ n)
      = fun p : ℝ × ℝ => ρ p.1
          * (angCut n p.2 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) := rfl

theorem modeTest_contDiff {m n : ℕ} {ρ : ℝ → ℝ} (hρ : ∀ k : ℕ, ContDiff ℝ k ρ)
    (hCut : CutFacts m) : ∀ k : ℕ, ContDiff ℝ k (Function.uncurry (modeTest m ρ n)) := by
  intro k
  rw [modeTest_uncurry]
  exact ((hρ k).comp contDiff_fst).mul
    (((hCut.1 n k).comp contDiff_snd).mul
      ((Work.FTS.ClassC.contDiff_eFam_nat m k).comp contDiff_snd))

theorem modeTest_hasCompactSupport {m n : ℕ} {ρ : ℝ → ℝ} (hρc : HasCompactSupport ρ)
    (hCut : CutFacts m) : HasCompactSupport (Function.uncurry (modeTest m ρ n)) := by
  rw [modeTest_uncurry]
  refine HasCompactSupport.of_support_subset_isCompact
    (K := tsupport ρ ×ˢ Set.Icc (delta n) (π / 2 - delta n))
    (hρc.isCompact.prod isCompact_Icc) ?_
  intro p hp
  have hmem : Function.uncurry (modeTest m ρ n) p ≠ 0 := Function.mem_support.mp hp
  have hρp : ρ p.1 ≠ 0 := fun h => hmem (by simp only [modeTest_uncurry, h, zero_mul, mul_zero])
  have hχp : angCut n p.2 ≠ 0 := fun h => hmem (by simp only [modeTest_uncurry, h, zero_mul, mul_zero])
  exact ⟨subset_tsupport _ (Function.mem_support.mpr hρp),
    hCut.tsupport_subset n (subset_tsupport _ (Function.mem_support.mpr hχp))⟩

theorem modeTest_tsupport_subset_Q0 {m n : ℕ} {ρ : ℝ → ℝ} (hρs : tsupport ρ ⊆ Set.Ioi 0)
    (hCut : CutFacts m) :
    tsupport (Function.uncurry (modeTest m ρ n)) ⊆ Work.FTS.EllipticEst.Q0 := by
  have hsupp : Function.support (Function.uncurry (modeTest m ρ n))
      ⊆ tsupport ρ ×ˢ tsupport (angCut n) := by
    intro p hp
    have hmem : Function.uncurry (modeTest m ρ n) p ≠ 0 := Function.mem_support.mp hp
    have hρp : ρ p.1 ≠ 0 := fun h => hmem (by simp only [modeTest_uncurry, h, zero_mul, mul_zero])
    have hχp : angCut n p.2 ≠ 0 := fun h => hmem (by simp only [modeTest_uncurry, h, zero_mul, mul_zero])
    exact ⟨subset_tsupport _ (Function.mem_support.mpr hρp),
      subset_tsupport _ (Function.mem_support.mpr hχp)⟩
  have hclosed : IsClosed (tsupport ρ ×ˢ tsupport (angCut n)) :=
    IsClosed.prod (isClosed_tsupport _) (isClosed_tsupport _)
  refine (closure_minimal hsupp hclosed).trans ?_
  intro p hp
  refine Work.FTS.EllipticEst.mem_Q0.mpr ⟨hρs hp.1, ?_, ?_⟩
  · exact lt_of_lt_of_le (hCut.delta_pos n) (hCut.tsupport_subset n hp.2).1
  · exact lt_of_le_of_lt (hCut.tsupport_subset n hp.2).2
      (by linarith [hCut.delta_pos n] : π / 2 - delta n < π / 2)


/-! ## The algebra of the cut-off difference -/

/-- The commutator of the angular operator with the cut-off. -/
def comm (m n : ℕ) (θ : ℝ) : ℝ :=
  Work.FTS.EllipticEst.Lzero1 (fun t => angCut n t * Work.FTS.PhiStar.Gegenbauer.eFam m t) θ
    - angCut n θ * Work.FTS.EllipticEst.Lzero1 (Work.FTS.PhiStar.Gegenbauer.eFam m) θ

/-- `bslOp` on the pure mode `ρ ⊗ e_m`. -/
lemma bslOp_sepMode {α : ℝ} {ρ : ℝ → ℝ} {m : ℕ} {z θ : ℝ} (hcos : Real.cos θ ≠ 0) :
    Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) z θ
      = (Work.FTS.PhiStar.Gegenbauer.lam m * ρ z - radOp α ρ z)
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
  rw [Work.FTS.PhiStar.bslOp_sep, Lzero1_eFam m hcos, radOp]
  have hiter : iteratedDeriv 2 ρ z = deriv (deriv ρ) z := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [hiter]
  ring

/-- `bslOp` on the cut-off test function splits as `χ_n·bslOp Ψ + ρ·comm_n`. -/
lemma bslOp_modeTest {α : ℝ} {ρ : ℝ → ℝ} {m n : ℕ} {z θ : ℝ} (hcos : Real.cos θ ≠ 0) :
    Work.Elliptic.bslOp α (modeTest m ρ n) z θ
      = angCut n θ * Work.Elliptic.bslOp α
          (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) z θ
        + ρ z * comm m n θ := by
  change Work.Elliptic.bslOp α
      (fun z θ => ρ z * (angCut n θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ)) z θ
      = angCut n θ * Work.Elliptic.bslOp α
          (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) z θ
        + ρ z * comm m n θ
  rw [Work.FTS.PhiStar.bslOp_sep, Work.FTS.PhiStar.bslOp_sep]
  have hiter : iteratedDeriv 2 ρ z = deriv (deriv ρ) z := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  simp only [comm, hiter]
  ring

/-! ## Bounds -/

/-- `|ρ|` is bounded by a constant times the indicator of a box containing its support. -/
theorem exists_bound_abs_rho {ρ : ℝ → ℝ} (hρ : ∀ k : ℕ, ContDiff ℝ k ρ) {a b : ℝ}
    (hsub : tsupport ρ ⊆ Set.Icc a b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, |ρ z| ≤ C * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hρ 0).continuous.continuousOn (s := Set.Icc a b))
  refine ⟨max C 0, le_max_right _ _, fun z => ?_⟩
  by_cases hz : z ∈ Set.Icc a b
  · have h1 : |ρ z| ≤ C := by
      have h2 := hC z hz
      rwa [Real.norm_eq_abs] at h2
    rw [Set.indicator_of_mem hz, mul_one]
    exact h1.trans (le_max_left _ _)
  · rw [Set.indicator_of_notMem hz, mul_zero,
      image_eq_zero_of_notMem_tsupport (fun h => hz (hsub h)), abs_zero]

/-- The weight `z^((5-α)/α)·cos θ` is bounded on a compact box of radii. -/
theorem exists_bound_bslWeight {α : ℝ} {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ × ℝ, p.1 ∈ Set.Icc a b → |bslWeight α p| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_id.rpow_const (fun z hz =>
      Or.inl (ne_of_gt (lt_of_lt_of_le ha hz.1))))
  refine ⟨max C 0, le_max_right _ _, fun p hp => ?_⟩
  have h1 : |p.1 ^ ((5 - α) / α)| ≤ C := by
    have h2 := hC p.1 hp
    rwa [Real.norm_eq_abs] at h2
  calc |bslWeight α p| = |p.1 ^ ((5 - α) / α)| * |Real.cos p.2| := by rw [bslWeight, abs_mul]
    _ ≤ max C 0 * 1 := mul_le_mul (h1.trans (le_max_left _ _)) (Real.abs_cos_le_one p.2)
        (abs_nonneg _) (le_max_right _ _)
    _ = max C 0 := mul_one _

end Work.FTS.StrongEps.EComparison
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EComparison.slice_abs_le_sqrt_sliceEnergy =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison

/-! ## Two algebraic lemmas about the weight `sin(2θ)^{-p}` -/

/-- For `0 ≤ c` and `2 + e ≠ 0`, `(x/c)² c^{-e} = x² c^{-(2+e)}`.  The endpoint case `c = 0`
is harmless: both sides vanish because `0^y = 0` for `y ≠ 0`. -/
private lemma div_sq_mul_rpow_eq {x c e : ℝ} (hc : 0 ≤ c) (he2 : 2 + e ≠ 0) :
    (x / c) ^ 2 * c ^ (-e) = x ^ 2 * c ^ (-(2 + e)) := by
  rcases eq_or_lt_of_le hc with h | h
  · subst h
    rw [div_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul,
      Real.zero_rpow (neg_ne_zero.mpr he2), mul_zero]
  · have hsplit : c ^ (-(2 + e)) = c ^ (-(2 : ℝ)) * c ^ (-e) := by
      rw [show -(2 + e) = -(2 : ℝ) + -e by ring, Real.rpow_add h]
    have hc2 : c ^ (-(2 : ℝ)) = (c ^ 2)⁻¹ := by
      rw [Real.rpow_neg (le_of_lt h)]
      exact congrArg Inv.inv (Real.rpow_natCast c 2)
    have hxc : (x / c) ^ 2 = x ^ 2 * (c ^ 2)⁻¹ := by rw [div_pow, div_eq_mul_inv]
    rw [hsplit, hc2, hxc]
    ring

/-- For `0 < c` the two square roots multiply to `|x|`:
`√((x/c)² c^{-e}) · √(c^{2+e}) = |x|`. -/
private lemma sqrt_mul_sqrt_eq_abs {x c e : ℝ} (hc : 0 < c) :
    Real.sqrt ((x / c) ^ 2 * c ^ (-e)) * Real.sqrt (c ^ (2 + e)) = |x| := by
  have hHnn : 0 ≤ (x / c) ^ 2 * c ^ (-e) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hc) _)
  have hprod : (x / c) ^ 2 * c ^ (-e) * c ^ (2 + e) = x ^ 2 := by
    have h1 : c ^ (-e) * c ^ (2 + e) = c ^ 2 := by
      rw [← Real.rpow_add hc, show -e + (2 + e) = (2 : ℝ) by ring]
      exact Real.rpow_natCast c 2
    calc (x / c) ^ 2 * c ^ (-e) * c ^ (2 + e)
        = (x / c) ^ 2 * (c ^ (-e) * c ^ (2 + e)) := by ring
      _ = (x / c) ^ 2 * c ^ 2 := by rw [h1]
      _ = x ^ 2 := by rw [← mul_pow, div_mul_cancel₀ x (ne_of_gt hc)]
  rw [← Real.sqrt_mul hHnn, hprod, Real.sqrt_sq_eq_abs]

/-! ## `sin(2θ) > 0` almost everywhere on any `E ⊆ Iθ` -/

/-- On any `E ⊆ Iθ` the function `θ ↦ sin(2θ)` is almost everywhere positive (the only zeros
in `Iθ` are the endpoints `0` and `π/2`). -/
private lemma ae_sin_two_pos {E : Set ℝ} (hE : E ⊆ Work.Spaces.Iθ) :
    ∀ᵐ θ ∂(volume.restrict E), 0 < Work.Construction.s2 θ := by
  have hpair : volume ({0, Real.pi / 2} : Set ℝ) = 0 := by
    rw [show ({0, Real.pi / 2} : Set ℝ) = {0} ∪ {Real.pi / 2} by
      ext y; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]]
    exact measure_union_null Real.volume_singleton Real.volume_singleton
  have hsub : {θ : ℝ | ¬ (θ ∈ E → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))}
      ⊆ ({0, Real.pi / 2} : Set ℝ) := by
    intro θ hθ
    rw [Set.mem_ofPred_eq, not_imp, Set.mem_Ioo] at hθ
    obtain ⟨hEθ, hJ⟩ := hθ
    have hIθ : θ ∈ Work.Spaces.Iθ := hE hEθ
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hIθ
    rw [not_and_or, not_lt, not_lt] at hJ
    rcases hJ with h | h
    · exact Or.inl (le_antisymm h hIθ.1)
    · exact Or.inr (le_antisymm hIθ.2 h)
  have h1 : ∀ᵐ θ ∂volume, θ ∈ E → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rw [MeasureTheory.ae_iff]
    exact measure_mono_null hsub hpair
  have hJ : ∀ᵐ θ ∂(volume.restrict E), θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rw [MeasureTheory.ae_restrict_iff (p := fun θ => θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
      measurableSet_Ioo]
    exact h1
  filter_upwards [hJ] with θ hθ
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-! ## The slice bound -/

theorem slice_abs_le_sqrt_sliceEnergy {Φ : ℝ → ℝ → ℝ} {z : ℝ} {E : Set ℝ}
    (hE : E ⊆ Work.Spaces.Iθ)
    (hint : MeasureTheory.IntegrableOn (fun θ => (Φ z θ / Work.Construction.s2 θ) ^ 2
        * (Work.Construction.s2 θ) ^ (-Work.Spaces.eta)) Work.Spaces.Iθ) :
    ∫ θ in E, |Φ z θ| ≤ Real.sqrt (Work.FTS.StrongEps.EComparison.sliceEnergy Φ z)
      * Real.sqrt (∫ θ in E, (Work.Construction.s2 θ) ^ (2 + Work.Spaces.eta)) := by
  -- the three weights appearing in the argument
  let H : ℝ → ℝ := fun θ => (Φ z θ / Work.Construction.s2 θ) ^ 2
    * (Work.Construction.s2 θ) ^ (-Work.Spaces.eta)
  let Q : ℝ → ℝ := fun θ => (Work.Construction.s2 θ) ^ (2 + Work.Spaces.eta)
  let P : ℝ → ℝ := fun θ => Φ z θ ^ 2
    * (Work.Construction.s2 θ) ^ (-(2 + Work.Spaces.eta))
  have heta2 : 2 + Work.Spaces.eta ≠ 0 := by rw [Work.Spaces.eta]; norm_num
  -- `sin(2θ) ≥ 0` on `Iθ`
  have hs2nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Work.Construction.s2 θ := by
    intro θ hθ
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    exact Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hHnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ H θ := fun θ hθ =>
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hs2nn θ hθ) _)
  have hQnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Q θ := fun θ hθ =>
    Real.rpow_nonneg (hs2nn θ hθ) _
  -- almost everywhere statements on `volume.restrict E`
  have hEae : ∀ᵐ θ ∂(volume.restrict E), θ ∈ Work.Spaces.Iθ := by
    rw [MeasureTheory.ae_restrict_iff (p := fun θ => θ ∈ Work.Spaces.Iθ) measurableSet_Icc]
    exact Eventually.of_forall hE
  have hHae : ∀ᵐ θ ∂(volume.restrict E), 0 ≤ H θ :=
    hEae.mono fun θ hθ => hHnn θ hθ
  have hQae : ∀ᵐ θ ∂(volume.restrict E), 0 ≤ Q θ :=
    hEae.mono fun θ hθ => hQnn θ hθ
  have hspos : ∀ᵐ θ ∂(volume.restrict E), 0 < Work.Construction.s2 θ := ae_sin_two_pos hE
  -- `H = P` on `Iθ`
  have hHP : ∀ θ ∈ Work.Spaces.Iθ, H θ = P θ := fun θ hθ =>
    div_sq_mul_rpow_eq (hs2nn θ hθ) heta2
  have hHint : MeasureTheory.IntegrableOn H Work.Spaces.Iθ := hint
  have hHaeP : H =ᵐ[volume.restrict Work.Spaces.Iθ] P := by
    filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc]
      with θ hθ
    exact hHP θ hθ
  have hPint : MeasureTheory.IntegrableOn P Work.Spaces.Iθ := hHint.congr hHaeP
  have hHintE : MeasureTheory.IntegrableOn H E := hHint.mono_set hE
  -- `∫_{Iθ} H = sliceEnergy Φ z`
  have hSE : ∫ θ in Work.Spaces.Iθ, H θ = sliceEnergy Φ z := by
    rw [integral_congr_ae hHaeP]
    show (∫ θ in Work.Spaces.Iθ,
        Φ z θ ^ 2 * (Work.Construction.s2 θ) ^ (-(2 + Work.Spaces.eta)))
      = sliceEnergy Φ z
    simp only [sliceEnergy, rootWeight, Work.Construction.s2_eq]
  -- integrability of `Q` on `E`
  have hQcont : Continuous Q := by
    have h1 : Continuous fun x : ℝ => x ^ (2 + Work.Spaces.eta) :=
      Real.continuous_rpow_const (by rw [Work.Spaces.eta]; norm_num)
    exact h1.comp (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  have hQint : MeasureTheory.IntegrableOn Q Work.Spaces.Iθ :=
    ContinuousOn.integrableOn_compact (K := Work.Spaces.Iθ) isCompact_Icc hQcont.continuousOn
  have hQintE : MeasureTheory.IntegrableOn Q E := hQint.mono_set hE
  -- `L²`-membership of the two square roots on `E`
  have hu_meas : AEStronglyMeasurable (fun θ => Real.sqrt (H θ)) (volume.restrict E) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hHintE.aestronglyMeasurable
  have hv_meas : AEStronglyMeasurable (fun θ => Real.sqrt (Q θ)) (volume.restrict E) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hQintE.aestronglyMeasurable
  have hu_sq : Integrable (fun θ => Real.sqrt (H θ) ^ 2) (volume.restrict E) :=
    hHintE.congr (hHae.mono fun θ hθ => (Real.sq_sqrt hθ).symm)
  have hv_sq : Integrable (fun θ => Real.sqrt (Q θ) ^ 2) (volume.restrict E) :=
    hQintE.congr (hQae.mono fun θ hθ => (Real.sq_sqrt hθ).symm)
  have hu_lp : MemLp (fun θ => Real.sqrt (H θ)) 2 (volume.restrict E) :=
    (memLp_two_iff_integrable_sq hu_meas).mpr hu_sq
  have hv_lp : MemLp (fun θ => Real.sqrt (Q θ)) 2 (volume.restrict E) :=
    (memLp_two_iff_integrable_sq hv_meas).mpr hv_sq
  have hcs := Work.Spaces.cs_integral hu_lp hv_lp
  -- the pointwise product identity, almost everywhere
  have hprod_ae : (fun θ => Real.sqrt (H θ) * Real.sqrt (Q θ))
      =ᵐ[volume.restrict E] (fun θ => |Φ z θ|) := by
    filter_upwards [hspos] with θ hθ
    exact sqrt_mul_sqrt_eq_abs (x := Φ z θ) (c := Work.Construction.s2 θ)
      (e := Work.Spaces.eta) hθ
  have hHsq : (∫ θ in E, Real.sqrt (H θ) ^ 2) = ∫ θ in E, H θ :=
    integral_congr_ae (hHae.mono fun θ hθ => Real.sq_sqrt hθ)
  have hQsq : (∫ θ in E, Real.sqrt (Q θ) ^ 2) = ∫ θ in E, Q θ :=
    integral_congr_ae (hQae.mono fun θ hθ => Real.sq_sqrt hθ)
  have hcsE : (∫ θ in E, Real.sqrt (H θ) * Real.sqrt (Q θ)) ^ 2
      ≤ (∫ θ in E, H θ) * (∫ θ in E, Q θ) := by
    rw [← hHsq, ← hQsq]
    exact hcs
  have hEHnn : 0 ≤ ∫ θ in E, H θ := integral_nonneg_of_ae hHae
  have hstep : ∫ θ in E, Real.sqrt (H θ) * Real.sqrt (Q θ)
      ≤ Real.sqrt (∫ θ in E, H θ) * Real.sqrt (∫ θ in E, Q θ) :=
    calc ∫ θ in E, Real.sqrt (H θ) * Real.sqrt (Q θ)
        ≤ Real.sqrt ((∫ θ in E, H θ) * (∫ θ in E, Q θ)) := Real.le_sqrt_of_sq_le hcsE
      _ = Real.sqrt (∫ θ in E, H θ) * Real.sqrt (∫ θ in E, Q θ) :=
          Real.sqrt_mul hEHnn _
  -- comparison of `∫_E H` with the slice energy
  have hmono : ∫ θ in E, H θ ≤ ∫ θ in Work.Spaces.Iθ, H θ :=
    MeasureTheory.setIntegral_mono_set hHint
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc]
          with θ hθ
        exact hHnn θ hθ)
      (Eventually.of_forall hE)
  calc ∫ θ in E, |Φ z θ|
      = ∫ θ in E, Real.sqrt (H θ) * Real.sqrt (Q θ) := integral_congr_ae hprod_ae.symm
    _ ≤ Real.sqrt (∫ θ in E, H θ) * Real.sqrt (∫ θ in E, Q θ) := hstep
    _ ≤ Real.sqrt (sliceEnergy Φ z) * Real.sqrt (∫ θ in E, Q θ) := by
        refine mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
        rw [hSE] at hmono
        exact hmono

end Work.FTS.StrongEps.EComparison
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.E1Open.Qang_sq_w_sq_le_HkSq_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.E1Open

open MeasureTheory
open scoped Real Topology

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Null sets and the radial weight -/

/-- The `z = 0`-slice of `Iz = [0,∞)` is null, so every almost-everywhere statement on `Iz`
may be proved on the open half-line. -/
private theorem Iz_ae_eq_Ioi : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
  (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm

/-- The two angular endpoints of `Iθ = [0,π/2]` are null. -/
private theorem Iθ_ae_eq_Ioo : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
  (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm

/-- The radial weight `w` squared is continuous on `(0,∞)`. -/
private theorem continuousOn_w_sq :
    ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) := by
  have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      = fun z : ℝ => (((1 + z) ^ 2 / z ^ 2) ^ 2) := by
    funext z; rw [Work.Spaces.w]
  rw [hfun]
  exact (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
    (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))).pow 2

/-! ## The slicewise domination by the `ℋ^k`-integrand -/

/-- For `z > 0` and `0 < θ < π/2` the square of the weighted pure `D_z`-iterate is
dominated by the `ℋ^k`-integrand, `(D_z^i g z θ)² w(z)² ≤ HkIntegrand α k g z θ` (`i ≤ k`).
This is `Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq` multiplied by `w² > 0`; the level `k` is
arbitrary (that is what makes the level-`n` statement below possible). -/
private theorem DzIter_sq_w_sq_le_HkIntegrand (α : ℝ) (g : ℝ → ℝ → ℝ) {k i : ℕ} (hi : i ≤ k)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.DzIter i g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have h1 := Work.FTS.H2.sq_DzIter_le_HkIntegrand_div_w_sq α k g i hi hz hθ
  have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg (Work.Spaces.w z))
  rwa [div_mul_cancel₀ _
    (pow_ne_zero 2 (ne_of_gt (Work.FTS.H2.w_pos hz)))] at h2

/-! ## The target -/

theorem Qang_sq_w_sq_le_HkSq_O (n : ℕ) :
    ∀ (α : ℝ) (g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen g →
      Work.Spaces.HkMem α n g → ∀ i : ℕ, i ≤ n →
      MeasureTheory.IntegrableOn
          (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
        (∫ z in Work.Spaces.Iz, (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α n g := by
  intro α g hα hα1 hO hmem i hi
  -- the pointwise (in `z > 0`) bound
  have hpt : ∀ z : ℝ, 0 < z →
      (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ) := by
    intro z hz
    -- Cauchy–Schwarz in `θ`, at level `n`, in the open-quadrant class
    have hCS := Work.FTS.OpenPkg.Qang_sq_leQ_gen_open α g hO hmem i hi hz
    -- the `θ`-slice domination, with the weight `w z` on the left
    have hslice : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2)
          * (Work.Spaces.w z) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ := by
      have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          (Work.Spaces.DzIter i g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            ≤ Work.Spaces.HkIntegrand α n g z θ := by
        rw [MeasureTheory.Measure.restrict_congr_set Iθ_ae_eq_Ioo]
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
          (fun θ hθ => DzIter_sq_w_sq_le_HkIntegrand α g hi hz hθ)
      have hmono := MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (hmem.1 z (le_of_lt hz)) hae
      simpa only [MeasureTheory.integral_mul_const] using hmono
    calc (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2))
            * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_right hCS (sq_nonneg _)
      _ = (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i g z θ) ^ 2)
                * (Work.Spaces.w z) ^ 2) := by ring
      _ ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ) :=
          mul_le_mul_of_nonneg_left hslice
            (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)
  -- the bound holds almost everywhere on `Iz`
  have hle : (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z => (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ)) := by
    rw [MeasureTheory.Measure.restrict_congr_set Iz_ae_eq_Ioi]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hpt
  -- a.e. strong measurability of the left-hand side
  have haesm : AEStronglyMeasurable
      (fun z => (Work.Elliptic.Qang g i z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hQ : AEStronglyMeasurable (fun z => Work.Elliptic.Qang g i z)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      have h := (Work.Spaces.aesm_of_continuousOn_Qd
        (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * Work.Spaces.DzIter i g p.1 p.2)
        (Work.FTS.OpenPkg.QangOpen.continuousOn_Ktheta_DzIter_open hO i)).integral_prod_right'
      simpa only [Work.Elliptic.Qang] using h
    have hw : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      rw [MeasureTheory.Measure.restrict_congr_set Iz_ae_eq_Ioi]
      exact continuousOn_w_sq.aestronglyMeasurable measurableSet_Ioi
    exact (hQ.pow 2).mul hw
  -- the dominating function is integrable
  have hdom : MeasureTheory.Integrable
      (fun z => (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hmem.2.const_mul _
  refine ⟨?_, ?_⟩
  · refine MeasureTheory.Integrable.mono' hdom haesm ?_
    filter_upwards [hle] with z hz
    rwa [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  · have hmono := MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      hdom hle
    rw [MeasureTheory.integral_const_mul] at hmono
    exact hmono.trans (le_of_eq rfl)

end Work.FTS.StrongEps.EpsE4Thr.E1Open
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.IntPkgSq_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Continuity of the weighted blocks on the open quadrant -/

/-- The `ℋ^k`-weight `Wt α z θ = w z · sin(2θ)^{-γ/2}` is continuous on the open quadrant. -/
theorem continuousOn_Wt_Q0O (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, h0, h1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.EllipticEst.Q0 := by
    have hfun2 : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun2]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    exact pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
  exact hw.mul
    (((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp))))

/-- The uncurried weighted `D_z`-summand of the `ℋ^k`-integrand has a continuous square on the
open quadrant, for a datum of class `SmoothOpen`. -/
theorem continuousOn_Dz_sq_O {f : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f) (i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter i f p.1 p.2
      * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.FTS.CoercivityFix.Coer1.Qd :=
  (hs.continuousOn_summand i).pow 2

/-- The uncurried mixed `ℋ^k`-summand has a continuous square on the open quadrant, for a datum
of class `SmoothOpen`. -/
theorem continuousOn_mixed_Wt_O (α : ℝ) {f : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f)
    (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
      Work.FTS.CoercivityFix.Coer1.Qd :=
  (((hs.mixed j i).continuousOn).mul (continuousOn_Wt_Q0O α)).pow 2

/-- The uncurried `D_z`-iterate is continuous on the open quadrant. -/
theorem continuousOn_DzIter_O {f : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f) (i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i f p.1 p.2)
      Work.FTS.CoercivityFix.Coer1.Qd :=
  (hs.DzIter i).continuousOn

/-- The uncurried mixed derivative is continuous on the open quadrant. -/
theorem continuousOn_mixed_O {f : Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f) (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2)
      Work.FTS.CoercivityFix.Coer1.Qd :=
  (hs.mixed j i).continuousOn

/-! ## The five squared-block certificates -/

theorem IntPkgSq_O (α : ℝ) (hα : 0 < α) {f : Work.FTS.Galerkin.Fn}
    (hs : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 2 f) :
    (∀ i : ℕ, i ≤ 2 → MeasureTheory.IntegrableOn
       (Function.uncurry (fun z θ => (Work.Spaces.DzIter i f z θ) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
       (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    ∧ (∀ i j : ℕ, 1 ≤ i → i + j ≤ 2 → MeasureTheory.IntegrableOn
       (Function.uncurry (fun z θ => (Work.Spaces.mixed j i f z θ) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
       (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    ∧ (∀ i j : ℕ, 1 ≤ i → i + j ≤ 2 → MeasureTheory.IntegrableOn
       (Function.uncurry (fun z θ => (Work.Spaces.mixed j i f z θ) ^ 2
          * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ))
       (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    ∧ (∀ i : ℕ, i ≤ 2 → MeasureTheory.IntegrableOn
       (Function.uncurry (fun z θ => (Work.Spaces.DzIter i f z θ) ^ 2 * Work.Spaces.w z ^ 2))
       (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    ∧ (∀ i j : ℕ, 1 ≤ i → i + j ≤ 2 → MeasureTheory.IntegrableOn
       (Function.uncurry (fun z θ => (Work.Spaces.mixed j i f z θ) ^ 2 * Work.Spaces.w z ^ 2))
       (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
  -- ## the `D_z`-blocks with the `η`-weight
  have hsqDzEta : ∀ i : ℕ, i ≤ 2 → MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.DzIter i f z θ) ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    intro i hi
    have h := Work.FTS.CoercivityFix.Coer1.joint_of_le_HkIntegrand α 2 hm
      (continuousOn_Dz_sq_O hs i)
      (fun z _ θ _ => Work.Spaces.sq_le_HkIntegrand_z α 2 f z θ i hi)
    refine h.congr (MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => ?_))
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair] at hp ⊢
    rw [mul_pow, Work.FTS.CoercivityFix.Coer1.sig_div_sq_Iθ Work.Spaces.eta
      (by rw [Work.Spaces.eta]; norm_num) z θ hp.2]
    rfl
  -- ## the mixed blocks with the `γ`-weight
  have hsqMixedGam : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 2 → MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.mixed j i f z θ) ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    intro i j hi hij
    have h := Work.FTS.CoercivityFix.Coer1.joint_of_le_HkIntegrand α 2 hm
      (continuousOn_mixed_Wt_O α hs j i)
      (fun z _ θ _ => Work.Spaces.sq_le_HkIntegrand_mixed α 2 f z θ i j hi hij)
    refine h.congr (MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => ?_))
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair] at hp ⊢
    rw [mul_pow, Work.FTS.CoercivityFix.Coer1.Wt_sq_self_Iθ α z θ hα hp.2]
    rfl
  -- ## the mixed blocks with the `η`-weight (dominated by the `γ`-weighted ones)
  have hsqMixedEta : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 2 → MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.mixed j i f z θ) ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    intro i j hi hij
    have h := hsqMixedGam i j hi hij
    refine Work.FTS.CoercivityFix.Coer1.integrableOn_of_le_Q
      (((continuousOn_mixed_O hs j i).pow 2).mul
        (Work.FTS.CoercivityFix.Coer1.continuousOn_Rho _)) h ?_
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem measurableSet_Icc
      (MeasureTheory.ae_restrict_mem measurableSet_Icc)] with p hp
    rcases p with ⟨z, θ⟩
    rw [abs_mul, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (Work.FTS.CoercivityFix.Coer1.Rho_nonneg _ z θ hp)]
    exact mul_le_mul_of_nonneg_left
      (Work.FTS.CoercivityFix.Coer1.Rho_eta_le_Rho_gam α hα z θ hp)
      (sq_nonneg (Work.Spaces.mixed j i f z θ))
  refine ⟨hsqDzEta, hsqMixedEta, hsqMixedGam, ?_, ?_⟩
  · -- ## the `D_z`-blocks with the plain radial weight
    intro i hi
    refine Work.FTS.CoercivityFix.Coer1.integrableOn_of_le_Q
      (((continuousOn_DzIter_O hs i).pow 2).mul
        Work.FTS.CoercivityFix.Coer1.continuousOn_w2) (hsqDzEta i hi) ?_
    refine (Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem_Ioo).mono (fun p hp => ?_)
    rcases p with ⟨z, θ⟩
    rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left
      (Work.FTS.CoercivityFix.Coer1.w2_le_Rho_eta z θ hp)
      (sq_nonneg (Work.Spaces.DzIter i f z θ))
  · -- ## the mixed blocks with the plain radial weight
    intro i j hi hij
    refine Work.FTS.CoercivityFix.Coer1.integrableOn_of_le_Q
      (((continuousOn_mixed_O hs j i).pow 2).mul
        Work.FTS.CoercivityFix.Coer1.continuousOn_w2) (hsqMixedGam i j hi hij) ?_
    refine (Work.FTS.CoercivityFix.Coer1.ae_prod_snd_mem_Ioo).mono (fun p hp => ?_)
    rcases p with ⟨z, θ⟩
    rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left
      (Work.FTS.CoercivityFix.Coer1.w2_le_Rho_gam α hα z θ hp)
      (sq_nonneg (Work.Spaces.mixed j i f z θ))

end Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.ae_Dz_Dth_comm_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux

/-- **Clairaut for the curvilinear operators, a.e. on the closed quadrant.**

For any `f` of class `SmoothOpen` (`C^∞` on the *open* quadrant `(0,∞) × (0,π/2)`),
the operators `D_z = z ∂_z` and `D_θ = sin(2θ) ∂_θ` commute at almost every point of
`Iz × Iθ` with respect to the product of the restricted Lebesgue measures.

The proof is the pointwise Clairaut identity `Work.Spaces.Dz_Dth_comm` applied at the a.e.
*interior* points: the `x`-measure of `{0}` is zero, so a.e. `z ∈ Iz` satisfies `z > 0`, and
a.e. `θ ∈ Iθ` avoids `{0, π/2}`; at such an interior point `(z,θ) ∈ Q0` the uncurried `f` is
`C²` (`SmoothOpen.forall 2` plus `IsOpen.mem_nhds` of the open quadrant `Q0`), which is
exactly the hypothesis of Clairaut–Schwarz. -/
theorem ae_Dz_Dth_comm_O {f : Work.FTS.Galerkin.Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      Work.Spaces.Dz (Work.Spaces.Dth f) p.1 p.2
        = Work.Spaces.Dth (Work.Spaces.Dz f) p.1 p.2 := by
  -- a.e. `z ∈ Iz` and a.e. `z ≠ 0`, whence a.e. `z > 0`
  have hzmem : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      z ∈ Work.Spaces.Iz := MeasureTheory.ae_restrict_mem measurableSet_Ici
  have hzne : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), z ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    have hset : {z : ℝ | ¬ z ≠ 0} = {0} := by ext z; simp
    rw [hset]
    exact Set.Finite.measure_zero (Set.finite_singleton 0) _
  have hzpos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z := by
    filter_upwards [hzmem, hzne] with z hz hne
    exact lt_of_le_of_ne hz (Ne.symm hne)
  -- a.e. `θ ∈ Iθ` with `θ ≠ 0`, `θ ≠ π/2`
  have hθmem : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Work.Spaces.Iθ := MeasureTheory.ae_restrict_mem measurableSet_Icc
  have hθne0 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    have hset : {θ : ℝ | ¬ θ ≠ 0} = {0} := by ext θ; simp
    rw [hset]
    exact Set.Finite.measure_zero (Set.finite_singleton 0) _
  have hθneπ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ≠ Real.pi / 2 := by
    rw [MeasureTheory.ae_iff]
    have hset : {θ : ℝ | ¬ θ ≠ Real.pi / 2} = {Real.pi / 2} := by ext θ; simp
    rw [hset]
    exact Set.Finite.measure_zero (Set.finite_singleton _) _
  -- a.e. point of the product lies in the open quadrant
  have hQ : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), p ∈ Work.FTS.EllipticEst.Q0 := by
    refine (MeasureTheory.Measure.ae_prod_iff_ae_ae
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (p := fun p : ℝ × ℝ => p ∈ Work.FTS.EllipticEst.Q0)
      Work.FTS.EllipticEst.isOpen_Q0.measurableSet).mpr ?_
    filter_upwards [hzpos] with z hz
    filter_upwards [hθmem, hθne0, hθneπ] with θ hθ h0 hp
    exact Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨hz, lt_of_le_of_ne hθ.1 (Ne.symm h0), lt_of_le_of_ne hθ.2 hp⟩
  filter_upwards [hQ] with p hp
  exact Work.Spaces.Dz_Dth_comm ((hs.forall 2).contDiffAt
    (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp))

end Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.continuousOn_E2hat_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux

open MeasureTheory Set Filter

/-- The rational factor `z ↦ z/(1+z)²` is continuous on the open quadrant. -/
theorem continuousOn_zdiv_sq_Qd :
    ContinuousOn (fun p : ℝ × ℝ => p.1 / (1 + p.1) ^ 2) Work.FTS.CoercivityFix.Coer1.Qd :=
  continuousOn_fst.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (fun p hp => pow_ne_zero 2 (by
      have h1 : (0 : ℝ) < p.1 := hp.1
      linarith))

/-- The defect `Ê₂f = (2zf + 3z·D_θf)/(1+z)²` is continuous on the open quadrant, for `f`
smooth there. -/
theorem continuousOn_E2hat_Qd {f : Work.FTS.Galerkin.Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.CoercivityFix.E2hat f p.1 p.2)
      Work.FTS.CoercivityFix.Coer1.Qd := by
  have hfun : (fun p : ℝ × ℝ => Work.FTS.CoercivityFix.E2hat f p.1 p.2)
      = fun p : ℝ × ℝ => (p.1 / (1 + p.1) ^ 2)
          * (2 * f p.1 p.2 + 3 * Work.Spaces.Dth f p.1 p.2) := by
    funext p
    obtain ⟨z, θ⟩ := p
    rw [Work.FTS.CoercivityFix.E2hat_eq]
    ring
  rw [hfun]
  exact continuousOn_zdiv_sq_Qd.mul
    ((hs.continuousOn.const_mul 2).add (hs.Dth.continuousOn.const_mul 3))

theorem continuousOn_E2hat_O {f : Work.FTS.Galerkin.Fn} (hs : Work.FTS.EllipticEst.SmoothOpen f)
    {ρ : Work.FTS.Galerkin.Fn}
    (hρc : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) Work.FTS.CoercivityFix.Coer1.Qd) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.CoercivityFix.E2hat f p.1 p.2
      * Work.Spaces.Dz f p.1 p.2 * ρ p.1 p.2) Work.FTS.CoercivityFix.Coer1.Qd := by
  exact ((continuousOn_E2hat_Qd hs).mul hs.Dz.continuousOn).mul hρc

end Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.intL_of_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux

theorem intL_of_O {u : Work.FTS.Galerkin.Fn} {ρ : Work.FTS.Galerkin.Fn}
    (hs : Work.FTS.EllipticEst.SmoothOpen u)
    (hρc : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) Work.FTS.CoercivityFix.Coer1.Qd)
    (hρnn : ∀ z θ, θ ∈ Work.Spaces.Iθ → 0 ≤ ρ z θ)
    (hsq : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => u z θ ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hdz : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.Dz u z θ) ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.L u z θ * u z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have hcross : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dz u z θ * u z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_mul_of_sq_Q
      (((hs.Dz).continuousOn.mul hs.continuousOn).mul hρc) hρnn hdz hsq
  have h1 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      u z θ ^ 2 * ρ z θ + Work.Spaces.Dz u z θ * u z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_add_Q hsq hcross
  have h3 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (u z θ ^ 2 * ρ z θ) / (1 + z))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_div_one_add_Q hsq
  have h4 := h3.const_mul (-2)
  have h5 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (u z θ ^ 2 * ρ z θ + Work.Spaces.Dz u z θ * u z θ * ρ z θ)
        + (-2) * ((u z θ ^ 2 * ρ z θ) / (1 + z)))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_add_Q h1 h4
  refine h5.congr (MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => ?_))
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair, Work.Coercivity.L]
  ring

end Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux.intTr_of_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux

theorem intTr_of_O {u : Work.FTS.Galerkin.Fn} {ρ : Work.FTS.Galerkin.Fn}
    (hs : Work.FTS.EllipticEst.SmoothOpen u)
    (hρc : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) Work.FTS.CoercivityFix.Coer1.Qd)
    (hρnn : ∀ z θ, θ ∈ Work.Spaces.Iθ → 0 ≤ ρ z θ)
    (hsq : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => u z θ ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hth : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.Dth u z θ) ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth u z θ * u z θ * ρ z θ / (1 + z)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  -- Continuity of the unweighted product on the open quadrant, from `SmoothOpen u` and `hρc`.
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.Dth u p.1 p.2 * u p.1 p.2 * ρ p.1 p.2)
      Work.FTS.CoercivityFix.Coer1.Qd :=
    (((hs.Dth).continuousOn).mul hs.continuousOn).mul hρc
  -- The product of two `L²`-blocks is integrable: `2|ab| ≤ a² + b²` and `ρ ≥ 0` on `Iθ`.
  exact Work.FTS.CoercivityFix.Coer1.integrableOn_div_one_add_Q
    (Work.FTS.CoercivityFix.Coer1.integrableOn_mul_of_sq_Q hcont hρnn hth hsq)

end Work.FTS.StrongEps.EpsE4Thr.IntPkgOAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.ef_le_efEta_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- On the open angular interval `(0,π/2)` the `ℋ¹`-weight `w / sin(2θ)^{η/2}` dominates
the plain radial weight `w`: there `0 < sin(2θ) ≤ 1`, so `1 ≤ sin(2θ)^{-η/2}`, and `w ≥ 0`. -/
private theorem w_le_w_div_sin {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.w z ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hpow_pos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
    Real.rpow_pos_of_pos hs _
  have hpow_le : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one (le_of_lt hs) (Real.sin_le_one _) (by rw [Work.Spaces.eta]; norm_num)
  have hinv : (1 : ℝ) ≤ ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))⁻¹ :=
    (one_le_inv₀ hpow_pos).mpr hpow_le
  have hw : 0 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w]
    positivity
  calc Work.Spaces.w z = Work.Spaces.w z * 1 := by ring
    _ ≤ Work.Spaces.w z * ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))⁻¹ :=
        mul_le_mul_of_nonneg_left hinv hw
    _ = Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
        (div_eq_mul_inv _ _).symm

/-- **The `η`-weighted energy dominates the unweighted one, in the open-quadrant class.**

Both energies are squared iterated `L²`-norms of `f` against the radial weight `w` resp. the
`ℋ¹`-weight `w·sin(2θ)^{-η/2}`.  On the open angular interval the second weight dominates
the first, and `HkMem α 1 f` supplies exactly the honesty of the `η`-weighted iterated
integral: `f·w/sin(2θ)^{η/2}` is (definitionally) the `D_z⁰`-summand of `HkIntegrand α 1 f`,
so `i2Mem_sq_of_le` gives that `∫_z ∫_θ (f·w/sin(2θ)^{η/2})²` is an honest iterated integral.
Monotonicity of the iterated integral then yields `Ef f ≤ EfEta f`. -/
theorem ef_le_efEta_open {α : ℝ} {f : Work.FTS.Galerkin.Fn}
    (hs : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 1 f) :
    Work.Coercivity.Ef f ≤ Work.Coercivity.EfEta f := by
  -- ## The `D_z⁰`-weighted summand is continuous on the open quadrant
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (Work.Coercivity.U0 f p.1 p.2) ^ 2)
      Work.FTS.CoercivityFix.Coer1.Qd := by
    have h := (hs.continuousOn_summand 0).pow 2
    have hfun : (fun p : ℝ × ℝ => (Work.Coercivity.U0 f p.1 p.2) ^ 2)
        = fun p : ℝ × ℝ => (Work.Spaces.DzIter 0 f p.1 p.2
            * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      funext p
      simp only [Work.Coercivity.U0, Work.Spaces.DzIter_zero]
    rw [hfun]
    exact h
  -- ## `(f·w/sin(2θ)^{η/2})²` is one of the summands of the `ℋ¹`-integrand
  have hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Coercivity.U0 f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 1 f z θ := by
    intro z _ θ _
    have h := Work.Spaces.sq_le_HkIntegrand_z α 1 f z θ 0 (by norm_num)
    simpa only [Work.Coercivity.U0, Work.Spaces.DzIter_zero] using h
  -- ## Honesty of the `η`-weighted iterated integral
  have hB : Work.Coercivity.I2Mem (fun z θ => (Work.Coercivity.U0 f z θ) ^ 2) :=
    Work.FTS.CoercivityFix.Coer1.i2Mem_sq_of_le α 1 hm hcont hle
  -- ## Both energies as iterated integrals
  have hEf : Work.Coercivity.Ef f
      = Work.Spaces.L2Sq (fun z θ => f z θ * Work.Spaces.w z) := rfl
  have hEfEta : Work.Coercivity.EfEta f = Work.Spaces.L2Sq (Work.Coercivity.U0 f) :=
    (Work.Coercivity.L2Sq_U0_eq_EfEta f).symm
  rw [hEf, hEfEta, Work.Spaces.L2Sq, Work.Spaces.L2Sq]
  -- ## The outer integral
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _) hB.2 ?_
  refine MeasureTheory.ae_restrict_of_forall_mem
    (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) fun z hz => ?_
  -- ## The inner (angular) integral
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun θ => sq_nonneg _) (hB.1 z hz) ?_
  filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo] with θ hθ
  have hw : 0 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w]
    positivity
  have h2 : (Work.Spaces.w z) ^ 2
      ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
    pow_le_pow_left₀ hw (w_le_w_div_sin hθ) 2
  have hmain := mul_le_mul_of_nonneg_left h2 (sq_nonneg (f z θ))
  simpa only [Work.Coercivity.U0, Work.Spaces.DzIter_zero, mul_pow] using hmain

end Work.FTS.StrongEps.EpsE4Thr
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.mixed_sub_of_contDiffOn_six =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

/-!
# Subtraction rule for `D_z^j D_θ^i` on the open quadrant, six derivatives

`Work.Spaces.mixed j i f = D_z^j D_θ^i f` with `D_z = z ∂_z`, `D_θ = sin(2θ) ∂_θ`, and
`Work.FTS.EllipticEst.Q0 = (0,∞) × (0,π/2)` is the open quadrant.  This is the order-`6`
counterpart of `Work.FTS.StrongEps.mixed_sub_of_contDiffOn_four`: for two functions that are
`C^6` on the open quadrant

  `D_z^j D_θ^i (A - B) = D_z^j D_θ^i A - D_z^j D_θ^i B`   on `Q0`, for `i + j ≤ 6`.

Route (identical to the order-`4` case).  Write `A - B = A + (-B)` and apply the finite-order
*additivity* lemma `Work.FTS.EllipticEst.Cores.DiagEstEllT.mixed_add_fin` at `m = 6` (it is
stated for arbitrary order `m`), then use that every iterate of `mixed` is *unconditionally*
scalar homogeneous — `Work.FTS.StrongEps.mixed_neg` — to turn `mixed j i (fun z θ => -(B z θ))`
into `- mixed j i B`.

The statement is byte-for-byte the requested one; the file only adds imports and this comment.
-/

theorem mixed_sub_of_contDiffOn_six {j i : ℕ} {A B : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hji : j + i ≤ 6) (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hA : ContDiffOn ℝ 6 (Function.uncurry A) Work.FTS.EllipticEst.Q0)
    (hB : ContDiffOn ℝ 6 (Function.uncurry B) Work.FTS.EllipticEst.Q0) :
    Work.Spaces.mixed j i (fun z θ => A z θ - B z θ) z θ
      = Work.Spaces.mixed j i A z θ - Work.Spaces.mixed j i B z θ := by
  -- `-B` is again `C^6` on the open quadrant
  have hBneg : ContDiffOn ℝ 6 (Function.uncurry (fun z θ => -(B z θ)))
      Work.FTS.EllipticEst.Q0 := by
    have hfun : Function.uncurry (fun z θ => -(B z θ))
        = fun p : ℝ × ℝ => -(Function.uncurry B p) := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [hfun]
    exact hB.neg
  -- the index bound in the shape expected by `mixed_add_fin`
  have hij : i + j ≤ 6 := by rw [Nat.add_comm i j]; exact hji
  -- rewrite `A - B` as `A + (-B)`
  have hfun : (fun z θ => A z θ - B z θ) = fun z θ => A z θ + -(B z θ) := by
    funext z θ; ring
  rw [hfun]
  -- finite-order additivity for `C^6` data on the open quadrant
  rw [Work.FTS.EllipticEst.Cores.DiagEstEllT.mixed_add_fin (f := A)
        (g := fun z' θ' => -(B z' θ')) hA hBneg j i hij z θ hz hθ.1 hθ.2]
  -- homogeneity at the scalar `-1`
  rw [Work.FTS.StrongEps.mixed_neg]
  ring

end Work.FTS.StrongEps.EpsE4Thr
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.RadBound.L12f_iter_regular_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Regularity of the `z∂_z`-iterates of `L₁₂ f` on `(0,∞)` (open-quadrant class)

For `0 < α ≤ 1`, a datum `f` which is `C^∞` on the *open* quadrant
(`Work.FTS.EllipticEst.SmoothOpen f`) with `HkMem α 4 f`, the radial profile
`L₁₂ f = Work.Coercivity.L12f f` is `C^4` on `(0,∞)`; consequently

* every `(z∂_z)`-iterate `D_z^c (L₁₂ f)`, `c ≤ 4`, is continuous on `(0,∞)`;
* every `D_z^b (L₁₂ f)`, `b ≤ 3`, is differentiable at every point of `(0,∞)`.

The two facts are the ones needed downstream to invoke the Leibniz rule
`D_z^q (ampA · L₁₂ f) = ∑ …` (`differentiableAt` of the iterates one order below).

## The proof

The operator of the elliptic chapter and that of the coercivity chapter agree:
`Work.Coercivity.L12f = Work.Elliptic.L12` (`FM.L12 Spaces.K` vs. `FM.L12 FM.Kpaper`,
and `Spaces.K` and `FM.Kpaper` are *the same* function `θ ↦ 3 sin θ cos²θ`, so this is `rfl`
after unfolding).

`Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k` (the open-quadrant version of the
`L₁₂`-regularity theorem: `L₁₂` gains one order over the density `-3 F_*/z`, which is
`C^{k-1}` for `HkMem α k f`) gives `ContDiffOn ℝ 4 (L₁₂ f) (0,∞)`.

From `ContDiffOn ℝ 4` on the *open* half-line, the iterate `D_z^c = Zop^[c]` loses exactly `c`
orders (`Work.FTS.CoercivityFix.Transfer.E1Parts.contDiffOn_Zop_iter'`, `c + (4-c) = 4`), so it
is `C^{4-c}` — in particular continuous; and for `b ≤ 3` it is `C^{b+1} ⊇ C^1`, hence
differentiable (`differentiableAt_Zop_iter_of_contDiffOn`).

The hypothesis `L₁₂ f 0 = 0` is not needed for regularity (it enters the consumer only to fix
the decay of `L₁₂ f` at the origin).
-/

namespace Work.FTS.StrongEps.EpsRLX.RadBound

theorem L12f_iter_regular_open (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (f : Work.FTS.Galerkin.Fn)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (h0 : Work.Construction.L12 f 0 = 0) :
    (∀ c : ℕ, c ≤ 4 → ContinuousOn (Work.Elliptic.DzdIter c (Work.Coercivity.L12f f))
        (Set.Ioi (0 : ℝ))) ∧
    (∀ b : ℕ, b ≤ 3 → ∀ z ∈ Set.Ioi (0 : ℝ),
        DifferentiableAt ℝ (Work.Elliptic.DzdIter b (Work.Coercivity.L12f f)) z) := by
  have _ := h0
  -- the coercivity operator and the elliptic operator are the same function
  have hL12 : Work.Coercivity.L12f f = Work.Elliptic.L12 f := by
    funext z
    show Work.FM.L12 Work.Spaces.K f z = Work.Elliptic.L12 f z
    rw [Work.Elliptic.L12_eq_FM]
    rfl
  -- `L₁₂ f` is `C^4` on the open half-line
  have hCd : ContDiffOn ℝ (4 : WithTop ℕ∞) (Work.Coercivity.L12f f) (Set.Ioi (0 : ℝ)) := by
    rw [hL12]
    exact Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 4 f hα hα1 hsm hmem (by norm_num)
  constructor
  · intro c hc
    -- `D_z^c = Zop^[c]` trades `c` orders of smoothness for `4 - c`
    have hcast : ((c + (4 - c) : ℕ) : WithTop ℕ∞) = (4 : WithTop ℕ∞) := by
      rw [Nat.add_sub_cancel' hc]; norm_num
    have hu : ContDiffOn ℝ ((c : WithTop ℕ∞) + ((4 - c : ℕ) : WithTop ℕ∞))
        (Work.Coercivity.L12f f) (Set.Ioi (0 : ℝ)) := by
      rw [← Nat.cast_add, hcast]
      exact hCd
    have hcd := Work.FTS.CoercivityFix.Transfer.E1Parts.contDiffOn_Zop_iter' c (4 - c) hu
    rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter c]
    exact hcd.continuousOn
  · intro b hb z hz
    have hle : ((b : WithTop ℕ∞) + 1) ≤ (4 : WithTop ℕ∞) := by
      rw [← Nat.cast_one, ← Nat.cast_add]
      exact_mod_cast (by omega : b + 1 ≤ 4)
    have hu : ContDiffOn ℝ ((b : WithTop ℕ∞) + 1) (Work.Coercivity.L12f f)
        (Set.Ioi (0 : ℝ)) :=
      hCd.of_le hle
    rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter b]
    exact Work.FTS.CoercivityFix.Transfer.E1Parts.differentiableAt_Zop_iter_of_contDiffOn hu hz

end Work.FTS.StrongEps.EpsRLX.RadBound
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.Atoms.DzIter_hKerSq_le5 =====
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
set_option linter.unusedSimpArgs false

/-!
# The level-`5` radial iterates of `hKer² = z²/(1+z)⁴`

This file is the level-`5` companion of
`Submission.Work.FTS.Nonlinear.Pieces.RNP.hkerSqAux` (which stops at order `4`).  It recomputes
the `D_z = z ∂_z`-iterates of the radial profile `hKer(z)² = z²/(1+z)⁴` in closed form

  `D_z^i hKer² = z² q_i(z)/(1+z)^(4+i)`,

and bounds the polynomials `q_i` on `[0,∞)`:

  `|q1| ≤ 2(1+z)`, `|q2| ≤ 12(1+z)²`, `|q3| ≤ 52(1+z)³`, `|q4| ≤ 416(1+z)⁴`,
  `|q5| ≤ 6720(1+z)⁵`.

Hence `|D_z^i hKer² z| ≤ C·z²/(1+z)^3` for `i ≤ 5`, `z ≥ 0`, with the single constant
`C = 6720` (the extra power of `1+z` in the numerator is absorbed by `(1+z)³ ≤ (1+z)⁴`).

The private lemmas of `hkerSqAux` (the recursion steps `hasDerivAt_g*`/`deriv_g*_val`, the closed
forms `dz0`–`dz4`, the coefficient bounds `q*_le`) are copied here verbatim — `hkerSqAux.lean` is
not edited — and the missing step of order `5` is added: the recurrence

  `q_{i+1} = (1+z)(2 q_i + z q_i') − (4+i) z q_i`

gives `q5 = (1+z)(2q4 + z·q4') − 8z·q4 = 32 − 684z + 2644z² − 2644z³ + 684z⁴ − 32z⁵`.
-/

/-! ## The radial profile -/

private noncomputable def hk2 (z : ℝ) : ℝ := (Work.Spaces.hKer z) ^ 2

private lemma hk2_apply (z : ℝ) : hk2 z = z ^ 2 / (1 + z) ^ 4 := by
  rw [hk2, Work.Spaces.hKer_apply, div_pow]
  congr 1
  ring

/-- `hk2` is, definitionally, the function occurring in the statement. -/
private lemma hk2_eq_fun : hk2 = fun z : ℝ => (Work.Spaces.hKer z) ^ 2 := by
  funext z; rw [hk2]

/-! ## The polynomial numerators of the `D_z`-iterates -/

private noncomputable def q1 : ℝ → ℝ := fun z => 2 - 2 * z
private noncomputable def q2 : ℝ → ℝ := fun z => 4 - 12 * z + 4 * z ^ 2
private noncomputable def q3 : ℝ → ℝ := fun z => 8 - 52 * z + 52 * z ^ 2 - 8 * z ^ 3
private noncomputable def q4 : ℝ → ℝ :=
  fun z => 16 - 196 * z + 416 * z ^ 2 - 196 * z ^ 3 + 16 * z ^ 4

/-- The level-`5` numerator, `q5 = (1+z)(2q4 + z·q4') − 8z·q4`. -/
private noncomputable def q5 : ℝ → ℝ :=
  fun z => 32 - 684 * z + 2644 * z ^ 2 - 2644 * z ^ 3 + 684 * z ^ 4 - 32 * z ^ 5

/-- The closed forms of the `D_z`-iterates of `hKer²`:
`D_z^i hKer² = z² q_i(z)/(1+z)^(4+i)`, with `q_0 = 1`. -/
private noncomputable def gfun : ℕ → ℝ → ℝ
  | 0 => fun z => z ^ 2 / (1 + z) ^ 4
  | 1 => fun z => z ^ 2 * q1 z / (1 + z) ^ 5
  | 2 => fun z => z ^ 2 * q2 z / (1 + z) ^ 6
  | 3 => fun z => z ^ 2 * q3 z / (1 + z) ^ 7
  | 4 => fun z => z ^ 2 * q4 z / (1 + z) ^ 8
  | _ => fun z => z ^ 2 * q5 z / (1 + z) ^ 9

/-! ## Derivative computations -/

private lemma hasDerivAt_one_add_pow (n : ℕ) (z : ℝ) :
    HasDerivAt (fun w : ℝ => (1 + w) ^ n) ((n : ℝ) * (1 + z) ^ (n - 1)) z := by
  have h := (hasDerivAt_pow n (1 + z)).comp z ((hasDerivAt_id z).const_add 1)
  convert h using 1
  all_goals first
    | (funext w; simp only [Function.comp_apply, id_eq])
    | ring

private lemma hasDerivAt_q1 (z : ℝ) : HasDerivAt q1 (-2) z := by
  have h := ((hasDerivAt_const (x := z) (c := (2 : ℝ))).sub ((hasDerivAt_id z).const_mul 2))
  convert h using 1
  all_goals first
    | (funext w; simp only [q1, Pi.sub_apply, Pi.mul_apply, id_eq])
    | ring

private lemma hasDerivAt_q2 (z : ℝ) : HasDerivAt q2 (8 * z - 12) z := by
  have h1 : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
  have h := (((hasDerivAt_const (x := z) (c := (4 : ℝ))).sub
    ((hasDerivAt_id z).const_mul 12)).add (h1.const_mul 4))
  convert h using 1
  all_goals first
    | (funext w; simp only [q2, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, id_eq])
    | ring

private lemma hasDerivAt_q3 (z : ℝ) : HasDerivAt q3 (-24 * z ^ 2 + 104 * z - 52) z := by
  have h1 : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
  have h2 : HasDerivAt (fun w : ℝ => w ^ 3) (3 * z ^ 2) z := by
    simpa using hasDerivAt_pow 3 z
  have h := ((((hasDerivAt_const (x := z) (c := (8 : ℝ))).sub
    ((hasDerivAt_id z).const_mul 52)).add (h1.const_mul 52)).sub (h2.const_mul 8))
  convert h using 1
  all_goals first
    | (funext w; simp only [q3, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, id_eq])
    | ring

private lemma hasDerivAt_q4 (z : ℝ) :
    HasDerivAt q4 (64 * z ^ 3 - 588 * z ^ 2 + 832 * z - 196) z := by
  have h1 : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
  have h2 : HasDerivAt (fun w : ℝ => w ^ 3) (3 * z ^ 2) z := by simpa using hasDerivAt_pow 3 z
  have h3 : HasDerivAt (fun w : ℝ => w ^ 4) (4 * z ^ 3) z := by simpa using hasDerivAt_pow 4 z
  have h := (((((hasDerivAt_const (x := z) (c := (16 : ℝ))).sub
    ((hasDerivAt_id z).const_mul 196)).add (h1.const_mul 416)).sub (h2.const_mul 196)).add
      (h3.const_mul 16))
  convert h using 1
  all_goals first
    | (funext w; simp only [q4, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, id_eq])
    | ring


/-! ## The recursion `q_{i+1} = (1+z)(2q_i + z q_i') − (4+i) z q_i`, one step at a time -/

private lemma deriv_g0_val (z : ℝ) (hz : 0 < z) :
    ((2 * z) * (1 + z) ^ 4 - z ^ 2 * ((4 : ℝ) * (1 + z) ^ (4 - 1)))
        / ((1 + z) ^ 4) ^ 2
      = z * q1 z / (1 + z) ^ 5 := by
  rw [q1]; norm_num
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

private lemma deriv_g1_val (z : ℝ) (hz : 0 < z) :
    ((2 * z * q1 z + z ^ 2 * (-2)) * (1 + z) ^ 5
        - (z ^ 2 * q1 z) * ((5 : ℝ) * (1 + z) ^ (5 - 1)))
        / ((1 + z) ^ 5) ^ 2
      = z * q2 z / (1 + z) ^ 6 := by
  rw [q1, q2]; norm_num
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

private lemma deriv_g2_val (z : ℝ) (hz : 0 < z) :
    ((2 * z * q2 z + z ^ 2 * (8 * z - 12)) * (1 + z) ^ 6
        - (z ^ 2 * q2 z) * ((6 : ℝ) * (1 + z) ^ (6 - 1)))
        / ((1 + z) ^ 6) ^ 2
      = z * q3 z / (1 + z) ^ 7 := by
  rw [q2, q3]; norm_num
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

private lemma deriv_g3_val (z : ℝ) (hz : 0 < z) :
    ((2 * z * q3 z + z ^ 2 * (-24 * z ^ 2 + 104 * z - 52)) * (1 + z) ^ 7
        - (z ^ 2 * q3 z) * ((7 : ℝ) * (1 + z) ^ (7 - 1)))
        / ((1 + z) ^ 7) ^ 2
      = z * q4 z / (1 + z) ^ 8 := by
  rw [q3, q4]; norm_num
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- The level-`5` step of the recurrence. -/
private lemma deriv_g4_val (z : ℝ) (hz : 0 < z) :
    ((2 * z * q4 z + z ^ 2 * (64 * z ^ 3 - 588 * z ^ 2 + 832 * z - 196)) * (1 + z) ^ 8
        - (z ^ 2 * q4 z) * ((8 : ℝ) * (1 + z) ^ (8 - 1)))
        / ((1 + z) ^ 8) ^ 2
      = z * q5 z / (1 + z) ^ 9 := by
  rw [q4, q5]; norm_num
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

private lemma hasDerivAt_g0 {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun w : ℝ => w ^ 2 / (1 + w) ^ 4) (z * q1 z / (1 + z) ^ 5) z := by
  have hnum : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
  have h : HasDerivAt (fun w : ℝ => w ^ 2 / (1 + w) ^ 4)
      (((2 * z) * (1 + z) ^ 4 - z ^ 2 * ((4 : ℝ) * (1 + z) ^ (4 - 1)))
        / ((1 + z) ^ 4) ^ 2) z :=
    hnum.div (hasDerivAt_one_add_pow 4 z) (by positivity)
  rw [deriv_g0_val z hz] at h
  exact h

private lemma hasDerivAt_g1 {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun w : ℝ => w ^ 2 * q1 w / (1 + w) ^ 5) (z * q2 z / (1 + z) ^ 6) z := by
  have hp : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
  have h : HasDerivAt (fun w : ℝ => w ^ 2 * q1 w / (1 + w) ^ 5)
      (((2 * z * q1 z + z ^ 2 * (-2)) * (1 + z) ^ 5
        - (z ^ 2 * q1 z) * ((5 : ℝ) * (1 + z) ^ (5 - 1))) / ((1 + z) ^ 5) ^ 2) z :=
    (hp.mul (hasDerivAt_q1 z)).div (hasDerivAt_one_add_pow 5 z) (by positivity)
  rw [deriv_g1_val z hz] at h
  exact h

private lemma hasDerivAt_g2 {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun w : ℝ => w ^ 2 * q2 w / (1 + w) ^ 6) (z * q3 z / (1 + z) ^ 7) z := by
  have hp : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
  have h : HasDerivAt (fun w : ℝ => w ^ 2 * q2 w / (1 + w) ^ 6)
      (((2 * z * q2 z + z ^ 2 * (8 * z - 12)) * (1 + z) ^ 6
        - (z ^ 2 * q2 z) * ((6 : ℝ) * (1 + z) ^ (6 - 1))) / ((1 + z) ^ 6) ^ 2) z :=
    (hp.mul (hasDerivAt_q2 z)).div (hasDerivAt_one_add_pow 6 z) (by positivity)
  rw [deriv_g2_val z hz] at h
  exact h

private lemma hasDerivAt_g3 {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun w : ℝ => w ^ 2 * q3 w / (1 + w) ^ 7) (z * q4 z / (1 + z) ^ 8) z := by
  have hp : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
  have h : HasDerivAt (fun w : ℝ => w ^ 2 * q3 w / (1 + w) ^ 7)
      (((2 * z * q3 z + z ^ 2 * (-24 * z ^ 2 + 104 * z - 52)) * (1 + z) ^ 7
        - (z ^ 2 * q3 z) * ((7 : ℝ) * (1 + z) ^ (7 - 1))) / ((1 + z) ^ 7) ^ 2) z :=
    (hp.mul (hasDerivAt_q3 z)).div (hasDerivAt_one_add_pow 7 z) (by positivity)
  rw [deriv_g3_val z hz] at h
  exact h

private lemma hasDerivAt_g4 {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun w : ℝ => w ^ 2 * q4 w / (1 + w) ^ 8) (z * q5 z / (1 + z) ^ 9) z := by
  have hp : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
  have h : HasDerivAt (fun w : ℝ => w ^ 2 * q4 w / (1 + w) ^ 8)
      (((2 * z * q4 z + z ^ 2 * (64 * z ^ 3 - 588 * z ^ 2 + 832 * z - 196)) * (1 + z) ^ 8
        - (z ^ 2 * q4 z) * ((8 : ℝ) * (1 + z) ^ (8 - 1))) / ((1 + z) ^ 8) ^ 2) z :=
    (hp.mul (hasDerivAt_q4 z)).div (hasDerivAt_one_add_pow 8 z) (by positivity)
  rw [deriv_g4_val z hz] at h
  exact h


private lemma dzStep1 {z : ℝ} (hz : 0 < z) : HasDerivAt (gfun 1) (z * q2 z / (1 + z) ^ 6) z :=
  hasDerivAt_g1 hz

private lemma dzStep2 {z : ℝ} (hz : 0 < z) : HasDerivAt (gfun 2) (z * q3 z / (1 + z) ^ 7) z :=
  hasDerivAt_g2 hz

private lemma dzStep3 {z : ℝ} (hz : 0 < z) : HasDerivAt (gfun 3) (z * q4 z / (1 + z) ^ 8) z :=
  hasDerivAt_g3 hz

private lemma dzStep4 {z : ℝ} (hz : 0 < z) : HasDerivAt (gfun 4) (z * q5 z / (1 + z) ^ 9) z :=
  hasDerivAt_g4 hz

/-! ## The closed forms of the `D_z`-iterates -/

private lemma dz0 : Set.EqOn (Work.Elliptic.DzdIter 0 hk2) (gfun 0) (Set.Ioi 0) := by
  intro z hz
  show hk2 z = z ^ 2 / (1 + z) ^ 4
  exact hk2_apply z

private lemma dz1 : Set.EqOn (Work.Elliptic.DzdIter 1 hk2) (gfun 1) (Set.Ioi 0) := by
  intro z hz
  rw [Work.Elliptic.DzdIter_succ]
  show z * deriv (Work.Elliptic.DzdIter 0 hk2) z = z ^ 2 * q1 z / (1 + z) ^ 5
  rw [show Work.Elliptic.DzdIter 0 hk2 = hk2 from rfl,
    (Filter.EventuallyEq.deriv_eq (Filter.Eventually.of_forall hk2_apply)),
    (hasDerivAt_g0 hz).deriv]
  ring

private lemma dz2 : Set.EqOn (Work.Elliptic.DzdIter 2 hk2) (gfun 2) (Set.Ioi 0) := by
  intro z hz
  rw [Work.Elliptic.DzdIter_succ]
  show z * deriv (Work.Elliptic.DzdIter 1 hk2) z = z ^ 2 * q2 z / (1 + z) ^ 6
  rw [show deriv (Work.Elliptic.DzdIter 1 hk2) z = deriv (gfun 1) z from
      (dz1.deriv isOpen_Ioi) hz,
    (dzStep1 hz).deriv]
  ring

private lemma dz3 : Set.EqOn (Work.Elliptic.DzdIter 3 hk2) (gfun 3) (Set.Ioi 0) := by
  intro z hz
  rw [Work.Elliptic.DzdIter_succ]
  show z * deriv (Work.Elliptic.DzdIter 2 hk2) z = z ^ 2 * q3 z / (1 + z) ^ 7
  rw [show deriv (Work.Elliptic.DzdIter 2 hk2) z = deriv (gfun 2) z from
      (dz2.deriv isOpen_Ioi) hz,
    (dzStep2 hz).deriv]
  ring

private lemma dz4 : Set.EqOn (Work.Elliptic.DzdIter 4 hk2) (gfun 4) (Set.Ioi 0) := by
  intro z hz
  rw [Work.Elliptic.DzdIter_succ]
  show z * deriv (Work.Elliptic.DzdIter 3 hk2) z = z ^ 2 * q4 z / (1 + z) ^ 8
  rw [show deriv (Work.Elliptic.DzdIter 3 hk2) z = deriv (gfun 3) z from
      (dz3.deriv isOpen_Ioi) hz,
    (dzStep3 hz).deriv]
  ring

/-- `D_z^4 hKer² = z² q4/(1+z)^8`; the new step is `D_z^5`. -/
private lemma dz5 : Set.EqOn (Work.Elliptic.DzdIter 5 hk2) (gfun 5) (Set.Ioi 0) := by
  intro z hz
  show z * deriv (Work.Elliptic.DzdIter 4 hk2) z = z ^ 2 * q5 z / (1 + z) ^ 9
  rw [show deriv (Work.Elliptic.DzdIter 4 hk2) z = deriv (gfun 4) z from
      (dz4.deriv isOpen_Ioi) hz,
    (dzStep4 hz).deriv]
  ring

private lemma dzIter_hk2_eqOn (i : ℕ) (hi : i ≤ 5) :
    Set.EqOn (Work.Elliptic.DzdIter i (fun z : ℝ => (Work.Spaces.hKer z) ^ 2)) (gfun i)
      (Set.Ioi 0) := by
  rw [← hk2_eq_fun]
  interval_cases i
  · exact dz0
  · exact dz1
  · exact dz2
  · exact dz3
  · exact dz4
  · exact dz5

/-! ## The coefficient bounds -/

private lemma q1_le (z : ℝ) (hz : 0 ≤ z) : |q1 z| ≤ 2 * (1 + z) := by
  rw [q1, abs_le]
  constructor <;> linarith

private lemma q2_le (z : ℝ) (hz : 0 ≤ z) : |q2 z| ≤ 12 * (1 + z) ^ 2 := by
  rw [q2, abs_le]
  constructor <;>
    nlinarith [hz, sq_nonneg z, sq_nonneg (1 + z), mul_nonneg hz hz]

private lemma q3_le (z : ℝ) (hz : 0 ≤ z) : |q3 z| ≤ 52 * (1 + z) ^ 3 := by
  rw [q3, abs_le]
  constructor <;>
    nlinarith [hz, sq_nonneg z, sq_nonneg (1 + z), mul_nonneg hz hz, mul_nonneg (sq_nonneg z) hz]

private lemma q4_le (z : ℝ) (hz : 0 ≤ z) : |q4 z| ≤ 416 * (1 + z) ^ 4 := by
  rw [q4, abs_le]
  constructor <;>
    nlinarith [hz, sq_nonneg z, sq_nonneg (1 + z), mul_nonneg hz hz, mul_nonneg (sq_nonneg z) hz]

/-- The level-`5` coefficient bound.  The constant `6720` is the sum of the absolute values of
the coefficients of `q5`, and `Σ|c_k| z^k ≤ Σ|c_k|(1+z)^k ≤ (Σ|c_k|)(1+z)^5` for `z ≥ 0`. -/
private lemma q5_le (z : ℝ) (hz : 0 ≤ z) : |q5 z| ≤ 6720 * (1 + z) ^ 5 := by
  have hexp : 6720 * (1 + z) ^ 5
      = 6720 + 33600 * z + 67200 * z ^ 2 + 67200 * z ^ 3 + 33600 * z ^ 4 + 6720 * z ^ 5 := by
    ring
  have h1 : (0 : ℝ) ≤ z := hz
  have h2 : (0 : ℝ) ≤ z ^ 2 := pow_nonneg hz 2
  have h3 : (0 : ℝ) ≤ z ^ 3 := pow_nonneg hz 3
  have h4 : (0 : ℝ) ≤ z ^ 4 := pow_nonneg hz 4
  have h5 : (0 : ℝ) ≤ z ^ 5 := pow_nonneg hz 5
  rw [q5, abs_le, hexp]
  constructor <;> linarith

/-! ## The level-`5` bound -/

/-- `(1+z)^3 ≤ (1+z)^4` in the form used below. -/
private lemma div_pow4_le_div_pow3 {z : ℝ} (hz : 0 ≤ z) :
    z ^ 2 / (1 + z) ^ 4 ≤ z ^ 2 / (1 + z) ^ 3 := by
  have h1z : 0 < 1 + z := by linarith
  have hpow : (1 : ℝ) / (1 + z) ^ 4 ≤ 1 / (1 + z) ^ 3 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by linarith) (by norm_num))
  calc z ^ 2 / (1 + z) ^ 4 = z ^ 2 * (1 / (1 + z) ^ 4) := by ring
    _ ≤ z ^ 2 * (1 / (1 + z) ^ 3) := mul_le_mul_of_nonneg_left hpow (sq_nonneg z)
    _ = z ^ 2 / (1 + z) ^ 3 := by ring

/-- The generic reduction: `|q z| ≤ c (1+z)^i` and `c ≤ 6720` give the level-`5` bound. -/
private lemma gf_le_of {z : ℝ} (hz : 0 ≤ z) (i : ℕ) (Q : ℝ → ℝ) {c : ℝ}
    (hc : c ≤ 6720) (hq : |Q z| ≤ c * (1 + z) ^ i) :
    |z ^ 2 * Q z / (1 + z) ^ (4 + i)| ≤ 6720 * z ^ 2 / (1 + z) ^ 3 := by
  have h1z : 0 < 1 + z := by linarith
  have hdiv : 0 < (1 + z) ^ (4 + i) := by positivity
  have hA : 0 ≤ z ^ 2 / (1 + z) ^ 4 := by positivity
  rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg z), abs_of_nonneg (le_of_lt hdiv)]
  have h1 : z ^ 2 * |Q z| ≤ z ^ 2 * (c * (1 + z) ^ i) :=
    mul_le_mul_of_nonneg_left hq (sq_nonneg z)
  have h2 : z ^ 2 * (c * (1 + z) ^ i) / (1 + z) ^ (4 + i) = c * (z ^ 2 / (1 + z) ^ 4) := by
    rw [pow_add]
    field_simp
  have h3 : c * (z ^ 2 / (1 + z) ^ 4) ≤ 6720 * (z ^ 2 / (1 + z) ^ 3) :=
    (mul_le_mul_of_nonneg_right hc hA).trans
      (mul_le_mul_of_nonneg_left (div_pow4_le_div_pow3 hz) (by norm_num))
  calc z ^ 2 * |Q z| / (1 + z) ^ (4 + i)
      ≤ z ^ 2 * (c * (1 + z) ^ i) / (1 + z) ^ (4 + i) :=
        div_le_div_of_nonneg_right h1 (le_of_lt hdiv)
    _ = c * (z ^ 2 / (1 + z) ^ 4) := h2
    _ ≤ 6720 * (z ^ 2 / (1 + z) ^ 3) := h3
    _ = 6720 * z ^ 2 / (1 + z) ^ 3 := by ring

/-- The pointwise bound on the closed forms, for `z > 0`. -/
private lemma hk2_iter_le (i : ℕ) (hi : i ≤ 5) {z : ℝ} (hz : 0 < z) :
    |gfun i z| ≤ 6720 * z ^ 2 / (1 + z) ^ 3 := by
  have hz0 : 0 ≤ z := le_of_lt hz
  interval_cases i
  · -- `i = 0`
    show |z ^ 2 / (1 + z) ^ 4| ≤ 6720 * z ^ 2 / (1 + z) ^ 3
    rw [abs_of_nonneg (by positivity)]
    calc z ^ 2 / (1 + z) ^ 4 ≤ z ^ 2 / (1 + z) ^ 3 := div_pow4_le_div_pow3 hz0
      _ ≤ 6720 * (z ^ 2 / (1 + z) ^ 3) := by
          have hnn : (0 : ℝ) ≤ z ^ 2 / (1 + z) ^ 3 := by positivity
          linarith
      _ = 6720 * z ^ 2 / (1 + z) ^ 3 := by ring
  · exact gf_le_of hz0 1 q1 (c := 2) (by norm_num) (by simpa using q1_le z hz0)
  · exact gf_le_of hz0 2 q2 (c := 12) (by norm_num) (by simpa using q2_le z hz0)
  · exact gf_le_of hz0 3 q3 (c := 52) (by norm_num) (by simpa using q3_le z hz0)
  · exact gf_le_of hz0 4 q4 (c := 416) (by norm_num) (by simpa using q4_le z hz0)
  · exact gf_le_of hz0 5 q5 (c := 6720) (by norm_num) (by simpa using q5_le z hz0)

/-- The level-`5` radial iterates of `hKer(z)² = z²/(1+z)⁴` are bounded by `C·z²/(1+z)³`:
`D_z^i hKer² = z²q_i(z)/(1+z)^(4+i)` with `deg q_i ≤ i`, so `|D_z^i hKer² z| ≤ (Σ|coeffs|)·z²/(1+z)³`.
The file `Submission.Work.FTS.Nonlinear.Pieces.RNP.hkerSqAux` contains the whole computation for
`i ≤ 4` (private: `dzIter_hk2_eqOn`, `q1`–`q4`, `deriv_g*_val`, `hasDerivAt_g*`, `q*_le`); the new
step is `q5 = (1+z)(2q4 + z·q4') − 8z·q4 = 32 − 684z + 2644z² − 2644z³ + 684z⁴ − 32z⁵`, with
`|q4 z| ≤ 416(1+z)^4`, `|q5 z| ≤ 6720(1+z)^5` on `[0,∞)`.  The private lemmas may be copied
into the new file (do not edit `hkerSqAux.lean`). -/
theorem DzIter_hKerSq_le5 : ∃ C : ℝ, 0 < C ∧ ∀ i : ℕ, i ≤ 5 → ∀ z : ℝ, 0 ≤ z →
    |Work.Elliptic.DzdIter i (fun z : ℝ => (Work.Spaces.hKer z) ^ 2) z|
      ≤ C * z ^ 2 / (1 + z) ^ 3 := by
  refine ⟨6720, by norm_num, fun i hi z hz => ?_⟩
  rcases eq_or_lt_of_le hz with h0 | hpos
  · -- `z = 0`: the iterates of order `≥ 1` carry a factor `z`, and `hKer 0 = 0`
    subst h0
    cases i with
    | zero => simp [Work.Elliptic.DzdIter_zero, Work.Spaces.hKer_apply]
    | succ k => rw [Work.Elliptic.DzdIter_succ]; simp [Work.Elliptic.Dzd]
  · -- `z > 0`: use the closed form `D_z^i hKer² = z² q_i/(1+z)^(4+i)`
    rw [dzIter_hk2_eqOn i hi hpos]
    exact hk2_iter_le i hi hpos

end Work.FTS.StrongEps.H5.Atoms
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.RadHkMemXn_gen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.H5

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The level-`k` version of `Work.FTS.StrongEps.ClassCRHS.RadHkMemXn`**: a radial profile
whose `z∂_z`-iterates up to order `k` are bounded by `C·z²/(1+z)³` is `ℋᵏ`-honest with an
`α`-uniform `ℋ⁴`-norm bound.

Because `r` depends on `z` only, every mixed slot `D_z^jD_θ^i r` with `i ≥ 1` vanishes, so the
`ℋᵏ`-integrand reduces to the pure `D_z`-sum; the weight `w(z) = (1+z)²/z²` converts the
hypothesis into `|D_z^i r · w| ≤ C/(1+z)`, whence the radial density is dominated by
`(k+1)(C/(1+z))²`, which is integrable on `[0,∞)` with integral at most `2`.

(Note `Work.FTS.Nonlin.Xn α g = HkNorm α 4 g` is fixed at level `4`; the intended uses are
`k = 4, 5`, where the conclusion bounds the level-`4` norm of the lift.) -/
theorem RadHkMemXn_gen {r : ℝ → ℝ} {C : ℝ} {k : ℕ} (hC : 0 < C)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n r (Set.Ioi 0))
    (h : ∀ i : ℕ, i ≤ k → ∀ z : ℝ, 0 ≤ z →
      |Work.Elliptic.DzdIter i r z| ≤ C * z ^ 2 / (1 + z) ^ 3) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
      Work.Spaces.HkMem α k (fun z (_ : ℝ) => r z) ∧
      Work.FTS.Nonlin.Xn α (fun z (_ : ℝ) => r z) ≤ C' := by
  -- ### Step 1: the pointwise slot bound `(D_z^i r)² w² ≤ (C/(1+z))²` on `Iz`.
  have hslot : ∀ (i : ℕ), i ≤ k → ∀ z ∈ Work.Spaces.Iz,
      (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2 ≤ (C / (1 + z)) ^ 2 := by
    intro i hi z hz
    have hz0 : 0 ≤ z := hz
    have habs := h i hi z hz0
    have hsq : (Work.Elliptic.DzdIter i r z) ^ 2 ≤ (C * z ^ 2 / (1 + z) ^ 3) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    have hprod := mul_le_mul_of_nonneg_right hsq (sq_nonneg (Work.Spaces.w z))
    rcases eq_or_lt_of_le hz0 with hz' | hz'
    · rw [← hz']
      have hw0 : Work.Spaces.w (0 : ℝ) = 0 := by simp [Work.Spaces.w]
      rw [hw0]
      simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero, div_one]
      exact sq_nonneg C
    · refine hprod.trans (le_of_eq ?_)
      rw [Work.Spaces.w]
      field_simp
  -- ### Step 2: the `θ`-integral of the level-`k` radial integrand.
  have hKth_pos : 0 < Work.FTS.Nonlinear.RadialProd.Kth :=
    lt_of_lt_of_le one_pos Work.FTS.Nonlinear.RadialProd.one_le_Kth
  refine ⟨max 1 (Real.sqrt (Work.FTS.Nonlinear.RadialProd.Rr r
      * Work.FTS.Nonlinear.RadialProd.Kth)), lt_of_lt_of_le one_pos (le_max_left 1 _), ?_⟩
  intro α _hα
  constructor
  · -- ### Step 3: `HkMem α k (fun z _ => r z)`.
    -- the pointwise bound for the pure `D_z`-sum
    have hsum_le : ∀ z ∈ Work.Spaces.Iz,
        (∑ i ∈ Finset.range (k + 1),
            (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ ((k : ℝ) + 1) * (C / (1 + z)) ^ 2 := by
      intro z hz
      calc (∑ i ∈ Finset.range (k + 1),
              (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ ∑ _i ∈ Finset.range (k + 1), (C / (1 + z)) ^ 2 :=
            Finset.sum_le_sum (fun i hi => hslot i (by
              have := Finset.mem_range.mp hi; omega) z hz)
        _ = ((k : ℝ) + 1) * (C / (1 + z)) ^ 2 := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    -- the exact value of the angular integral
    have hinner_eq : ∀ z : ℝ,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fun z (_ : ℝ) => r z) z θ)
          = (∑ i ∈ Finset.range (k + 1),
              (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2)
              * Work.FTS.Nonlinear.RadialProd.Kth := by
      intro z
      have hEq : (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (fun z (_ : ℝ) => r z) z θ)
          = ∫ θ in Work.Spaces.Iθ,
              (∑ i ∈ Finset.range (k + 1),
                (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2)
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        MeasureTheory.setIntegral_congr_fun (s := Work.Spaces.Iθ) measurableSet_Icc
          (fun θ hθ => by
            rw [Work.Elliptic.HkIntegrand_rad α k r z hθ, ← Finset.sum_mul])
      rw [hEq, MeasureTheory.integral_const_mul]
      simp only [Work.FTS.Nonlinear.RadialProd.Kth, Work.FTS.Nonlinear.RadialProd.smE]
    -- the pointwise bound on the angular integral
    have hinner_le : ∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fun z (_ : ℝ) => r z) z θ)
          ≤ (((k : ℝ) + 1) * (C / (1 + z)) ^ 2) * Work.FTS.Nonlinear.RadialProd.Kth := by
      intro z hz
      rw [hinner_eq z]
      exact mul_le_mul_of_nonneg_right (hsum_le z hz) hKth_pos.le
    -- the majorant is integrable on `Iz`
    have hmaj_int : MeasureTheory.IntegrableOn
        (fun z : ℝ => (((k : ℝ) + 1) * (C / (1 + z)) ^ 2)
          * Work.FTS.Nonlinear.RadialProd.Kth) Work.Spaces.Iz := by
      have h1 : MeasureTheory.Integrable (fun z : ℝ =>
          ((((k : ℝ) + 1) * C ^ 2) * Work.FTS.Nonlinear.RadialProd.Kth)
            * (1 / (1 + z)) ^ 2) (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
        Work.FTS.H2.InvOneAddSq.1.const_mul _
      have h2 : MeasureTheory.Integrable (fun z : ℝ =>
          (((k : ℝ) + 1) * (C / (1 + z)) ^ 2) * Work.FTS.Nonlinear.RadialProd.Kth)
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
        h1.congr (Filter.Eventually.of_forall fun z => by ring)
      rw [MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))] at h2
      exact h2
    -- a.e. strong measurability of a single radial slot
    have hw_aesm : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      (by
        have hfun : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
            = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by
          funext z; rw [Work.Spaces.w]
        rw [hfun]
        fun_prop : Measurable fun z : ℝ => (Work.Spaces.w z) ^ 2).aestronglyMeasurable
    have hDzd_aesm : ∀ i : ℕ, MeasureTheory.AEStronglyMeasurable
        (fun z : ℝ => (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      intro i
      by_cases hi0 : i = 0
      · subst hi0
        have hr_aesm : MeasureTheory.AEStronglyMeasurable r
            (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
          have h1 : MeasureTheory.AEStronglyMeasurable r
              (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
            (hsm 0).continuousOn.aestronglyMeasurable measurableSet_Ioi
          rwa [MeasureTheory.Measure.restrict_congr_set
            (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))] at h1
        have hfun : (fun z : ℝ => (Work.Elliptic.DzdIter 0 r z) ^ 2
              * (Work.Spaces.w z) ^ 2)
            = fun z : ℝ => (r z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
          funext z; rw [Work.Elliptic.DzdIter_zero]
        rw [hfun]
        exact (hr_aesm.pow 2).mul hw_aesm
      · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
        have hmeas : Measurable (Work.Elliptic.DzdIter (n + 1) r) := by
          have hfun : Work.Elliptic.DzdIter (n + 1) r
              = fun z : ℝ => z * deriv (Work.Elliptic.DzdIter n r) z := rfl
          rw [hfun]
          exact measurable_id.mul (measurable_deriv _)
        exact ((hmeas.aestronglyMeasurable).pow 2).mul hw_aesm
    -- a.e. strong measurability of the outer function
    have houter_aesm : MeasureTheory.AEStronglyMeasurable
        (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z (_ : ℝ) => r z) z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      rw [show (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (fun z (_ : ℝ) => r z) z θ)
          = (fun z : ℝ => (∑ i ∈ Finset.range (k + 1),
              (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2)
              * Work.FTS.Nonlinear.RadialProd.Kth) from funext hinner_eq]
      have hfun : (fun z : ℝ => (∑ i ∈ Finset.range (k + 1),
              (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2)
              * Work.FTS.Nonlinear.RadialProd.Kth)
          = ∑ i ∈ Finset.range (k + 1),
              fun z : ℝ => ((Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2)
                * Work.FTS.Nonlinear.RadialProd.Kth := by
        funext z
        rw [Finset.sum_apply]
        rw [Finset.sum_mul, ← Finset.sum_mul]
      rw [hfun]
      exact Finset.aestronglyMeasurable_sum _ (fun i _ => (hDzd_aesm i).mul_const _)
    refine ⟨?_, ?_⟩
    · -- every angular slice of the integrand is integrable
      intro z _hz
      have hconst : MeasureTheory.IntegrableOn
          (fun θ : ℝ => ((∑ i ∈ Finset.range (k + 1),
            (Work.Elliptic.DzdIter i r z) ^ 2) * (Work.Spaces.w z) ^ 2)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
        ((Work.FTS.LocData.integral_sin_two_rpow_neg Work.Spaces.eta Work.Spaces.eta_pos
          Work.Spaces.eta_lt_one).1).const_mul _
      refine hconst.congr_fun (fun θ hθ => ?_) measurableSet_Icc
      rw [Work.Elliptic.HkIntegrand_rad α k r z hθ]
    · -- the `z`-integral of the angular slices is integrable
      refine MeasureTheory.Integrable.mono' hmaj_int houter_aesm ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg
        (fun θ => Work.Spaces.HkIntegrand_nonneg α k (fun z (_ : ℝ) => r z) z θ))]
      exact hinner_le z hz
  · -- ### Step 4: the `α`-uniform `ℋ⁴`-norm bound (`Xn` is the *level-`4`* norm).
    calc Work.FTS.Nonlin.Xn α (fun z (_ : ℝ) => r z)
        = Real.sqrt (Work.Spaces.HkSq α 4 (fun z (_ : ℝ) => r z)) := by
          simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]
      _ = Real.sqrt (Work.FTS.Nonlinear.RadialProd.Rr r
            * Work.FTS.Nonlinear.RadialProd.Kth) := by
          rw [Work.FTS.Nonlinear.RadialProd.HkSq_rad_eq α r]
      _ ≤ max 1 (Real.sqrt (Work.FTS.Nonlinear.RadialProd.Rr r
            * Work.FTS.Nonlinear.RadialProd.Kth)) := le_max_right _ _

end Work.FTS.StrongEps.H5
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.WProd5.Gmaj5 =====
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

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `HgInt5 α g z = ∫_θ HkIntegrand α 5 g z θ`, the angular integral of the `ℋ⁵`-integrand of
`g` at fixed radius.  (Its `z`-integral is `HkSq α 5 g` by definition.) -/
def HgInt5 (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Iθ, HkIntegrand α 5 g z θ

/-- **The pointwise majorant of the `𝒲^{5,∞}`-priced product rule**: the `ℋ⁵`-integrand of `g`
plus the angular contribution of the mean-term bound for the radial slots of `g` (`HgInt5`) and
of the angular `L²`-norms `Aang` of the mixed slots of `g`, multiplied by the surviving angular
factor `TW`. -/
def GmajW5 (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  HkIntegrand α 5 g z θ
    + (HgInt5 α g z
        + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 5, Work.FTS.H2.WPQ.Aang α g d z)
      * Work.FTS.OpenPkg.WProdWin.TW α θ

/-! ## Elementary properties -/

theorem HgInt5_nonneg (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ HgInt5 α g z :=
  integral_nonneg fun θ => HkIntegrand_nonneg α 5 g z θ

theorem Aang_nonneg5 (α : ℝ) (g : ℝ → ℝ → ℝ) (d : ℕ) (z : ℝ) :
    0 ≤ Work.FTS.H2.WPQ.Aang α g d z :=
  setIntegral_nonneg measurableSet_Icc fun σ _ => sq_nonneg _

theorem sum_Aang_nonneg5 (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    0 ≤ ∑ d ∈ Finset.range 5, Work.FTS.H2.WPQ.Aang α g d z :=
  Finset.sum_nonneg fun d _ => Aang_nonneg5 α g d z

theorem GmajW5_nonneg {α : ℝ} (hα : 0 < α) (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Iθ) :
    0 ≤ GmajW5 α g z θ := by
  have hγ1 : (0 : ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
  refine add_nonneg (HkIntegrand_nonneg α 5 g z θ)
    (mul_nonneg (add_nonneg (HgInt5_nonneg α g z)
      (mul_nonneg (inv_nonneg.mpr hγ1.le) (sum_Aang_nonneg5 α g z)))
      (Work.FTS.OpenPkg.WProdWin.TW_nonneg hα.le hθ))

/-- The `ℋ⁵`-integrand of `g` is dominated by the majorant. -/
theorem HkIntegrand_le_GmajW5 {α : ℝ} (hα : 0 < α) (g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Iθ) :
    HkIntegrand α 5 g z θ ≤ GmajW5 α g z θ := by
  have hγ1 : (0 : ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
  refine le_add_of_nonneg_right (mul_nonneg (add_nonneg (HgInt5_nonneg α g z)
    (mul_nonneg (inv_nonneg.mpr hγ1.le) (sum_Aang_nonneg5 α g z)))
    (Work.FTS.OpenPkg.WProdWin.TW_nonneg hα.le hθ))

/-- The `ℋ⁵`-integrand vanishes whenever `sin(2θ) = 0` (the level-six instance of
`Work.FTS.H2.WPQ.HkIntegrand_eq_zero_of_sin_two_eq_zero`). -/
theorem HkIntegrand5_eq_zero_of_sin_two_eq_zero {α : ℝ} (hα : gam α ≠ 0)
    {F : ℝ → ℝ → ℝ} {z θ : ℝ} (h : Real.sin (2 * θ) = 0) :
    HkIntegrand α 5 F z θ = 0 := by
  have hη : (eta / 2 : ℝ) ≠ 0 := by norm_num [eta]
  have hg : -(gam α / 2) ≠ 0 := by
    intro hc
    exact hα (by linarith [neg_eq_zero.mp hc])
  simp only [HkIntegrand, Wt, wTheta]
  rw [h, Real.zero_rpow hη, Real.zero_rpow hg]
  simp

/-- The sum of the angular `L²`-norms of the mixed slots of `g` is dominated by the mean term. -/
theorem sum_Aang_le_HgInt5 {α : ℝ} {g : ℝ → ℝ → ℝ} (hgm : HkMem α 5 g) {z : ℝ}
    (hz : z ∈ Iz) :
    ∑ d ∈ Finset.range 5, Work.FTS.H2.WPQ.Aang α g d z ≤ 5 * HgInt5 α g z := by
  have hd : ∀ d ∈ Finset.range 5, Work.FTS.H2.WPQ.Aang α g d z ≤ HgInt5 α g z := by
    intro d hd5
    have hd4 : d ≤ 4 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd5)
    refine integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _) (hgm.1 z hz)
      (ae_restrict_of_forall_mem measurableSet_Icc fun θ _ =>
        sq_le_HkIntegrand_mixed α 5 g z θ 1 d le_rfl (by omega))
  calc ∑ d ∈ Finset.range 5, Work.FTS.H2.WPQ.Aang α g d z
      ≤ ∑ _d ∈ Finset.range 5, HgInt5 α g z := Finset.sum_le_sum hd
    _ = 5 * HgInt5 α g z := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num

/-- **The mean term controls the radial slots of `g`**:
`w(z)² ∫_σ (D_z^d g(z,σ))² ≤ HgInt5 α g z` for `d ≤ 5`. -/
theorem w_sq_mul_slice_le_HgInt5 {α : ℝ} {g : ℝ → ℝ → ℝ} (hgm : HkMem α 5 g) {d : ℕ}
    (hd : d ≤ 5) {z : ℝ} (hz : 0 < z) :
    (w z) ^ 2 * (∫ σ in Iθ, (DzIter d g z σ) ^ 2) ≤ HgInt5 α g z := by
  have hzI : z ∈ Iz := le_of_lt hz
  have hdiv : (w z) ^ 2 * (∫ σ in Iθ, (DzIter d g z σ) ^ 2)
      = ∫ σ in Iθ, (w z) ^ 2 * (DzIter d g z σ) ^ 2 := by
    rw [MeasureTheory.integral_const_mul]
  rw [hdiv]
  refine integral_mono_of_nonneg
    (Eventually.of_forall fun σ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hgm.1 z hzI) ?_
  filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ hσ
  have hs : 0 < Real.sin (2 * σ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1]) (by linarith [hσ.2, Real.pi_pos])
  have hspos : 0 < (Real.sin (2 * σ)) ^ (eta / 2) := Real.rpow_pos_of_pos hs _
  have hkey : DzIter d g z σ * (w z / (Real.sin (2 * σ)) ^ (eta / 2))
        * (Real.sin (2 * σ)) ^ (eta / 2) = DzIter d g z σ * w z := by
    rw [mul_assoc, div_mul_cancel₀ _ (ne_of_gt hspos)]
  have hsq : ((Real.sin (2 * σ)) ^ (eta / 2)) ^ (2 : ℕ) = (Real.sin (2 * σ)) ^ eta := by
    rw [pow_two, ← Real.rpow_add hs]
    congr 1
    rw [eta]; ring
  calc (w z) ^ 2 * (DzIter d g z σ) ^ 2
      = (DzIter d g z σ * w z) ^ 2 := by ring
    _ = (DzIter d g z σ * (w z / (Real.sin (2 * σ)) ^ (eta / 2))
          * (Real.sin (2 * σ)) ^ (eta / 2)) ^ 2 := by rw [hkey]
    _ = (DzIter d g z σ * (w z / (Real.sin (2 * σ)) ^ (eta / 2))) ^ 2
          * (Real.sin (2 * σ)) ^ eta := by
        rw [mul_pow, hsq]
    _ ≤ (DzIter d g z σ * (w z / (Real.sin (2 * σ)) ^ (eta / 2))) ^ 2 * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        exact Real.rpow_le_one hs.le (Real.sin_le_one _) (by norm_num [eta])
    _ ≤ HkIntegrand α 5 g z σ := by
        rw [mul_one]
        exact sq_le_HkIntegrand_z α 5 g z σ d hd

/-- `HgInt5` integrates to `HkSq α 5 g` (definitional). -/
theorem HgInt5_z_integral (α : ℝ) (g : ℝ → ℝ → ℝ) :
    (∫ z in Iz, HgInt5 α g z) = HkSq α 5 g := rfl

/-- The angular slice of the majorant is integrable, for every `z ∈ Iz`. -/
theorem GmajW5_integrableOn_theta {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hgm : HkMem α 5 g) {z : ℝ} (hz : z ∈ Iz) :
    IntegrableOn (fun θ => GmajW5 α g z θ) Iθ := by
  have h2 : IntegrableOn (fun θ => (HgInt5 α g z
      + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 5, Work.FTS.H2.WPQ.Aang α g d z)
        * Work.FTS.OpenPkg.WProdWin.TW α θ) Iθ :=
    (Work.FTS.OpenPkg.WProdWin.TW_integrable hα hα1).const_mul _
  refine Integrable.congr ((hgm.1 z hz).add h2) ?_
  filter_upwards with θ
  simp only [Pi.add_apply, GmajW5]

/-- The angular integral of the majorant at a fixed radius. -/
theorem GmajW5_theta_integral_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hgm : HkMem α 5 g) {z : ℝ} (hz : z ∈ Iz) :
    (∫ θ in Iθ, GmajW5 α g z θ) ≤ (1 + 700 * (1 + 5 * (gam α - 1)⁻¹)) * HgInt5 α g z := by
  have hγ1 : (0 : ℝ) < gam α - 1 := by rw [gam_sub_one]; linarith
  have hγinv : 0 ≤ (gam α - 1)⁻¹ := inv_nonneg.mpr hγ1.le
  have hhg : IntegrableOn (fun θ => HkIntegrand α 5 g z θ) Iθ := hgm.1 z hz
  have hsum : ∑ d ∈ Finset.range 5, Work.FTS.H2.WPQ.Aang α g d z ≤ 5 * HgInt5 α g z :=
    sum_Aang_le_HgInt5 hgm hz
  have h2 : IntegrableOn (fun θ => (HgInt5 α g z
      + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 5, Work.FTS.H2.WPQ.Aang α g d z)
        * Work.FTS.OpenPkg.WProdWin.TW α θ) Iθ :=
    (Work.FTS.OpenPkg.WProdWin.TW_integrable hα hα1).const_mul _
  have hsplit : (∫ θ in Iθ, GmajW5 α g z θ)
      = HgInt5 α g z + (HgInt5 α g z
          + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 5, Work.FTS.H2.WPQ.Aang α g d z)
            * (∫ θ in Iθ, Work.FTS.OpenPkg.WProdWin.TW α θ) := by
    have hfun : (fun θ : ℝ => GmajW5 α g z θ)
        = fun θ : ℝ => HkIntegrand α 5 g z θ
            + (HgInt5 α g z + (gam α - 1)⁻¹
                * ∑ d ∈ Finset.range 5, Work.FTS.H2.WPQ.Aang α g d z)
              * Work.FTS.OpenPkg.WProdWin.TW α θ := by
      funext θ; rw [GmajW5]
    rw [hfun, MeasureTheory.integral_add hhg h2, MeasureTheory.integral_const_mul]
    rfl
  rw [hsplit]
  have hT := Work.FTS.OpenPkg.WProdWin.TW_integral_le hα hα1
  have hTnn : 0 ≤ ∫ θ in Iθ, Work.FTS.OpenPkg.WProdWin.TW α θ :=
    setIntegral_nonneg measurableSet_Icc (fun θ hθ => Work.FTS.OpenPkg.WProdWin.TW_nonneg hα.le hθ)
  have hbr : HgInt5 α g z + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 5,
        Work.FTS.H2.WPQ.Aang α g d z
      ≤ HgInt5 α g z + (gam α - 1)⁻¹ * (5 * HgInt5 α g z) :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum hγinv)
  have hmain : (HgInt5 α g z + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 5,
        Work.FTS.H2.WPQ.Aang α g d z) * (∫ θ in Iθ, Work.FTS.OpenPkg.WProdWin.TW α θ)
      ≤ (HgInt5 α g z + (gam α - 1)⁻¹ * (5 * HgInt5 α g z)) * 700 :=
    mul_le_mul hbr hT hTnn
      (add_nonneg (HgInt5_nonneg α g z) (mul_nonneg hγinv (mul_nonneg (by norm_num)
        (HgInt5_nonneg α g z))))
  calc HgInt5 α g z + (HgInt5 α g z + (gam α - 1)⁻¹ * ∑ d ∈ Finset.range 5,
        Work.FTS.H2.WPQ.Aang α g d z) * (∫ θ in Iθ, Work.FTS.OpenPkg.WProdWin.TW α θ)
      ≤ HgInt5 α g z + (HgInt5 α g z + (gam α - 1)⁻¹ * (5 * HgInt5 α g z)) * 700 :=
        add_le_add le_rfl hmain
    _ = (1 + 700 * (1 + 5 * (gam α - 1)⁻¹)) * HgInt5 α g z := by ring


end Work.FTS.StrongEps.H5.WProd5
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.R.zw2_deriv_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux.R

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

/-!
# Integrability of `u²·∂_z(z w²)·σ` from integrability of `u²·w²·σ`

With the radial weight `w z = (1+z)²/z²` (so that `z w² = (1+z)⁴/z³`), the differentiated
weight factors through the weight itself:

  `∂_z(z w²) = ((z-3)/(1+z))·w²`   for `z > 0`,

and the factor `(z-3)/(1+z)` is **bounded by `3` in absolute value on `z ≥ 0`**.  Hence

  `u²·∂_z(z w²)·σ = ((z-3)/(1+z))·(u²·w²·σ)`   away from the null set `{z = 0}`,

so the `∂_z(z w²)`-integrand is the given integrand `u²·w²·σ` multiplied by a measurable
function that is bounded almost everywhere; integrability is preserved by
`MeasureTheory.Integrable.mul_bdd`.

This is the `∂_z(z w²)`-slot of the sharp-hypothesis package of the `H⁶` layer: the
`z`-integration by parts there replaces `u²·w²·σ` by `u²·∂_z(z w²)·σ`, and this lemma records
that the replacement preserves integrability (so no regularity of `u` is needed, only the
integrability of the original integrand).

The hypothesis `hσ` (`σ ≥ 0` on `Iθ`) is *not* needed for the implication — the factorisation
above multiplies the *given* integrand by a bounded factor, with no positivity argument — but
it is part of the requested interface.
-/

/-- The differentiated radial weight, factored through the weight itself:
`∂_z(z·w z²) = w z² · ((z-3)/(1+z))` for `z > 0`. -/
private theorem deriv_zw2_factor {z : ℝ} (hz : 0 < z) :
    deriv (fun z' => z' * (Work.Spaces.w z') ^ 2) z
      = (Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)) := by
  rw [Work.FTS.EllipticEst.weight_algebra_fts.2.2.2.1 z (ne_of_gt hz)]
  have hz0 : z ≠ 0 := ne_of_gt hz
  have h1z : (1 : ℝ) + z ≠ 0 := by linarith
  rw [Work.Spaces.w]
  field_simp

/-- The factor `(z-3)/(1+z)` is bounded by `3` in absolute value on `z ≥ 0`. -/
private theorem abs_ratio_le_three {z : ℝ} (hz : 0 ≤ z) : |(z - 3) / (1 + z)| ≤ 3 := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  rw [abs_div, abs_of_pos h1z, div_le_iff₀ h1z]
  have h : |z - 3| ≤ 3 + 3 * z := by
    rw [abs_le]
    constructor <;> linarith
  linarith

theorem zw2_deriv_integrable {u : ℝ → ℝ → ℝ} {σ : ℝ → ℝ}
    (hσ : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ σ θ)
    (h1 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * (Work.Spaces.w z) ^ 2 * σ θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2
        * deriv (fun z' => z' * (Work.Spaces.w z') ^ 2) z * σ θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  -- Work with the product of the two restricted measures on the quadrant.
  have hm : (volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_restrict]
  rw [MeasureTheory.IntegrableOn, hm] at h1 ⊢
  -- The sign hypothesis is not needed; record it for the reader.
  have hfnn : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      0 ≤ u z θ ^ 2 * (Work.Spaces.w z) ^ 2 * σ θ := fun z _ θ hθ =>
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hσ θ hθ)
  -- The bounded measurable factor `(z-3)/(1+z)`.
  have hg : AEStronglyMeasurable (fun p : ℝ × ℝ => (p.1 - 3) / (1 + p.1))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    have : Measurable (fun p : ℝ × ℝ => (p.1 - 3) / (1 + p.1)) := by fun_prop
    exact this.aestronglyMeasurable
  have hb : ∀ᵐ p ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)),
      ‖(p.1 - 3) / (1 + p.1)‖ ≤ (3 : ℝ) := by
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_prod_fst_pos] with p hp
    rw [Real.norm_eq_abs]
    exact abs_ratio_le_three hp.le
  -- Multiplying the given integrand by the bounded factor stays integrable.
  refine (h1.mul_bdd hg hb).congr ?_
  -- The product is the target integrand, a.e. (everywhere except on `{z = 0}`).
  filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_prod_fst_pos] with p hp
  dsimp only [Function.uncurry]
  rw [deriv_zw2_factor hp]
  ring

end

end Work.FTS.StrongPersist.H6Aux.R
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.Cd6Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.FTS.GalBasis.ApproxCC (partialZ partialT)

/-! ## The uncurried forms of `D_z` and `D_θ` -/

/-- `D_z X = z ∂_z X`, as an identity of uncurried functions. -/
theorem uncurry_Dz_eq (X : ℝ → ℝ → ℝ) :
    Function.uncurry (Work.Spaces.Dz X)
      = fun p : ℝ × ℝ => p.1 * partialZ (Function.uncurry X) p := rfl

/-- `D_θ X = sin(2θ) ∂_θ X`, as an identity of uncurried functions. -/
theorem uncurry_Dth_eq (X : ℝ → ℝ → ℝ) :
    Function.uncurry (Work.Spaces.Dth X)
      = fun p : ℝ × ℝ => Real.sin (2 * p.2) * partialT (Function.uncurry X) p := rfl

/-- `(z,θ) ↦ sin(2θ)` is `C^n` on the open quadrant. -/
theorem contDiffOn_sin_two_snd (n : ℕ) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
  (((Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).of_le le_top).contDiffOn).mono
    (Set.subset_univ _)

/-! ## The one-step order loss -/

/-- `D_z` loses one order of `ContDiffOn` on the open quadrant. -/
theorem contDiffOn_uncurry_Dz_step {M n : ℕ} {X : ℝ → ℝ → ℝ} (hn : n + 1 = M)
    (h : ContDiffOn ℝ M (Function.uncurry X) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz X)) Work.FTS.EllipticEst.Q0 := by
  rw [uncurry_Dz_eq]
  rw [← hn] at h
  exact contDiffOn_fst.mul
    (Work.FTS.GalBasis.ApproxCC.contDiffOn_partialZ Work.FTS.EllipticEst.isOpen_Q0 h)

/-- `D_θ` loses one order of `ContDiffOn` on the open quadrant. -/
theorem contDiffOn_uncurry_Dth_step {M n : ℕ} {X : ℝ → ℝ → ℝ} (hn : n + 1 = M)
    (h : ContDiffOn ℝ M (Function.uncurry X) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dth X)) Work.FTS.EllipticEst.Q0 := by
  rw [uncurry_Dth_eq]
  rw [← hn] at h
  exact (contDiffOn_sin_two_snd n).mul
    (Work.FTS.GalBasis.ApproxCC.contDiffOn_partialT Work.FTS.EllipticEst.isOpen_Q0 h)

/-! ## The iterated operators -/

/-- `D_z^i h` is `C^N` on the open quadrant whenever `h` is `C^{i+N}` there. -/
theorem contDiffOn_uncurry_DzIter_aux {M : ℕ} {X : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ M (Function.uncurry X) Work.FTS.EllipticEst.Q0) :
    ∀ i N : ℕ, i + N = M →
      ContDiffOn ℝ N (Function.uncurry (Work.Spaces.DzIter i X))
        Work.FTS.EllipticEst.Q0 := by
  intro i
  induction i with
  | zero =>
      intro N hN
      rw [← hN] at h
      simpa using h
  | succ i ih =>
      intro N hN
      have h1 : ContDiffOn ℝ (N + 1) (Function.uncurry (Work.Spaces.DzIter i X))
          Work.FTS.EllipticEst.Q0 := ih (N + 1) (by omega)
      have h2 := contDiffOn_uncurry_Dz_step (M := N + 1) (n := N) (by omega) h1
      simpa only [Work.Spaces.DzIter_succ] using h2

/-- `D_θ^i h` is `C^N` on the open quadrant whenever `h` is `C^{i+N}` there. -/
theorem contDiffOn_uncurry_DthIter_aux {M : ℕ} {X : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ M (Function.uncurry X) Work.FTS.EllipticEst.Q0) :
    ∀ i N : ℕ, i + N = M →
      ContDiffOn ℝ N (Function.uncurry (Work.Spaces.DthIter i X))
        Work.FTS.EllipticEst.Q0 := by
  intro i
  induction i with
  | zero =>
      intro N hN
      rw [← hN] at h
      simpa using h
  | succ i ih =>
      intro N hN
      have h1 : ContDiffOn ℝ (N + 1) (Function.uncurry (Work.Spaces.DthIter i X))
          Work.FTS.EllipticEst.Q0 := ih (N + 1) (by omega)
      have h2 := contDiffOn_uncurry_Dth_step (M := N + 1) (n := N) (by omega) h1
      simpa only [Work.Spaces.DthIter_succ] using h2

/-- `D_z^j D_θ^i h` is `C^N` on the open quadrant whenever `h` is `C^{i+j+N}` there. -/
theorem contDiffOn_uncurry_mixed_aux {M : ℕ} {X : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ M (Function.uncurry X) Work.FTS.EllipticEst.Q0) :
    ∀ j i N : ℕ, i + j + N = M →
      ContDiffOn ℝ N (Function.uncurry (Work.Spaces.mixed j i X))
        Work.FTS.EllipticEst.Q0 := by
  intro j i N hN
  set V : ℕ := j + N with hV
  have h1 : ContDiffOn ℝ V (Function.uncurry (Work.Spaces.DthIter i X))
      Work.FTS.EllipticEst.Q0 := contDiffOn_uncurry_DthIter_aux h i V (by omega)
  have h2 : ContDiffOn ℝ N
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.DthIter i X)))
      Work.FTS.EllipticEst.Q0 := contDiffOn_uncurry_DzIter_aux h1 j N (by omega)
  simpa only [Work.Spaces.mixed] using h2

/-- Continuity of `D_z^i h` on the open quadrant for `i ≤ 6`, for `h` of class `C^6`. -/
theorem continuousOn_uncurry_DzIter {X : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 6 (Function.uncurry X) Work.FTS.EllipticEst.Q0)
    {i : ℕ} (hi : i ≤ 6) :
    ContinuousOn (Function.uncurry (Work.Spaces.DzIter i X)) Work.FTS.EllipticEst.Q0 :=
  (contDiffOn_uncurry_DzIter_aux (M := 6) h i (6 - i) (by omega)).continuousOn

/-- Continuity of `D_z^j D_θ^i h` on the open quadrant for `i + j ≤ 6`. -/
theorem continuousOn_uncurry_mixed {X : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 6 (Function.uncurry X) Work.FTS.EllipticEst.Q0)
    {j i : ℕ} (hij : i + j ≤ 6) :
    ContinuousOn (Function.uncurry (Work.Spaces.mixed j i X)) Work.FTS.EllipticEst.Q0 :=
  (contDiffOn_uncurry_mixed_aux (M := 6) h j i (6 - i - j) (by omega)).continuousOn

/-- A pointwise product of two `C^6` functions on the open quadrant is `C^6`. -/
theorem contDiffOn_uncurry_mul_cd6 {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ 6 (Function.uncurry (fun z θ => f z θ * g z θ))
      Work.FTS.EllipticEst.Q0 := by
  have h : Function.uncurry (fun z θ => f z θ * g z θ)
      = Function.uncurry f * Function.uncurry g := by
    funext p; obtain ⟨z, θ⟩ := p; rfl
  rw [h]; exact hf.mul hg

/-! ## Continuity of the weighted integrand on the open quadrant -/

/-- `HkIntegrand α k h` is continuous on the open quadrant, for `k ≤ 6`, as soon as `h` is
`C^6` there.  (The `SmoothOpen` version is `EllipticEst.SmoothOpen.continuousOn_HkIntegrand`.) -/
theorem continuousOn_HkIntegrand_cd6 {α : ℝ} {k : ℕ} (hk : k ≤ 6) {h : ℝ → ℝ → ℝ}
    (hh : ContDiffOn ℝ 6 (Function.uncurry h) Work.FTS.EllipticEst.Q0) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hz : ∀ i : ℕ, i ≤ k →
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i h p.1 p.2)
        Work.FTS.EllipticEst.Q0 :=
    fun i hi => continuousOn_uncurry_DzIter hh (Nat.le_trans hi hk)
  have hm : ∀ j i : ℕ, i + j ≤ k →
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i h p.1 p.2)
        Work.FTS.EllipticEst.Q0 :=
    fun j i hij => continuousOn_uncurry_mixed hh (Nat.le_trans hij hk)
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hWt : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
        = fun p : ℝ × ℝ => Work.Spaces.w p.1
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
      funext p; rfl
    rw [hfun]
    have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        Work.FTS.EllipticEst.Q0 := by
      have hfun2 : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
          = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
      rw [hfun2]
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
        (continuousOn_fst.pow 2) (fun p hp => ?_)
      exact pow_ne_zero 2 (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
    refine hw.mul ?_
    exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hHk : (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2)
      = fun p : ℝ × ℝ =>
          (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i h p.1 p.2
              * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
            + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k
                then (Work.Spaces.mixed j i h p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2
                else 0 := by
    funext p; rfl
  rw [hHk]
  refine ContinuousOn.add ?_ ?_
  · refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i hi => ?_)
    exact (((hz i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).mul
      Work.FTS.EllipticEst.continuousOn_wdivsin_Q0)).pow 2
  · refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i hi =>
      continuousOn_finsetSum (Finset.range (k + 1)) (fun j hj => ?_))
    split_ifs with hc
    · exact (((hm j i hc.2).mul hWt)).pow 2
    · exact continuousOn_const

end Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.dzIter_w_mean_le6_cd6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Finite-order calculus on an open set -/

/-- `D_z = z ∂_z` costs one order of differentiability. -/
theorem contDiffOn_uncurry_Dz_le {f : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {n : ℕ}
    (h : ContDiffOn ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry f) V) :
    ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.Dz f)) V := by
  have hpz := Work.FTS.GalBasis.Xmb.contDiffOn_uncurry_pz_le hV (n := n) h
  have hfun : Function.uncurry (Work.Spaces.Dz f)
      = fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz f) p := by
    funext p
    rcases p with ⟨z, θ⟩
    rfl
  rw [hfun]
  exact contDiffOn_fst.mul hpz

/-- The iterated curvilinear radial derivative `D_z^i` costs `i` orders of differentiability. -/
theorem contDiffOn_uncurry_DzIter_le {f : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {N : ℕ}
    (h : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) (Function.uncurry f) V) :
    ∀ i k : ℕ, i + k ≤ N →
      ContDiffOn ℝ ((k : ℕ) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.DzIter i f)) V := by
  intro i
  induction i with
  | zero =>
      intro k hk
      simpa using h.of_le (Nat.cast_le.mpr (show k ≤ N by omega))
  | succ i ih =>
      intro k hik
      have h2 : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞)
          (Function.uncurry (Work.Spaces.DzIter i f)) V := ih (k + 1) (by omega)
      simpa only [Work.Spaces.DzIter_succ] using contDiffOn_uncurry_Dz_le hV h2

/-- The angular slice of a function that is `C^n` on a product of sets is `C^n` on the second
factor. -/
theorem contDiffOn_slice_snd_of_uncurry {f : ℝ → ℝ → ℝ} {s t : Set ℝ} {n : ℕ}
    (h : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (Function.uncurry f) (s ×ˢ t)) {z : ℝ}
    (hz : z ∈ s) : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (fun θ => f z θ) t := by
  have hcomp := h.comp ((contDiffOn_const (c := z)).prodMk contDiffOn_id)
    (fun θ hθ => ⟨hz, hθ⟩)
  exact hcomp.congr (fun θ _ => rfl)

/-- The angular slice of a function that is `C^n` at a point of an open set is `C^n` there. -/
theorem contDiffAt_slice_snd_of_uncurry {f : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {n : ℕ} (h : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (Function.uncurry f) V) {z θ : ℝ}
    (hzθ : (z, θ) ∈ V) : ContDiffAt ℝ ((n : ℕ) : WithTop ℕ∞) (fun θ' => f z θ') θ := by
  have hc : ContDiffAt ℝ ((n : ℕ) : WithTop ℕ∞) (Function.uncurry f) (z, θ) :=
    h.contDiffAt (hV.mem_nhds hzθ)
  have hlin : ContDiffAt ℝ ((n : ℕ) : WithTop ℕ∞) (fun θ' : ℝ => (z, θ')) θ := by fun_prop
  simpa only [Function.comp_def, Function.uncurry] using hc.comp θ hlin

/-- **Differentiability of the angular slice.**  The slice `θ ↦ f z θ` of a function that is
`C¹` on the product `s ×ˢ (0,π/2)` is differentiable on `(0,π/2)`. -/
theorem hasDerivAt_slice_snd_Ioo {f : ℝ → ℝ → ℝ} {s : Set ℝ}
    (h : ContDiffOn ℝ ((1 : ℕ) : WithTop ℕ∞) (Function.uncurry f) (s ×ˢ Set.Ioo (0 : ℝ) (π / 2)))
    {z θ : ℝ} (hz : z ∈ s) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    HasDerivAt (fun θ' => f z θ') (deriv (fun θ' => f z θ') θ) θ := by
  have hslice := contDiffOn_slice_snd_of_uncurry (n := 1) h hz
  have hc : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞) (fun θ' => f z θ') θ :=
    hslice.contDiffAt (isOpen_Ioo.mem_nhds hθ)
  exact (hc.differentiableAt (by simp)).hasDerivAt

/-! ## Clairaut with radial iterates at finite order -/

/-- Pointwise Clairaut for `∂_θ` and `D_z = z ∂_z`: at a point where the uncurried `f` is `C²`,
`∂_θ (z ∂_z f) = z ∂_z (∂_θ f)`. -/
private lemma pth_Dz_eq_of_contDiffAt_two {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ)) :
    Work.Spaces.pth (Work.Spaces.Dz f) z θ = Work.Spaces.Dz (Work.Spaces.pth f) z θ := by
  have h1 : Work.Spaces.pth (Work.Spaces.Dz f) z θ
      = z * Work.Spaces.pth (Work.Spaces.pz f) z θ := by
    show deriv (fun θ' => z * Work.Spaces.pz f z θ') θ
      = z * Work.Spaces.pth (Work.Spaces.pz f) z θ
    rw [deriv_const_mul_field]
    rfl
  have h2 : Work.Spaces.Dz (Work.Spaces.pth f) z θ
      = z * Work.Spaces.pz (Work.Spaces.pth f) z θ := rfl
  rw [h1, h2, (Work.Spaces.pz_pth_comm h).symm]

/-- **`∂_θ` commutes with every iterate of `D_z` at finite order.**  On an open set `V` where `g`
is `C^N`, and for `j + 1 ≤ N`, the plain angular derivative `∂_θ` commutes with `D_z^j`:

`∂_θ (D_z^j g) = D_z^j (∂_θ g)` on `V`.

(`D_z^j g` is `C²` as soon as `j + 2 ≤ N`, which is what Clairaut needs at the induction step;
the induction hypothesis is then used at level `j`, requiring only `j + 1 ≤ N`.) -/
theorem pth_DzIter_eqOn_of_contDiffOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {g : ℝ → ℝ → ℝ}
    {N : ℕ} (hg : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) (Function.uncurry g) V) :
    ∀ j : ℕ, j + 1 ≤ N →
      Set.EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter j g)))
        (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.pth g))) V := by
  intro j
  induction j with
  | zero => intro _ y _; rfl
  | succ j ih =>
      intro hj y hy
      obtain ⟨a, b⟩ := y
      have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DzIter j g)) (a, b) :=
        (contDiffOn_uncurry_DzIter_le hV hg j 2 (by omega)).contDiffAt (hV.mem_nhds hy)
      have hstep : Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DzIter j g)) a b
          = Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter j g)) a b :=
        pth_Dz_eq_of_contDiffAt_two hcd
      show Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DzIter j g)) a b
          = Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.pth g)) a b
      rw [hstep]
      show a * Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.DzIter j g)) a b
          = a * Work.Spaces.pz (Work.Spaces.DzIter j (Work.Spaces.pth g)) a b
      rw [Work.Spaces.pz_congr_of_isOpen hV (ih (by omega)) hy]

/-! ## The mixed slot is the angular derivative of the radial iterate -/

/-- **The mixed slot identity at finite order.**  For `g` of class `C⁶` on the open quadrant
`Q0` and `d ≤ 5`, on `Q0`:

`D_z^d D_θ g = sin(2θ) · ∂_θ(D_z^d g)`. -/
theorem mixed_one_eq_sin_pth_cd6 {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0) {d : ℕ} (hd : d ≤ 5)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.mixed d 1 g z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter d g) z θ := by
  have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hV := pth_DzIter_eqOn_of_contDiffOn (V := Work.FTS.EllipticEst.Q0) (N := 6)
    Work.FTS.EllipticEst.isOpen_Q0 hg d (by omega) hQ
  have hVs : Work.Spaces.DzIter d (Work.Spaces.pth g) z θ
      = Work.Spaces.pth (Work.Spaces.DzIter d g) z θ := by
    simpa only [Function.uncurry] using hV.symm
  calc Work.Spaces.mixed d 1 g z θ
      = Work.Spaces.DzIter d (Work.Spaces.Dth g) z θ := rfl
    _ = Work.Spaces.DzIter d (fun z θ => Real.sin (2 * θ) * Work.Spaces.pth g z θ) z θ := rfl
    _ = Real.sin (2 * θ) * Work.Spaces.DzIter d (Work.Spaces.pth g) z θ :=
        Work.FTS.TransportS.SupDzAux.sda_DzIter_const_mul_th (fun θ' => Real.sin (2 * θ'))
          (Work.Spaces.pth g) d z θ
    _ = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter d g) z θ := by rw [hVs]

/-- **The weight identity for the angular derivative at finite order:** the square of the angular
derivative of the radial iterate, against the weight `sin(2σ)^{2-γ}`, is the square of the mixed
slot against `sin(2σ)^{-γ}`. -/
theorem deriv_mixed_weight_cd6 {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0) {d : ℕ} (hd : d ≤ 5)
    {z σ : ℝ} (hz : 0 < z) (hσ : σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
      = (Work.Spaces.mixed d 1 g z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
  have hsin : 0 < Real.sin (2 * σ) := Work.FTS.OpenPkg.ProdOpen.sin_two_pos hσ
  have hshift : Work.Spaces.mixed d 1 g z σ
      = Real.sin (2 * σ) * Work.Spaces.pth (Work.Spaces.DzIter d g) z σ :=
    mixed_one_eq_sin_pth_cd6 hg hd hz hσ
  have hsp : Real.sin (2 * σ) ^ (2 - Work.Spaces.gam α)
      = (Real.sin (2 * σ)) ^ 2 * Real.sin (2 * σ) ^ (-(Work.Spaces.gam α)) := by
    rw [show (2 : ℝ) - Work.Spaces.gam α = 2 + (-(Work.Spaces.gam α)) by ring,
      Real.rpow_add hsin, Real.rpow_two]
  have hd0 : deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') σ
      = Work.Spaces.pth (Work.Spaces.DzIter d g) z σ := rfl
  rw [hd0, hshift, mul_pow, hsp]
  ring

/-! ## The mean-term bound -/

theorem dzIter_w_mean_le6_cd6 : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (g : ℝ → ℝ → ℝ) (d : ℕ), 0 < α → α ≤ 1 →
      ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem α 6 g → d ≤ 5 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
        ≤ C * ((Work.Spaces.w z) ^ 2
              * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
            + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.OpenPkg.ProdOpen.sob_theta_mean
  refine ⟨C, hCpos, ?_⟩
  intro α g d hα hα1 hg hmem hd z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hZpos : 0 < Work.Spaces.w z := Work.FTS.OpenPkg.ProdOpen.w_pos_of_pos hz
  have hZne : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 hZpos.ne'
  -- ### the angular slice `σ ↦ D_z^d g (z,σ)` is `C¹` on the open interval
  have hDz1 : ContDiffOn ℝ ((1 : ℕ) : WithTop ℕ∞)
      (Function.uncurry (Work.Spaces.DzIter d g)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_uncurry_DzIter_le (N := 6) Work.FTS.EllipticEst.isOpen_Q0 hg d 1 (by omega)
  have hslice1 : ContDiffOn ℝ ((1 : ℕ) : WithTop ℕ∞)
      (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    contDiffOn_slice_snd_of_uncurry (n := 1) hDz1 hz
  -- ### the mixed slot `D_z^d D_θ g` is continuous along the slice
  have hpthg : ContDiffOn ℝ ((5 : ℕ) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pth g))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.GalBasis.Xmb.contDiffOn_uncurry_pth_le Work.FTS.EllipticEst.isOpen_Q0 (n := 5) hg
  have hDzP0 : ContDiffOn ℝ ((0 : ℕ) : WithTop ℕ∞)
      (Function.uncurry (Work.Spaces.DzIter d (Work.Spaces.pth g))) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_uncurry_DzIter_le (N := 5) Work.FTS.EllipticEst.isOpen_Q0 hpthg d 0 (by omega)
  have hsliceP : ContinuousOn (fun σ' : ℝ => Work.Spaces.DzIter d (Work.Spaces.pth g) z σ')
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (contDiffOn_slice_snd_of_uncurry (n := 0) hDzP0 hz).continuousOn
  have hpoint : ∀ σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') σ
        = Work.Spaces.DzIter d (Work.Spaces.pth g) z σ := by
    intro σ hσ
    have hQ : (z, σ) ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hσ.1, hσ.2⟩
    have h := pth_DzIter_eqOn_of_contDiffOn (V := Work.FTS.EllipticEst.Q0) (N := 6)
      Work.FTS.EllipticEst.isOpen_Q0 hg d (by omega) hQ
    simpa only [Function.uncurry, Work.Spaces.pth] using h
  have hder : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun σ' : ℝ => Work.Spaces.DzIter d g z σ')
        (deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') x) x :=
    fun x hx => hasDerivAt_slice_snd_Ioo hDz1 hz hx
  have hcont : ContinuousOn (deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ'))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hsliceP.congr fun σ hσ => hpoint σ hσ
  -- ### the two integrability hypotheses of the angular inequality
  have hint1 : IntegrableOn (fun σ : ℝ => (Work.Spaces.DzIter d g z σ) ^ 2)
      Work.Spaces.Iθ := by
    refine Integrable.mono' (hmem.1 z hz.le)
      (Work.H2.T1Q.aesm_Iθ_of_continuousOn (g := fun σ : ℝ =>
        (Work.Spaces.DzIter d g z σ) ^ 2) (hslice1.continuousOn.pow 2)) ?_
    filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ hσ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [Work.Spaces.mixed_zero_right] using
      Work.FTS.StrongPersist.N6.mixed_sq_le_HkIntegrand6 α hα g d 0 (by omega) hz hσ.1 hσ.2
  have hsinC : ContinuousOn (fun σ : ℝ => (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn.rpow_const
      (fun σ hσ => Or.inl (ne_of_gt (Work.FTS.OpenPkg.ProdOpen.sin_two_pos hσ)))
  have hderivC : ContinuousOn (fun σ : ℝ =>
      (deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hcont.pow 2).mul hsinC
  have hint2 : IntegrableOn (fun σ : ℝ =>
      (deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
    refine Integrable.mono' ((hmem.1 z hz.le).const_mul (((Work.Spaces.w z) ^ 2)⁻¹))
      (Work.H2.T1Q.aesm_Iθ_of_continuousOn (g := fun σ : ℝ =>
        (deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') σ) ^ 2
          * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) hderivC) ?_
    filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ hσ
    have hsin : 0 < Real.sin (2 * σ) := Work.FTS.OpenPkg.ProdOpen.sin_two_pos hσ
    have hmw := deriv_mixed_weight_cd6 (α := α) hg hd hz hσ
    have hnn : 0 ≤ (deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _)
    rw [Real.norm_of_nonneg hnn, hmw]
    have hX : (Work.Spaces.mixed d 1 g z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        = (((Work.Spaces.w z) ^ 2)⁻¹) * ((Work.Spaces.w z) ^ 2
            * ((Work.Spaces.mixed d 1 g z σ) ^ 2
              * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)))) := by
      rw [← mul_assoc, inv_mul_cancel₀ hZne, one_mul]
    rw [hX]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (sq_nonneg _))
    have hkey : (Work.Spaces.w z) ^ 2 * ((Work.Spaces.mixed d 1 g z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)))
        = (Work.Spaces.mixed d 1 g z σ * Work.Spaces.Wt α z σ) ^ 2 := by
      rw [mul_pow, Work.H2.T1Q.Wt_sq_eq α z σ hsin]
      ring
    rw [hkey]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α 6 g z σ 1 d (by norm_num) (by omega)
  -- ### the angular Hardy inequality with the mean term
  have hmain := hC α (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') θ hα hα1 hθ hder hcont
    hint1 hint2
  -- ### the derivative term is exactly `Aang α g d z`, up to the radial weight
  have hAang : (Work.Spaces.w z) ^ 2 * (∫ σ in Work.Spaces.Iθ,
        (deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') σ) ^ 2
          * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
      = Work.FTS.H2.WPQ.Aang α g d z := by
    have hstep : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
          ((deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') σ) ^ 2
            * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)))
        = (Work.Spaces.w z) ^ 2 * (∫ σ in Work.Spaces.Iθ,
            (deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') σ) ^ 2
              * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) :=
      MeasureTheory.integral_const_mul (μ := volume.restrict Work.Spaces.Iθ) _ _
    rw [← hstep, Work.FTS.H2.WPQ.Aang]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ hσ
    have hsin : 0 < Real.sin (2 * σ) := Work.FTS.OpenPkg.ProdOpen.sin_two_pos hσ
    rw [deriv_mixed_weight_cd6 (α := α) hg hd hz hσ, mul_pow,
      Work.H2.T1Q.Wt_sq_eq α z σ hsin]
    ring
  -- ### assembly
  calc (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter d g z θ) ^ 2 := by ring
    _ ≤ (Work.Spaces.w z) ^ 2 * (C * ((∫ σ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter d g z σ) ^ 2)
          + (Work.Spaces.gam α - 1)⁻¹ * (∫ σ in Work.Spaces.Iθ,
              (deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') σ) ^ 2
                * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)))) :=
        mul_le_mul_of_nonneg_left hmain (sq_nonneg _)
    _ = C * ((Work.Spaces.w z) ^ 2 * (∫ σ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter d g z σ) ^ 2)
          + (Work.Spaces.gam α - 1)⁻¹ * ((Work.Spaces.w z) ^ 2
              * (∫ σ in Work.Spaces.Iθ,
                  (deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') σ) ^ 2
                    * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)))) := by ring
    _ = C * ((Work.Spaces.w z) ^ 2 * (∫ σ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter d g z σ) ^ 2)
          + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z) := by rw [hAang]

end Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Aux.L12f_slot_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L3Aux

open MeasureTheory Set Filter
open scoped Real Topology

/-- The target: the `q`-th pure `D_z`-slot of the radial function `L₁₂(g)` is in
`L²(w² dz)` and dominated by the weighted `ℋ⁴`-norm of `g`.

Route: `L₁₂(g)(z) = -∫_z^∞ Qang g 0 (s)/s ds` is radial, so `D_z^q L₁₂(g) = DzdIter q L₁₂(g)`
(`Work.Elliptic.DzIter_rad`) and the open-quadrant `L₁₂`-bundle
(`Work.FTS.OpenPkg.l12_open_bundle`) gives

* `DzdIter (k+1) L₁₂(g) = -Qang g k` on `z > 0` for `k ≤ 3`;
* the `k = 0` slot with the weighted Hardy estimate `∫ L₁₂(g)² w² ≤ 107 ∫ (Qang g 0)² w²`;

while `Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open` bounds every angular moment
`∫ (Qang g i)² w² ≤ (∫_θ Kθ²) · HkSq α 4 g` for `i ≤ 4`.  The constant is
`107·(1 + ∫_θ Kθ²)`. -/
theorem L12f_slot_le : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ g : ℝ → ℝ → ℝ,
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
      Work.Construction.L12 g 0 = 0 →
      ∀ q ≤ 4, MeasureTheory.IntegrableOn
          (fun z => (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 g z) z 0) ^ 2
            * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
        (∫ z in Work.Spaces.Iz,
            (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 g z) z 0) ^ 2
              * (Work.Spaces.w z) ^ 2) ≤ C * Work.Spaces.HkSq α 4 g := by
  refine ⟨107 * (1 + ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2), ?_, ?_⟩
  · have h : (0:ℝ) ≤ ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 :=
      integral_nonneg (fun θ => sq_nonneg _)
    nlinarith
  · intro α hα hα1 g hO hmem h0 q hq
    obtain ⟨hgen, hInt0, hbnd0⟩ :=
      Work.FTS.OpenPkg.l12_open_bundle α g hα hα1 hO hmem h0
    have hK2nn : (0:ℝ) ≤ ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 :=
      integral_nonneg (fun θ => sq_nonneg _)
    have hHnn : (0:ℝ) ≤ Work.Spaces.HkSq α 4 g := Work.Spaces.HkSq_nonneg α 4 g
    cases q with
    | zero =>
      have hfun : (fun z => (Work.Spaces.DzIter 0
            (fun z _ => Work.Construction.L12 g z) z 0) ^ 2 * (Work.Spaces.w z) ^ 2)
          = fun z => (Work.Elliptic.L12 g z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
        funext z
        simp only [Work.Spaces.DzIter_zero]
        rfl
      rw [hfun]
      obtain ⟨-, hQbnd⟩ := Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open
        (α := α) (g := g) hα hα1 hO hmem (i := 0) (by norm_num)
      exact ⟨hInt0, by nlinarith [hbnd0, hQbnd, hK2nn, hHnn]⟩
    | succ k =>
      have hk3 : k ≤ 3 := by omega
      obtain ⟨hQint, hQbnd⟩ := Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open
        (α := α) (g := g) hα hα1 hO hmem (i := k) (by omega)
      have haeeq : (fun z => (Work.Spaces.DzIter (k+1)
            (fun z _ => Work.Construction.L12 g z) z 0) ^ 2 * (Work.Spaces.w z) ^ 2)
          =ᵐ[volume.restrict Work.Spaces.Iz]
          (fun z => (Work.Elliptic.Qang g k z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
        rw [← Work.Elliptic.restrict_Ioi_eq_restrict_Iz]
        refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
        show Work.Spaces.DzIter (k+1) (fun z _ => Work.Construction.L12 g z) z 0 ^ 2
              * (Work.Spaces.w z) ^ 2
            = (Work.Elliptic.Qang g k z) ^ 2 * (Work.Spaces.w z) ^ 2
        have h1 : Work.Spaces.DzIter (k+1) (fun z _ => Work.Construction.L12 g z) z 0
            = Work.Elliptic.DzdIter (k+1) (fun z => Work.Construction.L12 g z) z :=
          Work.Elliptic.DzIter_rad (fun z => Work.Construction.L12 g z) (k+1) z 0
        have h2 : Work.Elliptic.DzdIter (k+1) (fun z => Work.Construction.L12 g z) z
            = - Work.Elliptic.Qang g k z := hgen k hk3 z hz
        rw [h1, h2]
        ring
      refine ⟨hQint.congr haeeq.symm, ?_⟩
      rw [MeasureTheory.integral_congr_ae (μ := volume.restrict Work.Spaces.Iz) haeeq]
      nlinarith [hQbnd, hK2nn, hHnn]

end Work.FTS.StrongPersist.L3Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L6Aux.PhiZopBound6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

noncomputable section

open scoped Real Topology
open Set Filter Polynomial

namespace Work.FTS.StrongPersist.L6Aux

open Work.FTS.CoercivityFix.E2Bound (zchart gpoly Tmul)

/-- The linear chart polynomial `(3/2)(1 - X)`, whose chart evaluation is `z ↦ 3/(1+z)`. -/
def P3 : Polynomial ℝ := Polynomial.C (3 / 2) * (1 - Polynomial.X)

/-- The sum of the absolute values of the coefficients of a real polynomial (all the
coefficients, not only the generic ones below the degree). -/
def coeffSum (P : Polynomial ℝ) : ℝ :=
  ∑ k ∈ Finset.range (P.natDegree + 1), |P.coeff k|

lemma coeffSum_nonneg (P : Polynomial ℝ) : 0 ≤ coeffSum P :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Evaluating a real polynomial at a point of `[-1,1]` is bounded by the sum of the
absolute values of its coefficients. -/
lemma abs_eval_le_coeffSum (P : Polynomial ℝ) {t : ℝ} (ht : |t| ≤ 1) :
    |P.eval t| ≤ coeffSum P :=
  Work.FTS.CoercivityFix.E2Bound.SlotMul.Polynomial_abs_eval_le_sum_abs_coeff P ht

/-- The chart evaluation of `P3` is the profile `3/(1+z)` on `(0,∞)`. -/
lemma gpoly_P3 {z : ℝ} (hz : 0 < z) : gpoly P3 z = 3 / (1 + z) := by
  have hz1 : z + 1 ≠ 0 := by positivity
  rw [Work.FTS.CoercivityFix.E2Bound.gpoly_apply]
  simp only [P3, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_X, Polynomial.eval_C, Work.FTS.CoercivityFix.E2Bound.zchart_apply]
  field_simp
  ring

/-- The profile `z ↦ 3/(1+z)` agrees with the chart evaluation of `P3` on all of `(0,∞)`,
which is what `Zop_iterate_eqOn_of_eqOn` needs to transport the `Zop`-iterates. -/
lemma eqOn_three_div_gpoly :
    Set.EqOn (fun z : ℝ => 3 / (1 + z)) (gpoly P3) (Set.Ioi 0) :=
  fun _ hz => (gpoly_P3 hz).symm

/-- Every `Zop`-iterate of order `≥ 1` vanishes at `z = 0`, since `Zop u = z ↦ z·u'(z)`. -/
lemma Zop_iterate_zero_of_pos (g : ℝ → ℝ) {b : ℕ} (hb : 1 ≤ b) :
    Work.Spaces.Zop^[b] g 0 = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show b ≠ 0 by omega)
  have h : Work.Spaces.Zop^[k + 1] g = Work.Spaces.Zop (Work.Spaces.Zop^[k] g) :=
    Function.iterate_succ_apply' Work.Spaces.Zop k g
  rw [h]
  simp [Work.Spaces.Zop]

/-- **The `Zop`-iterates of `z ↦ 3/(1+z)` up to order six are uniformly bounded.** -/
theorem PhiZopBound6 : ∃ K : ℝ, 0 < K ∧ ∀ b ≤ 6, ∀ z : ℝ, 0 ≤ z →
    |Work.Spaces.Zop^[b] (fun z : ℝ => 3 / (1 + z)) z| ≤ K := by
  refine ⟨max 3 (∑ b ∈ Finset.range 7, coeffSum (Tmul^[b] P3)) + 1, by positivity, ?_⟩
  intro b hb z hz
  have hb7 : b ∈ Finset.range 7 := Finset.mem_range.mpr (Nat.lt_succ_of_le hb)
  have hle : coeffSum (Tmul^[b] P3)
      ≤ ∑ b' ∈ Finset.range 7, coeffSum (Tmul^[b'] P3) :=
    Finset.single_le_sum (f := fun b' => coeffSum (Tmul^[b'] P3))
      (fun i _ => coeffSum_nonneg _) hb7
  have hBig : ∑ b' ∈ Finset.range 7, coeffSum (Tmul^[b'] P3)
      ≤ max 3 (∑ b' ∈ Finset.range 7, coeffSum (Tmul^[b'] P3)) + 1 := by
    have := le_max_right (3 : ℝ) (∑ b' ∈ Finset.range 7, coeffSum (Tmul^[b'] P3))
    linarith
  have h3 : (3 : ℝ) ≤ max 3 (∑ b' ∈ Finset.range 7, coeffSum (Tmul^[b'] P3)) :=
    le_max_left 3 _
  rcases eq_or_lt_of_le hz with hz0 | hzpos
  · -- `z = 0`: order `0` contributes `3`, orders `≥ 1` contribute `0`
    subst hz0
    rcases Nat.eq_zero_or_pos b with hb0 | hbpos
    · subst hb0
      have h0 : |Work.Spaces.Zop^[0] (fun z : ℝ => 3 / (1 + z)) (0 : ℝ)| = 3 := by
        rw [Function.iterate_zero_apply]
        norm_num
      rw [h0]
      linarith
    · rw [Zop_iterate_zero_of_pos (fun z : ℝ => 3 / (1 + z)) hbpos, abs_zero]
      linarith
  · -- `z > 0`: chart the iterate and bound it by its coefficient sum
    have h1 : Work.Spaces.Zop^[b] (fun z : ℝ => 3 / (1 + z)) z
        = (Tmul^[b] P3).eval (zchart z) := by
      rw [Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_iterate_eqOn_of_eqOn b isOpen_Ioi
            eqOn_three_div_gpoly hzpos,
          Work.FTS.CoercivityFix.E2Bound.SlotMul.Zop_gpoly_iterate P3 b z hzpos]
      rfl
    rw [h1]
    have h2 : |(Tmul^[b] P3).eval (zchart z)| ≤ coeffSum (Tmul^[b] P3) :=
      abs_eval_le_coeffSum _ (Work.FTS.CoercivityFix.E2Bound.abs_zchart_le_one hzpos)
    linarith

end Work.FTS.StrongPersist.L6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.SixAux.SliceSup6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.SixAux

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## §1. The pointwise domination of the two slice integrands -/


/-! ## §2. Integrability of the two angular slices -/

/-- The `θ`-slice of the pure `D_z`-slot `D_z^bf`, `b ≤ 6`, is integrable, given `HkMem α 6 f`. -/
theorem integrableOn_sq6 {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 6 f) {b : ℕ}
    (hb : b ≤ 6) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (Work.Spaces.DzIter b f z θ) ^ 2) Work.Spaces.Iθ := by
  have hzIz : z ∈ Work.Spaces.Iz := by
    simp only [Work.Spaces.Iz, Set.mem_Ici]; linarith
  have hkey : Integrable (fun θ => (Work.Spaces.DzIter b f z θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    refine Integrable.mono' ((hmem.1 z hzIz).mono_set Set.Ioo_subset_Icc_self)
      ((((hF.DzIter b).curry_θ hz).continuousOn.aestronglyMeasurable
        measurableSet_Ioo).pow 2) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Work.FTS.StrongPersist.N6.mixed_sq_le_HkIntegrand6 α hα f b 0 (by omega) hz hθ.1 hθ.2
  show Integrable (fun θ => (Work.Spaces.DzIter b f z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)
  rw [Work.FTS.TransportS.SlotT2.supOpen_restrict_Iθ]
  exact hkey

/-- The weighted angular slice `(∂_θD_z^bf z ·)² sin(2·)^{2-γ}`, `b ≤ 5`, is integrable, given
`HkMem α 6 f`. -/
theorem integrableOn_pth_weight6 {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 6 f) {b : ℕ}
    (hb : b ≤ 5) {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun θ => (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
  have hzIz : z ∈ Work.Spaces.Iz := by
    simp only [Work.Spaces.Iz, Set.mem_Ici]; linarith
  have hw2 : (Work.Spaces.w z) ^ 2 ≠ 0 := Work.FTS.TransportS.SlotT2.supOpen_w_sq_ne_zero hz
  have hsinpos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hderiv_cont : ContinuousOn
      (fun θ => deriv (fun θ' => Work.Spaces.DzIter b f z θ') θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (((hF.DzIter b).curry_θ hz).of_le
      (by simp [Work.Stability.smoothOrder])).continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  have hsincont : ContinuousOn (fun θ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun θ hθ => Or.inl (ne_of_gt (hsinpos θ hθ)))
  have hkey : Integrable
      (fun θ => (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    refine Integrable.mono'
      (((hmem.1 z hzIz).mono_set Set.Ioo_subset_Icc_self).const_mul
        ((Work.Spaces.w z) ^ 2)⁻¹) ?_ ?_
    · have hcont : ContinuousOn
          (fun θ => (deriv (fun θ' => Work.Spaces.DzIter b f z θ') θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        (hderiv_cont.pow 2).mul hsincont
      exact hcont.aestronglyMeasurable measurableSet_Ioo
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_of_nonneg
        (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt (hsinpos θ hθ)) _))]
      calc (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          = ((Work.Spaces.w z) ^ 2)⁻¹
              * (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
            rw [← Work.FTS.TransportS.SlotT2.supOpen_pth_weight hF hα hα1 b hz hθ]
            rw [show ((Work.Spaces.w z) ^ 2)⁻¹
                  * ((Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
                      * (Work.Spaces.w z) ^ 2
                      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
                = ((Work.Spaces.w z) ^ 2)⁻¹ * ((Work.Spaces.w z) ^ 2)
                    * ((Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
                        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) from by ring]
            rw [inv_mul_cancel₀ hw2, one_mul]
        _ ≤ ((Work.Spaces.w z) ^ 2)⁻¹ * Work.Spaces.HkIntegrand α 6 f z θ :=
            mul_le_mul_of_nonneg_left
              (Work.Spaces.sq_le_HkIntegrand_mixed α 6 f z θ 1 b le_rfl (by omega))
              (inv_nonneg.mpr (sq_nonneg _))
  show Integrable (fun θ => (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)
  rw [Work.FTS.TransportS.SlotT2.supOpen_restrict_Iθ]
  exact hkey

/-! ## §3. The two block estimates: the slice integrals at the same radius -/



/-! ## §4. The first rung: the slicewise bound at level six -/


end

end Work.FTS.StrongPersist.N6Trans.SixAux
end
-- ===== merged: Submission.Work.FTS_RegExport.C4.HkSqSwap_C4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.C4

open MeasureTheory Set Filter
open scoped Real Topology

theorem HkSqSwap_C4 {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) :
    (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ
        = Work.Spaces.HkSq α 4 f) ∧
      MeasureTheory.Integrable
        (fun σ : ℝ => ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
      (∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        MeasureTheory.IntegrableOn (fun s => Work.Spaces.HkIntegrand α 4 f s σ)
          Work.Spaces.Iz) := by
  -- Nonnegativity of the integrand.
  have hnn : ∀ z θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  -- A.e. strong measurability of the uncurried integrand: the integrand of a `C^4` datum is
  -- continuous on the open quadrant `Q0`.
  have haesm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry fun z θ : ℝ => Work.Spaces.HkIntegrand α 4 f z θ)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      (Work.FTS.StrongEps.continuousOn_HkIntegrand_fin α 4 f hF)
  -- The angular slices are integrable, for every `z ∈ Iz` (hence a.e.).
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 f z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hmem.1 z hz)
  -- ... and the `z`-integral of the angular slices is integrable.
  have houter : MeasureTheory.Integrable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hmem.2
  obtain ⟨h1, h2, h3⟩ :=
    Work.FTS.H2.swap_iterated_integral_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ) hnn haesm hslice houter
  refine ⟨?_, h2, h3⟩
  rw [Work.Spaces.HkSq]
  exact h1

end Work.FTS_RegExport.C4
end
-- ===== merged: Submission.Work.FTS_RegExport.C4.ae_integrableOn_mixed_sq_w_C4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.C4

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Elementary a.e. and continuity facts -/

/-- Almost every angle of `Iθ = [0,π/2]` is interior: `Iθ` and `(0,π/2)` differ by the two
endpoints, a null set. -/
theorem ae_mem_Ioo_of_Iθ :
    ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), σ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  have hmeas : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
    refine MeasureTheory.Measure.restrict_congr_set ?_
    exact (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := π / 2)).symm
  rw [hmeas]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- The square of the radial weight `w` is continuous away from `0`. -/
theorem continuousOn_w_sq :
    ContinuousOn (fun s : ℝ => (Work.Spaces.w s) ^ 2) (Set.Ioi (0 : ℝ)) := by
  have hnum : ContinuousOn (fun s : ℝ => ((1 + s) ^ 2) ^ 2) (Set.Ioi (0 : ℝ)) :=
    ((continuousOn_const.add continuousOn_id).pow 2).pow 2
  have hden : ContinuousOn (fun s : ℝ => (s ^ 2) ^ 2) (Set.Ioi (0 : ℝ)) :=
    (continuousOn_id.pow 2).pow 2
  refine (hnum.div hden (fun z hz => ?_)).congr (fun z _ => ?_)
  · exact pow_ne_zero 2 (pow_ne_zero 2 (ne_of_gt hz))
  · show (Work.Spaces.w z) ^ 2 = ((1 + z) ^ 2) ^ 2 / (z ^ 2) ^ 2
    rw [Work.Spaces.w, div_pow]

/-! ## A.e. slice integrability of the `ℋ⁴`-integrand -/

/-- **A.e. radial-slice integrability of the `ℋ⁴`-integrand, for a `C⁴` datum.**

For `f` of class `C⁴` on the open quadrant and honestly in `ℋ⁴`, the radial slice
`s ↦ HkIntegrand α 4 f s σ` is integrable on `Iz` for almost every angle `σ ∈ Iθ`.

This is the third conclusion of `HkSqSwap_C4` (the `C⁴`-analogue of `HkSqSwap`), extracted so
that it can be used without the two integral identities of that statement.  The proof is the
Tonelli engine `Work.FTS.H2.swap_iterated_integral_of_nonneg`, whose three inputs are
nonnegativity of the integrand, a.e. strong measurability (from continuity on the open
quadrant and the nullity of the boundary of the quadrant) and the two iterated-integral
hypotheses contained in `HkMem`. -/
theorem ae_integrableOn_HkIntegrand_slice_C4 {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) :
    ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun s => Work.Spaces.HkIntegrand α 4 f s σ) Work.Spaces.Iz := by
  have hnn : ∀ z θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  have haesm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry fun z θ : ℝ => Work.Spaces.HkIntegrand α 4 f z θ)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      (Work.FTS.StrongEps.continuousOn_HkIntegrand_fin α 4 f hF)
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 f z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hmem.1 z hz)
  exact (Work.FTS.H2.swap_iterated_integral_of_nonneg
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ) hnn haesm hslice hmem.2).2.2

/-! ## A.e. strong measurability of the weighted mixed square -/

/-- At an interior angle `σ`, the radial function `s ↦ (D_z^jD_θ^if (s,σ))² w(s)²` is a.e.
strongly measurable for `volume.restrict Iz`: the mixed slot is continuous on the open
quadrant, hence its `z`-slice is continuous on `(0,∞)`, and `w²` is continuous there as well;
the excluded point `s = 0` is null. -/
theorem aesm_zslice_mixed_sq_w_C4 {f : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0) (j i : ℕ)
    (hij : i + j ≤ 4) {σ : ℝ} (hσ : σ ∈ Set.Ioo 0 (π / 2)) :
    MeasureTheory.AEStronglyMeasurable
      (fun s => (Work.Spaces.mixed j i f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hmix : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.continuousOn_mixed_of_contDiffOn hF hij
  have hslice : ContinuousOn (fun s : ℝ => Work.Spaces.mixed j i f s σ) (Set.Ioi (0 : ℝ)) :=
    (hmix.comp (continuousOn_id.prodMk continuousOn_const)
      (fun s hs => ⟨hs, hσ⟩)).congr (fun s _ => rfl)
  have hcont : ContinuousOn
      (fun s : ℝ => (Work.Spaces.mixed j i f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
      (Set.Ioi (0 : ℝ)) :=
    (hslice.pow 2).mul continuousOn_w_sq
  rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]
  exact hcont.aestronglyMeasurable measurableSet_Ioi

/-! ## The target -/

theorem ae_integrableOn_mixed_sq_w_C4 {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn
        (fun s => (Work.Spaces.mixed j i f s σ) ^ 2 * (Work.Spaces.w s) ^ 2) Work.Spaces.Iz := by
  filter_upwards [ae_integrableOn_HkIntegrand_slice_C4 hF hmem, ae_mem_Ioo_of_Iθ] with σ hInt hσ
  refine MeasureTheory.Integrable.mono' hInt (aesm_zslice_mixed_sq_w_C4 hF j i hij hσ) ?_
  exact Filter.Eventually.of_forall fun s => by
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact Work.FTS.StrongEps.SupPort.AuxMixSq.mixed_sq_w_le_HkIntegrand hα j i hi hij hσ

end Work.FTS_RegExport.C4
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.L12DzIterTendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT


end Work.FTS_RegExport.RXT
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.dzIter_sum_coef_eqOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Linearity of the radial operator `D_z^j` over a finite sum with `θ`-only coefficients

The operator `D_z = z ∂_z` commutes with a sum whose coefficients do not depend on `z`:
for `F k z θ = F k z θ` and `c k θ` an arbitrary `θ`-dependent coefficient,

  `D_z^j (∑_{k∈s} c k θ · F k z θ) = ∑_{k∈s} c k θ · D_z^j (F k) z θ`  on the open quadrant.

The only smoothness needed is the *finite* order `j + 1 ≤ n` at which the induction step
differentiates the summands (the sibling `Work.FTS.EllSol.VopAux.dzIterSumConstMul` needs `C^∞`,
which is more than the consumers of this file have available).

The proof is the induction on `j`: the induction hypothesis identifies the two level-`j`
functions on the (open) quadrant, `pz_congr_of_isOpen` transfers that identity through `∂_z`,
and `deriv_sum` / `deriv_const_mul_field` differentiate the sum term by term.  The
differentiability of the summand slices is the finite-order statement
`contDiffOn_uncurry_DzIter_fin` proved below: `D_z^a` lowers the differentiability order by `a`.
-/

namespace Work.FTS_RegExport.RXT.Slots.JetCalc

/-- `Work.Spaces.DzIter a` lowers the differentiability order by `a` on an open set: if `G` is
`C^{N+a}` there, then `D_z^a G` is `C^N` there.  (Induction on `a`, the step being the one-order
statement `Work.FTS.StrongEps.contDiffOn_uncurry_Dz_fin`.) -/
private theorem contDiffOn_uncurry_DzIter_fin {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) :
    ∀ (a N : ℕ), ContDiffOn ℝ ((N + a : ℕ) : WithTop ℕ∞) (Function.uncurry G) V →
      ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.DzIter a G)) V := by
  intro a
  induction a with
  | zero => intro N h; simpa using h
  | succ n ih =>
      intro N h
      have h' : ContDiffOn ℝ ((N + 1 + n : ℕ) : WithTop ℕ∞) (Function.uncurry G) V := by
        rw [show N + 1 + n = N + (n + 1) from by omega]; exact h
      have h2 : ContDiffOn ℝ ((N + 1 : ℕ) : WithTop ℕ∞)
          (Function.uncurry (Work.Spaces.DzIter n G)) V := ih (N + 1) h'
      have h3 : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞)
          (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DzIter n G))) V :=
        Work.FTS.StrongEps.contDiffOn_uncurry_Dz_fin hV h2
      simpa [Work.Spaces.DzIter_succ] using h3

theorem dzIter_sum_coef_eqOn {ι : Type*} (s : Finset ι) (c : ι → ℝ → ℝ) (F : ι → ℝ → ℝ → ℝ) (j : ℕ)
    (hF : ∀ k ∈ s, ContDiffOn ℝ j (Function.uncurry (F k)) Work.FTS.EllipticEst.Q0) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j (fun z θ => ∑ k ∈ s, c k θ * F k z θ)))
      (Function.uncurry (fun z θ => ∑ k ∈ s, c k θ * Work.Spaces.DzIter j (F k) z θ))
      Work.FTS.EllipticEst.Q0 := by
  revert hF
  induction j with
  | zero => intro hF p hp; rfl
  | succ j ih =>
      intro hF
      -- the induction hypothesis only needs order `j`, which follows from order `j + 1`
      have hFj : ∀ k ∈ s, ContDiffOn ℝ ((j : ℕ) : WithTop ℕ∞)
          (Function.uncurry (F k)) Work.FTS.EllipticEst.Q0 :=
        fun k hk => (hF k hk).of_le (by norm_num)
      have hEq := ih hFj
      intro p hp
      obtain ⟨z, θ⟩ := p
      have hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := hp
      -- the `z`-slices of the summands are differentiable (only order `j + 1` is used)
      have hdiff : ∀ k ∈ s, DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter j (F k) z' θ) z := by
        intro k hk
        have hsm : ContDiffOn ℝ ((1 : ℕ) : WithTop ℕ∞)
            (Function.uncurry (Work.Spaces.DzIter j (F k))) Work.FTS.EllipticEst.Q0 :=
          contDiffOn_uncurry_DzIter_fin Work.FTS.EllipticEst.isOpen_Q0 j 1 (by
            rw [show (1 + j : ℕ) = j + 1 from by omega]
            exact hF k hk)
        have h1 : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.DzIter j (F k))) (z, θ) :=
          (hsm.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hQ)).differentiableAt
            (by norm_num)
        have h2 : DifferentiableAt ℝ (fun e : ℝ => (e, θ)) z :=
          (hasFDerivAt_prodMk_left z θ).differentiableAt
        have h3 : DifferentiableAt ℝ
            ((Function.uncurry (Work.Spaces.DzIter j (F k))) ∘ (fun e : ℝ => (e, θ))) z :=
          h1.comp z h2
        simpa [Function.comp_def, Function.uncurry] using h3
      -- the two level-`j` functions agree on the open quadrant, hence so do their `z`-derivatives
      have hpz1 : Work.Spaces.pz (Work.Spaces.DzIter j (fun z θ => ∑ k ∈ s, c k θ * F k z θ)) z θ
          = Work.Spaces.pz (fun z θ => ∑ k ∈ s, c k θ * Work.Spaces.DzIter j (F k) z θ) z θ :=
        Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEq hQ
      -- and the `z`-derivative of the sum is the sum of the `z`-derivatives
      have hpz2 : Work.Spaces.pz (fun z θ => ∑ k ∈ s, c k θ * Work.Spaces.DzIter j (F k) z θ) z θ
          = ∑ k ∈ s, c k θ * Work.Spaces.pz (Work.Spaces.DzIter j (F k)) z θ := by
        show deriv (fun z' => ∑ k ∈ s, c k θ * Work.Spaces.DzIter j (F k) z' θ) z = _
        rw [show (fun z' => ∑ k ∈ s, c k θ * Work.Spaces.DzIter j (F k) z' θ)
              = ∑ k ∈ s, (fun z' => c k θ * Work.Spaces.DzIter j (F k) z' θ) from by
            funext z'; rw [Finset.sum_apply]]
        rw [deriv_sum (fun k hk => (hdiff k hk).const_mul (c k θ))]
        exact Finset.sum_congr rfl fun k hk => deriv_const_mul_field (c k θ)
      show Work.Spaces.Dz (Work.Spaces.DzIter j (fun z θ => ∑ k ∈ s, c k θ * F k z θ)) z θ
          = ∑ k ∈ s, c k θ * Work.Spaces.DzIter (j + 1) (F k) z θ
      rw [show Work.Spaces.Dz (Work.Spaces.DzIter j (fun z θ => ∑ k ∈ s, c k θ * F k z θ)) z θ
            = z * Work.Spaces.pz (Work.Spaces.DzIter j (fun z θ => ∑ k ∈ s, c k θ * F k z θ)) z θ
            from rfl,
        hpz1, hpz2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [show Work.Spaces.DzIter (j + 1) (F k) z θ
            = z * Work.Spaces.pz (Work.Spaces.DzIter j (F k)) z θ from rfl]
      ring

end Work.FTS_RegExport.RXT.Slots.JetCalc
end
-- ===== merged: Submission.Work.FTS_StreamBdry.Inputs.theta_part_aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.Inputs

noncomputable section

open MeasureTheory Set Filter

/-! ## Auxiliary facts about the angular moment `Qang` and the radial operator `DzdIter` -/

/-- `Qang X 0 z = 𝔽K X z`: the two angular moments agree at level `0`. -/
theorem Qang_zero_eq_FK (X : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.Qang X 0 z = Work.Construction.FK X z := by
  rw [Work.Elliptic.Qang, Work.Construction.FK]
  refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  rw [Work.Spaces.DzIter_zero]
  exact mul_comm _ _

/-- `DzdIter (j+1) u = DzdIter j (DzdIter 1 u)`. -/
theorem DzdIter_succ_eq (j : ℕ) (u : ℝ → ℝ) :
    Work.Elliptic.DzdIter (j + 1) u = Work.Elliptic.DzdIter j (Work.Elliptic.DzdIter 1 u) := by
  rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter (j + 1) u,
    Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter j (Work.Elliptic.DzdIter 1 u),
    Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter 1 u,
    Function.iterate_one, Function.iterate_succ_apply]

/-- `DzdIter` commutes with multiplication by a constant. -/
theorem DzdIter_const_mul (j : ℕ) (c : ℝ) (u : ℝ → ℝ) :
    Work.Elliptic.DzdIter j (fun z => c * u z) = fun z => c * Work.Elliptic.DzdIter j u z := by
  rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter j (fun z => c * u z),
    Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter j u,
    Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul]

/-- The radial operator applied to a linear combination of two functions. -/
theorem DzdIter_const_mul_add {c d : ℝ} {u v : ℝ → ℝ} {j : ℕ}
    (hu : ∀ b < j, ∀ z ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (Work.Elliptic.DzdIter b u) z)
    (hv : ∀ b < j, ∀ z ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (Work.Elliptic.DzdIter b v) z)
    {z : ℝ} (hz : 0 < z) :
    Work.Elliptic.DzdIter j (fun w => c * u w + d * v w) z
      = c * Work.Elliptic.DzdIter j u z + d * Work.Elliptic.DzdIter j v z := by
  have hsum : (fun w => c * u w + d * v w) = (fun w => c * u w) + (fun w => d * v w) := rfl
  rw [hsum, Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_add_of_diff j _ _ ?_ ?_ z hz,
    DzdIter_const_mul j c u, DzdIter_const_mul j d v]
  · intro b hb z' hz'
    rw [DzdIter_const_mul b c u]
    exact (hu b hb z' hz').const_mul c
  · intro b hb z' hz'
    rw [DzdIter_const_mul b d v]
    exact (hv b hb z' hz').const_mul d

/-- `Qd` is open. -/
theorem isOpen_Qd : IsOpen Work.Construction.Qd := Work.FTS.EllipticEst.isOpen_Q0

/-- `DzdIter` of a negated function. -/
theorem DzdIter_neg (j : ℕ) (u : ℝ → ℝ) :
    Work.Elliptic.DzdIter j (fun z => -u z) = fun z => -Work.Elliptic.DzdIter j u z := by
  have h : (fun z : ℝ => -u z) = fun z => (-1 : ℝ) * u z := by funext z; ring
  rw [h, DzdIter_const_mul j (-1) u]
  funext z; ring

/-- The derivative of `w ↦ c/(1+w)`. -/
theorem deriv_const_div_one_add (c z : ℝ) (hz : z ≠ -1) :
    deriv (fun w : ℝ => c / (1 + w)) z = -c / (1 + z) ^ 2 := by
  have h1 : HasDerivAt (fun w : ℝ => 1 + w) 1 z := (hasDerivAt_id z).const_add 1
  have h0 : HasDerivAt (fun _ : ℝ => c) 0 z := hasDerivAt_const z c
  have h := h0.div h1 (by intro hc; exact hz (by linarith))
  rw [show deriv (fun w : ℝ => c / (1 + w)) z
    = (0 * (1 + z) - c * 1) / (1 + z) ^ 2 from h.deriv]
  ring

/-- `D_θ` kills the zero function. -/
theorem Dth_zero : Work.Spaces.Dth (0 : ℝ → ℝ → ℝ) = 0 := by
  funext z θ
  show Real.sin (2 * θ) * deriv (fun θ' : ℝ => (0 : ℝ)) θ = 0
  rw [deriv_const]
  ring

/-- `D_z` kills the zero function. -/
theorem Dz_zero : Work.Spaces.Dz (0 : ℝ → ℝ → ℝ) = 0 := by
  funext z θ
  show z * deriv (fun z' : ℝ => (0 : ℝ)) z = 0
  rw [deriv_const]
  ring

/-- `D_θ` kills a function that does not depend on `θ`. -/
theorem Dth_radial (r : ℝ → ℝ) : Work.Spaces.Dth (fun z _ => r z) = 0 := by
  funext z θ
  show Real.sin (2 * θ) * deriv (fun θ' : ℝ => r z) θ = 0
  rw [deriv_const]
  ring

/-- The iterated `D_θ` of a radial function vanishes from order one on. -/
theorem DthIter_radial_eq_zero (r : ℝ → ℝ) : ∀ i : ℕ, 1 ≤ i →
    Work.Spaces.DthIter i (fun z _ => r z) = 0 := by
  intro i hi
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  clear hi
  induction k with
  | zero => simpa using Dth_radial r
  | succ k ih =>
      rw [Work.Spaces.DthIter_succ (k + 1) (fun z _ => r z), ih, Dth_zero]

/-- The iterated `D_z` of the zero function vanishes. -/
theorem DzIter_zero_fun : ∀ j : ℕ, Work.Spaces.DzIter j (0 : ℝ → ℝ → ℝ) = 0 := by
  intro j
  induction j with
  | zero => rfl
  | succ k ih => rw [Work.Spaces.DzIter_succ, ih, Dz_zero]

end

end Work.FTS_StreamBdry.Inputs
end
-- ===== merged: Submission.Work.H2.T1Q.SliceIntQ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.H2.T1Q

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.FTS.H2

/-! ## Elementary integrability helpers -/






/-! ## The main statement -/


end Work.H2.T1Q
end
end
