import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Arctan
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Have
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.Coercivity.HkMem_mono
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.CoercivityFix.Transfer.HkMem_descent_Q0Sm
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zmoll_dDom
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zmoll_ttDom
import Submission.Work.FTS.EllipticEst.AeI1Fts.psiDeriv_layer
import Submission.Work.FTS.EllipticEst.AeI1Fts.psiDeriv_setup
import Submission.Work.FTS.EllipticEst.H2W.Ae.aeSigmaSliceLower
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.TT.ESW.Tk_B_le_chain_uniform
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.interpol_trunc_defs
import Submission.Work.FTS.EllipticEst.remov.SrdFork.EllWeakPos_DzIter_one_shift_fork
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.FinalClock.HkIntegrandMulDthSmooth
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.H2.HQ.BadsummandQ
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.H2.T3Q.Msurv_abs_le_Q
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgEngine
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four
import Submission.Work.FTS.OpenPkg.WProdWin.mslot_le_winf
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.OpenPkg.l12_open_bundle
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.IBPsub.Slots
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.JepsHkMem.continuousOn_Jeps
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongEps.wtZ_shift_le
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Gmaj6
import Submission.Work.FTS.StrongPersist.L3Aux.HkIntegrand_zmul_le
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS.StrongPersist.L3Aux.acoef_gamCoef_slots_le
import Submission.Work.FTS.StrongPersist.L3Aux.bcoefRadBound
import Submission.Work.FTS.StrongPersist.L3Rhs.L3MulDzBackupM
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.QangSq6
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2S
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_EllLimOK.SlotJets.slotPthSliceLe
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.T1Q.SlotPtQ
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H2.T1Q.T1EasyContQ
import Submission.Work.H2.WPQ.hardy_slice_Aang
import Submission.Work.H2W.PsiSlices.shiftedSourcePoleBound
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.H2W.momentChainAe
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.HProductRule_Badsummand
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.aesm_HkIntegrand_quad
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
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
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.FTS.ClassC.RopGen.Trace.mollDom =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.ClassC.RopGen.Trace.mollDom` — the dominations of the four functionals of `Φ`

The statement below is the "domination" ingredient of the trace-class single-function
interpolation estimate: for every datum `G` in the trace class (`TraceClass G`) with integrable
weighted functionals (`FourInts G`) and every pair of mollification parameters `δ, ε ∈ (0,1/2]`,
the doubly-mollified datum `Φ := zmoll G δ ε` has

* `∫ ddIntS Φ ≤ K ∫ ddIntS G`, `∫ ttIntS Φ ≤ K ∫ ttIntS G`, `∫ dIntS Φ ≤ K ∫ dIntS G`
  (the `D_z²`-, `∂_θ²`- and `D_z`-slots) with a constant `K` **uniform** in `G`, `δ`, `ε`;
* `mixIntS Φ`, `ddIntS Φ`, `ttIntS Φ`, `dIntS Φ` integrable on `Iz`.

## Proof

The obstruction to a direct proof is that `zmoll` probes `G` at a whole window of radii
`[z e^{-δ}, z e^{δ}]` and of angles, so the pointwise commutation of `D_z^j` with the angular
mollification fails on a null set; the transfer identity for the *log-radial* mollification is
however exact and is what the estimate is built on.  The argument is assembled here from the
following independently proved components of the `EllPkgAux/MollDom` directory:

* `MollDom.mollMasterUnif` — the two-kernel domination estimate with a constant uniform in
  `F, X, δ, ε`: if `|F z θ| ≤ ∫_t sKer δ (log z - t) (∫_s KJ ε θ s |X (e^t) s| ds) dt` for a.e.
  `z > 0` and all `θ ∈ Iθ`, and the slices of `F` and of `X` are `σ_η`-honest, the `X`-functional
  is `w²`-integrable and `F`, `(t,s) ↦ X (e^t) s` are jointly measurable, then
  `∫_z w² ∫_θ F² σ_η ≤ K ∫_z w² ∫_θ X² σ_η` and the left-hand side is integrable.  (Its proof is
  Jensen/Cauchy–Schwarz for the product kernel `sKer δ (log z - ·) ⊗ KJ ε`, Tonelli, the two
  Schur/weight comparisons (`KJ_schur_ae` from `K5cAux.thWeightCmp`, and `wExpCmp`) and the
  change of variables `z = e^t`.)
* `MollDom.zmoll_ddDom`, `MollDom.zmoll_dDom`, `MollDom.zmoll_ttDom` — the pointwise (a.e. in
  `z`, all `θ ∈ Iθ`) dominations of `D_z²Φ`, `D_zΦ` and `∂_θ²Φ` by the double convolution of the
  corresponding derivative of `G` with the two kernels; these are the *transfer identities* for
  the two mollifications together with the three-piece angular fold `|Kern| ≤ KJ`.
* `MollDom.zmoll_mixIntS_integrable` — the integrability of the mixed functional `mixIntS Φ`.
* `EllPkgAux.mollAdm` — `Φ` is `C^∞` on the half-strip `(0,∞) × (-1, π/2+1)` and vanishes on both
  angular boundary lines; this supplies the smoothness, measurability and `σ_η`-honesty of the
  `Φ`-side of `mollMasterUnif`.

The helpers below extract the `σ_η`-honesty and the joint measurability of the four slot
functions from `mollAdm` (for `Φ`), from `SliceHonestOpen G` and `SmoothOpen G` (for `G`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC.RopGen.Trace

set_option autoImplicit false

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "σθ" => Work.FTS.EllipticEst.thEta
local notation "OStrip" => Work.FTS.EllipticEst.ThetaU.OStrip

/-! ## helpers -/

/-- `1 ≤ w z²` for `z > 0`. -/
lemma one_le_w_sq {z : ℝ} (hz : 0 < z) : 1 ≤ (Work.Spaces.w z) ^ 2 := by
  have hz2 : (0 : ℝ) < z ^ 2 := by positivity
  have h1 : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, one_le_div hz2]
    nlinarith
  calc (1 : ℝ) = 1 ^ 2 := by norm_num
    _ ≤ (Work.Spaces.w z) ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2

/-- `SliceHonestOpen` gives the `σ_η`-honesty of the three right-hand-side slices, by dividing
out the (strictly positive) radial weight. -/
lemma sliceHon_of_sliceHonestOpen {G : ℝ → ℝ → ℝ}
    (h : Work.EllipticEst.Core.i0Aux.SliceHonestOpen G) :
    (∀ z : ℝ, 0 < z → IntegrableOn (fun θ : ℝ =>
        (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 * σθ θ) Iθ) ∧
    (∀ z : ℝ, 0 < z → IntegrableOn (fun θ : ℝ =>
        (Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2 * σθ θ) Iθ) ∧
    (∀ z : ℝ, 0 < z → IntegrableOn (fun θ : ℝ =>
        (Work.Spaces.Dz G z θ) ^ 2 * σθ θ) Iθ) := by
  obtain ⟨h1, h2, h3⟩ := h
  have key : ∀ (slot : ℝ → ℝ → ℝ) (z : ℝ), 0 < z →
      IntegrableOn (fun θ : ℝ => (slot z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * σθ θ) Iθ →
      IntegrableOn (fun θ : ℝ => (slot z θ) ^ 2 * σθ θ) Iθ := by
    intro slot z hz hint
    have hw2 : (0 : ℝ) < (Work.Spaces.w z) ^ 2 := by
      have := one_le_w_sq hz; linarith
    have hw2ne : (Work.Spaces.w z) ^ 2 ≠ 0 := ne_of_gt hw2
    have haesm : AEStronglyMeasurable (fun θ : ℝ => (slot z θ) ^ 2 * σθ θ)
        (volume.restrict Iθ) := by
      have heq : (fun θ : ℝ => (slot z θ) ^ 2 * σθ θ)
          = fun θ : ℝ => ((slot z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * σθ θ)
              * ((Work.Spaces.w z) ^ 2)⁻¹ := by
        funext θ
        rw [show ((slot z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * σθ θ) * ((Work.Spaces.w z) ^ 2)⁻¹
            = (slot z θ) ^ 2 * σθ θ
              * ((Work.Spaces.w z) ^ 2 * ((Work.Spaces.w z) ^ 2)⁻¹) by ring,
          mul_inv_cancel₀ hw2ne, mul_one]
      rw [heq]
      exact hint.aestronglyMeasurable.mul_const _
    refine Integrable.mono' hint haesm ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    have hσ : 0 ≤ σθ θ := Work.FTS.EllipticEst.thEta_nonneg hθ
    have hsq : 0 ≤ (slot z θ) ^ 2 := sq_nonneg _
    rw [Real.norm_of_nonneg (mul_nonneg hsq hσ)]
    have hw1 : 1 ≤ (Work.Spaces.w z) ^ 2 := one_le_w_sq hz
    have hstep : σθ θ ≤ σθ θ * (Work.Spaces.w z) ^ 2 := by
      calc σθ θ = σθ θ * 1 := (mul_one _).symm
        _ ≤ σθ θ * (Work.Spaces.w z) ^ 2 := mul_le_mul_of_nonneg_left hw1 hσ
    calc (slot z θ) ^ 2 * σθ θ
        ≤ (slot z θ) ^ 2 * (σθ θ * (Work.Spaces.w z) ^ 2) :=
          mul_le_mul_of_nonneg_left hstep hsq
      _ = (slot z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * σθ θ := by ring
  exact ⟨fun z hz => key _ z hz (h1 z hz),
         fun z hz => key _ z hz (h2 z hz),
         fun z hz => key _ z hz (h3 z hz)⟩

/-- A function continuous on the half strip has `σ_η`-honest angular slices. -/
lemma sliceHon_of_cont_on_strip {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (Function.uncurry F) OStrip) :
    ∀ z : ℝ, 0 < z → IntegrableOn (fun θ : ℝ => (F z θ) ^ 2 * σθ θ) Iθ := by
  intro z hz
  have hmem : ∀ θ : ℝ, θ ∈ Iθ → (z, θ) ∈ OStrip := by
    intro θ hθ
    refine ⟨hz, ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩
  have hslice : ContinuousOn (fun θ : ℝ => F z θ) Iθ :=
    hF.comp (continuousOn_const.prodMk continuousOn_id) (fun θ hθ => hmem θ hθ)
  have hsq : ContinuousOn (fun θ : ℝ => (F z θ) ^ 2) Iθ := hslice.pow 2
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hsq
  have hσ : Integrable (fun θ : ℝ => σθ θ) (volume.restrict Iθ) :=
    Work.FTS.EllipticEst.integrableOn_thEta.1
  have hg : Integrable (fun θ : ℝ => C * σθ θ) (volume.restrict Iθ) := hσ.const_mul C
  have haesm : AEStronglyMeasurable (fun θ : ℝ => (F z θ) ^ 2 * σθ θ)
      (volume.restrict Iθ) :=
    (hsq.aestronglyMeasurable measurableSet_Icc).mul hσ.aestronglyMeasurable
  refine Integrable.mono' hg haesm ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  have hσnn : 0 ≤ σθ θ := Work.FTS.EllipticEst.thEta_nonneg hθ
  have hb := hC θ hθ
  have hb' : F z θ ^ 2 ≤ C := by
    rwa [Real.norm_of_nonneg (sq_nonneg _)] at hb
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hσnn)]
  nlinarith [hb', hσnn]

lemma Ioi_prod_subset_strip : Set.Ioi (0:ℝ) ×ˢ Iθ ⊆ OStrip := by
  intro p hp
  obtain ⟨hz, hθ⟩ := hp
  exact ⟨hz, ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩

/-- A function continuous on the half strip is a.e. measurable for the product of the
restrictions to `(0,∞)` and `Iθ`. -/
lemma aemeasurable_strip {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (Function.uncurry F) OStrip) :
    AEMeasurable (fun p : ℝ × ℝ => F p.1 p.2)
      ((MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))).prod
        (MeasureTheory.volume.restrict Iθ)) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
      (Set.Ioi (0:ℝ) ×ˢ Iθ) := hF.mono Ioi_prod_subset_strip
  have h := hcont.aemeasurable (measurableSet_Ioi.prod measurableSet_Icc)
    (μ := MeasureTheory.volume.prod MeasureTheory.volume)
  rwa [← MeasureTheory.Measure.prod_restrict] at h

lemma volume_insert_pair : MeasureTheory.volume ({(0:ℝ), Real.pi/2} : Set ℝ) = 0 := by
  rw [show ({(0:ℝ), Real.pi/2} : Set ℝ) = {0} ∪ {Real.pi/2} by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]]
  exact MeasureTheory.measure_union_null (MeasureTheory.measure_singleton (0:ℝ))
    (MeasureTheory.measure_singleton (Real.pi/2))

lemma null_univ_prod_endpoints :
    (MeasureTheory.volume.prod MeasureTheory.volume)
      ((Set.univ : Set ℝ) ×ˢ ({(0:ℝ), Real.pi/2} : Set ℝ)) = 0 := by
  rw [MeasureTheory.Measure.prod_prod, volume_insert_pair, mul_zero]

lemma Ioo_ae_eq_Icc_prod :
    (Set.univ : Set ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi/2)
      =ᵐ[MeasureTheory.volume.prod MeasureTheory.volume] (Set.univ : Set ℝ) ×ˢ Iθ := by
  rw [MeasureTheory.ae_eq_set]
  constructor
  · have hempty : ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi/2)) \
        ((Set.univ : Set ℝ) ×ˢ Iθ) = ∅ := by
      rw [Set.sdiff_eq_empty]
      intro p hp
      obtain ⟨-, hp2⟩ := hp
      have h2 : 0 < p.2 ∧ p.2 < Real.pi/2 := hp2
      exact ⟨trivial, ⟨le_of_lt h2.1, le_of_lt h2.2⟩⟩
    rw [hempty, MeasureTheory.measure_empty]
  · have hsub : ((Set.univ : Set ℝ) ×ˢ Iθ) \
        ((Set.univ : Set ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi/2)) ⊆
        (Set.univ : Set ℝ) ×ˢ ({(0:ℝ), Real.pi/2} : Set ℝ) := by
      intro p hp
      obtain ⟨hpB, hpA⟩ := hp
      obtain ⟨-, hB⟩ := hpB
      have hB' : 0 ≤ p.2 ∧ p.2 ≤ Real.pi/2 := hB
      have hA' : ¬ (0 < p.2 ∧ p.2 < Real.pi/2) := by
        intro hcon
        exact hpA ⟨trivial, hcon⟩
      refine ⟨trivial, ?_⟩
      rcases lt_or_ge (0:ℝ) p.2 with h | h
      · rcases lt_or_ge p.2 (Real.pi/2) with h' | h'
        · exact absurd ⟨h, h'⟩ hA'
        · exact Or.inr (le_antisymm hB'.2 h')
      · exact Or.inl (le_antisymm h hB'.1)
    exact MeasureTheory.measure_mono_null hsub null_univ_prod_endpoints

/-- A function continuous on the open quadrant is a.e. measurable for the product of `volume`
with the restriction to `Iθ`, after the substitution `z = e^t`. -/
lemma aemeasurable_exp {X : ℝ → ℝ → ℝ}
    (hX : ContinuousOn (Function.uncurry X) Work.FTS.EllipticEst.Q0) :
    AEMeasurable (fun p : ℝ × ℝ => X (Real.exp p.1) p.2)
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Iθ)) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => X (Real.exp p.1) p.2)
      (Set.univ ×ˢ Set.Ioo (0:ℝ) (Real.pi/2)) := by
    have hexp : Continuous (fun p : ℝ × ℝ => Real.exp p.1) :=
      Real.continuous_exp.comp continuous_fst
    have hpair : Continuous (fun p : ℝ × ℝ => (Real.exp p.1, p.2)) :=
      hexp.prodMk continuous_snd
    exact hX.comp hpair.continuousOn (fun p hp => ⟨Real.exp_pos _, hp.2⟩)
  have h := hcont.aemeasurable (MeasurableSet.univ.prod measurableSet_Ioo)
    (μ := MeasureTheory.volume.prod MeasureTheory.volume)
  rw [MeasureTheory.Measure.restrict_congr_set Ioo_ae_eq_Icc_prod] at h
  have h2 : (MeasureTheory.volume.prod MeasureTheory.volume).restrict ((Set.univ : Set ℝ) ×ˢ Iθ)
      = MeasureTheory.volume.prod (MeasureTheory.volume.restrict Iθ) := by
    rw [← MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.restrict_univ]
  rwa [h2] at h

/-- Smoothness of the slot functions of the mollified datum. -/
lemma continuousOn_DzIter_zmoll (G : ℝ → ℝ → ℝ)
    (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G) (hF : Work.FTS.EllSol.EllPkgAux.FourInts G)
    (δ ε : ℝ) (hP : Work.FTS.EllSol.EllPkgAux.Params δ ε) :
    ContinuousOn (Function.uncurry (Work.Spaces.Dz (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε))) OStrip ∧
    ContinuousOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.Dz (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε)))) OStrip ∧
    ContinuousOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε)))) OStrip := by
  obtain ⟨hstrip, -, -⟩ := Work.FTS.EllSol.EllPkgAux.mollAdm G hT hF δ ε hP
  refine ⟨?_, ?_, ?_⟩
  · exact ((Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_Dz_fin
      (G := Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε)
      (n := 1) (hstrip 2)) : ContDiffOn ℝ 1 _ OStrip).continuousOn
  · exact ((Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_Dz_fin
      (G := Work.Spaces.Dz (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε)) (n := 1)
      (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_Dz_fin
        (G := Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) (n := 2) (hstrip 3)))
      : ContDiffOn ℝ 1 _ OStrip).continuousOn
  · exact ((Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_pth_fin
      (G := Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε)) (n := 1)
      (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_pth_fin
        (G := Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) (n := 2) (hstrip 3)))
      : ContDiffOn ℝ 1 _ OStrip).continuousOn

/-- Continuity on the open quadrant of the slot functions of the datum. -/
lemma continuousOn_slot_datum {G : ℝ → ℝ → ℝ} (hS : Work.FTS.EllipticEst.SmoothOpen G) :
    ContinuousOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.Dz G))) Work.FTS.EllipticEst.Q0 ∧
    ContinuousOn (Function.uncurry (Work.Spaces.Dz G)) Work.FTS.EllipticEst.Q0 ∧
    ContinuousOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth G))) Work.FTS.EllipticEst.Q0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact ((Work.FTS.EllipticEst.SmoothOpen.DzIter hS 2).forall 1).continuousOn
  · exact ((Work.FTS.EllipticEst.SmoothOpen.DzIter hS 1).forall 1).continuousOn
  · exact ((Work.FTS.EllipticEst.SmoothOpen.pth (Work.FTS.EllipticEst.SmoothOpen.pth hS)).forall 1).continuousOn

/-! ## the target -/

theorem mollDom : ∃ K : ℝ, 0 < K ∧ ∀ (G : ℝ → ℝ → ℝ),
    Work.FTS.EllSol.EllPkgAux.TraceClass G → Work.FTS.EllSol.EllPkgAux.FourInts G →
    ∀ (δ ε : ℝ), Work.FTS.EllSol.EllPkgAux.Params δ ε →
      (∫ z in Work.Spaces.Iz,
          Work.EllipticEst.Core.ddIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z
          ≤ K * ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ddIntS G z) ∧
      (∫ z in Work.Spaces.Iz,
          Work.EllipticEst.Core.ttIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z
          ≤ K * ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ttIntS G z) ∧
      (∫ z in Work.Spaces.Iz,
          Work.EllipticEst.Core.dIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z
          ≤ K * ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.dIntS G z) ∧
      MeasureTheory.IntegrableOn
        (fun z : ℝ => Work.EllipticEst.Core.mixIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z)
        Work.Spaces.Iz ∧
      MeasureTheory.IntegrableOn
        (fun z : ℝ => Work.EllipticEst.Core.ddIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z)
        Work.Spaces.Iz ∧
      MeasureTheory.IntegrableOn
        (fun z : ℝ => Work.EllipticEst.Core.ttIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z)
        Work.Spaces.Iz ∧
      MeasureTheory.IntegrableOn
        (fun z : ℝ => Work.EllipticEst.Core.dIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z)
        Work.Spaces.Iz := by
  obtain ⟨K, hK, hMaster⟩ := Work.FTS.EllSol.EllPkgAux.MollDom.mollMasterUnif
  refine ⟨K, hK, ?_⟩
  intro G hT hF δ ε hP
  obtain ⟨hε0, hε1, hδ0, hδ1⟩ := hP
  have hT0 : Work.FTS.EllSol.EllPkgAux.TraceClass G := hT
  have hF0 : Work.FTS.EllSol.EllPkgAux.FourInts G := hF
  have hP0 : Work.FTS.EllSol.EllPkgAux.Params δ ε := ⟨hε0, hε1, hδ0, hδ1⟩
  obtain ⟨hS, -, -, -, -, -, -, hsh⟩ := hT
  obtain ⟨hmi, hddG, httG, hdG⟩ := hF
  obtain ⟨hsl1, hsl2, hsl3⟩ := sliceHon_of_sliceHonestOpen hsh
  obtain ⟨hc1, hc2, hc3⟩ := continuousOn_DzIter_zmoll G hT0 hF0 δ ε hP0
  obtain ⟨hd1, hd2, hd3⟩ := continuousOn_slot_datum hS
  have hdd := hMaster (Work.Spaces.Dz (Work.Spaces.Dz (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε)))
      (Work.Spaces.Dz (Work.Spaces.Dz G)) δ ε hδ0 hδ1 hε0 hε1
      (Work.FTS.EllSol.EllPkgAux.MollDom.zmoll_ddDom G hT0 hF0 δ ε hP0)
      (sliceHon_of_cont_on_strip hc2) hsl2
      (by simpa only [Work.EllipticEst.Core.ddIntS] using hddG)
      (aemeasurable_strip hc2) (aemeasurable_exp hd1)
  have htt := hMaster (Work.Spaces.pth (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε)))
      (Work.Spaces.pth (Work.Spaces.pth G)) δ ε hδ0 hδ1 hε0 hε1
      (Work.FTS.EllSol.EllPkgAux.MollDom.zmoll_ttDom G hT0 hF0 δ ε hP0)
      (sliceHon_of_cont_on_strip hc3) hsl1
      (by simpa only [Work.EllipticEst.Core.ttIntS] using httG)
      (aemeasurable_strip hc3) (aemeasurable_exp hd3)
  have hd := hMaster (Work.Spaces.Dz (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε))
      (Work.Spaces.Dz G) δ ε hδ0 hδ1 hε0 hε1
      (Work.FTS.EllSol.EllPkgAux.MollDom.zmoll_dDom G hT0 hF0 δ ε hP0)
      (sliceHon_of_cont_on_strip hc1) hsl3
      (by simpa only [Work.EllipticEst.Core.dIntS] using hdG)
      (aemeasurable_strip hc1) (aemeasurable_exp hd2)
  exact ⟨by simpa only [Work.EllipticEst.Core.ddIntS] using hdd.1,
         by simpa only [Work.EllipticEst.Core.ttIntS] using htt.1,
         by simpa only [Work.EllipticEst.Core.dIntS] using hd.1,
         Work.FTS.EllSol.EllPkgAux.MollDom.zmoll_mixIntS_integrable G hT0 hF0 δ ε hP0,
         by simpa only [Work.EllipticEst.Core.ddIntS] using hdd.2,
         by simpa only [Work.EllipticEst.Core.ttIntS] using htt.2,
         by simpa only [Work.EllipticEst.Core.dIntS] using hd.2⟩

end Work.FTS.ClassC.RopGen.Trace
end
end
-- ===== merged: Submission.Work.FTS.ClassC.gsing_tendsto_atTop_zero_of_classC =====
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

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The patch at `z = 0` -/

/-- `patch g` is `g` with the value on the null slice `z = 0` replaced by `0`.  It agrees with
`g` on the open quadrant, so all the weighted/`L²` estimates are unchanged; the point is that
`HkMem` gives no information at `z = 0`, while `L2Mem` asks for it. -/
def patch (g : Fn) : Fn := fun z θ => if z = 0 then 0 else g z θ

theorem patch_apply_of_ne {g : Fn} {z θ : ℝ} (hz : z ≠ 0) : patch g z θ = g z θ := by
  simp [patch, hz]

@[simp] theorem patch_apply_zero (g : Fn) (θ : ℝ) : patch g 0 θ = 0 := by
  simp [patch]

/-! ## Elementary weight facts -/

/-- On the open quadrant the weight factor `w z / sin(2θ)^{η/2}` is `≥ 1`. -/
private lemma one_le_wdiv {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    1 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
  have hz2 : (0 : ℝ) < z ^ 2 := by positivity
  have hw : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, one_le_div hz2]
    exact pow_le_pow_left₀ (le_of_lt hz) (by linarith) 2
  have hsinpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs_pos : 0 < Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hsinpos _
  have hs_le : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one (le_of_lt hsinpos) (Real.sin_le_one _)
      (by rw [Work.Spaces.eta]; norm_num)
  rw [one_le_div hs_pos]
  exact le_trans hs_le hw

/-- Pointwise domination of `(g z θ)²` by the `k = 0` integrand on the open quadrant. -/
private lemma sq_le_wdiv_sq {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (g z θ) ^ 2
      ≤ (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  have hr : 1 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
    one_le_wdiv hz hθ
  have hr0 : 0 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
    le_trans zero_le_one hr
  have habs : |g z θ|
      ≤ |g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))| := by
    rw [abs_mul, abs_of_nonneg hr0]
    exact le_mul_of_one_le_right (abs_nonneg _) hr
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (g z θ)) habs 2

/-- The open interval `(0,π/2)` and the closed `Iθ` carry the same restriction of Lebesgue
measure (they differ by the two null endpoints). -/
private lemma restrict_Ioo_eq_restrict_Iθ :
    volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) = volume.restrict Work.Spaces.Iθ :=
  Measure.restrict_congr_set (by rw [Work.Spaces.Iθ]; exact Ioo_ae_eq_Icc)

/-! ## `L²`-honesty of the patch -/

/-- `HkMem α 0 g` plus `SmoothOpen g` imply the *unweighted* honesty `L2Mem (patch g)`. -/
theorem L2Mem_patch {α : ℝ} {g : Fn} (hreg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmem : Work.Spaces.HkMem α 0 g) : Work.Spaces.L2Mem (patch g) := by
  have hcontQ : ContinuousOn (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hreg.continuousOn
  -- ## the angular slices
  have hslice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => (patch g z θ) ^ 2) Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_ne z 0 with rfl | hz0
    · have h0 : (fun θ => (patch g 0 θ) ^ 2) = fun _ : ℝ => (0 : ℝ) := by
        funext θ; simp
      rw [h0]
      exact integrableOn_zero
    · have hzpos : 0 < z := lt_of_le_of_ne' hz hz0
      have hfun : (fun θ => (patch g z θ) ^ 2) = fun θ => (g z θ) ^ 2 := by
        funext θ; rw [patch_apply_of_ne (g := g) hz0]
      rw [hfun]
      refine Integrable.mono' (hmem.1 z hz) ?_ ?_
      · have h1 := (Work.Spaces.aesm_slice_of_continuousOn_Qd
          (Function.uncurry g) hcontQ hzpos).pow 2
        refine h1.congr (Filter.Eventually.of_forall fun θ => ?_)
        simp only [Function.uncurry, Pi.pow_apply]
      · rw [← restrict_Ioo_eq_restrict_Iθ]
        refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact le_trans (sq_le_wdiv_sq hzpos hθ)
          (by simpa only [Work.Spaces.DzIter_zero] using
            Work.Spaces.sq_le_HkIntegrand_z α 0 g z θ 0 (le_refl 0))
  refine ⟨hslice, ?_⟩
  -- ## the radial integral
  have hc : ContinuousOn (fun p : ℝ × ℝ => (patch g p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (g p.1 p.2) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
      have h2 : ((Function.uncurry g) ^ 2) = fun p : ℝ × ℝ => (g p.1 p.2) ^ 2 := by
        funext p
        rcases p with ⟨a, b⟩
        simp
      simpa only [h2] using hcontQ.pow 2
    refine h1.congr ?_
    intro p hp
    show (patch g p.1 p.2) ^ 2 = (g p.1 p.2) ^ 2
    rw [patch_apply_of_ne (g := g) (ne_of_gt hp.1)]
  have haesm : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ, (patch g z θ) ^ 2)
      (volume.restrict Work.Spaces.Iz) := by
    have := (Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => (patch g p.1 p.2) ^ 2) hc).integral_prod_right'
    simpa only using this
  refine Integrable.mono' hmem.2 haesm ?_
  refine ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
  rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
  rcases eq_or_ne z 0 with rfl | hz0
  · have h0 : (∫ θ in Work.Spaces.Iθ, (patch g 0 θ) ^ 2) = 0 := by
      simp [patch]
    rw [h0]
    exact integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 0 g 0 θ
  · have hzpos : 0 < z := lt_of_le_of_ne' hz hz0
    refine integral_mono_ae (hslice z hz) (hmem.1 z hz) ?_
    rw [← restrict_Ioo_eq_restrict_Iθ]
    refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    simp only [patch_apply_of_ne (g := g) hz0]
    exact le_trans (sq_le_wdiv_sq hzpos hθ)
      (by simpa only [Work.Spaces.DzIter_zero] using
        Work.Spaces.sq_le_HkIntegrand_z α 0 g z θ 0 (le_refl 0))

/-! ## `Gsing` only sees `g` on `z > 0` -/

/-- The angular moment of `patch g` agrees with that of `g` at every `r > 0`. -/
theorem Fstar_patch (g : Fn) {r : ℝ} (hr : 0 < r) :
    Work.Elliptic.Fstar (patch g) r = Work.Elliptic.Fstar g r := by
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar]
  refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  rw [patch_apply_of_ne (g := g) (ne_of_gt hr)]

/-- `Gstar` of `patch g` equals `Gstar` of `g` for `z > 0` (both only see `F_*(r)` for
`r > 0`). -/
theorem gstar_patch {α : ℝ} (g : Fn) {z : ℝ} (hz : 0 < z) :
    Work.Elliptic.Gstar α (patch g) z = Work.Elliptic.Gstar α g z := by
  rw [Work.Elliptic.Gstar, Work.Elliptic.Gstar, Work.Elliptic.L12, Work.Elliptic.L12]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
  rw [Work.Elliptic.L12dens, Work.Elliptic.L12dens]
  refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  rw [patch_apply_of_ne (g := g) (ne_of_gt (lt_trans hz hr))]

/-- `Gbar` of `patch g` equals `Gbar` of `g` for `z > 0`. -/
theorem gbar_patch {α : ℝ} (g : Fn) {z : ℝ} (hz : 0 < z) :
    Work.Elliptic.Gbar α (patch g) z = Work.Elliptic.Gbar α g z := by
  rw [Work.Elliptic.Gbar, Work.Elliptic.Gbar]
  congr 1
  rw [intervalIntegral.integral_of_le hz.le, intervalIntegral.integral_of_le hz.le]
  refine setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
  rw [Fstar_patch g hs.1]

/-- `Gsing` of `patch g` equals `Gsing` of `g` at every `z > 0`. -/
theorem gsing_patch {α : ℝ} (g : Fn) {z : ℝ} (hz : 0 < z) :
    Work.Elliptic.Gsing α (patch g) z = Work.Elliptic.Gsing α g z := by
  rw [Work.Elliptic.Gsing, Work.Elliptic.Gsing, gstar_patch g hz, gbar_patch g hz]

/-! ## The target -/

theorem gsing_tendsto_atTop_zero_of_classC {α : ℝ} {g : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hreg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmem : Work.Spaces.HkMem α 7 g) :
    Filter.Tendsto (fun z => Work.Elliptic.Gsing α g z) Filter.atTop (nhds 0) := by
  have hmem0 : Work.Spaces.HkMem α 0 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hreg 0 (Nat.zero_le 7) hmem
  have hL2 : Work.Spaces.L2Mem (patch g) := L2Mem_patch hreg hmem0
  have h := Work.FTS.EllipticEst.Gsing_tendsto_atTop_zero α (patch g) hα hL2
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
  exact gsing_patch g (by linarith : 0 < z)

end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Assembly.StepReg2_all =====
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

/-! ## The `SmoothQuad` version of `|D_z f|_{ℋⁿ}² ≤ |f|_{ℋ^{n+1}}²` -/

/-! ## The bundle -/


end

end Work.FTS.CoercivityFix.Assembly
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.CSQ_succ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer

theorem CSQ_succ (α : ℝ) (hα : 0 < α) (n : ℕ)
    {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ} {CC c₁ c₂ : ℝ}
    (hCC : 0 ≤ CC) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (h : Work.FTS.CoercivityFix.Transfer.CSQ α n IP CC) :
    Work.FTS.CoercivityFix.Transfer.CSQ α (n + 1)
      (Work.Coercivity.HkIPStep c₁ c₂ IP) (3 * max 1 (max c₁ c₂) * CC) := by
  intro X Y hXq hYq hXm hYm
  -- `ℋⁿ`-membership of the three functions at both arguments, from the descent
  obtain ⟨hXm0, hXmd, hXmz⟩ := HkMem_descent_Q0Sm α hα n hXq hXm
  obtain ⟨hYm0, hYmd, hYmz⟩ := HkMem_descent_Q0Sm α hα n hYq hYm
  -- `C^n`-smoothness of the three functions at both arguments
  have hXq0 : Q0Sm n X := hXq.mono (Nat.le_succ n)
  have hYq0 : Q0Sm n Y := hYq.mono (Nat.le_succ n)
  have hXqd : Q0Sm n (Work.Spaces.Dth X) := hXq.dth
  have hYqd : Q0Sm n (Work.Spaces.Dth Y) := hYq.dth
  have hXqz : Q0Sm n (Work.Spaces.Dz X) := hXq.dz
  have hYqz : Q0Sm n (Work.Spaces.Dz Y) := hYq.dz
  -- the three Cauchy–Schwarz bounds at level `n`
  have h1 := h X Y hXq0 hYq0 hXm0 hYm0
  have h2 := h (Work.Spaces.Dth X) (Work.Spaces.Dth Y) hXqd hYqd hXmd hYmd
  have h3 := h (Work.Spaces.Dz X) (Work.Spaces.Dz Y) hXqz hYqz hXmz hYmz
  -- the three norm comparisons with level `n+1`
  have hN0X : Work.Spaces.HkNorm α n X ≤ Work.Spaces.HkNorm α (n + 1) X := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt
      (Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (Nat.le_succ n) hXm)
  have hN0Y : Work.Spaces.HkNorm α n Y ≤ Work.Spaces.HkNorm α (n + 1) Y := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt
      (Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (Nat.le_succ n) hYm)
  have hN1X : Work.Spaces.HkNorm α n (Work.Spaces.Dth X)
      ≤ Work.Spaces.HkNorm α (n + 1) X := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt (Work.FTS.CoercivityStep.Norm.HkSq_Dth_le α hα n hXm)
  have hN1Y : Work.Spaces.HkNorm α n (Work.Spaces.Dth Y)
      ≤ Work.Spaces.HkNorm α (n + 1) Y := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt (Work.FTS.CoercivityStep.Norm.HkSq_Dth_le α hα n hYm)
  have hN2X : Work.Spaces.HkNorm α n (Work.Spaces.Dz X)
      ≤ Work.Spaces.HkNorm α (n + 1) X := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt (HkSq_Dz_le_Q0Sm α n hXq hXm)
  have hN2Y : Work.Spaces.HkNorm α n (Work.Spaces.Dz Y)
      ≤ Work.Spaces.HkNorm α (n + 1) Y := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt (HkSq_Dz_le_Q0Sm α n hYq hYm)
  -- the three products are dominated by `CC |X|_{n+1} |Y|_{n+1}`
  have hNX : 0 ≤ Work.Spaces.HkNorm α (n + 1) X := Work.Spaces.HkNorm_nonneg α (n + 1) X
  have hNY : 0 ≤ Work.Spaces.HkNorm α (n + 1) Y := Work.Spaces.HkNorm_nonneg α (n + 1) Y
  have hNXn : 0 ≤ Work.Spaces.HkNorm α n X := Work.Spaces.HkNorm_nonneg α n X
  have hNYn : 0 ≤ Work.Spaces.HkNorm α n Y := Work.Spaces.HkNorm_nonneg α n Y
  have e1 : CC * Work.Spaces.HkNorm α n X * Work.Spaces.HkNorm α n Y
      ≤ CC * Work.Spaces.HkNorm α (n + 1) X * Work.Spaces.HkNorm α (n + 1) Y :=
    mul_le_mul (mul_le_mul_of_nonneg_left hN0X hCC) hN0Y hNYn (mul_nonneg hCC hNX)
  have e2 : CC * Work.Spaces.HkNorm α n (Work.Spaces.Dth X)
        * Work.Spaces.HkNorm α n (Work.Spaces.Dth Y)
      ≤ CC * Work.Spaces.HkNorm α (n + 1) X * Work.Spaces.HkNorm α (n + 1) Y :=
    mul_le_mul (mul_le_mul_of_nonneg_left hN1X hCC) hN1Y
      (Work.Spaces.HkNorm_nonneg α n _) (mul_nonneg hCC hNX)
  have e3 : CC * Work.Spaces.HkNorm α n (Work.Spaces.Dz X)
        * Work.Spaces.HkNorm α n (Work.Spaces.Dz Y)
      ≤ CC * Work.Spaces.HkNorm α (n + 1) X * Work.Spaces.HkNorm α (n + 1) Y :=
    mul_le_mul (mul_le_mul_of_nonneg_left hN2X hCC) hN2Y
      (Work.Spaces.HkNorm_nonneg α n _) (mul_nonneg hCC hNX)
  -- the triangle inequality for the three terms of the step
  have habs : |Work.Coercivity.HkIPStep c₁ c₂ IP X Y|
      ≤ |IP X Y| + c₁ * |IP (Work.Spaces.Dth X) (Work.Spaces.Dth Y)|
        + c₂ * |IP (Work.Spaces.Dz X) (Work.Spaces.Dz Y)| := by
    have hA := abs_add_le (IP X Y + c₁ * IP (Work.Spaces.Dth X) (Work.Spaces.Dth Y))
      (c₂ * IP (Work.Spaces.Dz X) (Work.Spaces.Dz Y))
    have hB := abs_add_le (IP X Y) (c₁ * IP (Work.Spaces.Dth X) (Work.Spaces.Dth Y))
    simp only [Work.Coercivity.HkIPStep]
    simp only [abs_mul, abs_of_nonneg hc₁, abs_of_nonneg hc₂] at hA hB ⊢
    linarith
  refine le_trans habs ?_
  have e4 : |IP X Y|
      ≤ CC * Work.Spaces.HkNorm α (n + 1) X * Work.Spaces.HkNorm α (n + 1) Y :=
    le_trans h1 e1
  have e5 : |IP (Work.Spaces.Dth X) (Work.Spaces.Dth Y)|
      ≤ CC * Work.Spaces.HkNorm α (n + 1) X * Work.Spaces.HkNorm α (n + 1) Y :=
    le_trans h2 e2
  have e6 : |IP (Work.Spaces.Dz X) (Work.Spaces.Dz Y)|
      ≤ CC * Work.Spaces.HkNorm α (n + 1) X * Work.Spaces.HkNorm α (n + 1) Y :=
    le_trans h3 e3
  -- the arithmetic: `1 + c₁ + c₂ ≤ 3 max 1 (max c₁ c₂)`
  have hM1 : (1 : ℝ) ≤ max 1 (max c₁ c₂) := le_max_left _ _
  have hMc₁ : c₁ ≤ max 1 (max c₁ c₂) :=
    le_trans (le_max_left c₁ c₂) (le_max_right (1 : ℝ) (max c₁ c₂))
  have hMc₂ : c₂ ≤ max 1 (max c₁ c₂) :=
    le_trans (le_max_right c₁ c₂) (le_max_right (1 : ℝ) (max c₁ c₂))
  have hcoef : 1 + c₁ + c₂ ≤ 3 * max 1 (max c₁ c₂) := by linarith
  have hP : 0 ≤ CC * Work.Spaces.HkNorm α (n + 1) X * Work.Spaces.HkNorm α (n + 1) Y :=
    mul_nonneg (mul_nonneg hCC hNX) hNY
  have hsum : |IP X Y| + c₁ * |IP (Work.Spaces.Dth X) (Work.Spaces.Dth Y)|
        + c₂ * |IP (Work.Spaces.Dz X) (Work.Spaces.Dz Y)|
      ≤ (1 + c₁ + c₂)
        * (CC * Work.Spaces.HkNorm α (n + 1) X * Work.Spaces.HkNorm α (n + 1) Y) := by
    nlinarith [e4, e5, e6, hP]
  calc |IP X Y| + c₁ * |IP (Work.Spaces.Dth X) (Work.Spaces.Dth Y)|
        + c₂ * |IP (Work.Spaces.Dz X) (Work.Spaces.Dz Y)|
      ≤ (1 + c₁ + c₂)
          * (CC * Work.Spaces.HkNorm α (n + 1) X * Work.Spaces.HkNorm α (n + 1) Y) := hsum
    _ ≤ (3 * max 1 (max c₁ c₂))
          * (CC * Work.Spaces.HkNorm α (n + 1) X * Work.Spaces.HkNorm α (n + 1) Y) :=
        mul_le_mul_of_nonneg_right hcoef hP
    _ = 3 * max 1 (max c₁ c₂) * CC * Work.Spaces.HkNorm α (n + 1) X
          * Work.Spaces.HkNorm α (n + 1) Y := by ring

end Work.FTS.CoercivityFix.Transfer
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadA =====
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


end Work.FTS.CoercivityFix.Transfer.E1Parts
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeColl.aeGradTraceRateUnw =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeColl/aeGradTraceRateUnw` — the a.e. trace and endpoint rate of `z ∂_z u`, *unweighted*

The target

```
theorem aeGradTraceRateUnw : ∃ C > 0, ∀ α u G, AeData α u G →
    (∀ᵐ z ∂(volume.restrict (Ioi 0)), IntegrableOn ((z ∂_z∂_θu)² σ) Iθ) →
    IntegrableOn (z ↦ ∫_θ (z ∂_z∂_θu(z,θ))² σ(θ)) Iz →
    ∀ᵐ z ∂(volume.restrict (Ioi 0)),
      (z ∂_z u(z,·) → 0 at 0⁺) ∧ (z ∂_z u(z,·) → 0 at (π/2)⁻) ∧
      (∀ θ ∈ (0,π/2), (z∂_zu(z,θ))² ≤ C θ^{1+η} ∫_{0<θ'<θ} (z∂_z∂_θu(z,θ'))²σ(θ')) ∧
      (∀ θ ∈ (0,π/2), (z∂_zu(z,θ))² ≤ C (π/2-θ)^{1+η} ∫_{θ<θ'<π/2} (z∂_z∂_θu(z,θ'))²σ(θ'))
```

is the single a.e. statement that `AeColl.i1PaperWeakMixed` consumes: the *two* mixed honesties
(a.e. slicewise, and the *unweighted* outer `z`-integral — no radial weight `w²`) give, for
almost every `z > 0`, the vanishing of the two endpoint traces of the slice of `U = z ∂_z u`
**and** the two sharp endpoint rates with one constant `C` uniform in `α`, `u`, `G`, `z`, `θ`.

## Proof

Two independent halves, each already in the tree:

* the two traces: `Work.FTS.EllipticEst.H2W.AeProof.gradTraceAeUnw` — the unweighted replay of
  `AngAWeak.aeGradTraceAe` (its `boundU`-domination needs only the *local* `z`-integrability of
  the slice energy, which here is the hypothesis itself);
* the two rates: the universal boundary-rate lemma
  `Work.EllipticEst.Core.sliceBoundaryLimit` (`K = 2` outright) applied to the slice
  `θ ↦ z ∂_z u(z,θ)`, whose endpoint constants are identified with `0` by the trace statement,
  whose weighted derivative square is `V²σ` by Clairaut (`AeI1Fts.slice_deriv_eq`), and whose
  energy is finite at a.e. `z` by the a.e.-slicewise honesty.  This is the argument of
  `H2W/slot20A_pieces/aeGradRate`, with the two `ℋ⁰`-honesties replaced by the (weaker)
  a.e. ones.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeColl

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "σ" => Work.FTS.EllipticEst.AngSecond.sig




end Work.FTS.EllipticEst.AeColl
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AeI1Fts.tendsto_term_psi_cut =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeI1Fts/tendsto_term_psi_cut`

The `θ`-layer (boundary) term of the angular integration by parts, along the *sequential*
angular cut-off `χ_{1/(k+1)}` and with the *radial* cut-off `cut k → 1`:

`∫_z cut k z · w z² · ∫_θ σ θ (χ_{1/(k+1)})' θ (U u z θ · V u z θ) ⟶ 0` as `k → ∞`,

where `U u = z ∂_z u`, `V u = z ∂_z ∂_θ u = ∂_θ (U u)` (Clairaut),
`σ = sigE θ = sin(2θ)^{-η}`, `w z = (1+z)²/z²` and `cut k` is the radial cut-off of
`Submission/Work/FTS/EllipticEst/interpol_trunc_defs.lean`.

## Route

* the angular layer bound `layer_bound_theta` (module `psiDeriv_layer`) bounds the inner
  `θ`-integral, for `0 < ε ≤ π/4`, by
  `2S₁√(2·(2^η/(1+η))·(π/4)^η)·√A_z·√(L_ε + R_ε)` with `A_z` the total `σ`-energy of the slice
  of `V u` and `L_ε`, `R_ε` its two shrinking layer energies;
* the a.e. slice data `sliceBoundAe` (module `psiDeriv_setup`) supplies the two endpoint rates
  of the slice of `U u` and the slicewise integrability, and `tendsto_layerEnergy_zero` gives
  `L_ε, R_ε → 0`;
* `w²·A_· ∈ L¹((0,∞))` is `TT.AeI1.integrableOn_w2_sliceEnergy`;
* `cut k z → 1` for every `z > 0` and `cut k ≤ 1` pointwise, and `1/((k:ℝ)+1) → 0⁺`; the
  dominated convergence theorem in `k` then gives the limit `0`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeI1Fts

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-! ## Arithmetic helpers -/






/-! ## The target -/


end Work.FTS.EllipticEst.AeI1Fts
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.I1Ae.RIFPsiB =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.I1Ae

set_option autoImplicit false
set_option maxHeartbeats 1600000

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "χ" => Work.FTS.EllipticEst.cut
local notation "ψ" => Work.FTS.EllipticEst.SliceMixedAux.cut

open Work.FTS.EllipticEst.AeI1Fts (U V Hh AA BB sigE sig1 sig2 II nuQ Fp Fd)



/-- The `N`-energy slice `∫_θ U²cos²(2θ)σ₂` at fixed `z`. -/
def Nz (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Iθo, (U u z θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * sig2 θ




end Work.FTS.EllipticEst.I1Ae
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.l0_second =====
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
theorem l0_second (C₁ : ℝ) (hC₁ : 0 < C₁)
    (hfirst : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
      Work.Spaces.HkMem α 0 Ψ ∧
      Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) ∧
      Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ) ∧
      Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
        + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))
        + Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ))
        ≤ C₁ * Real.sqrt (Work.Spaces.HkSq α 0 F)) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
      Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ))
        ≤ C * (Real.sqrt (Work.Spaces.HkSq α 0 F)
            + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))) := by
  -- The `I₁` coercivity of Step 2 in the strengthened weak class: `Prop.i1_bare_hh` supplies it
  -- with the two first-order honesties, of which `EllWeakPos.memZPth2` is a field of the class
  -- and the other is part of `hfirst`; the assembly `l0_second_of_i1hh` then gives the target.
  exact l0_second_of_i1hh C₁ hC₁ i1_bare_hh hfirst

end Work.FTS.EllipticEst.Prop
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.est_step_weak =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TT.est_step_weak`: the induction step of Elgindi's `prop:Hk`, in the weak class

## Why the imports are what they are (read this before changing them)

`TT.propHk_core` (hence `remov.propHk_fts`) **imports** this very file: the certificate `prop:Hk`
consumes the induction step proved here.  Consequently nothing on the critical path of
`est_step_weak` may reach `remov.propHk_fts`, or Lean would report an import cycle.  The natural
modules of `Submission/Work/FTS/EllipticEst/remov/` for two of the ingredients

* `remov.EllWeakPos_DzIter_one_shift` (admissibility of the radially differentiated data),
* `remov.A_top_slot_bound` (the top angular slot of `z²∂_zzΨ`),
* `remov.Dz_slice_identities` (the two slice identities),
* `remov.EllEstUnif_step` (the assembly itself),

all have cones that reach `propHk_fts`, so they are replaced here by cone-clean twins:

* `TT.ESW.Pieces.EllEstUnif_step_of_pieces` — a verbatim copy of the assembly (`ESW/StepPieces.lean`);
* `TT.ESW.Shift.EllWeakPos_DzIter_one_shift_of_two_le` — a copy of the second (`ESW/ShiftWeak.lean`)
  with the unused `EllHyp_certificates` import dropped and two structural facts
  (`SmoothOpen.zsq_mul`, `HkMem_of_majorant_ae`) re-proved in `ESW/OpenMem.lean`;
* `remov.TopCoreB.ATopClean` — a cone-clean module declaring `remov.A_top_slot_bound` *under the
  same name* as the original;
* `H2W.Slot01W.DzSliceIdent` — likewise for `remov.Dz_slice_identities`.

The two top angular slots (`hcore`) are supplied by

* `remov.A_top_slot_bound` (from `remov.TopCoreB.ATopClean`, proved, cone-clean);
* `TT.ESW.bSlot_bound` (proved in `Prop/Rtilde/BSlot.lean`): the `B`-slot, assembled from the
  sharp angular chain, the one-dimensional far-region estimate `remov.slice_ang_gen` applied
  slicewise (`TT.ESW.U_le_of_1d`), the source domination (`Prop.Rtilde.SourceLe`, proved) and the
  low-order terms.  `bSlot_bound` takes those two inputs (`hSrc`, `hOneD`) as explicit hypotheses;
  they are instantiated here with `Prop.Rtilde.SourceLe` (proved) and
  `Prop.Rtilde.oneD_of_far` applied to the far-window bound `Prop.Rtilde.VFar` — the single
  unproved input of the whole route (the paper's far-region §"General `ℋ^k` case" analysis on
  `[3π/8, π/2]`, proved from `SliceHyp` by `remov.slice_ang_v_far`).
-/

namespace Work.FTS.EllipticEst.TT


end Work.FTS.EllipticEst.TT
end
-- ===== merged: Submission.Work.FTS.EpsEngine.PerzAssemblyGen =====
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

/-! ## Integrability of the level-`k` summands -/

/-- A finite sum of integrable functions is integrable. -/
private lemma integrable_finsetSum_perz {ι : Type*} (s : Finset ι) {g : ι → ℝ → ℝ}
    {μ : MeasureTheory.Measure ℝ} (h : ∀ i ∈ s, MeasureTheory.Integrable (g i) μ) :
    MeasureTheory.Integrable (fun x => ∑ i ∈ s, g i x) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using MeasureTheory.integrable_zero ℝ ℝ μ
  | insert a s ha ih =>
      have h1 : MeasureTheory.Integrable (g a) μ := h a (Finset.mem_insert_self a s)
      have h2 : MeasureTheory.Integrable (fun x => ∑ i ∈ s, g i x) μ :=
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      rw [show (fun x : ℝ => ∑ i ∈ insert a s, g i x)
          = fun x : ℝ => g a x + ∑ i ∈ s, g i x from by
        funext x; rw [Finset.sum_insert ha]]
      exact h1.add h2

/-- The `if`-guarded mixed slot of the level-`k` integrand is integrable on the angular slice,
from the level-`k` honesty of the datum. -/
private lemma integrableOn_if_mixed_perz (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f)
    (i j : ℕ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ k
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      Work.Spaces.Iθ := by
  by_cases h : 1 ≤ i ∧ i + j ≤ k
  · rw [show (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ k
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        = fun θ : ℝ => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 from by
      funext θ; rw [if_pos h]]
    refine MeasureTheory.Integrable.mono' (hmem.1 z (Set.mem_Ici.mpr hz.le))
      (Work.FTS.GalBasis.cc.aesm_slice_mixed_Wt_sq hF α j i hz) ?_
    rw [MeasureTheory.ae_restrict_iff' (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
    exact Filter.Eventually.of_forall fun θ _ => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i j h.1 h.2
  · rw [show (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ k
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        = fun _ : ℝ => (0 : ℝ) from by
      funext θ; rw [if_neg h]]
    exact MeasureTheory.integrableOn_zero

/-! ## The generic assembly -/

/-- **The per-`z` slab assembly, generic in the level.**  Given the two half-bounds — the
`z`-slots (`Cz`) and the mixed slots (`Cm`) of the level-`k` integrand, both at honesty
`ℋ^{k+2}` — the level-`k` per-`z` energy bound holds with constant `(k+1)·Cz + (k+1)²·Cm`. -/
theorem HkIntegrand_perz_le_of_halves (k : ℕ) (Cz Cm : ℝ) (hCz : 0 < Cz) (hCm : 0 < Cm)
    (hzslot : ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ {f : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α (k + 2) f →
      ∀ i : ℕ, i ≤ k → ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ Cz * (1 + (Work.Spaces.w z) ^ 2) * (1 + Work.Spaces.HkNorm α (k + 2) f) ^ 2)
    (hmixed : ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ {f : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α (k + 2) f →
      ∀ (i j : ℕ), 1 ≤ i → i + j ≤ k → ∀ {z : ℝ}, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ Cm * (1 + (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α (k + 2) f) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ {f : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α (k + 2) f →
      ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
        ≤ C * (1 + (Work.Spaces.w z) ^ 2) * (1 + Work.Spaces.HkNorm α (k + 2) f) ^ 2 := by
  refine ⟨((k + 1 : ℕ) : ℝ) * Cz + ((k + 1 : ℕ) : ℝ) ^ 2 * Cm, by positivity, ?_⟩
  intro α hα f hF hmem z hz
  obtain ⟨hα0, hα1⟩ := hα
  have hαI : α ∈ Set.Ioc 0 1 := ⟨hα0, hα1⟩
  have hmemk : Work.Spaces.HkMem α k f :=
    Work.FTS.OpenPkg.HkMem_mono_open hF k (by omega) hmem
  have hXsq : Work.Spaces.HkSq α (k + 2) f
      ≤ (1 + Work.Spaces.HkNorm α (k + 2) f) ^ 2 := by
    have h2 : 0 ≤ Work.Spaces.HkSq α (k + 2) f := Work.Spaces.HkSq_nonneg α (k + 2) f
    have h3 : 0 ≤ Work.Spaces.HkNorm α (k + 2) f := Work.Spaces.HkNorm_nonneg α (k + 2) f
    have h4 : Work.Spaces.HkNorm α (k + 2) f = Real.sqrt (Work.Spaces.HkSq α (k + 2) f) := rfl
    rw [h4]
    nlinarith [Real.sq_sqrt h2, h3, h2]
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- the degenerate case `z = 0`
    subst hz0
    have hzero : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f 0 θ) = 0 := by
      rw [show (fun θ : ℝ => Work.Spaces.HkIntegrand α k f 0 θ) = fun _ => (0 : ℝ) from
        funext fun θ => Work.Spaces.HkIntegrand_zero_z α k f θ]
      simp
    rw [hzero]
    have hw0 : (Work.Spaces.w 0) ^ 2 = 0 := by rw [Work.Spaces.w]; norm_num
    rw [hw0]
    have hX0 : 0 ≤ Work.Spaces.HkNorm α (k + 2) f := Work.Spaces.HkNorm_nonneg α (k + 2) f
    have hcoef : 0 < ((k + 1 : ℕ) : ℝ) * Cz + ((k + 1 : ℕ) : ℝ) ^ 2 * Cm := by positivity
    nlinarith [hX0, sq_nonneg (1 + Work.Spaces.HkNorm α (k + 2) f)]
  · -- the main case `z > 0`
    have hPint : MeasureTheory.Integrable
        (fun θ : ℝ => ∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      integrable_finsetSum_perz _ (fun i hi => Work.FTS.EllipticEst.integrableOn_zSummand α k hF
        hmemk i (by rw [Finset.mem_range] at hi; omega) (Set.mem_Ici.mpr hzpos.le))
    have hMint : MeasureTheory.Integrable
        (fun θ : ℝ => ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      integrable_finsetSum_perz _
        (fun i _ => integrable_finsetSum_perz _
          (fun j _ => integrableOn_if_mixed_perz α k hF hmemk i j hzpos))
    have hdef : (fun θ : ℝ => Work.Spaces.HkIntegrand α k f z θ)
        = fun θ : ℝ => (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k
                then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
      funext θ; rw [Work.Spaces.HkIntegrand]
    rw [hdef, MeasureTheory.integral_add hPint hMint]
    -- the bound for the pure-`z` part
    have hPbound : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ((k + 1 : ℕ) : ℝ) * (Cz * (1 + (Work.Spaces.w z) ^ 2)
            * (1 + Work.Spaces.HkNorm α (k + 2) f) ^ 2) := by
      rw [MeasureTheory.integral_finsetSum (s := Finset.range (k + 1)) (hf := fun i hi =>
        Work.FTS.EllipticEst.integrableOn_zSummand α k hF hmemk i
          (by rw [Finset.mem_range] at hi; omega) (Set.mem_Ici.mpr hzpos.le))]
      calc ∑ i ∈ Finset.range (k + 1), (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ ∑ _i ∈ Finset.range (k + 1), (Cz * (1 + (Work.Spaces.w z) ^ 2)
              * (1 + Work.Spaces.HkNorm α (k + 2) f) ^ 2) :=
            Finset.sum_le_sum fun i hi => hzslot α hαI hF hmem i
              (by rw [Finset.mem_range] at hi; omega) z hz
        _ = ((k + 1 : ℕ) : ℝ) * (Cz * (1 + (Work.Spaces.w z) ^ 2)
              * (1 + Work.Spaces.HkNorm α (k + 2) f) ^ 2) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    -- the bound for the mixed part
    have hMbound : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (k + 1),
          ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) * (Cm * (1 + (Work.Spaces.w z) ^ 2)
            * Work.Spaces.HkSq α (k + 2) f)) := by
      rw [MeasureTheory.integral_finsetSum (s := Finset.range (k + 1)) (hf := fun i _ =>
        integrable_finsetSum_perz _
          (fun j _ => integrableOn_if_mixed_perz α k hF hmemk i j hzpos))]
      calc ∑ i ∈ Finset.range (k + 1), (∫ θ in Work.Spaces.Iθ, ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k
                then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ ∑ _i ∈ Finset.range (k + 1), (((k + 1 : ℕ) : ℝ) * (Cm * (1 + (Work.Spaces.w z) ^ 2)
              * Work.Spaces.HkSq α (k + 2) f)) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [MeasureTheory.integral_finsetSum (s := Finset.range (k + 1)) (hf := fun j _ =>
              integrableOn_if_mixed_perz α k hF hmemk i j hzpos)]
            calc ∑ j ∈ Finset.range (k + 1), (∫ θ in Work.Spaces.Iθ,
                    (if 1 ≤ i ∧ i + j ≤ k
                      then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
                ≤ ∑ _j ∈ Finset.range (k + 1), (Cm * (1 + (Work.Spaces.w z) ^ 2)
                    * Work.Spaces.HkSq α (k + 2) f) := by
                  refine Finset.sum_le_sum fun j _ => ?_
                  by_cases hij : 1 ≤ i ∧ i + j ≤ k
                  · simp only [if_pos hij]
                    exact hmixed α hαI hF hmem i j hij.1 (by omega) hzpos
                  · simp only [if_neg hij]
                    have h1 : 0 ≤ Cm * (1 + (Work.Spaces.w z) ^ 2)
                        * Work.Spaces.HkSq α (k + 2) f := by
                      have := Work.Spaces.HkSq_nonneg α (k + 2) f
                      positivity
                    simpa using h1
              _ = ((k + 1 : ℕ) : ℝ) * (Cm * (1 + (Work.Spaces.w z) ^ 2)
                    * Work.Spaces.HkSq α (k + 2) f) := by
                  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ = ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) * (Cm * (1 + (Work.Spaces.w z) ^ 2)
              * Work.Spaces.HkSq α (k + 2) f)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    refine le_trans (add_le_add hPbound hMbound) ?_
    have hYsq : Work.Spaces.HkSq α (k + 2) f
        ≤ (1 + Work.Spaces.HkNorm α (k + 2) f) ^ 2 := hXsq
    have hstep : ((k + 1 : ℕ) : ℝ) * (Cm * (1 + (Work.Spaces.w z) ^ 2)
          * Work.Spaces.HkSq α (k + 2) f)
        ≤ ((k + 1 : ℕ) : ℝ) * (Cm * (1 + (Work.Spaces.w z) ^ 2)
          * (1 + Work.Spaces.HkNorm α (k + 2) f) ^ 2) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hYsq (by positivity)
    have hsum : ((k + 1 : ℕ) : ℝ) * (Cz * (1 + (Work.Spaces.w z) ^ 2)
          * (1 + Work.Spaces.HkNorm α (k + 2) f) ^ 2)
        + ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) * (Cm * (1 + (Work.Spaces.w z) ^ 2)
          * (1 + Work.Spaces.HkNorm α (k + 2) f) ^ 2))
        = (((k + 1 : ℕ) : ℝ) * Cz + ((k + 1 : ℕ) : ℝ) ^ 2 * Cm)
          * (1 + (Work.Spaces.w z) ^ 2) * (1 + Work.Spaces.HkNorm α (k + 2) f) ^ 2 := by
      ring
    have hstep2 : ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) * (Cm * (1 + (Work.Spaces.w z) ^ 2)
          * Work.Spaces.HkSq α (k + 2) f))
        ≤ ((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) * (Cm * (1 + (Work.Spaces.w z) ^ 2)
          * (1 + Work.Spaces.HkNorm α (k + 2) f) ^ 2)) :=
      mul_le_mul_of_nonneg_left hstep (by positivity)
    refine le_trans (add_le_add le_rfl hstep2) ?_
    rw [hsum]

end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.GalFields.Norm.RadA4.Efun_le_Maj_four =====
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
set_option maxHeartbeats 1600000


end Work.FTS.GalFields.Norm.RadA4
end
end
-- ===== merged: Submission.Work.FTS.GalFields.Norm.RadA4.RadA_Efun_eq_four =====
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

set_option maxHeartbeats 1000000





end Work.FTS.GalFields.Norm.RadA4
end
end
-- ===== merged: Submission.Work.FTS.GalFields.Norm.RadA4.continuousOn_Efun_four =====
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
set_option maxHeartbeats 1600000



end Work.FTS.GalFields.Norm.RadA4
end
end
-- ===== merged: Submission.Work.FTS.IPGen.N4ExtraQ_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `IPGen/N4ExtraQ_zero.lean` — the identically vanishing pairing inhabits `N4ExtraQ`

The contract `Work.FTS.IPGen.N4ExtraQ IP α₂ Ct` is a structure of *inequalities and
identities* about a pairing `IP : ℝ → Fn → Fn → ℝ`, all of whose hypotheses (`HQo`, `RegQ`,
`T2Clause`, `T3Clause`, …) are properties of the arguments only.  Hence the zero pairing
`IP ≡ 0` inhabits it for any positive `Ct`, `α₂`: every identity becomes `0 = 0` (or a
definitional redex), and every inequality becomes `0 ≤` a product of nonnegative factors.

The lemmas below supply the nonnegativity of the latter: `ℋ⁴`-norm, the flat angular norm
`CoefTh`, the `D`-sup norm `WDp`, the `𝒲^{l,∞}`-norm, and the real power `α ^ (-(1/2))` for
`α > 0`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.IPGen

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Nonnegativity of the norms appearing in the contract -/





/-! ## The zero pairing inhabits the contract -/


end Work.FTS.IPGen
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.AngRad.HkMem_ang_rad_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows.AngRad

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Continuity of the `ℋ⁴`-integrand of an angular `×` radial product

Everything below is the *open-quadrant* continuity of
`(z,θ) ↦ HkIntegrand α 4 (fun z θ => a θ * r z) z θ` under the weakest hypotheses that make it
true: the angular iterates `D_θ^i a` are continuous on `(0,π/2)` and the radial iterates
`D_z^b r` are continuous on `(0,∞)`.  (The sibling
`Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand` would need `C^∞` of the *uncurried*
product; the two separation identities `dzIter_ang_rad`/`mixed_ang_rad` make the iterates of the
product into products of the iterates of the factors, so only slice continuity is required.)

The weights are continuous where they are used: `w z = (1+z)²/z²` on `z ≠ 0` and
`sin(2θ)^c` on `(0,π/2)` (where `sin(2θ) > 0`). -/

/-- `(f * g) p = f p * g p` as a `ContinuousOn` statement (the `Pi`-instances are not
definitionally transparent, so the pointwise form is what the piecewise estimates need). -/
private lemma continuousOn_mul_apply {f g : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun p => f p * g p) s :=
  (hf.mul hg).congr (fun p _ => (Pi.mul_apply f g p).symm)

private lemma continuousOn_pow_apply {f : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (hf : ContinuousOn f s) (n : ℕ) :
    ContinuousOn (fun p => f p ^ n) s :=
  (hf.pow n).congr (fun p _ => (Pi.pow_apply f n p).symm)

private lemma continuousOn_w_angrad :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  simp only [Work.Spaces.w]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))

private lemma continuousOn_sinpow_angrad (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt
      (Work.FTS.Nonlinear.RadialProd.sin_two_pos_of_mem_Ioo hp.2)))

private lemma continuousOn_wdivsin_angrad :
    ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
  continuousOn_w_angrad.div (continuousOn_sinpow_angrad (Work.Spaces.eta / 2))
    (fun _p hp => ne_of_gt (Real.rpow_pos_of_pos
      (Work.FTS.Nonlinear.RadialProd.sin_two_pos_of_mem_Ioo hp.2) _))

private lemma continuousOn_Wt_angrad (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  refine (continuousOn_w_angrad.mul (continuousOn_sinpow_angrad (-(Work.Spaces.gam α / 2)))).congr
    (fun p _ => ?_)
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, Pi.mul_apply]

/-- **The `ℋ⁴`-integrand of `a θ · r z` is continuous on the open quadrant**, from the slice
continuity of the angular and radial iterates only. -/
private lemma continuousOn_HkIntegrand_ang_rad_aux (α : ℝ) (a r : ℝ → ℝ)
    (hcontA : ∀ i : ℕ, i ≤ 4 → ContinuousOn
      (fun θ : ℝ => Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) (Set.Ioo 0 (π / 2)))
    (hcontR : ∀ b : ℕ, b ≤ 4 → ContinuousOn
      (fun z : ℝ => Work.Elliptic.DzdIter b r z) (Set.Ioi 0)) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * r z) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hA0 : ContinuousOn (fun θ : ℝ => a θ) (Set.Ioo 0 (π / 2)) :=
    (hcontA 0 (by norm_num)).congr (fun θ _ => by simp)
  have hA : ContinuousOn (fun p : ℝ × ℝ => a p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hA0.comp continuousOn_snd (fun p hp => hp.2)
  have hDzd : ∀ b : ℕ, b ≤ 4 → ContinuousOn
      (fun p : ℝ × ℝ => Work.Elliptic.DzdIter b r p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    fun b hb => (hcontR b hb).comp continuousOn_fst (fun p hp => hp.1)
  have hDth : ∀ i : ℕ, i ≤ 4 → ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.DthIter i (fun _ θ' => a θ') 0 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    fun i hi => (hcontA i hi).comp continuousOn_snd (fun p hp => hp.2)
  refine ContinuousOn.congr (f := fun p : ℝ × ℝ =>
      (∑ i ∈ Finset.range 5, (a p.2 * Work.Elliptic.DzdIter i r p.1
          * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 p.2
                * Work.Elliptic.DzdIter j r p.1 * Work.Spaces.Wt α p.1 p.2) ^ 2
            else 0) ?_ ?_
  · refine ContinuousOn.add ?_ ?_
    · refine continuousOn_finsetSum _ (fun i hi => ?_)
      have h1 : ContinuousOn (fun p : ℝ × ℝ =>
          a p.2 * Work.Elliptic.DzdIter i r p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
        continuousOn_mul_apply hA (hDzd i (by have := Finset.mem_range.mp hi; omega))
      have h2 : ContinuousOn (fun p : ℝ × ℝ =>
          (a p.2 * Work.Elliptic.DzdIter i r p.1)
            * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)))
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
        continuousOn_mul_apply h1 continuousOn_wdivsin_angrad
      exact continuousOn_pow_apply h2 2
    · refine continuousOn_finsetSum _ (fun i hi => continuousOn_finsetSum _ (fun j hj => ?_))
      by_cases h : 1 ≤ i ∧ i + j ≤ 4
      · have hfun : (fun p : ℝ × ℝ =>
            if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 p.2
                * Work.Elliptic.DzdIter j r p.1 * Work.Spaces.Wt α p.1 p.2) ^ 2
            else 0)
            = fun p : ℝ × ℝ =>
              (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 p.2
                * Work.Elliptic.DzdIter j r p.1 * Work.Spaces.Wt α p.1 p.2) ^ 2 := by
          funext p; rw [if_pos h]
        rw [hfun]
        have h1 : ContinuousOn (fun p : ℝ × ℝ =>
            Work.Spaces.DthIter i (fun _ θ' => a θ') 0 p.2
              * Work.Elliptic.DzdIter j r p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
          continuousOn_mul_apply (hDth i (by have := Finset.mem_range.mp hi; omega))
            (hDzd j (by have := Finset.mem_range.mp hj; omega))
        have h2 : ContinuousOn (fun p : ℝ × ℝ =>
            (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 p.2
              * Work.Elliptic.DzdIter j r p.1) * Work.Spaces.Wt α p.1 p.2)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
          continuousOn_mul_apply h1 (continuousOn_Wt_angrad α)
        exact continuousOn_pow_apply h2 2
      · have hfun : (fun p : ℝ × ℝ =>
            if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 p.2
                * Work.Elliptic.DzdIter j r p.1 * Work.Spaces.Wt α p.1 p.2) ^ 2
            else 0) = fun _ : ℝ × ℝ => (0 : ℝ) := by
          funext p; rw [if_neg h]
        rw [hfun]
        exact continuousOn_const
  · intro p _hp
    simp only [Work.Spaces.HkIntegrand, Work.FTS.Nonlinear.Pieces.dzIter_ang_rad,
      Work.FTS.Nonlinear.Pieces.mixed_ang_rad]

-- `angular × radial` honesty of the weighted space `ℋ⁴`.
--
-- Let `a : ℝ → ℝ` be an angular profile bounded by `B0` whose `D_θ`-iterates of orders `1..4`
-- are bounded by `B1 · G`, and let `r : ℝ → ℝ` be radial with radial lift in `ℋ⁴`.  If the
-- angular iterates are continuous on `(0,π/2)` and the radial iterates `DzdIter b r`, `b ≤ 4`,
-- are continuous on `(0,∞)`, and if `G²·smG α` and `smE` are integrable on `Iθ`, then the
-- product `(z,θ) ↦ a θ · r z` lies in `ℋ⁴`.
--
-- PROOF RECIPE (all ingredients exist in the workspace):
-- * the *unconditional* identities `Work.FTS.Nonlinear.Pieces.dzIter_ang_rad` and
--   `Work.FTS.Nonlinear.Pieces.mixed_ang_rad` (`Submission/Work/FTS/Nonlinear/Pieces/rowsN0Q.lean`)
--   rewrite `DzIter i (a·r) z θ = a θ * DzdIter i r z` and
--   `mixed j i (a·r) z θ = DthIter i (fun _ θ' => a θ') 0 θ * DzdIter j r z`, with no
--   smoothness hypothesis;
-- * `Work.FTS.Nonlinear.RadialProd.light_sq` / `heavy_sq` turn the two weights into
--   `smE θ = sin(2θ)^(-η)` and `smG α θ = sin(2θ)^(-γ)`, giving, on the open quadrant,
--   `HkIntegrand α 4 (fun z θ => a θ * r z) z θ ≤ Rint r z * (B0^2 * smE θ + 4 * B1^2 * G θ^2 * smG α θ)`
--   (`Work.FTS.Nonlinear.RadialProd.Rint`); the mixed slots with a fixed `i` sum over `j ≤ 3`,
--   which `Rint r z` (a sum over `j ≤ 4`) dominates, and there are four `i`-values, whence the
--   coefficient `4`;
-- * continuity of `HkIntegrand α 4 (a·r)` on the open quadrant follows from the two `ContinuousOn`
--   hypotheses by the same pattern as `Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand`
--   (the weights `w` and `Wt α` are continuous there);
-- * conclude with `Work.FTS.LocData.HkMem_of_majorant` (or the a.e. variant
--   `Work.FTS.CoercivityFix.Assembly.HkMem_of_majorant_ae`, which only asks for the domination on
--   `Ioo 0 (π/2)`): the majorant's `θ`-slices are integrable by `hI1`, `hI2`, its `z`-integral
--   `Rint r z * (B0^2 * ∫ smE + 4 * B1^2 * ∫ G^2 smG)` is integrable by
--   `Work.FTS.Nonlinear.RadialProd.integrable_Rint` applied to `hrmem`.
theorem HkMem_ang_rad_le {α : ℝ} {a : ℝ → ℝ} {r : ℝ → ℝ} {B0 B1 : ℝ} {G : ℝ → ℝ}
    (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1)
    (hGnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ G θ)
    (ha0 : ∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ B0)
    (ha1 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ| ≤ B1 * G θ)
    (hI1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ)
    (hI2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.FTS.Nonlinear.RadialProd.smE θ) Work.Spaces.Iθ)
    (hrmem : Work.Spaces.HkMem α 4 (fun z θ => r z))
    (hcontA : ∀ i : ℕ, i ≤ 4 → ContinuousOn
      (fun θ : ℝ => Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) (Set.Ioo 0 (π / 2)))
    (hcontR : ∀ b : ℕ, b ≤ 4 → ContinuousOn
      (fun z : ℝ => Work.Elliptic.DzdIter b r z) (Set.Ioi 0)) :
    Work.Spaces.HkMem α 4 (fun z θ => a θ * r z) := by
  -- the pointwise domination holds on the whole *closed* angular interval `Iθ` (existing
  -- lemma), and the majorant has integrable `θ`-slices and integrable `θ`-integral
  have hmaj := Work.FTS.NonlinRows.AuxAngRad.angRad_majorant_integrable (α := α) (r := r)
    (G := G) (B0 := B0) (B1 := B1) hI1 hrmem
  refine Work.FTS.LocData.HkMem_of_majorant α 4 (f := fun z θ => a θ * r z)
    (M := fun z θ => Work.FTS.Nonlinear.RadialProd.Rint r z
      * (B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
          + 4 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)) ?_ ?_ ?_ ?_
  · exact continuousOn_HkIntegrand_ang_rad_aux α a r hcontA hcontR
  · exact hmaj.1
  · exact hmaj.2
  · intro z _hz θ hθ
    exact Work.FTS.NonlinRows.AuxAngRad.HkIntegrand_ang_rad_le ha0 ha1 hθ

end Work.FTS.NonlinRows.AngRad
end
-- ===== merged: Submission.Work.FTS.NonlinRows.AuxAngRad.HkMem_ang_rad =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows.AuxAngRad

/-! ## Honesty in `ℋ⁴` of an angular `×` radial product

`HkMem α 4 (fun z θ => a θ * r z)` for an angular profile `a` whose `D_θ`-iterates are
dominated by `B1 · G` and a radial function `r ∈ ℋ⁴`: the `ℋ⁴`-integrand of the product is
dominated pointwise (on the whole closed angular interval `Iθ`) by

`Rint r z * (B0² σ(θ) + 4 B1² G(θ)² τ(α,θ))`,

with `σ = smE`, `τ = smG` the two angular weights and `Rint r` the radial density of the
`ℋ⁴`-norm.  `σ` is integrable on `Iθ` and `G² τ` is integrable by hypothesis, so the slices
of the majorant are integrable; integrating in `θ` leaves the constant
`B0² ∫σ + 4 B1² ∫G²τ` times `Rint r z`, which is integrable in `z` because
`∫_θ HkIntegrand α 4 r z θ = Rint r z · Kth` with `Kth ≥ 1` and `r ∈ ℋ⁴`.

Continuity of the integrand on the open quadrant (needed to make the slices measurable and
to apply Fubini's measurability theorem) is inherited from `SmoothOpen` of the two factors.
The two ingredients are `HkIntegrand_ang_rad_le` (pointwise domination) and
`angRad_majorant_integrable` (integrability of the majorant); the assembly is
`HkMem_of_majorant`. -/

theorem HkMem_ang_rad {α : ℝ} {a : ℝ → ℝ} {r : ℝ → ℝ} {G : ℝ → ℝ} {B0 B1 : ℝ}
    (ha : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ))
    (hr : Work.FTS.EllipticEst.SmoothOpen (fun z _ => r z))
    (hGnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ G θ)
    (hGint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ)
    (ha0 : ∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ B0)
    (ha1 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ B1 * G θ)
    (hrmem : Work.Spaces.HkMem α 4 (fun z _ => r z)) :
    Work.Spaces.HkMem α 4 (fun z θ => a θ * r z) := by
  -- The product datum is `C^∞` on the open quadrant, hence its `ℋ⁴`-integrand is continuous
  -- there (this is what makes the `θ`-slices and their `z`-integral measurable).
  have hsmooth : Work.FTS.EllipticEst.SmoothOpen (fun z θ => a θ * r z) :=
    smoothOpen_ang_rad ha hr
  -- The majorant `M z θ = Rint r z * (B0² σ θ + 4 B1² G(θ)² τ α θ)` has integrable slices and
  -- an integrable slice-integral.
  have hmaj := angRad_majorant_integrable (α := α) (r := r) (G := G) (B0 := B0) (B1 := B1)
    hGint hrmem
  refine Work.FTS.LocData.HkMem_of_majorant α 4 (f := fun z θ => a θ * r z)
    (M := fun z θ => Work.FTS.Nonlinear.RadialProd.Rint r z
      * (B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
          + 4 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)) ?_ ?_ ?_ ?_
  · exact hsmooth.continuousOn_HkIntegrand α 4
  · exact hmaj.1
  · exact hmaj.2
  · intro z _ θ hθ
    exact HkIntegrand_ang_rad_le ha0 ha1 hθ

end Work.FTS.NonlinRows.AuxAngRad
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.row15_pzIter_tendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

set_option autoImplicit false

/-! ## `C^∞`-regularity of `𝒰` and of its `z`-jets on the open quadrant -/



/-! ## The Clairaut identity `∂_θ ∂_z^m = ∂_z^m ∂_θ` on the open quadrant -/


/-! ## A Lipschitz function on `(0,π/2)` has a limit at `0⁺` -/


/-! ## The statement -/


end Work.FTS.Nonlinear.Pieces.RNP.row15aux
end
end
-- ===== merged: Submission.Work.FTS.OpenPkg.l12H_field =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

set_option linter.unusedVariables false

theorem l12H_field :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ g : Work.FTS.Galerkin.Fn,
      Work.FTS.VocabO.HQo α 4 g → Work.Construction.L12 g 0 = 0 →
      Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 g z) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 g z)
        ≤ C * Work.FTS.Nonlin.Xn α g := by
  -- the two universal constants `∫_θ K²` and `∫_θ sin(2θ)^{-η}`
  set AK : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 with hAKdef
  set Cθ : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hCθdef
  have hAKnn : 0 ≤ AK := by
    rw [hAKdef]
    exact setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  have hCθnn : 0 ≤ Cθ := by
    rw [hCθdef]
    exact setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => Real.rpow_nonneg (Work.Elliptic.sin_two_nonneg_of_mem hθ) _)
  refine ⟨Real.sqrt (111 * AK * Cθ) + 1, ?_, ?_⟩
  · have h := Real.sqrt_nonneg (111 * AK * Cθ)
    linarith
  intro α hαpos hα1 g hg h0
  obtain ⟨hsm, hmem⟩ := hg
  have h0e : Work.Elliptic.L12 g 0 = 0 := by
    rw [← Work.FTS.H2.constructionL12_eq_ellipticL12 g]
    exact h0
  obtain ⟨hgen, hInt0, hBnd0⟩ := l12_open_bundle α g hαpos hα1 hsm hmem h0e
  set u : ℝ → ℝ := fun z => Work.Elliptic.L12 g z with hudef
  have hgen' : ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter (k + 1) u z = - Work.Elliptic.Qang g k z := by
    intro k hk z hz
    rw [hudef]
    exact hgen k hk z hz
  -- ## the a.e. transfer `D_z^i (L₁₂ g) = -Qang g (i-1)` on `Iz`, `1 ≤ i ≤ 4`
  have htrans : ∀ i : ℕ, 1 ≤ i → i ≤ 4 →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (Work.Elliptic.Qang g (i - 1) z) ^ 2 * (Work.Spaces.w z) ^ 2
          = (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    intro i hi hi4
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
    filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (0 : ℝ)] with z hz0 hzI
    have hzpos : 0 < z := lt_of_le_of_ne hzI (Ne.symm hz0)
    have hsub : i - 1 ≤ 3 := by omega
    have key : Work.Elliptic.DzdIter i u z = - Work.Elliptic.Qang g (i - 1) z := by
      have h := hgen' (i - 1) hsub z hzpos
      rwa [show i - 1 + 1 = i by omega] at h
    rw [key, neg_sq]
  -- ## integrability of every weighted slot
  have hInt : ∀ i : ℕ, i ≤ 4 → MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
    intro i hi4
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      simpa only [hudef, Work.Elliptic.DzdIter_zero] using hInt0
    · exact (Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open hαpos hα1 hsm hmem
        (i := i - 1) (by omega)).1.congr (htrans i h hi4)
  have hsum_int : ∀ i ∈ Finset.range 5, MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    fun i hi => hInt i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  -- ## the bounds of the individual slots
  have hBnd0' : (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter 0 u z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 107 * (AK * Work.Spaces.HkSq α 4 g) := by
    have hb : (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter 0 u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ 107 * (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.Qang g 0 z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      simpa only [hudef, Work.Elliptic.DzdIter_zero] using hBnd0
    have hQ := (Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open hαpos hα1 hsm hmem
      (i := 0) (by norm_num)).2
    rw [← hAKdef] at hQ
    exact le_trans hb (mul_le_mul_of_nonneg_left hQ (by norm_num))
  have hBndI : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → (∫ z in Work.Spaces.Iz,
        (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ AK * Work.Spaces.HkSq α 4 g := by
    intro i hi hi4
    rw [hAKdef, ← MeasureTheory.integral_congr_ae (htrans i hi hi4)]
    exact (Work.FTS.OpenPkg.QangOpen.Qang_sq_w_sq_integral_open hαpos hα1 hsm hmem
      (i := i - 1) (by omega)).2
  -- ## the sum of the slots
  have hsum_le : (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range 5,
        (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 111 * (AK * Work.Spaces.HkSq α 4 g) := by
    rw [MeasureTheory.integral_finsetSum (Finset.range 5) hsum_int,
      Finset.sum_range_succ']
    have h4 : (∑ i ∈ Finset.range 4, (∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter (i + 1) u z) ^ 2 * (Work.Spaces.w z) ^ 2))
        ≤ ∑ _i ∈ Finset.range 4, AK * Work.Spaces.HkSq α 4 g :=
      Finset.sum_le_sum fun i hi => by
        rw [Finset.mem_range] at hi
        exact hBndI (i + 1) (by omega) (by omega)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h4
    refine le_trans (add_le_add h4 hBnd0') (le_of_eq ?_)
    ring
  -- ## the energy
  have hHkSq : Work.Spaces.HkSq α 4 (fun z θ => u z)
      = (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range 5,
          (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) * Cθ := by
    rw [Work.Elliptic.HkSq_rad, hCθdef]
  have hbound : Work.Spaces.HkSq α 4 (fun z θ => u z)
      ≤ (111 * AK * Cθ) * Work.Spaces.HkSq α 4 g := by
    rw [hHkSq]
    refine le_trans (mul_le_mul_of_nonneg_right hsum_le hCθnn) (le_of_eq ?_)
    ring
  have hXng : 0 ≤ Work.FTS.Nonlin.Xn α g := Real.sqrt_nonneg _
  have hXn : Work.FTS.Nonlin.Xn α (fun z θ => u z)
      ≤ Real.sqrt (111 * AK * Cθ) * Work.FTS.Nonlin.Xn α g := by
    have h111 : 0 ≤ 111 * AK * Cθ := by nlinarith
    calc Work.FTS.Nonlin.Xn α (fun z θ => u z)
        = Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => u z)) := rfl
      _ ≤ Real.sqrt ((111 * AK * Cθ) * Work.Spaces.HkSq α 4 g) := Real.sqrt_le_sqrt hbound
      _ = Real.sqrt (111 * AK * Cθ) * Work.FTS.Nonlin.Xn α g := by
          rw [Real.sqrt_mul h111]
          rfl
  -- ## membership in `ℋ⁴`
  have hsinI : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by rw [Work.Spaces.eta]; norm_num)
      (by rw [Work.Spaces.eta]; norm_num)).1
  have hHkMem : Work.Spaces.HkMem α 4 (fun z θ => u z) := by
    constructor
    · intro z _
      refine MeasureTheory.Integrable.congr (f := fun θ =>
        (∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ?_ ?_
      · exact hsinI.const_mul _
      · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => (Work.FTS.H2.HkIntegrand_rad' α 4 u z hθ).symm)
    · refine MeasureTheory.Integrable.congr (f := fun z =>
        (∑ i ∈ Finset.range 5, (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * Cθ) ?_ ?_
      · exact (MeasureTheory.integrable_finsetSum (Finset.range 5) hsum_int).mul_const Cθ
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z _ => ?_)
        simp only [Work.Spaces.Iθ, hCθdef]
        rw [setIntegral_congr_fun (f := fun θ => Work.Spaces.HkIntegrand α 4 (fun z θ => u z) z θ)
          (g := fun θ => (∑ i ∈ Finset.range 5,
              (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          measurableSet_Icc (fun θ hθ => Work.FTS.H2.HkIntegrand_rad' α 4 u z hθ)]
        rw [MeasureTheory.integral_const_mul]
  -- ## back to `Work.Construction.L12`
  have hfun : (fun z (_ : ℝ) => Work.Construction.L12 g z) = (fun z (_ : ℝ) => u z) := by
    funext z θ
    rw [hudef]
    exact congrFun (Work.FTS.H2.constructionL12_eq_ellipticL12 g) z
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hHkMem
  · rw [hfun]
    exact le_trans hXn
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hXng)

end Work.FTS.OpenPkg
end
end
-- ===== merged: Submission.Work.FTS.OpenPkg.wprod_field_winf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- `√(x⁻¹) = x^(-1/2)` for `x > 0`. -/
theorem sqrt_inv_eq_rpow_neg_half {x : ℝ} (hx : 0 < x) :
    Real.sqrt x⁻¹ = x ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul hx.le]
  congr 1
  ring

/-- **The pointwise majorant of the `𝒲^{4,∞}`-priced product rule.**

Summing the five pure `D_z`-slots (`hzslot`) and the at most 25 mixed slots (`hmslot`) of
`HkIntegrand α 4 (f·g)`, using `HkIntegrand α 4 g ≤ GmajW α g`. -/
theorem prod_majorant_winf {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hfm : Work.Spaces.WlInfMem α 4 f)
    (hgsm : Work.FTS.EllipticEst.SmoothOpen g) (hgm : Work.Spaces.HkMem α 4 g)
    {Cz Cm : ℝ} (hCz0 : 0 < Cz) (hCm0 : 0 < Cm)
    (hzslot : ∀ i : ℕ, i ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Cz * (Work.Spaces.WlInf α 4 f) ^ 2 * Work.Spaces.HkIntegrand α 4 g z θ)
    (hmslot : ∀ I J : ℕ, 1 ≤ I → I + J ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 →
      (Work.Spaces.mixed J I (fun z θ => f z θ * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Cm * (Work.Spaces.WlInf α 4 f) ^ 2 * WProdWin.GmajW α g z θ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (fun z θ => f z θ * g z θ) z θ
        ≤ (5 * Cz + 25 * Cm) * (Work.Spaces.WlInf α 4 f) ^ 2 * WProdWin.GmajW α g z θ := by
  intro z hz θ hθ
  have hGnn : 0 ≤ WProdWin.GmajW α g z θ := WProdWin.GmajW_nonneg hα g hθ
  have hbase : 0 ≤ (5 * Cz + 25 * Cm) * (Work.Spaces.WlInf α 4 f) ^ 2
      * WProdWin.GmajW α g z θ :=
    mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) hGnn
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hzz | hzpos
  · have hz0 : z = 0 := hzz.symm
    subst hz0
    rw [Work.Spaces.HkIntegrand_zero_z]
    exact hbase
  · by_cases hθi : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
    · have hGle : Work.Spaces.HkIntegrand α 4 g z θ ≤ WProdWin.GmajW α g z θ :=
        WProdWin.HkIntegrand_le_GmajW hα g hθ
      have hsum1 : (∑ i ∈ Finset.range (4 + 1),
            (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ 5 * (Cz * (Work.Spaces.WlInf α 4 f) ^ 2 * WProdWin.GmajW α g z θ) := by
        calc (∑ i ∈ Finset.range (4 + 1),
              (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
            ≤ ∑ _i ∈ Finset.range (4 + 1), (Cz * (Work.Spaces.WlInf α 4 f) ^ 2
                * WProdWin.GmajW α g z θ) := by
              refine Finset.sum_le_sum fun i hi => ?_
              have hi4 : i ≤ 4 := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
              refine le_trans (hzslot i hi4 z θ hzpos hθi.1 hθi.2) ?_
              exact mul_le_mul_of_nonneg_left hGle (mul_nonneg (le_of_lt hCz0) (sq_nonneg _))
          _ = 5 * (Cz * (Work.Spaces.WlInf α 4 f) ^ 2 * WProdWin.GmajW α g z θ) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
      have hsum2 : (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
            (if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ 25 * (Cm * (Work.Spaces.WlInf α 4 f) ^ 2 * WProdWin.GmajW α g z θ) := by
        calc (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
              (if 1 ≤ i ∧ i + j ≤ 4 then
                (Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ
                  * Work.Spaces.Wt α z θ) ^ 2 else 0))
            ≤ ∑ _i ∈ Finset.range (4 + 1), ∑ _j ∈ Finset.range (4 + 1),
                (Cm * (Work.Spaces.WlInf α 4 f) ^ 2 * WProdWin.GmajW α g z θ) := by
              refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
              by_cases hc : 1 ≤ i ∧ i + j ≤ 4
              · rw [if_pos hc]
                exact hmslot i j hc.1 hc.2 z θ hzpos hθi.1 hθi.2
              · rw [if_neg hc]
                exact mul_nonneg (mul_nonneg (le_of_lt hCm0) (sq_nonneg _)) hGnn
          _ = 25 * (Cm * (Work.Spaces.WlInf α 4 f) ^ 2 * WProdWin.GmajW α g z θ) := by
              simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      rw [Work.Spaces.HkIntegrand]
      calc (∑ i ∈ Finset.range (4 + 1),
            (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
              (if 1 ≤ i ∧ i + j ≤ 4 then
                (Work.Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ
                  * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ 5 * (Cz * (Work.Spaces.WlInf α 4 f) ^ 2 * WProdWin.GmajW α g z θ)
            + 25 * (Cm * (Work.Spaces.WlInf α 4 f) ^ 2 * WProdWin.GmajW α g z θ) :=
            add_le_add hsum1 hsum2
        _ = (5 * Cz + 25 * Cm) * (Work.Spaces.WlInf α 4 f) ^ 2 * WProdWin.GmajW α g z θ := by
            ring
    · have hsin : Real.sin (2 * θ) = 0 := Work.Spaces.sin_two_eq_zero_of_not_Ioo hθ hθi
      rw [Work.FTS.H2.WPQ.HkIntegrand_eq_zero_of_sin_two_eq_zero
        (F := fun z θ => f z θ * g z θ) (by rw [Work.Spaces.gam]; linarith) hsin]
      exact hbase

theorem wprod_field_winf :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f g : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 4 f →
      Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g := by
  obtain ⟨Cz, hCz0, hzslot⟩ := WProdWin.zslot_le_winf
  obtain ⟨CB, hCB0, hCmean⟩ := WProdWin.dzIter_w_mean_le
  obtain ⟨Cm, hCm0, hmslot⟩ := WProdWin.mslot_le_winf CB
  refine ⟨Real.sqrt (28701 * (5 * Cz + 25 * Cm)), Real.sqrt_pos.mpr (by linarith), ?_⟩
  intro α hα hα1 f g hf hfm hg
  obtain ⟨hgsm, hgm⟩ := hg
  set K : ℝ := 5 * Cz + 25 * Cm with hKdef
  set Kg : ℝ := 1 + 700 * (1 + 4 * (Work.Spaces.gam α - 1)⁻¹) with hKgdef
  have hKpos : 0 < K := by rw [hKdef]; linarith
  have hKgpos : 0 < Kg := by
    rw [hKgdef]
    have h1 : (0 : ℝ) < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
    have h2 : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ := inv_nonneg.mpr h1.le
    linarith
  have hWnn : 0 ≤ Work.Spaces.WlInf α 4 f := Work.FTS.H2.WPQ.WlInf_nonneg' hfm
  -- the product is smooth on the open quadrant
  have hfgsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) :=
    hf.mul hgsm
  -- the pointwise majorant, with the two slot lemmas instantiated
  have hmajor : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (fun z θ => f z θ * g z θ) z θ
        ≤ K * (Work.Spaces.WlInf α 4 f) ^ 2 * WProdWin.GmajW α g z θ := by
    have h := prod_majorant_winf hα hα1 hf hfm hgsm hgm hCz0 hCm0
      (fun i hi z θ hz hθ1 hθ2 => hzslot α f g hα hα1 hf hfm hgsm i hi z θ hz hθ1 hθ2)
      (fun I J hI hIJ z θ hz hθ1 hθ2 =>
        hmslot α f g hα hα1 hf hfm hgsm hgm
          (fun d hd z' θ' hz' hθ1' hθ2' => hCmean α g d hα hα1 hgsm hgm hd z' θ' hz' hθ1' hθ2')
          I J hI hIJ z θ hz hθ1 hθ2)
    intro z hz θ hθ
    rw [hKdef]
    exact h z hz θ hθ
  -- integrability of the angular slices of the product's integrand
  have hslice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4
      (fun z θ => f z θ * g z θ) z θ) Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hzz | hzpos
    · have hz0 : z = 0 := hzz.symm
      subst hz0
      have hzero : (fun θ => Work.Spaces.HkIntegrand α 4 (fun z θ => f z θ * g z θ) 0 θ)
          = fun _ : ℝ => (0 : ℝ) :=
        funext fun θ => Work.Spaces.HkIntegrand_zero_z α 4 _ θ
      rw [hzero]
      exact integrableOn_zero
    · refine Integrable.mono'
        ((WProdWin.GmajW_integrableOn_theta hα hα1 hgm hz).const_mul (K
          * (Work.Spaces.WlInf α 4 f) ^ 2)) ?_ ?_
      · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _
          (hfgsm.continuousOn_HkIntegrand α 4) hzpos
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
        rw [Real.norm_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)]
        exact hmajor z hz θ hθ
  -- the angular integral of the majorant at every radius
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (fun z θ => f z θ * g z θ) z θ)
        ≤ K * (Work.Spaces.WlInf α 4 f) ^ 2 * (Kg * WProdWin.HgInt α g z) := by
    intro z hz
    have hint : IntegrableOn (fun θ => (K * (Work.Spaces.WlInf α 4 f) ^ 2)
        * WProdWin.GmajW α g z θ) Work.Spaces.Iθ :=
      (WProdWin.GmajW_integrableOn_theta hα hα1 hgm hz).const_mul _
    have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
          (fun z θ => f z θ * g z θ) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, (K * (Work.Spaces.WlInf α 4 f) ^ 2)
            * WProdWin.GmajW α g z θ :=
      integral_mono_of_nonneg
        (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 _ z θ) hint
        (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hmajor z hz θ hθ))
    rw [MeasureTheory.integral_const_mul] at h1
    have h2 : (∫ θ in Work.Spaces.Iθ, WProdWin.GmajW α g z θ)
        ≤ Kg * WProdWin.HgInt α g z := by
      simpa only [hKgdef] using WProdWin.GmajW_theta_integral_le hα hα1 hgm hz
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
          (fun z θ => f z θ * g z θ) z θ)
        ≤ (K * (Work.Spaces.WlInf α 4 f) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, WProdWin.GmajW α g z θ) := h1
      _ ≤ (K * (Work.Spaces.WlInf α 4 f) ^ 2) * (Kg * WProdWin.HgInt α g z) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hKpos.le (sq_nonneg _))
  -- the dominating function of the `z`-integral
  have hbdd : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (fun z θ => f z θ * g z θ) z θ)
        ≤ (K * (Work.Spaces.WlInf α 4 f) ^ 2 * Kg) * WProdWin.HgInt α g z := by
    intro z hz
    have h1 := hinner z hz
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
          (fun z θ => f z θ * g z θ) z θ)
        ≤ K * (Work.Spaces.WlInf α 4 f) ^ 2 * (Kg * WProdWin.HgInt α g z) := h1
      _ = (K * (Work.Spaces.WlInf α 4 f) ^ 2 * Kg) * WProdWin.HgInt α g z := by ring
  have hdom : IntegrableOn (fun z => (K * (Work.Spaces.WlInf α 4 f) ^ 2 * Kg)
      * WProdWin.HgInt α g z) Work.Spaces.Iz :=
    hgm.2.const_mul (K * (Work.Spaces.WlInf α 4 f) ^ 2 * Kg)
  -- a.e. strong measurability of the `z`-slice integral
  have haesm : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (fun z θ => f z θ * g z θ) z θ)
      (volume.restrict Work.Spaces.Iz) := by
    have h := (Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 (fun z θ => f z θ * g z θ) p.1 p.2)
      (hfgsm.continuousOn_HkIntegrand α 4)).integral_prod_right'
    have hfun : (fun z => ∫ θ, Work.Spaces.HkIntegrand α 4 (fun z θ => f z θ * g z θ) z θ
          ∂(volume.restrict Work.Spaces.Iθ))
        = (fun z => ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 4 (fun z θ => f z θ * g z θ) z θ) := rfl
    rw [← hfun]
    exact h
  have hzg : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (fun z θ => f z θ * g z θ) z θ) Work.Spaces.Iz := by
    refine Integrable.mono' hdom haesm ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)]
      with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)]
    exact hbdd z hz
  refine ⟨⟨hslice, hzg⟩, ?_⟩
  have hSq : Work.Spaces.HkSq α 4 (fun z θ => f z θ * g z θ)
      ≤ (K * (Work.Spaces.WlInf α 4 f) ^ 2 * Kg) * Work.Spaces.HkSq α 4 g := by
    have h1 : Work.Spaces.HkSq α 4 (fun z θ => f z θ * g z θ)
        ≤ ∫ z in Work.Spaces.Iz, (K * (Work.Spaces.WlInf α 4 f) ^ 2 * Kg)
            * WProdWin.HgInt α g z := by
      rw [Work.Spaces.HkSq]
      exact setIntegral_mono_of_nonneg
        (fun z _ => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)
        (fun z hz => hbdd z hz) hdom
    refine le_trans h1 ?_
    rw [MeasureTheory.integral_const_mul, WProdWin.HgInt_z_integral]
  -- the passage to the `ℋ⁴`-norm
  have hXn : Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
      ≤ Real.sqrt (K * Kg) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g := by
    have h1 : Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => f z θ * g z θ))
        ≤ Real.sqrt ((K * Kg) * (Work.Spaces.WlInf α 4 f) ^ 2 * Work.Spaces.HkSq α 4 g) := by
      refine Real.sqrt_le_sqrt ?_
      calc Work.Spaces.HkSq α 4 (fun z θ => f z θ * g z θ)
          ≤ (K * (Work.Spaces.WlInf α 4 f) ^ 2 * Kg) * Work.Spaces.HkSq α 4 g := hSq
        _ = (K * Kg) * (Work.Spaces.WlInf α 4 f) ^ 2 * Work.Spaces.HkSq α 4 g := by ring
    refine le_trans h1 ?_
    rw [show Work.FTS.Nonlin.Xn α g = Real.sqrt (Work.Spaces.HkSq α 4 g) from rfl,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (K * Kg) * (Work.Spaces.WlInf α 4 f) ^ 2),
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ K * Kg),
      Real.sqrt_sq hWnn]
  refine le_trans hXn ?_
  -- `√(K Kg) ≤ √(28701 K) α^{-1/2}`
  have hKg_le : Kg ≤ 28701 * α⁻¹ := by
    have h1 : (0 : ℝ) < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
    have hginv : (Work.Spaces.gam α - 1)⁻¹ = 10 / α := by
      rw [Work.Spaces.gam_sub_one, inv_div]
    have hαinv : (1 : ℝ) ≤ α⁻¹ := by rw [one_le_inv₀ hα]; exact hα1
    rw [hKgdef, hginv, div_eq_mul_inv]
    ring_nf
    nlinarith [hαinv]
  have hsqrt : Real.sqrt (K * Kg) ≤ Real.sqrt (28701 * K) * α ^ (-(1 / 2 : ℝ)) := by
    have h1 : K * Kg ≤ 28701 * K * α⁻¹ := by
      calc K * Kg ≤ K * (28701 * α⁻¹) := mul_le_mul_of_nonneg_left hKg_le hKpos.le
        _ = 28701 * K * α⁻¹ := by ring
    refine le_trans (Real.sqrt_le_sqrt h1) ?_
    rw [show (28701 : ℝ) * K * α⁻¹ = (28701 * K) * α⁻¹ from by ring,
      Real.sqrt_mul (show (0 : ℝ) ≤ 28701 * K by positivity),
      sqrt_inv_eq_rpow_neg_half hα]
  have hmain : Real.sqrt (K * Kg) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g
      ≤ Real.sqrt (28701 * K) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f
        * Work.FTS.Nonlin.Xn α g := by
    calc Real.sqrt (K * Kg) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g
        = Real.sqrt (K * Kg) * (Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g) := by ring
      _ ≤ (Real.sqrt (28701 * K) * α ^ (-(1 / 2 : ℝ)))
            * (Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g) :=
          mul_le_mul_of_nonneg_right hsqrt (mul_nonneg hWnn (Real.sqrt_nonneg _))
      _ = Real.sqrt (28701 * K) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f
            * Work.FTS.Nonlin.Xn α g := by ring
  calc Real.sqrt (K * Kg) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g
      ≤ Real.sqrt (28701 * K) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f
          * Work.FTS.Nonlin.Xn α g := hmain
    _ = Real.sqrt (28701 * (5 * Cz + 25 * Cm)) * α ^ (-(1 / 2 : ℝ))
          * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g := by
        rw [hKdef]

end Work.FTS.OpenPkg
end
end
-- ===== merged: Submission.Work.FTS.OpenPkg.wtoh_field_winf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **`W^{4,∞}` controls `ℋ⁴` in the open-quadrant class.**  This is the `wtoh` field of
`Work.FTS.OpenPkg.N4Norm'` (Elgindi's `WtoH`, tex 1237) with the interior class
`Work.FTS.EllipticEst.SmoothOpen` in place of `SmoothQuad` and without the `ℋ⁴`-honesty
hypothesis on `f`. -/
theorem wtoh_field_winf :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) →
      Work.FTS.Nonlin.Xn α f
        ≤ C * Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) := by
  refine ⟨10 ^ 10, by norm_num, ?_⟩
  intro α hα hα1 f hsm hmem
  have hΛ : 0 ≤ Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) := by
    rw [Work.Spaces.WlInf]
    exact add_nonneg (Work.Spaces.wlZSum_nonneg α 4 _ hmem)
      (Work.Spaces.wlThSum_nonneg α 4 _ hmem)
  have hA := WtohWin.wtoh_radial_open (α := α) (f := f) hα hα1 hsm hmem
  have hB := WtohWin.wtoh_mixed_open (α := α) (f := f) hα hα1 hsm hmem
  exact WtohWin.wtoHQ_pointwise_open hα hα1 hΛ hsm hA hB

end Work.FTS.OpenPkg
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.ClassCRHS.AngSlotBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.ClassCRHS

/-!
# Angular slot bounds for the two `F_*`-angular profiles

`SA0 α = αΓ/c` and `SA1 α = α D_θΓ/c` are the two angular profiles of the scaled
`F_*`-atoms (`StarAux`).  We prove that, uniformly for `α ∈ (0,1]`, both are bounded by a
constant `B0`, and that all their `D_θ`-iterates of order `1 ≤ i ≤ 4` are bounded by
`B1 · SGmj α θ = B1 · Γ(θ)(α + sin 2θ)`.

The only input is the sharp angular jet bound `RNP.dthU_pow_Gam_sharp`
(`|D_θ^m Γ| ≤ C α Γ (α + sin 2θ)` for `2 ≤ m ≤ 5`) together with the first-order bound
`RNP.dthIter_one_Gam_le`, plus `1/10 ≤ c ≤ 10` (`Spaces.c_bounds`) and `0 ≤ Γ ≤ 1` on `Iθ`
(`Spaces.Gam_bounds`).
-/

/-- `sin (2θ) ≥ 0` on `Iθ = [0, π/2]`. -/
lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  refine Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], ?_⟩
  linarith [hθ.2]

/-- The `D_θ`-iterates of the `θ`-only function `SA0 α` are `(α/c)` times those of `Γ`. -/
lemma DthIter_SA0_repr (α : ℝ) (i : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter i (fun _ (θ' : ℝ) => SA0 α θ') z θ
      = (α / Work.Spaces.c α) * Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ := by
  have hfun : (fun t : ℝ => SA0 α t)
      = (fun t : ℝ => (α / Work.Spaces.c α) * (fun s => Work.Spaces.Gam α s) t) := by
    funext t
    show α * (fun s => Work.Spaces.Gam α s) t / Work.Spaces.c α
        = (α / Work.Spaces.c α) * (fun s => Work.Spaces.Gam α s) t
    ring
  rw [Work.FTS.LocData.DthIter_rad_eq i (fun θ' => SA0 α θ') z θ, hfun,
    Work.Spaces.dthU_iter_const_mul i (α / Work.Spaces.c α) (fun s => Work.Spaces.Gam α s)]

/-- The `D_θ`-iterates of `SA1 α = (α/c) D_θΓ` are `(α/c)` times those of `Γ`, shifted by one. -/
lemma DthIter_SA1_repr (α : ℝ) (i : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter i (fun _ (θ' : ℝ) => SA1 α θ') z θ
      = (α / Work.Spaces.c α) * Work.Spaces.dthU^[i + 1] (fun t => Work.Spaces.Gam α t) θ := by
  have hfun : (fun t : ℝ => SA1 α t)
      = (fun t : ℝ => (α / Work.Spaces.c α)
          * Work.Spaces.dthU (fun s => Work.Spaces.Gam α s) t) := by
    funext t
    show α * Work.Spaces.dthU (fun s => Work.Spaces.Gam α s) t / Work.Spaces.c α
        = (α / Work.Spaces.c α) * Work.Spaces.dthU (fun s => Work.Spaces.Gam α s) t
    ring
  rw [Work.FTS.LocData.DthIter_rad_eq i (fun θ' => SA1 α θ') z θ, hfun,
    Work.Spaces.dthU_iter_const_mul i (α / Work.Spaces.c α)
      (Work.Spaces.dthU (fun s => Work.Spaces.Gam α s)),
    Work.Spaces.dthU_iter_comp i (fun s => Work.Spaces.Gam α s)]

/-- **The arithmetic core.**  `(α/c)·D_θ^iΓ` is bounded by `B1·Γ(α + sin 2θ)` uniformly in
`α ∈ (0,1]` and `1 ≤ i ≤ 5`, with `B1 = 10C + 40/3 + 1`.

For `i = 1` we use `|D_θΓ| ≤ (4/3)αΓ` and `α² ≤ α + sin 2θ`; for `i ≥ 2` the sharp bound
`|D_θ^iΓ| ≤ C α Γ (α + sin 2θ)` and `α² ≤ 1`. -/
lemma jet_cmul_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {C : ℝ} (hCpos : 0 < C)
    (hC : ∀ θ ∈ Work.Spaces.Iθ, ∀ m : ℕ, 2 ≤ m → m ≤ 5 →
      |Work.Spaces.dthU^[m] (fun t => Work.Spaces.Gam α t) θ|
        ≤ C * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)))
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (i : ℕ) (hi1 : 1 ≤ i) (hi5 : i ≤ 5) :
    |(α / Work.Spaces.c α) * Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
      ≤ (10 * C + 40 / 3 + 1)
        * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) := by
  have hc := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith [hc.1]
  have hdc : 0 ≤ α / Work.Spaces.c α := div_nonneg hα.le hcpos.le
  have hdiv : α / Work.Spaces.c α ≤ 10 * α := by
    rw [div_le_iff₀ hcpos]
    nlinarith [hc.1, hα]
  have hG := Work.Spaces.Gam_bounds α θ hα hθ
  have hsin := sin_two_nonneg_Iθ hθ
  have hα2 : α ^ 2 ≤ α + Real.sin (2 * θ) := by nlinarith [hα.le, hα1, hsin]
  have hα2' : α ^ 2 ≤ 1 := by nlinarith [hα.le, hα1]
  have hX : 0 ≤ Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) :=
    mul_nonneg hG.1 (by linarith [hα.le, hsin])
  rw [abs_mul, abs_of_nonneg hdc]
  rcases eq_or_lt_of_le hi1 with hone | hgt
  · subst hone
    rw [Function.iterate_one]
    have hb : |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
        ≤ (4 / 3) * α * Work.Spaces.Gam α θ := by
      have hrepr : Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ
          = Work.Spaces.DthIter 1 (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ := by
        rw [Work.FTS.LocData.DthIter_rad_eq 1 (fun t => Work.Spaces.Gam α t) 0 θ,
          Function.iterate_one]
      rw [hrepr]
      exact Work.FTS.Nonlinear.Pieces.RNP.dthIter_one_Gam_le hα hα1 θ hθ
    have h4nn : 0 ≤ (4 / 3) * α * Work.Spaces.Gam α θ :=
      mul_nonneg (mul_nonneg (by norm_num) hα.le) hG.1
    calc (α / Work.Spaces.c α) * |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
        ≤ (α / Work.Spaces.c α) * ((4 / 3) * α * Work.Spaces.Gam α θ) :=
          mul_le_mul_of_nonneg_left hb hdc
      _ ≤ (10 * α) * ((4 / 3) * α * Work.Spaces.Gam α θ) :=
          mul_le_mul_of_nonneg_right hdiv h4nn
      _ = (40 / 3) * (α ^ 2 * Work.Spaces.Gam α θ) := by ring
      _ ≤ (40 / 3) * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          calc α ^ 2 * Work.Spaces.Gam α θ
              ≤ (α + Real.sin (2 * θ)) * Work.Spaces.Gam α θ :=
                mul_le_mul_of_nonneg_right hα2 hG.1
            _ = Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) := by ring
      _ ≤ (10 * C + 40 / 3 + 1)
            * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) :=
          mul_le_mul_of_nonneg_right (by linarith) hX
  · have hb := hC θ hθ i (by omega) hi5
    have hCnn : 0 ≤ C * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) :=
      mul_nonneg (mul_nonneg (mul_nonneg hCpos.le hα.le) hG.1) (by linarith [hα.le, hsin])
    calc (α / Work.Spaces.c α) * |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
        ≤ (α / Work.Spaces.c α)
            * (C * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) :=
          mul_le_mul_of_nonneg_left hb hdc
      _ ≤ (10 * α) * (C * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) :=
          mul_le_mul_of_nonneg_right hdiv hCnn
      _ = (10 * C) * (α ^ 2 * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)))) := by ring
      _ ≤ (10 * C) * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith [hCpos])
          calc α ^ 2 * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)))
              ≤ 1 * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) :=
                mul_le_mul_of_nonneg_right hα2' hX
            _ = Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) := one_mul _
      _ ≤ (10 * C + 40 / 3 + 1)
            * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) :=
          mul_le_mul_of_nonneg_right (by linarith) hX

theorem AngSlotBounds :
    ∃ B0 B1 : ℝ, 0 < B0 ∧ 0 < B1 ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
      (∀ θ ∈ Work.Spaces.Iθ,
          |Work.FTS.StrongEps.ClassCRHS.SA0 α θ| ≤ B0) ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
          |Work.Spaces.DthIter i (fun _ (θ' : ℝ) =>
              Work.FTS.StrongEps.ClassCRHS.SA0 α θ') 0 θ|
            ≤ B1 * Work.FTS.StrongEps.ClassCRHS.SGmj α θ) ∧
      (∀ θ ∈ Work.Spaces.Iθ,
          |Work.FTS.StrongEps.ClassCRHS.SA1 α θ| ≤ B0) ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
          |Work.Spaces.DthIter i (fun _ (θ' : ℝ) =>
              Work.FTS.StrongEps.ClassCRHS.SA1 α θ') 0 θ|
            ≤ B1 * Work.FTS.StrongEps.ClassCRHS.SGmj α θ) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.Nonlinear.Pieces.RNP.dthU_pow_Gam_sharp
  refine ⟨10 ^ 6, 10 * C + 40 / 3 + 1, by norm_num, by linarith, ?_⟩
  intro α hαmem
  obtain ⟨hα, hα1⟩ := hαmem
  have hc := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith [hc.1]
  have hdc : 0 ≤ α / Work.Spaces.c α := div_nonneg hα.le hcpos.le
  have hdiv : α / Work.Spaces.c α ≤ 10 * α := by
    rw [div_le_iff₀ hcpos]
    nlinarith [hc.1, hα]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- clause 1: `|SA0| ≤ 10⁶`
    intro θ hθ
    have hG := Work.Spaces.Gam_bounds α θ hα hθ
    have h1 : |SA0 α θ| = α * Work.Spaces.Gam α θ / Work.Spaces.c α := by
      show |α * Work.Spaces.Gam α θ / Work.Spaces.c α|
          = α * Work.Spaces.Gam α θ / Work.Spaces.c α
      exact abs_of_nonneg (div_nonneg (mul_nonneg hα.le hG.1) hcpos.le)
    rw [h1, div_le_iff₀ hcpos]
    have h2 : α * Work.Spaces.Gam α θ ≤ 1 := by
      have h := mul_le_mul hα1 hG.2 hG.1 (by norm_num : (0 : ℝ) ≤ 1)
      simpa using h
    have h3 : 1 ≤ 10 ^ 6 * Work.Spaces.c α := by nlinarith [hc.1]
    linarith
  · -- clause 2: the `SA0`-slots
    intro i hi1 hi4 θ hθ
    rw [DthIter_SA0_repr α i 0 θ]
    show |(α / Work.Spaces.c α) * Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
        ≤ (10 * C + 40 / 3 + 1)
          * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)))
    exact jet_cmul_le hα hα1 hCpos (hC α hα hα1) hθ i hi1 (by omega)
  · -- clause 3: `|SA1| ≤ 10⁶`
    intro θ hθ
    have hG := Work.Spaces.Gam_bounds α θ hα hθ
    have hsa1 : SA1 α θ = (α / Work.Spaces.c α)
        * Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ := by
      show α * Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ / Work.Spaces.c α
          = (α / Work.Spaces.c α) * Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ
      ring
    have hb : |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
        ≤ (4 / 3) * α * Work.Spaces.Gam α θ := by
      have hrepr : Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ
          = Work.Spaces.DthIter 1 (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ := by
        rw [Work.FTS.LocData.DthIter_rad_eq 1 (fun t => Work.Spaces.Gam α t) 0 θ,
          Function.iterate_one]
      rw [hrepr]
      exact Work.FTS.Nonlinear.Pieces.RNP.dthIter_one_Gam_le hα hα1 θ hθ
    rw [hsa1, abs_mul, abs_of_nonneg hdc]
    have h4nn : 0 ≤ (4 / 3) * α * Work.Spaces.Gam α θ :=
      mul_nonneg (mul_nonneg (by norm_num) hα.le) hG.1
    have hα2' : α ^ 2 ≤ 1 := by nlinarith [hα.le, hα1]
    calc (α / Work.Spaces.c α)
          * |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
        ≤ (α / Work.Spaces.c α) * ((4 / 3) * α * Work.Spaces.Gam α θ) :=
          mul_le_mul_of_nonneg_left hb hdc
      _ ≤ (10 * α) * ((4 / 3) * α * Work.Spaces.Gam α θ) :=
          mul_le_mul_of_nonneg_right hdiv h4nn
      _ = (40 / 3) * (α ^ 2 * Work.Spaces.Gam α θ) := by ring
      _ ≤ (40 / 3) * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact (mul_le_mul hα2' hG.2 hG.1 (by norm_num)).trans_eq (by norm_num)
      _ ≤ 10 ^ 6 := by norm_num
  · -- clause 4: the `SA1`-slots
    intro i hi1 hi4 θ hθ
    rw [DthIter_SA1_repr α i 0 θ]
    show |(α / Work.Spaces.c α) * Work.Spaces.dthU^[i + 1] (fun t => Work.Spaces.Gam α t) θ|
        ≤ (10 * C + 40 / 3 + 1)
          * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)))
    exact jet_cmul_le hα hα1 hCpos (hC α hα hα1) hθ (i + 1) (by omega) (by omega)

end Work.FTS.StrongEps.ClassCRHS
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.DiffAux.hasDerivAt_Jeps_slice_z =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.DiffAux

/-- **`E1`, the `z`-slice form, `HasDerivAt` version.**  For a profile `g` which is `C^n` on the
open quadrant for every `n`, the `z`-slice `z' ↦ J_ε g z' θ` of the mollifier is differentiable
at every interior point `z > 0` with derivative the `p`-integral of the derivative of the
integrand, i.e. the kernel against `e^{-p₁} ∂_z g` at the shifted point.

The proof is a wrapper around the two `Commute.lean` results: `hasDerivAt_integral_Jeps_z`
differentiates the `p`-integral form under the integral (over the ball of radius `ε`, where the
kernel lives), `setIntegral_eq_integral_of_forall_compl_eq_zero` removes the restriction to that
ball, `Jeps_eq_integral` identifies the slice near `z` with the integral, and `Jeps_deriv_z`
supplies the value of the derivative.  The hypothesis `hg` only has to be fed at the two orders
`1` (`C¹` of `g`) and `2` (which gives, through `uncurry_partial_c1`, the continuity of `∂_z g`
on the quadrant). -/
theorem hasDerivAt_Jeps_slice_z (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {g : ℝ → ℝ → ℝ}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    HasDerivAt (fun z' => Work.FTS.StrongEps.Jeps ρ ε g z' θ)
      (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * (Real.exp (-p.1) * Work.Spaces.pz g (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2))) z := by
  have hf : ContDiffOn ℝ 1 (Function.uncurry g) Work.FTS.StrongEps.Quad := hg 1
  have hdf : ContinuousOn (Function.uncurry (Work.Spaces.pz g)) Work.FTS.StrongEps.Quad :=
    ((Work.Spaces.uncurry_partial_c1 Work.FTS.StrongEps.isOpen_Quad (hg 2)).1).continuousOn
  -- the restricted integral of `hasDerivAt_integral_Jeps_z` is the full integral: the kernel
  -- vanishes off the ball of radius `ε`
  have hball : (fun z' => ∫ p : ℝ × ℝ in Metric.closedBall (0 : ℝ × ℝ) ε,
        Work.FTS.StrongEps.Jker ρ ε p * g (Work.FTS.StrongEps.zShift z' p.1)
          (Work.FTS.StrongEps.thShift θ p.2))
      = fun z' => ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p * g
          (Work.FTS.StrongEps.zShift z' p.1) (Work.FTS.StrongEps.thShift θ p.2) := by
    funext z'
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
      (s := Metric.closedBall (0 : ℝ × ℝ) ε)
      (f := fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p * g
        (Work.FTS.StrongEps.zShift z' p.1) (Work.FTS.StrongEps.thShift θ p.2))
      (fun p hp => by rw [Work.FTS.StrongEps.Jker_eq_zero_of_not_mem hρ hε hp, zero_mul])
  -- near `z` the `z`-slice of `Jeps` is the `p`-integral of the shifted profile
  have hev : (fun z' => Work.FTS.StrongEps.Jeps ρ ε g z' θ)
      =ᶠ[𝓝 z] fun z' => ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p * g
          (Work.FTS.StrongEps.zShift z' p.1) (Work.FTS.StrongEps.thShift θ p.2) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact Work.FTS.StrongEps.Jeps_eq_integral ρ ε g hz' hθ
  have hdiff : DifferentiableAt ℝ (fun z' => Work.FTS.StrongEps.Jeps ρ ε g z' θ) z := by
    have h0 := Work.FTS.StrongEps.hasDerivAt_integral_Jeps_z (ρ := ρ) hρ hε hf hdf hz hθ
    rw [hball] at h0
    exact hev.differentiableAt_iff.mpr h0.differentiableAt
  rw [← Work.FTS.StrongEps.Jeps_deriv_z hρ hε hf hdf hz hθ]
  exact hdiff.hasDerivAt

end Work.FTS.StrongEps.DiffAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `JepsTransfer/Defs.lean` — the log-coordinate vocabulary of the `IP6`-transfer estimate

The log-coordinate transfer estimate for the Friedrichs mollifier `J_ε` of
`Submission.Work.FTS.StrongEps.Basic` compares the two sides of the level-`k` pairing

  `⟨J_ε f, h⟩_ρ − ⟨f, J_ε h⟩_ρ`,   where `⟨u, v⟩_ρ = ∫_{Quad} ρ · u · v`,

and shows that it is `O(ε) ‖f‖ ‖h‖` **without any derivative loss**.  The mechanism is that in
the log coordinates `(s, ζ) = (log z, log tan θ)` the mollifier is an even convolution over the
plane, so after a change of variables the difference is the integral of `Q(y) − Q(y − p)` times
the two profiles, where `Q = logJac · ρ ∘ Ψ` is the log-coordinate version of the weight.  Every
weight of the pairing (`leafEta`, `leafOne`, `leafGam α = slotW α a`) is log-Lipschitz, which is
what makes the difference `O(|p|)` *without* differentiating the profiles.

This module collects the two definitions shared by the pieces of the argument:

* `logPull g` — the profile `g` pulled back to the log coordinates `(s,ζ)` by `Ψ`;
* `logW w` — the leaf weight `w` together with the Jacobian `logJac` of the substitution, i.e.
  the density of the quadrant measure `dz dθ` w.r.t. `ds dζ`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The map `Ψ(s,ζ) = (e^s, arctan (e^ζ))` from the log plane onto the open quadrant. -/
def logPsi (y : ℝ × ℝ) : ℝ × ℝ := (Real.exp y.1, Real.arctan (Real.exp y.2))

/-- The pull-back of a profile to the log coordinates `(s,ζ) = (log z, log tan θ)`:
`logPull g s ζ = g (e^s) (arctan (e^ζ))`. -/
def logPull (g : Fn) : ℝ × ℝ → ℝ := fun y => g (Real.exp y.1) (Real.arctan (Real.exp y.2))

/-- The log-coordinate density of a leaf weight `w`: the quadrant weight `w(z,θ)` multiplied by
the Jacobian `logJac` of the substitution `(z,θ) = Ψ(s,ζ)`.  This is the function against which
the pulled-back pairings are integrated on the plane. -/
def logW (w : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun y => Work.FTS.StrongEps.HkSqAux.logJac y.1 y.2
    * w (Real.exp y.1) (Real.arctan (Real.exp y.2))

/-- The log-coordinate pairing `∫_y Q y · G₁ y · G₂ y`, with `Q = logW w` the pulled-back
weight; it is the plane integral into which `slotPairing w a b` turns. -/
def logPair (Q : ℝ × ℝ → ℝ) (G₁ G₂ : ℝ × ℝ → ℝ) : ℝ :=
  ∫ y : ℝ × ℝ, Q y * G₁ y * G₂ y

@[simp] theorem logPsi_apply (y : ℝ × ℝ) :
    logPsi y = (Real.exp y.1, Real.arctan (Real.exp y.2)) := rfl

@[simp] theorem logPull_apply (g : Fn) (y : ℝ × ℝ) :
    logPull g y = g (Real.exp y.1) (Real.arctan (Real.exp y.2)) := rfl

@[simp] theorem logW_apply (w : ℝ → ℝ → ℝ) (y : ℝ × ℝ) :
    logW w y = Work.FTS.StrongEps.HkSqAux.logJac y.1 y.2
      * w (Real.exp y.1) (Real.arctan (Real.exp y.2)) := rfl

@[simp] theorem logPair_apply (Q : ℝ × ℝ → ℝ) (G₁ G₂ : ℝ × ℝ → ℝ) :
    logPair Q G₁ G₂ = ∫ y : ℝ × ℝ, Q y * G₁ y * G₂ y := rfl


theorem logPsi_mem (y : ℝ × ℝ) :
    (logPsi y).2 ∈ Set.Ioo 0 (π / 2) :=
  ⟨Real.arctan_pos.mpr (Real.exp_pos y.2),
    Real.arctan_lt_pi_div_two (Real.exp y.2)⟩

theorem logPsi_mem_quad (y : ℝ × ℝ) : logPsi y ∈ Work.FTS.StrongEps.Quad :=
  Work.FTS.StrongEps.mem_Quad.mpr ⟨Real.exp_pos y.1, logPsi_mem y⟩

end Work.FTS.StrongEps.E4R3.Apriori4Proofs
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Nblock6.Auxiliary.Fstar_jet_rel =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Nblock6.aux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary profile facts -/

/-- `F_* z > 0` for `z > 0`. -/
private lemma Fstar_pos {z : ℝ} (hz : 0 < z) : 0 < Work.FM.Fstar z := by
  rw [Work.FM.Fstar]
  positivity

/-- For `k ≥ 1` and `z > 0`, `|z^{k-1}(z-k)| ≤ (k+1)(1+z)^k`. -/
private lemma abs_zpow_pred_mul_sub_le (k : ℕ) (hk : 1 ≤ k) {z : ℝ} (hz : 0 < z) :
    |z ^ (k - 1) * (z - (k : ℝ))| ≤ ((k : ℝ) + 1) * (1 + z) ^ k := by
  have hk1 : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos hk
  have hrew : z ^ (k - 1) * (z - (k : ℝ)) = z ^ k - (k : ℝ) * z ^ (k - 1) := by
    rw [mul_sub, ← pow_succ, hk1]
    ring
  rw [hrew]
  have hz1 : (1 : ℝ) ≤ 1 + z := by linarith
  have hA : z ^ k ≤ (1 + z) ^ k := pow_le_pow_left₀ hz.le (by linarith) k
  have hB : z ^ (k - 1) ≤ (1 + z) ^ k := by
    calc z ^ (k - 1) ≤ (1 + z) ^ (k - 1) := pow_le_pow_left₀ hz.le (by linarith) (k - 1)
      _ ≤ (1 + z) ^ k := pow_le_pow_right₀ hz1 (by omega)
  have h1 : |z ^ k - (k : ℝ) * z ^ (k - 1)| ≤ z ^ k + (k : ℝ) * z ^ (k - 1) := by
    rw [abs_le]
    constructor <;> nlinarith [pow_nonneg hz.le k, pow_nonneg hz.le (k - 1)]
  nlinarith [h1, hA, hB]

/-- **The weighted plain derivatives of the profile, relative to the profile**:
`|z^k ∂_z^k F_* z| ≤ (k+1)! · F_* z` for `z > 0`. -/
private lemma zpow_deriv_FM_Fstar_le (k : ℕ) {z : ℝ} (hz : 0 < z) :
    |z ^ k * deriv^[k] (fun z => Work.FM.Fstar z) z| ≤ ((k + 1).factorial : ℝ) * Work.FM.Fstar z := by
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  have hzI : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
  rcases k with _ | m
  · rw [pow_zero, one_mul, Function.iterate_zero_apply, abs_of_pos (Fstar_pos hz)]
    norm_num
  · rw [Work.FTS.StrongPersist.H6Pair6Aux.deriv_iter_FM_Fstar_eq (m + 1) hzI]
    have hkey : z ^ (m + 1) * (2 * (-1 : ℝ) ^ (m + 1) * (((m + 1).factorial : ℝ))
          * (z - (((m + 1 : ℕ) : ℝ))) / (1 + z) ^ (m + 1 + 2))
        = Work.FM.Fstar z * (((-1 : ℝ) ^ (m + 1) * ((m + 1).factorial : ℝ))
          * (z ^ m * (z - (((m + 1 : ℕ) : ℝ))) / (1 + z) ^ (m + 1))) := by
      rw [Work.FM.Fstar]
      field_simp
      ring
    rw [hkey, abs_mul, abs_of_pos (Fstar_pos hz)]
    have hb : |((-1 : ℝ) ^ (m + 1) * ((m + 1).factorial : ℝ))
        * (z ^ m * (z - (((m + 1 : ℕ) : ℝ))) / (1 + z) ^ (m + 1))|
        ≤ ((m + 1 + 1).factorial : ℝ) := by
      rw [abs_mul]
      have hc : |(-1 : ℝ) ^ (m + 1) * ((m + 1).factorial : ℝ)| = ((m + 1).factorial : ℝ) := by
        rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      rw [hc, abs_div, abs_of_pos (pow_pos hz1 (m + 1)), ← mul_div_assoc]
      rw [div_le_iff₀ (pow_pos hz1 (m + 1))]
      have hnum := abs_zpow_pred_mul_sub_le (m + 1) (Nat.le_add_left 1 m) hz
      have hnum' : |z ^ m * (z - (((m + 1 : ℕ) : ℝ)))|
          ≤ (((m + 1 : ℕ) : ℝ) + 1) * (1 + z) ^ (m + 1) := by
        simpa only [Nat.add_sub_cancel] using hnum
      calc ((m + 1).factorial : ℝ) * |z ^ m * (z - (((m + 1 : ℕ) : ℝ)))|
          ≤ ((m + 1).factorial : ℝ) * ((((m + 1 : ℕ) : ℝ) + 1) * (1 + z) ^ (m + 1)) :=
            mul_le_mul_of_nonneg_left hnum' (Nat.cast_nonneg _)
        _ = (((m + 1 + 1).factorial : ℝ)) * (1 + z) ^ (m + 1) := by
            have hf : (((m + 1 + 1).factorial : ℝ))
                = ((m + 1).factorial : ℝ) * ((((m + 1 : ℕ) : ℝ)) + 1) := by
              rw [Nat.factorial_succ (m + 1)]; push_cast; ring
            rw [hf]; ring
    calc Work.FM.Fstar z * |((-1 : ℝ) ^ (m + 1) * ((m + 1).factorial : ℝ))
            * (z ^ m * (z - (((m + 1 : ℕ) : ℝ))) / (1 + z) ^ (m + 1))|
        ≤ Work.FM.Fstar z * ((m + 1 + 1).factorial : ℝ) :=
          mul_le_mul_of_nonneg_left hb (Fstar_pos hz).le
      _ = (((m + 1) + 1).factorial : ℝ) * Work.FM.Fstar z := by ring

/-! ## The Bell-number bound -/

private lemma bell_le (b : ℕ) (hb : b ≤ 6) : (Work.Spaces.bell b : ℝ) ≤ 877 := by
  exact_mod_cast Work.FTS.StrongPersist.H6Pair6Aux.bell_le_seven b (by omega)

private lemma factorial_succ_le (k : ℕ) (hk : k ≤ 6) : ((k + 1).factorial : ℝ) ≤ 5040 := by
  have h : (k + 1).factorial ≤ Nat.factorial 7 := Nat.factorial_le (by omega)
  have h7 : ((Nat.factorial 7 : ℕ) : ℝ) = 5040 := by norm_num
  calc ((k + 1).factorial : ℝ) ≤ ((Nat.factorial 7 : ℕ) : ℝ) := by exact_mod_cast h
    _ = 5040 := h7

/-! ## The theorem -/

theorem Fstar_jet_rel : ∃ K : ℝ, 0 < K ∧ ∀ b : ℕ, b ≤ 6 → ∀ z : ℝ, 0 < z →
    |Work.Elliptic.DzdIter b Work.FM.Fstar z| ≤ K * Work.FM.Fstar z := by
  refine ⟨877 * 5040, by norm_num, ?_⟩
  intro b hb z hz
  have hzI : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
  have h0I : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, Real.pi_div_two_pos.le⟩
  have hsmooth : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ ⊤ (fun z => (fun z _ => Work.FM.Fstar z) z θ) (Set.Ioi (-1)) :=
    fun _ _ => Work.FTS.StrongPersist.H6Pair6Aux.contDiffOn_FM_Fstar_analytic
  rw [show Work.Elliptic.DzdIter b Work.FM.Fstar z
      = Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z 0 from
    (Work.Elliptic.DzIter_rad Work.FM.Fstar b z 0).symm]
  rw [Work.Spaces.DzIter_eq_sum_scoef hsmooth b z hzI 0 h0I]
  have hx : ∀ k ≤ b, |z ^ k * Work.Spaces.pzIter k (fun z _ => Work.FM.Fstar z) z 0|
      ≤ 5040 * Work.FM.Fstar z := by
    intro k hk
    rw [Work.FTS.StrongPersist.H6Pair6Aux.pzIter_zonly_eq_FM_deriv_iter]
    refine (zpow_deriv_FM_Fstar_le k hz).trans ?_
    exact mul_le_mul_of_nonneg_right (factorial_succ_le k (le_trans hk hb)) (Fstar_pos hz).le
  have hsum := Work.Spaces.abs_sum_scoef_mul_le b (5040 * Work.FM.Fstar z)
    (fun k => z ^ k * Work.Spaces.pzIter k (fun z _ => Work.FM.Fstar z) z 0) hx
  refine hsum.trans ?_
  calc (Work.Spaces.bell b : ℝ) * (5040 * Work.FM.Fstar z)
      ≤ 877 * (5040 * Work.FM.Fstar z) :=
        mul_le_mul_of_nonneg_right (bell_le b hb)
          (mul_nonneg (by norm_num) (Fstar_pos hz).le)
    _ = (877 * 5040) * Work.FM.Fstar z := by ring

end Work.FTS.StrongEps.E4R3.Nblock6.aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Nblock6.RadCoeffJets =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Nblock6

open scoped ContDiff Topology
open Set Filter

/-! ## Auxiliary calculus lemmas for the two radial profiles

We prove the pointwise bounds on the `∂_z^k`-derivatives of the two profiles
`z ↦ c·(1+z)⁻¹` and `z ↦ c·hKer z = c·z/(1+z)²` on `[0,∞)`, and then pass to the
iterated `D_z = z∂_z` by the Stirling expansion `D_z^j = ∑_{k≤j} S(j,k) z^k ∂_z^k`
(`Work.Spaces.DzIter_eq_sum_scoef`) together with the coefficient-mass bound
`Work.Spaces.abs_sum_scoef_mul_le`. -/

/-- `∂_z^k` commutes with multiplication by a constant. -/
private theorem deriv_iterate_const_mul (c : ℝ) (f : ℝ → ℝ) (k : ℕ) :
    deriv^[k] (fun z => c * f z) = fun z => c * deriv^[k] f z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply' deriv k (fun z => c * f z), ih]
    funext z
    rw [congrFun (Function.iterate_succ_apply' deriv k f) z]
    exact deriv_const_mul_field (v := deriv^[k] f) c

/-- The Bell number of a row `j ≤ 6` is at most `203` (`bell 6 = 203`). -/
private lemma bell_le_203 {j : ℕ} (hj : j ≤ 6) : Work.Spaces.bell j ≤ 203 := by
  interval_cases j <;> decide

/-- `k! ≤ 5040` for `k ≤ 6`. -/
private lemma factorial_le_5040 {k : ℕ} (hk : k ≤ 6) : (k.factorial : ℝ) ≤ 5040 := by
  have h1 : k.factorial ≤ Nat.factorial 6 := Nat.factorial_le hk
  calc (k.factorial : ℝ) ≤ (Nat.factorial 6 : ℝ) := by exact_mod_cast h1
    _ = 720 := by norm_num
    _ ≤ 5040 := by norm_num

/-- `k!·(k+1) ≤ 5040` for `k ≤ 6` (`6!·7 = 5040`). -/
private lemma factorial_mul_succ_le_5040 {k : ℕ} (hk : k ≤ 6) :
    (k.factorial : ℝ) * (k + 1) ≤ 5040 := by
  have h1 : (k.factorial : ℝ) ≤ 720 := by
    have h := Nat.factorial_le hk
    calc (k.factorial : ℝ) ≤ (Nat.factorial 6 : ℝ) := by exact_mod_cast h
      _ = 720 := by norm_num
  have h2 : (k : ℝ) + 1 ≤ 7 := by
    have hk' : k + 1 ≤ 7 := by omega
    exact_mod_cast hk'
  calc (k.factorial : ℝ) * (k + 1) ≤ 720 * 7 :=
        mul_le_mul h1 h2 (by positivity) (by norm_num)
    _ = 5040 := by norm_num

/-! ### The profile `z ↦ (1+z)⁻¹` -/

/-- The closed form `(-1)^k k! (1+z)^{-(k+1)}` of the `k`-th derivative of `z ↦ (1+z)⁻¹`. -/
private noncomputable def invClosed (k : ℕ) (z : ℝ) : ℝ :=
  ((-1 : ℝ) ^ k * (k.factorial : ℝ)) * ((1 + z)⁻¹) ^ (k + 1)

private lemma hasDerivAt_invClosed (k : ℕ) {z : ℝ} (hz : (1 + z) ≠ 0) :
    HasDerivAt (invClosed k) (invClosed (k + 1) z) z := by
  have hbase : HasDerivAt (fun t : ℝ => (1 + t)⁻¹) (-((1 + z)⁻¹) ^ 2) z := by
    have hh : HasDerivAt (fun t : ℝ => 1 + t) 1 z := by
      simpa using (hasDerivAt_id z).const_add (1 : ℝ)
    have hv := hh.inv hz
    have hval : -(1 : ℝ) / (1 + z) ^ 2 = -((1 + z)⁻¹) ^ 2 := by
      rw [div_eq_mul_inv, ← inv_pow]; ring
    rw [hval] at hv
    exact hv
  have hp := hbase.pow (k + 1)
  have hc := hp.const_mul ((-1 : ℝ) ^ k * (k.factorial : ℝ))
  have hfun : (fun y => ((-1 : ℝ) ^ k * (k.factorial : ℝ))
        * ((fun t : ℝ => (1 + t)⁻¹) ^ (k + 1)) y) = invClosed k := by
    funext y; simp only [Pi.pow_apply, invClosed]
  have hval : ((-1 : ℝ) ^ k * (k.factorial : ℝ))
        * ((↑(k + 1) : ℝ) * ((1 + z)⁻¹) ^ (k + 1 - 1) * (-((1 + z)⁻¹) ^ 2))
      = invClosed (k + 1) z := by
    have hsign : (-1 : ℝ) ^ (k + 1) = -(-1) ^ k := by rw [pow_succ]; ring
    have hfact : (((k + 1).factorial : ℝ)) = (↑(k + 1) * ↑k.factorial) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [show k + 1 - 1 = k by omega]
    simp only [invClosed]
    rw [hsign, hfact, pow_add, pow_add, pow_one]
    ring
  rw [hfun, hval] at hc
  exact hc

private theorem iter_deriv_inv (k : ℕ) {z : ℝ} (hz : -1 < z) :
    deriv^[k] (fun w : ℝ => (1 + w)⁻¹) z = invClosed k z := by
  induction k generalizing z with
  | zero => simp [invClosed]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hev : deriv^[k] (fun w : ℝ => (1 + w)⁻¹) =ᶠ[𝓝 z] invClosed k := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
      exact ih hy
    rw [hev.deriv_eq]
    exact (hasDerivAt_invClosed k (by intro h; linarith)).deriv

/-- The weighted derivative bound for `z ↦ (1+z)⁻¹`: `|z^k ∂_z^k (1+z)⁻¹| ≤ k!` for `z ≥ 0`. -/
private lemma inv_deriv_bound (k : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    |z ^ k * deriv^[k] (fun w : ℝ => (1 + w)⁻¹) z| ≤ (k.factorial : ℝ) := by
  rw [iter_deriv_inv k (by linarith : -1 < z)]
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  have hb1 : 0 ≤ z / (1 + z) := div_nonneg hz (by linarith)
  have hb2 : z / (1 + z) ≤ 1 := (div_le_one hz1).mpr (by linarith)
  have hc1 : 0 ≤ (1 + z)⁻¹ := inv_nonneg.mpr (by linarith)
  have hc2 : (1 + z)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hprod : |(z / (1 + z)) ^ k * (1 + z)⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg (pow_nonneg hb1 k) hc1)]
    calc (z / (1 + z)) ^ k * (1 + z)⁻¹ ≤ 1 * 1 :=
          mul_le_mul (pow_le_one₀ hb1 hb2) hc2 hc1 (by norm_num)
      _ = 1 := by ring
  have hrew : z ^ k * invClosed k z
      = ((-1 : ℝ) ^ k * (k.factorial : ℝ)) * ((z / (1 + z)) ^ k * (1 + z)⁻¹) := by
    simp only [invClosed]
    rw [div_eq_mul_inv, mul_pow, pow_succ]
    ring
  rw [hrew, abs_mul, abs_mul]
  have h1 : |(-1 : ℝ) ^ k| = 1 := by rw [abs_pow]; norm_num
  rw [h1, one_mul, abs_of_nonneg (Nat.cast_nonneg k.factorial)]
  exact mul_le_of_le_one_right (Nat.cast_nonneg k.factorial) hprod

/-- The weighted derivative bound for `z ↦ c·(1+z)⁻¹`: `|z^k ∂_z^k| ≤ k!·|c|` for `z ≥ 0`. -/
private lemma inv_const_deriv_bound (c : ℝ) (k : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    |z ^ k * deriv^[k] (fun w : ℝ => c * (1 + w)⁻¹) z| ≤ (k.factorial : ℝ) * |c| := by
  rw [congrFun (deriv_iterate_const_mul c (fun w : ℝ => (1 + w)⁻¹) k) z]
  rw [show z ^ k * (c * deriv^[k] (fun w : ℝ => (1 + w)⁻¹) z)
      = c * (z ^ k * deriv^[k] (fun w : ℝ => (1 + w)⁻¹) z) by ring]
  rw [abs_mul]
  calc |c| * |z ^ k * deriv^[k] (fun w : ℝ => (1 + w)⁻¹) z|
      ≤ |c| * (k.factorial : ℝ) :=
        mul_le_mul_of_nonneg_left (inv_deriv_bound k hz) (abs_nonneg c)
    _ = (k.factorial : ℝ) * |c| := by ring

/-- Analytic smoothness of `z ↦ c·(1+z)⁻¹` on the set where `1+z ≠ 0`. -/
private lemma contDiffOn_inv_const (c : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞ω) (fun z : ℝ => c * (1 + z)⁻¹) (Set.Ioi (-1)) := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞ω) (fun z : ℝ => 1 + z) (Set.Ioi (-1)) := by
    simpa [add_comm] using
      (contDiffOn_const (c := (1 : ℝ)) (s := Set.Ioi (-1)) (n := (⊤ : ℕ∞ω))).add
        (contDiffOn_id (𝕜 := ℝ) (n := (⊤ : ℕ∞ω)) (s := Set.Ioi (-1)))
  have h2 := h1.inv (fun x hx => ne_of_gt (by simp only [Set.mem_Ioi] at hx; linarith))
  simpa using (contDiffOn_const (c := c) (s := Set.Ioi (-1)) (n := (⊤ : ℕ∞ω))).mul h2

/-! ### The profile `z ↦ c·hKer z = c·z/(1+z)²` -/

/-- The weighted derivative bound for `hKer`: `|z^k ∂_z^k hKer z| ≤ k!·(k+1)` for `z ≥ 0`
(this is `Work.Spaces.pzIter_hKer_bound` with the factor `(1+z)^k` traded for `z^k ≥ 0`). -/
private lemma hKer_deriv_bound (k : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    |z ^ k * deriv^[k] Work.Spaces.hKer z| ≤ (k.factorial : ℝ) * (k + 1) := by
  have hkey : |(1 + z) ^ k * deriv^[k] Work.Spaces.hKer z| ≤ (k.factorial : ℝ) * (k + 1) := by
    rw [show (1 : ℝ) + z = z + 1 by ring]
    exact Work.Spaces.pzIter_hKer_bound k z hz
  have hz1 : (1 : ℝ) + z ≠ 0 := by positivity
  have hb1 : 0 ≤ z / (1 + z) := div_nonneg hz (by linarith)
  have hb2 : z / (1 + z) ≤ 1 := (div_le_one (by linarith : (0 : ℝ) < 1 + z)).mpr (by linarith)
  have hrew : z ^ k * deriv^[k] Work.Spaces.hKer z
      = (z / (1 + z)) ^ k * ((1 + z) ^ k * deriv^[k] Work.Spaces.hKer z) := by
    rw [← mul_assoc, ← mul_pow, div_mul_cancel₀ z hz1]
  rw [hrew, abs_mul, abs_of_nonneg (pow_nonneg hb1 k)]
  calc (z / (1 + z)) ^ k * |(1 + z) ^ k * deriv^[k] Work.Spaces.hKer z|
      ≤ 1 * ((k.factorial : ℝ) * (k + 1)) :=
        mul_le_mul (pow_le_one₀ hb1 hb2) hkey (abs_nonneg _) (by norm_num)
    _ = (k.factorial : ℝ) * (k + 1) := by ring

/-- The weighted derivative bound for `z ↦ c·hKer z`: `|z^k ∂_z^k| ≤ k!·(k+1)·|c|`. -/
private lemma hKer_const_deriv_bound (c : ℝ) (k : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    |z ^ k * deriv^[k] (fun w : ℝ => c * Work.Spaces.hKer w) z|
      ≤ (k.factorial : ℝ) * (k + 1) * |c| := by
  rw [congrFun (deriv_iterate_const_mul c Work.Spaces.hKer k) z]
  rw [show z ^ k * (c * deriv^[k] Work.Spaces.hKer z)
      = c * (z ^ k * deriv^[k] Work.Spaces.hKer z) by ring]
  rw [abs_mul]
  calc |c| * |z ^ k * deriv^[k] Work.Spaces.hKer z|
      ≤ |c| * ((k.factorial : ℝ) * (k + 1)) :=
        mul_le_mul_of_nonneg_left (hKer_deriv_bound k hz) (abs_nonneg c)
    _ = (k.factorial : ℝ) * (k + 1) * |c| := by ring

/-- Analytic smoothness of `hKer = z/(1+z)²` on the set where `1+z ≠ 0`. -/
private lemma contDiffOn_hKer_Ioi :
    ContDiffOn ℝ (⊤ : ℕ∞ω) Work.Spaces.hKer (Set.Ioi (-1)) := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞ω) (fun z : ℝ => 1 + z) (Set.Ioi (-1)) := by
    simpa [add_comm] using
      (contDiffOn_const (c := (1 : ℝ)) (s := Set.Ioi (-1)) (n := (⊤ : ℕ∞ω))).add
        (contDiffOn_id (𝕜 := ℝ) (n := (⊤ : ℕ∞ω)) (s := Set.Ioi (-1)))
  exact (contDiffOn_id (𝕜 := ℝ) (n := (⊤ : ℕ∞ω)) (s := Set.Ioi (-1))).div (h1.pow 2)
    (fun x hx => by
      have hx' : (0 : ℝ) < 1 + x := by simp only [Set.mem_Ioi] at hx; linarith
      positivity)

/-- Analytic smoothness of `z ↦ c·hKer z` on `(-1,∞)`. -/
private lemma contDiffOn_hKer_const (c : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞ω) (fun z : ℝ => c * Work.Spaces.hKer z) (Set.Ioi (-1)) := by
  simpa using
    (contDiffOn_const (c := c) (s := Set.Ioi (-1)) (n := (⊤ : ℕ∞ω))).mul contDiffOn_hKer_Ioi

/-! ### From `∂_z^k`-bounds to `D_z^j`-bounds -/

/-- **The Stirling passage.**  If the `z`-slices of `u` are analytic on `(-1,∞)` and
`|z^k ∂_z^k u z| ≤ M` on `[0,∞)` for every `k ≤ 6`, then `|D_z^j u z| ≤ bell j · M` for
`j ≤ 6` and `z > 0` (via `Work.Elliptic.DzIter_rad`, `Work.Spaces.DzIter_eq_sum_scoef` and
the coefficient-mass bound `Work.Spaces.abs_sum_scoef_mul_le`). -/
private theorem abs_DzdIter_le {u : ℝ → ℝ} {M : ℝ}
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞ω) u (Set.Ioi (-1)))
    (hbound : ∀ k ≤ 6, ∀ z : ℝ, 0 ≤ z → |z ^ k * deriv^[k] u z| ≤ M)
    (j : ℕ) (hj : j ≤ 6) :
    ∀ z : ℝ, 0 < z → |Work.Elliptic.DzdIter j u z| ≤ (Work.Spaces.bell j : ℝ) * M := by
  intro z hz
  have hz0 : 0 ≤ z := le_of_lt hz
  have hzIoi : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
  have h0I : (0 : ℝ) ∈ Work.Spaces.Iθ := by
    simp only [Work.Spaces.Iθ, Set.mem_Icc]
    exact ⟨le_refl 0, by positivity⟩
  rw [(Work.Elliptic.DzIter_rad u j z 0).symm]
  rw [Work.Spaces.DzIter_eq_sum_scoef (h := fun w _ : ℝ => u w)
    (fun θ _ => by simpa using hsmooth) j z hzIoi 0 h0I]
  have hterm : ∀ k : ℕ,
      z ^ k * Work.Spaces.pzIter k (fun w _ : ℝ => u w) z 0 = z ^ k * deriv^[k] u z := by
    intro k
    have hfun : (fun w _ : ℝ => u w) = (fun w θ : ℝ => (1 : ℝ) * u w) := by
      funext w θ; simp
    rw [hfun, Work.Spaces.pzIter_decomp k (fun _ : ℝ => (1 : ℝ)) u z 0, one_mul]
  have hcongr : (∑ k ∈ Finset.range (j + 1),
        (Work.Spaces.scoef j k : ℝ) * (z ^ k * Work.Spaces.pzIter k (fun w _ : ℝ => u w) z 0))
      = ∑ k ∈ Finset.range (j + 1), (Work.Spaces.scoef j k : ℝ) * (z ^ k * deriv^[k] u z) :=
    Finset.sum_congr rfl fun k _ => by rw [hterm k]
  rw [hcongr]
  exact Work.Spaces.abs_sum_scoef_mul_le j M (fun k => z ^ k * deriv^[k] u z)
    (fun k hk => hbound k (le_trans hk hj) z hz0)

/-- **Pointwise `D_z`-jet bounds for the two radial coefficients `c/(1+z)` and `c·hKer z`**
(namespace `Work.FTS.StrongEps.E4R3.Nblock6`), for orders `j ≤ 6`, with a constant relative to
`|c|` and the smoothness on `(0,∞)`.

Both profiles are rational with their only pole at `z = -1`, and every `D_z`-iterate is bounded
on `(0,∞)` by a multiple of `|c|`: for `r(z) = 1/(1+z)` one has
`z^k ∂_z^k r z = (-1)^k k! z^k/(1+z)^{k+1}` and `0 ≤ z/(1+z) ≤ 1`; for `hKer` use
`Work.Spaces.pzIter_hKer_bound` (`|(z+1)^k ∂_z^k hKer z| ≤ k!·(k+1)`).  The passage from
`∂_z^k`-bounds to `D_z^j`-bounds is `Work.Elliptic.DzdIter j r z = Σ_{k≤j} scoef j k · z^k ∂_z^k r z`
(the 1-D form of `Work.Spaces.DzIter_eq_sum_scoef`, via `Work.Spaces.DzIter_rad`) followed by the
triangle inequality, as in `Work.Spaces.DzIter_le_of_pzIter`. -/
theorem RadCoeffJets : ∃ C : ℝ, 0 < C ∧
    (∀ (c : ℝ) (j : ℕ), j ≤ 6 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter j (fun z => c / (1 + z)) z| ≤ C * |c|) ∧
    (∀ (c : ℝ), ContDiffOn ℝ 6 (fun z => c / (1 + z)) (Set.Ioi 0)) ∧
    (∀ (c : ℝ) (j : ℕ), j ≤ 6 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter j (fun z => c * Work.Spaces.hKer z) z| ≤ C * |c|) ∧
    (∀ (c : ℝ), ContDiffOn ℝ 6 (fun z => c * Work.Spaces.hKer z) (Set.Ioi 0)) := by
  refine ⟨2000000, by norm_num, ?_, ?_, ?_, ?_⟩
  · -- `j ≤ 6`-jet bound for `c/(1+z)`
    intro c j hj z hz
    have hfun : (fun w : ℝ => c / (1 + w)) = fun w => c * (1 + w)⁻¹ := by
      funext w; rw [div_eq_mul_inv]
    rw [hfun]
    have h := abs_DzdIter_le (u := fun w : ℝ => c * (1 + w)⁻¹) (M := 5040 * |c|)
      (contDiffOn_inv_const c)
      (fun k hk z hz' => le_trans (inv_const_deriv_bound c k hz')
        (mul_le_mul_of_nonneg_right (factorial_le_5040 hk) (abs_nonneg c)))
      j hj z hz
    refine le_trans h ?_
    have hbell : (Work.Spaces.bell j : ℝ) ≤ 203 := by
      exact_mod_cast bell_le_203 hj
    have h1 : (Work.Spaces.bell j : ℝ) * (5040 * |c|) ≤ 203 * (5040 * |c|) :=
      mul_le_mul_of_nonneg_right hbell (by positivity)
    have h2 : (203 : ℝ) * (5040 * |c|) ≤ 2000000 * |c| := by
      nlinarith [abs_nonneg c]
    linarith
  · -- smoothness of `c/(1+z)` on `(0,∞)`
    intro c
    have h : ContDiffOn ℝ (⊤ : ℕ∞ω) (fun w : ℝ => c / (1 + w)) (Set.Ioi (-1)) := by
      simpa only [div_eq_mul_inv] using contDiffOn_inv_const c
    exact (h.mono (fun x hx => by simp only [Set.mem_Ioi] at hx ⊢; linarith)).of_le le_top
  · -- `j ≤ 6`-jet bound for `c·hKer`
    intro c j hj z hz
    have h := abs_DzdIter_le (u := fun w : ℝ => c * Work.Spaces.hKer w) (M := 5040 * |c|)
      (contDiffOn_hKer_const c)
      (fun k hk z hz' => le_trans (hKer_const_deriv_bound c k hz')
        (by
          rw [show (k.factorial : ℝ) * (k + 1) * |c| = ((k.factorial : ℝ) * (k + 1)) * |c| by ring]
          exact mul_le_mul_of_nonneg_right (factorial_mul_succ_le_5040 hk) (abs_nonneg c)))
      j hj z hz
    refine le_trans h ?_
    have hbell : (Work.Spaces.bell j : ℝ) ≤ 203 := by
      exact_mod_cast bell_le_203 hj
    have h1 : (Work.Spaces.bell j : ℝ) * (5040 * |c|) ≤ 203 * (5040 * |c|) :=
      mul_le_mul_of_nonneg_right hbell (by positivity)
    have h2 : (203 : ℝ) * (5040 * |c|) ≤ 2000000 * |c| := by
      nlinarith [abs_nonneg c]
    linarith
  · -- smoothness of `c·hKer` on `(0,∞)`
    intro c
    exact ((contDiffOn_hKer_const c).mono
      (fun x hx => by simp only [Set.mem_Ioi] at hx ⊢; linarith)).of_le le_top

end Work.FTS.StrongEps.E4R3.Nblock6
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Nblock6.Tools.PtBdDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Nblock6.Tools.PtBdDefs` — the pointwise master-bound vocabulary and integral helpers

* `PtBdDth α` / `PtBdDz α` are the pointwise level-`6` master bounds of
  `Tools/ptBoundDth.lean` / `Tools/ptBoundDz.lean`;
* `ae_mem_Ioo_Iθ_fts`, `ae_mem_Ioi_Iz_fts`, `integral_add_three`, `integral_add_three_z`,
  `ten_le_inv_gam_sub_one` are the elementary integration helpers used by
  `Tools/shiftProdDth.lean` and `Tools/shiftProdDz.lean`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Nblock6.Tools

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

open Work.Spaces

/-- The pointwise master bound for `A · D_θ f` (the content of `Tools/ptBoundDth.lean`). -/
def PtBdDth (α : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ (A f : ℝ → ℝ → ℝ) (MA : ℝ),
    Work.FTS.EllipticEst.SmoothOpen A → Work.FTS.EllipticEst.SmoothOpen f →
    Work.Spaces.HkMem α 6 A → Work.Spaces.HkMem α 6 f → Work.Spaces.HkMem α 7 f →
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ MA) →
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.HkIntegrand α 6 (fun z θ => A z θ * Work.Spaces.Dth f z θ) z θ
        ≤ K * MA ^ 2 * Work.Spaces.HkIntegrand α 7 f z θ
          + K * (1 + (Work.Spaces.gam α - 1)⁻¹
              * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
            * (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ)
          + K * (Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 0 2 f z θ
              * Work.Spaces.Wt α z θ) ^ 2

/-- The pointwise master bound for `A · D_z f` (the content of `Tools/ptBoundDz.lean`). -/
def PtBdDz (α : ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ (A f : ℝ → ℝ → ℝ) (MA KA : ℝ),
    Work.FTS.EllipticEst.SmoothOpen A → Work.FTS.EllipticEst.SmoothOpen f →
    Work.Spaces.HkMem α 6 A → Work.Spaces.HkMem α 6 f → Work.Spaces.HkMem α 7 f →
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ MA) →
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Work.Spaces.pth A z θ| ≤ KA) →
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.HkIntegrand α 6 (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ
        ≤ K * MA ^ 2 * Work.Spaces.HkIntegrand α 7 f z θ
          + K * (1 + (Work.Spaces.gam α - 1)⁻¹
              * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
            * (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ)
          + K * KA ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
          + K * (Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 1 1 f z θ
              * Work.Spaces.Wt α z θ) ^ 2
          + K * (Work.Spaces.mixed 1 1 A z θ * Work.Spaces.DzIter 5 f z θ
              * Work.Spaces.Wt α z θ) ^ 2
          + K * (Work.Spaces.Dth A z θ * Work.Spaces.DzIter 5 f z θ
              * Work.Spaces.Wt α z θ) ^ 2
          + K * (Work.Spaces.DthIter 2 A z θ * Work.Spaces.DzIter 5 f z θ
              * Work.Spaces.Wt α z θ) ^ 2

/-- Almost every angle of `Iθ` is interior. -/
theorem ae_mem_Ioo_Iθ_fts : ∀ᵐ θ ∂(volume.restrict Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  have h := ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Ioo (a := (0 : ℝ))
    (b := Real.pi / 2))
  rwa [Measure.restrict_congr_set Ioo_ae_eq_Icc] at h

/-- Almost every radius of `Iz` is positive. -/
theorem ae_mem_Ioi_Iz_fts : ∀ᵐ z ∂(volume.restrict Iz), z ∈ Set.Ioi (0 : ℝ) := by
  have h := ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Ioi (a := (0 : ℝ)))
  rwa [Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))] at h

/-- Linearity of the integral over a sum of three functions (`Iθ`). -/
theorem integral_add_three {f g h : ℝ → ℝ}
    (hf : Integrable f (volume.restrict Iθ)) (hg : Integrable g (volume.restrict Iθ))
    (hh : Integrable h (volume.restrict Iθ)) :
    (∫ x in Iθ, (f x + g x + h x)) = (∫ x in Iθ, f x) + (∫ x in Iθ, g x)
      + (∫ x in Iθ, h x) := by
  have h2 : (∫ x in Iθ, (f x + g x) + h x) = (∫ x in Iθ, f x + g x)
      + (∫ x in Iθ, h x) := MeasureTheory.integral_add (hf.add hg) hh
  have h1 : (∫ x in Iθ, f x + g x) = (∫ x in Iθ, f x) + (∫ x in Iθ, g x) :=
    MeasureTheory.integral_add hf hg
  rw [h2, h1]

/-- Linearity of the integral over a sum of three functions (`Iz`). -/
theorem integral_add_three_z {f g h : ℝ → ℝ}
    (hf : Integrable f (volume.restrict Iz)) (hg : Integrable g (volume.restrict Iz))
    (hh : Integrable h (volume.restrict Iz)) :
    (∫ x in Iz, (f x + g x + h x)) = (∫ x in Iz, f x) + (∫ x in Iz, g x)
      + (∫ x in Iz, h x) := by
  have h2 : (∫ x in Iz, (f x + g x) + h x) = (∫ x in Iz, f x + g x)
      + (∫ x in Iz, h x) := MeasureTheory.integral_add (hf.add hg) hh
  have h1 : (∫ x in Iz, f x + g x) = (∫ x in Iz, f x) + (∫ x in Iz, g x) :=
    MeasureTheory.integral_add hf hg
  rw [h2, h1]

/-- `(γ-1)⁻¹ ≥ 10` for `0 < α ≤ 1`. -/
theorem ten_le_inv_gam_sub_one {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (10 : ℝ) ≤ (Work.Spaces.gam α - 1)⁻¹ := by
  have hsub : Work.Spaces.gam α - 1 = α / 10 := Work.Spaces.gam_sub_one α
  have hp : (0 : ℝ) < α / 10 := by linarith
  have hle : α / 10 ≤ 1 / 10 := by linarith
  have h := (inv_le_inv₀ (show (0 : ℝ) < 1 / 10 by norm_num) hp).mpr hle
  rw [show ((1 : ℝ) / 10)⁻¹ = 10 by norm_num] at h
  rwa [← hsub] at h

end Work.FTS.StrongEps.E4R3.Nblock6.Tools
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux.dens_tendsto_of_slot_tendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongEps.E5Aux

/-!
# Dominated convergence of the `θ`-integral defining `L₁₂^K`, from a pointwise slot bound

The angular density of the fundamental model is

`L12dens K f s = ∫_θ K(θ) f(s,θ) / s`   (`θ` over `Iθ = [0,π/2]`),

with `K(θ) = 3 sin θ cos²θ`.  This file shows that a *pointwise* domination of the
`(z,θ)`-slots `Yk k` by `C / sin(2θ)` — together with a.e. strong measurability and pointwise
convergence *on the open quadrant* `Qd = (0,∞) × (0,π/2)` — yields both the integrability of
every angular density `θ ↦ K θ * Yk k s θ` (for `s > 0`) and the convergence of the densities
`L12dens K (Yk k) s` at every `s > 0`, by the dominated convergence theorem.

The mechanism: on `Iθ` the domination collapses,

`K θ * (C / sin 2θ) = (3C/2) cos θ`   (`θ ∈ (0,π/2)`),

and `θ ↦ (3C/2) cos θ` is bounded (hence integrable on the finite measure `Iθ`).  At the two
endpoints `K` vanishes, so the pointwise bounds and the pointwise convergence extend to all of
`Iθ` without hypotheses; the only thing the pointwise convergence needs on the open quadrant is
continuity of multiplication by the constant `K θ`.
-/

/-- `[0,π/2]` is measurable. -/
private lemma Iθ_measurableSet : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc

/-- `cos θ ≥ 0` on `[0,π/2]`. -/
private lemma cos_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.cos θ :=
  Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩

/-- `K θ ≥ 0` on `[0,π/2]`. -/
private lemma K_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Spaces.K θ := by
  have hsin : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have h2 : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
  rw [Work.Spaces.K]
  nlinarith [hsin, h2]




end Work.FTS.StrongEps.E5Aux
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux.exists_dist_sPhi_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux

/-! ## The shift is jointly continuous on `K × (ball)` -/

/-- The three-variable map `(z, θ, q) ↦ sPhi z θ q` is continuous on `K × closedBall 0 1`
whenever `K ⊆ Quad` (the only obstruction to the *global* continuity of `sPhi` is the possible
vanishing of `cos θ`, which cannot happen on the quadrant). -/
private theorem continuousOn_sPhi_prod {K : Set (ℝ × ℝ)} (hKQ : K ⊆ Work.FTS.StrongEps.Quad) :
    ContinuousOn (fun x : (ℝ × ℝ) × (ℝ × ℝ) => Work.FTS.StrongEps.sPhi x.1.1 x.1.2 x.2)
      (K ×ˢ Metric.closedBall (0 : ℝ × ℝ) 1) := by
  have hproj : ContinuousOn (fun x : (ℝ × ℝ) × (ℝ × ℝ) => x.1.2)
      (K ×ˢ Metric.closedBall (0 : ℝ × ℝ) 1) :=
    (continuous_snd.comp continuous_fst).continuousOn
  have htan : ContinuousOn (fun x : (ℝ × ℝ) × (ℝ × ℝ) => Real.tan x.1.2)
      (K ×ˢ Metric.closedBall (0 : ℝ × ℝ) 1) := by
    refine Real.continuousOn_tan_Ioo.comp hproj ?_
    intro x hx
    simp only [Set.mem_prod] at hx
    simp only [Set.mem_Ioo]
    have h2 : x.1.2 ∈ Set.Ioo 0 (Real.pi / 2) :=
      (Work.FTS.StrongEps.mem_Quad.mp (hKQ hx.1)).2
    exact ⟨by linarith [h2.1, Real.pi_pos], by linarith [h2.2]⟩
  have h1 : ContinuousOn (fun x : (ℝ × ℝ) × (ℝ × ℝ) => Work.FTS.StrongEps.zShift x.1.1 x.2.1)
      (K ×ˢ Metric.closedBall (0 : ℝ × ℝ) 1) := by
    simp only [Work.FTS.StrongEps.zShift]
    fun_prop
  have h2 : ContinuousOn (fun x : (ℝ × ℝ) × (ℝ × ℝ) => Work.FTS.StrongEps.thShift x.1.2 x.2.2)
      (K ×ˢ Metric.closedBall (0 : ℝ × ℝ) 1) := by
    simp only [Work.FTS.StrongEps.thShift]
    exact Real.continuous_arctan.comp_continuousOn
      (htan.mul (by fun_prop : ContinuousOn
        (fun x : (ℝ × ℝ) × (ℝ × ℝ) => Real.exp (-x.2.2))
          (K ×ˢ Metric.closedBall (0 : ℝ × ℝ) 1)))
  have h := h1.prodMk h2
  refine h.congr ?_
  intro x _
  simp only [Work.FTS.StrongEps.sPhi, Work.FTS.StrongEps.zShift, Work.FTS.StrongEps.thShift]

/-- **The shift of the mollifier is uniformly close to the identity on a compact set.**  For every
compact `K` inside the open quadrant and every `η > 0` there is `δ > 0` such that for every
`p ∈ K` and every `q` with `‖q‖ ≤ δ`, the shifted point `sPhi p.1 p.2 q` is within `η` of `p`.

This is the Heine–Cantor statement for the joint continuity of `(p, q) ↦ sPhi p.1 p.2 q` on the
compact set `K × closedBall 0 1`, together with `sPhi p.1 p.2 0 = p`. -/
theorem exists_dist_sPhi_le {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKQ : K ⊆ Work.FTS.StrongEps.Quad) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ p ∈ K, ∀ q : ℝ × ℝ, ‖q‖ ≤ δ → dist (Work.FTS.StrongEps.sPhi p.1 p.2 q) p ≤ η := by
  have hsc : IsCompact (K ×ˢ Metric.closedBall (0 : ℝ × ℝ) 1) :=
    hK.prod (isCompact_closedBall 0 1)
  have huc : UniformContinuousOn
      (fun x : (ℝ × ℝ) × (ℝ × ℝ) => Work.FTS.StrongEps.sPhi x.1.1 x.1.2 x.2)
      (K ×ˢ Metric.closedBall (0 : ℝ × ℝ) 1) :=
    hsc.uniformContinuousOn_of_continuous (continuousOn_sPhi_prod hKQ)
  rw [Metric.uniformContinuousOn_iff_le] at huc
  obtain ⟨δ, hδ, hδprop⟩ := huc η hη
  refine ⟨min δ 1, lt_min hδ one_pos, fun p hp q hq => ?_⟩
  have hqB : q ∈ Metric.closedBall (0 : ℝ × ℝ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_trans hq (min_le_right _ _)
  have h0B : (0 : ℝ × ℝ) ∈ Metric.closedBall (0 : ℝ × ℝ) 1 := by
    rw [Metric.mem_closedBall, dist_self]
    norm_num
  have hdist : dist (p, q) (p, 0) ≤ δ := by
    rw [Prod.dist_eq, dist_self, dist_zero_right, max_eq_right (norm_nonneg q)]
    exact le_trans hq (min_le_left _ _)
  have hres := hδprop (p, q) ⟨hp, hqB⟩ (p, 0) ⟨hp, h0B⟩ hdist
  have hp2 : p.2 ∈ Set.Ioo 0 (Real.pi / 2) := (Work.FTS.StrongEps.mem_Quad.mp (hKQ hp)).2
  have hz : Work.FTS.StrongEps.sPhi p.1 p.2 0 = p := by
    rw [Work.FTS.StrongEps.sPhi_zero hp2]
  rwa [hz] at hres

end Work.FTS.StrongEps.E5Aux
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.DensTransportBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

theorem DensTransportBound :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 →
      ∀ {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {ε τ C₀ B : ℝ} {g : Fam} {Maj : ℝ → ℝ},
      Work.FTS.StrongEps.EpsDecay α ρ Φs E ε τ g Maj →
      Work.FTS.Nonlin.Xn α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) ≤ C₀ * α ^ 2 →
      Work.FTS.StrongGlobal.Xn6 α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) ≤ B →
      ∀ s ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.K θ * |Work.Coercivity.Transport (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) s θ|
          ≤ C * (1 + C₀) * (1 + B) * (Maj s + s / (1 + s) ^ 2) * Real.cos θ := by
  refine ⟨6, by norm_num, ?_⟩
  intro α hα ρ Φs E ε τ C₀ B g Maj hDec hXn hXn6 s hs θ hθ
  obtain ⟨hMaj0, hMaj1, -, hSlot1, -⟩ := hDec
  have hs0 : (0 : ℝ) < s := hs
  have hC₀0 : 0 ≤ C₀ := by
    have hX : 0 ≤ Work.FTS.Nonlin.Xn α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) :=
      Work.Spaces.HkNorm_nonneg α 4 _
    nlinarith [hX, hXn, pow_pos hα.1 2]
  have hB0 : 0 ≤ B := by
    have hX : 0 ≤ Work.FTS.StrongGlobal.Xn6 α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) :=
      Work.Spaces.HkNorm_nonneg α 6 _
    linarith
  have hA1 : 1 ≤ (1 + C₀) * (1 + B) := by nlinarith
  have hDth : |Work.Spaces.Dth (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) s θ| ≤ Maj s :=
    hSlot1 s hs θ 0 1 (by norm_num)
  have hTr : |Work.Coercivity.Transport (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) s θ|
      ≤ 3 * Maj s / (1 + s) := by
    have h1s : (0 : ℝ) < 1 + s := by linarith
    have h2 : Work.Coercivity.Transport (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) s θ
        = 3 * Work.Spaces.Dth (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) s θ / (1 + s) := rfl
    rw [h2, abs_div, abs_of_pos h1s, abs_mul]
    have h3 : |(3 : ℝ)| = 3 := by norm_num
    rw [h3]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hDth (by norm_num)) h1s.le
  obtain ⟨hKnn, hKcos, hcos0, -, -, -, -, -⟩ := AngFacts
  have hK0 : 0 ≤ Work.Spaces.K θ := hKnn θ hθ
  have hKle : Work.Spaces.K θ ≤ 2 * Real.cos θ := hKcos θ hθ
  have hc0 : 0 ≤ Real.cos θ := hcos0 θ hθ
  have hs2nn : 0 ≤ s / (1 + s) ^ 2 := div_nonneg hs0.le (sq_nonneg _)
  set Q : ℝ := Maj s + s / (1 + s) ^ 2 with hQdef
  have hQ0 : 0 ≤ Q := by rw [hQdef]; linarith [hMaj0 s]
  have hQge : Maj s ≤ Q := by rw [hQdef]; linarith
  have h1s : (0 : ℝ) < 1 + s := by linarith
  have hle3 : 3 * Maj s / (1 + s) ≤ 3 * Maj s := by
    rw [div_le_iff₀ h1s]
    nlinarith [hMaj0 s]
  have hstep : Work.Spaces.K θ * |Work.Coercivity.Transport
      (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) s θ| ≤ 6 * Q * Real.cos θ := by
    have h1 : Work.Spaces.K θ * |Work.Coercivity.Transport
        (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) s θ| ≤ Work.Spaces.K θ * (3 * Maj s / (1 + s)) :=
      mul_le_mul_of_nonneg_left hTr hK0
    have h2 : Work.Spaces.K θ * (3 * Maj s / (1 + s)) ≤ Work.Spaces.K θ * (3 * Maj s) :=
      mul_le_mul_of_nonneg_left hle3 hK0
    have h3 : Work.Spaces.K θ * (3 * Maj s) ≤ (2 * Real.cos θ) * (3 * Maj s) :=
      mul_le_mul_of_nonneg_right hKle (by linarith [hMaj0 s])
    have h4 : (2 * Real.cos θ) * (3 * Maj s) ≤ 6 * Q * Real.cos θ := by
      rw [hQdef]; nlinarith [hMaj0 s, hc0, hs2nn]
    linarith [h1, h2, h3, h4]
  have hfin : 6 * Q * Real.cos θ ≤ 6 * (1 + C₀) * (1 + B) * Q * Real.cos θ := by
    have h0 : 0 ≤ Q * Real.cos θ := mul_nonneg hQ0 hc0
    have h1 : 1 * (Q * Real.cos θ) ≤ ((1 + C₀) * (1 + B)) * (Q * Real.cos θ) :=
      mul_le_mul_of_nonneg_right hA1 h0
    nlinarith [h1]
  rw [hQdef] at hstep ⊢
  linarith [hstep, hfin]

end Work.FTS.StrongEps.E5Aux2
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.ThetaDiff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2

/-
The difference of the `Theta`-parts of the profiles `f` and `F_* + f`:
`Theta α F z θ = (1/(4α)) * sin (2θ) * L12 F z` and
`L12 (fun z θ => Fstar α z θ + f z θ) z = L12 (Fstar α) z + L12 f z`
(`Work.FTS_RegExport.RXT.L12_Fstar_add_c4`, whose hypotheses are exactly
`ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0` and `Work.Spaces.HkMem α 4 f`,
both available from `ClassC α f` via `hf.reg.forall 4` and
`Work.FTS.OpenPkg.HkMem_mono_open hf.reg 4 (by norm_num) hf.mem`), together with
`Work.Construction.L12_Fstar_eq hα hα1 hz.le : L12 (Fstar α) z = 2 * α / (1 + z)`.
-/
theorem ThetaDiff {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.ClassC.ClassC α f) :
    ∀ z θ : ℝ, 0 < z →
      Work.Construction.Theta α f z θ
        - Work.Construction.Theta α (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
      = -Real.sin (2 * θ) / (2 * (1 + z)) := by
  intro z θ hz
  -- `f` is `C^4` on the open quadrant and honestly in `ℋ⁴`
  have hcd : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0 := hf.reg.forall 4
  have hmem : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hf.reg 4 (by norm_num) hf.mem
  -- additivity of `L₁₂` over `F_* + f`
  have hadd : Work.Construction.L12 (fun z θ => Work.Construction.Fstar α z θ + f z θ) z
      = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 f z :=
    Work.FTS_RegExport.RXT.L12_Fstar_add_c4 hα hα1 hcd hmem hz.le
  -- the reference value `L₁₂(F_*) = 2α/(1+z)`
  have hF : Work.Construction.L12 (Work.Construction.Fstar α) z = 2 * α / (1 + z) :=
    Work.Construction.L12_Fstar_eq hα hα1 hz.le
  simp only [Work.Construction.Theta, Work.Construction.s2, hadd, hF]
  field_simp
  ring

end Work.FTS.StrongEps.E5Aux2
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux3.epsRHSP_dens_aesm_prod =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongEps.E5Aux3

set_option autoImplicit false

/-! ## The measure-theoretic toolbox for the triple product measure

The measure carried by the fake-time box is
`(dτ)|_{[0,T]} ⊗ (dz)|_{(0,∞)} ⊗ (dθ)|_{[0,π/2]}` on `ℝ × (ℝ × ℝ)` with the coordinate
order `(τ, (z, θ))`.  It is the restriction of the product Lebesgue measure to the *open*
box `(0,T) × (0,∞) × (0,π/2)`: the three factors `[0,T]`, `(0,∞)`, `[0,π/2]` differ from
`(0,T)`, `(0,∞)`, `(0,π/2)` only by null sets (`{0,T}`, `∅`, `{0,π/2}`). -/

/-- The product of the three restricted Lebesgue measures is the restriction of the product
Lebesgue measure to the open box `(0,T) × (0,∞) × (0,π/2)`. -/
private lemma restrict_prod_eq (T : ℝ) :
    ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = (MeasureTheory.volume.prod (MeasureTheory.volume.prod MeasureTheory.volume)).restrict
          (Set.Ioo (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))) := by
  have hA : (Set.Icc (0 : ℝ) T) =ᵐ[MeasureTheory.volume] Set.Ioo (0 : ℝ) T :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := (MeasureTheory.volume : Measure ℝ))
      (a := (0 : ℝ)) (b := T)).symm
  have hB : ((Set.Ioi (0 : ℝ)) : Set ℝ) =ᵐ[MeasureTheory.volume] Set.Ioi 0 :=
    Filter.EventuallyEq.rfl
  have hC : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := (MeasureTheory.volume : Measure ℝ))
      (a := (0 : ℝ)) (b := π / 2)).symm
  have hBC : ((Set.Ioi (0 : ℝ) ×ˢ Work.Spaces.Iθ) : Set (ℝ × ℝ))
      =ᵐ[MeasureTheory.volume.prod MeasureTheory.volume]
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    MeasureTheory.Measure.set_prod_ae_eq hB hC
  have hprod : ((Set.Icc (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Work.Spaces.Iθ)) :
        Set (ℝ × (ℝ × ℝ)))
      =ᵐ[MeasureTheory.volume.prod (MeasureTheory.volume.prod MeasureTheory.volume)]
        (Set.Ioo (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))) :=
    MeasureTheory.Measure.set_prod_ae_eq hA hBC
  have hmain : (MeasureTheory.volume.prod (MeasureTheory.volume.prod MeasureTheory.volume)).restrict
        (Set.Icc (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Work.Spaces.Iθ))
      = (MeasureTheory.volume.prod (MeasureTheory.volume.prod MeasureTheory.volume)).restrict
        (Set.Ioo (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))) :=
    MeasureTheory.Measure.restrict_congr_set hprod
  rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.prod_restrict]
  exact hmain

/-- The open box `(0,T) × (0,∞) × (0,π/2)` is measurable. -/
private lemma measurableSet_box (T : ℝ) :
    MeasurableSet (Set.Ioo (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))) :=
  (isOpen_Ioo.prod (isOpen_Ioi.prod isOpen_Ioo)).measurableSet

/-- A function continuous on the open box is a.e. strongly measurable for the triple product
measure of the fake-time box. -/
private lemma aesm_prod3_of_continuousOn {T : ℝ} {f : ℝ × (ℝ × ℝ) → ℝ}
    (hf : ContinuousOn f
      (Set.Ioo (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)))) :
    MeasureTheory.AEStronglyMeasurable f
      ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
  rw [restrict_prod_eq T]
  exact hf.aestronglyMeasurable (measurableSet_box T)

/-- Two functions agreeing on the open box agree a.e. for the triple product measure. -/
private lemma ae_eq_of_eqOn_box {T : ℝ} {f h : ℝ × (ℝ × ℝ) → ℝ}
    (hfh : Set.EqOn f h
      (Set.Ioo (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)))) :
    f =ᵐ[(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))] h := by
  rw [restrict_prod_eq T]
  exact hfh.aeEq_restrict (measurableSet_box T)

/-- The one-variable time derivative of a function on `ℝ × ℝ × ℝ` is the Fréchet derivative
in the direction of its third coordinate. -/
private lemma deriv_slice_eq_fderiv {G : ℝ × ℝ × ℝ → ℝ} {p : ℝ × ℝ × ℝ}
    (h : DifferentiableAt ℝ G p) :
    deriv (fun s : ℝ => G (p.1, (p.2.1, s))) p.2.2 = fderiv ℝ G p (0, (0, 1)) := by
  have hL : HasDerivAt (fun s : ℝ => (p.1, (p.2.1, s))) ((0 : ℝ), (0 : ℝ), (1 : ℝ)) p.2.2 := by
    simpa using (hasDerivAt_const (x := p.2.2) (c := p.1)).prodMk
      ((hasDerivAt_const (x := p.2.2) (c := p.2.1)).prodMk (hasDerivAt_id p.2.2))
  simpa only [Function.comp_def] using (h.hasFDerivAt.comp_hasDerivAt p.2.2 hL).deriv

/-! ## The lemma -/

/-- **A.e. strong measurability of the angular density of the projected scheme.**

`epsRHSP` is a convolution, so its measurability is *not* hereditary in the parameters: `E` is
an arbitrary map.  What makes the statement true is the scheme equation `hsol`: at every point
of the open box `(0,T) × (0,∞) × (0,π/2)` the right-hand side `epsRHSP … τ z θ` *equals* the
time derivative of the datum, and that derivative is continuous there because `g` is jointly
`C¹` on the box (`hcont`).  So the density agrees a.e. with a continuous function, and the
three restrictions of Lebesgue measure see the box up to a null set. -/
theorem epsRHSP_dens_aesm_prod {α T ε : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g₀ : Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g)
    (hcont : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T)) :
    MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × (ℝ × ℝ) => Work.Spaces.K q.2.2 *
        Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g q.1 q.2.1 q.2.2 / q.2.1)
      ((MeasureTheory.volume.restrict (Set.Icc 0 T)).prod
        ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
  -- On the open box the right-hand side is the time derivative of the datum.
  have hbox : ∀ q ∈ Set.Ioo (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)),
      Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g q.1 q.2.1 q.2.2
        = deriv (fun s => g q.2.1 q.2.2 s) q.1 := by
    intro q hq
    rw [Set.mem_prod] at hq
    obtain ⟨hτ, hq2⟩ := hq
    rw [Set.mem_prod] at hq2
    obtain ⟨hz, hθ⟩ := hq2
    exact ((hsol.2 q.2.1 q.2.2 q.1 hz hθ ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩).hasDerivAt
      (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hτ) Set.Ioo_subset_Icc_self)).deriv.symm
  -- On the open box the datum is differentiable, so the time derivative is the Fréchet
  -- derivative in the time direction.
  have hdiff : ∀ q ∈ Set.Ioo (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)),
      DifferentiableAt ℝ (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) (q.2.1, (q.2.2, q.1)) := by
    intro q hq
    rw [Set.mem_prod] at hq
    obtain ⟨hτ, hq2⟩ := hq
    rw [Set.mem_prod] at hq2
    obtain ⟨hz, hθ⟩ := hq2
    have hmem : (q.2.1, (q.2.2, q.1)) ∈
        interior (Set.Ioi (0 : ℝ) ×ˢ (Set.Ioo (0 : ℝ) (π / 2) ×ˢ Set.Icc (0 : ℝ) T)) := by
      rw [interior_prod_eq, interior_prod_eq, isOpen_Ioi.interior_eq, isOpen_Ioo.interior_eq,
        interior_Icc]
      exact ⟨hz, hθ, hτ⟩
    exact (hcont.differentiableOn (by norm_num)).differentiableAt
      (Filter.mem_of_superset (isOpen_interior.mem_nhds hmem) interior_subset)
  -- The Fréchet derivative in the time direction is continuous on the open box: `g` is `C¹`
  -- on an open neighbourhood of every point of the box, and the Fréchet derivative of a `C¹`
  -- function is continuous.
  have hcont_fderiv : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      fderiv ℝ (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) (q.2.1, (q.2.2, q.1)) (0, (0, 1)))
      (Set.Ioo (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))) := by
    have hVopen : IsOpen
        (interior (Set.Ioi (0 : ℝ) ×ˢ (Set.Ioo (0 : ℝ) (π / 2) ×ˢ Set.Icc (0 : ℝ) T))) :=
      isOpen_interior
    have hFV : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
        (interior (Set.Ioi (0 : ℝ) ×ˢ (Set.Ioo (0 : ℝ) (π / 2) ×ˢ Set.Icc (0 : ℝ) T))) :=
      hcont.mono interior_subset
    have hfd : ContDiffOn ℝ 0 (fun p : ℝ × ℝ × ℝ =>
        fderiv ℝ (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) p)
        (interior (Set.Ioi (0 : ℝ) ×ˢ (Set.Ioo (0 : ℝ) (π / 2) ×ˢ Set.Icc (0 : ℝ) T))) := by
      have h := hFV.fderivWithin (m := 0) (hVopen.uniqueDiffOn (𝕜 := ℝ)) (by simp)
      refine h.congr ?_
      intro p hp
      rw [fderivWithin_of_isOpen hVopen hp]
    have hfd2 : ContDiffOn ℝ 0 (fun p : ℝ × ℝ × ℝ =>
        fderiv ℝ (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) p (0, (0, 1)))
        (interior (Set.Ioi (0 : ℝ) ×ˢ (Set.Ioo (0 : ℝ) (π / 2) ×ˢ Set.Icc (0 : ℝ) T))) :=
      hfd.clm_apply (contDiffOn_const (c := ((0 : ℝ), (0 : ℝ), (1 : ℝ))))
    have hmap : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => (q.2.1, (q.2.2, q.1)))
        (Set.Ioo (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))) := by fun_prop
    have hmaps : MapsTo (fun q : ℝ × (ℝ × ℝ) => (q.2.1, (q.2.2, q.1)))
        (Set.Ioo (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)))
        (interior (Set.Ioi (0 : ℝ) ×ˢ (Set.Ioo (0 : ℝ) (π / 2) ×ˢ Set.Icc (0 : ℝ) T))) := by
      intro q hq
      rw [Set.mem_prod] at hq
      obtain ⟨hτ, hq2⟩ := hq
      rw [Set.mem_prod] at hq2
      obtain ⟨hz, hθ⟩ := hq2
      rw [interior_prod_eq, interior_prod_eq, isOpen_Ioi.interior_eq, isOpen_Ioo.interior_eq,
        interior_Icc]
      exact ⟨hz, hθ, hτ⟩
    exact hfd2.continuousOn.comp hmap hmaps
  -- hence the time derivative itself is continuous on the open box
  have hcont_deriv : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      deriv (fun s => g q.2.1 q.2.2 s) q.1)
      (Set.Ioo (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))) :=
    hcont_fderiv.congr (fun q hq => deriv_slice_eq_fderiv (hdiff q hq))
  -- and so is the whole density with `epsRHSP` replaced by that derivative
  have hcont_repl : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Work.Spaces.K q.2.2 * deriv (fun s => g q.2.1 q.2.2 s) q.1 / q.2.1)
      (Set.Ioo (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))) := by
    have hK : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => Work.Spaces.K q.2.2)
        (Set.Ioo (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))) := by
      have hKc : Continuous (fun q : ℝ × (ℝ × ℝ) => Work.Spaces.K q.2.2) := by
        unfold Work.Spaces.K
        fun_prop
      exact hKc.continuousOn
    have hden : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => q.2.1)
        (Set.Ioo (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))) := by fun_prop
    refine (hK.mul hcont_deriv).div hden ?_
    intro q hq
    rw [Set.mem_prod] at hq
    obtain ⟨-, hq2⟩ := hq
    rw [Set.mem_prod] at hq2
    exact ne_of_gt hq2.1
  -- the two densities agree on the open box
  have heq : Set.EqOn
      (fun q : ℝ × (ℝ × ℝ) => Work.Spaces.K q.2.2 *
        Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g q.1 q.2.1 q.2.2 / q.2.1)
      (fun q : ℝ × (ℝ × ℝ) => Work.Spaces.K q.2.2 *
        deriv (fun s => g q.2.1 q.2.2 s) q.1 / q.2.1)
      (Set.Ioo (0 : ℝ) T ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))) := by
    intro q hq
    simp only [hbox q hq]
  exact (aesm_prod3_of_continuousOn hcont_repl).congr (ae_eq_of_eqOn_box heq).symm

end Work.FTS.StrongEps.E5Aux3
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux3.epsRHSP_dens_aesm_slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongEps.E5Aux3

/-!
# `Work.FTS.StrongEps.E5Aux3.epsRHSP_dens_aesm_slice`

**Joint a.e. strong measurability of the averaged angular density of a `IsEpsSolP` family.**

The scheme `IsEpsSolP` provides the fake-time derivative of `g` only through the
*within-`Icc 0 T`* derivative of the pointwise function `τ ↦ g z θ τ`; the value of that
derivative, `epsRHSP α ρ ε Φs E g σ z θ`, is therefore **not** known to be measurable in
`(z,θ)` (a derivative is not a continuous function of its base point) and the hypothesis
`hcont` does not mention it.  It is nevertheless a.e.-strongly-measurable, because it is an
a.e. limit of *continuous* difference quotients of the family slices, which `hcont` does
control.

Route.  Fix the time `σ ∈ (0,T)` and the sequence `ts n = σ + (T-σ)/(n+1) ↓ σ`, which lies in
`Icc 0 T \ {σ}`.  On the open quadrant `S = Ioi 0 ×ˢ Ioo 0 (π/2)` each difference quotient

  `p ↦ slope (fun s => (K p.2 / p.1) * g p.1 p.2 s) σ (ts n)`

is continuous (`K` continuous, `g ∘ (p ↦ (p.1,p.2,ts n))` continuous by `hcont`, `p.1 ≠ 0`),
hence a.e.-strongly-measurable for `(volume|_(Ioi 0)).prod (volume|_Iθ)` once one rewrites that
measure as the restriction of the planar Lebesgue measure to `Ioi 0 ×ˢ Iθ`, which agrees with
`S` up to the null set `Ioi 0 ×ˢ {0, π/2}`.  Finally, for a.e. `p` of the quadrant the sequence
converges to `K p.2 * epsRHSP … σ p.1 p.2 / p.1`, by `hsol` (the base point `σ` is interior, so
the within-`Icc 0 T` derivative is a genuine derivative) combined with
`hasDerivWithinAt_iff_tendsto_slope`, and `aestronglyMeasurable_of_tendsto_ae` concludes.

Note on the statement: the angular cut-off `π / 2` in `hcont` is the notation for `Real.pi / 2`
(the file opens `scoped Real`), matching `Work.Spaces.Iθ = Icc 0 (Real.pi / 2)`.
-/
theorem epsRHSP_dens_aesm_slice {α T ε : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g₀ : Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g)
    (hcont : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T))
    {σ : ℝ} (hσ : σ ∈ Set.Ioo 0 T) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 *
        Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g σ p.1 p.2 / p.1)
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- the open quadrant and the approximating times
  set S : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) with hSdef
  set ts : ℕ → ℝ := fun n => σ + (T - σ) / ((n : ℝ) + 1) with htsdef
  have hTσ : 0 < T - σ := by linarith [hσ.2]
  have hIcc : σ ∈ Set.Icc (0 : ℝ) T := ⟨hσ.1.le, hσ.2.le⟩
  have hts_eq : ∀ n : ℕ, ts n = σ + (T - σ) / ((n : ℝ) + 1) := fun n => by simp only [htsdef]
  have hts_mem : ∀ n : ℕ, ts n ∈ Set.Icc (0 : ℝ) T := by
    intro n
    have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hq0 : 0 < (T - σ) / ((n : ℝ) + 1) := div_pos hTσ hden
    have hq : (T - σ) / ((n : ℝ) + 1) ≤ T - σ := by
      rw [div_le_iff₀ hden]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
    rw [hts_eq n]
    exact ⟨by linarith [hσ.1], by linarith⟩
  have hts_ne : ∀ n : ℕ, ts n ≠ σ := by
    intro n h
    have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hq0 : 0 < (T - σ) / ((n : ℝ) + 1) := div_pos hTσ hden
    rw [hts_eq n] at h
    linarith
  have hts_tend : Tendsto ts atTop (𝓝 σ) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      Filter.tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop (R := ℝ))
    have h2 : Tendsto (fun n : ℕ => (T - σ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds h1
    have h3 : Tendsto (fun n : ℕ => σ + (T - σ) / ((n : ℝ) + 1)) atTop (𝓝 (σ + 0)) :=
      h2.const_add σ
    rw [htsdef]
    simpa only [add_zero] using h3
  have hts_within : Tendsto ts atTop (𝓝[Set.Icc (0 : ℝ) T \ {σ}] σ) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within ts hts_tend
      (Eventually.of_forall fun n => ⟨hts_mem n, hts_ne n⟩)
  -- membership in the open quadrant
  have hS_mem : ∀ p : ℝ × ℝ, p ∈ S ↔ 0 < p.1 ∧ p.2 ∈ Set.Ioo 0 (π / 2) := by
    intro p
    rw [hSdef, Set.mem_prod, Set.mem_Ioi]
  -- the multiplier `K p.2 / p.1` is continuous on the quadrant
  have hKc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2 / p.1) S := by
    refine ((continuous_K.comp continuous_snd).continuousOn).div continuous_fst.continuousOn ?_
    intro p hp
    exact ne_of_gt ((hS_mem p).mp hp).1
  -- the slices of the family are continuous on the quadrant
  have hgc : ∀ τ ∈ Set.Icc (0 : ℝ) T, ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2 τ) S := by
    intro τ hτ
    have hmap : ContinuousOn (fun p : ℝ × ℝ => (p.1, (p.2, τ))) S :=
      (continuous_fst.prodMk (continuous_snd.prodMk continuous_const)).continuousOn
    refine (hcont.continuousOn).comp hmap ?_
    intro p hp
    exact ⟨((hS_mem p).mp hp).1, ((hS_mem p).mp hp).2, hτ⟩
  -- the (unfolded) difference quotients are continuous on the quadrant
  have hφc : ∀ n : ℕ, ContinuousOn (fun p : ℝ × ℝ => (ts n - σ)⁻¹ *
      (Work.Spaces.K p.2 / p.1 * g p.1 p.2 (ts n) - Work.Spaces.K p.2 / p.1 * g p.1 p.2 σ)) S :=
    fun n => ((hKc.mul (hgc (ts n) (hts_mem n))).sub
      (hKc.mul (hgc σ hIcc))).const_mul ((ts n - σ)⁻¹)
  -- hence the difference quotients in `slope` form are continuous on the quadrant
  have hφs : ∀ n : ℕ, ContinuousOn (fun p : ℝ × ℝ =>
      slope (fun s : ℝ => (Work.Spaces.K p.2 / p.1) * g p.1 p.2 s) σ (ts n)) S := by
    intro n
    have heq : ∀ p ∈ S, slope (fun s : ℝ => (Work.Spaces.K p.2 / p.1) * g p.1 p.2 s) σ (ts n)
        = (ts n - σ)⁻¹ * (Work.Spaces.K p.2 / p.1 * g p.1 p.2 (ts n)
            - Work.Spaces.K p.2 / p.1 * g p.1 p.2 σ) := by
      intro p hp
      simp only [slope, vsub_eq_sub, smul_eq_mul]
    exact ContinuousOn.congr (hφc n) heq
  -- the product measure is the planar Lebesgue measure restricted to the quadrant, up to null
  have hθae : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := π / 2)).symm
  have hprod : (Set.Ioi (0 : ℝ) ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ)) =ᵐ[volume.prod volume] S := by
    rw [hSdef]
    exact MeasureTheory.Measure.set_prod_ae_eq (Filter.EventuallyEq.refl _ _) hθae
  have hS_meas : MeasurableSet S := (isOpen_Ioi.prod isOpen_Ioo).measurableSet
  -- each difference quotient is a.e.-strongly-measurable
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun p : ℝ × ℝ =>
      slope (fun s : ℝ => (Work.Spaces.K p.2 / p.1) * g p.1 p.2 s) σ (ts n))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ)) := by
    intro n
    rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.restrict_congr_set hprod]
    exact (hφs n).aestronglyMeasurable hS_meas
  -- the quadrant is conull
  have haeS : ∀ᵐ p ∂((volume.restrict (Set.Ioi 0)).prod
      (volume.restrict Work.Spaces.Iθ)), p ∈ S := by
    rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.restrict_congr_set hprod]
    exact MeasureTheory.self_mem_ae_restrict hS_meas
  -- and the a.e. limit is the angular density of the right-hand side
  have hlim : ∀ᵐ p ∂((volume.restrict (Set.Ioi 0)).prod
      (volume.restrict Work.Spaces.Iθ)),
      Tendsto (fun n : ℕ => slope (fun s : ℝ => (Work.Spaces.K p.2 / p.1) * g p.1 p.2 s) σ (ts n))
        atTop (𝓝 (Work.Spaces.K p.2 * epsRHSP α ρ ε Φs E g σ p.1 p.2 / p.1)) := by
    filter_upwards [haeS] with p hp
    obtain ⟨hp1, hp2⟩ := (hS_mem p).mp hp
    have h1 : HasDerivWithinAt (fun s : ℝ => (Work.Spaces.K p.2 / p.1) * g p.1 p.2 s)
        ((Work.Spaces.K p.2 / p.1) * epsRHSP α ρ ε Φs E g σ p.1 p.2) (Set.Icc 0 T) σ :=
      (hsol.2 p.1 p.2 σ hp1 hp2 hIcc).const_mul (Work.Spaces.K p.2 / p.1)
    have h2 := (hasDerivWithinAt_iff_tendsto_slope.mp h1).comp hts_within
    have h3 : (Work.Spaces.K p.2 / p.1) * epsRHSP α ρ ε Φs E g σ p.1 p.2
        = Work.Spaces.K p.2 * epsRHSP α ρ ε Φs E g σ p.1 p.2 / p.1 := by ring
    rw [h3] at h2
    exact h2
  exact aestronglyMeasurable_of_tendsto_ae atTop hmeas hlim

end Work.FTS.StrongEps.E5Aux3
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.integral_mixed_mul_adjMixed_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

/-! ## The bridge between the set integral over `Q0` and the measure `Qμ`

The adjointness of `mixed j i = D_z^j D_θ^i` is available in the open-quadrant class in
`Work.FTS.OpenPkg.integral_mixed_mul_adjMixed_of_contDiffOn`, but phrased with the product
measure `Qμ = (volume ↾ Iz).prod (volume ↾ Iθ)`.  The statement below instead integrates over
the *open* quadrant `Q0` with the ambient volume.  The two agree on functions supported in
`Q0`, because `Q0 ⊆ Iz ×ˢ Iθ` and `Qμ = volume ↾ (Iz ×ˢ Iθ)`. -/

/-- For a function supported on the open quadrant, the set integral over `Work.FTS.EllipticEst.Q0`
(with the ambient volume) coincides with the integral against `Qμ`. -/
theorem setIntegral_Q0_eq_integral_Qμ {F : ℝ × ℝ → ℝ}
    (hF : ∀ p : ℝ × ℝ, p ∉ Work.FTS.EllipticEst.Q0 → F p = 0) :
    (∫ p in Work.FTS.EllipticEst.Q0, F p) = ∫ p, F p ∂Work.FTS.Apriori.Limit.Qμ := by
  have hsub : Work.FTS.EllipticEst.Q0 ⊆ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ := by
    intro p hp
    rw [Work.FTS.EllipticEst.mem_Q0] at hp
    refine Set.mem_prod.mpr ⟨?_, ?_⟩
    · rw [Work.Spaces.Iz]; exact Set.mem_Ici.mpr (le_of_lt hp.1)
    · rw [Work.Spaces.Iθ]; exact Set.mem_Icc.mpr ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩
  have hQμ : Work.FTS.Apriori.Limit.Qμ
      = (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
          (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    rw [Work.FTS.Apriori.Limit.Qμ, MeasureTheory.Measure.prod_restrict,
      ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  have hr : Work.FTS.Apriori.Limit.Qμ.restrict Work.FTS.EllipticEst.Q0
      = (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
          Work.FTS.EllipticEst.Q0 := by
    rw [hQμ, MeasureTheory.Measure.restrict_restrict_of_subset hsub]
  rw [← hr]
  exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hF

/-! ## The adjoints do not increase the support

Both sides of the identity are supported in the closed support of `ψ`, which lies in `Q0`;
this is what lets the two integrals be read against `Qμ`. -/

/-- The support of the iterated `z`-adjoint is contained in the closed support of the
function. -/
theorem support_adjDzIter_subset_tsupport (j : ℕ) (ψ : ℝ → ℝ → ℝ) :
    Function.support (Function.uncurry (Work.FTS.Apriori.Limit.adjDzIter j ψ))
      ⊆ tsupport (Function.uncurry ψ) := by
  induction j generalizing ψ with
  | zero => exact subset_tsupport _
  | succ j ih =>
      refine (ih (Work.FTS.Apriori.Limit.adjZ ψ)).trans ?_
      exact (closure_mono (Work.FTS.Apriori.Limit.support_adjZ_subset ψ)).trans_eq
        (IsClosed.closure_eq (isClosed_tsupport _))

/-- The support of the iterated `θ`-adjoint is contained in the closed support of the
function. -/
theorem support_adjDthIter_subset_tsupport (i : ℕ) (ψ : ℝ → ℝ → ℝ) :
    Function.support (Function.uncurry (Work.FTS.Apriori.Limit.adjDthIter i ψ))
      ⊆ tsupport (Function.uncurry ψ) := by
  induction i generalizing ψ with
  | zero => exact subset_tsupport _
  | succ i ih =>
      refine (ih (Work.FTS.Apriori.Limit.adjTh ψ)).trans ?_
      exact (closure_mono (Work.FTS.Apriori.Limit.support_adjTh_subset ψ)).trans_eq
        (IsClosed.closure_eq (isClosed_tsupport _))

/-- The closed support of the iterated `z`-adjoint is contained in the closed support of the
function. -/
theorem tsupport_adjDzIter_subset (j : ℕ) (ψ : ℝ → ℝ → ℝ) :
    tsupport (Function.uncurry (Work.FTS.Apriori.Limit.adjDzIter j ψ))
      ⊆ tsupport (Function.uncurry ψ) :=
  (closure_mono (support_adjDzIter_subset_tsupport j ψ)).trans_eq
    (IsClosed.closure_eq (isClosed_tsupport _))

/-- The closed support of `adjMixed (j,i) ψ` is contained in the closed support of `ψ`. -/
theorem support_adjMixed_subset_tsupport (j i : ℕ) (ψ : ℝ → ℝ → ℝ) :
    Function.support (Function.uncurry (Work.FTS.Apriori.Limit.adjMixed (j, i) ψ))
      ⊆ tsupport (Function.uncurry ψ) :=
  (support_adjDthIter_subset_tsupport i (Work.FTS.Apriori.Limit.adjDzIter j ψ)).trans
    (tsupport_adjDzIter_subset j ψ)

/-- The adjointness of `mixed j i = D_z^j D_θ^i` over the open quadrant, for a source that is
`C^∞` on the open quadrant and a test function of compact support inside it. -/
theorem integral_mixed_mul_adjMixed_open {g ψ : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hψ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ))
    (hcs : HasCompactSupport (Function.uncurry ψ))
    (hts : tsupport (Function.uncurry ψ) ⊆ Work.FTS.EllipticEst.Q0)
    (j i : ℕ) :
    ∫ p in Work.FTS.EllipticEst.Q0, Work.Spaces.mixed j i g p.1 p.2 * ψ p.1 p.2
      = ∫ p in Work.FTS.EllipticEst.Q0, g p.1 p.2
          * Work.FTS.Apriori.Limit.adjMixed (j, i) ψ p.1 p.2 := by
  -- `ψ` is a test function of the limit chapter (`Q0` and `Qd` are the same set)
  have hg' : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g)
      Work.FTS.Apriori.Limit.Qd := hg
  have hψ' : Work.FTS.Apriori.Limit.TestQ ψ := by
    refine ⟨?_, hcs, hts⟩
    exact contDiffOn_iff_forall_nat_le.mpr (fun n _ => (hψ n).contDiffOn)
  have key := Work.FTS.OpenPkg.integral_mixed_mul_adjMixed_of_contDiffOn hg' hψ' j i
  -- both integrands vanish off the (open) quadrant `Q0`
  have hF1 : ∀ p : ℝ × ℝ, p ∉ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.mixed j i g p.1 p.2 * ψ p.1 p.2 = 0 := by
    intro p hp
    have hψ0 : ψ p.1 p.2 = 0 := by
      by_contra h
      exact hp (hts (subset_tsupport (Function.uncurry ψ) (by
        show Function.uncurry ψ p ≠ 0
        exact h)))
    rw [hψ0, mul_zero]
  have hF2 : ∀ p : ℝ × ℝ, p ∉ Work.FTS.EllipticEst.Q0 →
      g p.1 p.2 * Work.FTS.Apriori.Limit.adjMixed (j, i) ψ p.1 p.2 = 0 := by
    intro p hp
    have hadj : Work.FTS.Apriori.Limit.adjMixed (j, i) ψ p.1 p.2 = 0 := by
      by_contra h
      exact hp (hts (support_adjMixed_subset_tsupport j i ψ (by
        show Function.uncurry (Work.FTS.Apriori.Limit.adjMixed (j, i) ψ) p ≠ 0
        exact h)))
    rw [hadj, mul_zero]
  rw [setIntegral_Q0_eq_integral_Qμ hF1, setIntegral_Q0_eq_integral_Qμ hF2, key]

end Work.FTS.StrongEps.E5G
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux.FubiniSwap =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Fubini swap for `Fstar (Jeps ρ ε W)`

`J_ε W` is, in the log coordinates, the convolution of `W` with the rescaled kernel `Jker ρ ε`,
which is supported in the closed ball of radius `ε`.  Hence the angular moment
`F_*(z) = ∫_{Iθ} (J_ε W)(z,θ) sin θ cos²θ dθ` is the triple integral

  `∫_{θ} ∫_{p₂} ∫_{p₁} sinCos2 θ · Jker ρ ε (p₁,p₂) · W (z e^{-p₁}) (thShift θ p₂)`

over `θ ∈ Iθ = [0,π/2]`, `|p₂| ≤ ε`, `p₁ ∈ ℝ`, and Fubini's theorem reorders it to

  `∫_{(θ,p₂)} sinCos2 θ · ∫_{p₁} Jker ρ ε (p₁,p₂) · W (z e^{-p₁}) (thShift θ p₂)`,

which is exactly the right hand side of `FubiniSwap` (a `p₁`-convolution at each log-angle).

The exchange is legitimate because the whole integrand is dominated by
`B · sinCos2 θ · G (thShift θ p₂)`, where `B` bounds the `p₁`-slices of the kernel
(`exists_bound_integral_Jker_slice`) and `sinCos2 θ · G (thShift θ p₂)` is integrable on
`Iθ × [-ε,ε]` by hypothesis (`hint`); the measurable structure is supplied by
`measurable_indicator_of_continuousOn` (the profile `W` is only assumed smooth on the *open*
quadrant, so it is extended by `0` off it).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux

/-! ### small local helpers -/

/-- `sin θ cos²θ ≥ 0` on `(0, π/2)`. -/
theorem sinCos2_nonneg_local {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  have hsin0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨le_of_lt hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  rw [Work.Elliptic.sinCos2]
  exact mul_nonneg hsin0 (sq_nonneg _)

/-- The rescaled kernel is nonnegative. -/
theorem Jker_nonneg_local {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ) (ε : ℝ)
    (p : ℝ × ℝ) : 0 ≤ Work.FTS.StrongEps.Jker ρ ε p := by
  simp only [Work.FTS.StrongEps.Jker]
  exact mul_nonneg (sq_nonneg _) (hρ.nonneg _)

/-- Every `q`-slice of the kernel is integrable: it is continuous with compact support. -/
theorem integrable_Jker_slice {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) (q : ℝ) :
    MeasureTheory.Integrable (fun p₁ : ℝ => Work.FTS.StrongEps.Jker ρ ε (p₁, q)) := by
  have hcont : Continuous fun p₁ : ℝ => Work.FTS.StrongEps.Jker ρ ε (p₁, q) :=
    (Work.FTS.StrongEps.Jker_continuous hρ ε).comp (by fun_prop)
  have hcs : HasCompactSupport fun p₁ : ℝ => Work.FTS.StrongEps.Jker ρ ε (p₁, q) := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ) ε) ?_
    intro p₁ hp₁
    have hmem : ((p₁, q) : ℝ × ℝ) ∈ Metric.closedBall 0 ε := by
      by_contra hc
      exact hp₁ (Work.FTS.StrongEps.Jker_eq_zero_of_not_mem hρ hε hc)
    have h' : max |p₁| |q| ≤ ε := by
      simpa only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs] using hmem
    have h1 : |p₁| ≤ ε := le_trans (le_max_left _ _) h'
    simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using h1
  exact hcont.integrable_of_hasCompactSupport hcs

/-! ### the swap -/

theorem FubiniSwap {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {W : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen W)
    {G : ℝ → ℝ} {a b : ℝ}
    (hdom : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |W z θ| ≤ G θ)
    (hint : MeasureTheory.Integrable (fun x : ℝ × ℝ => Work.Elliptic.sinCos2 x.1 * G (Work.FTS.StrongEps.thShift x.1 x.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod (MeasureTheory.volume.restrict (Set.Icc (-ε) ε))))
    (s : ℝ) (hs : ∀ p₁ : ℝ, p₁ ∈ Set.Icc (-ε) ε → Real.exp (s - p₁) ∈ Set.Icc a b) :
    Work.Elliptic.Fstar (Work.FTS.StrongEps.Jeps ρ ε W) (Real.exp s)
      = ∫ x : ℝ × ℝ, Work.Elliptic.sinCos2 x.1 *
          (∫ p₁ : ℝ, Work.FTS.StrongEps.Jker ρ ε (p₁, x.2) * W (Real.exp (s - p₁)) (Work.FTS.StrongEps.thShift x.1 x.2))
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod (MeasureTheory.volume.restrict (Set.Icc (-ε) ε))) := by
  classical
  set μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict Work.Spaces.Iθ with hμ
  set ν : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Icc (-ε) ε) with hν
  set Fun : ℝ × ℝ → ℝ := fun x => Work.Elliptic.sinCos2 x.1 *
      (∫ p₁ : ℝ, Work.FTS.StrongEps.Jker ρ ε (p₁, x.2) * W (Real.exp (s - p₁)) (Work.FTS.StrongEps.thShift x.1 x.2)) with hFun
  -- a.e. `θ ∈ (0, π/2)`
  have haeθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    rw [MeasureTheory.ae_restrict_iff (p := fun θ => θ ∈ Set.Ioo 0 (Real.pi / 2)) measurableSet_Ioo]
    filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2)] with θ hθ hmem
    exact hθ.mpr hmem
  -- integrability of the integrand over the product measure
  have hInt : MeasureTheory.Integrable Fun (μ.prod ν) := by
    have hGnn : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ G θ := by
      intro θ hθ
      have hmem : (-ε) ∈ Set.Icc (-ε) ε := ⟨le_rfl, by linarith⟩
      have hz : Real.exp (s - (-ε)) ∈ Set.Icc a b := hs (-ε) hmem
      exact le_trans (abs_nonneg _) (hdom _ hz θ hθ)
    obtain ⟨B, hB0, hB⟩ := exists_bound_integral_Jker_slice hρ hε
    have hae1 : ∀ᵐ x ∂(μ.prod ν), x.1 ∈ Set.Ioo 0 (Real.pi / 2) := by
      refine (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
        (s := {x : ℝ × ℝ | x.1 ∈ Set.Ioo 0 (Real.pi / 2)}) ?_).mpr ?_
      · exact measurableSet_Ioo.preimage measurable_fst
      · exact haeθ.mono (fun θ hθ => Filter.Eventually.of_forall (fun _ => hθ))
    have hae2 : ∀ᵐ x ∂(μ.prod ν), x.2 ∈ Set.Icc (-ε) ε := by
      refine (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
        (s := {x : ℝ × ℝ | x.2 ∈ Set.Icc (-ε) ε}) ?_).mpr ?_
      · exact measurableSet_Icc.preimage measurable_snd
      · exact Filter.Eventually.of_forall (fun _ => MeasureTheory.ae_restrict_mem measurableSet_Icc)
    have hae : ∀ᵐ x ∂(μ.prod ν), x.1 ∈ Set.Ioo 0 (Real.pi / 2) ∧ x.2 ∈ Set.Icc (-ε) ε :=
      hae1.and hae2
    have hIntB : MeasureTheory.Integrable
        (fun x : ℝ × ℝ => B * (Work.Elliptic.sinCos2 x.1 * G (Work.FTS.StrongEps.thShift x.1 x.2)))
        (μ.prod ν) := hint.const_mul B
    refine hIntB.mono' ?_ ?_
    · -- a.e. strong measurability: extend `W` by `0` off the open quadrant
      set Wm : ℝ × ℝ → ℝ := Set.indicator Work.FTS.EllipticEst.Q0 (fun p : ℝ × ℝ => W p.1 p.2) with hWm
      have hWm_meas : Measurable Wm := by
        rw [hWm]
        exact measurable_indicator_of_continuousOn Work.FTS.EllipticEst.isOpen_Q0 hsm.continuousOn
      have htan : Measurable Real.tan := by
        rw [show Real.tan = fun x => Real.sin x / Real.cos x from funext Real.tan_eq_sin_div_cos]
        exact Real.measurable_sin.div Real.measurable_cos
      have hth : Measurable fun y : (ℝ × ℝ) × ℝ => Work.FTS.StrongEps.thShift y.1.1 y.1.2 := by
        simp only [Work.FTS.StrongEps.thShift]
        exact Real.measurable_arctan.comp
          ((htan.comp (measurable_fst.comp measurable_fst)).mul
            (Real.measurable_exp.comp (measurable_neg.comp (measurable_snd.comp measurable_fst))))
      have hkmeas : Measurable (Function.uncurry (fun (x : ℝ × ℝ) (p₁ : ℝ) =>
          Work.FTS.StrongEps.Jker ρ ε (p₁, x.2) * Wm (Real.exp (s - p₁), Work.FTS.StrongEps.thShift x.1 x.2))) := by
        have h1 : Measurable fun y : (ℝ × ℝ) × ℝ => Work.FTS.StrongEps.Jker ρ ε (y.2, y.1.2) :=
          (Work.FTS.StrongEps.Jker_continuous hρ ε).measurable.comp
            (Measurable.prodMk measurable_snd (measurable_snd.comp measurable_fst))
        have h2 : Measurable fun y : (ℝ × ℝ) × ℝ =>
            Wm (Real.exp (s - y.2), Work.FTS.StrongEps.thShift y.1.1 y.1.2) :=
          hWm_meas.comp (Measurable.prodMk (Real.measurable_exp.comp (measurable_const.sub measurable_snd)) hth)
        exact h1.mul h2
      have hint_meas : MeasureTheory.StronglyMeasurable (fun x : ℝ × ℝ => ∫ p₁ : ℝ,
          Work.FTS.StrongEps.Jker ρ ε (p₁, x.2) * Wm (Real.exp (s - p₁), Work.FTS.StrongEps.thShift x.1 x.2)) :=
        MeasureTheory.StronglyMeasurable.integral_prod_right
          (f := fun (x : ℝ × ℝ) (p₁ : ℝ) => Work.FTS.StrongEps.Jker ρ ε (p₁, x.2) *
            Wm (Real.exp (s - p₁), Work.FTS.StrongEps.thShift x.1 x.2))
          hkmeas.stronglyMeasurable
      have hsin : MeasureTheory.StronglyMeasurable (fun x : ℝ × ℝ => Work.Elliptic.sinCos2 x.1) := by
        apply Continuous.stronglyMeasurable
        simp only [Work.Elliptic.sinCos2]
        fun_prop
      refine ((hsin.mul hint_meas).aestronglyMeasurable).congr ?_
      filter_upwards [hae1] with x hx1
      simp only [hFun, Pi.mul_apply]
      congr 1
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p₁ => ?_)
      rw [hWm]
      simp only [Set.indicator_of_mem (show (Real.exp (s - p₁), Work.FTS.StrongEps.thShift x.1 x.2)
        ∈ Work.FTS.EllipticEst.Q0 from ⟨Real.exp_pos _, Work.FTS.StrongEps.thShift_mem hx1⟩)]
    · -- the a.e. domination by the integrable envelope
      filter_upwards [hae] with x hx
      obtain ⟨hx1, hx2⟩ := hx
      have hJnn : ∀ p₁ : ℝ, 0 ≤ Work.FTS.StrongEps.Jker ρ ε (p₁, x.2) :=
        fun p₁ => Jker_nonneg_local hρ ε _
      have hbnd : ∀ p₁ : ℝ, Work.FTS.StrongEps.Jker ρ ε (p₁, x.2) *
            |W (Real.exp (s - p₁)) (Work.FTS.StrongEps.thShift x.1 x.2)|
          ≤ Work.FTS.StrongEps.Jker ρ ε (p₁, x.2) * G (Work.FTS.StrongEps.thShift x.1 x.2) := by
        intro p₁
        by_cases hp : p₁ ∈ Set.Icc (-ε) ε
        · exact mul_le_mul_of_nonneg_left
            (hdom _ (hs p₁ hp) _ (Work.FTS.StrongEps.thShift_mem hx1)) (hJnn p₁)
        · -- off `[-ε,ε]` the kernel vanishes (`x.2 ∈ [-ε,ε]`)
          have hz : Work.FTS.StrongEps.Jker ρ ε (p₁, x.2) = 0 := by
            refine Work.FTS.StrongEps.Jker_eq_zero_of_not_mem hρ hε ?_
            intro hmem
            have h' : max |p₁| |x.2| ≤ ε := by
              simpa only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs] using hmem
            exact hp (abs_le.mp (le_trans (le_max_left _ _) h'))
          rw [hz, zero_mul, zero_mul]
      have hslice_int : MeasureTheory.Integrable (fun p₁ : ℝ =>
          Work.FTS.StrongEps.Jker ρ ε (p₁, x.2) * G (Work.FTS.StrongEps.thShift x.1 x.2)) :=
        (integrable_Jker_slice hρ hε x.2).mul_const _
      calc ‖Fun x‖
          = Work.Elliptic.sinCos2 x.1 * ‖∫ p₁ : ℝ, Work.FTS.StrongEps.Jker ρ ε (p₁, x.2) *
              W (Real.exp (s - p₁)) (Work.FTS.StrongEps.thShift x.1 x.2)‖ := by
              rw [hFun]
              simp only [Real.norm_eq_abs, abs_mul]
              rw [abs_of_nonneg (sinCos2_nonneg_local hx1)]
        _ ≤ Work.Elliptic.sinCos2 x.1 * ∫ p₁ : ℝ, ‖Work.FTS.StrongEps.Jker ρ ε (p₁, x.2) *
              W (Real.exp (s - p₁)) (Work.FTS.StrongEps.thShift x.1 x.2)‖ :=
              mul_le_mul_of_nonneg_left (MeasureTheory.norm_integral_le_integral_norm _)
                (sinCos2_nonneg_local hx1)
        _ = Work.Elliptic.sinCos2 x.1 * ∫ p₁ : ℝ, Work.FTS.StrongEps.Jker ρ ε (p₁, x.2) *
              |W (Real.exp (s - p₁)) (Work.FTS.StrongEps.thShift x.1 x.2)| := by
              congr 1
              refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p₁ => ?_)
              simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hJnn p₁)]
        _ ≤ Work.Elliptic.sinCos2 x.1 * ∫ p₁ : ℝ, Work.FTS.StrongEps.Jker ρ ε (p₁, x.2) *
              G (Work.FTS.StrongEps.thShift x.1 x.2) := by
              refine mul_le_mul_of_nonneg_left ?_ (sinCos2_nonneg_local hx1)
              refine MeasureTheory.integral_mono_of_nonneg
                (Filter.Eventually.of_forall fun p₁ => mul_nonneg (hJnn p₁) (abs_nonneg _))
                hslice_int (Filter.Eventually.of_forall hbnd)
        _ = Work.Elliptic.sinCos2 x.1 * ((∫ p₁ : ℝ, Work.FTS.StrongEps.Jker ρ ε (p₁, x.2)) *
              G (Work.FTS.StrongEps.thShift x.1 x.2)) := by
              rw [MeasureTheory.integral_mul_const]
        _ ≤ Work.Elliptic.sinCos2 x.1 * (B * G (Work.FTS.StrongEps.thShift x.1 x.2)) := by
              refine mul_le_mul_of_nonneg_left ?_ (sinCos2_nonneg_local hx1)
              exact mul_le_mul_of_nonneg_right (hB x.2) (hGnn _ (Work.FTS.StrongEps.thShift_mem hx1))
        _ = B * (Work.Elliptic.sinCos2 x.1 * G (Work.FTS.StrongEps.thShift x.1 x.2)) := by ring
  -- the right hand side is the iterated integral
  have hR : (∫ x : ℝ × ℝ, Fun x ∂(μ.prod ν)) = ∫ θ : ℝ, ∫ q : ℝ, Fun (θ, q) ∂ν ∂μ :=
    MeasureTheory.integral_prod Fun hInt
  -- the left hand side is the same iterated integral (slicewise Fubini at fixed `θ`)
  have hL : Work.Elliptic.Fstar (Work.FTS.StrongEps.Jeps ρ ε W) (Real.exp s)
      = ∫ θ : ℝ, ∫ q : ℝ, Fun (θ, q) ∂ν ∂μ := by
    have hpt : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        Work.FTS.StrongEps.Jeps ρ ε W (Real.exp s) θ * Work.Elliptic.sinCos2 θ
          = ∫ q in Set.Icc (-ε) ε, Fun (θ, q) := by
      intro θ hθ
      rw [Jeps_eq_iterated hρ hε hsm hθ]
      simp only [hFun]
      rw [MeasureTheory.integral_const_mul]
      ring
    have h1 : Work.Elliptic.Fstar (Work.FTS.StrongEps.Jeps ρ ε W) (Real.exp s)
        = ∫ θ in Work.Spaces.Iθ, ∫ q in Set.Icc (-ε) ε, Fun (θ, q) := by
      rw [Work.Elliptic.Fstar]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [haeθ] with θ hθ
      exact hpt θ hθ
    rw [h1]
  change Work.Elliptic.Fstar (Work.FTS.StrongEps.Jeps ρ ε W) (Real.exp s) = ∫ x : ℝ × ℝ, Fun x ∂(μ.prod ν)
  rw [hL]
  exact hR.symm

end Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.GainDens.Jker_comp_zShift_exp_lt_top =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set

namespace Work.FTS.StrongEps.EpsE4Thr.GainDens

set_option maxHeartbeats 800000


/-- **The one-dimensional substitution `u = z * exp (-x)` on `[-ε, ε]`.**  For any
`G : ℝ → ℝ≥0∞` (no measurability needed) and `ε, z > 0`,

  `∫⁻ x in Icc (-ε) ε, G (z * exp (-x)) ≤ (exp ε / z) * ∫⁻ u in Ioi 0, G u`.

The constant is the inverse of the pointwise lower bound `z * exp (-ε)` of the stretching factor
`|d/dx (z exp (-x))| = z exp (-x)`. -/
private lemma lintegral_Icc_expNeg_le {G : ℝ → ENNReal} {ε z : ℝ} (_hε : 0 < ε) (hz : 0 < z) :
    (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x)))
      ≤ ENNReal.ofReal (Real.exp ε / z) * ∫⁻ u in Set.Ioi 0, G u := by
  have hzε : 0 < z * Real.exp (-ε) := mul_pos hz (Real.exp_pos _)
  -- the derivative of the substitution
  have hderiv : ∀ x ∈ Set.Icc (-ε) ε,
      HasDerivWithinAt (fun x : ℝ => z * Real.exp (-x)) (-(z * Real.exp (-x)))
        (Set.Icc (-ε) ε) x := by
    intro x _
    have h' : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-x)) x := by
      have h1 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-x) * (-1)) x :=
        (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
      simpa using h1
    have h2 : HasDerivAt (fun x : ℝ => z * Real.exp (-x)) (-(z * Real.exp (-x))) x := by
      have h3 := h'.const_mul z
      simpa using h3
    exact h2.hasDerivWithinAt
  -- the substitution is injective
  have hinj : Set.InjOn (fun x : ℝ => z * Real.exp (-x)) (Set.Icc (-ε) ε) := by
    intro x _ y _ hxy
    have hexp : Real.exp (-x) = Real.exp (-y) := mul_left_cancel₀ hz.ne' hxy
    have h2 : -x = -y := Real.exp_injective hexp
    linarith
  have hkey := MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul
    (s := Set.Icc (-ε) ε) (f := fun x : ℝ => z * Real.exp (-x))
    (f' := fun x : ℝ => -(z * Real.exp (-x))) measurableSet_Icc hderiv hinj G
  have himage_sub : (fun x : ℝ => z * Real.exp (-x)) '' Set.Icc (-ε) ε ⊆ Set.Ioi 0 := by
    rintro u ⟨x, _, rfl⟩
    exact mul_pos hz (Real.exp_pos _)
  have hpt : ∀ x : ℝ, ENNReal.ofReal |(-(z * Real.exp (-x)))| * G (z * Real.exp (-x))
      = ENNReal.ofReal (z * Real.exp (-x)) * G (z * Real.exp (-x)) := by
    intro x
    rw [abs_neg, abs_of_pos (mul_pos hz (Real.exp_pos _))]
  have h1 : ENNReal.ofReal (z * Real.exp (-ε))
        * (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x)))
      ≤ ∫⁻ x in Set.Icc (-ε) ε,
          ENNReal.ofReal |(-(z * Real.exp (-x)))| * G (z * Real.exp (-x)) := by
    rw [← lintegral_const_mul' (ENNReal.ofReal (z * Real.exp (-ε)))
      (fun x => G (z * Real.exp (-x))) ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Icc ?_
    intro x hx
    rw [hpt x]
    refine mul_le_mul_of_nonneg_right ?_ zero_le
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hx.2])) hz.le)
  have h2 : (∫⁻ x in Set.Icc (-ε) ε,
        ENNReal.ofReal |(-(z * Real.exp (-x)))| * G (z * Real.exp (-x)))
      ≤ ∫⁻ u in Set.Ioi 0, G u := by
    rw [← hkey]
    exact lintegral_mono_set himage_sub
  have hfin' : ENNReal.ofReal (z * Real.exp (-ε))
        * (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x)))
      ≤ ∫⁻ u in Set.Ioi 0, G u := le_trans h1 h2
  have hne0 : ENNReal.ofReal (z * Real.exp (-ε)) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]; exact hzε
  have hneTop : ENNReal.ofReal (z * Real.exp (-ε)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hstep : (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x)))
      ≤ (ENNReal.ofReal (z * Real.exp (-ε)))⁻¹ * ∫⁻ u in Set.Ioi 0, G u := by
    calc (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x)))
        = 1 * (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x))) := (one_mul _).symm
      _ = (ENNReal.ofReal (z * Real.exp (-ε)))⁻¹ * ENNReal.ofReal (z * Real.exp (-ε))
            * (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x))) := by
          rw [ENNReal.inv_mul_cancel hne0 hneTop]
      _ = (ENNReal.ofReal (z * Real.exp (-ε)))⁻¹ *
            (ENNReal.ofReal (z * Real.exp (-ε))
              * (∫⁻ x in Set.Icc (-ε) ε, G (z * Real.exp (-x)))) := by
          rw [mul_assoc]
      _ ≤ (ENNReal.ofReal (z * Real.exp (-ε)))⁻¹ * ∫⁻ u in Set.Ioi 0, G u :=
          mul_le_mul_of_nonneg_left hfin' zero_le
  have hreal : (z * Real.exp (-ε))⁻¹ = Real.exp ε / z := by
    rw [Real.exp_neg, mul_inv, inv_inv, div_eq_mul_inv, mul_comm]
  have hconst_eq : (ENNReal.ofReal (z * Real.exp (-ε)))⁻¹ = ENNReal.ofReal (Real.exp ε / z) := by
    rw [← ENNReal.ofReal_inv_of_pos hzε, hreal]
  rwa [hconst_eq] at hstep

/-- A point of `ℝ²` whose coordinate squares sum to at most `R²` (with `R ≥ 0`) lies in the closed
ball of radius `R`. -/
private lemma mem_closedBall_zero_of_sq_sum_le {x : ℝ × ℝ} {R : ℝ} (hR : 0 ≤ R)
    (h : x.1 ^ 2 + x.2 ^ 2 ≤ R ^ 2) : x ∈ Metric.closedBall (0 : ℝ × ℝ) R := by
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
  have h1 : |x.1| ≤ R := by
    nlinarith [sq_abs x.1, sq_nonneg x.2, abs_nonneg x.1, sq_nonneg (|x.1| - R)]
  have h2 : |x.2| ≤ R := by
    nlinarith [sq_abs x.2, sq_nonneg x.1, abs_nonneg x.2, sq_nonneg (|x.2| - R)]
  simpa only [Real.norm_eq_abs] using max_le h1 h2

/-- **The shifted integral over the ball of radius `ε`.**  For any `G : ℝ → ℝ≥0∞` and
`ε, z > 0`,

  `∫⁻ p in ball 0 ε, G (z * exp (-(p.1))) ≤ (2ε exp ε / z) * ∫⁻ u in Ioi 0, G u`.

The ball is contained in the square `Icc (-ε) ε ×ˢ Icc (-ε) ε`; Tonelli's inequality turns the
`p₂`-integration into the length `2ε` of that interval, and the remaining one-dimensional integral
is controlled by `lintegral_Icc_expNeg_le`. -/
private lemma lintegral_closedBall_zShift_le {G : ℝ → ENNReal} {ε z : ℝ} (hε : 0 < ε)
    (hz : 0 < z) :
    (∫⁻ p in Metric.closedBall (0 : ℝ × ℝ) ε, G (z * Real.exp (-(p.1))))
      ≤ ENNReal.ofReal (2 * ε * (Real.exp ε / z)) * ∫⁻ u in Set.Ioi 0, G u := by
  set s : Set ℝ := Set.Icc (-ε) ε with hs
  set Φ : ℝ × ℝ → ENNReal := fun p => G (z * Real.exp (-(p.1))) with hΦ
  have hΦa : ∀ p : ℝ × ℝ, Φ p = G (z * Real.exp (-(p.1))) := fun p => rfl
  have hball_sub : Metric.closedBall (0 : ℝ × ℝ) ε ⊆ s ×ˢ s := by
    intro p hp
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] at hp
    have hp' : max |p.1| |p.2| ≤ ε := by simpa only [Real.norm_eq_abs] using hp
    have h1 : |p.1| ≤ ε := le_trans (le_max_left _ _) hp'
    have h2 : |p.2| ≤ ε := le_trans (le_max_right _ _) hp'
    rw [hs]
    exact ⟨abs_le.mp h1, abs_le.mp h2⟩
  have hstep2 : (∫⁻ p in Metric.closedBall (0 : ℝ × ℝ) ε, Φ p) ≤ ∫⁻ p in s ×ˢ s, Φ p :=
    lintegral_mono_set hball_sub
  have hstep3 : (∫⁻ p in s ×ˢ s, Φ p)
      = ∫⁻ p, Φ p ∂((volume.restrict s).prod (volume.restrict s)) := by
    rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_restrict]
  have hstep4 : (∫⁻ p, Φ p ∂((volume.restrict s).prod (volume.restrict s)))
      ≤ ∫⁻ x in s, ∫⁻ y in s, Φ (x, y) := lintegral_prod_le Φ
  have hinner : ∀ x : ℝ, (∫⁻ y in s, Φ (x, y))
      = ENNReal.ofReal (2 * ε) * G (z * Real.exp (-x)) := by
    intro x
    have hpt : ∀ y : ℝ, Φ (x, y) = G (z * Real.exp (-x)) := by intro y; rw [hΦa]
    rw [show (∫⁻ y in s, Φ (x, y)) = ∫⁻ y in s, G (z * Real.exp (-x)) from
      lintegral_congr (fun y => hpt y)]
    rw [setLIntegral_const, hs, Real.volume_Icc]
    have : (ε : ℝ) - -ε = 2 * ε := by ring
    rw [this]
    exact mul_comm _ _
  have hstep5 : (∫⁻ x in s, ∫⁻ y in s, Φ (x, y))
      = ENNReal.ofReal (2 * ε) * ∫⁻ x in s, G (z * Real.exp (-x)) := by
    rw [show (∫⁻ x in s, ∫⁻ y in s, Φ (x, y))
        = ∫⁻ x in s, ENNReal.ofReal (2 * ε) * G (z * Real.exp (-x)) from
      lintegral_congr (fun x => hinner x)]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hstep6 : (∫⁻ x in s, G (z * Real.exp (-x)))
      ≤ ENNReal.ofReal (Real.exp ε / z) * ∫⁻ u in Set.Ioi 0, G u := by
    simpa only [hs] using lintegral_Icc_expNeg_le (G := G) hε hz
  calc (∫⁻ p in Metric.closedBall (0 : ℝ × ℝ) ε, G (z * Real.exp (-(p.1))))
      = (∫⁻ p in Metric.closedBall (0 : ℝ × ℝ) ε, Φ p) :=
        lintegral_congr (fun p => hΦa p)
    _ ≤ ∫⁻ p in s ×ˢ s, Φ p := hstep2
    _ = ∫⁻ p, Φ p ∂((volume.restrict s).prod (volume.restrict s)) := hstep3
    _ ≤ ∫⁻ x in s, ∫⁻ y in s, Φ (x, y) := hstep4
    _ = ENNReal.ofReal (2 * ε) * ∫⁻ x in s, G (z * Real.exp (-x)) := hstep5
    _ ≤ ENNReal.ofReal (2 * ε) * (ENNReal.ofReal (Real.exp ε / z) * ∫⁻ u in Set.Ioi 0, G u) :=
        mul_le_mul_right hstep6 _
    _ = ENNReal.ofReal (2 * ε * (Real.exp ε / z)) * ∫⁻ u in Set.Ioi 0, G u := by
        rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * ε by linarith), mul_assoc]

/-- namespace `Work.FTS.StrongEps.EpsE4Thr`, declaration name `Jker_comp_zShift_exp_lt_top`.
This is `JepsHkMem.Jker_comp_zShift_lt_top` with the kernel hypothesis weakened from `IsMollKernel`
to (nonneg, continuous, supported in the closed unit ball) and the extra bounded factor
`ENNReal.ofReal (Real.exp (δ(|p₁|+|p₂|)))`; the latter is `≤ Real.exp (2δε)` whenever
`Jker σ ε p ≠ 0` (support in the ball of radius `ε`), so it can be pulled out as a constant.
Template: `JepsHkMem/Jker_comp_zShift_lt_top.lean` (its private
`lintegral_Icc_expNeg_le` is the key one-dimensional substitution; note that the support
`σ q ≠ 0 → q.1^2 + q.2^2 ≤ 1` transfers to `Jker σ ε p ≠ 0 → p.1^2 + p.2^2 ≤ ε^2`). -/
theorem Jker_comp_zShift_exp_lt_top {σ : ℝ × ℝ → ℝ} (hσ0 : ∀ q : ℝ × ℝ, 0 ≤ σ q)
    (hσc : Continuous σ) (hσs : ∀ q : ℝ × ℝ, σ q ≠ 0 → q.1 ^ 2 + q.2 ^ 2 ≤ 1)
    {ε δ z : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) (hz : 0 < z) {G : ℝ → ENNReal}
    (hmeas : AEMeasurable (fun p₁ : ℝ => G (z * Real.exp (-p₁))) MeasureTheory.volume)
    (hfin : (∫⁻ z' in Set.Ioi (0 : ℝ), G z') < ⊤) :
    (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.Jker σ ε p)
      * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
      * G (z * Real.exp (-(p.1)))) < ⊤ := by
  -- (1) the density is bounded by `M` on the whole plane (it vanishes off the unit ball)
  obtain ⟨Cb, hCb⟩ := (isCompact_closedBall (0 : ℝ × ℝ) 1).exists_bound_of_continuousOn
    hσc.continuousOn
  set M : ℝ := max Cb 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hMub : ∀ q : ℝ × ℝ, σ q ≤ M := by
    intro q
    by_cases hq : q ∈ Metric.closedBall (0 : ℝ × ℝ) 1
    · have h := hCb q hq
      rw [Real.norm_eq_abs] at h
      exact le_trans (le_abs_self _) (le_trans h (le_max_left _ _))
    · have hzero : σ q = 0 := by
        by_contra hne
        exact hq (mem_closedBall_zero_of_sq_sum_le zero_le_one (by simpa using hσs q hne))
      rw [hzero]
      exact hM0
  -- (2) the pointwise bound for the rescaled kernel
  set C : ℝ := (ε⁻¹) ^ 2 * M with hCdef
  have hC0 : 0 ≤ C := mul_nonneg (sq_nonneg _) hM0
  have hJub : ∀ p : ℝ × ℝ, Work.FTS.StrongEps.Jker σ ε p ≤ C := by
    intro p
    rw [Work.FTS.StrongEps.Jker, hCdef]
    exact mul_le_mul_of_nonneg_left (hMub _) (sq_nonneg _)
  -- (3) where `σ (ε⁻¹ • p)` does not vanish, `p` lies in the ball of radius `ε`
  have hcomp : ∀ p : ℝ × ℝ, σ (ε⁻¹ • p) ≠ 0 → |p.1| ≤ ε ∧ |p.2| ≤ ε := by
    intro p hp
    have hq : (ε⁻¹ • p).1 ^ 2 + (ε⁻¹ • p).2 ^ 2 ≤ (1 : ℝ) ^ 2 := by
      simpa using hσs (ε⁻¹ • p) hp
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hq
    have hεinv : ε * ε⁻¹ = 1 := mul_inv_cancel₀ hε.ne'
    have key : ∀ a : ℝ, (ε⁻¹ * a) ^ 2 ≤ 1 → |a| ≤ ε := by
      intro a ha
      have h1 : |ε⁻¹ * a| ≤ 1 := by
        nlinarith [ha, abs_nonneg (ε⁻¹ * a), sq_abs (ε⁻¹ * a), sq_nonneg (|ε⁻¹ * a| - 1)]
      rw [abs_mul, abs_of_pos (inv_pos.mpr hε)] at h1
      calc |a| = ε * (ε⁻¹ * |a|) := by rw [← mul_assoc, hεinv, one_mul]
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left h1 hε.le
        _ = ε := mul_one ε
    exact ⟨key p.1 (by nlinarith [hq, sq_nonneg (ε⁻¹ * p.2)]),
      key p.2 (by nlinarith [hq, sq_nonneg (ε⁻¹ * p.1)])⟩
  have hball_of : ∀ p : ℝ × ℝ, σ (ε⁻¹ • p) ≠ 0 →
      p ∈ Metric.closedBall (0 : ℝ × ℝ) ε := by
    intro p hp
    obtain ⟨h1, h2⟩ := hcomp p hp
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
    simpa only [Real.norm_eq_abs] using max_le h1 h2
  -- (4) the gain is bounded on the support of the rescaled kernel
  have hexp_ball : ∀ p : ℝ × ℝ, σ (ε⁻¹ • p) ≠ 0 →
      Real.exp (δ * (|p.1| + |p.2|)) ≤ Real.exp (δ * (2 * ε)) := by
    intro p hp
    obtain ⟨h1, h2⟩ := hcomp p hp
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hδ, h1, h2, abs_nonneg p.1, abs_nonneg p.2]
  have hJker_nonneg : ∀ p : ℝ × ℝ, 0 ≤ Work.FTS.StrongEps.Jker σ ε p := by
    intro p
    rw [Work.FTS.StrongEps.Jker]
    exact mul_nonneg (sq_nonneg _) (hσ0 _)
  -- (5) the pointwise bound on the full density
  have hkey : ∀ p : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.Jker σ ε p)
        * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
      ≤ ENNReal.ofReal (C * Real.exp (δ * (2 * ε))) := by
    intro p
    rw [← ENNReal.ofReal_mul (hJker_nonneg p)]
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases hp : σ (ε⁻¹ • p) = 0
    · have hz0 : Work.FTS.StrongEps.Jker σ ε p = 0 := by
        simp only [Work.FTS.StrongEps.Jker, hp, mul_zero]
      rw [hz0, zero_mul]
      exact mul_nonneg hC0 (Real.exp_pos _).le
    · exact mul_le_mul (hJub p) (hexp_ball p hp) (Real.exp_pos _).le hC0
  -- (6) reduce the `p`-integral to the ball
  have hpt : ∀ p : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.Jker σ ε p)
        * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
        * G (z * Real.exp (-(p.1)))
      ≤ ENNReal.ofReal (C * Real.exp (δ * (2 * ε)))
        * (Metric.closedBall (0 : ℝ × ℝ) ε).indicator
            (fun p : ℝ × ℝ => G (z * Real.exp (-(p.1)))) p := by
    intro p
    by_cases hp : p ∈ Metric.closedBall (0 : ℝ × ℝ) ε
    · rw [Set.indicator_of_mem hp]
      exact mul_le_mul_left (hkey p) _
    · rw [Set.indicator_of_notMem hp]
      have hz0 : σ (ε⁻¹ • p) = 0 := by
        by_contra hne
        exact hp (hball_of p hne)
      have hpz : Work.FTS.StrongEps.Jker σ ε p = 0 := by
        simp only [Work.FTS.StrongEps.Jker, hz0, mul_zero]
      rw [hpz, ENNReal.ofReal_zero, zero_mul, zero_mul]
      exact zero_le
  have hmain : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.Jker σ ε p)
        * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
        * G (z * Real.exp (-(p.1))))
      ≤ ENNReal.ofReal (C * Real.exp (δ * (2 * ε)))
        * ∫⁻ p in Metric.closedBall (0 : ℝ × ℝ) ε, G (z * Real.exp (-(p.1))) := by
    calc (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.Jker σ ε p)
          * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
          * G (z * Real.exp (-(p.1))))
        ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (C * Real.exp (δ * (2 * ε)))
            * (Metric.closedBall (0 : ℝ × ℝ) ε).indicator
                (fun p : ℝ × ℝ => G (z * Real.exp (-(p.1)))) p := lintegral_mono hpt
      _ = ENNReal.ofReal (C * Real.exp (δ * (2 * ε)))
            * ∫⁻ p : ℝ × ℝ, (Metric.closedBall (0 : ℝ × ℝ) ε).indicator
                (fun p : ℝ × ℝ => G (z * Real.exp (-(p.1)))) p :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (C * Real.exp (δ * (2 * ε)))
            * ∫⁻ p in Metric.closedBall (0 : ℝ × ℝ) ε, G (z * Real.exp (-(p.1))) := by
          rw [lintegral_indicator (Metric.isClosed_closedBall.measurableSet)]
  -- (7) finiteness
  have hfinK : ENNReal.ofReal (C * Real.exp (δ * (2 * ε)))
        * (ENNReal.ofReal (2 * ε * (Real.exp ε / z)) * ∫⁻ u in Set.Ioi 0, G u) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
  refine lt_of_le_of_lt ?_ hfinK
  exact le_trans hmain
    (mul_le_mul_right (lintegral_closedBall_zShift_le (G := G) hε hz) _)

end Work.FTS.StrongEps.EpsE4Thr.GainDens
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.GainDens.Jker_lintegral_mul_exp_lt_top =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.GainDens

/-- namespace `Work.FTS.StrongEps.EpsE4Thr`, declaration name `Jker_lintegral_mul_exp_lt_top`.
The `δ`-moment of the rescaled kernel is finite: immediate from `StepFacts.Jker_moment_le`
(integrability of `p ↦ Jker σ ε p * exp (δ|p|)`), turned into the `lintegral` of `ofReal` via
`MeasureTheory.ofReal_integral_eq_lintegral_ofReal` (the integrand is nonnegative because `hσ0`
makes `Jker σ ε ≥ 0`). -/
theorem Jker_lintegral_mul_exp_lt_top {σ : ℝ × ℝ → ℝ} (hσ0 : ∀ q : ℝ × ℝ, 0 ≤ σ q)
    (hσc : Continuous σ) (hσs : ∀ q : ℝ × ℝ, σ q ≠ 0 → q.1 ^ 2 + q.2 ^ 2 ≤ 1)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 ≤ δ) :
    (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.Jker σ ε p
        * Real.exp (δ * (|p.1| + |p.2|)))) < ⊤ := by
  -- `Jker σ ε` is nonnegative, hence so is the whole integrand
  have hker_nonneg : ∀ p : ℝ × ℝ, 0 ≤ Work.FTS.StrongEps.Jker σ ε p := by
    intro p
    have h := hσ0 (ε⁻¹ • p)
    rw [Work.FTS.StrongEps.Jker]
    nlinarith [sq_nonneg (ε⁻¹ : ℝ)]
  have hnonneg : ∀ p : ℝ × ℝ,
      0 ≤ Work.FTS.StrongEps.Jker σ ε p * Real.exp (δ * (|p.1| + |p.2|)) :=
    fun p => mul_nonneg (hker_nonneg p) (Real.exp_nonneg _)
  -- integrability of the `δ`-moment, from `Jker_moment_le` with `γ = δ`
  have hInt : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.FTS.StrongEps.Jker σ ε p * Real.exp (δ * (|p.1| + |p.2|))) :=
    (Work.FTS.StrongEps.StepFacts.Jker_moment_le σ hσ0 hσc hσs hε hε1 hδ).1
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
    (Filter.Eventually.of_forall hnonneg)]
  exact ENNReal.ofReal_lt_top

end Work.FTS.StrongEps.EpsE4Thr.GainDens
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.JepsJoint.integrable_jker_fam =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.JepsJoint

open Work.FTS.StrongEps
open Work.FTS.StrongEps.JepsHkMem (aestronglyMeasurable_of_eq_zero_off
  continuousOn_shift_right' shift_mem_Quad')

set_option autoImplicit false


end Work.FTS.StrongEps.EpsE4Thr.JepsJoint
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.Jeps_family_deriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

open MeasureTheory Set Filter
open scoped Topology

set_option autoImplicit false

/-!
# `Jeps_family_deriv` — differentiation of the mollifier along a differentiable family

`Jeps ρ ε f z θ = ∫ p, Jker ρ ε p · f (z e^{-p₁}) (arctan (tan θ e^{-p₂}))` is an integral over
`p ∈ ℝ²`, so the derivative in the family parameter `s` of `s ↦ Jeps ρ ε (W s) z θ` is obtained
from the parametric differentiation lemma
`MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le`.

The four hypotheses it consumes:

* the pointwise differentiability of the slices (`hW`, on the open interval `(0,T)`);
* integrability of the integrand at the base time (`hint`, at `τ ∈ (0,T)`);
* a uniform bound on `Wdot` at the shifted points (`hbd`) — this dominates the derivative
  integrand by `C · ‖Jker ρ ε p‖`, which is integrable because `Jker ρ ε` is;
* a.e. strong measurability of the *derivative* integrand.  This last one is **not** free: `Wdot τ`
  is an arbitrary function (only bounded through `hbd`), and `Jker ρ ε` carries the measurability of
  `ρ` only through its support/continuity, so we recover measurability of
  `Jker ρ ε p · Wdot τ (zShift z p₁) (thShift θ p₂)` as the a.e. limit of the difference quotients
  `(Jker ρ ε p · W (τ + hₙ) (…) − Jker ρ ε p · W τ (…)) / hₙ`, each of which is a.e. strongly
  measurable by `hint` (the lemma `aestronglyMeasurable_Jker_mul_Wdot` below).

This is the exact repair of the false sibling `hasDerivWithinAt_Jeps_slice` (see
`NOTES_hasDerivWithinAt_Jeps_slice_FALSE.md`): the missing integrability hypothesis is present here
under the name `hint`.
-/



end Work.FTS.StrongEps.EpsE4Thr
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.L12JepsAux.aesm_logPull_epsRHSP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.L12JepsAux


end Work.FTS.StrongEps.EpsE4Thr.L12JepsAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.AEShiftPreimage =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

/-- **Transport of an a.e. statement along the log-shift.**  If a property holds for a.e. `w > 0`,
then it holds for `P (z * exp (-p.1))` for a.e. `p : ℝ × ℝ`, for every `z > 0`.

Route: reduce to the one-dimensional statement that `{p₁ | z * exp (-p₁) ∈ N}` is null for a null
set `N ⊆ (0,∞)` — the map `p₁ ↦ z exp (-p₁)` is the inverse of the differentiable bijection
`w ↦ log z - log w` on `(0,∞)`, so the image of a null set is null by
`addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`; then bound the bad set in `ℝ²` by
`{p₁ | z exp (-p₁) ∈ N} ×ˢ Set.univ` and use `MeasureTheory.Measure.prod_apply` together with
`MeasureTheory.Measure.volume_eq_prod ℝ ℝ`.
Declare the result in the namespace `Work.FTS.StrongEps.EpsLocalPStar`. -/
theorem AEShiftPreimage {z : ℝ} (hz : 0 < z) {P : ℝ → Prop}
    (h : ∀ᵐ w ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))), P w) :
    ∀ᵐ p ∂(MeasureTheory.volume : Measure (ℝ × ℝ)), P (z * Real.exp (-p.1)) := by
  classical
  -- The bad set on `(0,∞)`, which is null.
  set N : Set ℝ := {w | ¬ P w} ∩ Set.Ioi 0 with hN
  have hNvol : volume N = 0 := by
    have h' := (MeasureTheory.ae_iff).mp h
    rwa [Measure.restrict_apply' measurableSet_Ioi] at h'
  -- Members of `N` are exactly the `z * exp (-p.1)` with `¬ P` at them.
  have hTN : ∀ p : ℝ × ℝ, (z * Real.exp (-p.1) ∈ N ↔ ¬ P (z * Real.exp (-p.1))) := by
    intro p
    rw [hN]
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioi]
    exact ⟨fun h => h.1, fun h => ⟨h, mul_pos hz (Real.exp_pos _)⟩⟩
  -- Its preimage `T` under the shift.
  set T : Set ℝ := {p₁ | z * Real.exp (-p₁) ∈ N} with hT
  have hTvol : volume T = 0 := by
    -- `T` is the image of the null set `N` under the differentiable map `log z - log ·`.
    have himg : T = (fun w => Real.log z - Real.log w) '' N := by
      ext p
      rw [hT]
      constructor
      · intro hp
        have hlog : Real.log (z * Real.exp (-p)) = Real.log z - p := by
          rw [Real.log_mul hz.ne' (Real.exp_ne_zero _), Real.log_exp]
          ring
        refine ⟨z * Real.exp (-p), hp, ?_⟩
        show Real.log z - Real.log (z * Real.exp (-p)) = p
        rw [hlog]; ring
      · rintro ⟨w, hw, rfl⟩
        change z * Real.exp (-(Real.log z - Real.log w)) ∈ N
        have hwpos : 0 < w := by rw [hN] at hw; exact hw.2
        have harg : -(Real.log z - Real.log w) = Real.log w - Real.log z := by ring
        have hexp : Real.exp (Real.log w - Real.log z) = w / z := by
          rw [Real.exp_sub, Real.exp_log hwpos, Real.exp_log hz]
        rw [harg, hexp, mul_div_cancel₀ w hz.ne']
        exact hw
    rw [himg]
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ hNvol
    intro w hw
    rw [hN] at hw
    exact ((Real.differentiableAt_log (hw.2 : 0 < w).ne').const_sub
      (Real.log z)).differentiableWithinAt
  -- Conclude from `volume T = 0` by Fubini.
  rw [MeasureTheory.ae_iff]
  have hset : {p : ℝ × ℝ | ¬ P (z * Real.exp (-p.1))} = T ×ˢ Set.univ := by
    ext p
    simp only [Set.mem_prod, Set.mem_univ, and_true, hT, Set.mem_ofPred_eq]
    exact (hTN p).symm
  rw [hset, Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, hTvol]
  simp

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.JepsTraceTransfer =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Boundedness on compact `z`-intervals -/





/-! ## Measurability of the shifted profile -/


/-! ## The change of variables `p ↦ ε⁻¹ • p` and Fubini on the marginal -/


/-! ## The corrected statement -/





/-! ## The requested statement (kept as delegated; it is false as written, see the module
docstring: it is missing the measurability hypotheses of `JepsTraceTransfer_of_measurable`) -/


end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.JepsTraceTransferPi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Boundedness on compact `z`-intervals -/





/-! ## Measurability of the shifted profile -/


/-! ## The change of variables `p ↦ ε⁻¹ • p` and Fubini on the marginal -/


/-! ## The trace transfer at `θ = π/2⁻` -/


end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.JepsSubApply =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX

open Work.FTS.StrongEps

/-- `J_ε` is additive in its argument: the difference of two mollifications is the
mollification of the difference.  Both sides are the `p`-integral of `Jker ρ ε p` against the
corresponding shifted values (`Jeps_eq_integral`), so the identity is the linearity of the
Bochner integral on `ℝ²`; the two integrands are continuous with compact support (the kernel
vanishes off the ball of radius `ε`). -/
theorem JepsSubApply (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsMollKernel ρ) {ε : ℝ}
    (hε : 0 < ε) {g h : Work.FTS.Galerkin.Fn}
    (hg : ContinuousOn (Function.uncurry g) Work.FTS.StrongEps.Quad)
    (hh : ContinuousOn (Function.uncurry h) Work.FTS.StrongEps.Quad) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.FTS.StrongEps.Jeps ρ ε g z θ - Work.FTS.StrongEps.Jeps ρ ε h z θ
      = Work.FTS.StrongEps.Jeps ρ ε (fun z θ => g z θ - h z θ) z θ := by
  -- rewrite all three occurrences of `J_ε` as `p`-integrals
  rw [Jeps_eq_integral ρ ε g hz hθ, Jeps_eq_integral ρ ε h hz hθ,
      Jeps_eq_integral ρ ε (fun z θ => g z θ - h z θ) hz hθ]
  -- the shift of the quadrant point stays in the (open) quadrant
  have hmem : ∀ p : ℝ × ℝ, (zShift z p.1, thShift θ p.2) ∈ Quad :=
    fun _ => ⟨zShift_pos hz, thShift_mem hθ⟩
  have hcont_g : Continuous fun p : ℝ × ℝ => g (zShift z p.1) (thShift θ p.2) := by
    simpa only [Function.comp_def, Function.uncurry] using
      hg.comp_continuous (continuous_shift_pair z θ) hmem
  have hcont_h : Continuous fun p : ℝ × ℝ => h (zShift z p.1) (thShift θ p.2) := by
    simpa only [Function.comp_def, Function.uncurry] using
      hh.comp_continuous (continuous_shift_pair z θ) hmem
  -- both integrands are continuous with compact support, hence Bochner-integrable
  have hA : Integrable fun p : ℝ × ℝ => Jker ρ ε p * g (zShift z p.1) (thShift θ p.2) :=
    ((Jker_continuous hρ ε).mul hcont_g).integrable_of_hasCompactSupport
      (Jker_hasCompactSupport hρ hε).mul_right
  have hB : Integrable fun p : ℝ × ℝ => Jker ρ ε p * h (zShift z p.1) (thShift θ p.2) :=
    ((Jker_continuous hρ ε).mul hcont_h).integrable_of_hasCompactSupport
      (Jker_hasCompactSupport hρ hε).mul_right
  -- integrate the pointwise difference
  rw [← integral_sub hA hB]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  ring

end Work.FTS.StrongEps.EpsRLX
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsUniformMem_seq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false


end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.Atoms.QangDiff5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5.Atoms



end Work.FTS.StrongEps.H5.Atoms
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.Bricks5.L12Bundle5 =====
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
set_option linter.unusedVariables false


end Work.FTS.StrongEps.H5
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.HkSqAux.Wt_shift_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps.HkSqAux

/-! ## The shift bound for the weight `Wt`

The weight of the `ℋ^k`-spaces is `Wt α z θ = w z · sin(2θ)^{-γ/2}` with `w z = (1+z)²/z²` and
`γ = 1 + α/10` (see `Submission/Work/Spaces/Defs.lean` and
`Submission/Work/FTS/StrongEps/Weights.lean`, where `wtG α = (Wt α)²`).  The log-coordinate
shifts `zShift z p = z e^{-p}` and `thShift θ p = arctan (tan θ · e^{-p})` of the `ε`-scheme
change it by at most `e^{C(|p₁|+|p₂|)}`, *in either direction*: the two factors are shifted in
opposite directions (`w` increases as `z` decreases, `sin(2θ)^{-γ/2}` increases as `θ` moves
away from `π/4`), and the siblings `wtG_shift_le` / `wtZ_shift_le` / `wtE_shift_le` record the
other direction.

The two halves are elementary:

* **radial** — `w z ≤ e^{2|p₁|} w (zShift z p₁)`: this is `w_zShift_le` (`wtE_shift_le`) applied
  at the shifted point with the *opposite* shift, since the two shifts are inverse to each other
  (`zShift_add`, `zShift_neg_self`).
* **angular** — `sin(2θ)^{-γ/2} ≤ e^{2|p₂|} sin(2·thShift θ p₂)^{-γ/2}`: the lower bound
  `e^{-|p₂|} sin(2·thShift θ p₂) ≤ sin(2θ)` of `sinTwo_thShift_bounds` (again applied at the
  shifted point with the opposite shift) turns into an *upper* bound on the negative power
  `sin(2θ)^{-γ/2}`, because `x ↦ x^{-γ/2}` is antitone (`Real.rpow_le_rpow_of_nonpos`); the
  prefactor is `e^{(γ/2)|p₂|} ≤ e^{2|p₂|}` since `γ/2 ≤ 2`.

Multiplying the two and collecting the exponentials gives `C = 2`. -/

/-- The two `z`-shifts compose: `zShift (zShift z p) q = zShift z (p+q)`. -/
theorem zShift_add (z p q : ℝ) : zShift (zShift z p) q = zShift z (p + q) := by
  have h : -p + -q = -(p + q) := by ring
  simp only [zShift]
  rw [mul_assoc, ← Real.exp_add, h]

/-- The two `z`-shifts with opposite parameters are inverse to each other. -/
theorem zShift_neg_self (z p : ℝ) : zShift (zShift z p) (-p) = z := by
  rw [zShift_add]
  simp [zShift]

/-- The two `θ`-shifts compose: `thShift (thShift θ p) q = thShift θ (p+q)`.  (Valid for every
`θ : ℝ` — the identity `tan (arctan u) = u` that it uses carries no side condition.) -/
theorem thShift_add (θ p q : ℝ) : thShift (thShift θ p) q = thShift θ (p + q) := by
  have h : -p + -q = -(p + q) := by ring
  simp only [thShift]
  rw [Real.tan_arctan, mul_assoc, ← Real.exp_add, h]

/-- The two `θ`-shifts with opposite parameters are inverse to each other on the quadrant. -/
theorem thShift_neg_self {θ p : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    thShift (thShift θ p) (-p) = θ := by
  rw [thShift_add]
  have h0 : p + -p = 0 := by ring
  rw [h0]
  simp only [thShift, neg_zero, Real.exp_zero, mul_one]
  exact Real.arctan_tan (by linarith [hθ.1, Real.pi_pos]) hθ.2

/-- **The radial factor is shifted by at most `e^{2|p|}`** (in the "unshifted `≤` shifted"
direction needed here): `w z ≤ e^{2|p|} w (zShift z p)` for `z > 0`. -/
theorem w_shift_ge_le {z p : ℝ} (hz : 0 < z) :
    Work.Spaces.w z ≤ Real.exp (2 * |p|) * Work.Spaces.w (zShift z p) := by
  have h := w_zShift_le (zShift z p) (-p) (zShift_pos hz)
  rw [zShift_neg_self, abs_neg] at h
  exact h

/-- The angular factor `sin(2θ)^{-γ/2}` is nonnegative on the closed quadrant. -/
theorem wTheta_nonneg {α : ℝ} {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (π / 2)) :
    0 ≤ Work.Spaces.wTheta α θ := by
  rw [Work.Spaces.wTheta]
  exact Real.rpow_nonneg (sin_two_nonneg hθ) _

/-- **The angular factor is shifted by at most `e^{2|p₂|}`** (again in the "unshifted `≤`
shifted" direction): `sin(2θ)^{-γ/2} ≤ e^{2|p₂|} sin(2·thShift θ p₂)^{-γ/2}` for
`α ∈ (0,1]`, `θ ∈ (0,π/2)`. -/
theorem wTheta_shift_ge_le {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {θ p₂ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.wTheta α θ ≤ Real.exp (2 * |p₂|) * Work.Spaces.wTheta α (thShift θ p₂) := by
  have hθ' : thShift θ p₂ ∈ Set.Ioo 0 (Real.pi / 2) := thShift_mem hθ
  have hlo := (sinTwo_thShift_bounds (θ := thShift θ p₂) (p := -p₂) hθ').1
  rw [abs_neg, thShift_neg_self hθ] at hlo
  have hB : 0 < Real.sin (2 * thShift θ p₂) := sin_two_pos hθ'
  have hA : 0 < Real.exp (-|p₂|) * Real.sin (2 * thShift θ p₂) :=
    mul_pos (Real.exp_pos _) hB
  have hr : -(Work.Spaces.gam α / 2) ≤ 0 := by
    have : 0 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith [hα.1]
    linarith
  have h1 := Real.rpow_le_rpow_of_nonpos hA hlo hr
  have hexpneg : (Real.exp (-|p₂|)) ^ (-(Work.Spaces.gam α / 2))
      = Real.exp (|p₂| * (Work.Spaces.gam α / 2)) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  have hmul : (Real.exp (-|p₂|) * Real.sin (2 * thShift θ p₂)) ^ (-(Work.Spaces.gam α / 2))
      = Real.exp (|p₂| * (Work.Spaces.gam α / 2))
          * Real.sin (2 * thShift θ p₂) ^ (-(Work.Spaces.gam α / 2)) := by
    rw [Real.mul_rpow (Real.exp_pos _).le hB.le, hexpneg]
  rw [hmul] at h1
  have hgam : Work.Spaces.gam α / 2 ≤ 2 := by
    rw [Work.Spaces.gam]; linarith [hα.2]
  have hexp : Real.exp (|p₂| * (Work.Spaces.gam α / 2)) ≤ Real.exp (2 * |p₂|) := by
    rw [Real.exp_le_exp]
    nlinarith [abs_nonneg p₂, hgam]
  have hnn : 0 ≤ Real.sin (2 * thShift θ p₂) ^ (-(Work.Spaces.gam α / 2)) :=
    Real.rpow_nonneg hB.le _
  calc Work.Spaces.wTheta α θ
      = Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2)) := rfl
    _ ≤ Real.exp (|p₂| * (Work.Spaces.gam α / 2))
          * Real.sin (2 * thShift θ p₂) ^ (-(Work.Spaces.gam α / 2)) := h1
    _ ≤ Real.exp (2 * |p₂|) * Real.sin (2 * thShift θ p₂) ^ (-(Work.Spaces.gam α / 2)) :=
        mul_le_mul_of_nonneg_right hexp hnn
    _ = Real.exp (2 * |p₂|) * Work.Spaces.wTheta α (thShift θ p₂) := rfl

theorem Wt_shift_le :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ z θ p₁ p₂ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.Wt α z θ
        ≤ Real.exp (C * (|p₁| + |p₂|))
          * Work.Spaces.Wt α (Work.FTS.StrongEps.zShift z p₁) (Work.FTS.StrongEps.thShift θ p₂) := by
  refine ⟨2, by norm_num, ?_⟩
  intro α hα z θ p₁ p₂ hz hθ
  have h1 := w_shift_ge_le (z := z) (p := p₁) hz
  have h2 : Work.Spaces.wTheta α θ ≤ Real.exp (2 * |p₂|) * Work.Spaces.wTheta α (thShift θ p₂) :=
    wTheta_shift_ge_le (α := α) (p₂ := p₂) hα hθ
  have hθIcc : θ ∈ Set.Icc 0 (π / 2) := ⟨hθ.1.le, hθ.2.le⟩
  have hθ' : thShift θ p₂ ∈ Set.Ioo 0 (π / 2) := thShift_mem hθ
  have h2nn : 0 ≤ Work.Spaces.wTheta α θ := wTheta_nonneg hθIcc
  have h1rnn : 0 ≤ Real.exp (2 * |p₁|) * Work.Spaces.w (zShift z p₁) :=
    mul_nonneg (Real.exp_pos _).le (w_nonneg _)
  have hprod := mul_le_mul h1 h2 h2nn h1rnn
  rw [Work.Spaces.Wt, Work.Spaces.Wt]
  calc Work.Spaces.w z * Work.Spaces.wTheta α θ
      ≤ (Real.exp (2 * |p₁|) * Work.Spaces.w (zShift z p₁))
          * (Real.exp (2 * |p₂|) * Work.Spaces.wTheta α (thShift θ p₂)) := hprod
    _ = Real.exp (2 * (|p₁| + |p₂|))
          * (Work.Spaces.w (zShift z p₁) * Work.Spaces.wTheta α (thShift θ p₂)) := by
        have h2e : 2 * (|p₁| + |p₂|) = 2 * |p₁| + 2 * |p₂| := by ring
        rw [h2e, Real.exp_add]
        ring

end Work.FTS.StrongEps.HkSqAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.HkSqAux.aemeasurable_shift_slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.HkSqAux

open Work.FTS.StrongEps
open Work.Spaces

/-! ## The two null sets of the boundary -/

/-- `z = 0` is null for `volume.restrict Iz` with `Iz = [0, ∞)`. -/
private lemma measure_Iz_compl_Ioi_slice :
    (volume.restrict Iz) (Set.Ioi (0 : ℝ))ᶜ = 0 := by
  rw [Measure.restrict_apply measurableSet_Ioi.compl]
  refine measure_mono_null ?_ (measure_singleton (0 : ℝ))
  intro x hx
  simp only [Iz, Set.mem_inter_iff, Set.mem_Ici, Set.mem_compl_iff, Set.mem_Ioi,
    Set.mem_singleton_iff] at hx ⊢
  exact le_antisymm (not_lt.mp hx.1) hx.2

/-- `θ = 0` and `θ = π/2` are null for `volume.restrict Iθ` with `Iθ = [0, π/2]`. -/
private lemma measure_Iθ_compl_Ioo_slice :
    (volume.restrict Iθ) (Set.Ioo (0 : ℝ) (π / 2))ᶜ = 0 := by
  rw [Measure.restrict_apply measurableSet_Ioo.compl]
  have h0 : (volume : Measure ℝ) ({0} ∪ {π / 2}) = 0 :=
    measure_union_null (measure_singleton 0) (measure_singleton (π / 2))
  refine measure_mono_null ?_ h0
  intro x hx
  simp only [Iθ, Set.mem_inter_iff, Set.mem_Icc, Set.mem_compl_iff, Set.mem_Ioo,
    Set.mem_union, Set.mem_singleton_iff] at hx ⊢
  obtain ⟨hxn, hxI⟩ := hx
  rcases lt_or_ge (0 : ℝ) x with h | h
  · rcases lt_or_ge x (π / 2) with h2 | h2
    · exact absurd ⟨h, h2⟩ hxn
    · exact Or.inr (le_antisymm hxI.2 h2)
  · exact Or.inl (le_antisymm h hxI.1)

/-- The complement of the quadrant is null for `(volume.restrict Iz).prod (volume.restrict Iθ)`:
it is contained in the union of the two coordinate hyperplanes. -/
private lemma measure_quad_compl_slice :
    (volume.restrict Iz).prod (volume.restrict Iθ) Quadᶜ = 0 := by
  have hsub : Quadᶜ ⊆ (Set.Ioi (0 : ℝ))ᶜ ×ˢ (Set.univ : Set ℝ) ∪
      (Set.univ : Set ℝ) ×ˢ (Set.Ioo (0 : ℝ) (π / 2))ᶜ := by
    intro x hx
    simp only [Quad, Set.mem_compl_iff, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, not_and,
      Set.mem_union, Set.mem_univ, and_true, true_and] at hx ⊢
    tauto
  have h1 : (volume.restrict Iz).prod (volume.restrict Iθ)
      ((Set.Ioi (0 : ℝ))ᶜ ×ˢ (Set.univ : Set ℝ) ∪
        (Set.univ : Set ℝ) ×ˢ (Set.Ioo (0 : ℝ) (π / 2))ᶜ) = 0 := by
    rw [measure_union_null_iff]
    constructor
    · rw [Measure.prod_prod, measure_Iz_compl_Ioi_slice, zero_mul]
    · rw [Measure.prod_prod, measure_Iθ_compl_Ioo_slice, mul_zero]
  exact measure_mono_null hsub h1

/-! ## Continuity of the shift along a fixed parameter -/

/-- On the quadrant, `cos` does not vanish, so `tan` is continuous there. -/
private lemma cos_ne_zero_of_mem_quad_slice {q : ℝ × ℝ} (hq : q ∈ Quad) :
    Real.cos q.2 ≠ 0 := by
  have h2 : q.2 ∈ Set.Ioo 0 (π / 2) := hq.2
  exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, h2.1], h2.2⟩).ne'

/-- For a fixed `p₂`, the `θ`-shift `q ↦ thShift q.2 p₂` is continuous on the quadrant
(the monotone `tan` factor is harmless there because `cos ≠ 0`). -/
private lemma continuousOn_thShift_slice (p₂ : ℝ) :
    ContinuousOn (fun q : ℝ × ℝ => thShift q.2 p₂) Quad := by
  have h1 : ContinuousOn (fun q : ℝ × ℝ => Real.tan q.2 * Real.exp (-p₂)) Quad :=
    (Real.continuousOn_tan.comp continuousOn_snd
      (fun q hq => cos_ne_zero_of_mem_quad_slice hq)).mul continuousOn_const
  have h2 := Real.continuous_arctan.comp_continuousOn h1
  simpa only [thShift, Function.comp_def] using h2

/-- For a fixed parameter `p`, the shifted point `q ↦ (zShift q.1 p.1, thShift q.2 p.2)` is
continuous on the quadrant. -/
private lemma continuousOn_shift_slice_of_quad (p : ℝ × ℝ) :
    ContinuousOn (fun q : ℝ × ℝ => (zShift q.1 p.1, thShift q.2 p.2)) Quad := by
  refine ContinuousOn.prodMk ?_ (continuousOn_thShift_slice p.2)
  simp only [zShift]
  exact continuousOn_fst.mul continuousOn_const

/-- The shifted point of a base point of the quadrant lies again in the quadrant. -/
private lemma shift_mem_Quad_slice (p : ℝ × ℝ) {q : ℝ × ℝ} (hq : q ∈ Quad) :
    (zShift q.1 p.1, thShift q.2 p.2) ∈ Quad :=
  ⟨zShift_pos hq.1, thShift_mem hq.2⟩

/-! ## The target -/

theorem aemeasurable_shift_slice {G : ℝ → ℝ → ℝ}
    (hG : ContinuousOn (fun q : ℝ × ℝ => G q.1 q.2) Work.FTS.StrongEps.Quad) (p : ℝ × ℝ) :
    AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (G (Work.FTS.StrongEps.zShift q.1 p.1)
        (Work.FTS.StrongEps.thShift q.2 p.2)))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  classical
  have hSmeas : MeasurableSet Quad := (isOpen_Ioi.prod isOpen_Ioo).measurableSet
  have hnull : (volume.restrict Iz).prod (volume.restrict Iθ) Quadᶜ = 0 :=
    measure_quad_compl_slice
  -- On the quadrant the composite is continuous.
  have hcont : ContinuousOn (fun q : ℝ × ℝ => G (zShift q.1 p.1) (thShift q.2 p.2)) Quad :=
    hG.comp (continuousOn_shift_slice_of_quad p) (fun q hq => shift_mem_Quad_slice p hq)
  have hA : AEMeasurable (fun q : ℝ × ℝ => G (zShift q.1 p.1) (thShift q.2 p.2))
      (Measure.restrict ((volume.restrict Iz).prod (volume.restrict Iθ)) Quad) :=
    hcont.aemeasurable hSmeas
  -- Multiply by the indicator of the quadrant and remove it again using conullity.
  have hind : AEMeasurable (Quad.indicator
      (fun q : ℝ × ℝ => G (zShift q.1 p.1) (thShift q.2 p.2)))
      ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
    (aemeasurable_indicator_iff hSmeas).mpr hA
  have hcongr : (fun q : ℝ × ℝ => G (zShift q.1 p.1) (thShift q.2 p.2))
      =ᵐ[(volume.restrict Iz).prod (volume.restrict Iθ)]
      Quad.indicator (fun q : ℝ × ℝ => G (zShift q.1 p.1) (thShift q.2 p.2)) := by
    filter_upwards [compl_mem_ae_iff.mpr hnull] with q hq
    simp only [Set.mem_compl_iff, not_not] at hq
    exact (Set.indicator_of_mem hq
      (fun q : ℝ × ℝ => G (zShift q.1 p.1) (thShift q.2 p.2))).symm
  have hGae : AEMeasurable (fun q : ℝ × ℝ => G (zShift q.1 p.1) (thShift q.2 p.2))
      ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
    hind.congr hcongr.symm
  exact ENNReal.measurable_ofReal.comp_aemeasurable hGae

end Work.FTS.StrongEps.HkSqAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.HkSqAux.lintegral_arctan_exp_subst =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.HkSqAux

/-- `ζ ↦ arctan (e^ζ)` is strictly increasing. -/
theorem strictMono_arctan_exp : StrictMono fun ζ : ℝ => Real.arctan (Real.exp ζ) :=
  Real.arctan_strictMono.comp Real.exp_strictMono

/-- The derivative of `ζ ↦ arctan (e^ζ)` is `kappa`. -/
theorem hasDerivAt_arctan_exp (ζ : ℝ) :
    HasDerivAt (fun ζ' : ℝ => Real.arctan (Real.exp ζ')) (kappa ζ) ζ := by
  have h1 : HasDerivAt (fun ζ' : ℝ => Real.exp ζ') (Real.exp ζ) ζ := Real.hasDerivAt_exp ζ
  have h2 := (Real.hasDerivAt_arctan (Real.exp ζ)).comp ζ h1
  have hdv : (1 / (1 + (Real.exp ζ) ^ 2)) * Real.exp ζ = kappa ζ := by
    rw [kappa]
    have h4 : 1 + (Real.exp ζ) ^ 2 = 1 + Real.exp (2 * ζ) := by
      rw [sq, ← Real.exp_add]; ring_nf
    rw [h4, div_eq_mul_inv]
    ring_nf
  exact hdv ▸ h2


end Work.FTS.StrongEps.HkSqAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.HkSqAux.logJac_shift_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

open scoped Real

namespace Work.FTS.StrongEps.HkSqAux

/-- **The pure angular core of the shift bound.**  The ratio

  `kappa ζ / kappa (ζ - p) = e^p (1 + e^{2ζ-2p}) / (1 + e^{2ζ})`

is bounded by `e^{|p|} = max (e^p) (e^{-p})` (the function `t ↦ (1 + t e^{-2p})/(1+t)` is monotone
and interpolates between `1` and `e^{-2p}`), whence `kappa ζ ≤ e^{2|p|+p} kappa (ζ - p)`.

Concretely, with `D₁ = 1 + e^{2ζ}`, `D₂ = 1 + e^{2(ζ-p)}`, the claim is `1/D₁ ≤ e^{2|p|}/D₂`, i.e.
`D₂ ≤ e^{2|p|} D₁`, which follows from `e^{-2p} ≤ e^{2|p|}` and `1 ≤ e^{2|p|}`. -/
theorem kappa_shift_core (ζ p : ℝ) :
    kappa ζ ≤ Real.exp (2 * |p| + p) * kappa (ζ - p) := by
  have hD1 : 0 < 1 + Real.exp (2 * ζ) := by positivity
  have hD2 : 0 < 1 + Real.exp (2 * (ζ - p)) := by positivity
  have hE : Real.exp (-(2 * p)) ≤ Real.exp (2 * |p|) := by
    rw [Real.exp_le_exp]
    nlinarith [neg_le_abs p]
  have hkey : 1 + Real.exp (2 * (ζ - p)) ≤ Real.exp (2 * |p|) * (1 + Real.exp (2 * ζ)) := by
    have heq : Real.exp (2 * (ζ - p)) = Real.exp (2 * ζ) * Real.exp (-(2 * p)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    have h1 : Real.exp (2 * ζ) * Real.exp (-(2 * p)) ≤ Real.exp (2 * ζ) * Real.exp (2 * |p|) :=
      mul_le_mul_of_nonneg_left hE (Real.exp_pos (2 * ζ)).le
    have h2 : (1 : ℝ) ≤ Real.exp (2 * |p|) := Real.one_le_exp (by positivity)
    have h5 : Real.exp (2 * |p|) * Real.exp (2 * ζ) = Real.exp (2 * ζ) * Real.exp (2 * |p|) := by
      ring
    nlinarith [h1, h2, h5]
  have hfrac : (1 : ℝ) / (1 + Real.exp (2 * ζ))
      ≤ Real.exp (2 * |p|) / (1 + Real.exp (2 * (ζ - p))) := by
    rw [div_le_div_iff₀ hD1 hD2]
    linarith [hkey]
  have hmul := mul_le_mul_of_nonneg_left hfrac (Real.exp_pos ζ).le
  have hnum : Real.exp ζ * Real.exp (2 * |p|) = Real.exp (2 * |p| + p) * Real.exp (ζ - p) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [kappa, kappa]
  calc Real.exp ζ / (1 + Real.exp (2 * ζ))
      = Real.exp ζ * (1 / (1 + Real.exp (2 * ζ))) := by rw [div_eq_mul_one_div]
    _ ≤ Real.exp ζ * (Real.exp (2 * |p|) / (1 + Real.exp (2 * (ζ - p)))) := hmul
    _ = Real.exp ζ * Real.exp (2 * |p|) / (1 + Real.exp (2 * (ζ - p))) := by
        rw [mul_div_assoc]
    _ = Real.exp (2 * |p| + p) * Real.exp (ζ - p) / (1 + Real.exp (2 * (ζ - p))) := by
        rw [hnum]
    _ = Real.exp (2 * |p| + p) * (Real.exp (ζ - p) / (1 + Real.exp (2 * (ζ - p)))) := by
        rw [mul_div_assoc]

theorem logJac_shift_le :
    ∃ C : ℝ, 0 < C ∧ ∀ s ζ p₁ p₂ : ℝ,
      Work.FTS.StrongEps.HkSqAux.logJac s ζ
        ≤ Real.exp (C * (|p₁| + |p₂|)) * Work.FTS.StrongEps.HkSqAux.logJac (s - p₁) (ζ - p₂) := by
  refine ⟨4, by norm_num, fun s ζ p₁ p₂ => ?_⟩
  have hκ := kappa_shift_core ζ p₂
  -- the exponent gap left over from the two shifts is absorbed by `C = 4`
  have hexpmono : Real.exp (2 * |p₂| + p₂) ≤ Real.exp (4 * (|p₁| + |p₂|) - p₁) := by
    rw [Real.exp_le_exp]
    nlinarith [le_abs_self p₁, le_abs_self p₂, abs_nonneg p₁, abs_nonneg p₂]
  have hstep : kappa ζ ≤ Real.exp (4 * (|p₁| + |p₂|) - p₁) * kappa (ζ - p₂) :=
    le_trans hκ (mul_le_mul_of_nonneg_right hexpmono (kappa_nonneg _))
  have hE4 : Real.exp s * Real.exp (4 * (|p₁| + |p₂|) - p₁)
      = Real.exp (4 * (|p₁| + |p₂|)) * Real.exp (s - p₁) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [logJac, logJac]
  calc Real.exp s * kappa ζ
      ≤ Real.exp s * (Real.exp (4 * (|p₁| + |p₂|) - p₁) * kappa (ζ - p₂)) :=
        mul_le_mul_of_nonneg_left hstep (Real.exp_pos s).le
    _ = (Real.exp s * Real.exp (4 * (|p₁| + |p₂|) - p₁)) * kappa (ζ - p₂) := by ring
    _ = (Real.exp (4 * (|p₁| + |p₂|)) * Real.exp (s - p₁)) * kappa (ζ - p₂) := by rw [hE4]
    _ = Real.exp (4 * (|p₁| + |p₂|)) * (Real.exp (s - p₁) * kappa (ζ - p₂)) := by ring

end Work.FTS.StrongEps.HkSqAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.HkSqAux.wdiv_shift_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.HkSqAux

/-!
# `Submission/Work/FTS/StrongEps/HkSqAux/wdiv_shift_le.lean` — the shift bound for
`w / sin(2θ)^{η/2}`

The single-slot weight `w z / sin(2θ)^{η/2}` (`w z = (1+z)²/z²`, `η = 99/100`) is the square root
of the pure `D_z`-weight `wtE z θ = w z² sin(2θ)^{-η}` of
`Submission/Work/FTS/StrongEps/Weights.lean`.  Here we record the *reverse* direction of
`Work.FTS.StrongEps.wtE_shift_le`: the shifted weight dominates the unshifted one up to
`e^{C(|p₁|+|p₂|)}`,

  `w z / sin(2θ)^{η/2} ≤ e^{C(|p₁|+|p₂|)} · w (zShift z p₁) / sin(2·thShift θ p₂)^{η/2}`,

which is the "lower bound" form needed when the shift is used to *replace* the point `(z,θ)` by a
shifted one (the two directions are compatible because `p ↦ -p` inverts the shift).

Both halves are elementary.

* **the `z`-half.**  `w z = ((1+z)/z)²` while `w (z e^{-p}) = ((e^{p}+z)/z)²`, and
  `1 + z ≤ e^{|p|} (e^{p} + z)` because `1 ≤ e^{|p|}e^{p}` and `z ≤ e^{|p|}z`; whence
  `w z ≤ e^{2|p|} w (zShift z p)`.
  (The companion direction `w (zShift z p) ≤ e^{2|p|} w z` is `w_zShift_le`.)
* **the `θ`-half.**  `sinTwo_thShift_bounds` gives `sin(2·thShift θ p) ≤ e^{|p|} sin(2θ)`, hence,
  raising to the *nonnegative* power `η/2` and using `(e^{|p|})^{η/2} ≤ e^{|p|}`,
  `sin(2·thShift θ p)^{η/2} ≤ e^{|p|} sin(2θ)^{η/2}`, which after inverting is exactly
  `sin(2θ)^{-η/2} ≤ e^{|p|} sin(2·thShift θ p)^{-η/2}`.

`C = 3` suffices for the product (`2|p₁| + |p₂| ≤ 3(|p₁|+|p₂|)`).
-/

/-! ## The reverse radial bound -/

/-- **`w z ≤ e^{2|p|} w (zShift z p)`** — the reverse of `w_zShift_le`, which gives the same
inequality with the two sides exchanged (both are true, since `p ↦ -p` inverts the shift).  The
proof uses the forms `w z = ((1+z)/z)²`, `w (z e^{-p}) = ((e^{p}+z)/z)²` and the elementary bound
`1 + z ≤ e^{|p|} (e^{p} + z)`. -/
theorem w_le_w_zShift (z p : ℝ) (hz : 0 < z) :
    Work.Spaces.w z ≤ Real.exp (2 * |p|) * Work.Spaces.w (Work.FTS.StrongEps.zShift z p) := by
  -- the elementary inequality `1 + z ≤ e^{|p|} (e^{p} + z)`
  have hsum : 1 + z ≤ Real.exp |p| * (Real.exp p + z) := by
    have h1 : (1 : ℝ) ≤ Real.exp |p| * Real.exp p := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith [neg_le_abs p])
    have h2 : z ≤ Real.exp |p| * z := by
      rw [mul_comm]
      exact le_mul_of_one_le_right hz.le (Real.one_le_exp (abs_nonneg p))
    have h3 : 1 + z ≤ Real.exp |p| * Real.exp p + Real.exp |p| * z := add_le_add h1 h2
    rwa [← mul_add] at h3
  have hdiv : (1 + z) / z ≤ Real.exp |p| * ((Real.exp p + z) / z) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hsum hz.le
  have hsq : ((1 + z) / z) ^ 2
      ≤ (Real.exp |p| * ((Real.exp p + z) / z)) ^ 2 :=
    pow_le_pow_left₀ (div_nonneg (by linarith) hz.le) hdiv 2
  -- identify the two weights with the squares of the quotients
  have hexp2 : (Real.exp |p|) ^ 2 = Real.exp (2 * |p|) := by
    rw [sq, ← Real.exp_add, two_mul]
  have hA : Work.Spaces.w z = ((1 + z) / z) ^ 2 := by
    rw [Work.Spaces.w, div_pow]
  have hB : Work.Spaces.w (Work.FTS.StrongEps.zShift z p)
      = ((Real.exp p + z) / z) ^ 2 := by
    have hquot : (1 + z * Real.exp (-p)) / (z * Real.exp (-p))
        = (Real.exp p + z) / z := by
      have hep : Real.exp (-p) * Real.exp p = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      rw [show 1 + z * Real.exp (-p) = Real.exp (-p) * (Real.exp p + z) from by
            rw [mul_add, hep]; ring,
          show z * Real.exp (-p) = Real.exp (-p) * z from by rw [mul_comm]]
      exact mul_div_mul_left _ _ (Real.exp_ne_zero (-p))
    have hsq' : Work.Spaces.w (Work.FTS.StrongEps.zShift z p)
        = ((1 + z * Real.exp (-p)) / (z * Real.exp (-p))) ^ 2 := by
      rw [Work.FTS.StrongEps.zShift, Work.Spaces.w, div_pow]
    rw [hsq', hquot]
  rw [hA, hB]
  calc ((1 + z) / z) ^ 2
      ≤ (Real.exp |p| * ((Real.exp p + z) / z)) ^ 2 := hsq
    _ = Real.exp (2 * |p|) * ((Real.exp p + z) / z) ^ 2 := by rw [mul_pow, hexp2]

/-! ## The angular half -/

/-- **`sin(2θ)^{-η/2} ≤ e^{|p|} sin(2·thShift θ p)^{-η/2}`** for `θ ∈ (0, π/2)`.  From
`sin(2·thShift θ p) ≤ e^{|p|} sin(2θ)` (`sinTwo_thShift_bounds`) one raises to the nonnegative
power `η/2`, using `(e^{|p|})^{η/2} ≤ e^{|p|}` (as `η/2 ≤ 1` and `e^{|p|} ≥ 1`), and inverts.

The statement is given with the inverses `(sin(2θ)^{η/2})⁻¹` rather than the negative powers
`sin(2θ)^{-η/2}`, which is the form in which it is consumed. -/
theorem sEtaHalf_inv_thShift_le {θ p : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))⁻¹
      ≤ Real.exp |p|
        * (Real.sin (2 * Work.FTS.StrongEps.thShift θ p) ^ (Work.Spaces.eta / 2))⁻¹ := by
  have hs : 0 < Real.sin (2 * θ) := Work.FTS.StrongEps.sin_two_pos hθ
  have hs' : 0 < Real.sin (2 * Work.FTS.StrongEps.thShift θ p) :=
    Work.FTS.StrongEps.sin_two_pos (Work.FTS.StrongEps.thShift_mem hθ)
  have he : 0 ≤ Work.Spaces.eta / 2 := by rw [Work.Spaces.eta]; norm_num
  have he1 : Work.Spaces.eta / 2 ≤ 1 := by rw [Work.Spaces.eta]; norm_num
  have hE : (1 : ℝ) ≤ Real.exp |p| := Real.one_le_exp (abs_nonneg p)
  -- raise the bound `sin(2·thShift) ≤ e^{|p|} sin 2θ` to the nonnegative power `η/2`
  have h1 : Real.sin (2 * Work.FTS.StrongEps.thShift θ p) ^ (Work.Spaces.eta / 2)
      ≤ Real.exp |p| * Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := by
    have h0 : Real.sin (2 * Work.FTS.StrongEps.thShift θ p) ^ (Work.Spaces.eta / 2)
        ≤ (Real.exp |p| * Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
      Real.rpow_le_rpow hs'.le (Work.FTS.StrongEps.sinTwo_thShift_bounds hθ).2 he
    rw [Real.mul_rpow (Real.exp_pos _).le hs.le] at h0
    have h2 : (Real.exp |p|) ^ (Work.Spaces.eta / 2) ≤ Real.exp |p| :=
      Real.rpow_le_self_of_one_le hE he1
    have h3 : 0 ≤ Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) :=
      (Real.rpow_pos_of_pos hs _).le
    calc Real.sin (2 * Work.FTS.StrongEps.thShift θ p) ^ (Work.Spaces.eta / 2)
        ≤ (Real.exp |p|) ^ (Work.Spaces.eta / 2) * Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := h0
      _ ≤ Real.exp |p| * Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) :=
          mul_le_mul_of_nonneg_right h2 h3
  -- invert the inequality
  have h4 : (Real.exp |p| * Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))⁻¹
      ≤ (Real.sin (2 * Work.FTS.StrongEps.thShift θ p) ^ (Work.Spaces.eta / 2))⁻¹ :=
    (inv_le_inv₀ (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hs _))
      (Real.rpow_pos_of_pos hs' _)).mpr h1
  have h5 : (Real.exp |p| * Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))⁻¹
      = Real.exp (-|p|) * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))⁻¹ := by
    rw [mul_inv_rev, ← Real.exp_neg]
    ring
  rw [h5] at h4
  have h6 := mul_le_mul_of_nonneg_left h4 (Real.exp_pos |p|).le
  rwa [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at h6

/-! ## The two halves combined -/

theorem wdiv_shift_le :
    ∃ C : ℝ, 0 < C ∧ ∀ z θ p₁ p₂ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        ≤ Real.exp (C * (|p₁| + |p₂|))
          * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p₁)
              / (Real.sin (2 * (Work.FTS.StrongEps.thShift θ p₂))) ^ (Work.Spaces.eta / 2)) := by
  refine ⟨3, by norm_num, fun z θ p₁ p₂ hz hθ => ?_⟩
  have hs : 0 < Real.sin (2 * θ) := Work.FTS.StrongEps.sin_two_pos hθ
  have hs' : 0 < Real.sin (2 * Work.FTS.StrongEps.thShift θ p₂) :=
    Work.FTS.StrongEps.sin_two_pos (Work.FTS.StrongEps.thShift_mem hθ)
  have hw := w_le_w_zShift z p₁ hz
  have hth := sEtaHalf_inv_thShift_le (θ := θ) (p := p₂) hθ
  have hprod : Work.Spaces.w z * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))⁻¹
      ≤ (Real.exp (2 * |p₁|) * Work.Spaces.w (Work.FTS.StrongEps.zShift z p₁))
        * (Real.exp |p₂|
            * (Real.sin (2 * Work.FTS.StrongEps.thShift θ p₂)
                ^ (Work.Spaces.eta / 2))⁻¹) :=
    mul_le_mul hw hth (inv_nonneg.mpr (Real.rpow_nonneg hs.le _))
      (mul_nonneg (Real.exp_pos _).le (Work.FTS.StrongEps.w_nonneg _))
  have hexp : Real.exp (2 * |p₁| + |p₂|) ≤ Real.exp (3 * (|p₁| + |p₂|)) :=
    Real.exp_le_exp.mpr (by nlinarith [abs_nonneg p₁, abs_nonneg p₂])
  have hnn : 0 ≤ Work.Spaces.w (Work.FTS.StrongEps.zShift z p₁)
      * (Real.sin (2 * Work.FTS.StrongEps.thShift θ p₂) ^ (Work.Spaces.eta / 2))⁻¹ :=
    mul_nonneg (Work.FTS.StrongEps.w_nonneg _)
      (inv_nonneg.mpr (Real.rpow_nonneg hs'.le _))
  calc Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
      = Work.Spaces.w z * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))⁻¹ := by
        simp only [div_eq_mul_inv]
    _ ≤ (Real.exp (2 * |p₁|) * Work.Spaces.w (Work.FTS.StrongEps.zShift z p₁))
        * (Real.exp |p₂|
            * (Real.sin (2 * Work.FTS.StrongEps.thShift θ p₂)
                ^ (Work.Spaces.eta / 2))⁻¹) := hprod
    _ = Real.exp (2 * |p₁| + |p₂|)
          * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p₁)
              * (Real.sin (2 * Work.FTS.StrongEps.thShift θ p₂)
                  ^ (Work.Spaces.eta / 2))⁻¹) := by
        rw [Real.exp_add]; ring
    _ ≤ Real.exp (3 * (|p₁| + |p₂|))
          * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p₁)
              * (Real.sin (2 * Work.FTS.StrongEps.thShift θ p₂)
                  ^ (Work.Spaces.eta / 2))⁻¹) :=
        mul_le_mul_of_nonneg_right hexp hnn
    _ = Real.exp (3 * (|p₁| + |p₂|))
          * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p₁)
              / (Real.sin (2 * (Work.FTS.StrongEps.thShift θ p₂)))
                  ^ (Work.Spaces.eta / 2)) := by
        simp only [div_eq_mul_inv]

end Work.FTS.StrongEps.HkSqAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.JepsHkMem.aemeasurable_pair_slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.JepsHkMem

open Work.FTS.StrongEps

/-! ## Elementary facts about `Jker`, the shifts and the angular interval -/

/-- `Jker ρ ε` is continuous as soon as `ρ` is: no support/mass/nonnegativity hypothesis is
needed for measurability. -/
private lemma continuous_Jker_of_continuous (ρ : ℝ × ℝ → ℝ) (hρc : Continuous ρ) (ε : ℝ) :
    Continuous (Jker ρ ε) := by
  have h : Jker ρ ε = fun p : ℝ × ℝ => ε⁻¹ ^ 2 * ρ (ε⁻¹ • p) := by
    funext p; simp only [Jker]
  rw [h]
  exact continuous_const.mul (hρc.comp (continuous_const_smul ε⁻¹))

/-- The endpoints `θ = 0`, `θ = π/2` are null for `volume.restrict Iθ`. -/
private lemma measure_Iθ_compl_Ioo :
    (volume.restrict Work.Spaces.Iθ) (Set.Ioo (0 : ℝ) (π / 2))ᶜ = 0 := by
  rw [Measure.restrict_apply measurableSet_Ioo.compl]
  have h0 : (volume : Measure ℝ) ({0} ∪ {π / 2}) = 0 :=
    measure_union_null (measure_singleton 0) (measure_singleton (π / 2))
  refine measure_mono_null ?_ h0
  intro x hx
  simp only [Work.Spaces.Iθ, Set.mem_inter_iff, Set.mem_Icc, Set.mem_compl_iff, Set.mem_Ioo,
    Set.mem_union, Set.mem_singleton_iff] at hx ⊢
  obtain ⟨hxn, hxI⟩ := hx
  rcases lt_or_ge (0 : ℝ) x with h | h
  · rcases lt_or_ge x (π / 2) with h2 | h2
    · exact absurd ⟨h, h2⟩ hxn
    · exact Or.inr (le_antisymm hxI.2 h2)
  · exact Or.inl (le_antisymm h hxI.1)

/-- The complement of `{q | q.1 ∈ (0, π/2)}` is null for `(volume.restrict Iθ).prod volume`. -/
private lemma measure_compl_Ioo_prod :
    ((volume.restrict Work.Spaces.Iθ).prod (volume : Measure (ℝ × ℝ)))
      ({q : ℝ × (ℝ × ℝ) | q.1 ∈ Set.Ioo (0 : ℝ) (π / 2)}ᶜ) = 0 := by
  have hset : ({q : ℝ × (ℝ × ℝ) | q.1 ∈ Set.Ioo (0 : ℝ) (π / 2)}ᶜ :
      Set (ℝ × (ℝ × ℝ))) = (Set.Ioo (0 : ℝ) (π / 2))ᶜ ×ˢ (Set.univ : Set (ℝ × ℝ)) := by
    ext q; simp
  rw [hset, Measure.prod_prod, measure_Iθ_compl_Ioo]
  simp

/-- The `θ`-shift, as a function of the angular coordinate, is continuous on `(0, π/2)`. -/
private lemma continuousOn_thShift_slice :
    ContinuousOn (fun q : ℝ × (ℝ × ℝ) => thShift q.1 q.2.2)
      {q | q.1 ∈ Set.Ioo (0 : ℝ) (π / 2)} := by
  have htan : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => Real.tan q.1)
      {q | q.1 ∈ Set.Ioo (0 : ℝ) (π / 2)} := by
    refine Real.continuousOn_tan.comp continuous_fst.continuousOn (fun q hq => ?_)
    simp only [Set.mem_ofPred_eq] at hq
    exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hq.1], hq.2⟩).ne'
  have h1 : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => Real.tan q.1 * Real.exp (-q.2.2))
      {q | q.1 ∈ Set.Ioo (0 : ℝ) (π / 2)} :=
    htan.mul (Real.continuous_exp.comp_continuousOn (continuous_snd.snd.neg).continuousOn)
  have h2 := Real.continuous_arctan.comp_continuousOn h1
  simpa only [thShift, Function.comp_def] using h2

/-- The `z`-shift of the base `z` is continuous (in the shift variable). -/
private lemma continuousOn_zShift_theta (z : ℝ) :
    ContinuousOn (fun q : ℝ × (ℝ × ℝ) => zShift z q.2.1)
      {q | q.1 ∈ Set.Ioo (0 : ℝ) (π / 2)} := by
  simp only [zShift]
  exact (continuous_const.mul (Real.continuous_exp.comp (continuous_snd.fst.neg))).continuousOn

/-- The shifted point, as a function of `(θ, p)`, is continuous on `{θ ∈ (0, π/2)}`. -/
private lemma continuousOn_shift_pair_theta (z : ℝ) :
    ContinuousOn (fun q : ℝ × (ℝ × ℝ) => (zShift z q.2.1, thShift q.1 q.2.2))
      {q | q.1 ∈ Set.Ioo (0 : ℝ) (π / 2)} :=
  ContinuousOn.prodMk (continuousOn_zShift_theta z) continuousOn_thShift_slice

/-- For `θ ∈ (0, π/2)` and `z > 0`, the shifted point lies in the quadrant. -/
private lemma shift_mem_Quad_theta {z : ℝ} (hz : 0 < z) {q : ℝ × (ℝ × ℝ)}
    (hq : q.1 ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (zShift z q.2.1, thShift q.1 q.2.2) ∈ Quad :=
  ⟨zShift_pos hz, thShift_mem hq⟩

/-! ## The target -/

theorem aemeasurable_pair_slice {H : ℝ → ℝ → ℝ}
    (hH : ContinuousOn (fun q : ℝ × ℝ => H q.1 q.2) Work.FTS.StrongEps.Quad)
    {ρ : ℝ × ℝ → ℝ} (hρc : Continuous ρ) {ε c z : ℝ} (hz : 0 < z) :
    AEMeasurable (fun q : ℝ × (ℝ × ℝ) =>
        ENNReal.ofReal (Work.FTS.StrongEps.Jker ρ ε q.2)
          * ENNReal.ofReal (Real.exp (2 * c * (|q.2.1| + |q.2.2|)))
          * ENNReal.ofReal (H (Work.FTS.StrongEps.zShift z q.2.1)
              (Work.FTS.StrongEps.thShift q.1 q.2.2)))
      ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod MeasureTheory.volume) := by
  classical
  set S : Set (ℝ × (ℝ × ℝ)) := {q | q.1 ∈ Set.Ioo (0 : ℝ) (π / 2)} with hSdef
  -- `S` is measurable and conull.
  have hSmeas : MeasurableSet S := by
    rw [hSdef]
    exact (isOpen_Ioo.preimage continuous_fst).measurableSet
  have hnull : ((volume.restrict Work.Spaces.Iθ).prod (volume : Measure (ℝ × ℝ))) Sᶜ = 0 := by
    rw [hSdef]
    exact measure_compl_Ioo_prod
  -- On `S`, the composed profile is continuous.
  have hcont : ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      H (zShift z q.2.1) (thShift q.1 q.2.2)) S := by
    rw [hSdef]
    exact hH.comp (continuousOn_shift_pair_theta z)
      (fun q hq => shift_mem_Quad_theta hz hq)
  have hA : AEMeasurable (fun q : ℝ × (ℝ × ℝ) =>
      H (zShift z q.2.1) (thShift q.1 q.2.2))
      (Measure.restrict
        ((volume.restrict Work.Spaces.Iθ).prod (volume : Measure (ℝ × ℝ))) S) :=
    hcont.aemeasurable hSmeas
  -- Multiply by the indicator of `S` and remove it again using conullity.
  have hind : AEMeasurable (S.indicator (fun q : ℝ × (ℝ × ℝ) =>
      H (zShift z q.2.1) (thShift q.1 q.2.2)))
      ((volume.restrict Work.Spaces.Iθ).prod (volume : Measure (ℝ × ℝ))) :=
    (aemeasurable_indicator_iff hSmeas).mpr hA
  have hcongr : (fun q : ℝ × (ℝ × ℝ) => H (zShift z q.2.1) (thShift q.1 q.2.2))
      =ᵐ[((volume.restrict Work.Spaces.Iθ).prod (volume : Measure (ℝ × ℝ)))]
      S.indicator (fun q : ℝ × (ℝ × ℝ) => H (zShift z q.2.1) (thShift q.1 q.2.2)) := by
    filter_upwards [compl_mem_ae_iff.mpr hnull] with q hq
    simp only [Set.mem_compl_iff, not_not] at hq
    exact (Set.indicator_of_mem hq
      (fun q : ℝ × (ℝ × ℝ) => H (zShift z q.2.1) (thShift q.1 q.2.2))).symm
  have hHae : AEMeasurable (fun q : ℝ × (ℝ × ℝ) =>
      H (zShift z q.2.1) (thShift q.1 q.2.2))
      ((volume.restrict Work.Spaces.Iθ).prod (volume : Measure (ℝ × ℝ))) :=
    hind.congr hcongr.symm
  have hHenn : AEMeasurable (fun q : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (H (zShift z q.2.1) (thShift q.1 q.2.2)))
      ((volume.restrict Work.Spaces.Iθ).prod (volume : Measure (ℝ × ℝ))) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hHae
  -- The kernel factor.
  have hJ : AEMeasurable (fun q : ℝ × (ℝ × ℝ) => ENNReal.ofReal (Jker ρ ε q.2))
      ((volume.restrict Work.Spaces.Iθ).prod (volume : Measure (ℝ × ℝ))) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((continuous_Jker_of_continuous ρ hρc ε).comp continuous_snd).aemeasurable)
  -- The exponential weight factor.
  have hEcont : Continuous (fun q : ℝ × (ℝ × ℝ) =>
      Real.exp (2 * c * (|q.2.1| + |q.2.2|))) :=
    Real.continuous_exp.comp (continuous_const.mul
      ((continuous_snd.fst.abs).add (continuous_snd.snd.abs)))
  have hE : AEMeasurable (fun q : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (Real.exp (2 * c * (|q.2.1| + |q.2.2|))))
      ((volume.restrict Work.Spaces.Iθ).prod (volume : Measure (ℝ × ℝ))) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hEcont.aemeasurable
  exact (hJ.mul hE).mul hHenn

end Work.FTS.StrongEps.JepsHkMem
end
-- ===== merged: Submission.Work.FTS.StrongEps.Jeps_tendsto_of_tendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Filter MeasureTheory Set

namespace Work.FTS.StrongEps

set_option autoImplicit false



end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.L12Sub4.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.StrongEps.L12Sub4

/-- The angular weight of `L₁₂(·)(0)` in the log coordinate `ζ = log tan θ`:
`Glw ζ = κ(ζ) · K(arctan (e^ζ))` with `κ = (arctan ∘ exp)'`. -/
def Glw (ζ : ℝ) : ℝ :=
  Work.FTS.StrongEps.HkSqAux.kappa ζ * Work.Spaces.K (Real.arctan (Real.exp ζ))

/-- The pull-back `h̃(s,ζ) = h (e^s) (arctan (e^ζ))` of a profile to the log coordinates. -/
def logF (h : ℝ → ℝ → ℝ) (s ζ : ℝ) : ℝ := h (Real.exp s) (Real.arctan (Real.exp ζ))


/-- `L₁₂(h)(0)` as the double integral over the quadrant, by unfolding the definitions. -/
theorem L12_zero_eq_double (h : ℝ → ℝ → ℝ) :
    Work.Construction.L12 h 0
      = ∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * h z θ / z := rfl

end Work.FTS.StrongEps.L12Sub4
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.StepFacts.KernelFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.StepFacts

set_option autoImplicit false

/-! ## The two derivative densities and the combined kernel -/

/-- The `p₁`-derivative density of the kernel: `|∂_{p₁}ρ|`. -/
def sigma1 (ρ : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun q => |deriv (fun s : ℝ => ρ (s, q.2)) q.1|

/-- The `p₂`-derivative density of the kernel: `|∂_{p₂}ρ|`. -/
def sigma2 (ρ : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun q => |deriv (fun t : ℝ => ρ (q.1, t)) q.2|

/-- The combined kernel `ρ̃ = ρ + |∂₁ρ| + |∂₂ρ|`, whose rescaled version dominates the kernel and
both of its partial derivatives. -/
def rhoTilde (ρ : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun p => ρ p + sigma1 ρ p + sigma2 ρ p

/-- The mass of the `p₁`-derivative density: `|∂_{p₁}Jker ρ ε| = K1`. -/
def K1 (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (p : ℝ × ℝ) : ℝ :=
  ε⁻¹ * Work.FTS.StrongEps.Jker (sigma1 ρ) ε p

/-- The mass of the `p₂`-derivative density: `|∂_{p₂}Jker ρ ε| = K2`. -/
def K2 (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (p : ℝ × ℝ) : ℝ :=
  ε⁻¹ * Work.FTS.StrongEps.Jker (sigma2 ρ) ε p

/-- The combined density `Ψ = ε⁻¹ · Jker ρ̃ ε` dominating the kernel and its two partial
derivatives, and carrying the `ε⁻¹` of one routed derivative. -/
def Psi (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (p : ℝ × ℝ) : ℝ :=
  ε⁻¹ * Work.FTS.StrongEps.Jker (rhoTilde ρ) ε p

/-- `Ψ` as a single rescaled kernel: `Ψ = Jker (ε⁻¹ · ρ̃) ε`. -/
theorem Psi_eq_Jker (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (p : ℝ × ℝ) :
    Psi ρ ε p = Work.FTS.StrongEps.Jker (fun q : ℝ × ℝ => ε⁻¹ * rhoTilde ρ q) ε p := by
  simp only [Psi, Work.FTS.StrongEps.Jker]
  ring

/-- The total mass `∫ |∂_{p₁}Jker ρ ε|`. -/
def M1 (ρ : ℝ × ℝ → ℝ) (ε : ℝ) : ℝ := ∫ p, K1 ρ ε p

/-- The total mass `∫ |∂_{p₂}Jker ρ ε|`. -/
def M2 (ρ : ℝ × ℝ → ℝ) (ε : ℝ) : ℝ := ∫ p, K2 ρ ε p

/-- The largest of the three masses that can occur for a routed slot. -/
def Mmax (ρ : ℝ × ℝ → ℝ) (ε : ℝ) : ℝ := max 1 (max (M1 ρ ε) (4 * M2 ρ ε))

/-- The `ε`-free bound `ε⁻¹ Dm` for `Mmax`. -/
def Dm (ρ : ℝ × ℝ → ℝ) : ℝ := max 1 (max (∫ p, sigma1 ρ p) (4 * ∫ p, sigma2 ρ p))

/-- The `γ`-moment of the combined kernel `ρ̃`, i.e. the mass of `Ψ` seen with the shift gain
`e^{γ|p|}`. -/
def Dmass (ρ : ℝ × ℝ → ℝ) (γ : ℝ) : ℝ :=
  ∫ t : ℝ × ℝ, rhoTilde ρ t * Real.exp (γ * (|t.1| + |t.2|))

/-! ## Elementary properties -/

theorem sigma1_nonneg (ρ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : 0 ≤ sigma1 ρ p := abs_nonneg _

theorem sigma2_nonneg (ρ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : 0 ≤ sigma2 ρ p := abs_nonneg _

theorem rhoTilde_nonneg (ρ : ℝ × ℝ → ℝ) (hρ : ∀ p, 0 ≤ ρ p) (p : ℝ × ℝ) :
    0 ≤ rhoTilde ρ p := by
  refine add_nonneg (add_nonneg (hρ p) (sigma1_nonneg ρ p)) (sigma2_nonneg ρ p)

theorem rho_le_rhoTilde_pt (ρ : ℝ × ℝ → ℝ) (hρ : ∀ p, 0 ≤ ρ p) (p : ℝ × ℝ) :
    ρ p ≤ rhoTilde ρ p := by
  have h1 : ρ p ≤ ρ p + sigma1 ρ p := le_add_of_nonneg_right (sigma1_nonneg ρ p)
  have h2 : ρ p + sigma1 ρ p ≤ ρ p + sigma1 ρ p + sigma2 ρ p :=
    le_add_of_nonneg_right (sigma2_nonneg ρ p)
  exact le_trans h1 h2

theorem sigma1_le_rhoTilde (ρ : ℝ × ℝ → ℝ) (hρ : ∀ p, 0 ≤ ρ p) (p : ℝ × ℝ) :
    sigma1 ρ p ≤ rhoTilde ρ p := by
  have h1 : sigma1 ρ p ≤ ρ p + sigma1 ρ p := le_add_of_nonneg_left (hρ p)
  have h2 : ρ p + sigma1 ρ p ≤ ρ p + sigma1 ρ p + sigma2 ρ p :=
    le_add_of_nonneg_right (sigma2_nonneg ρ p)
  exact le_trans h1 h2

theorem sigma2_le_rhoTilde (ρ : ℝ × ℝ → ℝ) (hρ : ∀ p, 0 ≤ ρ p) (p : ℝ × ℝ) :
    sigma2 ρ p ≤ rhoTilde ρ p := by
  have h1 : sigma2 ρ p ≤ ρ p + sigma2 ρ p := le_add_of_nonneg_left (hρ p)
  have h2 : ρ p + sigma2 ρ p ≤ ρ p + sigma1 ρ p + sigma2 ρ p := by linarith [sigma1_nonneg ρ p]
  exact le_trans h1 h2

/-- The rescaled kernel is monotone in the density. -/
theorem Jker_mono {σ τ : ℝ × ℝ → ℝ} (h : ∀ p, σ p ≤ τ p) (ε : ℝ) (p : ℝ × ℝ) :
    Work.FTS.StrongEps.Jker σ ε p ≤ Work.FTS.StrongEps.Jker τ ε p :=
  mul_le_mul_of_nonneg_left (h (ε⁻¹ • p)) (sq_nonneg _)

theorem Jker_nonneg_of_nonneg {σ : ℝ × ℝ → ℝ} (h : ∀ p, 0 ≤ σ p) (ε : ℝ) (p : ℝ × ℝ) :
    0 ≤ Work.FTS.StrongEps.Jker σ ε p :=
  mul_nonneg (sq_nonneg _) (h (ε⁻¹ • p))


/-! ## The identification of the routed densities -/

/-- `K1` is the absolute value of the `p₁`-derivative of the kernel. -/
theorem K1_eq_abs_deriv (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε)
    (p : ℝ × ℝ) :
    K1 ρ ε p = |deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1| :=
  ((abs_deriv_Jker ρ hρ hε).1 p).symm

/-- `K2` is the absolute value of the `p₂`-derivative of the kernel. -/
theorem K2_eq_abs_deriv (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε)
    (p : ℝ × ℝ) :
    K2 ρ ε p = |deriv (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (p.1, t)) p.2| :=
  ((abs_deriv_Jker ρ hρ hε).2.1 p).symm



/-! ## The domination of the three densities by `Ψ` -/

theorem Jker_le_Psi (ρ : ℝ × ℝ → ℝ) (hρ0 : ∀ p, 0 ≤ ρ p) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (p : ℝ × ℝ) :
    Work.FTS.StrongEps.Jker ρ ε p ≤ Psi ρ ε p := by
  have hle : Work.FTS.StrongEps.Jker ρ ε p
      ≤ Work.FTS.StrongEps.Jker (rhoTilde ρ) ε p :=
    Jker_mono (rho_le_rhoTilde_pt ρ hρ0) ε p
  have h0 : 0 ≤ Work.FTS.StrongEps.Jker ρ ε p := Jker_nonneg_of_nonneg hρ0 ε p
  have h1 : (1 : ℝ) ≤ ε⁻¹ := by
    rw [← one_div]
    exact one_le_one_div hε hε1
  calc Work.FTS.StrongEps.Jker ρ ε p ≤ 1 * Work.FTS.StrongEps.Jker (rhoTilde ρ) ε p := by
        rw [one_mul]; exact hle
    _ ≤ ε⁻¹ * Work.FTS.StrongEps.Jker (rhoTilde ρ) ε p :=
        mul_le_mul_of_nonneg_right h1 (Jker_nonneg_of_nonneg (rhoTilde_nonneg ρ hρ0) ε p)
    _ = Psi ρ ε p := rfl

theorem K1_le_Psi (ρ : ℝ × ℝ → ℝ) (hρ0 : ∀ p, 0 ≤ ρ p) {ε : ℝ} (hε : 0 < ε) (p : ℝ × ℝ) :
    K1 ρ ε p ≤ Psi ρ ε p := by
  have hle : Work.FTS.StrongEps.Jker (sigma1 ρ) ε p
      ≤ Work.FTS.StrongEps.Jker (rhoTilde ρ) ε p :=
    Jker_mono (sigma1_le_rhoTilde ρ hρ0) ε p
  exact mul_le_mul_of_nonneg_left hle (by positivity)

theorem K2_le_Psi (ρ : ℝ × ℝ → ℝ) (hρ0 : ∀ p, 0 ≤ ρ p) {ε : ℝ} (hε : 0 < ε) (p : ℝ × ℝ) :
    K2 ρ ε p ≤ Psi ρ ε p := by
  have hle : Work.FTS.StrongEps.Jker (sigma2 ρ) ε p
      ≤ Work.FTS.StrongEps.Jker (rhoTilde ρ) ε p :=
    Jker_mono (sigma2_le_rhoTilde ρ hρ0) ε p
  exact mul_le_mul_of_nonneg_left hle (by positivity)

/-! ## Continuity, nonnegativity and support of the derived densities -/

theorem rhoTilde_continuous (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) :
    Continuous (rhoTilde ρ) := by
  have h := abs_deriv_Jker ρ hρ (ε := 1) zero_lt_one
  exact (hρ.moll.cont.add h.2.2.1.abs).add h.2.2.2.1.abs

theorem rhoTilde_support (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {p : ℝ × ℝ}
    (hp : rhoTilde ρ p ≠ 0) : p.1 ^ 2 + p.2 ^ 2 ≤ 1 := by
  have h := abs_deriv_Jker ρ hρ (ε := 1) zero_lt_one
  have hρ0 := hρ.moll.nonneg
  have hs1 : 0 ≤ sigma1 ρ p := sigma1_nonneg ρ p
  have hs2 : 0 ≤ sigma2 ρ p := sigma2_nonneg ρ p
  have hsum : ρ p + sigma1 ρ p + sigma2 ρ p ≠ 0 := hp
  rcases eq_or_lt_of_le (hρ0 p) with h0 | h0
  · rcases eq_or_lt_of_le hs1 with h1 | h1
    · have h2 : sigma2 ρ p ≠ 0 := by
        intro hh
        exact hsum (by rw [← h0, ← h1, hh, add_zero, zero_add])
      exact h.2.2.2.2.2 p (by simpa [sigma2] using h2)
    · exact h.2.2.2.2.1 p (by simpa [sigma1] using h1.ne')
  · exact hρ.moll.support p h0.ne'

theorem sigma1_support (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {p : ℝ × ℝ}
    (hp : sigma1 ρ p ≠ 0) : p.1 ^ 2 + p.2 ^ 2 ≤ 1 :=
  (abs_deriv_Jker ρ hρ (ε := 1) zero_lt_one).2.2.2.2.1 p (by simpa [sigma1] using hp)

theorem sigma2_support (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {p : ℝ × ℝ}
    (hp : sigma2 ρ p ≠ 0) : p.1 ^ 2 + p.2 ^ 2 ≤ 1 :=
  (abs_deriv_Jker ρ hρ (ε := 1) zero_lt_one).2.2.2.2.2 p (by simpa [sigma2] using hp)

theorem sigma1_continuous (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) : Continuous (sigma1 ρ) :=
  ((abs_deriv_Jker ρ hρ (ε := 1) zero_lt_one).2.2.1).abs

theorem sigma2_continuous (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) : Continuous (sigma2 ρ) :=
  ((abs_deriv_Jker ρ hρ (ε := 1) zero_lt_one).2.2.2.1).abs

/-! ## The mass bounds -/

/-- The mass of `K1` is at most `ε⁻¹` times the mass of `|∂₁ρ|`. -/
theorem M1_le (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    M1 ρ ε ≤ ε⁻¹ * ∫ p, sigma1 ρ p := by
  have hmom := (Jker_moment_le (sigma1 ρ) (sigma1_nonneg ρ) (sigma1_continuous ρ hρ)
    (fun p hp => sigma1_support ρ hρ hp) (ε := ε) (γ := 0) hε hε1 le_rfl).2
  simp only [zero_mul, mul_zero, Real.exp_zero, mul_one] at hmom
  have hconst : (∫ p : ℝ × ℝ, K1 ρ ε p)
      = ε⁻¹ * ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker (sigma1 ρ) ε p := by
    simp only [K1]
    exact MeasureTheory.integral_const_mul _ _
  rw [M1, hconst]
  exact mul_le_mul_of_nonneg_left hmom (by positivity)

/-- The mass of `K2` is at most `ε⁻¹` times the mass of `|∂₂ρ|`. -/
theorem M2_le (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    M2 ρ ε ≤ ε⁻¹ * ∫ p, sigma2 ρ p := by
  have hmom := (Jker_moment_le (sigma2 ρ) (sigma2_nonneg ρ) (sigma2_continuous ρ hρ)
    (fun p hp => sigma2_support ρ hρ hp) (ε := ε) (γ := 0) hε hε1 le_rfl).2
  simp only [zero_mul, mul_zero, Real.exp_zero, mul_one] at hmom
  have hconst : (∫ p : ℝ × ℝ, K2 ρ ε p)
      = ε⁻¹ * ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker (sigma2 ρ) ε p := by
    simp only [K2]
    exact MeasureTheory.integral_const_mul _ _
  rw [M2, hconst]
  exact mul_le_mul_of_nonneg_left hmom (by positivity)

/-- **`Mmax ≤ ε⁻¹ Dm`**: the three masses of the routed slots are bounded by `ε⁻¹` times the
`ε`-free quantity `Dm`. -/
theorem Mmax_le (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Mmax ρ ε ≤ ε⁻¹ * Dm ρ := by
  have h1 := M1_le ρ hρ hε hε1
  have h2 := M2_le ρ hρ hε hε1
  have h0 : (0 : ℝ) < ε⁻¹ := by positivity
  have hDm1 : (1 : ℝ) ≤ Dm ρ := le_max_left _ _
  have hDm2 : (∫ p, sigma1 ρ p) ≤ Dm ρ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hDm3 : 4 * ∫ p, sigma2 ρ p ≤ Dm ρ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hnn1 : 0 ≤ ∫ p, sigma1 ρ p :=
    integral_nonneg fun p => sigma1_nonneg ρ p
  have hnn2 : 0 ≤ ∫ p, sigma2 ρ p :=
    integral_nonneg fun p => sigma2_nonneg ρ p
  have hεinv1 : (1 : ℝ) ≤ ε⁻¹ := by
    rw [← one_div]
    exact one_le_one_div hε hε1
  rw [Mmax]
  refine max_le ?_ (max_le ?_ ?_)
  · calc (1 : ℝ) ≤ ε⁻¹ * 1 := by rw [mul_one]; exact hεinv1
      _ ≤ ε⁻¹ * Dm ρ := mul_le_mul_of_nonneg_left hDm1 (by positivity)
  · exact h1.trans (mul_le_mul_of_nonneg_left hDm2 (by positivity))
  · calc 4 * M2 ρ ε ≤ 4 * (ε⁻¹ * ∫ p, sigma2 ρ p) :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = ε⁻¹ * (4 * ∫ p, sigma2 ρ p) := by ring
      _ ≤ ε⁻¹ * Dm ρ := mul_le_mul_of_nonneg_left hDm3 (by positivity)

/-- **The moment bound for the combined density**: `∫ Ψ p e^{γ|p|} dp ≤ ε⁻¹ Dmass`. -/
theorem Psi_mass (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε γ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hγ : 0 ≤ γ) :
    (∫ p : ℝ × ℝ, Psi ρ ε p * Real.exp (γ * (|p.1| + |p.2|)))
      ≤ ε⁻¹ * Dmass ρ γ := by
  have hmom := (Jker_moment_le (rhoTilde ρ) (rhoTilde_nonneg ρ hρ.moll.nonneg)
    (rhoTilde_continuous ρ hρ) (fun p hp => rhoTilde_support ρ hρ hp)
    (ε := ε) (γ := γ) hε hε1 hγ).2
  rw [Dmass]
  calc (∫ p : ℝ × ℝ, Psi ρ ε p * Real.exp (γ * (|p.1| + |p.2|)))
      = ∫ p : ℝ × ℝ, ε⁻¹ * (Work.FTS.StrongEps.Jker (rhoTilde ρ) ε p
          * Real.exp (γ * (|p.1| + |p.2|))) := by
        refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun p => ?_)
        simp only [Psi]
        ring
    _ = ε⁻¹ * ∫ p : ℝ × ℝ,
          Work.FTS.StrongEps.Jker (rhoTilde ρ) ε p * Real.exp (γ * (|p.1| + |p.2|)) :=
        MeasureTheory.integral_const_mul _ _
    _ ≤ ε⁻¹ * ∫ t : ℝ × ℝ, rhoTilde ρ t * Real.exp (γ * (|t.1| + |t.2|)) :=
        mul_le_mul_of_nonneg_left hmom (by positivity)

/-- The moment integrand of `Ψ` is integrable. -/
theorem Psi_moment_integrable (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε γ : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hγ : 0 ≤ γ) :
    Integrable (fun p : ℝ × ℝ => Psi ρ ε p * Real.exp (γ * (|p.1| + |p.2|))) := by
  have hint := (Jker_moment_le (rhoTilde ρ) (rhoTilde_nonneg ρ hρ.moll.nonneg)
    (rhoTilde_continuous ρ hρ) (fun p hp => rhoTilde_support ρ hρ hp)
    (ε := ε) (γ := γ) hε hε1 hγ).1
  refine (hint.const_mul ε⁻¹).congr (Eventually.of_forall fun p => ?_)
  simp only [Psi]
  ring

/-! ## Measurability of the shifted integrand against `Ψ` -/

/-- **Joint a.e. measurability of the density-times-shifted-integrand**, in the exact shape in
which the Tonelli step of the chain lemma uses it. -/
theorem aemeasurable_Psi_shift {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {ε c : ℝ}
    {α : ℝ} {k : ℕ} {u : ℝ → ℝ → ℝ}
    (hu : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k u q.1 q.2)
      Work.FTS.StrongEps.Quad) :
    AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
        ENNReal.ofReal (Psi ρ ε q.2)
          * ENNReal.ofReal (Real.exp (2 * c * (|q.2.1| + |q.2.2|)))
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k u
              (Work.FTS.StrongEps.zShift q.1.1 q.2.1)
              (Work.FTS.StrongEps.thShift q.1.2 q.2.2)))
      (((volume.restrict Work.Spaces.Iz).prod
          (volume.restrict Work.Spaces.Iθ)).prod volume) := by
  have hτc : Continuous (rhoTilde ρ) := rhoTilde_continuous ρ hρ
  have hbase := HkSqAux.aemeasurable_shift_pair
    (G := fun z θ => Work.Spaces.HkIntegrand α k u z θ) hu
    (fun q : ℝ × ℝ => ε⁻¹ * rhoTilde ρ q) (hτc.const_mul _) ε
  have hcont_exp : Continuous fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      Real.exp (2 * c * (|q.2.1| + |q.2.2|)) := by
    refine Real.continuous_exp.comp ?_
    refine Continuous.mul continuous_const (Continuous.add ?_ ?_)
    · exact continuous_abs.comp (continuous_fst.comp continuous_snd)
    · exact continuous_abs.comp (continuous_snd.comp continuous_snd)
  have hexp : AEMeasurable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      ENNReal.ofReal (Real.exp (2 * c * (|q.2.1| + |q.2.2|))))
      (((volume.restrict Work.Spaces.Iz).prod
          (volume.restrict Work.Spaces.Iθ)).prod volume) :=
    (ENNReal.measurable_ofReal.comp hcont_exp.measurable).aemeasurable
  refine (hbase.mul hexp).congr (Eventually.of_forall fun q => ?_)
  simp only [Pi.mul_apply, Psi_eq_Jker]
  ring

end Work.FTS.StrongEps.StepFacts
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.Xn_le_of_convLocUnif =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

theorem Xn_le_of_convLocUnif {α B C₀ : ℝ} {G : ℕ → Work.FTS.Galerkin.Fn} {f : Work.FTS.Galerkin.Fn}
    (hconv : Work.FTS.StrongEps.ConvLocUnifH6 α B G f)
    (hmem : ∀ n : ℕ, Work.Spaces.HkMem α 4 (G n))
    (hbsq : ∀ n : ℕ, Work.FTS.Nonlin.Xn α (G n) ≤ C₀ * α ^ 2) :
    Work.FTS.Nonlin.Xn α f ≤ C₀ * α ^ 2 := by
  -- `Xn` is `HkNorm α 4`, so the hypothesis is a uniform bound on the `ℋ⁴`-norms of the
  -- approximants, hence (by squaring) a uniform bound on their `ℋ⁴`-energies.
  have hC₀ : 0 ≤ C₀ * α ^ 2 :=
    le_trans (Work.Spaces.HkNorm_nonneg α 4 (G 0)) (hbsq 0)
  have hsq : ∀ n : ℕ, Work.Spaces.HkSq α 4 (G n) ≤ (C₀ * α ^ 2) ^ 2 := by
    intro n
    have hsqn : Work.Spaces.HkSq α 4 (G n) = (Work.Spaces.HkNorm α 4 (G n)) ^ 2 :=
      (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 (G n))).symm
    rw [hsqn]
    exact pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 (G n)) (hbsq n) 2
  -- lower semicontinuity of the `ℋ⁴`-energy along the locally uniform slot convergence
  have hlim : Work.Spaces.HkSq α 4 f ≤ (C₀ * α ^ 2) ^ 2 :=
    HkSq_four_le_of_conv (B4 := (C₀ * α ^ 2) ^ 2) hconv hmem hsq
  calc Work.FTS.Nonlin.Xn α f = Real.sqrt (Work.Spaces.HkSq α 4 f) := rfl
    _ ≤ Real.sqrt ((C₀ * α ^ 2) ^ 2) := Real.sqrt_le_sqrt hlim
    _ = C₀ * α ^ 2 := Real.sqrt_sq hC₀

end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongEps.axis_Jeps =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

theorem axis_Jeps {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    (hax : ∀ ε' > 0, ∃ δ > 0, ∀ z : ℝ, 0 < z → z < δ →
      ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) → |f z θ / z| ≤ ε') :
    ∀ θ ∈ Set.Ioo 0 (π / 2),
      Filter.Tendsto (fun z : ℝ => Jeps ρ ε f z θ / z) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  -- the smoothness hypothesis is not needed: the bound uses only the axis condition
  have _hsm := hsm
  intro θ hθ
  rw [Metric.tendsto_nhds]
  intro η hη
  -- the tolerance of the axis condition: `ε' = η / (2 e^ε)`
  have heps' : (0 : ℝ) < η / (2 * Real.exp ε) := by positivity
  obtain ⟨δ', hδ'pos, hδ'⟩ := hax (η / (2 * Real.exp ε)) heps'
  -- the `z`-window: `z e^ε < δ'`
  set δ : ℝ := δ' / 2 * Real.exp (-ε) with hδdef
  have hδpos : 0 < δ := mul_pos (by linarith) (Real.exp_pos _)
  refine Filter.mem_of_superset (Ioc_mem_nhdsGT hδpos) ?_
  intro z hz
  rw [Set.mem_Ioc] at hz
  obtain ⟨hzpos, hzle⟩ := hz
  -- the mollified profile is `O(z)`
  have hJ : |Jeps ρ ε f z θ| ≤ η / 2 * z := by
    refine abs_Jeps_le_sup ρ hρ hε hzpos hθ (M := η / 2 * z) ?_
      (mul_nonneg (by linarith) hzpos.le)
    intro p hp1 hp2
    -- the shifted point still lies in the region where the axis condition holds
    have hneg : -p.1 ≤ ε := by
      have h := (abs_le.mp hp1).1
      linarith
    have hshift : z * Real.exp (-p.1) ≤ δ' / 2 := by
      have h1 : Real.exp (-p.1) ≤ Real.exp ε := Real.exp_le_exp.mpr hneg
      have h2 : z * Real.exp (-p.1) ≤ δ * Real.exp ε :=
        mul_le_mul hzle h1 (Real.exp_pos _).le hδpos.le
      have h3 : δ * Real.exp ε = δ' / 2 := by
        rw [hδdef]
        rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      linarith
    have hzsp : 0 < zShift z p.1 := zShift_pos hzpos
    have hzsp' : zShift z p.1 < δ' := by
      have h4 : zShift z p.1 = z * Real.exp (-p.1) := rfl
      rw [h4]
      linarith
    have hbd := hδ' (zShift z p.1) hzsp hzsp' (thShift θ p.2) (thShift_mem hθ)
    -- `|f| ≤ ε' · z e^ε` on the shifted point, and `ε' e^ε = η/2`
    calc |f (zShift z p.1) (thShift θ p.2)|
        = |f (zShift z p.1) (thShift θ p.2) / zShift z p.1| * zShift z p.1 := by
          rw [abs_div, abs_of_pos hzsp, div_mul_cancel₀ _ hzsp.ne']
      _ ≤ (η / (2 * Real.exp ε)) * zShift z p.1 :=
          mul_le_mul_of_nonneg_right hbd hzsp.le
      _ ≤ (η / (2 * Real.exp ε)) * (z * Real.exp ε) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          simp only [zShift]
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hneg) hzpos.le
      _ = η / 2 * z := by
          field_simp
  -- divide by `z > 0`
  show dist (Jeps ρ ε f z θ / z) 0 < η
  rw [Real.dist_eq, sub_zero]
  have hbound : |Jeps ρ ε f z θ / z| ≤ η / 2 := by
    rw [abs_div, abs_of_pos hzpos, div_le_iff₀ hzpos]
    exact hJ
  linarith

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongLWP.Library =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongLWP

open Work.FTS.Galerkin (Fn Fam slice gdot)

set_option autoImplicit false

/-! ## General monotonicity of `ℋ^k`-membership -/

/-- **`ℋ^k`-membership descends in the order**, for data smooth on a neighbourhood of the closed
quadrant (`SmoothNbhd`, which makes every atom of `HkIntegrand` measurable).

This is the general `k' ≤ k` form; its one-step instance is the frozen
`Work.Coercivity.HkMem_mono`. -/
theorem HkMem_mono {α : ℝ} {k k' : ℕ} (hkk : k' ≤ k) {f : Fn}
    (hsm : Work.Spaces.SmoothNbhd f) (hm : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k' f := by
  induction k generalizing k' with
  | zero =>
      obtain rfl : k' = 0 := Nat.le_zero.mp hkk
      exact hm
  | succ k ih =>
      rcases Nat.eq_or_lt_of_le hkk with hEq | hLt
      · subst hEq; exact hm
      · exact ih (Nat.lt_succ_iff.mp hLt) (Work.Coercivity.HkMem_mono α k hsm hm)

/-! ## The class conversions -/

/-- **`RegQ α k f → RegQ α k' f` for `k' ≤ k`** (re-export of
`Work.FTS.GalerkinFix.RegQ.regQ_mono`).  In particular `RegQ α 6 g → RegQ α 4 g`, which is how
the order-`6` datum of the strong route feeds the `ℋ⁴`-level classes (`GalClass`, `UnifIP`). -/
theorem RegQ_mono {α : ℝ} {k k' : ℕ} (hkk : k' ≤ k) {f : Fn}
    (h : Work.FTS.Nonlin.RegQ α k f) : Work.FTS.Nonlin.RegQ α k' f :=
  Work.FTS.GalerkinFix.RegQ.regQ_mono h hkk




end Work.FTS.StrongLWP
end
end
-- ===== merged: Submission.Work.FTS.StrongLWP.Xn6Limit.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongLWP.Xn6Limit

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open Work.FTS.Apriori.Limit (Qd Qμ TestQ slot slotWeight adjMixed adjZ adjTh adjDzIter adjDthIter
  HksqCut activeSlots mem_Qd_iff sin_two_pos_of_mem_Qd contDiffOn_w_Qd contDiffOn_sin_rpow_Qd
  integrable_of_continuousOn_of_support TestQ_adjDzIter TestQ_mul_adjMixed)

/-! ## The active slots of the order-`k` norm -/




/-! ## The cut-off `ℋ^k`-energy -/



/-! ## Continuity of the `ℋ^k`-integrand on the open quadrant

This is the open-quadrant counterpart of `Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad`
(which needs genuine `C^∞` through `z = 0`, i.e. `SmoothQuad`).  It is proved directly from the
definition of `HkIntegrand`, so that it does not depend on the slot decomposition: each factor
`D_z^i f`, `mixed j i f`, `w`, `sin(2θ)^{c}` is `C^∞` on the open quadrant. -/

theorem continuousOn_w_Qd : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Qd :=
  contDiffOn_w_Qd.continuousOn

theorem continuousOn_sin_rpow_Qd (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Qd :=
  (contDiffOn_sin_rpow_Qd c).continuousOn

theorem continuousOn_DzIter_Qd {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Qd) (i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i f p.1 p.2) Qd :=
  (Work.FTS.LocData.contDiffOn_DzIter Work.FTS.Apriori.Limit.isOpen_Qd hf i).continuousOn

theorem continuousOn_mixed_Qd {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Qd) (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2) Qd :=
  (Work.FTS.LocData.contDiffOn_mixed Work.FTS.Apriori.Limit.isOpen_Qd hf j i).continuousOn

theorem continuousOn_Wt_Qd (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Qd := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  exact continuousOn_w_Qd.mul (continuousOn_sin_rpow_Qd _)


end Work.FTS.StrongLWP.Xn6Limit
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.midSlotSupLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

/-- **The middle-slot sup bound.**  For a datum `f` which is `C^∞` on the open quadrant and
honestly in `ℋ⁶`, and for indices with `a₁ ≤ a`, `b₁ ≤ b`, `3 ≤ a₁ + b₁`, `a + b ≤ 6`, the
left-over slot `D_z^{b-b₁} D_θ^{a-a₁} f` — of total order `≤ 3` — is bounded pointwise on the
open quadrant by `C α^{-1/2}` times `(1 + M)` when its order is `≤ 2` (with `M` an a-priori
bound for the `ℋ⁴`-norm of `f`) and by `C α^{-1/2}` times the `ℋ⁶`-norm of `f` when its order
is exactly `3`.

The three ingredients are the pointwise bounds available at the two levels:
`Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn` (α-uniform for the genuinely mixed slots of
order `≤ 2`), `Work.FTS.TransportS.sup_dz_le_hk` (the pure `D_z`-slots of order `≤ 2`, with the
`(γ-1)^{-1/2} = √10 · α^{-1/2}` loss) and `Work.FTS.StrongPersist.N6.PwAny6` (all slots of
order `≤ 4` against the `ℋ⁶`-norm, again with the `α^{-1/2}` loss). -/
theorem midSlotSupLe :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (a b a₁ b₁ : ℕ) (M : ℝ),
      α ∈ Set.Ioc 0 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      Work.FTS.Nonlin.Xn α f ≤ M →
      a₁ ≤ a → b₁ ≤ b → 3 ≤ a₁ + b₁ → a + b ≤ 6 →
      (((a - a₁) + (b - b₁) ≤ 2) →
          ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
            |Work.Spaces.mixed (b - b₁) (a - a₁) f z θ|
              ≤ C * α ^ (-(1 / 2 : ℝ)) * (1 + M)) ∧
      (((a - a₁) + (b - b₁) = 3) →
          ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
            |Work.Spaces.mixed (b - b₁) (a - a₁) f z θ|
              ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 f) := by
  obtain ⟨C1, hC1pos, hC1⟩ := Work.FTS.TransportS.sup_dz_le_hk
  obtain ⟨C2, hC2pos, hC2⟩ := Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
  obtain ⟨C3, hC3pos, hC3⟩ := Work.FTS.StrongPersist.N6.PwAny6
  refine ⟨100 * (C1 + C2 + C3 + 1), by positivity, ?_⟩
  intro α f a b a₁ b₁ M hα hF hmem6 hbdd ha₁ hb₁ h3 hab
  set p : ℝ := α ^ (-(1 / 2 : ℝ)) with hpdef
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have h4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hF 4 (by norm_num) hmem6
  have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
  -- the two square-root rewrites making the `α^{-1/2}` explicit
  have hp_sqrt : p = (Real.sqrt α)⁻¹ := by
    rw [hpdef, Real.rpow_neg hα0.le, Real.sqrt_eq_rpow]
  have hp1 : 1 ≤ p := by
    rw [hp_sqrt]
    exact (one_le_inv₀ (Real.sqrt_pos.mpr hα0)).mpr (Real.sqrt_le_one.mpr hα1)
  have hp0 : 0 ≤ p := le_trans zero_le_one hp1
  have hgam : Work.Spaces.gam α - 1 = α / 10 := Work.Spaces.gam_sub_one α
  have hroot : Real.sqrt (Work.Spaces.gam α - 1) = Real.sqrt α / Real.sqrt 10 := by
    rw [hgam, Real.sqrt_div hα0.le]
  have hrootinv : (Real.sqrt (Work.Spaces.gam α - 1))⁻¹ = Real.sqrt 10 * p := by
    rw [hroot, inv_div, div_eq_mul_inv, ← hp_sqrt]
  have hroot3 : Real.sqrt (C3 / (Work.Spaces.gam α - 1)) = Real.sqrt (10 * C3) * p := by
    have h10 : C3 / (Work.Spaces.gam α - 1) = (10 * C3) / α := by rw [hgam]; ring
    rw [h10, Real.sqrt_div (mul_nonneg (by norm_num) hC3pos.le), div_eq_mul_inv, ← hp_sqrt]
  -- the size of the constant
  have hC2le : C2 ≤ 100 * (C1 + C2 + C3 + 1) := by nlinarith
  have hC1le : Real.sqrt 10 * C1 ≤ 100 * (C1 + C2 + C3 + 1) := by
    have hs : Real.sqrt 10 ≤ 4 := by rw [Real.sqrt_le_iff]; norm_num
    nlinarith
  have hC3le : Real.sqrt (10 * C3) ≤ 100 * (C1 + C2 + C3 + 1) := by
    have hle : Real.sqrt (10 * C3) ≤ 10 * C3 + 1 := by
      rw [Real.sqrt_le_iff]
      exact ⟨by positivity, by nlinarith [sq_nonneg (10 * C3)]⟩
    nlinarith
  have hK0 : 0 ≤ 100 * (C1 + C2 + C3 + 1) := by positivity
  have hKp0 : 0 ≤ 100 * (C1 + C2 + C3 + 1) * p := mul_nonneg hK0 hp0
  have hX1 : Work.FTS.Nonlin.Xn α f ≤ 1 + M := le_trans hbdd (by linarith)
  constructor
  · -- the order-`≤ 2` slots
    intro hle z θ hz hθ hθ2
    rcases Nat.eq_zero_or_pos (a - a₁) with hi | hi
    · -- the pure radial slot `D_z^{b-b₁}`
      have hb : b - b₁ ≤ 2 := by omega
      have heq : Work.Spaces.mixed (b - b₁) (a - a₁) f = Work.Spaces.DzIter (b - b₁) f := by
        rw [hi, Work.Spaces.mixed_zero_right]
      have h := hC1 α f hα0 hα1 hF h4 (b - b₁) hb z θ hz hθ hθ2
      rw [heq]
      have hfin : C1 / Real.sqrt (Work.Spaces.gam α - 1) ≤ Real.sqrt 10 * C1 * p :=
        le_of_eq (by rw [div_eq_mul_inv, hrootinv]; ring)
      calc |Work.Spaces.DzIter (b - b₁) f z θ|
          ≤ C1 / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α f := h
        _ ≤ Real.sqrt 10 * C1 * p * Work.FTS.Nonlin.Xn α f :=
              mul_le_mul_of_nonneg_right hfin hXn0
        _ ≤ 100 * (C1 + C2 + C3 + 1) * p * (1 + M) := by
              have h1 : Real.sqrt 10 * C1 * p * Work.FTS.Nonlin.Xn α f
                  ≤ 100 * (C1 + C2 + C3 + 1) * p * Work.FTS.Nonlin.Xn α f :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1le hp0) hXn0
              have h2 : 100 * (C1 + C2 + C3 + 1) * p * Work.FTS.Nonlin.Xn α f
                  ≤ 100 * (C1 + C2 + C3 + 1) * p * (1 + M) :=
                mul_le_mul_of_nonneg_left hX1 hKp0
              linarith
    · -- a genuine mixed slot
      have hi1 : 1 ≤ a - a₁ := by omega
      have h := hC2 α f hα0 hα1 hF h4 (b - b₁) (a - a₁) hi1 hle z θ hz hθ hθ2
      calc |Work.Spaces.mixed (b - b₁) (a - a₁) f z θ|
          ≤ C2 * Work.FTS.Nonlin.Xn α f := h
        _ ≤ 100 * (C1 + C2 + C3 + 1) * p * (1 + M) := by
              have h1 : C2 * Work.FTS.Nonlin.Xn α f
                  ≤ 100 * (C1 + C2 + C3 + 1) * Work.FTS.Nonlin.Xn α f :=
                mul_le_mul_of_nonneg_right hC2le hXn0
              have hstep : Work.FTS.Nonlin.Xn α f ≤ p * (1 + M) := by
                have a1 : Work.FTS.Nonlin.Xn α f ≤ p * Work.FTS.Nonlin.Xn α f := by
                  simpa using mul_le_mul_of_nonneg_right hp1 hXn0
                exact le_trans a1 (mul_le_mul_of_nonneg_left hX1 hp0)
              have h2 : 100 * (C1 + C2 + C3 + 1) * Work.FTS.Nonlin.Xn α f
                  ≤ 100 * (C1 + C2 + C3 + 1) * p * (1 + M) := by
                calc 100 * (C1 + C2 + C3 + 1) * Work.FTS.Nonlin.Xn α f
                    ≤ 100 * (C1 + C2 + C3 + 1) * (p * (1 + M)) :=
                      mul_le_mul_of_nonneg_left hstep hK0
                  _ = 100 * (C1 + C2 + C3 + 1) * p * (1 + M) := by ring
              linarith
  · -- the order-`3` slot
    intro heq3 z θ hz hθ hθ2
    have h := hC3 α f (b - b₁) (a - a₁) hα0 hα1 hF hmem6 (by omega) z hz θ ⟨hθ, hθ2⟩
    have hnorm0 : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
    have hden0 : 0 ≤ Work.Spaces.gam α - 1 := by rw [hgam]; linarith
    have hsq : |Work.Spaces.mixed (b - b₁) (a - a₁) f z θ|
        ≤ Real.sqrt (C3 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkNorm α 6 f := by
      rw [← Real.sqrt_sq_eq_abs, Work.Spaces.HkNorm]
      calc Real.sqrt ((Work.Spaces.mixed (b - b₁) (a - a₁) f z θ) ^ 2)
          ≤ Real.sqrt (C3 / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 f) :=
            Real.sqrt_le_sqrt h
        _ = Real.sqrt (C3 / (Work.Spaces.gam α - 1))
              * Real.sqrt (Work.Spaces.HkSq α 6 f) :=
            Real.sqrt_mul (div_nonneg hC3pos.le hden0) (Work.Spaces.HkSq α 6 f)
    have hfin : Real.sqrt (C3 / (Work.Spaces.gam α - 1))
        ≤ 100 * (C1 + C2 + C3 + 1) * p := by
      rw [hroot3]
      exact mul_le_mul_of_nonneg_right hC3le hp0
    calc |Work.Spaces.mixed (b - b₁) (a - a₁) f z θ|
        ≤ Real.sqrt (C3 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkNorm α 6 f := hsq
      _ ≤ 100 * (C1 + C2 + C3 + 1) * p * Work.Spaces.HkNorm α 6 f :=
            mul_le_mul_of_nonneg_right hfin hnorm0

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.SlotSum_dz_le_of =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! The `D_z`-shift of the slot pairing and of the slot sum, with the pointwise identity
`D_z^bD_θ^a(D_z u) = D_z^{b+1}D_θ^a u` on the open quadrant taken as a hypothesis instead of
being derived from `SmoothOpen` (`Work.FTS.TransportS.mixed_dz_eqOn`). -/

/-- **The slot pairing shifts along `D_z`**, given the pointwise identity on `Q0`. -/
theorem slotPairing_dz_of (ρ : ℝ → ℝ → ℝ) (a b : ℕ) {u v : ℝ → ℝ → ℝ}
    (hu : Set.EqOn (Function.uncurry (Work.Spaces.mixed b a (Work.Spaces.Dz u)))
      (Function.uncurry (Work.Spaces.mixed (b + 1) a u)) Work.FTS.EllipticEst.Q0)
    (hv : Set.EqOn (Function.uncurry (Work.Spaces.mixed b a (Work.Spaces.Dz v)))
      (Function.uncurry (Work.Spaces.mixed (b + 1) a v)) Work.FTS.EllipticEst.Q0) :
    Work.FTS.TransportS.slotPairing ρ a b (Work.Spaces.Dz u) (Work.Spaces.Dz v)
      = Work.FTS.TransportS.slotPairing ρ a (b + 1) u v := by
  unfold Work.FTS.TransportS.slotPairing
  refine Work.FTS.TransportS.setIntegral2_congr_Q0 (fun p hp => ?_)
  simp only [Function.uncurry]
  have h1 := hu hp
  have h2 := hv hp
  simp only [Function.uncurry] at h1 h2
  rw [h1, h2]

/-- **The slot term shifts along `D_z`**, given the pointwise identity on `Q0`. -/
theorem SlotTerm_dz_le_of (α : ℝ) (a b : ℕ) {u v : ℝ → ℝ → ℝ}
    (hu : Set.EqOn (Function.uncurry (Work.Spaces.mixed b a (Work.Spaces.Dz u)))
      (Function.uncurry (Work.Spaces.mixed (b + 1) a u)) Work.FTS.EllipticEst.Q0)
    (hv : Set.EqOn (Function.uncurry (Work.Spaces.mixed b a (Work.Spaces.Dz v)))
      (Function.uncurry (Work.Spaces.mixed (b + 1) a v)) Work.FTS.EllipticEst.Q0) :
    Work.FTS.TransportS.SlotTerm α a b (Work.Spaces.Dz u) (Work.Spaces.Dz v)
      ≤ Work.FTS.TransportS.SlotTerm α a (b + 1) u v := by
  unfold Work.FTS.TransportS.SlotTerm
  rw [slotPairing_dz_of Work.FTS.TransportS.leafEta a b hu hv,
    slotPairing_dz_of Work.FTS.TransportS.leafOne a b hu hv,
    slotPairing_dz_of (Work.FTS.TransportS.leafGam α) a b hu hv]

/-- The `D_z`-shift of the slot sum at finite order: the proved `Work.FTS.TransportS.SlotSum_dz_le`
is the instance where the pointwise identity `D_z^bD_θ^a(D_z u) = D_z^{b+1}D_θ^a u` on the open
quadrant is supplied by `Work.FTS.TransportS.mixed_dz_eqOn` from `SmoothOpen`; here that identity
is a hypothesis, so the statement is a strict generalisation and hence true. -/
theorem SlotSum_dz_le_of {α : ℝ} {n : ℕ} {u v : ℝ → ℝ → ℝ}
    (hu : ∀ a b : ℕ, a + b ≤ n →
      Set.EqOn (Function.uncurry (Work.Spaces.mixed b a (Work.Spaces.Dz u)))
        (Function.uncurry (Work.Spaces.mixed (b + 1) a u)) Work.FTS.EllipticEst.Q0)
    (hv : ∀ a b : ℕ, a + b ≤ n →
      Set.EqOn (Function.uncurry (Work.Spaces.mixed b a (Work.Spaces.Dz v)))
        (Function.uncurry (Work.Spaces.mixed (b + 1) a v)) Work.FTS.EllipticEst.Q0) :
    Work.FTS.TransportS.SlotSum α n (Work.Spaces.Dz u) (Work.Spaces.Dz v)
      ≤ Work.FTS.TransportS.SlotSum α (n + 1) u v := by
  rw [Work.FTS.TransportS.SlotSum_eq_sum_SlotTerm,
    Work.FTS.TransportS.SlotSum_eq_sum_SlotTerm]
  calc (∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a),
          Work.FTS.TransportS.SlotTerm α a b (Work.Spaces.Dz u) (Work.Spaces.Dz v))
      ≤ ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 1 - a),
          Work.FTS.TransportS.SlotTerm α a (b + 1) u v :=
        Finset.sum_le_sum (fun a ha =>
          Finset.sum_le_sum (fun b hb =>
            SlotTerm_dz_le_of α a b
              (hu a b (by
                simp only [Finset.mem_range] at ha hb
                omega))
              (hv a b (by
                simp only [Finset.mem_range] at ha hb
                omega))))
    _ ≤ ∑ a ∈ Finset.range (n + 1), ∑ b ∈ Finset.range (n + 2 - a),
          Work.FTS.TransportS.SlotTerm α a b u v := by
        refine Finset.sum_le_sum (fun a _ => ?_)
        by_cases ha : a ≤ n + 1
        · rw [show n + 2 - a = (n + 1 - a) + 1 from by omega]
          conv_rhs => rw [Finset.sum_range_succ']
          exact le_add_of_nonneg_right
            (show (0 : ℝ) ≤ Work.FTS.TransportS.SlotTerm α a 0 u v from
              Work.FTS.TransportS.SlotTerm_nonneg α a 0 u v)
        · rw [show n + 1 - a = 0 from by omega]
          simp only [Finset.range_zero, Finset.sum_empty]
          exact Finset.sum_nonneg (fun b _ => Work.FTS.TransportS.SlotTerm_nonneg α a b u v)
    _ ≤ ∑ a' ∈ Finset.range (n + 2), ∑ b ∈ Finset.range (n + 2 - a'),
          Work.FTS.TransportS.SlotTerm α a' b u v := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun a ha => ?_)
          (fun a _ _ => Finset.sum_nonneg
            (fun b _ => Work.FTS.TransportS.SlotTerm_nonneg α a b u v))
        simp only [Finset.mem_range] at ha ⊢
        omega

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Aux.Acoef_Mf_le =====
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
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-!
# `Work.FTS.StrongPersist.L3Aux.Acoef_Mf_le`

The `ℋ³`-regularity and the `ℋ³`-bound of the **nonlocal summand** `A(α)·L₁₂(f)` of the
level-three linear operator, in its open-quadrant (`C³`) form:

* `Acf α f = acf(z)·(Γ(θ)/c(α))·L₁₂(f)(z)` is `C³` on the open quadrant `Q0 = (0,∞)×(0,π/2)`;
* `Acf α f ∈ ℋ³` (weighted-integral honesty);
* `HkSq α 3 (Acf α f) ≤ C·HkSq α 4 f`.

The route (all pieces are already in the workspace):

* the *first* conjunct: `L₁₂(f) ∈ C³((0,∞))` from the residue class (`HkMem α 4 f`,
  `UopHk.contDiffOn_L12_of_smoothOpen_Hk`), `z ↦ 2z/(1+z)²` is `C^∞` there, and
  `θ ↦ (sinθcos²θ)^{α/3}/c(α)` is `C^∞` on `(0,π/2)`; a product of separated smooth factors is
  jointly smooth;
* the *multiplier step*: `D_z` does not see the angular factor, so every `ℋ³`-slot of
  `acf·(gc·L₁₂f)` is a binomial sum of slots of `gc·L₁₂f` weighted by the bounded `Zop`-jets of
  `z ↦ 2z/(1+z)²` (`zslot_supBound`, value `24000`).  This is `zmul_pt` (`ZmulCore`),
  instantiated at finite smoothness (`zmul_finite_open` below);
* the *angular step*: for a separated datum `C(θ)·B(z)` the `ℋ³`-integrand factorises
  (`HkIntegrand_sep_le`), and the angular masses `∫(Γ/c)² sin^{-η}` and
  `∫(D_θ^i(Γ/c))² sin^{-γ}` are bounded uniformly in `α` (`GamJetBounds`, `10¹⁵`);
* the *radial step*: the pure `D_z`-slots of `L₁₂ f` are bounded by `HkSq α 4 f` on `Iz`
  (`L12f_slot_le`);
* the assembly integrates the resulting pointwise bound (`HkMem_of_majorant`,
  `integral_mono_of_nonneg`).
-/

/-! ## The function of the statement in separated form

`Acf α f = acf(z) · (Γ(θ)/c(α)) · L₁₂(f)(z)` with `acf(z) = 2z/(1+z)²`; the association of
the product is chosen so that the `z`-only and `θ`-only factors separate. -/

/-- The radial factor `z ↦ 2z/(1+z)²` of the nonlocal coefficient. -/
private def acf (z : ℝ) : ℝ := 2 * z / (1 + z) ^ 2

/-- The angular factor `θ ↦ Γ(θ)/c(α)`. -/
private def gcf (α : ℝ) (θ : ℝ) : ℝ := Work.Spaces.Gam α θ / Work.Spaces.c α

/-- The nonlocal summand `acf(z)·(Γ(θ)/c(α))·L₁₂(f)(z)`. -/
private def Acf (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => acf z * (gcf α θ * Work.Construction.L12 f z)

private theorem Acf_apply (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Acf α f z θ
      = (2 * z / (1 + z) ^ 2)
        * ((Work.Spaces.Gam α θ / Work.Spaces.c α) * Work.Construction.L12 f z) := rfl

/-- The function of the statement equals `Acf α f`. -/
private theorem Acf_eq_stmt (α : ℝ) (f : ℝ → ℝ → ℝ) :
    (fun z θ => ((2 * z / (1 + z) ^ 2) * (Work.Spaces.Gam α θ / Work.Spaces.c α))
        * Work.Construction.L12 f z) = Acf α f := by
  funext z θ
  rw [Acf_apply]
  ring

/-- `sin(2θ) ≥ 0` on `Iθ`. -/
private theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-! ## The first conjunct: `C³` on the open quadrant -/

/-- `z ↦ 2z/(1+z)²` is `C³` on `(0,∞)`. -/
private theorem contDiffOn_three_acf : ContDiffOn ℝ 3 acf (Set.Ioi (0 : ℝ)) := by
  have h0 : ContDiffOn ℝ ⊤ acf (Set.Ioi (-1 : ℝ)) := by
    have hfun : acf = fun z => 2 * z / (1 + z) ^ 2 := by funext z; rfl
    rw [hfun]
    exact contDiffOn_two_z_div
  exact (h0.mono (fun z hz => by
    simp only [Set.mem_Ioi] at hz ⊢
    linarith)).of_le le_top

/-- `θ ↦ Γ(θ)/c(α)` is `C³` on `(0,π/2)`. -/
private theorem contDiffOn_three_gcf (α : ℝ) :
    ContDiffOn ℝ 3 (gcf α) (Set.Ioo (0 : ℝ) (π / 2)) := by
  have hbase : ContDiffOn ℝ ⊤ (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    (Real.contDiff_sin.contDiffOn).mul ((Real.contDiff_cos.contDiffOn).pow 2)
  have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), Real.sin θ * Real.cos θ ^ 2 ≠ 0 := by
    intro θ hθ
    have h1 : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have h2 : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    positivity
  have hgam : ContDiffOn ℝ ⊤ (fun θ : ℝ => Work.Spaces.Gam α θ)
      (Set.Ioo (0 : ℝ) (π / 2)) := hbase.rpow_const_of_ne hne
  exact (hgam.div_const (Work.Spaces.c α)).of_le le_top

/-- **The nonlocal summand is `C³` on the open quadrant.** -/
private theorem contDiffOn_three_Acf {α : ℝ} {f : ℝ → ℝ → ℝ}
    (h12 : ContDiffOn ℝ 3 (Work.Construction.L12 f) (Set.Ioi (0 : ℝ))) :
    ContDiffOn ℝ 3 (Function.uncurry (Acf α f)) Work.FTS.EllipticEst.Q0 := by
  have hA : ContDiffOn ℝ 3 (fun z => acf z * Work.Construction.L12 f z) (Set.Ioi (0 : ℝ)) :=
    contDiffOn_three_acf.mul h12
  have hB : ContDiffOn ℝ 3 (gcf α) (Set.Ioo (0 : ℝ) (π / 2)) := contDiffOn_three_gcf α
  have hprod : ContDiffOn ℝ 3
      (fun p : ℝ × ℝ => (fun z => acf z * Work.Construction.L12 f z) p.1 * gcf α p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    (hA.comp contDiffOn_fst (fun p hp => hp.1)).mul
      (hB.comp contDiffOn_snd (fun p hp => hp.2))
  have hfun : Function.uncurry (Acf α f)
      = fun p : ℝ × ℝ => (fun z => acf z * Work.Construction.L12 f z) p.1 * gcf α p.2 := by
    funext p
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Acf, gcf, acf]
    ring
  rw [hfun]
  exact hprod

/-! ## The finite-order multiplier estimate

`zmul_pt` (`ZmulCore`) is the algebraic core: given, at a point, the two Leibniz expansions
of `D_z^i(φ·g)` and `D_z^jD_θ^i(φ·g)` for a `z`-only multiplier `φ` and a bound `K` on the
`Zop`-jets of `φ`, it proves `HkIntegrand α k (φ·g) ≤ zmulConst k·(1+K)²·HkIntegrand α k g`.
Here the expansions are supplied at *finite* smoothness on `(0,∞)` by
`FinalClock.DzIter_mul_of_contDiffOn` / `mixed_mul_of_contDiffOn`, which is exactly the regime
needed when `g` contains `L₁₂(f)`. -/

private theorem zmul_finite_open (α : ℝ) (k : ℕ) (φ : ℝ → ℝ) (g : ℝ → ℝ → ℝ) {K : ℝ}
    (hK : 0 ≤ K)
    (hB : ∀ (b : ℕ), b ≤ k → ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[b] φ z| ≤ K)
    (hφ : ∀ (b : ℕ), b ≤ k → ContDiffOn ℝ b φ (Set.Ioi (0 : ℝ)))
    (hg : ∀ (i : ℕ), i ≤ k → ∀ θ : ℝ,
      ContDiffOn ℝ i (fun z => g z θ) (Set.Ioi (0 : ℝ)))
    (hgθ : ∀ (j i : ℕ), 1 ≤ i → i + j ≤ k → ∀ θ : ℝ,
      ContDiffOn ℝ j (fun z => Work.Spaces.DthIter i g z θ) (Set.Ioi (0 : ℝ))) :
    ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ,
      Work.Spaces.HkIntegrand α k (fun z θ => φ z * g z θ) z θ
        ≤ zmulConst k * (1 + K) ^ 2 * Work.Spaces.HkIntegrand α k g z θ := by
  intro z hz θ
  refine zmul_pt α k φ g hK (fun b hb => hB b hb z hz) ?_ ?_
  · intro i hi
    exact Work.FTS.FinalClock.DzIter_mul_of_contDiffOn i φ g isOpen_Ioi
      (hφ i hi) (hg i hi θ) z hz
  · intro j i hi hij
    exact Work.FTS.FinalClock.mixed_mul_of_contDiffOn j i φ g isOpen_Ioi
      (hφ j (by omega)) (hgθ j i hi hij θ) z hz

/-- **Step A**: the `ℋ³`-integrand of the nonlocal summand is dominated by that of
`(Γ(θ)/c(α))·L₁₂(f)(z)`, with the constant `zmulConst 3·(1+24000)²`.

(`24000` is `zslot_supBound`: every `D_z`-iterate of `z ↦ 2z/(1+z)²` up to order `4` is bounded
by `24000` on `Iz`.) -/
private theorem acf_integrand_le (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 3 (Acf α f) z θ
        ≤ zmulConst 3 * (1 + 24000) ^ 2
          * Work.Spaces.HkIntegrand α 3 (fun z θ => gcf α θ * Work.Construction.L12 f z) z θ := by
  have hK : (0 : ℝ) ≤ 24000 := by norm_num
  have hL3 : ContDiffOn ℝ 3 (Work.Construction.L12 f) (Set.Ioi (0 : ℝ)) :=
    (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk α 4 f hsm hmem
      (by norm_num)).1
  have h12 : ∀ (i : ℕ), i ≤ 3 → ContDiffOn ℝ i (Work.Construction.L12 f)
      (Set.Ioi (0 : ℝ)) := by
    intro i hi
    exact hL3.of_le (by exact_mod_cast hi)
  have hB : ∀ (b : ℕ), b ≤ 3 → ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Spaces.Zop^[b] acf z| ≤ 24000 := by
    intro b hb z hz
    have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr (le_of_lt hz)
    have h0 : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_refl 0, by linarith [Real.pi_pos]⟩
    have h1 := zslot_supBound b (by omega) z hzI 0 h0
    have h2 : Work.Spaces.Zop^[b] acf z
        = Work.Spaces.DzIter b (fun z (_ : ℝ) => acf z) z 0 :=
      (congrFun (Work.Spaces.Zop_slice b (fun z (_ : ℝ) => acf z) 0) z).symm
    rw [h2]
    exact h1
  have hφ : ∀ (b : ℕ), b ≤ 3 → ContDiffOn ℝ b acf (Set.Ioi (0 : ℝ)) := by
    intro b hb
    exact contDiffOn_three_acf.of_le (by exact_mod_cast hb)
  have hg : ∀ (i : ℕ), i ≤ 3 → ∀ θ : ℝ,
      ContDiffOn ℝ i (fun z => gcf α θ * Work.Construction.L12 f z) (Set.Ioi (0 : ℝ)) := by
    intro i hi θ
    simpa only [smul_eq_mul] using (h12 i hi).const_smul (gcf α θ)
  have hgθ : ∀ (j i : ℕ), 1 ≤ i → i + j ≤ 3 → ∀ θ : ℝ,
      ContDiffOn ℝ j (fun z => Work.Spaces.DthIter i
        (fun z θ => gcf α θ * Work.Construction.L12 f z) z θ) (Set.Ioi (0 : ℝ)) := by
    intro j i hi hij θ
    have hdec : (fun z => Work.Spaces.DthIter i
        (fun z θ => gcf α θ * Work.Construction.L12 f z) z θ)
        = fun z => Work.Spaces.dthU^[i] (gcf α) θ * Work.Construction.L12 f z := by
      funext z
      exact Work.Spaces.DthIter_decomp i (gcf α) (fun z => Work.Construction.L12 f z) z θ
    rw [hdec]
    have hj : ContDiffOn ℝ j (Work.Construction.L12 f) (Set.Ioi (0 : ℝ)) :=
      h12 j (by omega)
    simpa only [smul_eq_mul] using hj.const_smul (Work.Spaces.dthU^[i] (gcf α) θ)
  intro z hz θ hθ
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · subst hz0
    rw [Work.FTS.LocData.HkIntegrand_zero_fst, Work.FTS.LocData.HkIntegrand_zero_fst]
    exact le_of_eq (by ring)
  · exact zmul_finite_open α 3 acf
      (fun z θ => gcf α θ * Work.Construction.L12 f z) hK hB hφ hg hgθ z hzpos θ

/-! ## The angular masses

The `θ`-factor of the majorant: the `η`-summand plus the `γ`-summands of the mixed block, with
their masses bounded uniformly in `α` by `GamJetBounds`. -/

/-- The angular factor of the majorant of the `ℋ³`-integrand of a separated datum. -/
private def Mth (α : ℝ) : ℝ → ℝ := fun θ =>
  (gcf α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    + ∑ i ∈ Finset.range 4,
        (if 1 ≤ i then (Work.Spaces.dthU^[i] (gcf α) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)


/-- The `γ`-mass integrand of the `dthU`-jet, in the `DthIter`-form of `GamJetBounds`. -/
private theorem gam_mass_form (i : ℕ) (α : ℝ) :
    (fun θ : ℝ => (Work.Spaces.dthU^[i] (gcf α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = fun θ : ℝ =>
          (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  funext θ
  rw [Work.FTS.LocData.DthIter_rad_eq i (fun θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ]
  rfl

/-- **The angular majorant and its mass.**  From the two `GamJetBounds` inputs (the `η`-mass of
`Γ/c` and the `γ`-masses of its `θ`-jets, both bounded by `K`), the angular factor `Mth α`
is integrable on `Iθ` with `∫_θ Mth α ≤ 5K`. -/
private theorem Mth_int_le (α : ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hη : MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ≤ K)
    (hγ : ∀ (i : ℕ), 1 ≤ i → i ≤ 4 →
      MeasureTheory.IntegrableOn (fun θ : ℝ =>
        (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DthIter i
        (fun _ θ' => Work.Spaces.Gam α θ' / Work.Spaces.c α) 0 θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) ≤ K) :
    MeasureTheory.IntegrableOn (Mth α) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, Mth α θ) ≤ 5 * K := by
  have hγ' : ∀ (i : ℕ), 1 ≤ i → i ≤ 4 →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.dthU^[i] (gcf α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.dthU^[i] (gcf α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) ≤ K := by
    intro i hi1 hi4
    obtain ⟨hI, hB⟩ := hγ i hi1 hi4
    exact ⟨by rwa [← gam_mass_form i α] at hI, by rwa [← gam_mass_form i α] at hB⟩
  -- integrability
  have hsum : MeasureTheory.IntegrableOn (fun θ : ℝ => ∑ i ∈ Finset.range 4,
      (if 1 ≤ i then (Work.Spaces.dthU^[i] (gcf α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)) Work.Spaces.Iθ := by
    refine MeasureTheory.integrable_finset_sum (Finset.range 4) (fun i hi => ?_)
    by_cases h : 1 ≤ i
    · simp only [if_pos h]
      exact (hγ' i h (by rw [Finset.mem_range] at hi; omega)).1
    · simp only [if_neg h]
      exact integrableOn_zero
  have hInt : MeasureTheory.IntegrableOn (Mth α) Work.Spaces.Iθ := hη.1.add hsum
  refine ⟨hInt, ?_⟩
  -- the value of the integral
  have hMth : Mth α = fun θ : ℝ =>
      (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + ∑ i ∈ Finset.range 4,
            (if 1 ≤ i then (Work.Spaces.dthU^[i] (gcf α) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0) := rfl
  have hsumInt : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range 4,
      (if 1 ≤ i then (Work.Spaces.dthU^[i] (gcf α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0))
      = ∑ i ∈ Finset.range 4,
          (∫ θ in Work.Spaces.Iθ, (if 1 ≤ i then (Work.Spaces.dthU^[i] (gcf α) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)) :=
    MeasureTheory.integral_finset_sum (Finset.range 4) (fun i hi => by
      by_cases h : 1 ≤ i
      · simp only [if_pos h]
        exact (hγ' i h (by rw [Finset.mem_range] at hi; omega)).1
      · simp only [if_neg h]
        exact integrableOn_zero)
  have hsplit : (∫ θ in Work.Spaces.Iθ, Mth α θ)
      = (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        + ∑ i ∈ Finset.range 4,
            (∫ θ in Work.Spaces.Iθ, (if 1 ≤ i then (Work.Spaces.dthU^[i] (gcf α) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)) := by
    rw [hMth, MeasureTheory.integral_add hη.1 hsum, hsumInt]
  rw [hsplit]
  have hsum_le : (∑ i ∈ Finset.range 4,
      (∫ θ in Work.Spaces.Iθ, (if 1 ≤ i then (Work.Spaces.dthU^[i] (gcf α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0))) ≤ 4 * K := by
    calc (∑ i ∈ Finset.range 4,
          (∫ θ in Work.Spaces.Iθ, (if 1 ≤ i then (Work.Spaces.dthU^[i] (gcf α) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)))
        ≤ ∑ _i ∈ Finset.range 4, K := Finset.sum_le_sum fun i hi => by
          by_cases h : 1 ≤ i
          · simp only [if_pos h]
            exact (hγ' i h (by rw [Finset.mem_range] at hi; omega)).2
          · simp only [if_neg h]
            rw [MeasureTheory.integral_zero]
            exact hK
      _ = 4 * K := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  linarith [hη.2, hsum_le]

/-- The radial factor of the majorant: the `D_z`-slots of `L₁₂(f)`. -/
private def Sz (f : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∑ q ∈ Finset.range 4,
    (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z) z 0) ^ 2 * (Work.Spaces.w z) ^ 2

private theorem Sz_nonneg (f : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ Sz f z :=
  Finset.sum_nonneg fun q _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- **The radial factor and its weighted mass**: the four `D_z`-slots of `L₁₂(f)` are integrable
on `Iz` and their total mass is at most `4·C₂·HkSq α 4 f`. -/
private theorem Sz_integrable {α : ℝ} (f : ℝ → ℝ → ℝ) {C₂ : ℝ}
    (h : ∀ q ≤ 4, MeasureTheory.IntegrableOn (fun z : ℝ =>
        (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z) z 0) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, (Work.Spaces.DzIter q
          (fun z _ => Work.Construction.L12 f z) z 0) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ C₂ * Work.Spaces.HkSq α 4 f) :
    MeasureTheory.IntegrableOn (Sz f) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, Sz f z) ≤ 4 * (C₂ * Work.Spaces.HkSq α 4 f) := by
  have hint : MeasureTheory.IntegrableOn (Sz f) Work.Spaces.Iz :=
    MeasureTheory.integrable_finset_sum (Finset.range 4)
      (fun q hq => (h q (by rw [Finset.mem_range] at hq; omega)).1)
  refine ⟨hint, ?_⟩
  have hval : (∫ z in Work.Spaces.Iz, Sz f z) = ∑ q ∈ Finset.range 4,
      (∫ z in Work.Spaces.Iz, (Work.Spaces.DzIter q
        (fun z _ => Work.Construction.L12 f z) z 0) ^ 2 * (Work.Spaces.w z) ^ 2) :=
    MeasureTheory.integral_finset_sum (Finset.range 4)
      (fun q hq => (h q (by rw [Finset.mem_range] at hq; omega)).1)
  rw [hval]
  calc (∑ q ∈ Finset.range 4, (∫ z in Work.Spaces.Iz, (Work.Spaces.DzIter q
        (fun z _ => Work.Construction.L12 f z) z 0) ^ 2 * (Work.Spaces.w z) ^ 2))
      ≤ ∑ _q ∈ Finset.range 4, (C₂ * Work.Spaces.HkSq α 4 f) :=
        Finset.sum_le_sum fun q hq =>
          (h q (by rw [Finset.mem_range] at hq; omega)).2
    _ = 4 * (C₂ * Work.Spaces.HkSq α 4 f) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

theorem Acoef_Mf_le : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.Construction.L12 f 0 = 0 →
    ContDiffOn ℝ 3 (Function.uncurry (fun z θ =>
      ((2 * z / (1 + z) ^ 2) * (Work.Spaces.Gam α θ / Work.Spaces.c α))
        * Work.Construction.L12 f z)) Work.FTS.EllipticEst.Q0 ∧
    Work.Spaces.HkMem α 3 (fun z θ => ((2 * z / (1 + z) ^ 2)
        * (Work.Spaces.Gam α θ / Work.Spaces.c α)) * Work.Construction.L12 f z) ∧
    Work.Spaces.HkSq α 3 (fun z θ => ((2 * z / (1 + z) ^ 2)
        * (Work.Spaces.Gam α θ / Work.Spaces.c α)) * Work.Construction.L12 f z)
      ≤ C * Work.Spaces.HkSq α 4 f := by
  obtain ⟨C₂, hC₂pos, hC₂⟩ := L12f_slot_le
  obtain ⟨K₂, hK₂pos, -, hK₂η, hK₂γ⟩ := GamJetBounds
  refine ⟨zmulConst 3 * (1 + 24000) ^ 2 * (5 * K₂) * (4 * C₂) + 1, ?_, ?_⟩
  · have h1 : 0 < zmulConst 3 * (1 + 24000) ^ 2 := by
      have := zmulConst_pos 3
      positivity
    have h2 : 0 < 5 * K₂ := by linarith
    have h3 : 0 < 4 * C₂ := by linarith
    positivity
  · intro α f hα hα1 hsm hmem hL120
    have hC₀pos : (0 : ℝ) < zmulConst 3 * (1 + 24000) ^ 2 := by
      have := zmulConst_pos 3
      positivity
    -- ### `L₁₂(f)` is `C³` on `(0,∞)`, hence the nonlocal summand is `C³` on the quadrant
    have hL3 : ContDiffOn ℝ 3 (Work.Construction.L12 f) (Set.Ioi (0 : ℝ)) :=
      (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk α 4 f hsm hmem
        (by norm_num)).1
    have hAcf3 : ContDiffOn ℝ 3 (Function.uncurry (Acf α f)) Work.FTS.EllipticEst.Q0 :=
      contDiffOn_three_Acf hL3
    -- ### the auxiliary estimates
    have hslot : ∀ q ≤ 4, MeasureTheory.IntegrableOn (fun z : ℝ =>
        (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z) z 0) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
        (∫ z in Work.Spaces.Iz, (Work.Spaces.DzIter q
            (fun z _ => Work.Construction.L12 f z) z 0) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ C₂ * Work.Spaces.HkSq α 4 f := fun q hq =>
      hC₂ α hα hα1 f hsm hmem hL120 q hq
    have hSz := Sz_integrable (α := α) f hslot
    have hMth := Mth_int_le α hK₂pos.le (hK₂η α hα hα1) (hK₂γ α hα hα1)
    -- ### the pointwise domination of the integrand
    have hstepA : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 3 (Acf α f) z θ
          ≤ zmulConst 3 * (1 + 24000) ^ 2
            * Work.Spaces.HkIntegrand α 3
                (fun z θ => gcf α θ * Work.Construction.L12 f z) z θ :=
      acf_integrand_le α f hsm hmem
    have hstepB : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 3
            (fun z θ => gcf α θ * Work.Construction.L12 f z) z θ ≤ Mth α θ * Sz f z := by
      intro z _ θ hθ
      simpa only [Mth, Sz] using
        (HkIntegrand_sep_le (α := α) (C := gcf α)
          (B := fun z => Work.Construction.L12 f z) (z := z) (θ := θ) hθ)
    have hpoint : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 3 (Acf α f) z θ
          ≤ (zmulConst 3 * (1 + 24000) ^ 2) * (Mth α θ * Sz f z) := by
      intro z hz θ hθ
      exact le_trans (hstepA z hz θ hθ)
        (mul_le_mul_of_nonneg_left (hstepB z hz θ hθ) hC₀pos.le)
    -- ### conjunct 2: `Acf α f ∈ ℋ³`
    have hMslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ => (zmulConst 3 * (1 + 24000) ^ 2) * (Mth α θ * Sz f z)) Work.Spaces.Iθ :=
      fun z _ => (hMth.1.mul_const (Sz f z)).const_mul (zmulConst 3 * (1 + 24000) ^ 2)
    have hMz : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        (zmulConst 3 * (1 + 24000) ^ 2) * (Mth α θ * Sz f z)) Work.Spaces.Iz := by
      have hval : (fun z => ∫ θ in Work.Spaces.Iθ,
            (zmulConst 3 * (1 + 24000) ^ 2) * (Mth α θ * Sz f z))
          = fun z => (zmulConst 3 * (1 + 24000) ^ 2 * (∫ θ in Work.Spaces.Iθ, Mth α θ))
              * Sz f z := by
        funext z
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const]
        ring
      rw [hval]
      exact hSz.1.const_mul (zmulConst 3 * (1 + 24000) ^ 2 * (∫ θ in Work.Spaces.Iθ, Mth α θ))
    have hconj2acf : Work.Spaces.HkMem α 3 (Acf α f) :=
      Work.FTS.LocData.HkMem_of_majorant α 3
        (Work.FTS.OpenPkg.continuousOn_HkIntegrand_of_contDiffOn α le_rfl hAcf3)
        hMslice hMz hpoint
    -- ### conjunct 3: the weighted bound
    have hinner : ∀ z ∈ Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 3 (Acf α f) z θ)
        ≤ (zmulConst 3 * (1 + 24000) ^ 2) * (Sz f z * (5 * K₂)) := by
      intro z hz
      have hii := MeasureTheory.integral_mono_of_nonneg
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (f := fun θ => Work.Spaces.HkIntegrand α 3 (Acf α f) z θ)
        (g := fun θ => (zmulConst 3 * (1 + 24000) ^ 2) * (Mth α θ * Sz f z))
        (Filter.Eventually.of_forall fun θ =>
          Work.Spaces.HkIntegrand_nonneg α 3 (Acf α f) z θ)
        (hMslice z hz)
        ((MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
          (Filter.Eventually.of_forall fun θ hθ => hpoint z hz θ hθ))
      have hvalθ : (∫ θ in Work.Spaces.Iθ,
            (zmulConst 3 * (1 + 24000) ^ 2) * (Mth α θ * Sz f z))
          = (zmulConst 3 * (1 + 24000) ^ 2)
              * ((∫ θ in Work.Spaces.Iθ, Mth α θ) * Sz f z) := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const]
      refine hii.trans ?_
      rw [hvalθ]
      refine mul_le_mul_of_nonneg_left ?_ hC₀pos.le
      calc (∫ θ in Work.Spaces.Iθ, Mth α θ) * Sz f z ≤ (5 * K₂) * Sz f z :=
            mul_le_mul_of_nonneg_right hMth.2 (Sz_nonneg f z)
        _ = Sz f z * (5 * K₂) := by ring
    have hdomInt : MeasureTheory.IntegrableOn (fun z : ℝ =>
        (zmulConst 3 * (1 + 24000) ^ 2) * (Sz f z * (5 * K₂))) Work.Spaces.Iz :=
      (hSz.1.mul_const (5 * K₂)).const_mul (zmulConst 3 * (1 + 24000) ^ 2)
    have houter := MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (f := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 3 (Acf α f) z θ)
      (g := fun z => (zmulConst 3 * (1 + 24000) ^ 2) * (Sz f z * (5 * K₂)))
      (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg_of_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 3 (Acf α f) z θ)))
      hdomInt
      ((MeasureTheory.ae_restrict_iff' measurableSet_Ici).mpr
        (Filter.Eventually.of_forall fun z hz => hinner z hz))
    have hfinal : Work.Spaces.HkSq α 3 (Acf α f)
        ≤ (zmulConst 3 * (1 + 24000) ^ 2 * (5 * K₂) * (4 * C₂)) * Work.Spaces.HkSq α 4 f := by
      have hvalz : (∫ z in Work.Spaces.Iz,
            (zmulConst 3 * (1 + 24000) ^ 2) * (Sz f z * (5 * K₂)))
          = (zmulConst 3 * (1 + 24000) ^ 2 * (5 * K₂))
              * (∫ z in Work.Spaces.Iz, Sz f z) := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const]
        ring
      calc Work.Spaces.HkSq α 3 (Acf α f)
          = ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 3 (Acf α f) z θ) := rfl
        _ ≤ ∫ z in Work.Spaces.Iz,
              (zmulConst 3 * (1 + 24000) ^ 2) * (Sz f z * (5 * K₂)) := houter
        _ = (zmulConst 3 * (1 + 24000) ^ 2 * (5 * K₂))
              * (∫ z in Work.Spaces.Iz, Sz f z) := hvalz
        _ ≤ (zmulConst 3 * (1 + 24000) ^ 2 * (5 * K₂)) * (4 * (C₂ * Work.Spaces.HkSq α 4 f)) :=
            mul_le_mul_of_nonneg_left hSz.2 (by positivity)
        _ = (zmulConst 3 * (1 + 24000) ^ 2 * (5 * K₂) * (4 * C₂))
              * Work.Spaces.HkSq α 4 f := by ring
    have hconj3 : Work.Spaces.HkSq α 3 (fun z θ => ((2 * z / (1 + z) ^ 2)
          * (Work.Spaces.Gam α θ / Work.Spaces.c α)) * Work.Construction.L12 f z)
        ≤ (zmulConst 3 * (1 + 24000) ^ 2 * (5 * K₂) * (4 * C₂) + 1)
            * Work.Spaces.HkSq α 4 f := by
      rw [Acf_eq_stmt α f]
      exact le_trans hfinal (mul_le_mul_of_nonneg_right (by linarith)
        (Work.Spaces.HkSq_nonneg α 4 f))
    refine ⟨?_, ?_, hconj3⟩
    · rw [Acf_eq_stmt α f]
      exact hAcf3
    · rw [Acf_eq_stmt α f]
      exact hconj2acf

end Work.FTS.StrongPersist.L3Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Aux.locOp_HkSq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L3Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-!
# `Work.FTS.StrongPersist.L3Aux.locOp_HkSq_le`

The local part `locOp f = -𝓛 f + Transport f` of the linearised operator `𝓛_Γ^T` is a
*first-order* differential operator with smooth bounded coefficients,

  `locOp f z θ = -f z θ - D_z f z θ + (2/(1+z))·f z θ + (3/(1+z))·D_θ f z θ`,

and the module proves that it preserves the class `SmoothOpen` and `ℋ³`, with a norm
estimate against `ℋ⁴`:

  `HkSq α 3 (locOp f) ≤ C · HkSq α 4 f`.

The pointwise skeleton is the `ℋ³`-integrand bound

  `HkIntegrand α 3 (locOp f) z θ ≤ C · HkIntegrand α 4 f z θ`

on the closed quadrant.  It is assembled from

* subadditivity of `HkIntegrand` on the open quadrant
  (`Work.FTS.EllipticEst.HkIntegrand_add_le_of_contDiffOn`);
* the shift estimate `HkIntegrand α 3 (D_z^b D_θ^a f) ≤ HkIntegrand α 4 f`
  (`Work.FTS.StrongPersist.L3Aux.HkIntegrand_mixed_shift`, for `a + b ≤ 1`);
* the radial-multiplier estimate
  `HkIntegrand α 3 (φ·g) ≤ C(1+K)² HkIntegrand α 3 g` for a `z`-only multiplier `φ` with
  `|Zop^b φ| ≤ K` (`Work.FTS.StrongPersist.L3Aux.HkIntegrand_zmul_le`), applied with
  `φ z = 3/(1+z)`, whose iterates are bounded by `100`
  (`Work.FTS.FinalClock.PhiZopBound`).

The membership `HkMem α 3 (locOp f)` and the integrated estimate follow from the pointwise
bound by the majorant criterion `Work.FTS.LocData.HkMem_of_majorant` and monotonicity of the
integral.
-/

/-! ## Elementary smoothness helpers -/

/-- `SmoothOpen` of a function of `z` alone which is `C^∞` on `(-1,∞)`. -/
private lemma smoothOpen_radial {φ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ Work.Stability.smoothOrder φ (Set.Ioi (-1))) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => φ z) := by
  rw [Work.FTS.EllipticEst.SmoothOpen]
  have hfst : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1)
      Work.FTS.EllipticEst.Q0 := contDiff_fst.contDiffOn
  exact hφ.comp hfst (fun p hp => by
    have hz : 0 < p.1 := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
    exact show (-1 : ℝ) < p.1 from by linarith)

/-- `SmoothOpen` is closed under addition. -/
private lemma smoothOpen_add' {g h : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hh : Work.FTS.EllipticEst.SmoothOpen h) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => g z θ + h z θ) := by
  rw [Work.FTS.EllipticEst.SmoothOpen] at hg hh ⊢
  have hfun : Function.uncurry (fun z θ => g z θ + h z θ)
      = fun p : ℝ × ℝ => Function.uncurry g p + Function.uncurry h p := by
    funext p; rfl
  rw [hfun]
  exact hg.add hh

/-- `SmoothOpen` is closed under multiplication. -/
private lemma smoothOpen_mul' {g h : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hh : Work.FTS.EllipticEst.SmoothOpen h) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => g z θ * h z θ) := by
  rw [Work.FTS.EllipticEst.SmoothOpen] at hg hh ⊢
  have hfun : Function.uncurry (fun z θ => g z θ * h z θ)
      = fun p : ℝ × ℝ => Function.uncurry g p * Function.uncurry h p := by
    funext p; rfl
  rw [hfun]
  exact hg.mul hh

/-- `SmoothOpen` is closed under multiplication by a constant. -/
private lemma smoothOpen_const_mul' (c : ℝ) {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * g z θ) := by
  rw [Work.FTS.EllipticEst.SmoothOpen] at hg ⊢
  have hfun : Function.uncurry (fun z θ => c * g z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry g p := by
    funext p; rfl
  rw [hfun]
  exact contDiffOn_const.mul hg

/-! ## Pointwise domination of different levels integrates -/

/-- The pointwise domination of the `ℋ^k`-integrand of `f` by a multiple of the
`ℋ^l`-integrand of `g` (`k ≠ l` allowed) integrates to the corresponding domination of the
squared norms, provided the dominating datum is honest (`HkMem α l g`). -/
private lemma HkSq_le_of_pointwise_levels (α : ℝ) (k l : ℕ) {f g : ℝ → ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hmg : Work.Spaces.HkMem α l g)
    (hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k f z θ ≤ C * Work.Spaces.HkIntegrand α l g z θ) :
    Work.Spaces.HkSq α k f ≤ C * Work.Spaces.HkSq α l g := by
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
        ≤ C * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α l g z θ := by
    intro z hz
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun θ => Work.Spaces.HkIntegrand α k f z θ)
      (g := fun θ => C * Work.Spaces.HkIntegrand α l g z θ)
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
      ((hmg.1 z hz).const_mul C)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hpt z hz θ hθ))
    rwa [MeasureTheory.integral_const_mul] at hmono
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  have houter := MeasureTheory.integral_mono_of_nonneg
    (μ := volume.restrict Work.Spaces.Iz)
    (f := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
    (g := fun z => C * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α l g z θ)
    (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α k f z θ)
    (hmg.2.const_mul C)
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hinner z hz)
  rw [MeasureTheory.integral_const_mul] at houter
  exact houter

/-! ## The estimate -/

theorem locOp_HkSq_le : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => -(Work.Coercivity.L f z θ) + Work.Coercivity.Transport f z θ) ∧
    Work.Spaces.HkMem α 3
      (fun z θ => -(Work.Coercivity.L f z θ) + Work.Coercivity.Transport f z θ) ∧
    Work.Spaces.HkSq α 3
      (fun z θ => -(Work.Coercivity.L f z θ) + Work.Coercivity.Transport f z θ)
      ≤ C * Work.Spaces.HkSq α 4 f := by
  obtain ⟨Cz, hCzpos, hCz⟩ := HkIntegrand_zmul_le 3
  refine ⟨4 * (2 + 2 * (Cz * 101 ^ 2)) + 1, by nlinarith [hCzpos], ?_⟩
  intro α f hα _hα1 hf hmem
  -- the multiplier `φ z = 3/(1+z)` and its iterate bound `K = 100`
  have hφsm : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => 3 / (1 + z))
      (Set.Ioi (-1)) :=
    contDiffOn_iff_forall_nat_le.mpr (fun m _ => Work.FTS.FinalClock.contDiffOn_phiThree m)
  have hφZop : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Spaces.Zop^[b] (fun z : ℝ => 3 / (1 + z)) z| ≤ 100 := fun b hb z hz =>
    Work.FTS.FinalClock.PhiZopBound b (by omega) z (le_of_lt hz)
  -- the four summands of `locOp`
  set A1 : ℝ → ℝ → ℝ := fun z θ => -f z θ with hA1
  set A2 : ℝ → ℝ → ℝ := fun z θ => -(Work.Spaces.Dz f z θ) with hA2
  set A3 : ℝ → ℝ → ℝ := fun z θ => (2 / 3) * ((fun z : ℝ => 3 / (1 + z)) z * f z θ)
    with hA3
  set A4 : ℝ → ℝ → ℝ := fun z θ => (fun z : ℝ => 3 / (1 + z)) z * (Work.Spaces.Dth f z θ)
    with hA4
  set A12 : ℝ → ℝ → ℝ := fun z θ => A1 z θ + A2 z θ with hA12
  set A34 : ℝ → ℝ → ℝ := fun z θ => A3 z θ + A4 z θ with hA34
  set E : ℝ → ℝ → ℝ := fun z θ => A12 z θ + A34 z θ with hE
  -- `locOp` is exactly `E`
  have hlocOp :
      (fun z θ => -(Work.Coercivity.L f z θ) + Work.Coercivity.Transport f z θ) = E := by
    rw [hE, hA12, hA34, hA1, hA2, hA3, hA4]
    funext z θ
    simp only [Work.Coercivity.L, Work.Coercivity.Transport]
    ring
  -- smoothness of the pieces
  have hA1sm : Work.FTS.EllipticEst.SmoothOpen A1 := by
    have h1 : A1 = fun z θ => (-1 : ℝ) * f z θ := by
      rw [hA1]; funext z θ; ring
    rw [h1]
    exact smoothOpen_const_mul' (-1) hf
  have hA2sm : Work.FTS.EllipticEst.SmoothOpen A2 := by
    have h2 : A2 = fun z θ => (-1 : ℝ) * Work.Spaces.Dz f z θ := by
      rw [hA2]; funext z θ; ring
    rw [h2]
    exact smoothOpen_const_mul' (-1) hf.Dz
  have hA3sm : Work.FTS.EllipticEst.SmoothOpen A3 := by
    rw [hA3]
    exact smoothOpen_const_mul' (2 / 3)
      (smoothOpen_mul' (smoothOpen_radial hφsm) hf)
  have hA4sm : Work.FTS.EllipticEst.SmoothOpen A4 := by
    rw [hA4]
    exact smoothOpen_mul' (smoothOpen_radial hφsm) hf.Dth
  have hA12sm : Work.FTS.EllipticEst.SmoothOpen A12 := by
    rw [hA12]; exact smoothOpen_add' hA1sm hA2sm
  have hA34sm : Work.FTS.EllipticEst.SmoothOpen A34 := by
    rw [hA34]; exact smoothOpen_add' hA3sm hA4sm
  have hEsm : Work.FTS.EllipticEst.SmoothOpen E := by
    rw [hE]; exact smoothOpen_add' hA12sm hA34sm
  -- the four piecewise bounds
  have hA1bd : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 3 A1 z θ ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
    intro z hz θ hθ
    have h1 : A1 = fun z θ => (-1 : ℝ) * f z θ := by
      rw [hA1]; funext z θ; ring
    have h2 : Work.Spaces.HkIntegrand α 3 f z θ ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
      simpa using Work.Spaces.HkIntegrand_mono α 3 f z θ
    rw [h1, Work.FTS.Galerkin.Hilbert.HkIntegrand_const_mul α 3 (-1) f z θ]
    have hneg : ((-1 : ℝ) ^ 2) = 1 := by norm_num
    rw [hneg, one_mul]
    exact h2
  have hA2bd : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 3 A2 z θ ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
    intro z hz θ hθ
    have h1 : A2 = fun z θ => (-1 : ℝ) * Work.Spaces.Dz f z θ := by
      rw [hA2]; funext z θ; ring
    rw [h1, Work.FTS.Galerkin.Hilbert.HkIntegrand_const_mul α 3 (-1)
      (Work.Spaces.Dz f) z θ]
    have hneg : ((-1 : ℝ) ^ 2) = 1 := by norm_num
    rw [hneg, one_mul]
    have h2 : Work.Spaces.HkIntegrand α 3 (Work.Spaces.mixed 1 0 f) z θ
        ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
      simpa using HkIntegrand_mixed_shift α hα 3 0 1 hf z hz θ hθ
    simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_succ,
      Work.Spaces.DzIter_zero] using h2
  have hA3bd : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 3 A3 z θ
        ≤ Cz * 101 ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
    intro z hz θ hθ
    have hpt := (hCz α (fun z : ℝ => 3 / (1 + z)) 100 (by norm_num) hφZop hφsm f hf).1
      z hz θ hθ
    have hmono : Work.Spaces.HkIntegrand α 3 f z θ ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
      simpa using Work.Spaces.HkIntegrand_mono α 3 f z θ
    have hpt' : Work.Spaces.HkIntegrand α 3
          (fun z θ => (fun z : ℝ => 3 / (1 + z)) z * f z θ) z θ
        ≤ Cz * 101 ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
      calc Work.Spaces.HkIntegrand α 3
            (fun z θ => (fun z : ℝ => 3 / (1 + z)) z * f z θ) z θ
          ≤ Cz * (1 + 100) ^ 2 * Work.Spaces.HkIntegrand α 3 f z θ := hpt
        _ ≤ Cz * (1 + 100) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ :=
            mul_le_mul_of_nonneg_left hmono (by nlinarith [hCzpos])
        _ = Cz * 101 ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by norm_num
    have h3 : A3 = fun z θ => (2 / 3) *
        ((fun z : ℝ => 3 / (1 + z)) z * f z θ) := hA3
    have hkey := Work.FTS.Galerkin.Hilbert.HkIntegrand_const_mul α 3 (2 / 3)
      (fun z θ => (fun z : ℝ => 3 / (1 + z)) z * f z θ) z θ
    have hnn : 0 ≤ Cz * 101 ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ :=
      mul_nonneg (mul_nonneg hCzpos.le (by norm_num))
        (Work.Spaces.HkIntegrand_nonneg α 4 f z θ)
    have h23 : ((2 : ℝ) / 3) ^ 2 ≤ 1 := by norm_num
    calc Work.Spaces.HkIntegrand α 3 A3 z θ
        = ((2 : ℝ) / 3) ^ 2 * Work.Spaces.HkIntegrand α 3
            (fun z θ => (fun z : ℝ => 3 / (1 + z)) z * f z θ) z θ := by
          rw [h3, hkey]
      _ ≤ 1 * (Cz * 101 ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ) := by
          refine mul_le_mul h23 hpt' ?_ (by norm_num)
          exact Work.Spaces.HkIntegrand_nonneg α 3
            (fun z θ => (fun z : ℝ => 3 / (1 + z)) z * f z θ) z θ
      _ = Cz * 101 ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by ring
  have hA4bd : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 3 A4 z θ
        ≤ Cz * 101 ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
    intro z hz θ hθ
    have hpt := (hCz α (fun z : ℝ => 3 / (1 + z)) 100 (by norm_num) hφZop hφsm
      (Work.Spaces.Dth f) hf.Dth).1 z hz θ hθ
    have hD : Work.Spaces.HkIntegrand α 3 (Work.Spaces.Dth f) z θ
        ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
      have h := HkIntegrand_mixed_shift α hα 3 1 0 hf z hz θ hθ
      simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ,
        Work.Spaces.DthIter_zero] using h
    have h4 : A4 = fun z θ => (fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth f z θ := hA4
    rw [h4]
    calc Work.Spaces.HkIntegrand α 3
          (fun z θ => (fun z : ℝ => 3 / (1 + z)) z * Work.Spaces.Dth f z θ) z θ
        ≤ Cz * (1 + 100) ^ 2 * Work.Spaces.HkIntegrand α 3 (Work.Spaces.Dth f) z θ := hpt
      _ ≤ Cz * (1 + 100) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ :=
          mul_le_mul_of_nonneg_left hD (by nlinarith [hCzpos])
      _ = Cz * 101 ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by norm_num
  -- the pointwise bound on the closed quadrant
  have hptE : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 3 E z θ
        ≤ (4 * (2 + 2 * (Cz * 101 ^ 2)) + 1) * Work.Spaces.HkIntegrand α 4 f z θ := by
    intro z hz θ hθ
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hz0
    · rw [← hz0, hE, hA12, hA34, hA1, hA2, hA3, hA4]
      rw [Work.FTS.LocData.HkIntegrand_zero_fst, Work.FTS.LocData.HkIntegrand_zero_fst]
      simp
    · by_cases hs : Real.sin (2 * θ) = 0
      · rw [hE, hA12, hA34, hA1, hA2, hA3, hA4,
          Work.FTS.EllipticEst.HkIntegrand_eq_zero_of_sin_eq_zero' α 3 _ hα hs,
          Work.FTS.EllipticEst.HkIntegrand_eq_zero_of_sin_eq_zero' α 4 f hα hs]
        rw [mul_zero]
      · have hθ0 : 0 < θ := by
          rcases eq_or_lt_of_le hθ.1 with h | h
          · exact absurd (by rw [← h]; simp) hs
          · exact h
        have hθ1 : θ < π / 2 := by
          rcases lt_or_eq_of_le hθ.2 with h | h
          · exact h
          · exact absurd (by rw [h, show 2 * (π / 2) = π by ring, Real.sin_pi]) hs
        have h12 := Work.FTS.EllipticEst.HkIntegrand_add_le_of_contDiffOn α 3 hA1sm hA2sm
          z hz θ hθ
        have h34 := Work.FTS.EllipticEst.HkIntegrand_add_le_of_contDiffOn α 3 hA3sm hA4sm
          z hz θ hθ
        have hTop := Work.FTS.EllipticEst.HkIntegrand_add_le_of_contDiffOn α 3 hA12sm hA34sm
          z hz θ hθ
        have h12' : Work.Spaces.HkIntegrand α 3 A12 z θ
            ≤ 2 * Work.Spaces.HkIntegrand α 3 A1 z θ
              + 2 * Work.Spaces.HkIntegrand α 3 A2 z θ := by
          rw [hA12]; exact h12
        have h34' : Work.Spaces.HkIntegrand α 3 A34 z θ
            ≤ 2 * Work.Spaces.HkIntegrand α 3 A3 z θ
              + 2 * Work.Spaces.HkIntegrand α 3 A4 z θ := by
          rw [hA34]; exact h34
        have hTop' : Work.Spaces.HkIntegrand α 3 E z θ
            ≤ 2 * Work.Spaces.HkIntegrand α 3 A12 z θ
              + 2 * Work.Spaces.HkIntegrand α 3 A34 z θ := by
          rw [hE]; exact hTop
        have e1 := hA1bd z hz θ hθ
        have e2 := hA2bd z hz θ hθ
        have e3 := hA3bd z hz θ hθ
        have e4 := hA4bd z hz θ hθ
        have hH4 : 0 ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
          Work.Spaces.HkIntegrand_nonneg α 4 f z θ
        have hC101 : (0 : ℝ) ≤ Cz * 101 ^ 2 :=
          mul_nonneg hCzpos.le (by norm_num)
        linarith [hTop', h12', h34', e1, e2, e3, e4, hH4, hC101,
          mul_nonneg hC101 hH4, mul_nonneg hC101 (mul_nonneg hC101 hH4)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hlocOp]; exact hEsm
  · rw [hlocOp]
    refine Work.FTS.LocData.HkMem_of_majorant α 3 (f := E)
      (M := fun z θ => (4 * (2 + 2 * (Cz * 101 ^ 2)) + 1) *
        Work.Spaces.HkIntegrand α 4 f z θ)
      ?_ ?_ ?_ hptE
    · exact hEsm.continuousOn_HkIntegrand α 3
    · intro z hz
      exact (hmem.1 z hz).const_mul _
    · have h : (fun z => ∫ θ in Work.Spaces.Iθ,
            (4 * (2 + 2 * (Cz * 101 ^ 2)) + 1) * Work.Spaces.HkIntegrand α 4 f z θ)
          = fun z => (4 * (2 + 2 * (Cz * 101 ^ 2)) + 1) *
              ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ := by
        funext z
        rw [MeasureTheory.integral_const_mul]
      rw [h]
      exact hmem.2.const_mul _
  · rw [hlocOp]
    exact HkSq_le_of_pointwise_levels α 3 4 (by nlinarith [hCzpos]) hmem hptE

end Work.FTS.StrongPersist.L3Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.Hon.hardyG_ae_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongPersist.N6Trans.Hon

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem hardyG_ae_open {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hsm : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    (hdec : Work.Spaces.DecayAll 4 g) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ∀ z ∈ Set.Ioi (0 : ℝ),
        (Work.Spaces.mixed 1 1 g z θ) ^ 2
          ≤ ∫ s in Work.Spaces.Iz,
              (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2 := by
  obtain ⟨_hswap, _hmarg, hslice⟩ :=
    Work.FTS.TransportS.SupDzAux.sda_HkSqSwap_open α g hsm hmem
  have hIoo : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo 0 (π / 2) := by
    rw [Work.FTS.TransportS.SlotT2.supOpen_restrict_Iθ]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo 0 (π / 2) ∧
        MeasureTheory.IntegrableOn
          (fun s => (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2)
          Work.Spaces.Iz := by
    filter_upwards [hIoo, hslice] with θ hθ hI
    refine ⟨hθ, ?_⟩
    refine hI.mono' ?_ ?_
    · have hcont : ContinuousOn
          (fun s : ℝ => (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2)
          (Set.Ioi 0) := by
        have h1 : ContinuousOn (fun s : ℝ => (Work.Spaces.w s) ^ 2) (Set.Ioi 0) := by
          simp only [Work.Spaces.w]
          exact (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
            (continuousOn_id.pow 2) (fun s hs => pow_ne_zero 2 (ne_of_gt hs))).pow 2
        exact h1.mul (((hsm.mixed 2 1).curry_z hθ).continuousOn.pow 2 |>.mono
          (fun s hs => by simp only [Set.mem_Ioi] at hs ⊢; linarith))
      rw [Work.FTS.TransportS.SlotT2.supOpen_restrict_Iz]
      exact hcont.aestronglyMeasurable measurableSet_Ioi
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun s hs => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      rcases eq_or_lt_of_le (show (0 : ℝ) ≤ s from hs) with h0 | hspos
      · subst h0
        have hzero : (Work.Spaces.w 0) ^ 2 * (Work.Spaces.mixed 2 1 g 0 θ) ^ 2 = 0 := by
          rw [show Work.Spaces.w 0 = 0 from by simp [Work.Spaces.w]]
          ring
        rw [hzero]
        exact Work.Spaces.HkIntegrand_nonneg α 4 g 0 θ
      · have hsin : 0 < Real.sin (2 * θ) :=
          Real.sin_pos_of_pos_of_lt_pi (by show (0 : ℝ) < 2 * θ; linarith [hθ.1])
            (by show 2 * θ < Real.pi; linarith [hθ.2, Real.pi_pos])
        have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
        have hslot := Work.FTS.TransportS.SlotT2.canonW_mul_mixed_le α g
          (Work.Spaces.gam_pos hα) le_rfl hspos hθI 2 1 le_rfl (by norm_num)
        have hcanon : Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) s θ
            = (Work.Spaces.w s) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
          rw [Work.FTS.TransportS.SlotT2.canonW_gam_eq α s θ hθI,
            show Work.Spaces.Wt α s θ = Work.FTS.H2.Wm α s θ from rfl,
            Work.FTS.H2.hbi_Wm_sq α s θ (le_of_lt hsin)]
        have hone : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
          Work.FTS.TransportS.T2Sup.delicate_one_le_rpow_neg hsin (Real.sin_le_one _)
            (le_of_lt (Work.Spaces.gam_pos hα))
        calc (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2
            ≤ (Work.Spaces.w s) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed 2 1 g s θ) ^ 2 := by
              have h0 : 0 ≤ (Work.Spaces.mixed 2 1 g s θ) ^ 2 := sq_nonneg _
              have h1 : (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2
                  ≤ (Work.Spaces.w s) ^ 2
                    * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                      * (Work.Spaces.mixed 2 1 g s θ) ^ 2) :=
                mul_le_mul_of_nonneg_left (le_mul_of_one_le_left h0 hone) (sq_nonneg _)
              linarith [h1]
          _ = Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) s θ
                * (Work.Spaces.mixed 2 1 g s θ) ^ 2 := by
              rw [hcanon]
          _ ≤ Work.Spaces.HkIntegrand α 4 g s θ := hslot
  filter_upwards [hae] with θ hθ z hz
  obtain ⟨hθIoo, hIint⟩ := hθ
  have hslicecont : ContDiffOn ℝ 1 (fun s : ℝ => Work.Spaces.mixed 1 1 g s θ) (Set.Ioi 0) :=
    ((hsm.mixed 1 1).curry_z hθIoo).of_le
        (by simp [Work.Stability.smoothOrder]) |>.mono
      (fun x hx => by simp only [Set.mem_Ioi] at hx ⊢; linarith)
  have hdec' : Tendsto (fun s : ℝ => Work.Spaces.mixed 1 1 g s θ) atTop (𝓝 0) :=
    hdec.2 1 1 (by norm_num) θ ⟨le_of_lt hθIoo.1, le_of_lt hθIoo.2⟩
  have hint : MeasureTheory.IntegrableOn
      (fun s => (s * deriv (fun s' : ℝ => Work.Spaces.mixed 1 1 g s' θ) s) ^ 2
        * (Work.Spaces.w s) ^ 2) Work.Spaces.Iz := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
      Work.Spaces.Dz, Work.Spaces.pz, mul_comm, mul_left_comm, mul_assoc] using hIint
  have h := Work.FTS.H2.hardyZ_open hslicecont hdec' hint z hz
  simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
    Work.Spaces.Dz, Work.Spaces.pz, mul_comm, mul_left_comm, mul_assoc] using h

end Work.FTS.StrongPersist.N6Trans.Hon
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.Hon.psiMarginal_le_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongPersist.N6Trans.Hon

/-- The `θ`-marginal of the `(2,1)`-slot of `g`, in the *open* (weak-hypothesis) setting:
`∫_θ σ^{-γ} ∫_s w²(D_z²D_θ g)² ≤ |g|_{ℋ⁴}²`, from only `SmoothOpen g` and `HkMem α 4 g`.

This is the twin of `Work.FTS.TransportS.T2Sup.delicate_psiMarginal_le`, whose hypothesis
bundle `T2SG α g` (= `RegQ α 4 g ∧ HkMem α 5 g ∧ DecayAll 4 g`) enters its proof only through
`SmoothOpen g` and `HkMem α 4 g`.  Every slot lemma invoked below is stated and proved for
exactly those two hypotheses (`SmoothOpen g`, `HkMem α 4 g`) in
`Submission/Work/FTS/TransportS/SlotT2/Basic.lean`. -/
theorem psiMarginal_le_open {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hsm : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g) :
    MeasureTheory.IntegrableOn
        (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * ∫ s in Work.Spaces.Iz, (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2)
        Work.Spaces.Iθ
      ∧ (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * ∫ s in Work.Spaces.Iz, (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2)
        ≤ Work.Spaces.HkSq α 4 g := by
  have hγpos : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα
  set G : ℝ → ℝ → ℝ := fun s θ =>
    Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) s θ * (Work.Spaces.mixed 2 1 g s θ) ^ 2
    with hGdef
  have haesm : MeasureTheory.AEStronglyMeasurable (Function.uncurry G)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [hGdef]
    exact Work.FTS.TransportS.SlotT2.mslot_joint_aesm hsm 2 1
  have hslice : ∀ᵐ s ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => G s θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun s hs => by
      rw [hGdef]
      exact Work.FTS.TransportS.SlotT2.mslot_slice_integrable hγpos le_rfl hsm hmem 2 1
        le_rfl (by norm_num) hs)
  have hmarg : MeasureTheory.Integrable
      (fun s => ∫ θ, G s θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    rw [hGdef]
    exact Work.FTS.TransportS.SlotT2.mslot_marginal_integrable hγpos le_rfl hsm hmem 2 1
      le_rfl (by norm_num)
  have hnorm : (fun s => ∫ θ, ‖G s θ‖ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      = fun s => ∫ θ, G s θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    funext s
    refine MeasureTheory.integral_congr_ae ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    exact Real.norm_of_nonneg (mul_nonneg
      (Work.FTS.TransportS.SlotT2.canonW_nonneg (q := Work.Spaces.gam α)
        (z := s) (θ := θ) hθ) (sq_nonneg _))
  have hjoint : MeasureTheory.Integrable (Function.uncurry G)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (MeasureTheory.integrable_prod_iff haesm).mpr
      ⟨hslice, by simpa only [Function.uncurry, hnorm] using hmarg⟩
  have hmargθ : MeasureTheory.Integrable
      (fun θ => ∫ s, G s θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.Integrable.integral_prod_right hjoint
  have hswap := MeasureTheory.integral_integral_swap
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ) hjoint
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * ∫ s in Work.Spaces.Iz, (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2
        = ∫ s, G s θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    intro θ hθ
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
    have hcanon : Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) s θ
        = (Work.Spaces.w s) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      rw [Work.FTS.TransportS.SlotT2.canonW_gam_eq α s θ hθ,
        show Work.Spaces.Wt α s θ = Work.FTS.H2.Wm α s θ from rfl,
        Work.FTS.H2.hbi_Wm_sq α s θ (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ)]
    rw [hGdef]
    simp only
    rw [hcanon]
    ring
  constructor
  · exact MeasureTheory.IntegrableOn.congr_fun hmargθ (fun θ hθ => (hpt θ hθ).symm)
      measurableSet_Icc
  · have h1 : (∫ θ in Work.Spaces.Iθ,
          (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * ∫ s in Work.Spaces.Iz, (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2)
        = ∫ θ in Work.Spaces.Iθ,
            (∫ s, G s θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => hpt θ hθ)
    rw [h1]
    rw [← hswap]
    have hslot := Work.FTS.TransportS.SlotT2.canonW_mixed_iterated_le (α := α)
      (q := Work.Spaces.gam α) hγpos le_rfl hmem 2 1 le_rfl (by norm_num)
    simpa only [hGdef] using hslot

end Work.FTS.StrongPersist.N6Trans.Hon
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.Hon.qFun_le_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `qFun_le_open`: the honest `(3,1)`-slot energy bound

The frozen sibling `Work.FTS.TransportS.T2Sup.delicate_qFun_le` proves this statement for the
*rich* bundle `T2SG α g` (which carries `SmoothQuad`, `HkMem α 5 g`, decay and the boundary
traces).  Here the same conclusion is obtained from the **honest** bundle
`SmoothOpen g ∧ HkMem α 4 g` alone: the only inputs actually used are

* `Work.FTS.TransportS.SlotT2.mslot_slice_integrable` — `θ`-slice integrability of
  `w²σ^{-γ}(mixed 3 1 g)²` (from `SmoothOpen`, `HkMem α 4`);
* `Work.FTS.TransportS.SlotT2.mslot_marginal_integrable` — the same for the `z`-marginal of
  `w²σ^{-γ}(mixed 3 1 g)²`;
* `Work.FTS.TransportS.SlotT2.canonW_mixed_iterated_le` — the iterated bound by `HkSq α 4 g`;
* `Work.FTS.TransportS.T2Sup.delicate_aesm_weight_mul` — a.e. strong measurability of
  `θ ↦ σ^{-γ}v(θ)` for `v` continuous on the open interval;
* the `rpow` identity `Wt α z θ ^ 2 = w z ^ 2 · sin(2θ)^{-γ}` (`hbi_Wm_sq`), which upgrades
  `w²σ^{-γ}` to the canonical slot weight `canonW (gam α)`.
-/

open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.Hon

set_option maxHeartbeats 1600000

theorem qFun_le_open {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hsm : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g) :
    (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
        (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed 3 1 g z θ) ^ 2) Work.Spaces.Iθ)
      ∧ MeasureTheory.IntegrableOn
          (fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed 3 1 g z θ) ^ 2)
          Work.Spaces.Iz
      ∧ (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed 3 1 g z θ) ^ 2)
        ≤ Work.Spaces.HkSq α 4 g := by
  have hγpos : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα
  -- the canonical slot weight equals `w z ^ 2 · sin(2θ)^{-γ}` on `Iθ`
  have hcanon : ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ →
      Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
        = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    intro z θ hθ
    rw [Work.FTS.TransportS.SlotT2.canonW_gam_eq α z θ hθ,
      show Work.Spaces.Wt α z θ = Work.FTS.H2.Wm α z θ from rfl,
      Work.FTS.H2.hbi_Wm_sq α z θ (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ)]
  refine ⟨?_, ?_, ?_⟩
  · -- `θ`-slice integrability
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · -- at `z = 0` the `D_z`-flow kills the integrand
      subst hz0
      have hzero : (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed 3 1 g 0 θ) ^ 2) = fun _ : ℝ => (0 : ℝ) := by
        funext θ
        have hm : Work.Spaces.mixed 3 1 g 0 θ = 0 := by
          show (0 : ℝ) * Work.Spaces.pz (Work.Spaces.DzIter 2 (Work.Spaces.DthIter 1 g)) 0 θ = 0
          ring
        rw [hm]
        simp
      rw [hzero]
      exact integrableOn_zero
    · have hcw := Work.FTS.TransportS.SlotT2.mslot_slice_integrable (α := α)
        (q := Work.Spaces.gam α) hγpos le_rfl hsm hmem 3 1 le_rfl (by norm_num) hz
      refine hcw.mono' ?_ ?_
      · exact Work.FTS.TransportS.T2Sup.delicate_aesm_weight_mul
          (((hsm.mixed 3 1).curry_θ (z := z) hzpos).continuousOn.pow 2)
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
        have hw1 : 1 ≤ (Work.Spaces.w z) ^ 2 :=
          one_le_pow₀ (Work.FTS.TransportS.one_le_w hzpos)
        have hσnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
          Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _
        have h0 : 0 ≤ (Work.Spaces.mixed 3 1 g z θ) ^ 2 := sq_nonneg _
        rw [Real.norm_of_nonneg (mul_nonneg hσnn h0), hcanon z θ hθ]
        have h1 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 3 1 g z θ) ^ 2
            ≤ (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed 3 1 g z θ) ^ 2) :=
          le_mul_of_one_le_left (mul_nonneg hσnn h0) hw1
        linarith [h1]
  · -- `z`-marginal integrability
    have hmarg := Work.FTS.TransportS.SlotT2.mslot_marginal_integrable (α := α)
      (q := Work.Spaces.gam α) hγpos le_rfl hsm hmem 3 1 le_rfl (by norm_num)
    refine MeasureTheory.IntegrableOn.congr_fun hmarg (fun z _ => ?_) measurableSet_Ici
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    rw [hcanon z θ hθ]
    ring
  · -- the iterated bound
    have hEq : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * ∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed 3 1 g z θ) ^ 2)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
              * (Work.Spaces.mixed 3 1 g z θ) ^ 2 := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      rw [hcanon z θ hθ]
      ring
    rw [hEq]
    exact Work.FTS.TransportS.SlotT2.canonW_mixed_iterated_le (α := α)
      (q := Work.Spaces.gam α) hγpos le_rfl hmem 3 1 le_rfl (by norm_num)

end Work.FTS.StrongPersist.N6Trans.Hon
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.excSlotTerm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.T1SixAux

open Work.Spaces
open Work.FTS.TransportS.SlotT2 (canonW canonW_gam_eq)

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-! ## The `L²`-membership of a weighted level-six mixed slot -/


/-! ## The arithmetic of the `α^{-1/2}` rate -/


/-! ## The requested term -/


end Work.FTS.StrongPersist.N6Trans.T1SixAux
end
end
-- ===== merged: Submission.Work.FTS.TransportS.ClauseBridge =====
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


/-- The `25` leaf terms of `leafSum` are each at most `3R`, hence the sum is at most `75R`. -/
private theorem leafSum_le (α : ℝ) (u v : Fn) (R : ℝ) (hR : 0 ≤ R)
    (hterm : ∀ a ∈ Finset.range 5, ∀ b ∈ Finset.range 5,
      (if a + b ≤ 4 then
          |slotPairing leafEta a b u v| + |slotPairing leafOne a b u v|
            + (if 1 ≤ a then |slotPairing (leafGam α) a b u v| else 0)
        else 0) ≤ 3 * R) :
    leafSum α u v ≤ 75 * R := by
  unfold leafSum
  refine le_trans (Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb =>
    hterm a ha b hb) ?_
  have : (∑ _a ∈ Finset.range 5, ∑ _b ∈ Finset.range 5, (3 * R)) = 75 * R := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [this]






end Work.FTS.TransportS
end
end
-- ===== merged: Submission.Work.FTS.TransportS.T2S_final =====
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


end Work.FTS.TransportS
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.Fatou.HkMem_fatou_z =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false

/-! Copy of `HkMem_fatou` with the angular-slice hypothesis weakened from `≤ C` to the
`z`-local bound `≤ C * (1 + 1/z)` (the shape of `RulingELF.PkgMemSqH`).  `hTheta` is used only to
get finiteness of the angular lintegral of the limit, for which any real bound works. -/

theorem HkMem_fatou_z {α : ℝ} {k : ℕ} {C : ℝ} {un : ℕ → ℝ → ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hMem : ∀ n, Work.Spaces.HkMem α k (un n))
    (hSq : ∀ n, Work.Spaces.HkSq α k (un n) ≤ C)
    (hTheta : ∀ n, ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (un n) z θ) ≤ C * (1 + 1 / z))
    (hmeas : AEMeasurable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k u p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hconv : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (un n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i u z θ))) :
    Work.Spaces.HkMem α k u ∧ Work.Spaces.HkSq α k u ≤ C := by
  classical
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  -- the `HkSq`-half is exactly `HkSq_le_of_JConv`
  have hsq : Work.Spaces.HkSq α k u ≤ C :=
    HkSq_le_of_JConv (α := α) (k := k) (Ψn := un) (Ψ := u) (B := C) hMem hSq
      (fun j i hji z θ hq => hconv j i hji z θ hq)
  refine ⟨?_, hsq⟩
  -- (i) a.e. convergence in `θ`, for every fixed `z ∈ Iz`
  have hconv_ae : ∀ z ∈ Work.Spaces.Iz,
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        Filter.Tendsto (fun n => Work.Spaces.HkIntegrand α k (un n) z θ) Filter.atTop
          (nhds (Work.Spaces.HkIntegrand α k u z θ)) :=
    fun z hz => HkMem_fatou_ae_tendsto (α := α) (k := k) hconv hz
  -- (ii) the angular slices of the limit integrand are a.e. strongly measurable
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      AEMeasurable (fun θ => Work.Spaces.HkIntegrand α k u z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    have hlim : AEMeasurable
        (fun θ => Filter.liminf
          (fun n => Work.Spaces.HkIntegrand α k (un n) z θ) Filter.atTop)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      AEMeasurable.liminf (fun n => ((hMem n).1 z hz).aestronglyMeasurable.aemeasurable)
    refine hlim.congr ?_
    filter_upwards [hconv_ae z hz] with θ hθ
    exact hθ.liminf_eq
  -- (iii) Fatou in `θ`, for each fixed `z`
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k u z θ)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        ≤ Filter.liminf (fun n => ∫⁻ θ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k (un n) z θ)
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) Filter.atTop := by
    intro z hz
    have hfat := MeasureTheory.lintegral_liminf_le'
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ) (u := Filter.atTop)
      (f := fun n θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k (un n) z θ))
      (fun n => ((hMem n).1 z hz).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    have hEq : (fun θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k u z θ))
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ => Filter.liminf
          (fun n => ENNReal.ofReal (Work.Spaces.HkIntegrand α k (un n) z θ))
            Filter.atTop) := by
      filter_upwards [hconv_ae z hz] with θ hθ
      exact ((ENNReal.continuous_ofReal.tendsto
        (Work.Spaces.HkIntegrand α k u z θ)).comp hθ).liminf_eq.symm
    rw [MeasureTheory.lintegral_congr_ae hEq]
    exact hfat
  -- (iv) the resulting real inequality for each fixed `z`
  have hGle : ∀ z ∈ Work.Spaces.Iz,
      ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k u z θ)
        ≤ Filter.liminf (fun n => ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (un n) z θ))
              Filter.atTop := by
    intro z hz
    have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k u z θ)
        = (∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k u z θ)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)).toReal :=
      MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k u z θ)
        (hslice z hz).aestronglyMeasurable
    calc ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k u z θ)
        = ENNReal.ofReal ((∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k u z θ)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)).toReal) := by rw [h1]
      _ ≤ (∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k u z θ)
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := ENNReal.ofReal_toReal_le
      _ ≤ Filter.liminf (fun n => ∫⁻ θ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k (un n) z θ)
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) Filter.atTop := hinner z hz
      _ = Filter.liminf (fun n => ENNReal.ofReal
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (un n) z θ)) Filter.atTop := by
          refine Filter.liminf_congr (Filter.Eventually.of_forall fun n => ?_)
          exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal ((hMem n).1 z hz)
            (Filter.Eventually.of_forall fun θ =>
              Work.Spaces.HkIntegrand_nonneg α k (un n) z θ)).symm
  -- (v) the uniform bound on the angular lintegrals: finiteness of every slice
  have hlin_theta : ∀ z ∈ Work.Spaces.Iz,
      (∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k u z θ)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        ≤ ENNReal.ofReal (C * (1 + 1 / z)) := by
    intro z hz
    refine (hinner z hz).trans ?_
    rw [Filter.liminf_eq_iSup_iInf_of_nat]
    refine iSup_le fun n => ?_
    calc (⨅ i, ⨅ (_ : i ≥ n), (∫⁻ θ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k (un i) z θ)
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)))
        ≤ (⨅ (_ : n ≥ n), (∫⁻ θ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k (un n) z θ)
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))) := iInf_le _ n
      _ ≤ (∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k (un n) z θ)
              ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)) := iInf_le _ le_rfl
      _ = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (un n) z θ) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal ((hMem n).1 z hz)
            (Filter.Eventually.of_forall fun θ =>
              Work.Spaces.HkIntegrand_nonneg α k (un n) z θ)).symm
      _ ≤ ENNReal.ofReal (C * (1 + 1 / z)) := ENNReal.ofReal_le_ofReal (hTheta n z hz)
  -- (vi) hence every angular slice of the limit integrand is integrable
  have hslice_int : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k u z θ) Work.Spaces.Iθ := by
    intro z hz
    refine ⟨(hslice z hz).aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k u z θ)]
    exact lt_of_le_of_lt (hlin_theta z hz) ENNReal.ofReal_lt_top
  -- (vii) the `z`-function `z ↦ ∫⁻_θ ofReal (integrand)` is a.e. measurable, by Fubini
  have hmeas_lin : AEMeasurable
      (fun z => ∫⁻ θ, ENNReal.ofReal (Work.Spaces.HkIntegrand α k u z θ)
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    AEMeasurable.lintegral_prod_right
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun z θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k u z θ))
      hmeas.ennreal_ofReal
  -- (viii) hence so is the real `z`-function `z ↦ ∫_θ (integrand)`
  have hzmeas : AEMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k u z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine hmeas_lin.ennreal_toReal.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hIz] with z hz
    exact (MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k u z θ)
      (hslice z hz).aestronglyMeasurable).symm
  -- (ix) Fatou in `z`
  have hchain : (∫⁻ z, ENNReal.ofReal
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k u z θ)
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) ≤ ENNReal.ofReal C := by
    have hFatouZ := MeasureTheory.lintegral_liminf_le'
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz) (u := Filter.atTop)
      (f := fun n z => ENNReal.ofReal
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (un n) z θ))
      (fun n => ((hMem n).2).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    refine le_trans (MeasureTheory.lintegral_mono_ae ?_) (le_trans hFatouZ ?_)
    · filter_upwards [MeasureTheory.ae_restrict_mem hIz] with z hz
      exact hGle z hz
    · rw [Filter.liminf_eq_iSup_iInf_of_nat]
      refine iSup_le fun n => ?_
      calc (⨅ i, ⨅ (_ : i ≥ n), (∫⁻ z, ENNReal.ofReal
              (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (un i) z θ)
                ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)))
          ≤ (∫⁻ z, ENNReal.ofReal
              (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (un n) z θ)
                ∂(MeasureTheory.volume.restrict Work.Spaces.Iz)) :=
            le_trans (iInf_le _ n) (iInf_le _ le_rfl)
        _ = ENNReal.ofReal (Work.Spaces.HkSq α k (un n)) :=
            (MeasureTheory.ofReal_integral_eq_lintegral_ofReal ((hMem n).2)
              (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg
                (fun θ => Work.Spaces.HkIntegrand_nonneg α k (un n) z θ))).symm
        _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (hSq n)
  -- (x) hence the `z`-function is integrable, which is the second half of `HkMem`
  have hzint : IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k u z θ)
      Work.Spaces.Iz := by
    refine ⟨hzmeas.aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg
        (fun θ => Work.Spaces.HkIntegrand_nonneg α k u z θ))]
    exact lt_of_le_of_lt hchain ENNReal.ofReal_lt_top
  exact ⟨hslice_int, hzint⟩

end Work.FTS_EllLimOK
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.Fstar_ode_of_bslOp_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## The box calculus at a fixed radial point -/

/-- The box calculus of `Work.FTS_EllLimOK.boxReg_facts`, transported to the box
`[z/2, 2z] × [0,π/2]` around a fixed `z > 0`: the slices of `δ` and of `∂_zδ` are
differentiable in the radial variable at every angle of `Iθ`, and the two partials `∂_zδ`,
`∂_z²δ` are jointly continuous on the (radially open) box. -/
private theorem box_facts_at {δ : ℝ → ℝ → ℝ} (hbox : BoxReg δ) {z : ℝ} (hz : 0 < z) :
    (∀ s ∈ Set.Ioo (z / 2) (2 * z), ∀ θ ∈ Work.Spaces.Iθ,
      HasDerivAt (fun s' : ℝ => δ s' θ) (Work.Spaces.pz δ s θ) s) ∧
    (∀ s ∈ Set.Ioo (z / 2) (2 * z), ∀ θ ∈ Work.Spaces.Iθ,
      HasDerivAt (fun s' : ℝ => Work.Spaces.pz δ s' θ) (Work.Spaces.pzIter 2 δ s θ) s) ∧
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz δ p.1 p.2)
      (Set.Ioo (z / 2) (2 * z) ×ˢ Work.Spaces.Iθ) ∧
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 δ p.1 p.2)
      (Set.Ioo (z / 2) (2 * z) ×ˢ Work.Spaces.Iθ) := by
  have hab : z / 2 < 2 * z := by linarith
  have hδ : ContDiffOn ℝ 2 (Function.uncurry δ)
      (Set.Icc (z / 2) (2 * z) ×ˢ Set.Icc 0 (π / 2)) :=
    hbox (z / 2) (2 * z) (by linarith) (le_of_lt hab)
  obtain ⟨hsl, hslpz, hpc, hp2c⟩ := boxReg_facts hab hδ
  have hsub : Set.Ioo (z / 2) (2 * z) ×ˢ Work.Spaces.Iθ
      ⊆ Set.Ioo (z / 2) (2 * z) ×ˢ Set.Icc 0 (π / 2) := by
    intro p hp
    exact ⟨hp.1, hp.2⟩
  exact ⟨fun s hs θ hθ => hsl s hs θ hθ, fun s hs θ hθ => hslpz s hs θ hθ,
    hpc.mono hsub, hp2c.mono hsub⟩

/-- The angular slices of the two radial partials of a box-regular datum are continuous on the
(compact, closed) angular interval. -/
private theorem slices_continuous {δ : ℝ → ℝ → ℝ} (hbox : BoxReg δ) {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun θ : ℝ => Work.Spaces.pz δ z θ) Work.Spaces.Iθ ∧
    ContinuousOn (fun θ : ℝ => Work.Spaces.pzIter 2 δ z θ) Work.Spaces.Iθ := by
  obtain ⟨-, -, hpc, hp2c⟩ := box_facts_at hbox hz
  have hzV : z ∈ Set.Ioo (z / 2) (2 * z) := ⟨by linarith, by linarith⟩
  have h1 : ContinuousOn (fun θ : ℝ => Work.Spaces.pz δ z θ) Work.Spaces.Iθ := by
    have h := hpc.comp (continuousOn_const.prodMk continuousOn_id)
      (fun θ hθ => ⟨hzV, hθ⟩)
    simpa only [Function.comp_def, id_eq] using h
  have h2 : ContinuousOn (fun θ : ℝ => Work.Spaces.pzIter 2 δ z θ) Work.Spaces.Iθ := by
    have h := hp2c.comp (continuousOn_const.prodMk continuousOn_id)
      (fun θ hθ => ⟨hzV, hθ⟩)
    simpa only [Function.comp_def, id_eq] using h
  exact ⟨h1, h2⟩

/-! ## The two derivatives of the angular moment -/

/-- **Differentiation under the angular integral sign.**  For box-regular `δ` and `z > 0`, the
angular moment `F_*δ` has the two expected radial derivatives. -/
private theorem hasDerivAt_moment {δ : ℝ → ℝ → ℝ} (hbox : BoxReg δ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (Work.Elliptic.Fstar δ) (Work.Elliptic.Fstar (Work.Spaces.pz δ) z) z ∧
    HasDerivAt (Work.Elliptic.Fstar (Work.Spaces.pz δ))
      (Work.Elliptic.Fstar (Work.Spaces.pzIter 2 δ) z) z := by
  obtain ⟨hsl, hslpz, hpc, hp2c⟩ := box_facts_at hbox hz
  have hzV : z ∈ Set.Ioo (z / 2) (2 * z) := ⟨by linarith, by linarith⟩
  have hab : z / 2 < 2 * z := by linarith
  have hcontδ : ContinuousOn (fun p : ℝ × ℝ => δ p.1 p.2)
      (Set.Ioo (z / 2) (2 * z) ×ˢ Work.Spaces.Iθ) := by
    have hδ : ContDiffOn ℝ 2 (Function.uncurry δ)
        (Set.Icc (z / 2) (2 * z) ×ˢ Set.Icc 0 (π / 2)) :=
      hbox (z / 2) (2 * z) (by linarith) (le_of_lt hab)
    refine hδ.continuousOn.mono ?_
    intro p hp
    exact ⟨⟨le_of_lt hp.1.1, le_of_lt hp.1.2⟩, hp.2⟩
  have hφ : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2)
      (Set.Ioo (z / 2) (2 * z) ×ˢ Work.Spaces.Iθ) := by
    unfold Work.Elliptic.sinCos2
    fun_prop
  constructor
  · refine Work.Coercivity.hasDerivAt_integral_Itheta_of_hasDerivAt
      (g := fun s θ => δ s θ * Work.Elliptic.sinCos2 θ)
      (g' := fun s θ => Work.Spaces.pz δ s θ * Work.Elliptic.sinCos2 θ)
      isOpen_Ioo hzV ?_ ?_ ?_
    · exact hcontδ.mul hφ
    · exact hpc.mul hφ
    · intro θ hθ s hs
      exact (hsl s hs θ hθ).mul_const _
  · refine Work.Coercivity.hasDerivAt_integral_Itheta_of_hasDerivAt
      (g := fun s θ => Work.Spaces.pz δ s θ * Work.Elliptic.sinCos2 θ)
      (g' := fun s θ => Work.Spaces.pzIter 2 δ s θ * Work.Elliptic.sinCos2 θ)
      isOpen_Ioo hzV ?_ ?_ ?_
    · exact hpc.mul hφ
    · exact hp2c.mul hφ
    · intro θ hθ s hs
      exact (hslpz s hs θ hθ).mul_const _

/-- The second angular moment `F_*(∂_z²δ)` is continuous on `(0,∞)`. -/
private theorem continuousOn_fstar_pzIter2 {δ : ℝ → ℝ → ℝ} (hbox : BoxReg δ) :
    ContinuousOn (Work.Elliptic.Fstar (Work.Spaces.pzIter 2 δ)) (Set.Ioi (0 : ℝ)) := by
  intro z hz
  have hzpos : (0 : ℝ) < z := hz
  obtain ⟨-, -, hpc, hp2c⟩ := box_facts_at hbox hzpos
  have hzV : z ∈ Set.Ioo (z / 2) (2 * z) := ⟨by linarith, by linarith⟩
  have hφ : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2)
      (Set.Ioo (z / 2) (2 * z) ×ˢ Work.Spaces.Iθ) := by
    unfold Work.Elliptic.sinCos2
    fun_prop
  have hcont := Work.Coercivity.continuousOn_integral_Itheta_of_continuousOn
    (g := fun s θ => Work.Spaces.pzIter 2 δ s θ * Work.Elliptic.sinCos2 θ)
    isOpen_Ioo (hp2c.mul hφ)
  exact (hcont.continuousAt (isOpen_Ioo.mem_nhds hzV)).continuousWithinAt

/-! ## The main theorem -/

theorem Fstar_ode_of_bslOp_zero {α : ℝ} (hα : 0 < α) {δ : ℝ → ℝ → ℝ}
    (hsol : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Work.Elliptic.bslOp α δ z θ = 0)
    (hbox : Work.FTS_EllLimOK.BoxReg δ)
    (h0 : ∀ z ∈ Set.Ioi (0 : ℝ), δ z 0 = 0)
    (h1 : ∀ z ∈ Set.Ioi (0 : ℝ), δ z (π / 2) = 0) :
    ContDiffOn ℝ 2 (Work.Elliptic.Fstar δ) (Set.Ioi (0 : ℝ)) ∧
      ∀ z ∈ Set.Ioi (0 : ℝ),
        α ^ 2 * z ^ 2 * deriv (deriv (Work.Elliptic.Fstar δ)) z
          + α * (5 + α) * z * deriv (Work.Elliptic.Fstar δ) z = 0 := by
  have hD1 : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (Work.Elliptic.Fstar δ)
      (Work.Elliptic.Fstar (Work.Spaces.pz δ) z) z :=
    fun z hz => (hasDerivAt_moment hbox hz).1
  have hD2 : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (Work.Elliptic.Fstar (Work.Spaces.pz δ))
      (Work.Elliptic.Fstar (Work.Spaces.pzIter 2 δ) z) z :=
    fun z hz => (hasDerivAt_moment hbox hz).2
  have hcont2 : ContinuousOn (Work.Elliptic.Fstar (Work.Spaces.pzIter 2 δ))
      (Set.Ioi (0 : ℝ)) := continuousOn_fstar_pzIter2 hbox
  -- the derivative of `F_*(∂_zδ)` is `F_*(∂_z²δ)` on `(0,∞)`
  have hcont_deriv : ContinuousOn (deriv (Work.Elliptic.Fstar (Work.Spaces.pz δ)))
      (Set.Ioi (0 : ℝ)) :=
    hcont2.congr (fun z hz => (hD2 z hz).deriv)
  -- `F_*(∂_zδ)` is `C¹`
  have hI1_cd1 : ContDiffOn ℝ 1 (Work.Elliptic.Fstar (Work.Spaces.pz δ))
      (Set.Ioi (0 : ℝ)) := by
    refine (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ)
      (f := Work.Elliptic.Fstar (Work.Spaces.pz δ)) (n := (0 : WithTop ℕ∞))
      (s := Set.Ioi (0 : ℝ)) isOpen_Ioi).2 ⟨?_, ?_, ?_⟩
    · exact fun z hz => (hD2 z hz).differentiableAt.differentiableWithinAt
    · intro h
      exact absurd h (by simp)
    · rw [contDiffOn_zero]
      exact hcont_deriv
  refine ⟨?_, ?_⟩
  · -- `F_*δ` is `C²`
    refine (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (f := Work.Elliptic.Fstar δ)
      (n := (1 : WithTop ℕ∞)) (s := Set.Ioi (0 : ℝ)) isOpen_Ioi).2 ⟨?_, ?_, ?_⟩
    · exact fun z hz => (hD1 z hz).differentiableAt.differentiableWithinAt
    · intro h
      exact absurd h (by simp)
    · exact hI1_cd1.congr (fun z hz => (hD1 z hz).deriv)
  · -- the Euler ODE
    intro z hz
    have hder1 : deriv (Work.Elliptic.Fstar δ) z
        = Work.Elliptic.Fstar (Work.Spaces.pz δ) z := (hD1 z hz).deriv
    have hder2 : deriv (deriv (Work.Elliptic.Fstar δ)) z
        = Work.Elliptic.Fstar (Work.Spaces.pzIter 2 δ) z := by
      have hns : deriv (Work.Elliptic.Fstar δ)
          =ᶠ[𝓝 z] Work.Elliptic.Fstar (Work.Spaces.pz δ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with s hs
        exact (hD1 s hs).deriv
      rw [Filter.EventuallyEq.deriv_eq hns]
      exact (hD2 z hz).deriv
    rw [hder2, hder1]
    -- the integrability side conditions of the moment identity
    obtain ⟨hslc, h2c⟩ := slices_continuous hbox hz
    have hφ : ContinuousOn (fun θ : ℝ => Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
      unfold Work.Elliptic.sinCos2
      fun_prop
    have hIntA : IntegrableOn
        (fun θ : ℝ => (α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 δ z θ
          * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
      ((continuousOn_const.mul h2c).mul hφ).integrableOn_compact isCompact_Icc
    have hIntB : IntegrableOn
        (fun θ : ℝ => (α * (5 + α) * z) * Work.Spaces.pz δ z θ
          * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
      ((continuousOn_const.mul hslc).mul hφ).integrableOn_compact isCompact_Icc
    have hIntL : IntegrableOn
        (fun θ : ℝ => Work.Elliptic.Lzero δ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
      Work.Elliptic.integrableOn_Lzero_mul_sinCos2 δ z (hbox.slice hz)
    have hmom := Work.FTS.ClassC.Fstar_bslOp_moment (α := α) (Ψ := δ) (z := z)
      (hbox.slice hz) (h0 z hz) (h1 z hz) hIntA hIntB hIntL
    -- the moment of the equation vanishes, since the equation does
    have hz0 : Work.Elliptic.Fstar (Work.Elliptic.bslOp α δ) z = 0 := by
      have h := Work.FTS.ClassC.Fstar_bslOp_eq_Fstar (α := α) (F := fun _ _ => (0 : ℝ))
        (Ψ := δ) (z := z) (fun θ hθ hθ2 => hsol z hz θ ⟨hθ, hθ2⟩)
      rw [h]
      simp [Work.Elliptic.Fstar]
    rw [hz0] at hmom
    linarith [hmom]

end Work.FTS_EllLimOK
end
end
-- ===== merged: Submission.Work.FTS_LocDatum3a.BdryTraces_data_locG6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_LocDatum3a

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The separability of the datum -/

/-- The localised datum is the product of its radial and angular factors. -/
theorem bdry_locG6_eq_sep (α L β : ℝ) :
    Work.FTS.LocData6.locG6 α L β
      = fun z θ => Work.FTS.LocDataExt.locR α L β z * Work.Spaces.Gam α θ :=
  Work.FTS.LocDataExt.locG_eq_locR_Gam α L β

/-- **Every mixed slot of the datum is the product of a radial and an angular jet.** -/
theorem bdry_mixed_eq (α L β : ℝ) (b a : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed b a (Work.FTS.LocData6.locG6 α L β) z θ
      = Work.Spaces.DzIter b (fun z _ => Work.FTS.LocDataExt.locR α L β z) z θ
        * Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ := by
  rw [bdry_locG6_eq_sep α L β]
  exact congrFun (congrFun (Work.FTS.LocDataExt.mixed_sepGam α
    (Work.FTS.LocDataExt.locR α L β) b a) z) θ

/-! ## The two radial bounds -/

/-- **The radial jets of `locR` are bounded on `(0,∞)`, uniformly in `z`.**  This is the
weighted bound `hB_locR8` divided by the weight: `w z = (1+z)²/z²` gives
`(D_z^b locR z)² ≤ R z⁴/(1+z)⁶ ≤ R`. -/
theorem bdry_rad_uniform (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ b : ℕ, b ≤ 7 → ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ,
      |Work.Spaces.DzIter b (fun z _ => Work.FTS.LocDataExt.locR α L β z) z θ| ≤ M := by
  obtain ⟨R, hR0, hR⟩ := hB_locR8 α L β hα hα1 hL
  refine ⟨Real.sqrt R, Real.sqrt_nonneg R, fun b hb z hz θ => ?_⟩
  set A : ℝ := Work.Spaces.DzIter b (fun z _ => Work.FTS.LocDataExt.locR α L β z) z θ with hA
  have hzIz : z ∈ Work.Spaces.Iz := by
    rw [Work.Spaces.Iz, Set.mem_Ici]
    exact le_of_lt hz
  have hzpos : 0 < z := hz
  have h1z : 0 < 1 + z := by linarith
  -- the weighted bound, multiplied by `(1+z)²`
  have h1 : A ^ 2 * (Work.Spaces.w z) ^ 2 ≤ R / (1 + z) ^ 2 := by
    have h := hR b (by omega) z hzIz θ
    rw [← hA, mul_pow] at h
    exact h
  have h2 : A ^ 2 * (Work.Spaces.w z) ^ 2 * (1 + z) ^ 2 ≤ R := by
    rw [le_div_iff₀ (pow_pos h1z 2)] at h1
    exact h1
  -- `w z² (1+z)² = ((1+z)³/z²)²`
  have hw2 : (Work.Spaces.w z) ^ 2 * (1 + z) ^ 2 = ((1 + z) ^ 3 / z ^ 2) ^ 2 := by
    rw [Work.Spaces.w, div_pow, div_pow]
    field_simp
  have h3 : A ^ 2 * ((1 + z) ^ 3 / z ^ 2) ^ 2 ≤ R := by
    rw [← hw2]
    calc A ^ 2 * ((Work.Spaces.w z) ^ 2 * (1 + z) ^ 2)
        = A ^ 2 * (Work.Spaces.w z) ^ 2 * (1 + z) ^ 2 := by ring
      _ ≤ R := h2
  have hge : 1 ≤ ((1 + z) ^ 3 / z ^ 2) ^ 2 := by
    have h1' : 1 ≤ (1 + z) ^ 3 / z ^ 2 := by
      rw [le_div_iff₀ (pow_pos hzpos 2)]
      nlinarith [hzpos]
    nlinarith [h1']
  have h4 : A ^ 2 ≤ R := by
    have := mul_le_mul_of_nonneg_left hge (sq_nonneg A)
    linarith
  have h5 : Real.sqrt (A ^ 2) ≤ Real.sqrt R := Real.sqrt_le_sqrt h4
  simpa [Real.sqrt_sq_eq_abs] using h5

/-- **The far-field decay of the radial jets of `locR`.**  Beyond `max (2L) (7/4)` the factor
`locR` agrees with `-(α/c)·F_*` near `z`, and the `D_z`-jets of `F_*` decay like `1/z`. -/
theorem bdry_rad_far (α L β : ℝ) (hL : 1 ≤ L) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ b : ℕ, b ≤ 8 → ∀ z : ℝ, max (2 * L) (7 / 4) < z → ∀ θ : ℝ,
      |Work.Spaces.DzIter b (fun z _ => Work.FTS.LocDataExt.locR α L β z) z θ| ≤ A / z := by
  obtain ⟨CF, hCF, hF⟩ := FM_jet8safe
  refine ⟨|α / Work.Spaces.c α| * CF, by positivity, fun b hb z hz θ => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hz2 : 2 * L < z := lt_of_le_of_lt (le_max_left _ _) hz
  have hz7 : 7 / 4 < z := lt_of_le_of_lt (le_max_right _ _) hz
  have hz1 : (1 : ℝ) ≤ z := by linarith
  have hev := Work.FTS.LocDataExt.locR_eventuallyEq_far (α := α) (L := L) (β := β)
    hLpos hz2 hz7
  have hcongr := Work.FTS.LocDataExt.DzIter_z_congr_of_eventuallyEq hev b θ
  have hcm : Work.Spaces.DzIter b (fun z _ => -(α / Work.Spaces.c α) * Work.FM.Fstar z) z θ
      = -(α / Work.Spaces.c α) * Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z θ :=
    congrFun (congrFun (Work.FTS.LocDataExt.DzIter_const_mul (-(α / Work.Spaces.c α))
      (fun z _ => Work.FM.Fstar z) b) z) θ
  rw [hcongr, hcm, abs_mul, abs_neg]
  have h2 := hF b hb z hz1 θ
  calc |α / Work.Spaces.c α| * |Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z θ|
      ≤ |α / Work.Spaces.c α| * (CF / z) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ = |α / Work.Spaces.c α| * CF / z := by ring

/-! ## The datum lemma -/

theorem BdryTraces_data_locG6 (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L) :
    (∀ a b : ℕ, a + b ≤ 7 → ∃ M : ℝ, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
        |Work.Spaces.mixed b a (Work.FTS.LocData6.locG6 α L β) z θ| ≤ M) ∧
      (∀ a b : ℕ, a + b ≤ 7 → ∀ ε' > 0, ∃ δ > 0, ∀ z : ℝ, 0 < z → z < δ →
        ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) →
          z * (Work.Spaces.mixed b a (Work.FTS.LocData6.locG6 α L β) z θ * Work.Spaces.w z) ^ 2
            ≤ ε') ∧
      (∀ a b : ℕ, a + b ≤ 7 → ∀ ε' > 0, ∃ Z : ℝ, ∀ z : ℝ, Z < z →
        ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) →
          z * (Work.Spaces.mixed b a (Work.FTS.LocData6.locG6 α L β) z θ * Work.Spaces.w z) ^ 2
            ≤ ε') ∧
      (∀ a b : ℕ, a + b ≤ 7 → ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, 0 < θ → θ < δ →
        ∀ z : ℝ, 0 < z → Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a (Work.FTS.LocData6.locG6 α L β) z θ) ^ 2 ≤ ε') ∧
      (∀ a b : ℕ, a + b ≤ 7 → ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, θ < π / 2 → π / 2 - δ < θ →
        ∀ z : ℝ, 0 < z → Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a (Work.FTS.LocData6.locG6 α L β) z θ) ^ 2 ≤ ε') := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨M, hM0, hM⟩ := bdry_rad_uniform α L β hα hα1 hL
  obtain ⟨A, hA0, hA⟩ := bdry_rad_far α L β hL
  -- the angular bound `|D_θ^a Γ| ≤ 10⁷` for `a ≤ 8`
  have hang : ∀ a : ℕ, a ≤ 8 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ| ≤ 10000000 := by
    intro a ha θ hθ
    have h1 := DthIter_Gam_abs_le8 a ha α hα hα1 hθ
    have h2 : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- ## the slots are bounded
    intro a b hab
    have hb7 : b ≤ 7 := by omega
    have ha8 : a ≤ 8 := by omega
    refine ⟨M * 10000000, fun z θ hz hθ => ?_⟩
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    rw [bdry_mixed_eq α L β b a z θ, abs_mul]
    exact mul_le_mul (hM b hb7 z hz θ) (hang a ha8 θ hθI) (abs_nonneg _) hM0
  · -- ## the `z → 0⁺` traces: the datum vanishes near `z = 0`
    intro a b hab ε' hε'
    refine ⟨min L (3 / 4), lt_min hLpos (by norm_num), fun z hz hzδ θ hθ => ?_⟩
    have hev : ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ, Work.FTS.LocData6.locG6 α L β z' θ' = 0 := by
      filter_upwards [Ioo_mem_nhds hz hzδ] with z' hz' θ'
      rw [bdry_locG6_eq_sep α L β]
      have h1 : Work.FTS.LocDataExt.locR α L β z' = 0 :=
        Work.FTS.LocDataExt.locR_eq_zero_of_le hLpos (le_of_lt hz'.1)
          (le_of_lt (lt_of_lt_of_le hz'.2 (min_le_left _ _)))
          (le_of_lt (lt_of_lt_of_le hz'.2 (min_le_right _ _)))
      show Work.FTS.LocDataExt.locR α L β z' * Work.Spaces.Gam α θ' = 0
      rw [h1, zero_mul]
    have hzero : Work.Spaces.mixed b a (Work.FTS.LocData6.locG6 α L β) z θ = 0 :=
      Work.FTS.LocData.ZFBase.mixed_eq_zero_of_eventually_zero hev b a
    have hz0 : z * (Work.Spaces.mixed b a (Work.FTS.LocData6.locG6 α L β) z θ
        * Work.Spaces.w z) ^ 2 = 0 := by
      rw [hzero]; ring
    rw [hz0]
    exact le_of_lt hε'
  · -- ## the `z → ∞` traces, from the `1/z`-decay of the radial jets
    intro a b hab ε' hε'
    have hb8 : b ≤ 8 := by omega
    have ha8 : a ≤ 8 := by omega
    refine ⟨max (max (2 * L) (7 / 4) + 1)
      (16 * A ^ 2 * (10000000 : ℝ) ^ 2 / ε' + 1), fun z hz θ hθ => ?_⟩
    have hzfar : max (2 * L) (7 / 4) < z := by
      have h : max (2 * L) (7 / 4) + 1 ≤ z := le_trans (le_max_left _ _) (le_of_lt hz)
      linarith
    have hzbig : 16 * A ^ 2 * (10000000 : ℝ) ^ 2 / ε' < z := by
      have h : 16 * A ^ 2 * (10000000 : ℝ) ^ 2 / ε' + 1 ≤ z :=
        le_trans (le_max_right _ _) (le_of_lt hz)
      linarith
    have hz7 : (7 / 4 : ℝ) < z := lt_of_le_of_lt (le_max_right _ _) hzfar
    have hzpos : 0 < z := by linarith
    have hz1 : (1 : ℝ) ≤ z := by linarith
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hrad := hA b hb8 z hzfar θ
    have hangb := hang a ha8 θ hθI
    have hmix : |Work.Spaces.mixed b a (Work.FTS.LocData6.locG6 α L β) z θ|
        ≤ A / z * 10000000 := by
      rw [bdry_mixed_eq α L β b a z θ, abs_mul]
      exact mul_le_mul hrad hangb (abs_nonneg _) (by positivity)
    have hmix2 : (Work.Spaces.mixed b a (Work.FTS.LocData6.locG6 α L β) z θ) ^ 2
        ≤ (A / z * 10000000) ^ 2 := by
      have h1 := pow_le_pow_left₀ (abs_nonneg _) hmix 2
      rwa [sq_abs] at h1
    have hw16 : (Work.Spaces.w z) ^ 2 ≤ 16 := Work.FTS.LocDataExt.w_sq_le_sixteen hz1
    have hfinal : 16 * A ^ 2 * (10000000 : ℝ) ^ 2 / z ≤ ε' := by
      rw [div_le_iff₀ hzpos]
      have h2 : 16 * A ^ 2 * (10000000 : ℝ) ^ 2 < z * ε' := (div_lt_iff₀ hε').mp hzbig
      linarith
    calc z * (Work.Spaces.mixed b a (Work.FTS.LocData6.locG6 α L β) z θ * Work.Spaces.w z) ^ 2
        = z * (Work.Spaces.mixed b a (Work.FTS.LocData6.locG6 α L β) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 := by ring
      _ ≤ z * (A / z * 10000000) ^ 2 * 16 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hmix2 (le_of_lt hzpos)) hw16
            (sq_nonneg _) ?_
          positivity
      _ = 16 * A ^ 2 * (10000000 : ℝ) ^ 2 / z := by
          field_simp
      _ ≤ ε' := hfinal
  · -- ## the `θ → 0⁺` traces, uniformly in `z`
    intro a b hab ε' hε'
    have hb7 : b ≤ 7 := by omega
    have ha8 : a ≤ 8 := by omega
    have hC0 : 0 ≤ M * 10000000 := by positivity
    have hbound : ∀ θ ∈ Work.Spaces.Iθ,
        |M * Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
          ≤ (M * 10000000) * Work.Spaces.Gam α θ := by
      intro θ hθ
      rw [abs_mul, abs_of_nonneg hM0]
      have h1 := DthIter_Gam_abs_le8 a ha8 α hα hα1 hθ
      calc M * |Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
          ≤ M * (10000000 * Work.Spaces.Gam α θ) := mul_le_mul_of_nonneg_left h1 hM0
        _ = M * 10000000 * Work.Spaces.Gam α θ := by ring
    have hlim := (Work.FTS.LocDataExt.tendsto_sin_gam_trace α hα hC0 hbound).1
    obtain ⟨δ₁, hδ₁0, hδ₁⟩ := Metric.tendsto_nhdsWithin_nhds.mp hlim ε' hε'
    refine ⟨min δ₁ (π / 4), lt_min hδ₁0 (by positivity), fun θ hθ0 hθδ z hz => ?_⟩
    have hθδ₁ : θ < δ₁ := lt_of_lt_of_le hθδ (min_le_left _ _)
    have hθπ : θ < π / 4 := lt_of_lt_of_le hθδ (min_le_right _ _)
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, by linarith [hθπ, Real.pi_pos]⟩
    have hdist : dist θ (0 : ℝ) < δ₁ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hθ0]
      exact hθδ₁
    have hkey : Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (M * Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2 < ε' := by
      have h := hδ₁ (Set.mem_Ioi.mpr hθ0) hdist
      rw [Real.dist_eq, sub_zero] at h
      exact (abs_lt.mp h).2
    have hmix2 : (Work.Spaces.mixed b a (Work.FTS.LocData6.locG6 α L β) z θ) ^ 2
        ≤ (M * Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2 := by
      rw [bdry_mixed_eq α L β b a z θ, mul_pow, mul_pow]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have h1 := pow_le_pow_left₀ (abs_nonneg _) (hM b hb7 z hz θ) 2
      rwa [sq_abs] at h1
    have hsin0 : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
      Real.rpow_nonneg (Work.FTS.LocData.ZFBase.sin_two_nonneg_Iθ hθI) _
    calc Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a (Work.FTS.LocData6.locG6 α L β) z θ) ^ 2
        ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (M * Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2 :=
          mul_le_mul_of_nonneg_left hmix2 hsin0
      _ ≤ ε' := le_of_lt hkey
  · -- ## the `θ → (π/2)⁻` traces, uniformly in `z`
    intro a b hab ε' hε'
    have hb7 : b ≤ 7 := by omega
    have ha8 : a ≤ 8 := by omega
    have hC0 : 0 ≤ M * 10000000 := by positivity
    have hbound : ∀ θ ∈ Work.Spaces.Iθ,
        |M * Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
          ≤ (M * 10000000) * Work.Spaces.Gam α θ := by
      intro θ hθ
      rw [abs_mul, abs_of_nonneg hM0]
      have h1 := DthIter_Gam_abs_le8 a ha8 α hα hα1 hθ
      calc M * |Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
          ≤ M * (10000000 * Work.Spaces.Gam α θ) := mul_le_mul_of_nonneg_left h1 hM0
        _ = M * 10000000 * Work.Spaces.Gam α θ := by ring
    have hlim := (Work.FTS.LocDataExt.tendsto_sin_gam_trace α hα hC0 hbound).2
    obtain ⟨δ₁, hδ₁0, hδ₁⟩ := Metric.tendsto_nhdsWithin_nhds.mp hlim ε' hε'
    refine ⟨min δ₁ (π / 4), lt_min hδ₁0 (by positivity), fun θ hθπ hθδ z hz => ?_⟩
    have hδ' : π / 2 - δ₁ ≤ π / 2 - min δ₁ (π / 4) := by
      have := min_le_left δ₁ (π / 4)
      linarith
    have hθδ₁ : π / 2 - δ₁ < θ := by linarith
    have hθpos : 0 < θ := by
      have hmin : min δ₁ (π / 4) ≤ π / 4 := min_le_right _ _
      have h : (0 : ℝ) < π / 2 - min δ₁ (π / 4) := by linarith [Real.pi_pos, hmin]
      linarith
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθpos, le_of_lt hθπ⟩
    have hdist : dist θ (π / 2) < δ₁ := by
      rw [Real.dist_eq, abs_of_neg (by linarith : θ - π / 2 < 0)]
      linarith
    have hkey : Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (M * Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2 < ε' := by
      have h := hδ₁ (Set.mem_Iio.mpr hθπ) hdist
      rw [Real.dist_eq, sub_zero] at h
      exact (abs_lt.mp h).2
    have hmix2 : (Work.Spaces.mixed b a (Work.FTS.LocData6.locG6 α L β) z θ) ^ 2
        ≤ (M * Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2 := by
      rw [bdry_mixed_eq α L β b a z θ, mul_pow, mul_pow]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have h1 := pow_le_pow_left₀ (abs_nonneg _) (hM b hb7 z hz θ) 2
      rwa [sq_abs] at h1
    have hsin0 : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
      Real.rpow_nonneg (Work.FTS.LocData.ZFBase.sin_two_nonneg_Iθ hθI) _
    calc Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a (Work.FTS.LocData6.locG6 α L β) z θ) ^ 2
        ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (M * Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2 :=
          mul_le_mul_of_nonneg_left hmix2 hsin0
      _ ≤ ε' := le_of_lt hkey

end Work.FTS_LocDatum3a
end
end
-- ===== merged: Submission.Work.FTS_LocDatum3a.HkMem_locG8 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_LocDatum3a

set_option autoImplicit false

/-! ## The angular jet bound at order `8` -/

/-- The squared angular jet bound `(D_θ^i Γ)² ≤ 10¹⁴·Γ²` on `Iθ`, for `i ≤ 8`, obtained by
squaring `|D_θ^i Γ| ≤ 10⁷·Γ` (`DthIter_Gam_abs_le8`). -/
theorem hGam8 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {i : ℕ} (hi : i ≤ 8) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
      ≤ (10 : ℝ) ^ 14 * (Work.Spaces.Gam α θ) ^ 2 := by
  have h := DthIter_Gam_abs_le8 i hi α hα hα1 hθ
  have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs, mul_pow] at h2
  have h14 : ((10000000 : ℝ)) ^ 2 = (10 : ℝ) ^ 14 := by norm_num
  calc (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
      ≤ (10000000 : ℝ) ^ 2 * (Work.Spaces.Gam α θ) ^ 2 := h2
    _ = (10 : ℝ) ^ 14 * (Work.Spaces.Gam α θ) ^ 2 := by rw [h14]

/-! ## The target -/

/-- **The localised order-`6` datum lies in `ℋ⁸`.**  For `0 < α ≤ 1`, `1 ≤ L` and every `β`,
`Work.Spaces.HkMem α 8 (locG6 α L β)`: the weighted `ℋ⁸`-integrand of the datum is dominated by
the integrable majorant `K·angMaj α θ/(1+z)²`.

This is the order-`8` companion of `Work.FTS.LocData6.HkMem_locG6` (and the `mem8` input of
`Work.FTS.StrongEps.softClass_Jeps` for the datum `locG6 α L β` of clause (3a′)). -/
theorem HkMem_locG8 (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L) :
    Work.Spaces.HkMem α 8 (Work.FTS.LocData6.locG6 α L β) := by
  obtain ⟨CF, hCF, hF⟩ := FM_jet8safe
  obtain ⟨R, hR0, hB⟩ := hB_locR8_of_FMjet α L β hα hα1 hL hCF hF
  have hΓ : ∀ i ≤ 8, ∀ θ' ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ') ^ 2
        ≤ (10 : ℝ) ^ 14 * (Work.Spaces.Gam α θ') ^ 2 :=
    fun i hi θ' hθ' => hGam8 α hα hα1 hi hθ'
  -- the separability of the datum: `locG6 α L β = locR α L β(z)·Γ(θ)`
  have hloc : Work.FTS.LocData6.locG6 α L β
      = fun z θ => Work.FTS.LocDataExt.locR α L β z * Work.Spaces.Gam α θ := by
    rw [Work.FTS.LocData6.locG6_eq]
    exact Work.FTS.LocDataExt.locG_eq_locR_Gam α L β
  -- joint continuity of the integrand on the open quadrant
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.HkIntegrand α 8 (Work.FTS.LocData6.locG6 α L β) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hsq : Work.FTS.LocData.SmoothQuad (Work.FTS.LocData6.locG6 α L β) := by
      rw [hloc]
      exact Work.FTS.LocDataExt.smoothQuad_sepGam
        (Work.FTS.LocDataExt.contDiffOn_locR α L β)
    exact Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 8 _ hsq
  -- membership by domination with the integrable majorant
  refine Work.FTS.LocData.HkMem_of_majorant (f := Work.FTS.LocData6.locG6 α L β)
    (M := fun z θ => (((8 + 1 : ℕ) : ℝ) + (((8 + 1 : ℕ) ^ 2 : ℕ) : ℝ) * (10 : ℝ) ^ 14) * R
      * Work.FTS.LocData.angMaj α θ / (1 + z) ^ 2) α 8 hcont ?_ ?_ ?_
  · exact (Work.FTS.LocData.integrableOn_angMaj_majorant α
      ((((8 + 1 : ℕ) : ℝ) + (((8 + 1 : ℕ) ^ 2 : ℕ) : ℝ) * (10 : ℝ) ^ 14) * R)
      hα hα1).1
  · exact (Work.FTS.LocData.integrableOn_angMaj_majorant α
      ((((8 + 1 : ℕ) : ℝ) + (((8 + 1 : ℕ) ^ 2 : ℕ) : ℝ) * (10 : ℝ) ^ 14) * R)
      hα hα1).2
  · -- the pointwise bound: the generic separable majorant at `k = 8`
    intro z hz θ hθ
    rw [hloc]
    exact Work.FTS.LocDataExt.HkIntegrand_sepGam_le α hα 8
      (ρ := Work.FTS.LocDataExt.locR α L β) (R := R) (Rθ := (10 : ℝ) ^ 14)
      hR0 (by norm_num) hB hΓ hz hθ

end Work.FTS_LocDatum3a
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `JetCalc/Expand` — the jet expansion of a differential combination

This module assembles the primitive jet-calculus lemmas proved in the sibling modules
(`dthIter_coef_mul_eqOn`, `dzIter_sum_coef_eqOn`, `dthIter_Dz_eqOn`, and the two
congruence lemmas) into the two identities used by the slot-convergence theorem:

* `mixed_coef_mul_pt`: the mixed jet of `c(θ)·X` is the angular Leibniz sum of `c`
  against the mixed jets of `X` (`coefJetS c j i 0 X`);
* `mixed_combo_pt`: for `j + i ≤ 2`, the mixed jet of the combination
  `a(θ)·X + b(θ)·D_zX + c(θ)·∂_θX` is `EJet a b c j i X`.

Also here: the two elementary quadrant facts (`sin_two_pos_quad`, `cos_pos_quad`),
the `z`-independence of the angular coefficients (`dthIter_const_z`), the `D_z`-shift
`mixed_Dz_shift`, and the congruence of `mixed` on the open quadrant.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT.Slots.JetCalc

/-- `sin(2θ)` is positive on the open quadrant. -/
theorem sin_two_pos_quad {z θ : ℝ} (h : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [h.2.1]) (by linarith [h.2.2, Real.pi_pos])

/-- `cos θ` is positive on the open quadrant. -/
theorem cos_pos_quad {z θ : ℝ} (h : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [h.2.1, Real.pi_pos], by linarith [h.2.2, Real.pi_pos]⟩

/-! ## Congruence and the `z`-independence of the angular coefficients -/

/-- Congruence of `mixed` under equality on the open quadrant. -/
theorem mixed_congr_eqOn {F G : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry F) (Function.uncurry G) Work.FTS.EllipticEst.Q0) (j i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.mixed j i F))
      (Function.uncurry (Work.Spaces.mixed j i G)) Work.FTS.EllipticEst.Q0 :=
  dzIter_congr_eqOn (dthIter_congr_eqOn h i) j

/-- The iterated angular operator applied to a `θ`-only function does not depend on `z`. -/
theorem dthIter_const_z (k : ℕ) (c : ℝ → ℝ) (z z' : ℝ) :
    Work.Spaces.DthIter k (fun _ (θ' : ℝ) => c θ') z
      = Work.Spaces.DthIter k (fun _ (θ' : ℝ) => c θ') z' := by
  induction k generalizing z z' with
  | zero => rfl
  | succ k ih =>
      funext θ
      show Real.sin (2 * θ)
            * deriv (fun θ' => Work.Spaces.DthIter k (fun _ (θ'' : ℝ) => c θ'') z θ') θ
        = Real.sin (2 * θ)
            * deriv (fun θ' => Work.Spaces.DthIter k (fun _ (θ'' : ℝ) => c θ'') z' θ') θ
      rw [ih z z']

/-- Pointwise form of `dthIter_const_z`. -/
theorem dthIter_const_z_pt (k : ℕ) (c : ℝ → ℝ) (z z' θ : ℝ) :
    Work.Spaces.DthIter k (fun _ (θ' : ℝ) => c θ') z θ
      = Work.Spaces.DthIter k (fun _ (θ' : ℝ) => c θ') z' θ :=
  congrFun (dthIter_const_z k c z z') θ

/-! ## Congruence of `D_θ` and Clairaut for the iterates

The child module `JetCalc/dthIter_Dz_eqOn` carries the same commutation identity; as it is not
needed by anything else here, the identity is reproved below in a form self-contained in this
module (so that the slot theorem does not depend on it). -/


/-- Clairaut for the iterates at finite order: `D_θ^i(D_zX) = D_z(D_θ^iX)` on the open
quadrant, for `X` of class `C^{i+1}`. -/
theorem dthIter_Dz_eqOn_alt : ∀ (i : ℕ) (X : ℝ → ℝ → ℝ),
    ContDiffOn ℝ (i + 1) (Function.uncurry X) Work.FTS.EllipticEst.Q0 →
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz X)))
      (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i X)))
      Work.FTS.EllipticEst.Q0 := by
  intro i
  induction i with
  | zero => intro X hX; exact fun _ _ => rfl
  | succ i ih =>
      intro X hX p hp
      obtain ⟨z, θ⟩ := p
      have hXi : ContDiffOn ℝ (i + 1) (Function.uncurry X) Work.FTS.EllipticEst.Q0 :=
        hX.of_le (Nat.cast_le.mpr (Nat.le_succ (i + 1)))
      have hih : Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz X)))
          (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i X)))
          Work.FTS.EllipticEst.Q0 := ih X hXi
      have hDthC : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.DthIter i X))
          Work.FTS.EllipticEst.Q0 :=
        Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_DthIter_le
          (n := Nat.succ i + 1) Work.FTS.EllipticEst.isOpen_Q0 i 2 le_rfl hX
      have hstep : Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.Dz X)) z θ
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DthIter i X)) z θ := by
        show Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DthIter i (Work.Spaces.Dz X)) z θ
            = Real.sin (2 * θ)
                * Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DthIter i X)) z θ
        rw [Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hih hp]
      have hcl : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i X)) z θ
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DthIter i X)) z θ :=
        Work.Spaces.Dz_Dth_comm
          (hDthC.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp))
      show Work.Spaces.DthIter (i + 1) (Work.Spaces.Dz X) z θ
          = Work.Spaces.Dz (Work.Spaces.DthIter (i + 1) X) z θ
      rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_succ, hstep, hcl]

/-! ## The `D_z`-shift of a mixed jet -/

/-- A `D_z` inside a mixed jet shifts the radial order by one. -/
theorem mixed_Dz_shift {j i : ℕ} {Y : ℝ → ℝ → ℝ}
    (hY : ContDiffOn ℝ (j + i + 1) (Function.uncurry Y) Work.FTS.EllipticEst.Q0) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.mixed j i (Work.Spaces.Dz Y) z θ
        = Work.Spaces.mixed (j + 1) i Y z θ := by
  intro z θ hp
  have h1 : ContDiffOn ℝ (i + 1) (Function.uncurry Y) Work.FTS.EllipticEst.Q0 :=
    hY.of_le (Nat.cast_le.mpr (by omega : i + 1 ≤ j + i + 1))
  have hcomm : Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz Y)))
      (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i Y))) Work.FTS.EllipticEst.Q0 :=
    dthIter_Dz_eqOn_alt i Y h1
  have h2 := dzIter_congr_eqOn hcomm j hp
  have hDz1 : Work.Spaces.Dz (Work.Spaces.DthIter i Y)
      = Work.Spaces.DzIter 1 (Work.Spaces.DthIter i Y) := by
    rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz Y)) z θ
      = Work.Spaces.DzIter (j + 1) (Work.Spaces.DthIter i Y) z θ
  rw [show Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz Y)) z θ
      = Work.Spaces.DzIter j (Work.Spaces.Dz (Work.Spaces.DthIter i Y)) z θ from h2, hDz1]
  exact congrFun (congrFun (Work.Spaces.DzIter_add_right j 1
    (Work.Spaces.DthIter i Y)).symm z) θ

/-! ## The expansion of a coefficient times a function -/

/-- **The coefficient expansion.**  For a `θ`-dependent coefficient `c` and a function `X`
which is `C^{i+j}` on the open quadrant, the mixed jet `D_z^jD_θ^i(c·X)` is the angular
Leibniz sum of the coefficient against the mixed jets of `X`. -/
theorem mixed_coef_mul_pt {j i : ℕ} {c : ℝ → ℝ} {X : ℝ → ℝ → ℝ}
    (hX : ContDiffOn ℝ (i + j) (Function.uncurry X) Work.FTS.EllipticEst.Q0)
    (hc : ContDiffOn ℝ i (fun p : ℝ × ℝ => c p.2) Work.FTS.EllipticEst.Q0) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.mixed j i (fun z θ => c θ * X z θ) z θ = coefJetS c j i 0 X z θ := by
  intro z θ hp
  have hXi : ContDiffOn ℝ i (Function.uncurry X) Work.FTS.EllipticEst.Q0 :=
    hX.of_le (Nat.cast_le.mpr (by omega : i ≤ i + j))
  have h1 : Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (fun z θ => c θ * X z θ)))
      (Function.uncurry (fun z θ => ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) *
        (Work.Spaces.DthIter k (fun _ (θ' : ℝ) => c θ') z θ
          * Work.Spaces.DthIter (i - k) X z θ)))
      Work.FTS.EllipticEst.Q0 := dthIter_coef_mul_eqOn hXi hc
  have hsumEq : Set.EqOn
      (Function.uncurry (fun z θ => ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) *
        (Work.Spaces.DthIter k (fun _ (θ' : ℝ) => c θ') z θ
          * Work.Spaces.DthIter (i - k) X z θ)))
      (Function.uncurry (fun z θ => ∑ k ∈ Finset.range (i + 1),
        ((i.choose k : ℝ) * Work.Spaces.DthIter k (fun _ (θ' : ℝ) => c θ') z θ)
          * Work.Spaces.DthIter (i - k) X z θ))
      Work.FTS.EllipticEst.Q0 := by
    intro p hp'
    simp only [Function.uncurry]
    exact Finset.sum_congr rfl (fun k hk => by ring)
  have hkey := h1.trans hsumEq
  have h2 := dzIter_congr_eqOn hkey j hp
  have hbridge : Set.EqOn
      (Function.uncurry (fun z θ => ∑ k ∈ Finset.range (i + 1),
        ((i.choose k : ℝ) * Work.Spaces.DthIter k (fun _ (θ' : ℝ) => c θ') z θ)
          * Work.Spaces.DthIter (i - k) X z θ))
      (Function.uncurry (fun z' θ' => ∑ k ∈ Finset.range (i + 1),
        ((i.choose k : ℝ) * Work.Spaces.DthIter k (fun _ (θ'' : ℝ) => c θ'') z θ')
          * Work.Spaces.DthIter (i - k) X z' θ'))
      Work.FTS.EllipticEst.Q0 := by
    intro p hp'
    simp only [Function.uncurry]
    exact Finset.sum_congr rfl (fun k hk => by rw [dthIter_const_z_pt k c p.1 z p.2])
  have h2b := dzIter_congr_eqOn hbridge j hp
  have hF : ∀ k ∈ Finset.range (i + 1),
      ContDiffOn ℝ j (Function.uncurry (Work.Spaces.DthIter (i - k) X))
        Work.FTS.EllipticEst.Q0 :=
    fun k hk => Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_DthIter_le
      Work.FTS.EllipticEst.isOpen_Q0 (i - k) j (Nat.add_le_add_right (Nat.sub_le i k) j) hX
  have h3 := dzIter_sum_coef_eqOn (s := Finset.range (i + 1))
    (c := fun k (θ' : ℝ) => (i.choose k : ℝ) * Work.Spaces.DthIter k (fun _ (θ'' : ℝ) => c θ'') z θ')
    (F := fun k => Work.Spaces.DthIter (i - k) X) j hF hp
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => c θ * X z θ)) z θ
      = coefJetS c j i 0 X z θ
  rw [show Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => c θ * X z θ)) z θ
      = Work.Spaces.DzIter j (fun z θ => ∑ k ∈ Finset.range (i + 1),
          ((i.choose k : ℝ) * Work.Spaces.DthIter k (fun _ (θ' : ℝ) => c θ') z θ)
            * Work.Spaces.DthIter (i - k) X z θ) z θ from h2]
  rw [show Work.Spaces.DzIter j (fun z θ => ∑ k ∈ Finset.range (i + 1),
          ((i.choose k : ℝ) * Work.Spaces.DthIter k (fun _ (θ' : ℝ) => c θ') z θ)
            * Work.Spaces.DthIter (i - k) X z θ) z θ
      = Work.Spaces.DzIter j (fun z' θ' => ∑ k ∈ Finset.range (i + 1),
          ((i.choose k : ℝ) * Work.Spaces.DthIter k (fun _ (θ'' : ℝ) => c θ'') z θ')
            * Work.Spaces.DthIter (i - k) X z' θ') z θ from h2b]
  rw [show Work.Spaces.DzIter j (fun z' θ' => ∑ k ∈ Finset.range (i + 1),
          ((i.choose k : ℝ) * Work.Spaces.DthIter k (fun _ (θ'' : ℝ) => c θ'') z θ')
            * Work.Spaces.DthIter (i - k) X z' θ') z θ
      = ∑ k ∈ Finset.range (i + 1),
          ((i.choose k : ℝ) * Work.Spaces.DthIter k (fun _ (θ'' : ℝ) => c θ'') z θ)
            * Work.Spaces.DzIter j (Work.Spaces.DthIter (i - k) X) z θ from h3]
  rw [coefJetS]
  simp only [Nat.add_zero]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [show Work.Spaces.DzIter j (Work.Spaces.DthIter (i - k) X) z θ
      = Work.Spaces.mixed j (i - k) X z θ from rfl]
  ring

/-! ## The master expansion of the combination -/

/-- **The combinatorial identity.**  For `j + i ≤ 2`, the mixed jet of
`a(θ)·X + b(θ)·D_zX + c(θ)·∂_θX` is the jet functional `EJet`. -/
theorem mixed_combo_pt {j i : ℕ} (hji : j + i ≤ 2) {a b c : ℝ → ℝ} {X : ℝ → ℝ → ℝ}
    (hX : ContDiffOn ℝ 3 (Function.uncurry X) Work.FTS.EllipticEst.Q0)
    (ha : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => a p.2) Work.FTS.EllipticEst.Q0)
    (hb : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => b p.2) Work.FTS.EllipticEst.Q0)
    (hc : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => c p.2) Work.FTS.EllipticEst.Q0) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.mixed j i (combo a b c X) z θ = EJet a b c j i X z θ := by
  intro z θ hp
  have hji3 : j + i ≤ 3 := by omega
  have hij : i + j ≤ 3 := by omega
  have hT1 : ContDiffOn ℝ (i + j) (fun p : ℝ × ℝ => a p.2 * X p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
    have h1 : ContDiffOn ℝ (i + j) (fun p : ℝ × ℝ => a p.2) Work.FTS.EllipticEst.Q0 :=
      ha.of_le (Nat.cast_le.mpr (by omega : i + j ≤ 2))
    have h2 : ContDiffOn ℝ (i + j) (fun p : ℝ × ℝ => X p.1 p.2) Work.FTS.EllipticEst.Q0 :=
      hX.of_le (Nat.cast_le.mpr hij)
    exact h1.mul h2
  have hDzX : ContDiffOn ℝ (i + j) (fun p : ℝ × ℝ => Work.Spaces.Dz X p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_Dz_of_succ
      Work.FTS.EllipticEst.isOpen_Q0 (n := 2) hX).of_le (Nat.cast_le.mpr (by omega : i + j ≤ 2))
  have hT2 : ContDiffOn ℝ (i + j) (fun p : ℝ × ℝ => b p.2 * Work.Spaces.Dz X p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
    have h1 : ContDiffOn ℝ (i + j) (fun p : ℝ × ℝ => b p.2) Work.FTS.EllipticEst.Q0 :=
      hb.of_le (Nat.cast_le.mpr (by omega : i + j ≤ 2))
    exact h1.mul hDzX
  have hpthX : ContDiffOn ℝ (i + j) (fun p : ℝ × ℝ => Work.Spaces.pth X p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_pth_of_succ
      Work.FTS.EllipticEst.isOpen_Q0 (n := 2) hX).of_le (Nat.cast_le.mpr (by omega : i + j ≤ 2))
  have hT3 : ContDiffOn ℝ (i + j) (fun p : ℝ × ℝ => c p.2 * Work.Spaces.pth X p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
    have h1 : ContDiffOn ℝ (i + j) (fun p : ℝ × ℝ => c p.2) Work.FTS.EllipticEst.Q0 :=
      hc.of_le (Nat.cast_le.mpr (by omega : i + j ≤ 2))
    exact h1.mul hpthX
  have hT12 : ContDiffOn ℝ (i + j)
      (fun p : ℝ × ℝ => a p.2 * X p.1 p.2 + b p.2 * Work.Spaces.Dz X p.1 p.2)
      Work.FTS.EllipticEst.Q0 := hT1.add hT2
  -- additivity of `mixed` over the two sums
  have hadd1 : Work.Spaces.mixed j i
      (fun z θ => a θ * X z θ + b θ * Work.Spaces.Dz X z θ + c θ * Work.Spaces.pth X z θ) z θ
      = Work.Spaces.mixed j i (fun z θ => a θ * X z θ + b θ * Work.Spaces.Dz X z θ) z θ
        + Work.Spaces.mixed j i (fun z θ => c θ * Work.Spaces.pth X z θ) z θ :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.mixed_add_of_contDiffOn Work.FTS.EllipticEst.isOpen_Q0
      hT12 hT3 i j le_rfl (z, θ) hp
  have hadd2 : Work.Spaces.mixed j i (fun z θ => a θ * X z θ + b θ * Work.Spaces.Dz X z θ) z θ
      = Work.Spaces.mixed j i (fun z θ => a θ * X z θ) z θ
        + Work.Spaces.mixed j i (fun z θ => b θ * Work.Spaces.Dz X z θ) z θ :=
    Work.FTS.CoercivityFix.Transfer.E2pkg.mixed_add_of_contDiffOn Work.FTS.EllipticEst.isOpen_Q0
      hT1 hT2 i j le_rfl (z, θ) hp
  -- the three expansions
  have hXi : ContDiffOn ℝ (i + j) (Function.uncurry X) Work.FTS.EllipticEst.Q0 :=
    hX.of_le (Nat.cast_le.mpr hij)
  have eT1 : Work.Spaces.mixed j i (fun z θ => a θ * X z θ) z θ = coefJetS a j i 0 X z θ :=
    mixed_coef_mul_pt hXi (ha.of_le (Nat.cast_le.mpr (by omega : i ≤ 2))) z θ hp
  have eT2 : Work.Spaces.mixed j i (fun z θ => b θ * Work.Spaces.Dz X z θ) z θ
      = coefJetS b (j + 1) i 0 X z θ := by
    have hbase : Work.Spaces.mixed j i (fun z θ => b θ * Work.Spaces.Dz X z θ) z θ
        = coefJetS b j i 0 (Work.Spaces.Dz X) z θ :=
      mixed_coef_mul_pt hDzX (hb.of_le (Nat.cast_le.mpr (by omega : i ≤ 2))) z θ hp
    rw [hbase, coefJetS, coefJetS]
    simp only [Nat.add_zero]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hY : ContDiffOn ℝ (j + (i - k) + 1) (Function.uncurry X) Work.FTS.EllipticEst.Q0 :=
      hX.of_le (Nat.cast_le.mpr (by omega : j + (i - k) + 1 ≤ 3))
    rw [mixed_Dz_shift (j := j) (i := i - k) (Y := X) hY z θ hp]
  have hcd : ContDiffOn ℝ i (fun p : ℝ × ℝ => c p.2 / Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 := by
    have h1 : ContDiffOn ℝ i (fun p : ℝ × ℝ => c p.2) Work.FTS.EllipticEst.Q0 :=
      hc.of_le (Nat.cast_le.mpr (by omega : i ≤ 2))
    have h2 : ContDiffOn ℝ i (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
    show ContDiffOn ℝ i ((fun p : ℝ × ℝ => c p.2) / (fun p : ℝ × ℝ => Real.sin (2 * p.2)))
      Work.FTS.EllipticEst.Q0
    exact h1.div h2 (fun p hp' => ne_of_gt (sin_two_pos_quad hp'))
  have eT3 : Work.Spaces.mixed j i (fun z θ => c θ * Work.Spaces.pth X z θ) z θ
      = coefJetS (fun θ => c θ / Real.sin (2 * θ)) j i 1 X z θ := by
    have hcong : Set.EqOn (Function.uncurry (fun z θ => c θ * Work.Spaces.pth X z θ))
        (Function.uncurry (fun z θ => (c θ / Real.sin (2 * θ)) * Work.Spaces.Dth X z θ))
        Work.FTS.EllipticEst.Q0 := by
      intro p hp'
      obtain ⟨z', θ'⟩ := p
      have hs : Real.sin (2 * θ') ≠ 0 := ne_of_gt (sin_two_pos_quad hp')
      simp only [Function.uncurry, Work.Spaces.Dth, Work.Spaces.pth]
      field_simp
    have hstep := mixed_congr_eqOn hcong j i hp
    have hDthX : ContDiffOn ℝ (i + j) (Function.uncurry (Work.Spaces.Dth X))
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_Dth_of_succ
        Work.FTS.EllipticEst.isOpen_Q0 (n := 2) hX).of_le (Nat.cast_le.mpr (by omega : i + j ≤ 2))
    have hbase : Work.Spaces.mixed j i
        (fun z θ => (c θ / Real.sin (2 * θ)) * Work.Spaces.Dth X z θ) z θ
        = coefJetS (fun θ => c θ / Real.sin (2 * θ)) j i 0 (Work.Spaces.Dth X) z θ :=
      mixed_coef_mul_pt hDthX hcd z θ hp
    rw [show Work.Spaces.mixed j i (fun z θ => c θ * Work.Spaces.pth X z θ) z θ
        = Work.Spaces.mixed j i
            (fun z θ => c θ / Real.sin (2 * θ) * Work.Spaces.Dth X z θ) z θ from hstep,
      hbase, coefJetS, coefJetS]
    simp only [Nat.add_zero]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hDth1 : Work.Spaces.Dth X = Work.Spaces.DthIter 1 X := by
      rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
    rw [hDth1]
    show (i.choose k : ℝ) * (Work.Spaces.DthIter k (fun _ (θ'' : ℝ) => c θ'' / Real.sin (2 * θ'')) z θ
          * Work.Spaces.DzIter j (Work.Spaces.DthIter (i - k) (Work.Spaces.DthIter 1 X)) z θ)
        = (i.choose k : ℝ) * (Work.Spaces.DthIter k (fun _ (θ'' : ℝ) => c θ'' / Real.sin (2 * θ'')) z θ
          * Work.Spaces.DzIter j (Work.Spaces.DthIter (i - k + 1) X) z θ)
    rw [Work.Spaces.DthIter_add_right (i - k) 1 X]
  show Work.Spaces.mixed j i
      (fun z θ => a θ * X z θ + b θ * Work.Spaces.Dz X z θ + c θ * Work.Spaces.pth X z θ) z θ
    = EJet a b c j i X z θ
  rw [hadd1, hadd2, eT1, eT2, eT3, EJet]

/-- `tan` is `C²` on the open quadrant. -/
theorem contDiffOn_tan_quad : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.tan p.2)
    Work.FTS.EllipticEst.Q0 := by
  have hsin : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.sin p.2) Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_sin.comp contDiff_snd).contDiffOn
  have hcos : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.cos p.2) Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_cos.comp contDiff_snd).contDiffOn
  have h3 : ContDiffOn ℝ 2 ((fun p : ℝ × ℝ => Real.sin p.2) / (fun p : ℝ × ℝ => Real.cos p.2))
      Work.FTS.EllipticEst.Q0 :=
    hsin.div hcos (fun p hp' => ne_of_gt (cos_pos_quad hp'))
  convert h3 using 1
  funext p
  rw [Pi.div_apply, Real.tan_eq_sin_div_cos]

end Work.FTS_RegExport.RXT.Slots.JetCalc
end
end
