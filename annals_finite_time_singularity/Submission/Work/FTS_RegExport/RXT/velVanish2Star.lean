import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.AeI1Fts.zibp_cut
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.H2W.Ae.TruncIdentAe
import Submission.Work.FTS.EllipticEst.H2W.Ae.aeSigmaSliceLower
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.TT.ESW.Tk_B_le_chain_uniform
import Submission.Work.FTS.EllipticEst.TT.Shim.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.TT.Shim.HkMem_pthIter2_EllResid
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.H2.ModalSol.Defs
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.LocData6.zfarR_jet_le6_of_jets
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.N4Fields.AngSmoothIntHelpers
import Submission.Work.FTS.Nonlinear.N4Fields.angmul_field_smooth
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.Pgs
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.OpenPkg.C4Factors
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.OpenPkg.l12_open_bundle
import Submission.Work.FTS.OpenPkg.radialMul_field
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EpsE4Thr.JepsJoint.Jeps_fam_continuous
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS.StrongPersist.N6.sliceAvg_le6
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
import Submission.Work.FTS.TransportS.T3SlotAux.Pointwise
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.BoxDataH.BoxUniform
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.FTS_RegExport.RXB.sup_bound_all_alpha
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.H2.T1Q.T1EasyContQ
import Submission.Work.H2.WPQ.hardy_slice_Aang
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.ProductRuleInW
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.aesm_HkIntegrand_quad
import Submission.Work.Spaces.continuousOn_HkIntegrand_Qd
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.CutFactorFderivZero
import Submission.Work.Stability.Cutoff
import Submission.Work.Stability.ZcutSmoothCompact
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.StabilityFar.Decay.hasDerivAt_bsK
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E1Norm.Main =====
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
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Two elementary inputs -/




/-! ## The squared `ℋⁿ`-bound for `E1` -/


end Work.FTS.CoercivityFix.Transfer.E1Norm
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.I1Ae.RIFMainB =====
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

/-! ## Continuity and a.e. measurability helpers on the open quadrant -/














end Work.FTS.EllipticEst.I1Ae
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Straight.CoerciveInput =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Straight

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. The straightened solution and its moment form -/

/-- The straightened solution `V = Ψ + Gsing α F · sin 2θ`. -/
def Vf (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ)

/-- The explicit moment form `W = Ψ - (15/4)·F_*(Ψ)·sin 2θ` of the straightened solution.  On
the open quadrant `W` agrees with `V` whenever the orthogonality condition holds
(`Vf_eq_Wf`). -/
def Wf (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Ψ z θ + (-(15 / 4)) * (Work.Elliptic.Fstar Ψ z * Real.sin (2 * θ))




/-! ## 2. Smoothness of the explicit form -/








/-! ## 3. The analytic facts about `F_*`, `L₁₂` and `Gsing` -/



/-! ## 4. The `ℋ^k`-memberships -/









/-! ## 5. The estimate -/


end Work.FTS.EllipticEst.Straight
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.VopSlot =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

set_option autoImplicit false

/-! ## The decomposition -/

/-- **The `Vop` slot's decomposition into its three pieces.** -/
theorem Vop_decomp {α : ℝ} {f Φs : ℝ → ℝ → ℝ} {E : (ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz₁ : DifferentiableAt ℝ (fun z' => Work.Construction.PhiTil α f (E f) z' θ) z)
    (hz₂ : DifferentiableAt ℝ (fun z' => Φs z' θ) z)
    (hz₃ : DifferentiableAt ℝ (fun z' => Work.Construction.PhiTil α (Work.Construction.Fstar α)
      Φs z' θ) z)
    (hz₄ : DifferentiableAt ℝ (fun z' => Work.Construction.Theta α (Work.Construction.Fstar α)
      z' θ) z)
    (hθ₁ : DifferentiableAt ℝ (fun θ' => Work.Construction.PhiTil α f (E f) z θ') θ)
    (hθ₂ : DifferentiableAt ℝ (fun θ' => Φs z θ') θ)
    (hθ₃ : DifferentiableAt ℝ (fun θ' => Work.Construction.PhiTil α (Work.Construction.Fstar α)
      Φs z θ') θ)
    (hθ₄ : DifferentiableAt ℝ (fun θ' => Work.Construction.Theta α (Work.Construction.Fstar α)
      z θ') θ) :
    Work.Construction.Vop (Work.Construction.PhiTil α f (fun z θ => Φs z θ + E f z θ)) z θ
      = Work.Construction.Vop (Work.Construction.PhiTil α f (E f)) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Vop (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ := by
  have hfun₁ : Work.Construction.PhiTil α f (fun z θ => Φs z θ + E f z θ)
      = fun z θ => Work.Construction.PhiTil α f (E f) z θ + Φs z θ := by
    funext z θ
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    ring
  have hfun₂ : Φs = fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
      + Work.Construction.Theta α (Work.Construction.Fstar α) z θ := by
    funext z θ
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    ring
  rw [hfun₁]
  have h₁ := (Work.FTS.EpsEngine.Rop_Uop_Vop_add (α := α) (z := z) (θ := θ)
    (Ψ₁ := Work.Construction.PhiTil α f (E f)) (Ψ₂ := Φs) hz₁ hz₂ hθ₁ hθ₂).2.2
  rw [h₁]
  have h₂ := (Work.FTS.EpsEngine.Rop_Uop_Vop_add (α := α) (z := z) (θ := θ)
    (Ψ₁ := Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)
    (Ψ₂ := Work.Construction.Theta α (Work.Construction.Fstar α)) hz₃ hz₄ hθ₃ hθ₄).2.2
  have hVΦ : Work.Construction.Vop Φs z θ
      = Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Vop (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ := by
    conv_lhs => rw [hfun₂]
    exact h₂
  rw [hVΦ]
  ring

/-! ## The two pieces' bounds -/

/-- **The `EllPkgGo` piece of the `Vop` slot.** -/
theorem ell_Vop_le {α Ce Cpt : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCpt : 0 ≤ Cpt)
    (hpt : ∀ g : Fn, ContDiffOn ℝ 4 (Function.uncurry g) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem α 4 g → ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ →
        θ < Real.pi / 2 →
        |Work.Spaces.mixed b a g z θ| ≤ Cpt * min z 1 * Work.Spaces.HkNorm α 4 g)
    {f : Fn} {E : Fn → Fn} (hf : Work.FTS.ClassC.ClassC α f)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Construction.Vop (Work.Construction.PhiTil α f (E f)) z θ|
      ≤ Cpt * (Ce * Work.FTS.Nonlin.Xn α f) * min z 1 := by
  have hU : Work.FTS.VocabO.HQo α 4
      (Work.Construction.Vop (Work.Construction.PhiTil α f (E f))) := (hEll f hf).1.V.1
  have hsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.Construction.PhiTil α f (E f))) := hU.1
  have hmem : Work.Spaces.HkMem α 4 (Work.Construction.Vop (Work.Construction.PhiTil α f (E f))) :=
    hU.2
  have h4 : ContDiffOn ℝ 4 (Function.uncurry
      (Work.Construction.Vop (Work.Construction.PhiTil α f (E f))))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsm 4
  have h := hpt _ h4 hmem 0 0 (by norm_num) z θ hz hθ.1 hθ.2
  simp only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right, Work.Spaces.DthIter_zero,
    Work.Spaces.DzIter_zero] at h
  refine h.trans ?_
  have hXn : Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.Construction.PhiTil α f (E f)))
      ≤ Ce * Work.FTS.Nonlin.Xn α f := (hEll f hf).1.V.2
  calc Cpt * min z 1 * Work.Spaces.HkNorm α 4
        (Work.Construction.Vop (Work.Construction.PhiTil α f (E f)))
      = Cpt * min z 1 * Work.FTS.Nonlin.Xn α
          (Work.Construction.Vop (Work.Construction.PhiTil α f (E f))) := by
        rw [Work.FTS.Nonlin.Xn]
    _ ≤ Cpt * min z 1 * (Ce * Work.FTS.Nonlin.Xn α f) := by
        refine mul_le_mul_of_nonneg_left hXn (by positivity)
    _ = Cpt * (Ce * Work.FTS.Nonlin.Xn α f) * min z 1 := by ring

/-- **The star piece of the `Vop` slot**, from the `V` field of `StarPkgo2`
(`WDp 4 (Vop (PhiTil α F_* Φs)) ≤ Cs α`) through `Work.FTS.OpenPkg.WDMem_of_WDp_le`. -/
theorem star_Vop_le {α Cs : ℝ} {Φs : ℝ → ℝ → ℝ}
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
        ≤ Cs * α := by
  intro z θ hz hθ0 hθ1
  exact Work.FTS.OpenPkg.WDMem_of_WDp_le hstar.V.1 hstar.V.2 0 0 (by norm_num) z θ hz hθ0 hθ1

/-! ## The assembly -/

/-- **The `Vop` slot of `EpsDecay`, with `C = 3`.** -/
theorem vop_slot_abs_le_three {α Cpt Ce Cs C₀ : ℝ} {f Φs : Fn} {E : Fn → Fn} {z θ : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hCpt : 0 ≤ Cpt) (hCe : 0 ≤ Ce) (hCs : 0 ≤ Cs) (hC₀ : 0 ≤ C₀)
    (hsmall : Cpt * (Ce * (C₀ * α ^ 2)) + Cs * α ≤ 1)
    (hdec : Work.Construction.Vop (Work.Construction.PhiTil α f
          (fun z θ => Φs z θ + E f z θ)) z θ
        = Work.Construction.Vop (Work.Construction.PhiTil α f (E f)) z θ
          + Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
          + Work.Construction.Vop (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ)
    (hE : |Work.Construction.Vop (Work.Construction.PhiTil α f (E f)) z θ|
        ≤ Cpt * (Ce * (C₀ * α ^ 2)) * min z 1)
    (hS : |Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
        ≤ Cs * α) :
    |Work.Construction.Vop (Work.Construction.PhiTil α f (fun z θ => Φs z θ + E f z θ)) z θ|
      ≤ 3 := by
  have hΘ := (Work.FTS.EpsEngine.Theta_Fstar_ops (α := α) hα hα1).2.1 z θ hz hθ.1 hθ.2
  -- the explicit piece is `c2m θ/(1+z)`, of absolute value `≤ 2`
  have hc2m : |Work.Construction.c2m θ| ≤ 2 := by
    have h1 : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
    have h2 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
    have h3 : |Real.cos (2 * θ) - Real.sin θ ^ 2| ≤ |Real.cos (2 * θ)| + Real.sin θ ^ 2 := by
      have h := abs_sub_le (Real.cos (2 * θ)) 0 (Real.sin θ ^ 2)
      rw [sub_zero, zero_sub, abs_neg, abs_of_nonneg (sq_nonneg (Real.sin θ))] at h
      exact h
    simp only [Work.Construction.c2m]
    linarith
  have hdiv : |Work.Construction.c2m θ / (1 + z)| ≤ 2 := by
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 + z), div_le_iff₀ (by linarith)]
    nlinarith [abs_nonneg (Work.Construction.c2m θ), hc2m]
  have hpiece : |Work.Construction.Vop (Work.Construction.Theta α (Work.Construction.Fstar α))
      z θ| ≤ 2 := by
    rw [hΘ]
    exact hdiv
  have hP : Cpt * (Ce * (C₀ * α ^ 2)) * min z 1 ≤ Cpt * (Ce * (C₀ * α ^ 2)) := by
    have h1 : min z 1 ≤ 1 := min_le_right _ _
    have h2 : 0 ≤ Cpt * (Ce * (C₀ * α ^ 2)) := by positivity
    calc Cpt * (Ce * (C₀ * α ^ 2)) * min z 1 ≤ Cpt * (Ce * (C₀ * α ^ 2)) * 1 :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = Cpt * (Ce * (C₀ * α ^ 2)) := mul_one _
  rw [hdec]
  calc |Work.Construction.Vop (Work.Construction.PhiTil α f (E f)) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Vop (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ|
      ≤ |Work.Construction.Vop (Work.Construction.PhiTil α f (E f)) z θ|
        + |Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
        + |Work.Construction.Vop (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ| := by
        refine (abs_add_le _ _).trans ?_
        exact add_le_add_left (abs_add_le _ _) _
    _ ≤ 3 := by linarith [hE.trans hP, hS, hpiece, hsmall]

end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.ZTracesAux.Dth_mixed_eq_gen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine.ZTracesAux

theorem Dth_mixed_eq_gen {f : ℝ → ℝ → ℝ} {N : ℕ}
    (hF : ContDiffOn ℝ N (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (b a : ℕ) (hab : a + b + 1 ≤ N) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ = Work.Spaces.mixed b (a + 1) f z θ := by
  have hy : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ⟩
  -- `f` is `C^{a+b+1}` on `Q0`, hence `D_θ^a f` is `C^{b+1}` there
  have hab2 : (b + 1 + a : ℕ) ≤ N := by omega
  have h1 : ContDiffOn ℝ (b + 1 + a) (Function.uncurry f) Work.FTS.EllipticEst.Q0 :=
    hF.of_le (Nat.cast_le.mpr hab2)
  have hfin : ContDiffOn ℝ (b + 1) (Function.uncurry (Work.Spaces.DthIter a f))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.contDiffOn_uncurry_DthIter_shift
      Work.FTS.EllipticEst.isOpen_Q0 a (b + 1) h1
  -- Clairaut at the finite order: `D_θ` commutes with `D_z^b`
  have hpt := (Work.FTS_RegExport.C4.Dth_DzIter_comm_fin b
      Work.FTS.EllipticEst.isOpen_Q0 hfin) hy
  rw [show Work.Spaces.mixed b a f
      = Work.Spaces.DzIter b (Work.Spaces.DthIter a f) from rfl]
  rw [show Work.Spaces.mixed b (a + 1) f
      = Work.Spaces.DzIter b (Work.Spaces.Dth (Work.Spaces.DthIter a f)) from rfl]
  simpa only [Function.uncurry] using hpt

end Work.FTS.EpsEngine.ZTracesAux
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.Subcut.Maj_facts_and_split =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.cc.Subcut

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000


end Work.FTS.GalBasis.cc.Subcut
end
-- ===== merged: Submission.Work.FTS.GalFields.Norm.RadA4.Maj_int_le_four =====
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
-- ===== merged: Submission.Work.FTS.GalLimit.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalLimit

open Work.FTS.Galerkin (Fn Fam slice galFun galFam galField IsGalFam ConvLocUnif IsDynWeakOn
  IsDynEqOn RegPkg gdot dynLin dynRHS Slab ProfileBdd ProfileEquicont)
open Work.FTS.Nonlin (GalBasis GalClass UnifIP RegQ CoerAdm PsiCan Xn BdryTraces)
open Work.FTS.VocabO (HQo EllPkgGo)
open Work.FTS.VocabO2 (StarPkgo2)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The coefficient ball -/

/-- The Euclidean ball of radius `r` in `Fin n → ℝ` in the **`ℓ²` form** — the shape the
coercivity of the inner product actually controls (`clo·|f|²₄ ≤ IP(f,f) = Σ cₖ²`), as opposed
to the sup-norm ball `Metric.closedBall 0 R` whose `Σc²` can reach `4nR²`. -/
def EBall (n : ℕ) (r : ℝ) : Set (Fin n → ℝ) := {c | ∑ k, c k ^ 2 ≤ r ^ 2}

theorem mem_EBall {n : ℕ} {r : ℝ} {c : Fin n → ℝ} : c ∈ EBall n r ↔ ∑ k, c k ^ 2 ≤ r ^ 2 :=
  Iff.rfl

/-! ## The density of the Galerkin span, and the class of the test functions -/



/-! ## Linearity of the concrete `IP4` on the honest class -/




/-! ## The corrected elliptic law -/

/-- **The elliptic (Biot–Savart) law with the boundary conditions only for `z ≥ 0`.**
`IsBslSolPos α F Ψ` asks `bslOp α Ψ = F` on the open quadrant, the Dirichlet conditions
`Ψ z 0 = Ψ z (π/2) = 0` only for `z ≥ 0`, and the decay `Ψ z θ → 0` as `z → ∞`.

The restriction to `z ≥ 0` is forced by the compactness convergence: `ConvLocUnif` pins the
Galerkin families only on the slab `[0,∞) × [0,π/2] × [0,∞)`, so nothing at all is known about the
elliptic law, or the boundary values, for `z < 0` (`Work.Elliptic.IsBslSol` asks them for all `z`,
which is why it cannot be a limit law — see the integration audit §2). -/
def IsBslSolPos (α : ℝ) (F Ψ : Fn) : Prop :=
  (∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 → Work.Elliptic.bslOp α Ψ z θ = F z θ) ∧
    (∀ z, 0 ≤ z → Ψ z 0 = 0) ∧ (∀ z, 0 ≤ z → Ψ z (π / 2) = 0) ∧
    (∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => Ψ z θ) atTop (𝓝 0))



theorem IsBslSolPos.bsl {α : ℝ} {F Ψ : Fn} (h : IsBslSolPos α F Ψ) {z : ℝ} (hz : 0 < z)
    {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < π / 2) : Work.Elliptic.bslOp α Ψ z θ = F z θ :=
  h.1 z hz θ hθ hθ'

/-! ## The extra regularity class of the two sides of the equation -/


/-! ## The fundamental lemma for the Galerkin span -/


/-! ## The corrected passage-to-the-limit inputs

All four are the fields of the corrected Galerkin bundle in the form the Open3 re-run needs: the
stream functions are allowed to converge only along a *further* subsequence, the regularity package
and the datum are asked only where the compactness convergence pins them, and the elliptic law is
`IsBslSolPos`. -/





/-- The Lipschitz form of the field bound, on the `ℓ²`-ball `EBall n (2R)`. -/
def hField_lip' (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) (Φs : Fn) (EllSol : Fn → Fn)
    (R : ℝ) (K : ℕ → ℝ) (hK : ∀ n, 0 ≤ K n) : Prop :=
  ∀ (n : ℕ) (τ : ℝ), 0 ≤ τ →
    LipschitzOnWith ⟨K n, hK n⟩ (galField α (IP α) φ n (PsiCan Φs EllSol) τ) (EBall n (2 * R))

end Work.FTS.GalLimit
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.Goals =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.NonlinRows

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The three group obligations (the `rowsN0`/`rowsN`/`rowsAux` fields of `N4Rows'`) -/






/-! ## The individual `NRows` goals still to be proved -/

















/-! ## The two remaining obligations in the upgraded (`StarPkgo2`) context -/



end Work.FTS.NonlinRows
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows.NRow10aux

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

/-!
# Multiplication by the bounded radial factor `φ(z) = z/(1+z)` costs nothing in `ℋ⁴`

The statement `Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk` is assembled from the three
pieces of the `NRow10aux` chain:

* `radialBounded_majorant` — the pointwise majorant
  `HkIntegrand α 4 (r·g) ≤ K · HkIntegrand α 4 g` for a radial factor `r` with
  `|D_z^b r| ≤ 1`, `b ≤ 4`;
* `phiSelfFacts` — those bounds for `φ` (plus `SmoothOpen φ`);
* `hkmem_of_majorant` — transport of `HkMem`/`HkSq` along a pointwise majorant.

The constant is `C = √K + 1`, which works because `HkMem α 4 g` makes `HkSq α 4 g ≥ 0`
honest and `HkNorm = √(HkSq)`.
-/

/-- At `z = 0` the weight `w` vanishes (`w 0 = (1+0)²/0² = 1/0 = 0`, Lean's totalised
division), so *every* term of the weighted `ℋ^k`-integrand vanishes there. -/
theorem HkIntegrand_zero (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta, Work.Spaces.w]
  simp

theorem mul_phi_Hk :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ} {g : ℝ → ℝ → ℝ}, 0 < α → α ≤ 1 →
      Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => z / (1 + z) * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * g z θ) ≤ C * Work.FTS.Nonlin.Xn α g := by
  obtain ⟨K, hKpos, hK⟩ := radialBounded_majorant
  have hphiSO : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => phiF z) := phiSelf_smoothOpen
  have hphiBnd : ∀ b : ℕ, b ≤ 4 → ∀ z : ℝ, 0 ≤ z →
      |Work.Elliptic.DzdIter b phiF z| ≤ 1 := fun b hb z hz => phiSelf_DzdIter_bound_phiF b hb z hz
  refine ⟨Real.sqrt K + 1, by positivity, ?_⟩
  intro α g hα hα1 hg
  obtain ⟨hgSO, hgm⟩ := hg
  -- the product is again smooth on the open quadrant
  have hSO : Work.FTS.EllipticEst.SmoothOpen (fun z θ => phiF z * g z θ) := by
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => p.1 / (1 + p.1)) Work.FTS.EllipticEst.Q0 := hphiSO
    have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => g p.1 p.2) Work.FTS.EllipticEst.Q0 := hgSO
    exact h1.mul h2
  -- the pointwise majorant, including the degenerate slice `z = 0`
  have hmaj : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.Spaces.HkIntegrand α 4 (fun z θ => phiF z * g z θ) z θ
        ≤ K * Work.Spaces.HkIntegrand α 4 g z θ := by
    intro z hz θ hθ
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · rw [← hz0]
      have h0 : Work.Spaces.HkIntegrand α 4 (fun z θ => phiF z * g z θ) 0 θ = 0 :=
        HkIntegrand_zero α 4 _ θ
      have h1 : Work.Spaces.HkIntegrand α 4 g 0 θ = 0 := HkIntegrand_zero α 4 g θ
      rw [h0, h1, mul_zero]
    · exact hK α phiF g hphiSO hgSO hphiBnd z θ hzpos hθ.1 hθ.2
  -- transport of `HkMem` and of the norm along the majorant
  obtain ⟨hHkMem, hHkSq⟩ := hkmem_of_majorant α 4 hKpos.le hSO hgm hmaj
  refine ⟨hHkMem, ?_⟩
  have hXn : 0 ≤ Work.FTS.Nonlin.Xn α g := Real.sqrt_nonneg _
  calc Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * g z θ)
      = Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => z / (1 + z) * g z θ)) := rfl
    _ ≤ Real.sqrt (K * Work.Spaces.HkSq α 4 g) := Real.sqrt_le_sqrt hHkSq
    _ = Real.sqrt K * Real.sqrt (Work.Spaces.HkSq α 4 g) := Real.sqrt_mul hKpos.le _
    _ = Real.sqrt K * Work.FTS.Nonlin.Xn α g := rfl
    _ ≤ (Real.sqrt K + 1) * Work.FTS.Nonlin.Xn α g := by
        apply mul_le_mul_of_nonneg_right _ hXn
        linarith [Real.sqrt_nonneg K]

end

end Work.FTS.NonlinRows.NRow10aux
end
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow2 =====
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

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The slot-wise Cauchy–Schwarz lemma (local copy of the tool of `row2_bound`) -/

/-- Cauchy–Schwarz for a binomial slot sum: `(∑ c_b(x_by_b))² ≤ 256·card·Kc·∑ y_b²` when the
coefficients `c_b` are bounded by `16` and the first factors satisfy `x_b² ≤ Kc`. -/
private theorem slot_sum_sq_le {ι : Type*} (s : Finset ι) (c x y : ι → ℝ) {Kc : ℝ} (hK : 0 ≤ Kc)
    (hc : ∀ b ∈ s, |c b| ≤ 16) (hx : ∀ b ∈ s, (x b) ^ 2 ≤ Kc) :
    (∑ b ∈ s, c b * (x b * y b)) ^ 2 ≤ 256 * (s.card : ℝ) * Kc * ∑ b ∈ s, (y b) ^ 2 := by
  have h1 : (∑ b ∈ s, c b * (x b * y b)) ^ 2
      ≤ (s.card : ℝ) * ∑ b ∈ s, (c b * (x b * y b)) ^ 2 :=
    _root_.sq_sum_le_card_mul_sum_sq
  have h2 : ∑ b ∈ s, (c b * (x b * y b)) ^ 2 ≤ ∑ b ∈ s, 256 * (Kc * (y b) ^ 2) := by
    refine Finset.sum_le_sum fun b hb => ?_
    have hc2 : (c b) ^ 2 ≤ 256 := by
      have h := hc b hb
      nlinarith [sq_nonneg (c b), sq_abs (c b), abs_nonneg (c b)]
    have hx2 := hx b hb
    have hy2 : 0 ≤ (y b) ^ 2 := sq_nonneg _
    have hxy : (x b) ^ 2 * (y b) ^ 2 ≤ Kc * (y b) ^ 2 :=
      mul_le_mul_of_nonneg_right hx2 hy2
    have hcx : (c b) ^ 2 * ((x b) ^ 2 * (y b) ^ 2) ≤ 256 * (Kc * (y b) ^ 2) := by
      have h1 : (c b) ^ 2 * ((x b) ^ 2 * (y b) ^ 2) ≤ 256 * ((x b) ^ 2 * (y b) ^ 2) :=
        mul_le_mul_of_nonneg_right hc2 (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      calc (c b) ^ 2 * ((x b) ^ 2 * (y b) ^ 2) ≤ 256 * ((x b) ^ 2 * (y b) ^ 2) := h1
        _ ≤ 256 * (Kc * (y b) ^ 2) := mul_le_mul_of_nonneg_left hxy (by norm_num)
    calc (c b * (x b * y b)) ^ 2 = (c b) ^ 2 * ((x b) ^ 2 * (y b) ^ 2) := by ring
      _ ≤ 256 * (Kc * (y b) ^ 2) := hcx
  have h3 : ∑ b ∈ s, 256 * (Kc * (y b) ^ 2) = 256 * Kc * ∑ b ∈ s, (y b) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  calc (∑ b ∈ s, c b * (x b * y b)) ^ 2
      ≤ (s.card : ℝ) * ∑ b ∈ s, (c b * (x b * y b)) ^ 2 := h1
    _ ≤ (s.card : ℝ) * (256 * Kc * ∑ b ∈ s, (y b) ^ 2) :=
        mul_le_mul_of_nonneg_left (h2.trans (le_of_eq h3)) (Nat.cast_nonneg _)
    _ = 256 * (s.card : ℝ) * Kc * ∑ b ∈ s, (y b) ^ 2 := by ring


end Work.FTS.NonlinRows
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow3 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

set_option linter.unusedVariables false


end Work.FTS.NonlinRows
end
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Local helpers (pointwise and `ℋ⁴`-level facts about the factors of row 5)

Row 5 of the §8 table is the piece `N₀₅ᵃ = -c2m(θ)·L₁₂(g)(z)·D_zF_*`, i.e. the product of the
`𝒲^{4,∞}`-factor `D_zF_*` (with norm `≤ Cα`, `Work.FTS.Nonlin.DzFstar_W`) with the `ℋ⁴`-coefficient
`c2m(θ)·L₁₂(g)(z)`.  The plan is therefore the `wprod` clause of `N4Norm'` (which prices the
`𝒲^{4,∞}`-factor by `α^{-1/2}·α = √α` and yields both the honesty and the bound of the piece),
applied to the coefficient `c2m·L₁₂(g)`, whose `ℋ⁴`-honesty and norm bound come from
`Work.FTS.OpenPkg.angmul_field` (multiplication by the bounded angular profile `c2m` is honest
with an absolute constant, so no knowledge of `Ci` is needed) together with `N4Norm'.l12H`. -/

/-- `c2m(θ) = cos 2θ - sin²θ` is `C^∞` on the open quadrant. -/
theorem smoothOpen_c2m : Work.FTS.EllipticEst.SmoothOpen
    (fun (_ : ℝ) (θ : ℝ) => Work.Construction.c2m θ) :=
  Work.FTS.EllipticEst.smoothOpen_of_forall fun n => Work.FTS.OpenPkg.contDiffOn_c2m_Q0 n

/-- The `D_θ`-iterates of `c2m` are `O(sin 2θ)` on `Iθ` — the form needed by
`Work.FTS.OpenPkg.angmul_field` with the profile bound `Ca = 1000`. -/
theorem DthIter_c2m_le_sin (i : ℕ) (hi : 1 ≤ i) (hi4 : i ≤ 4) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Construction.c2m θ') 0 θ|
      ≤ 1000 * Real.sin (2 * θ) := by
  have h := Work.FTS.Nonlinear.Pieces.DthIter_c2m_le i hi hi4 θ
  have hs0 : 0 ≤ Real.sin (2 * θ) := by
    refine Real.sin_nonneg_of_mem_Icc ⟨?_, ?_⟩
    · linarith [hθ.1]
    · linarith [hθ.2, Real.pi_pos]
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hsq : (Real.sin (2 * θ)) ^ (2 : ℝ) ≤ Real.sin (2 * θ) := by
    rw [Real.rpow_two]
    nlinarith
  have h1000 : 1000 * (Real.sin (2 * θ)) ^ (2 : ℝ) ≤ 1000 * Real.sin (2 * θ) :=
    mul_le_mul_of_nonneg_left hsq (by norm_num)
  linarith [h]

/-- Negation preserves `HkMem` (a local copy, to avoid depending on the module
`Work.FTS.EllipticEst.HypAPI`). -/
theorem HkMem_neg' (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ} (h : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k (-f) := by
  obtain ⟨h1, h2⟩ := h
  have hfac : ∀ z θ, Work.Spaces.HkIntegrand α k (-f) z θ = Work.Spaces.HkIntegrand α k f z θ :=
    fun z θ => congrFun (congrFun (Work.FTS.EllipticEst.HkIntegrand_neg α k f) z) θ
  refine ⟨fun z hz => ?_, ?_⟩
  · rw [show (fun θ => Work.Spaces.HkIntegrand α k (-f) z θ)
          = (fun θ => Work.Spaces.HkIntegrand α k f z θ) from funext fun θ => hfac z θ]
    exact h1 z hz
  · have hIθ : (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (-f) z θ)
        = (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) :=
      funext fun z => MeasureTheory.setIntegral_congr_fun
        (by show MeasurableSet (Set.Icc (0 : ℝ) (Real.pi / 2)); exact measurableSet_Icc)
        (fun θ _ => hfac z θ)
    rw [hIθ]
    exact h2


end Work.FTS.NonlinRows
end
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Row 6 of the §8 table, in the primed vocabulary

`N₀₅ᵇ = -c2m(θ)·L₁₂(g)·D_z g`, priced by the `D_z`-transport clause `N4Extra'.t2`
(`VocabO.T2Clause`), i.e. by the flat angular coefficient norm `CoefTh 1`.

The piece is written as the product `fcoef · D_z g` with the `θ`-dependent coefficient
`fcoef = fun z θ => -1 * (c2m θ * L₁₂(g)(z))`, so that

* the `ℋ⁴`-honesty comes from the interface product rule `N4Norm'.prod` applied to
  `fcoef` (angular coefficient `c2m` times a radial factor, priced by
  `OpenPkg.angmul_field`) and to `D_z g` (`HkMem_Dz_quad`);
* the pairing is the clause `t2`, whose hypotheses are `SmoothOpen fcoef`,
  `HkMem α 4 fcoef`, `CoefThMem 1 fcoef`, `RegQ α 4 g`, `HkMem α 5 g`, `DecayAll 4 g`.

The only non-trivial estimate is the bound of the flat angular norm: `pth fcoef` is the
product of `∂_θ c2m(θ) = -3 sin 2θ` and the radial factor `L₁₂(g)`, whose `D`-iterates up
to order one are bounded by `K·|g|_{ℋ⁴}` (the angular-moment bounds
`L12_dzdIter_abs_le`).
-/

namespace Work.FTS.NonlinRows

open scoped Real Topology

noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Work.FTS.Galerkin (Fn)

/-! ## The angular profile `3 sin 2θ` and its basic calculus -/

/-- `∂_θ c2m(θ) = -3 sin 2θ`; the profile `3 sin 2θ` is the angular factor of `pth (coeff6 g)`. -/
private def Aang : ℝ → ℝ := fun θ => 3 * Real.sin (2 * θ)

private theorem hasDerivAt_Aang (θ : ℝ) : HasDerivAt Aang (6 * Real.cos (2 * θ)) θ := by
  have h : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * (2 * 1)) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul (2 : ℝ))
  have h3 : HasDerivAt (fun t : ℝ => 3 * Real.sin (2 * t))
      (3 * (Real.cos (2 * θ) * (2 * 1))) θ := h.const_mul 3
  have h3' : HasDerivAt Aang (3 * (Real.cos (2 * θ) * (2 * 1))) θ := h3
  rwa [show (3 : ℝ) * (Real.cos (2 * θ) * (2 * 1)) = 6 * Real.cos (2 * θ) from by ring] at h3'

private theorem abs_Aang_le (θ : ℝ) : |Aang θ| ≤ 3 := by
  have h : |Real.sin (2 * θ)| ≤ 1 := Real.abs_sin_le_one _
  simp only [Aang, abs_mul]
  have h3 : |(3 : ℝ)| = 3 := by norm_num
  rw [h3]
  linarith

private theorem abs_dthU_Aang_le (θ : ℝ) : |Work.Spaces.dthU Aang θ| ≤ 6 := by
  have hd : deriv Aang θ = 6 * Real.cos (2 * θ) := (hasDerivAt_Aang θ).deriv
  have hs : |Real.sin (2 * θ)| ≤ 1 := Real.abs_sin_le_one _
  have hc : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  show |Real.sin (2 * θ) * deriv Aang θ| ≤ 6
  rw [hd, abs_mul, abs_mul]
  have h6 : |(6 : ℝ)| = 6 := by norm_num
  rw [h6]
  nlinarith [abs_nonneg (Real.sin (2 * θ)), abs_nonneg (Real.cos (2 * θ))]

/-! ## The angular smoothness of `c2m` -/

private theorem contDiff_c2m (n : WithTop ℕ∞) : ContDiff ℝ n Work.Construction.c2m := by
  show ContDiff ℝ n (fun θ : ℝ => Real.cos (2 * θ) - Real.sin θ ^ 2)
  exact (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).sub (Real.contDiff_sin.pow 2)

private theorem differentiableAt_c2m (θ : ℝ) : DifferentiableAt ℝ Work.Construction.c2m θ := by
  show DifferentiableAt ℝ (fun t : ℝ => Real.cos (2 * t) - Real.sin t ^ 2) θ
  fun_prop

private theorem smoothOpen_c2m_ang :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Work.Construction.c2m θ) := by
  rw [Work.FTS.EllipticEst.SmoothOpen]
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (fun p : ℝ × ℝ => Work.Construction.c2m p.2) Work.FTS.EllipticEst.Q0
  exact (contDiff_c2m Work.Stability.smoothOrder).contDiffOn.comp contDiffOn_snd
    (fun p _ => Set.mem_univ p.2)

/-! ## The coefficient `fcoef = -c2m(θ)·L₁₂(g)(z)` -/

/-- The `θ`-dependent coefficient of `N₀₅ᵇ`. -/
private abbrev coeff6 (g : Fn) : Fn :=
  fun z θ => (-1 : ℝ) * (Work.Construction.c2m θ * Work.Construction.L12 g z)

/-- `∂_θ` of an angular `×` radial product. -/
private theorem pth_ang_rad (a : ℝ → ℝ) (r : ℝ → ℝ) (ha : ∀ θ, DifferentiableAt ℝ a θ) :
    Work.Spaces.pth (fun z θ => a θ * r z) = fun z θ => deriv a θ * r z := by
  funext z θ
  show deriv (fun θ' => a θ' * r z) θ = deriv a θ * r z
  exact deriv_mul_const (ha θ) (r z)

/-- `∂_θ (coeff6 g) = 3 sin(2θ)·L₁₂(g)(z)`. -/
private theorem pth_coeff6 (g : Fn) :
    Work.Spaces.pth (coeff6 g) = fun z θ => Aang θ * Work.Construction.L12 g z := by
  have hcongr : coeff6 g = fun z θ =>
      (fun θ' => (-1 : ℝ) * Work.Construction.c2m θ') θ
        * (fun z' => Work.Construction.L12 g z') z := by
    funext z θ
    simp only [coeff6]
    ring
  rw [hcongr, pth_ang_rad (fun θ' => (-1 : ℝ) * Work.Construction.c2m θ')
    (fun z' => Work.Construction.L12 g z')
    (fun θ => (differentiableAt_c2m θ).const_mul (-1))]
  funext z θ
  show deriv (fun θ' => (-1 : ℝ) * Work.Construction.c2m θ') θ
      * Work.Construction.L12 g z = Aang θ * Work.Construction.L12 g z
  rw [deriv_const_mul (-1) (differentiableAt_c2m θ),
    Work.FTS.Nonlinear.FstarPkg.dthU_c2m_deriv θ]
  simp only [Aang]
  ring

/-- The mixed iterates of `∂_θ (coeff6 g)`. -/
private theorem mixed_pth_coeff6 (g : Fn) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j i (Work.Spaces.pth (coeff6 g)) z θ
      = Work.Spaces.DthIter i (fun _ θ' => Aang θ') 0 θ
        * Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 g z) z := by
  rw [pth_coeff6]
  exact Work.FTS.Nonlinear.Pieces.mixed_ang_rad Aang
    (fun z => Work.Construction.L12 g z) j i z θ

/-- The pointwise bound of the constituents of `CoefTh 1 (coeff6 g)`. -/
private theorem mixed_pth_coeff6_le {M : ℝ} (hM : 0 ≤ M) {g : Fn}
    (hLpt : ∀ b : ℕ, b ≤ 4 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z| ≤ M)
    {b i : ℕ} (hbi : b + i ≤ 1) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    |Work.Spaces.mixed b i (Work.Spaces.pth (coeff6 g)) z θ| ≤ 6 * M := by
  have hDi : |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Aang θ') 0 θ| ≤ 6 := by
    have hi1 : i ≤ 1 := by omega
    interval_cases i
    · simp only [Work.Spaces.DthIter_zero]
      exact le_trans (abs_Aang_le θ) (by norm_num)
    · rw [Work.FTS.LocData.DthIter_rad_eq 1 Aang 0 θ, Function.iterate_one]
      exact abs_dthU_Aang_le θ
  have hDj : |Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z| ≤ M :=
    hLpt b (by omega) z hz
  rw [mixed_pth_coeff6]
  rw [abs_mul]
  exact mul_le_mul hDi hDj (abs_nonneg _) (by norm_num)

/-- The `supAbsO`-bound of the constituents of `CoefTh 1 (coeff6 g)`. -/
private theorem sup_mixed_pth_coeff6 {M : ℝ} (hM : 0 ≤ M) {g : Fn}
    (hLpt : ∀ b : ℕ, b ≤ 4 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z| ≤ M)
    {b i : ℕ} (hbi : b + i ≤ 1) :
    Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth (coeff6 g))) ≤ 6 * M :=
  Work.FTS.H2.supAbsO_le (fun z θ hz hθ0 hθ1 => mixed_pth_coeff6_le hM hLpt hbi hz hθ0 hθ1)

/-- `CoefTh 1 f ≤ 4 K` from a uniform bound `K` on the three constituents. -/
private theorem coefTh_one_le_of_sup {f : ℝ → ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ b i : ℕ, b + i ≤ 1 →
      Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f)) ≤ K) :
    Work.FTS.VocabO.CoefTh 1 f ≤ 4 * K := by
  have hterm : ∀ b ∈ Finset.range 2, ∀ i ∈ Finset.range 2,
      (if b + i ≤ 1 then
        Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f)) else 0) ≤ K := by
    intro b _ i _
    by_cases hc : b + i ≤ 1
    · rw [if_pos hc]; exact h b i hc
    · rw [if_neg hc]; exact hK
  unfold Work.FTS.VocabO.CoefTh
  refine le_trans (Finset.sum_le_sum fun b hb => Finset.sum_le_sum fun i hi =>
    hterm b hb i hi) ?_
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact le_of_eq (by ring)

/-! ## Row 6 -/


end

end Work.FTS.NonlinRows
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Row22 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option maxHeartbeats 1600000

/-! ## Row 22 of the §8 table in the open-quadrant (primed) vocabulary

`Work.FTS.Nonlin.N4sg α g = -(1/2)·FK(F_*)·D_θ g` is the slot of the transport estimate in which
the coefficient `-(1/2)·FK(F_*)` is a function of `z` alone and the derivative `D_θ g` falls on
the test function.  The relevant clause of the primed `IP`-interface is `N4Extra'.t4`,

  `|IP α (f·D_θ g) g| ≤ Ct·α^{-1/2}·WDp 4 f·|g|²`,

so everything reduces to the open-quadrant `D`-sup norm `WDp 4` of the radial coefficient.

The two facts needed about the coefficient, both established below:

* `FK (F_*(α)) z = α·(2z/(1+z)²) = α·2·hKer z` (`FstarPkg.FK_Fstar`), so the coefficient is
  `-α·hKer`, a constant multiple of the radial profile `hKer`;
* `WDp 4 (c·hKer) ≤ 200·C_W·|c|` (`hKerConstWlInf` for the `𝒲^{4,∞}`-membership and
  `WDp_le_WlInf` for the comparison `WDp ≤ C_W·WlInf`).

The loss `α^{-1/2}·α = √α` is what produces the `√α` of the stated bound, with the constant
`K = Ct·C_W·200 + 1` (positive because `Ct > 0`).

### The `ℋ⁴`-honesty conjunct

`N₄^{sg} = (-α·hKer)·D_θ g` is a `𝒲^{4,∞}`-coefficient times `D_θ g`, so the mixed product rule
`N4Norm'.wprod` applies (once `D_θ g ∈ ℋ⁴`, which follows from `RegQ α 5 g` by
`CoercivityFix.QuadPorts.RegQ_dth`).

The hypotheses `StarPkgo α Cs Φs` and `EllPkgGo α Ce g Φg` are not needed for this row;
`GalClass α g` is used only through `galClass_regQ4` and the `RegQ α 5 g` slice of its
`RegQ α 6`-membership.
-/



end Work.FTS.Nonlinear.Open
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Row4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false


end Work.FTS.Nonlinear.Open
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.Row7 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false


end Work.FTS.Nonlinear.Open
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Open.smoothOpen_FK_radial =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Open


end Work.FTS.Nonlinear.Open
end
-- ===== merged: Submission.Work.FTS.StrongEps.ClassCRHS.StarAtomsFK =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.ClassCRHS

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

/-- `SmoothOpen` is preserved by multiplication of the angular variable by a constant. -/
private theorem smoothOpen_ang_const_mul {c : ℝ} {a : ℝ → ℝ}
    (ha : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ)) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => c * a θ) :=
  ContDiffOn.const_smul (𝕜 := ℝ) c ha

/-- **The two `F_*`-products with the angular moment `FK (F_*)` are `ℋ⁴`-honest with bounded
`ℋ⁴`-norm (uniformly in `α ∈ (0,1]`).**

`FK (F_*) z = (F_*, K)_{L²_θ}(z) = ∫_θ F_* z θ · K(θ)` is the angular moment of the fundamental
profile; `Work.FTS.Nonlin.FK_Fstar` gives the explicit value
`FK (F_*) z = α·2z/(1+z)² = 2α·hKer z` where `hKer z = z/(1+z)²` (`Work.Spaces.hKer`), and
`F_* = α(Γ/c)·2hKer`, `D_θF_* = α(D_θΓ/c)·2hKer`.

Route: both products are separable angular `×` radial:
* `FK(F_*)·D_θF_* = (D_θΓ/c)(θ) · (4α² hKer²)(z)`,
* `FK(F_*)·F_*  = (Γ/c)(θ) · (4α² hKer²)(z)`,
so `Work.FTS.Nonlinear.Open.AngRadHkMem` applies (with the angular majorant
`G = Γ·(α + sin 2θ)` of `Row23`, i.e. `gamWeightInt`'s sharp data, and the radial input
`hkerSq_radial_alt` composed with `HkMem_const_mul`) and the norm bound follows from
`Work.FTS.Nonlinear.Pieces.RNP.Xn_ang_rad_le_gen`.  The pattern is `Row23` (which does
`N4ss = -(2α²/c)dθUΓ·hKer²`) and `NRow26`.  The constant may depend on `α` but must be uniform
over `α ∈ (0,1]`. -/
theorem StarAtomsFK : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
    Work.FTS.VocabO.HQo α 4 (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
      * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ∧
    Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
      * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ≤ C ∧
    Work.FTS.VocabO.HQo α 4 (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
      * Work.Construction.Fstar α z θ) ∧
    Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
      * Work.Construction.Fstar α z θ) ≤ C := by
  obtain ⟨Cr, hCrpos, hCr⟩ := Work.FTS.Nonlinear.Pieces.RNP.hkerSq_radial_alt
  obtain ⟨Cg, hCgpos, hCg⟩ := Work.FTS.Nonlinear.Pieces.RNP.dthU_pow_Gam_sharp
  obtain ⟨M, hMpos, hM⟩ := Work.FTS.Nonlinear.Pieces.RNP.gamWeightInt
  -- the two constants produced by the angular `×` radial engine, one for each product
  set K1 : ℝ := Real.sqrt ((160 / 3) ^ 2 * 10000 + 4 * (40 * Cg) ^ 2 * M) * Cr with hK1
  set K2 : ℝ := Real.sqrt (40 ^ 2 * 10000 + 4 * (160 / 3 + 40 * Cg) ^ 2 * M) * Cr with hK2
  have hK1nn : 0 ≤ K1 := by
    rw [hK1]; exact mul_nonneg (Real.sqrt_nonneg _) hCrpos.le
  have hK2nn : 0 ≤ K2 := by
    rw [hK2]; exact mul_nonneg (Real.sqrt_nonneg _) hCrpos.le
  refine ⟨K1 + K2 + 1, by linarith, fun α hαIoc => ?_⟩
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  -- the normalisation constant `c(α) ∈ [1/10, 10]`
  have hcge : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hc4 : 4 * α ^ 2 / Work.Spaces.c α ≤ 40 * α ^ 2 := by
    rw [div_le_iff₀ hcpos]; nlinarith [hcge, sq_nonneg α, hα]
  have hc4nn : (0 : ℝ) ≤ 4 * α ^ 2 / Work.Spaces.c α := div_nonneg (by positivity) hcpos.le
  have hDle40 : 4 * α ^ 2 / Work.Spaces.c α ≤ 40 := by
    have hα2 : α ^ 2 ≤ 1 := (pow_le_one₀ hα.le hα1 : α ^ 2 ≤ 1)
    nlinarith [hc4, sq_nonneg α]
  have hα3 : α ^ 3 ≤ 1 := (pow_le_one₀ hα.le hα1 : α ^ 3 ≤ 1)
  -- ### the radial profile `r = hKer²` and its `ℋ⁴`-data
  set r : ℝ → ℝ := fun z => (Work.Spaces.hKer z) ^ 2 with hr
  have hr_sm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => r z) := by
    rw [hr]
    exact Work.FTS.Nonlinear.Open.row23_smoothOpen_radial
      (fun n => (Work.FTS.Nonlinear.Open.row23_contDiffOn_hKer n).pow 2)
  obtain ⟨hrmemR, hXnR⟩ := hCr α hα hα1
  have hrmem : Work.Spaces.HkMem α 4 (fun z (_ : ℝ) => r z) := by rw [hr]; exact hrmemR
  have hXnR' : Work.FTS.Nonlin.Xn α (fun z (_ : ℝ) => r z) ≤ Cr := by rw [hr]; exact hXnR
  -- ### the sharp angular majorant `G = Γ·(α + sin 2θ)`
  set G : ℝ → ℝ := fun θ => Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) with hG
  have hGnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ G θ := by
    intro θ hθ
    have h1 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
    have h2 : 0 ≤ Real.sin (2 * θ) :=
      Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
    rw [hG]; positivity
  obtain ⟨hI1raw, hm1raw⟩ := hM α hα hα1
  have hGae : (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
      = fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2 * (α + Real.sin (2 * θ)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ := by
    funext θ; rw [hG]; ring
  have hI1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ := by
    rw [hGae]; exact hI1raw
  have hm1 : ∫ θ in Work.Spaces.Iθ, G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ ≤ M := by
    rw [hGae]; exact hm1raw
  -- ### product 1: `FK(F_*)·D_θF_* = a₁(θ)·r(z)` with `a₁ = (4α²/c)·D_θΓ`
  set a1 : ℝ → ℝ := fun θ => (4 * α ^ 2 / Work.Spaces.c α)
    * Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ with ha1
  have ha1_sm : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a1 θ) := by
    rw [ha1]
    exact smoothOpen_ang_const_mul (Work.FTS.Nonlinear.Open.row23_smoothOpen_dthU_Gam α)
  have ha1_0 : ∀ θ ∈ Work.Spaces.Iθ, |a1 θ| ≤ 160 / 3 := by
    intro θ hθ
    rw [ha1]
    have hΓ0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
    have hΓ1 : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
    have hdth := Work.FTS.Nonlinear.Pieces.RNP.dthIter_one_Gam_le hα hα1 θ hθ
    have hrepr : Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ
        = Work.Spaces.DthIter 1 (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ := by
      rw [Work.FTS.LocData.DthIter_rad_eq 1 (fun t => Work.Spaces.Gam α t) 0 θ,
        Function.iterate_one]
    have hb : |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
        ≤ (4 / 3) * α * Work.Spaces.Gam α θ := by rw [hrepr]; exact hdth
    have habs : |(4 * α ^ 2 / Work.Spaces.c α)
          * Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
        = (4 * α ^ 2 / Work.Spaces.c α)
          * |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ| := by
      rw [abs_mul, abs_of_nonneg hc4nn]
    rw [habs]
    calc (4 * α ^ 2 / Work.Spaces.c α) * |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
        ≤ (4 * α ^ 2 / Work.Spaces.c α) * ((4 / 3) * α * Work.Spaces.Gam α θ) :=
          mul_le_mul_of_nonneg_left hb hc4nn
      _ ≤ 40 * ((4 / 3) * α * Work.Spaces.Gam α θ) :=
          mul_le_mul_of_nonneg_right hDle40 (by positivity)
      _ = (160 / 3) * α * Work.Spaces.Gam α θ := by ring
      _ ≤ 160 / 3 := by nlinarith [hα1, hΓ1, hΓ0, hα.le]
  have ha1_1 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a1 θ') 0 θ| ≤ (40 * Cg) * G θ := by
    intro i hi1 hi4 θ hθ
    have hΓ0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
    have hsin0 : 0 ≤ Real.sin (2 * θ) :=
      Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
    have hprodnn : (0 : ℝ) ≤ Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) :=
      mul_nonneg hΓ0 (by linarith)
    have hrepr : Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a1 θ') 0 θ
        = (4 * α ^ 2 / Work.Spaces.c α)
          * Work.Spaces.dthU^[i + 1] (fun t => Work.Spaces.Gam α t) θ := by
      rw [Work.FTS.LocData.DthIter_rad_eq i a1 0 θ]
      simp only [ha1]
      rw [Work.Spaces.dthU_iter_const_mul, Work.Spaces.dthU_iter_comp]
    rw [hrepr, abs_mul, abs_of_nonneg hc4nn, hG]
    have hb := hCg α hα hα1 θ hθ (i + 1) (by omega) (by omega)
    have hcoef : (4 * α ^ 2 / Work.Spaces.c α) * Cg * α ≤ 40 * Cg := by
      have h1 : (4 * α ^ 2 / Work.Spaces.c α) * Cg ≤ 40 * α ^ 2 * Cg :=
        mul_le_mul_of_nonneg_right hc4 hCgpos.le
      have h2 : (4 * α ^ 2 / Work.Spaces.c α) * Cg * α ≤ 40 * α ^ 2 * Cg * α :=
        mul_le_mul_of_nonneg_right h1 hα.le
      have h3 : 40 * α ^ 2 * Cg * α ≤ 40 * Cg := by
        rw [show 40 * α ^ 2 * Cg * α = 40 * Cg * α ^ 3 from by ring]
        exact mul_le_of_le_one_right (by positivity) hα3
      exact h2.trans h3
    calc (4 * α ^ 2 / Work.Spaces.c α)
          * |Work.Spaces.dthU^[i + 1] (fun t => Work.Spaces.Gam α t) θ|
        ≤ (4 * α ^ 2 / Work.Spaces.c α)
            * (Cg * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) :=
          mul_le_mul_of_nonneg_left hb hc4nn
      _ = ((4 * α ^ 2 / Work.Spaces.c α) * Cg * α)
            * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) := by ring
      _ ≤ (40 * Cg) * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) :=
          mul_le_mul_of_nonneg_right hcoef hprodnn
  have hid1 : (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) = fun z θ => a1 θ * r z := by
    funext z θ
    have hFK : Work.Construction.FK (Work.Construction.Fstar α) z = α * Work.FM.Fstar z := by
      rw [Work.FTS.Nonlin.FK_Fstar hα hα1, Work.FM.Fstar]
    have hpth : Work.Spaces.pth (Work.Construction.Fstar α) z θ
        = (α * Work.FM.Fstar z / Work.Spaces.c α)
          * deriv (fun t => Work.Spaces.Gam α t) θ := by
      rw [Work.Spaces.pth]
      rw [show (fun θ' => Work.Construction.Fstar α z θ')
          = fun θ' => (α * Work.FM.Fstar z / Work.Spaces.c α) * Work.Spaces.Gam α θ' from by
        funext θ'; rw [Work.Construction.Fstar]; ring]
      rw [Work.Spaces.deriv_const_mul']
    rw [Work.Spaces.Dth, hFK, hpth]
    simp only [ha1, hr, Work.Spaces.dthU_apply, Work.Spaces.hKer_apply, Work.FM.Fstar]
    ring_nf
  have hHk1 : Work.Spaces.HkMem α 4 (fun z θ => a1 θ * r z) :=
    Work.FTS.Nonlinear.Open.AngRadHkMem (α := α) (a := a1) (r := r) (G := G)
      (B0 := 160 / 3) (B1 := 40 * Cg) ha1_sm hr_sm hGnn hI1 ha1_0 ha1_1 hrmem
  have hXn1 : Work.FTS.Nonlin.Xn α (fun z θ => a1 θ * r z)
      ≤ Real.sqrt ((160 / 3) ^ 2 * 10000 + 4 * (40 * Cg) ^ 2 * M) * Cr := by
    have hmain := Work.FTS.Nonlinear.Pieces.RNP.Xn_ang_rad_le_gen α hα a1 r G
      (B0 := 160 / 3) (B1 := 40 * Cg) (M1 := M) (by norm_num) (by positivity)
      hMpos.le hGnn ha1_0 ha1_1 hI1 hm1 hrmem
    exact hmain.trans (mul_le_mul_of_nonneg_left hXnR' (Real.sqrt_nonneg _))
  -- ### product 2: `FK(F_*)·F_* = a₂(θ)·r(z)` with `a₂ = (4α²/c)·Γ`
  set a2 : ℝ → ℝ := fun θ => (4 * α ^ 2 / Work.Spaces.c α) * Work.Spaces.Gam α θ with ha2
  have ha2_sm : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a2 θ) := by
    rw [ha2]
    exact smoothOpen_ang_const_mul (Work.FTS.Nonlinear.Open.row23_smoothOpen_Gam α)
  have ha2_0 : ∀ θ ∈ Work.Spaces.Iθ, |a2 θ| ≤ 40 := by
    intro θ hθ
    rw [ha2]
    have hΓ0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
    have hΓ1 : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
    rw [abs_mul, abs_of_nonneg hc4nn, abs_of_nonneg hΓ0]
    calc (4 * α ^ 2 / Work.Spaces.c α) * Work.Spaces.Gam α θ
        ≤ 40 * Work.Spaces.Gam α θ := mul_le_mul_of_nonneg_right hDle40 hΓ0
      _ ≤ 40 := by nlinarith [hΓ1]
  have ha2_1 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a2 θ') 0 θ|
        ≤ (160 / 3 + 40 * Cg) * G θ := by
    intro i hi1 hi4 θ hθ
    have hΓ0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
    have hsin0 : 0 ≤ Real.sin (2 * θ) :=
      Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
    have hprodnn : (0 : ℝ) ≤ Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) :=
      mul_nonneg hΓ0 (by linarith)
    have hrepr : Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a2 θ') 0 θ
        = (4 * α ^ 2 / Work.Spaces.c α)
          * Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ := by
      rw [Work.FTS.LocData.DthIter_rad_eq i a2 0 θ]
      simp only [ha2]
      rw [Work.Spaces.dthU_iter_const_mul]
    rw [hrepr, abs_mul, abs_of_nonneg hc4nn, hG]
    have hcoef : (4 * α ^ 2 / Work.Spaces.c α) * Cg * α ≤ 40 * Cg := by
      have h1 : (4 * α ^ 2 / Work.Spaces.c α) * Cg ≤ 40 * α ^ 2 * Cg :=
        mul_le_mul_of_nonneg_right hc4 hCgpos.le
      have h2 : (4 * α ^ 2 / Work.Spaces.c α) * Cg * α ≤ 40 * α ^ 2 * Cg * α :=
        mul_le_mul_of_nonneg_right h1 hα.le
      have h3 : 40 * α ^ 2 * Cg * α ≤ 40 * Cg := by
        rw [show 40 * α ^ 2 * Cg * α = 40 * Cg * α ^ 3 from by ring]
        exact mul_le_of_le_one_right (by positivity) hα3
      exact h2.trans h3
    rcases eq_or_lt_of_le hi1 with h1 | h1
    · -- `i = 1`: the first-order bound `|D_θ Γ| ≤ (4/3)αΓ` suffices
      subst h1
      rw [Function.iterate_one]
      have hdth := Work.FTS.Nonlinear.Pieces.RNP.dthIter_one_Gam_le hα hα1 θ hθ
      have hrepr1 : Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ
          = Work.Spaces.DthIter 1 (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ := by
        rw [Work.FTS.LocData.DthIter_rad_eq 1 (fun t => Work.Spaces.Gam α t) 0 θ,
          Function.iterate_one]
      have hb : |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
          ≤ (4 / 3) * α * Work.Spaces.Gam α θ := by rw [hrepr1]; exact hdth
      calc (4 * α ^ 2 / Work.Spaces.c α)
            * |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
          ≤ (4 * α ^ 2 / Work.Spaces.c α) * ((4 / 3) * α * Work.Spaces.Gam α θ) :=
            mul_le_mul_of_nonneg_left hb hc4nn
        _ ≤ 40 * ((4 / 3) * α * Work.Spaces.Gam α θ) :=
            mul_le_mul_of_nonneg_right hDle40 (by positivity)
        _ = (160 / 3) * α * Work.Spaces.Gam α θ := by ring
        _ ≤ (160 / 3) * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) := by
            nlinarith [mul_nonneg hΓ0 hsin0]
        _ ≤ (160 / 3 + 40 * Cg) * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) :=
            mul_le_mul_of_nonneg_right (by linarith) hprodnn
    · -- `i ≥ 2`: the sharp iterate bound
      have hb := hCg α hα hα1 θ hθ i (by omega) (by omega)
      calc (4 * α ^ 2 / Work.Spaces.c α)
            * |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
          ≤ (4 * α ^ 2 / Work.Spaces.c α)
              * (Cg * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) :=
            mul_le_mul_of_nonneg_left hb hc4nn
        _ = ((4 * α ^ 2 / Work.Spaces.c α) * Cg * α)
              * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) := by ring
        _ ≤ (40 * Cg) * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) :=
            mul_le_mul_of_nonneg_right hcoef hprodnn
        _ ≤ (160 / 3 + 40 * Cg) * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) :=
            mul_le_mul_of_nonneg_right (by linarith) hprodnn
  have hid2 : (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Construction.Fstar α z θ) = fun z θ => a2 θ * r z := by
    funext z θ
    have hFK : Work.Construction.FK (Work.Construction.Fstar α) z = α * Work.FM.Fstar z := by
      rw [Work.FTS.Nonlin.FK_Fstar hα hα1, Work.FM.Fstar]
    rw [hFK]
    simp only [ha2, hr, Work.Construction.Fstar, Work.Spaces.hKer_apply, Work.FM.Fstar]
    ring_nf
  have hHk2 : Work.Spaces.HkMem α 4 (fun z θ => a2 θ * r z) :=
    Work.FTS.Nonlinear.Open.AngRadHkMem (α := α) (a := a2) (r := r) (G := G)
      (B0 := 40) (B1 := 160 / 3 + 40 * Cg) ha2_sm hr_sm hGnn hI1 ha2_0 ha2_1 hrmem
  have hXn2 : Work.FTS.Nonlin.Xn α (fun z θ => a2 θ * r z)
      ≤ Real.sqrt (40 ^ 2 * 10000 + 4 * (160 / 3 + 40 * Cg) ^ 2 * M) * Cr := by
    have hmain := Work.FTS.Nonlinear.Pieces.RNP.Xn_ang_rad_le_gen α hα a2 r G
      (B0 := 40) (B1 := 160 / 3 + 40 * Cg) (M1 := M) (by norm_num) (by linarith)
      hMpos.le hGnn ha2_0 ha2_1 hI1 hm1 hrmem
    exact hmain.trans (mul_le_mul_of_nonneg_left hXnR' (Real.sqrt_nonneg _))
  -- ### assembly
  have hQ1 : Work.FTS.VocabO.HQo α 4 (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
      * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) := by
    rw [hid1]
    exact ⟨Work.FTS.NonlinRows.AuxAngRad.smoothOpen_ang_rad ha1_sm hr_sm, hHk1⟩
  have hQ2 : Work.FTS.VocabO.HQo α 4 (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
      * Work.Construction.Fstar α z θ) := by
    rw [hid2]
    exact ⟨Work.FTS.NonlinRows.AuxAngRad.smoothOpen_ang_rad ha2_sm hr_sm, hHk2⟩
  refine ⟨hQ1, ?_, hQ2, ?_⟩
  · rw [hid1, hK1]
    linarith [hXn1, hK2nn]
  · rw [hid2, hK2]
    linarith [hXn2, hK1nn]

end

end Work.FTS.StrongEps.ClassCRHS
end
-- ===== merged: Submission.Work.FTS.StrongEps.ClassCRHS.StarAtomsScaled =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.ClassCRHS

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The smoothness and the pointwise decompositions of the three scaled atoms

The three `F_*`-atoms are

`F0 = z/(1+z)·F_*`,  `F1 = z/(1+z)·D_θF_*`,  `F2 = z/(1+z)·D_zF_*`,

and each of them is, on the open quadrant, the product of an angular profile and one of
the two radial profiles `SR0 = 2z²/(1+z)³` (for `F0`, `F1`) and `SR2 = 2z²(1-z)/(1+z)⁴`
(for `F2`) — with angular profiles `SA0 = αΓ/c` (for `F0`, `F2`) resp. `SA1 = αD_θΓ/c`
(for `F1`).  The identities are proved below (`agree0`, `agree1`, `agree2`); the only
genuinely analytic input is `deriv (2z/(1+z)²) z = 2(1-z)/(1+z)³`, which is
`Work.FM.deriv_Fstar`.

The point of this file is then: the four facts

* `Work.FTS.EllipticEst.SmoothOpen` of each product,
* `Work.Spaces.HkMem α 4` of each product (via the angular `×` radial engine
  `Work.FTS.Nonlinear.Open.AngRadHkMem`),
* `Work.FTS.Nonlin.Xn α` of each product bounded by an `α`-uniform constant (via
  `Work.FTS.Nonlinear.Pieces.RNP.Xn_ang_rad_le_gen`),
* the transfer of all of these to the literal atoms `F0, F1, F2`

follow from the `α`-uniform angular slot bounds `AngSlotBounds` (sibling file), the
`α`-uniform radial `D_z`-iterate bounds `DzBoundR0`/`DzBoundR2` (sibling files), the
radial `ℋ⁴`-package `RadHkMemXn` (sibling file) and the `α`-uniform angular mass bound
`gamWeightInt`. -/

/-! ### Smoothness -/

lemma contDiffOn_SR0 (n : ℕ) : ContDiffOn ℝ n SR0 (Set.Ioi 0) := by
  have h : ContDiffOn ℝ n (fun z : ℝ => 2 * z ^ 2 / (1 + z) ^ 3) (Set.Ioi 0) := by
    have hnum : ContDiffOn ℝ n (fun z : ℝ => 2 * z ^ 2) (Set.Ioi 0) := by fun_prop
    have hden : ContDiffOn ℝ n (fun z : ℝ => (1 + z) ^ 3) (Set.Ioi 0) := by fun_prop
    exact hnum.div hden (fun z hz => pow_ne_zero 3
      (ne_of_gt (by linarith [Set.mem_Ioi.mp hz] : (0 : ℝ) < 1 + z)))
  exact h

lemma contDiffOn_SR2 (n : ℕ) : ContDiffOn ℝ n SR2 (Set.Ioi 0) := by
  have h : ContDiffOn ℝ n (fun z : ℝ => 2 * z ^ 2 * (1 - z) / (1 + z) ^ 4) (Set.Ioi 0) := by
    have hnum : ContDiffOn ℝ n (fun z : ℝ => 2 * z ^ 2 * (1 - z)) (Set.Ioi 0) := by fun_prop
    have hden : ContDiffOn ℝ n (fun z : ℝ => (1 + z) ^ 4) (Set.Ioi 0) := by fun_prop
    exact hnum.div hden (fun z hz => pow_ne_zero 4
      (ne_of_gt (by linarith [Set.mem_Ioi.mp hz] : (0 : ℝ) < 1 + z)))
  exact h

lemma smoothOpen_SA0 (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => SA0 α θ) := by
  have h0 := Work.FTS.Nonlinear.Open.row23_smoothOpen_Gam α
  have h1 := Work.FTS.NonlinRows.smoothOpen_const_mul (α / Work.Spaces.c α) h0
  exact h1.congr (fun _ θ _ _ _ => by simp only [SA0]; ring)

lemma smoothOpen_SA1 (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => SA1 α θ) := by
  have h0 := Work.FTS.Nonlinear.Open.row23_smoothOpen_dthU_Gam α
  have h1 := Work.FTS.NonlinRows.smoothOpen_const_mul (α / Work.Spaces.c α) h0
  exact h1.congr (fun _ θ _ _ _ => by simp only [SA1]; ring)

lemma smoothOpen_SRrad0 : Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => SR0 z) :=
  Work.FTS.Nonlinear.Open.row23_smoothOpen_radial contDiffOn_SR0

lemma smoothOpen_SRrad2 : Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => SR2 z) :=
  Work.FTS.Nonlinear.Open.row23_smoothOpen_radial contDiffOn_SR2

/-! ### The three decompositions on the open quadrant -/

lemma agree0 {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 < z) :
    SA0 α θ * SR0 z = z / (1 + z) * Work.Construction.Fstar α z θ := by
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    intro h0; rw [h0] at h; norm_num at h
  have hz0 : z ≠ 0 := ne_of_gt hz
  have h1z : (1 : ℝ) + z ≠ 0 := by linarith
  simp only [SA0, SR0, Work.Construction.Fstar, Work.FM.Fstar]
  field_simp

lemma agree1 {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 < z) :
    SA1 α θ * SR0 z = z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ := by
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    intro h0; rw [h0] at h; norm_num at h
  have hz0 : z ≠ 0 := ne_of_gt hz
  have h1z : (1 : ℝ) + z ≠ 0 := by linarith
  rw [Work.Spaces.Dth, Work.Spaces.pth]
  have hfun : (fun θ' : ℝ => Work.Construction.Fstar α z θ')
      = fun θ' : ℝ => (α * Work.FM.Fstar z / Work.Spaces.c α)
          * Work.Spaces.Gam α θ' := by
    funext θ'; rw [Work.Construction.Fstar]; ring
  rw [hfun, Work.Spaces.deriv_const_mul']
  simp only [SA1, SR0, Work.Spaces.dthU_apply, Work.FM.Fstar]
  field_simp

lemma agree2 {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 < z) :
    SA0 α θ * SR2 z = z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ := by
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    intro h0; rw [h0] at h; norm_num at h
  have hz0 : z ≠ 0 := ne_of_gt hz
  have h1z : (1 : ℝ) + z ≠ 0 := by linarith
  rw [Work.Spaces.Dz, Work.Spaces.pz]
  have hfun : (fun z' : ℝ => Work.Construction.Fstar α z' θ)
      = fun z' : ℝ => (α * Work.Spaces.Gam α θ / Work.Spaces.c α)
          * Work.FM.Fstar z' := by
    funext z'; rw [Work.Construction.Fstar]; ring
  rw [hfun, Work.Spaces.deriv_const_mul', Work.FM.deriv_Fstar z (by linarith)]
  simp only [SA0, SR2]
  field_simp

/-! ### The angular majorant -/

lemma SGmj_nonneg {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ SGmj α θ := by
  have h1 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have h2 : 0 ≤ Real.sin (2 * θ) :=
    Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
  simp only [SGmj]
  positivity

/-- The mass bound of the angular majorant `Γ(α + sin 2θ)` against the weight
`sin(2θ)^{-γ}`, uniform in `α ∈ (0,1]` (`Work.FTS.Nonlinear.Pieces.RNP.gamWeightInt`). -/
lemma SGmj_mass : ∃ M : ℝ, 0 < M ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => SGmj α θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ ∧
    ∫ θ in Work.Spaces.Iθ, SGmj α θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ ≤ M := by
  obtain ⟨M, hMpos, hM⟩ := Work.FTS.Nonlinear.Pieces.RNP.gamWeightInt
  refine ⟨M, hMpos, fun α hα hα1 => ?_⟩
  obtain ⟨hint, hbd⟩ := hM α hα hα1
  have heq : (fun θ : ℝ => SGmj α θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
      = fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2 * (α + Real.sin (2 * θ)) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ := by
    funext θ
    simp only [SGmj]
    ring
  rw [heq]
  exact ⟨hint, hbd⟩

/-! ### The angular `×` radial engine, packaged -/

/-- The angular `×` radial engine of `Work.FTS.Nonlinear.Open.AngRadHkMem` together with the
norm bound `Work.FTS.Nonlinear.Pieces.RNP.Xn_ang_rad_le_gen`. -/
lemma atom_hk {α : ℝ} (hα : 0 < α) {a r G : ℝ → ℝ} {B0 B1 M Crad : ℝ}
    (ha : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ))
    (hr : Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => r z))
    (hGnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ G θ)
    (hGint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ)
    (hB0n : 0 ≤ B0) (hB1n : 0 ≤ B1) (hMn : 0 ≤ M)
    (ha0 : ∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ B0)
    (ha1 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ B1 * G θ)
    (hmass : ∫ θ in Work.Spaces.Iθ,
      G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ ≤ M)
    (hrmem : Work.Spaces.HkMem α 4 (fun z (_ : ℝ) => r z))
    (hXnR : Work.FTS.Nonlin.Xn α (fun z (_ : ℝ) => r z) ≤ Crad) :
    Work.Spaces.HkMem α 4 (fun z θ => a θ * r z) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => a θ * r z)
        ≤ Real.sqrt (B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M) * Crad := by
  have hHk : Work.Spaces.HkMem α 4 (fun z θ => a θ * r z) :=
    Work.FTS.Nonlinear.Open.AngRadHkMem (α := α) (a := a) (r := r) (G := G)
      (B0 := B0) (B1 := B1) ha hr hGnn hGint ha0 ha1 hrmem
  refine ⟨hHk, ?_⟩
  refine (Work.FTS.Nonlinear.Pieces.RNP.Xn_ang_rad_le_gen α hα a r G (B0 := B0) (B1 := B1)
    (M1 := M) hB0n hB1n hMn hGnn ha0 ha1 hGint hmass hrmem).trans ?_
  exact mul_le_mul_of_nonneg_left hXnR (Real.sqrt_nonneg _)

/-! ## The three scaled atoms -/

/-- **The three scaled `F_*`-atoms are `ℋ⁴`-honest with `ℋ⁴`-norm bounded uniformly in `α`.**

`F_* = F_*(α) = α (Γ(θ)/c(α)) 2z/(1+z)²` is the fundamental profile; `Dth = D_θ = sin(2θ)∂_θ`
and `Dz = z ∂_z`.  Note that the *unscaled* `F_*` is **not** in `ℋ⁴` (the weight `w` has a `1/z²`
at `z = 0` while `F_* ≍ z`); the assertion is about the scaled data `(z/(1+z))·F_*`, which is a
`𝒲^{4,∞}`-type function of the shape `const·(Γ or D_θΓ)(θ)·z²/(1+z)³`.

Route: `F_* = a θ * r z` is a separable angular `×` radial product (with `a = αΓ/c`,
`r z = 2z/(1+z)²`); write the scaled data in the same separable form, e.g.
`z/(1+z)·F_* = a θ * (z·r z/(1+z))`, `z/(1+z)·D_θF_* = a₁ θ * (z r z/(1+z))` with
`a₁ = α D_θΓ/c`, `z/(1+z)·D_zF_* = a₂ θ * (z r₂ z/(1+z))` with `r₂ = D_z r`, and apply the
angular `×` radial engine `Work.FTS.Nonlinear.Open.AngRadHkMem` (route/pattern of
`Submission/Work/FTS/Nonlinear/Open/Row23.lean`, which does exactly this for the profile
`dthU (Γ)/c` against `hKer²`), plus `Work.FTS.Nonlinear.Pieces.RNP.Xn_ang_rad_le_gen` for the
norm bound, and `FstarPkg.dthIter_one_Gam_le` / `FstarPkg.dthU_pow_Gam_sharp` for the angular
slot bounds on `D_θ^iΓ` (the good majorant for the `AngRadHkMem` hypothesis is `G = Γ` — note
`∫_Iθ Γ² sin(2θ)^{-γ} < ∞`; `FstarPkg.GamSinRpowMulLeOne` is available).
The two radial profiles `z·r/(1+z)` and `z·r₂/(1+z)` are smooth on `(0,∞)` with bounded
`D_z`-iterates up to order 4 and decay `O(1/z)` at `∞`, so the pure radial slots are directly
integrable.  `Work.Spaces.c_bounds` gives `1/10 ≤ c(α) ≤ 10`; the constant `C` must however be
*uniform* over `α ∈ (0,1]` (both reviewers checked that the norms are `O(√α)` as `α → 0⁺`, so
this is achievable). -/
theorem StarAtomsScaled : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 →
    Work.FTS.VocabO.HQo α 4 (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) ∧
    Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) ≤ C ∧
    Work.FTS.VocabO.HQo α 4
      (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ∧
    Work.FTS.Nonlin.Xn α
      (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ≤ C ∧
    Work.FTS.VocabO.HQo α 4
      (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ∧
    Work.FTS.Nonlin.Xn α
      (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ≤ C := by
  -- ### the four facts furnished by the sibling files of this directory
  obtain ⟨B0, B1, hB0pos, hB1pos, hang⟩ := AngSlotBounds
  obtain ⟨M, hMpos, hMmass⟩ := SGmj_mass
  obtain ⟨Cr0, hCr0pos, hCr0bd⟩ := DzBoundR0
  obtain ⟨Cr2, hCr2pos, hCr2bd⟩ := DzBoundR2
  obtain ⟨Crd0, hCrd0pos, hCrd0⟩ :=
    RadHkMemXn (r := SR0) (C := Cr0) hCr0pos contDiffOn_SR0 hCr0bd
  obtain ⟨Crd2, hCrd2pos, hCrd2⟩ :=
    RadHkMemXn (r := SR2) (C := Cr2) hCr2pos contDiffOn_SR2 hCr2bd
  have hB0nn : 0 ≤ B0 := le_of_lt hB0pos
  have hB1nn : 0 ≤ B1 := le_of_lt hB1pos
  have hMnn : 0 ≤ M := le_of_lt hMpos
  have hCrd0nn : 0 ≤ Crd0 := le_of_lt hCrd0pos
  set S : ℝ := Real.sqrt (B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M) with hSdef
  have hSnn : 0 ≤ S := Real.sqrt_nonneg _
  refine ⟨S * max Crd0 Crd2 + 1, ?_, fun α hαI => ?_⟩
  · have h1 : 0 ≤ S * max Crd0 Crd2 :=
      mul_nonneg hSnn (le_trans hCrd0nn (le_max_left _ _))
    linarith
  · obtain ⟨hα, hα1⟩ := Set.mem_Ioc.mp hαI
    obtain ⟨hA0bd, hA0sl, hA1bd, hA1sl⟩ := hang α hαI
    obtain ⟨hMint, hMbd⟩ := hMmass α hα hα1
    have hGnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ SGmj α θ := fun θ hθ => SGmj_nonneg hα hθ
    -- ### the three engineered products
    have hK0 := atom_hk (α := α) hα (a := SA0 α) (r := SR0) (G := SGmj α)
      (B0 := B0) (B1 := B1) (M := M) (Crad := Crd0) (smoothOpen_SA0 α) smoothOpen_SRrad0
      hGnn hMint hB0nn hB1nn hMnn hA0bd hA0sl hMbd (hCrd0 α hαI).1 (hCrd0 α hαI).2
    have hK1 := atom_hk (α := α) hα (a := SA1 α) (r := SR0) (G := SGmj α)
      (B0 := B0) (B1 := B1) (M := M) (Crad := Crd0) (smoothOpen_SA1 α) smoothOpen_SRrad0
      hGnn hMint hB0nn hB1nn hMnn hA1bd hA1sl hMbd (hCrd0 α hαI).1 (hCrd0 α hαI).2
    have hK2 := atom_hk (α := α) hα (a := SA0 α) (r := SR2) (G := SGmj α)
      (B0 := B0) (B1 := B1) (M := M) (Crad := Crd2) (smoothOpen_SA0 α) smoothOpen_SRrad2
      hGnn hMint hB0nn hB1nn hMnn hA0bd hA0sl hMbd (hCrd2 α hαI).1 (hCrd2 α hαI).2
    -- ### the transfers to the literal atoms
    have hq0 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        SA0 α θ * SR0 z = z / (1 + z) * Work.Construction.Fstar α z θ :=
      fun z θ hz _ _ => agree0 hα hα1 hz
    have hq1 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        SA1 α θ * SR0 z
          = z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ :=
      fun z θ hz _ _ => agree1 hα hα1 hz
    have hq2 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        SA0 α θ * SR2 z
          = z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ :=
      fun z θ hz _ _ => agree2 hα hα1 hz
    have hs0 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => SA0 α θ * SR0 z) :=
      Work.FTS.NonlinRows.AuxAngRad.smoothOpen_ang_rad (smoothOpen_SA0 α) smoothOpen_SRrad0
    have hs1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => SA1 α θ * SR0 z) :=
      Work.FTS.NonlinRows.AuxAngRad.smoothOpen_ang_rad (smoothOpen_SA1 α) smoothOpen_SRrad0
    have hs2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => SA0 α θ * SR2 z) :=
      Work.FTS.NonlinRows.AuxAngRad.smoothOpen_ang_rad (smoothOpen_SA0 α) smoothOpen_SRrad2
    have hsq0 := Work.FTS.EllipticEst.HkSq_congr_open α 4 hq0
    have hsq1 := Work.FTS.EllipticEst.HkSq_congr_open α 4 hq1
    have hsq2 := Work.FTS.EllipticEst.HkSq_congr_open α 4 hq2
    refine ⟨⟨hs0.congr hq0,
        Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hK0.1
          (fun z hz θ hθ => hq0 z θ hz hθ.1 hθ.2)⟩,
      ?_, ⟨hs1.congr hq1,
        Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hK1.1
          (fun z hz θ hθ => hq1 z θ hz hθ.1 hθ.2)⟩,
      ?_, ⟨hs2.congr hq2,
        Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hK2.1
          (fun z hz θ hθ => hq2 z θ hz hθ.1 hθ.2)⟩,
      ?_⟩
    · show Real.sqrt (Work.Spaces.HkSq α 4
        (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ))
          ≤ S * max Crd0 Crd2 + 1
      rw [← hsq0]
      exact hK0.2.trans (le_trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hSnn)
        (by linarith))
    · show Real.sqrt (Work.Spaces.HkSq α 4
        (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ))
          ≤ S * max Crd0 Crd2 + 1
      rw [← hsq1]
      exact hK1.2.trans (le_trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hSnn)
        (by linarith))
    · show Real.sqrt (Work.Spaces.HkSq α 4
        (fun z θ => z / (1 + z) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ))
          ≤ S * max Crd0 Crd2 + 1
      rw [← hsq2]
      exact hK2.2.trans (le_trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hSnn)
        (by linarith))

end Work.FTS.StrongEps.ClassCRHS
end
-- ===== merged: Submission.Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.ClassCRHS

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The radial function `z ↦ L₁₂(w)(z)` is `C^∞` on `(0,∞)`, hence `SmoothOpen` on the open
quadrant, for every profile `w` of the class `ClassC α`.**

`L₁₂(w)` is the tail integral `z ↦ ∫_z^∞ F_*(w)(r)/r dr` (`Work.Elliptic.L12_eq_radial`), so its
derivative on `(0,∞)` is `z ↦ -3 F_*(w)(z)/z` (`HasDerivAt_L12_of_Fstar_facts`).  For a profile of
the class `ClassC α` all three ingredients are available:

* `F_*(w)` is `C^∞` on `(0,∞)` — the field `ClassC.fsm`;
* `r ↦ F_*(w)(r)/r` is integrable on `(0,∞)` (`FstarDivOpen.fstar_div_integrable_of_smoothOpen`,
  from the fields `ClassC.reg` (`SmoothOpen w`) and `ClassC.mem` (`HkMem α 7 w`));
* consequently `z ↦ -3 F_*(w)(z)/z` is `C^∞` on `(0,∞)`, and the primitive lemma
  `contDiffOn_infty_iff_deriv_of_isOpen` upgrades `L₁₂(w)` to `C^∞` there.

Promoting the radial smoothness to the open quadrant is `NonlinRows.smoothOpen_radial`, and the
two definitions of `L₁₂` are identified by `Work.FTS.H2.constructionL12_eq_ellipticL12`. -/
theorem smoothOpen_L12_radial_classC {α : ℝ} {w : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hw : Work.FTS.ClassC.ClassC α w) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 w z) := by
  have hFint : IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar w r / r) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen α 7 w hw.reg hw.mem
  have hderiv := Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts w hw.fsm hFint
  have hgTop : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => -(3 * Work.Elliptic.Fstar w z / z)) (Set.Ioi 0) :=
    ((contDiffOn_const.mul (contDiffOn_infty.mpr hw.fsm)).div contDiffOn_id
      (fun z hz => ne_of_gt hz)).neg
  have hTop : ContDiffOn ℝ Work.Stability.smoothOrder (Work.Elliptic.L12 w) (Set.Ioi 0) := by
    rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi]
    exact ⟨fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt,
      hgTop.congr (fun z hz => (hderiv z hz).deriv)⟩
  refine Work.FTS.NonlinRows.smoothOpen_radial
    (r := fun z => Work.Construction.L12 w z) fun n => ?_
  refine (contDiffOn_infty.mp hTop n).congr fun z hz => ?_
  rw [Work.FTS.H2.constructionL12_eq_ellipticL12 w]

end Work.FTS.StrongEps.ClassCRHS
end
-- ===== merged: Submission.Work.FTS.StrongEps.DiffAux.DzIter_sub_Jeps =====
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

/-- **Slotwise subtraction of the iterated `D_z`-operator.**  If the `z`-slices of the iterates
`D_z^k A`, `D_z^k B` (at the fixed angle `θ`) are differentiable on `(0,∞)` for every `k ≤ j`,
then `D_z^j` is subtractive at `(z,θ)`.

(`D_z = z∂_z` is a `deriv`-based operator, so the induction has to produce the differentiability
of the slices from the hypotheses at each level; this is where the `DifferentiableOn` hypotheses
are used.) -/
theorem DzIter_sub_of_diffOn :
    ∀ j : ℕ, ∀ {A B : ℝ → ℝ → ℝ} {z θ : ℝ}, 0 < z →
      (∀ k ≤ j, DifferentiableOn ℝ (fun z' => Work.Spaces.DzIter k A z' θ) (Set.Ioi 0)) →
      (∀ k ≤ j, DifferentiableOn ℝ (fun z' => Work.Spaces.DzIter k B z' θ) (Set.Ioi 0)) →
      Work.Spaces.DzIter j (fun z θ => A z θ - B z θ) z θ
        = Work.Spaces.DzIter j A z θ - Work.Spaces.DzIter j B z θ := by
  intro j
  induction j with
  | zero => intro A B z θ hz hA hB; rfl
  | succ n ih =>
    intro A B z θ hz hA hB
    have hzmem : Set.Ioi (0 : ℝ) ∈ 𝓝 z := isOpen_Ioi.mem_nhds hz
    have hA' : ∀ k ≤ n, DifferentiableOn ℝ (fun z' => Work.Spaces.DzIter k A z' θ)
        (Set.Ioi 0) := fun k hk => hA k (le_trans hk (Nat.le_succ n))
    have hB' : ∀ k ≤ n, DifferentiableOn ℝ (fun z' => Work.Spaces.DzIter k B z' θ)
        (Set.Ioi 0) := fun k hk => hB k (le_trans hk (Nat.le_succ n))
    have heq : (fun z' => Work.Spaces.DzIter n (fun z θ => A z θ - B z θ) z' θ)
        =ᶠ[𝓝 z] (fun z' => Work.Spaces.DzIter n A z' θ - Work.Spaces.DzIter n B z' θ) := by
      filter_upwards [hzmem] with z' hz'
      exact ih hz' hA' hB'
    have hdA : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n A z' θ) z :=
      (hA' n le_rfl).differentiableAt hzmem
    have hdB : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n B z' θ) z :=
      (hB' n le_rfl).differentiableAt hzmem
    have hd : deriv (fun z' => Work.Spaces.DzIter n A z' θ - Work.Spaces.DzIter n B z' θ) z
        = deriv (fun z' => Work.Spaces.DzIter n A z' θ) z
          - deriv (fun z' => Work.Spaces.DzIter n B z' θ) z := deriv_sub hdA hdB
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
    rw [heq.deriv_eq, hd]
    ring

/-- **The `D_z^j`-slot of the mollifier difference `J_ε f - f`** is the difference of the slots:
`D_z^j (J_ε f - f) = J_ε (D_z^j f) - D_z^j f` at every point of the open quadrant, for `f` which
is `C^n` on the quadrant for every `n`.

The two ingredients are `DzIter_sub_of_diffOn` above (subtraction of the `deriv`-based iterated
operator, from the differentiability of the slices) and the two commuting results
`DzIter_Jeps_of_smooth` (`D_z^j` commutes with `J_ε` on the quadrant for a smooth profile) and
`hasDerivAt_Jeps_slice_z` (the `z`-slices of `J_ε g` are differentiable, with an explicit
derivative, for any profile smooth on the quadrant). -/
theorem DzIter_sub_Jeps (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsMollKernel ρ) {ε : ℝ}
    (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (j : ℕ) :
    Work.Spaces.DzIter j (fun z θ => Work.FTS.StrongEps.Jeps ρ ε f z θ - f z θ) z θ
      = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.DzIter j f) z θ
        - Work.Spaces.DzIter j f z θ := by
  have hS : Work.FTS.StrongEps.SmQ f := Work.FTS.StrongEps.smQ_of_forall_nat hf
  -- the `z`-slices of the `D_z`-iterates of `J_ε f` are differentiable on `(0,∞)`: on the open
  -- quadrant the iterates agree with `J_ε` of the iterates of the profile, whose slices are
  -- differentiable by `hasDerivAt_Jeps_slice_z`
  have hAz : ∀ k ≤ j, DifferentiableOn ℝ
      (fun z' => Work.Spaces.DzIter k (Work.FTS.StrongEps.Jeps ρ ε f) z' θ) (Set.Ioi 0) := by
    intro k hk z' hz'
    have hk' : Work.FTS.StrongEps.SmQ (Work.Spaces.DzIter k f) := hS.DzIter k
    have hforall : ∀ n : ℕ,
        ContDiffOn ℝ n (Function.uncurry (Work.Spaces.DzIter k f)) Work.FTS.StrongEps.Quad :=
      fun n => contDiffOn_infty.mp hk' n
    have hev : (fun z'' => Work.Spaces.DzIter k (Work.FTS.StrongEps.Jeps ρ ε f) z'' θ)
        =ᶠ[𝓝 z'] (fun z'' =>
          Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.DzIter k f) z'' θ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz'] with z'' hz''
      exact (Work.FTS.StrongEps.DzIter_Jeps_of_smooth ρ hρ hε (g := f) hS k)
        (show (z'', θ) ∈ Work.FTS.StrongEps.Quad from ⟨hz'', hθ⟩)
    have hd : DifferentiableAt ℝ
        (fun z'' => Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.DzIter k f) z'' θ) z' :=
      (hasDerivAt_Jeps_slice_z ρ hρ hε hforall hz' hθ).differentiableAt
    exact (hev.differentiableAt_iff.mpr hd).differentiableWithinAt
  -- the `z`-slices of the `D_z`-iterates of the profile itself are differentiable, by smoothness
  have hBz : ∀ k ≤ j, DifferentiableOn ℝ (fun z' => Work.Spaces.DzIter k f z' θ) (Set.Ioi 0) :=
    fun k _ => ((Work.FTS.LocData.contDiffOn_slice_z (G := Work.Spaces.DzIter k f)
      (hS.DzIter k) hθ).differentiableOn (by simp [Work.Stability.smoothOrder]))
  rw [DzIter_sub_of_diffOn j hz hAz hBz]
  rw [show Work.Spaces.DzIter j (Work.FTS.StrongEps.Jeps ρ ε f) z θ
      = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.DzIter j f) z θ from
    (Work.FTS.StrongEps.DzIter_Jeps_of_smooth ρ hρ hε (g := f) hS j)
      (show (z, θ) ∈ Work.FTS.StrongEps.Quad from ⟨hz, hθ⟩)]

end Work.FTS.StrongEps.DiffAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.DiffAux.mixed_sub_Jeps =====
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

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ## Slotwise subtraction of the iterated operators -/

/-- **Slotwise subtraction of the iterated `D_z`-operator.**  If the `z`-slices of the iterates
`D_z^k A`, `D_z^k B` (at the fixed angle `θ`) are differentiable on `(0,∞)` for every `k ≤ j`,
then `D_z^j` is subtractive at `(z,θ)`.

(`D_z = z∂_z` is a `deriv`-based operator, so the induction has to produce the differentiability
of the slices from the hypotheses at each level; this is where the `DifferentiableOn` hypotheses
are used.) -/
theorem msj_DzIter_sub_of_diffOn :
    ∀ (j : ℕ) {A B : ℝ → ℝ → ℝ} {z θ : ℝ}, 0 < z →
      (∀ k ≤ j, DifferentiableOn ℝ (fun z' => Work.Spaces.DzIter k A z' θ) (Set.Ioi 0)) →
      (∀ k ≤ j, DifferentiableOn ℝ (fun z' => Work.Spaces.DzIter k B z' θ) (Set.Ioi 0)) →
      Work.Spaces.DzIter j (fun z θ => A z θ - B z θ) z θ
        = Work.Spaces.DzIter j A z θ - Work.Spaces.DzIter j B z θ
  | 0, _, _, _, _, _, _, _ => rfl
  | j + 1, A, B, z, θ, hz, hA, hB => by
    have hzmem : Set.Ioi (0 : ℝ) ∈ 𝓝 z := isOpen_Ioi.mem_nhds hz
    have hA' : ∀ k ≤ j, DifferentiableOn ℝ (fun z' => Work.Spaces.DzIter k A z' θ)
        (Set.Ioi 0) := fun k hk => hA k (le_trans hk (Nat.le_succ j))
    have hB' : ∀ k ≤ j, DifferentiableOn ℝ (fun z' => Work.Spaces.DzIter k B z' θ)
        (Set.Ioi 0) := fun k hk => hB k (le_trans hk (Nat.le_succ j))
    have heq : (fun z' => Work.Spaces.DzIter j (fun z θ => A z θ - B z θ) z' θ)
        =ᶠ[𝓝 z] (fun z' => Work.Spaces.DzIter j A z' θ - Work.Spaces.DzIter j B z' θ) := by
      filter_upwards [hzmem] with z' hz'
      exact msj_DzIter_sub_of_diffOn j hz' hA' hB'
    have hdA : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter j A z' θ) z :=
      (hA' j le_rfl).differentiableAt hzmem
    have hdB : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter j B z' θ) z :=
      (hB' j le_rfl).differentiableAt hzmem
    have hd : deriv (fun z' => Work.Spaces.DzIter j A z' θ - Work.Spaces.DzIter j B z' θ) z
        = deriv (fun z' => Work.Spaces.DzIter j A z' θ) z
          - deriv (fun z' => Work.Spaces.DzIter j B z' θ) z := deriv_sub hdA hdB
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
    rw [heq.deriv_eq, hd]
    ring

/-- **Slotwise subtraction of the iterated `D_θ`-operator.**  The `θ`-analogue of
`msj_DzIter_sub_of_diffOn`. -/
theorem msj_DthIter_sub_of_diffOn :
    ∀ (i : ℕ) {A B : ℝ → ℝ → ℝ} {z θ : ℝ}, θ ∈ Set.Ioo 0 (π / 2) →
      (∀ k ≤ i, DifferentiableOn ℝ (fun θ' => Work.Spaces.DthIter k A z θ')
        (Set.Ioo 0 (π / 2))) →
      (∀ k ≤ i, DifferentiableOn ℝ (fun θ' => Work.Spaces.DthIter k B z θ')
        (Set.Ioo 0 (π / 2))) →
      Work.Spaces.DthIter i (fun z θ => A z θ - B z θ) z θ
        = Work.Spaces.DthIter i A z θ - Work.Spaces.DthIter i B z θ
  | 0, _, _, _, _, _, _, _ => rfl
  | i + 1, A, B, z, θ, hθ, hA, hB => by
    have hθmem : Set.Ioo (0 : ℝ) (π / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
    have hA' : ∀ k ≤ i, DifferentiableOn ℝ (fun θ' => Work.Spaces.DthIter k A z θ')
        (Set.Ioo 0 (π / 2)) := fun k hk => hA k (le_trans hk (Nat.le_succ i))
    have hB' : ∀ k ≤ i, DifferentiableOn ℝ (fun θ' => Work.Spaces.DthIter k B z θ')
        (Set.Ioo 0 (π / 2)) := fun k hk => hB k (le_trans hk (Nat.le_succ i))
    have heq : (fun θ' => Work.Spaces.DthIter i (fun z θ => A z θ - B z θ) z θ')
        =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DthIter i A z θ' - Work.Spaces.DthIter i B z θ') := by
      filter_upwards [hθmem] with θ' hθ'
      exact msj_DthIter_sub_of_diffOn i hθ' hA' hB'
    have hdA : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter i A z θ') θ :=
      (hA' i le_rfl).differentiableAt hθmem
    have hdB : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter i B z θ') θ :=
      (hB' i le_rfl).differentiableAt hθmem
    have hd : deriv (fun θ' => Work.Spaces.DthIter i A z θ' - Work.Spaces.DthIter i B z θ') θ
        = deriv (fun θ' => Work.Spaces.DthIter i A z θ') θ
          - deriv (fun θ' => Work.Spaces.DthIter i B z θ') θ := deriv_sub hdA hdB
    simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
    rw [heq.deriv_eq, hd]
    ring

/-- **Slotwise subtraction of the mixed operators `D_z^j D_θ^i`.**  Given the differentiability of
the `z`-slices of `D_z^k (D_θ^i ·)` (`k ≤ j`) and of the `θ`-slices of `D_θ^m ·` (`m ≤ i`) for
both profiles, the mixed slot of the difference is the difference of the mixed slots. -/
theorem msj_mixed_sub_of_diffOn (j i : ℕ) :
    ∀ {A B : ℝ → ℝ → ℝ} {z θ : ℝ}, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      (∀ k ≤ j, DifferentiableOn ℝ
        (fun z' => Work.Spaces.DzIter k (Work.Spaces.DthIter i A) z' θ) (Set.Ioi 0)) →
      (∀ k ≤ j, DifferentiableOn ℝ
        (fun z' => Work.Spaces.DzIter k (Work.Spaces.DthIter i B) z' θ) (Set.Ioi 0)) →
      (∀ z' : ℝ, 0 < z' → ∀ m ≤ i, DifferentiableOn ℝ
        (fun θ' => Work.Spaces.DthIter m A z' θ') (Set.Ioo 0 (π / 2))) →
      (∀ z' : ℝ, 0 < z' → ∀ m ≤ i, DifferentiableOn ℝ
        (fun θ' => Work.Spaces.DthIter m B z' θ') (Set.Ioo 0 (π / 2))) →
      Work.Spaces.mixed j i (fun z θ => A z θ - B z θ) z θ
        = Work.Spaces.mixed j i A z θ - Work.Spaces.mixed j i B z θ := by
  intro A B z θ hz hθ hAz hBz hAθ hBθ
  have hsubθ : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < π / 2 →
      Work.Spaces.DthIter i (fun z θ => A z θ - B z θ) z' θ'
        = Work.Spaces.DthIter i A z' θ' - Work.Spaces.DthIter i B z' θ' :=
    fun z' θ' hz' h1 h2 =>
      msj_DthIter_sub_of_diffOn i (A := A) (B := B) (z := z') (θ := θ') ⟨h1, h2⟩
        (fun m hm => hAθ z' hz' m hm) (fun m hm => hBθ z' hz' m hm)
  have hcongr := Work.FTS.EllipticEst.SmoothOpen.DzIter_congr
    (F := Work.Spaces.DthIter i (fun z θ => A z θ - B z θ))
    (G := fun z θ => Work.Spaces.DthIter i A z θ - Work.Spaces.DthIter i B z θ)
    hsubθ j z θ hz hθ.1 hθ.2
  have hadd := msj_DzIter_sub_of_diffOn j hz hAz hBz
  simp only [Work.Spaces.mixed]
  exact hcongr.trans hadd

/-! ## The differentiability of the slots of `J_ε f` -/

/-- The `θ`-slices of the `D_θ`-iterates of `J_ε f` are differentiable, for `f` smooth on the
open quadrant and any admissible (merely continuous) kernel. -/
theorem msj_Jeps_slots_diffOn_theta (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ → ℝ} (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) (i : ℕ) :
    ∀ z : ℝ, 0 < z → ∀ m ≤ i,
      DifferentiableOn ℝ (fun θ' => Work.Spaces.DthIter m (Jeps ρ ε f) z θ')
        (Set.Ioo 0 (π / 2)) := by
  intro z hz m _
  intro θ' hθ'
  have hF : Work.FTS.EllipticEst.SmoothOpen f :=
    Work.FTS.EllipticEst.smoothOpen_of_forall (F := f) (fun n => hf n)
  have hev : (fun θ'' => Work.Spaces.DthIter m (Jeps ρ ε f) z θ'')
      =ᶠ[𝓝 θ'] (fun θ'' => Jeps ρ ε (Work.Spaces.DthIter m f) z θ'') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ'] with θ'' hθ''
    have hp : (z, θ'') ∈ Quad := ⟨hz, hθ''⟩
    exact DthIter_mixed_Jeps ρ hρ hε hf m hp
  have hd : DifferentiableAt ℝ (fun θ'' => Jeps ρ ε (Work.Spaces.DthIter m f) z θ'') θ' :=
    (hasDerivAt_Jeps_slice_th ρ hρ hε (fun n => (hF.DthIter m).forall n) hz hθ')
      |>.differentiableAt
  exact (hev.differentiableAt_iff.mpr hd).differentiableWithinAt

/-- The `z`-slices of the `D_z`-iterates of `D_θ^i (J_ε f)` are differentiable, for `f` smooth on
the open quadrant and any admissible (merely continuous) kernel. -/
theorem msj_Jeps_slots_diffOn_z (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ → ℝ} (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (j i : ℕ) :
    ∀ k ≤ j, DifferentiableOn ℝ
      (fun z' => Work.Spaces.DzIter k (Work.Spaces.DthIter i (Jeps ρ ε f)) z' θ)
      (Set.Ioi 0) := by
  intro k _
  intro z' hz'
  have hF : Work.FTS.EllipticEst.SmoothOpen f :=
    Work.FTS.EllipticEst.smoothOpen_of_forall (F := f) (fun n => hf n)
  have hev : (fun z'' => Work.Spaces.DzIter k (Work.Spaces.DthIter i (Jeps ρ ε f)) z'' θ)
      =ᶠ[𝓝 z'] (fun z'' => Jeps ρ ε (Work.Spaces.mixed k i f) z'' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz'] with z'' hz''
    have hp : (z'', θ) ∈ Quad := ⟨hz'', hθ⟩
    exact (Work.FTS.TransportS.DzIter_congrOn isOpen_Quad
        (DthIter_mixed_Jeps ρ hρ hε hf i) k hp).trans
      (DzIter_Jeps_of_smooth ρ hρ hε ((smQ_of_forall_nat hf).DthIter i) k hp)
  have hd : DifferentiableAt ℝ (fun z'' => Jeps ρ ε (Work.Spaces.mixed k i f) z'' θ) z' :=
    (hasDerivAt_Jeps_slice_z ρ hρ hε (fun n => (hF.mixed k i).forall n) hz' hθ)
      |>.differentiableAt
  exact (hev.differentiableAt_iff.mpr hd).differentiableWithinAt

/-! ## The target -/

theorem mixed_sub_Jeps (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsMollKernel ρ) {ε : ℝ}
    (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (j i : ℕ) :
    Work.Spaces.mixed j i (fun z θ => Work.FTS.StrongEps.Jeps ρ ε f z θ - f z θ) z θ
      = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed j i f) z θ
        - Work.Spaces.mixed j i f z θ := by
  have hF : Work.FTS.EllipticEst.SmoothOpen f :=
    Work.FTS.EllipticEst.smoothOpen_of_forall (F := f) (fun n => hf n)
  -- the slotwise subtraction `D_z^jD_θ^i (J_ε f - f) = D_z^jD_θ^i (J_ε f) - D_z^jD_θ^i f`
  have hAz := msj_Jeps_slots_diffOn_z ρ hρ hε hf hz hθ j i
  have hBz : ∀ k ≤ j, DifferentiableOn ℝ
      (fun z' => Work.Spaces.DzIter k (Work.Spaces.DthIter i f) z' θ) (Set.Ioi 0) :=
    fun k _ => ((hF.mixed k i).curry_z hθ).differentiableOn (by simp [Work.Stability.smoothOrder])
  have hAθ := msj_Jeps_slots_diffOn_theta ρ hρ hε hf i
  have hBθ : ∀ z' : ℝ, 0 < z' → ∀ m ≤ i, DifferentiableOn ℝ
      (fun θ' => Work.Spaces.DthIter m f z' θ') (Set.Ioo 0 (π / 2)) :=
    fun z' hz' m _ =>
      ((hF.DthIter m).curry_θ hz').differentiableOn (by simp [Work.Stability.smoothOrder])
  have hsub := msj_mixed_sub_of_diffOn j i (A := Jeps ρ ε f) (B := f) hz hθ hAz hBz hAθ hBθ
  -- and the commutativity `D_z^jD_θ^i (J_ε f) = J_ε (D_z^jD_θ^i f)`
  have hA := mixed_Jeps ρ hρ hε hf hz hθ j i
  rw [hsub, hA]

end Work.FTS.StrongEps.DiffAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.leaf_logW_shift_uniform =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped Real Topology
open MeasureTheory Set Filter

/-!
# `leaf_logW_shift_uniform` — a *single* shift constant for all three leaf weights

`leaf_logW_shift` proves, for each fixed `α > 0` and each of the three leaf weights
`w²sin(2θ)^{-η}`, `w²`, `w²sin(2θ)^{-γ α}`, the existence of a constant `C` with

`logW w (y+p) ≤ e^{C(|p.1|+|p.2|)} logW w y`

(and the reverse).  The exponent produced there is `8 + κ`, where `κ` is the angular constant:
`κ = 1` for the `η`-leaf, `κ = 0` for the `w²`-leaf and `κ = γ α = 1 + α/10` for the `γ`-leaf.
Since `α ≤ 1` forces `γ α ≤ 11/10` and `η = 99/100 ≤ 11/10`, all three leaves satisfy the angular
bound with the **same** constant `κ = 11/10`, hence all of them — uniformly in `α ∈ (0,1]` — are
controlled with the single constant

  `C = 8 + 11/10`.

The two ingredients of `8` are the Jacobian factor (`logJac_add_le`, giving `e^{4(|p.1|+|p.2|)}`)
and the radial factor (`wtZ_exp_add_le`, giving `e^{4|p.1|}`); they combine exactly as in
`logW_shift_aux`, whose proof we re-run with the constant exposed (`logW_shift_uniform_aux`) so
that a common `κ` can be fed to all three leaves.
-/

/-! ## The angular factors, with the common exponent `11/10` -/

/-- **The `η`-factor with the uniform exponent**: `sin(2θ)^{-η}` at `θ = arctan (e^ζ)` shifts by
at most `e^{(11/10)|p|}`.  (`sEtaW_thShift_le` gives `e^{|p|}`, and `1 ≤ 11/10`.) -/
theorem sEtaW_arctan_exp_shift (ζ p : ℝ) :
    Work.FTS.StrongEps.sEtaW (Real.arctan (Real.exp (ζ + p)))
      ≤ Real.exp ((11 / 10 : ℝ) * |p|)
        * Work.FTS.StrongEps.sEtaW (Real.arctan (Real.exp ζ)) := by
  have h := Work.FTS.StrongEps.sEtaW_thShift_le (θ := Real.arctan (Real.exp ζ)) (p := -p)
    (arctan_exp_mem ζ)
  rw [← arctan_exp_add ζ p, abs_neg] at h
  have hexp : Real.exp |p| ≤ Real.exp ((11 / 10 : ℝ) * |p|) :=
    Real.exp_le_exp.mpr (by nlinarith [abs_nonneg p])
  exact h.trans (mul_le_mul_of_nonneg_right hexp
    (le_of_lt (Work.FTS.StrongEps.sEtaW_pos (arctan_exp_mem ζ))))

/-- **The `γ`-factor with the uniform exponent**: for `α ∈ (0,1]`, `sin(2θ)^{-γ α}` at
`θ = arctan (e^ζ)` shifts by at most `e^{(11/10)|p|}`.  This is `sGamW_shift_le_sharp`
(`e^{γ α |p|}`) together with `γ α = 1 + α/10 ≤ 11/10`. -/
theorem sGamW_arctan_exp_shift {α : ℝ} (hα : α ∈ Set.Ioc (0 : ℝ) 1) (ζ p : ℝ) :
    Work.FTS.StrongEps.sGamW α (Real.arctan (Real.exp (ζ + p)))
      ≤ Real.exp ((11 / 10 : ℝ) * |p|)
        * Work.FTS.StrongEps.sGamW α (Real.arctan (Real.exp ζ)) := by
  have h := sGamW_shift_le_sharp (α := α) hα.1 (θ := Real.arctan (Real.exp ζ)) (p := -p)
    (arctan_exp_mem ζ)
  rw [← arctan_exp_add ζ p, abs_neg] at h
  have hgam : Work.Spaces.gam α ≤ 11 / 10 := by
    rw [Work.Spaces.gam]; linarith [hα.2]
  have hexp : Real.exp (Work.Spaces.gam α * |p|) ≤ Real.exp ((11 / 10 : ℝ) * |p|) :=
    Real.exp_le_exp.mpr (by nlinarith [abs_nonneg p, hgam])
  exact h.trans (mul_le_mul_of_nonneg_right hexp
    (le_of_lt (Work.FTS.StrongEps.sGamW_pos (α := α) (arctan_exp_mem ζ))))

/-! ## The two-sided shift bound with an exposed constant -/

/-- **Two-sided shift bound for `logW`, with the constant `8 + κ` exposed.**  If `Θ` is a positive
angular factor which shifts by at most `e^{κ|p|}` and `w`, evaluated at `Ψ y = (e^{y.1},
arctan (e^{y.2}))`, is `wtZ (e^{y.1}) · Θ y.2`, then `logW w` shifts by at most
`e^{(8+κ)(|p.1|+|p.2|)}` in both directions.  The forward direction is the proof of
`logW_shift_aux` with `∃C` replaced by the explicit `8 + κ`; the reverse is the forward bound
applied at `(y + p, -p)`. -/
theorem logW_shift_uniform_aux {Θ : ℝ → ℝ} (hΘpos : ∀ ζ : ℝ, 0 < Θ ζ) {κ : ℝ} (hκ : 0 ≤ κ)
    (hΘ : ∀ ζ p : ℝ, Θ (ζ + p) ≤ Real.exp (κ * |p|) * Θ ζ) (w : ℝ → ℝ → ℝ)
    (hw : ∀ y : ℝ × ℝ, w (Real.exp y.1) (Real.arctan (Real.exp y.2))
      = Work.FTS.StrongEps.wtZ (Real.exp y.1) * Θ y.2) :
    ∀ y p : ℝ × ℝ,
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (y + p)
          ≤ Real.exp ((8 + κ) * (|p.1| + |p.2|))
            * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y)
      ∧ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          ≤ Real.exp ((8 + κ) * (|p.1| + |p.2|))
            * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (y + p)) := by
  -- fold `logW w` into the `logJac · (wtZ · Θ)` form
  have hpi : ∀ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
      = Work.FTS.StrongEps.HkSqAux.logJac y.1 y.2
        * (Work.FTS.StrongEps.wtZ (Real.exp y.1) * Θ y.2) := by
    intro y
    rw [Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW_apply, hw y]
  have hfwd : ∀ y p : ℝ × ℝ,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (y + p)
        ≤ Real.exp ((8 + κ) * (|p.1| + |p.2|))
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y := by
    intro y p
    have hJ : Work.FTS.StrongEps.HkSqAux.logJac (y + p).1 (y + p).2
        ≤ Real.exp (4 * (|p.1| + |p.2|)) * Work.FTS.StrongEps.HkSqAux.logJac y.1 y.2 := by
      simpa only [Prod.fst_add, Prod.snd_add] using logJac_add_le y.1 y.2 p.1 p.2
    have hZ : Work.FTS.StrongEps.wtZ (Real.exp (y + p).1)
        ≤ Real.exp (4 * |p.1|) * Work.FTS.StrongEps.wtZ (Real.exp y.1) := by
      simpa only [Prod.fst_add] using wtZ_exp_add_le y.1 p.1
    have hT : Θ (y + p).2 ≤ Real.exp (κ * |p.2|) * Θ y.2 := by
      simpa only [Prod.snd_add] using hΘ y.2 p.2
    have hinner : Work.FTS.StrongEps.wtZ (Real.exp (y + p).1) * Θ (y + p).2
        ≤ (Real.exp (4 * |p.1|) * Work.FTS.StrongEps.wtZ (Real.exp y.1))
          * (Real.exp (κ * |p.2|) * Θ y.2) :=
      mul_le_mul hZ hT (le_of_lt (hΘpos _))
        (mul_nonneg (Real.exp_pos _).le (Work.FTS.StrongEps.wtZ_nonneg _))
    have hmain := mul_le_mul hJ hinner
      (mul_nonneg (Work.FTS.StrongEps.wtZ_nonneg _) (le_of_lt (hΘpos _)))
      (mul_nonneg (Real.exp_pos _).le (Work.FTS.StrongEps.HkSqAux.logJac_pos _ _).le)
    have heq : (Real.exp (4 * (|p.1| + |p.2|)) * Work.FTS.StrongEps.HkSqAux.logJac y.1 y.2)
          * ((Real.exp (4 * |p.1|) * Work.FTS.StrongEps.wtZ (Real.exp y.1))
              * (Real.exp (κ * |p.2|) * Θ y.2))
        = Real.exp (4 * (|p.1| + |p.2|) + 4 * |p.1| + κ * |p.2|)
          * (Work.FTS.StrongEps.HkSqAux.logJac y.1 y.2
              * (Work.FTS.StrongEps.wtZ (Real.exp y.1) * Θ y.2)) := by
      rw [Real.exp_add (4 * (|p.1| + |p.2|) + 4 * |p.1|) (κ * |p.2|)]
      rw [Real.exp_add (4 * (|p.1| + |p.2|)) (4 * |p.1|)]
      ring
    have hstep : Work.FTS.StrongEps.HkSqAux.logJac (y + p).1 (y + p).2
          * (Work.FTS.StrongEps.wtZ (Real.exp (y + p).1) * Θ (y + p).2)
        ≤ Real.exp ((8 + κ) * (|p.1| + |p.2|))
          * (Work.FTS.StrongEps.HkSqAux.logJac y.1 y.2
              * (Work.FTS.StrongEps.wtZ (Real.exp y.1) * Θ y.2)) := by
      refine hmain.trans ?_
      rw [heq]
      apply mul_le_mul_of_nonneg_right
      · exact Real.exp_le_exp.mpr (by nlinarith [abs_nonneg p.1, abs_nonneg p.2, hκ])
      · exact le_of_lt (mul_pos (Work.FTS.StrongEps.HkSqAux.logJac_pos _ _)
          (mul_pos (Work.FTS.StrongEps.wtZ_pos (Real.exp_pos _)) (hΘpos _)))
    rw [hpi (y + p), hpi y]
    exact hstep
  intro y p
  refine ⟨hfwd y p, ?_⟩
  have h := hfwd (y + p) (-p)
  simpa only [Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, abs_neg,
    add_neg_cancel_right] using h

/-! ## The uniform statement -/

theorem leaf_logW_shift_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ w : ℝ → ℝ → ℝ,
      (w = Work.FTS.TransportS.leafEta ∨ w = Work.FTS.TransportS.leafOne
        ∨ w = Work.FTS.TransportS.leafGam α) →
      ∀ y p : ℝ × ℝ,
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (y + p)
            ≤ Real.exp (C * (|p.1| + |p.2|))
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y)
        ∧ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
            ≤ Real.exp (C * (|p.1| + |p.2|))
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (y + p)) := by
  refine ⟨8 + 11 / 10, by norm_num, ?_⟩
  intro α hα w hw y p
  have hκ : (0 : ℝ) ≤ 11 / 10 := by norm_num
  rcases hw with hw | hw | hw
  · -- the `η`-leaf
    subst hw
    have hΘpos : ∀ ζ : ℝ, 0 < Work.FTS.StrongEps.sEtaW (Real.arctan (Real.exp ζ)) :=
      fun ζ => Work.FTS.StrongEps.sEtaW_pos (arctan_exp_mem ζ)
    have hΘ : ∀ ζ p : ℝ, Work.FTS.StrongEps.sEtaW (Real.arctan (Real.exp (ζ + p)))
        ≤ Real.exp ((11 / 10 : ℝ) * |p|)
          * Work.FTS.StrongEps.sEtaW (Real.arctan (Real.exp ζ)) :=
      fun ζ p => sEtaW_arctan_exp_shift ζ p
    have hw' : ∀ y : ℝ × ℝ,
        Work.FTS.TransportS.leafEta (Real.exp y.1) (Real.arctan (Real.exp y.2))
          = Work.FTS.StrongEps.wtZ (Real.exp y.1)
            * Work.FTS.StrongEps.sEtaW (Real.arctan (Real.exp y.2)) := by
      intro y
      simp only [Work.FTS.TransportS.leafEta, Work.FTS.StrongEps.wtZ,
        Work.FTS.StrongEps.sEtaW]
    exact logW_shift_uniform_aux
      (Θ := fun ζ => Work.FTS.StrongEps.sEtaW (Real.arctan (Real.exp ζ)))
      (κ := 11 / 10) hΘpos hκ hΘ Work.FTS.TransportS.leafEta hw' y p
  · -- the `w²`-leaf
    subst hw
    have hΘpos : ∀ ζ : ℝ, 0 < (fun _ : ℝ => (1 : ℝ)) ζ := fun _ => one_pos
    have hΘ : ∀ ζ p : ℝ, (fun _ : ℝ => (1 : ℝ)) (ζ + p)
        ≤ Real.exp ((11 / 10 : ℝ) * |p|) * (fun _ : ℝ => (1 : ℝ)) ζ := by
      intro ζ p
      have h0 : (0 : ℝ) ≤ (11 / 10 : ℝ) * |p| :=
        mul_nonneg (by norm_num) (abs_nonneg p)
      simpa only [Pi.one_apply, mul_one] using Real.one_le_exp h0
    have hw' : ∀ y : ℝ × ℝ,
        Work.FTS.TransportS.leafOne (Real.exp y.1) (Real.arctan (Real.exp y.2))
          = Work.FTS.StrongEps.wtZ (Real.exp y.1) * (fun _ : ℝ => (1 : ℝ)) y.2 := by
      intro y
      simp only [Work.FTS.TransportS.leafOne, Work.FTS.StrongEps.wtZ, mul_one]
    exact logW_shift_uniform_aux (Θ := fun _ : ℝ => (1 : ℝ)) (κ := 11 / 10) hΘpos hκ hΘ
      Work.FTS.TransportS.leafOne hw' y p
  · -- the `γ`-leaf
    subst hw
    have hΘpos : ∀ ζ : ℝ, 0 < Work.FTS.StrongEps.sGamW α (Real.arctan (Real.exp ζ)) :=
      fun ζ => Work.FTS.StrongEps.sGamW_pos (α := α) (arctan_exp_mem ζ)
    have hΘ : ∀ ζ p : ℝ, Work.FTS.StrongEps.sGamW α (Real.arctan (Real.exp (ζ + p)))
        ≤ Real.exp ((11 / 10 : ℝ) * |p|)
          * Work.FTS.StrongEps.sGamW α (Real.arctan (Real.exp ζ)) :=
      fun ζ p => sGamW_arctan_exp_shift hα ζ p
    have hw' : ∀ y : ℝ × ℝ,
        Work.FTS.TransportS.leafGam α (Real.exp y.1) (Real.arctan (Real.exp y.2))
          = Work.FTS.StrongEps.wtZ (Real.exp y.1)
            * Work.FTS.StrongEps.sGamW α (Real.arctan (Real.exp y.2)) := by
      intro y
      simp only [Work.FTS.TransportS.leafGam, Work.FTS.StrongEps.wtZ,
        Work.FTS.StrongEps.sGamW]
    exact logW_shift_uniform_aux
      (Θ := fun ζ => Work.FTS.StrongEps.sGamW α (Real.arctan (Real.exp ζ)))
      (κ := 11 / 10) hΘpos hκ hΘ (Work.FTS.TransportS.leafGam α) hw' y p

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.IP4Prep =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TransferDeriv/IP4Prep.lean` — the bookkeeping of the level-four derivative-priced transfer

`IP4_transfer_deriv` reduces the `O(ε)`-smallness of the level-four transfer defect
`IP4 α (J_ε f) h − IP4 α f (J_ε h)` to the hypothesised *slot* transfer `hslot`.  The slot transfer
is stated for the flat pairings `wip w (mixed b a ·) (mixed b a ·)`, while the recursion
`IP4 = HkIPStep c₁'' c₂'' (HkIPStep c₁' c₂' (HkIPStep c₁ c₂ (H1IP α)))` produces the pairing at the
mixed slots `D_z^b D_θ^a` of *shifted* profiles.

This file contains the two elementary ingredients of that reduction.

* `cut u` — the profile which agrees with `u` on the open quadrant and vanishes outside.  It is the
  representative on which the slot transfer is applied: the pairing `wip` only sees the open
  quadrant, while the *integrability certificates* of the slot transfer are honest
  `Integrable`-statements over the whole plane, which can only hold for representatives that
  vanish off the quadrant.
* `mixed_comp` — the composition rule `D_z^{b'} D_θ^{a'} (D_z^b D_θ^a f) = D_z^{b'+b} D_θ^{a'+a} f`
  on the open quadrant, i.e. the fact that the slot of a slot is again a slot (it is the
  commutation of `D_θ` with the iterates of `D_z`, Clairaut's theorem on the open quadrant).
* `IsLeafW.mono` — the leaf weights of the slot transfer are indexed by the *angular* slot order
  `a`, the only constraint being `1 ≤ a` for the `γ`-weight, so the index may be raised.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The cut of a profile to the open quadrant -/

/-- The profile which is `u` on the open quadrant and `0` outside it.  The pairings `wip` of the
coercivity chapter only see the open quadrant (the boundary of `Iz × Iθ` is null), so `cut u`
represents the same slot data as `u`; on the other hand `cut u` and all its mixed derivatives
vanish off the closed quadrant, which is what makes the `Integrable`-certificates of the slot
transfer available. -/
def cut (u : Fn) : Fn := fun z θ => if 0 < z ∧ 0 < θ ∧ θ < π / 2 then u z θ else 0

@[simp] theorem cut_apply (u : Fn) (z θ : ℝ) :
    cut u z θ = if 0 < z ∧ 0 < θ ∧ θ < π / 2 then u z θ else 0 := rfl

/-- `cut u` agrees with `u` on the open quadrant. -/
theorem cut_eqOn_Q0 (u : Fn) :
    Set.EqOn (Function.uncurry (cut u)) (Function.uncurry u) Work.FTS.EllipticEst.Q0 := by
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  show cut u p.1 p.2 = u p.1 p.2
  rw [cut_apply, if_pos (show 0 < p.1 ∧ 0 < p.2 ∧ p.2 < π / 2 from ⟨hz, hθ0, hθ1⟩)]

/-- `cut u` is smooth wherever `u` is: the two agree on the open quadrant. -/
theorem smoothOpen_cut {u : Fn} (hu : Work.FTS.EllipticEst.SmoothOpen u) :
    Work.FTS.EllipticEst.SmoothOpen (cut u) :=
  Work.FTS.EllipticEst.smoothOpen_of_forall fun n =>
    (hu.forall n).congr (fun p hp => cut_eqOn_Q0 u hp)

/-- `cut u` vanishes on the complement of the product of the open half lines. -/
theorem cut_eq_zero_of_not_mem {u : Fn} {z θ : ℝ}
    (h : ¬ (0 < z ∧ 0 < θ ∧ θ < π / 2)) : cut u z θ = 0 := by
  rw [cut_apply, ite_eq_right h]

/-! ## The leaf weights of the slot transfer -/

/-- The leaf weights are indexed by the angular order `a`, and the only constraint on the index is
the guard `1 ≤ a` of the `γ`-weight: hence the index may be raised. -/
theorem IsLeafW.mono {α : ℝ} {a : ℕ} {w : ℝ → ℝ → ℝ} (h : Work.FTS.TransportS.IsLeafW α a w)
    {a' : ℕ} (ha : a ≤ a') : Work.FTS.TransportS.IsLeafW α a' w := by
  rcases h with h | h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨le_trans h1 ha, h2⟩)

/-- A leaf weight at the slot `a` is a leaf weight at every larger slot: the form used with the
composed slots. -/
theorem IsLeafW.add {α : ℝ} {a a' : ℕ} {w : ℝ → ℝ → ℝ} (h : Work.FTS.TransportS.IsLeafW α a w) :
    Work.FTS.TransportS.IsLeafW α (a + a') w :=
  IsLeafW.mono h (Nat.le_add_right a a')

/-! ## The composition of the slot operators -/

/-- **The slot of a slot is a slot**: on the open quadrant,
`D_z^{b'}D_θ^{a'}(D_z^bD_θ^a f) = D_z^{b'+b}D_θ^{a'+a} f` for `f` smooth there.  This is the
commutation of `D_θ` with the iterates of `D_z` (`DthIter_DzIter_eqOn`), which holds on the open
quadrant because the two operators carry multipliers depending on the *other* variable. -/
theorem mixed_comp {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (b a b' a' : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.mixed b' a' (Work.Spaces.mixed b a f)))
      (Function.uncurry (Work.Spaces.mixed (b' + b) (a' + a) f))
      Work.FTS.EllipticEst.Q0 := by
  have hX : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DthIter a f) := hf.DthIter a
  have h1 := Work.FTS.TransportS.DthIter_DzIter_eqOn hX b a'
  have h2 := Work.FTS.TransportS.DzIter_congrOn Work.FTS.EllipticEst.isOpen_Q0 h1 b'
  intro p hp
  have h3 := h2 hp
  change Work.Spaces.DzIter b' (Work.Spaces.DthIter a'
      (Work.Spaces.DzIter b (Work.Spaces.DthIter a f))) p.1 p.2
    = Work.Spaces.DzIter b'
      (Work.Spaces.DzIter b (Work.Spaces.DthIter a' (Work.Spaces.DthIter a f))) p.1 p.2 at h3
  change Work.Spaces.DzIter b'
        (Work.Spaces.DthIter a' (Work.Spaces.DzIter b (Work.Spaces.DthIter a f))) p.1 p.2
      = Work.Spaces.DzIter (b' + b) (Work.Spaces.DthIter (a' + a) f) p.1 p.2
  rw [h3, Work.Spaces.DthIter_add_right a' a f,
    (Work.Spaces.DzIter_add_right b' b (Work.Spaces.DthIter (a' + a) f)).symm]

/-- The shift identity `D_θ (D_z^b D_θ^a f) = D_z^b D_θ^{a+1} f` on the open quadrant, obtained
from `mixed_comp` with the outer slot `(a',b') = (1,0)`; it is the form in which the recursion
`HkIPStep` shifts the slot. -/
theorem Dth_mixed_eqOn {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (b a : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dth (Work.Spaces.mixed b a f)))
      (Function.uncurry (Work.Spaces.mixed b (a + 1) f)) Work.FTS.EllipticEst.Q0 := by
  intro p hp
  have h := mixed_comp hf b a 0 1 hp
  change Work.Spaces.mixed 0 1 (Work.Spaces.mixed b a f) p.1 p.2
    = Work.Spaces.mixed (0 + b) (1 + a) f p.1 p.2 at h
  change Work.Spaces.Dth (Work.Spaces.mixed b a f) p.1 p.2
      = Work.Spaces.mixed b (a + 1) f p.1 p.2
  rw [show Work.Spaces.Dth (Work.Spaces.mixed b a f)
      = Work.Spaces.mixed 0 1 (Work.Spaces.mixed b a f) from rfl, h,
    Nat.zero_add, Nat.add_comm 1 a]

/-! ## Slots of a profile vanishing off the open quadrant

The `Integrable`-certificates of the slot transfer are statements about the *whole* plane, while
the `ℋ^k`-membership of the paper only constrains the quadrant.  The representatives on which the
slot transfer is applied therefore have to vanish off the open quadrant — and so must all their
mixed slots, which is the content of this section.

The proof is a locality argument.  Away from the two coordinate axes the profile vanishes on a
neighbourhood of the point, so every derivative vanishes there.  On the axes two reductions
suffice: `D_z` carries the factor `z` and `D_θ` the factor `sin(2θ)`, and at a point of the
boundary of the quadrant one of the two factors vanishes, while for the other factor the relevant
slice is identically zero. -/

/-- **`D_θ` of a profile vanishing off the open quadrant vanishes off it.**  On `θ = 0` and
`θ = π/2` the factor `sin(2θ)` vanishes.  Otherwise, if `z ≤ 0` the whole angular slice is zero,
while for `z > 0` the point lies strictly outside `(0, π/2)` and the slice is zero on a
neighbourhood. -/
theorem Dth_eq_zero_of_zero_off {G : Fn}
    (hG : ∀ z θ : ℝ, ¬ (0 < z ∧ 0 < θ ∧ θ < π / 2) → G z θ = 0)
    {z θ : ℝ} (hzθ : ¬ (0 < z ∧ 0 < θ ∧ θ < π / 2)) :
    Work.Spaces.Dth G z θ = 0 := by
  show Real.sin (2 * θ) * Work.Spaces.pth G z θ = 0
  rcases eq_or_ne θ 0 with h0 | h0
  · rw [h0]; simp
  rcases eq_or_ne θ (π / 2) with h2 | h2
  · rw [h2, show 2 * (π / 2) = π from by ring, Real.sin_pi]; ring
  have hslice : ∀ᶠ θ' in 𝓝 θ, G z θ' = 0 := by
    rcases lt_trichotomy z 0 with hz | hz | hz
    · exact Filter.Eventually.of_forall fun θ' => hG z θ' (by rintro ⟨h1, -⟩; linarith)
    · subst hz
      exact Filter.Eventually.of_forall fun θ' => hG 0 θ' (by rintro ⟨h1, -⟩; exact lt_irrefl 0 h1)
    · have hth : θ < 0 ∨ π / 2 < θ := by
        by_contra h
        push_neg at h
        exact hzθ ⟨hz, lt_of_le_of_ne h.1 (Ne.symm h0), lt_of_le_of_ne h.2 h2⟩
      rcases hth with h | h
      · filter_upwards [Iio_mem_nhds h] with θ' hθ'
        rw [Set.mem_Iio] at hθ'
        exact hG z θ' (by rintro ⟨-, h2', -⟩; linarith)
      · filter_upwards [Ioi_mem_nhds h] with θ' hθ'
        rw [Set.mem_Ioi] at hθ'
        exact hG z θ' (by rintro ⟨-, -, h3'⟩; linarith)
  have hslice' : (fun θ' => G z θ') =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := hslice
  rw [Work.Spaces.pth, hslice'.deriv_eq]
  simp

/-- **`D_z` of a profile vanishing off the open quadrant vanishes off it.**  At `z = 0` the factor
`z` vanishes; for `z < 0` the radial slice is zero on a neighbourhood; for `z > 0` the angular
coordinate lies outside `(0, π/2)` and the radial slice is identically zero. -/
theorem Dz_eq_zero_of_zero_off {G : Fn}
    (hG : ∀ z θ : ℝ, ¬ (0 < z ∧ 0 < θ ∧ θ < π / 2) → G z θ = 0)
    {z θ : ℝ} (hzθ : ¬ (0 < z ∧ 0 < θ ∧ θ < π / 2)) :
    Work.Spaces.Dz G z θ = 0 := by
  show z * Work.Spaces.pz G z θ = 0
  rcases eq_or_ne z 0 with hz0 | hz0
  · rw [hz0]; ring
  have hslice : ∀ᶠ z' in 𝓝 z, G z' θ = 0 := by
    rcases lt_or_gt_of_ne hz0 with hz | hz
    · filter_upwards [Iio_mem_nhds hz] with z' hz'
      rw [Set.mem_Iio] at hz'
      exact hG z' θ (by rintro ⟨h1, -⟩; linarith)
    · have hth : θ ≤ 0 ∨ π / 2 ≤ θ := by
        by_contra h
        push_neg at h
        exact hzθ ⟨hz, h.1, h.2⟩
      rcases hth with h | h
      · exact Filter.Eventually.of_forall fun z' =>
          hG z' θ (by rintro ⟨-, h2', -⟩; linarith)
      · exact Filter.Eventually.of_forall fun z' =>
          hG z' θ (by rintro ⟨-, -, h3'⟩; linarith)
  have hslice' : (fun z' => G z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := hslice
  rw [Work.Spaces.pz, hslice'.deriv_eq]
  simp

/-- **Every mixed slot of a profile vanishing off the open quadrant vanishes off it.** -/
theorem mixed_eq_zero_of_zero_off {G : Fn}
    (hG : ∀ z θ : ℝ, ¬ (0 < z ∧ 0 < θ ∧ θ < π / 2) → G z θ = 0) :
    ∀ (b a : ℕ) (z θ : ℝ), ¬ (0 < z ∧ 0 < θ ∧ θ < π / 2) →
      Work.Spaces.mixed b a G z θ = 0 := by
  have hDth : ∀ a : ℕ, ∀ z θ : ℝ, ¬ (0 < z ∧ 0 < θ ∧ θ < π / 2) →
      Work.Spaces.DthIter a G z θ = 0 := by
    intro a
    induction a with
    | zero => exact hG
    | succ a ih => exact fun z θ h => Dth_eq_zero_of_zero_off ih h
  intro b
  induction b with
  | zero => exact fun a z θ h => hDth a z θ h
  | succ b ih =>
      intro a z θ h
      exact Dz_eq_zero_of_zero_off (G := Work.Spaces.DzIter b (Work.Spaces.DthIter a G))
        (fun z' θ' h' => ih a z' θ' h') h

/-- `cut u` vanishes off the open quadrant. -/
theorem cut_zero_off (u : Fn) :
    ∀ z θ : ℝ, ¬ (0 < z ∧ 0 < θ ∧ θ < π / 2) → cut u z θ = 0 :=
  fun z θ h => cut_eq_zero_of_not_mem h

/-- **`J_ε f` vanishes off the open quadrant** (it is defined to be `0` there). -/
theorem Jeps_zero_off (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (f : Fn) :
    ∀ z θ : ℝ, ¬ (0 < z ∧ 0 < θ ∧ θ < π / 2) → Work.FTS.StrongEps.Jeps ρ ε f z θ = 0 := by
  intro z θ h
  rw [Work.FTS.StrongEps.Jeps]
  exact ite_eq_right (by intro hc; exact h ⟨hc.1, hc.2.1, hc.2.2⟩)

/-- The slot transfer is applied to the representative `cut A₀`, which agrees with `A₀` on the
open quadrant; consequently every pairing written with `cut A₀` equals the one written with
`A₀` (`wip` only sees the open quadrant). -/
theorem mixed_cut_eqOn_Q0 (u : Fn) (b a : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.mixed b a (cut (u : Fn))))
      (Function.uncurry (Work.Spaces.mixed b a (u : Fn))) Work.FTS.EllipticEst.Q0 := by
  have h := Work.FTS.TransportS.DthIter_congrOn (V := Work.FTS.EllipticEst.Q0)
    Work.FTS.EllipticEst.isOpen_Q0 (cut_eqOn_Q0 u) a
  exact Work.FTS.TransportS.DzIter_congrOn Work.FTS.EllipticEst.isOpen_Q0 h b

/-! ## Congruence of `J_ε` on the open quadrant -/

/-- `J_ε` only depends on its argument through the values on the *open* quadrant: it samples the
argument at points of the quadrant and vanishes outside it. -/
theorem Jeps_congr_Q0 {X X' : Fn}
    (h : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → X z θ = X' z θ)
    (ρ : ℝ × ℝ → ℝ) (ε : ℝ) :
    Work.FTS.StrongEps.Jeps ρ ε X = Work.FTS.StrongEps.Jeps ρ ε X' := by
  funext z θ
  by_cases hc : 0 < z ∧ θ ∈ Set.Ioo (0 : ℝ) (π / 2)
  · rw [Work.FTS.StrongEps.Jeps, if_pos hc, Work.FTS.StrongEps.Jeps, if_pos hc]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    have hz : 0 < z * Real.exp (-p.1) := mul_pos hc.1 (Real.exp_pos _)
    have hth : Real.arctan (Real.tan θ * Real.exp (-p.2)) ∈ Set.Ioo (0 : ℝ) (π / 2) :=
      ⟨Real.arctan_pos.mpr (mul_pos (Real.tan_pos_of_pos_of_lt_pi_div_two hc.2.1 hc.2.2)
          (Real.exp_pos _)),
        Real.arctan_lt_pi_div_two _⟩
    exact congrArg (fun c : ℝ => ε⁻¹ ^ 2 * ρ (ε⁻¹ • p) * c)
      (h _ _ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hth.1, hth.2⟩))
  · rw [Work.FTS.StrongEps.Jeps, if_neg hc, Work.FTS.StrongEps.Jeps, if_neg hc]

/-- `J_ε (cut u) = J_ε u`. -/
theorem Jeps_cut (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (u : Fn) :
    Work.FTS.StrongEps.Jeps ρ ε (cut u) = Work.FTS.StrongEps.Jeps ρ ε u :=
  Jeps_congr_Q0 (fun z θ h => cut_eqOn_Q0 u h) ρ ε

/-! ## A.e. strong measurability of profiles vanishing off the open quadrant -/

/-- A function continuous on the open quadrant and vanishing outside it is a.e. strongly
measurable (it is the indicator of the open quadrant times a function continuous there). -/
theorem aestronglyMeasurable_of_zero_off {F : ℝ × ℝ → ℝ}
    (hcont : ContinuousOn F Work.FTS.EllipticEst.Q0)
    (hzero : ∀ p : ℝ × ℝ, p ∉ Work.FTS.EllipticEst.Q0 → F p = 0) :
    AEStronglyMeasurable F volume := by
  have hs : MeasurableSet Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  have h1 : F = Set.indicator Work.FTS.EllipticEst.Q0 F := by
    funext p
    by_cases hp : p ∈ Work.FTS.EllipticEst.Q0
    · rw [Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem hp, hzero p hp]
  rw [h1]
  exact (aestronglyMeasurable_indicator_iff hs).mpr (hcont.aestronglyMeasurable hs)

/-! ## Integrability of the cross term -/

/-- **The weighted cross term is integrable** when the two weighted squares are: pointwise AM–GM
on the open quadrant, and both profiles vanish outside it. -/
theorem integrable_cross_of_zero_off {ρ X Y : ℝ → ℝ → ℝ}
    (hX0 : ∀ z θ : ℝ, ¬ (0 < z ∧ 0 < θ ∧ θ < π / 2) → X z θ = 0)
    (hY0 : ∀ z θ : ℝ, ¬ (0 < z ∧ 0 < θ ∧ θ < π / 2) → Y z θ = 0)
    (hXc : ContinuousOn (Function.uncurry X) Work.FTS.EllipticEst.Q0)
    (hYc : ContinuousOn (Function.uncurry Y) Work.FTS.EllipticEst.Q0)
    (hρc : ContinuousOn (Function.uncurry ρ) Work.FTS.EllipticEst.Q0)
    (hρ0 : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ ρ z θ)
    (hX : MeasureTheory.Integrable (Function.uncurry (fun z θ => ρ z θ * (X z θ) ^ 2)) volume)
    (hY : MeasureTheory.Integrable (Function.uncurry (fun z θ => ρ z θ * (Y z θ) ^ 2)) volume) :
    MeasureTheory.Integrable (Function.uncurry (fun z θ => ρ z θ * X z θ * Y z θ)) volume := by
  refine Integrable.mono' (hX.add hY) ?_ ?_
  · refine aestronglyMeasurable_of_zero_off ((hρc.mul hXc).mul hYc) ?_
    intro p hp
    show ρ p.1 p.2 * X p.1 p.2 * Y p.1 p.2 = 0
    rw [hX0 p.1 p.2 hp, hY0 p.1 p.2 hp]
    ring
  · filter_upwards with p
    obtain ⟨z, θ⟩ := p
    simp only [Pi.add_apply, Function.uncurry_apply_pair]
    by_cases hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0
    · obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      have hρz : 0 ≤ ρ z θ := hρ0 z (le_of_lt hz) θ ⟨le_of_lt hθ0, le_of_lt hθ1⟩
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hρz]
      have h2 : 2 * |X z θ| * |Y z θ| ≤ (X z θ) ^ 2 + (Y z θ) ^ 2 := by
        have h := sq_nonneg (|X z θ| - |Y z θ|)
        rw [sub_sq, sq_abs, sq_abs] at h
        nlinarith [h]
      nlinarith [h2, hρz, abs_nonneg (X z θ), abs_nonneg (Y z θ)]
    · have hP : ¬ (0 < z ∧ 0 < θ ∧ θ < π / 2) := fun hc => hp (Work.FTS.EllipticEst.mem_Q0.mpr hc)
      rw [hX0 z θ hP, hY0 z θ hP]
      simp




end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Decay3Aux.ellPkg_mono =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology MeasureTheory

namespace Work.FTS.StrongEps.E4R3.Decay3Aux

set_option autoImplicit false

/-- `α ^ (-(1/2)) ≥ 0` for **every** real `α`.  For `α ≥ 0` this is `Real.rpow_nonneg`; for
`α < 0` the Mathlib definition of `rpow` is `exp (log α * y) * cos (y π)`, and the factor
`cos (-(1/2) π) = 0`.  (No positivity of `α` is available in `ellPkg_mono`, unlike in its
sibling `starPkg_mono`.) -/
theorem rpow_neg_half_nonneg (α : ℝ) : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := by
  by_cases hα : 0 ≤ α
  · exact Real.rpow_nonneg hα _
  · rw [Real.rpow_def_of_neg (lt_of_not_ge hα)]
    have hc : Real.cos (-(1 / 2 : ℝ) * Real.pi) = 0 := by
      rw [show -(1 / 2 : ℝ) * Real.pi = -(Real.pi / 2) by ring, Real.cos_neg, Real.cos_pi_div_two]
    rw [hc, mul_zero]

/-- Monotonicity of the elliptic package in the constant `Ce`.  Every `Ce`-occurrence in
`EllPkgGo`/`EllPkgK` is a single estimate of the shape `A ≤ Ce * B` with `B ≥ 0`
(`B = Xn α g`, `B = HkNorm α k g`, or `B = α ^ (-(1/2)) * Xn α g`); the non-estimate fields
are `Ce`-free.  Hence `Ce ≤ Ce'` transports the whole package. -/
theorem ellPkg_mono {α Ce Ce' : ℝ} (h : Ce ≤ Ce') {k : ℕ} {g Φg : Work.FTS.Galerkin.Fn}
    (hp : Work.FTS.VocabO.EllPkgGo α Ce g Φg ∧ Work.FTS.ClassC.EllPkgK α k Ce g Φg) :
    Work.FTS.VocabO.EllPkgGo α Ce' g Φg ∧ Work.FTS.ClassC.EllPkgK α k Ce' g Φg := by
  obtain ⟨hGo, hK⟩ := hp
  have hA : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := rpow_neg_half_nonneg α
  have hXn : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hHk : (0 : ℝ) ≤ Work.Spaces.HkNorm α k g := Work.Spaces.HkNorm_nonneg α k g
  refine ⟨{ hGo with
    R := ⟨hGo.R.1, le_trans hGo.R.2 (mul_le_mul_of_nonneg_right h hXn)⟩,
    U := ⟨hGo.U.1, le_trans hGo.U.2 (mul_le_mul_of_nonneg_right h hXn)⟩,
    V := ⟨hGo.V.1, le_trans hGo.V.2 (mul_le_mul_of_nonneg_right h hXn)⟩,
    Vth := ⟨hGo.Vth.1,
      le_trans hGo.Vth.2
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hA) hXn)⟩ }, ?_⟩
  exact { hK with
    R := ⟨hK.R.1, le_trans hK.R.2 (mul_le_mul_of_nonneg_right h hHk)⟩,
    U := ⟨hK.U.1, le_trans hK.U.2 (mul_le_mul_of_nonneg_right h hHk)⟩,
    V := ⟨hK.V.1, le_trans hK.V.2 (mul_le_mul_of_nonneg_right h hHk)⟩ }

end Work.FTS.StrongEps.E4R3.Decay3Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (Xn)
open Work.FTS.VocabO (HQo CoefTh CoefThMem WDp WDMem)
open Work.Spaces (HkMem HkSq HkNorm Dz Dth)

set_option autoImplicit false

/-- The abbreviation of the concrete level-four coercive pairing of the a-priori chapter. -/
abbrev IP4 (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) : ℝ → Fn → Fn → ℝ :=
  Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂''

/-- **The honest `g`-side bundle of the level-four transport clauses**, in the form in which the
class-`C` data of the route supplies them: open-quadrant smoothness, `ℋ⁴`- and `ℋ⁵`-honesty
and the `L¹`-decay of the plain partials (`DecayAll 4`).

`ClassC α g` together with `CoerAdmO α g` gives `SmoothOpen g` and `HkMem α k g` for every
`k ≤ 10`; the `DecayAll 4 g` conjunct follows from `BdryTraces α 6 g` (a field of `ClassC`) by
`N4C.decayAll_of_bdryTraces`. -/
def HAdm (α : ℝ) (g : Fn) : Prop :=
  Work.FTS.EllipticEst.SmoothOpen g ∧ HkMem α 4 g ∧ HkMem α 5 g ∧ HkMem α 6 g ∧
    Work.Spaces.DecayAll 4 g

/-- **The honest clause bundle of the level-four pairing** — the coefficient-free form of the
clause list of `OpenPkg.N4Extra'` which the rows consume, with the *second* argument in the
honest class `HQo α 4` instead of the frozen `RegQ α 4` (whose `SmoothQuad` conjunct is not
available along the route).

The clause list is exactly the one used by the row proofs of `Nonlinear.Open`:
`cs`, `add`, `smul`, `neg`, `congr` (algebraic), `dz` (the lossless `D_z`-self-pairing),
`t1` (`D_θ`-transport with an `ℋ⁴`-coefficient), `t2`/`t3` (`D_z`-transport with a flat
resp. `𝒲^{4,∞}`-coefficient) and `t4` (`D_θ`-transport with a `𝒲^{4,∞}`-coefficient). -/
structure N4ExtraH (IP : ℝ → Fn → Fn → ℝ) (α₂ Ct : ℝ) : Prop where
  /-- positivity of the two constants. -/
  pos : 0 < Ct ∧ 0 < α₂
  /-- Cauchy–Schwarz against the `ℋ⁴`-norm, on the honest class. -/
  cs : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, HQo α 4 f → HQo α 4 g →
    |IP α f g| ≤ Ct * Xn α f * Xn α g
  /-- additivity in the first argument. -/
  add : ∀ α ∈ Set.Ioc 0 α₂, ∀ f₁ f₂ g : Fn, HQo α 4 f₁ → HQo α 4 f₂ → HQo α 4 g →
    IP α (f₁ + f₂) g = IP α f₁ g + IP α f₂ g
  /-- homogeneity in the first argument. -/
  smul : ∀ α ∈ Set.Ioc 0 α₂, ∀ (c : ℝ), ∀ f g : Fn, HQo α 4 f → HQo α 4 g →
    IP α (fun z θ => c * f z θ) g = c * IP α f g
  /-- negation in the first argument. -/
  neg : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, HQo α 4 f → HQo α 4 g →
    IP α (fun z θ => -f z θ) g = -IP α f g
  /-- `IP` only depends on the first argument through its values on the open quadrant. -/
  congr : ∀ α ∈ Set.Ioc 0 α₂, ∀ f f' g : Fn, HQo α 4 f → HQo α 4 f' → HQo α 4 g →
    (∀ z θ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) → IP α f g = IP α f' g
  /-- the lossless `D_z`-self-pairing (design §5 T5), on the open coercivity class. -/
  dz : ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn, Work.FTS.StrongEps.EpsE4Thr.RegQo α 5 g →
    |IP α (Dz g) g| ≤ Ct * Xn α g ^ 2
  /-- `T1Q`: transport with `D_θ` and an `ℋ⁴`-coefficient (tex 1119). -/
  t1 : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, HQo α 4 f → Work.FTS.EllipticEst.SmoothOpen g →
    HkMem α 4 g → Work.Spaces.DecayAll 4 g →
    |IP α (fun z θ => f z θ * Dth g z θ) g| ≤ Ct * α ^ (-(1 / 2 : ℝ)) * Xn α f * Xn α g ^ 2
  /-- `T2S`: transport with `D_z` and a flat angular coefficient. -/
  t2 : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, Work.FTS.EllipticEst.SmoothOpen f → HkMem α 4 f →
    CoefThMem 1 f → Work.FTS.EllipticEst.SmoothOpen g → HkMem α 4 g → HkMem α 5 g →
    Work.Spaces.DecayAll 4 g →
    |IP α (fun z θ => f z θ * Dz g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * (Xn α f + CoefTh 1 f) * Xn α g ^ 2
  /-- `T3S`: transport with `D_z` and a `𝒲^{4,∞}`-coefficient. -/
  t3 : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, Work.FTS.EllipticEst.SmoothOpen f →
    Work.Spaces.WlInfMem α 4 f → CoefThMem 3 f → Work.FTS.EllipticEst.SmoothOpen g →
    HkMem α 4 g → HkMem α 5 g → Work.Spaces.DecayAll 4 g →
    |IP α (fun z θ => f z θ * Dz g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * (Work.Spaces.WlInf α 4 f + CoefTh 3 f) * Xn α g ^ 2
  /-- `T3Q` with `D_θ` and a `𝒲^{4,∞}`-coefficient, in the `D`-sup norm. -/
  t4 : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, Work.FTS.EllipticEst.SmoothOpen f → WDMem 4 f →
    Work.FTS.EllipticEst.SmoothOpen g →
    HkMem α 4 g → HkMem α 5 g → Work.Spaces.DecayAll 4 g →
    |IP α (fun z θ => f z θ * Dth g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * WDp 4 f * Xn α g ^ 2

/-! ## Elementary projections

The two classes of the route: `ClassC α g` (the honest class of the elliptic chapter) and
`CoerAdmO α g` (the open coercivity class). -/

/-- `ClassC` refines the honest `ℋ⁴`-class `HQo α 4`. -/
theorem classC_hqo4 {α : ℝ} {g : Fn} (h : Work.FTS.ClassC.ClassC α g) : HQo α 4 g :=
  ⟨h.reg, Work.FTS.OpenPkg.HkMem_mono_open h.reg 4 (by norm_num) h.mem⟩




/-- **The context of one honest §8 row**: the hypotheses of the target, namely the class-`C`
profile data (`ClassC α g` and the open coercivity class `CoerAdmO α g`), the two open-quadrant
elliptic packages of `Φs` and `Φg`, and the ranges of `α`.

This is the honest (class-`C`) replacement of the frozen row context `NonlinRows.Ctx` /
`Open2.CtxO` (which carry `GalClass α g`, i.e. `SmoothQuad`, not available along the route). -/
def CtxT (Cs Ce α₂ α : ℝ) (g Φs Φg : Fn) : Prop :=
  0 < α ∧ α ≤ 1 ∧ α ≤ α₂ ∧ Work.FTS.ClassC.ClassC α g ∧
    Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α g ∧
    Work.FTS.VocabO2.StarPkgo2 α Cs Φs ∧ Work.FTS.VocabO.EllPkgGo α Ce g Φg

theorem CtxT.hα {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) : 0 < α := h.1

theorem CtxT.hα1 {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) : α ≤ 1 :=
  h.2.1

theorem CtxT.hαα₂ {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) : α ≤ α₂ :=
  h.2.2.1

theorem CtxT.hg {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.FTS.ClassC.ClassC α g := h.2.2.2.1

theorem CtxT.hco {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α g := h.2.2.2.2.1

theorem CtxT.hs {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.FTS.VocabO2.StarPkgo2 α Cs Φs := h.2.2.2.2.2.1

theorem CtxT.hell {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    Work.FTS.VocabO.EllPkgGo α Ce g Φg := h.2.2.2.2.2.2

/-- The honest profile bundle `HAdm α g` from the row context, given the decay (which
`ClassC` supplies via `N4C.decayAll_of_classC`). -/
theorem CtxT.hAdm {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg)
    (hdec : Work.Spaces.DecayAll 4 g) : HAdm α g :=
  ⟨h.hg.reg, Work.FTS.OpenPkg.HkMem_mono_open h.hg.reg 4 (by norm_num) h.hg.mem,
    Work.FTS.OpenPkg.HkMem_mono_open h.hg.reg 5 (by norm_num) h.hg.mem,
    Work.FTS.OpenPkg.HkMem_mono_open h.hg.reg 6 (by norm_num) h.hg.mem, hdec⟩

/-- The honest `ℋ⁴`-class of the profile, from the row context. -/
theorem CtxT.hqo4 {Cs Ce α₂ α : ℝ} {g Φs Φg : Fn} (h : CtxT Cs Ce α₂ α g Φs Φg) :
    HQo α 4 g := classC_hqo4 h.hg


/-! ## The honest row table

The honest (class-`C`) version of the §8 row bundle: the three row groups
(`Nonlinear.Pieces.N0Rows`, `VocabO2.NRows2`, `Nonlinear.Pieces.AuxRows`) and the `ℋ⁴`-honesty
table `OpenPkg.PiecesHk`, all in the context `CtxT` (class-`C` data and the open-quadrant
packages).  The single constant of each group is uniform in `α, g, Φs, Φg`. -/
structure RowsT (IP : ℝ → Fn → Fn → ℝ) (α₂ Ce Cs : ℝ) where
  /-- the constant of rows 1--7. -/
  K₁ : ℝ
  /-- the constant of rows 8--26. -/
  K₂ : ℝ
  /-- the constant of the auxiliary rows. -/
  K₃ : ℝ
  hK₁ : 0 < K₁
  hK₂ : 0 < K₂
  hK₃ : 0 < K₃
  /-- rows 1--7 (the `N₀`-block). -/
  rowsN0 : ∀ {α : ℝ} {g Φs Φg : Fn}, CtxT Cs Ce α₂ α g Φs Φg →
    Work.FTS.Nonlinear.Pieces.N0Rows IP α K₁ g Φs Φg
  /-- rows 8--26 (the `N`-block). -/
  rowsN : ∀ {α : ℝ} {g Φs Φg : Fn}, CtxT Cs Ce α₂ α g Φs Φg →
    Work.FTS.VocabO2.NRows2 IP α K₂ g Φs Φg
  /-- the auxiliary rows `rak`, `rl0`--`rl2`. -/
  rowsAux : ∀ {α : ℝ} {g Φs Φg : Fn}, CtxT Cs Ce α₂ α g Φs Φg →
    Work.FTS.Nonlinear.Pieces.AuxRows IP α K₃ g Φs Φg
  /-- the `ℋ⁴`-honesty of every piece and of the three blocks. -/
  hk : ∀ {α : ℝ} {g Φs Φg : Fn}, CtxT Cs Ce α₂ α g Φs Φg →
    Work.FTS.OpenPkg.PiecesHk α g Φs Φg
  /-- the two exact splits of `N₀` and `N`, and the collapse of `N_*`. -/
  splits : ∀ {α : ℝ} {g Φs Φg : Fn}, CtxT Cs Ce α₂ α g Φs Φg →
    Work.FTS.NonlinRows.SplitsData α g Φs Φg

/-- **The clause bundle is monotone in the range `α₂`**: a bundle on `(0, α₂]` restricts to
`(0, α₂']` for `α₂' ≤ α₂`. -/
theorem N4ExtraH.mono {IP : ℝ → Fn → Fn → ℝ} {α₂ α₂' Ct : ℝ} (hα₂' : α₂' ≤ α₂)
    (hα₂'pos : 0 < α₂') (h : N4ExtraH IP α₂ Ct) : N4ExtraH IP α₂' Ct :=
  ⟨⟨h.pos.1, hα₂'pos⟩,
   fun α hα f g hf hg => h.cs α ⟨hα.1, le_trans hα.2 hα₂'⟩ f g hf hg,
   fun α hα f₁ f₂ g h₁ h₂ h₃ => h.add α ⟨hα.1, le_trans hα.2 hα₂'⟩ f₁ f₂ g h₁ h₂ h₃,
   fun α hα c f g h₁ h₂ => h.smul α ⟨hα.1, le_trans hα.2 hα₂'⟩ c f g h₁ h₂,
   fun α hα f g h₁ h₂ => h.neg α ⟨hα.1, le_trans hα.2 hα₂'⟩ f g h₁ h₂,
   fun α hα f f' g h₁ h₂ h₃ hh => h.congr α ⟨hα.1, le_trans hα.2 hα₂'⟩ f f' g h₁ h₂ h₃ hh,
   fun α hα f hf => h.dz α ⟨hα.1, le_trans hα.2 hα₂'⟩ f hf,
   fun α hα f g h₁ h₂ h₃ h₄ => h.t1 α ⟨hα.1, le_trans hα.2 hα₂'⟩ f g h₁ h₂ h₃ h₄,
   fun α hα f g h₁ h₂ h₃ h₄ h₅ h₆ h₇ =>
     h.t2 α ⟨hα.1, le_trans hα.2 hα₂'⟩ f g h₁ h₂ h₃ h₄ h₅ h₆ h₇,
   fun α hα f g h₁ h₂ h₃ h₄ h₅ h₆ h₇ =>
     h.t3 α ⟨hα.1, le_trans hα.2 hα₂'⟩ f g h₁ h₂ h₃ h₄ h₅ h₆ h₇,
   fun α hα f g h₁ h₂ h₃ h₄ h₅ h₆ =>
     h.t4 α ⟨hα.1, le_trans hα.2 hα₂'⟩ f g h₁ h₂ h₃ h₄ h₅ h₆⟩

end Work.FTS.StrongEps.E4R3.N4C
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux.HkIntegrand_four_perz_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Integrability of a finite sum of integrable functions -/

private lemma integrable_finsetSum {ι : Type*} (s : Finset ι) {g : ι → ℝ → ℝ}
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

/-! ## The per-`z` bound for a mixed slot -/

theorem mixed_slot_perz_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ {f : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
      ∀ (i j : ℕ), 1 ≤ i → i + j ≤ 4 → ∀ {z : ℝ}, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ C * (1 + (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α 6 f := by
  obtain ⟨CB, hCBpos, hCB⟩ := Work.FTS.StrongPersist.N6.sliceAng_le6
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
  have hHk := Work.Spaces.HkSq_nonneg α 6 f
  calc (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed j i f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ (Work.Spaces.w z) ^ 2 * (CB * Work.Spaces.HkSq α 6 f) :=
        mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ ≤ CB * (1 + (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α 6 f := by
        nlinarith [hCBpos, hHk, sq_nonneg (Work.Spaces.w z)]

/-! ## Integrability of the individual summands of the level-4 integrand -/

private lemma integrableOn_if_mixed (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (i j : ℕ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ 4
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      Work.Spaces.Iθ := by
  by_cases h : 1 ≤ i ∧ i + j ≤ 4
  · rw [show (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ 4
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        = fun θ : ℝ => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 from by
      funext θ; rw [if_pos h]]
    refine MeasureTheory.Integrable.mono' (hmem.1 z (Set.mem_Ici.mpr hz.le))
      (Work.FTS.GalBasis.cc.aesm_slice_mixed_Wt_sq hF α j i hz) ?_
    rw [MeasureTheory.ae_restrict_iff' (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)]
    exact Filter.Eventually.of_forall fun θ _ => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ i j h.1 (by omega)
  · rw [show (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ 4
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        = fun _ : ℝ => (0 : ℝ) from by
      funext θ; rw [if_neg h]]
    exact MeasureTheory.integrableOn_zero

/-! ## The target -/

theorem HkIntegrand_four_perz_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ {f : ℝ → ℝ → ℝ},
      Work.FTS.ClassC.ClassC α f → ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        ≤ C * (1 + (Work.Spaces.w z) ^ 2) * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 := by
  obtain ⟨Cz, hCzpos, hCz⟩ := Work.FTS.StrongEps.E5Aux.HkIntegrand_zslot_perz_le
  obtain ⟨Cm, hCmpos, hCm⟩ := mixed_slot_perz_le
  refine ⟨5 * Cz + 25 * Cm, by positivity, ?_⟩
  intro α hα f hf z hz
  obtain ⟨hα0, hα1⟩ := hα
  have hαI : α ∈ Set.Ioc 0 1 := ⟨hα0, hα1⟩
  have hreg : Work.FTS.EllipticEst.SmoothOpen f := hf.reg
  have hmem7 : Work.Spaces.HkMem α 7 f := hf.mem
  have hmem6 : Work.Spaces.HkMem α 6 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hreg 6 (by norm_num) hmem7
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hreg 4 (by norm_num) hmem7
  have htr : Work.FTS.Nonlin.BdryTraces α 6 f := hf.tr
  have hXsq : Work.Spaces.HkSq α 6 f ≤ (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 := by
    have h2 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
    have h3 : 0 ≤ Work.FTS.StrongGlobal.Xn6 α f := Work.Spaces.HkNorm_nonneg α 6 f
    have h4 : Work.FTS.StrongGlobal.Xn6 α f = Real.sqrt (Work.Spaces.HkSq α 6 f) := rfl
    rw [h4]
    nlinarith [Real.sq_sqrt h2, h3, h2]
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- the degenerate case `z = 0`
    subst hz0
    have hzero : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f 0 θ) = 0 := by
      rw [show (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 f 0 θ) = fun _ => (0 : ℝ) from
        funext fun θ => Work.Spaces.HkIntegrand_zero_z α 4 f θ]
      simp
    rw [hzero]
    have hw0 : (Work.Spaces.w 0) ^ 2 = 0 := by rw [Work.Spaces.w]; norm_num
    rw [hw0]
    have hX0 : 0 ≤ Work.FTS.StrongGlobal.Xn6 α f := Work.Spaces.HkNorm_nonneg α 6 f
    have hcoef : 0 < 5 * Cz + 25 * Cm := by positivity
    nlinarith [hX0]
  · -- the main case `z > 0`
    have hPint : MeasureTheory.Integrable
        (fun θ : ℝ => ∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      integrable_finsetSum _ (fun i hi => Work.FTS.EllipticEst.integrableOn_zSummand α 4 hreg
        hmem4 i (by rw [Finset.mem_range] at hi; omega) (Set.mem_Ici.mpr hzpos.le))
    have hMint : MeasureTheory.Integrable
        (fun θ : ℝ => ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4
            then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      integrable_finsetSum _
        (fun i _ => integrable_finsetSum _
          (fun j _ => integrableOn_if_mixed α hreg hmem4 i j hzpos))
    have hdef : (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 f z θ)
        = fun θ : ℝ => (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
              (if 1 ≤ i ∧ i + j ≤ 4
                then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
      funext θ; rw [Work.Spaces.HkIntegrand]
    rw [hdef, MeasureTheory.integral_add hPint hMint]
    -- the bound for the pure-`z` part
    have hPbound : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ 5 * (Cz * (1 + (Work.Spaces.w z) ^ 2)
            * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2) := by
      rw [MeasureTheory.integral_finsetSum (s := Finset.range 5) (hf := fun i hi =>
        Work.FTS.EllipticEst.integrableOn_zSummand α 4 hreg hmem4 i
          (by rw [Finset.mem_range] at hi; omega) (Set.mem_Ici.mpr hzpos.le))]
      calc ∑ i ∈ Finset.range 5, (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ ∑ _i ∈ Finset.range 5, (Cz * (1 + (Work.Spaces.w z) ^ 2)
              * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2) :=
            Finset.sum_le_sum fun i hi => hCz α hαI hreg hmem6 htr i
              (by rw [Finset.mem_range] at hi; omega) z hz
        _ = 5 * (Cz * (1 + (Work.Spaces.w z) ^ 2)
              * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
    -- the bound for the mixed part
    have hMbound : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4
            then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ 25 * (Cm * (1 + (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α 6 f) := by
      rw [MeasureTheory.integral_finsetSum (s := Finset.range 5) (hf := fun i _ =>
        integrable_finsetSum _ (fun j _ => integrableOn_if_mixed α hreg hmem4 i j hzpos))]
      calc ∑ i ∈ Finset.range 5, (∫ θ in Work.Spaces.Iθ, ∑ j ∈ Finset.range 5,
              (if 1 ≤ i ∧ i + j ≤ 4
                then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ ∑ _i ∈ Finset.range 5, (5 * (Cm * (1 + (Work.Spaces.w z) ^ 2)
              * Work.Spaces.HkSq α 6 f)) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [MeasureTheory.integral_finsetSum (s := Finset.range 5) (hf := fun j _ =>
              integrableOn_if_mixed α hreg hmem4 i j hzpos)]
            calc ∑ j ∈ Finset.range 5, (∫ θ in Work.Spaces.Iθ,
                    (if 1 ≤ i ∧ i + j ≤ 4
                      then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
                ≤ ∑ _j ∈ Finset.range 5, (Cm * (1 + (Work.Spaces.w z) ^ 2)
                    * Work.Spaces.HkSq α 6 f) := by
                  refine Finset.sum_le_sum fun j _ => ?_
                  by_cases hij : 1 ≤ i ∧ i + j ≤ 4
                  · simp only [if_pos hij]
                    exact hCm α hαI hreg hmem6 i j hij.1 (by omega) hzpos
                  · simp only [if_neg hij]
                    have h1 : 0 ≤ Cm * (1 + (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α 6 f := by
                      have := Work.Spaces.HkSq_nonneg α 6 f
                      positivity
                    simpa using h1
              _ = 5 * (Cm * (1 + (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α 6 f) := by
                  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
        _ = 25 * (Cm * (1 + (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α 6 f) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    refine le_trans (add_le_add hPbound hMbound) ?_
    have hPnn : 0 ≤ (1 : ℝ) + (Work.Spaces.w z) ^ 2 := by positivity
    have hX2nn : 0 ≤ (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 := sq_nonneg _
    have hkey : 25 * (Cm * (1 + (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α 6 f)
        ≤ 25 * (Cm * (1 + (Work.Spaces.w z) ^ 2)
            * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2) := by
      have h1 : Cm * (1 + (Work.Spaces.w z) ^ 2) * Work.Spaces.HkSq α 6 f
          ≤ Cm * (1 + (Work.Spaces.w z) ^ 2) * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 :=
        mul_le_mul_of_nonneg_left hXsq (by positivity)
      exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    nlinarith [hkey, hPbound, hMbound, hPnn, hX2nn, hXsq, hCzpos, hCmpos,
      Work.Spaces.HkSq_nonneg α 6 f, Work.Spaces.HkNorm_nonneg α 6 f]

end Work.FTS.StrongEps.E5Aux
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5Clamp =====
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

/-- **The quadrant clamp**: the limit profile `F τ` on the open quadrant, the datum elsewhere. -/
def clampQ (F : ℝ → Fn) (g₀ : Fn) : Fam := fun z θ τ =>
  if z ∈ Set.Ioi 0 then (if θ ∈ Set.Ioo 0 (π / 2) then F τ z θ else g₀ z θ) else g₀ z θ

theorem clampQ_of_mem {F : ℝ → Fn} {g₀ : Fn} {z θ τ : ℝ}
    (hz : z ∈ Set.Ioi (0 : ℝ)) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    clampQ F g₀ z θ τ = F τ z θ := by
  rw [clampQ, if_pos hz, if_pos hθ]

theorem clampQ_of_not_mem_z {F : ℝ → Fn} {g₀ : Fn} {z θ τ : ℝ}
    (hz : z ∉ Set.Ioi (0 : ℝ)) : clampQ F g₀ z θ τ = g₀ z θ := by
  rw [clampQ, if_neg hz]

theorem clampQ_of_not_mem_θ {F : ℝ → Fn} {g₀ : Fn} {z θ τ : ℝ}
    (hz : z ∈ Set.Ioi (0 : ℝ)) (hθ : θ ∉ Set.Ioo (0 : ℝ) (π / 2)) :
    clampQ F g₀ z θ τ = g₀ z θ := by
  rw [clampQ, if_pos hz, if_neg hθ]


/-- The `ℋᵏ`-square is unchanged by the clamp. -/
theorem clampQ_hkSq (α : ℝ) (k : ℕ) (F : ℝ → Fn) (g₀ : Fn) (τ : ℝ) :
    Work.Spaces.HkSq α k (slice (clampQ F g₀) τ) = Work.Spaces.HkSq α k (F τ) :=
  Work.FTS.EllipticEst.HkSq_congr_open α k
    (fun z θ hz hθ hθ2 => clampQ_of_mem hz ⟨hθ, hθ2⟩)

/-- The `ℋᵏ`-norm is unchanged by the clamp. -/
theorem clampQ_hkNorm (α : ℝ) (k : ℕ) (F : ℝ → Fn) (g₀ : Fn) (τ : ℝ) :
    Work.Spaces.HkNorm α k (slice (clampQ F g₀) τ) = Work.Spaces.HkNorm α k (F τ) := by
  rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, clampQ_hkSq]

/-- The `ℋᵏ`-membership is unchanged by the clamp. -/
theorem clampQ_hkMem (α : ℝ) (k : ℕ) {F : ℝ → Fn} {g₀ : Fn} {τ : ℝ}
    (h : Work.Spaces.HkMem α k (F τ)) : Work.Spaces.HkMem α k (slice (clampQ F g₀) τ) :=
  Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k h
    (fun z hz θ hθ => (clampQ_of_mem hz hθ).symm)

/-- **`init` for the quadrant clamp.** -/
theorem clampQ_init {F : ℝ → Fn} {g₀ : Fn}
    (hF : ∀ z θ, z ∈ Set.Ioi (0 : ℝ) → θ ∈ Set.Ioo (0 : ℝ) (π / 2) →
      F 0 z θ = g₀ z θ) :
    ∀ z θ, clampQ F g₀ z θ 0 = g₀ z θ := by
  intro z θ
  by_cases hz : z ∈ Set.Ioi (0 : ℝ)
  · by_cases hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)
    · rw [clampQ_of_mem hz hθ]; exact hF z θ hz hθ
    · rw [clampQ_of_not_mem_θ hz hθ]
  · rw [clampQ_of_not_mem_z hz]

/-- **`vanish` for the quadrant clamp**, from the datum's angular vanishing. -/
theorem clampQ_vanish {F : ℝ → Fn} {g₀ : Fn}
    (h0 : ∀ z, 0 ≤ z → g₀ z 0 = 0 ∧ g₀ z (π / 2) = 0) :
    ∀ τ z, 0 ≤ z → clampQ F g₀ z 0 τ = 0 ∧ clampQ F g₀ z (π / 2) τ = 0 := by
  intro τ z hz
  rcases eq_or_lt_of_le hz with h | h
  · subst h
    have hzn : (0 : ℝ) ∉ Set.Ioi (0 : ℝ) := by simp
    refine ⟨?_, ?_⟩
    · rw [clampQ_of_not_mem_z hzn]; exact (h0 0 le_rfl).1
    · rw [clampQ_of_not_mem_z hzn]; exact (h0 0 le_rfl).2
  · have hzi : z ∈ Set.Ioi (0 : ℝ) := h
    have h0n : (0 : ℝ) ∉ Set.Ioo (0 : ℝ) (π / 2) := by simp
    have h1n : (π / 2 : ℝ) ∉ Set.Ioo (0 : ℝ) (π / 2) := by simp [Set.mem_Ioo]
    rw [clampQ_of_not_mem_θ hzi h0n, clampQ_of_not_mem_θ hzi h1n]
    exact h0 z hz

/-- The clamp is `C^n` in space wherever the limit profile is. -/
theorem clampQ_contDiffOn {n : ℕ} {F : ℝ → Fn} {g₀ : Fn} {τ : ℝ}
    (h : ContDiffOn ℝ n (Function.uncurry (F τ)) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ n (Function.uncurry (slice (clampQ F g₀) τ)) Work.FTS.EllipticEst.Q0 :=
  h.congr (fun p hp => clampQ_of_mem hp.1 ⟨hp.2.1, hp.2.2⟩)


/-- Continuity in the fake time transports to the clamp on the open quadrant. -/
theorem clampQ_continuousOn {F : ℝ → Fn} {g₀ : Fn} {z θ : ℝ} {T : ℝ}
    (hz : z ∈ Set.Ioi (0 : ℝ)) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2))
    (h : ContinuousOn (fun τ => F τ z θ) (Set.Icc 0 T)) :
    ContinuousOn (fun τ => clampQ F g₀ z θ τ) (Set.Icc 0 T) :=
  h.congr (fun τ _ => clampQ_of_mem hz hθ)

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.E2_norm_OAux.RadSBase =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E2O

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 2000000

abbrev IoiA : Set ℝ := Set.Ioi (0 : ℝ)

/-! ## Bridges between the two `L₁₂` vocabularies -/

/-- `Coercivity.L12f` is the paper's `L₁₂`. -/
theorem L12f_eq_elliptic (f : ℝ → ℝ → ℝ) :
    Work.Coercivity.L12f f = Work.Elliptic.L12 f :=
  Work.Coercivity.L12f_eq_Elliptic_L12 f

/-- `Construction.L12` is the paper's `L₁₂`. -/
theorem constructionL12_eq_elliptic (f : ℝ → ℝ → ℝ) :
    Work.Construction.L12 f = Work.Elliptic.L12 f :=
  Work.FTS.H2.constructionL12_eq_ellipticL12 f

/-! ## `L₁₂ f` is `C⁴` on `(0,∞)` in the open class -/

/-- **`L₁₂ f` is `C⁴` on `(0,∞)`** for a smooth-open, `ℋ⁵`-honest datum. -/
theorem contDiffOn_four_L12f (α : ℝ) {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hO : Work.FTS.EllipticEst.SmoothOpen f) (hmem5 : Work.Spaces.HkMem α 5 f) :
    ContDiffOn ℝ 4 (Work.Coercivity.L12f f) (Set.Ioi 0) := by
  have h := (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk α 5 f hO hmem5
    (by norm_num : 2 ≤ 5)).1
  rw [← L12f_eq_elliptic f] at h
  exact h

/-! ## The index-raising recursion for `L₁₂ f` -/

/-- **`D_z^c (L₁₂ f) = −Qang f (c−1)`** on `(0,∞)`, for `1 ≤ c ≤ 3` (the `OpenPkg` bundle). -/
theorem DzdIter_L12f_eq_neg_Qang_O (α : ℝ) {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hO : Work.FTS.EllipticEst.SmoothOpen f) (hmem4 : Work.Spaces.HkMem α 4 f)
    (hl12 : Work.Construction.L12 f 0 = 0) :
    ∀ c : ℕ, 1 ≤ c → c ≤ 3 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter c (Work.Coercivity.L12f f) z = - Work.Elliptic.Qang f (c - 1) z := by
  have h0e : Work.Elliptic.L12 f 0 = 0 := by
    rw [← constructionL12_eq_elliptic f]; exact hl12
  have hb := Work.FTS.OpenPkg.l12_open_bundle α f hα hα1 hO hmem4 h0e
  intro c hc hc3 z hz
  have h := hb.1 (c - 1) (by omega) z hz
  rw [show c - 1 + 1 = c from by omega] at h
  rw [L12f_eq_elliptic]
  exact h

/-! ## The angular-moment tower in the open class -/

/-- **`D_z^i (Qang f 0) = Qang f i` on `(0,∞)`** for `i ≤ 3`. -/
theorem DzdIter_Qang_open {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) :
    ∀ i ≤ 3, ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang f 0 z) z = Work.Elliptic.Qang f i z := by
  have hderiv : ∀ j ≤ 2, ∀ z : ℝ, 0 < z →
      HasDerivAt (fun z => Work.Elliptic.Qang f j z) (Work.Elliptic.Qang f (j + 1) z / z) z :=
    fun j hj z hz => Work.FTS.OpenPkg.QangOpen.hasDerivAt_Qang_open α f hO hmem hj hz
      (Work.FTS.OpenPkg.QangOpen.continuousOn_Qang_open α f hO hmem (by omega))
  intro i
  induction i with
  | zero => intro _ z _; rfl
  | succ i ih =>
      intro hi z hz
      have hprev : Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang f 0 z)
          =ᶠ[𝓝 z] (fun w => Work.Elliptic.Qang f i w) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
        exact ih (by omega) w hw
      show z * deriv (Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang f 0 z)) z
        = Work.Elliptic.Qang f (i + 1) z
      rw [hprev.deriv_eq, (hderiv i (by omega) z hz).deriv]
      field_simp

/-- The angular moments `Qang f i` are differentiable on `(0,∞)` for `i ≤ 2`. -/
theorem differentiableAt_Qang_open {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) {i : ℕ}
    (hi : i ≤ 2) {z : ℝ} (hz : 0 < z) :
    DifferentiableAt ℝ (fun z => Work.Elliptic.Qang f i z) z :=
  ((Work.FTS.OpenPkg.QangOpen.hasDerivAt_Qang_open α f hO hmem hi hz
    (Work.FTS.OpenPkg.QangOpen.continuousOn_Qang_open α f hO hmem (by omega))).differentiableAt)

/-! ## The decomposition of `radS` on `(0,∞)` -/

/-- **The decomposition of `radS` on `(0,∞)`**: with `z·(L₁₂ f)' = −Qang f 0`, the middle term
`−a(z)·z·(L₁₂ f)'(z)` becomes `+a(z)·Qang f 0 z`. -/
theorem radS_split_O (α : ℝ) {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hO : Work.FTS.EllipticEst.SmoothOpen f) (hmem4 : Work.Spaces.HkMem α 4 f)
    (hl12 : Work.Construction.L12 f 0 = 0) :
    ∀ z ∈ IoiA,
      Work.FTS.CoercivityFix.Transfer.radS α f z
        = -(Work.FTS.CoercivityFix.Transfer.dAmpA α z * Work.Coercivity.L12f f z)
          + Work.FTS.CoercivityFix.Transfer.ampA α z * Work.Elliptic.Qang f 0 z
          + (Work.FTS.CoercivityFix.Transfer.dAmpB α z / Work.Spaces.c α)
              * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 := by
  intro z hz
  have hQ := Work.FTS.CoercivityFix.Transfer.E1Parts.Qang_zero_eq_integral f z
  have h := DzdIter_L12f_eq_neg_Qang_O α hα hα1 hO hmem4 hl12 1 le_rfl (by norm_num) z hz
  have h1 : Work.Elliptic.DzdIter 1 (Work.Coercivity.L12f f) z
      = z * deriv (Work.Coercivity.L12f f) z := rfl
  rw [h1] at h
  simp only [Work.FTS.CoercivityFix.Transfer.radS]
  rw [h, show (1 : ℕ) - 1 = 0 from rfl, hQ]
  ring_nf


end Work.FTS.StrongEps.EpsE4Thr.E2O
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.ProjSlotDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false



end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.TransO.CsO =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.TransO

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The open-class `normSub`.**  For `f` which is `C^∞` on the open quadrant and honest at
order `n+1`, the level-`n` norms of the three slots `f`, `D_θ f`, `D_z f` are dominated by the
level-`(n+1)` norm of `f`. -/
theorem normSub_O (α : ℝ) (hα : 0 < α) (n : ℕ) (f : Fn)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α (n + 1) f) :
    Work.Spaces.HkSq α n f ≤ Work.Spaces.HkSq α (n + 1) f
      ∧ Work.Spaces.HkSq α n (Work.Spaces.Dth f) ≤ Work.Spaces.HkSq α (n + 1) f
      ∧ Work.Spaces.HkSq α n (Work.Spaces.Dz f) ≤ Work.Spaces.HkSq α (n + 1) f :=
  ⟨Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (Nat.le_succ n) hmem,
   Work.FTS.CoercivityFix.Assembly.HkSq_Dth_le_ge α (by linarith) n hmem,
   Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm α n
     ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hsm (n + 1)) hmem⟩

/-- **The Cauchy–Schwarz clause of the step, at level `n+1`** (open class).  From the level-`n`
Cauchy–Schwarz bound of `IP` and the three one-sided norm comparisons
(`|f|_n ≤ |f|_{n+1}`, `|D_θ f|_n ≤ |f|_{n+1}`, `|D_z f|_n ≤ |f|_{n+1}`) one obtains the
level-`(n+1)` bound for `HkIPStep c₁ c₂ IP = IP + c₁ IP(D_θ·, D_θ·) + c₂ IP(D_z·, D_z·)`, with
the constant `3 * max 1 (max c₁ c₂) * CC`.

This is the public copy of the private helper of `step2_data_ge_O`. -/
theorem cs_clause_succ_O (α : ℝ) (hα : 0 < α) (n : ℕ)
    {IP : Fn → Fn → ℝ} {CC : ℝ}
    (hcs : ∀ f g : Fn, RegQo α n f → RegQo α n g →
      |IP f g| ≤ CC * Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g)
    (hCC : 0 ≤ CC)
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    ∀ f g : Fn, RegQo α (n + 1) f → RegQo α (n + 1) g →
      |Work.Coercivity.HkIPStep c₁ c₂ IP f g|
        ≤ 3 * max 1 (max c₁ c₂) * CC * Work.Spaces.HkNorm α (n + 1) f
            * Work.Spaces.HkNorm α (n + 1) g := by
  intro f g hf hg
  have hfn : RegQo α n f := regQo_mono (Nat.le_succ n) hf
  have hgn : RegQo α n g := regQo_mono (Nat.le_succ n) hg
  have hdfn : RegQo α n (Work.Spaces.Dth f) := (regQo_dth_dz hα hf).1
  have hdgn : RegQo α n (Work.Spaces.Dth g) := (regQo_dth_dz hα hg).1
  have hdzn : RegQo α n (Work.Spaces.Dz f) := (regQo_dth_dz hα hf).2
  have hdzn' : RegQo α n (Work.Spaces.Dz g) := (regQo_dth_dz hα hg).2
  have e0 := hcs f g hfn hgn
  have e1 := hcs (Work.Spaces.Dth f) (Work.Spaces.Dth g) hdfn hdgn
  have e2 := hcs (Work.Spaces.Dz f) (Work.Spaces.Dz g) hdzn hdzn'
  obtain ⟨ns0f, ns1f, ns2f⟩ := normSub_O α hα n f hf.1 hf.2.1
  obtain ⟨ns0g, ns1g, ns2g⟩ := normSub_O α hα n g hg.1 hg.2.1
  have n0f : Work.Spaces.HkNorm α n f ≤ Work.Spaces.HkNorm α (n + 1) f := Real.sqrt_le_sqrt ns0f
  have n0g : Work.Spaces.HkNorm α n g ≤ Work.Spaces.HkNorm α (n + 1) g := Real.sqrt_le_sqrt ns0g
  have n1f : Work.Spaces.HkNorm α n (Work.Spaces.Dth f) ≤ Work.Spaces.HkNorm α (n + 1) f :=
    Real.sqrt_le_sqrt ns1f
  have n1g : Work.Spaces.HkNorm α n (Work.Spaces.Dth g) ≤ Work.Spaces.HkNorm α (n + 1) g :=
    Real.sqrt_le_sqrt ns1g
  have n2f : Work.Spaces.HkNorm α n (Work.Spaces.Dz f) ≤ Work.Spaces.HkNorm α (n + 1) f :=
    Real.sqrt_le_sqrt ns2f
  have n2g : Work.Spaces.HkNorm α n (Work.Spaces.Dz g) ≤ Work.Spaces.HkNorm α (n + 1) g :=
    Real.sqrt_le_sqrt ns2g
  have hF : 0 ≤ Work.Spaces.HkNorm α (n + 1) f := Real.sqrt_nonneg _
  have hG : 0 ≤ Work.Spaces.HkNorm α (n + 1) g := Real.sqrt_nonneg _
  have b0 : |IP f g|
      ≤ CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g := by
    calc |IP f g| ≤ CC * Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g := e0
      _ = CC * (Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g) := by ring
      _ ≤ CC * (Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul n0f n0g (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hCC
      _ = CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g := by ring
  have b1 : |IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)|
      ≤ CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g := by
    calc |IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)|
        ≤ CC * Work.Spaces.HkNorm α n (Work.Spaces.Dth f)
            * Work.Spaces.HkNorm α n (Work.Spaces.Dth g) := e1
      _ = CC * (Work.Spaces.HkNorm α n (Work.Spaces.Dth f)
            * Work.Spaces.HkNorm α n (Work.Spaces.Dth g)) := by ring
      _ ≤ CC * (Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul n1f n1g (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hCC
      _ = CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g := by ring
  have b2 : |IP (Work.Spaces.Dz f) (Work.Spaces.Dz g)|
      ≤ CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g := by
    calc |IP (Work.Spaces.Dz f) (Work.Spaces.Dz g)|
        ≤ CC * Work.Spaces.HkNorm α n (Work.Spaces.Dz f)
            * Work.Spaces.HkNorm α n (Work.Spaces.Dz g) := e2
      _ = CC * (Work.Spaces.HkNorm α n (Work.Spaces.Dz f)
            * Work.Spaces.HkNorm α n (Work.Spaces.Dz g)) := by ring
      _ ≤ CC * (Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul n2f n2g (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hCC
      _ = CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g := by ring
  have key : |Work.Coercivity.HkIPStep c₁ c₂ IP f g|
      ≤ CC * (Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g)
        + c₁ * (CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g)
        + c₂ * (CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g) := by
    have h1 : Work.Coercivity.HkIPStep c₁ c₂ IP f g
        = IP f g + c₁ * IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)
          + c₂ * IP (Work.Spaces.Dz f) (Work.Spaces.Dz g) := rfl
    have main : |IP f g + c₁ * IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)
          + c₂ * IP (Work.Spaces.Dz f) (Work.Spaces.Dz g)|
        ≤ |IP f g| + c₁ * |IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)|
          + c₂ * |IP (Work.Spaces.Dz f) (Work.Spaces.Dz g)| := by
      have t1 := abs_add_le (IP f g + c₁ * IP (Work.Spaces.Dth f) (Work.Spaces.Dth g))
        (c₂ * IP (Work.Spaces.Dz f) (Work.Spaces.Dz g))
      have t2 := abs_add_le (IP f g) (c₁ * IP (Work.Spaces.Dth f) (Work.Spaces.Dth g))
      have E1 : |c₁ * IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)|
          = c₁ * |IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)| := by
        rw [abs_mul, abs_of_pos hc₁]
      have E2 : |c₂ * IP (Work.Spaces.Dz f) (Work.Spaces.Dz g)|
          = c₂ * |IP (Work.Spaces.Dz f) (Work.Spaces.Dz g)| := by
        rw [abs_mul, abs_of_pos hc₂]
      linarith
    have A1 := mul_le_mul_of_nonneg_left b1 hc₁.le
    have A2 := mul_le_mul_of_nonneg_left b2 hc₂.le
    rw [h1]
    calc |IP f g + c₁ * IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)
            + c₂ * IP (Work.Spaces.Dz f) (Work.Spaces.Dz g)|
        ≤ |IP f g| + c₁ * |IP (Work.Spaces.Dth f) (Work.Spaces.Dth g)|
            + c₂ * |IP (Work.Spaces.Dz f) (Work.Spaces.Dz g)| := main
      _ ≤ CC * (Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g)
            + c₁ * (CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g)
            + c₂ * (CC * Work.Spaces.HkNorm α (n + 1) f
                * Work.Spaces.HkNorm α (n + 1) g) := by linarith [b0, A1, A2]
  have hcoef : 1 + c₁ + c₂ ≤ 3 * max 1 (max c₁ c₂) := by
    have h1 : (1 : ℝ) ≤ max 1 (max c₁ c₂) := le_max_left _ _
    have h2 : c₁ ≤ max 1 (max c₁ c₂) := le_trans (le_max_left _ _) (le_max_right _ _)
    have h3 : c₂ ≤ max 1 (max c₁ c₂) := le_trans (le_max_right _ _) (le_max_right _ _)
    linarith
  have hmax : 0 ≤ max 1 (max c₁ c₂) := le_trans zero_le_one (le_max_left _ _)
  have hpos : (0 : ℝ) ≤ 1 + c₁ + c₂ := by linarith
  have hfin : CC * (1 + c₁ + c₂) ≤ 3 * max 1 (max c₁ c₂) * CC := by
    nlinarith [hcoef, hCC, hmax, hpos]
  calc |Work.Coercivity.HkIPStep c₁ c₂ IP f g|
      ≤ CC * (Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g)
        + c₁ * (CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g)
        + c₂ * (CC * Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g) := key
    _ = (CC * (1 + c₁ + c₂))
          * (Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g) := by
        ring
    _ ≤ (3 * max 1 (max c₁ c₂) * CC)
          * (Work.Spaces.HkNorm α (n + 1) f * Work.Spaces.HkNorm α (n + 1) g) :=
        mul_le_mul_of_nonneg_right hfin (mul_nonneg hF hG)
    _ = 3 * max 1 (max c₁ c₂) * CC * Work.Spaces.HkNorm α (n + 1) f
          * Work.Spaces.HkNorm α (n + 1) g := by
        ring

end Work.FTS.StrongEps.EpsE4Thr.TransO
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsZero.Pieces =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsZero

set_option autoImplicit false

/-- The linear piece `-𝓛_Γ^T f` of the scheme's right-hand side. -/
abbrev PLin (α : ℝ) (f : Work.FTS.Galerkin.Fn) : Work.FTS.Galerkin.Fn :=
  fun z θ => -(Work.Coercivity.LGammaT α f z θ)

/-- The term `N₀` of the `g`-equation at the full profile `F = F_* + f` and the perturbation `f`. -/
abbrev PN0 (α : ℝ) (f : Work.FTS.Galerkin.Fn) : Work.FTS.Galerkin.Fn :=
  Work.Construction.N0 α (fun z θ => Work.Construction.Fstar α z θ + f z θ) f

/-- The term `N` of the `g`-equation at `F = F_* + f` and the stream function `Ψ`. -/
abbrev PN (α : ℝ) (f Ψ : Work.FTS.Galerkin.Fn) : Work.FTS.Galerkin.Fn :=
  Work.Construction.N α (fun z θ => Work.Construction.Fstar α z θ + f z θ) Ψ

/-- The term `N_*` of the `g`-equation. -/
abbrev PNs (μ lam : ℝ) (f : Work.FTS.Galerkin.Fn) : Work.FTS.Galerkin.Fn :=
  Work.Construction.Nstar μ lam f

/-- The `μ̄`-term `-μ̄·AK α` of the `g`-equation, at the modulation constant `mbar`. -/
abbrev PK (mbar : ℝ) (α : ℝ) : Work.FTS.Galerkin.Fn :=
  fun z θ => -mbar * Work.Construction.AK α z θ

/-- The `mubar`-constant of the `g`-equation at `F = F_* + f` and the stream function `Ψ`. -/
abbrev Pmubar (α : ℝ) (f Ψ : Work.FTS.Galerkin.Fn) : ℝ :=
  Work.Construction.mubar (PN0 α f) (PN α f Ψ)

/-- The right-hand side `gRHS α μ lam (F_*+f) Ψ f` of the `g`-equation. -/
abbrev PgRHS (α μ lam : ℝ) (f Ψ : Work.FTS.Galerkin.Fn) : Work.FTS.Galerkin.Fn :=
  Work.Construction.gRHS α μ lam (fun z θ => Work.Construction.Fstar α z θ + f z θ) Ψ f

/-- The stream function of the scheme at the profile `f`: `Φ_s + E f`. -/
abbrev PPsi (E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn)
    (Φs f : Work.FTS.Galerkin.Fn) : Work.FTS.Galerkin.Fn :=
  fun z θ => Φs z θ + E f z θ

end Work.FTS.StrongEps.EpsZero
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.AngRad5.Engine5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5.AngRad5

set_option autoImplicit false

/-- **The level-`5` angular-`×`-radial engine** (see the module docstring). -/
def AngRadEngine5 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ}, 0 < α → α ≤ 1 →
    ∀ {a r G : ℝ → ℝ} {B0 B1 M Crad : ℝ},
      Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ) →
      Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => r z) →
      (∀ θ ∈ Work.Spaces.Iθ, 0 ≤ G θ) →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ →
      0 ≤ B0 → 0 ≤ B1 → 0 ≤ M → 0 ≤ Crad →
      (∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ B0) →
      (∀ i : ℕ, 1 ≤ i → i ≤ 5 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ B1 * G θ) →
      (∫ θ in Work.Spaces.Iθ, G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ ≤ M) →
      Work.Spaces.HkMem α 5 (fun z (_ : ℝ) => r z) →
      Work.Spaces.HkNorm α 5 (fun z (_ : ℝ) => r z) ≤ Crad →
      Work.Spaces.HkMem α 5 (fun z θ => a θ * r z) ∧
      Work.Spaces.HkNorm α 5 (fun z θ => a θ * r z)
        ≤ C * Real.sqrt (B0 ^ 2 * 10 ^ 4 + 5 * B1 ^ 2 * M) * Crad

end Work.FTS.StrongEps.H5.AngRad5
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.Atoms.QangAe5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.StrongEps.H5.Atoms

open MeasureTheory


end Work.FTS.StrongEps.H5.Atoms
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.H5.Atoms.radialBounded5_majorant =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.H5.Atoms

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# `radialBounded5_majorant` — a bounded radial factor is a bounded multiplier on `ℋ⁵`

The claim is purely pointwise.  Let `r : ℝ → ℝ` be a radial factor whose one-dimensional
`D_z`-iterates (`DzdIter`, i.e. `z ↦ (z ∂_z)^k r`) are bounded by `Br` up to order `5`, and let
`g` be `C^∞` on the quadrant.  Then, at every interior point `(z,θ)`,

`HkIntegrand α 5 (r·g) ≤ 10^6 · Br² · HkIntegrand α 5 g`.

This is the level-`5` instance of the sibling `radialBounded6_majorant`
(`Submission/Work/FTS/StrongPersist/H6Rows/Npair6SupAux/radialBounded6_majorant.lean`), and the
proof is the same one; the constants are recomputed for `k = 5`.  The two ingredients are

* the Leibniz rules for a radial factor, `Work.FTS.OpenPkg.leibniz_rad_Dz` and
  `Work.FTS.OpenPkg.leibniz_rad_mixed`:
  `D_z^j(r·g) = ∑_{b≤j} C(j,b) (D_z^b r)(D_z^{j-b} g)` and
  `D_z^jD_θ^i(r·g) = ∑_{b≤j} C(j,b) (D_z^b r)(D_z^{j-b}D_θ^i g)` (all the `D_θ`-derivatives
  fall on `g`, since `r` is constant in `θ`);
* the weighted Cauchy–Schwarz bound `sum_choose_mul_sq_le` for such a Leibniz sum, in which the
  binomial coefficients cost the universal factor `10^4` and every slot
  `D_z^{j-b}D_θ^i g` is priced by the whole integrand `HkIntegrand α 5 g`
  (`Work.Spaces.sq_le_HkIntegrand_z`, `Work.Spaces.sq_le_HkIntegrand_mixed`).

There are `6` pure slots and `6·6 = 36` mixed slots, so the total cost is
`42 · 10^4 ≤ 10^6`.  No smoothness of `g` beyond `C^∞` on the open quadrant is used, and no
integrability at all: the statement is a pointwise majorant of the integrand.
-/

/-- **Weighted Cauchy–Schwarz for a Leibniz sum.**  For `n ≤ 5`, a family `A` bounded by `Br` and
a family `X` whose squares are bounded by `M`, the square of the binomial Leibniz sum
`∑_{b≤n} C(n,b)·(A b·X b)` is at most `10^4 · Br² · M`.

The constant is very generous: `∑_b C(n,b)² ≤ 1024` (as `C(n,b) ≤ 2^n ≤ 32`) and the
Cauchy–Schwarz cardinal factor is at most `6`, giving `6 · 1024 · Br² M = 6144 · Br² M
≤ 10^4 · Br² M`. -/
private theorem sum_choose_mul_sq_le {n : ℕ} (hn : n ≤ 5) {Br M : ℝ} (hBr : 0 ≤ Br)
    (hM : 0 ≤ M) {A X : ℕ → ℝ} (hA : ∀ b ≤ n, |A b| ≤ Br) (hX : ∀ b ≤ n, X b ^ 2 ≤ M) :
    (∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * (A b * X b)) ^ 2
      ≤ 10 ^ 4 * Br ^ 2 * M := by
  -- the sum of the squared binomial coefficients
  have hC : (∑ b ∈ Finset.range (n + 1), ((n.choose b : ℝ)) ^ 2) ≤ 1024 := by
    have h1 : ∀ b ∈ Finset.range (n + 1),
        ((n.choose b : ℝ)) ^ 2 ≤ 32 * ((n.choose b : ℝ)) := by
      intro b _
      have hb2 : n.choose b ≤ 32 := by
        have h : n.choose b ≤ 2 ^ n := Nat.choose_le_two_pow n b
        have h2 : 2 ^ n ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) hn
        omega
      have hc0 : (0 : ℝ) ≤ (n.choose b : ℝ) := Nat.cast_nonneg _
      have hc32 : ((n.choose b : ℝ)) ≤ 32 := by exact_mod_cast hb2
      nlinarith
    calc (∑ b ∈ Finset.range (n + 1), ((n.choose b : ℝ)) ^ 2)
        ≤ ∑ b ∈ Finset.range (n + 1), 32 * ((n.choose b : ℝ)) := Finset.sum_le_sum h1
      _ = 32 * ∑ b ∈ Finset.range (n + 1), ((n.choose b : ℝ)) := by rw [Finset.mul_sum]
      _ = 32 * (2 : ℝ) ^ n := by
            rw [← Nat.cast_sum, Nat.sum_range_choose]
            push_cast
            ring
      _ ≤ 1024 := by
            have h2n : (2 : ℝ) ^ n ≤ 2 ^ 5 := pow_le_pow_right₀ (by norm_num) hn
            norm_num at h2n ⊢
            linarith
  -- Cauchy–Schwarz with the binomial weights
  have hcs : (∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * |X b|) ^ 2
      ≤ (∑ b ∈ Finset.range (n + 1), ((n.choose b : ℝ)) ^ 2)
        * ∑ b ∈ Finset.range (n + 1), |X b| ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (n + 1)) _ _
  rw [show (∑ b ∈ Finset.range (n + 1), |X b| ^ 2)
      = ∑ b ∈ Finset.range (n + 1), X b ^ 2 from
        Finset.sum_congr rfl fun b _ => sq_abs (X b)] at hcs
  have h2 : (∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * |X b|) ^ 2
      ≤ 1024 * ∑ b ∈ Finset.range (n + 1), X b ^ 2 :=
    le_trans hcs (mul_le_mul_of_nonneg_right hC (Finset.sum_nonneg fun b _ => sq_nonneg _))
  -- each square is bounded by `M`
  have h3 : ∑ b ∈ Finset.range (n + 1), X b ^ 2 ≤ ((n + 1 : ℕ) : ℝ) * M := by
    calc ∑ b ∈ Finset.range (n + 1), X b ^ 2
        ≤ ∑ _b ∈ Finset.range (n + 1), M :=
          Finset.sum_le_sum fun b hb => hX b (by simpa [Finset.mem_range] using hb)
      _ = ((n + 1 : ℕ) : ℝ) * M := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h3' : ∑ b ∈ Finset.range (n + 1), X b ^ 2 ≤ 6 * M := by
    refine le_trans h3 ?_
    have hn6 : ((n + 1 : ℕ) : ℝ) ≤ 6 := by
      have : n + 1 ≤ 6 := by omega
      exact_mod_cast this
    exact mul_le_mul_of_nonneg_right hn6 hM
  -- the absolute-value bound on the Leibniz sum
  have h1 : |∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * (A b * X b)|
      ≤ Br * ∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * |X b| := by
    calc |∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * (A b * X b)|
        ≤ ∑ b ∈ Finset.range (n + 1), |(n.choose b : ℝ) * (A b * X b)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * |A b * X b| := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (n.choose b))]
      _ = ∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * (|A b| * |X b|) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [abs_mul]
      _ ≤ ∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * (Br * |X b|) := by
          refine Finset.sum_le_sum fun b hb => ?_
          have hb' : b ≤ n := by simpa [Finset.mem_range] using hb
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hA b hb') (abs_nonneg _))
            (Nat.cast_nonneg (n.choose b))
      _ = Br * ∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * |X b| := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun b _ => by ring
  calc (∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * (A b * X b)) ^ 2
      = |∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * (A b * X b)| ^ 2 :=
        (sq_abs _).symm
    _ ≤ (Br * ∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * |X b|) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = Br ^ 2 * (∑ b ∈ Finset.range (n + 1), (n.choose b : ℝ) * |X b|) ^ 2 := by ring
    _ ≤ Br ^ 2 * (1024 * ∑ b ∈ Finset.range (n + 1), X b ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg Br)
    _ ≤ Br ^ 2 * (1024 * (6 * M)) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg Br)
        exact mul_le_mul_of_nonneg_left h3' (by norm_num)
    _ ≤ 10 ^ 4 * Br ^ 2 * M := by
        have hB2 : (0 : ℝ) ≤ Br ^ 2 := sq_nonneg Br
        nlinarith [hB2, hM]

/-- A radial factor all of whose `D_z`-iterates of order `≤ 5` are bounded by `Br` is a bounded multiplier on the weighted `ℋ⁵`-integrand. -/
theorem radialBounded5_majorant :
    ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (r : ℝ → ℝ) (g : ℝ → ℝ → ℝ) (Br : ℝ),
      Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => r z) →
      Work.FTS.EllipticEst.SmoothOpen g → 0 ≤ Br →
      (∀ b : ℕ, b ≤ 5 → ∀ z : ℝ, 0 ≤ z → |Work.Elliptic.DzdIter b r z| ≤ Br) →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.HkIntegrand α 5 (fun z θ => r z * g z θ) z θ
          ≤ K * Br ^ 2 * Work.Spaces.HkIntegrand α 5 g z θ := by
  refine ⟨10 ^ 6, by norm_num, ?_⟩
  intro α r g Br hr hg hBr hbdd z θ hz hθ0 hθ1
  have hzI : z ∈ Set.Ioi (0 : ℝ) := hz
  have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hHg : 0 ≤ Work.Spaces.HkIntegrand α 5 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 5 g z θ
  have hM0 : (0 : ℝ) ≤ 10 ^ 4 * Br ^ 2 * Work.Spaces.HkIntegrand α 5 g z θ :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg Br)) hHg
  -- the pure `D_z` slot, priced by the whole integrand
  have hz1 : ∀ i : ℕ, i ≤ 5 →
      (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ 10 ^ 4 * Br ^ 2 * Work.Spaces.HkIntegrand α 5 g z θ := by
    intro i hi
    have hleib := Work.FTS.OpenPkg.leibniz_rad_Dz r g hr hg i z hzI θ hθI
    have hfac : (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
            * (Work.Elliptic.DzdIter b r z * Work.Spaces.DzIter (i - b) g z θ))
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))
        = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
            * (Work.Elliptic.DzdIter b r z
              * (Work.Spaces.DzIter (i - b) g z θ
                * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)))) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [hleib, hfac]
    exact sum_choose_mul_sq_le (n := i) hi hBr hHg
      (fun b hb => hbdd b (by omega) z hz.le)
      (fun b hb => Work.Spaces.sq_le_HkIntegrand_z α 5 g z θ (i - b) (by omega))
  -- the mixed slots, priced by the whole integrand
  have hm1 : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 5 →
      (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ 10 ^ 4 * Br ^ 2 * Work.Spaces.HkIntegrand α 5 g z θ := by
    intro i j hi hij
    have hleib := Work.FTS.OpenPkg.leibniz_rad_mixed r g hr hg j i hi z hzI θ hθI
    have hfac : (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b r z * Work.Spaces.mixed (j - b) i g z θ))
          * Work.Spaces.Wt α z θ
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b r z
              * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ)) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [hleib, hfac]
    exact sum_choose_mul_sq_le (n := j) (by omega) hBr hHg
      (fun b hb => hbdd b (by omega) z hz.le)
      (fun b hb => Work.Spaces.sq_le_HkIntegrand_mixed α 5 g z θ i (j - b) hi (by omega))
  -- the two sums
  have hS1 : (∑ i ∈ Finset.range (5 + 1),
        (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 6 * (10 ^ 4 * Br ^ 2 * Work.Spaces.HkIntegrand α 5 g z θ) := by
    have h := Finset.sum_le_card_nsmul (Finset.range (5 + 1))
      (fun i => (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      (10 ^ 4 * Br ^ 2 * Work.Spaces.HkIntegrand α 5 g z θ)
      (fun i hi => hz1 i (by have h := Finset.mem_range.mp hi; omega))
    refine le_trans h (le_of_eq ?_)
    rw [Finset.card_range, nsmul_eq_mul]
    norm_num
  have hS2 : (∑ i ∈ Finset.range (5 + 1), ∑ j ∈ Finset.range (5 + 1),
        if 1 ≤ i ∧ i + j ≤ 5 then
          (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)
      ≤ 36 * (10 ^ 4 * Br ^ 2 * Work.Spaces.HkIntegrand α 5 g z θ) := by
    have hinner : ∀ i : ℕ, (∑ j ∈ Finset.range (5 + 1),
          if 1 ≤ i ∧ i + j ≤ 5 then
            (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        ≤ 6 * (10 ^ 4 * Br ^ 2 * Work.Spaces.HkIntegrand α 5 g z θ) := by
      intro i
      have h := Finset.sum_le_card_nsmul (Finset.range (5 + 1))
        (fun j => if 1 ≤ i ∧ i + j ≤ 5 then
            (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        (10 ^ 4 * Br ^ 2 * Work.Spaces.HkIntegrand α 5 g z θ)
        (fun j _ => by
          split_ifs with hguard
          · exact hm1 i j hguard.1 hguard.2
          · exact hM0)
      refine le_trans h (le_of_eq ?_)
      rw [Finset.card_range, nsmul_eq_mul]
      norm_num
    calc (∑ i ∈ Finset.range (5 + 1), ∑ j ∈ Finset.range (5 + 1),
          if 1 ≤ i ∧ i + j ≤ 5 then
            (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        ≤ ∑ _i ∈ Finset.range (5 + 1),
            (6 * (10 ^ 4 * Br ^ 2 * Work.Spaces.HkIntegrand α 5 g z θ)) :=
          Finset.sum_le_sum fun i _ => hinner i
      _ = 36 * (10 ^ 4 * Br ^ 2 * Work.Spaces.HkIntegrand α 5 g z θ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have hunf : Work.Spaces.HkIntegrand α 5 (fun z θ => r z * g z θ) z θ
      = (∑ i ∈ Finset.range (5 + 1),
            (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
        + ∑ i ∈ Finset.range (5 + 1), ∑ j ∈ Finset.range (5 + 1),
            if 1 ≤ i ∧ i + j ≤ 5 then
              (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
            else 0 := rfl
  rw [hunf]
  refine le_trans (add_le_add hS1 hS2) ?_
  have h1 : (0 : ℝ) ≤ Br ^ 2 * Work.Spaces.HkIntegrand α 5 g z θ :=
    mul_nonneg (sq_nonneg Br) hHg
  nlinarith [h1]

end Work.FTS.StrongEps.H5.Atoms
end
-- ===== merged: Submission.Work.FTS.StrongEps.HkSqAux.LogCoord =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.HkSqAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem continuous_kappa : Continuous kappa := by
  unfold kappa
  refine Continuous.div Real.continuous_exp ?_ (fun ζ => ?_)
  · exact continuous_const.add (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  · positivity

/-- **The `H^k`-square as a log-coordinate integral.** -/
theorem ofReal_HkSq_eq_logIntegral (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ}
    (hF : Work.Spaces.HkMem α k f)
    (hcont : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k f q.1 q.2)
      Work.FTS.StrongEps.Quad) :
    ENNReal.ofReal (Work.Spaces.HkSq α k f)
      = ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (logJac s ζ)
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Real.exp s)
              (Real.arctan (Real.exp ζ))) := by
  have hnn : ∀ z θ, 0 ≤ Work.Spaces.HkIntegrand α k f z θ :=
    Work.Spaces.HkIntegrand_nonneg α k f
  -- (1) the iterated Bochner integral as an iterated `lintegral`
  have h1 : ENNReal.ofReal (Work.Spaces.HkSq α k f)
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z θ) := by
    rw [Work.Spaces.HkSq]
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hF.2
      (Eventually.of_forall fun z => integral_nonneg fun θ => hnn z θ)]
    exact MeasureTheory.setLIntegral_congr_fun measurableSet_Ici
      (fun z hz => MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hF.1 z hz)
        (Eventually.of_forall fun θ => hnn z θ))
  rw [h1]
  -- (2) replace the closed intervals by the open ones (null sets)
  have hIθ : (fun z : ℝ => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z θ))
      = fun z : ℝ => ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z θ) := by
    funext z
    exact (MeasureTheory.setLIntegral_congr (f := fun θ : ℝ =>
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z θ))
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := π / 2))).symm
  rw [hIθ]
  have hIz : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z θ))
      = ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z θ) :=
    (MeasureTheory.setLIntegral_congr (f := fun z : ℝ => ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z θ))
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))).symm
  rw [hIz]
  -- (3) the `θ`-substitution
  have hθ : (fun z : ℝ => ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z θ))
      = fun z : ℝ => ∫⁻ ζ, ENNReal.ofReal (kappa ζ)
        * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z (Real.arctan (Real.exp ζ))) := by
    funext z
    exact lintegral_arctan_exp_subst_gen
      (fun θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z θ))
  rw [hθ]
  -- (4) the `z`-substitution
  rw [lintegral_exp_subst_gen (fun z : ℝ => ∫⁻ ζ, ENNReal.ofReal (kappa ζ)
      * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z (Real.arctan (Real.exp ζ))))]
  -- (5) move the factor `ofReal (exp s)` inside the `ζ`-integral and identify the Jacobian
  refine MeasureTheory.lintegral_congr fun s => ?_
  have hcontζ : Continuous fun ζ : ℝ =>
      Work.Spaces.HkIntegrand α k f (Real.exp s) (Real.arctan (Real.exp ζ)) :=
    hcont.comp_continuous
      (Continuous.prodMk continuous_const (Real.continuous_arctan.comp Real.continuous_exp))
      (fun ζ => ⟨Real.exp_pos s, Real.arctan_pos.2 (Real.exp_pos ζ),
        Real.arctan_lt_pi_div_two _⟩)
  have hmeas : Measurable fun ζ : ℝ => ENNReal.ofReal (kappa ζ)
      * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Real.exp s)
          (Real.arctan (Real.exp ζ))) :=
    (ENNReal.measurable_ofReal.comp continuous_kappa.measurable).mul
      (ENNReal.measurable_ofReal.comp hcontζ.measurable)
  rw [(MeasureTheory.lintegral_const_mul (ENNReal.ofReal (Real.exp s)) hmeas).symm]
  refine MeasureTheory.lintegral_congr fun ζ => ?_
  rw [logJac, ENNReal.ofReal_mul (Real.exp_pos s).le]
  ring

end Work.FTS.StrongEps.HkSqAux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.HkSqAux.continuousOn_HkIntegrand_Quad =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.HkSqAux

open scoped Real Topology
open MeasureTheory Set Filter

/-- **Continuity of the `ℋ^k`-integrand on the open quadrant.**

If `f` is `C^n` on the open quadrant `Quad = (0,∞) × (0,π/2)` for every `n`, then the
integrand

  `(z,θ) ↦ HkIntegrand α k f z θ`

is continuous on `Quad`.  On `Quad` the two weights `w z = (1+z)²/z²` and `sin(2θ)^{-η/2}`
resp. `Wt α z θ = w z · sin(2θ)^{-γ/2}` are continuous (the denominators `z` and `sin(2θ)`
do not vanish there), and every one of the finitely many derivatives `D_z^i f`,
`D_z^j D_θ^i f` entering `HkIntegrand` is `C^∞` on `Quad` because `D_z`, `D_θ` preserve
smoothness on an open set (`Work.FTS.LocData.contDiffOn_DzIter`,
`Work.FTS.LocData.contDiffOn_mixed`), hence continuous. -/
theorem continuousOn_HkIntegrand_Quad (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad) :
    ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k f q.1 q.2)
      Work.FTS.StrongEps.Quad := by
  have hOpen : IsOpen Work.FTS.StrongEps.Quad := Work.FTS.StrongEps.isOpen_Quad
  -- `C^n` for every `n` is `C^∞` (the genuine smooth order, not analyticity)
  have hfq : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f)
      Work.FTS.StrongEps.Quad := contDiffOn_infty.mpr hf
  -- on the open quadrant `sin(2θ) > 0`, so every power is finite and continuous
  have hsinpos : ∀ p ∈ Work.FTS.StrongEps.Quad, 0 < Real.sin (2 * p.2) := fun p hp =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])
  -- the radial weight `w z = (1+z)²/z²`
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.StrongEps.Quad := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
      funext p; rfl
    rw [hfun]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  have hsinpow : ∀ c : ℝ,
      ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Work.FTS.StrongEps.Quad :=
    fun c => ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn)
      |>.rpow_const (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  -- the product weight `Wt α z θ = w z · sin(2θ)^{-γ/2}`
  have hWt : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      Work.FTS.StrongEps.Quad := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
        = fun p : ℝ × ℝ => Work.Spaces.w p.1
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
      funext p; rfl
    rw [hfun]
    exact hw.mul (hsinpow _)
  -- the pure `D_z`-weight `w z / sin(2θ)^{η/2}`
  have hwdiv : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))
      Work.FTS.StrongEps.Quad :=
    hw.div (hsinpow _) (fun p hp => ne_of_gt (Real.rpow_pos_of_pos (hsinpos p hp) _))
  -- the derivatives entering the integrand are smooth, hence continuous, on the quadrant
  have hDzC : ∀ i : ℕ,
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i f p.1 p.2)
        Work.FTS.StrongEps.Quad :=
    fun i => (Work.FTS.LocData.contDiffOn_DzIter hOpen hfq i).continuousOn
  have hmC : ∀ j i : ℕ,
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2)
        Work.FTS.StrongEps.Quad :=
    fun j i => (Work.FTS.LocData.contDiffOn_mixed hOpen hfq j i).continuousOn
  -- unfold the integrand and assemble the (finite) sum of continuous summands
  have hHk : (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
      = fun p : ℝ × ℝ =>
          (∑ i ∈ Finset.range (k + 1),
              (Work.Spaces.DzIter i f p.1 p.2
                * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
            + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k
                then (Work.Spaces.mixed j i f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2
                else 0 := by
    funext p; rfl
  rw [hHk]
  refine ContinuousOn.add ?_ ?_
  · refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i _ => ?_)
    exact ((hDzC i).mul hwdiv).pow 2
  · refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i _ =>
      continuousOn_finsetSum (Finset.range (k + 1)) (fun j _ => ?_))
    split_ifs with h
    · exact ((hmC j i).mul hWt).pow 2
    · exact continuousOn_const

end Work.FTS.StrongEps.HkSqAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.HkSqAux.continuousOn_mixed_Quad =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.HkSqAux

/-- `D_z^j D_θ^i f` is continuous on the open quadrant, for `f` that is `C^n` there for every
`n`.  Immediate from smoothness preservation (`contDiffOn_mixed`) and the fact that a `C^∞`
function is continuous. -/
theorem continuousOn_mixed_Quad {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad) (j i : ℕ) :
    ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.mixed j i f q.1 q.2) Work.FTS.StrongEps.Quad := by
  have hsm : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f)
      Work.FTS.StrongEps.Quad := contDiffOn_infty.mpr hf
  have h := Work.FTS.LocData.contDiffOn_mixed Work.FTS.StrongEps.isOpen_Quad hsm j i
  exact h.continuousOn

end Work.FTS.StrongEps.HkSqAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.JepsHkMem.lintegral_thShift_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `lintegral_thShift_le`

The angular half of the `L¹`-stability of the `ε`-mollifier weights under the log-coordinate
shifts: for an **arbitrary** `ENNReal`-valued function `U`,

  `∫⁻ θ ∈ Iθ, U (thShift θ p₂) ≤ e^{3|p₂|} ∫⁻ θ ∈ Iθ, U θ`,

where `Iθ = [0, π/2]` and `thShift θ p = arctan (tan θ · e^{-p})`.

## Proof

The map `θ ↦ thShift θ p₂` is the translation `ζ ↦ ζ - p₂` in the log coordinate
`ζ = log tan θ` (`thShift_arctan_exp`), and `θ ↦ arctan (e^ζ)` is a bijection of `ℝ` onto
`(0, π/2)` with Jacobian `kappa ζ = e^ζ/(1 + e^{2ζ})`.  So

  `∫⁻_{Iθ} U (thShift θ p₂) = ∫⁻_{Ioo 0 (π/2)} U (thShift θ p₂)`
  `   = ∫⁻_ζ kappa ζ · U (arctan (e^{ζ-p₂}))        (lintegral_arctan_exp_subst_gen)`
  `   = ∫⁻_ζ kappa (ζ + p₂) · U (arctan (e^ζ))      (translation invariance)`

and the comparison with `∫⁻_{Iθ} U` is the pointwise bound
`kappa (ζ + p₂) ≤ e^{3|p₂|} kappa ζ`, which is `kappa_shift_core` (`kappa (ζ+p) ≤ e^{2|p|+p}
kappa ζ`, `logJac_shift_le.lean`) together with `2|p₂| + p₂ ≤ 3|p₂|`.

The passage `Icc 0 (π/2) ↔ Ioo 0 (π/2)` is a null-set argument (`Ioo_ae_eq_Icc`); no
measurability of `U` is ever needed, since the substitution and translation lemmas are
`lintegral` (not Bochner) statements.
-/

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.JepsHkMem

/-- **`thShift` in the log coordinate `ζ = log tan θ`**: the shift of
`θ = arctan (e^ζ)` is `arctan (e^{ζ - p})`, i.e. the translation `ζ ↦ ζ - p`. -/
theorem thShift_arctan_exp' (ζ p : ℝ) :
    Work.FTS.StrongEps.thShift (Real.arctan (Real.exp ζ)) p
      = Real.arctan (Real.exp (ζ - p)) := by
  rw [Work.FTS.StrongEps.thShift, Real.tan_arctan, ← Real.exp_add, sub_eq_add_neg]

theorem lintegral_thShift_le (U : ℝ → ENNReal) (p₂ : ℝ) :
    (∫⁻ θ in Work.Spaces.Iθ, U (Work.FTS.StrongEps.thShift θ p₂))
      ≤ ENNReal.ofReal (Real.exp (3 * |p₂|)) * (∫⁻ θ in Work.Spaces.Iθ, U θ) := by
  -- `Iθ = Icc 0 (π/2)` differs from `Ioo 0 (π/2)` by the null set `{0, π/2}`
  have hIccI : (∫⁻ θ in Work.Spaces.Iθ, U (Work.FTS.StrongEps.thShift θ p₂))
      = ∫⁻ θ in Set.Ioo 0 (π / 2), U (Work.FTS.StrongEps.thShift θ p₂) :=
    setLIntegral_congr (Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := (π / 2))).symm
  have hIccU : (∫⁻ θ in Work.Spaces.Iθ, U θ) = ∫⁻ θ in Set.Ioo 0 (π / 2), U θ :=
    setLIntegral_congr (Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := (π / 2))).symm
  -- the log-coordinate substitution `θ = arctan (e^ζ)`
  have hA : (∫⁻ θ in Set.Ioo 0 (π / 2), U (Work.FTS.StrongEps.thShift θ p₂))
      = ∫⁻ ζ : ℝ, ENNReal.ofReal (HkSqAux.kappa ζ)
          * U (Real.arctan (Real.exp (ζ - p₂))) := by
    rw [HkSqAux.lintegral_arctan_exp_subst_gen
      (fun θ => U (Work.FTS.StrongEps.thShift θ p₂))]
    simp only [thShift_arctan_exp']
  -- translation invariance in the log coordinate
  have hB : (∫⁻ ζ : ℝ, ENNReal.ofReal (HkSqAux.kappa ζ)
        * U (Real.arctan (Real.exp (ζ - p₂))))
      = ∫⁻ ζ : ℝ, ENNReal.ofReal (HkSqAux.kappa (ζ + p₂))
          * U (Real.arctan (Real.exp ζ)) := by
    have h := lintegral_add_right_eq_self (μ := volume)
      (fun ζ : ℝ => ENNReal.ofReal (HkSqAux.kappa ζ)
        * U (Real.arctan (Real.exp (ζ - p₂)))) p₂
    simp only [add_sub_cancel_right] at h
    exact h.symm
  -- the pointwise Jacobian comparison
  have hk : ∀ ζ : ℝ, HkSqAux.kappa (ζ + p₂) ≤ Real.exp (3 * |p₂|) * HkSqAux.kappa ζ := by
    intro ζ
    have h1 := HkSqAux.kappa_shift_core (ζ + p₂) p₂
    simp only [add_sub_cancel_right] at h1
    have h2 : Real.exp (2 * |p₂| + p₂) ≤ Real.exp (3 * |p₂|) := by
      rw [Real.exp_le_exp]
      nlinarith [le_abs_self p₂]
    exact le_trans h1 (mul_le_mul_of_nonneg_right h2 (HkSqAux.kappa_nonneg ζ))
  have hC : (∫⁻ ζ : ℝ, ENNReal.ofReal (HkSqAux.kappa (ζ + p₂))
        * U (Real.arctan (Real.exp ζ)))
      ≤ ENNReal.ofReal (Real.exp (3 * |p₂|))
          * ∫⁻ ζ : ℝ, ENNReal.ofReal (HkSqAux.kappa ζ)
              * U (Real.arctan (Real.exp ζ)) := by
    calc (∫⁻ ζ : ℝ, ENNReal.ofReal (HkSqAux.kappa (ζ + p₂))
          * U (Real.arctan (Real.exp ζ)))
        ≤ ∫⁻ ζ : ℝ, (ENNReal.ofReal (Real.exp (3 * |p₂|))
            * ENNReal.ofReal (HkSqAux.kappa ζ)) * U (Real.arctan (Real.exp ζ)) := by
          refine lintegral_mono fun ζ => ?_
          refine mul_le_mul_of_nonneg_right ?_
            (zero_le (a := U (Real.arctan (Real.exp ζ))))
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
          exact ENNReal.ofReal_le_ofReal (hk ζ)
      _ = ENNReal.ofReal (Real.exp (3 * |p₂|))
            * ∫⁻ ζ : ℝ, ENNReal.ofReal (HkSqAux.kappa ζ)
                * U (Real.arctan (Real.exp ζ)) := by
          rw [← lintegral_const_mul' (ENNReal.ofReal (Real.exp (3 * |p₂|)))
                (fun ζ => ENNReal.ofReal (HkSqAux.kappa ζ)
                  * U (Real.arctan (Real.exp ζ)))
                ENNReal.ofReal_ne_top]
          exact lintegral_congr fun ζ => mul_assoc _ _ _
  calc (∫⁻ θ in Work.Spaces.Iθ, U (Work.FTS.StrongEps.thShift θ p₂))
      = ∫⁻ θ in Set.Ioo 0 (π / 2), U (Work.FTS.StrongEps.thShift θ p₂) := hIccI
    _ = ∫⁻ ζ : ℝ, ENNReal.ofReal (HkSqAux.kappa ζ)
          * U (Real.arctan (Real.exp (ζ - p₂))) := hA
    _ = ∫⁻ ζ : ℝ, ENNReal.ofReal (HkSqAux.kappa (ζ + p₂))
          * U (Real.arctan (Real.exp ζ)) := hB
    _ ≤ ENNReal.ofReal (Real.exp (3 * |p₂|))
          * ∫⁻ ζ : ℝ, ENNReal.ofReal (HkSqAux.kappa ζ)
              * U (Real.arctan (Real.exp ζ)) := hC
    _ = ENNReal.ofReal (Real.exp (3 * |p₂|)) * (∫⁻ θ in Set.Ioo 0 (π / 2), U θ) := by
        rw [← HkSqAux.lintegral_arctan_exp_subst_gen U]
    _ = ENNReal.ofReal (Real.exp (3 * |p₂|)) * (∫⁻ θ in Work.Spaces.Iθ, U θ) := by
        rw [hIccU]

end Work.FTS.StrongEps.JepsHkMem
end
-- ===== merged: Submission.Work.FTS.StrongEps.StepFacts.DthIter_Jeps_route_theta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.StepFacts

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1000000

/-! ## The pointwise `∂_{p₂} ↔ D_θ` dictionary

Differentiating the shifted profile in the *shift parameter* `p₂` is differentiation of the
profile along `D_θ` at the shifted point, up to the factor `-1/2` (`deriv_shift_snd` of
`KernAux`); reversing the constant gives the form used below. -/

/-- **`D_θ` at the shifted point is `-2 ∂_{p₂}` of the shifted slice.**  For `g` of class `C¹` on
the open quadrant, `z > 0`, `θ ∈ (0,π/2)` and every shift parameter `p`,
`D_θ g (z e^{-p₁}) (thShift θ p₂) = -2 ∂_{p₂} [t ↦ g (z e^{-p₁}) (thShift θ t)]`. -/
theorem Dth_eq_neg_two_deriv_snd {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ 1 (Function.uncurry g) Quad) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (p : ℝ × ℝ) :
    Work.Spaces.Dth g (zShift z p.1) (thShift θ p.2)
      = -2 * deriv (fun t : ℝ => g (zShift z p.1) (thShift θ t)) p.2 := by
  rw [KernAux.deriv_shift_snd g hz hθ hg p]
  ring

/-- **The iterated form**: for `i ≥ 1`, the value of `D_θ^i g` at the shifted point is `-2` times
the `p₂`-derivative of the shifted `D_θ^{i-1} g`. -/
theorem DthIter_eq_neg_two_deriv_snd {g : ℝ → ℝ → ℝ} (hg : SmQ g) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) (i : ℕ) (hi : 1 ≤ i) (p : ℝ × ℝ) :
    Work.Spaces.DthIter i g (zShift z p.1) (thShift θ p.2)
      = -2 * deriv (fun t : ℝ => Work.Spaces.DthIter (i - 1) g (zShift z p.1)
          (thShift θ t)) p.2 := by
  -- `D_θ^i g = D_θ (D_θ^{i-1} g)` because `i = (i - 1) + 1`
  have hsucc : Work.Spaces.DthIter i g
      = Work.Spaces.Dth (Work.Spaces.DthIter (i - 1) g) := by
    conv_lhs => rw [← Nat.sub_add_cancel hi]
    rw [Work.Spaces.DthIter_succ]
  rw [hsucc]
  exact Dth_eq_neg_two_deriv_snd ((hg.DthIter (i - 1)).one) hz hθ p

/-! ## The target -/

-- context: namespace Work.FTS.StrongEps.StepFacts; `DthIter i f = D_θ^i f` with `D_θ = sin(2θ)∂_θ`; the conclusion is the single routed θ-derivative identity.
theorem DthIter_Jeps_route_theta (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (i : ℕ) (hi : 1 ≤ i) :
    Work.Spaces.DthIter i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
      = 2 * ∫ p : ℝ × ℝ,
          deriv (fun t : ℝ => Work.FTS.StrongEps.Jker ρ ε (p.1, t)) p.2
          * Work.Spaces.DthIter (i - 1) f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) := by
  have hsm : SmQ f := smQ_of_forall_nat hf
  -- (1) `J_ε` commutes with `D_θ^i` (`E1`), so the left-hand side is the mollified
  -- `D_θ^i f`, i.e. the `p`-integral of the kernel against the shifted `D_θ^i f`.
  have hmem : (z, θ) ∈ Quad := ⟨hz, hθ⟩
  have h1 : Work.Spaces.DthIter i (Jeps ρ ε f) z θ = Jeps ρ ε (Work.Spaces.DthIter i f) z θ :=
    DthIter_mixed_Jeps ρ hρ.moll hε hf i hmem
  rw [h1, Jeps_eq_integral ρ ε (Work.Spaces.DthIter i f) hz hθ]
  -- (2) pointwise, `D_θ^i f` at the shifted point is `-2 ∂_{p₂}` of the shifted `D_θ^{i-1} f`
  have hpt : ∀ p : ℝ × ℝ, Jker ρ ε p
        * Work.Spaces.DthIter i f (zShift z p.1) (thShift θ p.2)
      = -2 * (Jker ρ ε p * deriv (fun t : ℝ =>
          Work.Spaces.DthIter (i - 1) f (zShift z p.1) (thShift θ t)) p.2) := by
    intro p
    rw [DthIter_eq_neg_two_deriv_snd hsm hz hθ i hi p]
    ring
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul]
  -- (3) integrate by parts in `p₂`: the kernel is `C^∞` with compact support, the shifted
  -- `D_θ^{i-1} f` is `C¹` (it is the shift of a smooth profile), so there is no boundary term
  have hv : ContDiff ℝ 1 (fun p : ℝ × ℝ => Work.Spaces.DthIter (i - 1) f
      (zShift z p.1) (thShift θ p.2)) :=
    KernAux.contDiff_shift (Work.Spaces.DthIter (i - 1) f) hz hθ
      (contDiffOn_infty.mp (hsm.DthIter (i - 1))) 1
  have hIBP : ∫ p : ℝ × ℝ, Jker ρ ε p * deriv (fun t : ℝ =>
        Work.Spaces.DthIter (i - 1) f (zShift z p.1) (thShift θ t)) p.2
      = - ∫ p : ℝ × ℝ, deriv (fun t : ℝ => Jker ρ ε (p.1, t)) p.2
          * Work.Spaces.DthIter (i - 1) f (zShift z p.1) (thShift θ p.2) :=
    KernAux.integral_mul_partSnd_eq_neg (Jker_smooth hρ ε)
      (Jker_hasCompactSupport hρ.moll hε) hv
  rw [hIBP]
  ring

end Work.FTS.StrongEps.StepFacts
end
-- ===== merged: Submission.Work.FTS.StrongEps.StepFacts.mixed_Jeps_route_z =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.StepFacts

open scoped Real Topology
open MeasureTheory Set Filter

/-- Smoothness helper: if `f` is `C^n` on the open quadrant for every `n`, so is every
mixed derivative `D_z^a D_θ^b f`. -/
theorem mixed_Jeps_route_z_smooth (f : ℝ → ℝ → ℝ)
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad) (a b : ℕ) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.mixed a b f))
      Work.FTS.StrongEps.Quad :=
  contDiffOn_infty.mp (Work.FTS.LocData.contDiffOn_mixed Work.FTS.StrongEps.isOpen_Quad
    (contDiffOn_infty.mpr hf) a b)

/-- The index bookkeeping: `D_z (D_z^{j-1} D_θ^i f) = D_z^j D_θ^i f` for `1 ≤ j`. -/
theorem mixed_Jeps_route_z_Dz_pred (f : ℝ → ℝ → ℝ) {j : ℕ} (hj : 1 ≤ j) (i : ℕ) :
    Work.Spaces.Dz (Work.Spaces.mixed (j - 1) i f) = Work.Spaces.mixed j i f := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, (Nat.sub_add_cancel hj).symm⟩
  rw [Nat.add_sub_cancel]
  simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ]

-- context: namespace Work.FTS.StrongEps.StepFacts; imports Mathlib, Submission.Work.FTS.StrongEps.Basic, .Kernel, .mixed_Jeps, Submission.Work.Spaces.Defs
-- `Jeps ρ ε f` is the log-coordinate mollifier; `Jker ρ ε p = ε⁻¹^2 * ρ (ε⁻¹ • p)`; `zShift z p = z*exp(-p)`,
-- `thShift θ p = arctan (tan θ * exp(-p))`; `Quad = (0,∞) × (0,π/2)`; `mixed j i = D_z^j D_θ^i`.
theorem mixed_Jeps_route_z (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (j i : ℕ) (hj : 1 ≤ j) :
    Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
      = ∫ p : ℝ × ℝ,
          deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1
          * Work.Spaces.mixed (j - 1) i f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) := by
  -- the profile carrying the remaining `D_z^{j-1}` is smooth on the open quadrant
  have hsm : ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry (Work.Spaces.mixed (j - 1) i f)) Work.FTS.StrongEps.Quad :=
    mixed_Jeps_route_z_smooth f hf (j - 1) i
  have hDz : Work.Spaces.Dz (Work.Spaces.mixed (j - 1) i f) = Work.Spaces.mixed j i f :=
    mixed_Jeps_route_z_Dz_pred f hj i
  -- Step 1: `mixed_Jeps` and the integral (log-coordinate convolution) form of `Jeps`
  have hbase : Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
      = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * Work.Spaces.mixed j i f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) := by
    rw [Work.FTS.StrongEps.mixed_Jeps ρ hρ.moll hε hf hz hθ j i,
      Work.FTS.StrongEps.Jeps_eq_integral ρ ε (Work.Spaces.mixed j i f) hz hθ]
  rw [hbase]
  -- Step 2: integration by parts in `p₁`, moving the derivative onto the kernel
  have hv : ContDiff ℝ 1 (fun p : ℝ × ℝ =>
      Work.Spaces.mixed (j - 1) i f (Work.FTS.StrongEps.zShift z p.1)
        (Work.FTS.StrongEps.thShift θ p.2)) :=
    Work.FTS.StrongEps.KernAux.contDiff_shift _ hz hθ hsm 1
  have hu : ContDiff ℝ 1 (Work.FTS.StrongEps.Jker ρ ε) :=
    Work.FTS.StrongEps.Jker_smooth hρ ε (n := 1)
  have hus : HasCompactSupport (Work.FTS.StrongEps.Jker ρ ε) :=
    Work.FTS.StrongEps.Jker_hasCompactSupport hρ.moll hε
  have hIBP : (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
        * deriv (fun s : ℝ => Work.Spaces.mixed (j - 1) i f
            (Work.FTS.StrongEps.zShift z s) (Work.FTS.StrongEps.thShift θ p.2)) p.1)
      = - ∫ p : ℝ × ℝ, deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1
          * Work.Spaces.mixed (j - 1) i f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) :=
    Work.FTS.StrongEps.KernAux.integral_mul_partFst_eq_neg hu hus hv
  -- the chain rule: differentiating the shifted profile in the shift parameter is `-D_z`
  have hvs : ∀ p : ℝ × ℝ,
      deriv (fun s : ℝ => Work.Spaces.mixed (j - 1) i f
          (Work.FTS.StrongEps.zShift z s) (Work.FTS.StrongEps.thShift θ p.2)) p.1
        = - Work.Spaces.mixed j i f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) := by
    intro p
    rw [Work.FTS.StrongEps.KernAux.deriv_shift_fst (Work.Spaces.mixed (j - 1) i f)
      hz hθ (hsm 1) p, hDz]
  calc ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
        * Work.Spaces.mixed j i f (Work.FTS.StrongEps.zShift z p.1)
            (Work.FTS.StrongEps.thShift θ p.2)
      = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * (- deriv (fun s : ℝ => Work.Spaces.mixed (j - 1) i f
              (Work.FTS.StrongEps.zShift z s) (Work.FTS.StrongEps.thShift θ p.2)) p.1) := by
        refine integral_congr_ae (Eventually.of_forall fun p => ?_)
        simp only [hvs p]
        ring
    _ = - ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * deriv (fun s : ℝ => Work.Spaces.mixed (j - 1) i f
              (Work.FTS.StrongEps.zShift z s) (Work.FTS.StrongEps.thShift θ p.2)) p.1 := by
        rw [← integral_neg]
        exact integral_congr_ae (Eventually.of_forall fun p => by ring)
    _ = - (- ∫ p : ℝ × ℝ, deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1
          * Work.Spaces.mixed (j - 1) i f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2)) := by rw [hIBP]
    _ = ∫ p : ℝ × ℝ, deriv (fun s : ℝ => Work.FTS.StrongEps.Jker ρ ε (s, p.2)) p.1
          * Work.Spaces.mixed (j - 1) i f (Work.FTS.StrongEps.zShift z p.1)
              (Work.FTS.StrongEps.thShift θ p.2) := by rw [neg_neg]

end Work.FTS.StrongEps.StepFacts
end
-- ===== merged: Submission.Work.FTS.StrongEps.blocks.star_blocks_bnd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.blocks

set_option autoImplicit false

/-! ## Pointwise bounds on the star coefficients `ℛ, 𝒰, 𝒱` at `Φ̃_* = Φ_* - Θ_*(α)`

The package `StarPkgo2` records, among other things, the `𝒲^{4,∞}`-bounds of the two weighted
coefficients `((z+1)/z)·ℛ(Φ̃_*)` and `𝒱(Φ̃_*)`.  The pointwise consequence of the `𝒲^{4,∞}`-norm
(`Work.Spaces.WlInf_z_bound`) turns those into the pointwise bounds `Rop_PhiTs_abs_le_max` and
`Vop_PhiTs_abs_le_max`; note that they hold for **every** value of `α` (in particular no
positivity of `α` is required: the weight `(z+1)/z` is `≥ 1` for `z > 0`, and a negative bound
only makes the statement stronger).

The third operator `𝒰` is *not* bounded in the package, but it is not independent of the other
two: the pointwise identity (valid on `cos θ ≠ 0`)

  `ℛ(Ψ) - 𝒱(Ψ) = tan θ·(3Ψ + α z ∂_zΨ) = - tan θ·𝒰(Ψ)`

(`Work.FTS.Nonlinear.Pieces.Rl1.Rop_sub_Vop_eq_tan`) shows that on the angular region
`θ ≥ c > 0`, on which `tan θ` is bounded *below* by `tan c > 0`, the uniform bound on `𝒰` is
that of `ℛ` and `𝒱` multiplied by the finite constant `cot c`.  This is the content of
`Uop_PhiTs_abs_le_mul`; it is the reason the statement is true up to the axis `θ = π/2`
(as `θ → π/2` the factor `cot θ` *decreases* to `0`, while the corresponding factor for the
field `𝒰/sin(2θ)` of the package would blow up). -/

/-- Pointwise bound on `ℛ(Φ̃_*)` from the `𝒲^{4,∞}`-field `StarPkgo2.RW`: the weight `(z+1)/z`
is `≥ 1` for `z > 0`. -/
theorem Rop_PhiTs_abs_le_max {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ| ≤ max (Cs * α) 0 := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hmem : Work.Spaces.WlInfMem α 4
      (fun z θ => (z + 1) / z
        * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) := hstar.RW.1
  have hb : Work.Spaces.WlInf α 4
      (fun z θ => (z + 1) / z
        * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) ≤ Cs * α := hstar.RW.2
  have h0 := Work.Spaces.WlInf_z_bound α 4 _ hmem 0 (Nat.zero_le 4) z θ hzI hθ
  have h1 : |(z + 1) / z * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
      ≤ Cs * α := by
    refine le_trans ?_ hb
    simpa only [Work.Spaces.pzIter_zero, pow_zero, one_mul] using h0
  have hge1 : (1 : ℝ) ≤ (z + 1) / z := by
    rw [le_div_iff₀ hz]
    linarith
  have hpos : 0 < (z + 1) / z := lt_of_lt_of_le zero_lt_one hge1
  calc |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
      = 1 * |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ| := (one_mul _).symm
    _ ≤ ((z + 1) / z) * |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ| :=
        mul_le_mul_of_nonneg_right hge1 (abs_nonneg _)
    _ = |(z + 1) / z * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ| := by
        rw [abs_mul, abs_of_pos hpos]
    _ ≤ max (Cs * α) 0 := le_trans h1 (le_max_left _ _)

/-- Pointwise bound on `𝒱(Φ̃_*)` from the `𝒲^{4,∞}`-field `StarPkgo2.VW`. -/
theorem Vop_PhiTs_abs_le_max {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ| ≤ max (Cs * α) 0 := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hmem : Work.Spaces.WlInfMem α 4
      (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs)) := hstar.VW.1
  have hb : Work.Spaces.WlInf α 4
      (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs)) ≤ Cs * α := hstar.VW.2
  have h1 := Work.Spaces.WlInf_z_bound α 4 _ hmem 0 (Nat.zero_le 4) z θ hzI hθ
  have h1' : |Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ| ≤ Cs * α := by
    refine le_trans ?_ hb
    simpa only [Work.Spaces.pzIter_zero, pow_zero, one_mul] using h1
  exact le_trans h1' (le_max_left _ _)

/-- Pointwise bound on `𝒰(Φ̃_*)` on the angular region `c ≤ θ < π/2`, `c > 0`, from the bounds
on `ℛ` and `𝒱` and the identity `tan θ·𝒰 = 𝒱 - ℛ`.  The constant is `2·cot c·max (Cs α) 0`,
which is finite precisely because `θ ≥ c > 0`. -/
theorem Uop_PhiTs_abs_le_mul {α Cs c : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) {z θ : ℝ} (hz : 0 < z) (hc : 0 < c)
    (hcθ : c ≤ θ) (hθ : θ < Real.pi / 2) :
    |Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
      ≤ 2 * max (Cs * α) 0 * |Real.cos c / Real.sin c| := by
  have hθpos : 0 < θ := lt_of_lt_of_le hc hcθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθpos, le_of_lt hθ⟩
  have hclt : c < Real.pi / 2 := lt_of_le_of_lt hcθ hθ
  have hR := Rop_PhiTs_abs_le_max hstar hz hθI
  have hV := Vop_PhiTs_abs_le_max hstar hz hθI
  -- the pointwise identity `tan θ·𝒰 = -(ℛ - 𝒱)`
  have hcosθ : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ⟩)
  have htanU : Real.tan θ * Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
      = -(Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
          - Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ) := by
    have h := Work.FTS.Nonlinear.Pieces.Rl1.Rop_sub_Vop_eq_tan α
      (Work.FTS.VocabO2.PhiTs α Φs) (z := z) hcosθ
    have h2 : 3 * Work.FTS.VocabO2.PhiTs α Φs z θ
        + α * z * Work.Spaces.pz (Work.FTS.VocabO2.PhiTs α Φs) z θ
        = -(Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) := by
      simp only [Work.Construction.Uop]
      ring
    rw [h2] at h
    rw [h]
    ring
  have htan_le : Real.tan c ≤ Real.tan θ := by
    rcases lt_or_eq_of_le hcθ with hlt | heq
    · exact le_of_lt (Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two hc.le hθ hlt)
    · rw [heq]
  have htanθpos : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two hθpos hθ
  have htri : |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
      - Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ| ≤ 2 * max (Cs * α) 0 := by
    have hab : |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
        - Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ|
        ≤ |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
          + |Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ| := by
      have h := abs_add_le (Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ)
        (-(Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ))
      rw [abs_neg] at h
      simpa only [sub_eq_add_neg] using h
    linarith [hR, hV]
  have hTU : Real.tan c * |Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
      ≤ 2 * max (Cs * α) 0 := by
    have h2 : Real.tan θ * |Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
        = |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
            - Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ| := by
      have h := congrArg (fun x : ℝ => |x|) htanU
      rw [abs_mul, abs_neg, abs_of_pos htanθpos] at h
      exact h
    calc Real.tan c * |Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
        ≤ Real.tan θ * |Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ| :=
          mul_le_mul_of_nonneg_right htan_le (abs_nonneg _)
      _ = |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
            - Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ| := h2
      _ ≤ 2 * max (Cs * α) 0 := htri
  have htanpos : 0 < Real.tan c := Real.tan_pos_of_pos_of_lt_pi_div_two hc hclt
  have hU1 : |Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
      ≤ 2 * max (Cs * α) 0 / Real.tan c := by
    rw [le_div_iff₀ htanpos]
    have h := hTU
    rw [mul_comm (Real.tan c)] at h
    exact h
  have hsinpos : 0 < Real.sin c :=
    Real.sin_pos_of_pos_of_lt_pi hc (by linarith [hclt, Real.pi_pos])
  have hcospos : 0 < Real.cos c := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hclt⟩
  have hU2 : 2 * max (Cs * α) 0 / Real.tan c
      = 2 * max (Cs * α) 0 * |Real.cos c / Real.sin c| := by
    rw [Real.tan_eq_sin_div_cos, abs_of_pos (div_pos hcospos hsinpos),
      div_eq_mul_inv (2 * max (Cs * α) 0) (Real.sin c / Real.cos c),
      inv_div (Real.sin c) (Real.cos c)]
  exact hU1.trans (le_of_eq hU2)

theorem star_blocks_bnd {α Cs c : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ z θ : ℝ, 0 < z → c ≤ θ → θ < Real.pi / 2 →
      |Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
        + |Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
        + |Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
        ≤ C := by
  change ∃ C : ℝ, 0 < C ∧ ∀ z θ : ℝ, 0 < z → c ≤ θ → θ < Real.pi / 2 →
      |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
        + |Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
        + |Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ| ≤ C
  refine ⟨(2 + 2 * |Real.cos c / Real.sin c|) * max (Cs * α) 0 + 1, ?_, ?_⟩
  · have h1 : 0 ≤ (2 + 2 * |Real.cos c / Real.sin c|) * max (Cs * α) 0 :=
      mul_nonneg (by positivity) (le_max_right _ _)
    linarith
  · intro z θ hz hcθ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt (lt_of_lt_of_le hc hcθ), le_of_lt hθ⟩
    have hR := Rop_PhiTs_abs_le_max hstar hz hθI
    have hV := Vop_PhiTs_abs_le_max hstar hz hθI
    have hU := Uop_PhiTs_abs_le_mul hstar hz hc hcθ hθ
    calc |Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
          + |Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ|
          + |Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ|
        ≤ (2 + 2 * |Real.cos c / Real.sin c|) * max (Cs * α) 0 := by
          nlinarith [hR, hV, hU]
      _ ≤ (2 + 2 * |Real.cos c / Real.sin c|) * max (Cs * α) 0 + 1 := by linarith

end Work.FTS.StrongEps.blocks
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux.mismatchCaseLt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `a₁ < a` case of the mismatch coefficient estimate

This file proves the `a₁ < a` branch of `T6CoefAux.mismatchCoefCase`: the coefficient

`∫∫ w² sin(2θ)^{-γ} · (D_z^{b₁}D_θ^{a₁} A) · (D_z^{b-b₁}D_θ^{a-a₁} f) · (D_z^b D_θ^a f)`

where the `A`-slot carries `1 ≤ a₁` angular derivatives and `a₁ + b₁ ≤ 2`.  The pointwise
bound `|D_z^{b₁}D_θ^{a₁} A(z,θ)| ≤ √15 · Xn α A` (`T2SupB2.mixed_pointwise_le_Xn`) turns
the `A`-factor into the constant `K4`, and the two `f`-factors — both *mixed* slots of total
order `≤ 6` with at least one angular derivative — are absorbed by the `σ^{-γ}`-weighted
AM–GM estimate against the single mixed slots of `HkSq α 6 f` (`mismatchAux.mixed_slot_le`).
-/

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

/-- The product measure on the quadrant, spelled out (so that every statement below is
syntactically the measure occurring in the goal). -/
local notation "PM" => MeasureTheory.Measure.prod
  (MeasureTheory.volume.restrict Work.Spaces.Iz) (MeasureTheory.volume.restrict Work.Spaces.Iθ)

/-- `|a b| ≤ (a² + b²)/2`. -/
private lemma abs_mul_le_half_sq_add (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  rw [abs_mul]
  have h := two_mul_le_add_sq |a| |b|
  rw [sq_abs a, sq_abs b] at h
  linarith

set_option maxHeartbeats 1600000 in
theorem mismatchCaseLt : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (A f : ℝ → ℝ → ℝ) (K0 K4 : ℝ) (a b a₁ b₁ : ℕ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.HkMem α 4 A →
      Work.Spaces.HkMem α 6 A →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ K0) →
      Work.FTS.Nonlin.Xn α A ≤ K4 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 7 f →
      Work.Spaces.VanishTheta f →
      1 ≤ a₁ → a₁ + b₁ ≤ 2 → a₁ ≤ a → b₁ ≤ b → a + b ≤ 6 → a₁ < a →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2
          * Work.Spaces.mixed b₁ a₁ A p.1 p.2
          * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
          * Work.Spaces.mixed b a f p.1 p.2)
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      |∫ p, Work.FTS.TransportS.leafGam α p.1 p.2
            * Work.Spaces.mixed b₁ a₁ A p.1 p.2
            * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
            * Work.Spaces.mixed b a f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ C * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) := by
  obtain ⟨Cm, hCmpos, hCm⟩ := Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
  refine ⟨Cm, hCmpos, ?_⟩
  intro α hα A f K0 K4 a b a₁ b₁ hAsm hA4 hA6 hAbdd hA4bnd hfsm hf7 hfv
    ha₁ hab₁ ha₁a hb₁b hab hlt
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hK0 : 0 ≤ K0 := by
    have h := hAbdd 1 (Real.pi / 4) one_pos (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
    have h2 := abs_nonneg (A 1 (Real.pi / 4))
    linarith
  have hK4 : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hA4bnd
  have h6 : Work.Spaces.HkMem α 6 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hfsm 6 (by norm_num) hf7
  have hH : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hα3 : (1 : ℝ) ≤ α ^ (-(3 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (show (-(3 : ℝ)) ≤ 0 by norm_num)
    rwa [Real.rpow_zero] at h
  -- the two mixed `f`-slots and their `σ^{-γ}`-weighted bounds
  have hYint := mixed_slot_le (α := α) 6 hfsm h6 (i := a - a₁) (j := b - b₁)
    (by omega) (by omega)
  have hZint := mixed_slot_le (α := α) 6 hfsm h6 (i := a) (j := b) (by omega) (by omega)
  have hYint' : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2) ^ 2) PM := hYint.1
  have hZint' : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed b a f p.1 p.2) ^ 2) PM := hZint.1
  have hYval : (∫ p, (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2) ^ 2 ∂PM)
      ≤ Work.Spaces.HkSq α 6 f := hYint.2
  have hZval : (∫ p, (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed b a f p.1 p.2) ^ 2 ∂PM) ≤ Work.Spaces.HkSq α 6 f := hZint.2
  -- the pointwise bound on the `A`-slot
  have hXpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b₁ a₁ A z θ| ≤ Cm * K4 := by
    intro z θ hz hθ0 hθ1
    exact le_trans (hCm α A hα0 hα1 hAsm hA4 b₁ a₁ ha₁ hab₁ z θ hz hθ0 hθ1)
      (mul_le_mul_of_nonneg_left hA4bnd hCmpos.le)
  set F : ℝ × ℝ → ℝ := fun p => Work.FTS.TransportS.leafGam α p.1 p.2
      * Work.Spaces.mixed b₁ a₁ A p.1 p.2
      * Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2
      * Work.Spaces.mixed b a f p.1 p.2 with hFdef
  have hFaesm : MeasureTheory.AEStronglyMeasurable F PM := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.leafGam α p.1 p.2)
        Work.FTS.EllipticEst.Q0 := by
      unfold Work.FTS.TransportS.leafGam
      exact contOn_w.mul (contOn_sig α)
    have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed b₁ a₁ A p.1 p.2)
        Work.FTS.EllipticEst.Q0 := (hAsm.mixed b₁ a₁).continuousOn
    have h3 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2)
        Work.FTS.EllipticEst.Q0 := (hfsm.mixed (b - b₁) (a - a₁)).continuousOn
    have h4 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed b a f p.1 p.2)
        Work.FTS.EllipticEst.Q0 := (hfsm.mixed b a).continuousOn
    rw [hFdef]
    exact Work.Spaces.aesm_of_continuousOn_Qd _ (((h1.mul h2).mul h3).mul h4)
  -- the pointwise AM–GM majorant
  have hpt : ∀ᵐ p ∂PM, |F p| ≤ Cm * K4 * ((1 / 2) *
      ((Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2) ^ 2
        + (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed b a f p.1 p.2) ^ 2)) := by
    refine Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ0 hθ1 => ?_)
    dsimp only
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have hWnn : 0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs.le _)
    have hb := hXpt z θ hz hθ0 hθ1
    have hgm : |Work.Spaces.mixed (b - b₁) (a - a₁) f z θ| * |Work.Spaces.mixed b a f z θ|
        ≤ (1 / 2) * ((Work.Spaces.mixed (b - b₁) (a - a₁) f z θ) ^ 2
            + (Work.Spaces.mixed b a f z θ) ^ 2) := by
      have h := abs_mul_le_half_sq_add (Work.Spaces.mixed (b - b₁) (a - a₁) f z θ)
        (Work.Spaces.mixed b a f z θ)
      rw [abs_mul] at h
      linarith
    have hFp : |F (z, θ)| = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * |Work.Spaces.mixed b₁ a₁ A z θ|
        * (|Work.Spaces.mixed (b - b₁) (a - a₁) f z θ| * |Work.Spaces.mixed b a f z θ|) := by
      rw [hFdef]
      simp only [Work.FTS.TransportS.leafGam]
      rw [abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs.le _))]
      ring
    rw [hFp]
    have hnn : 0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (|Work.Spaces.mixed (b - b₁) (a - a₁) f z θ| * |Work.Spaces.mixed b a f z θ|) :=
      mul_nonneg hWnn (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hkey : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * |Work.Spaces.mixed b₁ a₁ A z θ|
          * (|Work.Spaces.mixed (b - b₁) (a - a₁) f z θ| * |Work.Spaces.mixed b a f z θ|)
        ≤ Cm * K4 * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (|Work.Spaces.mixed (b - b₁) (a - a₁) f z θ| * |Work.Spaces.mixed b a f z θ|)) := by
      calc (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * |Work.Spaces.mixed b₁ a₁ A z θ|
            * (|Work.Spaces.mixed (b - b₁) (a - a₁) f z θ| * |Work.Spaces.mixed b a f z θ|)
          = ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (|Work.Spaces.mixed (b - b₁) (a - a₁) f z θ| * |Work.Spaces.mixed b a f z θ|))
            * |Work.Spaces.mixed b₁ a₁ A z θ| := by ring
        _ ≤ ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (|Work.Spaces.mixed (b - b₁) (a - a₁) f z θ| * |Work.Spaces.mixed b a f z θ|))
            * (Cm * K4) := mul_le_mul_of_nonneg_left hb hnn
        _ = Cm * K4 * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (|Work.Spaces.mixed (b - b₁) (a - a₁) f z θ| * |Work.Spaces.mixed b a f z θ|)) := by
            ring
    have hgm2 : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (|Work.Spaces.mixed (b - b₁) (a - a₁) f z θ| * |Work.Spaces.mixed b a f z θ|)
        ≤ (1 / 2) * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed (b - b₁) (a - a₁) f z θ) ^ 2
          + (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed b a f z θ) ^ 2) := by
      have h1 := mul_le_mul_of_nonneg_left hgm hWnn
      have h2 : (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * ((1 / 2) * ((Work.Spaces.mixed (b - b₁) (a - a₁) f z θ) ^ 2
              + (Work.Spaces.mixed b a f z θ) ^ 2))
          = (1 / 2) * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed (b - b₁) (a - a₁) f z θ) ^ 2
            + (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed b a f z θ) ^ 2) := by ring
      linarith
    exact hkey.trans (mul_le_mul_of_nonneg_left hgm2 (mul_nonneg hCmpos.le hK4))
  have hMint : MeasureTheory.Integrable (fun p : ℝ × ℝ => Cm * K4 * ((1 / 2) *
      ((Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2) ^ 2
        + (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed b a f p.1 p.2) ^ 2))) PM :=
    ((hYint'.add hZint').const_mul (1 / 2)).const_mul (Cm * K4)
  have hval : (∫ p, Cm * K4 * ((1 / 2) *
      ((Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed (b - b₁) (a - a₁) f p.1 p.2) ^ 2
        + (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed b a f p.1 p.2) ^ 2)) ∂PM)
      ≤ Cm * K4 * (1 + Work.Spaces.HkSq α 6 f) := by
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add hYint' hZint']
    have hCK : 0 ≤ Cm * K4 := mul_nonneg hCmpos.le hK4
    nlinarith [hYval, hZval, hCK, hH]
  have hmain := abs_integral_le_of_pointwise hMint hFaesm hpt
  have hbnd : |∫ p, F p ∂PM| ≤ Cm * K4 * (1 + Work.Spaces.HkSq α 6 f) := hmain.trans hval
  refine ⟨?_, ?_⟩
  · rw [hFdef]
    exact MeasureTheory.Integrable.mono' hMint hFaesm (by
      filter_upwards [hpt] with p hp
      rwa [hFdef] at hp)
  · calc |∫ p, F p ∂PM|
        ≤ Cm * K4 * (1 + Work.Spaces.HkSq α 6 f) := hbnd
      _ ≤ Cm * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f))) := by
          rw [show Cm * K4 * (1 + Work.Spaces.HkSq α 6 f)
              = Cm * (K4 * (1 + Work.Spaces.HkSq α 6 f)) from by ring]
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hCmpos)
          have h5 : 0 ≤ 1 + Work.Spaces.HkSq α 6 f := by linarith
          calc K4 * (1 + Work.Spaces.HkSq α 6 f)
              ≤ (1 + K4) * (1 + Work.Spaces.HkSq α 6 f) :=
                mul_le_mul_of_nonneg_right (by linarith) h5
            _ ≤ (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f) :=
                mul_le_mul_of_nonneg_right (by linarith) h5
            _ ≤ α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) :=
                le_mul_of_one_le_left (mul_nonneg (by linarith) h5) hα3
      _ = Cm * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) := by ring

end

end Work.FTS.StrongPersist.H6Pair6Aux.T6CoefAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.wprod6.zslot_le_winf6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-
# `zslot_le_winf6` — the radial `D_z`-slots of the `𝒲^{6,∞}`-priced product rule

For `f` of class `Work.FTS.EllipticEst.SmoothOpen` (`C^∞` on the *open* quadrant) and of class
`𝒲^{6,∞}` (`Work.Spaces.WlInfMem α 6 f`), and for an arbitrary `SmoothOpen` `g`, every pure
radial slot of the product `f·g` is dominated pointwise by the `𝒲^{6,∞}`-norm of the coefficient
times the `ℋ⁶`-integrand of `g`:

`(D_z^i (f·g)(z,θ) · w(z)/sin(2θ)^{η/2})² ≤ C |f|²_{𝒲^{6,∞}} · HkIntegrand α 6 g z θ`,  `i ≤ 6`,

with a universal constant `C` (here `10^12`), at every *interior* point `z > 0`, `0 < θ < π/2`.

This is the level-six instance of `Work.FTS.OpenPkg.WProdWin.zslot_le_winf` (the proved level-four
statement).  The proof is the same:

* expand `D_z^i (f·g)` with the Leibniz rule for `D_z = z∂_z` in the open quadrant
  (`Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz`, which needs only `SmoothOpen f`, `SmoothOpen g`
  at `z > 0`, `0 < θ < π/2`);
* bound the square of the finite sum by `card • Σ (·)²` (`sq_sum_le_card_mul_sum_sq`);
* bound each `f`-factor by `1000 |f|_𝒲` (`Work.FTS.StrongPersist.N6Trans.dzIter_le_WlInf6`,
  the level-six instance of the `𝒲^{6,∞}`-bound on the radial derivatives) and each `g`-factor by
  the corresponding slot of `HkIntegrand α 6 g` (`Work.Spaces.sq_le_HkIntegrand_z`, which needs no
  hypothesis at all since `HkIntegrand` is a sum of squares);
* bound the binomial coefficients by `4096` (`Nat.choose_le_two_pow`: `i.choose b ≤ 2^i ≤ 2^6 = 64`
  for `i ≤ 6`).

Note that `g` is *not* required to lie in `ℋ⁶`: the `g`-side only appears through the
(nonnegative, always finite) integrand `HkIntegrand α 6 g`, which is exactly what the consumer
of this slot bounds by the `ℋ⁶`-norm.
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.FTS.StrongPersist.H6Rows.wprod6

/-- The binomial coefficients of the rows `0 ≤ n ≤ 6` are at most `20`, in particular
`squared` they are at most `4096` (via the coarse but purely structural bound
`n.choose k ≤ 2^n ≤ 2^6 = 64`). -/
private theorem choose_sq_le_4096 (n k : ℕ) (_hkn : k ≤ n) (hn : n ≤ 6) :
    ((n.choose k : ℕ) : ℝ) ^ 2 ≤ 4096 := by
  have h1 : n.choose k ≤ 64 := by
    have h2 : n.choose k ≤ 2 ^ n := Nat.choose_le_two_pow n k
    have h3 : 2 ^ n ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hn
    have h4 : (2 : ℕ) ^ 6 = 64 := by norm_num
    omega
  have h1' : ((n.choose k : ℕ) : ℝ) ≤ 64 := by exact_mod_cast h1
  have h0 : (0 : ℝ) ≤ ((n.choose k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hm := mul_self_le_mul_self h0 h1'
  rw [sq]
  norm_num at hm ⊢
  linarith [hm]

theorem zslot_le_winf6 : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 6 f →
      Work.FTS.EllipticEst.SmoothOpen g →
      ∀ i : ℕ, i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ C * (Work.Spaces.WlInf α 6 f) ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ := by
  refine ⟨10 ^ 12, by norm_num, ?_⟩
  intro α f g _hα _hα1 hf hfm hg i hi z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hW : 0 ≤ Work.Spaces.WlInf α 6 f := Work.Spaces.WlInf_nonneg α 6 f hfm
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
  -- the per-term bound: the `f`-factor costs `1000 |f|_𝒲`, the binomial coefficient costs `4096`
  have hper : ∀ b ∈ Finset.range (i + 1),
      (((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
          * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2
        ≤ 4096000000 * (Work.Spaces.WlInf α 6 f) ^ 2
          * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by
    intro b hb
    have hbi : b ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hDf : |Work.Spaces.DzIter b f z θ| ≤ 1000 * Work.Spaces.WlInf α 6 f :=
      Work.FTS.StrongPersist.N6Trans.dzIter_le_WlInf6 hf hfm (by omega) hz hθ
    have hx : (Work.Spaces.DzIter b f z θ) ^ 2
        ≤ (1000 * Work.Spaces.WlInf α 6 f) ^ 2 := by
      have hB : (0 : ℝ) ≤ 1000 * Work.Spaces.WlInf α 6 f := mul_nonneg (by norm_num) hW
      have h1 := (abs_le.mp hDf).1
      have h2 := (abs_le.mp hDf).2
      nlinarith [hB, h1, h2]
    have hch : ((i.choose b : ℝ)) ^ 2 ≤ 4096 := choose_sq_le_4096 i b hbi hi
    calc (((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
          * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2
        = ((i.choose b : ℝ)) ^ 2 * (Work.Spaces.DzIter b f z θ) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by ring
      _ ≤ 4096 * (1000 * Work.Spaces.WlInf α 6 f) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by gcongr
      _ = 4096000000 * (Work.Spaces.WlInf α 6 f) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2 := by ring
  -- each surviving `g`-factor is a pure slot of `HkIntegrand α 6 g`
  have hsumsq : ∑ b ∈ Finset.range (i + 1),
        (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2
      ≤ 7 * Work.Spaces.HkIntegrand α 6 g z θ := by
    calc ∑ b ∈ Finset.range (i + 1), (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2
        ≤ ∑ _b ∈ Finset.range (i + 1), Work.Spaces.HkIntegrand α 6 g z θ :=
          Finset.sum_le_sum (fun b _ =>
            Work.Spaces.sq_le_HkIntegrand_z α 6 g z θ (i - b) (by omega))
      _ = ((i : ℝ) + 1) * Work.Spaces.HkIntegrand α 6 g z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ 7 * Work.Spaces.HkIntegrand α 6 g z θ := by
          have hnn := Work.Spaces.HkIntegrand_nonneg α 6 g z θ
          have hI2 : (i : ℝ) + 1 ≤ 7 := by exact_mod_cast (by omega : i + 1 ≤ 7)
          nlinarith
  calc (∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
            * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2
      ≤ (((Finset.range (i + 1)).card : ℕ) : ℝ) *
          ∑ b ∈ Finset.range (i + 1),
            (((i.choose b : ℝ) * Work.Spaces.DzIter b f z θ)
              * (Work.Spaces.DzIter (i - b) g z θ * Hv)) ^ 2 := hcs
    _ ≤ ((i : ℝ) + 1) * ∑ b ∈ Finset.range (i + 1),
          (4096000000 * (Work.Spaces.WlInf α 6 f) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2) := by
        rw [hcard]
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hper) (by positivity)
    _ = 4096000000 * (Work.Spaces.WlInf α 6 f) ^ 2 * (((i : ℝ) + 1)
          * ∑ b ∈ Finset.range (i + 1), (Work.Spaces.DzIter (i - b) g z θ * Hv) ^ 2) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ 4096000000 * (Work.Spaces.WlInf α 6 f) ^ 2
          * (7 * (7 * Work.Spaces.HkIntegrand α 6 g z θ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hI2 : (i : ℝ) + 1 ≤ 7 := by exact_mod_cast (by omega : i + 1 ≤ 7)
        exact mul_le_mul hI2 hsumsq (Finset.sum_nonneg (fun b _ => sq_nonneg _)) (by norm_num)
    _ ≤ 10 ^ 12 * (Work.Spaces.WlInf α 6 f) ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ := by
        have hnn := Work.Spaces.HkIntegrand_nonneg α 6 g z θ
        have h2 : 0 ≤ (Work.Spaces.WlInf α 6 f) ^ 2 := sq_nonneg _
        have hh : 4096000000 * (Work.Spaces.WlInf α 6 f) ^ 2
              * (7 * (7 * Work.Spaces.HkIntegrand α 6 g z θ))
            = 200704000000 * ((Work.Spaces.WlInf α 6 f) ^ 2
              * Work.Spaces.HkIntegrand α 6 g z θ) := by ring
        rw [hh, show (10 : ℝ) ^ 12 * (Work.Spaces.WlInf α 6 f) ^ 2
              * Work.Spaces.HkIntegrand α 6 g z θ
            = 10 ^ 12 * ((Work.Spaces.WlInf α 6 f) ^ 2
              * Work.Spaces.HkIntegrand α 6 g z θ) from by ring]
        exact mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg h2 hnn)

end Work.FTS.StrongPersist.H6Rows.wprod6
end
-- ===== merged: Submission.Work.FTS.StrongPersist.HkAddFin =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist

open MeasureTheory Set

/-- **Closure of `ℋ^k` under addition, at finite smoothness, together with the `√2`-triangle
inequality for the norm.**

Both halves are already available in the library in exactly the required form:

* the *membership* half is `Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkMem_add_of_contDiffOn_le`
  — the `C^k`-on-the-open-quadrant version of `HkMem`-closure (its proof uses the pointwise
  subadditivity `HkIntegrand_add_le_domain` of the integrand, which extends the interior
  inequality `Work.FTS.EllipticEst.Cores.DiagEstEllT.HkIntegrand_add_le_of_contDiffOn` to the
  boundary lines `z = 0` and `sin 2θ = 0` where every integrand vanishes);
* the *norm* half is `Work.FTS.EllipticEst.HkSq_add_le_of_pointwise` (which needs only the
  pointwise subadditivity of the integrand together with `HkMem` of the two summands, no further
  smoothness), followed by the scalar inequality `√(2x + 2y) ≤ √2 (√x + √y)`.

Note that `HkMem α k (f + g)` is *not* needed for the norm half beyond what
`HkSq_add_le_of_pointwise` consumes: the honesty of the three squared norms is precisely the two
hypotheses `hmf`, `hmg` (the pointwise inequality `hpt` bounds the integrand of the sum by an
integrable majorant, and `HkIntegrand_nonneg` supplies the a.e.-positivity). -/
theorem HkAddFin {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ k (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ k (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => f z θ + g z θ) ∧
      Work.Spaces.HkNorm α k (fun z θ => f z θ + g z θ)
        ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k f + Work.Spaces.HkNorm α k g) := by
  -- the pointwise subadditivity of the integrand on the closed quadrant
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α k f z θ
          + 2 * Work.Spaces.HkIntegrand α k g z θ :=
    Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α k hf hg
  refine ⟨Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkMem_add_of_contDiffOn_le α k hf hg hmf hmg,
    ?_⟩
  -- the squared estimate
  have hsq : Work.Spaces.HkSq α k (fun z θ => f z θ + g z θ)
      ≤ 2 * Work.Spaces.HkSq α k f + 2 * Work.Spaces.HkSq α k g :=
    Work.FTS.EllipticEst.HkSq_add_le_of_pointwise α k hmf hmg hpt
  have hx : 0 ≤ Work.Spaces.HkSq α k f := Work.Spaces.HkSq_nonneg α k f
  have hy : 0 ≤ Work.Spaces.HkSq α k g := Work.Spaces.HkSq_nonneg α k g
  -- take square roots: `HkNorm` is `√(HkSq)`
  have hroot : Work.Spaces.HkNorm α k (fun z θ => f z θ + g z θ)
      ≤ Real.sqrt (2 * Work.Spaces.HkSq α k f + 2 * Work.Spaces.HkSq α k g) :=
    Real.sqrt_le_sqrt hsq
  refine le_trans hroot ?_
  have hsqrt : Real.sqrt (2 * Work.Spaces.HkSq α k f + 2 * Work.Spaces.HkSq α k g)
      = Real.sqrt 2 * Real.sqrt (Work.Spaces.HkSq α k f + Work.Spaces.HkSq α k g) := by
    rw [show 2 * Work.Spaces.HkSq α k f + 2 * Work.Spaces.HkSq α k g
        = 2 * (Work.Spaces.HkSq α k f + Work.Spaces.HkSq α k g) by ring,
      Real.sqrt_mul (by norm_num)]
  rw [hsqrt, Work.Spaces.HkNorm, Work.Spaces.HkNorm]
  exact mul_le_mul_of_nonneg_left
    (Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.sqrt_add_le_honest hx hy)
    (Real.sqrt_nonneg 2)

end Work.FTS.StrongPersist
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Aux.HkMem_HkSq_add3_le =====
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
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- The datum `f + g - h` of `HkMem_HkSq_add3_le`. -/
private abbrev add3E (f g h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => f z θ + g z θ - h z θ

/-- The partial sum `f + g` of `HkMem_HkSq_add3_le`. -/
private abbrev add3A (f g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => f z θ + g z θ

/-- The negated third summand `-h` of `HkMem_HkSq_add3_le`. -/
private abbrev add3B (h : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => - h z θ

theorem HkMem_HkSq_add3_le (α : ℝ) (k : ℕ) (hk : 1 ≤ k) {f g h : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ k (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ k (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    (hh : ContDiffOn ℝ k (Function.uncurry h) Work.FTS.EllipticEst.Q0)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g)
    (hmh : Work.Spaces.HkMem α k h) :
    Work.Spaces.HkMem α k (fun z θ => f z θ + g z θ - h z θ) ∧
    Work.Spaces.HkSq α k (fun z θ => f z θ + g z θ - h z θ)
      ≤ 4 * (Work.Spaces.HkSq α k f + Work.Spaces.HkSq α k g + Work.Spaces.HkSq α k h) := by
  -- The two summands of the split `f + g - h = A + B`, with `A = f + g` and `B = -h`.
  have hA : ContDiffOn ℝ k (Function.uncurry (add3A f g)) Work.FTS.EllipticEst.Q0 :=
    (hf.add hg).congr (fun p hp => by rfl)
  have hB : ContDiffOn ℝ k (Function.uncurry (add3B h)) Work.FTS.EllipticEst.Q0 :=
    (hh.neg).congr (fun p hp => by rfl)
  have hE : ContDiffOn ℝ k (Function.uncurry (add3E f g h)) Work.FTS.EllipticEst.Q0 :=
    (hA.add hB).congr (fun p hp => by rfl)
  -- Honesty of the first summand, and the pointwise subadditivity for both splits.
  have hmA : Work.Spaces.HkMem α k (add3A f g) :=
    Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkMem_add_of_contDiffOn_le α k hf hg hmf hmg
  have hptA : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (add3A f g) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α k f z θ + 2 * Work.Spaces.HkIntegrand α k g z θ :=
    Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain α k hf hg
  -- The integrand is invariant under the sign flip `h ↦ -h`.
  have hneg : ∀ z θ, Work.Spaces.HkIntegrand α k (add3B h) z θ
      = Work.Spaces.HkIntegrand α k h z θ :=
    fun z θ => congrFun (congrFun (Work.FTS.EllipticEst.HkIntegrand_neg α k h) z) θ
  have hptE : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (add3E f g h) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α k (add3A f g) z θ
          + 2 * Work.Spaces.HkIntegrand α k h z θ := by
    intro z hz θ hθ
    have h1 := Work.FTS.EllipticEst.Cores.AlphaRateEstEllT.HkIntegrand_add_le_domain
      α k hA hB z hz θ hθ
    rw [hneg z θ] at h1
    exact h1
  -- The first conjunct: honesty of `f + g - h` by domination.
  have hmE : Work.Spaces.HkMem α k (add3E f g h) := by
    refine Work.FTS.EllipticEst.Cores.DiagEstEllT.HkMem_of_add_dominated_cont α k
      (Work.FTS.EllipticEst.Cores.DiagEstEllT.continuousOn_HkIntegrand_of_contDiffOn hE α)
      hmA hmh ?_
    intro z hz
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact hptE z hz θ hθ
  -- The second conjunct: the square, integrated twice.
  have hsqA : Work.Spaces.HkSq α k (add3A f g)
      ≤ 2 * Work.Spaces.HkSq α k f + 2 * Work.Spaces.HkSq α k g :=
    Work.FTS.EllipticEst.HkSq_add_le_of_pointwise α k hmf hmg hptA
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (add3E f g h) z θ)
        ≤ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (add3A f g) z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ) := by
    intro z hz
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun θ => Work.Spaces.HkIntegrand α k (add3E f g h) z θ)
      (g := fun θ => 2 * Work.Spaces.HkIntegrand α k (add3A f g) z θ
        + 2 * Work.Spaces.HkIntegrand α k h z θ)
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k (add3E f g h) z θ)
      (((hmA.1 z hz).const_mul 2).add ((hmh.1 z hz).const_mul 2))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => hptE z hz θ hθ)
    exact hmono.trans_eq (by
      rw [MeasureTheory.integral_add ((hmA.1 z hz).const_mul 2) ((hmh.1 z hz).const_mul 2),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul])
  have houter := MeasureTheory.integral_mono_of_nonneg
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (f := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (add3E f g h) z θ)
    (g := fun z => 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (add3A f g) z θ)
      + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ))
    (Eventually.of_forall fun z => integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α k (add3E f g h) z θ)
    ((hmA.2.const_mul 2).add (hmh.2.const_mul 2))
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hinner z hz)
  have hsqE : Work.Spaces.HkSq α k (add3E f g h)
      ≤ 2 * Work.Spaces.HkSq α k (add3A f g) + 2 * Work.Spaces.HkSq α k h := by
    rw [Work.Spaces.HkSq, Work.Spaces.HkSq, Work.Spaces.HkSq]
    refine houter.trans_eq ?_
    rw [MeasureTheory.integral_add (hmA.2.const_mul 2) (hmh.2.const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  exact ⟨hmE, le_trans hsqE (by
    nlinarith [hsqA, Work.Spaces.HkSq_nonneg α k f, Work.Spaces.HkSq_nonneg α k g,
      Work.Spaces.HkSq_nonneg α k h])⟩

end Work.FTS.StrongPersist.L3Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.N4ssPriced =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

set_option linter.unusedVariables false

/-- **Priced row 23**: the `ℋ⁴`-honesty and the `α³`-bound of the profile-only star piece
`N₄^{**} = -(1/2) sin(2θ) · FK(F_*) · ∂_θF_*`, with a *constant* independent of all data.

This piece does not involve `g`, `Φs` or `Φg` at all: it is the explicit function
`-(2α²/c(α)) · (sin(2θ) · ∂_θΓ(θ)) · (z²/(1+z)⁴)`, an angular `×` radial product.  The
corresponding row of the open vocabulary is `Work.FTS.Nonlinear.Open.Row23`, whose statement
carries the interfaces `N4Norm'`, `N4Extra'`, `GalClass α g`, `StarPkgo α Cs Φs`, `EllPkgGo α Ce g Φg`
and the three hypotheses `0 < α`, `α ≤ 1`, `α ≤ α₂` — but its proof uses *only* `0 < α` and
`α ≤ 1` (the remaining hypotheses are never touched: the body works with the explicit
factorisation `N4ss α = fun z θ => a θ * r z`, the angular `D_θ`-iterates of
`sin²θ`-type profiles and `Work.Spaces.hKer`; the constants are `Csh`, `Cr` of the
`AngRadHkMem`/`hkerSq_radial_alt` machinery and are independent of every hypothesis).  So the
proof is a verbatim copy of that proof with the interface hypotheses dropped. -/
theorem N4ssPriced : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N4ss α) ∧
    Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N4ss α) ≤ C * α ^ 3 := by
  obtain ⟨Cg, hCgpos, hCg⟩ := Work.FTS.Nonlinear.Pieces.RNP.dthU_pow_Gam_sharp
  obtain ⟨Cr, hCrpos, hCr⟩ := Work.FTS.Nonlinear.Pieces.RNP.hkerSq_radial_alt
  obtain ⟨M, hMpos, hM⟩ := Work.FTS.Nonlinear.Pieces.RNP.gamWeightInt
  refine ⟨Real.sqrt (27 ^ 2 * 10000 + 4 * (20 * Cg) ^ 2 * M) * Cr + 1, ?_, ?_⟩
  · have h1 : 0 ≤ Real.sqrt (27 ^ 2 * 10000 + 4 * (20 * Cg) ^ 2 * M) := Real.sqrt_nonneg _
    nlinarith [hCrpos]
  · intro α hαIoc
    have hα : 0 < α := hαIoc.1
    have hα1 : α ≤ 1 := hαIoc.2
    -- the weight `c(α)` of the fundamental solution is bounded below by `1/10`
    have hcge : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
    have hcpos : 0 < Work.Spaces.c α := by linarith
    -- the angular profile, the radial profile, and their angular majorant
    set a : ℝ → ℝ := fun θ => (-(2 * α ^ 2 / Work.Spaces.c α))
      * Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ with ha
    set r : ℝ → ℝ := fun z => (Work.Spaces.hKer z) ^ 2 with hr
    set G : ℝ → ℝ := fun θ => Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) with hG
    -- ### 1. the factorisation `N₄^{**} = a(θ)·r(z)`
    have hid : Work.FTS.Nonlin.N4ss α = fun z θ => a θ * r z := by
      funext z θ
      rw [Work.FTS.Nonlin.N4ss]
      have hpth : Work.Spaces.pth (Work.Construction.Fstar α) z θ
          = (α * Work.FM.Fstar z / Work.Spaces.c α)
            * deriv (fun t => Work.Spaces.Gam α t) θ := by
        rw [Work.Spaces.pth]
        rw [show (fun θ' => Work.Construction.Fstar α z θ')
            = fun θ' => (α * Work.FM.Fstar z / Work.Spaces.c α)
                * Work.Spaces.Gam α θ' from by
          funext θ'; rw [Work.Construction.Fstar]; ring]
        rw [Work.Spaces.deriv_const_mul']
      rw [Work.FTS.Nonlin.FK_Fstar hα hα1, hpth]
      simp only [ha, hr, Work.Spaces.dthU_apply, Work.Spaces.hKer_apply, Work.FM.Fstar,
        Work.Construction.s2]
      ring_nf
    -- ### 2. the bounds on the two profiles
    have hc2 : 2 * α ^ 2 / Work.Spaces.c α ≤ 20 * α ^ 2 := by
      rw [div_le_iff₀ hcpos]
      nlinarith [hcge, sq_nonneg α, hα]
    have hGnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ G θ := by
      intro θ hθ
      have h1 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
      have h2 : 0 ≤ Real.sin (2 * θ) :=
        Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
      rw [hG]
      positivity
    have ha0 : ∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ 27 * α ^ 3 := by
      intro θ hθ
      have hΓ0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
      have hΓ1 : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
      have hdth := Work.FTS.Nonlinear.Pieces.RNP.dthIter_one_Gam_le hα hα1 θ hθ
      have hrepr : Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ
          = Work.Spaces.DthIter 1 (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ := by
        rw [Work.FTS.LocData.DthIter_rad_eq 1 (fun t => Work.Spaces.Gam α t) 0 θ,
          Function.iterate_one]
      have hb : |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
          ≤ (4 / 3) * α * Work.Spaces.Gam α θ := by rw [hrepr]; exact hdth
      have hc2' : (0 : ℝ) ≤ 2 * α ^ 2 / Work.Spaces.c α :=
        div_nonneg (by positivity) hcpos.le
      have habs : |a θ| = (2 * α ^ 2 / Work.Spaces.c α)
          * |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ| := by
        simp only [ha]
        rw [abs_mul, abs_neg, abs_of_nonneg hc2']
      rw [habs]
      calc (2 * α ^ 2 / Work.Spaces.c α)
              * |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
          ≤ (2 * α ^ 2 / Work.Spaces.c α) * ((4 / 3) * α * Work.Spaces.Gam α θ) :=
            mul_le_mul_of_nonneg_left hb hc2'
        _ ≤ (20 * α ^ 2) * ((4 / 3) * α * Work.Spaces.Gam α θ) :=
            mul_le_mul_of_nonneg_right hc2 (by positivity)
        _ ≤ 27 * α ^ 3 := by
          have hα3 : (0 : ℝ) ≤ α ^ 3 := by positivity
          have h := mul_le_mul_of_nonneg_left hΓ1
            (by positivity : (0 : ℝ) ≤ (80 / 3) * α ^ 3)
          nlinarith [h, hα3]
    have ha1 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ (20 * Cg * α ^ 3) * G θ := by
      intro i hi hi4 θ hθ
      have hrepr : Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ
          = (-(2 * α ^ 2 / Work.Spaces.c α))
            * Work.Spaces.dthU^[i + 1] (fun t => Work.Spaces.Gam α t) θ := by
        rw [Work.FTS.LocData.DthIter_rad_eq i a 0 θ]
        simp only [ha]
        rw [Work.Spaces.dthU_iter_const_mul, Work.Spaces.dthU_iter_comp]
      have hchild := hCg α hα hα1 θ hθ (i + 1) (by omega) (by omega)
      have hc2' : (0 : ℝ) ≤ 2 * α ^ 2 / Work.Spaces.c α :=
        div_nonneg (by positivity) hcpos.le
      have hΓ0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
      have hsin0 : 0 ≤ Real.sin (2 * θ) :=
        Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
      have hGunfold : G θ = Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) := by rw [hG]
      rw [hrepr, abs_mul, abs_neg, abs_of_nonneg hc2', hGunfold]
      have h1 : (2 * α ^ 2 / Work.Spaces.c α)
            * |Work.Spaces.dthU^[i + 1] (fun t => Work.Spaces.Gam α t) θ|
          ≤ (2 * α ^ 2 / Work.Spaces.c α)
            * (Cg * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) :=
        mul_le_mul_of_nonneg_left hchild hc2'
      have h2 : (2 * α ^ 2 / Work.Spaces.c α)
            * (Cg * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)))
          ≤ (20 * Cg * α ^ 3) * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) := by
        rw [show (2 * α ^ 2 / Work.Spaces.c α)
              * (Cg * α * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)))
            = ((2 * α ^ 2 / Work.Spaces.c α) * Cg * α)
              * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) from by ring]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        calc (2 * α ^ 2 / Work.Spaces.c α) * Cg * α
            = (2 * α ^ 2 / Work.Spaces.c α) * (Cg * α) := by ring
          _ ≤ (20 * α ^ 2) * (Cg * α) :=
              mul_le_mul_of_nonneg_right hc2 (by positivity)
          _ = 20 * Cg * α ^ 3 := by ring
      exact h1.trans h2
    -- ### 3. the `θ`-mass of the angular profile
    obtain ⟨hI1raw, hm1raw⟩ := hM α hα hα1
    have hGae : (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
        = fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2 * (α + Real.sin (2 * θ)) ^ 2
            * Work.FTS.Nonlinear.RadialProd.smG α θ := by
      funext θ; rw [hG]; ring
    have hI1 : MeasureTheory.IntegrableOn
        (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
        Work.Spaces.Iθ := by rw [hGae]; exact hI1raw
    have hm1 : ∫ θ in Work.Spaces.Iθ, G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ
        ≤ M := by rw [hGae]; exact hm1raw
    -- ### 4. the radial function
    obtain ⟨hrmemR, hXnR⟩ := hCr α hα hα1
    have hrmem : Work.Spaces.HkMem α 4 (fun z θ => r z) := by rw [hr]; exact hrmemR
    have hXnR' : Work.FTS.Nonlin.Xn α (fun z θ => r z) ≤ Cr := by rw [hr]; exact hXnR
    -- ### 5. the smoothness of the two factors (for the `ℋ⁴`-honesty)
    have ha_sm : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ) := by
      simp only [ha]
      exact contDiffOn_const.mul (Work.FTS.Nonlinear.Open.row23_smoothOpen_dthU_Gam α)
    have hr_sm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => r z) := by
      simp only [hr]
      exact Work.FTS.Nonlinear.Open.row23_smoothOpen_radial
        (fun n => (Work.FTS.Nonlinear.Open.row23_contDiffOn_hKer n).pow 2)
    have hHk : Work.Spaces.HkMem α 4 (fun z θ => a θ * r z) :=
      Work.FTS.Nonlinear.Open.AngRadHkMem (α := α) (a := a) (r := r) (G := G)
        (B0 := 27 * α ^ 3) (B1 := 20 * Cg * α ^ 3) ha_sm hr_sm hGnn hI1 ha0 ha1 hrmem
    -- ### 6. the separated `ℋ⁴`-estimate
    have hmain := Work.FTS.Nonlinear.Pieces.RNP.Xn_ang_rad_le_gen α hα a r G
      (B0 := 27 * α ^ 3) (B1 := 20 * Cg * α ^ 3) (M1 := M) (by positivity) (by positivity)
      (le_of_lt hMpos) hGnn ha0 ha1 hI1 hm1 hrmem
    -- ### 7. the arithmetic
    have hsqrt : Real.sqrt ((27 * α ^ 3) ^ 2 * 10000 + 4 * (20 * Cg * α ^ 3) ^ 2 * M)
        = α ^ 3 * Real.sqrt (27 ^ 2 * 10000 + 4 * (20 * Cg) ^ 2 * M) := by
      rw [show (27 * α ^ 3) ^ 2 * 10000 + 4 * (20 * Cg * α ^ 3) ^ 2 * M
          = (α ^ 3) ^ 2 * (27 ^ 2 * 10000 + 4 * (20 * Cg) ^ 2 * M) from by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    constructor
    · rw [hid]; exact hHk
    · rw [hid]
      calc Work.FTS.Nonlin.Xn α (fun z θ => a θ * r z)
          ≤ Real.sqrt ((27 * α ^ 3) ^ 2 * 10000 + 4 * (20 * Cg * α ^ 3) ^ 2 * M)
              * Work.FTS.Nonlin.Xn α (fun z θ => r z) := hmain
        _ ≤ Real.sqrt ((27 * α ^ 3) ^ 2 * 10000 + 4 * (20 * Cg * α ^ 3) ^ 2 * M) * Cr :=
            mul_le_mul_of_nonneg_left hXnR' (Real.sqrt_nonneg _)
        _ = α ^ 3 * (Real.sqrt (27 ^ 2 * 10000 + 4 * (20 * Cg) ^ 2 * M) * Cr) := by
            rw [hsqrt]; ring
        _ ≤ (Real.sqrt (27 ^ 2 * 10000 + 4 * (20 * Cg) ^ 2 * M) * Cr + 1) * α ^ 3 := by
            nlinarith [sq_nonneg α, le_of_lt hα]

end Work.FTS.StrongPersist.L3Rhs
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.HardPair.mixedTerm_le_six =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.HardPair



end Work.FTS.StrongPersist.N6Trans.HardPair
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.L6FBound.mixed_le_WlInf6_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.L6FBound



end Work.FTS.StrongPersist.N6Trans.L6FBound
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.coefFamSix =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

/-! ## The weight algebra of the `γ`-slot

A leaf weight `ρ` of the slot with `a ≥ 1` angular derivatives is dominated by the canonical
weight `canonW γ = w² sin(2θ)^{-γ}` (`IsLeafW.le_canonW` and `qOf α a = γ` for `a ≠ 0`), and
the `sin(2θ)`-gain of `CoefTh 3 f` (`H2.OpenPort.coefTh3_mixed_gain`) converts one factor
`sin(2θ)` into the shift `γ ↦ γ - 1 = α/10` of the exponent.  The next lemma is that shift. -/


/-- The open interval `(0,π/2)` is co-null in `Iθ`: `volume.restrict (0,π/2) = volume.restrict Iθ`. -/
theorem restrict_Ioo_eq_restrict_Iθ :
    MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
  MeasureTheory.Measure.restrict_congr_set
    (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)

/-- The open half-line `(0,∞)` is co-null in `Iz`: `volume.restrict (0,∞) = volume.restrict Iz`. -/
theorem restrict_Ioi_eq_restrict_Iz :
    MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
      = MeasureTheory.volume.restrict Work.Spaces.Iz :=
  MeasureTheory.Measure.restrict_congr_set
    (by rw [Work.Spaces.Iz]; exact MeasureTheory.Ioi_ae_eq_Ici)


end Work.FTS.StrongPersist.N6Trans.SixRoute
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.PkgJets.Pieces.qang_deriv_classC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets.Pieces

/-- **The `z`-derivative of the angular moment of a class-`C` datum.**

`Qang g m z = ∫_θ K(θ)·D_z^m g(z,θ) dθ` is differentiable at every `z > 0`, with

  `∂_z (Qang g m) z = Qang g (m+1) z / z`,

as soon as `g` is `C^∞` on the open quadrant and honestly weighted-`ℋ^{m+1}`.
The identity is the `z = z` case of the primitive identity
`Qang g j z - Qang g j z₀ = ∫_{z₀}^{z} Qang g (j+1) x / x dx`
of `Work.FTS.OpenPkg.QangOpen.Qang_primitive_open`; the derivative then follows from the
continuity of the integrand `x ↦ Qang g (j+1) x / x` at `z > 0`.

Here we read it off the assembled module `Work.FTS.StrongPersist.QangDiff6`, which supplies the
identity in the exact open-quadrant class at the level `ℋ⁶` (it runs the level-`ℋ⁴` chain twice,
once for `g` and once for the `D_z²`-shift of `g`, by `Qang g (k+2) = Qang (D_z²g) k`).
The class `ClassC` carries `SmoothOpen g` and `HkMem α 7 g`, so `HkMem α 6 g` (and a fortiori
the level `ℋ^{m+1}` needed for `m ≤ 3`) is the monotonicity step
`Work.FTS.OpenPkg.HkMem_mono_open`. -/
theorem qang_deriv_classC {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.ClassC.ClassC α g) {m : ℕ} (hm : m ≤ 3) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun x => Work.Elliptic.Qang g m x) (Work.Elliptic.Qang g (m + 1) z / z) z := by
  -- the class supplies open-quadrant smoothness and `ℋ⁷`-honesty; descend to the level `ℋ⁶`
  -- at which the assembled moment calculus `QangDiff6` is stated
  have hmem6 : Work.Spaces.HkMem α 6 g :=
    Work.FTS.OpenPkg.HkMem_mono_open (k := 7) hg.reg 6 (by norm_num) hg.mem
  exact (Work.FTS.StrongPersist.QangDiff6 hg.reg hmem6).1 m (by omega) z hz

end Work.FTS_EllLimOK.PkgJets.Pieces
end
-- ===== merged: Submission.Work.FTS_LocDatum3a.contDiffOn_Fstar_Jeps_sep =====
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
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace FJS

/-! ## Elementary facts about the angular interval `Iθ` -/

theorem measurableSet_Iθ : MeasurableSet Work.Spaces.Iθ := by
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl]
  exact measurableSet_Icc

theorem isCompact_Iθ : IsCompact Work.Spaces.Iθ := by
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl]
  exact isCompact_Icc

theorem mem_Iθ_zero : (0 : ℝ) ∈ Work.Spaces.Iθ :=
  show (0 : ℝ) ∈ Set.Icc (0 : ℝ) (π / 2) from ⟨le_refl 0, by linarith [Real.pi_pos]⟩

theorem isFiniteMeasure_restrict_Iθ : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) :=
  ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
      exact lt_top_iff_ne_top.mpr isCompact_Iθ.measure_ne_top⟩

/-- `volume.restrict Iθ` may be replaced by `volume.restrict (0,π/2)`: the two endpoints form a
null set. -/
theorem volume_restrict_Iθ :
    volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl]
  exact (Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm

/-- Almost-everywhere statements w.r.t. `volume.restrict Iθ` may be checked on the open
interval `(0,π/2)`. -/
theorem eventually_restrict_Iθ {p : ℝ → Prop} (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), p θ) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), p θ := by
  rw [volume_restrict_Iθ]
  exact (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun θ hθ => h θ hθ)

/-- Almost-everywhere statements w.r.t. `volume.restrict Iθ` may be checked on all of `Iθ`. -/
theorem eventually_restrict_Iθ_of_Iθ {p : ℝ → Prop}
    (h : ∀ θ ∈ Work.Spaces.Iθ, p θ) : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), p θ := by
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl] at h ⊢
  exact (ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall fun θ hθ => h θ hθ)

/-! ## The angular weights `sin θ cos²θ` and `Γ(θ)` -/

theorem continuousOn_sinCos2 : ContinuousOn Work.Elliptic.sinCos2 Work.Spaces.Iθ :=
  (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn

theorem abs_sinCos2_le_one : ∀ θ ∈ Work.Spaces.Iθ, |Work.Elliptic.sinCos2 θ| ≤ 1 := by
  intro θ hθ
  have hθ' : θ ∈ Set.Icc (0 : ℝ) (π / 2) := hθ
  have hs : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ'.1 (by linarith [hθ'.2, Real.pi_pos])
  have hc : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
  have hle : Real.sin θ * Real.cos θ ^ 2 ≤ 1 := by
    calc Real.sin θ * Real.cos θ ^ 2 ≤ 1 * 1 :=
          mul_le_mul (Real.sin_le_one θ) hc (sq_nonneg _) zero_le_one
      _ = 1 := by ring
  rw [Work.Elliptic.sinCos2, abs_of_nonneg (mul_nonneg hs (sq_nonneg _))]
  exact hle

/-- `|Γ(θ)| ≤ 1` on `Iθ` for `0 < α`. -/
theorem abs_Gam_le_one {α : ℝ} (hα : 0 < α) :
    ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.Gam α θ| ≤ 1 := by
  intro θ hθ
  have hθ' : θ ∈ Set.Icc (0 : ℝ) (π / 2) := hθ
  have hs : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ'.1 (by linarith [hθ'.2, Real.pi_pos])
  have hc : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
  have h0 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := mul_nonneg hs (sq_nonneg _)
  have hle : Real.sin θ * Real.cos θ ^ 2 ≤ 1 := by
    calc Real.sin θ * Real.cos θ ^ 2 ≤ 1 * 1 :=
          mul_le_mul (Real.sin_le_one θ) hc (sq_nonneg _) zero_le_one
      _ = 1 := by ring
  rw [Work.Spaces.Gam, abs_of_nonneg (Real.rpow_nonneg h0 _)]
  calc (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) ≤ 1 ^ (α / 3) :=
        Real.rpow_le_rpow h0 hle (by linarith)
    _ = 1 := Real.one_rpow _

/-! ## The generic parametric-integral lemma -/

/-- `F` pulled back to the log coordinate `s = log z`. -/
def logPullZ (F : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun s θ => F (Real.exp s) θ

/-- `D_z^k F` pulled back to the log coordinate `s = log z`. -/
def logPullDz (F : ℝ → ℝ → ℝ) (k : ℕ) : ℝ → ℝ → ℝ :=
  fun s θ => Work.Spaces.DzIter k F (Real.exp s) θ

/-- **Smoothness of a parametric integral in the log variable.**

Let `Φ k` be the `k`-th `s`-derivative of `Φ 0` on `ℝ × (0,π/2)` (in the sense that the slices
have the stated derivatives), with every `Φ k` `C^∞` on `ℝ × (0,π/2)` and uniformly bounded on
`[s₀-1,s₀+1] × Iθ` for every `s₀`.  Then `s ↦ ∫_θ Φ 0 s θ · φ θ dθ` is `C^∞` on `ℝ`.

The proof is the textbook induction: the parametric integral of `Φ k` is `C^n`, its derivative is
the parametric integral of `Φ (k+1)` (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, with the
constant bound on the slab `[s₀-1,s₀+1]`), and the base case is dominated convergence
(`tendsto_integral_filter_of_norm_le_const`); a.e. statements are checked on the open interval
`(0,π/2)`, which is enough because both endpoints are null. -/
theorem contDiffOn_integral_Iθ_univ {Φ : ℕ → ℝ → ℝ → ℝ} {φ : ℝ → ℝ}
    (hsmooth : ∀ (k n : ℕ), ContDiffOn ℝ n (Function.uncurry (Φ k))
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) (π / 2)))
    (hderiv : ∀ (k : ℕ) (s θ : ℝ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) →
      HasDerivAt (fun s' => Φ k s' θ) (Φ (k + 1) s θ) s)
    (hbdd : ∀ (k : ℕ) (s₀ : ℝ), ∃ C, ∀ s, |s - s₀| ≤ 1 →
      ∀ θ ∈ Work.Spaces.Iθ, |Φ k s θ| ≤ C)
    (hφ : ContinuousOn φ Work.Spaces.Iθ) (hφb : ∀ θ ∈ Work.Spaces.Iθ, |φ θ| ≤ 1) :
    ∀ m : ℕ, ContDiffOn ℝ m (fun s => ∫ θ in Work.Spaces.Iθ, Φ 0 s θ * φ θ) Set.univ := by
  -- continuity of the slices in the parameter
  have hslice : ∀ (k : ℕ) {θ : ℝ}, θ ∈ Set.Ioo (0 : ℝ) (π / 2) →
      Continuous (fun s : ℝ => Φ k s θ) := by
    intro k θ hθ
    have hf : ContDiffOn ℝ 0 (fun s : ℝ => (s, θ)) (Set.univ : Set ℝ) :=
      (contDiffOn_zero (𝕜 := ℝ)).mpr (continuous_id.prodMk continuous_const).continuousOn
    have h : ContDiffOn ℝ 0 (fun s : ℝ => Φ k s θ) Set.univ :=
      (hsmooth k 0).comp hf (fun s _ => ⟨Set.mem_univ s, hθ⟩)
    exact continuousOn_univ.mp ((contDiffOn_zero (𝕜 := ℝ)).mp h)
  -- a.e. strong measurability of the slices
  have haesm : ∀ (k : ℕ) (s : ℝ),
      AEStronglyMeasurable (fun θ : ℝ => Φ k s θ * φ θ) (volume.restrict Work.Spaces.Iθ) := by
    intro k s
    have hc1 : ContinuousOn (fun θ : ℝ => Φ k s θ) (Set.Ioo (0 : ℝ) (π / 2)) := by
      have hf : ContDiffOn ℝ 0 (fun θ : ℝ => (s, θ)) (Set.Ioo (0 : ℝ) (π / 2)) :=
        (contDiffOn_zero (𝕜 := ℝ)).mpr (continuous_const.prodMk continuous_id).continuousOn
      have h := (hsmooth k 0).comp hf (fun θ hθ => ⟨Set.mem_univ s, hθ⟩)
      exact (contDiffOn_zero (𝕜 := ℝ)).mp (by
        show ContDiffOn ℝ 0 (fun θ : ℝ => Φ k s θ) (Set.Ioo (0 : ℝ) (π / 2)); exact h)
    have hc2 : ContinuousOn φ (Set.Ioo (0 : ℝ) (π / 2)) :=
      hφ.mono fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have h1 : AEStronglyMeasurable (fun θ : ℝ => Φ k s θ * φ θ)
        (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) :=
      (hc1.mul hc2).aestronglyMeasurable measurableSet_Ioo
    rwa [volume_restrict_Iθ]
  -- the base case: continuity of every integral
  have hcont : ∀ k : ℕ, Continuous (fun s => ∫ θ in Work.Spaces.Iθ, Φ k s θ * φ θ) := by
    intro k
    rw [continuous_iff_continuousAt]
    intro s₀
    obtain ⟨C, hC⟩ := hbdd k s₀
    have hCnn : 0 ≤ C := le_trans (abs_nonneg _) (hC s₀ (by simp) 0 mem_Iθ_zero)
    refine tendsto_integral_filter_of_norm_le_const
      (F := fun s θ => Φ k s θ * φ θ) (f := fun θ => Φ k s₀ θ * φ θ) (l := 𝓝 s₀) ?_ ?_ ?_
    · exact Eventually.of_forall fun s => haesm k s
    · refine ⟨C, ?_⟩
      filter_upwards [isOpen_Ioo.mem_nhds (show s₀ ∈ Set.Ioo (s₀ - 1) (s₀ + 1) from
        ⟨by linarith, by linarith⟩)] with s hs
      refine eventually_restrict_Iθ_of_Iθ fun θ hθ => ?_
      have hs1 : |s - s₀| ≤ 1 := by
        rw [abs_le]; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
      rw [Real.norm_eq_abs, abs_mul]
      exact le_trans (mul_le_mul (hC s hs1 θ hθ) (hφb θ hθ) (abs_nonneg _) hCnn)
        (le_of_eq (mul_one C))
    · refine eventually_restrict_Iθ fun θ hθ => ?_
      exact ((hslice k hθ).continuousAt.mul continuousAt_const).tendsto
  -- differentiation under the integral sign
  have hkey : ∀ (k : ℕ) (s₀ : ℝ),
      HasDerivAt (fun s => ∫ θ in Work.Spaces.Iθ, Φ k s θ * φ θ)
        (∫ θ in Work.Spaces.Iθ, Φ (k + 1) s₀ θ * φ θ) s₀ := by
    intro k s₀
    obtain ⟨C, hC⟩ := hbdd (k + 1) s₀
    obtain ⟨C₀, hC₀⟩ := hbdd k s₀
    have hCnn : 0 ≤ C := le_trans (abs_nonneg _) (hC s₀ (by simp) 0 mem_Iθ_zero)
    have hC₀nn : 0 ≤ C₀ := le_trans (abs_nonneg _) (hC₀ s₀ (by simp) 0 mem_Iθ_zero)
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict Work.Spaces.Iθ) (𝕜 := ℝ)
      (bound := fun _ : ℝ => C)
      (F := fun s θ => Φ k s θ * φ θ) (F' := fun s θ => Φ (k + 1) s θ * φ θ)
      (x₀ := s₀) (s := Set.Ioo (s₀ - 1) (s₀ + 1))
      (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩) ?_ ?_ ?_ ?_ ?_ ?_).2
    · exact Eventually.of_forall fun s => haesm k s
    · refine MeasureTheory.Integrable.of_bound (haesm k s₀) C₀ ?_
      refine eventually_restrict_Iθ_of_Iθ fun θ hθ => ?_
      have h1 : |Φ k s₀ θ| ≤ C₀ := hC₀ s₀ (by simp) θ hθ
      rw [Real.norm_eq_abs, abs_mul]
      exact le_trans (mul_le_mul h1 (hφb θ hθ) (abs_nonneg _) hC₀nn) (le_of_eq (mul_one C₀))
    · exact haesm (k + 1) s₀
    · refine eventually_restrict_Iθ_of_Iθ fun θ hθ => ?_
      intro s hs
      have hs1 : |s - s₀| ≤ 1 := by
        rw [abs_le]; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
      show ‖Φ (k + 1) s θ * φ θ‖ ≤ C
      rw [Real.norm_eq_abs, abs_mul]
      exact le_trans (mul_le_mul (hC s hs1 θ hθ) (hφb θ hθ) (abs_nonneg _) hCnn)
        (le_of_eq (mul_one C))
    · exact integrable_const C
    · refine eventually_restrict_Iθ fun θ hθ => ?_
      intro s _
      exact (hderiv k s θ hθ).mul_const (φ θ)
  -- the induction on the order
  have hmain : ∀ (m : ℕ) (k : ℕ),
      ContDiffOn ℝ m (fun s => ∫ θ in Work.Spaces.Iθ, Φ k s θ * φ θ) Set.univ := by
    intro m
    induction m with
    | zero =>
      intro k
      exact (contDiffOn_zero (𝕜 := ℝ)).mpr (hcont k).continuousOn
    | succ m ih =>
      intro k
      rw [Nat.cast_add, Nat.cast_one]
      refine (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ)
        (f := fun s => ∫ θ in Work.Spaces.Iθ, Φ k s θ * φ θ)
        (n := ((m : ℕ) : WithTop ℕ∞)) (s := Set.univ) isOpen_univ).2 ⟨?_, ?_, ?_⟩
      · exact fun s _ => (hkey k s).differentiableAt.differentiableWithinAt
      · intro h; exact absurd h (by simp)
      · refine (ih (k + 1)).congr fun s _ => ?_
        exact (hkey k s).deriv
  intro m
  simpa using hmain m 0

/-! ## From `C^∞` on the quadrant plus `D_z`-bounds to `F_*`-smoothness -/

/-- **`F_*` is `C^∞` on `(0,∞)`** for a datum `F` which is `C^∞` on the open quadrant and whose
`D_z`-iterates, pulled back to the log coordinate, are locally bounded on `Iθ`. -/
theorem contDiffOn_Fstar_of_dzBound {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hb : ∀ (k : ℕ) (s₀ : ℝ), ∃ C, ∀ s, |s - s₀| ≤ 1 →
      ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.DzIter k F (Real.exp s) θ| ≤ C) :
    ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar F) (Set.Ioi 0) := by
  have hsmooth : ∀ (k n : ℕ), ContDiffOn ℝ n (Function.uncurry (logPullDz F k))
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
    intro k n
    have h1 : ContDiffOn ℝ n (Function.uncurry (Work.Spaces.DzIter k F))
        Work.FTS.EllipticEst.Q0 := (hF.DzIter k).forall n
    have h2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => (Real.exp p.1, p.2))
        (Set.univ ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
      ContDiffOn.prodMk
        ((((Real.contDiff_exp.comp contDiff_fst).contDiffOn).of_le le_top).mono
          (Set.subset_univ _))
        contDiffOn_snd
    have h3 := h1.comp h2 (fun p hp => ⟨Real.exp_pos _, hp.2⟩)
    show ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Spaces.DzIter k F (Real.exp p.1) p.2)
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) (π / 2))
    exact h3
  have hderiv : ∀ (k : ℕ) (s θ : ℝ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) →
      HasDerivAt (fun s' => logPullDz F k s' θ) (logPullDz F (k + 1) s θ) s := by
    intro k s θ hθ
    have h1 : HasDerivAt (fun z' => Work.Spaces.DzIter k F z' θ)
        (Work.Spaces.pz (Work.Spaces.DzIter k F) (Real.exp s) θ) (Real.exp s) :=
      hF.hasDerivAt_slice_DzIter k hθ (Real.exp_pos s)
    have h2 : HasDerivAt Real.exp (Real.exp s) s := Real.hasDerivAt_exp s
    have h3 := h1.comp s h2
    have h4 : Work.Spaces.pz (Work.Spaces.DzIter k F) (Real.exp s) θ * Real.exp s
        = Work.Spaces.DzIter (k + 1) F (Real.exp s) θ := by
      rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz]
      ring
    rw [h4] at h3
    show HasDerivAt (fun s' : ℝ => Work.Spaces.DzIter k F (Real.exp s') θ)
      (Work.Spaces.DzIter (k + 1) F (Real.exp s) θ) s
    exact h3
  have hmain := contDiffOn_integral_Iθ_univ (Φ := logPullDz F) (φ := Work.Elliptic.sinCos2)
    hsmooth hderiv hb continuousOn_sinCos2 abs_sinCos2_le_one
  intro m
  have h1 : ContDiff ℝ m
      (fun s => ∫ θ in Work.Spaces.Iθ, logPullZ F s θ * Work.Elliptic.sinCos2 θ) :=
    contDiffOn_univ.mp (hmain m)
  have h2 : ContDiffOn ℝ m
      ((fun s => ∫ θ in Work.Spaces.Iθ, logPullZ F s θ * Work.Elliptic.sinCos2 θ) ∘ Real.log)
      (Set.Ioi 0) :=
    h1.comp_contDiffOn ((Real.contDiffOn_log (n := m)).mono fun x hx => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt hx)
  refine h2.congr fun z hz => ?_
  have hz' : Real.exp (Real.log z) = z := Real.exp_log hz
  simp only [Function.comp_def, logPullZ, hz', Work.Elliptic.Fstar]

/-! ## The separable datum `a(z)·Γ(θ)` -/

/-- The separable datum `(z,θ) ↦ a z · Γ(θ)`. -/
abbrev sepDatum (a : ℝ → ℝ) (α : ℝ) : ℝ → ℝ → ℝ := fun z θ => a z * Work.Spaces.Gam α θ

theorem smoothOpen_sepDatum {α : ℝ} {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ Work.Stability.smoothOrder a (Set.Ioi 0)) :
    Work.FTS.EllipticEst.SmoothOpen (sepDatum a α) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall fun n => ?_
  have ha_n : ContDiffOn ℝ n a (Set.Ioi 0) := contDiffOn_iff_forall_nat_le.mp ha n le_top
  have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => a p.1) Work.FTS.EllipticEst.Q0 := by
    have h := ha_n.comp (contDiffOn_fst (𝕜 := ℝ) (s := Work.FTS.EllipticEst.Q0))
      (fun p hp => hp.1)
    show ContDiffOn ℝ n (fun p : ℝ × ℝ => a p.1) Work.FTS.EllipticEst.Q0
    exact h
  have h2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2)
      Work.FTS.EllipticEst.Q0 := by
    have hbase : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin p.2 * Real.cos p.2 ^ 2)
        Work.FTS.EllipticEst.Q0 :=
      ((((Real.contDiff_sin.comp contDiff_snd).mul
        ((Real.contDiff_cos.comp contDiff_snd).pow 2)).contDiffOn).of_le le_top).mono
        (Set.subset_univ _)
    have hne : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.sin p.2 * Real.cos p.2 ^ 2 ≠ 0 := by
      intro p hp
      obtain ⟨-, h1', h2'⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      have hs : 0 < Real.sin p.2 := Real.sin_pos_of_pos_of_lt_pi
        (by linarith [h1', Real.pi_pos]) (by linarith [h2', Real.pi_pos])
      have hc : 0 < Real.cos p.2 := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [h1', Real.pi_pos], h2'⟩
      positivity
    simpa only [Work.Spaces.Gam] using hbase.rpow_const_of_ne hne
  have h3 := h1.mul h2
  show ContDiffOn ℝ n (fun p : ℝ × ℝ => a p.1 * Work.Spaces.Gam α p.2)
    Work.FTS.EllipticEst.Q0
  exact h3

theorem exp_mul_exp_neg (x ε : ℝ) : Real.exp x * Real.exp (-ε) = Real.exp (x - ε) := by
  rw [← Real.exp_add, sub_eq_add_neg]

theorem exp_mul_exp_pos (x ε : ℝ) : Real.exp x * Real.exp ε = Real.exp (x + ε) := by
  rw [← Real.exp_add]

/-! ## Local uniform bounds for the `D_z`-iterates -/

/-- `D_z^k` of a separable datum `a(z)Γ(θ)` only differs in the radial factor. -/
theorem DzIter_sepDatum (α : ℝ) (a : ℝ → ℝ) (k : ℕ) :
    Work.Spaces.DzIter k (sepDatum a α)
      = fun z θ => Work.Spaces.DzIter k (fun z _ => a z) z θ * Work.Spaces.Gam α θ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
    funext z θ
    simp only [Work.Spaces.Dz, Work.Spaces.pz, deriv_mul_const_field']
    ring

/-- The one-variable iterate `(z d/dz)^k a`. -/
def dzA (a : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => a
  | k + 1 => fun z => z * deriv (dzA a k) z

@[simp] theorem dzA_zero (a : ℝ → ℝ) : dzA a 0 = a := rfl

@[simp] theorem dzA_succ (a : ℝ → ℝ) (k : ℕ) :
    dzA a (k + 1) = fun z => z * deriv (dzA a k) z := rfl

/-- `D_z^k` of a radial datum is the one-variable iterate `(z d/dz)^k`. -/
theorem DzIter_radial_eq (a : ℝ → ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter k (fun z _ => a z) z θ = dzA a k z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz, dzA_succ]
    have hfun : (fun z' => Work.Spaces.DzIter k (fun z _ => a z) z' θ) = dzA a k :=
      funext fun z' => ih z'
    rw [hfun]

/-- `(z d/dz)^k a` is `C^n` on `(0,∞)` for every `n`, when `a` is `C^∞` there. -/
theorem contDiffOn_dzA {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ Work.Stability.smoothOrder a (Set.Ioi 0)) :
    ∀ (k n : ℕ), ContDiffOn ℝ n (dzA a k) (Set.Ioi 0) := by
  intro k
  induction k with
  | zero =>
    intro n
    simpa only [dzA_zero] using contDiffOn_iff_forall_nat_le.mp ha n le_top
  | succ k ih =>
    intro n
    have h1 : ContDiffOn ℝ (((n : ℕ) : WithTop ℕ∞) + 1) (dzA a k) (Set.Ioi 0) := by
      simpa only [Nat.cast_add, Nat.cast_one] using ih (n + 1)
    have h2 : ContDiffOn ℝ n (deriv (dzA a k)) (Set.Ioi 0) :=
      ((contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (s := Set.Ioi (0 : ℝ))
        isOpen_Ioi).mp h1).2.2
    have h3 : ContDiffOn ℝ n (fun z => z * deriv (dzA a k) z) (Set.Ioi 0) :=
      (contDiffOn_id (𝕜 := ℝ) (s := Set.Ioi (0 : ℝ))).mul h2
    simpa only [dzA_succ] using h3

/-- **The `D_z`-iterates of the separable datum are locally uniformly bounded on `Iθ`.** -/
theorem radial_mul_Gam_DzIter_bound {α : ℝ} (hα : 0 < α) {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ Work.Stability.smoothOrder a (Set.Ioi 0)) (k : ℕ) {z₁ z₂ : ℝ}
    (hz₁ : 0 < z₁) :
    ∃ C, ∀ z, z₁ ≤ z → z ≤ z₂ → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DzIter k (fun z θ => a z * Work.Spaces.Gam α θ) z θ| ≤ C := by
  have hcont : ContinuousOn (dzA a k) (Set.Icc z₁ z₂) :=
    ((contDiffOn_dzA ha k 0).mono
      (fun z hz => lt_of_lt_of_le hz₁ hz.1)).continuousOn
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨|C|, fun z hz1 hz2 θ hθ => ?_⟩
  simp only [DzIter_sepDatum, DzIter_radial_eq, abs_mul]
  have h1 : |dzA a k z| ≤ |C| := by
    have h := hC z ⟨hz1, hz2⟩
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_abs_self C)
  calc |dzA a k z| * |Work.Spaces.Gam α θ| ≤ |C| * 1 :=
        mul_le_mul h1 (abs_Gam_le_one hα θ hθ) (abs_nonneg _) (abs_nonneg _)
    _ = |C| := mul_one _

/-- A function vanishing on a whole `z`-line has vanishing `D_z`-iterates on that line. -/
theorem DzIter_eq_zero_of_slice_zero {g : ℝ → ℝ → ℝ} {θ : ℝ} (h : ∀ z, g z θ = 0) :
    ∀ (k : ℕ) (z : ℝ), Work.Spaces.DzIter k g z θ = 0 := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih =>
    intro z
    rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
    have hfun : (fun z' => Work.Spaces.DzIter k g z' θ) = fun _ => 0 := funext ih
    rw [hfun, deriv_const, mul_zero]

/-- **`J_ε` preserves local uniform bounds on the `D_z`-iterates.**

If `|D_z^k f| ≤ M` on the slightly enlarged rectangle `[a e^{-ε}, b e^{ε}] × [0, π/2]`, then
`|D_z^k (J_ε f)| ≤ max M 0` on `[a, b] × [0, π/2]`.

On the open quadrant this is the commutation `D_z^k ∘ J_ε = J_ε ∘ D_z^k`
(`DzIter_Jeps_of_smooth`) followed by the elementary domination of the convolution by the
supremum over the shift region (`abs_Jeps_le_sup`): a shift `p` with `|p₁| ≤ ε` sends `z ∈ [a,b]`
into `zShift z p₁ = z e^{-p₁} ∈ [a e^{-ε}, b e^{ε}]`, and the angular shift `thShift θ p₂` stays
in the open quadrant.  On the boundary `θ = 0, π/2` both sides vanish identically in `z`. -/
theorem DzIter_Jeps_bound {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ) {ε : ℝ}
    (hε : 0 < ε) {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (k : ℕ) {a b M : ℝ}
    (ha : 0 < a)
    (hM : ∀ z, a * Real.exp (-ε) ≤ z → z ≤ b * Real.exp ε → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DzIter k f z θ| ≤ M) :
    ∃ C, ∀ z, a ≤ z → z ≤ b → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DzIter k (Work.FTS.StrongEps.Jeps ρ ε f) z θ| ≤ C := by
  refine ⟨max M 0, fun z hza hzb θ hθ => ?_⟩
  have hzpos : 0 < z := lt_of_lt_of_le ha hza
  by_cases hθo : θ ∈ Set.Ioo (0 : ℝ) (π / 2)
  · have hcomm : Work.Spaces.DzIter k (Work.FTS.StrongEps.Jeps ρ ε f) z θ
        = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.DzIter k f) z θ :=
      Work.FTS.StrongEps.DzIter_Jeps_of_smooth ρ hρ hε hf k
        (show (z, θ) ∈ Work.FTS.StrongEps.Quad from ⟨hzpos, hθo⟩)
    rw [hcomm]
    refine Work.FTS.StrongEps.abs_Jeps_le_sup ρ hρ hε hzpos hθo (fun p hp1 hp2 => ?_)
      (le_max_right _ _)
    obtain ⟨hp1, hp1'⟩ := abs_le.mp hp1
    have hbpos : 0 < b := lt_of_lt_of_le hzpos hzb
    have hzlo : a * Real.exp (-ε) ≤ Work.FTS.StrongEps.zShift z p.1 := by
      rw [Work.FTS.StrongEps.zShift]
      exact mul_le_mul hza (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
        (le_of_lt hzpos)
    have hzhi : Work.FTS.StrongEps.zShift z p.1 ≤ b * Real.exp ε := by
      rw [Work.FTS.StrongEps.zShift]
      exact mul_le_mul hzb (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
        (le_of_lt hbpos)
    have hθin : Work.FTS.StrongEps.thShift θ p.2 ∈ Work.Spaces.Iθ :=
      let h := Work.FTS.StrongEps.thShift_mem hθo
      ⟨le_of_lt h.1, le_of_lt h.2⟩
    exact le_trans (hM _ hzlo hzhi _ hθin) (le_max_left _ _)
  · have hzline : ∀ z' : ℝ, Work.FTS.StrongEps.Jeps ρ ε f z' θ = 0 :=
      fun z' => Work.FTS.StrongEps.Jeps_eq_zero_of_theta ρ ε f (fun hc => hθo hc)
    rw [DzIter_eq_zero_of_slice_zero hzline k z, abs_zero]
    exact le_max_right _ _

end FJS

open FJS

theorem contDiffOn_Fstar_Jeps_sep {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) {α : ℝ} (hα : 0 < α)
    {a : ℝ → ℝ} (ha : ContDiffOn ℝ Work.Stability.smoothOrder a (Set.Ioi 0)) :
    ∀ m : ℕ, ContDiffOn ℝ m
      (Work.Elliptic.Fstar (Work.FTS.StrongEps.Jeps ρ ε (fun z θ => a z * Work.Spaces.Gam α θ)))
      (Set.Ioi 0) := by
  have hmoll : Work.FTS.StrongEps.IsMollKernel ρ := hρ.moll
  have hf : Work.FTS.EllipticEst.SmoothOpen (sepDatum a α) := smoothOpen_sepDatum ha
  have hF : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε (sepDatum a α)) :=
    Work.FTS.EllipticEst.smoothOpen_of_forall fun n =>
      Work.FTS.StrongEps.SmoothOpen_Jeps ρ hmoll hε
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall (sepDatum a α)).mp hf) n
  refine contDiffOn_Fstar_of_dzBound (F := Work.FTS.StrongEps.Jeps ρ ε (sepDatum a α)) hF ?_
  intro k s₀
  obtain ⟨M, hM⟩ := radial_mul_Gam_DzIter_bound (α := α) hα ha k
    (z₁ := Real.exp (s₀ - 1 - ε)) (z₂ := Real.exp (s₀ + 1 + ε)) (Real.exp_pos _)
  have hMex : ∀ z, Real.exp (s₀ - 1) * Real.exp (-ε) ≤ z →
      z ≤ Real.exp (s₀ + 1) * Real.exp ε →
      ∀ θ ∈ Work.Spaces.Iθ, |Work.Spaces.DzIter k (sepDatum a α) z θ| ≤ M := by
    intro z hz1 hz2 θ hθ
    refine hM z ?_ ?_ θ hθ
    · rw [exp_mul_exp_neg] at hz1; exact hz1
    · rw [exp_mul_exp_pos] at hz2; exact hz2
  obtain ⟨C, hC⟩ := DzIter_Jeps_bound (f := sepDatum a α) hmoll hε hf k
    (a := Real.exp (s₀ - 1)) (b := Real.exp (s₀ + 1)) (Real.exp_pos _) hMex
  exact ⟨C, fun s hs θ hθ => hC (Real.exp s)
    (Real.exp_le_exp_of_le (by linarith [(abs_le.mp hs).1]))
    (Real.exp_le_exp_of_le (by linarith [(abs_le.mp hs).2])) θ hθ⟩

end Work.FTS_LocDatum3a
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXA1.integrableOn_pth_mixed_sq_sin_C4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXA1

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Elementary facts about the exponent, the weights and the `θ`-slices -/

/-- The exponent `γ = gam α = 1 + α/10` is positive for `α > 0`. -/
private lemma gam_pos_C4 {α : ℝ} (hα : 0 < α) : 0 < Work.Spaces.gam α := by
  rw [Work.Spaces.gam]; linarith

/-- For `α ≤ 1` one has `γ = gam α ≤ 11/10`, in particular `γ ≠ 2`. -/
private lemma gam_le_eleven_tenths {α : ℝ} (hα1 : α ≤ 1) :
    Work.Spaces.gam α ≤ 11 / 10 := by
  rw [Work.Spaces.gam]; linarith

/-- `sin(2θ) ≥ 0` on the angular interval `Iθ = [0,π/2]`. -/
private lemma sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

/-- The radial weight satisfies `1 ≤ (w z)²` for `z > 0`. -/
private lemma one_le_w_sq_C4 {z : ℝ} (hz : 0 < z) : 1 ≤ (Work.Spaces.w z) ^ 2 := by
  have h1 : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, one_le_div (by positivity : (0 : ℝ) < z ^ 2)]
    nlinarith [hz]
  nlinarith [h1]

/-- The weight algebra `(Wt α z θ)² = (w z)² · sin(2θ)^{-γ}` on the closed angular interval. -/
private lemma Wt_sq_Iθ {α z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  have h1 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hs]
    ring_nf
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, h1]

/-- The weight algebra underlying the angular Hardy inequality:
`(∂_θ u)² sin(2θ)^{2-γ} = (D_θ u)² sin(2θ)^{-γ}` on `Iθ`. -/
private lemma pth_sq_mul_sin_eq_C4 {α : ℝ} (hα1 : α ≤ 1) (u : ℝ → ℝ → ℝ)
    (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.pth u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      = (Work.Spaces.Dth u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  have hne : 2 + (-(Work.Spaces.gam α)) ≠ 0 := by
    have hg1 := gam_le_eleven_tenths hα1
    intro h
    linarith
  have hD : Work.Spaces.Dth u z θ = Real.sin (2 * θ) * Work.Spaces.pth u z θ := rfl
  rw [hD, mul_pow, show 2 - Work.Spaces.gam α = 2 + (-(Work.Spaces.gam α)) by ring,
    Real.rpow_add' hs hne]
  simp only [mul_assoc, mul_left_comm, mul_comm, Real.rpow_two]

/-! ## The target -/

theorem integrableOn_pth_mixed_sq_sin_C4 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) (b a : ℕ) (hab : a + b ≤ 2) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun σ => (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
  have hγne : Work.Spaces.gam α ≠ 0 := ne_of_gt (gam_pos_C4 hα)
  have hab4 : a + 1 + b ≤ 4 := by omega
  -- The angular slice of `HkIntegrand` at the fixed radial variable `z` is integrable: this is
  -- the second component of `HkMem α 4 f`.
  have hHk : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 4 f z θ)
      Work.Spaces.Iθ := hmem.1 z (show z ∈ Work.Spaces.Iz from hz.le)
  -- Continuity of the slot `(D_z^bD_θ^{a+1}f)² sin(2θ)^{-γ}` on the open quadrant.
  have hsinposQ : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hpθ⟩ := hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hpθ.1])
      (by linarith [hpθ.2, Real.pi_pos])
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.mixed b (a + 1) f p.1 p.2) ^ 2
      * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))) Work.FTS.EllipticEst.Q0 :=
    ((Work.FTS.StrongEps.continuousOn_mixed_of_contDiffOn hF hab4).pow 2).mul
      (ContinuousOn.rpow_const
        ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn)
        (fun p hp => Or.inl (ne_of_gt (hsinposQ p hp))))
  -- The slot `(D_z^bD_θ^{a+1}f)² sin(2θ)^{-γ}` is integrable on `Iθ`.
  have hint : MeasureTheory.IntegrableOn (fun σ => (Work.Spaces.mixed b (a + 1) f z σ) ^ 2
      * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' hHk
      (Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun σ hσ => ?_
    have hs : 0 ≤ Real.sin (2 * σ) := sin_two_nonneg_Iθ hσ
    have hnn : 0 ≤ (Work.Spaces.mixed b (a + 1) f z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)
    rw [Real.norm_of_nonneg hnn]
    -- the slot is dominated by the corresponding summand of `HkIntegrand α 4 f`
    have hslot := Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z σ (a + 1) b (by omega) (by omega)
    rw [mul_pow, Wt_sq_Iθ hσ] at hslot
    have hw : 1 ≤ (Work.Spaces.w z) ^ 2 := one_le_w_sq_C4 hz
    calc (Work.Spaces.mixed b (a + 1) f z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        ≤ (Work.Spaces.mixed b (a + 1) f z σ) ^ 2
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))) :=
          mul_le_mul_of_nonneg_left
            (le_mul_of_one_le_left (Real.rpow_nonneg hs _) hw) (sq_nonneg _)
      _ ≤ Work.Spaces.HkIntegrand α 4 f z σ := hslot
  -- Transfer to the `pth`-form of the integrand, pointwise on `Iθ`.
  refine hint.congr_fun (fun σ hσ => ?_) measurableSet_Icc
  show (Work.Spaces.mixed b (a + 1) f z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
      = (Work.Spaces.pth (Work.Spaces.mixed b a f) z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
  rw [pth_sq_mul_sin_eq_C4 hα1 (Work.Spaces.mixed b a f) z σ hσ]
  -- `D_θ (D_z^bD_θ^af) = D_z^bD_θ^{a+1}f` on the open interval; at the two endpoints both
  -- sides vanish because `sin(2σ)^{-γ} = 0` there.
  rcases eq_or_lt_of_le hσ.1 with h0 | h0
  · have hs0 : Real.sin (2 * σ) = 0 := by rw [← h0]; simp
    have hz0 : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) = 0 := by
      rw [hs0]
      exact Real.zero_rpow (neg_ne_zero.mpr hγne)
    rw [hz0, mul_zero, mul_zero]
  · rcases eq_or_lt_of_le hσ.2 with hπ | hπ
    · have hs0 : Real.sin (2 * σ) = 0 := by
        rw [hπ, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      have hz0 : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) = 0 := by
        rw [hs0]
        exact Real.zero_rpow (neg_ne_zero.mpr hγne)
      rw [hz0, mul_zero, mul_zero]
    · rw [Work.FTS_RegExport.C4.Dth_mixed_eq_C4 hF b a (by omega) hz ⟨h0, hπ⟩]

end Work.FTS_RegExport.RXA1
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXA1.mixed_T_le_HkSq_C4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXA1

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Elementary pointwise identities

The energy of a mixed slot is the angular partial integral of the corresponding `ℋ⁴`-summand:
on `Iθ` the angular weight `w_θ = sin(2θ)^{-γ/2}` squares to `sin(2θ)^{-γ}`, so

`(D_z^bD_θ^a f · Wt)² = sin(2θ)^{-γ} · ((D_z^bD_θ^a f)² · w²)`.

This is the identity `mixed_Wt_sq_eq_fts` of the smooth (`SmoothOpen`) development, re-proved
here for a bare curried function so that the `C⁴` statement does not have to import the
`StrongEps/SupPort` cone. -/





end Work.FTS_RegExport.RXA1
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.velVanish2Star =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `ℛ`-slot of the star residual (part of `velVanish2`)

`|D_z^jD_θ^i (Rop α (PhiTs α Φs))| ≤ 2·10⁴·(max Cs 1·α)·min z 1` for `j + i ≤ 2` on the open
quadrant, from the `𝒲^{4,∞}`-field `RW` of `StarPkgo2` via the *proved*
`Work.FTS.NonlinRows.Rop_pointwiseW_aux` and the Stirling expansion of `D_z`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

theorem v2_zdiv_one_add_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ z / (1 + z) := by
  have h : 0 < 1 + z := by linarith
  exact div_nonneg hz h.le

theorem v2_zdiv_one_add_le_min {z : ℝ} (hz : 0 < z) : z / (1 + z) ≤ min z 1 := by
  have h1 : 0 < 1 + z := by linarith
  rcases le_total z 1 with h | h
  · rw [min_eq_left h, div_le_iff₀ h1]
    nlinarith
  · rw [min_eq_right h, div_le_one h1]
    linarith

/-- `σ(θ)·Λ(θ) = 1`, the de-weighting identity of the angular factors of `WlInf`. -/
theorem v2_sig_mul_lam {α θ : ℝ} (hs : 0 < Real.sin (2 * θ)) (ht : 0 < α + Real.sin (2 * θ)) :
    ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) = 1 := by
  have h1 : (Real.sin (2 * θ)) ^ (-(α / 5)) * (Real.sin (2 * θ)) ^ (α / 5) = 1 := by
    rw [← Real.rpow_add hs, show -(α / 5) + α / 5 = 0 by ring, Real.rpow_zero]
  calc ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
      = (((Real.sin (2 * θ)) ^ (-(α / 5)) * (Real.sin (2 * θ)) ^ (α / 5))
          * (α + Real.sin (2 * θ))) / (α + Real.sin (2 * θ)) := by ring
    _ = 1 := by
        rw [h1, one_mul]
        exact div_self (ne_of_gt ht)

/-! ## The `Rop`-slot of the star residual -/

/-- The four pointwise bounds for `ℛ(Φ̃_*)` produced by `Rop_pointwiseW_aux`, converted into the
form consumed below: for `i + j ≤ 2`, every `z^k ∂_z^k D_θ^i ℛ(Φ̃_*)` is bounded by
`200·(max Cs 1 · α)·z/(1+z)` on the open quadrant. -/
theorem v2_starRop_aux {α Cs : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hS : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    (∀ k ≤ 4, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |z ^ k * Work.Spaces.pzIter k
          (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
        ≤ 200 * (max Cs 1 * α) * (z / (1 + z))) ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ 2 → ∀ k : ℕ, i + k ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 →
      |z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter i
          (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs))) z θ|
        ≤ 200 * (max Cs 1 * α) * (z / (1 + z))) := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen Φs := hS.smooth
  obtain ⟨h1, h2, h3, h4⟩ := Work.FTS.NonlinRows.Rop_pointwiseW_aux hα hα1
    (Work.FTS.NonlinRows.RopW_smoothOpen_local hα hα1 hsm) hS.RW.1 hS.RW.2
  have hK0 : (0 : ℝ) ≤ max Cs 1 * α :=
    mul_nonneg (le_trans zero_le_one (le_max_right Cs 1)) hα.le
  have hh100 : (0 : ℝ) ≤ 100 * (max Cs 1 * α) := by positivity
  have hA : ∀ k ≤ 4, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |z ^ k * Work.Spaces.pzIter k (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ| ≤ 200 * (max Cs 1 * α) * (z / (1 + z)) := by
    intro k hk z θ hz hθ hθ2
    have hzk : (0 : ℝ) ≤ z ^ k := by positivity
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      simp only [pow_zero, one_mul, Work.Spaces.pzIter_zero]
      have h := h1 z hz θ ⟨hθ, hθ2⟩
      have he : 100 * (max Cs 1 * α) * z / (1 + z)
          = 100 * (max Cs 1 * α) * (z / (1 + z)) := by ring
      rw [he] at h
      have h0 : 0 ≤ z / (1 + z) := v2_zdiv_one_add_nonneg hz.le
      have h' : 100 * (max Cs 1 * α) * (z / (1 + z))
          ≤ 200 * (max Cs 1 * α) * (z / (1 + z)) := by
        have hk : 0 ≤ (max Cs 1 * α) * (z / (1 + z)) := mul_nonneg hK0 h0
        linarith
      exact le_trans h h'
    · have h := h2 k (by omega) z hz θ ⟨hθ, hθ2⟩
      have hpow : z ^ k * (100 * (max Cs 1 * α) / (1 + z) ^ k)
          = 100 * (max Cs 1 * α) * (z / (1 + z)) ^ k := by
        rw [div_pow]; field_simp
      have hr0 : 0 ≤ z / (1 + z) := v2_zdiv_one_add_nonneg hz.le
      have hr1 : z / (1 + z) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      have hle : (z / (1 + z)) ^ k ≤ z / (1 + z) := pow_le_of_le_one hr0 hr1 (by omega : k ≠ 0)
      calc |z ^ k * Work.Spaces.pzIter k (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ| = z ^ k * |Work.Spaces.pzIter k (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ| := by
            rw [abs_mul, abs_of_nonneg hzk]
        _ ≤ z ^ k * (100 * (max Cs 1 * α) / (1 + z) ^ k) :=
            mul_le_mul_of_nonneg_left h hzk
        _ = 100 * (max Cs 1 * α) * (z / (1 + z)) ^ k := hpow
        _ ≤ 100 * (max Cs 1 * α) * (z / (1 + z)) :=
            mul_le_mul_of_nonneg_left hle hh100
        _ = 100 * ((max Cs 1 * α) * (z / (1 + z))) := by ring
        _ ≤ 200 * ((max Cs 1 * α) * (z / (1 + z))) := by
            have hk : 0 ≤ (max Cs 1 * α) * (z / (1 + z)) :=
              mul_nonneg hK0 (v2_zdiv_one_add_nonneg hz.le)
            linarith
        _ = 200 * (max Cs 1 * α) * (z / (1 + z)) := by ring
  refine ⟨hA, ?_⟩
  intro i hi hi2 k hik z θ hz hθ hθ2
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have ht : 0 < α + Real.sin (2 * θ) := by linarith
  have hΛ : (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) ≤ 2 :=
    Work.FTS.Nonlinear.Pieces.RNP.row19.lam_le_two hα hα1
      (Set.mem_Icc.mpr ⟨hθ.le, hθ2.le⟩)
  have hL0 : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    le_of_lt (mul_pos ht (Real.rpow_pos_of_pos hs _))
  have hzk : (0 : ℝ) ≤ z ^ k := by positivity
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    simp only [pow_zero, one_mul, Work.Spaces.pzIter_zero]
    have h := h4 i hi (by omega) z hz θ ⟨hθ, hθ2⟩
    have he : 100 * (max Cs 1 * α) * z / (1 + z)
        = 100 * (max Cs 1 * α) * (z / (1 + z)) := by ring
    rw [he] at h
    rw [show |Work.Spaces.DthIter i (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
          = (|Work.Spaces.DthIter i (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))))
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
        from by rw [mul_assoc, v2_sig_mul_lam hs ht, mul_one]]
    calc (|Work.Spaces.DthIter i (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))))
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
        ≤ (100 * (max Cs 1 * α) * (z / (1 + z)))
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
          mul_le_mul_of_nonneg_right h hL0
      _ ≤ (100 * (max Cs 1 * α) * (z / (1 + z))) * 2 :=
          mul_le_mul_of_nonneg_left hΛ (by positivity)
      _ = 200 * (max Cs 1 * α) * (z / (1 + z)) := by ring
  · have h := h3 i k hi (by omega) z hz θ ⟨hθ, hθ2⟩
    have hpow : z ^ k * (100 * (max Cs 1 * α) / (1 + z) ^ k)
        = 100 * (max Cs 1 * α) * (z / (1 + z)) ^ k := by
      rw [div_pow]; field_simp
    have hr0 : 0 ≤ z / (1 + z) := v2_zdiv_one_add_nonneg hz.le
    have hr1 : z / (1 + z) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have hle : (z / (1 + z)) ^ k ≤ z / (1 + z) := pow_le_of_le_one hr0 hr1 (by omega : k ≠ 0)
    have hkey : z ^ k * |Work.Spaces.pzIter k (Work.Spaces.DthIter i (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs))) z θ|
        = (z ^ k * |Work.Spaces.pzIter k (Work.Spaces.DthIter i (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs))) z θ|)
          * (((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
      rw [v2_sig_mul_lam hs ht, mul_one]
    rw [abs_mul, abs_of_nonneg hzk, hkey]
    calc (z ^ k * |Work.Spaces.pzIter k (Work.Spaces.DthIter i (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs))) z θ|)
          * (((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
        = (z ^ k * (|Work.Spaces.pzIter k (Work.Spaces.DthIter i (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs))) z θ|
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))))
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by ring
      _ ≤ (z ^ k * (100 * (max Cs 1 * α) / (1 + z) ^ k))
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hzk) hL0
      _ = (100 * (max Cs 1 * α) * (z / (1 + z)) ^ k)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by rw [hpow]
      _ ≤ (100 * (max Cs 1 * α) * (z / (1 + z)))
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hh100) hL0
      _ ≤ (100 * (max Cs 1 * α) * (z / (1 + z))) * 2 :=
          mul_le_mul_of_nonneg_left hΛ (mul_nonneg hh100 hr0)
      _ = 200 * (max Cs 1 * α) * (z / (1 + z)) := by ring

/-- **The star half for the `ℛ`-slot**: every mixed derivative of order `≤ 2` of `ℛ(Φ̃_*)` is
bounded by `2·10⁴·(max Cs 1·α)·min z 1` on the open quadrant. -/
theorem v2_starRop_mixed {α Cs : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hS : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i
          (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
        ≤ 2 * 10 ^ 4 * (max Cs 1 * α) * min z 1 := by
  obtain ⟨hA, hB⟩ := v2_starRop_aux hα hα1 hS
  have hsm : Work.FTS.EllipticEst.SmoothOpen Φs := hS.smooth
  have hΘ : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Theta α (Work.Construction.Fstar α)) :=
    Work.FTS.NonlinRows.RopW_ThetaFstar hα hα1
  have hPhi : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) :=
    Work.FTS.NonlinRows.RopW_sub hsm hΘ
  have hRsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) :=
    Work.FTS.NonlinRows.RopW_Rop (α := α) hPhi
  have hM0 : (0 : ℝ) ≤ 200 * (max Cs 1 * α) := by positivity
  have hK0 : (0 : ℝ) ≤ max Cs 1 * α :=
    mul_nonneg (le_trans zero_le_one (le_max_right Cs 1)) hα.le
  intro j i hji z θ hz hθ hθ2
  have hzmin : z / (1 + z) ≤ min z 1 := v2_zdiv_one_add_le_min hz
  have hmm : (0 : ℝ) ≤ min z 1 := le_min hz.le zero_le_one
  have hle : 200 * (max Cs 1 * α) * (z / (1 + z))
      ≤ 200 * (max Cs 1 * α) * min z 1 := mul_le_mul_of_nonneg_left hzmin hM0
  have hfin : 200 * (max Cs 1 * α) * min z 1 ≤ 2 * 10 ^ 4 * (max Cs 1 * α) * min z 1 := by
    have hk : 0 ≤ (max Cs 1 * α) * min z 1 := mul_nonneg hK0 hmm
    linarith
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    rw [Work.Spaces.mixed_zero_left]
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      have h := hA 0 (by norm_num) z θ hz hθ hθ2
      simp only [pow_zero, one_mul, Work.Spaces.pzIter_zero, Work.Spaces.DthIter_zero] at h
      exact le_trans (le_trans h hle) hfin
    · have h := hB i hipos (by omega) 0 (by omega) z θ hz hθ hθ2
      simp only [pow_zero, one_mul, Work.Spaces.pzIter_zero] at h
      exact le_trans (le_trans h hle) hfin
  · rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      rw [Work.Spaces.mixed_zero_right]
      have hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder (fun z' => (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z' θ) (Set.Ioi 0) :=
        hRsm.curry_z ⟨hθ, hθ2⟩
      rw [Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open (h := (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs))) (θ := θ) hsmooth j z
        (Set.mem_Ioi.mpr hz)]
      refine le_trans (Work.Spaces.abs_sum_scoef_mul_le j
        (200 * (max Cs 1 * α) * min z 1) (fun k => z ^ k * Work.Spaces.pzIter k (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ) ?_) ?_
      · intro k hk
        exact le_trans (hA k (by omega) z θ hz hθ hθ2) hle
      · have hbell : (Work.Spaces.bell j : ℝ) ≤ 100 := by
          exact_mod_cast Work.Spaces.bell_le j (by omega)
        have h0 : 0 ≤ 200 * (max Cs 1 * α) * min z 1 := mul_nonneg hM0 hmm
        calc (Work.Spaces.bell j : ℝ) * (200 * (max Cs 1 * α) * min z 1)
            ≤ 100 * (200 * (max Cs 1 * α) * min z 1) :=
              mul_le_mul_of_nonneg_right hbell h0
          _ = 2 * 10 ^ 4 * (max Cs 1 * α) * min z 1 := by ring
    · rw [Work.Spaces.mixed]
      have hZsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DthIter i (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs))) := hRsm.DthIter i
      have hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder
          (fun z' => Work.Spaces.DthIter i (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z' θ) (Set.Ioi 0) :=
        hZsm.curry_z ⟨hθ, hθ2⟩
      rw [Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open (h := Work.Spaces.DthIter i (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs))) (θ := θ)
        hsmooth j z (Set.mem_Ioi.mpr hz)]
      refine le_trans (Work.Spaces.abs_sum_scoef_mul_le j
        (200 * (max Cs 1 * α) * min z 1)
        (fun k => z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter i (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs))) z θ) ?_) ?_
      · intro k hk
        exact le_trans (hB i hipos (by omega) k (by omega) z θ hz hθ hθ2) hle
      · have hbell : (Work.Spaces.bell j : ℝ) ≤ 100 := by
          exact_mod_cast Work.Spaces.bell_le j (by omega)
        have h0 : 0 ≤ 200 * (max Cs 1 * α) * min z 1 := mul_nonneg hM0 hmm
        calc (Work.Spaces.bell j : ℝ) * (200 * (max Cs 1 * α) * min z 1)
            ≤ 100 * (200 * (max Cs 1 * α) * min z 1) :=
              mul_le_mul_of_nonneg_right hbell h0
          _ = 2 * 10 ^ 4 * (max Cs 1 * α) * min z 1 := by ring


end Work.FTS_RegExport.RXT
end
end
