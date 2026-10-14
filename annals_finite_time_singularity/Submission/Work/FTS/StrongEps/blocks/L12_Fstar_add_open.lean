import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Have
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.EllipticEst.H2W.Ae.TruncIdentAe
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.TT.Shim.DzPsiAux
import Submission.Work.FTS.EllipticEst.TT.psiDerivSq_lower
import Submission.Work.FTS.EllipticEst.ThetaSliceIdent
import Submission.Work.FTS.EllipticEst.Tools.aesm_Fpair_fts
import Submission.Work.FTS.EllipticEst.ZCuts.zHardy_compact
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.H2.ModalSol.Defs
import Submission.Work.FTS.H2.ModalSolR.PerModeBasic
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.LocDataExt.Defs
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongPersist.N6.Swap6
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_EllLimOK.Pinning.integrableOn_sq_rpow_of_HkMem
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.RPFresh.slice_sq_le
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.SolutionDelivery.Scaling.Main
import Submission.Work.Spaces.BadTermSqBound
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.aesm_HkIntegrand_quad
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.StabilityFar.Decay.hasDerivAt_bsK
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.Blocks.poincare_Half =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks

open Work.FTS.EllipticEst Work.FTS.EllipticEst.Blocks

set_option autoImplicit false

/-
**The weighted angular Poincaré estimate in the half-strip smoothness class `SmoothHalf`.**

Namespace `Work.FTS.EllipticEst.Blocks`.

This is the **port** of the *already proved* estimate
`Work.FTS.EllipticEst.Blocks.theta_Hk_poincare`
(`Submission/Work/FTS/EllipticEst/Blocks/theta_Hk_poincare.lean`, verified `sorry`-free with
`#print axioms`) from the hypothesis `Work.Spaces.SmoothNbhd` to the weaker, *provable*
hypothesis `Work.FTS.EllipticEst.SmoothHalf` (see `Submission/Work/FTS/EllipticEst/HalfSmooth.lean`).

WHY the port is needed.  `SmoothNbhd f` demands `C^∞` on an open *neighbourhood of the closed
quadrant*, in particular on `z < 0`.  For the straightened residual
`Ξ = Work.Elliptic.EllResid α F Ψ = Ψ - (1/(4α))·sin 2θ·L₁₂(F)` that is FALSE, because
`EllHyp.sol` forces `F = bslOp α Ψ` only for `z > 0`; see the counterexample recorded in
`Submission/Work/Blocks/NOTES_EllResid_certs_counterexample.md`.  `SmoothHalf Ξ` *does* hold.

ROUTE.  The two per-`z` comparisons of the angular integrals are
`Work.Blocks.HkIntegrand_integral_le_pth2_half` and `…_pth_half` (ports of
`Blocks.HkIntegrand_integral_le_pth2` and `Blocks.HkIntegrand_integral_le_pth2_pth` to the
half-strip class; they consume the slice estimates `Blocks.slice_f_bound` / `Blocks.slice_d_bound`
and the half-strip layer `Work.FTS.EllipticEst.HalfU` of
`Submission/Work/Blocks/SmoothHalfAux.lean`).  What is left — and what this file does — is exactly
the `z`-integration bookkeeping of `theta_Hk_poincare`: `HkSq` is the iterated integral over
`Iz × Iθ`, the slice comparisons hold at *every* `z ∈ Iz` (at `z = 0` both sides vanish because
`w 0 = 0`), the right-hand integrand is honest by `HkMem α k (∂_θ²f)`, so
`integral_mono_of_nonneg` compares the outer integrals and `Real.sqrt_le_sqrt` plus the
square-root arithmetic finishes.  The only difference from the `SmoothNbhd` version is that the
slice constants are uniformised over the finitely many levels `K ≤ k` (`cf`, `cd` below) exactly
as there.
-/

end Work.Blocks
end
end
-- ===== merged: Submission.Work.EllipticEst.Assembly.bslOp_pairing_self =====
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
set_option maxHeartbeats 1600000
/-! ## The main theorem -/

theorem bslOp_pairing_self {α : ℝ} (hα : 0 < α) {Φ φ : ℝ → ℝ → ℝ}
    (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ)
    (hφ : Work.FTS.EllipticEst.SmoothOpen φ) (hcφ : HasCompactSupport (Function.uncurry φ))
    (hsub : tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0) :
    (∫ p in Work.FTS.EllipticEst.Q0,
        Work.Elliptic.bslOp α Φ p.1 p.2 * φ p.1 p.2
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2))
      = ∫ p in Work.FTS.EllipticEst.Q0,
          Φ p.1 p.2 * Work.Elliptic.bslOp α φ p.1 p.2
            * (p.1 ^ ((5 - α) / α) * Real.cos p.2) := by
  change (∫ p in Work.FTS.EllipticEst.Q0,
      Work.Elliptic.bslOp α Φ p.1 p.2 * φ p.1 p.2 * pairWeight α p)
    = ∫ p in Work.FTS.EllipticEst.Q0,
        Φ p.1 p.2 * Work.Elliptic.bslOp α φ p.1 p.2 * pairWeight α p
  -- ## the support of `φ` and a rectangle around it
  have hK : IsCompact (tsupport (Function.uncurry φ)) := hcφ
  obtain ⟨a, b, hab, ha1, ha2, hb2, hbox⟩ := existsBoxQ0Aux hK hsub
  have hKIcc : tsupport (Function.uncurry φ) ⊆ Set.Icc a b := by
    intro x hx
    rw [Set.Icc_prod_eq]
    exact Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self (hbox hx)
  have hboxQ0 : Set.Icc a b ⊆ Work.FTS.EllipticEst.Q0 := by
    intro x hx
    rw [Set.Icc_prod_eq] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [Work.FTS.EllipticEst.mem_Q0]
    exact ⟨lt_of_lt_of_le ha1 hx1.1, lt_of_lt_of_le ha2 hx2.1, lt_of_le_of_lt hx2.2 hb2⟩
  have hIcc_compact : IsCompact (Set.Icc a b) := by
    rw [Set.Icc_prod_eq]
    exact isCompact_Icc.prod isCompact_Icc
  have hpt : ∀ x ∈ Set.Icc a b, (0 : ℝ) < x.1 ∧ x.2 ∈ Set.Ioo 0 (π / 2) := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := Work.FTS.EllipticEst.mem_Q0.mp (hboxQ0 hx)
    exact ⟨h1, h2, h3⟩
  -- ## the integrands
  set F1 : ℝ × ℝ → ℝ := fun x =>
    Work.Elliptic.bslOp α Φ x.1 x.2 * φ x.1 x.2 * pairWeight α x with hF1
  set F2 : ℝ × ℝ → ℝ := fun x =>
    Φ x.1 x.2 * Work.Elliptic.bslOp α φ x.1 x.2 * pairWeight α x with hF2
  have hWcont : ContinuousOn (pairWeight α) Work.FTS.EllipticEst.Q0 :=
    continuousOn_pairWeight α
  -- ## integrability of the two integrands on the rectangle
  have hF1cont : ContinuousOn F1 (Set.Icc a b) := by
    rw [hF1]
    exact ((continuousOn_bslOp_smoothOpen hΦ).mul hφ.continuousOn).mul
      hWcont |>.mono hboxQ0
  have hF2cont : ContinuousOn F2 (Set.Icc a b) := by
    rw [hF2]
    exact (hΦ.continuousOn.mul (continuousOn_bslOp_smoothOpen hφ)).mul
      hWcont |>.mono hboxQ0
  have hF1int : IntegrableOn F1 (Set.Icc a b) := hF1cont.integrableOn_compact hIcc_compact
  have hF2int : IntegrableOn F2 (Set.Icc a b) := hF2cont.integrableOn_compact hIcc_compact
  -- ## differentiability and continuity of the two halves of the divergence form
  have hRadDiff : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ (pairRad α Φ φ) x := by
    intro x hx
    exact ((contDiffOnPairAux hΦ hφ).1.contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds (hboxQ0 hx))).differentiableAt (by norm_num)
  have hAngDiff : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ (pairAng α Φ φ) x := by
    intro x hx
    exact ((contDiffOnPairAux hΦ hφ).2.contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds (hboxQ0 hx))).differentiableAt (by norm_num)
  have hRadCont : ContinuousOn (pairRad α Φ φ) (Set.Icc a b) :=
    (contDiffOnPairAux hΦ hφ).1.continuousOn.mono hboxQ0
  have hAngCont : ContinuousOn (pairAng α Φ φ) (Set.Icc a b) :=
    (contDiffOnPairAux hΦ hφ).2.continuousOn.mono hboxQ0
  have hDsmooth : ContinuousOn (fderiv ℝ (pairRad α Φ φ)) Work.FTS.EllipticEst.Q0 :=
    (contDiffOnPairAux hΦ hφ).1.continuousOn_fderiv_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0 le_rfl
  have hEsmooth : ContinuousOn (fderiv ℝ (pairAng α Φ φ)) Work.FTS.EllipticEst.Q0 :=
    (contDiffOnPairAux hΦ hφ).2.continuousOn_fderiv_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0 le_rfl
  have hdivInt : IntegrableOn (fun x : ℝ × ℝ =>
      (fderiv ℝ (pairRad α Φ φ) x) (1, 0) + (fderiv ℝ (pairAng α Φ φ) x) (0, 1))
      (Set.Icc a b) :=
    (ContinuousOn.add ((hDsmooth.mono hboxQ0).clm_apply continuousOn_const)
      ((hEsmooth.mono hboxQ0).clm_apply continuousOn_const)).integrableOn_compact hIcc_compact
  -- ## the pointwise identity on the rectangle
  have hdiv_pt : ∀ x ∈ Set.Icc a b, F1 x - F2 x =
      deriv (fun z' => pairRad α Φ φ (z', x.2)) x.1
        + deriv (fun θ' => pairAng α Φ φ (x.1, θ')) x.2 := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hpt x hx
    have h := pairDivIdentityAux hα hx1 hx2
      (hasDerivAt_slice_z hΦ hx1 hx2) (hasDerivAt_slice_pz hΦ hx1 hx2)
      (hasDerivAt_slice_z hφ hx1 hx2) (hasDerivAt_slice_pz hφ hx1 hx2)
      (hasDerivAt_slice_θ hΦ hx1 hx2) (hasDerivAt_slice_pth hΦ hx1 hx2)
      (hasDerivAt_slice_θ hφ hx1 hx2) (hasDerivAt_slice_pth hφ hx1 hx2)
    rw [← h]
    show Work.Elliptic.bslOp α Φ x.1 x.2 * φ x.1 x.2 * pairWeight α x
        - Φ x.1 x.2 * Work.Elliptic.bslOp α φ x.1 x.2 * pairWeight α x
      = pairWeight α (x.1, x.2) * (Work.Elliptic.bslOp α Φ x.1 x.2 * φ x.1 x.2
        - Φ x.1 x.2 * Work.Elliptic.bslOp α φ x.1 x.2)
    simp only [Prod.mk.eta]
    ring
  have hbox_eq1 : (∫ x in Set.Icc a b, (F1 x - F2 x)) =
      ∫ x in Set.Icc a b, ((fderiv ℝ (pairRad α Φ φ) x) (1, 0)
        + (fderiv ℝ (pairAng α Φ φ) x) (0, 1)) := by
    refine setIntegral_congr_fun measurableSet_Icc (fun x hx => ?_)
    rw [hdiv_pt x hx, fderiv_fst_eq_deriv (hRadDiff x hx),
      fderiv_snd_eq_deriv (hAngDiff x hx)]
  -- ## the planar divergence theorem
  have hdiv := MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le
    (pairRad α Φ φ) (pairAng α Φ φ) (fun x => fderiv ℝ (pairRad α Φ φ) x)
    (fun x => fderiv ℝ (pairAng α Φ φ) x) a b hab ∅ countable_empty
    hRadCont hAngCont
    (fun x hx => (hRadDiff x (by
      obtain ⟨hx1, hx2⟩ := Set.mem_prod.mp hx.1
      rw [Set.Icc_prod_eq]
      exact ⟨⟨hx1.1.le, hx1.2.le⟩, ⟨hx2.1.le, hx2.2.le⟩⟩)).hasFDerivAt)
    (fun x hx => (hAngDiff x (by
      obtain ⟨hx1, hx2⟩ := Set.mem_prod.mp hx.1
      rw [Set.Icc_prod_eq]
      exact ⟨⟨hx1.1.le, hx1.2.le⟩, ⟨hx2.1.le, hx2.2.le⟩⟩)).hasFDerivAt)
    hdivInt
  -- ## the four boundary integrals vanish
  have hB_b2 : ∀ x : ℝ, pairAng α Φ φ (x, b.2) = 0 := by
    intro x
    refine pairAng_eq_zero_off_tsupport (fun hmem => ?_)
    exact absurd (hbox hmem).2.2 (lt_irrefl b.2)
  have hB_a2 : ∀ x : ℝ, pairAng α Φ φ (x, a.2) = 0 := by
    intro x
    refine pairAng_eq_zero_off_tsupport (fun hmem => ?_)
    exact absurd (hbox hmem).2.1 (lt_irrefl a.2)
  have hA_b1 : ∀ y : ℝ, pairRad α Φ φ (b.1, y) = 0 := by
    intro y
    refine pairRad_eq_zero_off_tsupport (fun hmem => ?_)
    exact absurd (hbox hmem).1.2 (lt_irrefl b.1)
  have hA_a1 : ∀ y : ℝ, pairRad α Φ φ (a.1, y) = 0 := by
    intro y
    refine pairRad_eq_zero_off_tsupport (fun hmem => ?_)
    exact absurd (hbox hmem).1.1 (lt_irrefl a.1)
  have hbdry : (((∫ x in a.1..b.1, pairAng α Φ φ (x, b.2))
        - ∫ x in a.1..b.1, pairAng α Φ φ (x, a.2))
      + ∫ y in a.2..b.2, pairRad α Φ φ (b.1, y))
      - ∫ y in a.2..b.2, pairRad α Φ φ (a.1, y) = 0 := by
    have h1 : (∫ x in a.1..b.1, pairAng α Φ φ (x, b.2)) = 0 := by
      rw [show (∫ x in a.1..b.1, pairAng α Φ φ (x, b.2))
          = ∫ x in a.1..b.1, (0 : ℝ) from
        intervalIntegral.integral_congr (fun x _ => hB_b2 x),
        intervalIntegral.integral_zero]
    have h2 : (∫ x in a.1..b.1, pairAng α Φ φ (x, a.2)) = 0 := by
      rw [show (∫ x in a.1..b.1, pairAng α Φ φ (x, a.2))
          = ∫ x in a.1..b.1, (0 : ℝ) from
        intervalIntegral.integral_congr (fun x _ => hB_a2 x),
        intervalIntegral.integral_zero]
    have h3 : (∫ y in a.2..b.2, pairRad α Φ φ (b.1, y)) = 0 := by
      rw [show (∫ y in a.2..b.2, pairRad α Φ φ (b.1, y))
          = ∫ y in a.2..b.2, (0 : ℝ) from
        intervalIntegral.integral_congr (fun y _ => hA_b1 y),
        intervalIntegral.integral_zero]
    have h4 : (∫ y in a.2..b.2, pairRad α Φ φ (a.1, y)) = 0 := by
      rw [show (∫ y in a.2..b.2, pairRad α Φ φ (a.1, y))
          = ∫ y in a.2..b.2, (0 : ℝ) from
        intervalIntegral.integral_congr (fun y _ => hA_a1 y),
        intervalIntegral.integral_zero]
    rw [h1, h2, h3, h4]
    ring
  have hzero : (∫ x in Set.Icc a b, (F1 x - F2 x)) = 0 := by
    rw [hbox_eq1, hdiv, hbdry]
  have hIcc_eq : (∫ x in Set.Icc a b, F1 x) = ∫ x in Set.Icc a b, F2 x := by
    have h := hzero
    rw [MeasureTheory.integral_sub hF1int hF2int] at h
    exact sub_eq_zero.mp h
  -- ## reduce both `Q0`-integrals to the rectangle
  have hF1vanish : ∀ x ∈ Work.FTS.EllipticEst.Q0 \ Set.Icc a b, F1 x = 0 := by
    intro x hx
    have hxK : x ∉ tsupport (Function.uncurry φ) := fun h => hx.2 (hKIcc h)
    obtain ⟨h1, -, -⟩ := supportVanishAux (g := φ) hxK
    show Work.Elliptic.bslOp α Φ x.1 x.2 * φ x.1 x.2 * pairWeight α x = 0
    rw [h1]; ring
  have hF2vanish : ∀ x ∈ Work.FTS.EllipticEst.Q0 \ Set.Icc a b, F2 x = 0 := by
    intro x hx
    have hxK : x ∉ tsupport (Function.uncurry φ) := fun h => hx.2 (hKIcc h)
    show Φ x.1 x.2 * Work.Elliptic.bslOp α φ x.1 x.2 * pairWeight α x = 0
    rw [bslOp_eq_zero_off_tsupport hxK]; ring
  have hQ1 : (∫ x in Work.FTS.EllipticEst.Q0, F1 x) = ∫ x in Set.Icc a b, F1 x :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Work.FTS.EllipticEst.isOpen_Q0.measurableSet
      hboxQ0 hF1vanish
  have hQ2 : (∫ x in Work.FTS.EllipticEst.Q0, F2 x) = ∫ x in Set.Icc a b, F2 x :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Work.FTS.EllipticEst.isOpen_Q0.measurableSet
      hboxQ0 hF2vanish
  rw [hQ1, hQ2]
  exact hIcc_eq

end Work.EllipticEst.Assembly
end
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.SliceAgmonAux.SharpHardyOpenAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Core.i0Aux.SliceAgmonAux

open Work.FTS.EllipticEst.Honest (gapDelta gapDelta_pos)
open Work.FTS.EllipticEst.AeStepOneAux (hbA hbA_nonneg hbPrim hbDeriv hbPrim_def)
open Work.FTS.EllipticEst.AeStepOneAux.HardyBdd (primPointwise hbPrim_hasDerivAt)

/-- `gapDelta n = 1/(n+2) ≤ 1/2`. -/
private theorem gD_le_half (n : ℕ) : gapDelta n ≤ 1 / 2 := by
  rw [gapDelta]
  apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- `gapDelta n → 0`. -/
private theorem gD_tendsto : Filter.Tendsto gapDelta Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
  have hfun : (fun n : ℕ => ((n : ℝ) + 2)⁻¹) = gapDelta := by
    funext n
    simp [gapDelta, one_div]
  rw [hfun] at h
  exact h

/-- `gapDelta n < π/2 - gapDelta n`. -/
private theorem gD_lt_gap (n : ℕ) : gapDelta n < Real.pi / 2 - gapDelta n := by
  have h1 := gD_le_half n
  have h2 : (1 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
  linarith

/-- The gap interval sits inside `(0, π/2)`. -/
private theorem gD_subset (n : ℕ) :
    Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
  fun x hx => ⟨lt_trans (gapDelta_pos n) hx.1,
    lt_trans hx.2 (by linarith [gapDelta_pos n])⟩

/-- `gapDelta n → 0⁺`. -/
private theorem tendsto_gD_within : Filter.Tendsto gapDelta Filter.atTop
    (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
  rw [tendsto_nhdsWithin_iff]
  exact ⟨gD_tendsto, Eventually.of_forall (fun n => gapDelta_pos n)⟩

/-- `π/2 - gapDelta n → (π/2)⁻`. -/
private theorem tendsto_sub_gD_within :
    Filter.Tendsto (fun n : ℕ => Real.pi / 2 - gapDelta n) Filter.atTop
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, Eventually.of_forall (fun n => by
    simp only [Set.mem_Iio]; linarith [gapDelta_pos n])⟩
  have h : Filter.Tendsto (fun n : ℕ => Real.pi / 2 - gapDelta n) Filter.atTop
      (nhds (Real.pi / 2 - 0)) := tendsto_const_nhds.sub gD_tendsto
  simpa using h

/-- **The sharp `σ`-weighted Hardy inequality** on the open interval, with the integrability of
the singular weight. -/
theorem sharpHardyOpenAux {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hrate0 : Filter.Tendsto
      (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hrate1 : Filter.Tendsto
      (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hA : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))
        Work.Spaces.Iθ
      ∧ (1 + Work.Spaces.eta) ^ 2
            * (∫ θ in Work.Spaces.Iθ,
                (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))
        ≤ (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
  have h1eta : (0 : ℝ) < 1 + Work.Spaces.eta := by linarith [Work.Spaces.eta_pos]
  have hcoef : (0 : ℝ) < (1 + Work.Spaces.eta) ^ 2 := pow_pos h1eta 2
  have hf1 : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)) := hf.of_le (by norm_num)
  have hT : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hAoo : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := hA.mono_set hT
  -- ## standing facts about the integrand
  have hsinT : ContinuousOn (fun x : ℝ => Real.sin (2 * x)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hg : ContinuousOn
      (fun x : ℝ => (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
      (Set.Ioo 0 (Real.pi / 2)) :=
    (hf.continuousOn.pow 2).mul
      (hsinT.rpow_const (fun x hx => Or.inl (ne_of_gt (sin_two_pos hx))))
  have hnn : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      0 ≤ (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)) :=
    fun x hx => mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (le_of_lt (sin_two_pos hx)) _)
  -- ## the pointwise inequality
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (1 + Work.Spaces.eta) ^ 2 * ((f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))
        ≤ (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ - hbDeriv f θ :=
    fun θ hθ => primPointwise hf1 θ hθ
  -- ## the flux tends to `0` at both endpoints
  have hbp0 : Filter.Tendsto (hbPrim f) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hc : Filter.Tendsto
        (fun θ : ℝ => (2 * hbA) * ((f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      simpa using hrate0.const_mul (2 * hbA)
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    refine squeeze_zero' (Eventually.of_forall (fun θ => norm_nonneg _)) ?_ hc
    filter_upwards [Ioo_mem_nhdsGT hpi2] with θ hθ
    rw [Real.norm_eq_abs]
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) := Real.rpow_nonneg hs.le _
    have h2a : (0 : ℝ) ≤ 2 * hbA := by linarith [hbA_nonneg]
    have hrepr : |hbPrim f θ| = 2 * hbA * |Real.cos (2 * θ)| * (f θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) := by
      rw [hbPrim_def, abs_mul, abs_mul, abs_mul, abs_of_nonneg h2a,
        abs_of_nonneg (sq_nonneg (f θ)), abs_of_nonneg hsnn]
    calc |hbPrim f θ|
        = 2 * hbA * |Real.cos (2 * θ)| * (f θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) := hrepr
      _ ≤ 2 * hbA * 1 * (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)) hsnn
          exact mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (2 * θ)) h2a
      _ = (2 * hbA) * ((f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))) := by ring
  have hbp1 : Filter.Tendsto (hbPrim f) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds 0) := by
    have hc : Filter.Tendsto
        (fun θ : ℝ => (2 * hbA) * ((f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      simpa using hrate1.const_mul (2 * hbA)
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    refine squeeze_zero' (Eventually.of_forall (fun θ => norm_nonneg _)) ?_ hc
    filter_upwards [Ioo_mem_nhdsLT hpi2] with θ hθ
    rw [Real.norm_eq_abs]
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) := Real.rpow_nonneg hs.le _
    have h2a : (0 : ℝ) ≤ 2 * hbA := by linarith [hbA_nonneg]
    have hrepr : |hbPrim f θ| = 2 * hbA * |Real.cos (2 * θ)| * (f θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) := by
      rw [hbPrim_def, abs_mul, abs_mul, abs_mul, abs_of_nonneg h2a,
        abs_of_nonneg (sq_nonneg (f θ)), abs_of_nonneg hsnn]
    calc |hbPrim f θ|
        = 2 * hbA * |Real.cos (2 * θ)| * (f θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) := hrepr
      _ ≤ 2 * hbA * 1 * (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)) hsnn
          exact mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (2 * θ)) h2a
      _ = (2 * hbA) * ((f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))) := by ring
  -- ## the sub-interval estimate
  have hbound : ∀ n : ℕ,
      (1 + Work.Spaces.eta) ^ 2
        * (∫ x in Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n),
            (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
      ≤ (∫ x in Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n),
            (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
        - hbPrim f (Real.pi / 2 - gapDelta n) + hbPrim f (gapDelta n) := by
    intro n
    have hle : gapDelta n ≤ Real.pi / 2 - gapDelta n := le_of_lt (gD_lt_gap n)
    have hmem : ∀ x ∈ Set.Icc (gapDelta n) (Real.pi / 2 - gapDelta n),
        x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
      ⟨lt_of_lt_of_le (gapDelta_pos n) hx.1,
        lt_of_le_of_lt hx.2 (by linarith [gapDelta_pos n])⟩
    have hcontn : ContinuousOn
        (fun x : ℝ => (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
        (Set.Icc (gapDelta n) (Real.pi / 2 - gapDelta n)) :=
      ((hf.continuousOn.mono hmem).pow 2).mul
        ((hsinT.mono hmem).rpow_const
          (fun x hx => Or.inl (ne_of_gt (sin_two_pos (hmem x hx)))))
    have hcontD : ContinuousOn (hbDeriv f)
        (Set.Icc (gapDelta n) (Real.pi / 2 - gapDelta n)) := by
      have hsin : ContinuousOn (fun x : ℝ => Real.sin (2 * x))
          (Set.Icc (gapDelta n) (Real.pi / 2 - gapDelta n)) :=
        (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
      have hcos : ContinuousOn (fun x : ℝ => Real.cos (2 * x))
          (Set.Icc (gapDelta n) (Real.pi / 2 - gapDelta n)) :=
        (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
      have hff : ContinuousOn f (Set.Icc (gapDelta n) (Real.pi / 2 - gapDelta n)) :=
        hf.continuousOn.mono hmem
      have hdd : ContinuousOn (deriv f)
          (Set.Icc (gapDelta n) (Real.pi / 2 - gapDelta n)) :=
        (hf.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono hmem
      have hs1 : ContinuousOn (fun x : ℝ => (Real.sin (2 * x)) ^ (-(1 + Work.Spaces.eta)))
          (Set.Icc (gapDelta n) (Real.pi / 2 - gapDelta n)) :=
        hsin.rpow_const (fun x hx => Or.inl (ne_of_gt (sin_two_pos (hmem x hx))))
      have hs2 : ContinuousOn (fun x : ℝ => (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
          (Set.Icc (gapDelta n) (Real.pi / 2 - gapDelta n)) :=
        hsin.rpow_const (fun x hx => Or.inl (ne_of_gt (sin_two_pos (hmem x hx))))
      have hA1 : ContinuousOn (fun x : ℝ => -4 * hbA * Real.sin (2 * x) * (f x) ^ 2
          * (Real.sin (2 * x)) ^ (-(1 + Work.Spaces.eta)))
          (Set.Icc (gapDelta n) (Real.pi / 2 - gapDelta n)) :=
        (((continuousOn_const.mul hsin).mul (hff.pow 2)).mul hs1)
      have hA2 : ContinuousOn (fun x : ℝ => 4 * hbA * Real.cos (2 * x) * (f x) * deriv f x
          * (Real.sin (2 * x)) ^ (-(1 + Work.Spaces.eta)))
          (Set.Icc (gapDelta n) (Real.pi / 2 - gapDelta n)) :=
        (((continuousOn_const.mul hcos).mul hff).mul hdd).mul hs1
      have hA3pos : ContinuousOn (fun x : ℝ => 4 * hbA * (1 + Work.Spaces.eta)
          * (Real.cos (2 * x)) ^ 2 * (f x) ^ 2
          * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
          (Set.Icc (gapDelta n) (Real.pi / 2 - gapDelta n)) :=
        (((continuousOn_const.mul (hcos.pow 2)).mul (hff.pow 2)).mul hs2)
      have hA3 : ContinuousOn (fun x : ℝ => -(4 * hbA * (1 + Work.Spaces.eta)
          * (Real.cos (2 * x)) ^ 2 * (f x) ^ 2
          * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))))
          (Set.Icc (gapDelta n) (Real.pi / 2 - gapDelta n)) := hA3pos.neg
      exact (hA1.add hA2).add hA3
    have hIg : MeasureTheory.IntegrableOn
        (fun x : ℝ => (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
        (Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n)) :=
      hcontn.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self
    have hIA : MeasureTheory.IntegrableOn
        (fun x : ℝ => (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
        (Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n)) :=
      hAoo.mono_set (gD_subset n)
    have hID : MeasureTheory.IntegrableOn (hbDeriv f)
        (Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n)) :=
      hcontD.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self
    have hmono := MeasureTheory.setIntegral_mono_on
      (hf := hIg.const_mul ((1 + Work.Spaces.eta) ^ 2))
      (hg := hIA.sub hID) measurableSet_Ioo (fun x hx => hpt x (gD_subset n hx))
    have e1 : (∫ x in Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n),
          (1 + Work.Spaces.eta) ^ 2
            * ((f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))))
        = (1 + Work.Spaces.eta) ^ 2
          * (∫ x in Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n),
              (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))) :=
      MeasureTheory.integral_const_mul _ _
    have e2 : (∫ x in Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n),
          ((fun x : ℝ => (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x) - hbDeriv f) x)
        = (∫ x in Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n),
            (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
          - (∫ x in Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n), hbDeriv f x) :=
      MeasureTheory.integral_sub hIA hID
    have e3 : (∫ x in Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n), hbDeriv f x)
        = hbPrim f (Real.pi / 2 - gapDelta n) - hbPrim f (gapDelta n) := by
      have hder : ∀ θ ∈ Set.uIcc (gapDelta n) (Real.pi / 2 - gapDelta n),
          HasDerivAt (hbPrim f) (hbDeriv f θ) θ := by
        intro θ hθ
        rw [Set.uIcc_of_le hle, Set.mem_Icc] at hθ
        exact hbPrim_hasDerivAt hf1 θ (hmem θ hθ)
      have hint : IntervalIntegrable (hbDeriv f) MeasureTheory.volume
          (gapDelta n) (Real.pi / 2 - gapDelta n) :=
        hcontD.intervalIntegrable_of_Icc hle
      have h1 : (∫ x in (gapDelta n)..(Real.pi / 2 - gapDelta n), hbDeriv f x)
          = hbPrim f (Real.pi / 2 - gapDelta n) - hbPrim f (gapDelta n) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint
      rw [intervalIntegral.integral_of_le hle, MeasureTheory.integral_Ioc_eq_integral_Ioo] at h1
      exact h1
    rw [e1, e2, e3] at hmono
    linarith [hmono]
  -- ## the limit of the sub-interval majorants
  have hL0 : Filter.Tendsto
      (fun n : ℕ => ∫ x in Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n),
        (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      Filter.atTop
      (nhds (∫ x in Set.Ioo 0 (Real.pi / 2),
        (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)) :=
    SliceAgmonOpen.tendsto_subinterval hAoo tendsto_gD_within tendsto_sub_gD_within
      (Eventually.of_forall (fun n => gD_lt_gap n))
  have hLmain : Filter.Tendsto
      (fun n : ℕ => (∫ x in Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n),
            (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
          - hbPrim f (Real.pi / 2 - gapDelta n) + hbPrim f (gapDelta n))
      Filter.atTop
      (nhds (∫ x in Set.Ioo 0 (Real.pi / 2),
        (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)) := by
    have h := (hL0.sub (hbp1.comp tendsto_sub_gD_within)).add (hbp0.comp tendsto_gD_within)
    simpa using h
  have hL : Filter.Tendsto
      (fun n : ℕ => ((∫ x in Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n),
            (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
          - hbPrim f (Real.pi / 2 - gapDelta n) + hbPrim f (gapDelta n))
        / (1 + Work.Spaces.eta) ^ 2)
      Filter.atTop
      (nhds ((∫ x in Set.Ioo 0 (Real.pi / 2),
        (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x) / (1 + Work.Spaces.eta) ^ 2)) := by
    have h := hLmain.mul_const ((1 + Work.Spaces.eta) ^ 2)⁻¹
    simpa [div_eq_mul_inv] using h
  -- ## the monotone-convergence step
  have hkey := integrableOn_Ioo_of_le (g := fun x : ℝ =>
        (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
      (u := gapDelta) (v := fun n : ℕ => Real.pi / 2 - gapDelta n)
      (L := fun n : ℕ => ((∫ x in Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n),
            (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
          - hbPrim f (Real.pi / 2 - gapDelta n) + hbPrim f (gapDelta n))
        / (1 + Work.Spaces.eta) ^ 2)
      (C := (∫ x in Set.Ioo 0 (Real.pi / 2),
        (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x) / (1 + Work.Spaces.eta) ^ 2)
      hg hnn tendsto_gD_within tendsto_sub_gD_within
      (Eventually.of_forall (fun n => gD_lt_gap n)) hL
      (fun n => by
        rw [le_div_iff₀ hcoef]
        calc (∫ x in Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n),
              (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
              * (1 + Work.Spaces.eta) ^ 2
            = (1 + Work.Spaces.eta) ^ 2
              * (∫ x in Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n),
                  (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))) := by ring
          _ ≤ (∫ x in Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n),
                (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
              - hbPrim f (Real.pi / 2 - gapDelta n) + hbPrim f (gapDelta n) := hbound n)
  -- ## converting back to `Iθ`
  have hcancel : (1 + Work.Spaces.eta) ^ 2
      * ((∫ x in Set.Ioo 0 (Real.pi / 2),
          (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x) / (1 + Work.Spaces.eta) ^ 2)
      = (∫ x in Set.Ioo 0 (Real.pi / 2),
          (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x) := by
    rw [mul_comm ((1 + Work.Spaces.eta) ^ 2)
      ((∫ x in Set.Ioo 0 (Real.pi / 2),
          (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x) / (1 + Work.Spaces.eta) ^ 2)]
    exact div_mul_cancel₀ _ (ne_of_gt hcoef)
  have hmain : (1 + Work.Spaces.eta) ^ 2
      * (∫ x in Set.Ioo 0 (Real.pi / 2),
          (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
      ≤ (∫ x in Set.Ioo 0 (Real.pi / 2),
          (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x) := by
    have h := mul_le_mul_of_nonneg_left hkey.2 (le_of_lt hcoef)
    linarith [h, hcancel.le, hcancel.ge]
  have hIθint : MeasureTheory.IntegrableOn
      (fun x : ℝ => (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
      Work.Spaces.Iθ :=
    hkey.1.mono_set_ae (by
      filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2)]
        with x hx
      intro hxI
      exact hx.mpr hxI)
  have hIθg : (∫ x in Work.Spaces.Iθ,
        (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
      = (∫ x in Set.Ioo 0 (Real.pi / 2),
          (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))) :=
    (MeasureTheory.setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm
  have hIθA : (∫ x in Work.Spaces.Iθ,
        (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      = (∫ x in Set.Ioo 0 (Real.pi / 2),
          (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x) :=
    (MeasureTheory.setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm
  exact ⟨hIθint, by rw [hIθg, hIθA]; exact hmain⟩

end Work.EllipticEst.Core.i0Aux.SliceAgmonAux
end
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.SliceAgmonOpen.EndpointRate =====
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

set_option autoImplicit false

/-- `x^{1+η} sin(2x)^{-(1+η)} ≤ (π/4)^{1+η}` for `0 < x ≤ π/4`. -/
private lemma pow_mul_sin_inv_le {x : ℝ} (hx0 : 0 < x) (hx : x ≤ Real.pi / 4) :
    x ^ (1 + Work.Spaces.eta) * (Real.sin (2 * x)) ^ (-(1 + Work.Spaces.eta))
      ≤ (Real.pi / 4) ^ (1 + Work.Spaces.eta) := by
  have hpi := Real.pi_pos
  have hη : 0 ≤ 1 + Work.Spaces.eta := by linarith [Work.Spaces.eta_pos]
  have hs : 0 < Real.sin (2 * x) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hx, hpi])
  have hsin : 4 * x / Real.pi ≤ Real.sin (2 * x) := by
    have h := Real.mul_le_sin (by linarith : (0:ℝ) ≤ 2 * x)
      (by linarith [hx, hpi] : 2 * x ≤ Real.pi / 2)
    have he : 2 / Real.pi * (2 * x) = 4 * x / Real.pi := by ring
    rwa [he] at h
  have hle : x ≤ (Real.pi / 4) * Real.sin (2 * x) := by
    have hkey := mul_le_mul_of_nonneg_left hsin (show (0:ℝ) ≤ Real.pi / 4 by positivity)
    have hsimp : Real.pi / 4 * (4 * x / Real.pi) = x := by
      calc Real.pi / 4 * (4 * x / Real.pi)
          = (Real.pi / Real.pi) * ((4:ℝ) / 4) * x := by ring
        _ = 1 * 1 * x := by
            rw [div_self (ne_of_gt hpi), div_self (by norm_num : (4:ℝ) ≠ 0)]
        _ = x := by ring
    rwa [hsimp] at hkey
  have h2 : (Real.sin (2 * x)) ^ (1 + Work.Spaces.eta)
      * (Real.sin (2 * x)) ^ (-(1 + Work.Spaces.eta)) = 1 := by
    rw [← Real.rpow_add hs,
      show (1 + Work.Spaces.eta) + (-(1 + Work.Spaces.eta)) = 0 by ring, Real.rpow_zero]
  have hstep : x ^ (1 + Work.Spaces.eta)
      ≤ ((Real.pi / 4) * Real.sin (2 * x)) ^ (1 + Work.Spaces.eta) :=
    Real.rpow_le_rpow hx0.le hle hη
  rw [Real.mul_rpow (by positivity) (le_of_lt hs)] at hstep
  calc x ^ (1 + Work.Spaces.eta) * (Real.sin (2 * x)) ^ (-(1 + Work.Spaces.eta))
      ≤ ((Real.pi / 4) ^ (1 + Work.Spaces.eta)
          * (Real.sin (2 * x)) ^ (1 + Work.Spaces.eta))
        * (Real.sin (2 * x)) ^ (-(1 + Work.Spaces.eta)) :=
        mul_le_mul_of_nonneg_right hstep (Real.rpow_nonneg (le_of_lt hs) _)
    _ = (Real.pi / 4) ^ (1 + Work.Spaces.eta)
        * ((Real.sin (2 * x)) ^ (1 + Work.Spaces.eta)
          * (Real.sin (2 * x)) ^ (-(1 + Work.Spaces.eta))) := by ring
    _ = (Real.pi / 4) ^ (1 + Work.Spaces.eta) := by rw [h2, mul_one]

/-- The local angular energy `θ ↦ ∫_{(0,θ)} g` tends to `0` at `0⁺`, for `g` integrable on
`(0, π/2)`. -/
private theorem tendsto_localEnergy {g : ℝ → ℝ}
    (hg : MeasureTheory.IntegrableOn g (Set.Ioo 0 (Real.pi / 2))) :
    Filter.Tendsto (fun θ : ℝ => ∫ t in Set.Ioo 0 θ, g t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hpi2 : (0:ℝ) < Real.pi / 2 := by positivity
  have hμlim : Filter.Tendsto
      (fun θ : ℝ => (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) (Set.Ioo 0 θ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    refine Filter.Tendsto.congr' (f₁ := fun θ : ℝ => ENNReal.ofReal θ) ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT hpi2] with θ hθ
      have hsub : Set.Ioo (0:ℝ) θ ⊆ Set.Ioo 0 (Real.pi / 2) :=
        fun x hx => ⟨hx.1, lt_trans hx.2 hθ.2⟩
      rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioo, Set.inter_eq_left.mpr hsub,
        Real.volume_Ioo, sub_zero]
    · have hcomp' : Filter.Tendsto (fun θ : ℝ => ENNReal.ofReal θ) (nhds 0) (nhds 0) := by
        simpa [ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.tendsto (0 : ℝ)
      have hid : Filter.Tendsto (fun θ : ℝ => θ) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) :=
        Filter.Tendsto.mono_right tendsto_id nhdsWithin_le_nhds
      refine Filter.Tendsto.congr' ?_ (hcomp'.comp hid)
      filter_upwards with θ
      rfl
  have hmain := hg.tendsto_setIntegral_nhds_zero hμlim
  refine Filter.Tendsto.congr' (f₁ := fun θ : ℝ => ∫ t in Set.Ioo 0 θ,
      g t ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)))) ?_ hmain
  filter_upwards [Ioo_mem_nhdsGT hpi2] with θ hθ
  have hsub : Set.Ioo (0:ℝ) θ ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun x hx => ⟨hx.1, lt_trans hx.2 hθ.2⟩
  rw [← Measure.restrict_restrict_of_subset (μ := MeasureTheory.volume)
    (s := Set.Ioo (0:ℝ) θ) (t := Set.Ioo 0 (Real.pi / 2)) hsub]

/-- The mirror image: `θ ↦ ∫_{(θ, π/2)} g` tends to `0` at `(π/2)⁻`. -/
private theorem tendsto_localEnergyR {g : ℝ → ℝ}
    (hg : MeasureTheory.IntegrableOn g (Set.Ioo 0 (Real.pi / 2))) :
    Filter.Tendsto (fun θ : ℝ => ∫ t in Set.Ioo θ (Real.pi / 2), g t)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hpi2 : (0:ℝ) < Real.pi / 2 := by positivity
  have hμlim : Filter.Tendsto
      (fun θ : ℝ => (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)))
        (Set.Ioo θ (Real.pi / 2)))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    refine Filter.Tendsto.congr' (f₁ := fun θ : ℝ => ENNReal.ofReal (Real.pi / 2 - θ)) ?_ ?_
    · filter_upwards [Ioo_mem_nhdsLT hpi2] with θ hθ
      have hsub : Set.Ioo θ (Real.pi / 2) ⊆ Set.Ioo (0:ℝ) (Real.pi / 2) :=
        fun x hx => ⟨lt_trans hθ.1 hx.1, hx.2⟩
      rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioo, Set.inter_eq_left.mpr hsub,
        Real.volume_Ioo]
    · have hcomp' : Filter.Tendsto (fun θ : ℝ => ENNReal.ofReal θ) (nhds 0) (nhds 0) := by
        simpa [ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.tendsto (0 : ℝ)
      have hid : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
        have h2 : Filter.Tendsto (fun θ : ℝ => Real.pi / 2 - θ)
            (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
            (nhds (Real.pi / 2 - Real.pi / 2)) :=
          Filter.Tendsto.sub tendsto_const_nhds
            (Filter.Tendsto.mono_right tendsto_id nhdsWithin_le_nhds)
        simpa using h2
      refine Filter.Tendsto.congr' ?_ (hcomp'.comp hid)
      filter_upwards with θ
      rfl
  have hmain := hg.tendsto_setIntegral_nhds_zero hμlim
  refine Filter.Tendsto.congr' (f₁ := fun θ : ℝ => ∫ t in Set.Ioo θ (Real.pi / 2),
      g t ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)))) ?_ hmain
  filter_upwards [Ioo_mem_nhdsLT hpi2] with θ hθ
  have hsub : Set.Ioo θ (Real.pi / 2) ⊆ Set.Ioo (0:ℝ) (Real.pi / 2) :=
    fun x hx => ⟨lt_trans hθ.1 hx.1, hx.2⟩
  rw [← Measure.restrict_restrict_of_subset (μ := MeasureTheory.volume)
    (s := Set.Ioo θ (Real.pi / 2)) (t := Set.Ioo 0 (Real.pi / 2)) hsub]

/-- The endpoint rate: `f² sin(2θ)^{-(1+η)} → 0` at both endpoints. -/
theorem EndpointRate {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (h0 : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (h1 : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hA : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) :
    (Filter.Tendsto (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) ∧
    (Filter.Tendsto (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) := by
  have hpi := Real.pi_pos
  have hpi2 : (0:ℝ) < Real.pi / 2 := by positivity
  have hpi4 : (0:ℝ) < Real.pi / 4 := by positivity
  have hAoo : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    hA.mono_set (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  have hf1 : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)) := hf.of_le (by norm_num)
  obtain ⟨K, hKpos, hK⟩ := Work.EllipticEst.Core.sliceBoundaryLimit
  obtain ⟨hleft, hright⟩ := hK f hf1 hAoo
  have hEL : Filter.Tendsto
      (fun θ : ℝ => ∫ t in Set.Ioo 0 θ,
        (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := tendsto_localEnergy hAoo
  have hER : Filter.Tendsto
      (fun θ : ℝ => ∫ t in Set.Ioo θ (Real.pi / 2),
        (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := tendsto_localEnergyR hAoo
  have hlimL : Filter.Tendsto
      (fun θ : ℝ => (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)) *
        ∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa using hEL.const_mul (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta))
  have hlimR : Filter.Tendsto
      (fun θ : ℝ => (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)) *
        ∫ t in Set.Ioo θ (Real.pi / 2),
          (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    simpa using hER.const_mul (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta))
  obtain ⟨cL, hcL_tend, hcL_bd⟩ := hleft
  obtain ⟨cR, hcR_tend, hcR_bd⟩ := hright
  have hcL0 : cL = 0 := tendsto_nhds_unique hcL_tend h0
  have hcR0 : cR = 0 := tendsto_nhds_unique hcR_tend h1
  have hbdL : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      (f θ) ^ 2 ≤ K * θ ^ (1 + Work.Spaces.eta) *
        ∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t := by
    intro θ hθ
    have h := hcL_bd θ hθ
    rwa [hcL0, sub_zero] at h
  have hbdR : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      (f θ) ^ 2 ≤ K * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) *
        ∫ t in Set.Ioo θ (Real.pi / 2), (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t := by
    intro θ hθ
    have h := hcR_bd θ hθ
    rwa [hcR0, sub_zero] at h
  constructor
  · -- left endpoint
    refine squeeze_zero' ?_ ?_ hlimL
    · filter_upwards [Ioo_mem_nhdsGT hpi2] with θ hθ
      exact mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (le_of_lt (sin_two_pos hθ)) _)
    · filter_upwards [Ioo_mem_nhdsGT hpi4] with θ hθ
      have hθ' : θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) := ⟨hθ.1, by linarith [hθ.2, hpi]⟩
      have h1' := hbdL θ hθ'
      have hs := sin_two_pos hθ'
      have hspow := Real.rpow_nonneg (le_of_lt hs) (-(1 + Work.Spaces.eta))
      have hE : 0 ≤ (∫ t in Set.Ioo 0 θ,
          (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) :=
        MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun t ht =>
          mul_nonneg (sq_nonneg _)
            (Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt ht.1,
              le_of_lt (lt_trans ht.2 hθ'.2)⟩))
      have h2' := pow_mul_sin_inv_le hθ.1 (le_of_lt hθ.2)
      calc (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))
          ≤ (K * θ ^ (1 + Work.Spaces.eta) *
              (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t))
            * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_right h1' hspow
        _ = (K * (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t))
            * (θ ^ (1 + Work.Spaces.eta)
              * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))) := by ring
        _ ≤ (K * (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t))
            * (Real.pi / 4) ^ (1 + Work.Spaces.eta) :=
            mul_le_mul_of_nonneg_left h2' (mul_nonneg hKpos.le hE)
        _ = (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)) *
            (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) := by ring
  · -- right endpoint
    refine squeeze_zero' ?_ ?_ hlimR
    · filter_upwards [Ioo_mem_nhdsLT hpi2] with θ hθ
      exact mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (le_of_lt (sin_two_pos hθ)) _)
    · filter_upwards [Ioo_mem_nhdsLT (show Real.pi / 4 < Real.pi / 2 by linarith)]
        with θ hθ
      have h2pi : Real.pi / 4 < θ := hθ.1
      have hθ' : θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) := ⟨by linarith [hpi, h2pi], hθ.2⟩
      have h1' := hbdR θ hθ'
      have hs := sin_two_pos hθ'
      have hspow := Real.rpow_nonneg (le_of_lt hs) (-(1 + Work.Spaces.eta))
      have hE : 0 ≤ (∫ t in Set.Ioo θ (Real.pi / 2),
          (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) :=
        MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun t ht =>
          mul_nonneg (sq_nonneg _)
            (Work.FTS.EllipticEst.thEta_nonneg ⟨le_of_lt (lt_trans hθ'.1 ht.1),
              le_of_lt ht.2⟩))
      have h2' : (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
          * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))
            ≤ (Real.pi / 4) ^ (1 + Work.Spaces.eta) := by
        have hsin : Real.sin (2 * θ) = Real.sin (2 * (Real.pi / 2 - θ)) := by
          rw [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]
        rw [hsin]
        exact pow_mul_sin_inv_le (by linarith [hθ.2]) (by linarith [h2pi])
      calc (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))
          ≤ (K * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta) *
              (∫ t in Set.Ioo θ (Real.pi / 2),
                (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t))
            * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_right h1' hspow
        _ = (K * (∫ t in Set.Ioo θ (Real.pi / 2),
              (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t))
            * ((Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
              * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))) := by ring
        _ ≤ (K * (∫ t in Set.Ioo θ (Real.pi / 2),
              (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t))
            * (Real.pi / 4) ^ (1 + Work.Spaces.eta) :=
            mul_le_mul_of_nonneg_left h2' (mul_nonneg hKpos.le hE)
        _ = (K * (Real.pi / 4) ^ (1 + Work.Spaces.eta)) *
            (∫ t in Set.Ioo θ (Real.pi / 2),
              (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) := by ring

end Work.EllipticEst.Core.i0Aux
end
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.SliceAgmonOpen.PhiGeNearZero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Core.i0Aux.SliceAgmonOpen

set_option autoImplicit false

/-- The pointwise derivative of `β f = f² sin(2θ)^η`:

  `(β f)' = 2 sin(2θ)^{2η} Φ f`     on `(0, π/2)`. -/
theorem beta_hasDerivAt {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (beta f) (2 * (Real.sin (2 * θ)) ^ (2 * Work.Spaces.eta) * Phi f θ) θ := by
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos hθ
  have hcd : ContDiffAt ℝ 2 f θ := hf.contDiffAt (isOpen_Ioo.mem_nhds hθ)
  have hdf : HasDerivAt f (deriv f θ) θ := (hcd.differentiableAt two_ne_zero).hasDerivAt
  have hlin : HasDerivAt (fun t : ℝ => 2 * t) (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have hsinD : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ := by
    have h := hlin.sin
    refine h.congr_deriv ?_
    ring
  have hpow : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ (Work.Spaces.eta))
      (2 * Real.cos (2 * θ) * Work.Spaces.eta
        * (Real.sin (2 * θ)) ^ (Work.Spaces.eta - 1)) θ :=
    hsinD.rpow_const (Or.inl hs.ne')
  have hsq : HasDerivAt (fun t : ℝ => (f t) ^ 2) (2 * f θ * deriv f θ) θ := by
    have h := hdf.pow 2
    refine h.congr_deriv ?_
    ring
  have hprod := hsq.mul hpow
  have key : 2 * (Real.sin (2 * θ)) ^ (2 * Work.Spaces.eta) * Phi f θ
      = 2 * f θ * deriv f θ * (Real.sin (2 * θ)) ^ (Work.Spaces.eta)
        + (f θ) ^ 2 * (2 * Real.cos (2 * θ) * Work.Spaces.eta
            * (Real.sin (2 * θ)) ^ (Work.Spaces.eta - 1)) := by
    have r1 : (Real.sin (2 * θ)) ^ (2 * Work.Spaces.eta)
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
      rw [← Real.rpow_add hs]; congr 1; ring
    have r2 : (Real.sin (2 * θ)) ^ (2 * Work.Spaces.eta)
        * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))
        = (Real.sin (2 * θ)) ^ (Work.Spaces.eta - 1) := by
      rw [← Real.rpow_add hs]; congr 1; ring
    simp only [Phi, Work.FTS.EllipticEst.thEta]
    rw [show (2 * (Real.sin (2 * θ)) ^ (2 * Work.Spaces.eta)) *
        (f θ * deriv f θ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) +
          Work.Spaces.eta / 2 * (f θ) ^ 2 * (2 * Real.cos (2 * θ)) *
            (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)))
        = (2 * (f θ * deriv f θ)) * ((Real.sin (2 * θ)) ^ (2 * Work.Spaces.eta)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          + ((f θ) ^ 2 * (Work.Spaces.eta * (2 * Real.cos (2 * θ))))
            * ((Real.sin (2 * θ)) ^ (2 * Work.Spaces.eta)
              * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))) from by ring]
    rw [r1, r2]
    ring
  exact hprod.congr_deriv key.symm


/-- `Φ f` is continuous on the open interval `(0, π/2)`. -/
theorem continuousOn_Phi {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (Phi f) (Set.Ioo 0 (Real.pi / 2)) := by
  have hcontf : ContinuousOn f (Set.Ioo 0 (Real.pi / 2)) := hf.continuousOn
  have hcontdf : ContinuousOn (deriv f) (Set.Ioo 0 (Real.pi / 2)) :=
    hf.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hcontsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hcontcos : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
  have hcontth : ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    simpa only [Work.FTS.EllipticEst.thEta] using
      hcontsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos hθ)))
  have hconts2 : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hcontsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos hθ)))
  have h1 : ContinuousOn
      (fun θ : ℝ => f θ * deriv f θ * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := (hcontf.mul hcontdf).mul hcontth
  have h2 : ContinuousOn
      (fun θ : ℝ => (Work.Spaces.eta / 2) * (f θ) ^ 2 * (2 * Real.cos (2 * θ))
        * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)))
      (Set.Ioo 0 (Real.pi / 2)) :=
    ((continuousOn_const.mul (hcontf.pow 2)).mul (continuousOn_const.mul hcontcos)).mul hconts2
  unfold Phi
  exact h1.add h2

/-- `β f` is non-negative on `(0, π/2)`. -/
theorem beta_nonneg {f : ℝ → ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 ≤ beta f θ :=
  mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt (sin_two_pos hθ)) _)

/-- The rate hypothesis at `0⁺` implies `β f → 0` there. -/
theorem beta_tendsto_zero {f : ℝ → ℝ}
    (hrate0 : Filter.Tendsto
      (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) :
    Filter.Tendsto (beta f) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hpi2 : (0:ℝ) < Real.pi / 2 := by positivity
  have hpi4 : (0:ℝ) < Real.pi / 4 := by positivity
  have hr : Filter.Tendsto (fun θ => (rho f θ) ^ 2)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ hrate0
    filter_upwards [Ioo_mem_nhdsGT hpi2] with θ hθ
    exact (rho_sq f hθ).symm
  refine squeeze_zero' ?_ ?_ hr
  · filter_upwards [Ioo_mem_nhdsGT hpi2] with θ hθ
    exact beta_nonneg hθ
  · filter_upwards [Ioo_mem_nhdsGT hpi4] with θ hθ
    have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    rw [beta_eq f hθ']
    calc (rho f θ) ^ 2 * (Real.sin (2 * θ)) ^ (1 + 2 * Work.Spaces.eta)
        ≤ (rho f θ) ^ 2 * 1 := by
          gcongr
          exact Real.rpow_le_one (le_of_lt (sin_two_pos hθ')) (Real.sin_le_one (2 * θ))
            (by linarith [Work.Spaces.eta_pos])
      _ = (rho f θ) ^ 2 := mul_one _

/-- The quantitative lower bound for the integral of `sin(2θ)^{2η}` used in the proof:
for `0 < t ≤ π/8` and `0 < ε < t/2`,

  `(t/4) sin(t)^{2η} ≤ ∫_ε^t sin(2θ)^{2η} dθ`,

the left-hand side being a *positive* constant independent of `ε`. -/
theorem integral_sin_two_rpow_lower {t ε : ℝ} (ht : 0 < t) (ht8 : t ≤ Real.pi / 8)
    (hε : ε ∈ Set.Ioo 0 (t / 2)) :
    (t / 4) * (Real.sin t) ^ (2 * Work.Spaces.eta)
      ≤ ∫ x in ε..t, (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) := by
  have hpi := Real.pi_pos
  have hη : 0 ≤ 2 * Work.Spaces.eta := by linarith [Work.Spaces.eta_pos]
  have ht2 : 0 < t / 2 := by linarith
  have ht3 : t / 2 ≤ 3 * t / 4 := by linarith
  have h3t : 3 * t / 4 ≤ t := by linarith
  have hcont : ContinuousOn (fun x : ℝ => (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta))
      (Set.uIcc (t / 2) (3 * t / 4)) := by
    apply ContinuousOn.rpow_const
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    · intro x hx
      rw [Set.uIcc_of_le ht3, Set.mem_Icc] at hx
      exact Or.inl (ne_of_gt (sin_two_pos
        ⟨by linarith [hx.1, ht2], by linarith [hx.2, h3t, ht8, hpi]⟩))
  have hint1 : IntervalIntegrable (fun x : ℝ => (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta))
      volume (t / 2) (3 * t / 4) := hcont.intervalIntegrable
  have hstep1 : (Real.sin t) ^ (2 * Work.Spaces.eta) * (3 * t / 4 - t / 2)
      ≤ ∫ x in t / 2..3 * t / 4, (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) := by
    have h := intervalIntegral.integral_mono_on ht3
      (intervalIntegrable_const (c := (Real.sin t) ^ (2 * Work.Spaces.eta))) hint1
      (fun x hx => ?_)
    · simpa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h
    · rw [Set.mem_Icc] at hx
      exact Real.rpow_le_rpow
        (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht]) (by linarith [ht8, hpi]))
        (Real.monotoneOn_sin ⟨by linarith, by linarith [ht8, hpi]⟩
          ⟨by linarith [hx.1, ht2], by linarith [hx.2, ht3, ht8, hpi]⟩ (by linarith [hx.1])) hη
  have hint2 : IntervalIntegrable (fun x : ℝ => (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta))
      volume ε t := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.rpow_const
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    · intro x hx
      rw [Set.uIcc_of_le (le_of_lt (lt_trans hε.2 (by linarith : t / 2 < t))), Set.mem_Icc] at hx
      exact Or.inl (ne_of_gt (sin_two_pos
        ⟨by linarith [hx.1, hε.1], by linarith [hx.2, ht8, hpi]⟩))
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Set.Ioc ε t)]
      (fun x : ℝ => (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta)) := by
    change ∀ᵐ x ∂(volume.restrict (Set.Ioc ε t)),
      (0:ℝ) ≤ (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta)
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    exact MeasureTheory.ae_of_all _ (fun x hx => Real.rpow_nonneg (le_of_lt
      (sin_two_pos ⟨by linarith [hx.1, hε.1], by linarith [hx.2, ht8, hpi]⟩)) _)
  have hstep2 := intervalIntegral.integral_mono_interval hε.2.le ht3 h3t hnn hint2
  calc (t / 4) * (Real.sin t) ^ (2 * Work.Spaces.eta)
      = (Real.sin t) ^ (2 * Work.Spaces.eta) * (3 * t / 4 - t / 2) := by ring
    _ ≤ ∫ x in t / 2..3 * t / 4, (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) := hstep1
    _ ≤ ∫ x in ε..t, (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) := hstep2

theorem PhiGeNearZero {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hrate0 : Filter.Tendsto
      (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) :
    ∀ a δ : ℝ, 0 < a → 0 < δ → ∃ θ ∈ Set.Ioo 0 a, -(δ) ≤ Phi f θ := by
  intro a δ ha hδ
  by_contra hcon
  push_neg at hcon
  have hpi := Real.pi_pos
  set t : ℝ := min a (Real.pi / 8) / 2 with ht_def
  have ht_pos : 0 < t := by
    rw [ht_def]
    have : 0 < min a (Real.pi / 8) := lt_min ha (by linarith)
    linarith
  have ht_lt_a : t < a := by
    rw [ht_def]
    have : min a (Real.pi / 8) ≤ a := min_le_left _ _
    linarith
  have ht_le8 : t ≤ Real.pi / 8 := by
    rw [ht_def]
    have : min a (Real.pi / 8) ≤ Real.pi / 8 := min_le_right _ _
    linarith
  have ht_lt_pi2 : t < Real.pi / 2 := by linarith
  have ht2pos : 0 < t / 2 := by linarith
  set c : ℝ := (t / 4) * (Real.sin t) ^ (2 * Work.Spaces.eta) with hc_def
  have hc_pos : 0 < c := by
    rw [hc_def]
    exact mul_pos (by linarith)
      (Real.rpow_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi ht_pos (by linarith)) _)
  have hc0_pos : 0 < 2 * δ * c := mul_pos (by linarith) hc_pos
  have hbeta_tend := beta_tendsto_zero (f := f) hrate0
  have hbeta_t_ge : 0 ≤ beta f t := beta_nonneg ⟨ht_pos, ht_lt_pi2⟩
  have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 2 * δ * c ≤ beta f ε := by
    filter_upwards [Ioo_mem_nhdsGT ht2pos] with ε hε
    have hε_pos : 0 < ε := hε.1
    have hεt : ε ≤ t := le_of_lt (by linarith [hε.2])
    -- the derivative of `β` is the integrand of the fundamental theorem
    have hderiv : ∀ x ∈ Set.uIcc ε t,
        HasDerivAt (beta f) (2 * (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) * Phi f x) x := by
      intro x hx
      rw [Set.uIcc_of_le hεt, Set.mem_Icc] at hx
      exact beta_hasDerivAt hf
        ⟨by linarith [hx.1, hε_pos], by linarith [hx.2, ht_lt_pi2]⟩
    have hscont : ContinuousOn (fun x : ℝ => (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta))
        (Set.uIcc ε t) := by
      apply ContinuousOn.rpow_const
      · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
      · intro x hx
        rw [Set.uIcc_of_le hεt, Set.mem_Icc] at hx
        exact Or.inl (ne_of_gt (sin_two_pos
          ⟨by linarith [hx.1, hε_pos], by linarith [hx.2, ht_lt_pi2]⟩))
    have hint1 : IntervalIntegrable
        (fun x : ℝ => 2 * (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) * Phi f x)
        volume ε t := by
      apply ContinuousOn.intervalIntegrable
      refine ContinuousOn.mul (hscont.const_mul 2) ?_
      exact (continuousOn_Phi hf).mono (fun x hx => by
        rw [Set.uIcc_of_le hεt, Set.mem_Icc] at hx
        exact ⟨by linarith [hx.1, hε_pos], by linarith [hx.2, ht_lt_pi2]⟩)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint1
    have hmono : ∫ x in ε..t, 2 * (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) * Phi f x
        ≤ ∫ x in ε..t, (-2 * δ) * (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) := by
      apply intervalIntegral.integral_mono_on hεt hint1
      · apply ContinuousOn.intervalIntegrable
        exact (hscont.const_mul (-2 * δ))
      · intro x hx
        rw [Set.mem_Icc] at hx
        have hxmem : x ∈ Set.Ioo 0 a :=
          ⟨by linarith [hx.1, hε_pos], by linarith [hx.2, ht_lt_a]⟩
        have hΦ : Phi f x < -δ := hcon x hxmem
        have hxI : x ∈ Set.Ioo 0 (Real.pi / 2) :=
          ⟨by linarith [hx.1, hε_pos], by linarith [hx.2, ht_lt_pi2]⟩
        have hp : 0 ≤ 2 * (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) :=
          mul_nonneg (by norm_num) (Real.rpow_nonneg (le_of_lt (sin_two_pos hxI)) _)
        calc 2 * (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) * Phi f x
            ≤ 2 * (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) * (-δ) :=
              mul_le_mul_of_nonneg_left (le_of_lt hΦ) hp
          _ = (-2 * δ) * (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) := by ring
    have hIntEq : ∫ x in ε..t, (-2 * δ) * (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta)
        = (-2 * δ) * ∫ x in ε..t, (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) :=
      intervalIntegral.integral_const_mul _ _
    have hLow : c ≤ ∫ x in ε..t, (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) := by
      rw [hc_def]
      exact integral_sin_two_rpow_lower ht_pos ht_le8 hε
    have hfin : ∫ x in ε..t, 2 * (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) * Phi f x
        ≤ (-2 * δ) * c := by
      calc ∫ x in ε..t, 2 * (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) * Phi f x
          ≤ ∫ x in ε..t, (-2 * δ) * (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) := hmono
        _ = (-2 * δ) * ∫ x in ε..t, (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) := hIntEq
        _ ≤ (-2 * δ) * c := mul_le_mul_of_nonpos_left hLow (by linarith)
    -- `β ε = β t - ∫ ≥ 2 δ c`
    have hbε : beta f ε
        = beta f t - ∫ x in ε..t, 2 * (Real.sin (2 * x)) ^ (2 * Work.Spaces.eta) * Phi f x := by
      linarith [hFTC]
    show 2 * δ * c ≤ beta f ε
    linarith [hbε, hfin, hbeta_t_ge]
  have hle := ge_of_tendsto hbeta_tend hev
  linarith [hc0_pos, hle]

end Work.EllipticEst.Core.i0Aux.SliceAgmonOpen
end
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.SliceAgmonOpen.PhiIdentity =====
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

set_option autoImplicit false

/-- The pointwise derivative of the primitive `Φ`. -/
theorem Phi_hasDerivAt {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (Phi f)
      ((deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
        + f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ
        - 2 * Work.Spaces.eta * (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
        - 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * (f θ) ^ 2
            * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))) θ := by
  have hs := sin_two_pos hθ
  have hcd : ContDiffAt ℝ 2 f θ := hf.contDiffAt (isOpen_Ioo.mem_nhds hθ)
  have hdf : HasDerivAt f (deriv f θ) θ := (hcd.differentiableAt two_ne_zero).hasDerivAt
  have hdf' : HasDerivAt (deriv f) (deriv (deriv f) θ) θ :=
    ((hcd.derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasDerivAt
  have hlin : HasDerivAt (fun t : ℝ => 2 * t) (2 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have hsinD : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ := by
    have h := hlin.sin
    refine h.congr_deriv ?_
    ring
  have hcosD : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-2 * Real.sin (2 * θ)) θ := by
    have h := hlin.cos
    refine h.congr_deriv ?_
    ring
  -- the rpow relation used to absorb the derivative of `cos (2·)`
  have key1 : Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [mul_comm]
    have h := Real.rpow_add hs (-(1 + Work.Spaces.eta)) (1 : ℝ)
    rw [Real.rpow_one] at h
    rw [show (-(1 + Work.Spaces.eta) + (1 : ℝ)) = -(Work.Spaces.eta) by ring] at h
    exact h.symm
  have hsig1 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)))
      (-2 * Work.Spaces.eta * Real.cos (2 * θ)
        * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))) θ := by
    have h := hsinD.rpow_const (p := -(Work.Spaces.eta)) (Or.inl hs.ne')
    refine h.congr_deriv ?_
    rw [show (-(Work.Spaces.eta) - 1 : ℝ) = -(1 + Work.Spaces.eta) by ring]
    ring
  have hsig2 : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ (-(1 + Work.Spaces.eta)))
      (-2 * (1 + Work.Spaces.eta) * Real.cos (2 * θ)
        * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))) θ := by
    have h := hsinD.rpow_const (p := -(1 + Work.Spaces.eta)) (Or.inl hs.ne')
    refine h.congr_deriv ?_
    rw [show (-(1 + Work.Spaces.eta) - 1 : ℝ) = -(2 + Work.Spaces.eta) by ring]
    ring
  have hgg : HasDerivAt
      (fun t : ℝ => (2 * Real.cos (2 * t)) * (Real.sin (2 * t)) ^ (-(1 + Work.Spaces.eta)))
      (-4 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        - 4 * (1 + Work.Spaces.eta) * (Real.cos (2 * θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))) θ := by
    have h := (hcosD.const_mul 2).mul hsig2
    refine h.congr_deriv ?_
    rw [show (2 * (-2 * Real.sin (2 * θ))) * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))
        = -4 * (Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))) by ring,
      key1]
    ring
  have hA := (hdf.mul hdf').mul hsig1
  have hB := ((hdf.pow 2).const_mul (Work.Spaces.eta / 2)).mul hgg
  have hsum := hA.add hB
  have hfun : Phi f = fun t : ℝ => f t * deriv f t * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta))
      + (Work.Spaces.eta / 2) * (f t) ^ 2
        * ((2 * Real.cos (2 * t)) * (Real.sin (2 * t)) ^ (-(1 + Work.Spaces.eta))) := by
    funext t
    simp only [Phi, Work.FTS.EllipticEst.thEta]
    ring
  rw [hfun]
  refine hsum.congr_deriv ?_
  simp only [Work.FTS.EllipticEst.thEta, Pi.mul_apply, Pi.pow_apply,
    show (2:ℕ) - 1 = 1 from rfl, pow_one]
  ring

/-- The integration by parts in primitive form. -/
theorem PhiIdentity {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < Real.pi / 2) :
    Phi f b - Phi f a
      = ∫ θ in a..b, ((deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
          + f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ
          - 2 * Work.Spaces.eta * (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
          - 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * (f θ) ^ 2
              * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))) := by
  have hmem : ∀ θ ∈ Set.uIcc a b, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro θ hθ
    rw [Set.uIcc_of_le hab, Set.mem_Icc] at hθ
    exact ⟨by linarith [hθ.1, ha], by linarith [hθ.2, hb]⟩
  have hcontf : ContinuousOn f (Set.uIcc a b) := hf.continuousOn.mono hmem
  have hcontdf : ContinuousOn (deriv f) (Set.uIcc a b) :=
    (hf.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono hmem
  have hcontddf : ContinuousOn (deriv (deriv f)) (Set.uIcc a b) :=
    (((hf.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).continuousOn_deriv_of_isOpen
      isOpen_Ioo (by norm_num))).mono hmem
  have hcontsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.uIcc a b) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hcontth : ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ) (Set.uIcc a b) := by
    simpa only [Work.FTS.EllipticEst.thEta] using
      hcontsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos (hmem θ hθ))))
  have hconts2 : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))
      (Set.uIcc a b) :=
    hcontsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos (hmem θ hθ))))
  have hcontcos2 : ContinuousOn (fun θ : ℝ => (Real.cos (2 * θ)) ^ 2) (Set.uIcc a b) :=
    (((Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn).pow 2)
  have ht1 : ContinuousOn (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.uIcc a b) := (hcontdf.pow 2).mul hcontth
  have ht2 : ContinuousOn
      (fun θ : ℝ => f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ) (Set.uIcc a b) :=
    (hcontf.mul hcontddf).mul hcontth
  have ht3 : ContinuousOn (fun θ : ℝ => 2 * Work.Spaces.eta * (f θ) ^ 2
      * Work.FTS.EllipticEst.thEta θ) (Set.uIcc a b) :=
    (continuousOn_const.mul (hcontf.pow 2)).mul hcontth
  have ht4 : ContinuousOn (fun θ : ℝ => 2 * Work.Spaces.eta * (1 + Work.Spaces.eta)
      * (f θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta))) (Set.uIcc a b) :=
    ((continuousOn_const.mul (hcontf.pow 2)).mul hcontcos2).mul hconts2
  have hint : IntervalIntegrable (fun θ : ℝ => ((deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
      + f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ
      - 2 * Work.Spaces.eta * (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
      - 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * (f θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))) volume a b :=
    (((ht1.add ht2).sub ht3).sub ht4).intervalIntegrable
  have hderiv : ∀ θ ∈ Set.uIcc a b,
      HasDerivAt (Phi f) (((deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
        + f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ
        - 2 * Work.Spaces.eta * (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
        - 2 * Work.Spaces.eta * (1 + Work.Spaces.eta) * (f θ) ^ 2
            * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))) θ :=
    fun θ hθ => Phi_hasDerivAt hf (hmem θ hθ)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  exact hFTC.symm

end Work.EllipticEst.Core.i0Aux
end
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.SliceAgmonOpen.PhiLeNearPi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.SliceAgmonOpen

open scoped Real Topology
open MeasureTheory Set Filter

/-- The derivative of `β = f²·sin(2θ)^η` is `2·sin(2θ)^{2η}·Φ`, where `Φ` is the primitive
of the weighted `θ`-integration by parts (see `Defs.lean`).  Consequently the sign of `Φ`
is the sign of `β'`, which is what forces `Φ` to become small near `π/2`. -/
theorem PhiLeNearPi_deriv_beta {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (beta f) θ = 2 * (Real.sin (2 * θ)) ^ (2 * Work.Spaces.eta) * Phi f θ := by
  have hsin2 : 0 < Real.sin (2 * θ) := sin_two_pos hθ
  have hfd : DifferentiableOn ℝ f (Set.Ioo 0 (Real.pi / 2)) := hf.differentiableOn (by norm_num)
  have hf' : HasDerivAt f (deriv f θ) θ :=
    (hfd.differentiableAt (isOpen_Ioo.mem_nhds hθ)).hasDerivAt
  have hsin : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ)) (2 * Real.cos (2 * θ)) θ := by
    have h := (Real.hasDerivAt_sin (2 * θ)).comp θ ((hasDerivAt_id θ).const_mul 2)
    simpa [Function.comp_def, mul_comm] using h
  have hpow : HasDerivAt (fun θ : ℝ => (Real.sin (2 * θ)) ^ Work.Spaces.eta)
      ((2 * Real.cos (2 * θ)) * Work.Spaces.eta
        * (Real.sin (2 * θ)) ^ (Work.Spaces.eta - 1)) θ :=
    hsin.rpow_const (Or.inl (ne_of_gt hsin2))
  have hmul : HasDerivAt (beta f)
      ((2 * f θ ^ (2 - 1) * deriv f θ) * (Real.sin (2 * θ)) ^ Work.Spaces.eta
        + f θ ^ 2 * ((2 * Real.cos (2 * θ)) * Work.Spaces.eta
          * (Real.sin (2 * θ)) ^ (Work.Spaces.eta - 1))) θ := by
    change HasDerivAt (fun y : ℝ => f y ^ 2 * (Real.sin (2 * y)) ^ Work.Spaces.eta) _ θ
    have h := (hf'.pow 2).mul hpow
    have hfun : (f ^ 2 * fun θ : ℝ => (Real.sin (2 * θ)) ^ Work.Spaces.eta)
        = fun y : ℝ => f y ^ 2 * (Real.sin (2 * y)) ^ Work.Spaces.eta := by
      funext y; simp only [Pi.mul_apply, Pi.pow_apply]
    rw [hfun] at h
    exact h
  rw [hmul.deriv]
  have h1 : (Real.sin (2 * θ)) ^ (2 * Work.Spaces.eta)
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
      = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
    rw [← Real.rpow_add hsin2]; congr 1; ring
  have h2 : (Real.sin (2 * θ)) ^ (2 * Work.Spaces.eta)
        * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta - 1) := by
    rw [← Real.rpow_add hsin2]; congr 1; ring
  rw [Phi, Work.FTS.EllipticEst.thEta]
  rw [show 2 * (Real.sin (2 * θ)) ^ (2 * Work.Spaces.eta)
        * (f θ * deriv f θ * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
          + Work.Spaces.eta / 2 * f θ ^ 2 * (2 * Real.cos (2 * θ))
              * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)))
      = 2 * (f θ * deriv f θ)
          * ((Real.sin (2 * θ)) ^ (2 * Work.Spaces.eta)
              * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        + f θ ^ 2 * (2 * Real.cos (2 * θ) * Work.Spaces.eta)
          * ((Real.sin (2 * θ)) ^ (2 * Work.Spaces.eta)
              * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)))
      from by ring]
  rw [h1, h2]
  norm_num
  ring

/-- `β = f²·sin(2θ)^η` tends to `0` at `(π/2)⁻` as soon as `f²·sin(2θ)^{-(1+η)}` does:
`β = (f² sin(2θ)^{-(1+η)}) · sin(2θ)^{1+2η}` and `sin(2θ) ≤ 1` near `π/2`. -/
theorem PhiLeNearPi_beta_tendsto {f : ℝ → ℝ}
    (hrate1 : Filter.Tendsto
      (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    Filter.Tendsto (beta f) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hIoo : Set.Ioo 0 (Real.pi / 2) ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := by
    rw [Set.Ioo]
    exact Filter.inter_mem
      (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by linarith [Real.pi_pos])))
      self_mem_nhdsWithin
  refine squeeze_zero' ?_ ?_ hrate1
  · filter_upwards [hIoo] with θ hθ
    rw [beta]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_pos hθ).le _)
  · filter_upwards [hIoo] with θ hθ
    have hs : 0 < Real.sin (2 * θ) := sin_two_pos hθ
    have hbeta_eq : beta f θ = (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))
        * (Real.sin (2 * θ)) ^ (1 + 2 * Work.Spaces.eta) := by
      rw [beta, mul_assoc, ← Real.rpow_add hs,
        show -(1 + Work.Spaces.eta) + (1 + 2 * Work.Spaces.eta) = Work.Spaces.eta by ring]
    rw [hbeta_eq]
    refine mul_le_of_le_one_right ?_ ?_
    · exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs.le _)
    · exact Real.rpow_le_one hs.le (Real.sin_le_one _) (by linarith [Work.Spaces.eta_pos])

theorem PhiLeNearPi {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hrate1 : Filter.Tendsto
      (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    ∀ b δ : ℝ, b < Real.pi / 2 → 0 < δ → ∃ θ ∈ Set.Ioo b (Real.pi / 2), Phi f θ ≤ δ := by
  intro b δ hb hδ
  by_contra hcon
  have hcon' : ∀ θ, θ ∈ Set.Ioo b (Real.pi / 2) → δ < Phi f θ :=
    fun θ hθ => not_le.mp (fun hle => hcon ⟨θ, hθ, hle⟩)
  -- Work on a sub-interval `(c, π/2)` with `b < c` and `0 < c`.
  have hmax : max b 0 < Real.pi / 2 := max_lt hb (half_pos Real.pi_pos)
  obtain ⟨c, hc₁, hc₂⟩ := exists_between hmax
  have hbc : b < c := lt_of_le_of_lt (le_max_left b 0) hc₁
  have h0c : 0 < c := lt_of_le_of_lt (le_max_right b 0) hc₁
  have hcpi : c < Real.pi / 2 := hc₂
  have hsub : Set.Ioo c (Real.pi / 2) ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun x hx => ⟨lt_trans h0c hx.1, hx.2⟩
  -- `β` is continuous on `(c, π/2)` and strictly increasing there, since `Φ > δ > 0`.
  have hcont : ContinuousOn (beta f) (Set.Ioo c (Real.pi / 2)) := by
    have hfcont : ContinuousOn f (Set.Ioo c (Real.pi / 2)) := hf.continuousOn.mono hsub
    have hsincont : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo c (Real.pi / 2)) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    have hpowcont : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ Work.Spaces.eta)
        (Set.Ioo c (Real.pi / 2)) :=
      hsincont.rpow_const
        (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos ⟨lt_trans h0c hθ.1, hθ.2⟩)))
    have h := (hfcont.pow 2).mul hpowcont
    have hfun : (f ^ 2 * fun θ : ℝ => (Real.sin (2 * θ)) ^ Work.Spaces.eta) = beta f := by
      funext θ; simp only [Pi.mul_apply, Pi.pow_apply, beta]
    rw [hfun] at h
    exact h
  have hpos : ∀ x ∈ Set.Ioo c (Real.pi / 2), 0 < deriv (beta f) x := by
    intro x hx
    have hx0 : x ∈ Set.Ioo 0 (Real.pi / 2) := hsub hx
    have hxb : x ∈ Set.Ioo b (Real.pi / 2) := ⟨lt_trans hbc hx.1, hx.2⟩
    rw [PhiLeNearPi_deriv_beta hf hx0]
    exact mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (sin_two_pos hx0) _))
      (lt_trans hδ (hcon' x hxb))
  have hmono : StrictMonoOn (beta f) (Set.Ioo c (Real.pi / 2)) :=
    strictMonoOn_of_deriv_pos (convex_Ioo c (Real.pi / 2)) hcont
      (fun x hx => hpos x (by simpa [interior_Ioo] using hx))
  -- Two points `θ₀ < θ₁` of the interval; monotonicity gives `β θ₀ < β θ₁`.
  obtain ⟨θ₀, hcθ₀, hθ₀π⟩ := exists_between hcpi
  obtain ⟨θ₁, hθ₀θ₁, hθ₁π⟩ := exists_between hθ₀π
  have hθ₀ : θ₀ ∈ Set.Ioo c (Real.pi / 2) := ⟨hcθ₀, hθ₀π⟩
  have hθ₁ : θ₁ ∈ Set.Ioo c (Real.pi / 2) := ⟨lt_trans hcθ₀ hθ₀θ₁, hθ₁π⟩
  have hstrict : beta f θ₀ < beta f θ₁ := (hmono.lt_iff_lt hθ₀ hθ₁).mpr hθ₀θ₁
  -- But `β → 0` at `(π/2)⁻`: monotonicity forces `β θ₁ ≤ 0`, while `β θ₀ ≥ 0`.
  have hbt : Filter.Tendsto (beta f) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds 0) := PhiLeNearPi_beta_tendsto hrate1
  have hIoi1 : Set.Ioi θ₁ ∈ nhds (Real.pi / 2) := Ioi_mem_nhds hθ₁π
  have hIoi : Set.Ioi θ₁ ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) :=
    mem_nhdsWithin_of_mem_nhds hIoi1
  have hev : ∀ᶠ θ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)), beta f θ₁ ≤ beta f θ := by
    filter_upwards [self_mem_nhdsWithin, hIoi] with θ hθI hθgt
    have hθ : θ ∈ Set.Ioo c (Real.pi / 2) := ⟨lt_trans hθ₁.1 (show θ₁ < θ from hθgt), hθI⟩
    exact le_of_lt ((hmono.lt_iff_lt hθ₁ hθ).mpr (show θ₁ < θ from hθgt))
  have hle0 : beta f θ₁ ≤ 0 := ge_of_tendsto hbt hev
  have hge0 : 0 ≤ beta f θ₀ := by
    rw [beta]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_pos (hsub hθ₀)).le _)
  exact absurd hstrict (not_lt.mpr (le_trans hle0 hge0))

end Work.EllipticEst.Core.i0Aux.SliceAgmonOpen
end
-- ===== merged: Submission.Work.EllipticEst.Core.i0Aux.TVRed.sScaleBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.TVRed

open scoped Real

/-- With `L = sScale P E = (P / (16 (P + E)))^{1/4}` and `η = 99/100`, the hypothesis
`F₀² + F₁² ≤ 4 L^{3+η} E + 200 L^{η-1} P` gives, after multiplying by `L^{1-η}`,
`(F₀² + F₁²) L^{1-η} ≤ 4 L⁴ E + 200 P ≤ (1/4) P + 200 P ≤ 201 P`. -/
theorem sScaleBounds {P E F₀ F₁ Cb : ℝ} (hP : 0 < P) (hE : 0 ≤ E) (hCb : 0 < Cb)
    (hS : F₀ ^ 2 + F₁ ^ 2
      ≤ 4 * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (3 + Work.Spaces.eta) * E
        + 200 * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (Work.Spaces.eta - 1) * P) :
    (1000 * (Cb + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2)
        * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (1 - Work.Spaces.eta)
      ≤ 1000 * (Cb + 1) ^ 2 * 201 * P) ∧
    (1000 * (Cb + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2)
        * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (-(3 + Work.Spaces.eta))
      ≤ 1000 * (Cb + 1) ^ 2 * 3204 * (P + E)) := by
  have hL := sScale_pos hP hE
  have hA := sScale_mul_A hP hE
  have hB := sScale_mul_B hP hE
  have hC := sScale_mul_C hP hE
  have hD := sScale_mul_D hP hE
  have h4 := sScale_rpow_four hP hE
  have hcoef : 0 ≤ 1000 * (Cb + 1) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  -- the first exponent: multiply through by `L ^ (1 - η) ≥ 0`
  have key1 : (F₀ ^ 2 + F₁ ^ 2) * (Work.EllipticEst.Core.i0Aux.sScale P E)
        ^ (1 - Work.Spaces.eta) ≤ 201 * P := by
    have h := mul_le_mul_of_nonneg_right hS (Real.rpow_nonneg hL.le (1 - Work.Spaces.eta))
    have hkey : (F₀ ^ 2 + F₁ ^ 2) * (Work.EllipticEst.Core.i0Aux.sScale P E)
          ^ (1 - Work.Spaces.eta) ≤ 4 * E * (P / (16 * (P + E))) + 200 * P := by
      calc (F₀ ^ 2 + F₁ ^ 2) * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (1 - Work.Spaces.eta)
          ≤ (4 * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (3 + Work.Spaces.eta) * E
              + 200 * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (Work.Spaces.eta - 1) * P)
            * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (1 - Work.Spaces.eta) := h
        _ = 4 * E * ((Work.EllipticEst.Core.i0Aux.sScale P E) ^ (3 + Work.Spaces.eta)
              * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (1 - Work.Spaces.eta))
            + 200 * P * ((Work.EllipticEst.Core.i0Aux.sScale P E) ^ (Work.Spaces.eta - 1)
              * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (1 - Work.Spaces.eta)) := by ring
        _ = 4 * E * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (4 : ℝ) + 200 * P * 1 := by
              rw [hA, hB]
        _ = 4 * E * (P / (16 * (P + E))) + 200 * P := by rw [h4, mul_one]
    have hfin : 4 * E * (P / (16 * (P + E))) + 200 * P ≤ 201 * P := by
      have hden : (0 : ℝ) < 4 * (P + E) := by nlinarith
      have hsplit : 4 * E * (P / (16 * (P + E))) = P * E / (4 * (P + E)) := by
        field_simp
        ring
      have h1 : P * E / (4 * (P + E)) ≤ P / 4 := by
        rw [div_le_iff₀ hden]
        nlinarith
      linarith
    linarith
  -- the second exponent: multiply through by `L ^ (-(3 + η)) ≥ 0`
  have key2 : (F₀ ^ 2 + F₁ ^ 2) * (Work.EllipticEst.Core.i0Aux.sScale P E)
        ^ (-(3 + Work.Spaces.eta)) ≤ 3204 * (P + E) := by
    have h := mul_le_mul_of_nonneg_right hS (Real.rpow_nonneg hL.le (-(3 + Work.Spaces.eta)))
    have hkey : (F₀ ^ 2 + F₁ ^ 2) * (Work.EllipticEst.Core.i0Aux.sScale P E)
          ^ (-(3 + Work.Spaces.eta)) ≤ 4 * E + 200 * P * (16 * (P + E) / P) := by
      calc (F₀ ^ 2 + F₁ ^ 2) * (Work.EllipticEst.Core.i0Aux.sScale P E)
            ^ (-(3 + Work.Spaces.eta))
          ≤ (4 * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (3 + Work.Spaces.eta) * E
              + 200 * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (Work.Spaces.eta - 1) * P)
            * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (-(3 + Work.Spaces.eta)) := h
        _ = 4 * E * ((Work.EllipticEst.Core.i0Aux.sScale P E) ^ (3 + Work.Spaces.eta)
              * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (-(3 + Work.Spaces.eta)))
            + 200 * P * ((Work.EllipticEst.Core.i0Aux.sScale P E) ^ (Work.Spaces.eta - 1)
              * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (-(3 + Work.Spaces.eta))) := by ring
        _ = 4 * E + 200 * P * (16 * (P + E) / P) := by
              rw [mul_comm ((Work.EllipticEst.Core.i0Aux.sScale P E) ^ (3 + Work.Spaces.eta)) _,
                hC, mul_one,
                mul_comm ((Work.EllipticEst.Core.i0Aux.sScale P E) ^ (Work.Spaces.eta - 1)) _,
                hD]
    have hfin : 4 * E + 200 * P * (16 * (P + E) / P) ≤ 3204 * (P + E) := by
      have hsplit : 200 * P * (16 * (P + E) / P) = 3200 * (P + E) := by
        field_simp
        ring
      linarith
    linarith
  constructor
  · calc 1000 * (Cb + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2)
          * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (1 - Work.Spaces.eta)
        = 1000 * (Cb + 1) ^ 2 * ((F₀ ^ 2 + F₁ ^ 2)
            * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (1 - Work.Spaces.eta)) := by ring
      _ ≤ 1000 * (Cb + 1) ^ 2 * (201 * P) := mul_le_mul_of_nonneg_left key1 hcoef
      _ = 1000 * (Cb + 1) ^ 2 * 201 * P := by ring
  · calc 1000 * (Cb + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2)
          * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (-(3 + Work.Spaces.eta))
        = 1000 * (Cb + 1) ^ 2 * ((F₀ ^ 2 + F₁ ^ 2)
            * (Work.EllipticEst.Core.i0Aux.sScale P E) ^ (-(3 + Work.Spaces.eta))) := by ring
      _ ≤ 1000 * (Cb + 1) ^ 2 * (3204 * (P + E)) := mul_le_mul_of_nonneg_left key2 hcoef
      _ = 1000 * (Cb + 1) ^ 2 * 3204 * (P + E) := by ring

end Work.EllipticEst.Core.i0Aux.TVRed
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.Q0.RRBasic =====
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

/-! ## `exp`/`rpow` algebra -/

theorem exp_mul_rpow {α σ : ℝ} (hα : α ≠ 0) :
    (Real.exp (α * σ)) ^ ((5 - α) / α) = Real.exp ((5 - α) * σ) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  field_simp

theorem exp_alpha_eq_self {α : ℝ} (hα : 0 < α) {z : ℝ} (hz : 0 < z) :
    Real.exp (α * ((1 / α) * Real.log z)) = z := by
  have h1 : α * ((1 / α) * Real.log z) = Real.log z := by field_simp
  rw [h1, Real.exp_log hz]

theorem continuous_wtRR (α : ℝ) : Continuous (fun q : ℝ × ℝ => wtRR α q.1 q.2) := by
  have h : (fun q : ℝ × ℝ => wtRR α q.1 q.2)
      = fun q : ℝ × ℝ => α * Real.exp (5 * q.1) * Real.cos q.2 := rfl
  rw [h]
  fun_prop

/-! ## Locality of `kopDr` -/

theorem deriv_eq_zero_of_eventuallyEq_zero {f : ℝ → ℝ} {x : ℝ} (h : f =ᶠ[𝓝 x] 0) :
    deriv f x = 0 := by
  rw [h.deriv_eq]
  exact deriv_const x 0

/-- `kopDr ψ` vanishes outside the (topological) support of `ψ`. -/
theorem kopDr_eq_zero_of_notMem_tsupport {ψ : ℝ → ℝ → ℝ} {σ θ : ℝ}
    (h : (σ, θ) ∉ tsupport (Function.uncurry ψ)) : kopDr ψ σ θ = 0 := by
  have hev : Function.uncurry ψ =ᶠ[𝓝 (σ, θ)] 0 := notMem_tsupport_iff_eventuallyEq.mp h
  have hslσ : (fun σ' : ℝ => ψ σ' θ) =ᶠ[𝓝 σ] 0 := by
    have h1 := hev.comp_tendsto (g := fun σ' : ℝ => (σ', θ))
      (show Tendsto (fun σ' : ℝ => (σ', θ)) (𝓝 σ) (𝓝 (σ, θ)) from by
        rw [nhds_prod_eq]; exact tendsto_id.prodMk tendsto_const_nhds)
    have heq : (Function.uncurry ψ ∘ fun σ' : ℝ => (σ', θ)) = fun σ' => ψ σ' θ := by
      funext σ'; rfl
    have hz : ((0 : ℝ × ℝ → ℝ) ∘ fun σ' : ℝ => (σ', θ)) = 0 := by
      funext σ'; rfl
    rwa [heq, hz] at h1
  have hslθ : (fun θ' : ℝ => ψ σ θ') =ᶠ[𝓝 θ] 0 := by
    have h1 := hev.comp_tendsto (g := fun θ' : ℝ => (σ, θ'))
      (show Tendsto (fun θ' : ℝ => (σ, θ')) (𝓝 θ) (𝓝 (σ, θ)) from by
        rw [nhds_prod_eq]; exact tendsto_const_nhds.prodMk tendsto_id)
    have heq : (Function.uncurry ψ ∘ fun θ' : ℝ => (σ, θ')) = fun θ' => ψ σ θ' := by
      funext θ'; rfl
    have hz : ((0 : ℝ × ℝ → ℝ) ∘ fun θ' : ℝ => (σ, θ')) = 0 := by
      funext θ'; rfl
    rwa [heq, hz] at h1
  have hzero : deriv (0 : ℝ → ℝ) = 0 := funext fun x => deriv_const x 0
  have hval : ψ σ θ = 0 := by
    have := hev.eq_of_nhds
    simpa [Function.uncurry] using this
  have hdσ : deriv (fun σ' : ℝ => ψ σ' θ) σ = 0 := deriv_eq_zero_of_eventuallyEq_zero hslσ
  have hdθ : deriv (fun θ' : ℝ => ψ σ θ') θ = 0 := deriv_eq_zero_of_eventuallyEq_zero hslθ
  have hslσ'd : deriv (fun σ'' : ℝ => ψ σ'' θ) =ᶠ[𝓝 σ] 0 := by
    have h1 := hslσ.deriv
    rwa [hzero] at h1
  have hslθ'd : deriv (fun θ'' : ℝ => ψ σ θ'') =ᶠ[𝓝 θ] 0 := by
    have h1 := hslθ.deriv
    rwa [hzero] at h1
  have h2σ : deriv (fun σ' : ℝ => deriv (fun σ'' : ℝ => ψ σ'' θ) σ') σ = 0 :=
    deriv_eq_zero_of_eventuallyEq_zero hslσ'd
  have h2θ : deriv (fun θ' : ℝ => deriv (fun θ'' : ℝ => ψ σ θ'') θ') θ = 0 :=
    deriv_eq_zero_of_eventuallyEq_zero hslθ'd
  simp only [kopDr, hval, hdσ, hdθ, h2σ, h2θ]
  ring


/-! ## The operator `bslOp` on `0`, and its locality -/

theorem pzIter_zero_eq (n : ℕ) :
    Work.Spaces.pzIter n (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Work.Spaces.pzIter_succ, ih]
    funext z θ
    simp only [Work.Spaces.pz, deriv_const]

theorem pthIter_zero_eq (n : ℕ) :
    Work.Spaces.pthIter n (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Work.Spaces.pthIter_succ, ih]
    funext z θ
    simp only [Work.Spaces.pth, deriv_const]

theorem bslOp_zero (α z θ : ℝ) :
    Work.Elliptic.bslOp α (fun _ _ : ℝ => (0 : ℝ)) z θ = 0 := by
  have h1 : Work.Spaces.pzIter 2 (fun _ _ : ℝ => (0 : ℝ)) z θ = 0 := by
    rw [pzIter_zero_eq 2]
  have h2 : Work.Spaces.pz (fun _ _ : ℝ => (0 : ℝ)) z θ = 0 := by
    simp [Work.Spaces.pz]
  have h3 : Work.Spaces.pthIter 2 (fun _ _ : ℝ => (0 : ℝ)) z θ = 0 := by
    rw [pthIter_zero_eq 2]
  have h4 : Work.Spaces.pth
      (fun z θ : ℝ => Real.tan θ * (fun _ _ : ℝ => (0 : ℝ)) z θ) z θ = 0 := by
    have : (fun z θ : ℝ => Real.tan θ * (fun _ _ : ℝ => (0 : ℝ)) z θ)
        = fun _ _ : ℝ => (0 : ℝ) := by
      funext z θ; simp
    rw [this]; simp [Work.Spaces.pth]
  rw [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero, h1, h2, h3, h4]
  ring

/-- `bslOp α φ` vanishes outside the (topological) support of `φ`. -/
theorem bslOp_eq_zero_of_notMem_tsupport {α : ℝ} {φ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : (z, θ) ∉ tsupport (Function.uncurry φ)) : Work.Elliptic.bslOp α φ z θ = 0 := by
  have hV : IsOpen (tsupport (Function.uncurry φ))ᶜ := (isClosed_tsupport _).isOpen_compl
  have hEq : Set.EqOn (Function.uncurry φ)
      (Function.uncurry (fun _ _ : ℝ => (0 : ℝ))) (tsupport (Function.uncurry φ))ᶜ := by
    intro p hp
    simp only [Function.uncurry]
    by_contra hne
    exact hp (subset_tsupport _ (Function.mem_support.mpr hne))
  have hcongr := bslOp_congr_of_isOpen (α := α) hV hEq h
  exact hcongr.trans (bslOp_zero α z θ)

end Work.EllipticEst.InteriorRegularity.Q0
end
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.Q0.barPsi_compact =====
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

theorem integrableOn_barPsi_compact {α : ℝ} (hα : 0 < α) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : MeasureTheory.LocallyIntegrableOn (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKs : K ⊆ stripRR) :
    MeasureTheory.IntegrableOn
      (fun q : ℝ × ℝ => if q.2 ∈ Set.Ioo 0 (Real.pi / 2) then Ψ (Real.exp (α * q.1)) q.2 else 0)
      K := by
  -- the image of `K` under `(σ,θ) ↦ (exp (ασ), θ)`
  set Φ : ℝ × ℝ → ℝ × ℝ := fun p => (Real.exp (α * p.1), p.2) with hΦ
  have hΦc : Continuous Φ := by
    rw [hΦ]
    exact (Real.continuous_exp.comp (continuous_fst.const_mul α)).prodMk continuous_snd
  have hK'c : IsCompact (Φ '' K) := hK.image hΦc
  have hK'Q : Φ '' K ⊆ Work.FTS.EllipticEst.Q0 := by
    rintro p ⟨q, hq, rfl⟩
    exact ⟨Real.exp_pos _, (hKs hq).2⟩
  have hΨK' : MeasureTheory.IntegrableOn (Function.uncurry Ψ) (Φ '' K) :=
    hΨ.integrableOn_compact_subset hK'Q hK'c
  -- a cut-off on the `Q0`-side, supported in the image
  classical
  set Y : ℝ × ℝ → ℝ :=
    fun p => if p ∈ Φ '' K then (α * p.1)⁻¹ * Ψ p.1 p.2 else 0 with hY
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (α * p.1)⁻¹) (Φ '' K) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => α * p.1) (Φ '' K) :=
      (continuous_const.mul continuous_fst).continuousOn
    refine h1.inv₀ (fun p hp => ?_)
    have hp1 : 0 < p.1 := by
      obtain ⟨q, hq, hq'⟩ := hp
      have hq1 : (Φ q).1 = Real.exp (α * q.1) := by rw [hΦ]
      rw [← hq', hq1]
      exact Real.exp_pos _
    positivity
  have hIntK' : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Function.uncurry Ψ p * (α * p.1)⁻¹) (Φ '' K) :=
    hΨK'.mul_continuousOn hcont hK'c
  have hYK : MeasureTheory.IntegrableOn Y (Φ '' K) :=
    (integrableOn_congr_fun
      (fun p hp => by simp only [hY, hp, if_true, Function.uncurry]; rw [mul_comm])
      hK'c.measurableSet).mpr hIntK'
  have hYQ : MeasureTheory.IntegrableOn Y Work.FTS.EllipticEst.Q0 := by
    have hsupp : Function.support Y ⊆ Φ '' K := by
      intro p hp
      by_contra hcon
      exact (Function.mem_support.mp hp) (by simp only [hY, hcon, if_false])
    have hind : (Φ '' K).indicator Y = Y := by
      funext p
      by_cases hp : p ∈ Φ '' K
      · rw [Set.indicator_of_mem hp]
      · rw [Set.indicator_of_notMem hp]
        by_contra hne
        exact hp (hsupp (Function.mem_support.mpr (fun h => hne h.symm)))
    have hInt : MeasureTheory.Integrable Y := by
      rw [← hind, integrable_indicator_iff hK'c.measurableSet]
      exact hYK
    exact hInt.integrableOn
  -- transfer to the strip
  have hpull : MeasureTheory.IntegrableOn
      (fun q : ℝ × ℝ => (α * Real.exp (α * q.1)) • Y (Real.exp (α * q.1), q.2)) stripRR :=
    (integrableOn_Q0_iff_strip hα Y).mp hYQ
  have hEq : Set.EqOn (fun q : ℝ × ℝ => (α * Real.exp (α * q.1)) • Y (Real.exp (α * q.1), q.2))
      (fun q : ℝ × ℝ =>
        if q.2 ∈ Set.Ioo 0 (Real.pi / 2) then Ψ (Real.exp (α * q.1)) q.2 else 0) K := by
    intro q hq
    have hq2 : q.2 ∈ Set.Ioo 0 (Real.pi / 2) := (hKs hq).2
    have hmem : (Real.exp (α * q.1), q.2) ∈ Φ '' K := ⟨q, hq, by rw [hΦ]⟩
    simp only [hY, hmem, if_true, hq2, smul_eq_mul]
    have hne : α * Real.exp (α * q.1) ≠ 0 := by positivity
    field_simp
  exact (integrableOn_congr_fun hEq hK.measurableSet).mp (hpull.mono_set hKs)

end Work.EllipticEst.InteriorRegularity.Q0
end
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.Q0.continuousOn_kopDr =====
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

/-- The `σ`-partial derivative of a function of two variables, as a function of the point. -/
def pderivσ (Φ : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun q => deriv (fun σ' => Φ (σ', q.2)) q.1

/-- The `θ`-partial derivative of a function of two variables, as a function of the point. -/
def pderivθ (Φ : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun q => deriv (fun θ' => Φ (q.1, θ')) q.2

/-- The `σ`-partial derivative at a point is `fderiv` applied to the first coordinate vector. -/
lemma pderivσ_eq_fderiv {Φ : ℝ × ℝ → ℝ} {σ θ : ℝ} (hΦ : DifferentiableAt ℝ Φ (σ, θ)) :
    pderivσ Φ (σ, θ) = fderiv ℝ Φ (σ, θ) (1, 0) := by
  show deriv (fun σ' => Φ (σ', θ)) σ = fderiv ℝ Φ (σ, θ) (1, 0)
  have h1 : HasFDerivAt (fun e : ℝ => (e, θ)) (ContinuousLinearMap.inl ℝ ℝ ℝ) σ :=
    hasFDerivAt_prodMk_left σ θ
  have h2 : HasFDerivAt (fun e : ℝ => Φ (e, θ))
      ((fderiv ℝ Φ (σ, θ)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) σ := by
    have h := hΦ.hasFDerivAt.comp σ h1
    simpa [Function.comp_def] using h
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
    using h2.hasDerivAt.deriv

/-- The `θ`-partial derivative at a point is `fderiv` applied to the second coordinate vector. -/
lemma pderivθ_eq_fderiv {Φ : ℝ × ℝ → ℝ} {σ θ : ℝ} (hΦ : DifferentiableAt ℝ Φ (σ, θ)) :
    pderivθ Φ (σ, θ) = fderiv ℝ Φ (σ, θ) (0, 1) := by
  show deriv (fun θ' => Φ (σ, θ')) θ = fderiv ℝ Φ (σ, θ) (0, 1)
  have h1 : HasFDerivAt (fun e : ℝ => (σ, e)) (ContinuousLinearMap.inr ℝ ℝ ℝ) θ :=
    hasFDerivAt_prodMk_right σ θ
  have h2 : HasFDerivAt (fun e : ℝ => Φ (σ, e))
      ((fderiv ℝ Φ (σ, θ)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) θ := by
    have h := hΦ.hasFDerivAt.comp θ h1
    simpa [Function.comp_def] using h
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    using h2.hasDerivAt.deriv

/-- `pderivσ` preserves smoothness. -/
lemma contDiff_pderivσ {Φ : ℝ × ℝ → ℝ} (hΦ : ∀ n : ℕ, ContDiff ℝ n Φ) :
    ∀ n : ℕ, ContDiff ℝ n (pderivσ Φ) := by
  intro n
  have h1 : ContDiff ℝ (n : WithTop ℕ∞)
      (fun p : (ℝ × ℝ) × (ℝ × ℝ) => (fderiv ℝ Φ p.1 : (ℝ × ℝ) →L[ℝ] ℝ) p.2) :=
    (hΦ (n + 1)).contDiff_fderiv_apply (by simp)
  have h2 : ContDiff ℝ (n : WithTop ℕ∞)
      (fun q : ℝ × ℝ => (fderiv ℝ Φ q : (ℝ × ℝ) →L[ℝ] ℝ) ((1 : ℝ), 0)) :=
    h1.comp (ContDiff.prodMk contDiff_id contDiff_const)
  rw [show pderivσ Φ = fun q : ℝ × ℝ => (fderiv ℝ Φ q : (ℝ × ℝ) →L[ℝ] ℝ) ((1 : ℝ), 0) from
    funext fun q => pderivσ_eq_fderiv ((hΦ 1).differentiable (by norm_num) q)]
  exact h2

/-- `pderivθ` preserves smoothness. -/
lemma contDiff_pderivθ {Φ : ℝ × ℝ → ℝ} (hΦ : ∀ n : ℕ, ContDiff ℝ n Φ) :
    ∀ n : ℕ, ContDiff ℝ n (pderivθ Φ) := by
  intro n
  have h1 : ContDiff ℝ (n : WithTop ℕ∞)
      (fun p : (ℝ × ℝ) × (ℝ × ℝ) => (fderiv ℝ Φ p.1 : (ℝ × ℝ) →L[ℝ] ℝ) p.2) :=
    (hΦ (n + 1)).contDiff_fderiv_apply (by simp)
  have h2 : ContDiff ℝ (n : WithTop ℕ∞)
      (fun q : ℝ × ℝ => (fderiv ℝ Φ q : (ℝ × ℝ) →L[ℝ] ℝ) ((0 : ℝ), 1)) :=
    h1.comp (ContDiff.prodMk contDiff_id contDiff_const)
  rw [show pderivθ Φ = fun q : ℝ × ℝ => (fderiv ℝ Φ q : (ℝ × ℝ) →L[ℝ] ℝ) ((0 : ℝ), 1) from
    funext fun q => pderivθ_eq_fderiv ((hΦ 1).differentiable (by norm_num) q)]
  exact h2

/-- **Continuity of the transported operator.**  For a jointly smooth `ψ`, the operator
`kopDr ψ` is continuous on the half-strip `ℝ × (0, π/2)`. -/
theorem continuousOn_kopDr {ψ : ℝ → ℝ → ℝ} (hψ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ)) :
    ContinuousOn (fun q : ℝ × ℝ => kopDr ψ q.1 q.2) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  let s : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)
  change ContinuousOn (fun q : ℝ × ℝ => kopDr ψ q.1 q.2) s
  have hF : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ) := hψ
  have hσ : ∀ n : ℕ, ContDiff ℝ n (pderivσ (Function.uncurry ψ)) := contDiff_pderivσ hF
  have hθ : ∀ n : ℕ, ContDiff ℝ n (pderivθ (Function.uncurry ψ)) := contDiff_pderivθ hF
  have hσσ : ∀ n : ℕ, ContDiff ℝ n (pderivσ (pderivσ (Function.uncurry ψ))) :=
    contDiff_pderivσ hσ
  have hθθ : ∀ n : ℕ, ContDiff ℝ n (pderivθ (pderivθ (Function.uncurry ψ))) :=
    contDiff_pderivθ hθ
  have cF : ContinuousOn (Function.uncurry ψ) s := (hF 0).continuous.continuousOn
  have cσ : ContinuousOn (pderivσ (Function.uncurry ψ)) s := (hσ 0).continuous.continuousOn
  have cθ : ContinuousOn (pderivθ (Function.uncurry ψ)) s := (hθ 0).continuous.continuousOn
  have cσσ : ContinuousOn (pderivσ (pderivσ (Function.uncurry ψ))) s :=
    (hσσ 0).continuous.continuousOn
  have cθθ : ContinuousOn (pderivθ (pderivθ (Function.uncurry ψ))) s :=
    (hθθ 0).continuous.continuousOn
  have hcos : ∀ q ∈ s, Real.cos q.2 ≠ 0 := by
    intro q hq
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, hq.2.1], hq.2.2⟩)
  have ctan : ContinuousOn (fun q : ℝ × ℝ => Real.tan q.2) s :=
    Real.continuousOn_tan.comp continuous_snd.continuousOn hcos
  have hmain : ContinuousOn (fun q : ℝ × ℝ =>
      - pderivσ (pderivσ (Function.uncurry ψ)) q - pderivθ (pderivθ (Function.uncurry ψ)) q
      - 5 * pderivσ (Function.uncurry ψ) q + Real.tan q.2 * pderivθ (Function.uncurry ψ) q
      + ((Real.tan q.2) ^ 2 - 5) * Function.uncurry ψ q) s := by
    have hA : ContinuousOn (fun q : ℝ × ℝ => - pderivσ (pderivσ (Function.uncurry ψ)) q
        - pderivθ (pderivθ (Function.uncurry ψ)) q - 5 * pderivσ (Function.uncurry ψ) q) s :=
      (cσσ.neg.sub cθθ).sub (cσ.const_mul 5)
    have hB : ContinuousOn (fun q : ℝ × ℝ => Real.tan q.2 * pderivθ (Function.uncurry ψ) q
        + ((Real.tan q.2) ^ 2 - 5) * Function.uncurry ψ q) s :=
      (ctan.mul cθ).add (((ctan.pow 2).sub continuousOn_const).mul cF)
    refine (hA.add hB).congr fun q hq => ?_
    simp only [Pi.add_apply]
    ring
  refine hmain.congr fun q hq => ?_
  simp only [kopDr, pderivσ, pderivθ, Function.uncurry]

end Work.EllipticEst.InteriorRegularity.Q0
end
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.Q0.locallyIntegrableOn_Gf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity.Q0

theorem locallyIntegrableOn_Gf {α : ℝ} (hα : 0 < α) {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    MeasureTheory.LocallyIntegrableOn
      (fun x : Work.EllipticEst.InteriorRegularity.E2 =>
        (Work.EllipticEst.InteriorRegularity.Q0.Gf α F x : ℂ))
      Work.EllipticEst.InteriorRegularity.stripE := by
  -- The strip is open (and hence measurable): it is the preimage of `(0, π/2)` under `x ↦ x 1`.
  have hmeas : MeasurableSet Work.EllipticEst.InteriorRegularity.stripE := by
    rw [Work.EllipticEst.InteriorRegularity.stripE]
    exact measurableSet_Ioo.preimage
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) (1 : Fin 2)).measurable
  -- `Gf α F` is `C^∞` on the strip, in particular continuous there; a function continuous on a
  -- measurable set is locally integrable on it.
  exact ((smoothOn_Gf hα hF 0).continuousOn).locallyIntegrableOn hmeas

end Work.EllipticEst.InteriorRegularity.Q0
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.Q0.locallyIntegrableOn_coords_of_stripRR =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity.Q0

open MeasureTheory Set Filter
open scoped Topology

theorem locallyIntegrableOn_coords_of_stripRR {g : ℝ × ℝ → ℂ}
    (hg : MeasureTheory.LocallyIntegrableOn g (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    MeasureTheory.LocallyIntegrableOn
      (fun x : Work.EllipticEst.InteriorRegularity.E2 => g (x 0, x 1))
      Work.EllipticEst.InteriorRegularity.stripE := by
  -- the coordinate identification `(s,θ) ↦ s • e0 + θ • e1` is measure preserving and an embedding
  have hmp : MeasurePreserving (fun p : ℝ × ℝ => coords p.1 p.2)
      (volume : Measure (ℝ × ℝ)) (volume : Measure E2) :=
    Work.EllipticEst.InteriorRegularity.VT.coords_measurePreserving
  have hme : MeasurableEmbedding (fun p : ℝ × ℝ => coords p.1 p.2) :=
    Work.EllipticEst.InteriorRegularity.VT.coords_measurableEmbedding
  rw [MeasureTheory.locallyIntegrableOn_iff
    (Work.EllipticEst.InteriorRegularity.VT.isOpen_stripE).isLocallyClosed]
  intro K hKsub hKc
  -- the coordinate projections of the compact set `K` bound the preimage of `K`
  set A : Set ℝ := (fun x : E2 => x 0) '' K with hA
  set B : Set ℝ := (fun x : E2 => x 1) '' K with hB
  have hAcont : Continuous fun x : E2 => x 0 :=
    PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) (0 : Fin 2)
  have hBcont : Continuous fun x : E2 => x 1 :=
    Work.EllipticEst.InteriorRegularity.VT.continuous_coord_one
  have hAc : IsCompact A := hKc.image hAcont
  have hBc : IsCompact B := hKc.image hBcont
  have hABsub : A ×ˢ B ⊆ Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    refine ⟨trivial, ?_⟩
    rw [hB] at hb
    obtain ⟨x, hxK, hxb⟩ := hb
    rw [← hxb]
    exact hKsub hxK
  have hIntAB : IntegrableOn g (A ×ˢ B) :=
    hg.integrableOn_compact_subset hABsub (hAc.prod hBc)
  -- the preimage of `K` under the coordinate map lies in that rectangle
  have hPre : (fun p : ℝ × ℝ => coords p.1 p.2) ⁻¹' K ⊆ A ×ˢ B := by
    intro p hp
    have hp' : (fun p : ℝ × ℝ => coords p.1 p.2) p ∈ K := hp
    refine ⟨?_, ?_⟩
    · rw [hA]
      exact ⟨coords p.1 p.2, hp', Work.EllipticEst.InteriorRegularity.VT.coords_zero p.1 p.2⟩
    · rw [hB]
      exact ⟨coords p.1 p.2, hp', Work.EllipticEst.InteriorRegularity.VT.coords_one p.1 p.2⟩
  have hIntPre : IntegrableOn g ((fun p : ℝ × ℝ => coords p.1 p.2) ⁻¹' K) :=
    hIntAB.mono_set hPre
  -- the pull-back of `g` along the coordinate map is `g` itself
  have hcomp : (fun x : E2 => g (x 0, x 1)) ∘ (fun p : ℝ × ℝ => coords p.1 p.2) = g := by
    funext p
    obtain ⟨a, b⟩ := p
    exact congrArg g (Prod.ext (Work.EllipticEst.InteriorRegularity.VT.coords_zero a b)
      (Work.EllipticEst.InteriorRegularity.VT.coords_one a b))
  have hIntPre' : IntegrableOn
      ((fun x : E2 => g (x 0, x 1)) ∘ (fun p : ℝ × ℝ => coords p.1 p.2))
      ((fun p : ℝ × ℝ => coords p.1 p.2) ⁻¹' K) := by
    rw [hcomp]
    exact hIntPre
  -- change of variables
  exact (hmp.integrableOn_comp_preimage hme (f := fun x : E2 => g (x 0, x 1))
    (s := K)).mp hIntPre'

end Work.EllipticEst.InteriorRegularity.Q0
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.Q0.stripWeakQ0_of_RR =====
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

/-! ### Elementary facts about `coords` and the strip -/

/-- The coordinate map is a bijection: `coords (x 0) (x 1) = x`. -/
lemma coords_mk (x : E2) : coords (x 0) (x 1) = x := by
  ext i
  fin_cases i <;> simp [coords]

/-- Membership in the strip, in terms of the second coordinate. -/
lemma mem_stripE_iff (σ θ : ℝ) :
    coords σ θ ∈ stripE ↔ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  simp only [stripE, Set.mem_setOf_eq, VT.coords_one]

/-- The preimage of the strip `stripE ⊆ E2` under `coords` is the half-strip `stripRR`. -/
lemma preimage_stripE : (fun q : ℝ × ℝ => coords q.1 q.2) ⁻¹' stripE = stripRR := by
  ext q
  simp only [Set.mem_preimage, mem_stripE_iff, stripRR, Set.mem_prod, Set.mem_univ, true_and]


/-! ### The transported data agree on the strip -/

/-- The transported unknown `VRR` is the pull-back of `Vf` along `coords`. -/
lemma VRR_eq_Vf (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (σ θ : ℝ) :
    VRR α Ψ σ θ = Vf α Ψ (coords σ θ) := by
  by_cases hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
  · rw [VRR, if_pos hθ]
    rw [Vf, Set.indicator_of_mem ((mem_stripE_iff σ θ).mpr hθ)]
    simp only [wt, wtRR, VT.coords_zero, VT.coords_one]
  · rw [VRR, if_neg hθ]
    rw [Vf, Set.indicator_of_notMem (fun h => hθ ((mem_stripE_iff σ θ).mp h))]

/-- The transported source `GRR` is the pull-back of `Gf` along `coords`. -/
lemma GRR_eq_Gf (α : ℝ) (F : ℝ → ℝ → ℝ) (σ θ : ℝ) :
    GRR α F σ θ = Gf α F (coords σ θ) := by
  by_cases hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
  · rw [GRR, if_pos hθ]
    rw [Gf, Set.indicator_of_mem ((mem_stripE_iff σ θ).mpr hθ)]
    simp only [wt, wtRR, VT.coords_zero, VT.coords_one]
  · rw [GRR, if_neg hθ]
    rw [Gf, Set.indicator_of_notMem (fun h => hθ ((mem_stripE_iff σ θ).mp h))]

/-! ### The change of variables `ℝ × ℝ ↔ E2` -/

/-- The coordinate map `q ↦ coords q.1 q.2` is smooth at every order. -/
lemma contDiff_coords : ∀ n : ℕ, ContDiff ℝ n (fun q : ℝ × ℝ => coords q.1 q.2) := by
  intro n
  have h1 : ContDiff ℝ n (fun q : ℝ × ℝ => (fun i : Fin 2 => if i = 0 then q.1 else q.2)) := by
    refine contDiff_pi' (fun i => ?_)
    fin_cases i
    · simpa using (contDiff_fst : ContDiff ℝ n (Prod.fst : ℝ × ℝ → ℝ))
    · simpa using (contDiff_snd : ContDiff ℝ n (Prod.snd : ℝ × ℝ → ℝ))
  have h2 : ContDiff ℝ n (WithLp.toLp 2 : (Fin 2 → ℝ) → E2) := PiLp.contDiff_toLp
  exact h2.comp h1

/-- **Change of variables for the integral.**  Since `coords` is a measure-preserving
measurable embedding `ℝ × ℝ → E2`, the integral over `E2` equals the integral over
`ℝ × ℝ` of the pull-back. -/
lemma coordsIntegral (g : E2 → ℂ) :
    ∫ q : ℝ × ℝ, g (coords q.1 q.2) = ∫ x : E2, g x :=
  MeasureTheory.MeasurePreserving.integral_comp VT.coords_measurePreserving
    VT.coords_measurableEmbedding g

/-! ### The operator identity -/

/-- **The two forms of `bslOp` agree.**  For a smooth `ψ : E2 → ℂ`, the `deriv`-level operator
`kopD` applied to the pull-back `(σ,θ) ↦ ψ (coords σ θ)` is `Kop ψ` evaluated at
`coords σ θ`. -/
lemma kopD_coords_aux {ψ : E2 → ℂ} (hψ : ∀ n : ℕ, ContDiff ℝ n ψ) (σ θ : ℝ) :
    kopD (fun σ θ => ψ (coords σ θ)) σ θ = Kop ψ (coords σ θ) := by
  have hsm : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry (fun σ θ : ℝ => ψ (coords σ θ))) := by
    intro n
    exact (hψ n).comp (contDiff_coords n)
  have hcur : curryC (fun σ θ : ℝ => ψ (coords σ θ)) = ψ := by
    funext x
    simp only [curryC]
    rw [coords_mk]
  obtain ⟨-, hd0, hd1, hd2⟩ := curryC_bridge hsm
  have h0 := hd0 (coords σ θ)
  have h1 := hd1 (coords σ θ)
  have h2 := hd2 (coords σ θ)
  simp only [hcur] at h0 h1 h2
  rw [VT.coords_zero, VT.coords_one] at h0 h1 h2
  have hA : d0 ψ (coords σ θ) = deriv (fun s => ψ (coords s θ)) σ := h0
  have hB : d1 ψ (coords σ θ) = deriv (fun θ' => ψ (coords σ θ')) θ := h1
  have hAB : d0 (d0 ψ) (coords σ θ) + d1 (d1 ψ) (coords σ θ)
      = deriv (fun s => deriv (fun s' => ψ (coords s' θ)) s) σ
        + deriv (fun θ' => deriv (fun θ'' => ψ (coords σ θ'')) θ') θ := h2
  simp only [kopD, Kop]
  rw [VT.coords_one]
  rw [← hA, ← hB]
  linear_combination hAB

/-! ### Pulling a test function back to the half-strip -/

/-- Every smooth compactly supported `ψ : E2 → ℂ` whose topological support lies in `stripE`
pulls back along `coords` to a smooth compactly supported `φ : ℝ → ℝ → ℂ` whose topological
support lies in the half-strip `stripRR`. -/
lemma uncurryCoords_aux {ψ : E2 → ℂ} (hψ : ∀ n : ℕ, ContDiff ℝ n ψ)
    (hc : HasCompactSupport ψ) (hts : tsupport ψ ⊆ stripE) :
    ∃ φ : ℝ → ℝ → ℂ, (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) ∧
      HasCompactSupport (Function.uncurry φ) ∧
      tsupport (Function.uncurry φ) ⊆ stripRR ∧
      (∀ σ θ, φ σ θ = ψ (coords σ θ)) := by
  have hfinv_cont : Continuous (fun x : E2 => (x 0, x 1)) :=
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) (0 : Fin 2)).prodMk
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) (1 : Fin 2))
  have hsub : tsupport (fun q : ℝ × ℝ => ψ (coords q.1 q.2))
      ⊆ (fun q : ℝ × ℝ => coords q.1 q.2) ⁻¹' tsupport ψ := by
    rw [tsupport]
    refine closure_minimal ?_ (isClosed_closure.preimage VT.continuous_coords)
    intro q hq
    have hq' : ψ (coords q.1 q.2) ≠ 0 := by simpa [Function.mem_support] using hq
    exact subset_tsupport ψ (by simpa [Function.mem_support] using hq')
  refine ⟨fun σ θ => ψ (coords σ θ), ?_, ?_, ?_, fun σ θ => rfl⟩
  · intro n
    exact (hψ n).comp (contDiff_coords n)
  · rw [HasCompactSupport]
    refine IsCompact.of_isClosed_subset (hc.image hfinv_cont) isClosed_closure ?_
    intro q hq
    refine ⟨(fun q : ℝ × ℝ => coords q.1 q.2) q, hsub hq, ?_⟩
    simp [VT.coords_zero, VT.coords_one]
  · intro q hq
    have h1 : q ∈ (fun q : ℝ × ℝ => coords q.1 q.2) ⁻¹' stripE :=
      preimage_mono hts (hsub hq)
    rwa [preimage_stripE] at h1

/-! ### The main implication -/

theorem stripWeakQ0_of_RR {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.EllipticEst.InteriorRegularity.Q0.StripWeakRR
      (fun σ θ => (Work.EllipticEst.InteriorRegularity.Q0.VRR α Ψ σ θ : ℂ))
      (fun σ θ => (Work.EllipticEst.InteriorRegularity.Q0.GRR α F σ θ : ℂ))) :
    Work.EllipticEst.InteriorRegularity.Q0.StripWeakQ0 α
      (Work.EllipticEst.InteriorRegularity.Q0.Vf α Ψ)
      (Work.EllipticEst.InteriorRegularity.Q0.Gf α F) := by
  intro ψ hψ hc hts
  obtain ⟨φ, hφsm, hφc, hφts, hφeq⟩ := uncurryCoords_aux hψ hc hts
  have hφfun : φ = fun σ θ => ψ (coords σ θ) := funext fun σ => funext fun θ => hφeq σ θ
  have hRR := h φ hφsm hφc hφts
  have hptL : ∀ q : ℝ × ℝ, (VRR α Ψ q.1 q.2 : ℂ) * kopD φ q.1 q.2
      = (Vf α Ψ (coords q.1 q.2) : ℂ) * Kop ψ (coords q.1 q.2) := by
    intro q
    rw [VRR_eq_Vf, hφfun, kopD_coords_aux hψ q.1 q.2]
  have hptR : ∀ q : ℝ × ℝ, (GRR α F q.1 q.2 : ℂ) * φ q.1 q.2
      = (Gf α F (coords q.1 q.2) : ℂ) * ψ (coords q.1 q.2) := by
    intro q
    rw [GRR_eq_Gf, hφeq q.1 q.2]
  have hL : (∫ q : ℝ × ℝ, (VRR α Ψ q.1 q.2 : ℂ) * kopD φ q.1 q.2)
      = ∫ x : E2, (Vf α Ψ x : ℂ) * Kop ψ x := by
    rw [show (∫ q : ℝ × ℝ, (VRR α Ψ q.1 q.2 : ℂ) * kopD φ q.1 q.2)
        = ∫ q : ℝ × ℝ, (Vf α Ψ (coords q.1 q.2) : ℂ) * Kop ψ (coords q.1 q.2)
        from MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hptL)]
    exact coordsIntegral (fun x : E2 => (Vf α Ψ x : ℂ) * Kop ψ x)
  have hR : (∫ q : ℝ × ℝ, (GRR α F q.1 q.2 : ℂ) * φ q.1 q.2)
      = ∫ x : E2, (Gf α F x : ℂ) * ψ x := by
    rw [show (∫ q : ℝ × ℝ, (GRR α F q.1 q.2 : ℂ) * φ q.1 q.2)
        = ∫ q : ℝ × ℝ, (Gf α F (coords q.1 q.2) : ℂ) * ψ (coords q.1 q.2)
        from MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hptR)]
    exact coordsIntegral (fun x : E2 => (Gf α F x : ℂ) * ψ x)
  rw [← hL, ← hR]
  exact hRR

end Work.EllipticEst.InteriorRegularity.Q0
end
end
-- ===== merged: Submission.Work.EllipticEst.InteriorRegularity.VT.TransportDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.EllipticEst.InteriorRegularity.VT

set_option autoImplicit false

/-! ## The substitution and the candidate representative -/




/-- The substitution `(s,θ) ↦ (e^{αs},θ)` of the half-strip onto the quadrant. -/
def TsubV (α : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (Real.exp (α * p.1), p.2)


/-! ## Elementary facts about the substitution -/






/-- The substitution `(s,θ) ↦ (e^{αs},θ)` is differentiable everywhere. -/
lemma differentiable_TsubV (α : ℝ) : Differentiable ℝ (TsubV α) :=
  (Differentiable.exp (differentiable_fst.const_mul α)).prodMk differentiable_snd

/-! ## The weight factor at the inverse substitution -/





/-- The transported unknown `Ws α Ψ`, read at a point `coords s θ` of the strip coordinates. -/
@[simp] lemma Ws_coords (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (s θ : ℝ) :
    Ws α Ψ (coords s θ) = ((wt α (coords s θ) * Ψ (Real.exp (α * s)) θ : ℝ) : ℂ) := by
  simp [Ws, coords_zero, coords_one]

/-! ## Smoothness of the coordinate map -/

theorem contDiff_coords {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun p : ℝ × ℝ => coords p.1 p.2) := by
  have h : (fun p : ℝ × ℝ => coords p.1 p.2) =
      fun p : ℝ × ℝ => p.1 • e0 + p.2 • e1 := by
    funext p
    ext i
    fin_cases i <;> simp [coords, e0, e1]
  rw [h]
  exact (contDiff_fst.smul contDiff_const).add (contDiff_snd.smul contDiff_const)

end Work.EllipticEst.InteriorRegularity.VT
end
end
-- ===== merged: Submission.Work.FTS.ClassC.HkMem_of_pure_and_vanishing =====
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
set_option maxHeartbeats 1000000

/-! ## The vanishing-weight plain-slot integrand -/

/-- The *vanishing-weight* plain-slot integrand of the sharp reduction:
`(D_z^l ∂_θ^r f z θ · w(z))² · sin(2θ)^{2r-γ}`.  Its angular weight vanishes at the
endpoints as soon as `r ≥ 1` (because `2r - γ ≥ 2 - γ > 0`). -/
def vig (α : ℝ) (f : ℝ → ℝ → ℝ) (r j : ℕ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ * Work.Spaces.w z) ^ 2
    * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α)

/-- `vig` with the two squares separated (the shape produced by
`mixedSlot_vanishing_weight_domination`). -/
theorem vig_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (r j : ℕ) (z θ : ℝ) :
    vig α f r j z θ
      = (Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α) := by
  rw [vig, mul_pow]

/-- `sin (2θ) ≥ 0` on `Iθ`. -/
theorem sin_two_nonneg_of_mem_Iθ' {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  have h1 : 0 ≤ 2 * θ := by linarith [hθ.1]
  have h2 : 2 * θ ≤ Real.pi := by linarith [hθ.2]
  exact Real.sin_nonneg_of_nonneg_of_le_pi h1 h2


/-! ## The per-slot constant of the sharp domination -/

/-- The constant of the sharp domination for the slot `(i,j)` (`1 ≤ i`). -/
def vanC (α : ℝ) (hα : 0 < α) (hγ : Work.Spaces.gam α ≤ 3 / 2) (f : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (i j : ℕ) (hi : 1 ≤ i) : ℝ :=
  Classical.choose (mixedSlot_vanishing_weight_domination hα hγ hsm i j hi)

theorem vanC_pos (α : ℝ) (hα : 0 < α) (hγ : Work.Spaces.gam α ≤ 3 / 2) (f : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (i j : ℕ) (hi : 1 ≤ i) :
    0 < vanC α hα hγ f hsm i j hi :=
  (Classical.choose_spec (mixedSlot_vanishing_weight_domination hα hγ hsm i j hi)).1

/-- The sharp domination in the `vig` notation. -/
theorem vanC_spec (α : ℝ) (hα : 0 < α) (hγ : Work.Spaces.gam α ≤ 3 / 2) (f : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (i j : ℕ) (hi : 1 ≤ i) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ vanC α hα hγ f hsm i j hi * ∑ r ∈ Finset.Icc 1 i, vig α f r j z θ := by
  intro z hz θ hθ
  refine le_trans
    ((Classical.choose_spec (mixedSlot_vanishing_weight_domination hα hγ hsm i j hi)).2
      z hz θ hθ) ?_
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (vanC_pos α hα hγ f hsm i j hi))
  exact le_of_eq (Finset.sum_congr rfl fun r _ => (vig_eq α f r j z θ).symm)

/-! ## The reduction -/


end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.ClassC.NormPiecesAux.zsqPz2_DzIter_eqOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC.NormPiecesAux

/-- `D_z^i` commutes with `z²∂_z² = D_z² − D_z` **on the open quadrant**, i.e.
`D_z^i (z² ∂_z² Ψ) = z² ∂_z² (D_z^i Ψ)` there (`zsqPz2 g := z^2 * pzIter 2 g` is the
abbreviation `Work.FTS.EllipticEst.DzAmgm.zsqPz2`; the statement above writes it out).

Route.  Induction on `i`.  The base is `rfl`.  For the step use
`DzAmgm.zsqPz2_Dz : Set.EqOn (uncurry (zsqPz2 (Dz g))) (uncurry (Dz (zsqPz2 g))) Q0` with
`g := DzIter i Ψ` (`SmoothOpen (DzIter i Ψ)` from `hΨ.DzIter i`), so that on `Q0`
`z²∂_z²(DzIter (i+1) Ψ) = D_z (z²∂_z²(DzIter i Ψ))`; the induction hypothesis gives the pointwise
equality with `D_z (DzIter i (z²∂_z² Ψ))` on `Q0`, and the two are identified by
`Work.FTS.H2.Dz_congr_of_isOpen` (`Set.EqOn`-congruence of `D_z` on an open set, which is
`Work.Spaces.pz_congr_of_isOpen`).  Everything is definitional after unfolding
`DzIter_succ`. -/
theorem zsqPz2_DzIter_eqOn (Ψ : ℝ → ℝ → ℝ) (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) (i : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter i (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        = z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter i Ψ) z θ := by
  intro z θ hz hθ hπ
  -- The goal is the symmetric form of the commuting identity `Qop_DzIter_eq` for
  -- `Qop = z²∂_z²` — which is the definitional unfolding of `zsqPz2` — read off at the
  -- point `(z,θ)` of the open quadrant `Q0 = (0,∞) × (0,π/2)`.
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hπ⟩
  have h := Work.FTS.EllipticEst.DzAmgm.Qop_DzIter_eq (g := Ψ) hΨ i hp
  exact h.symm

end Work.FTS.ClassC.NormPiecesAux
end
-- ===== merged: Submission.Work.FTS.ClassCHon.LzeroSliceDzIter =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassCHon

set_option autoImplicit false

/-- `D_z^{j+i} = D_z^j ∘ D_z^i`. -/
theorem DzIter_add (j i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter (j + i) f = Work.Spaces.DzIter j (Work.Spaces.DzIter i f) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Nat.succ_add, Work.Spaces.DzIter_succ, ih]
      rfl

/-- **The `θ`-ODE of the `D_z`-iterate.**  If `Ψ` is smooth on the open quadrant and
`bslOp α Ψ = F` there, then for every `a` the slice `θ ↦ D_z^a Ψ(z,θ)` solves

`Lzero1 (D_z^a Ψ(z,·)) = D_z^a F(z,·) + α² D_z^{a+2}Ψ(z,·) + 5α D_z^{a+1}Ψ(z,·)`

on `(0,π/2)`. -/
theorem lzero1_slice_DzIter {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hEq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ) (a : ℕ) :
    ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.FTS.EllipticEst.Lzero1 (fun t => Work.Spaces.DzIter a Ψ z t) θ
        = Work.Spaces.DzIter a F z θ + α ^ 2 * Work.Spaces.DzIter (a + 2) Ψ z θ
          + 5 * α * Work.Spaces.DzIter (a + 1) Ψ z θ := by
  intro z hz θ hθ0 hθ1
  have hsmForall : ∀ n : ℕ,
      ContDiffOn ℝ n (Function.uncurry Ψ)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ).mp hsm
  -- the equation for the shifted datum
  have hShift : ∀ z', 0 < z' → ∀ θ', 0 < θ' → θ' < Real.pi / 2 →
      Work.Elliptic.bslOp α (Work.Spaces.DzIter a Ψ) z' θ'
        = Work.Spaces.DzIter a F z' θ' :=
    Work.FTS.EllipticEst.TT.bslOp_DzIter_eq α F Ψ a hsmForall hEq
  have hmain := Work.FTS.EllipticEst.TT.Lzero_eq_of_bsl (α := α) (F := Work.Spaces.DzIter a F)
    (Ψ := Work.Spaces.DzIter a Ψ) (hsm.DzIter a) hShift z hz θ hθ0 hθ1
  -- identify the two `D_z`-iterates of the shifted datum
  have h2 : Work.Spaces.DzIter 2 (Work.Spaces.DzIter a Ψ)
      = Work.Spaces.DzIter (a + 2) Ψ := by
    rw [show Work.Spaces.DzIter 2 (Work.Spaces.DzIter a Ψ)
        = Work.Spaces.DzIter (2 + a) Ψ from (DzIter_add 2 a Ψ).symm]
    rw [show 2 + a = a + 2 from by omega]
  rw [h2] at hmain
  rw [← Work.Spaces.DzIter_succ a Ψ] at hmain
  exact hmain

end Work.FTS.ClassCHon
end
end
-- ===== merged: Submission.Work.FTS.ClassCHon.SliceMassUpgrade.piece_mass_lt_top =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

namespace Work.FTS.ClassCHon.SliceMassUpgrade

/-! ## The measurability of a `τ`-weighted slice density

The up-estimate `sliceMass_lintegral_up_gen` and the a.e.-finiteness upgrade both need the
almost-everywhere measurability of `(z,θ) ↦ ofReal (τ θ · X(z,θ)²)` for the product measure
`(volume ↾ (0,∞)) ⊗ (volume ↾ (0,π/2))`, where `τ` is only assumed `ContinuousOn (0,π/2)`
(not globally measurable) and `X` is continuous on the open quadrant.  Both functions are
continuous on the open quadrant — `τ` because the second coordinate stays inside `(0,π/2)` —
and the product measure is the restriction of the planar Lebesgue measure to the quadrant, so
continuity on a measurable set gives a.e.-strong-measurability. -/

theorem aemeasurable_tau_mul_sq {X : ℝ → ℝ → ℝ} {τ : ℝ → ℝ}
    (hX : ContinuousOn (fun p : ℝ × ℝ => X p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hτc : ContinuousOn τ (Set.Ioo 0 (π / 2))) :
    AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (τ p.2 * (X p.1 p.2) ^ 2))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2)))) := by
  have hQ0 : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    (isOpen_Ioi.prod isOpen_Ioo).measurableSet
  -- the product of the two restricted Lebesgue measures *is* the planar Lebesgue measure
  -- restricted to the open quadrant
  have hvol : ((volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
      = (volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2))) := by
    show (volume.prod volume).restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))
      = (volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2)))
    rw [Measure.prod_restrict]
  have hXaesm : AEStronglyMeasurable (fun p : ℝ × ℝ => X p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2)))) :=
    hvol ▸ hX.aestronglyMeasurable hQ0
  have hτcont : ContinuousOn (fun p : ℝ × ℝ => τ p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hτc.comp continuous_snd.continuousOn (fun p hp => hp.2)
  have hτaesm : AEStronglyMeasurable (fun p : ℝ × ℝ => τ p.2)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2)))) :=
    hvol ▸ (hτcont.aestronglyMeasurable hQ0)
  have hXsq : AEMeasurable (fun p : ℝ × ℝ => (X p.1 p.2) ^ 2)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2)))) :=
    hXaesm.aemeasurable.pow aemeasurable_const
  have hprod : AEMeasurable (fun p : ℝ × ℝ => τ p.2 * (X p.1 p.2) ^ 2)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2)))) :=
    hτaesm.aemeasurable.mul hXsq
  exact hprod.ennreal_ofReal

/-! ## The every-`z` finiteness of the `τ`-weighted slice mass

This is the `τ`-weighted analogue of `sliceMass_lintegral_lt_top_of_outer`, with `hmeas` /
`hmeasmine` replaced by the measurability supplied by the continuity of `τ`
(`aemeasurable_tau_mul_sq`). -/

theorem piece_mass_lt_top {g : ℝ → ℝ → ℝ} {τ : ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hτc : ContinuousOn τ (Set.Ioo 0 (π / 2)))
    (hτ : ∀ θ ∈ Set.Ioo 0 (π / 2), 0 ≤ τ θ)
    (hO0 : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (τ θ * (g z θ) ^ 2)) < ⊤)
    (hO1 : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (τ θ * (z * Work.Spaces.pz g z θ) ^ 2)) < ⊤) :
    ∀ z ∈ Set.Ioi 0,
      (∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (τ θ * (g z θ) ^ 2)) < ⊤ := by
  intro z hz
  have hzpos : 0 < z := hz
  -- the two a.e.-measurabilities (of the `g`-density and of the `z ∂_z g`-density)
  have hmeas_pz : AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (τ p.2 * (Work.Spaces.pz g p.1 p.2) ^ 2))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2)))) :=
    aemeasurable_tau_mul_sq (hg.pz).continuousOn hτc
  have hmeas_g : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (τ p.2 * (g p.1 p.2) ^ 2))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2)))) :=
    aemeasurable_tau_mul_sq hg.continuousOn hτc
  have hmeasmine : AEMeasurable (fun z => ∫⁻ θ in Set.Ioo 0 (π / 2),
      ENNReal.ofReal (τ θ * (g z θ) ^ 2)) (volume.restrict (Set.Ioi 0)) :=
    hmeas_g.lintegral_prod_right'
  -- a.e. finiteness of the slice mass from the outer bound `hO0`
  have haefin : ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)),
      (∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (τ θ * (g t θ) ^ 2)) < ⊤ :=
    MeasureTheory.ae_lt_top' hmeasmine (ne_of_lt hO0)
  have hpos : 0 < z / 2 := by linarith
  have hlt : z / 2 < z := by linarith
  have hae0 : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioi (0 : ℝ) →
      (∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (τ θ * (g t θ) ^ 2)) < ⊤ :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mp haefin
  have hae_sub : ∀ᵐ t ∂(volume.restrict (Set.Ioo (z / 2) z)),
      (∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (τ θ * (g t θ) ^ 2)) < ⊤ := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hae0] with t ht htm
    exact ht (lt_of_lt_of_le hpos (le_of_lt htm.1))
  -- a good (finite) radius `z₁ ∈ (z/2, z)`
  obtain ⟨z₁, hz₁mem, hz₁fin⟩ := exists_lt_top_of_ae_lt_top hlt hae_sub
  have hz₁pos : 0 < z₁ := by linarith [hz₁mem.1]
  have hz₁le : z₁ ≤ z := le_of_lt hz₁mem.2
  -- the up-estimate at `(z₁, z)`, with the pointwise Cauchy–Schwarz bound and the
  -- `∂_z`-mass comparison both for the general weight `τ`
  refine lt_of_le_of_lt (sliceMass_lintegral_up_gen hg hτ hmeas_pz
    (fun z₁ z₂ θ hz₁ hz₁₂ hθ => ?_) (fun z₁ s hz₁ hz₁s => ?_) hz₁pos hz₁le) ?_
  · simpa only [mul_assoc] using ofReal_sliceMass_pointwise_gen hg hτ hz₁ hz₁₂ hθ
  · exact sliceMass_dz_comparison_gen hz₁ hz₁s
  · refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
    · exact ENNReal.mul_lt_top (by norm_num) hz₁fin
    · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hO1

end Work.FTS.ClassCHon.SliceMassUpgrade
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollConvDefs =====
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

/-- The datum `G` killed outside the *open* quadrant.  All the hypotheses of `TraceClass` and
`FourInts` concern the open quadrant (and the two boundary lines, where `TraceClass` provides
the values), so `Gquad G` may be used in place of `G` when the arguments of `Qext` are known
to lie in `(0,π/2)`. -/
def Gquad (G : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => if θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) then G z θ else 0

/-- The uncurried integrand of the double mollification, `(t,s) ↦ Qext G (exp t) s`. -/
def Hxy (G : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => Work.FTS.EllSol.PkgK5.K5c.Qext G (Real.exp p.1) p.2

/-- The two-dimensional mollifier `(t,s) ↦ sKer δ t · sKer ε s` (`t` is the logarithmic radial
variable, `s` the angular one). -/
def Kd (δ ε : ℝ) : ℝ × ℝ → ℝ :=
  fun p => Work.FTS.EllSol.PkgK5.K5c.sKer δ p.1 * Work.FTS.EllSol.PkgK5.K5c.sKer ε p.2

/-- The angular slice functional `∫_{Iθ} (∂_θ²G(w,θ))² σ_η(θ)` (without the radial weight). -/
def E2sl (G : ℝ → ℝ → ℝ) (w : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2
    * Work.FTS.EllipticEst.thEta θ

/-- **The dominating function of the slice.**  `MG G w` bounds `|G w τ|` uniformly for
`τ ∈ (0,π/2)`; it is built from the two interior values at `θ = π/4` (continuous, hence locally
bounded, in `w`) and the square root of the slice functional `E2sl G w` (locally integrable in
`w` by Cauchy–Schwarz from the `ttIntS`-integrability hypothesis). -/
def MG (G : ℝ → ℝ → ℝ) (w : ℝ) : ℝ :=
  |G w (Real.pi / 4)| + |Work.Spaces.pth G w (Real.pi / 4)| + Real.sqrt (E2sl G w)

/-- The half strip which is the domain of the strip-admissibility predicate. -/
def Strp : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)

end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_data =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Elementary one-dimensional and angular facts -/

/-- `√a ≤ 1 + a` for `a ≥ 0`. -/
private theorem sqrt_le_one_add_self {a : ℝ} (ha : 0 ≤ a) : Real.sqrt a ≤ 1 + a := by
  have h : a ≤ (1 + a) ^ 2 := by nlinarith
  calc Real.sqrt a ≤ Real.sqrt ((1 + a) ^ 2) := Real.sqrt_le_sqrt h
    _ = 1 + a := Real.sqrt_sq (by linarith)

/-- The squared radial weight is at least `1`. -/
private theorem one_le_w_sq {w : ℝ} (hw : 0 < w) : 1 ≤ (Work.Spaces.w w) ^ 2 := by
  have h : 1 ≤ Work.Spaces.w w := by
    rw [Work.Spaces.w, one_le_div (by positivity : (0 : ℝ) < w ^ 2)]
    nlinarith
  calc (1 : ℝ) = 1 ^ 2 := by norm_num
    _ ≤ (Work.Spaces.w w) ^ 2 := pow_le_pow_left₀ (by norm_num) h 2

/-- On the open angular interval the weight `σ_η` is at least `1`. -/
private theorem one_le_thEta_of_mem_Ioo_prv {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.thEta θ := by
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hneg : -(Work.Spaces.eta) ≤ 0 := by rw [Work.Spaces.eta]; norm_num
  have h := Real.rpow_le_rpow_of_nonpos hs0 hs1 hneg
  rw [Real.one_rpow] at h
  simpa [Work.FTS.EllipticEst.thEta] using h

/-- Almost every point of `Iθ` is an interior point. -/
private theorem ae_mem_Ioo_Iθ : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
    θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [Work.Spaces.Iθ, ← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2))]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- The angular weight is at least `1` almost everywhere on `Iθ`. -/
private theorem one_le_thEta_ae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
    1 ≤ Work.FTS.EllipticEst.thEta θ := by
  filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
  exact one_le_thEta_of_mem_Ioo_prv hθ

/-! ## Continuity of a slice from interior continuity and the two endpoint traces -/

/-- A slice which is continuous on the open interval `(0, π/2)`, vanishes at both endpoints
and has vanishing one-sided traces there, is continuous on the closed interval `Iθ`. -/
private theorem continuousOn_Iθ_of_traces {F : ℝ → ℝ → ℝ} {w : ℝ}
    (hopen : ContinuousOn (fun s : ℝ => F w s) (Set.Ioo 0 (Real.pi / 2)))
    (hval0 : F w 0 = 0)
    (htr0 : Tendsto (fun θ : ℝ => F w θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hvalpi : F w (Real.pi / 2) = 0)
    (htrpi : Tendsto (fun θ : ℝ => F w θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    ContinuousOn (fun s : ℝ => F w s) Work.Spaces.Iθ := by
  show ContinuousOn (fun s : ℝ => F w s) (Set.Icc 0 (Real.pi / 2))
  have hL0 : ContinuousWithinAt (fun θ : ℝ => F w θ) (Set.Ioi 0) 0 := by
    rw [ContinuousWithinAt, hval0]
    exact htr0
  have hLpi : ContinuousWithinAt (fun θ : ℝ => F w θ) (Set.Iio (Real.pi / 2)) (Real.pi / 2) := by
    rw [ContinuousWithinAt, hvalpi]
    exact htrpi
  have hj0 : ContinuousWithinAt (fun s : ℝ => F w s) (Set.Icc 0 (Real.pi / 2)) 0 :=
    (continuousWithinAt_Ioi_iff_Ici.mp hL0).mono (fun x hx => hx.1)
  have hjpi : ContinuousWithinAt (fun s : ℝ => F w s) (Set.Icc 0 (Real.pi / 2)) (Real.pi / 2) :=
    (continuousWithinAt_Iio_iff_Iic.mp hLpi).mono (fun x hx => hx.2)
  intro θ hθ
  rcases lt_trichotomy θ 0 with h | h | h
  · exact absurd hθ.1 (not_le.mpr h)
  · subst h; exact hj0
  · rcases lt_trichotomy θ (Real.pi / 2) with h2 | h2 | h2
    · exact (hopen.continuousAt (isOpen_Ioo.mem_nhds ⟨h, h2⟩)).continuousWithinAt
    · subst h2; exact hjpi
    · exact absurd hθ.2 (not_le.mpr h2)

/-! ## The vanishing endpoint values of `D_z`-derivatives -/

/-- If a datum vanishes identically at `θ = 0`, then so does `D_z` of it: the `θ = 0` slice is
the constant `0` in the radial variable, so its radial derivative vanishes. -/
private theorem dz_zero_of_slice_zero {F : ℝ → ℝ → ℝ} (hF : ∀ z : ℝ, F z 0 = 0) (z : ℝ) :
    Work.Spaces.Dz F z 0 = 0 := by
  have hslice : (fun z' : ℝ => F z' 0) = fun _ : ℝ => (0 : ℝ) := funext hF
  have hpz : Work.Spaces.pz F z 0 = 0 := by
    show deriv (fun z' : ℝ => F z' 0) z = 0
    rw [hslice, deriv_const]
  rw [Work.Spaces.Dz, hpz, mul_zero]

/-- The `θ = π/2` analogue. -/
private theorem dz_zero_pi_of_slice_zero {F : ℝ → ℝ → ℝ} (hF : ∀ z : ℝ, F z (Real.pi / 2) = 0)
    (z : ℝ) : Work.Spaces.Dz F z (Real.pi / 2) = 0 := by
  have hslice : (fun z' : ℝ => F z' (Real.pi / 2)) = fun _ : ℝ => (0 : ℝ) := funext hF
  have hpz : Work.Spaces.pz F z (Real.pi / 2) = 0 := by
    show deriv (fun z' : ℝ => F z' (Real.pi / 2)) z = 0
    rw [hslice, deriv_const]
  rw [Work.Spaces.Dz, hpz, mul_zero]

/-! ## The target -/

theorem slice_data {G : ℝ → ℝ → ℝ} (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G) :
    (∀ w : ℝ, 0 < w → ContinuousOn (fun s : ℝ => G w s) Work.Spaces.Iθ) ∧
    (∀ w : ℝ, 0 < w → ContinuousOn (fun s : ℝ => Work.Spaces.Dz G w s) Work.Spaces.Iθ) ∧
    (∀ w : ℝ, Work.Spaces.Dz G w 0 = 0) ∧ (∀ w : ℝ, Work.Spaces.Dz G w (Real.pi / 2) = 0) ∧
    (∀ w : ℝ, Work.Spaces.Dz (Work.Spaces.Dz G) w 0 = 0) ∧
    (∀ w : ℝ, Work.Spaces.Dz (Work.Spaces.Dz G) w (Real.pi / 2) = 0) ∧
    (∀ w : ℝ, 0 < w → MeasureTheory.IntegrableOn (fun s : ℝ => Work.Spaces.Dz (Work.Spaces.Dz G) w s) Work.Spaces.Iθ) := by
  obtain ⟨hsm, h0, hpi, htr0, htrpi, hdz0, hdzpi, hhon⟩ := hT
  -- the endpoint *values* of the two `D_z`-derivatives (structural, from `G z 0 = G z (π/2) = 0`)
  have hDz0' : ∀ z : ℝ, Work.Spaces.Dz G z 0 = 0 := fun z => dz_zero_of_slice_zero h0 z
  have hDzpi' : ∀ z : ℝ, Work.Spaces.Dz G z (Real.pi / 2) = 0 :=
    fun z => dz_zero_pi_of_slice_zero hpi z
  have hD2_0 : ∀ z : ℝ, Work.Spaces.Dz (Work.Spaces.Dz G) z 0 = 0 :=
    fun z => dz_zero_of_slice_zero hDz0' z
  have hD2_pi : ∀ z : ℝ, Work.Spaces.Dz (Work.Spaces.Dz G) z (Real.pi / 2) = 0 :=
    fun z => dz_zero_pi_of_slice_zero hDzpi' z
  refine ⟨?_, ?_, hDz0', hDzpi', hD2_0, hD2_pi, ?_⟩
  · -- continuity of the slice of `G` itself
    intro w hw
    exact continuousOn_Iθ_of_traces ((hsm.curry_θ hw).continuousOn) (h0 w) (htr0 w hw) (hpi w)
      (htrpi w hw)
  · -- continuity of the slice of `D_zG`: the trace hypotheses of `TraceClass` give the endpoints
    intro w hw
    refine continuousOn_Iθ_of_traces ?_ (hDz0' w) (hdz0 w hw) (hDzpi' w) (hdzpi w hw)
    have h := ((hsm.pz).curry_θ hw).continuousOn
    simpa only [Work.Spaces.Dz] using h.const_mul w
  · -- integrability of the slice of `D_z²G`, from the honest second-order slice energy
    intro w hw
    have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ]
      exact MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
        (by simp)
    have hbulk : IntegrableOn (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2
        * (Work.Spaces.w w) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := hhon.2.1 w hw
    have hdom : IntegrableOn (fun θ : ℝ => 1 + (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2
        * (Work.Spaces.w w) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := hone.add hbulk
    have haesm : AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.Dz (Work.Spaces.Dz G) w θ)
        (volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => Work.Spaces.Dz (Work.Spaces.Dz G) p.1 p.2)
        (hsm.DzIter 2).continuousOn hw
    refine hdom.mono' haesm ?_
    filter_upwards [one_le_thEta_ae] with θ hθ1
    have hA0 : 0 ≤ (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2 := sq_nonneg _
    have hc1 : 1 ≤ (Work.Spaces.w w) ^ 2 := one_le_w_sq hw
    have hB0 : 0 ≤ (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2 * (Work.Spaces.w w) ^ 2
        * Work.FTS.EllipticEst.thEta θ := mul_nonneg (mul_nonneg hA0 (by linarith)) (by linarith)
    have hkey : (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2
        ≤ (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2 * (Work.Spaces.w w) ^ 2
          * Work.FTS.EllipticEst.thEta θ := by
      calc (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2
          ≤ (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2 * (Work.Spaces.w w) ^ 2 :=
            le_mul_of_one_le_right hA0 hc1
        _ ≤ (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2 * (Work.Spaces.w w) ^ 2
              * Work.FTS.EllipticEst.thEta θ :=
            le_mul_of_one_le_right (mul_nonneg hA0 (by linarith)) hθ1
    have hbd : |Work.Spaces.Dz (Work.Spaces.Dz G) w θ|
        ≤ 1 + (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2 * (Work.Spaces.w w) ^ 2
          * Work.FTS.EllipticEst.thEta θ := by
      calc |Work.Spaces.Dz (Work.Spaces.Dz G) w θ|
          = Real.sqrt ((Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2) := by
            rw [Real.sqrt_sq_eq_abs]
        _ ≤ Real.sqrt ((Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2 * (Work.Spaces.w w) ^ 2
              * Work.FTS.EllipticEst.thEta θ) := Real.sqrt_le_sqrt hkey
        _ ≤ 1 + (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2 * (Work.Spaces.w w) ^ 2
              * Work.FTS.EllipticEst.thEta θ := sqrt_le_one_add_self hB0
    simpa only [Pi.add_apply, Real.norm_eq_abs] using hbd

end Work.FTS.EllSol.EllPkgAux.MollDom
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.thSlice_window_aesm_pth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open scoped Real Topology
open MeasureTheory Set Filter

/-- The angular weight `thEta θ = sin(2θ)^{-η}` is continuous on the open angular interval
`(0, π/2)` (there `sin(2θ) > 0`, so the real power is a composition of continuous maps). -/
lemma continuousOn_thEta_Ioo :
    ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  show ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
    (Set.Ioo (0 : ℝ) (Real.pi / 2))
  exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn.rpow_const
    (fun θ hθ => Or.inl (ne_of_gt (Work.FTS.EllipticEst.sin_two_pos hθ)))

/-- **A.e. strong measurability of the windowed weighted `∂_θG`-square of the trace datum.**

`G` is `C^∞` on the open quadrant (first component of `TraceClass`), hence so is `∂_θG`, so the
uncurried `(z,θ) ↦ thEta θ · (∂_θG z θ)²` is continuous on the (open) quadrant `Q0`: `thEta` is
continuous on `(0, π/2)` where `sin(2θ) > 0`, and `∂_θG` is continuous there.  Composing with
the continuous map `p ↦ (exp p.1, p.2)`, whose image of the half strip
`ℝ × (0,π/2)` (a set of full measure for `volume.prod (volume.restrict Iθ)`, see
`aeStronglyMeasurable_exp`) lies in `Q0`, gives the unwindowed a.e. strong measurability.
Multiplying by the indicator of the measurable window `{p | |log z - p.1| ≤ δ}` (a closed slab
in the logarithm of the radius) gives the statement.

No hypothesis on `δ` or on the sign of `z` is needed: the window is a closed (possibly empty)
interval, and its indicator is measurable regardless. -/
theorem thSlice_window_aesm_pth (G : ℝ → ℝ → ℝ)
    (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G) (δ z : ℝ) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => if |Real.log z - p.1| ≤ δ then
        Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.pth G (Real.exp p.1) p.2) ^ 2 else 0)
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- the angular weight and the first angular derivative of the datum are continuous on `Q0`
  have hth : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.thEta p.2)
      Work.FTS.EllipticEst.Q0 :=
    continuousOn_thEta_Ioo.comp continuous_snd.continuousOn
      (fun p hp => (Set.mem_prod.mp hp).2)
  have hcont : ContinuousOn (Function.uncurry
      (fun z θ : ℝ => Work.FTS.EllipticEst.thEta θ * (Work.Spaces.pth G z θ) ^ 2))
      Work.FTS.EllipticEst.Q0 :=
    hth.mul (((hT.1.pth).continuousOn).pow 2)
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.FTS.EllipticEst.thEta p.2 *
        (Work.Spaces.pth G (Real.exp p.1) p.2) ^ 2)
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    aeStronglyMeasurable_exp
      (X := fun z θ : ℝ => Work.FTS.EllipticEst.thEta θ * (Work.Spaces.pth G z θ) ^ 2) hcont
  -- the window `{p | |log z - p.1| ≤ δ}` is measurable
  have hmeas : Measurable (fun p : ℝ × ℝ => |Real.log z - p.1|) :=
    (continuous_const.sub continuous_fst).abs.measurable
  have hS : MeasurableSet {p : ℝ × ℝ | |Real.log z - p.1| ≤ δ} :=
    measurableSet_Iic.preimage hmeas
  -- the windowed function is the indicator of the window applied to the unwindowed one
  rw [show (fun p : ℝ × ℝ => if |Real.log z - p.1| ≤ δ then
        Work.FTS.EllipticEst.thEta p.2 * (Work.Spaces.pth G (Real.exp p.1) p.2) ^ 2 else 0)
      = {p : ℝ × ℝ | |Real.log z - p.1| ≤ δ}.indicator
          (fun p : ℝ × ℝ => Work.FTS.EllipticEst.thEta p.2 *
            (Work.Spaces.pth G (Real.exp p.1) p.2) ^ 2)
      from by
        funext p
        by_cases hp : |Real.log z - p.1| ≤ δ <;>
          simp [Set.indicator, hp]]
  exact haesm.indicator hS

end Work.FTS.EllSol.EllPkgAux.MollDom
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollMFA.zmollSliceHonest =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollMFA

set_option autoImplicit false

/-! ## The finite-order chain rule for the curried partials

`Work.Spaces.contDiffOn_uncurry_pz`/`_pth` state that `pz`/`pth` preserve `C^∞`-smoothness
*for the analytic order* `⊤`.  The version used below only has the *finite* orders of the
mollification hypothesis; the proofs are the same, with `ContDiffOn.fderivWithin` at the
finite order. -/

/-- `∂_z` lowers the smoothness order by one: the `z`-partial of a `C^{n+1}` function is
`C^n`. -/
theorem contDiffOn_uncurry_pz_succ {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} {n : ℕ} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pz G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (1, 0) := fun p hp =>
    Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin hV.uniqueDiffOn (m := (n : WithTop ℕ∞)) (by simp)
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ n
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- `∂_θ` lowers the smoothness order by one: the `θ`-partial of a `C^{n+1}` function is
`C^n`. -/
theorem contDiffOn_uncurry_pth_succ {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} {n : ℕ} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (0, 1) := fun p hp =>
    Work.Spaces.pth_eq_fderiv
      ((h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin hV.uniqueDiffOn (m := (n : WithTop ℕ∞)) (by simp)
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ n
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-! ## The target -/

theorem zmollSliceHonest (G : ℝ → ℝ → ℝ) (δ ε : ℝ) (hstrip : Work.FTS.EllSol.EllPkgAux.StripAdm G δ ε) :
    ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε)) z θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
  intro z hz
  set F : ℝ → ℝ → ℝ := Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε with hF
  have hU : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have h2 : ContDiffOn ℝ 2 (Function.uncurry F)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := hstrip.1 2
  have h1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth F))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
    contDiffOn_uncurry_pth_succ hU h2
  -- the mixed partial `∂_z∂_θF` is continuous on the half strip, hence on `{z} × Iθ`
  have hcont : ContinuousOn (fun θ : ℝ => Work.Spaces.pz (Work.Spaces.pth F) z θ)
      Work.Spaces.Iθ := by
    have hinner : ContinuousOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth F)))
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
      (contDiffOn_uncurry_pz_succ hU h1).continuousOn
    have hmap : ContinuousOn (fun θ : ℝ => (z, θ)) Work.Spaces.Iθ :=
      continuousOn_const.prodMk continuousOn_id
    have hmaps : Set.MapsTo (fun θ : ℝ => (z, θ)) Work.Spaces.Iθ
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := by
      intro θ hθ
      rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
      show (z, θ) ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)
      rw [Set.mem_prod]
      exact ⟨hz, ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩
    exact (hinner.comp hmap hmaps).congr (fun θ _ => rfl)
  have hcsq : ContinuousOn
      (fun θ : ℝ => (z * Work.Spaces.pz (Work.Spaces.pth F) z θ) ^ 2) Work.Spaces.Iθ :=
    (continuousOn_const.mul hcont).pow 2
  -- bounded continuous factor times the integrable weight `thEta` on the compact `Iθ`
  have hint : IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ
      * (z * Work.Spaces.pz (Work.Spaces.pth F) z θ) ^ 2) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.integrableOn_thEta.1 |>.mul_continuousOn hcsq
      (by rw [Work.Spaces.Iθ]; exact isCompact_Icc)
  refine hint.congr_fun ?_ (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
  intro θ hθ
  simp only [Work.Spaces.Dz]
  ring

end Work.FTS.EllSol.EllPkgAux.MollMFA
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.ThMollDefs =====
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

/-- The angular slice killed outside the closed angle interval `Iθ = [0, π/2]`. -/
def Qcut (g : ℝ → ℝ) : ℝ → ℝ := Set.indicator (Set.Icc 0 (Real.pi / 2)) g

/-- The three-image kernel combination of a kernel `ρ`: the fold of the doubly odd extension
of a slice carries the signs `+ - -`. -/
def Kern (ρ : ℝ → ℝ) (θ s : ℝ) : ℝ := ρ (θ - s) - ρ (θ + s) - ρ (θ + s - Real.pi)

theorem Qcut_of_mem {g : ℝ → ℝ} {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    Qcut g s = g s :=
  Set.indicator_of_mem hs g

theorem Qcut_of_lt_zero {g : ℝ → ℝ} {s : ℝ} (hs : s < 0) : Qcut g s = 0 := by
  refine Set.indicator_of_notMem ?_ g
  intro h
  exact absurd (Set.mem_Icc.mp h).1 (not_le.mpr hs)

theorem Qcut_of_pihalf_lt {g : ℝ → ℝ} {s : ℝ} (hs : Real.pi / 2 < s) : Qcut g s = 0 := by
  refine Set.indicator_of_notMem ?_ g
  intro h
  exact absurd (Set.mem_Icc.mp h).2 (not_le.mpr hs)

theorem Qcut_apply (g : ℝ → ℝ) (s : ℝ) :
    Qcut g s = if s ∈ Set.Icc (0 : ℝ) (Real.pi / 2) then g s else 0 := by
  rw [Qcut, Set.indicator_apply]

theorem Kern_apply (ρ : ℝ → ℝ) (θ s : ℝ) :
    Kern ρ θ s = ρ (θ - s) - ρ (θ + s) - ρ (θ + s - Real.pi) := rfl

/-- The three-image kernel is differentiable in its first variable, with derivative the
three-image kernel of the derivative. -/
theorem Kern_hasDerivAt {ρ ρ' : ℝ → ℝ} (h : ∀ t : ℝ, HasDerivAt ρ (ρ' t) t) (θ s : ℝ) :
    HasDerivAt (fun θ' : ℝ => Kern ρ θ' s) (Kern ρ' θ s) θ := by
  have h1 : HasDerivAt (fun θ' : ℝ => ρ (θ' - s)) (ρ' (θ - s)) θ :=
    HasDerivAt.comp_sub_const θ s (h (θ - s))
  have h2 : HasDerivAt (fun θ' : ℝ => ρ (θ' + s)) (ρ' (θ + s)) θ :=
    HasDerivAt.comp_add_const θ s (h (θ + s))
  have h3 : HasDerivAt (fun θ' : ℝ => ρ (θ' + s - Real.pi)) (ρ' (θ + s - Real.pi)) θ := by
    have := HasDerivAt.comp_add_const θ (s - Real.pi) (h (θ + (s - Real.pi)))
    simpa only [add_sub_assoc] using this
  show HasDerivAt (fun θ' : ℝ => ρ (θ' - s) - ρ (θ' + s) - ρ (θ' + s - Real.pi))
    (ρ' (θ - s) - ρ' (θ + s) - ρ' (θ + s - Real.pi)) θ
  exact (h1.sub h2).sub h3

end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.integrableOn_pth_pth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux




end Work.FTS.EllSol.EllPkgAux
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.logJensen =====
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

/-! ### the weight `Ω` -/

/-- The logarithmic radial weight `Ω(s) = w(e^s)^2 e^s`. -/
def ljOm (s : ℝ) : ℝ := (Work.Spaces.w (Real.exp s)) ^ 2 * Real.exp s

lemma ljOm_nonneg (s : ℝ) : 0 ≤ ljOm s := by
  rw [ljOm]
  exact mul_nonneg (sq_nonneg _) (Real.exp_pos s).le


/-! ### elementary facts about the kernel `sKer` -/

lemma lj_sKer_continuous (ε : ℝ) : Continuous (sKer ε) := by
  have h : sKer ε = fun t : ℝ => (ε * sMass)⁻¹ * sBump (t / ε) := by
    funext t; rw [sKer]
  rw [h]
  exact continuous_const.mul (sBump_continuous.comp (continuous_id.div_const ε))

lemma lj_sKer_hasCompactSupport {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (sKer ε) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-ε) ε) isCompact_Icc ?_
  intro t ht
  rw [Function.mem_support] at ht
  have hlt : |t| < ε := by
    by_contra h
    exact ht (sKer_eq_zero_of_le_abs hε (not_lt.mp h))
  rw [abs_lt] at hlt
  exact ⟨le_of_lt hlt.1, le_of_lt hlt.2⟩

lemma lj_sKer_integrable {ε : ℝ} (hε : 0 < ε) : Integrable (sKer ε) volume :=
  (lj_sKer_continuous ε).integrable_of_hasCompactSupport (lj_sKer_hasCompactSupport hε)


lemma lj_sKer_sub_eq (δ s t : ℝ) : sKer δ (s - t) = sKer δ (t - s) := by
  rw [show s - t = -(t - s) by ring, sKer_even]

lemma lj_sKer_integrable_sub {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    Integrable (fun t : ℝ => sKer δ (s - t)) volume := by
  have h : Integrable (fun t : ℝ => sKer δ (t - s)) volume := (lj_sKer_integrable hδ).comp_sub_right s
  refine h.congr ?_
  filter_upwards with t
  exact (lj_sKer_sub_eq δ s t).symm

lemma lj_sKer_integral_sub (δ : ℝ) (hδ : 0 < δ) (s : ℝ) : (∫ t : ℝ, sKer δ (s - t)) = 1 := by
  have h1 : (∫ t : ℝ, sKer δ (s - t)) = ∫ t : ℝ, sKer δ (t - s) := by
    refine integral_congr_ae ?_
    filter_upwards with t
    exact lj_sKer_sub_eq δ s t
  rw [h1, integral_sub_right_eq_self, sKer_integral_eq_one hδ]



/-! ### the completed-square (Jensen) inequality for a probability density -/


/-! ### the pointwise Jensen bound -/



/-! ### the weighted Young inequality -/


/-! ### the theorem -/


end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.thMollTransfer =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux


end Work.FTS.EllSol.EllPkgAux
end
-- ===== merged: Submission.Work.FTS.EllSol.FlatFT.integrable_normSq_slice1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory
open scoped FourierTransform

namespace Work.FTS.EllSol.FlatFT

/-- The Fourier slice `slice1 h` of a continuous compactly supported `h` is square-integrable.
Indeed `h ∈ L¹ ∩ L²`, so Plancherel gives that `𝓕 h` (which is `slice1 h` pointwise) lies in
`L²`, and `‖·‖ ^ 2` of an `L²` function is integrable.  This is the "left-hand side is finite"
half of Plancherel, `plancherelSlice1`. -/
theorem integrable_normSq_slice1 {h : ℝ → ℂ} (hh : Continuous h) (hs : HasCompactSupport h) :
    MeasureTheory.Integrable (fun ξ : ℝ => ‖Work.FTS.EllSol.FlatFT.slice1 h ξ‖ ^ 2) := by
  have hInt : Integrable h := hh.integrable_of_hasCompactSupport hs
  have hMem : MemLp h 2 (volume : Measure ℝ) := hh.memLp_of_hasCompactSupport hs
  have hF : MemLp (((𝓕 (hMem.toLp h) : Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ) 2 volume :=
    Lp.memLp _
  refine (hF.integrable_norm_pow (by norm_num)).congr ?_
  filter_upwards [fourier_lp_ae_eq hInt hMem] with ξ hξ
  rw [slice1_eq_fourier h ξ, ← hξ]

end Work.FTS.EllSol.FlatFT
end
-- ===== merged: Submission.Work.FTS.EllSol.FlatFT.plancherelSlice1Deriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory
open scoped FourierTransform

namespace Work.FTS.EllSol.FlatFT

noncomputable section

/-- The modulus squared of the factor `2πIξ` acting on `ℂ`. -/
theorem norm_sq_mul_two_pi_I (F : ℂ) (ξ : ℝ) :
    ‖(2 * Real.pi * Complex.I * ξ) * F‖ ^ 2 = (2 * Real.pi * ξ) ^ 2 * ‖F‖ ^ 2 := by
  have h1 : ((2 * Real.pi * Complex.I * ξ : ℂ)) = ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h1, norm_mul, norm_mul, Complex.norm_I, mul_one, mul_pow, Complex.sq_norm,
    Complex.normSq_ofReal]
  ring

/-- The pointwise derivative rule for the `t`-slice: `slice1 (deriv h) ξ = 2πIξ · slice1 h ξ`. -/
theorem slice1_deriv (h : ℝ → ℂ) (hh : ContDiff ℝ 1 h) (hs : HasCompactSupport h) (ξ : ℝ) :
    slice1 (deriv h) ξ = (2 * Real.pi * Complex.I * ξ) * slice1 h ξ := by
  rw [slice1_eq_fourier, slice1_eq_fourier]
  have hint : Integrable h := hh.continuous.integrable_of_hasCompactSupport hs
  have h'cont : Continuous (deriv h) := hh.continuous_deriv_one
  have h'supp : HasCompactSupport (deriv h) := hs.deriv
  have h'int : Integrable (deriv h) := h'cont.integrable_of_hasCompactSupport h'supp
  have hfd := Real.fourier_deriv hint (hh.differentiable (by norm_num)) h'int
  rw [congr_fun hfd ξ, smul_eq_mul]


end

end Work.FTS.EllSol.FlatFT
end
-- ===== merged: Submission.Work.FTS.EllSol.HeavyFlat.omOfFlat =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.HeavyFlat

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

noncomputable section

set_option autoImplicit false

/-! ## The shifted data `u_k = e^{b_k t}g` and the binomial expansion of `Ω`

The weight `Ω(t) = (1+e^t)^4 e^{-3t} = Σ_{k<5} C(4,k) e^{(k-3)t}` expands as a binomial, so
with `b_k = (k-3)/2` the `k`-th summand is `e^{2 b_k t}` and `Ω` dominates each of them.  The
operator `∂_t - b` acts on `u_k = e^{b_k t}g` as `e^{b_k t}∂_t`.

This block is a self-contained copy of the corresponding statements of
`Work.FTS.EllSol.shiftReduceDefs` / `Work.FTS.EllSol.Shift2Flat.*`, so that this module does not
import those files (whose import graph currently contains a cycle). -/

private def bS (k : ℕ) : ℝ := ((k : ℝ) - 3) / 2

private def cS (k : ℕ) : ℝ := (Nat.choose 4 k : ℝ)

private def shiftD (k : ℕ) (g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t θ => Real.exp (bS k * t) * g t θ

@[simp] private theorem shiftD_def (k : ℕ) (g : ℝ → ℝ → ℝ) (t θ : ℝ) :
    shiftD k g t θ = Real.exp (bS k * t) * g t θ := rfl

private theorem cS_nonneg (k : ℕ) : 0 ≤ cS k := by
  rw [cS]; exact Nat.cast_nonneg _

private theorem exp_two_bS (k : ℕ) (t : ℝ) :
    Real.exp (2 * (bS k * t)) = Real.exp (((k : ℝ) - 3) * t) := by
  congr 1
  simp only [bS]
  ring

private theorem omw_pow_four (y : ℝ) :
    (1 + y) ^ 4 = ∑ k ∈ Finset.range 5, (Nat.choose 4 k : ℝ) * y ^ k := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num [Nat.choose]
  ring

private theorem omw_eq_exp_sum (t : ℝ) :
    omw t = ∑ k ∈ Finset.range 5, (Nat.choose 4 k : ℝ) * Real.exp (((k : ℝ) - 3) * t) := by
  have hterm : ∀ k : ℕ, Real.exp (((k : ℝ) - 3) * t)
      = (Real.exp t) ^ k * Real.exp (-(3 * t)) := by
    intro k
    have h : ((k : ℝ) - 3) * t = (k : ℝ) * t + (-(3 * t)) := by ring
    rw [h, Real.exp_add, Real.exp_nat_mul]
  have hsum : (∑ k ∈ Finset.range 5, (Nat.choose 4 k : ℝ) * Real.exp (((k : ℝ) - 3) * t))
      = (∑ k ∈ Finset.range 5, (Nat.choose 4 k : ℝ) * (Real.exp t) ^ k)
        * Real.exp (-(3 * t)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hterm k]
    ring
  rw [hsum, ← omw_pow_four (Real.exp t), omw]

private theorem exp_shift_le_omw (k : ℕ) (hk : k ≤ 4) (t : ℝ) :
    Real.exp (((k : ℝ) - 3) * t) ≤ omw t := by
  rw [omw_eq_exp_sum t]
  have hmem : k ∈ Finset.range 5 := Finset.mem_range.mpr (by omega)
  have hnonneg : ∀ j ∈ Finset.range 5,
      0 ≤ (Nat.choose 4 j : ℝ) * Real.exp (((j : ℝ) - 3) * t) :=
    fun j _ => mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hle : Real.exp (((k : ℝ) - 3) * t)
      ≤ (Nat.choose 4 k : ℝ) * Real.exp (((k : ℝ) - 3) * t) := by
    have h1 : (1 : ℝ) ≤ (Nat.choose 4 k : ℝ) := by
      have := Nat.choose_pos hk
      exact_mod_cast this
    simpa using mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg (((k : ℝ) - 3) * t))
  exact le_trans hle (Finset.single_le_sum hnonneg hmem)

private theorem omw_eq_sum (t : ℝ) :
    omw t = ∑ k ∈ Finset.range 5, cS k * Real.exp (2 * (bS k * t)) := by
  rw [omw_eq_exp_sum t]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [cS, ← exp_two_bS]

private theorem exp_bS_le_omw (k : ℕ) (hk : k ≤ 4) (t : ℝ) :
    Real.exp (2 * (bS k * t)) ≤ omw t := by
  rw [exp_two_bS]
  exact exp_shift_le_omw k hk t

private theorem sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

private theorem sigE_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ sigE θ := by
  simp only [sigE]
  exact Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _


private def oS : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)

private lemma isOpen_oS : IsOpen oS := isOpen_univ.prod isOpen_Ioo

private lemma measurableSet_oS : MeasurableSet oS := isOpen_oS.measurableSet

private lemma mem_oS {t θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : (t, θ) ∈ oS :=
  ⟨mem_univ t, hθ⟩

/-- The strip `univ ×ˢ Iθ` differs from the open strip `oS` by the null set
`univ ×ˢ {0, π/2}`, hence the two restricted measures agree. -/
private lemma restrict_strip_eq :
    (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ) : Measure (ℝ × ℝ))
      = volume.restrict oS := by
  apply Measure.restrict_congr_set
  rw [ae_eq_set]
  constructor
  · refine measure_mono_null ?_ Work.FTS.EllSol.Shift2Flat.shiftSq_volume_prod_endpoints
    rintro p hp
    rw [Set.mem_sdiff, Set.mem_prod] at hp
    obtain ⟨⟨-, h2⟩, hnot⟩ := hp
    simp only [oS, Set.mem_prod, Set.mem_univ, true_and] at hnot
    refine ⟨trivial, ?_⟩
    have hmem : p.2 ∈ Set.Icc 0 (Real.pi / 2) \ Set.Ioo 0 (Real.pi / 2) := ⟨h2, hnot⟩
    rwa [Set.Icc_sdiff_Ioo_same (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)] at hmem
  · rw [Set.sdiff_eq_empty.mpr, measure_empty]
    exact Set.prod_mono Subset.rfl Set.Ioo_subset_Icc_self

private lemma sin_two_pos_of_mem_oS {p : ℝ × ℝ} (hp : p ∈ oS) : 0 < Real.sin (2 * p.2) := by
  have hθ : p.2 ∈ Set.Ioo 0 (Real.pi / 2) := hp.2
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])



private theorem sdContDiff_slice_fst {g : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g) oS) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContDiff ℝ 2 (fun s : ℝ => g s θ) := by
  have hmap : ContDiffOn ℝ 2 (fun s : ℝ => (s, θ)) Set.univ :=
    contDiffOn_id.prodMk contDiffOn_const
  have hcomp : ContDiffOn ℝ 2 (Function.uncurry g ∘ fun s : ℝ => (s, θ)) Set.univ :=
    hsm.comp hmap fun s _ => mem_oS hθ
  have hfun : (fun s : ℝ => g s θ) = Function.uncurry g ∘ fun s : ℝ => (s, θ) := rfl
  rw [hfun]
  exact contDiffOn_univ.mp hcomp

private theorem sdContDiffOn_slice_snd {g : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g) oS) (t : ℝ) :
    ContDiffOn ℝ 2 (fun θ' : ℝ => g t θ') (Set.Ioo 0 (Real.pi / 2)) := by
  have hmap : ContDiffOn ℝ 2 (fun θ' : ℝ => (t, θ')) (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_const.prodMk contDiffOn_id
  have hcomp : ContDiffOn ℝ 2 (Function.uncurry g ∘ fun θ' : ℝ => (t, θ'))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hsm.comp hmap fun θ' hθ' => mem_oS hθ'
  exact hcomp.congr fun θ' _ => rfl

private theorem sdContDiffAt_slice_snd {g : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g) oS) {t θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContDiffAt ℝ 2 (fun θ' : ℝ => g t θ') θ :=
  (sdContDiffOn_slice_snd hsm t).contDiffAt (isOpen_Ioo.mem_nhds hθ)

private theorem sdContDiffOn_uncurry_pz {V : Set (ℝ × ℝ)} (hV : IsOpen V) {G : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 2 (Function.uncurry G) V) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz G)) V := by
  have hfd : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := (1 : WithTop ℕ∞)) hV.uniqueDiffOn (by norm_num)
    refine h'.congr fun p hp => ?_
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ 1
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V := by
    simpa using hfd.clm_apply
      (contDiffOn_const : ContDiffOn ℝ 1 (fun _ : ℝ × ℝ => ((1, 0) : ℝ × ℝ)) V)
  refine hcomp.congr fun p hp => ?_
  exact Work.Spaces.pz_eq_fderiv
    ((h.differentiableOn (by norm_num)).differentiableAt (hV.mem_nhds hp))

private theorem sdDifferentiableAt_pz_slice_snd {g : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g) oS) {t θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    DifferentiableAt ℝ (fun θ' : ℝ => Work.Spaces.pz g t θ') θ := by
  have h1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz g)) oS :=
    sdContDiffOn_uncurry_pz isOpen_oS hsm
  have h2 : ContDiffAt ℝ 1 (Function.uncurry (Work.Spaces.pz g)) (t, θ) :=
    h1.contDiffAt (isOpen_oS.mem_nhds (mem_oS hθ))
  have h3 : ContDiffAt ℝ 1 (fun θ' : ℝ => (t, θ')) θ := by fun_prop
  have h4 : ContDiffAt ℝ 1 (fun θ' : ℝ => Work.Spaces.pz g t θ') θ := h2.comp θ h3
  exact h4.differentiableAt (by norm_num)


private theorem hasDerivAt_exp_mul_const (c s : ℝ) :
    HasDerivAt (fun s' : ℝ => Real.exp (c * s')) (c * Real.exp (c * s)) s := by
  have h1 : HasDerivAt (fun s' : ℝ => c * s') c s := by
    simpa using (hasDerivAt_id s).const_mul c
  have h2 : HasDerivAt Real.exp (Real.exp (c * s)) (c * s) := Real.hasDerivAt_exp (c * s)
  simpa only [Function.comp_def, mul_comm] using h2.comp s h1

private theorem deriv_mul_fun {f g : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    deriv (fun y : ℝ => f y * g y) x = deriv f x * g x + f x * deriv g x := by
  rw [show (fun y : ℝ => f y * g y) = f * g from rfl, deriv_mul hf hg]

private theorem deriv_add_fun {f g : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    deriv (fun y : ℝ => f y + g y) x = deriv f x + deriv g x := by
  rw [show (fun y : ℝ => f y + g y) = f + g from rfl, deriv_add hf hg]

private theorem deriv_exp_mul {c : ℝ} {H : ℝ → ℝ} {t : ℝ} (hH : DifferentiableAt ℝ H t) :
    deriv (fun s : ℝ => Real.exp (c * s) * H s) t
      = Real.exp (c * t) * (c * H t + deriv H t) := by
  rw [deriv_mul_fun (hasDerivAt_exp_mul_const c t).differentiableAt hH,
    (hasDerivAt_exp_mul_const c t).deriv]
  ring

/-- The second-order product rule for `s ↦ e^{c s} H s`.  Since the exponential factor is
differentiable everywhere, no regularity beyond `C²` of `H` is needed. -/
private theorem deriv_deriv_exp_mul {c : ℝ} {H : ℝ → ℝ} (hH : ContDiff ℝ 2 H) (t : ℝ) :
    deriv (deriv (fun s : ℝ => Real.exp (c * s) * H s)) t
      = Real.exp (c * t) * (c ^ 2 * H t + 2 * c * deriv H t + deriv (deriv H) t) := by
  have hdiff : Differentiable ℝ H := hH.differentiable (by norm_num)
  have hddiff : Differentiable ℝ (deriv H) := hH.differentiable_deriv_two
  have hFeq : deriv (fun s : ℝ => Real.exp (c * s) * H s)
      = fun s : ℝ => Real.exp (c * s) * (c * H s + deriv H s) := by
    funext s
    rw [deriv_exp_mul (hH := hdiff.differentiableAt)]
  rw [hFeq]
  have hE : DifferentiableAt ℝ (fun s : ℝ => Real.exp (c * s)) t :=
    (hasDerivAt_exp_mul_const c t).differentiableAt
  have hcH : DifferentiableAt ℝ (fun s : ℝ => c * H s) t := hdiff.differentiableAt.const_mul c
  have hdH : DifferentiableAt ℝ (deriv H) t := hddiff.differentiableAt
  have hK : DifferentiableAt ℝ (fun s : ℝ => c * H s + deriv H s) t := hcH.add hdH
  rw [deriv_mul_fun hE hK, (hasDerivAt_exp_mul_const c t).deriv, deriv_add_fun hcH hdH,
    deriv_const_mul_field]
  ring




private theorem pz_shiftD {g : ℝ → ℝ → ℝ} {k : ℕ}
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g) oS) {t θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pz (shiftD k g) t θ
      = Real.exp (bS k * t)
        * (bS k * g t θ + Work.Spaces.pz g t θ) := by
  have hslice : ContDiff ℝ 2 (fun s : ℝ => g s θ) := sdContDiff_slice_fst hsm hθ
  show deriv (fun s : ℝ => Real.exp (bS k * s) * g s θ) t
      = Real.exp (bS k * t)
        * (bS k * g t θ + Work.Spaces.pz g t θ)
  exact deriv_exp_mul (c := bS k) (hslice.differentiable (by norm_num)).differentiableAt

private theorem pz_pz_shiftD {g : ℝ → ℝ → ℝ} {k : ℕ}
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g) oS) {t θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pz (Work.Spaces.pz (shiftD k g)) t θ
      = Real.exp (bS k * t)
        * (bS k ^ 2 * g t θ
            + 2 * bS k * Work.Spaces.pz g t θ
            + Work.Spaces.pz (Work.Spaces.pz g) t θ) := by
  have hslice : ContDiff ℝ 2 (fun s : ℝ => g s θ) := sdContDiff_slice_fst hsm hθ
  show deriv (deriv (fun s : ℝ => Real.exp (bS k * s) * g s θ)) t
      = Real.exp (bS k * t)
        * (bS k ^ 2 * g t θ
            + 2 * bS k * Work.Spaces.pz g t θ
            + Work.Spaces.pz (Work.Spaces.pz g) t θ)
  exact deriv_deriv_exp_mul hslice t

private theorem pth_shiftD {g : ℝ → ℝ → ℝ} {k : ℕ} (t θ : ℝ) :
    Work.Spaces.pth (shiftD k g) t θ
      = Real.exp (bS k * t) * Work.Spaces.pth g t θ := by
  show deriv (fun θ' : ℝ => Real.exp (bS k * t) * g t θ') θ
      = Real.exp (bS k * t) * deriv (fun θ' : ℝ => g t θ') θ
  rw [deriv_const_mul_field]

private theorem pth_pth_shiftD {g : ℝ → ℝ → ℝ} {k : ℕ} (t θ : ℝ) :
    Work.Spaces.pth (Work.Spaces.pth (shiftD k g)) t θ
      = Real.exp (bS k * t) * Work.Spaces.pth (Work.Spaces.pth g) t θ := by
  have h1 : ∀ θ' : ℝ, Work.Spaces.pth (shiftD k g) t θ'
      = Real.exp (bS k * t) * Work.Spaces.pth g t θ' :=
    fun θ' => pth_shiftD t θ'
  show deriv (fun θ' : ℝ => Work.Spaces.pth (shiftD k g) t θ') θ
      = Real.exp (bS k * t)
        * deriv (fun θ' : ℝ => Work.Spaces.pth g t θ') θ
  rw [show (fun θ' : ℝ => Work.Spaces.pth (shiftD k g) t θ')
      = fun θ' : ℝ => Real.exp (bS k * t) * Work.Spaces.pth g t θ'
      from funext h1]
  rw [deriv_const_mul_field]

private theorem pth_pz_shiftD {g : ℝ → ℝ → ℝ} {k : ℕ}
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g) oS) {t θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pth (Work.Spaces.pz (shiftD k g)) t θ
      = Real.exp (bS k * t)
        * (bS k * Work.Spaces.pth g t θ
            + Work.Spaces.pth (Work.Spaces.pz g) t θ) := by
  have hev : (fun θ' : ℝ => Work.Spaces.pz (shiftD k g) t θ')
      =ᶠ[𝓝 θ] fun θ' : ℝ => Real.exp (bS k * t)
        * (bS k * g t θ' + Work.Spaces.pz g t θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    have hslice : ContDiff ℝ 2 (fun s : ℝ => g s θ') := sdContDiff_slice_fst hsm hθ'
    show deriv (fun s : ℝ => Real.exp (bS k * s) * g s θ') t
        = Real.exp (bS k * t)
          * (bS k * g t θ' + Work.Spaces.pz g t θ')
    exact deriv_exp_mul (c := bS k)
      (hslice.differentiable (by norm_num)).differentiableAt
  have hgmul : DifferentiableAt ℝ
      (fun θ' : ℝ => bS k * g t θ') θ :=
    ((sdContDiffAt_slice_snd hsm hθ).differentiableAt (by norm_num)).const_mul _
  have hgpz : DifferentiableAt ℝ (fun θ' : ℝ => Work.Spaces.pz g t θ') θ :=
    sdDifferentiableAt_pz_slice_snd hsm hθ
  show deriv (fun θ' : ℝ => Work.Spaces.pz (shiftD k g) t θ') θ
      = Real.exp (bS k * t)
        * (bS k * Work.Spaces.pth g t θ
            + Work.Spaces.pth (Work.Spaces.pz g) t θ)
  rw [hev.deriv_eq, deriv_const_mul_field]
  have key : deriv (fun θ' : ℝ => bS k * g t θ'
        + Work.Spaces.pz g t θ') θ
      = bS k * Work.Spaces.pth g t θ
        + Work.Spaces.pth (Work.Spaces.pz g) t θ := by
    have h1 : deriv (fun θ' : ℝ => g t θ') θ = Work.Spaces.pth g t θ := rfl
    have h2 : deriv (fun θ' : ℝ => Work.Spaces.pz g t θ') θ
        = Work.Spaces.pth (Work.Spaces.pz g) t θ := rfl
    rw [deriv_add_fun hgmul hgpz, deriv_const_mul_field, h1, h2]
  rw [key]




/-- The four pointwise shift identities for `u_k = e^{b_k t} g` on the open strip
`0 < θ < π/2`: the second `t`-slot, the second `θ`-slot, the first `t`-slot and the mixed
`(θ,t)`-slot of the shifted datum equal `e^{b_k t}` times the corresponding slot of `g`. -/
private theorem shiftD_pointwise {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    (∀ t θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pz (Work.Spaces.pz (shiftD k g)) t θ
        - 2 * bS k * Work.Spaces.pz (shiftD k g) t θ
        + bS k ^ 2 * shiftD k g t θ
      = Real.exp (bS k * t) * Work.Spaces.pz (Work.Spaces.pz g) t θ) ∧
    (∀ t θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pth (Work.Spaces.pth (shiftD k g)) t θ
      = Real.exp (bS k * t) * Work.Spaces.pth (Work.Spaces.pth g) t θ) ∧
    (∀ t θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pz (shiftD k g) t θ - bS k * shiftD k g t θ
      = Real.exp (bS k * t) * Work.Spaces.pz g t θ) ∧
    (∀ t θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pth (Work.Spaces.pz (shiftD k g)) t θ
        - bS k * Work.Spaces.pth (shiftD k g) t θ
      = Real.exp (bS k * t) * Work.Spaces.pth (Work.Spaces.pz g) t θ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t θ hθ
    rw [pz_pz_shiftD (k := k) (g := g) hsm (t := t) (θ := θ) hθ,
      pz_shiftD (k := k) (g := g) hsm (t := t) (θ := θ) hθ, shiftD]
    ring
  · intro t θ _
    exact pth_pth_shiftD (k := k) (g := g) t θ
  · intro t θ hθ
    rw [pz_shiftD (k := k) (g := g) hsm (t := t) (θ := θ) hθ, shiftD]
    ring
  · intro t θ hθ
    rw [pth_pz_shiftD (k := k) (g := g) hsm (t := t) (θ := θ) hθ, pth_shiftD]
    ring


private lemma continuousOn_sigE : ContinuousOn (fun p : ℝ × ℝ => sigE p.2) oS := by
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2)) oS :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  exact hsin.rpow_const (fun p hp => Or.inl (ne_of_gt (sin_two_pos_of_mem_oS hp)))

/-- `p ↦ ∂_θ∂_t g (p.1, p.2)` is continuous on the open strip: `∂_t g` is `C¹` there, so its
`θ`-partial is the (continuous) Fréchet derivative against the direction `(0,1)`. -/
private lemma continuousOn_pth_pz {g : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 (Function.uncurry g) oS) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) oS := by
  have hC1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz g)) oS :=
    sdContDiffOn_uncurry_pz isOpen_oS hsm
  have hfd : ContinuousOn (fun p : ℝ × ℝ =>
      fderiv ℝ (Function.uncurry (Work.Spaces.pz g)) p) oS :=
    hC1.continuousOn_fderiv_of_isOpen isOpen_oS le_rfl
  have hev : ContinuousOn (fun p : ℝ × ℝ =>
      fderiv ℝ (Function.uncurry (Work.Spaces.pz g)) p (0, 1)) oS :=
    hfd.clm_apply (continuousOn_const : ContinuousOn (fun _ : ℝ × ℝ => ((0 : ℝ), (1 : ℝ))) oS)
  refine hev.congr (fun p hp => ?_)
  exact Work.Spaces.pth_eq_fderiv (G := Work.Spaces.pz g)
    ((hC1.contDiffAt (isOpen_oS.mem_nhds hp)).differentiableAt (by norm_num))

/-- **The `Ω`-weighted heavy mixed-slot finiteness from the flat shifted one.**  The
decomposition `Ω(t) = (1+e^t)^4 e^{-3t} = Σ_{k<5} C(4,k) e^{2 b_k t}` with `b_k = (k-3)/2`,
together with `e^{b t}∂_t g = (∂_t - b)(e^{b t}g)`, reduces the `Ω`-weighted strip statement to
the flat shifted statement applied to the scaled data `u_k = e^{b_k t}g` (`k < 5`), each of whose
three diagonal slots is dominated by the corresponding `Ω`-weighted slot of `g` because
`e^{2 b_k t} ≤ Ω(t)` (the coefficient of `e^{2b_k t}` in the binomial expansion of `Ω` is
`C(4,k) ≥ 1`); the conclusion is summed over `k < 5` by `lintegral_finset_sum`.  Both the
hypotheses and the conclusion are on the strip `univ ×ˢ Iθ`. -/
theorem omOfFlat : Work.FTS.EllSol.HeavyFlat.FlatHeavy → Work.FTS.EllSol.HeavyFlat.OmHeavy := by
  intro hFlat g hsm h0 hπ hA hP hE
  classical
  -- ### Step 1: the per-shift finiteness, for each `k < 5`
  have key : ∀ k ∈ Finset.range 5,
      ∫⁻ p in oS, ENNReal.ofReal
        ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2
          * Real.exp (2 * (bS k * p.1)) * sigE p.2) < ⊤ := by
    intro k hk
    have hk4 : k ≤ 4 := by have h5 := Finset.mem_range.mp hk; omega
    -- the shifted datum `u_k = e^{b_k t} g` is smooth on the open strip and vanishes at `θ = 0, π/2`
    have hsmk : ContDiffOn ℝ 2 (Function.uncurry (shiftD k g))
        (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      have hf : ContDiff ℝ 2 (fun p : ℝ × ℝ => Real.exp (bS k * p.1)) :=
        Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst)
      have hgoal : Function.uncurry (shiftD k g)
          = fun p : ℝ × ℝ =>
              Real.exp (bS k * p.1) * Function.uncurry g p := by
        funext p; rfl
      rw [hgoal]
      exact hf.contDiffOn.mul hsm
    have h0k : ∀ t : ℝ, shiftD k g t 0 = 0 := by
      intro t; rw [shiftD_def, h0 t, mul_zero]
    have hπk : ∀ t : ℝ, shiftD k g t (Real.pi / 2) = 0 := by
      intro t; rw [shiftD_def, hπ t, mul_zero]
    have hexp : ∀ t : ℝ, Real.exp (2 * bS k * t)
        ≤ Work.FTS.EllSol.omegaAux t := by
      intro t
      rw [show 2 * bS k * t = 2 * (bS k * t) by ring]
      exact exp_bS_le_omw k hk4 t
    have hσ : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ sigE θ :=
      fun θ hθ => sigE_nonneg hθ
    have hpw := shiftD_pointwise (k := k) (g := g) hsm
    -- the three shifted diagonal slots are integrable on the strip
    have hI1 : IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz (shiftD k g) p.1 p.2
          - bS k * shiftD k g p.1 p.2) ^ 2
        * sigE p.2) (Set.univ ×ˢ Work.Spaces.Iθ) :=
      Work.FTS.EllSol.Shift2Flat.integrableOn_shift_sq (b := bS k)
        (u := fun t θ => Work.Spaces.pz (shiftD k g) t θ
          - bS k * shiftD k g t θ)
        (v := fun t θ => Work.Spaces.pz g t θ) (σ := sigE) hexp hσ hA
        (fun t θ hθ => hpw.2.2.1 t θ hθ)
    have hI2 : IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz (Work.Spaces.pz (shiftD k g)) p.1 p.2
          - 2 * bS k
            * Work.Spaces.pz (shiftD k g) p.1 p.2
          + bS k ^ 2 * shiftD k g p.1 p.2) ^ 2
        * sigE p.2) (Set.univ ×ˢ Work.Spaces.Iθ) :=
      Work.FTS.EllSol.Shift2Flat.integrableOn_shift_sq (b := bS k)
        (u := fun t θ => Work.Spaces.pz (Work.Spaces.pz (shiftD k g)) t θ
          - 2 * bS k * Work.Spaces.pz (shiftD k g) t θ
          + bS k ^ 2 * shiftD k g t θ)
        (v := fun t θ => Work.Spaces.pz (Work.Spaces.pz g) t θ) (σ := sigE) hexp hσ hP
        (fun t θ hθ => hpw.1 t θ hθ)
    have hI3 : IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pth (Work.Spaces.pth (shiftD k g)) p.1 p.2) ^ 2
        * sigE p.2) (Set.univ ×ˢ Work.Spaces.Iθ) :=
      Work.FTS.EllSol.Shift2Flat.integrableOn_shift_sq (b := bS k)
        (u := fun t θ => Work.Spaces.pth (Work.Spaces.pth (shiftD k g)) t θ)
        (v := fun t θ => Work.Spaces.pth (Work.Spaces.pth g) t θ) (σ := sigE) hexp hσ hE
        (fun t θ hθ => hpw.2.1 t θ hθ)
    have hkfin := hFlat (bS k) (shiftD k g)
      hsmk h0k hπk hI1 hI2 hI3
    -- identify the shifted `(1,1)`-slot with `e^{2 b_k t}` times the slot of `g`
    have hconv1 : ∫⁻ p in oS, ENNReal.ofReal
          ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2
            * Real.exp (2 * (bS k * p.1)) * sigE p.2)
        = ∫⁻ p in oS, ENNReal.ofReal
          ((Work.Spaces.pth (Work.Spaces.pz (shiftD k g)) p.1 p.2
            - bS k
              * Work.Spaces.pth (shiftD k g) p.1 p.2) ^ 2 * sigE p.2) := by
      refine lintegral_congr_ae ?_
      filter_upwards [self_mem_ae_restrict measurableSet_oS] with p hp
      have hθ : p.2 ∈ Set.Ioo 0 (Real.pi / 2) := hp.2
      rw [hpw.2.2.2 p.1 p.2 hθ]
      congr 1
      rw [mul_pow, show Real.exp (bS k * p.1) ^ 2
            = Real.exp (2 * (bS k * p.1)) by
          rw [pow_two, ← Real.exp_add]; ring_nf]
      ring
    have hconv2 : ∫⁻ p in oS, ENNReal.ofReal
          ((Work.Spaces.pth (Work.Spaces.pz (shiftD k g)) p.1 p.2
            - bS k
              * Work.Spaces.pth (shiftD k g) p.1 p.2) ^ 2 * sigE p.2)
        = ∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal
          ((Work.Spaces.pth (Work.Spaces.pz (shiftD k g)) p.1 p.2
            - bS k
              * Work.Spaces.pth (shiftD k g) p.1 p.2) ^ 2 * sigE p.2) := by
      rw [restrict_strip_eq]
    rw [hconv1, hconv2]
    exact hkfin
  -- ### Step 2: the decomposition of the `Ω`-weighted integrand
  have haesm : ∀ k ∈ Finset.range 5, AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
        (cS k *
          ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2
            * Real.exp (2 * (bS k * p.1)) * sigE p.2)))
      (volume.restrict oS) := by
    intro k hk
    have hY : AEMeasurable (fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2)
        (volume.restrict oS) := (continuousOn_pth_pz hsm).aemeasurable measurableSet_oS
    have hσ : AEMeasurable (fun p : ℝ × ℝ => sigE p.2) (volume.restrict oS) :=
      continuousOn_sigE.aemeasurable measurableSet_oS
    have he : AEMeasurable (fun p : ℝ × ℝ =>
        Real.exp (2 * (bS k * p.1))) (volume.restrict oS) := by
      refine Measurable.aemeasurable ?_
      have h : Measurable (fun p : ℝ × ℝ =>
          Real.exp ((2 * bS k) * p.1)) :=
        Real.measurable_exp.comp
          ((measurable_const : Measurable (fun _ : ℝ × ℝ => 2 * bS k)).mul
            measurable_fst)
      simpa only [mul_assoc] using h
    have h1 : AEMeasurable (fun p : ℝ × ℝ =>
        (Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2) (volume.restrict oS) := by
      have h := hY.mul hY
      have hfun : ((fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2)
            * fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2)
          = fun p : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2 := by
        funext p; rw [Pi.mul_apply, sq]
      rwa [hfun] at h
    have h2 : AEMeasurable (fun p : ℝ × ℝ =>
        (Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2
          * Real.exp (2 * (bS k * p.1))) (volume.restrict oS) :=
      h1.mul he
    have h3 : AEMeasurable (fun p : ℝ × ℝ =>
        (Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2
          * Real.exp (2 * (bS k * p.1)) * sigE p.2)
        (volume.restrict oS) := h2.mul hσ
    exact ENNReal.measurable_ofReal.comp_aemeasurable (h3.const_mul (cS k))
  have hGk : ∀ k ∈ Finset.range 5,
      ∫⁻ p in oS, ENNReal.ofReal (cS k *
          ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2
            * Real.exp (2 * (bS k * p.1)) * sigE p.2))
      = ENNReal.ofReal (cS k) *
          ∫⁻ p in oS, ENNReal.ofReal
            ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2
              * Real.exp (2 * (bS k * p.1)) * sigE p.2) := by
    intro k hk
    have hfac : (fun p : ℝ × ℝ => ENNReal.ofReal (cS k *
          ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2
            * Real.exp (2 * (bS k * p.1)) * sigE p.2)))
        = fun p : ℝ × ℝ => ENNReal.ofReal (cS k)
          * ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2
            * Real.exp (2 * (bS k * p.1)) * sigE p.2) := by
      funext p
      exact ENNReal.ofReal_mul (cS_nonneg k)
    rw [hfac, MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hdecomp : ∫⁻ p in oS, ENNReal.ofReal
        ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2 * omw p.1 * sigE p.2)
      = ∑ k ∈ Finset.range 5, ENNReal.ofReal (cS k)
          * ∫⁻ p in oS, ENNReal.ofReal
              ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2
                * Real.exp (2 * (bS k * p.1)) * sigE p.2) := by
    have hae : (fun p : ℝ × ℝ => ENNReal.ofReal
          ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2 * omw p.1 * sigE p.2))
        =ᵐ[volume.restrict oS] (fun p : ℝ × ℝ => ∑ k ∈ Finset.range 5,
          ENNReal.ofReal (cS k *
            ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2
              * Real.exp (2 * (bS k * p.1)) * sigE p.2))) := by
      filter_upwards [self_mem_ae_restrict measurableSet_oS] with p hp
      have hsig : 0 ≤ sigE p.2 :=
        le_of_lt (Real.rpow_pos_of_pos (sin_two_pos_of_mem_oS hp) _)
      have homw : omw p.1 = ∑ k ∈ Finset.range 5, cS k
          * Real.exp (2 * (bS k * p.1)) :=
        omw_eq_sum p.1
      have hsplit : (Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2
            * (∑ k ∈ Finset.range 5, cS k
                * Real.exp (2 * (bS k * p.1))) * sigE p.2
          = ∑ k ∈ Finset.range 5, cS k
              * ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2
                * Real.exp (2 * (bS k * p.1)) * sigE p.2) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      rw [homw, hsplit]
      rw [ENNReal.ofReal_sum_of_nonneg (s := Finset.range 5)
        (f := fun k => cS k *
          ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2
            * Real.exp (2 * (bS k * p.1)) * sigE p.2))
        (fun k _ => mul_nonneg (cS_nonneg k)
          (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)) hsig))]
    rw [lintegral_congr_ae hae, MeasureTheory.lintegral_finsetSum' _ haesm]
    exact Finset.sum_congr rfl (fun k hk => hGk k hk)
  -- ### Step 3: the sum is finite
  have hfin : ∫⁻ p in oS, ENNReal.ofReal
      ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2 * omw p.1 * sigE p.2) < ⊤ := by
    rw [hdecomp]
    refine ENNReal.sum_lt_top.mpr (fun k hk => ?_)
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (key k hk)
  have hgoal : ∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal
        ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2 * omw p.1 * sigE p.2)
      = ∫⁻ p in oS, ENNReal.ofReal
        ((Work.Spaces.pth (Work.Spaces.pz g) p.1 p.2) ^ 2 * omw p.1 * sigE p.2) := by
    rw [restrict_strip_eq]
  rw [hgoal]
  exact hfin

end

end Work.FTS.EllSol.HeavyFlat
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.TraceEngine.SlotEngineCore =====
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

/-! # The three level-`0` slots of `TraceEngine.slotBounds`

The generic product-form transfer (Tonelli) and its three instances: the slot `D_z(D_z^rV)` of
`HkSq α k (D_zV)`, the slot `∂_θ²(D_z^rV)` of `HkSq α k (∂_θ²V)` and the slot `D_z²(D_z^rV)` of
`HkSq α k (D_z²V)`. -/

/-- If the `θ`-slice integrands of the level-`0` radial slot of `F` are honest, then the
product-mode integral of the same integrand is honest and bounded by `B`. -/
theorem slotAux_slotProdCore {B : ℝ} {F : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry (fun z θ : ℝ =>
      (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hslice : ∀ z : ℝ, 0 < z → IntegrableOn (fun θ : ℝ =>
      (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hnn : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      0 ≤ (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
    (hint : IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iz)
    (hval : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ) ≤ B) :
    IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        * (F p.1 p.2) ^ 2) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ∧ (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
          * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2) ≤ B := by
  obtain ⟨hInt, hval₀⟩ := Work.FTS.ClassC.NormPieces.prodIntegrableNonneg hcont hslice hnn hint
  have hInt' : Integrable (Function.uncurry (fun z θ : ℝ =>
      (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ))
      ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    rw [slotAux_volume_restrict_dom]; exact hInt
  have heq : ∀ p ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
      (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2
        = Function.uncurry (fun z θ : ℝ =>
            (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ) p := by
    rintro ⟨z, θ⟩ hp
    show (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ * (F z θ) ^ 2
      = (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ
    ring
  have hae : (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        * (F p.1 p.2) ^ 2)
      =ᵐ[(volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)]
      (Function.uncurry (fun z θ : ℝ =>
        (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)) :=
    MeasureTheory.ae_restrict_of_forall_mem slotAux_measurableSet_dom heq
  refine ⟨hInt'.congr hae.symm, ?_⟩
  calc (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2)
      = ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, Function.uncurry (fun z θ : ℝ =>
          (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ) p :=
        MeasureTheory.integral_congr_ae hae
    _ = ∫ p, Function.uncurry (fun z θ : ℝ =>
          (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ) p
          ∂((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := rfl
    _ = ∫ p, Function.uncurry (fun z θ : ℝ =>
          (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ) p
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
        rw [slotAux_volume_restrict_dom]
    _ = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ := hval₀
    _ ≤ B := hval

/-- The `D_z`-slot of `D_zV` at radial level `r ≤ k`. -/
theorem slotAux_slotZ_prod {k r : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hV : Work.FTS.EllipticEst.SmoothOpen V)
    (hd : Work.Spaces.HkMem α k (Work.Spaces.Dz V)) (hr : r ≤ k) :
    IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ∧ (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
          * Work.FTS.EllipticEst.thEta p.2
          * (Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
        ≤ Work.Spaces.HkSq α k (Work.Spaces.Dz V) := by
  have hcont : ContinuousOn (Function.uncurry (fun z θ : ℝ =>
      (Work.Spaces.Dz (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ =>
        (Work.Spaces.DzIter r (Work.Spaces.Dz V) p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
          * Work.FTS.EllipticEst.thEta p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      Work.EllipticEst.Core.i0Aux.continuousOn_dzIter_weight (g := Work.Spaces.Dz V) hV.Dz r
    refine h1.congr ?_
    intro p hp
    show (Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2
      = (Work.Spaces.DzIter r (Work.Spaces.Dz V) p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2
    rw [slotAux_Dz_iter_comm_apply r V p.1 p.2]
  have hslice : ∀ z : ℝ, 0 < z → IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.Dz (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
    intro z hz
    have h1 := Work.EllipticEst.Core.i0Aux.integrableOn_slice_summand
      (g := Work.Spaces.Dz V) hV.Dz hd hr hz
    refine h1.congr (Filter.Eventually.of_forall fun θ => ?_)
    show (Work.Spaces.DzIter r (Work.Spaces.Dz V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ
      = (Work.Spaces.Dz (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ
    rw [slotAux_Dz_iter_comm_apply r V z θ]
  have hnn : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      0 ≤ (Work.Spaces.Dz (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ :=
    fun z θ _ hθ => mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Work.EllipticEst.Core.i0Aux.thEta_nonneg_Iθ hθ)
  have hpt : ∀ z : ℝ, Work.EllipticEst.Core.dIntS (Work.Spaces.DzIter r V) z
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.DzIter r V) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
    intro z
    rw [Work.EllipticEst.Core.dIntS, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    ring
  have hint : IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iz :=
    (Work.EllipticEst.Core.i0Aux.dIntS_integrableOn (V := V) hV hd hr).congr
      (Filter.Eventually.of_forall fun z => hpt z)
  have hval : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) ≤ Work.Spaces.HkSq α k (Work.Spaces.Dz V) := by
    calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dz (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * Work.FTS.EllipticEst.thEta θ)
        = ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.dIntS (Work.Spaces.DzIter r V) z := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          exact (hpt z).symm
      _ ≤ Work.Spaces.HkSq α k (Work.Spaces.Dz V) :=
          Work.EllipticEst.Core.i0Aux.dIntS_integral_le_HkSq (V := V) hd hr
  exact slotAux_slotProdCore hcont hslice hnn hint hval

/-- The `∂_θ²`-slot at radial level `r ≤ k`. -/
theorem slotAux_slotT_prod {k r : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hV : Work.FTS.EllipticEst.SmoothOpen V)
    (htt : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V)) (hr : r ≤ k) :
    IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ∧ (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
          * Work.FTS.EllipticEst.thEta p.2
          * (Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
        ≤ Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V) := by
  have hcont : ContinuousOn (Function.uncurry (fun z θ : ℝ =>
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ =>
        (Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
          * Work.FTS.EllipticEst.thEta p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      Work.EllipticEst.Core.i0Aux.continuousOn_dzIter_weight (g := Work.Spaces.pthIter 2 V)
        hV.pth.pth r
    refine h1.congr ?_
    intro p hp
    obtain ⟨hz, hθ1, hθ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    show (Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) p.1 p.2) ^ 2
        * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
      = (Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) p.1 p.2) ^ 2
        * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
    rw [Work.EllipticEst.Core.i0Aux.pthIter2_DzIter_comm hV hz hθ1 hθ2 r]
  have hslice : ∀ z : ℝ, 0 < z → IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
    intro z hz
    have h1 := Work.EllipticEst.Core.i0Aux.integrableOn_slice_summand
      (g := Work.Spaces.pthIter 2 V) hV.pth.pth htt hr hz
    refine h1.congr ?_
    filter_upwards [slotAux_ae_mem_Ioo_Itheta] with θ hθ
    show (Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ
      = (Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ
    rw [Work.EllipticEst.Core.i0Aux.pthIter2_DzIter_comm hV hz hθ.1 hθ.2 r]
  have hnn : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      0 ≤ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ :=
    fun z θ _ hθ => mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Work.EllipticEst.Core.i0Aux.thEta_nonneg_Iθ hθ)
  have hpt : ∀ z : ℝ, Work.EllipticEst.Core.ttIntS (Work.Spaces.DzIter r V) z
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
    intro z
    rw [Work.EllipticEst.Core.ttIntS, ← MeasureTheory.integral_const_mul,
      slotAux_pthIter_two_eq (Work.Spaces.DzIter r V)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    ring
  have hint : IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iz :=
    (Work.EllipticEst.Core.i0Aux.ttIntS_integrableOn (V := V) hV htt hr).congr
      (Filter.Eventually.of_forall fun z => hpt z)
  have hval : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) ≤ Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V) := by
    calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * Work.FTS.EllipticEst.thEta θ)
        = ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ttIntS (Work.Spaces.DzIter r V) z := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          exact (hpt z).symm
      _ ≤ Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V) :=
          Work.EllipticEst.Core.i0Aux.ttIntS_integral_le_HkSq (V := V) hV htt hr
  exact slotAux_slotProdCore hcont hslice hnn hint hval

/-- The `D_z²`-slot at radial level `r ≤ k`. -/
theorem slotAux_slotD2_prod {k r : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hV : Work.FTS.EllipticEst.SmoothOpen V)
    (hdd : Work.Spaces.HkMem α k (Work.Spaces.DzIter 2 V)) (hr : r ≤ k) :
    IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ∧ (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
          * Work.FTS.EllipticEst.thEta p.2
          * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
        ≤ Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V) := by
  have hcont : ContinuousOn (Function.uncurry (fun z θ : ℝ =>
      (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ =>
        (Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
          * Work.FTS.EllipticEst.thEta p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      Work.EllipticEst.Core.i0Aux.continuousOn_dzIter_weight (g := Work.Spaces.DzIter 2 V)
        (hV.DzIter 2) r
    refine h1.congr ?_
    intro p hp
    show (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2) ^ 2
        * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
      = (Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) p.1 p.2) ^ 2
        * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
    rw [slotAux_DzIter_two_comm_apply r V p.1 p.2]
  have hslice : ∀ z : ℝ, 0 < z → IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
    intro z hz
    have h1 := Work.EllipticEst.Core.i0Aux.integrableOn_slice_summand
      (g := Work.Spaces.DzIter 2 V) (hV.DzIter 2) hdd hr hz
    refine h1.congr (Filter.Eventually.of_forall fun θ => ?_)
    show (Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ
      = (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ
    rw [slotAux_DzIter_two_comm_apply r V z θ]
  have hnn : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      0 ≤ (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ :=
    fun z θ _ hθ => mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Work.EllipticEst.Core.i0Aux.thEta_nonneg_Iθ hθ)
  have hpt : ∀ z : ℝ, Work.EllipticEst.Core.ddIntS (Work.Spaces.DzIter r V) z
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
    intro z
    rw [Work.EllipticEst.Core.ddIntS, ← MeasureTheory.integral_const_mul,
      slotAux_DzIter_two_eq (Work.Spaces.DzIter r V)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    ring
  have hint : IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iz :=
    (Work.EllipticEst.Core.i0Aux.ddIntS_integrableOn (V := V) hV hdd hr).congr
      (Filter.Eventually.of_forall fun z => hpt z)
  have hval : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) ≤ Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V) := by
    calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * Work.FTS.EllipticEst.thEta θ)
        = ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ddIntS (Work.Spaces.DzIter r V) z := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          exact (hpt z).symm
      _ ≤ Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V) :=
          Work.EllipticEst.Core.i0Aux.ddIntS_integral_le_HkSq (V := V) hdd hr
  exact slotAux_slotProdCore hcont hslice hnn hint hval

end Work.FTS.EllSol.PkgK5.TraceEngine
end
end
-- ===== merged: Submission.Work.FTS.EllSol.Shift2Flat.reflectData =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.Shift2Flat

open MeasureTheory Set
open scoped Real

/-! ## Pointwise derivative identities for the time reversal `t ↦ -t`

For `w = (t,θ) ↦ u (-t) θ` (the time reversal of the datum `u`) the partial derivatives obey

* `∂_t w (t,θ) = - ∂_t u (-t,θ)` (one sign flip),
* `∂_t² w (t,θ) = ∂_t²u (-t,θ)`   (two sign flips, hence none),
* `∂_θ w (t,θ) = ∂_θ u (-t,θ)` and `∂_θ² w (t,θ) = ∂_θ²u (-t,θ)`.

None of these needs a regularity hypothesis: `deriv` is total and `deriv_comp_neg` is
unconditional, and the `θ`-identities are definitional.  This is what turns each slot of the
reflected data into the time-reversal of the corresponding slot of the original datum, so that
the (measure preserving, see `SpecAux.timFlipIntegral`) reflection `(t,θ) ↦ (-t,θ)` transfers
the hypotheses to the conclusions. -/

/-- `∂_t` of the time-reversed datum picks up a sign. -/
theorem pz_timeReflect (u : ℝ → ℝ → ℝ) (t θ : ℝ) :
    Work.Spaces.pz (fun t θ => u (-t) θ) t θ = -Work.Spaces.pz u (-t) θ := by
  simp only [Work.Spaces.pz]
  exact deriv_comp_neg (f := fun s => u s θ) (x := t)

/-- `∂_t²` of the time-reversed datum does not pick up a sign (the two sign flips cancel). -/
theorem pz_pz_timeReflect (u : ℝ → ℝ → ℝ) (t θ : ℝ) :
    Work.Spaces.pz (Work.Spaces.pz (fun t θ => u (-t) θ)) t θ
      = Work.Spaces.pz (Work.Spaces.pz u) (-t) θ := by
  have hfun : (fun s => Work.Spaces.pz (fun t θ => u (-t) θ) s θ)
      = fun s => -(fun a => Work.Spaces.pz u a θ) (-s) := by
    funext s
    exact pz_timeReflect u s θ
  show deriv (fun s => Work.Spaces.pz (fun t θ => u (-t) θ) s θ) t
      = deriv (fun a => Work.Spaces.pz u a θ) (-t)
  rw [hfun]
  have hneg : deriv (fun s => -(fun a => Work.Spaces.pz u a θ) (-s)) t
      = -deriv (fun s => (fun a => Work.Spaces.pz u a θ) (-s)) t := deriv.neg
  have hcomp : deriv (fun s => (fun a => Work.Spaces.pz u a θ) (-s)) t
      = -deriv (fun a => Work.Spaces.pz u a θ) (-t) :=
    deriv_comp_neg (fun a => Work.Spaces.pz u a θ) t
  rw [hneg, hcomp, neg_neg]


/-- `∂_θ²` of the time-reversed datum is the time-reversal of `∂_θ²u`. -/
theorem pth_pth_timeReflect (u : ℝ → ℝ → ℝ) (t θ : ℝ) :
    Work.Spaces.pth (Work.Spaces.pth (fun t θ => u (-t) θ)) t θ
      = Work.Spaces.pth (Work.Spaces.pth u) (-t) θ := rfl

/-- The reflection `(t,θ) ↦ (-t,θ)` transfers `IntegrableOn`-ness on the strip
`univ ×ˢ Iθ` to the reflected function (specialisation of `SpecAux.timFlipIntegral`). -/
theorem integrableOn_timeReflect {F : ℝ × ℝ → ℝ}
    (hF : MeasureTheory.IntegrableOn F (Set.univ ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F (-p.1, p.2))
      (Set.univ ×ˢ Work.Spaces.Iθ) :=
  (Work.FTS.EllSol.SpecAux.timFlipIntegral F hF).1

/-- **Time reflection of the data.**

Given `u` with the three `σ_η`-weighted slots of `(∂_t - b)u` finite on the strip
`ℝ × Iθ`, the time-reversed datum `(t,θ) ↦ u (-t) θ` satisfies the same hypotheses with
parameter `-b`: the operator `∂_t - b` becomes `-(∂_t + b)`, and since all slots are
*squares* the reflection transports them; the reflection also preserves the `C²`-regularity on
the open strip and the two boundary values. -/
theorem reflectData (b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (h0 : ∀ t : ℝ, u t 0 = 0) (hπ : ∀ t : ℝ, u t (Real.pi / 2) = 0)
    (hV : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ))
    (hZ : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz (Work.Spaces.pz u) p.1 p.2 - 2 * b * Work.Spaces.pz u p.1 p.2
          + b ^ 2 * u p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ))
    (hQ : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pth (Work.Spaces.pth u) p.1 p.2) ^ 2 * Work.FTS.EllipticEst.sEta p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ)) :
    ContDiffOn ℝ 2 (Function.uncurry (fun t θ => u (-t) θ))
        (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) ∧
      (∀ t : ℝ, (fun t θ => u (-t) θ) t 0 = 0) ∧
      (∀ t : ℝ, (fun t θ => u (-t) θ) t (Real.pi / 2) = 0) ∧
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz (fun t θ => u (-t) θ) p.1 p.2
          - (-b) * (fun t θ => u (-t) θ) p.1 p.2) ^ 2
          * Work.FTS.EllipticEst.sEta p.2) (Set.univ ×ˢ Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pz (Work.Spaces.pz (fun t θ => u (-t) θ)) p.1 p.2
          - 2 * (-b) * Work.Spaces.pz (fun t θ => u (-t) θ) p.1 p.2
          + (-b) ^ 2 * (fun t θ => u (-t) θ) p.1 p.2) ^ 2
          * Work.FTS.EllipticEst.sEta p.2) (Set.univ ×ˢ Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pth (Work.Spaces.pth (fun t θ => u (-t) θ)) p.1 p.2) ^ 2
          * Work.FTS.EllipticEst.sEta p.2) (Set.univ ×ˢ Work.Spaces.Iθ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- joint `C²`-regularity is preserved by the (smooth, strip preserving) reversal
    have hfun : Function.uncurry (Work.FTS.EllSol.SpecAux.timFlip u)
        = Function.uncurry (fun t θ => u (-t) θ) := rfl
    rw [← hfun]
    exact Work.FTS.EllSol.SpecAux.timFlip_strip_contDiffOn u hu
  · intro t
    simpa using h0 (-t)
  · intro t
    simpa using hπ (-t)
  · -- `(∂_t + b)w` slot: the reflection of the `(∂_t - b)u` slot
    have h1 := integrableOn_timeReflect hV
    have heq : (fun p : ℝ × ℝ =>
          (Work.Spaces.pz (fun t θ => u (-t) θ) p.1 p.2
            - (-b) * (fun t θ => u (-t) θ) p.1 p.2) ^ 2
            * Work.FTS.EllipticEst.sEta p.2)
        = fun p : ℝ × ℝ =>
          (Work.Spaces.pz u (-p.1) p.2 - b * u (-p.1) p.2) ^ 2
            * Work.FTS.EllipticEst.sEta p.2 := by
      funext p
      rw [pz_timeReflect u p.1 p.2]
      ring
    rw [heq]
    exact h1
  · -- `(∂_t + b)²w` slot: the reflection of the `(∂_t - b)²u` slot
    have h2 := integrableOn_timeReflect hZ
    have heq : (fun p : ℝ × ℝ =>
          (Work.Spaces.pz (Work.Spaces.pz (fun t θ => u (-t) θ)) p.1 p.2
            - 2 * (-b) * Work.Spaces.pz (fun t θ => u (-t) θ) p.1 p.2
            + (-b) ^ 2 * (fun t θ => u (-t) θ) p.1 p.2) ^ 2
            * Work.FTS.EllipticEst.sEta p.2)
        = fun p : ℝ × ℝ =>
          (Work.Spaces.pz (Work.Spaces.pz u) (-p.1) p.2
            - 2 * b * Work.Spaces.pz u (-p.1) p.2 + b ^ 2 * u (-p.1) p.2) ^ 2
            * Work.FTS.EllipticEst.sEta p.2 := by
      funext p
      rw [pz_pz_timeReflect u p.1 p.2, pz_timeReflect u p.1 p.2]
      ring
    rw [heq]
    exact h2
  · -- `∂_θ²w` slot: the reversal acts on `t` only, so this is the reflection of the
    -- `∂_θ²u` slot verbatim
    have h3 := integrableOn_timeReflect hQ
    have heq : (fun p : ℝ × ℝ =>
          (Work.Spaces.pth (Work.Spaces.pth (fun t θ => u (-t) θ)) p.1 p.2) ^ 2
            * Work.FTS.EllipticEst.sEta p.2)
        = fun p : ℝ × ℝ =>
          (Work.Spaces.pth (Work.Spaces.pth u) (-p.1) p.2) ^ 2
            * Work.FTS.EllipticEst.sEta p.2 := by
      funext p
      rw [pth_pth_timeReflect u p.1 p.2]
    rw [heq]
    exact h3

end Work.FTS.EllSol.Shift2Flat
end
-- ===== merged: Submission.Work.FTS.EllSol.Shift2Flat.reflectMixed =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project (area `FTS.EllSol`).

# Time reversal of the *mixed* slot (`∂_θ∂_z u - b ∂_θu`)

The `b ≤ 0` branch of the shifted Agmon passage is handled by the time reversal
`t ↦ -t`: it turns the operator `L_b = ∂_t - b` into `-L_{-b}`, and since every slot of the
estimate is a *square*, the reversal transports the slot to the reflected datum.  This file
proves the transport for the mixed slot, i.e.

`∫⁻_{(t,θ) ∈ ℝ × [0,π/2]} (∂_θ∂_z u - b ∂_θu)² sin(2θ)^{-η}
   = ∫⁻ (∂_θ∂_z ũ + b ∂_θũ)² sin(2θ)^{-η}`,  `ũ(t,θ) = u(-t,θ)`.

The mathematical content is exactly the change of variables `t ↦ -t` (which preserves the
Lebesgue measure of `ℝ × [0,π/2]`) combined with the pointwise derivative identities

* `∂_z ũ(t,θ) = -(∂_z u)(-t,θ)`, hence `∂_θ∂_z ũ(t,θ) = -(∂_θ∂_zu)(-t,θ)`;
* `∂_θ ũ(t,θ) = (∂_θu)(-t,θ)`.

Both hold *unconditionally* (Mathlib's `deriv` is total, and `deriv_comp_neg`/`deriv.neg`
are unconditional), so the hypothesis `hu` — which makes the slot meaningful — is not
needed in the proof.  The assignment is a genuine *lintegral* identity, so no measurability
of the integrand is available; we use `MeasurableEmbedding.lintegral_map`, which applies to
arbitrary `ℝ≥0∞`-valued functions.
-/

namespace Work.FTS.EllSol.Shift2Flat

open MeasureTheory Set
open scoped ENNReal

noncomputable section

set_option autoImplicit false

/-- The time reflection `(t,θ) ↦ (-t,θ)` preserves the restricted Lebesgue measure
`(dz ⊗ dθ)|_{univ ×ˢ Iθ}`: the reflection is the product of the (measure preserving)
negation on `ℝ` with the identity on `Iθ`, and `univ ×ˢ Iθ` is invariant under it. -/
private theorem map_reflect_restrict_Iθ :
    Measure.map (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ))
        ((volume : Measure (ℝ × ℝ)).restrict ((univ : Set ℝ) ×ˢ Work.Spaces.Iθ))
      = (volume : Measure (ℝ × ℝ)).restrict ((univ : Set ℝ) ×ˢ Work.Spaces.Iθ) := by
  -- `univ ×ˢ Iθ` with the product measure is `volume ⊗ (volume|_{Iθ})`.
  have hkey : (volume : Measure ℝ).prod (volume.restrict Work.Spaces.Iθ)
      = (volume : Measure (ℝ × ℝ)).restrict ((univ : Set ℝ) ×ˢ Work.Spaces.Iθ) := by
    have h := Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (univ : Set ℝ) Work.Spaces.Iθ
    rwa [Measure.restrict_univ] at h
  have hmap' : Measure.map (Prod.map Neg.neg id)
        ((volume : Measure ℝ).prod (volume.restrict Work.Spaces.Iθ))
      = (volume : Measure ℝ).prod (volume.restrict Work.Spaces.Iθ) := by
    have h := (MeasurePreserving.prod
      (Measure.measurePreserving_neg (volume : Measure ℝ))
      (MeasurePreserving.id (volume.restrict Work.Spaces.Iθ)))
    simpa using h.map_eq
  rw [← hkey]
  exact hmap'

/-- Change of variables for the Lebesgue integral over `univ ×ˢ Iθ` under the time
reflection.  The integrand is an arbitrary `ℝ≥0∞`-valued function: no measurability
hypothesis is needed, because the reflection is a measurable embedding
(`MeasurableEmbedding.lintegral_map`). -/
private theorem lintegral_reflect_Iθ (F : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ p in (univ : Set ℝ) ×ˢ Work.Spaces.Iθ, F (-p.1, p.2))
      = ∫⁻ p in (univ : Set ℝ) ×ˢ Work.Spaces.Iθ, F p := by
  have hemb : MeasurableEmbedding (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ)) :=
    MeasurableEmbedding.prodMap (measurableEmbedding_neg)
      (MeasurableEmbedding.id : MeasurableEmbedding (id : ℝ → ℝ))
  have hfun : (fun p : ℝ × ℝ => F (-p.1, p.2))
      = fun p : ℝ × ℝ => F (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ) p) := by
    funext p
    simp [Prod.map_apply', id_eq]
  rw [hfun]
  calc ∫⁻ p, F (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ) p)
        ∂((volume : Measure (ℝ × ℝ)).restrict ((univ : Set ℝ) ×ˢ Work.Spaces.Iθ))
      = ∫⁻ p, F p ∂(Measure.map (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ))
          ((volume : Measure (ℝ × ℝ)).restrict ((univ : Set ℝ) ×ˢ Work.Spaces.Iθ))) :=
        (hemb.lintegral_map F).symm
    _ = ∫⁻ p, F p ∂((volume : Measure (ℝ × ℝ)).restrict ((univ : Set ℝ) ×ˢ Work.Spaces.Iθ)) := by
        rw [map_reflect_restrict_Iθ]

theorem reflectMixed (b : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    (∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal
        ((Work.Spaces.pth (Work.Spaces.pz u) p.1 p.2 - b * Work.Spaces.pth u p.1 p.2) ^ 2
          * Work.FTS.EllipticEst.sEta p.2))
      = (∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal
        ((Work.Spaces.pth (Work.Spaces.pz (fun t θ => u (-t) θ)) p.1 p.2
            - (-b) * Work.Spaces.pth (fun t θ => u (-t) θ) p.1 p.2) ^ 2
          * Work.FTS.EllipticEst.sEta p.2)) := by
  -- `∂_θ∂_z` of the reflected datum is minus `∂_θ∂_zu` of `u`, evaluated at `-t`.
  have hpthpz : ∀ t θ : ℝ,
      Work.Spaces.pth (Work.Spaces.pz (fun t θ => u (-t) θ)) t θ
        = - Work.Spaces.pth (Work.Spaces.pz u) (-t) θ := by
    intro t θ
    have h1 : (fun θ' => Work.Spaces.pz (fun t θ => u (-t) θ) t θ')
        = fun θ' => - Work.Spaces.pz u (-t) θ' := by
      funext θ'
      exact deriv_comp_neg (f := fun s => u s θ') (x := t)
    change deriv (fun θ' => Work.Spaces.pz (fun t θ => u (-t) θ) t θ') θ
      = - deriv (fun θ' => Work.Spaces.pz u (-t) θ') θ
    rw [h1]
    exact deriv.neg
  -- `∂_θ` of the reflected datum is `∂_θu` of `u`, evaluated at `-t` (definitionally).
  have hpth : ∀ t θ : ℝ, Work.Spaces.pth (fun t θ => u (-t) θ) t θ
      = Work.Spaces.pth u (-t) θ := fun t θ => rfl
  -- hence the reflected integrand is the original one composed with the reflection.
  have hfun : (fun p : ℝ × ℝ => ENNReal.ofReal
        ((Work.Spaces.pth (Work.Spaces.pz (fun t θ => u (-t) θ)) p.1 p.2
            - (-b) * Work.Spaces.pth (fun t θ => u (-t) θ) p.1 p.2) ^ 2
          * Work.FTS.EllipticEst.sEta p.2))
      = fun p : ℝ × ℝ => ENNReal.ofReal
        ((Work.Spaces.pth (Work.Spaces.pz u) (-p.1) p.2 - b * Work.Spaces.pth u (-p.1) p.2) ^ 2
          * Work.FTS.EllipticEst.sEta p.2) := by
    funext p
    rw [hpthpz p.1 p.2, hpth p.1 p.2]
    congr 1
    ring
  rw [hfun]
  exact (lintegral_reflect_Iθ (fun p : ℝ × ℝ => ENNReal.ofReal
      ((Work.Spaces.pth (Work.Spaces.pz u) p.1 p.2 - b * Work.Spaces.pth u p.1 p.2) ^ 2
        * Work.FTS.EllipticEst.sEta p.2))).symm

end

end Work.FTS.EllSol.Shift2Flat
end
-- ===== merged: Submission.Work.FTS.EllSol.ShiftFT.ShiftPrimDefs =====
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

/-- The shifted operator `L_b u = ∂_t u - b·u`. -/
def sh (b : ℝ) (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun t θ => Work.Spaces.pz u t θ - b * u t θ

/-- Iterated shifted operator `L_b^{n} u`. -/
def shIter : ℕ → ℝ → (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)
  | 0, _, u => u
  | n + 1, b, u => sh b (shIter n b u)

@[simp] theorem shIter_zero (b : ℝ) (u : ℝ → ℝ → ℝ) : shIter 0 b u = u := rfl
@[simp] theorem shIter_succ (n : ℕ) (b : ℝ) (u : ℝ → ℝ → ℝ) :
    shIter (n + 1) b u = sh b (shIter n b u) := rfl


/-- The backward particular solution of `L_b G = chi N · v` (`v = L_b u`), used for `b ≥ 0`.
It is the interval integral of `e^{-bs}(chi N)'·u` over `s ∈ [t, 2N]`, which agrees with the
improper integral `∫_t^∞ e^{-bs}(chi N)'·u ds` because `(chi N)'` is supported in `[-2N,2N]`. -/
def Gc (N b : ℝ) (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun t θ =>
  Work.FTS.EllSol.Trunc.chi N t * u t θ
    + Real.exp (b * t)
        * ∫ s in t..(2 * N),
            Real.exp (-(b * s)) * deriv (Work.FTS.EllSol.Trunc.chi N) s * u s θ


/-- The `t`-cutoff killing the exponentially small tail: `chi (4096·N)`. -/
def phiTr (N : ℝ) (t : ℝ) : ℝ := Work.FTS.EllSol.Trunc.chi (4096 * N) t

/-- The truncated data (backward solution): `u_N = phiTr N · G_N`. -/
def uTr (N b : ℝ) (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun t θ => phiTr N t * Gc N b u t θ


/-! ## Elementary facts about the cutoffs -/

theorem phiTr_eq_chi (N t : ℝ) : phiTr N t = Work.FTS.EllSol.Trunc.chi (4096 * N) t := rfl

theorem phiTr_contDiff (n : ℕ) (N : ℝ) : ContDiff ℝ n (phiTr N) :=
  Work.FTS.EllSol.Trunc.chi_contDiff n (4096 * N)

theorem phiTr_nonneg (N t : ℝ) : 0 ≤ phiTr N t := Work.FTS.EllSol.Trunc.chi_nonneg _ _

theorem phiTr_le_one (N t : ℝ) : phiTr N t ≤ 1 := Work.FTS.EllSol.Trunc.chi_le_one _ _

/-- `phiTr N = 1` on `[-2N, 2N]` (for `N ≥ 0`), so the second cutoff does not disturb the
support of `chi N`. -/
theorem phiTr_eq_one {N t : ℝ} (hN : 0 < N) (ht : |t| ≤ 2 * N) : phiTr N t = 1 := by
  refine Work.FTS.EllSol.Trunc.chi_eq_one (N := 4096 * N) (by linarith) ?_
  calc |t| ≤ 2 * N := ht
    _ ≤ 4096 * N := by nlinarith

/-- `phiTr N = 0` off `[-8192N, 8192N]`. -/
theorem phiTr_eq_zero {N t : ℝ} (hN : 0 < N) (ht : 2 * (4096 * N) ≤ |t|) : phiTr N t = 0 :=
  Work.FTS.EllSol.Trunc.chi_eq_zero (N := 4096 * N) (by linarith) ht


end

end Work.FTS.EllSol.ShiftFT
end
-- ===== merged: Submission.Work.FTS.EllSol.Trunc.chiDeriv2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.Trunc

open Filter Set
open scoped Topology

/-- `deriv (deriv tk)` is bounded: it is continuous and vanishes off `[-2,2]`. -/
theorem exists_bound_deriv2_tk : ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, |deriv (deriv tk) t| ≤ K := by
  have hcont : Continuous (deriv (deriv tk)) :=
    ((tk_contDiff 2).deriv').continuous_deriv_one
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (-2:ℝ)) (b := 2)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max K 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Set.Icc (-2:ℝ) 2
  · exact le_trans (hK t ht) (le_max_left _ _)
  · have h0 : deriv (deriv tk) t = 0 := by
      have htk : tk =ᶠ[𝓝 t] (fun _ : ℝ => (0:ℝ)) := by
        have hopen : IsOpen {s : ℝ | 2 < |s|} := isOpen_lt continuous_const continuous_abs
        have hmem : t ∈ {s : ℝ | 2 < |s|} := by
          change 2 < |t|
          exact lt_of_not_ge fun hle => ht (Set.mem_Icc.mpr (abs_le.mp hle))
        filter_upwards [hopen.mem_nhds hmem] with s hs
        exact tk_eq_zero (le_of_lt hs)
      have hd : deriv tk =ᶠ[𝓝 t] (fun _ : ℝ => (0:ℝ)) := by
        simpa using htk.deriv
      rw [hd.deriv_eq, deriv_const]
    rw [h0, abs_zero]
    exact le_max_right _ _

/-- The second derivative of the cutoff at scale `N`. -/
theorem deriv2_chi_eq (N t : ℝ) :
    deriv (deriv (chi N)) t = deriv (deriv tk) (t / N) / N ^ 2 := by
  have hchi : deriv (chi N) = fun s : ℝ => deriv tk (s / N) / N := by
    funext s; exact deriv_chi_eq N s
  rw [hchi, deriv_div_const]
  have hcomp : deriv (fun s : ℝ => deriv tk (s / N)) t
      = deriv (deriv tk) (t / N) * deriv (fun s : ℝ => s / N) t := by
    rw [show (fun s : ℝ => deriv tk (s / N))
        = (deriv tk) ∘ (fun s : ℝ => s / N) from rfl]
    exact deriv_comp t
      ((ContDiff.differentiable_deriv_two (tk_contDiff 2)).differentiableAt)
      (differentiableAt_id.div_const N)
  rw [hcomp, deriv_div_const, deriv_id'']
  ring


end Work.FTS.EllSol.Trunc
end
-- ===== merged: Submission.Work.FTS.EllSol.Trunc.chiMulDerivs =====
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

/-! ## Slice differentiability -/

/-- The `z`-partial of a function of class `C^{n+1}` on an open set is of class `C^n` there.
Finite-order version of `Work.Spaces.contDiffOn_uncurry_pz`. -/
theorem contDiffOn_uncurry_pz_succ {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) (n : ℕ)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pz G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (1, 0) := by
    intro p hp
    exact Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (by simp)
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- The `θ`-partial of a function of class `C^{n+1}` on an open set is of class `C^n` there.
Finite-order version of `Work.Spaces.contDiffOn_uncurry_pth`. -/
theorem contDiffOn_uncurry_pth_succ {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) (n : ℕ)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (0, 1) := by
    intro p hp
    exact Work.Spaces.pth_eq_fderiv
      ((h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (by simp)
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- Both curried slices of a function of class `C^n` (`n > 0`) on an open set are
differentiable at every point of the set. -/
theorem curry_differentiableAt_of_contDiffOn {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {n : ℕ} (hn : 0 < n) (h : ContDiffOn ℝ n (Function.uncurry G) V) {z θ : ℝ}
    (hmem : (z, θ) ∈ V) :
    DifferentiableAt ℝ (fun z' => G z' θ) z ∧ DifferentiableAt ℝ (fun θ' => G z θ') θ := by
  have hd : DifferentiableAt ℝ (Function.uncurry G) (z, θ) :=
    (h.contDiffAt (hV.mem_nhds hmem)).differentiableAt (by simpa using hn.ne')
  exact ⟨Work.Spaces.differentiableAt_curry_left hd, Work.Spaces.differentiableAt_curry_right hd⟩

/-! ## Product rules for a `θ`-independent left factor -/

/-- `∂_z(c · f) = (∂_z c) f + c ∂_z f` for a function `c` of the single variable `z`. -/
theorem pz_mul_slice (c : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (t θ : ℝ)
    (hc : DifferentiableAt ℝ c t) (hf : DifferentiableAt ℝ (fun s => f s θ) t) :
    Work.Spaces.pz (fun s θ => c s * f s θ) t θ
      = deriv c t * f t θ + c t * Work.Spaces.pz f t θ := by
  show deriv (fun s => c s * f s θ) t = deriv c t * f t θ + c t * deriv (fun s => f s θ) t
  rw [show (fun s => c s * f s θ) = c * (fun s => f s θ) from rfl, deriv_mul hc hf]

/-- `∂_z²(c · f) = (∂_z² c) f + 2 (∂_z c)(∂_z f) + c ∂_z² f`. -/
theorem pz_pz_mul_slice (c : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (t θ : ℝ)
    (hc : Differentiable ℝ c) (hc1 : Differentiable ℝ (deriv c))
    (hf : Differentiable ℝ (fun s => f s θ))
    (hf1 : Differentiable ℝ (fun s => Work.Spaces.pz f s θ)) :
    Work.Spaces.pz (Work.Spaces.pz (fun s θ => c s * f s θ)) t θ
      = deriv (deriv c) t * f t θ + 2 * deriv c t * Work.Spaces.pz f t θ
        + c t * Work.Spaces.pz (Work.Spaces.pz f) t θ := by
  have hpt : (fun s => Work.Spaces.pz (fun s θ => c s * f s θ) s θ)
      = fun s => deriv c s * f s θ + c s * Work.Spaces.pz f s θ :=
    funext fun s => pz_mul_slice c f s θ (hc s) (hf s)
  show deriv (fun s => Work.Spaces.pz (fun s θ => c s * f s θ) s θ) t
    = deriv (deriv c) t * f t θ + 2 * deriv c t * Work.Spaces.pz f t θ
      + c t * Work.Spaces.pz (Work.Spaces.pz f) t θ
  rw [hpt]
  rw [show (fun s => deriv c s * f s θ + c s * Work.Spaces.pz f s θ)
      = (deriv c * (fun s => f s θ)) + (c * (fun s => Work.Spaces.pz f s θ)) from rfl]
  rw [deriv_add ((hc1 t).mul (hf t)) ((hc t).mul (hf1 t))]
  rw [deriv_mul (hc1 t) (hf t), deriv_mul (hc t) (hf1 t)]
  simp only [Work.Spaces.pz]
  ring





/-! ## The requested identities -/


end

end Work.FTS.EllSol.Trunc
end
-- ===== merged: Submission.Work.FTS.EllSol.VopAux.sliceW_pthIter2_eq_sliceW_sliceV =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.VopAux

/-
# The single-slice functional of `D_z^j (∂_θ² f)` and of the second derivative of the slice agree

For `f` of class `C^∞` on the open quadrant, `z > 0` and interior angles `θ ∈ (0,π/2)`:

  `sliceW K α (fun θ' => D_z^j (pthIter 2 f) z θ') θ
     = sliceW K α (sliceV (fun θ' => D_z^j f z θ')) θ`,

where `sliceW K α u θ = (u θ)²thEta θ + ∑_{1≤i≤K}(L^i u θ)²thGam α θ` (see
`Submission/Work/FTS/EllSol/VopAux/SliceTraceDefs.lean`), `sliceV u = deriv (deriv u)` and
`pthIter 2 f = ∂_θ² f`.

This is the bridge that lets the single-slice estimate be applied to the `j`-th slice of `f` with
the datum taken from the `j`-th slice group of `∂_θ² f`.

ROUTE. First, the two functions of `θ'` agree at every `θ' ∈ (0,π/2)`:
`pthIter 2 (D_z^j f) z θ' = D_z^j (pthIter 2 f) z θ'` — the open-quadrant Clairaut identity,
which is `pth_DzIter_eqOn_of_isOpen` from
`Submission/Work/FTS/EllipticEst/ThetaU/OpenSliceAux/pth_DzIter_eqOn_of_isOpen.lean` applied twice
(it works for an arbitrary open set `V` with the raw `∀ n, ContDiffOn ℝ n` hypothesis; take
`V = Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2)` and the open-quadrant smoothness of `f`; the hypothesis for the
second application, smoothness of `pth f`, comes from `SmoothOpen.pth`-style closure, which for the
raw `∀ n` hypothesis is `Work.FTS.LocData.contDiffOn_pth`). Since
`sliceV (fun θ' => D_z^j f z θ') = fun θ' => pthIter 2 (D_z^j f) z θ'` definitionally, the two
functions agree on the whole open interval `(0,π/2)`.
Second, two functions equal on the open interval have the same `L`-iterates at every interior
point: `deriv` is local, so `Filter.EventuallyEq.deriv_eq` (with `isOpen_Ioo.mem_nhds` at an
interior point) gives equality of the first derivatives on `(0,π/2)`, and induction on `i` gives
`LopIter i u₁ θ = LopIter i u₂ θ` for `θ ∈ (0,π/2)`. Both terms of `sliceW` are then equal,
including the zeroth-order terms `(u θ)²thEta θ`.

The first step is available ready-made: `Work.FTS.EllSol.WeakSlice.sliceV_DzIter_smoothOpen`
(`Submission/Work/FTS/EllSol/WeakSlice/sliceV_DzIter_smoothOpen.lean`) states exactly
`deriv (deriv (fun θ' => D_z^j f z θ')) θ' = D_z^j (∂_θ² f) z θ'` for a datum which is `C^∞` on
the open quadrant, i.e. for the `SmoothOpen f` obtained from `hf` by
`Work.FTS.EllipticEst.smoothOpen_iff_forall`.  The second step is the *locality* of the
functional: `sliceW` only sees the germ of its argument, since `LopIter m u θ = LopIter m v θ`
whenever `u =ᶠ[𝓝 θ] v` (`Work.FTS.EllipticEst.LopIter_congr_nhds`, proved by induction on `m`
from the locality of `deriv`).  Together with the agreement of the two functions at every
interior angle this closes the statement.
-/
/-- The single-slice functional `sliceW` only sees the germ of its argument: two functions which
agree near `θ` have the same value of `sliceW K α · θ`, because both the zeroth-order term and
every `L`-iterate are local. -/
lemma sliceW_congr_nhds {u v : ℝ → ℝ} {θ : ℝ} (h : u =ᶠ[𝓝 θ] v) (K : ℕ) (α : ℝ) :
    sliceW K α u θ = sliceW K α v θ := by
  have hθ : u θ = v θ := h.self_of_nhds
  rw [sliceW, sliceW, hθ]
  congr 1
  exact Finset.sum_congr rfl fun i _ =>
    congrArg (fun x => x ^ 2 * Work.FTS.EllipticEst.thGam α θ)
      (Work.FTS.EllipticEst.LopIter_congr_nhds h i)

theorem sliceW_pthIter2_eq_sliceW_sliceV (α : ℝ) (K j : ℕ) (f : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z)
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllSol.VopAux.sliceW K α
          (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ') θ
        = Work.FTS.EllSol.VopAux.sliceW K α
            (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ := by
  have hfS : Work.FTS.EllipticEst.SmoothOpen f :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall f).mpr hf
  -- the two functions agree at every interior angle
  have hpt : ∀ θ' ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ'
        = Work.FTS.EllipticEst.sliceV (fun θ'' => Work.Spaces.DzIter j f z θ'') θ' :=
    fun θ' hθ' =>
      (Work.FTS.EllSol.WeakSlice.sliceV_DzIter_smoothOpen hfS j hz hθ').symm
  intro θ hθ
  -- hence they agree near `θ`, and `sliceW` is local
  refine sliceW_congr_nhds (v := fun θ' => Work.FTS.EllipticEst.sliceV
      (fun θ'' => Work.Spaces.DzIter j f z θ'') θ') ?_ K α
  filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
  exact hpt θ' hθ'

end Work.FTS.EllSol.VopAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.intervalIntegrable_rpow_Fstar =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol

open MeasureTheory Set Filter
open scoped Real Topology

/-! ## Interval integrability of `s^{(5-α)/α} F_*(g)(s)`

The singular radial piece `Ḡ(α,g)(z) = -(3/(4α)) z^{-5/α} ∫_0^z s^{(5-α)/α} F_*(g)(s) ds`
of §'The singular term' is only a genuine integral if the integrand
`s ↦ s^{(5-α)/α} · F_*(g)(s)` is interval integrable on `[0,z]`; this is what is proved here
for every datum `g` that is `C^∞` on the open half-strip and lies honestly in `ℋ⁴`.

The mathematics is a two-step domination, valid for *every* `α > 0` (no `α ≤ 1` is needed):

* **Cauchy–Schwarz against the weight.**  `Cert.Fstar_mul_w_le_sqrt` gives
  `|F_*(g)(s)| · w(s) ≤ √((π/2) ∫_θ (g(s,θ) w(s)/sin(2θ)^{η/2})² dθ)`, and the angular
  integral is at most the `θ`-slice `G(s) = ∫_θ HkIntegrand α 4 g s θ` of the `ℋ⁴`-integrand
  (`Cert.slice_le_HkIntegrand`).  Since `1/w(s) = s²/(1+s)² ≤ s²`, this yields
  `|F_*(g)(s)| ≤ √(π/2)·√(G(s))·s²`.
* **The radial exponents.**  Multiplying by `s^c`, `c = (5-α)/α`,
  `|s^c F_*(g)(s)| ≤ √(π/2)·s^{c+2}·√(G(s))`; here `c + 2 = (5+α)/α > 0`, so on `(0,z]` the
  factor `s^{c+2}` is bounded by `z^{c+2}` (this is exactly what makes the argument work also
  for `α > 5`, where `c < 0` and `s^c` alone is unbounded at `0`).  Finally `√X ≤ 1 + X`, and
  `s ↦ 1 + G(s)` is integrable on the *finite* interval `(0,z]` by `HkMem`, so the majorant
  `√(π/2)·z^{c+2}·(1 + G(s))` is integrable.

The only remaining input is measurability: `F_*(g) = B_0` is the zeroth radial moment, hence
continuous on `(0,∞)` by `continuousOn_Bmom`. -/


end Work.FTS.EllSol
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.Gsing_identities_eh =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## The smooth angular integrand of the moment

`Work.FTS.EllipticEst.Cert.FstarInt α Ψ` is the reformulation of
`bslOp α Ψ · sinθcos²θ` in which the `tan`-pole has been cancelled by the weight: it is
smooth on a neighbourhood of the closed quadrant as soon as `Ψ` is.  This is the first
step of the smoothness of the angular moment `F_*`: the moment of the source is the
`θ`-integral of a *smooth* function of `(z,θ)`, and parametric integrals of smooth
functions are smooth (`contDiffOn_infty_integral_Itheta_Ioi_neg_one`). -/





/-! ## Piece 1: `F_*` is `C^∞` on `(0,∞)` -/


/-! ## Piece 2: `Gsing α F` is `C^∞` on `(0,∞)` -/



/-! ## Assembly -/


end Work.FTS.EllipticEst.Cert
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.aeMixedAe_mem_of_fin =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeStep2Aux.aeMixedAe_mem_of_fin` — the reduction

For a datum `AeData α u G` (so `u` is `C^∞` on the open quadrant) the finiteness of the
*iterated* weighted Lebesgue integral

`X^𝓁 := ∫⁻ z in Iz, ∫⁻ θ in Iθ, ofReal ((z · ∂_z∂_θu)² σ(θ)) < ⊤`,  `σ = sin(2θ)^{-η}`,

implies both conjuncts of `aeMixedAe_mem`:

* the angular slices `θ ↦ (z · ∂_z∂_θu)² σ` are integrable for almost every `z > 0`, and
* the outer function `z ↦ ∫ θ in Iθ, (z · ∂_z∂_θu)² σ` is integrable on `Iz`.

The mathematics is Tonelli plus the fact that the integrand is continuous on the open
quadrant (so a.e. strongly measurable there) and nonnegative on `Iz × Iθ`.  Everything is
done in the product measure `mz.prod mθ`; the two endpoints `z = 0`, `θ = 0, π/2` are null
sets and are handled by `Measure.restrict_congr_set`.

The converse direction (the two conjuncts imply the finiteness, hence the equivalence) is
not needed downstream, and the *unconditional* statement `aeMixedAe_mem` (finiteness from
`AeData` alone) is the project's open `aePpFinite` crux, cf.
`Cores/AeStep2Aux/NOTES_aeMixedAe_mem.md`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux

set_option autoImplicit false

/-! ## The two restricted measures of the quadrant -/



/-- The open quadrant of the elliptic estimates. -/
private abbrev quad : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

/-! ## Almost everywhere strong measurability on the product -/


/-! ## The reduction -/


/-! ## The target -/


end Work.FTS.EllipticEst.Cores.AeStep2Aux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.sliceAgmonVanishing =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

noncomputable section

local notation "sigA" => Work.FTS.EllipticEst.Cores.sigA
local notation "sigDR" => Work.FTS.EllipticEst.TT.sigDR

/-!
# The vanishing-boundary Agmon interpolation on an angular slice

For `a ∈ (0,1)` and `u` of class `C²` on `(0, π/2)`, with `u → 0` at both endpoints and with
the three weighted integrals `∫ (u')²σ`, `∫ u²σ`, `∫ (u'')²σ` finite (`σ = sin(2θ)^a`), one has

  `∫ (u')²σ ≤ C √(∫ u²σ · ∫ (u'')²σ)`.

The proof has two halves.

* **The endpoint control.**  The `σ`-weighted integrability of `u''` forces `∫_0^ε |u''| < ∞`
  (`2|x| ≤ x²σ + σ⁻¹`), hence `u'` is bounded on `(0,π/2)` (`ftc_at_quarter`) and, since
  `u → 0` at the endpoints, `|u| ≤ M θ` near `0` and `|u| ≤ M(π/2 - θ)` near `π/2`.
  Consequently `|u| ≤ M sin(2θ)` and the two boundary products of `slice_ibp_light`,
  `u u' σ` and `u² σ'`, tend to `0` at both endpoints, while the three remaining
  integrability clauses of that lemma follow by domination with `σ`.

* **The interpolation.**  `slice_ibp_light` gives
  `∫ (u')²σ = -∫ u u'' σ - 2a∫ u²σ - 2a(1-a)∫ u² cos²(2θ) sin(2θ)^{a-2}`; the last two terms
  are `≤ 0` (their integrands are `≥ 0` and `0 < a < 1`), and the first is bounded by
  Cauchy–Schwarz.  This is the already-proved `sliceInterpVanishing`, applied below.
-/

/-! ## Elementary exponent identities -/

lemma rpow_one_add {y a : ℝ} (hy : 0 < y) : y ^ (1 + a) = y * y ^ a := by
  rw [Real.rpow_add hy, Real.rpow_one]

lemma mul_rpow_sub_one {y a : ℝ} (hy : 0 < y) (ha : a ≠ 0) : y * y ^ (a - 1) = y ^ a := by
  have h : (1 : ℝ) + (a - 1) ≠ 0 := by
    intro hc
    exact ha (by linarith [show (1 : ℝ) + (a - 1) = a by ring])
  rw [← Real.rpow_one_add' hy.le h, show (1 : ℝ) + (a - 1) = a by ring]

lemma mul_rpow_sub_two {y a : ℝ} (hy : 0 < y) : y ^ 2 * y ^ (a - 2) = y ^ a := by
  rw [← Real.rpow_natCast y 2, ← Real.rpow_add hy ((2 : ℕ) : ℝ) (a - 2),
    show ((2 : ℕ) : ℝ) + (a - 2) = a by ring]


/-! ## The two squeeze lemmas for the boundary limits -/

/-- Squeeze at `0⁺`: a function dominated by `A y^e` (`e > 0`) near `0` tends to `0`. -/
lemma tendsto_zero_of_abs_le_eventually {F : ℝ → ℝ} {A e ε : ℝ} (he : 0 < e) (hε : 0 < ε)
    (h : ∀ y ∈ Set.Ioo (0 : ℝ) ε, |F y| ≤ A * y ^ e) :
    Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  refine tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (f := fun y : ℝ => ‖F y‖) (g := fun y : ℝ => A * y ^ e) ?_ ?_
      (Work.FTS.EllipticEst.Cores.tendsto_const_mul_rpow_zero (A := A) he))
  · filter_upwards with y
    exact norm_nonneg (F y)
  · filter_upwards [Ioo_mem_nhdsGT hε] with y hy
    rw [Real.norm_eq_abs]
    exact h y hy

/-- The reflected squeeze, at `(π/2)⁻`. -/
lemma tendsto_zero_of_abs_le_eventually_right {F : ℝ → ℝ} {A e ε : ℝ} (he : 0 < e) (hε : 0 < ε)
    (h : ∀ y ∈ Set.Ioo (0 : ℝ) ε, |F (Real.pi / 2 - y)| ≤ A * y ^ e) :
    Tendsto F (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
  (Work.FTS.EllipticEst.Cores.tendsto_reflect_iff (Φ := F) (c := 0)).mp
    (tendsto_zero_of_abs_le_eventually he hε h)

/-- `(θ, π/2) ∈ nhdsWithin (π/2) (Iio (π/2))`. -/
lemma Ioo_mem_nhdsWithin_Iio {a b : ℝ} (hab : a < b) :
    Set.Ioo a b ∈ nhdsWithin b (Set.Iio b) := by
  have h1 : Set.Ioi a ∈ nhds b := Ioi_mem_nhds hab
  have h2 : Set.Iio b ∈ nhdsWithin b (Set.Iio b) := self_mem_nhdsWithin
  have h3 := Filter.inter_mem (nhdsWithin_le_nhds h1) h2
  rwa [Set.Ioi_inter_Iio] at h3

/-! ## Integrability of `u''` and the endpoint bounds -/

/-- `σ`-weighted `L²`-integrability of `u''` implies honest integrability of `u''`. -/
lemma integrableOn_deriv_deriv {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ}
    (hD : IntegrableOn (fun θ : ℝ => (deriv (deriv F) θ) ^ 2 * sigA α θ)
      (Set.Ioo 0 (Real.pi / 2))) :
    IntegrableOn (deriv (deriv F)) (Set.Ioo 0 (Real.pi / 2)) :=
  Work.FTS.EllipticEst.Cores.integrableOn_deriv measurableSet_Ioo (fun _ hx => hx) hD
    ((Work.FTS.EllipticEst.Cores.integrableOn_sigA_inv hα hα1).mono_set Ioo_subset_Icc_self)

/-- **Endpoint control of `u'`.**  The `σ`-weighted integrability of `u''` bounds `|u'|` on
`(0, π/2)` (the FTC identity of `ftc_at_quarter` at `θ₀ = π/4` and `|∫| ≤ ∫|·|`). -/
lemma exists_deriv_abs_bound {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ}
    (hcd : ContDiffOn ℝ 2 F (Set.Ioo 0 (Real.pi / 2)))
    (hD : IntegrableOn (fun θ : ℝ => (deriv (deriv F) θ) ^ 2 * sigA α θ)
      (Set.Ioo 0 (Real.pi / 2))) :
    ∃ M : ℝ, 0 < M ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv F θ| ≤ M := by
  have hIdd : IntegrableOn (deriv (deriv F)) (Set.Ioo 0 (Real.pi / 2)) :=
    integrableOn_deriv_deriv hα hα1 hD
  have hC1 : ContDiffOn ℝ 1 (deriv F) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hcd.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  set c : ℝ := deriv F (Real.pi / 4) - ∫ t in Set.Ioo 0 (Real.pi / 4), deriv (deriv F) t with hc
  have hftc : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv F θ - c = ∫ t in Set.Ioo 0 θ, deriv (deriv F) t :=
    Work.FTS.EllipticEst.Cores.ftc_at_quarter hC1 hIdd
  refine ⟨|c| + (∫ t in Set.Ioo 0 (Real.pi / 2), |deriv (deriv F) t|) + 1, by positivity, ?_⟩
  intro θ hθ
  have hnn : ∀ x ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ |deriv (deriv F) x| := fun x _ => abs_nonneg _
  have hmono : (∫ t in Set.Ioo 0 θ, |deriv (deriv F) t|)
      ≤ ∫ t in Set.Ioo 0 (Real.pi / 2), |deriv (deriv F) t| :=
    Work.FTS.EllipticEst.Cores.setIntegral_mono_Ioo hθ.2.le hIdd.abs hnn
  have h1 : |deriv F θ| ≤ |deriv F θ - c| + |c| := by
    have h := abs_add_le (deriv F θ - c) c
    rwa [sub_add_cancel] at h
  have h2 : |deriv F θ - c| ≤ ∫ t in Set.Ioo 0 θ, |deriv (deriv F) t| := by
    rw [hftc θ hθ]
    exact MeasureTheory.abs_integral_le_integral_abs
  linarith [h1, h2, hmono]

/-- **The left endpoint value bound**: `|u θ| ≤ M θ` (the Lipschitz bound `|u'| ≤ M` plus the
prescribed limit `u → 0` at `0⁺`). -/
lemma value_abs_le_mul_left {F : ℝ → ℝ} (hcd : ContDiffOn ℝ 2 F (Set.Ioo 0 (Real.pi / 2)))
    (hint : IntegrableOn (deriv F) (Set.Ioo 0 (Real.pi / 2)))
    (h0 : Tendsto F (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    {M : ℝ} (hMnn : 0 ≤ M) (hM : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv F θ| ≤ M) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |F θ| ≤ M * θ := by
  have hC1 : ContDiffOn ℝ 1 F (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hcd.of_le (by norm_num)
  have hC1d : ContDiffOn ℝ 1 (deriv F) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hcd.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  intro θ hθ
  have htend : Tendsto (fun θ' : ℝ => |F θ - F θ'|) (nhdsWithin 0 (Set.Ioi 0)) (nhds |F θ|) := by
    have h1 : Tendsto (fun θ' : ℝ => F θ - F θ') (nhdsWithin 0 (Set.Ioi 0)) (nhds (F θ - 0)) :=
      tendsto_const_nhds.sub h0
    simpa using h1.abs
  refine le_of_tendsto htend ?_
  filter_upwards [Ioo_mem_nhdsGT hθ.1] with θ' hθ'
  have hsub : Set.Ioo θ' θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun x hx => ⟨hθ'.1.trans hx.1, hx.2.trans hθ.2⟩
  have hul : Set.uIcc θ' θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rw [Set.uIcc_of_le hθ'.2.le]
    exact fun x hx => ⟨hθ'.1.trans_le hx.1, hx.2.trans_lt hθ.2⟩
  have hftc : F θ - F θ' = ∫ t in Set.Ioo θ' θ, deriv F t :=
    Work.FTS.EllipticEst.Cores.ftc_interior hC1 ⟨hθ'.1, hθ'.2.trans hθ.2⟩ hθ hθ'.2
      ((hC1d.continuousOn.mono hul).intervalIntegrable)
  have hInt1 : IntegrableOn (fun t : ℝ => |deriv F t|) (Set.Ioo θ' θ) :=
    (hint.mono_set hsub).abs
  have hInt2 : IntegrableOn (fun _ : ℝ => M) (Set.Ioo θ' θ) :=
    MeasureTheory.integrableOn_const (s := Set.Ioo θ' θ) (by rw [Real.volume_Ioo]; simp) (by simp)
  calc |F θ - F θ'| = |∫ t in Set.Ioo θ' θ, deriv F t| := by rw [hftc]
    _ ≤ ∫ t in Set.Ioo θ' θ, |deriv F t| := MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ t in Set.Ioo θ' θ, M :=
        MeasureTheory.setIntegral_mono_on hInt1 hInt2 measurableSet_Ioo
          (fun t ht => hM t (hsub ht))
    _ = M * (θ - θ') := by
        rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioo,
          max_eq_left (by linarith [hθ'.2]), smul_eq_mul]
        ring
    _ ≤ M * θ := by nlinarith [hMnn, hθ'.1]

/-- **The right endpoint value bound**: `|u θ| ≤ M (π/2 - θ)`. -/
lemma value_abs_le_mul_right {F : ℝ → ℝ} (hcd : ContDiffOn ℝ 2 F (Set.Ioo 0 (Real.pi / 2)))
    (hint : IntegrableOn (deriv F) (Set.Ioo 0 (Real.pi / 2)))
    (h1 : Tendsto F (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    {M : ℝ} (hMnn : 0 ≤ M) (hM : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv F θ| ≤ M) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |F θ| ≤ M * (Real.pi / 2 - θ) := by
  have hC1 : ContDiffOn ℝ 1 F (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hcd.of_le (by norm_num)
  have hC1d : ContDiffOn ℝ 1 (deriv F) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hcd.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  intro θ hθ
  have htend : Tendsto (fun θ' : ℝ => |F θ - F θ'|)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds |F θ|) := by
    have h1' : Tendsto (fun θ' : ℝ => F θ - F θ')
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (F θ - 0)) :=
      tendsto_const_nhds.sub h1
    simpa using h1'.abs
  refine le_of_tendsto htend ?_
  filter_upwards [Ioo_mem_nhdsWithin_Iio hθ.2] with θ' hθ'
  have hsub : Set.Ioo θ θ' ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun x hx => ⟨hθ.1.trans hx.1, hx.2.trans hθ'.2⟩
  have hul : Set.uIcc θ θ' ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rw [Set.uIcc_of_le hθ'.1.le]
    exact fun x hx => ⟨hθ.1.trans_le hx.1, hx.2.trans_lt hθ'.2⟩
  have hftc : F θ' - F θ = ∫ t in Set.Ioo θ θ', deriv F t :=
    Work.FTS.EllipticEst.Cores.ftc_interior hC1 hθ ⟨hθ.1.trans hθ'.1, hθ'.2⟩ hθ'.1
      ((hC1d.continuousOn.mono hul).intervalIntegrable)
  have hInt1 : IntegrableOn (fun t : ℝ => |deriv F t|) (Set.Ioo θ θ') :=
    (hint.mono_set hsub).abs
  have hInt2 : IntegrableOn (fun _ : ℝ => M) (Set.Ioo θ θ') :=
    MeasureTheory.integrableOn_const (s := Set.Ioo θ θ') (by rw [Real.volume_Ioo]; simp) (by simp)
  have hneg : F θ - F θ' = -(F θ' - F θ) := by ring
  calc |F θ - F θ'| = |F θ' - F θ| := by rw [hneg, abs_neg]
    _ = |∫ t in Set.Ioo θ θ', deriv F t| := by rw [hftc]
    _ ≤ ∫ t in Set.Ioo θ θ', |deriv F t| := MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ t in Set.Ioo θ θ', M :=
        MeasureTheory.setIntegral_mono_on hInt1 hInt2 measurableSet_Ioo
          (fun t ht => hM t (hsub ht))
    _ = M * (θ' - θ) := by
        rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioo,
          max_eq_left (by linarith [hθ'.1]), smul_eq_mul]
        ring
    _ ≤ M * (Real.pi / 2 - θ) := by nlinarith [hMnn, hθ'.2]

/-- Transfer of `IntegrableOn` from the open interval to `Iθ` (they differ by a null set). -/
lemma integrableOn_Iθ_of_Ioo {f : ℝ → ℝ}
    (h : IntegrableOn f (Set.Ioo 0 (Real.pi / 2))) : IntegrableOn f Work.Spaces.Iθ := by
  show Integrable f (volume.restrict Work.Spaces.Iθ)
  rw [Work.FTS.EllipticEst.Cores.restrict_Iθ_eq_Ioo]
  exact h


end

end Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Deleg.mixedTruncPairLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Deleg

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open Work.FTS.EllipticEst (cut cut_nonneg cut_contDiff cut_le_one)
open Work.FTS.EllipticEst.AeColl (Ptr Atr Dtr Trtr Wtr Col wt sigθ psiD Uz Vz Az
  wt_nonneg sigθ_nonneg_of_mem psiD_nonneg psiD_contDiff psiD_hasCompactSupport
  psiD_tsupport_subset' psiD_tsupport_subset_Ioo
  cut_contDiff_one cut_hasCompactSupport cut_tsupport_subset_Ioi cut_support_subset_Ioi)



/-! ## Elementary nonnegativity -/

/-- `sin(2θ)^{−η} ≥ 0` whenever `0 ≤ θ` and `2θ ≤ π` (division-free form of the
angular-boundary condition, convenient for `linarith`). -/
theorem sigθ_nonneg_of_two_mul_le {θ : ℝ} (h0 : 0 ≤ θ) (hπ : 2 * θ ≤ Real.pi) :
    0 ≤ sigθ θ := by
  rw [Work.FTS.EllipticEst.AeColl.sigθ]
  exact Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith only [h0]) hπ) _

/-- `4δ ≤ π` from the building convention `4δ ≤ π/2`. -/
theorem four_mul_le_pi_of {δ : ℝ} (hδ2 : 4 * δ ≤ Real.pi / 2) : 4 * δ ≤ Real.pi := by
  have hπ2 : Real.pi / 2 ≤ Real.pi := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    linarith only [Real.pi_pos]
  exact le_trans hδ2 hπ2

/-- `2δ ≤ π` from the building convention `4δ ≤ π/2`. -/
theorem two_mul_le_pi_of {δ : ℝ} (hδ : 0 < δ) (hδ2 : 4 * δ ≤ Real.pi / 2) :
    2 * δ ≤ Real.pi := by
  have h4 : 4 * δ ≤ Real.pi := four_mul_le_pi_of hδ2
  linarith only [h4, hδ]

/-- `0 ≤ π/2 - δ` whenever `2δ ≤ π`. -/
theorem pi_half_sub_nonneg {δ : ℝ} (h2 : 2 * δ ≤ Real.pi) : 0 ≤ Real.pi / 2 - δ := by
  have h : Real.pi / 2 - δ = (Real.pi - 2 * δ) / 2 := by ring
  rw [h]
  exact div_nonneg (by linarith only [h2]) (by norm_num)

/-- `2·(π/2) ≤ π`. -/
theorem two_mul_pi_half_le : 2 * (Real.pi / 2) ≤ Real.pi := by
  rw [show 2 * (Real.pi / 2) = Real.pi by ring]

/-- The `θ`-integral of `σ · (z ∂_z∂_θu)²` over an interval inside `[0,π/2]` is nonnegative. -/
theorem inner_nonneg {f : ℝ → ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : 2 * b ≤ Real.pi)
    (z : ℝ) :
    0 ≤ ∫ θ in Set.Ioo a b, sigθ θ * (Vz f z θ) ^ 2 := by
  refine Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.integral_nonneg_of_ae' ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  refine Eventually.of_forall fun θ hθ => ?_
  refine mul_nonneg (sigθ_nonneg_of_two_mul_le (le_trans ha (le_of_lt hθ.1)) ?_) (sq_nonneg _)
  have h1 : 2 * θ < 2 * b := by linarith only [hθ.2]
  linarith only [h1, hb]



/-! ## The `W`-term bound -/

/-- **The `W`-term bound**: the collar hypothesis controls the `ψ_δ''`-moment of `U` slicewise,
and the a.e. mixed honesty makes the collar energies honest. -/
theorem wBound (Cw : ℝ) (hCw : 0 < Cw) (hc : Work.FTS.EllipticEst.Deleg.CollarBound Cw)
    (u : ℝ → ℝ → ℝ) (K : ℝ) (hK : 0 < K)
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hMix : Work.FTS.EllipticEst.Deleg.MixedHon u)
    (hRate : Work.FTS.EllipticEst.Deleg.SliceRate K u)
    (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ2 : 4 * δ ≤ Real.pi / 2) :
    (1 / 2) * |Wtr u n δ| ≤ Cw * K * Col u n δ := by
  rw [Wtr, Col]
  obtain ⟨hslice, hle1, hle2, hInt1, hInt2⟩ :=
    mixedTrunc.collarAe u n δ hδ hδ2 hsm hMix
  -- the a.e. pointwise collar bound (the collar hypothesis, slicewise)
  have hbd : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      |∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ
          * deriv (deriv (psiD δ)) θ * (Uz u z θ) ^ 2|
        ≤ Cw * K * ((∫ θ in Set.Ioo 0 δ, sigθ θ * (Vz u z θ) ^ 2)
          + (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
              sigθ θ * (Vz u z θ) ^ 2)) := by
    filter_upwards [hRate, hslice, ae_restrict_mem measurableSet_Ioi] with z hrate hslice hz
    exact mixedTrunc.sliceCollarLe Cw hc u K z δ hK hδ hδ2 hz
      (contDiffOn_Uz_slice hsm hz) hslice
      (fun θ hθ => deriv_Uz_eq_Vz hsm hz hθ) hrate.1 hrate.2
  -- the dominating function is integrable
  have hg : MeasureTheory.IntegrableOn (fun z => cut n z * wt z
      * (Cw * K * ((∫ θ in Set.Ioo 0 δ, sigθ θ * (Vz u z θ) ^ 2)
          + (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
              sigθ θ * (Vz u z θ) ^ 2)))) (Set.Ioi 0) := by
    refine ((hInt1.add hInt2).const_mul (Cw * K)).congr ?_
    filter_upwards with z
    simp only [Pi.add_apply]
    ring
  -- the dominated function `|G|` is integrable
  have hfint : MeasureTheory.IntegrableOn (fun z => cut n z * wt z
      * |∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ
          * deriv (deriv (psiD δ)) θ * (Uz u z θ) ^ 2|) (Set.Ioi 0) := by
    refine MeasureTheory.Integrable.mono' hg ?_ ?_
    · have haesmG : MeasureTheory.AEStronglyMeasurable
          (fun z => ∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ
              * deriv (deriv (psiD δ)) θ * (Uz u z θ) ^ 2)
          (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
        refine aesm_thetaIntegral_Ioi ?_ measurableSet_Ioo (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
        have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
          (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
        have h1 : ContinuousOn (fun p : ℝ × ℝ => sigθ p.2)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
          (hsin.rpow_const (fun p hp => Or.inl
            (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
              (by linarith [hp.2.2, Real.pi_pos]))))).congr (fun p _ => rfl)
        have hd2 : Continuous (deriv (deriv (psiD δ))) := by
          have hc := (psiD_contDiff δ).continuous_iteratedDeriv' 2
          simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hc
        have h2 : ContinuousOn (fun p : ℝ × ℝ => deriv (deriv (psiD δ)) p.2)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
          (hd2.comp continuous_snd).continuousOn
        exact (h1.mul h2).mul ((continuousOn_Uz_quad hsm).pow 2)
      have hwtm : Measurable (fun z : ℝ => wt z) := by
        have h1 : Measurable (fun z : ℝ => (1 : ℝ) + z) :=
          (measurable_const : Measurable (fun _ : ℝ => (1 : ℝ))).add measurable_id
        have hz : Measurable (fun z : ℝ => z) := measurable_id
        have h5 : Measurable (fun z : ℝ =>
            (((1 : ℝ) + z) * (1 + z)) / (z * z)
              * ((((1 : ℝ) + z) * (1 + z)) / (z * z))) :=
          ((h1.mul h1).div (hz.mul hz)).mul ((h1.mul h1).div (hz.mul hz))
        rw [show (fun z : ℝ => wt z) = fun z : ℝ =>
            (((1 : ℝ) + z) * (1 + z)) / (z * z)
              * ((((1 : ℝ) + z) * (1 + z)) / (z * z)) from by
          funext z; rw [Work.FTS.EllipticEst.AeColl.wt, Work.Spaces.w]; ring]
        exact h5
      have hcutwt : MeasureTheory.AEStronglyMeasurable (fun z => cut n z * wt z)
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
        (((cut_contDiff n).continuous.measurable).mul hwtm).aestronglyMeasurable
      have hGabs : MeasureTheory.AEStronglyMeasurable
          (fun z => |∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ
              * deriv (deriv (psiD δ)) θ * (Uz u z θ) ^ 2|)
          (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
        have hnorm := (haesmG.aemeasurable.norm).aestronglyMeasurable
        simpa only [Real.norm_eq_abs] using hnorm
      exact hcutwt.mul hGabs
    · filter_upwards [hbd] with z hz
      have h1 : ‖cut n z * wt z
          * |∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ
              * deriv (deriv (psiD δ)) θ * (Uz u z θ) ^ 2|‖
          = cut n z * wt z
          * |∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ
              * deriv (deriv (psiD δ)) θ * (Uz u z θ) ^ 2| := by
        simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (cut_nonneg n z),
          abs_of_nonneg (wt_nonneg z), abs_of_nonneg (abs_nonneg _)]
      rw [h1]
      exact mul_le_mul_of_nonneg_left hz (mul_nonneg (cut_nonneg n z) (wt_nonneg z))
  -- the two comparison inequalities for the outer integral
  have hnorm : |∫ z in Set.Ioi 0, cut n z * wt z
        * (∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ
            * deriv (deriv (psiD δ)) θ * (Uz u z θ) ^ 2)|
      ≤ ∫ z in Set.Ioi 0, cut n z * wt z
        * |∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ
            * deriv (deriv (psiD δ)) θ * (Uz u z θ) ^ 2| := by
    have h0 : ‖∫ z in Set.Ioi 0, cut n z * wt z
          * (∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ
              * deriv (deriv (psiD δ)) θ * (Uz u z θ) ^ 2)‖
        ≤ ∫ z in Set.Ioi 0, ‖cut n z * wt z
          * (∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ
              * deriv (deriv (psiD δ)) θ * (Uz u z θ) ^ 2)‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    have h1 : (∫ z in Set.Ioi 0, ‖cut n z * wt z
          * (∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ
              * deriv (deriv (psiD δ)) θ * (Uz u z θ) ^ 2)‖)
        = ∫ z in Set.Ioi 0, cut n z * wt z
          * |∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ
              * deriv (deriv (psiD δ)) θ * (Uz u z θ) ^ 2| := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (cut_nonneg n z),
        abs_of_nonneg (wt_nonneg z), abs_of_nonneg (abs_nonneg _)]
    rw [h1] at h0
    simpa only [Real.norm_eq_abs] using h0
  have hmono : (∫ z in Set.Ioi 0, cut n z * wt z
        * |∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ
            * deriv (deriv (psiD δ)) θ * (Uz u z θ) ^ 2|)
      ≤ ∫ z in Set.Ioi 0, cut n z * wt z
        * (Cw * K * ((∫ θ in Set.Ioo 0 δ, sigθ θ * (Vz u z θ) ^ 2)
            + (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
                sigθ θ * (Vz u z θ) ^ 2))) := by
    refine MeasureTheory.integral_mono_ae hfint hg ?_
    filter_upwards [hbd] with z hz
    exact mul_le_mul_of_nonneg_left hz (mul_nonneg (cut_nonneg n z) (wt_nonneg z))
  -- the dominating integral is `Cw·K·Col`
  have hsplit : (∫ z in Set.Ioi 0, cut n z * wt z
        * (Cw * K * ((∫ θ in Set.Ioo 0 δ, sigθ θ * (Vz u z θ) ^ 2)
            + (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
                sigθ θ * (Vz u z θ) ^ 2))))
      = Cw * K * ((∫ z in Set.Ioi 0, cut n z * wt z
              * (∫ θ in Set.Ioo 0 δ, sigθ θ * (Vz u z θ) ^ 2))
          + ∫ z in Set.Ioi 0, cut n z * wt z
              * (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
                  sigθ θ * (Vz u z θ) ^ 2)) := by
    rw [show (fun z => cut n z * wt z
          * (Cw * K * ((∫ θ in Set.Ioo 0 δ, sigθ θ * (Vz u z θ) ^ 2)
              + (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
                  sigθ θ * (Vz u z θ) ^ 2))))
        = fun z => (Cw * K) * (cut n z * wt z
            * ((∫ θ in Set.Ioo 0 δ, sigθ θ * (Vz u z θ) ^ 2)
              + (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
                  sigθ θ * (Vz u z θ) ^ 2))) from by
      funext z; ring]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [show (fun z => cut n z * wt z
          * ((∫ θ in Set.Ioo 0 δ, sigθ θ * (Vz u z θ) ^ 2)
            + (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
                sigθ θ * (Vz u z θ) ^ 2)))
        = fun z => cut n z * wt z * (∫ θ in Set.Ioo 0 δ, sigθ θ * (Vz u z θ) ^ 2)
            + cut n z * wt z * (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
                sigθ θ * (Vz u z θ) ^ 2) from by
      funext z; ring]
    rw [MeasureTheory.integral_add hInt1 hInt2]
  -- conclusion
  have hCol : Cw * K * Col u n δ
      = Cw * K * ((∫ z in Set.Ioi 0, cut n z * wt z
              * (∫ θ in Set.Ioo 0 δ, sigθ θ * (Vz u z θ) ^ 2))
          + ∫ z in Set.Ioi 0, cut n z * wt z
              * (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
                  sigθ θ * (Vz u z θ) ^ 2)) := rfl
  have h1 : |∫ z in Set.Ioi 0, cut n z * wt z
        * (∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ
            * deriv (deriv (psiD δ)) θ * (Uz u z θ) ^ 2)| ≤ Cw * K * Col u n δ := by
    rw [hCol, ← hsplit]
    exact le_trans hnorm hmono
  rw [hCol] at h1
  have h2δ : 2 * δ ≤ Real.pi := two_mul_le_pi_of hδ hδ2
  have hY0 : 0 ≤ Cw * K * Col u n δ := by
    rw [hCol, ← hsplit]
    refine Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.integral_nonneg_of_ae' ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun z hz => ?_
    have hAB : 0 ≤ (∫ θ in Set.Ioo 0 δ, sigθ θ * (Vz u z θ) ^ 2)
        + (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
            sigθ θ * (Vz u z θ) ^ 2) :=
      add_nonneg (inner_nonneg (f := u) le_rfl h2δ z)
        (inner_nonneg (f := u) (pi_half_sub_nonneg h2δ) two_mul_pi_half_le z)
    exact mul_nonneg (mul_nonneg (cut_nonneg n z) (wt_nonneg z))
      (mul_nonneg (le_of_lt (mul_pos hCw hK)) hAB)
  rw [hCol] at hY0
  linarith only [h1, hY0, abs_nonneg (∫ z in Set.Ioi 0, cut n z * wt z
      * (∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ
          * deriv (deriv (psiD δ)) θ * (Uz u z θ) ^ 2))]

/-! ## The defect term of the truncated angular identity -/

/-- The defect integral of `I1Wk.truncIdentity` at `χ = cut n`, `ψ = psiD δ`. -/
def defTerm (u : ℝ → ℝ → ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  ∫ z in Set.Ioi 0, cut n z * (Work.Spaces.w z) ^ 2
    * (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * psiD δ θ
          * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ
              - (1 + Work.Spaces.eta) * (z * Work.Spaces.pz u z θ)
                * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-(1 : ℝ))) ^ 2)

/-- The defect integral is nonnegative (it is the integral of a pointwise nonnegative
integrand). -/
theorem defTerm_nonneg (u : ℝ → ℝ → ℝ) (n : ℕ) (δ : ℝ) : 0 ≤ defTerm u n δ := by
  rw [defTerm]
  refine Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.integral_nonneg_of_ae' ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun z hz => ?_
  refine mul_nonneg (mul_nonneg (cut_nonneg n z) (sq_nonneg _)) ?_
  refine Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.integral_nonneg_of_ae' ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  refine Eventually.of_forall fun θ hθ => ?_
  have h2θ : 2 * θ ≤ Real.pi := by
    have h := mul_lt_mul_of_pos_left hθ.2 (by norm_num : (0 : ℝ) < 2)
    rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring] at h
    linarith only [h]
  exact mul_nonneg (mul_nonneg (sigθ_nonneg_of_two_mul_le (le_of_lt hθ.1) h2θ)
    (psiD_nonneg δ θ)) (sq_nonneg _)

/-! ## The main theorem -/

theorem mixedTruncPairLe (Cw : ℝ) (hCw : 0 < Cw)
    (hc : Work.FTS.EllipticEst.Deleg.CollarBound Cw) :
    Work.FTS.EllipticEst.Deleg.TruncPairLe Cw := by
  intro α u G hA hU hMix K hKpos hRate n δ hδ hδ2
  have hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hA.smooth
  obtain ⟨ho1, ho2, ho3, ho4⟩ := mixedTrunc.outerIntegrable u n δ hsm hδ hδ2
  have hχ : ContDiff ℝ 1 (cut n) := cut_contDiff_one n
  have hχc : HasCompactSupport (cut n) := cut_hasCompactSupport n
  have hχsupp : tsupport (cut n) ⊆ Set.Ioi (0 : ℝ) := cut_tsupport_subset_Ioi n
  have hχsupp' : Function.support (cut n) ⊆ Set.Ioi (0 : ℝ) := cut_support_subset_Ioi n
  have hχnn : ∀ z, 0 ≤ cut n z := cut_nonneg n
  have hψ : ContDiff ℝ 2 (psiD δ) := psiD_contDiff δ
  have hψc : HasCompactSupport (psiD δ) := psiD_hasCompactSupport δ
  have hψnn : ∀ θ, 0 ≤ psiD δ θ := psiD_nonneg δ
  have h4δ : 4 * δ ≤ Real.pi := four_mul_le_pi_of hδ2
  have h2δ : 2 * δ ≤ Real.pi := two_mul_le_pi_of hδ hδ2
  have h2π : δ < 2 * Real.pi := by linarith only [h2δ, Real.pi_pos]
  have hab : δ / 8 < Real.pi / 2 - δ / 8 := by
    rw [lt_sub_iff_add_lt, show δ / 8 + δ / 8 = δ / 4 by ring]
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 4)]
    rw [show Real.pi / 2 * 4 = 2 * Real.pi by ring]
    exact h2π
  have hψsep : ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < Real.pi / 2
      ∧ tsupport (psiD δ) ⊆ Set.Ioo a b :=
    ⟨δ / 8, Real.pi / 2 - δ / 8, by positivity, hab,
      sub_lt_self _ (by positivity), psiD_tsupport_subset' hδ h4δ⟩
  have hψsep1 : tsupport (psiD δ) ⊆ Set.Ioo 0 (Real.pi / 2) :=
    psiD_tsupport_subset_Ioo hδ h4δ
  have hId := Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.truncIdentity u (cut n) (psiD δ)
    hsm hχ hχc hχsupp hχsupp' hψ hψc hψsep hψsep1 ho1 ho2 ho3 ho4
  have hId' : Dtr u n δ = -Trtr u n δ + 2 * Work.Spaces.eta * Atr u n δ + kap * Ptr u n δ
      + (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * defTerm u n δ
      - (1 / 2) * Wtr u n δ := hId
  have hη : (0 : ℝ) ≤ Work.Spaces.eta := by rw [Work.Spaces.eta]; norm_num
  have hDef0 : 0 ≤ (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * defTerm u n δ :=
    mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hη) (by linarith only [hη]))
      (defTerm_nonneg u n δ)
  have hWle : (1 / 2) * Wtr u n δ ≤ Cw * K * Col u n δ :=
    le_trans (mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num))
      (wBound Cw hCw hc u K hKpos hsm hMix hRate n δ hδ hδ2)
  linarith only [hId', hDef0, hWle]

end Work.FTS.EllipticEst.Deleg
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Deleg.psiDLayerLimit =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.Deleg

/-! ## The general layer limit -/

/-- **Dominated convergence for a family of angular layers.**  Let `c` be a.e. strongly
measurable on `(0,∞)`, let `G` be jointly measurable on `(0,∞) × (0,π/2)` with a.e. integrable
`θ`-slices and nonnegative on the strip, and let `z ↦ |c z| ∫_θ |G z θ|` be integrable.  If
`S δ ⊆ (0, π/2)` are measurable layers whose `θ`-measure tends to `0` as `δ → 0⁺`, then the
`z`-integral of `c · (θ-mass of `G` on `S δ`)` tends to `0`. -/
theorem layerTendstoZero {c : ℝ → ℝ} {G : ℝ → ℝ → ℝ} {S : ℝ → Set ℝ}
    (hc : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))))
    (hjoint : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => G p.1 p.2)
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi/2)))))
    (hGz : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.Integrable (fun θ => G z θ) (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi/2))))
    (hGnn : ∀ z θ, θ ∈ Set.Ioo 0 (Real.pi/2) → 0 ≤ G z θ)
    (hdom : MeasureTheory.Integrable (fun z => |c z| * ∫ θ, |G z θ| ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi/2))))
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hSmeas : ∀ δ, MeasurableSet (S δ))
    (hSsub : ∀ δ, S δ ⊆ Set.Ioo 0 (Real.pi/2))
    (hSν : Tendsto (fun δ => (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi/2))) (S δ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    Tendsto (fun δ => ∫ z, c z * (∫ θ in S δ, G z θ) ∂(MeasureTheory.volume.restrict (Set.Ioi 0)))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
  set l : Filter ℝ := nhdsWithin 0 (Ioi 0) with hl
  set μ : Measure ℝ := volume.restrict (Ioi 0) with hμ
  set ν : Measure ℝ := volume.restrict (Ioo 0 (Real.pi/2)) with hν
  have hjoint' : AEStronglyMeasurable (fun p : ℝ × ℝ => G p.1 p.2) (μ.prod ν) := by
    rw [hμ, hν]; exact hjoint
  have hνrestr : ∀ δ, ν.restrict (S δ) = volume.restrict (S δ) := fun δ => by
    rw [hν, Measure.restrict_restrict_of_subset (hSsub δ)]
  -- (1) a.e. strong measurability of the integrands, uniformly in `δ`
  have hmeas : ∀ᶠ δ in l, AEStronglyMeasurable (fun z => c z * (∫ θ, (S δ).indicator (G z) θ ∂ν)) μ := by
    refine Eventually.of_forall fun δ => ?_
    have hset : MeasurableSet {p : ℝ × ℝ | p.2 ∈ S δ} := (hSmeas δ).preimage measurable_snd
    have h1 : AEStronglyMeasurable ({p : ℝ × ℝ | p.2 ∈ S δ}.indicator
        (fun p : ℝ × ℝ => G p.1 p.2)) (μ.prod ν) := hjoint'.indicator hset
    have h2 : AEStronglyMeasurable (fun z => ∫ θ,
        ({p : ℝ × ℝ | p.2 ∈ S δ}.indicator (fun p : ℝ × ℝ => G p.1 p.2)) (z, θ) ∂ν) μ :=
      h1.integral_prod_right'
    have h3 : AEStronglyMeasurable (fun z => ∫ θ, (S δ).indicator (G z) θ ∂ν) μ := by
      refine h2.congr (Eventually.of_forall fun z => ?_)
      apply integral_congr_ae
      filter_upwards with θ
      by_cases h : θ ∈ S δ
      · rw [Set.indicator_of_mem (show (z, θ) ∈ {p : ℝ × ℝ | p.2 ∈ S δ} from h)
            (fun p : ℝ × ℝ => G p.1 p.2), Set.indicator_of_mem h (G z)]
      · rw [Set.indicator_of_notMem (show (z, θ) ∉ {p : ℝ × ℝ | p.2 ∈ S δ} from h)
            (fun p : ℝ × ℝ => G p.1 p.2), Set.indicator_of_notMem h (G z)]
    exact hc.mul h3
  -- (2) domination by the weighted full `θ`-mass
  have hbound : ∀ᶠ δ in l, ∀ᵐ z ∂μ,
      ‖c z * (∫ θ, (S δ).indicator (G z) θ ∂ν)‖ ≤ |c z| * ∫ θ, |G z θ| ∂ν := by
    refine Eventually.of_forall fun δ => ?_
    filter_upwards [hGz] with z hz
    have hnn : 0 ≤ ∫ θ, (S δ).indicator (G z) θ ∂ν :=
      integral_nonneg (Set.indicator_nonneg fun θ hθ => hGnn z θ (hSsub δ hθ))
    have hle : ∫ θ, (S δ).indicator (G z) θ ∂ν ≤ ∫ θ, |G z θ| ∂ν :=
      integral_mono_ae (hz.indicator (hSmeas δ)) hz.norm
        (Eventually.of_forall fun θ => by
          by_cases h : θ ∈ S δ
          · rw [Set.indicator_of_mem h]; exact le_abs_self _
          · rw [Set.indicator_of_notMem h]; exact abs_nonneg _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_left hle (abs_nonneg _)
  -- (3) pointwise convergence for a.e. `z`
  have hlim : ∀ᵐ z ∂μ, Tendsto (fun δ => c z * (∫ θ, (S δ).indicator (G z) θ ∂ν)) l (nhds 0) := by
    filter_upwards [hGz] with z hz
    have h1 : Tendsto (fun δ => ∫ θ, (S δ).indicator (G z) θ ∂ν) l (nhds 0) :=
      Tendsto.congr' (Eventually.of_forall fun δ =>
        (integral_indicator (hSmeas δ) (f := G z) (μ := ν)).symm)
        (hz.tendsto_setIntegral_nhds_zero (l := l) (s := S) hSν)
    have h2 : Tendsto (fun δ => c z * (∫ θ, (S δ).indicator (G z) θ ∂ν)) l (nhds (c z * 0)) :=
      tendsto_const_nhds.mul h1
    simpa using h2
  have hBd : Integrable (fun z => |c z| * ∫ θ, |G z θ| ∂ν) μ := hdom
  have hmain := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (l := l) (F := fun δ z => c z * (∫ θ, (S δ).indicator (G z) θ ∂ν))
    (f := fun _ => (0:ℝ)) (fun z => |c z| * ∫ θ, |G z θ| ∂ν) hmeas hbound hBd hlim
  have hmain' : Tendsto (fun δ => ∫ z, c z * (∫ θ, (S δ).indicator (G z) θ ∂ν) ∂μ) l (nhds 0) := by
    simpa using hmain
  -- back to the honest set integrals, with respect to the unrestricted measure
  refine Tendsto.congr' (Eventually.of_forall fun δ => ?_) hmain'
  apply integral_congr_ae
  filter_upwards with z
  congr 1
  rw [integral_indicator (hSmeas δ) (f := G z) (μ := ν), hνrestr δ]

/-! ## The measures of the two layers tend to zero -/

/-- The `(0, π/2)`-measure of the lower layer `(0, min δ (π/2))` tends to `0` as `δ → 0⁺`. -/
theorem tendsto_nu_min :
    Tendsto (fun δ : ℝ => (volume.restrict (Ioo 0 (Real.pi/2))) (Ioo 0 (min δ (Real.pi/2))))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  set l : Filter ℝ := nhdsWithin 0 (Ioi 0) with hl
  set ν : Measure ℝ := volume.restrict (Ioo 0 (Real.pi/2)) with hν
  have hev : (fun δ : ℝ => ν (Ioo 0 (min δ (Real.pi/2))))
      = fun δ : ℝ => ENNReal.ofReal (min δ (Real.pi/2)) := by
    funext δ
    have hsub : Ioo 0 (min δ (Real.pi/2)) ⊆ Ioo 0 (Real.pi/2) :=
      fun θ hθ => ⟨hθ.1, lt_of_lt_of_le hθ.2 (min_le_right _ _)⟩
    rw [hν, Measure.restrict_apply measurableSet_Ioo,
      Set.inter_eq_self_of_subset_left hsub, Real.volume_Ioo, sub_zero]
  have hmin : Tendsto (fun δ : ℝ => min δ (Real.pi/2)) l (nhds 0) := by
    have h : Tendsto (fun δ : ℝ => min δ (Real.pi/2)) l (nhds (min 0 (Real.pi/2))) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).min tendsto_const_nhds
    rwa [min_eq_left (by linarith [Real.pi_pos])] at h
  have h2 : Tendsto (fun δ : ℝ => ENNReal.ofReal (min δ (Real.pi/2))) l (nhds 0) := by
    have h3 : Tendsto (fun δ : ℝ => ENNReal.ofReal (min δ (Real.pi/2))) l
        (nhds (ENNReal.ofReal 0)) :=
      (ENNReal.continuous_ofReal.tendsto 0).comp hmin
    simpa using h3
  exact Tendsto.congr' (Filter.EventuallyEq.of_eq hev.symm) h2

/-- The `(0, π/2)`-measure of the upper layer `(max (π/2 - δ) 0, π/2)` tends to `0` as `δ → 0⁺`. -/
theorem tendsto_nu_max :
    Tendsto (fun δ : ℝ => (volume.restrict (Ioo 0 (Real.pi/2))) (Ioo (max (Real.pi/2 - δ) 0) (Real.pi/2)))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  set l : Filter ℝ := nhdsWithin 0 (Ioi 0) with hl
  set ν : Measure ℝ := volume.restrict (Ioo 0 (Real.pi/2)) with hν
  have hlt : ∀ᶠ δ : ℝ in l, δ < Real.pi/2 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by linarith [Real.pi_pos]))
  have hev : (fun δ : ℝ => ν (Ioo (max (Real.pi/2 - δ) 0) (Real.pi/2)))
      =ᶠ[l] fun δ : ℝ => ENNReal.ofReal δ := by
    filter_upwards [hlt] with δ hδ
    have hsub : Ioo (Real.pi/2 - δ) (Real.pi/2) ⊆ Ioo 0 (Real.pi/2) :=
      fun θ hθ => ⟨lt_of_le_of_lt (by linarith : (0:ℝ) ≤ Real.pi/2 - δ) hθ.1, hθ.2⟩
    rw [hν, Measure.restrict_apply measurableSet_Ioo, max_eq_left (by linarith),
      Set.inter_eq_self_of_subset_left hsub, Real.volume_Ioo,
      show Real.pi/2 - (Real.pi/2 - δ) = δ from by ring]
  have h2 : Tendsto (fun δ : ℝ => ENNReal.ofReal δ) l (nhds 0) := by
    have h3 : Tendsto (fun δ : ℝ => ENNReal.ofReal δ) l (nhds (ENNReal.ofReal 0)) :=
      (ENNReal.continuous_ofReal.tendsto 0).comp (tendsto_id.mono_left nhdsWithin_le_nhds)
    simpa using h3
  exact Tendsto.congr' hev.symm h2

/-! ## The requested lemma -/

theorem psiDLayerLimit {c : ℝ → ℝ} {G : ℝ → ℝ → ℝ}
    (hc : MeasureTheory.AEStronglyMeasurable c
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hjoint : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => G p.1 p.2)
      ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
        (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))))
    (hGz : Filter.Eventually (fun z => MeasureTheory.Integrable (fun θ => G z θ)
        (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      (MeasureTheory.ae (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))))
    (hGnn : ∀ z θ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) → 0 ≤ G z θ)
    (hdom : MeasureTheory.Integrable (fun z => |c z| *
        ∫ θ, |G z θ| ∂(MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) :
    Filter.Tendsto (fun δ : ℝ =>
        (∫ z, c z * (∫ θ in Set.Ioo (0 : ℝ) δ, G z θ)
          ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
      + (∫ z, c z * (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2), G z θ)
          ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  set l : Filter ℝ := nhdsWithin 0 (Ioi 0) with hl
  have hlt : ∀ᶠ δ : ℝ in l, δ < Real.pi/2 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by linarith [Real.pi_pos]))
  have hlo : Tendsto (fun δ : ℝ => ∫ z, c z * (∫ θ in Set.Ioo 0 (min δ (Real.pi/2)), G z θ)
      ∂(volume.restrict (Set.Ioi 0))) l (nhds 0) :=
    layerTendstoZero (S := fun δ => Set.Ioo 0 (min δ (Real.pi/2))) hc hjoint hGz hGnn hdom
      (fun δ => measurableSet_Ioo)
      (fun δ θ hθ => ⟨hθ.1, lt_of_lt_of_le hθ.2 (min_le_right _ _)⟩) tendsto_nu_min
  have hlo' : Tendsto (fun δ : ℝ => ∫ z, c z * (∫ θ in Set.Ioo 0 δ, G z θ)
      ∂(volume.restrict (Set.Ioi 0))) l (nhds 0) := by
    refine Tendsto.congr' ?_ hlo
    filter_upwards [hlt] with δ hδ
    rw [min_eq_left (le_of_lt hδ)]
  have hhi : Tendsto (fun δ : ℝ => ∫ z, c z * (∫ θ in Set.Ioo (max (Real.pi/2 - δ) 0) (Real.pi/2), G z θ)
      ∂(volume.restrict (Set.Ioi 0))) l (nhds 0) :=
    layerTendstoZero (S := fun δ => Set.Ioo (max (Real.pi/2 - δ) 0) (Real.pi/2)) hc hjoint hGz hGnn hdom
      (fun δ => measurableSet_Ioo)
      (fun δ θ hθ => ⟨lt_of_le_of_lt (le_max_right _ _) hθ.1, hθ.2⟩) tendsto_nu_max
  have hhi' : Tendsto (fun δ : ℝ => ∫ z, c z * (∫ θ in Set.Ioo (Real.pi/2 - δ) (Real.pi/2), G z θ)
      ∂(volume.restrict (Set.Ioi 0))) l (nhds 0) := by
    refine Tendsto.congr' ?_ hhi
    filter_upwards [hlt] with δ hδ
    rw [max_eq_left (by linarith : (0:ℝ) ≤ Real.pi/2 - δ)]
  have hsum := hlo'.add hhi'
  simpa [l] using hsum

end Work.FTS.EllipticEst.Deleg
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.FstarDivOpen

set_option maxHeartbeats 1000000

/-! ## Measurability of the angular-moment quotient -/

/-- **Measurability of the angular-moment quotient.**  For a source `F` which is `C^∞` on the
open quadrant, `r ↦ F_*(F)(r)/r` is a.e. strongly measurable on `(0,∞)`.

This is the `SmoothOpen`-analogue of `Work.FTS.EllipticEst.Cert.aesm_Fstar_div_of_bslSol` (which
derives the same measurability from `F = bslOp α Ψ`); here no PDE is needed, `C^∞` on the open
quadrant suffices. -/
theorem aesm_Fstar_div_of_smoothOpen (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) :
    MeasureTheory.AEStronglyMeasurable (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have hφ : ContinuousOn Work.Elliptic.sinCos2 Work.Spaces.Iθ := by
    show ContinuousOn (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) Work.Spaces.Iθ
    exact (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn
  have hmom := Work.FTS.EllipticEst.aestronglyMeasurable_integral_Itheta_Q0 F hF.continuousOn
    Work.Elliptic.sinCos2 hφ
  have hinv : MeasureTheory.AEStronglyMeasurable (fun r : ℝ => r⁻¹)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (continuousOn_id.inv₀ (fun r hr => ne_of_gt hr)).aestronglyMeasurable measurableSet_Ioi
  have hmul := hmom.mul hinv
  rw [show (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      = (fun r : ℝ => (∫ θ in Work.Spaces.Iθ, F r θ * Work.Elliptic.sinCos2 θ) * r⁻¹)
      from by funext r; rw [Work.Elliptic.Fstar, div_eq_mul_inv]]
  exact hmul

/-! ## The target statement -/

/-- **`r ↦ F_*(F)(r)/r` is integrable on `(0,∞)`** for a source `F` which is `C^∞` on the open
quadrant `(0,∞) × (0,π/2)` and whose weighted `ℋ^k`-norm is honest.

Assembled from the two majorants of `Cert.FstarDivIntegrableOfSolHk`
(`Fstar_div_le_majorant_Ioc` on `(0,1]`, `Fstar_div_le_majorant_Ioi` on `(1,∞)`) and the
measurability `aesm_Fstar_div_of_smoothOpen` above. -/
theorem fstar_div_integrable_of_smoothOpen (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r) (Set.Ioi 0) := by
  have haesm : MeasureTheory.AEStronglyMeasurable (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := aesm_Fstar_div_of_smoothOpen F hF
  have hIoc_aesm : MeasureTheory.AEStronglyMeasurable (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (MeasureTheory.volume.restrict (Set.Ioc 0 1)) :=
    haesm.mono_measure (Measure.restrict_mono (fun r hr => by
      simp only [Set.mem_Ioc] at hr; simp only [Set.mem_Ioi]; exact hr.1) le_rfl)
  have hIoi_aesm : MeasureTheory.AEStronglyMeasurable (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (MeasureTheory.volume.restrict (Set.Ioi 1)) :=
    haesm.mono_measure (Measure.restrict_mono (fun r hr => by
      simp only [Set.mem_Ioi] at hr ⊢; linarith) le_rfl)
  have hGIoc : MeasureTheory.IntegrableOn
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ) (Set.Ioc 0 1) :=
    hmem.2.mono_set (fun r hr => by rw [Work.Spaces.Iz]; exact le_of_lt hr.1)
  have hGIoi : MeasureTheory.IntegrableOn
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ) (Set.Ioi 1) :=
    hmem.2.mono_set (fun r hr => by
      rw [Work.Spaces.Iz]
      exact le_of_lt (lt_trans zero_lt_one (Set.mem_Ioi.mp hr)))
  have hc1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 1) :=
    integrableOn_const (s := Set.Ioc 0 1) (C := (1 : ℝ))
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hM1 : MeasureTheory.IntegrableOn (fun r : ℝ =>
      ((Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ) + 1) / 2)
      (Set.Ioc 0 1) :=
    ((hGIoc.const_mul (Real.pi / 2)).add hc1).div_const 2
  have hrpow : MeasureTheory.IntegrableOn (fun r : ℝ => r ^ (-2 : ℝ)) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (a := -2) (c := 1) (by norm_num) (by norm_num)
  have hInvSq : MeasureTheory.IntegrableOn (fun r : ℝ => (r⁻¹) ^ 2) (Set.Ioi 1) :=
    hrpow.congr_fun (fun r hr => by
      show r ^ (-2 : ℝ) = (r⁻¹) ^ 2
      rw [Real.rpow_neg (le_of_lt (lt_trans zero_lt_one (Set.mem_Ioi.mp hr)))]
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast, inv_pow])
      measurableSet_Ioi
  have hM2 : MeasureTheory.IntegrableOn (fun r : ℝ =>
      ((Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ)
        + (r⁻¹) ^ 2) / 2) (Set.Ioi 1) :=
    ((hGIoi.const_mul (Real.pi / 2)).add hInvSq).div_const 2
  have h1 : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (Set.Ioc 0 1) :=
    hM1.mono' hIoc_aesm (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hr.1]
      exact Work.FTS.EllipticEst.Cert.Fstar_div_le_majorant_Ioc α k F hF hmem hr)
  have h2 : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar F r / r)
      (Set.Ioi 1) := by
    have hr0 : ∀ r : ℝ, r ∈ Set.Ioi 1 → (0 : ℝ) < r := fun r hr =>
      lt_trans zero_lt_one (Set.mem_Ioi.mp hr)
    refine hM2.mono' hIoi_aesm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hr0 r hr)]
    exact Work.FTS.EllipticEst.Cert.Fstar_div_le_majorant_Ioi α k F hF hmem (Set.mem_Ioi.mp hr)
  have hset : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 := by
    ext r
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (⟨h1, _⟩ | h1) <;> linarith
    · intro hr
      rcases lt_or_ge r 1 with h | h
      · exact Or.inl ⟨hr, le_of_lt h⟩
      · rcases eq_or_lt_of_le h with h' | h'
        · exact Or.inl ⟨hr, le_of_eq h'.symm⟩
        · exact Or.inr h'
  have hU := h1.union h2
  rw [hset] at hU
  exact hU

end Work.FTS.EllipticEst.FstarDivOpen
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AeWAux.aeI4Of =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AeWAux

set_option maxHeartbeats 1600000

/-!
# `aeI4Of`: the `I₄` upper bound from the single-slice inequality

`Work.FTS.EllipticEst.Honest.SliceIneq` is the *single-angular-slice* inequality

`∫_θ ∂_θ(tan θ·Φ)·Φ''·σ ≤ 50∫_θ(Φ/cos θ)²σ + √(∫_θ(Φ/cos θ)²σ)·√(∫_θ(Φ'')²σ)`

for `Φ : ℝ → ℝ` of class `C²` on `(0,π/2)` whose two weighted squares are integrable.

The lemma below turns it into the *two-dimensional* (`z`-integrated) `I₄` upper bound in the
weakest hypothesis class in which the assembly makes sense: `u` smooth on the open quadrant,
`HkMem α 0 (u/cos θ)` and `HkMem α 0 (∂_θθu)`.  Neither the equation `bslOp α u = G`, nor the
Dirichlet data, nor the solvability conditions, nor the honesty of `G`/`z²∂_zz u` are needed:
the source term of the honest statement simply disappears from the estimate, and for every
`z > 0` the slice `Φ := u z ·` satisfies the hypotheses of `SliceIneq` because the two weighted
`θ`-integrals are `(w2 z)⁻¹`-multiples of `HkIntegrand`-slices of the two honest functions.

The constant produced is `51`.
-/

/-- **The slicewise `I₄` inequality in the weak class.**

Let `u` be smooth on the open quadrant, `HkMem α 0 (∂_θθ u)` and `HkMem α 0 (u / cos θ)`.  Then for
every `z > 0` the `θ`-slice `θ ↦ u z θ` satisfies the single-slice inequality of
`Work.FTS.EllipticEst.Honest.SliceIneq`: the two weighted squares are integrable on `Iθ` (they are
`(w2 z)⁻¹`-multiples of the corresponding `HkIntegrand`-slices).

This is `Work.FTS.EllipticEst.Honest.I4SliceStep` with the `Hon α F Ψ` hypothesis weakened to the
two facts that proof actually consumes (the slice smoothness for the `C²` requirement and
`HkMem α 0 (∂_θθ u)` for the integrability of the `∂_θθ`-slice). -/
theorem sliceStepOf (hS : Work.FTS.EllipticEst.Honest.SliceIneq) {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 u))
    (hQ : Work.Spaces.HkMem α 0 (fun z θ => u z θ / Real.cos θ))
    {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z θ
          * Work.Spaces.pthIter 2 u z θ * Work.FTS.EllipticEst.AngSecond.sig θ)
      ≤ 50 * (∫ θ in Work.Spaces.Iθ,
            (u z θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
        + Real.sqrt (∫ θ in Work.Spaces.Iθ,
              (u z θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pthIter 2 u z θ) ^ 2
                * Work.FTS.EllipticEst.AngSecond.sig θ) := by
  -- (1) the slice is `C²` on the open interval
  have hslice : ContDiffOn ℝ 2 (fun θ : ℝ => u z θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have h2 := hsm 2
    have hg : ContDiffOn ℝ 2 (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2)) := by
      fun_prop
    have hcomp := h2.comp hg (fun θ hθ => ⟨hz, hθ⟩)
    simpa [Function.comp_def] using hcomp
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hw2ne : Work.FTS.EllipticEst.AngSecond.w2 z ≠ 0 := by
    have hwpos := Work.FTS.EllipticEst.AngSecond.w_pos hz
    simp only [Work.FTS.EllipticEst.AngSecond.w2]
    positivity
  -- (2) integrability of the two weighted squares, from `HkMem α 0 (u/cos)` and `HkMem α 0 (∂_θθu)`
  have hptQ : Set.EqOn
      (fun θ => Work.Spaces.HkIntegrand α 0 (fun z θ => u z θ / Real.cos θ) z θ)
      (fun θ => Work.FTS.EllipticEst.AngSecond.w2 z
        * ((u z θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ))
      Work.Spaces.Iθ := by
    intro θ hθ
    beta_reduce
    rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
      Work.FTS.EllipticEst.Honest.sq_profile_eq (fun z θ => u z θ / Real.cos θ) z θ
        (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ),
      Work.FTS.EllipticEst.AngSecond.w2, Work.FTS.EllipticEst.AngSecond.sig]
    ring
  have hQz : MeasureTheory.IntegrableOn
      (fun θ => (u z θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (Set.Icc 0 (Real.pi / 2)) := by
    have h0 := MeasureTheory.IntegrableOn.congr_fun (hQ.1 z hzI) hptQ measurableSet_Icc
    have h1 := Work.FTS.EllipticEst.Honest.I4IntegrableOnOfConstMul h0 hw2ne measurableSet_Icc
    refine MeasureTheory.IntegrableOn.congr_fun h1 (fun θ hθ => ?_) measurableSet_Icc
    show (u z θ / Real.cos θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ
      = (u z θ / Real.cos θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))
    rfl
  have hptB : Set.EqOn
      (fun θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) z θ)
      (fun θ => Work.FTS.EllipticEst.AngSecond.w2 z
        * ((Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ))
      Work.Spaces.Iθ := by
    intro θ hθ
    beta_reduce
    rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
      Work.FTS.EllipticEst.Honest.sq_profile_eq (Work.Spaces.pthIter 2 u) z θ
        (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ),
      Work.FTS.EllipticEst.AngSecond.w2, Work.FTS.EllipticEst.AngSecond.sig]
    ring
  have hBz : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv (fun θ' => u z θ')) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))) (Set.Icc 0 (Real.pi / 2)) := by
    have h0 := MeasureTheory.IntegrableOn.congr_fun (hB.1 z hzI) hptB measurableSet_Icc
    have h1 := Work.FTS.EllipticEst.Honest.I4IntegrableOnOfConstMul h0 hw2ne measurableSet_Icc
    refine MeasureTheory.IntegrableOn.congr_fun h1 (fun θ hθ => ?_) measurableSet_Icc
    show (Work.Spaces.pthIter 2 u z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ
      = (deriv (deriv (fun θ' => u z θ')) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ))
    rw [Work.FTS.EllipticEst.AngSecond.sig]
    rfl
  -- (3) instantiate the assumed slice inequality
  have hsl := hS (fun θ : ℝ => u z θ) hslice hQz hBz
  refine le_trans hsl ?_
  exact le_of_eq rfl

/-- **The `I₄` upper bound, from the single-slice inequality.**

Given `Work.FTS.EllipticEst.Honest.SliceIneq`, the estimate
`IP (∂_θ(tan θ·u)) (∂_θθu) ≤ C (‖u/cos θ‖² + ‖u/cos θ‖·‖∂_θθu‖)`

holds for every `α` and every `u` smooth on the open quadrant with `HkMem α 0 (u / cos θ)` and
`HkMem α 0 (∂_θθ u)`.

Proof: for each `z > 0` apply the slice inequality (`sliceStepOf`) to the slice `u z`; the two
weighted `θ`-integrals are `(w2 z)⁻¹`-multiples of the corresponding `HkSq`-slices
(`Honest.hksq_eq_w2_sliceIntegral`), multiply by `w2 z ≥ 0` and integrate in `z`; the cross term
`∫_z w2·√A·√B` is bounded by the radial Cauchy–Schwarz
(`AngSecond.setIntegral_w_mul_sqrt_le`, with the two `z`-integrals identified with
`HkSq α 0 (u/cos θ)` resp. `HkSq α 0 (∂_θθu)`).  The `z = 0` slice contributes `0` because
`w2 0 = 0`, so the pointwise domination `Fz ≤ Gz` holds on all of `Iz`.  The source term of the
honest statement is absent from the conclusion and is never used. -/
theorem aeI4Of (hslice : Work.FTS.EllipticEst.Honest.SliceIneq) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u : ℝ → ℝ → ℝ),
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
      Work.Spaces.HkMem α 0 (fun z θ => u z θ / Real.cos θ) →
      Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 u) →
      Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z θ)
          (Work.Spaces.pthIter 2 u)
        ≤ C * (Work.Spaces.HkSq α 0 (fun z θ => u z θ / Real.cos θ)
            + Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => u z θ / Real.cos θ))
              * Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u))) := by
  refine ⟨51, by norm_num, ?_⟩
  intro α u hsm hQmem hBmem
  set Q : ℝ → ℝ → ℝ := fun z θ => u z θ / Real.cos θ with hQdef
  set B : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 u with hBdef
  set U : ℝ → ℝ → ℝ :=
    fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z θ with hUdef
  set A : ℝ → ℝ := fun z =>
    ∫ θ in Work.Spaces.Iθ, (Q z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ with hAdef
  set Bz : ℝ → ℝ := fun z =>
    ∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ with hBzdef
  set Fz : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
    U z θ * B z θ * Work.FTS.EllipticEst.AngSecond.w2 z
      * Work.FTS.EllipticEst.AngSecond.sig θ with hFzdef
  set Gz : ℝ → ℝ := fun z => Work.FTS.EllipticEst.AngSecond.w2 z
    * (50 * A z + Real.sqrt (A z) * Real.sqrt (Bz z)) with hGzdef
  -- `HkSq α 0 g` is the iterated integral of `w z² ∫_θ g² σ`
  have hA := Work.FTS.EllipticEst.Honest.hksq_eq_w2_sliceIntegral (α := α) (g := Q) hQmem
  have hBz' := Work.FTS.EllipticEst.Honest.hksq_eq_w2_sliceIntegral (α := α) (g := B) hBmem
  have hAint : MeasureTheory.IntegrableOn
      (fun z => Work.FTS.EllipticEst.AngSecond.w2 z * A z) Work.Spaces.Iz := hA.1
  have hBzint : MeasureTheory.IntegrableOn
      (fun z => Work.FTS.EllipticEst.AngSecond.w2 z * Bz z) Work.Spaces.Iz := hBz'.1
  have hAval : ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.w2 z * A z
      = Work.Spaces.HkSq α 0 Q := hA.2
  have hBzval : ∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.w2 z * Bz z
      = Work.Spaces.HkSq α 0 B := hBz'.2
  -- the two angular slice integrals are nonnegative
  have hA0 : ∀ z, 0 ≤ A z := fun z =>
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _)
        (Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ))
  have hBz0 : ∀ z, 0 ≤ Bz z := fun z =>
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _)
        (Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ))
  -- the radial Cauchy–Schwarz for the cross term
  have hcross := Work.FTS.EllipticEst.AngSecond.setIntegral_w_mul_sqrt_le (s := Work.Spaces.Iz)
    (m := Work.FTS.EllipticEst.AngSecond.w2) (A := A) (B := Bz)
    Work.FTS.EllipticEst.AngSecond.w2_nonneg hA0 hBz0 hAint hBzint
  have hcrossB : (∫ z in Work.Spaces.Iz,
        Work.FTS.EllipticEst.AngSecond.w2 z * Real.sqrt (A z) * Real.sqrt (Bz z))
      ≤ Real.sqrt (Work.Spaces.HkSq α 0 Q) * Real.sqrt (Work.Spaces.HkSq α 0 B) := by
    refine le_trans hcross.2 ?_
    rw [hAval, hBzval]
  -- integrability and value of `∫_z Gz`
  have hGsum : (fun z => Work.FTS.EllipticEst.AngSecond.w2 z
        * (50 * A z + Real.sqrt (A z) * Real.sqrt (Bz z)))
      = fun z => 50 * (Work.FTS.EllipticEst.AngSecond.w2 z * A z)
          + Work.FTS.EllipticEst.AngSecond.w2 z * Real.sqrt (A z) * Real.sqrt (Bz z) :=
    funext fun z => by ring
  have hGint : MeasureTheory.IntegrableOn Gz Work.Spaces.Iz := by
    rw [hGzdef, hGsum]
    exact (hAint.const_mul 50).add hcross.1
  have hGval : ∫ z in Work.Spaces.Iz, Gz z
      = 50 * (Work.Spaces.HkSq α 0 Q)
        + ∫ z in Work.Spaces.Iz,
            Work.FTS.EllipticEst.AngSecond.w2 z * Real.sqrt (A z) * Real.sqrt (Bz z) := by
    rw [hGzdef, hGsum]
    rw [MeasureTheory.integral_add (hAint.const_mul 50) hcross.1,
      MeasureTheory.integral_const_mul, hAval]
  -- the pointwise domination `Fz ≤ Gz` on `Iz`
  have hpoint : ∀ z ∈ Work.Spaces.Iz, Fz z ≤ Gz z := by
    intro z hz
    rcases eq_or_ne z 0 with hz0 | hz0
    · -- at `z = 0` both sides vanish because `w2 0 = 0`
      subst hz0
      have hw0 : Work.FTS.EllipticEst.AngSecond.w2 0 = 0 := by
        rw [Work.FTS.EllipticEst.AngSecond.w2, Work.Spaces.w]
        norm_num
      have hFz0 : Fz 0 = 0 := by
        rw [hFzdef]
        beta_reduce
        simp only [hw0, mul_zero]
        simp
      have hGz0 : Gz 0 = 0 := by
        rw [hGzdef]
        beta_reduce
        rw [hw0]; ring
      rw [hFz0, hGz0]
    · -- at `z > 0` use the slice inequality
      have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
      have hsl := sliceStepOf hslice hsm hBmem hQmem hzpos
      have hsl' : (∫ θ in Work.Spaces.Iθ,
            U z θ * B z θ * Work.FTS.EllipticEst.AngSecond.sig θ)
          ≤ 50 * A z + Real.sqrt (A z) * Real.sqrt (Bz z) := hsl
      have hconst : Fz z = Work.FTS.EllipticEst.AngSecond.w2 z
          * (∫ θ in Work.Spaces.Iθ,
              U z θ * B z θ * Work.FTS.EllipticEst.AngSecond.sig θ) := by
        rw [hFzdef]
        beta_reduce
        rw [show (fun θ => U z θ * B z θ * Work.FTS.EllipticEst.AngSecond.w2 z
              * Work.FTS.EllipticEst.AngSecond.sig θ)
            = (fun θ => Work.FTS.EllipticEst.AngSecond.w2 z
                * (U z θ * B z θ * Work.FTS.EllipticEst.AngSecond.sig θ)) from
          funext fun θ => by ring]
        exact MeasureTheory.integral_const_mul _ _
      have hGz : Gz z = Work.FTS.EllipticEst.AngSecond.w2 z
          * (50 * A z + Real.sqrt (A z) * Real.sqrt (Bz z)) := by
        rw [hGzdef]
      rw [hconst, hGz]
      exact mul_le_mul_of_nonneg_left hsl'
        (Work.FTS.EllipticEst.AngSecond.w2_nonneg z)
  have hFG : Fz ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz] Gz :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mpr
      (Filter.Eventually.of_forall fun z hz => hpoint z hz)
  have hGz0 : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz] Gz :=
    Filter.Eventually.of_forall fun z => by
      rw [hGzdef]
      exact mul_nonneg (Work.FTS.EllipticEst.AngSecond.w2_nonneg z)
        (add_nonneg (mul_nonneg (by norm_num) (hA0 z))
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
  -- the iterated integral is the pairing, and the assembly
  have hIP : Work.FTS.EllipticEst.AngSecond.IP U B = ∫ z in Work.Spaces.Iz, Fz z := by
    rw [hFzdef]
    rfl
  have hfinal : Work.FTS.EllipticEst.AngSecond.IP U B
      ≤ 50 * (Work.Spaces.HkSq α 0 Q)
        + Real.sqrt (Work.Spaces.HkSq α 0 Q) * Real.sqrt (Work.Spaces.HkSq α 0 B) := by
    calc Work.FTS.EllipticEst.AngSecond.IP U B = ∫ z in Work.Spaces.Iz, Fz z := hIP
      _ ≤ ∫ z in Work.Spaces.Iz, Gz z :=
          Work.FTS.EllipticEst.integral_le_integral_of_ae_le hFG hGint hGz0
      _ = 50 * (Work.Spaces.HkSq α 0 Q)
            + ∫ z in Work.Spaces.Iz,
                Work.FTS.EllipticEst.AngSecond.w2 z * Real.sqrt (A z) * Real.sqrt (Bz z) :=
          hGval
      _ ≤ 50 * (Work.Spaces.HkSq α 0 Q)
            + Real.sqrt (Work.Spaces.HkSq α 0 Q) * Real.sqrt (Work.Spaces.HkSq α 0 B) :=
          add_le_add le_rfl hcrossB
  have hQ0 : 0 ≤ Work.Spaces.HkSq α 0 Q :=
    Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α Q
  have hc0 : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 Q) * Real.sqrt (Work.Spaces.HkSq α 0 B) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  linarith [hfinal, hQ0, hc0]

end Work.FTS.EllipticEst.H2W.AeWAux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.WeakPureAux.eigenPoleHalves =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `WeakPureAux/eigenPoleHalves` — the two halves of the eigen-slice pole bound

For a `C^2` function `u` on `(0, π/2)` with `Lzero1 u = mu * u` (the eigenrelation of the
`Lzero1`-slice), the running quantities of the `(Dfun, Rfun)` system are bounded:

* right half: `∃ B ≥ 0, ∀ θ ∈ [π/4, π/2), |Rfun u θ| ≤ |Rfun u (π/4)| + B · Ki θ`
  (`Rfun_right_const`), obtained from `Rfun_run_bound` together with the uniform bound on the
  running mass `Gd u θ = ∫_{π/4}^{θ}|Rfun u| · ew` (`Gd_bound`);
* left half: the mirror statement with `Kl`
  (`Rfun_left_const`), from `Rfun_run_bound_left` and `GdL u θ = ∫_{θ}^{π/4}|Rfun u| · ew`
  bounded (`GdL_bound`).

Both uniform bounds are constant-coefficient Grönwall inequalities: the weights satisfy
`ew · Ki ≤ π⁴/128` on `[π/4, π/2)` and `ew · Kl ≤ π³/16` on `(0, π/4]`, which makes the
coefficient of the running mass bounded, so Mathlib's
`norm_le_gronwallBound_of_norm_deriv_right_le` applies (directly on the right half, and to the
mirrored primitive `x ↦ ∫_0^x |Rfun u (π/4 - t)| ew (π/4 - t) dt` on the left half).
-/

namespace Work.FTS.EllipticEst.H2W.WeakPureAux

open scoped Real Topology Interval
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section




/-! ## The Grönwall step on the left half -/





/-! ## The right half -/




end

end Work.FTS.EllipticEst.H2W.WeakPureAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.WeakPureAux.poleBoundOfSourcePow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.WeakPureAux

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.EllipticEst.H2W.LzeroGrowth

/-! ## Elementary `rpow` algebra -/

/-- `1 ≤ x ^ (-R)` for `0 < x ≤ 1` and `R > 0`. -/
private theorem one_le_rpow_neg {x R : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hR : 0 < R) :
    1 ≤ x ^ (-R) := by
  have hinv : 1 ≤ x⁻¹ := by
    have h := div_le_div_of_nonneg_right hx1 hx.le
    rwa [div_self (ne_of_gt hx), one_div] at h
  have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hinv hR.le
  rw [Real.inv_rpow hx.le R, ← Real.rpow_neg hx.le R] at h
  simpa using h

/-- `y ^ (-R) ≤ x ^ (-R)` for `0 < x ≤ y` and `R > 0`. -/
private theorem rpow_neg_mono_prv {x y R : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hR : 0 < R) :
    y ^ (-R) ≤ x ^ (-R) :=
  Real.rpow_le_rpow_of_nonpos hx hxy (by linarith)







/-! ## The left half `(0, π/4]` -/


/-! ## The right half `[π/4, π/2)` -/



end Work.FTS.EllipticEst.H2W.WeakPureAux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.lzeroSliceFiber =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular slice of `∂_z^m F` against the weight `sinθcos²θ` is integrable

For a weak-class solution pair `(F,Ψ)` of the elliptic problem of Elgindi, Annals **194**
(2021), §'Elliptic Regularity Estimates', the angular moment of the source is

  `F_*(F)(z) = ∫_θ F(z,θ)·sinθcos²θ dθ`

(`Work.Elliptic.Fstar`).  The moment conditions of the weak class (`Work.FTS.EllipticEst.MomentZ`)
require the *angular slices* at a fixed `z` of the plain radial derivatives of the source,

  `θ ↦ ∂_z^m F(z,θ)·sinθcos²θ`  on  `Iθ = [0,π/2]`,

to be honest (integrable) for `m ≤ 2`: this is the prerequisite for differentiating the moment
under the integral sign in the `z`-variable.  This module supplies exactly that.

## The argument

The hypotheses of `Work.FTS.EllipticEst.WeakPos2` are: the equation `bslOp α Ψ = F` on the open
quadrant, the Dirichlet *values* of `Ψ`, the decay of `Ψ` at `z → ∞`, the two orthogonality
conditions and, crucially, `C^∞`-smoothness of `Ψ` on the open quadrant and
`Work.Spaces.HkMem α 2 F` (honesty of the weighted `ℋ²`-integrand of the source).

1. **Smoothness of the source.**  On the open quadrant `F` coincides with `bslOp α Ψ`; the
   elliptic operator is built from `Ψ` and its partials and the `C^∞` factors `z`, `z²`, `tan θ`
   (`tan` is smooth on `Q0` since `cos θ ≠ 0` there), so `SmoothOpen F`
   (`remov.SmoothOpen_bslOp_of_smoothOpen` followed by the congruence
   `Cert.smoothOpen_congr_bsl`).

2. **The `D_z = z∂_z` slices.**  For `z > 0` and `i ≤ 2`, the absorption inequality
   `|a·sinθcos²θ| ≤ (a·w(z)/sin(2θ)^{η/2})² + 1` for `θ ∈ Iθ` (with `w(z) ≥ 1` and
   `sin(2θ)^{η/2} ≤ 1`) together with `ℋ²`-honesty of the source
   (`OpenQDefs.integrableOn_zSummand`) gives the integrability of the slices of `D_z^i F`
   (`GbarSin.integrableOn_DzIter_mul_sinCos2`), for **every** `z > 0` (the weight `w(z)` and the
   angular weight are the only inputs, so no `z`-a.e. caveat is needed).

3. **From `D_z` back to `∂_z`.**  `D_z = z∂_z`, hence `D_z^i` is triangular in the `∂_z^k`
   (`k ≤ i`) with invertible diagonal, and

   * `m = 0`: `∂_z^0 F = D_z^0 F`;
   * `m = 1`: `z·∂_z F = D_z F` holds *by definition* (`rfl`), so the slice of `∂_z F` is the
     constant multiple `z⁻¹` of an integrable slice;
   * `m = 2`: `D_z²F = D_zF + z²∂_z²F` at every point of the open quadrant (product rule, using
     that the `z`-slice of `∂_z F` is differentiable there, `SmoothOpen.hasDerivAt_slice_pzIter`),
     i.e. `z²·∂_z²F = D_z²F - D_zF`.  The identity only holds on the open interval; since
     `Iθ \ (0,π/2) = {0,π/2}` is a null set, it holds a.e. on `Iθ` and transports integrability.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false

/-! ## The two pointwise identities relating `∂_z^m` and `D_z^m` for `m ≤ 2` -/





/-! ## The requested statement -/


end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Mine.SourceBoundsTwoD =====
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
set_option maxHeartbeats 1600000



namespace Work.FTS.EllipticEst.Mine

/-! ## The slot functions -/

/-- The pointwise weighted angular slot of level `n` with weight `σ`:
`w(z)²·((∂_θⁿX(z,θ))²·σ(θ))`.  The factor `w(z)²` is kept *inside* so that the slot vanishes
identically at `z = 0`; this is what makes the measurability statements uniform in `z`. -/
private def slotFun (n : ℕ) (σ : ℝ → ℝ) (X : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter n X z θ) ^ 2 * σ θ)

/-- The angular slot of level `n` with weight `σ`, integrated over `Iθ`. -/
private def slot (n : ℕ) (σ : ℝ → ℝ) (X : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, slotFun n σ X z θ

private lemma slotFun_nonneg {n : ℕ} {σ : ℝ → ℝ}
    (hσnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ σ θ) (X : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ slotFun n σ X z θ :=
  mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (hσnn θ hθ))

private lemma slot_nonneg {n : ℕ} {σ : ℝ → ℝ}
    (hσnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ σ θ) (X : ℝ → ℝ → ℝ) (z : ℝ) :
    0 ≤ slot n σ X z :=
  integral_nonneg_of_ae
    (ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => slotFun_nonneg hσnn X z θ hθ)




/-! ## The angular weights `σ₂ = sin(2θ)^{2-γ}` and `σ₄ = sin(2θ)^{4-γ}` -/








/-! ## Three algebraic inequalities -/


private lemma sq_three_le (a b c α : ℝ) :
    (a + α ^ 2 * b + α * (5 + α) * c) ^ 2
      ≤ 3 * a ^ 2 + 3 * α ^ 4 * b ^ 2 + 3 * α ^ 2 * (5 + α) ^ 2 * c ^ 2 := by
  nlinarith [sq_nonneg (a - α ^ 2 * b), sq_nonneg (α ^ 2 * b - α * (5 + α) * c),
    sq_nonneg (a - α * (5 + α) * c)]


/-! ## The `θ`-level dichotomy -/


/-! ## The `z`-level assembly -/




/-! ## Converting the slot form into the statement form -/


/-! ## The pointwise comparison inequalities at the two levels -/

/-! ## The two-dimensional statement -/


/-! ## The two-dimensional statement -/


end Work.FTS.EllipticEst.Mine
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.Rtilde.OneD =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Prop.Rtilde.OneD`: the one-dimensional angular estimate `slice_ang_gen` (`ESW.OneD`)
from the two window bounds.

The outer window `[0, 3π/8]` is `remov.slice_ang_v_outer` (proved); the far window
`[3π/8, π/2]` is the input `FarB`.  Their sum gives `VBound`, and `SliceGen.genFinal`
converts that into the `u^{(k+2)}`-estimate.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.Prop.Rtilde

set_option autoImplicit false
set_option maxHeartbeats 2000000






end Work.FTS.EllipticEst.Prop.Rtilde
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.TIProp.SurrEnergy =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted energies of the surrogate

From the estimates of `TVRed.surrIntegrals` and the endpoint bounds for `F₀`, `F₁` at the scale
`L⁴ = P/(16(P+E))`, the surrogate `ℓ = surrFun ψ F₀ F₁ L` satisfies

* `∫ (ℓ')² σ ≤ 10⁶ (Cb+1)² (P + √(P E))`,
* `∫ (ℓ'')² σ ≤ 10⁸ (Cb+1)² (P + E)`,

and the three weighted squares of `ℓ`, `ℓ'`, `ℓ''` are integrable on `Iθ`.
-/

namespace Work.FTS.EllipticEst.Prop.TIProp

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 4000000

local notation "σ" => Work.FTS.EllipticEst.thEta

/-- The weighted energies of the surrogate and the integrability of its weighted squares. -/
theorem surr_energy {ψ : ℝ → ℝ} {Cb F₀ F₁ L P E : ℝ}
    (hψ : Work.EllipticEst.Core.i0Aux.IsBump ψ Cb) (hL : 0 < L) (hLp : L ≤ Real.pi / 4)
    (hPpos : 0 < P) (hEnn : 0 ≤ E)
    (hL4 : L ^ 4 = P / (16 * (P + E)))
    (hF0 : F₀ ^ 2 ≤ 2 * L ^ (3 + Work.Spaces.eta) * E
      + 100 * L ^ (Work.Spaces.eta - 1) * P)
    (hF1 : F₁ ^ 2 ≤ 2 * L ^ (3 + Work.Spaces.eta) * E
      + 100 * L ^ (Work.Spaces.eta - 1) * P) :
    ((∫ θ in Work.Spaces.Iθ,
        (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2 * σ θ)
          ≤ 10 ^ 6 * (Cb + 1) ^ 2 * (P + Real.sqrt (P * E)))
    ∧ ((∫ θ in Work.Spaces.Iθ,
        (deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ) ^ 2 * σ θ)
          ≤ 10 ^ 8 * (Cb + 1) ^ 2 * (P + E))
    ∧ (MeasureTheory.IntegrableOn (fun θ : ℝ =>
        (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) ^ 2 * σ θ) Work.Spaces.Iθ)
    ∧ (MeasureTheory.IntegrableOn (fun θ : ℝ =>
        (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2 * σ θ)
          Work.Spaces.Iθ)
    ∧ (MeasureTheory.IntegrableOn (fun θ : ℝ =>
        (deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ) ^ 2 * σ θ)
          Work.Spaces.Iθ) := by
  have hPnn : 0 ≤ P := hPpos.le
  have hPEpos : 0 < P + E := by linarith
  have hXnn : 0 ≤ Real.sqrt (P * E) := Real.sqrt_nonneg _
  obtain ⟨-, hS2, hS3, -⟩ :=
    Work.EllipticEst.Core.i0Aux.TVRed.surrIntegrals (F₀ := F₀) (F₁ := F₁) hψ hL hLp
  -- ## the two elementary scale facts
  have hL2r : L ^ (2 : ℝ) = Real.sqrt (P / (16 * (P + E))) := by
    have h : (L ^ 2) ^ 2 = P / (16 * (P + E)) := by rw [← pow_mul, hL4]
    have hL2 : L ^ 2 = Real.sqrt (P / (16 * (P + E))) := by
      rw [← h, Real.sqrt_sq (sq_nonneg L)]
    have hc : L ^ (2 : ℝ) = L ^ 2 := Real.rpow_natCast L 2
    rw [hc, hL2]
  have hL2E : L ^ (2 : ℝ) * E ≤ Real.sqrt (P * E) := by
    have hkey : L ^ (2 : ℝ) * E = Real.sqrt (P * E ^ 2 / (16 * (P + E))) := by
      have h1 : L ^ (2 : ℝ) * E
          = Real.sqrt (P / (16 * (P + E))) * Real.sqrt (E ^ 2) := by
        rw [hL2r, Real.sqrt_sq hEnn]
      have h2 : Real.sqrt (P / (16 * (P + E))) * Real.sqrt (E ^ 2)
          = Real.sqrt (P * E ^ 2 / (16 * (P + E))) := by
        rw [show P * E ^ 2 / (16 * (P + E)) = P / (16 * (P + E)) * E ^ 2 by ring]
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ P / (16 * (P + E))) (E ^ 2)]
      exact h1.trans h2
    rw [hkey]
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 16 * (P + E))]
    have h8 : E ≤ 16 * (P + E) := by linarith [hPEpos.le]
    have h9 : E ^ 2 ≤ (16 * (P + E)) * E := by
      have h10 := mul_le_mul_of_nonneg_right h8 hEnn
      simpa [pow_two, mul_comm] using h10
    nlinarith [h9, hPnn, hEnn]
  have hinv4 : L ^ (-4 : ℝ) = 16 * (P + E) / P := by
    have h4r : L ^ (4 : ℝ) = P / (16 * (P + E)) := by
      have hc : L ^ (4 : ℝ) = L ^ 4 := Real.rpow_natCast L 4
      rw [hc]; exact hL4
    rw [show (-4 : ℝ) = -(4 : ℝ) by ring, Real.rpow_neg hL.le, h4r, inv_div]
  have hL2inv : L ^ (-2 : ℝ) * P = 4 * Real.sqrt (P * (P + E)) := by
    have hsq : (L ^ (-2 : ℝ) * P) ^ 2 = (4 * Real.sqrt (P * (P + E))) ^ 2 := by
      have h4r : L ^ (4 : ℝ) = P / (16 * (P + E)) := by
        have hc : L ^ (4 : ℝ) = L ^ 4 := Real.rpow_natCast L 4
        rw [hc]; exact hL4
      have hA : (L ^ (-2 : ℝ) * P) ^ 2 = (L ^ (-4 : ℝ)) * P ^ 2 := by
        rw [mul_pow, show (L ^ (-2 : ℝ)) ^ 2 = L ^ (-4 : ℝ) by
          rw [pow_two, ← Real.rpow_add hL]
          congr 1
          ring]
      have hB : L ^ (-4 : ℝ) = 16 * (P + E) / P := by
        rw [show (-4 : ℝ) = -(4 : ℝ) by ring, Real.rpow_neg hL.le, h4r, inv_div]
      have hC : (4 * Real.sqrt (P * (P + E))) ^ 2 = 16 * (P * (P + E)) := by
        rw [mul_pow, show (4 : ℝ) ^ 2 = 16 by norm_num,
          Real.sq_sqrt (by positivity : (0 : ℝ) ≤ P * (P + E))]
      have hPne : P ≠ 0 := ne_of_gt hPpos
      rw [hA, hB, hC]
      field_simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact h
    · exfalso
      have h1 : 0 ≤ L ^ (-2 : ℝ) * P := mul_nonneg (Real.rpow_nonneg hL.le _) hPnn
      have h2 : 0 < 4 * Real.sqrt (P * (P + E)) := by
        have h3 : 0 < Real.sqrt (P * (P + E)) := Real.sqrt_pos.mpr (by positivity)
        linarith
      linarith
  -- ## the products of powers
  have hpA : L ^ (3 + Work.Spaces.eta) * L ^ (-(1 + Work.Spaces.eta)) = L ^ (2 : ℝ) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  have hpA2 : L ^ (Work.Spaces.eta - 1) * L ^ (-(1 + Work.Spaces.eta)) = L ^ (-2 : ℝ) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  have hpB : L ^ (3 + Work.Spaces.eta) * L ^ (-(3 + Work.Spaces.eta)) = 1 := by
    rw [← Real.rpow_add hL,
      show 3 + Work.Spaces.eta + (-(3 + Work.Spaces.eta)) = (0 : ℝ) by ring, Real.rpow_zero]
  have hpB2 : L ^ (Work.Spaces.eta - 1) * L ^ (-(3 + Work.Spaces.eta)) = L ^ (-4 : ℝ) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  -- ## the two scaled endpoint bounds
  have hsum : F₀ ^ 2 + F₁ ^ 2 ≤ 4 * L ^ (3 + Work.Spaces.eta) * E
      + 200 * L ^ (Work.Spaces.eta - 1) * P := by linarith [hF0, hF1]
  have hscA : (F₀ ^ 2 + F₁ ^ 2) * L ^ (-(1 + Work.Spaces.eta)) ≤ 1000 * (P + Real.sqrt (P * E)) := by
    have h1 : (4 * L ^ (3 + Work.Spaces.eta) * E + 200 * L ^ (Work.Spaces.eta - 1) * P)
          * L ^ (-(1 + Work.Spaces.eta))
        = 4 * (L ^ (3 + Work.Spaces.eta) * L ^ (-(1 + Work.Spaces.eta))) * E
          + 200 * (L ^ (Work.Spaces.eta - 1) * L ^ (-(1 + Work.Spaces.eta))) * P := by ring
    have h2 := mul_le_mul_of_nonneg_right hsum (Real.rpow_nonneg hL.le (-(1 + Work.Spaces.eta)))
    rw [h1, hpA, hpA2] at h2
    have h3 : 4 * (L ^ (2 : ℝ) * E) ≤ 4 * Real.sqrt (P * E) :=
      mul_le_mul_of_nonneg_left hL2E (by norm_num)
    have h5 : 200 * (L ^ (-2 : ℝ) * P) = 800 * Real.sqrt (P * (P + E)) := by
      rw [hL2inv]; ring
    have h6 : Real.sqrt (P * (P + E)) ≤ P + Real.sqrt (P * E) :=
      Work.EllipticEst.Core.i0Aux.tvc_sqrt_mul_le hPnn hEnn
    linarith [h2, h3, h5, h6]
  have hscB : (F₀ ^ 2 + F₁ ^ 2) * L ^ (-(3 + Work.Spaces.eta)) ≤ 4000 * (P + E) := by
    have h1 : (4 * L ^ (3 + Work.Spaces.eta) * E + 200 * L ^ (Work.Spaces.eta - 1) * P)
          * L ^ (-(3 + Work.Spaces.eta))
        = 4 * (L ^ (3 + Work.Spaces.eta) * L ^ (-(3 + Work.Spaces.eta))) * E
          + 200 * (L ^ (Work.Spaces.eta - 1) * L ^ (-(3 + Work.Spaces.eta))) * P := by ring
    have h2 := mul_le_mul_of_nonneg_right hsum (Real.rpow_nonneg hL.le (-(3 + Work.Spaces.eta)))
    rw [h1, hpB, hpB2, hinv4] at h2
    have h3 : 200 * (16 * (P + E) / P) * P = 3200 * (P + E) := by
      field_simp
      ring
    linarith [h2, h3, hEnn, hPEpos.le]
  -- ## the two energy bounds
  have hAE : (∫ θ in Work.Spaces.Iθ,
        (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2 * σ θ)
      ≤ 10 ^ 6 * (Cb + 1) ^ 2 * (P + Real.sqrt (P * E)) := by
    refine hS2.trans ?_
    have h2 : (0 : ℝ) ≤ (Cb + 1) ^ 2 := by positivity
    calc 1000 * (Cb + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) * L ^ (-(1 + Work.Spaces.eta))
        = 1000 * (Cb + 1) ^ 2 * ((F₀ ^ 2 + F₁ ^ 2) * L ^ (-(1 + Work.Spaces.eta))) := by ring
      _ ≤ 1000 * (Cb + 1) ^ 2 * (1000 * (P + Real.sqrt (P * E))) :=
          mul_le_mul_of_nonneg_left hscA (by positivity)
      _ = 10 ^ 6 * (Cb + 1) ^ 2 * (P + Real.sqrt (P * E)) := by ring
  have hEE : (∫ θ in Work.Spaces.Iθ,
        (deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ) ^ 2 * σ θ)
      ≤ 10 ^ 8 * (Cb + 1) ^ 2 * (P + E) := by
    refine hS3.trans ?_
    have h2 : (0 : ℝ) ≤ (Cb + 1) ^ 2 := by positivity
    calc 1000 * (Cb + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) * L ^ (-(3 + Work.Spaces.eta))
        = 1000 * (Cb + 1) ^ 2 * ((F₀ ^ 2 + F₁ ^ 2) * L ^ (-(3 + Work.Spaces.eta))) := by ring
      _ ≤ 1000 * (Cb + 1) ^ 2 * (4000 * (P + E)) :=
          mul_le_mul_of_nonneg_left hscB (by positivity)
      _ ≤ 10 ^ 8 * (Cb + 1) ^ 2 * (P + E) := by
          have h3 : 0 ≤ P + E := by linarith
          nlinarith [h2, h3, sq_nonneg (Cb + 1)]
  -- ## the integrability of the three weighted squares
  have hℓc : Continuous (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) :=
    (Work.EllipticEst.Core.i0Aux.TVRed.surr_smooth hψ (ne_of_gt hL)).continuous
  have hℓ1c : ContDiff ℝ 1 (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) := by
    simpa using (Work.EllipticEst.Core.i0Aux.TVRed.surr_smooth hψ
      (ne_of_gt hL)).deriv' (n := 1)
  have hℓbound : ∀ θ : ℝ,
      (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) ^ 2 ≤ (|F₀| + |F₁|) ^ 2 := by
    intro θ
    have h := Work.EllipticEst.Core.i0Aux.TVRed.surr_bound (F₀ := F₀) (F₁ := F₁) (L := L) hψ θ
    calc (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) ^ 2
        = |Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ| ^ 2 := (sq_abs _).symm
      _ ≤ (|F₀| + |F₁|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  have hℓ1bound : ∀ θ : ℝ,
      (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2
        ≤ (Cb * (|F₀| + |F₁|) / L) ^ 2 := by
    intro θ
    have h := Work.EllipticEst.Core.i0Aux.TVRed.deriv_surr_bound (F₀ := F₀) (F₁ := F₁) (L := L) hψ hL θ
    calc (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2
        = |deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ| ^ 2 := (sq_abs _).symm
      _ ≤ (Cb * (|F₀| + |F₁|) / L) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  have hℓ2bound : ∀ θ : ℝ,
      (deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ) ^ 2
        ≤ (Cb * (|F₀| + |F₁|) / L ^ 2) ^ 2 := by
    intro θ
    have h := Work.EllipticEst.Core.i0Aux.TVRed.deriv2_surr_bound (F₀ := F₀) (F₁ := F₁) (L := L) hψ hL θ
    calc (deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ) ^ 2
        = |deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ| ^ 2 := (sq_abs _).symm
      _ ≤ (Cb * (|F₀| + |F₁|) / L ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  have hint0 : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) ^ 2 * σ θ) Work.Spaces.Iθ := by
    have haesm : AEStronglyMeasurable (fun θ : ℝ =>
        (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) ^ 2 * σ θ)
        (volume.restrict Work.Spaces.Iθ) :=
      ((hℓc.pow 2).aestronglyMeasurable).mul
        (Work.EllipticEst.Core.i0Aux.TVRed.tvh_aesm_thEta)
    refine Work.EllipticEst.Core.i0Aux.TVRed.tvh_integrableOn_of_abs_le
      (Work.EllipticEst.Core.i0Aux.TVRed.tvh_integrableOn_const_mul_thEta
        ((|F₀| + |F₁|) ^ 2)) haesm ?_
    intro θ hθ
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.thEta_nonneg hθ))]
    exact mul_le_mul_of_nonneg_right (hℓbound θ)
      (Work.FTS.EllipticEst.thEta_nonneg hθ)
  have hint1 : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2 * σ θ)
      Work.Spaces.Iθ := by
    have haesm : AEStronglyMeasurable (fun θ : ℝ =>
        (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2 * σ θ)
        (volume.restrict Work.Spaces.Iθ) :=
      (((hℓ1c.continuous).pow 2).aestronglyMeasurable).mul
        (Work.EllipticEst.Core.i0Aux.TVRed.tvh_aesm_thEta)
    refine Work.EllipticEst.Core.i0Aux.TVRed.tvh_integrableOn_of_abs_le
      (Work.EllipticEst.Core.i0Aux.TVRed.tvh_integrableOn_const_mul_thEta
        ((Cb * (|F₀| + |F₁|) / L) ^ 2)) haesm ?_
    intro θ hθ
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.thEta_nonneg hθ))]
    exact mul_le_mul_of_nonneg_right (hℓ1bound θ)
      (Work.FTS.EllipticEst.thEta_nonneg hθ)
  have hℓ2cont : ContinuousOn (deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h1 : ContDiffOn ℝ 1 (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      have h2 : ContDiff ℝ 1 (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) := by
        simpa using (Work.EllipticEst.Core.i0Aux.TVRed.surr_smooth hψ
          (ne_of_gt hL)).deriv' (n := 1)
      exact h2.contDiffOn
    exact contDiffOn_zero.1 (h1.deriv_of_isOpen isOpen_Ioo (by norm_num))
  have hint2 : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ) ^ 2 * σ θ)
      Work.Spaces.Iθ := by
    have haesm : AEStronglyMeasurable (fun θ : ℝ =>
        (deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ) ^ 2 * σ θ)
        (volume.restrict Work.Spaces.Iθ) :=
      ((Work.EllipticEst.Core.i0Aux.TVRed.tvh_aesm_of_continuousOn hℓ2cont).pow 2).mul
        (Work.EllipticEst.Core.i0Aux.TVRed.tvh_aesm_thEta)
    refine Work.EllipticEst.Core.i0Aux.TVRed.tvh_integrableOn_of_abs_le
      (Work.EllipticEst.Core.i0Aux.TVRed.tvh_integrableOn_const_mul_thEta
        ((Cb * (|F₀| + |F₁|) / L ^ 2) ^ 2)) haesm ?_
    intro θ hθ
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.thEta_nonneg hθ))]
    exact mul_le_mul_of_nonneg_right (hℓ2bound θ)
      (Work.FTS.EllipticEst.thEta_nonneg hθ)
  exact ⟨hAE, hEE, hint0, hint1, hint2⟩

end Work.FTS.EllipticEst.Prop.TIProp
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.traceBoundLeft =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1000000


end Work.FTS.EllipticEst.Prop
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.traceBoundRight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop

open MeasureTheory


end Work.FTS.EllipticEst.Prop
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.Shim.HkMemDzAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## The four input terms

Each input term is a summand of an integrand whose honesty is a field of `EllHyp`, so
`Work.FTS.EllipticEst.Cert.DzAux.summand_props` delivers the four facts (slice integrability, integrability of the slice
integrals, `z`-integrability of the slices for a.e. angle, finiteness of the outer `∫⁻`). -/





/-! ## The two excess terms -/





/-! ## The certificate -/




end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.weakIPMems =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TT.weakIPMems` — the six cross-honesty pairings of the weak level-`0` class

For a datum `(F,Ψ)` of the weak class `TT.EllWeakPos α 0 F Ψ` together with the two Step-1
honesties `HkMem α 0 Ψ` and `HkMem α 0 (z∂_zΨ)`, the six pairings against
`B = ∂_θθΨ = pthIter 2 Ψ` that the Step-2 identity `Σ Iᵢ = -IP F B` consumes are honest
(`AngSecond.IPMem`):

`IPMem F B`, `IPMem (z²∂_zzΨ) B`, `IPMem (z∂_zΨ) B`, `IPMem (∂_θ(tan θ·Ψ)) B`,
`IPMem Ψ B`, `IPMem B B`.

## Route

Five of the six first slots are already known to be honest:

* `F`, `z²∂_zzΨ`, `∂_θθΨ` are the `HkMem α 0` fields of `EllWeakPos`;
* `Ψ` and `z∂_zΨ` are the two additional hypotheses.

All six first slots (and the second slot `B`) agree on the open quadrant with a `C^∞` profile
(`SmoothOpen`): for the smooth profiles this is immediate, and for the source `F` the equation
`bslOp α Ψ = F` identifies `F` there with the smooth `bslOp α Ψ`.  The diagonal honesties
`IPMem g g` come from `HkMem α 0 g` (`AngClean.HkMem_zero_IPMem`), and the mixed honesty
`IPMem g B` then follows from `AngClean.IPMem_of_diag_aesm` (the polarisation
`|g B| ≤ g² + B²`), whose only extra inputs are the a.e. strong measurabilities supplied by
`Honest.AesmCross.aesmSliceCross` and `aesmProdCross` from the two `SmoothOpen` representatives.

The only first slot that is *not* a field or an hypothesis is the angular term
`u = ∂_θ(tan θ·Ψ)`.  Its honesty follows from the equation on the open quadrant, rewritten as

  `∂_θ(tan θ·Ψ) = α²z²∂_zzΨ + F + α(5+α)z∂_zΨ + ∂_θθΨ + 6Ψ`,

each summand of which is `HkMem α 0`; the five-term Cauchy–Schwarz domination of the
`ℋ⁰`-integrand and `Blocks.HkMem_of_majorant_aesm` then give `HkMem α 0 u`.  This is the weak
(`EllWeakPos`) version of `Honest.HonMemU.honMemPthTan`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

/-! ## Cross honesty from the two diagonal honesties and open-quadrant smoothness -/

/-- **Cross honesty from the two diagonal honesties and open-quadrant smoothness.**

If `g` and `h` are honest (`HkMem α 0`, hence `IPMem` on the diagonal) and each agrees on the
open quadrant with a `C^∞` profile (`AgreeOnQ g g'`, `SmoothOpen g'`, and likewise for `h`),
then the mixed pairing `IPMem g h` is honest. -/
private theorem ipMem_of_agreeOnQ {α : ℝ} {g h g' h' : ℝ → ℝ → ℝ}
    (hg' : Work.FTS.EllipticEst.SmoothOpen g') (hh' : Work.FTS.EllipticEst.SmoothOpen h')
    (hgg : Work.FTS.EllipticEst.AgreeOnQ g g') (hhh : Work.FTS.EllipticEst.AgreeOnQ h h')
    (hmg : Work.Spaces.HkMem α 0 g) (hmh : Work.Spaces.HkMem α 0 h) :
    Work.FTS.EllipticEst.AngSecond.IPMem g h :=
  Work.FTS.EllipticEst.AngClean.IPMem_of_diag_aesm
    (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hmg)
    (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hmh)
    (fun z hz => Work.FTS.EllipticEst.Honest.AesmCross.aesmSliceCross hg' hh' hgg hhh z hz)
    (Work.FTS.EllipticEst.Honest.AesmCross.aesmProdCross hg' hh' hgg hhh)

/-! ## The equation, solved for `∂_θ(tan θ · Ψ)` -/

/-- **`(PolarBSL)` solved for the second derivatives.**  On the open quadrant,
`α² z²∂_zzΨ = -F - α(5+α) z∂_zΨ - ∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ`. -/
private theorem EllWeakPos.eq_solve {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ)
    {z θ : ℝ} (hz : 0 < z) (h0 : 0 < θ) (h1 : θ < π / 2) :
    α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      = -F z θ - α * (5 + α) * (z * Work.Spaces.pz Ψ z θ)
        - Work.Spaces.pthIter 2 Ψ z θ
        + Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - 6 * Ψ z θ := by
  have hb := h.eq z hz θ h0 h1
  rw [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero] at hb
  linarith [hb]

/-! ## Helpers for the honesty of `∂_θ(tan θ · Ψ)` -/

/-- The level-`0` `HkIntegrand` vanishes at the left angular boundary. -/
private lemma hki_zero (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z 0 = 0 := by
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq]
  simp [Work.Spaces.eta]

/-- The level-`0` `HkIntegrand` vanishes at the right angular boundary. -/
private lemma hki_pi (α : ℝ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z (Real.pi / 2) = 0 := by
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq]
  have hs : Real.sin (2 * (Real.pi / 2)) = 0 := by
    rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
  rw [hs]
  simp [Work.Spaces.eta]

/-- The five-term Cauchy–Schwarz inequality, with the common factor `c` factored out. -/
private lemma sq_sum_five (a1 a2 a3 a4 a5 c : ℝ) :
    ((a1 + a2 + a3 + a4 + a5) * c) ^ 2
      ≤ 5 * ((a1 * c) ^ 2 + (a2 * c) ^ 2 + (a3 * c) ^ 2 + (a4 * c) ^ 2 + (a5 * c) ^ 2) := by
  have h1 : (a1 + a2 + a3 + a4 + a5) ^ 2 ≤ 5 * (a1 ^ 2 + a2 ^ 2 + a3 ^ 2 + a4 ^ 2 + a5 ^ 2) := by
    nlinarith [sq_nonneg (a1 - a2), sq_nonneg (a1 - a3), sq_nonneg (a1 - a4),
      sq_nonneg (a1 - a5), sq_nonneg (a2 - a3), sq_nonneg (a2 - a4), sq_nonneg (a2 - a5),
      sq_nonneg (a3 - a4), sq_nonneg (a3 - a5), sq_nonneg (a4 - a5)]
  have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg c)
  nlinarith [h2]

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

/-- The pointwise majorant of the level-`0` `HkIntegrand` of `∂_θ(tan θ · Ψ)`: it is the sum of
the five summands appearing in the rearranged equation, each dominating term weighted by the
Cauchy–Schwarz constant `5`. -/
private def Mj (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  5 * (Work.Spaces.HkIntegrand α 0 (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
    + Work.Spaces.HkIntegrand α 0 F z θ
    + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ)) z θ
    + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ
    + Work.Spaces.HkIntegrand α 0 (fun z θ => 6 * Ψ z θ) z θ)

/-- **The pointwise domination.**  If `u = g₁ + ⋯ + g₅` on the open quadrant then the
level-`0` `HkIntegrand` of `u` is dominated on the closed quadrant by `5` times the sum of the
`HkIntegrand`s of the `gᵢ`.

On the open quadrant this is the five-term Cauchy–Schwarz inequality (`sq_sum_five`); on the
boundary it is trivial because the angular weight vanishes there (`HkIntegrand_zero_z`,
`hki_zero`, `hki_pi`). -/
private theorem hki_le_five {α : ℝ} {u g1 g2 g3 g4 g5 : ℝ → ℝ → ℝ}
    (h : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      u z θ = g1 z θ + g2 z θ + g3 z θ + g4 z θ + g5 z θ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 u z θ
        ≤ 5 * (Work.Spaces.HkIntegrand α 0 g1 z θ + Work.Spaces.HkIntegrand α 0 g2 z θ
              + Work.Spaces.HkIntegrand α 0 g3 z θ + Work.Spaces.HkIntegrand α 0 g4 z θ
              + Work.Spaces.HkIntegrand α 0 g5 z θ) := by
  have hnn : ∀ z θ : ℝ, 0 ≤ 5 * (Work.Spaces.HkIntegrand α 0 g1 z θ
      + Work.Spaces.HkIntegrand α 0 g2 z θ + Work.Spaces.HkIntegrand α 0 g3 z θ
      + Work.Spaces.HkIntegrand α 0 g4 z θ + Work.Spaces.HkIntegrand α 0 g5 z θ) := by
    intro z θ
    have e1 := Work.Spaces.HkIntegrand_nonneg α 0 g1 z θ
    have e2 := Work.Spaces.HkIntegrand_nonneg α 0 g2 z θ
    have e3 := Work.Spaces.HkIntegrand_nonneg α 0 g3 z θ
    have e4 := Work.Spaces.HkIntegrand_nonneg α 0 g4 z θ
    have e5 := Work.Spaces.HkIntegrand_nonneg α 0 g5 z θ
    linarith
  intro z hz θ hθ
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · rw [← hz0, Work.Spaces.HkIntegrand_zero_z]
    exact hnn 0 θ
  · rcases eq_or_lt_of_le hθ.1 with hθ0 | hθpos
    · rw [← hθ0, hki_zero]
      exact hnn z 0
    · rcases eq_or_lt_of_le hθ.2 with hθ2 | hθlt
      · rw [hθ2, hki_pi]
        exact hnn z (Real.pi / 2)
      · simp only [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq, h z hzpos θ hθpos hθlt]
        exact sq_sum_five _ _ _ _ _ _

/-! ## Honesty of `∂_θ(tan θ · Ψ)` -/

/-- **`HkMem α 0 (∂_θ(tan θ · Ψ))`.**  The rearranged equation expresses `∂_θ(tan θ·Ψ)` as the
sum of the five `HkMem α 0` profiles `α²z²∂_zzΨ`, `F`, `α(5+α)z∂_zΨ`, `∂_θθΨ`, `6Ψ`, so the
five-term Cauchy–Schwarz domination (`hki_le_five`) of the `ℋ⁰`-integrands closes it. -/
private theorem hkMem_pth_tan_mul (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ)
    (hΨ : Work.Spaces.HkMem α 0 Ψ)
    (hzΨ : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ)) :
    Work.Spaces.HkMem α 0 (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ) := by
  set u : ℝ → ℝ → ℝ := Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) with hu
  -- `u` is `C^∞` on the open quadrant
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have htan : Work.FTS.EllipticEst.SmoothOpen (fun _ : ℝ => Real.tan) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl
  have htanΨ : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl htan hΨso
  have htgt : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.SmoothOpen.pth htanΨ
  have hcont := Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand htgt α 0
  -- the a.e. strong measurability of the integrand of `u`
  have haesmJoint : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 u p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  have haesmSlice : ∀ z ∈ Work.Spaces.Iz, AEStronglyMeasurable
      (fun θ => Work.Spaces.HkIntegrand α 0 u z θ) (volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · rw [show (fun θ => Work.Spaces.HkIntegrand α 0 u z θ) = fun θ => (0 : ℝ) from by
        funext θ
        rw [← hz0, Work.Spaces.HkIntegrand_zero_z]]
      exact aestronglyMeasurable_const
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hzpos
  have haesmOuter : AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 u z θ)
      (volume.restrict Work.Spaces.Iz) := haesmJoint.integral_prod_right'
  -- the five sample `ℋ⁰` functions
  have hm1 : Work.Spaces.HkMem α 0 (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
    Work.FTS.LocData.HkMem_const_mul α 0 (α ^ 2) h.memA
  have hm2 : Work.Spaces.HkMem α 0 F := h.memF
  have hm3 : Work.Spaces.HkMem α 0 (fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ)) :=
    Work.FTS.LocData.HkMem_const_mul α 0 (α * (5 + α)) hzΨ
  have hm4 : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ) := h.memB
  have hm5 : Work.Spaces.HkMem α 0 (fun z θ => 6 * Ψ z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 0 6 hΨ
  -- integrability of the angular slices of the majorant
  have hMslice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => Mj α F Ψ z θ) Work.Spaces.Iθ := by
    intro z hz
    simp only [Mj]
    have h12 : Integrable (fun θ => Work.Spaces.HkIntegrand α 0
          (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        + Work.Spaces.HkIntegrand α 0 F z θ) (volume.restrict Work.Spaces.Iθ) :=
      (hm1.1 z hz).add (hm2.1 z hz)
    have h123 : Integrable (fun θ => (Work.Spaces.HkIntegrand α 0
          (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        + Work.Spaces.HkIntegrand α 0 F z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ)) z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      h12.add (hm3.1 z hz)
    have h1234 : Integrable (fun θ => ((Work.Spaces.HkIntegrand α 0
          (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        + Work.Spaces.HkIntegrand α 0 F z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ)) z θ)
        + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      h123.add (hm4.1 z hz)
    have h12345 : Integrable (fun θ => (((Work.Spaces.HkIntegrand α 0
          (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        + Work.Spaces.HkIntegrand α 0 F z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ)) z θ)
        + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => 6 * Ψ z θ) z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      h1234.add (hm5.1 z hz)
    exact h12345.const_mul 5
  -- integrability of the `θ`-integral of the majorant
  have hMz : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, Mj α F Ψ z θ) Work.Spaces.Iz := by
    have hs1 : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
        (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ) Work.Spaces.Iz := hm1.2
    have hs2 : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.HkIntegrand α 0 (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        + Work.Spaces.HkIntegrand α 0 F z θ)) Work.Spaces.Iz :=
      integrableOn_integral_add
        (f := fun z θ => Work.Spaces.HkIntegrand α 0
          (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ)
        (g := fun z θ => Work.Spaces.HkIntegrand α 0 F z θ)
        hm1.1 hm2.1 hm1.2 hm2.2
    have hs3 : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        ((Work.Spaces.HkIntegrand α 0 (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        + Work.Spaces.HkIntegrand α 0 F z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ)) z θ))
        Work.Spaces.Iz :=
      integrableOn_integral_add (f := fun z θ => Work.Spaces.HkIntegrand α 0
          (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        + Work.Spaces.HkIntegrand α 0 F z θ)
        (g := fun z θ => Work.Spaces.HkIntegrand α 0
          (fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ)) z θ)
        (fun z hz => (hm1.1 z hz).add (hm2.1 z hz)) hm3.1 hs2 hm3.2
    have hs4 : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        (((Work.Spaces.HkIntegrand α 0 (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        + Work.Spaces.HkIntegrand α 0 F z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ)) z θ)
        + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ)) Work.Spaces.Iz :=
      integrableOn_integral_add (f := fun z θ => (Work.Spaces.HkIntegrand α 0
          (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        + Work.Spaces.HkIntegrand α 0 F z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ)) z θ)
        (g := fun z θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ)
        (fun z hz => ((hm1.1 z hz).add (hm2.1 z hz)).add (hm3.1 z hz)) hm4.1 hs3 hm4.2
    have hs5 : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        ((((Work.Spaces.HkIntegrand α 0 (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        + Work.Spaces.HkIntegrand α 0 F z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ)) z θ)
        + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => 6 * Ψ z θ) z θ)) Work.Spaces.Iz :=
      integrableOn_integral_add (f := fun z θ => ((Work.Spaces.HkIntegrand α 0
          (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
        + Work.Spaces.HkIntegrand α 0 F z θ)
        + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ)) z θ)
        + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ)
        (g := fun z θ => Work.Spaces.HkIntegrand α 0 (fun z θ => 6 * Ψ z θ) z θ)
        (fun z hz => (((hm1.1 z hz).add (hm2.1 z hz)).add (hm3.1 z hz)).add (hm4.1 z hz))
        hm5.1 hs4 hm5.2
    have hkey : (fun z => ∫ θ in Work.Spaces.Iθ, Mj α F Ψ z θ)
        = fun z => 5 * ∫ θ in Work.Spaces.Iθ,
            ((((Work.Spaces.HkIntegrand α 0
              (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z θ
            + Work.Spaces.HkIntegrand α 0 F z θ)
            + Work.Spaces.HkIntegrand α 0 (fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ)) z θ)
            + Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 Ψ) z θ)
            + Work.Spaces.HkIntegrand α 0 (fun z θ => 6 * Ψ z θ) z θ) := by
      funext z
      simp only [Mj]
      exact MeasureTheory.integral_const_mul 5 _
    rw [hkey]
    exact hs5.const_mul 5
  -- the pointwise domination
  have hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 u z θ ≤ Mj α F Ψ z θ := by
    have hb := hki_le_five (α := α) (u := u)
      (g1 := fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
      (g2 := F) (g3 := fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz Ψ z θ))
      (g4 := Work.Spaces.pthIter 2 Ψ) (g5 := fun z θ => 6 * Ψ z θ)
      (fun z hz θ hθ0 hθ1 => by
        have h0 := EllWeakPos.eq_solve h hz hθ0 hθ1
        linarith [h0])
    intro z hz θ hθ
    simp only [Mj]
    exact hb z hz θ hθ
  exact Work.Blocks.HkMem_of_majorant_aesm α 0 haesmSlice haesmOuter hMslice hMz hle

/-! ## The six cross-honesty pairings -/

theorem weakIPMems (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ)
    (hmΨ : Work.Spaces.HkMem α 0 Ψ)
    (hmG : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ)) :
    Work.FTS.EllipticEst.AngSecond.IPMem F (Work.Spaces.pthIter 2 Ψ) ∧
    Work.FTS.EllipticEst.AngSecond.IPMem (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      (Work.Spaces.pthIter 2 Ψ) ∧
    Work.FTS.EllipticEst.AngSecond.IPMem (fun z θ => z * Work.Spaces.pz Ψ z θ)
      (Work.Spaces.pthIter 2 Ψ) ∧
    Work.FTS.EllipticEst.AngSecond.IPMem
      (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
      (Work.Spaces.pthIter 2 Ψ) ∧
    Work.FTS.EllipticEst.AngSecond.IPMem Ψ (Work.Spaces.pthIter 2 Ψ) ∧
    Work.FTS.EllipticEst.AngSecond.IPMem (Work.Spaces.pthIter 2 Ψ)
      (Work.Spaces.pthIter 2 Ψ) := by
  -- `Ψ` is `C^∞` on the open quadrant, hence so are all the profiles below.
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hBso : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    (hΨso.pth).pth
  have hAso : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl
      (hΨso.pzIter 2)
  have hGso : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z * Work.Spaces.pz Ψ z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl Work.FTS.EllipticEst.Cert.smoothOpen_z_bsl
      hΨso.pz
  have huso : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ) :=
    Work.FTS.EllipticEst.SmoothOpen.pth (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl hΨso)
  -- the source is the smooth `bslOp α Ψ` on the open quadrant
  have hFso : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ) :=
    Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hΨso
  have hFag : Work.FTS.EllipticEst.AgreeOnQ F (Work.Elliptic.bslOp α Ψ) :=
    fun z θ hz hθ0 hθ1 => (h.eq z hz θ hθ0 hθ1).symm
  -- the angular profile `∂_θ(tan θ·Ψ)` is honest
  have hu : Work.Spaces.HkMem α 0
      (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ) :=
    hkMem_pth_tan_mul α F Ψ h hmΨ hmG
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ipMem_of_agreeOnQ hFso hBso hFag (fun _ _ _ _ _ => rfl) h.memF h.memB
  · exact ipMem_of_agreeOnQ hAso hBso (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
      h.memA h.memB
  · exact ipMem_of_agreeOnQ hGso hBso (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
      hmG h.memB
  · exact ipMem_of_agreeOnQ huso hBso (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
      hu h.memB
  · exact ipMem_of_agreeOnQ hΨso hBso (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
      hmΨ h.memB
  · exact ipMem_of_agreeOnQ hBso hBso (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
      h.memB h.memB

end Work.FTS.EllipticEst.TT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.AeI1PaperDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `remov/AeI1PaperDefs` — the *decoupled* paper-shaped `I₁` interface

`remov.AeI1LowerPos` (in `remov/AeChainDefs.lean`) states the `I₁` lower bound with
`‖G‖_ρ`-errors, so its proof needs Step 1's radial bound `α‖z∂_zu‖_ρ ≤ C‖G‖_ρ`.  The
paper's computation (the `z`- and `θ`-integrations by parts plus the sharp Hardy inequality)
produces instead the *`⟨z∂_zu, z∂_zu⟩`-form* collected here as `AeI1Paper`, which is
Step-1-free; the conversion to `AeI1LowerPos` is the pure arithmetic
`remov.AeI1LowerPos_of_paper` in `remov/AeStep2Holds.lean`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false



end Work.FTS.EllipticEst.remov
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.AeIPMemsSlim =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `remov/AeIPMemsSlim` — the six `IPMem` honesties of the Step 2 identity, in the a.e. class

`Work.FTS.EllipticEst.H2W.AeWAux.aeIPMems` proves
`Work.FTS.EllipticEst.AngAWeak.AeIPMems` (the six cross-honesties of
`AngAWeak.Basic.I_identity_weak`) but imports `Honest.honCrossIPMems`, which in turn pulls in
`EllHyp_certificates` and the whole `Cert/` interface — an import cone of ~670 modules that is
irrelevant to the argument.  This module re-proves the same statement with the *minimal*
imports: the only ingredients are

* `AngClean.HkMem_zero_IPMem` (the diagonal honesty `HkMem α 0 g ⟹ IPMem g g`),
* `AngClean.IPMem_of_diag_aesm` (the polarisation `|g h| ≤ g² + h²`),
* the a.e. strong measurability of the mixed integrand off the boundary of the quadrant
  (`Honest.AesmCross.aesmSliceCross`, `aesmProdCross`, which need only `SmoothOpen`
  representatives and `AgreeOnQ`),
* `RPFresh.HkMem_of_agreeOnQ`, `FTS.LocData.HkMem_const_mul`, `SmoothOpenAdd.smoothOpen_add`,
  `HkIntegrand_add_le_open` + `LocData.HkMem_of_majorant` (for the honesty of the sums below),
* `remov.SmoothOpen_bslOp_of_smoothOpen` and `Cert.SmoothOpen_bslOp` for the `SmoothOpen`
  certificates of the profiles.

The content is a verbatim re-run of `aeIPMems`'s argument: every one of the six profiles is
`HkMem α 0` and agrees on the open quadrant with a `C^∞` profile, and the only profile which is
not a field of `AeData` is the angular term `∂_θ(tan θ·u)`, whose honesty follows from the
equation rewritten as
`∂_θ(tan θ·u) = (∂_θ²u + 6u) + ((bslOp α u + α²z²∂_zzu) + α(5+α)z∂_zu)`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

/-- Scalar multiples of `SmoothOpen` functions are `SmoothOpen`.  (A local copy of
`RPFresh.smoothOpen_const_mul`, whose module drags in the `Cert/` interface.) -/
theorem smoothOpen_const_mul_ae {c : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  rw [Work.FTS.EllipticEst.SmoothOpen] at hf ⊢
  have h : (Function.uncurry fun z θ => c * f z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry f p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [h]
  exact (contDiffOn_const (c := c) (s := Work.FTS.EllipticEst.Q0)).mul hf

/-- **`ℋ^k` is closed under addition** for `SmoothOpen` data.  (A local copy of
`RPFresh.HkMem_add_open`, whose module drags in the `Cert/` interface.) -/
theorem hkMem_add_open_ae (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => f z θ + g z θ) := by
  have hfg : Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) :=
    Work.FTS.EllipticEst.smoothOpen_add hf hg
  refine Work.FTS.LocData.HkMem_of_majorant α k
    (f := fun z θ => f z θ + g z θ)
    (M := fun z θ => 2 * Work.Spaces.HkIntegrand α k f z θ
      + 2 * Work.Spaces.HkIntegrand α k g z θ)
    (hfg.continuousOn_HkIntegrand α k) ?_ ?_ ?_
  · intro z hz
    exact ((hmf.1 z hz).const_mul 2).add ((hmg.1 z hz).const_mul 2)
  · have htarget : IntegrableOn (fun z : ℝ => 2 * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k f z θ) + 2 * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k g z θ)) Work.Spaces.Iz :=
      (hmf.2.const_mul 2).add (hmg.2.const_mul 2)
    refine Integrable.congr htarget ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [MeasureTheory.integral_add ((hmf.1 z hz).const_mul 2) ((hmg.1 z hz).const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  · intro z hz θ hθ
    exact Work.FTS.EllipticEst.HkIntegrand_add_le_open α k hf hg hz hθ

/-- **Cross honesty from the two diagonal honesties and open-quadrant smoothness.**  (A local
copy of `Honest.IPMem_of_HkMem_agreeOnQ`, whose module drags in the `Cert/` interface.) -/
theorem ipMem_of_HkMem_agreeOnQ_ae {α : ℝ} {g h g' h' : ℝ → ℝ → ℝ}
    (hg' : Work.FTS.EllipticEst.SmoothOpen g') (hh' : Work.FTS.EllipticEst.SmoothOpen h')
    (hgg : Work.FTS.EllipticEst.AgreeOnQ g g') (hhh : Work.FTS.EllipticEst.AgreeOnQ h h')
    (hmg : Work.Spaces.HkMem α 0 g) (hmh : Work.Spaces.HkMem α 0 h) :
    Work.FTS.EllipticEst.AngSecond.IPMem g h :=
  Work.FTS.EllipticEst.AngClean.IPMem_of_diag_aesm
    (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hmg)
    (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hmh)
    (fun z hz => Work.FTS.EllipticEst.Honest.AesmCross.aesmSliceCross hg' hh' hgg hhh z hz)
    (Work.FTS.EllipticEst.Honest.AesmCross.aesmProdCross hg' hh' hgg hhh)

/-- **The `IPMem` bookkeeping of the Step 2 identity in the class `AeData`**: the six pairings
occurring in `AngAWeak.Basic.I_identity_weak` against `B = ∂_θθu` are honest. -/
theorem aeIPMemsSlim : Work.FTS.EllipticEst.AngAWeak.AeIPMems := by
  intro α u G hA hmu hmuU
  have hα : 0 < α := hA.hα
  -- ### The `SmoothOpen` representatives of the profiles
  have huS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hA.smooth
  have hBS : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 u) :=
    (huS.pth).pth
  have hQS : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl Work.FTS.EllipticEst.Cert.smoothOpen_zsq_bsl
      (Work.FTS.EllipticEst.SmoothOpen.pzIter huS 2)
  have hUS : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z * Work.Spaces.pz u z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl Work.FTS.EllipticEst.Cert.smoothOpen_z_bsl
      (Work.FTS.EllipticEst.SmoothOpen.pz huS)
  have hG1S : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z θ) :=
    Work.FTS.EllipticEst.SmoothOpen.pth (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl
      Work.FTS.EllipticEst.Cert.smoothOpen_tan_bsl huS)
  have hGop : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α u) :=
    Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen huS
  have hGagree : Work.FTS.EllipticEst.AgreeOnQ G (Work.Elliptic.bslOp α u) :=
    fun z θ hz hθ0 hθ1 => (hA.eq z hz θ hθ0 hθ1).symm
  -- ### The honesty of the summands of `∂_θ(tan θ·u)`
  have hmBsl : Work.Spaces.HkMem α 0 (Work.Elliptic.bslOp α u) :=
    Work.FTS.EllipticEst.RPFresh.HkMem_of_agreeOnQ hGagree hA.memG
  have h6uS : Work.FTS.EllipticEst.SmoothOpen (fun z θ => 6 * u z θ) :=
    smoothOpen_const_mul_ae huS
  have h6u : Work.Spaces.HkMem α 0 (fun z θ => 6 * u z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 0 6 hmu
  have h1S : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Spaces.pthIter 2 u z θ + 6 * u z θ) :=
    Work.FTS.EllipticEst.smoothOpen_add hBS h6uS
  have h1 : Work.Spaces.HkMem α 0 (fun z θ => Work.Spaces.pthIter 2 u z θ + 6 * u z θ) :=
    hkMem_add_open_ae α 0 hBS h6uS hA.memAng2 h6u
  have hα2QS : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ)) :=
    smoothOpen_const_mul_ae hQS
  have hα2Q : Work.Spaces.HkMem α 0 (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ)) :=
    Work.FTS.LocData.HkMem_const_mul α 0 (α ^ 2) hA.memRad2
  have h2S : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Elliptic.bslOp α u z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ)) :=
    Work.FTS.EllipticEst.smoothOpen_add hGop hα2QS
  have h2 : Work.Spaces.HkMem α 0
      (fun z θ => Work.Elliptic.bslOp α u z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ)) :=
    hkMem_add_open_ae α 0 hGop hα2QS hmBsl hα2Q
  have hαUS : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => α * (5 + α) * (z * Work.Spaces.pz u z θ)) :=
    smoothOpen_const_mul_ae hUS
  have hαU : Work.Spaces.HkMem α 0 (fun z θ => α * (5 + α) * (z * Work.Spaces.pz u z θ)) :=
    Work.FTS.LocData.HkMem_const_mul α 0 (α * (5 + α)) hmuU
  have h3S : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (Work.Elliptic.bslOp α u z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))
        + α * (5 + α) * (z * Work.Spaces.pz u z θ)) :=
    Work.FTS.EllipticEst.smoothOpen_add h2S hαUS
  have h3 : Work.Spaces.HkMem α 0
      (fun z θ => (Work.Elliptic.bslOp α u z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))
        + α * (5 + α) * (z * Work.Spaces.pz u z θ)) :=
    hkMem_add_open_ae α 0 h2S hαUS h2 hαU
  have h4S : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (Work.Spaces.pthIter 2 u z θ + 6 * u z θ)
        + ((Work.Elliptic.bslOp α u z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))
          + α * (5 + α) * (z * Work.Spaces.pz u z θ))) :=
    Work.FTS.EllipticEst.smoothOpen_add h1S h3S
  have h4 : Work.Spaces.HkMem α 0
      (fun z θ => (Work.Spaces.pthIter 2 u z θ + 6 * u z θ)
        + ((Work.Elliptic.bslOp α u z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))
          + α * (5 + α) * (z * Work.Spaces.pz u z θ))) :=
    hkMem_add_open_ae α 0 h1S h3S h1 h3
  -- ### The equation identifies the sum with `∂_θ(tan θ·u)` on the open quadrant
  have hG1agree : Work.FTS.EllipticEst.AgreeOnQ
      (fun z θ => (Work.Spaces.pthIter 2 u z θ + 6 * u z θ)
        + ((Work.Elliptic.bslOp α u z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))
          + α * (5 + α) * (z * Work.Spaces.pz u z θ)))
      (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z θ) := by
    intro z θ _hz _hθ0 _hθ1
    simp only [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero]
    ring
  have hmG1 : Work.Spaces.HkMem α 0
      (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z θ) :=
    Work.FTS.EllipticEst.RPFresh.HkMem_of_agreeOnQ hG1agree h4
  -- ### The six pairings
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ipMem_of_HkMem_agreeOnQ_ae hGop hBS hGagree
      (fun _ _ _ _ _ => rfl) hA.memG hA.memAng2
  · exact ipMem_of_HkMem_agreeOnQ_ae hQS hBS
      (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) hA.memRad2 hA.memAng2
  · exact ipMem_of_HkMem_agreeOnQ_ae hUS hBS
      (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) hmuU hA.memAng2
  · exact ipMem_of_HkMem_agreeOnQ_ae hG1S hBS
      (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) hmG1 hA.memAng2
  · exact ipMem_of_HkMem_agreeOnQ_ae huS hBS
      (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) hmu hA.memAng2
  · exact ipMem_of_HkMem_agreeOnQ_ae hBS hBS
      (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) hA.memAng2 hA.memAng2

end Work.FTS.EllipticEst.remov
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.SixNoTracesAux =====
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

open Work.Spaces

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Tonelli for the `ℋ⁸`-integrand of an open-class datum.**  For `f` of class `C^∞` on the
open quadrant with `HkMem α 8 f`, the iterated integral of `HkIntegrand α 8 f` in the order
`∫_θ ∫_z` equals `HkSq α 8 f`, its partially integrated function is integrable on the angles,
and for almost every angle the radial slice is integrable. -/
theorem sda_HkSqSwap_open8 (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : HkMem α 8 f) :
    (∫ σ in Iθ, ∫ s in Iz, HkIntegrand α 8 f s σ = HkSq α 8 f) ∧
      Integrable (fun σ : ℝ => ∫ s in Iz, HkIntegrand α 8 f s σ) (volume.restrict Iθ) ∧
      (∀ᵐ σ ∂(volume.restrict Iθ),
        IntegrableOn (fun s => HkIntegrand α 8 f s σ) Iz) := by
  have hnn : ∀ z θ : ℝ, 0 ≤ HkIntegrand α 8 f z θ :=
    fun z θ => HkIntegrand_nonneg α 8 f z θ
  have haesm : AEStronglyMeasurable
      (Function.uncurry fun z θ : ℝ => HkIntegrand α 8 f z θ)
      ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (hF.continuousOn_HkIntegrand α 8)
  have hslice : ∀ᵐ z ∂(volume.restrict Iz),
      Integrable (fun θ : ℝ => HkIntegrand α 8 f z θ) (volume.restrict Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hmem.1 z hz)
  have houter : Integrable (fun z : ℝ => ∫ θ in Iθ, HkIntegrand α 8 f z θ)
      (volume.restrict Iz) := hmem.2
  obtain ⟨h1, h2, h3⟩ :=
    Work.FTS.H2.swap_iterated_integral_of_nonneg
      (μ := volume.restrict Iz) (ν := volume.restrict Iθ) hnn haesm hslice houter
  exact ⟨by rw [HkSq]; exact h1, h2, h3⟩

end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cc.CutSpec =====
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
set_option maxHeartbeats 1600000

/-! ## The clauses of `psiCut_spec` that the assembly uses -/

/-- The properties of the cutoff family proved in `psiCut_spec`, in packaged form. -/
structure CutSpec (ψ : ℕ → Fn) (K : ℝ) : Prop where
  Kpos : 0 < K
  smooth : ∀ N : ℕ, ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (ψ N))
  nonneg : ∀ N : ℕ, ∀ z θ : ℝ, 0 ≤ ψ N z θ
  leone : ∀ N : ℕ, ∀ z θ : ℝ, ψ N z θ ≤ 1
  one : ∀ N : ℕ, ∀ z θ : ℝ, InPlateau N z θ → ψ N z θ = 1
  zero : ∀ N : ℕ, ∀ z θ : ℝ, OffBox N z θ → ψ N z θ = 0
  bound : ∀ N : ℕ, ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ,
    |Work.Spaces.mixed j i (ψ N) z θ| ≤ K
  lay : ∀ N : ℕ, ∀ j i : ℕ, 1 ≤ i → ∀ z θ : ℝ,
    NotInThetaLayer N θ → Work.Spaces.mixed j i (ψ N) z θ = 0


end Work.FTS.GalBasis.cc
end
end
-- ===== merged: Submission.Work.FTS.GalBasis.cut.LN_indicator_weighted_tendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis.cut

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The two angular layers of `LN N`, and the majorant weight

Everything below is stated in terms of the two closed intervals that make up `cc.LN N`; the
identifications `LN N = layA N ∪ layB N` (immediate from the definitions) and
`layA N, layB N ⊆ Iθ` (for `N ≥ 1`) are collected first, together with the pointwise bound
`ε/(sin 2θ) ≥ 1_{LN N}·G²·sin(2θ)^{-γ}` that the trace hypotheses supply. -/



/-- The majorant: `wgt ε θ = ε · sin(2θ)^{-1}`. -/
private def wgt (ε : ℝ) (θ : ℝ) : ℝ := ε * (Real.sin (2 * θ)) ^ (-1 : ℝ)





/-! ## The trace hypotheses as pointwise smallness -/




/-! ## The two layer integrals -/



/-! ## Continuity and integrability of the majorant -/



/-! ## The layer mass is at most `2ε` -/


/-! ## The main theorem -/


end Work.FTS.GalBasis.cut
end
end
-- ===== merged: Submission.Work.FTS.H2.ModalSolR.CoeffBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.H2.ModalSolR

/-- `eNorm m ≥ 0`. -/
theorem eNorm_nonneg (m : ℕ) : 0 ≤ Work.EllipticEst.ModalSolution.eNorm m :=
  (Work.EllipticEst.ModalSolution.eNorm_pos m).le

/-- **The sum of the coefficient `L²`-masses is bounded by the `L²`-mass of the source.** -/
theorem coeffL2_sum_le {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      Work.FTS.EllipticEst.Q0) (N : ℕ) :
    (∑ m ∈ Finset.range (N + 1), Work.EllipticEst.ModalSolution.eNorm m
        * ∫ z in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)
      ≤ ∫ p in Work.FTS.EllipticEst.Q0, F p.1 p.2 ^ 2 := by
  have hcm : ∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun z => (Work.FTS.PhiStar.Series.cmode m F z) ^ 2) (Set.Ioi 0) := fun m =>
    Work.EllipticEst.ModalSolution.cmode_memLp hsm hL2 m
  -- ## the real identity: sum of integrals = integral of the finite sum
  have hsum : (∑ m ∈ Finset.range (N + 1), Work.EllipticEst.ModalSolution.eNorm m
        * ∫ z in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)
      = ∫ z in Set.Ioi 0, ∑ m ∈ Finset.range (N + 1),
          Work.EllipticEst.ModalSolution.eNorm m
            * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 := by
    rw [MeasureTheory.integral_finsetSum]
    · exact Finset.sum_congr rfl (fun m _ => (MeasureTheory.integral_const_mul _ _).symm)
    · intro m _
      exact (hcm m).const_mul _
  have hnn_sum : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Set.Ioi 0)] fun z =>
      ∑ m ∈ Finset.range (N + 1), Work.EllipticEst.ModalSolution.eNorm m
        * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 :=
    Filter.Eventually.of_forall fun z => Finset.sum_nonneg fun m _ =>
      mul_nonneg (eNorm_nonneg m) (sq_nonneg _)
  have hint_sum : MeasureTheory.IntegrableOn (fun z =>
      ∑ m ∈ Finset.range (N + 1), Work.EllipticEst.ModalSolution.eNorm m
        * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2) (Set.Ioi 0) :=
    MeasureTheory.integrable_finsetSum (Finset.range (N + 1))
      (fun m _ => (hcm m).const_mul _)
  have hofReal : ENNReal.ofReal (∑ m ∈ Finset.range (N + 1),
        Work.EllipticEst.ModalSolution.eNorm m
          * ∫ z in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)
      = ∫⁻ z in Set.Ioi 0, ENNReal.ofReal (∑ m ∈ Finset.range (N + 1),
          Work.EllipticEst.ModalSolution.eNorm m
            * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2) := by
    rw [hsum, MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint_sum hnn_sum]

  -- ## Bessel at each `z`, integrated
  have hbessel : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal (∑ m ∈ Finset.range (N + 1),
        Work.EllipticEst.ModalSolution.eNorm m
          * (Work.FTS.PhiStar.Series.cmode m F z) ^ 2))
      ≤ ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (F z θ ^ 2 * Real.cos θ) :=
    lintegral_mono fun z => Work.EllipticEst.ModalSolution.cmode_bessel F z N
  -- ## Tonelli
  have hcont_g : ContinuousOn (fun p : ℝ × ℝ =>
      ENNReal.ofReal (F p.1 p.2 ^ 2 * Real.cos p.2)) Work.FTS.EllipticEst.Q0 :=
    ENNReal.continuous_ofReal.comp_continuousOn
      ((hsm.continuousOn.pow 2).mul (Real.continuous_cos.comp_continuousOn continuousOn_snd))
  have htonelli : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (F z θ ^ 2 * Real.cos θ))
      = ∫⁻ p in Set.Ioi 0 ×ˢ Work.Spaces.Iθ,
          ENNReal.ofReal (F p.1 p.2 ^ 2 * Real.cos p.2) := by
    refine (MeasureTheory.setLIntegral_prod (μ := volume) (ν := volume)
      (f := fun p : ℝ × ℝ => ENNReal.ofReal (F p.1 p.2 ^ 2 * Real.cos p.2))
      (s := Set.Ioi 0) (t := Work.Spaces.Iθ) ?_).symm
    have : AEMeasurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal (F p.1 p.2 ^ 2 * Real.cos p.2))
        ((volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)) := by
      rw [Work.EllipticEst.ModalSolution.restrict_Ioi_prod_Iθ_eq_Q0]
      exact hcont_g.aemeasurable Work.FTS.EllipticEst.isOpen_Q0.measurableSet
    exact this
  -- ## bound by the `Q0`-integral of `F²`
  have hbound : (∫⁻ p in Set.Ioi 0 ×ˢ Work.Spaces.Iθ,
        ENNReal.ofReal (F p.1 p.2 ^ 2 * Real.cos p.2))
      ≤ ∫⁻ p in Work.FTS.EllipticEst.Q0, ENNReal.ofReal (F p.1 p.2 ^ 2) := by
    rw [show (volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)
        = (volume : Measure (ℝ × ℝ)).restrict Work.FTS.EllipticEst.Q0 from
      Work.EllipticEst.ModalSolution.restrict_Ioi_prod_Iθ_eq_Q0]
    exact lintegral_mono fun p => ENNReal.ofReal_le_ofReal (by
      calc F p.1 p.2 ^ 2 * Real.cos p.2 ≤ F p.1 p.2 ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left (Real.cos_le_one p.2) (sq_nonneg (F p.1 p.2))
        _ = F p.1 p.2 ^ 2 := mul_one _)
  -- ## the `ofReal` of the source integral
  have hsource : (∫⁻ p in Work.FTS.EllipticEst.Q0, ENNReal.ofReal (F p.1 p.2 ^ 2))
      = ENNReal.ofReal (∫ p in Work.FTS.EllipticEst.Q0, F p.1 p.2 ^ 2) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hL2
      (Filter.Eventually.of_forall fun p => sq_nonneg _)).symm
  -- ## assemble
  have hchain : ENNReal.ofReal (∑ m ∈ Finset.range (N + 1),
        Work.EllipticEst.ModalSolution.eNorm m
          * ∫ z in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F z) ^ 2)
      ≤ ENNReal.ofReal (∫ p in Work.FTS.EllipticEst.Q0, F p.1 p.2 ^ 2) := by
    rw [hofReal]
    exact le_trans hbessel (le_trans (le_of_eq htonelli) (le_trans hbound (le_of_eq hsource)))
  exact (ENNReal.ofReal_le_ofReal_iff (MeasureTheory.integral_nonneg
    (fun p => sq_nonneg _))).mp hchain


/-- `lam m ≥ 0`. -/
theorem lam_nonneg' (m : ℕ) : 0 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
  simp only [Work.FTS.PhiStar.Gegenbauer.lam]; positivity

/-- **Bounds on the partial sums of the mode coefficients.** -/
theorem coeffSq_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ → ℝ}
    (horth : Work.Elliptic.OrthCond F) (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hL2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2)
      Work.FTS.EllipticEst.Q0) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z : ℝ, 0 < z → ∀ N : ℕ,
      ((∑ m ∈ Finset.range (N + 1), Work.EllipticEst.ModalSolution.eNorm m
          * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2) ≤ D * z ^ (-(1 : ℝ))) ∧
      ((∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Gegenbauer.lam m
          * Work.EllipticEst.ModalSolution.eNorm m
          * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2) ≤ D * z ^ (-(1 : ℝ))) := by
  set S : ℝ := ∫ p in Work.FTS.EllipticEst.Q0, F p.1 p.2 ^ 2 with hS
  have hS0 : 0 ≤ S := MeasureTheory.integral_nonneg fun p => sq_nonneg _
  have hcm : ∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun t => (Work.FTS.PhiStar.Series.cmode m F t) ^ 2) (Set.Ioi 0) := fun m =>
    Work.EllipticEst.ModalSolution.cmode_memLp hsm hL2 m
  refine ⟨S / α ^ 2, by positivity, fun z hz N => ?_⟩
  have hzq : 0 ≤ z ^ (-(1 : ℝ)) := Real.rpow_nonneg hz.le _
  have hsum := coeffL2_sum_le hsm hL2 N
  -- ## the squared Green's function bound for a single mode
  have hBsq : ∀ m : ℕ, 1 ≤ m →
      (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2
        ≤ (∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)
            * z ^ (-(1 : ℝ)) / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)) := by
    intro m hm
    set C : ℝ := ∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2 with hC
    set A : ℝ := Work.FTS.PhiStar.Series.acoeff α m F z with hAdef
    have hC0 : 0 ≤ C := by
      rw [hC]; exact MeasureTheory.integral_nonneg fun t => sq_nonneg _
    have hAeq : A = Work.FTS.PhiStar.Radial.radGreen α m
        (Work.FTS.PhiStar.Series.cmode m F) z := by
      rw [hAdef]; rfl
    have hB := Work.EllipticEst.ModalSolution.radGreen_abs_le α hα hα1 m hm (hcm m) hz
    have hB' : |A| ≤ Real.sqrt C * z ^ (-(1 / 2) : ℝ)
        / (α * (4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ)) := by
      rw [hAeq, hC]
      exact hB
    have hB2 : (Real.sqrt C * z ^ (-(1 / 2) : ℝ)
          / (α * (4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ))) ^ 2
        = C * z ^ (-(1 : ℝ)) / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)) := by
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hC0,
        Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (m : ℝ)), pow_two, ← Real.rpow_add hz]
      norm_num
      ring
    calc A ^ 2 = |A| ^ 2 := by rw [sq_abs]
      _ = |A| * |A| := by ring
      _ ≤ _ * _ := mul_le_mul hB' hB' (abs_nonneg _) (le_trans (abs_nonneg _) hB')
      _ = (Real.sqrt C * z ^ (-(1 / 2) : ℝ)
          / (α * (4 * (m : ℝ) + 5) * Real.sqrt (m : ℝ))) ^ 2 := by ring
      _ = C * z ^ (-(1 : ℝ)) / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)) := hB2
  -- ## reduction of a single term to `z⁻¹/α² · eNorm m · ‖cmode m‖²`
  have hred : ∀ m : ℕ, 1 ≤ m →
      (∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)
          * z ^ (-(1 : ℝ)) / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ))
        ≤ z ^ (-(1 : ℝ)) / α ^ 2
            * (∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2) := by
    intro m hm
    have hM1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hD1 : 1 ≤ (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ) := by
      nlinarith [hM1, sq_nonneg (4 * (m : ℝ) + 5)]
    have hC0 : 0 ≤ ∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2 :=
      MeasureTheory.integral_nonneg fun t => sq_nonneg _
    have hD0 : (0 : ℝ) < (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ) := by linarith
    have hden : α ^ 2 * 1 ≤ α ^ 2 * ((4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)) := by
      nlinarith [hD1, sq_nonneg α, hα]
    have hDne : ((4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)) ≠ 0 := ne_of_gt hD0
    have hgoal : (∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)
        * z ^ (-(1 : ℝ)) / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ))
        ≤ z ^ (-(1 : ℝ)) / α ^ 2
          * (∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2) := by
      have hαne : α ^ 2 ≠ 0 := by positivity
      field_simp
      nlinarith [hC0, hzq, hD1, sq_nonneg α, hα,
        mul_nonneg hC0 hzq, mul_nonneg (mul_nonneg hC0 hzq) (le_of_lt hα)]
    exact hgoal
  -- ## the two partial-sum bounds
  constructor
  · have hkey : ∀ m : ℕ,
        Work.EllipticEst.ModalSolution.eNorm m
            * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2
          ≤ z ^ (-(1 : ℝ)) / α ^ 2 * (Work.EllipticEst.ModalSolution.eNorm m
              * ∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2) := by
      intro m
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [acoeff_zero_of_orth horth α z]
        have h0 : (0 : ℝ) ≤ z ^ (-(1 : ℝ)) / α ^ 2
            * (Work.EllipticEst.ModalSolution.eNorm 0
              * ∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode 0 F t) ^ 2) :=
          mul_nonneg (div_nonneg hzq (by positivity))
            (mul_nonneg (eNorm_nonneg 0) (MeasureTheory.integral_nonneg fun t => sq_nonneg _))
        simpa using h0
      · have h1 := hBsq m hm
        have h2 := hred m hm
        have h3 : Work.EllipticEst.ModalSolution.eNorm m
              * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2
            ≤ Work.EllipticEst.ModalSolution.eNorm m
              * (z ^ (-(1 : ℝ)) / α ^ 2
                * (∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)) :=
          le_trans (mul_le_mul_of_nonneg_left h1 (eNorm_nonneg m))
            (mul_le_mul_of_nonneg_left h2 (eNorm_nonneg m))
        calc Work.EllipticEst.ModalSolution.eNorm m
              * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2
            ≤ Work.EllipticEst.ModalSolution.eNorm m
              * (z ^ (-(1 : ℝ)) / α ^ 2
                * (∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)) := h3
          _ = z ^ (-(1 : ℝ)) / α ^ 2 * (Work.EllipticEst.ModalSolution.eNorm m
                * ∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2) := by ring
    refine le_trans (Finset.sum_le_sum fun m _ => hkey m) ?_
    rw [← Finset.mul_sum]
    have hfin := mul_le_mul_of_nonneg_left hsum (div_nonneg hzq (by positivity : (0:ℝ) ≤ α ^ 2))
    rw [hS]
    calc z ^ (-(1 : ℝ)) / α ^ 2 * (∑ m ∈ Finset.range (N + 1),
          Work.EllipticEst.ModalSolution.eNorm m
            * ∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)
        ≤ z ^ (-(1 : ℝ)) / α ^ 2 * (∫ p in Work.FTS.EllipticEst.Q0, F p.1 p.2 ^ 2) := hfin
      _ = (∫ p in Work.FTS.EllipticEst.Q0, F p.1 p.2 ^ 2) / α ^ 2 * z ^ (-(1 : ℝ)) := by ring
  · have hkey2 : ∀ m : ℕ,
        Work.FTS.PhiStar.Gegenbauer.lam m * Work.EllipticEst.ModalSolution.eNorm m
            * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2
          ≤ z ^ (-(1 : ℝ)) / α ^ 2 * (Work.EllipticEst.ModalSolution.eNorm m
              * ∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2) := by
      intro m
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · have hlam0 : Work.FTS.PhiStar.Gegenbauer.lam 0 = 0 := by
          simp only [Work.FTS.PhiStar.Gegenbauer.lam]; norm_num
        rw [hlam0, zero_mul, zero_mul]
        exact mul_nonneg (div_nonneg hzq (by positivity))
          (mul_nonneg (eNorm_nonneg 0) (MeasureTheory.integral_nonneg fun t => sq_nonneg _))
      · have hM1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        have hD1 : 1 ≤ (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ) := by
          nlinarith [hM1, sq_nonneg (4 * (m : ℝ) + 5)]
        have hD0 : (0 : ℝ) < (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ) := by linarith
        have hlam : Work.FTS.PhiStar.Gegenbauer.lam m
            ≤ (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ) := by
          rw [Work.FTS.PhiStar.Gegenbauer.lam]
          nlinarith [hM1, sq_nonneg (4 * (m : ℝ) + 5)]
        have h1 := hBsq m hm
        have hE := eNorm_nonneg m
        have hstep1 : Work.FTS.PhiStar.Gegenbauer.lam m
              * (Work.EllipticEst.ModalSolution.eNorm m
                * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2)
            ≤ Work.FTS.PhiStar.Gegenbauer.lam m
              * (Work.EllipticEst.ModalSolution.eNorm m
                * ((∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)
                    * z ^ (-(1 : ℝ))
                    / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hE) (lam_nonneg' m)
        have hstep2 : Work.FTS.PhiStar.Gegenbauer.lam m
              * (Work.EllipticEst.ModalSolution.eNorm m
                * ((∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)
                    * z ^ (-(1 : ℝ))
                    / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ))))
            ≤ ((4 * (m : ℝ) + 5) ^ 2 * (m : ℝ))
              * (Work.EllipticEst.ModalSolution.eNorm m
                * ((∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)
                    * z ^ (-(1 : ℝ))
                    / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)))) :=
          mul_le_mul_of_nonneg_right hlam (by positivity)
        have hX : ∀ Y : ℝ, ((4 * (m : ℝ) + 5) ^ 2 * (m : ℝ))
              * (Y / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ))) = Y / α ^ 2 := by
          intro Y
          rw [show ((4 * (m : ℝ) + 5) ^ 2 * (m : ℝ))
                * (Y / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)))
              = Y * ((4 * (m : ℝ) + 5) ^ 2 * (m : ℝ))
                  / (α ^ 2 * ((4 * (m : ℝ) + 5) ^ 2 * (m : ℝ))) from by ring]
          exact mul_div_mul_right Y (α ^ 2)
            (by positivity : (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ) ≠ 0)
        have hstep3 : ((4 * (m : ℝ) + 5) ^ 2 * (m : ℝ))
              * (Work.EllipticEst.ModalSolution.eNorm m
                * ((∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)
                    * z ^ (-(1 : ℝ))
                    / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ))))
            = z ^ (-(1 : ℝ)) / α ^ 2 * (Work.EllipticEst.ModalSolution.eNorm m
                * ∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2) := by
          rw [show ((4 * (m : ℝ) + 5) ^ 2 * (m : ℝ))
                * (Work.EllipticEst.ModalSolution.eNorm m
                  * ((∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)
                      * z ^ (-(1 : ℝ))
                      / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ))))
              = Work.EllipticEst.ModalSolution.eNorm m
                * (((4 * (m : ℝ) + 5) ^ 2 * (m : ℝ))
                  * (((∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)
                      * z ^ (-(1 : ℝ)))
                      / (α ^ 2 * (4 * (m : ℝ) + 5) ^ 2 * (m : ℝ)))) from by ring,
            hX ((∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)
                * z ^ (-(1 : ℝ)))]
          ring
        have h4 : Work.FTS.PhiStar.Gegenbauer.lam m
              * (Work.EllipticEst.ModalSolution.eNorm m
                * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2)
            ≤ z ^ (-(1 : ℝ)) / α ^ 2 * (Work.EllipticEst.ModalSolution.eNorm m
                * ∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2) :=
          le_trans hstep1 (le_trans hstep2 (le_of_eq hstep3))
        calc Work.FTS.PhiStar.Gegenbauer.lam m * Work.EllipticEst.ModalSolution.eNorm m
              * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2
            = Work.FTS.PhiStar.Gegenbauer.lam m
              * (Work.EllipticEst.ModalSolution.eNorm m
                * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2) := by ring
          _ ≤ z ^ (-(1 : ℝ)) / α ^ 2 * (Work.EllipticEst.ModalSolution.eNorm m
                * ∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2) := h4
    refine le_trans (Finset.sum_le_sum fun m _ => hkey2 m) ?_
    rw [← Finset.mul_sum]
    have hfin := mul_le_mul_of_nonneg_left hsum (div_nonneg hzq (by positivity : (0:ℝ) ≤ α ^ 2))
    rw [hS]
    calc z ^ (-(1 : ℝ)) / α ^ 2 * (∑ m ∈ Finset.range (N + 1),
          Work.EllipticEst.ModalSolution.eNorm m
            * ∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m F t) ^ 2)
        ≤ z ^ (-(1 : ℝ)) / α ^ 2 * (∫ p in Work.FTS.EllipticEst.Q0, F p.1 p.2 ^ 2) := hfin
      _ = (∫ p in Work.FTS.EllipticEst.Q0, F p.1 p.2 ^ 2) / α ^ 2 * z ^ (-(1 : ℝ)) := by ring

end Work.FTS.H2.ModalSolR
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.hardyLocRight =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptApp

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

theorem hardyLocRight (c θ₁ : ℝ) (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) (hθ : θ₁ < Real.pi / 2)
    (hθ2 : Real.pi / 4 ≤ θ₁) {u : ℝ → ℝ} (hu : ContDiffOn ℝ 1 u (Set.Ioo θ₁ (Real.pi / 2)))
    (h1 : Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    MeasureTheory.lintegral
        (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioo θ₁ (Real.pi / 2)))
        (fun θ => ENNReal.ofReal ((Real.sin (2 * θ)) ^ (-c) * (u θ) ^ 2))
      ≤ ENNReal.ofReal (4 / (c - 1) ^ 2) *
        MeasureTheory.lintegral
          (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioo θ₁ (Real.pi / 2)))
          (fun θ => ENNReal.ofReal ((Real.sin (2 * θ)) ^ (2 - c) * (deriv u θ) ^ 2)) := by
  -- the reflected interval is a genuine left-end interval of length at most `π/4`
  have hX0 : 0 < Real.pi / 2 - θ₁ := by linarith
  have hX4 : Real.pi / 2 - θ₁ ≤ Real.pi / 4 := by linarith
  -- reflection: hypotheses for the left-end problem, and the two integral identities
  obtain ⟨hgsm, hgtend, hL, hR⟩ := reflect_hardyLocRight c θ₁ hθ hu h1
  rw [hL, hR]
  exact hardyLoc c (Real.pi / 2 - θ₁) hc1 hc2 hX0 hX4 hgsm hgtend

end Work.FTS.PhiStar.Honesty.CptApp
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.tendsto_lintegral_Omega =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp

set_option autoImplicit false

theorem tendsto_lintegral_Omega {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ}
    (hF : Work.Spaces.HkMem α k F) :
    Filter.Tendsto (fun n : ℕ =>
        MeasureTheory.lintegral
          (MeasureTheory.Measure.restrict MeasureTheory.volume
            (Work.FTS.PhiStar.Honesty.CptApp.Omega n ∩ Work.Spaces.Dom))
          (fun p => ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2)))
      Filter.atTop (nhds 0) := by
  classical
  set g : ℝ × ℝ → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (Work.Spaces.HkIntegrand α k F p.1 p.2) with hg
  have hIz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hIth : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hDom : MeasurableSet Work.Spaces.Dom := hIz.prod hIth
  have hOmeas : ∀ n : ℕ, MeasurableSet (Omega n ∩ Work.Spaces.Dom) :=
    fun n => (Omega_measurable n).inter hDom
  -- Finiteness of the total integral over `Dom`.
  have hprod : (volume : Measure (ℝ × ℝ)).restrict Work.Spaces.Dom
      = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
    rw [Work.Spaces.Dom]
    exact (Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      Work.Spaces.Iz Work.Spaces.Iθ).symm
  have hfin : ∫⁻ p, g p ∂(volume.restrict Work.Spaces.Dom) < ⊤ := by
    calc ∫⁻ p, g p ∂(volume.restrict Work.Spaces.Dom)
        = ∫⁻ p, g p ∂((volume.restrict Work.Spaces.Iz).prod
            (volume.restrict Work.Spaces.Iθ)) := by
          rw [hprod]
      _ ≤ ∫⁻ z, ∫⁻ θ, g (z, θ) ∂(volume.restrict Work.Spaces.Iθ)
              ∂(volume.restrict Work.Spaces.Iz) := lintegral_prod_le g
      _ = ∫⁻ z, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ)
              ∂(volume.restrict Work.Spaces.Iz) := by
          refine lintegral_congr_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
          exact (ofReal_integral_eq_lintegral_ofReal (hF.1 z hz)
            (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k F z θ)).symm
      _ = ENNReal.ofReal (∫ z in Work.Spaces.Iz,
            ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) := by
          rw [ofReal_integral_eq_lintegral_ofReal hF.2]
          exact Eventually.of_forall fun z =>
            integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k F z θ
      _ < ⊤ := ENNReal.ofReal_lt_top
  -- The finite measure `ν` whose masses are the wanted lintegrals.
  set ν : Measure (ℝ × ℝ) := (volume.restrict Work.Spaces.Dom).withDensity g with hν
  have hνuniv : ν Set.univ < ⊤ := by
    rw [hν, withDensity_apply _ MeasurableSet.univ]
    simpa using hfin
  have hA : ∀ n : ℕ,
      (∫⁻ p, g p ∂(volume.restrict (Omega n ∩ Work.Spaces.Dom)))
        = ν (Omega n ∩ Work.Spaces.Dom) := by
    intro n
    rw [hν, withDensity_apply _ (hOmeas n), Measure.restrict_restrict (hOmeas n),
      Set.inter_assoc, Set.inter_self]
  -- The decreasing family `t n = Ω_{n+1} ∩ Dom`.
  set t : ℕ → Set (ℝ × ℝ) := fun n => Omega (n + 1) ∩ Work.Spaces.Dom with ht
  have ht_meas : ∀ n : ℕ, MeasurableSet (t n) := fun n => hOmeas (n + 1)
  have ht_anti : Antitone t := antitone_nat_of_succ_le fun n =>
    Set.inter_subset_inter (Omega_succ_subset (m := n + 1) (by omega)) (subset_refl _)
  have hνt0 : ν (t 0) ≠ ∞ :=
    (lt_of_le_of_lt (measure_mono (Set.subset_univ _)) hνuniv).ne
  have hνnull : ν (⋂ n, t n) = 0 := by
    have hBmeas : MeasurableSet ({p : ℝ × ℝ | p.1 = 0} ∪ {p : ℝ × ℝ | p.2 = 0}
        ∪ {p : ℝ × ℝ | p.2 = Real.pi / 2}) :=
      ((measurable_fst (measurableSet_singleton 0)).union
        (measurable_snd (measurableSet_singleton 0))).union
        (measurable_snd (measurableSet_singleton _))
    have hbase : (volume.restrict Work.Spaces.Dom)
        ({p : ℝ × ℝ | p.1 = 0} ∪ {p : ℝ × ℝ | p.2 = 0}
          ∪ {p : ℝ × ℝ | p.2 = Real.pi / 2}) = 0 := by
      rw [Measure.restrict_apply hBmeas]
      exact measure_mono_null Set.inter_subset_left volume_boundary_union_zero
    have hνB : ν ({p : ℝ × ℝ | p.1 = 0} ∪ {p : ℝ × ℝ | p.2 = 0}
        ∪ {p : ℝ × ℝ | p.2 = Real.pi / 2}) = 0 := by
      rw [hν, withDensity_apply' g _]
      exact setLIntegral_measure_zero _ g hbase
    exact measure_mono_null Omega_iInter_subset_boundary hνB
  have hlim : Tendsto (fun n => ν (t n)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := ν) (s := t)
      (fun n => (ht_meas n).nullMeasurableSet) ht_anti ⟨0, hνt0⟩
    rw [hνnull] at h
    exact h
  -- `ν (Ω_{n+1} ∩ Dom)` is the lintegral of the shifted index.
  have hshift : Tendsto (fun n : ℕ =>
      ∫⁻ p, g p ∂(volume.restrict (Omega (n + 1) ∩ Work.Spaces.Dom))) atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ hlim
    filter_upwards with n
    exact (hA (n + 1)).symm
  -- Shift the index back: `Ω_n = Ω_{(n-1)+1}` for `n ≥ 1`.
  have hpred : Tendsto (fun n : ℕ => n - 1) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b + 1, fun a ha => by omega⟩
  have hcomp : Tendsto (fun n : ℕ =>
      ∫⁻ p, g p ∂(volume.restrict (Omega (n - 1 + 1) ∩ Work.Spaces.Dom))) atTop (𝓝 0) :=
    hshift.comp hpred
  refine Tendsto.congr' ?_ hcomp
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Nat.sub_add_cancel hn]

end Work.FTS.PhiStar.Honesty.CptApp
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.EllWeakAux.Fstar_source_sub =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.EllWeakAux

/-- **`F_*` subtracts on sources of the weak class.**

If `G = bslOp α Ψ` and `H = bslOp α Φ` are two sources of the weak class `EllWeakPos` (so that
both angular moments `F_*(G)(z) = ∫_θ G z θ · sinθcos²θ dθ` and `F_*(H)(z)` vanish for `z > 0`),
then the source `G - H` of the difference is again orthogonal to `sinθcos²θ`:

  `F_*(G - H)(z) = 0`  for every `z > 0`.

The content is the linearity `F_*(G - H) = F_*(G) - F_*(H)` of the angular moment on the
relevant slices.  It is not available for free (`F_*` is a Bochner integral, additive only on
integrable functions), so the proof establishes the integrability of the two slices
`θ ↦ G z θ · sinθcos²θ` and `θ ↦ H z θ · sinθcos²θ`:

* a *source* of the weak class is a priori neither smooth nor even known to have measurable
  angular slices — it only satisfies the weighted `L²` hypothesis `HkMem α k G`, whose
  integrand contains the single `D_z`-summand with `i = 0`, i.e.
  `(G z θ · w z / sin(2θ)^{η/2})²`.  Splitting that summand off (all summands are squares) gives
  the `L²(Iθ)` control of the weighted slice;
* measurability of the slice comes from the *equation*: on the open quadrant `G = bslOp α Ψ`
  with `Ψ` of class `C^∞` there, hence `G` agrees a.e. on `Iθ` with the slice of the smooth
  function `bslOp α Ψ` (`SmoothOpen_bslOp_of_smoothOpen`), which is a.e. strongly measurable by
  continuity (`aesm_slice_of_continuousOn_Qd`);
* `LamEst.integrable_mul_sinCos2` then converts the weighted `L²` control plus that
  measurability into the `L¹`-integrability against `sinθcos²θ`.

The final step is `integral_sub` on `volume.restrict Iθ` plus the two moment hypotheses. -/
theorem Fstar_source_sub (k : ℕ) {α : ℝ} {G H Ψ Φ : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.TT.EllWeakPos α k G Ψ)
    (hH : Work.FTS.EllipticEst.TT.EllWeakPos α k H Φ) :
    ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (fun z θ => G z θ - H z θ) z = 0 := by
  intro z hz
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  -- `Ψ` and `Φ` are `C^∞` on the open quadrant, hence so are `bslOp α Ψ` and `bslOp α Φ`.
  have hsoΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ).mpr (hG.smooth)
  have hsoΦ : Work.FTS.EllipticEst.SmoothOpen Φ :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall Φ).mpr (hH.smooth)
  have hsoB : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Ψ) :=
    Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hsoΨ
  have hsoB' : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α Φ) :=
    Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hsoΦ
  -- On the open interval the slices of the sources are those of the smooth representatives.
  have haeG : (fun θ => G z θ) =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => Work.Elliptic.bslOp α Ψ z θ) := by
    rw [show MeasureTheory.volume.restrict Work.Spaces.Iθ
        = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) from
      (MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2))).symm]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    exact (hG.eq z hz θ hθ.1 hθ.2).symm
  have haeH : (fun θ => H z θ) =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => Work.Elliptic.bslOp α Φ z θ) := by
    rw [show MeasureTheory.volume.restrict Work.Spaces.Iθ
        = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) from
      (MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2))).symm]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    exact (hH.eq z hz θ hθ.1 hθ.2).symm
  -- A.e. strong measurability of the two slices.
  have haesmG : MeasureTheory.AEStronglyMeasurable (fun θ => G z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (Work.Spaces.aesm_slice_of_continuousOn_Qd
      (Function.uncurry (Work.Elliptic.bslOp α Ψ)) hsoB.continuousOn hz).congr haeG.symm
  have haesmH : MeasureTheory.AEStronglyMeasurable (fun θ => H z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (Work.Spaces.aesm_slice_of_continuousOn_Qd
      (Function.uncurry (Work.Elliptic.bslOp α Φ)) hsoB'.continuousOn hz).congr haeH.symm
  -- The angular weight factor `φ θ = w z / sin(2θ)^{η/2}` is measurable.
  have hφmeas : Measurable (fun θ : ℝ => Work.Spaces.w z
      / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) :=
    measurable_const.div
      ((Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _)
  -- The `i = 0` summand of the `ℋ^k`-integrand is the weighted square of the slice.
  have hsqG : MeasureTheory.Integrable (fun θ => (G z θ * (Work.Spaces.w z
      / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (hG.memF.1 z hzI).mono' ((haesmG.mul hφmeas.aestronglyMeasurable).pow 2)
      (Filter.Eventually.of_forall fun θ => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact Work.Spaces.sq_le_HkIntegrand_z α k G z θ 0 (Nat.zero_le k))
  have hsqH : MeasureTheory.Integrable (fun θ => (H z θ * (Work.Spaces.w z
      / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (hH.memF.1 z hzI).mono' ((haesmH.mul hφmeas.aestronglyMeasurable).pow 2)
      (Filter.Eventually.of_forall fun θ => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact Work.Spaces.sq_le_HkIntegrand_z α k H z θ 0 (Nat.zero_le k))
  -- Integrability of the two slices against `sinθcos²θ`.
  have hIntG : MeasureTheory.Integrable (fun θ => G z θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.PhiStar.Honesty.CptApp.LamEst.integrable_mul_sinCos2 hz haesmG hsqG
  have hIntH : MeasureTheory.Integrable (fun θ => H z θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.PhiStar.Honesty.CptApp.LamEst.integrable_mul_sinCos2 hz haesmH hsqH
  -- `F_*(G - H) = F_*(G) - F_*(H) = 0 - 0 = 0`.
  rw [Work.Elliptic.Fstar]
  rw [show (∫ θ in Work.Spaces.Iθ, (G z θ - H z θ) * Work.Elliptic.sinCos2 θ)
      = ∫ θ in Work.Spaces.Iθ, (G z θ * Work.Elliptic.sinCos2 θ
          - H z θ * Work.Elliptic.sinCos2 θ) from
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
  rw [MeasureTheory.integral_sub hIntG hIntH]
  rw [show (∫ θ in Work.Spaces.Iθ, G z θ * Work.Elliptic.sinCos2 θ)
        = Work.Elliptic.Fstar G z from rfl,
    show (∫ θ in Work.Spaces.Iθ, H z θ * Work.Elliptic.sinCos2 θ)
        = Work.Elliptic.Fstar H z from rfl]
  rw [hG.orthF z hz, hH.orthF z hz, sub_zero]

end Work.FTS.PhiStar.Honesty.EllWeakAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.IBPsub.Iterate =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.SlotsLimit

set_option autoImplicit false
set_option maxHeartbeats 2000000

local notation "Q0" => Work.FTS.EllipticEst.Q0

/-! ## Pointwise product rules for the weighted factors -/

/-- `∂_z(z · ψ) = ψ + z ∂_zψ`. -/
theorem pz_mul_z {ψ : ℝ → ℝ → ℝ} (hψ : TestQ0 ψ) (z θ : ℝ) :
    Work.Spaces.pz (fun z θ => z * ψ z θ) z θ
      = ψ z θ + z * Work.Spaces.pz ψ z θ := by
  have h1 : HasDerivAt (fun z' : ℝ => z') (1 : ℝ) z := hasDerivAt_id z
  have h2 : HasDerivAt (fun z' : ℝ => ψ z' θ) (Work.Spaces.pz ψ z θ) z :=
    ((hψ.smooth.comp (contDiff_id.prodMk (contDiff_const (c := θ)))).differentiable
      (by norm_num)).differentiableAt (x := z) |>.hasDerivAt
  have hmul : HasDerivAt (fun z' : ℝ => z' * ψ z' θ)
      (1 * ψ z θ + z * Work.Spaces.pz ψ z θ) z := h1.mul h2
  show deriv (fun z' : ℝ => z' * ψ z' θ) z = ψ z θ + z * Work.Spaces.pz ψ z θ
  rw [hmul.deriv]
  ring

/-- `∂_θ(sin 2θ · ψ) = sin 2θ ∂_θψ + 2 cos 2θ · ψ`. -/
theorem pth_mul_sin {ψ : ℝ → ℝ → ℝ} (hψ : TestQ0 ψ) (z θ : ℝ) :
    Work.Spaces.pth (fun z θ => Real.sin (2 * θ) * ψ z θ) z θ
      = Real.sin (2 * θ) * Work.Spaces.pth ψ z θ
        + 2 * Real.cos (2 * θ) * ψ z θ := by
  have h1 : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ'))
      (2 * Real.cos (2 * θ)) θ := by
    have h := ((hasDerivAt_id θ).const_mul (2 : ℝ)).sin
    simpa only [id_eq, mul_one, mul_comm (Real.cos (2 * θ))] using h
  have h2 : HasDerivAt (fun θ' : ℝ => ψ z θ') (Work.Spaces.pth ψ z θ) θ :=
    ((hψ.smooth.comp (contDiff_const.prodMk contDiff_id)).differentiable
      (by norm_num)).differentiableAt (x := θ) |>.hasDerivAt
  have hmul : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ') * ψ z θ')
      (2 * Real.cos (2 * θ) * ψ z θ + Real.sin (2 * θ) * Work.Spaces.pth ψ z θ) θ :=
    h1.mul h2
  show deriv (fun θ' : ℝ => Real.sin (2 * θ') * ψ z θ') θ
      = Real.sin (2 * θ) * Work.Spaces.pth ψ z θ + 2 * Real.cos (2 * θ) * ψ z θ
  rw [hmul.deriv]
  ring

/-! ## The iterated plain transposes -/

/-- `∂_z^j (∂_zψ) = ∂_z(∂_z^j ψ)`. -/
theorem pzIter_pz_comm (j : ℕ) (ψ : ℝ → ℝ → ℝ) :
    Work.Spaces.pzIter j (Work.Spaces.pz ψ) = Work.Spaces.pz (Work.Spaces.pzIter j ψ) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Work.Spaces.pzIter_succ, ih, Work.Spaces.pzIter_succ]

/-- `∂_θ^i (∂_θψ) = ∂_θ(∂_θ^i ψ)`. -/
theorem pthIter_pth_comm (i : ℕ) (ψ : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter i (Work.Spaces.pth ψ) = Work.Spaces.pth (Work.Spaces.pthIter i ψ) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]

/-- **Iterated integration by parts for `∂_z`.** -/
theorem integral_pzIter_mul_eq : ∀ j : ℕ, ∀ {g ψ : ℝ → ℝ → ℝ},
    Work.FTS.EllipticEst.SmoothOpen g → TestQ0 ψ →
    ∫ p : ℝ × ℝ, Work.Spaces.pzIter j g p.1 p.2 * ψ p.1 p.2
      = (-1 : ℝ) ^ j * ∫ p : ℝ × ℝ, g p.1 p.2 * Work.Spaces.pzIter j ψ p.1 p.2
  | 0, g, ψ, hg, hψ => by simp
  | (j + 1), g, ψ, hg, hψ => by
      have hpg : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pzIter j g) :=
        Work.FTS.EllipticEst.SmoothOpen.pzIter hg j
      have hstep : ∫ p : ℝ × ℝ, Work.Spaces.pzIter (j + 1) g p.1 p.2 * ψ p.1 p.2
          = -∫ p : ℝ × ℝ,
              Work.Spaces.pzIter j g p.1 p.2 * Work.Spaces.pz ψ p.1 p.2 :=
        integral_pz_mul_eq_neg (g := Work.Spaces.pzIter j g) (ψ := ψ) hpg hψ
      rw [hstep]
      rw [integral_pzIter_mul_eq j (ψ := Work.Spaces.pz ψ) hg (testQ0_pz hψ)]
      rw [pzIter_pz_comm j ψ, ← Work.Spaces.pzIter_succ]
      rw [pow_succ]
      ring

/-- **Iterated integration by parts for `∂_θ`.** -/
theorem integral_pthIter_mul_eq : ∀ i : ℕ, ∀ {g ψ : ℝ → ℝ → ℝ},
    Work.FTS.EllipticEst.SmoothOpen g → TestQ0 ψ →
    ∫ p : ℝ × ℝ, Work.Spaces.pthIter i g p.1 p.2 * ψ p.1 p.2
      = (-1 : ℝ) ^ i * ∫ p : ℝ × ℝ, g p.1 p.2 * Work.Spaces.pthIter i ψ p.1 p.2
  | 0, g, ψ, hg, hψ => by simp
  | (i + 1), g, ψ, hg, hψ => by
      have hpg : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter i g) :=
        smoothOpen_pthIter hg i
      have hstep : ∫ p : ℝ × ℝ, Work.Spaces.pthIter (i + 1) g p.1 p.2 * ψ p.1 p.2
          = -∫ p : ℝ × ℝ,
              Work.Spaces.pthIter i g p.1 p.2 * Work.Spaces.pth ψ p.1 p.2 :=
        integral_pth_mul_eq_neg (g := Work.Spaces.pthIter i g) (ψ := ψ) hpg hψ
      rw [hstep]
      rw [integral_pthIter_mul_eq i (ψ := Work.Spaces.pth ψ) hg (testQ0_pth hψ)]
      rw [pthIter_pth_comm i ψ, ← Work.Spaces.pthIter_succ]
      rw [pow_succ]
      ring

/-! ## The weighted transposes `D_z`, `D_θ` and their iterates -/

/-- **Integration by parts for `D_z = z ∂_z`**: the transpose `DzStar ψ = -(z ∂_zψ + ψ)`. -/
theorem integral_Dz_mul_eq {g ψ : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hψ : TestQ0 ψ) :
    ∫ p : ℝ × ℝ, Work.Spaces.Dz g p.1 p.2 * ψ p.1 p.2
      = ∫ p : ℝ × ℝ, g p.1 p.2 * DzStar ψ p.1 p.2 := by
  have hzψ : TestQ0 (fun z θ => z * ψ z θ) := by
    simpa using testQ0_zpow_mul 1 hψ
  have h1 : ∫ p : ℝ × ℝ, Work.Spaces.pz g p.1 p.2 * (p.1 * ψ p.1 p.2)
      = -∫ p : ℝ × ℝ,
          g p.1 p.2 * Work.Spaces.pz (fun z θ => z * ψ z θ) p.1 p.2 :=
    integral_pz_mul_eq_neg hg hzψ
  calc ∫ p : ℝ × ℝ, Work.Spaces.Dz g p.1 p.2 * ψ p.1 p.2
      = ∫ p : ℝ × ℝ, Work.Spaces.pz g p.1 p.2 * (p.1 * ψ p.1 p.2) := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        simp only [Work.Spaces.Dz]; ring
    _ = -∫ p : ℝ × ℝ,
          g p.1 p.2 * Work.Spaces.pz (fun z θ => z * ψ z θ) p.1 p.2 := h1
    _ = ∫ p : ℝ × ℝ,
          -(g p.1 p.2 * Work.Spaces.pz (fun z θ => z * ψ z θ) p.1 p.2) :=
        (MeasureTheory.integral_neg _).symm
    _ = ∫ p : ℝ × ℝ, g p.1 p.2 * DzStar ψ p.1 p.2 := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        show -(g p.1 p.2 * Work.Spaces.pz (fun z θ => z * ψ z θ) p.1 p.2)
            = g p.1 p.2 * DzStar ψ p.1 p.2
        rw [pz_mul_z hψ p.1 p.2]
        simp only [DzStar, Work.Spaces.Dz]; ring

/-- **Integration by parts for `D_θ = sin 2θ · ∂_θ`**: the transpose
`DthStar ψ = -(sin 2θ ∂_θψ + 2 cos 2θ · ψ)`. -/
theorem integral_Dth_mul_eq {g ψ : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hψ : TestQ0 ψ) :
    ∫ p : ℝ × ℝ, Work.Spaces.Dth g p.1 p.2 * ψ p.1 p.2
      = ∫ p : ℝ × ℝ, g p.1 p.2 * DthStar ψ p.1 p.2 := by
  have hsψ : TestQ0 (fun z θ => Real.sin (2 * θ) * ψ z θ) := testQ0_sin_mul hψ
  have h1 : ∫ p : ℝ × ℝ,
        Work.Spaces.pth g p.1 p.2 * (Real.sin (2 * p.2) * ψ p.1 p.2)
      = -∫ p : ℝ × ℝ,
          g p.1 p.2 * Work.Spaces.pth (fun z θ => Real.sin (2 * θ) * ψ z θ) p.1 p.2 :=
    integral_pth_mul_eq_neg hg hsψ
  calc ∫ p : ℝ × ℝ, Work.Spaces.Dth g p.1 p.2 * ψ p.1 p.2
      = ∫ p : ℝ × ℝ,
          Work.Spaces.pth g p.1 p.2 * (Real.sin (2 * p.2) * ψ p.1 p.2) := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        simp only [Work.Spaces.Dth]; ring
    _ = -∫ p : ℝ × ℝ,
          g p.1 p.2 * Work.Spaces.pth (fun z θ => Real.sin (2 * θ) * ψ z θ) p.1 p.2 := h1
    _ = ∫ p : ℝ × ℝ,
          -(g p.1 p.2 * Work.Spaces.pth (fun z θ => Real.sin (2 * θ) * ψ z θ) p.1 p.2) :=
        (MeasureTheory.integral_neg _).symm
    _ = ∫ p : ℝ × ℝ, g p.1 p.2 * DthStar ψ p.1 p.2 := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        show -(g p.1 p.2 * Work.Spaces.pth (fun z θ => Real.sin (2 * θ) * ψ z θ) p.1 p.2)
            = g p.1 p.2 * DthStar ψ p.1 p.2
        rw [pth_mul_sin hψ p.1 p.2]
        simp only [DthStar, Work.Spaces.Dth]; ring

/-- **Iterated integration by parts for `D_z`**: the transpose is the iterate of `DzStar`. -/
theorem integral_DzIter_mul_eq : ∀ j : ℕ, ∀ {g ψ : ℝ → ℝ → ℝ},
    Work.FTS.EllipticEst.SmoothOpen g → TestQ0 ψ →
    ∫ p : ℝ × ℝ, Work.Spaces.DzIter j g p.1 p.2 * ψ p.1 p.2
      = ∫ p : ℝ × ℝ, g p.1 p.2 * DzIterStar j ψ p.1 p.2
  | 0, g, ψ, hg, hψ => rfl
  | (j + 1), g, ψ, hg, hψ => by
      have hstep : ∫ p : ℝ × ℝ, Work.Spaces.DzIter (j + 1) g p.1 p.2 * ψ p.1 p.2
          = ∫ p : ℝ × ℝ,
              Work.Spaces.DzIter j g p.1 p.2 * DzStar ψ p.1 p.2 :=
        integral_Dz_mul_eq (g := Work.Spaces.DzIter j g) (ψ := ψ)
          (Work.FTS.EllipticEst.SmoothOpen.DzIter hg j) hψ
      rw [hstep]
      exact integral_DzIter_mul_eq j (ψ := DzStar ψ) hg (testQ0_DzStar hψ)

/-- **Iterated integration by parts for `D_θ`**: the transpose is the iterate of `DthStar`. -/
theorem integral_DthIter_mul_eq : ∀ i : ℕ, ∀ {g ψ : ℝ → ℝ → ℝ},
    Work.FTS.EllipticEst.SmoothOpen g → TestQ0 ψ →
    ∫ p : ℝ × ℝ, Work.Spaces.DthIter i g p.1 p.2 * ψ p.1 p.2
      = ∫ p : ℝ × ℝ, g p.1 p.2 * DthIterStar i ψ p.1 p.2
  | 0, g, ψ, hg, hψ => rfl
  | (i + 1), g, ψ, hg, hψ => by
      have hstep : ∫ p : ℝ × ℝ, Work.Spaces.DthIter (i + 1) g p.1 p.2 * ψ p.1 p.2
          = ∫ p : ℝ × ℝ,
              Work.Spaces.DthIter i g p.1 p.2 * DthStar ψ p.1 p.2 :=
        integral_Dth_mul_eq (g := Work.Spaces.DthIter i g) (ψ := ψ)
          (Work.FTS.EllipticEst.SmoothOpen.DthIter hg i) hψ
      rw [hstep]
      exact integral_DthIter_mul_eq i (ψ := DthStar ψ) hg (testQ0_DthStar hψ)

/-- **Integration by parts for a mixed operator** `mixed j i = D_z^j D_θ^i`. -/
theorem integral_mixed_mul_eq (j i : ℕ) {g ψ : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hψ : TestQ0 ψ) :
    ∫ p : ℝ × ℝ, Work.Spaces.mixed j i g p.1 p.2 * ψ p.1 p.2
      = ∫ p : ℝ × ℝ, g p.1 p.2 * mixedStar j i ψ p.1 p.2 := by
  rw [Work.Spaces.mixed]
  rw [integral_DzIter_mul_eq j (ψ := ψ)
    (Work.FTS.EllipticEst.SmoothOpen.DthIter hg i) hψ]
  exact integral_DthIter_mul_eq i (ψ := DzIterStar j ψ) hg (testQ0_DzIterStar hψ j)

end Work.FTS.PhiStar.Honesty.SlotsLimit
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.blocks

/-- **Additivity of `L₁₂` over `F_* + u`** at every `z ≥ 0`, for a datum of the open smooth class
(`SmoothOpen` + `ℋ⁴`).  The `SmoothOpen`-scoped companion of
`Work.FTS.GalFields.Tail.L12_Fstar_add`. -/
theorem L12_Fstar_add_open {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {u : ℝ → ℝ → ℝ}
    (huS : Work.FTS.EllipticEst.SmoothOpen u) (hu4 : Work.Spaces.HkMem α 4 u) {z : ℝ}
    (hz : 0 ≤ z) :
    Work.Construction.L12 (fun z θ => Work.Construction.Fstar α z θ + u z θ) z
      = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 u z := by
  -- the angular slice of `u`: `s > z ≥ 0`, so `s > 0` and the `HkMem`-Cauchy–Schwarz applies
  have hslice : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * u s θ / s) Work.Spaces.Iθ :=
    fun s hs =>
      Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem huS hu4
        (lt_of_le_of_lt hz hs)
  -- the density of `u`: integrable on `(0,∞)`, hence on the smaller `(z,∞)` since `z ≥ 0`
  have hdens : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K u) (Set.Ioi z) :=
    (Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem huS hu4).mono_set
      (fun s hs => lt_of_le_of_lt hz hs)
  exact (Work.FTS.LocData.L12_add_mul (c := 0) (z := z)
    (a := Work.Construction.Fstar α) (b := u)
    (fun s _ => Work.Stability.integrableOn_slice_Fstar α hα s)
    hslice
    (Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn hα hα1 z hz)
    hdens).1

end Work.FTS.StrongEps.blocks
end
