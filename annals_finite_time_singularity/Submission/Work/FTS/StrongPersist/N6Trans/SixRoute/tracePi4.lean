import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.ClassCHon.CmodeDefs
import Submission.Work.FTS.EllipticEst.Alpha4.integrable_slice_pthDz_sigma
import Submission.Work.FTS.EllipticEst.H2W.Ae.TruncIdentAe
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.interpol_trunc_defs
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.LocDataExt.Defs
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongPersist.N6.Swap6
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS.TransportS.SupDzWeighted.supDz_weighted_avg_le
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.SolutionDelivery.Scaling.vorticityDecay_rescaleDatum
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.dzSliceHonest =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

/-! ## The two elementary weight facts

`w` is the radial weight `(1+z)²/z²`; for `z > 0` it is `≥ 1` (indeed `w z = (1 + 1/z)²`),
so its square is `≥ 1` as well.  `thEta θ = sin(2θ)^{-η}` is `≥ 1` on the open angular
interval, because `sin(2θ) ∈ (0,1]` there and the exponent `-η` is negative. -/

theorem one_le_w_of_pos {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
  nlinarith

theorem one_le_w_sq_of_pos {z : ℝ} (hz : 0 < z) : 1 ≤ (Work.Spaces.w z) ^ 2 := by
  nlinarith [one_le_w_of_pos hz]

theorem one_le_thEta_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.thEta θ := by
  rw [Work.FTS.EllipticEst.thEta]
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h := Real.rpow_le_rpow_of_nonpos (z := -(Work.Spaces.eta)) hsin
    (Real.sin_le_one (2 * θ)) (by norm_num [Work.Spaces.eta])
  rwa [Real.one_rpow] at h

/-- **The `D_z`-slice of a `SliceHonestOpen` datum is integrable on `Iθ`.**

`SliceHonestOpen G` gives, at every `z > 0`, the integrability of the weighted square
`(D_zG z θ)² (w z)² sin(2θ)^{-η}` on `Iθ`.  On the open interval both factors of the extra
weight are `≥ 1` (`w z ≥ 1` for `z > 0`, `sin(2θ)^{-η} ≥ 1` for `0 < θ < π/2`), so the
weighted square dominates the square `(D_zG z θ)²` there; and `|t| ≤ t² + 1`, so the slice
itself is dominated by `(D_zG z θ)² + 1 ≤ (D_zG z θ)² (w z)² sin(2θ)^{-η} + (w z)²
sin(2θ)^{-η}`, a sum of two integrable functions (the first is the hypothesis, the second is
a constant multiple of `thEta`, integrable on `Iθ`).  The endpoints `θ = 0, π/2` are null,
which is why the estimates are stated on `Ioo 0 (π/2)` and transported with
`volume.restrict Iθ = volume.restrict (Ioo 0 (π/2))`. -/
theorem dzSliceHonest (G : ℝ → ℝ → ℝ) (hsm : Work.FTS.EllipticEst.SmoothOpen G)
    (hhon : Work.EllipticEst.Core.i0Aux.SliceHonestOpen G) :
    ∀ w : ℝ, 0 < w → MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.Dz G w θ)
      Work.Spaces.Iθ := by
  intro w hw
  have hIθrestrict : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
  have hw2 : 1 ≤ (Work.Spaces.w w) ^ 2 := one_le_w_sq_of_pos hw
  have hIntF : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Dz G w θ) ^ 2 * (Work.Spaces.w w) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := hhon.2.2 w hw
  have hIntG : MeasureTheory.Integrable
      (fun θ : ℝ => (Work.Spaces.Dz G w θ) ^ 2 * (Work.Spaces.w w) ^ 2
        * Work.FTS.EllipticEst.thEta θ + (Work.Spaces.w w) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    rw [← hIθrestrict]
    exact hIntF.add (Work.FTS.EllipticEst.integrableOn_thEta.1.const_mul _)
  show MeasureTheory.Integrable (fun θ : ℝ => Work.Spaces.Dz G w θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)
  rw [hIθrestrict]
  refine MeasureTheory.Integrable.mono' hIntG ?_ ?_
  · have hcont : ContinuousOn (fun θ : ℝ => w * Work.Spaces.pz G w θ)
        (Set.Ioo 0 (Real.pi / 2)) :=
      continuousOn_const.mul ((hsm.pz.curry_θ hw).continuousOn)
    exact hcont.aestronglyMeasurable measurableSet_Ioo
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hσ1 : 1 ≤ Work.FTS.EllipticEst.thEta θ := one_le_thEta_of_mem_Ioo hθ
    have hMσ : 1 ≤ (Work.Spaces.w w) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
      nlinarith [hw2, hσ1]
    rw [Real.norm_eq_abs]
    have habs : |Work.Spaces.Dz G w θ| ≤ (Work.Spaces.Dz G w θ) ^ 2 + 1 := by
      have h := sq_nonneg (|Work.Spaces.Dz G w θ| - 1)
      have h2 : (|Work.Spaces.Dz G w θ|) ^ 2 = (Work.Spaces.Dz G w θ) ^ 2 := sq_abs _
      nlinarith [h, abs_nonneg (Work.Spaces.Dz G w θ), h2]
    have hquad : (Work.Spaces.Dz G w θ) ^ 2 ≤ (Work.Spaces.Dz G w θ) ^ 2
        * (Work.Spaces.w w) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
      have h1 := le_mul_of_one_le_right (sq_nonneg (Work.Spaces.Dz G w θ)) hw2
      have h1' : 0 ≤ (Work.Spaces.Dz G w θ) ^ 2 * (Work.Spaces.w w) ^ 2 :=
        mul_nonneg (sq_nonneg _) (by linarith)
      have h2' := le_mul_of_one_le_right h1' hσ1
      linarith
    linarith

end Work.FTS.EllSol.EllPkgAux.MollDom
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_continuousOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 400000

/-- **Continuity of the angular slice of a trace-class datum on the closed interval
`[0, π/2]`.**

For `G` in the trace class (`TraceClass G`) and a positive radius `w > 0` the slice
`s ↦ G w s` is continuous on `Iθ = [0, π/2]`.  On the *open* interval `(0, π/2)` this is
`SmoothOpen G` restricted to the slice (`SmoothOpen.curry_θ`); at the two endpoints the
continuity within `[0, π/2]` is exactly the pair (endpoint *value*, one-sided *trace*) of
`TraceClass`: `G w 0 = 0` together with `G w s → 0` as `s → 0⁺`, and `G w (π/2) = 0`
together with `G w s → 0` as `s → (π/2)⁻`.  (`ContinuousWithinAt` on `Ioi 0` upgrades to
`Ici 0` by `continuousWithinAt_Ioi_iff_Ici`, and the closed interval `[0, π/2]` is a
subset of `Ici 0`; dually at `π/2`.) -/
theorem slice_continuousOn (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    {w : ℝ} (hw : 0 < w) :
    ContinuousOn (fun s : ℝ => G w s) Work.Spaces.Iθ := by
  obtain ⟨hsm, h0, hpi, htr0, htrpi, -, -, -⟩ := hT
  show ContinuousOn (fun s : ℝ => G w s) (Set.Icc 0 (Real.pi / 2))
  -- the slice is continuous on the open interval, and its two one-sided endpoint
  -- limits vanish (the endpoint values are `0` by `TraceClass`)
  have hslice : ContinuousOn (fun θ : ℝ => G w θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (hsm.curry_θ hw).continuousOn
  have hL0 : ContinuousWithinAt (fun θ : ℝ => G w θ) (Set.Ioi 0) 0 := by
    simpa only [ContinuousWithinAt, h0 w] using htr0 w hw
  have hLpi : ContinuousWithinAt (fun θ : ℝ => G w θ) (Set.Iio (Real.pi / 2))
      (Real.pi / 2) := by
    simpa only [ContinuousWithinAt, hpi w] using htrpi w hw
  -- the two endpoints, now with the closed interval as the ambient set
  have hj0 : ContinuousWithinAt (fun s : ℝ => G w s) (Set.Icc 0 (Real.pi / 2)) 0 := by
    have h1 : ContinuousWithinAt (fun s : ℝ => G w s) (Set.Ici 0) 0 := by
      apply (continuousWithinAt_Ioi_iff_Ici (a := (0 : ℝ)) (f := fun s : ℝ => G w s)).1
      exact hL0
    exact h1.mono (fun x hx => hx.1)
  have hjpi : ContinuousWithinAt (fun s : ℝ => G w s) (Set.Icc 0 (Real.pi / 2))
      (Real.pi / 2) := by
    have h1 : ContinuousWithinAt (fun s : ℝ => G w s) (Set.Iic (Real.pi / 2))
        (Real.pi / 2) := by
      apply (continuousWithinAt_Iio_iff_Iic (a := Real.pi / 2) (f := fun s : ℝ => G w s)).1
      exact hLpi
    exact h1.mono (fun x hx => hx.2)
  intro θ hθ
  rcases lt_trichotomy θ 0 with h | h | h
  · exact absurd hθ.1 (not_le.mpr h)
  · subst h; exact hj0
  · rcases lt_trichotomy θ (Real.pi / 2) with h2 | h2 | h2
    · exact (hslice.continuousAt (isOpen_Ioo.mem_nhds ⟨h, h2⟩)).continuousWithinAt
    · subst h2; exact hjpi
    · exact absurd hθ.2 (not_le.mpr h2)

end Work.FTS.EllSol.EllPkgAux.MollDom
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_deriv2_integrableOn =====
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

set_option maxHeartbeats 800000

theorem slice_deriv2_integrableOn (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    {w : ℝ} (hw : 0 < w) :
    MeasureTheory.IntegrableOn (fun s : ℝ => deriv (deriv (fun s' : ℝ => G w s')) s)
      Work.Spaces.Iθ := by
  obtain ⟨hS, -, -, -, -, -, -, hHon⟩ := hT
  -- the honest hypothesis: the weighted square of the angular second derivative is integrable
  have hgf : MeasureTheory.IntegrableOn
      (fun s : ℝ => (Work.Spaces.pth (Work.Spaces.pth G) w s) ^ 2 * (Work.Spaces.w w) ^ 2
        * Work.FTS.EllipticEst.thEta s) Work.Spaces.Iθ := hHon.1 w hw
  -- the target is the `θ`-slice of `pth (pth G)` at `z = w`
  rw [show (fun s : ℝ => deriv (deriv (fun s' : ℝ => G w s')) s)
      = fun s : ℝ => Work.Spaces.pth (Work.Spaces.pth G) w s from rfl]
  -- `Iθ` carries the same restricted measure as the open interval `(0, π/2)`
  have hIθ : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [Work.Spaces.Iθ]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := Real.pi / 2))).symm
  -- the constant `1` is integrable on the finite-measure interval `Iθ`
  have h1 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const (s := Work.Spaces.Iθ) (C := (1 : ℝ))
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
  have hdom : MeasureTheory.IntegrableOn
      (fun s : ℝ => (Work.Spaces.pth (Work.Spaces.pth G) w s) ^ 2 * (Work.Spaces.w w) ^ 2
        * Work.FTS.EllipticEst.thEta s + 1) Work.Spaces.Iθ := hgf.add h1
  -- a.e. strong measurability: on the open interval the slice is the composition of the
  -- continuous `pth (pth G)` on `Q0` with `s ↦ (w, s)`
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => Work.Spaces.pth (Work.Spaces.pth G) w s)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [hIθ]
    have hcont : ContinuousOn (fun s : ℝ => Work.Spaces.pth (Work.Spaces.pth G) w s)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2)
          Work.FTS.EllipticEst.Q0 := ((hS.pth).pth).continuousOn
      have hg : ContinuousOn (fun s : ℝ => (w, s)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
        fun_prop
      exact h2.comp hg (fun s hs => ⟨hw, hs⟩)
    exact hcont.aestronglyMeasurable measurableSet_Ioo
  -- the pointwise domination
  have hbound : ∀ᵐ s ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖Work.Spaces.pth (Work.Spaces.pth G) w s‖
        ≤ (Work.Spaces.pth (Work.Spaces.pth G) w s) ^ 2 * (Work.Spaces.w w) ^ 2
          * Work.FTS.EllipticEst.thEta s + 1 := by
    rw [hIθ]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with s hs
    have hσ : 1 ≤ Work.FTS.EllipticEst.thEta s := by
      have hsinpos : 0 < Real.sin (2 * s) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hs.1]) (by linarith [hs.2, Real.pi_pos])
      have hsinle : Real.sin (2 * s) ≤ 1 := Real.sin_le_one _
      rw [Work.FTS.EllipticEst.thEta]
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hsinpos hsinle
        (by norm_num [Work.Spaces.eta])
    have hW : 1 ≤ (Work.Spaces.w w) ^ 2 := by
      have h1w : 1 ≤ Work.Spaces.w w := by
        rw [Work.Spaces.w, one_le_div (by positivity : (0 : ℝ) < w ^ 2)]
        nlinarith
      calc (1 : ℝ) = 1 ^ 2 := by norm_num
        _ ≤ (Work.Spaces.w w) ^ 2 := pow_le_pow_left₀ (by norm_num) h1w 2
    have hprod : 1 ≤ (Work.Spaces.w w) ^ 2 * Work.FTS.EllipticEst.thEta s :=
      one_le_mul_of_one_le_of_one_le hW hσ
    have hfsq : (Work.Spaces.pth (Work.Spaces.pth G) w s) ^ 2
        ≤ (Work.Spaces.pth (Work.Spaces.pth G) w s) ^ 2 * (Work.Spaces.w w) ^ 2
          * Work.FTS.EllipticEst.thEta s := by
      calc (Work.Spaces.pth (Work.Spaces.pth G) w s) ^ 2
          = (Work.Spaces.pth (Work.Spaces.pth G) w s) ^ 2 * 1 := (mul_one _).symm
        _ ≤ (Work.Spaces.pth (Work.Spaces.pth G) w s) ^ 2
              * ((Work.Spaces.w w) ^ 2 * Work.FTS.EllipticEst.thEta s) :=
            mul_le_mul_of_nonneg_left hprod (sq_nonneg _)
        _ = (Work.Spaces.pth (Work.Spaces.pth G) w s) ^ 2 * (Work.Spaces.w w) ^ 2
              * Work.FTS.EllipticEst.thEta s := by ring
    have habs : |Work.Spaces.pth (Work.Spaces.pth G) w s|
        ≤ (Work.Spaces.pth (Work.Spaces.pth G) w s) ^ 2 + 1 := by
      nlinarith [sq_nonneg (|Work.Spaces.pth (Work.Spaces.pth G) w s| - 1),
        abs_nonneg (Work.Spaces.pth (Work.Spaces.pth G) w s),
        sq_abs (Work.Spaces.pth (Work.Spaces.pth G) w s)]
    rw [Real.norm_eq_abs]
    linarith [habs, hfsq]
  exact MeasureTheory.Integrable.mono' hdom haesm hbound

end Work.FTS.EllSol.EllPkgAux.MollDom
end
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_deriv2_weighted_integrableOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

theorem slice_deriv2_weighted_integrableOn (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    {w : ℝ} (hw : 0 < w) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (deriv (fun s' : ℝ => G w s')) θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
  obtain ⟨-, -, -, -, -, -, -, hhon⟩ := hT
  -- the angular `∂_θ²`-weight `sin(2θ)^{-η}` carried by the slice at radius `w` is the one
  -- already controlled by `SliceHonestOpen G` (the last conjunct of `TraceClass`), up to the
  -- constant factor `w(w)²` coming from the `z`-weight of `SliceHonestOpen`
  have hc : (0 : ℝ) < (Work.Spaces.w w) ^ 2 := by
    rw [Work.Spaces.w]; positivity
  have h0' := hhon.1 w hw
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
  have hfun : (fun θ : ℝ => (deriv (deriv (fun s' : ℝ => G w s')) θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ)
      = fun θ : ℝ => ((Work.Spaces.w w) ^ 2)⁻¹ *
        (Work.Spaces.pth (Work.Spaces.pth G) w θ ^ 2 * (Work.Spaces.w w) ^ 2
          * Work.FTS.EllipticEst.thEta θ) := by
    funext θ
    rw [hEq θ]
    rfl
  rw [hfun]
  exact h0'.const_mul _

end Work.FTS.EllSol.EllPkgAux.MollDom
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.thSlice_window_aesm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open scoped Real Topology
open MeasureTheory Set Filter

/-- **A.e. strong measurability of the windowed angular second derivative of the trace datum.**

The datum `G` is `C^∞` on the open quadrant (first component of `TraceClass`), so the uncurried
`(z,θ) ↦ (∂_θ²G z θ)²` is continuous there; composing with the continuous map
`p ↦ (exp p.1, p.2)` and observing that the half strip `ℝ × (0,π/2)` has full measure for
`volume.prod (volume.restrict Iθ)` (`aeStronglyMeasurable_exp`) gives the (unwindowed) a.e.
strong measurability.  Multiplying by the indicator of the measurable window
`{p | |log z - p.1| ≤ δ}` (a closed slab in the logarithm of the radius) gives the statement.

No hypothesis on `δ` or on the sign of `z` is needed: the window is a closed (possibly empty)
interval, and its indicator is measurable regardless. -/
theorem thSlice_window_aesm (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (δ z : ℝ) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => if |Real.log z - p.1| ≤ δ then
        (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp p.1) p.2) ^ 2 else 0)
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- the unwindowed angular second derivative is continuous on the open quadrant
  have hcont : ContinuousOn (Function.uncurry
      (fun z θ => (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2))
      Work.FTS.EllipticEst.Q0 :=
    ((hT.1.pth).pth).continuousOn.pow 2
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp p.1) p.2) ^ 2)
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    aeStronglyMeasurable_exp
      (X := fun z θ => (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2) hcont
  -- the window is a measurable set
  have hmeas : Measurable (fun p : ℝ × ℝ => |Real.log z - p.1|) :=
    (continuous_const.sub continuous_fst).abs.measurable
  have hS : MeasurableSet {p : ℝ × ℝ | |Real.log z - p.1| ≤ δ} :=
    measurableSet_Iic.preimage hmeas
  -- the windowed function is the indicator of the window applied to the unwindowed one
  rw [show (fun p : ℝ × ℝ => if |Real.log z - p.1| ≤ δ then
        (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp p.1) p.2) ^ 2 else 0)
      = {p : ℝ × ℝ | |Real.log z - p.1| ≤ δ}.indicator
          (fun p : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp p.1) p.2) ^ 2)
      from by
        funext p
        by_cases hp : |Real.log z - p.1| ≤ δ <;>
          simp [Set.indicator, hp]]
  exact haesm.indicator hS

end Work.FTS.EllSol.EllPkgAux.MollDom
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.window_ttIntS_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The logarithmic window `|log z - t| ≤ δ`

The `z`-integration of the project is carried out on `Iz = [0,∞)` with the weight `w(z)²`, and
the logarithmic (mollification) estimates are stated in the variable `t = log z`, where the
weight window becomes `|log z - t| ≤ δ`, i.e. `t ∈ [log z - δ, log z + δ]`.

This file proves the integrability of the two `ttIntS`-type windowed quantities.  The key point
is that the window is a *compact* interval in `t`, so on it the factor `exp t` (the Jacobian of
`z = exp t`) is comparable to `z`, and the two `z`-integrals that occur (`w(z)²·∫_θ (∂_θ²G)²σθ`
and the *unweighted* angular integral) are equivalent to each other up to a bounded factor. -/

/-- The radial weight `w` is positive on the positive half-line. -/
private lemma w_pos {u : ℝ} (hu : 0 < u) : 0 < Work.Spaces.w u := by
  have h1 : (0 : ℝ) < (1 + u) ^ 2 := by positivity
  have h2 : (0 : ℝ) < u ^ 2 := by positivity
  have h : Work.Spaces.w u = (1 + u) ^ 2 / u ^ 2 := rfl
  rw [h]
  exact div_pos h1 h2

/-- The radial weight along the substitution `z = exp t` is continuous. -/
private lemma continuous_w_exp : Continuous (fun t : ℝ => Work.Spaces.w (Real.exp t)) := by
  have h : (fun t : ℝ => Work.Spaces.w (Real.exp t))
      = fun t : ℝ => (1 + Real.exp t) ^ 2 / (Real.exp t) ^ 2 := by
    funext t
    rfl
  rw [h]
  exact ((continuous_const.add Real.continuous_exp).pow 2).div (Real.continuous_exp.pow 2)
    (fun t => pow_ne_zero 2 (Real.exp_ne_zero t))

/-- The logarithmic window is the interval `[log z - δ, log z + δ]`. -/
private lemma window_eq_Icc {δ z : ℝ} :
    {t : ℝ | |Real.log z - t| ≤ δ} = Set.Icc (Real.log z - δ) (Real.log z + δ) := by
  ext t
  rw [Set.mem_ofPred_eq, abs_le, Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- On the window, the weight `w²` is bounded below: for `0 < u ≤ v`,
`(w u ^ 2)⁻¹ ≤ v ^ 4`. -/
private lemma w_sq_inv_le_pow_four (u v : ℝ) (hu : 0 < u) (huv : u ≤ v) :
    ((Work.Spaces.w u) ^ 2)⁻¹ ≤ v ^ 4 := by
  have hw : (Work.Spaces.w u) ^ 2 = (1 + u) ^ 4 / u ^ 4 := by
    have h : Work.Spaces.w u = (1 + u) ^ 2 / u ^ 2 := rfl
    rw [h, div_pow]
    ring
  rw [hw, inv_div]
  calc u ^ 4 / (1 + u) ^ 4 ≤ u ^ 4 :=
        div_le_self (le_of_lt (pow_pos hu 4)) (one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + u))
    _ ≤ v ^ 4 := pow_le_pow_left₀ hu.le huv 4

/-- The `θ`-part of `ttIntS`, recovered from `ttIntS` by dividing out the weight `w²`. -/
private lemma inv_w_sq_mul_ttIntS (G : ℝ → ℝ → ℝ) (u : ℝ) (hu : 0 < u) :
    ((Work.Spaces.w u) ^ 2)⁻¹ * Work.EllipticEst.Core.ttIntS G u
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.pth G) u θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ := by
  have h : Work.EllipticEst.Core.ttIntS G u
      = (Work.Spaces.w u) ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.Spaces.pth G) u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := rfl
  rw [h, inv_mul_cancel_left₀ (pow_ne_zero 2 (ne_of_gt (w_pos hu)))]

/-- The windowed `exp`-pullback of a datum integrable on `Iz = [0,∞)` is integrable: the window
is compact, and `t ↦ F (exp t)` is integrable on every compact interval. -/
private lemma window_comp_integrable (F : ℝ → ℝ)
    (hF : MeasureTheory.IntegrableOn F Work.Spaces.Iz) (δ z : ℝ) :
    MeasureTheory.Integrable (fun t : ℝ => if |Real.log z - t| ≤ δ then F (Real.exp t) else 0) := by
  have hFcd : ∀ a b : ℝ, 0 < a → a ≤ b → MeasureTheory.IntegrableOn F (Set.Icc a b) :=
    fun a b ha _ => hF.mono_set (fun x hx => le_of_lt (lt_of_lt_of_le ha hx.1))
  have hII : MeasureTheory.IntegrableOn (fun t : ℝ => F (Real.exp t))
      (Set.Icc (Real.log z - δ) (Real.log z + δ)) :=
    integrableOn_exp_comp hFcd (Real.log z - δ) (Real.log z + δ)
  have hfun : (fun t : ℝ => if |Real.log z - t| ≤ δ then F (Real.exp t) else 0)
      = Set.indicator {t : ℝ | |Real.log z - t| ≤ δ} (fun t : ℝ => F (Real.exp t)) := by
    funext t
    by_cases h : |Real.log z - t| ≤ δ
    · rw [if_pos h, Set.indicator_of_mem (show t ∈ {u : ℝ | |Real.log z - u| ≤ δ} from h)]
    · rw [if_neg h, Set.indicator_of_notMem (show t ∉ {u : ℝ | |Real.log z - u| ≤ δ} from h)]
  rw [hfun, window_eq_Icc]
  exact hII.integrable_indicator measurableSet_Icc

theorem window_ttIntS_integrable (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) (δ z : ℝ) (hδ : 0 < δ) (hz : 0 < z) :
    MeasureTheory.Integrable (fun t : ℝ =>
        if |Real.log z - t| ≤ δ then Work.EllipticEst.Core.ttIntS G (Real.exp t) else 0) ∧
      MeasureTheory.Integrable (fun t : ℝ =>
        if |Real.log z - t| ≤ δ then
          (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ) else 0) := by
  have hTt : MeasureTheory.IntegrableOn (Work.EllipticEst.Core.ttIntS G) Work.Spaces.Iz := hF.2.2.1
  have hf₁ : MeasureTheory.Integrable (fun t : ℝ =>
      if |Real.log z - t| ≤ δ then Work.EllipticEst.Core.ttIntS G (Real.exp t) else 0) :=
    window_comp_integrable (Work.EllipticEst.Core.ttIntS G) hTt δ z
  refine ⟨hf₁, ?_⟩
  -- the target function factors as a bounded weight times the already integrable one
  have hpt : ∀ t : ℝ,
      (if |Real.log z - t| ≤ δ then
          (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ) else 0)
        = (if |Real.log z - t| ≤ δ then ((Work.Spaces.w (Real.exp t)) ^ 2)⁻¹ else 0)
          * (if |Real.log z - t| ≤ δ then Work.EllipticEst.Core.ttIntS G (Real.exp t) else 0) := by
    intro t
    by_cases h : |Real.log z - t| ≤ δ
    · rw [if_pos h, if_pos h, if_pos h, inv_w_sq_mul_ttIntS G (Real.exp t) (Real.exp_pos t)]
    · rw [if_neg h, if_neg h, if_neg h, mul_zero]
  refine MeasureTheory.Integrable.mono' (hf₁.norm.const_mul ((z * Real.exp δ) ^ 4)) ?_ ?_
  · have hmeasA : MeasureTheory.AEStronglyMeasurable
        (fun t : ℝ => if |Real.log z - t| ≤ δ then ((Work.Spaces.w (Real.exp t)) ^ 2)⁻¹ else 0)
        MeasureTheory.volume := by
      have hset : MeasurableSet {t : ℝ | |Real.log z - t| ≤ δ} :=
        measurableSet_le (continuous_abs.comp
          (continuous_const.sub continuous_id : Continuous fun t : ℝ => Real.log z - t)).measurable
          measurable_const
      have hcont : Measurable (fun t : ℝ => ((Work.Spaces.w (Real.exp t)) ^ 2)⁻¹) :=
        (continuous_w_exp.pow 2).measurable.inv
      exact (Measurable.ite hset hcont measurable_const).aestronglyMeasurable
    exact MeasureTheory.AEStronglyMeasurable.congr
      (hmeasA.mul hf₁.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => (hpt t).symm)
  · filter_upwards with t
    rw [hpt t, Real.norm_eq_abs, abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    by_cases h : |Real.log z - t| ≤ δ
    · rw [if_pos h, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
      have ht : Real.exp t ≤ z * Real.exp δ := by
        calc Real.exp t ≤ Real.exp (Real.log z + δ) :=
              Real.exp_le_exp.mpr (by linarith [(abs_le.mp h).1])
          _ = z * Real.exp δ := by rw [Real.exp_add, Real.exp_log hz]
      exact w_sq_inv_le_pow_four (Real.exp t) (z * Real.exp δ) (Real.exp_pos t) ht
    · rw [if_neg h, abs_zero]
      positivity

end Work.FTS.EllSol.EllPkgAux.MollDom
end
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux =====
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

/-- The diagonal sequence of mollification parameters, `tₙ = 1/(n+2) ∈ (0, 1/2]`. -/
def tseq (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

theorem tseq_pos (n : ℕ) : 0 < tseq n := by
  simp only [tseq]
  positivity

theorem tseq_le_half (n : ℕ) : tseq n ≤ 1 / 2 := by
  rw [tseq, ← sub_nonpos]
  have hkey : (1:ℝ) / ((n:ℝ) + 2) - 1/2 = (2 - ((n:ℝ) + 2)) / (2*((n:ℝ)+2)) := by
    field_simp
  rw [hkey]
  have hn : (0:ℝ) ≤ (n:ℝ) := by positivity
  have h2 : (2:ℝ) - ((n:ℝ)+2) ≤ 0 := by linarith
  have h1 : (0:ℝ) ≤ 2*((n:ℝ)+2) := by linarith
  exact div_nonpos_of_nonpos_of_nonneg h2 h1

theorem tendsto_tseq : Tendsto tseq atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have h : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ht
  change Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0)
  simpa only [one_div] using h

theorem params_tseq (n : ℕ) : Params (tseq n) (tseq n) :=
  ⟨tseq_pos n, tseq_le_half n, tseq_pos n, tseq_le_half n⟩

/-- The derivative of the mollifying kernel. -/
def sKerd (ε : ℝ) : ℝ → ℝ := deriv (Work.FTS.EllSol.PkgK5.K5c.sKer ε)

/-- The (uncurried, logarithmic-variable) integrand of the double mollification. -/
def Hxyc (G : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t s => Work.FTS.EllSol.PkgK5.K5c.Qext G (Real.exp t) s

/-- The unweighted angular slice energy `∫_{Iθ} (∂_θ²G(w,·))² σ_η`. -/
def E2s (G : ℝ → ℝ → ℝ) (w : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.pth G) w θ) ^ 2
    * Work.FTS.EllipticEst.thEta θ

/-- **The dominating function of the angular slice of `G`.**  It is built from the interior
values of `G` and `∂_θG` at `θ = π/4` (continuous, hence locally bounded, in `w`) and from the
square root of the slice energy (locally integrable in `w` by the `ttIntS` integrability
hypothesis). -/
def MGf (G : ℝ → ℝ → ℝ) (w : ℝ) : ℝ :=
  1 + |G w (Real.pi / 4)| + |Work.Spaces.pth G w (Real.pi / 4)| + Real.sqrt (E2s G w)

/-- `sKer` is smooth. -/
theorem contDiff_sKer (ε : ℝ) {n : ℕ∞} : ContDiff ℝ n (Work.FTS.EllSol.PkgK5.K5c.sKer ε) := by
  have hfun : Work.FTS.EllSol.PkgK5.K5c.sKer ε
      = fun t : ℝ => (ε * Work.FTS.EllSol.PkgK5.K5c.sMass)⁻¹
          * Real.smoothTransition (1 - t ^ 2 / ε ^ 2) := by
    funext t
    simp only [Work.FTS.EllSol.PkgK5.K5c.sKer, Work.FTS.EllSol.PkgK5.K5c.sBump]
    rw [show t / ε = ε⁻¹ * t by rw [div_eq_inv_mul]]
    rw [show 1 - (ε⁻¹ * t) ^ 2 = 1 - t ^ 2 / ε ^ 2 by field_simp]
  rw [hfun]
  fun_prop

end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Alpha4.cut_integration =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Alpha4

set_option autoImplicit false


end Work.FTS.EllipticEst.Alpha4
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Alpha4.ibp_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllipticEst
open Work.Spaces

namespace Work.FTS.EllipticEst.Alpha4

set_option maxHeartbeats 2000000

/-! ## The two test functions of the integration by parts -/



/-! ## The angular and radial pieces of the dominating functions -/














/-! ## Elementary numerical and linearity lemmas -/










/-! ## The three bounds -/


end Work.FTS.EllipticEst.Alpha4
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.AeEnergyMain =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
noncomputable section
open scoped Real Topology BigOperators ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak.AeMain
set_option autoImplicit false
set_option linter.unusedVariables false

theorem restrict_Iz_eq_Ioi' : MeasureTheory.volume.restrict Work.Spaces.Iz
    = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
  rw [Work.Spaces.Iz]
  exact MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm

theorem cut_mono (n : ℕ) (z : ℝ) :
    Work.FTS.EllipticEst.cut n z ≤ Work.FTS.EllipticEst.cut (n + 1) z := by
  rcases le_or_gt 0 z with hz | hz
  · have h1 : ((n:ℝ)+1) * z - 1 ≤ ((n:ℝ)+1+1) * z - 1 := by nlinarith
    have h2 : z / ((n:ℝ)+1+1) - 2 ≤ z / ((n:ℝ)+1) - 2 := by
      have h2' : (0:ℝ) < (n:ℝ)+1 := by linarith
      have h4 : z / ((n:ℝ)+1+1) ≤ z / ((n:ℝ)+1) :=
        div_le_div_of_nonneg_left hz h2' (by linarith)
      linarith
    have ha : Real.smoothTransition (((n:ℝ)+1) * z - 1)
        ≤ Real.smoothTransition (((n:ℝ)+1+1) * z - 1) := Real.smoothTransition.monotone h1
    have hb : (1 - Real.smoothTransition (z / ((n:ℝ)+1) - 2)) ≤
        (1 - Real.smoothTransition (z / ((n:ℝ)+1+1) - 2)) := by
      have := Real.smoothTransition.monotone h2
      linarith
    have hb0 : (0:ℝ) ≤ 1 - Real.smoothTransition (z / ((n:ℝ)+1) - 2) :=
      sub_nonneg.mpr (Real.smoothTransition.le_one _)
    have ha0 : (0:ℝ) ≤ Real.smoothTransition (((n:ℝ)+1) * z - 1) :=
      Real.smoothTransition.nonneg _
    simp only [Work.FTS.EllipticEst.cut]
    push_cast
    exact mul_le_mul ha hb hb0 (le_trans ha0 ha)
  · have h1 : ((n:ℝ)+1) * z - 1 < 0 := by
      have : (0:ℝ) < (n:ℝ)+1 := by positivity
      nlinarith
    have hzero : Real.smoothTransition (((n:ℝ)+1) * z - 1) = 0 :=
      Real.smoothTransition.zero_of_nonpos h1.le
    have hnc : Work.FTS.EllipticEst.cut n z = 0 := by
      simp only [Work.FTS.EllipticEst.cut]
      push_cast
      rw [hzero, zero_mul]
    rw [hnc]
    exact Work.FTS.EllipticEst.cut_nonneg _ _


/-- **The sup over the cut-off family**: for a nonnegative a.e.-measurable `g` on `Iz`,
`⨆_n ∫⁻_z ofReal (cut n z) * g z = ∫⁻_z g z`. -/
theorem iSup_cut_mul {g : ℝ → ℝ≥0∞}
    (hg : AEMeasurable g (MeasureTheory.volume.restrict Work.Spaces.Iz)) :
    (⨆ n : ℕ, ∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (Work.FTS.EllipticEst.cut n z) * g z)
      = ∫⁻ z in Work.Spaces.Iz, g z := by
  have hmeas : ∀ n : ℕ, AEMeasurable
      (fun z => ENNReal.ofReal (Work.FTS.EllipticEst.cut n z) * g z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    intro n
    exact ((ENNReal.measurable_ofReal.comp
      ((Work.FTS.EllipticEst.cut_contDiff n).continuous.measurable)).aemeasurable).mul hg
  have hmono : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      Monotone (fun n : ℕ => ENNReal.ofReal (Work.FTS.EllipticEst.cut n z) * g z) := by
    refine Filter.Eventually.of_forall fun z m n hmn => ?_
    refine mul_le_mul_of_nonneg_right ?_ (bot_le : (⊥ : ℝ≥0∞) ≤ g z)
    refine ENNReal.ofReal_le_ofReal ?_
    exact Nat.le_induction le_rfl (fun k _ hk => le_trans hk (cut_mono k z)) n hmn
  have hlim : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (Work.FTS.EllipticEst.cut n z) * g z)
        Filter.atTop (nhds (g z)) := by
    rw [restrict_Iz_eq_Ioi']
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun z hz => ?_)
    -- `cut n z = 1` for all large `n`
    have hN : ∃ N : ℕ, ∀ n ≥ N, Work.FTS.EllipticEst.cut n z = 1 := by
      refine ⟨Nat.ceil (2 / z) + Nat.ceil z, fun n hn => ?_⟩
      have hnc : (Nat.ceil (2 / z) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast le_trans (Nat.le_add_right _ _) hn
      have hzc : (Nat.ceil z : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast le_trans (Nat.le_add_left _ _) hn
      have h2z : 2 / z ≤ (n : ℝ) := le_trans (Nat.le_ceil _) hnc
      have hz2 : z ≤ (n : ℝ) := le_trans (Nat.le_ceil _) hzc
      have h2n : 2 ≤ (n : ℝ) * z := by rw [div_le_iff₀ hz] at h2z; linarith
      refine Work.FTS.EllipticEst.cut_eq_one_of_mem n ?_ ?_
      · rw [div_le_iff₀ (by positivity : (0:ℝ) < (n:ℝ)+1)]; nlinarith
      · nlinarith
    obtain ⟨N, hN⟩ := hN
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_atTop.mpr ⟨N, hN⟩] with n hn
    simp [hn]
  have htend := MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone hmeas hmono hlim
  have hmonoL : Monotone (fun n : ℕ => ∫⁻ z in Work.Spaces.Iz,
      ENNReal.ofReal (Work.FTS.EllipticEst.cut n z) * g z) := by
    intro m n hmn
    refine lintegral_mono fun z => ?_
    refine mul_le_mul_of_nonneg_right ?_ (bot_le : (⊥ : ℝ≥0∞) ≤ g z)
    refine ENNReal.ofReal_le_ofReal ?_
    exact Nat.le_induction le_rfl (fun k _ hk => le_trans hk (cut_mono k z)) n hmn
  exact iSup_eq_of_tendsto hmonoL htend

end Work.FTS.EllipticEst.AngAWeak.AeMain

namespace Work.FTS.EllipticEst.AngAWeak.AeMain
set_option autoImplicit false
set_option linter.unusedVariables false


theorem cut_hasCompactSupport (n : ℕ) : HasCompactSupport (Work.FTS.EllipticEst.cut n) := by
  have hsub : Function.support (Work.FTS.EllipticEst.cut n) ⊆
      Set.Icc (1 / ((n + 1 : ℕ) : ℝ)) (3 * ((n + 1 : ℕ) : ℝ)) := by
    intro z hz
    simp only [Function.mem_support] at hz
    by_contra hc
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hc
    rcases hc with hc | hc
    · refine hz (Work.FTS.EllipticEst.cut_apply_zero_of_le n ?_)
      push_cast at hc ⊢
      exact le_of_lt hc
    · refine hz (Work.FTS.EllipticEst.cut_apply_zero_of_ge n ?_)
      push_cast at hc ⊢
      exact le_of_lt hc
  have hts : tsupport (Work.FTS.EllipticEst.cut n) ⊆
      Set.Icc (1 / ((n + 1 : ℕ) : ℝ)) (3 * ((n + 1 : ℕ) : ℝ)) :=
    closure_minimal hsub isClosed_Icc
  exact IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hts

theorem cut_contDiff_two (n : ℕ) : ContDiff ℝ 2 (Work.FTS.EllipticEst.cut n) :=
  (Work.FTS.EllipticEst.cut_contDiff n).of_le (by
    rw [Work.Stability.smoothOrder]
    exact WithTop.coe_le_coe.mpr le_top)

theorem cut_zero_of_nonpos (n : ℕ) {z : ℝ} (hz : z ≤ 0) : Work.FTS.EllipticEst.cut n z = 0 :=
  Work.FTS.EllipticEst.cut_apply_zero_of_le n (le_trans hz (by positivity))

end Work.FTS.EllipticEst.AngAWeak.AeMain

namespace Work.FTS.EllipticEst.AngAWeak.AeMain
set_option autoImplicit false
set_option linter.unusedVariables false

theorem w_sq_measurable' : Measurable (fun z : ℝ => (Work.Spaces.w z) ^ 2) := by
  have h : Work.Spaces.w = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := rfl
  rw [h]
  exact (Measurable.div ((measurable_const.add measurable_id).pow_const 2)
    (measurable_id.pow_const 2)).pow_const 2

/-- The measurability of the two target integrands. -/
theorem gA_aemeasurable {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    AEMeasurable (fun z : ℝ => ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((z * Work.Spaces.pz u z θ) ^ 2)))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hSO : Work.FTS.EllipticEst.SmoothOpen u := Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hpz : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (Work.FTS.EllipticEst.SmoothOpen.pz hSO).continuousOn
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (continuousOn_fst.mul hpz).pow 2
  have h1 : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal ((p.1 * Work.Spaces.pz u p.1 p.2) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).aemeasurable.ennreal_ofReal
  have h2 := h1.lintegral_prod_right'
  have hw : AEMeasurable (fun z : ℝ => ENNReal.ofReal ((Work.Spaces.w z) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (w_sq_measurable').aemeasurable.ennreal_ofReal
  exact hw.mul h2

theorem gB_aemeasurable {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    AEMeasurable (fun z : ℝ => ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hSO : Work.FTS.EllipticEst.SmoothOpen u := Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hpth : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (Work.FTS.EllipticEst.SmoothOpen.pth hSO).continuousOn
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.pth u p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hpth.pow 2
  have h1 : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal ((Work.Spaces.pth u p.1 p.2) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).aemeasurable.ennreal_ofReal
  have h2 := h1.lintegral_prod_right'
  have hw : AEMeasurable (fun z : ℝ => ENNReal.ofReal ((Work.Spaces.w z) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (w_sq_measurable').aemeasurable.ennreal_ofReal
  exact hw.mul h2

end Work.FTS.EllipticEst.AngAWeak.AeMain

namespace Work.FTS.EllipticEst.AngAWeak.AeMain
set_option autoImplicit false
set_option linter.unusedVariables false

/-- `sEta` is nonnegative on `Iθ`. -/
theorem sEta_nonneg' {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  refine Real.rpow_nonneg ?_ _
  refine Real.sin_nonneg_of_mem_Icc ⟨?_, ?_⟩ <;> linarith [hθ.1, hθ.2, Real.pi_pos]

end Work.FTS.EllipticEst.AngAWeak.AeMain

namespace Work.FTS.EllipticEst.AngAWeak.AeMain
set_option autoImplicit false
set_option linter.unusedVariables false

/-- `P z = ∫_θ (u z θ)^2` is a.e.-strongly measurable. -/
theorem P_aesm {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    MeasureTheory.AEStronglyMeasurable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hSO : Work.FTS.EllipticEst.SmoothOpen u := Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (u p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((hSO.continuousOn).comp (by fun_prop) (fun p hp => hp)).pow 2
  exact (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'

end Work.FTS.EllipticEst.AngAWeak.AeMain

namespace Work.FTS.EllipticEst.AngAWeak.AeMain
set_option autoImplicit false
set_option linter.unusedVariables false

/-- `ofReal (∫ f) ≤ ∫⁻ ofReal f` for a nonnegative a.e.-strongly-measurable `f` on `Iθ`. -/
theorem ofReal_integral_le_lintegral {f : ℝ → ℝ}
    (hae : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (h0 : ∀ θ, 0 ≤ f θ) :
    ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, f θ)
      ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (f θ) := by
  rcases eq_or_ne (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (f θ)) ⊤ with h | h
  · rw [h]; exact le_top
  · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      ((MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hae
        (Filter.Eventually.of_forall h0)).mp h)
      (Filter.Eventually.of_forall h0)]

/-- **The final step**: a monotone family of truncated inequalities with a vanishing error
gives the limiting inequality. -/
theorem final_step {a : ℝ} {A B : ℝ≥0∞} {An Bn : ℕ → ℝ≥0∞} {R : ℝ≥0∞} {e : ℕ → ℝ}
    (hAmono : Monotone An) (hBmono : Monotone Bn)
    (hA : (⨆ n, An n) = A) (hB : (⨆ n, Bn n) = B)
    (hineq : ∀ n, ENNReal.ofReal a * An n + Bn n ≤ R + ENNReal.ofReal (e n))
    (herr : Filter.Tendsto e Filter.atTop (nhds 0)) (he0 : ∀ n, 0 ≤ e n) :
    ENNReal.ofReal a * A + B ≤ R := by
  have hadd : ∀ (c : ℝ≥0∞) (g : ℕ → ℝ≥0∞), c + (⨆ i, g i) = ⨆ i, (c + g i) := by
    intro c g
    rw [add_comm, ENNReal.iSup_add]
    exact iSup_congr fun i => add_comm _ _
  have hsup : (⨆ n, (ENNReal.ofReal a * An n + Bn n)) = ENNReal.ofReal a * A + B := by
    rw [← hA, ← hB]
    refine le_antisymm ?_ ?_
    · refine iSup_le fun n => ?_
      exact add_le_add (mul_le_mul_of_nonneg_left (le_iSup (f := An) n) (by positivity)) (le_iSup (f := Bn) n)
    · have h1 : ENNReal.ofReal a * (⨆ n, An n) + (⨆ n, Bn n)
          = ⨆ m, ⨆ n, (ENNReal.ofReal a * An m + Bn n) := by
        rw [ENNReal.mul_iSup]
        rw [ENNReal.iSup_add]
        exact iSup_congr fun m => hadd (ENNReal.ofReal a * An m) Bn
      rw [h1]
      refine iSup_le fun m => iSup_le fun n => ?_
      refine le_trans (add_le_add (mul_le_mul_of_nonneg_left (hAmono (le_max_left m n))
        (by positivity)) (hBmono (le_max_right m n))) ?_
      exact le_iSup (f := fun k => ENNReal.ofReal a * An k + Bn k) (max m n)
  have htend : Filter.Tendsto (fun n => ENNReal.ofReal a * An n + Bn n) Filter.atTop
      (nhds (ENNReal.ofReal a * A + B)) := by
    rw [← hsup]
    exact tendsto_atTop_iSup (fun m n hmn => add_le_add
      (mul_le_mul_of_nonneg_left (hAmono hmn) (by positivity)) (hBmono hmn))
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hRlt => ?_
  have hεpos : (0:ℝ) < (ε:ℝ) := by exact_mod_cast hε
  refine le_of_tendsto htend ?_
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 herr) (ε:ℝ) hεpos
  refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
  refine le_trans (hineq n) (add_le_add le_rfl ?_)
  have h1 : dist (e n) 0 < (ε:ℝ) := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (he0 n)] at h1
  rw [ENNReal.coe_nnreal_eq]
  exact ENNReal.ofReal_le_ofReal (by linarith [h1])

end Work.FTS.EllipticEst.AngAWeak.AeMain

namespace Work.FTS.EllipticEst.AngAWeak.AeMain
set_option autoImplicit false
set_option linter.unusedVariables false


end Work.FTS.EllipticEst.AngAWeak.AeMain
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.aeUMassBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The slicewise mass bound `aeUMassBound` of the weak angular class

For a datum `(u, G)` of the almost-everywhere class `AeData α u G` (the weak class of the
level-`0` elliptic estimate, `H2W/Ae/Defs.lean`), the values of the solution `u` on a compact
radial interval `[a,b] ⊂ (0,∞)` are bounded by the *angular* `H²`-mass of the slice

  `AAA u z = ∫_θ (∂_θθ u(z,θ))² sin(2θ)^{-η} dθ`

of the same slice, up to a constant `K` (allowed to depend on `α`, `u`, `G`, `a`, `b`, but
not on `z ∈ [a,b]` or `θ ∈ Iθ`).

## Route

For a fixed `z ∈ [a,b]` the slice `θ ↦ u(z,·)` is `C^∞` on `(0,π/2)` and its second derivative
is square integrable against `σ = sin(2θ)^{-η}` (`HkMem α 0 (∂_θθu)` is a hypothesis of
`AeData`, and `HkIntegrand α 0 (∂_θθu) = w(z)² (∂_θθu)² σ` on `Iθ`).  Hence

* `∫_{Iθ} |∂_θθ u(z,·)| ≤ √(AAA u z) · √(∫_{Iθ} sin(2θ)^η)` (weighted Cauchy–Schwarz,
  `sliceCSWeightedOpen`);
* the fundamental theorem of calculus based at the interior point `π/4` bounds `u` and
  `∂_θ u` on the slice by their values at `π/4` plus that mass
  (`Endpt.psi_le_of_strip_HkMem`).

The values at `π/4` are bounded *uniformly in `z ∈ [a,b]`* because `z ↦ u(z,π/4)` and
`z ↦ ∂_θu(z,π/4)` are continuous on the compact interval `[a,b]` (joint `C^∞`-regularity of
`u` on the open quadrant); this is where the compactness of `[a,b]` and the positivity of `a`
enter, and it is the only place where the constant is not explicit.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option maxHeartbeats 1000000

/-- `σ θ = sEta θ = sin(2θ)^{-η} ≥ 0` on `Iθ`. -/
private lemma sEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ :=
  Real.rpow_nonneg (Work.FTS.EllipticEst.sin_two_nonneg hθ) _


end Work.FTS.EllipticEst.AngAWeak
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.FstarSin_mem =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## Integrability of the angular profiles `angZ` and `angA` -/









/-! ## The `θ`-integral of the separated integrand `HkExp` -/


/-! ## The crude bound on a slice -/




/-! ## Integrability of a slice, from continuity and boundedness -/


/-! ## The explicit measurable function `Psi_prv` -/

/-- The a.e. value of the slice integral `z ↦ ∫_θ HkIntegrand α k (F_*·sin 2θ) z θ`: the
angular integrals are evaluated and the radial factors are the moments
`Bmom F i z = F_*(D_z^i F)(z)`. -/
private def Psi_prv (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  (∫ θ in Work.Spaces.Iθ, angZ θ)
      * (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F i z) ^ 2)
    + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.w z) ^ 2 * (Work.FTS.EllipticEst.Bmom F j z) ^ 2 else 0)
          * (∫ θ in Work.Spaces.Iθ, angA α i θ)





/-! ## The a.e. identity `radIter (B_0) j = B_j` -/


/-! ## The a.e. evaluation of the slice integral -/


/-! ## The membership certificate -/


end Work.FTS.EllipticEst.Cert
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cert.Fstar_div_integrable_of_EllHyp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}

/-! ## 1. Elementary angular facts -/

theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])


theorem sinCos2_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Elliptic.sinCos2 θ := by
  rw [Work.Elliptic.sinCos2]
  exact mul_nonneg
    (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])) (sq_nonneg _)

theorem sinCos2_le_one (θ : ℝ) : Work.Elliptic.sinCos2 θ ≤ 1 := by
  rw [Work.Elliptic.sinCos2]
  have hc : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [Real.abs_cos_le_one θ, sq_abs (Real.cos θ), abs_nonneg (Real.cos θ)]
  have h1 : Real.sin θ * Real.cos θ ^ 2 ≤ 1 * Real.cos θ ^ 2 :=
    mul_le_mul_of_nonneg_right (Real.sin_le_one θ) (sq_nonneg _)
  have h2 : (1 : ℝ) * Real.cos θ ^ 2 ≤ 1 * 1 :=
    mul_le_mul_of_nonneg_left hc zero_le_one
  linarith


/-! ## 2. The weighted Young inequality -/

/-- **Weighted Young inequality.**  For `r > 0`, `0 ≤ σ ≤ 1`, `0 < T ≤ 1` and `x : ℝ`,

  `|x|·σ/r ≤ (x·(w(r)/T^{η/2}))² + ((r·w(r))⁻¹)²`.

It is Young's inequality `2uv ≤ u² + v²` applied to `u = |x|·w(r)/T^{η/2}` and
`v = σ/(r·w(r)/T^{η/2})`; the small factors `σ² ≤ 1` and `T^η ≤ 1` turn the second square into
`((r·w(r))⁻¹)²`. -/
theorem young_weighted (x r T σ : ℝ) (hr : 0 < r) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hT0 : 0 < T) (hT1 : T ≤ 1) :
    |x| * σ / r ≤ (x * (Work.Spaces.w r / T ^ (Work.Spaces.eta / 2))) ^ 2
      + ((r * Work.Spaces.w r)⁻¹) ^ 2 := by
  have hw : 0 < Work.Spaces.w r := by
    rw [Work.Spaces.w]; positivity
  have hTp : 0 < T ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hT0 _
  set A : ℝ := Work.Spaces.w r / T ^ (Work.Spaces.eta / 2) with hA
  have hAp : 0 < A := div_pos hw hTp
  set u : ℝ := |x| * A with hu
  set v : ℝ := σ / (r * A) with hv
  have hu0 : 0 ≤ u := mul_nonneg (abs_nonneg _) hAp.le
  have hv0 : 0 ≤ v := div_nonneg hσ (mul_pos hr hAp).le
  have huv : u * v = |x| * σ / r := by
    rw [hu, hv]; field_simp
  have hu2 : u ^ 2 = (x * A) ^ 2 := by rw [hu, mul_pow, sq_abs, mul_pow]
  have hv_le : v ≤ (r * Work.Spaces.w r)⁻¹ := by
    have hstep : v = σ * T ^ (Work.Spaces.eta / 2) / (r * Work.Spaces.w r) := by
      rw [hv, hA, ← mul_div_assoc, div_div_eq_mul_div]
    rw [hstep, inv_eq_one_div]
    refine div_le_div_of_nonneg_right ?_ (mul_pos hr hw).le
    have hTle : T ^ (Work.Spaces.eta / 2) ≤ 1 :=
      Real.rpow_le_one hT0.le hT1
        (by norm_num [Work.Spaces.eta] : (0 : ℝ) ≤ Work.Spaces.eta / 2)
    calc σ * T ^ (Work.Spaces.eta / 2) ≤ 1 * 1 :=
          mul_le_mul hσ1 hTle hTp.le zero_le_one
      _ = 1 := by ring
  have hv2 : v ^ 2 ≤ ((r * Work.Spaces.w r)⁻¹) ^ 2 := by
    have hc : 0 ≤ (r * Work.Spaces.w r)⁻¹ := inv_nonneg.mpr (mul_pos hr hw).le
    calc v ^ 2 = v * v := by ring
      _ ≤ (r * Work.Spaces.w r)⁻¹ * v := mul_le_mul hv_le (le_refl v) hv0 hc
      _ ≤ (r * Work.Spaces.w r)⁻¹ * (r * Work.Spaces.w r)⁻¹ :=
          mul_le_mul (le_refl _) hv_le hv0 hc
      _ = ((r * Work.Spaces.w r)⁻¹) ^ 2 := by ring
  have hamgm : u * v ≤ (u ^ 2 + v ^ 2) / 2 := by nlinarith [sq_nonneg (u - v)]
  have hmid : u ^ 2 + v ^ 2 ≤ 2 * (x * A) ^ 2 + 2 * ((r * Work.Spaces.w r)⁻¹) ^ 2 := by
    nlinarith [hu2, hv2]
  have hfin : |x| * σ / r ≤ (x * A) ^ 2 + ((r * Work.Spaces.w r)⁻¹) ^ 2 := by
    nlinarith [huv.le, hamgm, hmid]
  rw [hA] at hfin
  exact hfin

/-! ## 3. Measurability of the angular moment -/

theorem Iθ_ae_eq_Ioo : (Work.Spaces.Iθ : Set ℝ) =ᵐ[volume] Set.Ioo 0 (π / 2) :=
  MeasureTheory.Ioo_ae_eq_Icc.symm

theorem prod_restrict_eq :
    ((volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ) : Measure (ℝ × ℝ))
      = (volume : Measure (ℝ × ℝ)).restrict Work.FTS.EllipticEst.Q0 := by
  have hv : (volume : Measure (ℝ × ℝ)) = volume.prod volume := Measure.volume_eq_prod ℝ ℝ
  rw [Measure.prod_restrict, hv]
  exact Measure.restrict_congr_set
    (MeasureTheory.Measure.set_prod_ae_eq Filter.EventuallyEq.rfl Iθ_ae_eq_Ioo)



/-! ## 4. The pointwise bound in `ℝ≥0∞` -/


/-! ## 5. The main estimate -/


end Work.FTS.EllipticEst.Cert
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.AeWAux.sharpHardyCosOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.AeWAux

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

/-! ## A pointwise comparison of the weights

For `0 < u ≤ π/2` and `0 ≤ η`, `sin u ≤ u` together with `η ≥ 0` gives `u^{-(2+η)} ≤ sin(u)^{-(2+η)}`,
and since `cos²u + sin²u = 1` the latter equals `cos²u·sin(u)^{-(2+η)} + sin(u)^{-η}`.  So the
power weight is dominated by the `cos²`-weighted singular weight plus the `η`-weight. -/



/-- `sin (2 (π/2 - x)) = sin (2x)`. -/
private lemma sin_two_pi_half_sub (x : ℝ) :
    Real.sin (2 * (Real.pi / 2 - x)) = Real.sin (2 * x) := by
  rw [show 2 * (Real.pi / 2 - x) = Real.pi - 2 * x by ring, Real.sin_pi_sub]

/-! ## Integrability bookkeeping -/

/-- If `0 ≤ f ≤ g` pointwise on a measurable set `s` and `g` is integrable on `s`, then so is
`f` (an `AEStronglyMeasurable` hypothesis is all else that is needed). -/
private lemma integrableOn_of_le {s : Set ℝ} {f g : ℝ → ℝ} (hms : MeasurableSet s)
    (hg : IntegrableOn g s) (hf : AEStronglyMeasurable f (volume.restrict s))
    (hnn : ∀ x ∈ s, 0 ≤ f x) (hle : ∀ x ∈ s, f x ≤ g x) : IntegrableOn f s := by
  have hg' : Integrable g (volume.restrict s) := hg
  refine hg'.mono' hf ?_
  rw [MeasureTheory.ae_restrict_iff' hms]
  filter_upwards with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (hnn x hx)]
  exact hle x hx




/-! ## The left half of the sharp Hardy inequality -/


/-! ## Reflection to the right half -/







end

end Work.FTS.EllipticEst.H2W.AeWAux
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.aSliceData =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## The `θ`-slice data of `z² ∂_z² Ψ`

For a datum `Ψ` of the weak class `TT.EllWeakPos α 2 F Ψ` (i.e. `bslOp α Ψ = F` on the open
quadrant, the two Dirichlet data, the two moment conditions, and `HkMem`-honesty of `F`, of
`z²∂_z²Ψ` and of `∂_θ²Ψ`), this file records the two elementary facts about the *angular slices*
of `z²∂_z²Ψ` that the level-`0` angular estimate consumes:

* as a function of `θ` it is `C^n` on `(0,π/2)` for every `n`, and it *vanishes* at the two
  endpoints `θ = 0`, `θ = π/2` (this is where the Dirichlet data `Ψ(z,0) = Ψ(z,π/2) = 0` is
  used: the `θ₀`-slice of `Ψ` vanishes identically, hence so do all its `z`-derivatives);
* it is the pointwise difference `D_z²Ψ - D_zΨ` of the first two `D_z`-iterates on the open
  quadrant, which is the identity `z²∂_z² = D_z² - D_z` used to transfer the elliptic equation
  to `z²∂_z²Ψ`. -/

/-- If the `θ₀`-slice of `f` vanishes identically, then so does the `θ₀`-slice of every
iterated `z`-derivative `∂_z^n f`: the slice `z ↦ ∂_z^n f z θ₀` is the `n`-th derivative of the
zero function.  (`deriv` is totalised but agrees with the usual derivative on the constant
function `0`.) -/
theorem pzIter_eq_zero_of_slice_eq_zero {f : ℝ → ℝ → ℝ} {θ₀ : ℝ}
    (h0 : ∀ z, f z θ₀ = 0) : ∀ n : ℕ, ∀ z : ℝ, Work.Spaces.pzIter n f z θ₀ = 0 := by
  intro n
  induction n with
  | zero => intro z; exact h0 z
  | succ n ih =>
      intro z
      have hfun : (fun a : ℝ => Work.Spaces.pzIter n f a θ₀) = fun _ => (0 : ℝ) := funext ih
      show deriv (fun a : ℝ => Work.Spaces.pzIter n f a θ₀) z = 0
      rw [hfun]
      simp

/-- **The slice data of `z²∂_z²Ψ`.**  For a datum of the weak class: every angular slice of
`z²∂_z²Ψ` is `C^∞` on the open interval and vanishes at the two endpoints. -/
theorem aSliceData : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      (∀ z ∈ Work.Spaces.Iz,
          (∀ n : ℕ, ContDiffOn ℝ n (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              (Set.Ioo 0 (Real.pi / 2)))
            ∧ (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) 0 = 0
            ∧ (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (Real.pi / 2) = 0)
        ∧ ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
            z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
              = Work.Spaces.DzIter 2 Ψ z θ - Work.Spaces.DzIter 1 Ψ z θ := by
  intro α F Ψ hα hα4 h
  -- `Ψ` is `C^∞` on the open quadrant
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  refine ⟨?_, ?_⟩
  · -- the slice data at every `z ∈ [0,∞)`
    intro z hz
    have hzle : (0 : ℝ) ≤ z := by simpa [Work.Spaces.Iz] using hz
    rcases eq_or_lt_of_le hzle with hz0 | hzpos
    · -- at `z = 0` the slice is identically zero, whatever `Ψ` does there
      have hfun : (fun θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) = fun _ => (0 : ℝ) := by
        funext θ
        rw [show z = 0 from hz0.symm]
        simp
      refine ⟨fun n => ?_, ?_, ?_⟩
      · rw [hfun]
        exact contDiffOn_const
      · show z ^ 2 * Work.Spaces.pzIter 2 Ψ z 0 = 0
        rw [show z = 0 from hz0.symm]
        simp
      · show z ^ 2 * Work.Spaces.pzIter 2 Ψ z (Real.pi / 2) = 0
        rw [show z = 0 from hz0.symm]
        simp
    · -- at `z > 0` the slice of `∂_z²Ψ` is smooth on the open quadrant, by `curry_θ`
      have hslice : ∀ n : ℕ,
          ContDiffOn ℝ n (fun θ => Work.Spaces.pzIter 2 Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
        fun n => contDiffOn_iff_forall_nat_le.mp ((hΨ.pzIter 2).curry_θ hzpos) n le_top
      refine ⟨fun n => ?_, ?_, ?_⟩
      · exact (contDiffOn_const (c := z ^ 2)).mul (hslice n)
      · -- `∂_z²Ψ z 0 = 0`, because the slice `z' ↦ Ψ z' 0` vanishes identically
        have h2 : Work.Spaces.pzIter 2 Ψ z 0 = 0 :=
          pzIter_eq_zero_of_slice_eq_zero (fun z' => h.zero z') 2 z
        show z ^ 2 * Work.Spaces.pzIter 2 Ψ z 0 = 0
        rw [h2, mul_zero]
      · -- `∂_z²Ψ z (π/2) = 0`, for the same reason
        have h2 : Work.Spaces.pzIter 2 Ψ z (Real.pi / 2) = 0 :=
          pzIter_eq_zero_of_slice_eq_zero (fun z' => h.pi_half z') 2 z
        show z ^ 2 * Work.Spaces.pzIter 2 Ψ z (Real.pi / 2) = 0
        rw [h2, mul_zero]
  · -- the identity `z²∂_z²Ψ = D_z²Ψ - D_zΨ` on the open quadrant
    intro z hz θ hθ0 hθ1
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using
      Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_eq_open Ψ hΨ hz ⟨hθ0, hθ1⟩

end Work.FTS.EllipticEst.H2W
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.hksqSplitAux =====
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
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# Bookkeeping layer for `hksqSplitMixed`

The self-contained auxiliary layer of `Work.FTS.EllipticEst.H2W.hksqSplitMixed`: the generic
splitting of an iterated integral over `Iz × Iθ` into a finite sum, the honesty of the
individual summands inherited from `HkMem` by domination with the `ℋ^k`-integrand, and the
congruence of weighted `L²`-squares on the open quadrant.
-/

/-! ## Small pointwise and measure-theoretic bookkeeping -/

/-- Multiplication of a function which is `C^∞` on the open quadrant by the radial factor
`z ^ 2` keeps it `C^∞` there. -/
theorem smoothOpen_zsq_mul {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * f z θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => z ^ 2 * f z θ)) Work.FTS.EllipticEst.Q0
  rw [show Function.uncurry (fun z θ => z ^ 2 * f z θ)
      = fun p : ℝ × ℝ => p.1 ^ 2 * f p.1 p.2 from rfl]
  have hf' : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => f p.1 p.2)
      Work.FTS.EllipticEst.Q0 := hf
  exact ((contDiffOn_fst (𝕜 := ℝ) (s := Work.FTS.EllipticEst.Q0)).pow 2).mul hf'

/-- The product weight `Wt α` is continuous on the open quadrant. -/
theorem continuousOn_Wt_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hmem : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2 :=
    fun p hp => Work.FTS.EllipticEst.mem_Q0.mp hp
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := fun p hp => by
    obtain ⟨-, h0, h1⟩ := hmem p hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.EllipticEst.Q0 := by
    have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
    rw [hfun]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    exact pow_ne_zero 2 (ne_of_gt (hmem p hp).1)
  have hWt : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by funext p; rfl
  rw [hWt]
  refine hw.mul ?_
  exact (((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn)).rpow_const
    (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))

/-- The `ℋ^k`-integrand vanishes identically at `z = 0`. -/
theorem HkIntegrand_at_zero (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.wTheta, Work.Spaces.w]
  norm_num


/-! ## Splitting an iterated integral into a finite sum -/




/-- **Honesty of the iterated integral of a square dominated by the `ℋ^k`-integrand.**
This is the `HkMem`-version of the integrability of a single summand of the
`ℋ^k`-integrand: a nonnegative square bounded pointwise by the (integrable) full integrand
is honest.  The a.e. strong measurability comes from continuity on the open quadrant. -/
theorem i2Mem_sq_of_le {α : ℝ} {k : ℕ} {f A : ℝ → ℝ → ℝ} (hm : Work.Spaces.HkMem α k f)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => (A p.1 p.2) ^ 2) Work.FTS.EllipticEst.Q0)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (A z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k f z θ) :
    Work.Coercivity.I2Mem (fun z θ => (A z θ) ^ 2) := by
  constructor
  · intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      refine MeasureTheory.IntegrableOn.congr_fun MeasureTheory.integrableOn_zero
        (fun θ hθ => ?_) measurableSet_Icc
      have h1 := hle 0 (le_refl (0 : ℝ)) θ hθ
      rw [HkIntegrand_at_zero] at h1
      exact (le_antisymm h1 (sq_nonneg _)).symm
    · have hsl : ContinuousOn (fun θ : ℝ => (A z θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) :=
        hcont.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun θ hθ => ⟨hz0, hθ⟩)
      have haesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (A z θ) ^ 2)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
        have h1 : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (A z θ) ^ 2)
            (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
          hsl.aestronglyMeasurable measurableSet_Ioo
        have hset : MeasureTheory.volume.restrict Work.Spaces.Iθ
            = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
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
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
        fun θ hθ => hle z hz θ hθ)


end Work.FTS.EllipticEst.H2W
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.FOH.bridge =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest.FOH

open MeasureTheory Set Filter
open scoped ENNReal Topology



end Work.FTS.EllipticEst.Honest.FOH
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.HkSqAssembly =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option maxHeartbeats 1000000

/-! ## Elementary algebra -/

/-- **Five-term Cauchy–Schwarz**: `(a+b+c+d+e)² ≤ 5(a²+b²+c²+d²+e²)`. -/
lemma sq_sum_five_le (a b c d e : ℝ) :
    (a + b + c + d + e) ^ 2 ≤ 5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (a - e),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (b - e), sq_nonneg (c - d),
    sq_nonneg (c - e), sq_nonneg (d - e)]


/-! ## The level-`0` integrand -/

/-- The level-`0` `HkIntegrand` is the square of `|g|` times the level-`0` weight
`w z / sin(2θ)^{η/2}`. -/
lemma HkIntegrand_zero_eq_abs (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (|g z θ| * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  rw [HkIntegrand_zero_eq, mul_pow, mul_pow, sq_abs]

/-- The level-`0` `HkIntegrand` vanishes on the angular boundary `sin(2θ) = 0`. -/
lemma HkIntegrand_zero_of_sin_eq_zero (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hs : Real.sin (2 * θ) = 0) : Work.Spaces.HkIntegrand α 0 f z θ = 0 := by
  rw [HkIntegrand_zero_eq]
  have hsin : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) = 0 := by
    rw [hs, Real.zero_rpow (by norm_num [Work.Spaces.eta])]
  rw [hsin, div_zero, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

/-! ## The pointwise five-term domination -/

/-- **The pointwise five-term Cauchy–Schwarz for the level-`0` integrand.**  If
`|u| ≤ |g₁| + ⋯ + |g₅|` on the *open* quadrant, then on the *closed* quadrant the level-`0`
`HkIntegrand` of `u` is dominated by `5` times the sum of the `HkIntegrand`s of the `gᵢ`.

On the open quadrant this is `sq_sum_five_le` applied after multiplying by the nonnegative
weight `w z / sin(2θ)^{η/2}`; on the boundary `z = 0` or `sin 2θ = 0` the integrand is `0`
on both sides. -/
theorem HkIntegrand_zero_le_five {α : ℝ} {u g1 g2 g3 g4 g5 : ℝ → ℝ → ℝ}
    (h : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      |u z θ| ≤ |g1 z θ| + |g2 z θ| + |g3 z θ| + |g4 z θ| + |g5 z θ|) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 u z θ
        ≤ 5 * (Work.Spaces.HkIntegrand α 0 g1 z θ + Work.Spaces.HkIntegrand α 0 g2 z θ
              + Work.Spaces.HkIntegrand α 0 g3 z θ + Work.Spaces.HkIntegrand α 0 g4 z θ
              + Work.Spaces.HkIntegrand α 0 g5 z θ) := by
  have hnn : ∀ z θ, 0 ≤ 5 * (Work.Spaces.HkIntegrand α 0 g1 z θ
      + Work.Spaces.HkIntegrand α 0 g2 z θ + Work.Spaces.HkIntegrand α 0 g3 z θ
      + Work.Spaces.HkIntegrand α 0 g4 z θ + Work.Spaces.HkIntegrand α 0 g5 z θ) := by
    intro z θ
    have h1 := Work.Spaces.HkIntegrand_nonneg α 0 g1 z θ
    have h2 := Work.Spaces.HkIntegrand_nonneg α 0 g2 z θ
    have h3 := Work.Spaces.HkIntegrand_nonneg α 0 g3 z θ
    have h4 := Work.Spaces.HkIntegrand_nonneg α 0 g4 z θ
    have h5 := Work.Spaces.HkIntegrand_nonneg α 0 g5 z θ
    linarith
  intro z hz θ hθ
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · rw [← hz0, Work.Spaces.HkIntegrand_zero_z]
    exact hnn 0 θ
  · by_cases hs : Real.sin (2 * θ) = 0
    · rw [HkIntegrand_zero_of_sin_eq_zero α u hs]
      exact hnn z θ
    · -- the open quadrant
      have hθb : 0 ≤ θ ∧ θ ≤ Real.pi / 2 := hθ
      have hθ0 : 0 < θ := by
        rcases eq_or_lt_of_le hθb.1 with h' | h'
        · exact absurd (by rw [← h']; simp) hs
        · exact h'
      have hθ1 : θ < Real.pi / 2 := by
        rcases lt_or_eq_of_le hθb.2 with h' | h'
        · exact h'
        · exact absurd (by rw [h', show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring,
            Real.sin_pi]) hs
      have hwt : 0 ≤ Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := by
        have hw : 0 ≤ Work.Spaces.w z := by
          rw [Work.Spaces.w]
          exact div_nonneg (sq_nonneg _) (sq_nonneg _)
        have hsden : 0 ≤ Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) :=
          (Real.rpow_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
            _).le
        exact div_nonneg hw hsden
      set wt : ℝ := Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) with hwtdef
      have hbase : |u z θ| * wt ≤ (|g1 z θ| + |g2 z θ| + |g3 z θ| + |g4 z θ| + |g5 z θ|) * wt :=
        mul_le_mul_of_nonneg_right (h z hzpos θ hθ0 hθ1) hwt
      have hsq : (|u z θ| * wt) ^ 2
          ≤ ((|g1 z θ| + |g2 z θ| + |g3 z θ| + |g4 z θ| + |g5 z θ|) * wt) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) hwt) hbase 2
      have hexp : (|g1 z θ| + |g2 z θ| + |g3 z θ| + |g4 z θ| + |g5 z θ|) * wt
          = |g1 z θ| * wt + |g2 z θ| * wt + |g3 z θ| * wt + |g4 z θ| * wt + |g5 z θ| * wt := by
        ring
      have hfive : (|g1 z θ| * wt + |g2 z θ| * wt + |g3 z θ| * wt + |g4 z θ| * wt
            + |g5 z θ| * wt) ^ 2
          ≤ 5 * ((|g1 z θ| * wt) ^ 2 + (|g2 z θ| * wt) ^ 2 + (|g3 z θ| * wt) ^ 2
              + (|g4 z θ| * wt) ^ 2 + (|g5 z θ| * wt) ^ 2) :=
        sq_sum_five_le _ _ _ _ _
      calc Work.Spaces.HkIntegrand α 0 u z θ
          = (|u z θ| * wt) ^ 2 := by rw [HkIntegrand_zero_eq_abs]
        _ ≤ ((|g1 z θ| + |g2 z θ| + |g3 z θ| + |g4 z θ| + |g5 z θ|) * wt) ^ 2 := hsq
        _ = (|g1 z θ| * wt + |g2 z θ| * wt + |g3 z θ| * wt + |g4 z θ| * wt
              + |g5 z θ| * wt) ^ 2 := by rw [hexp]
        _ ≤ 5 * ((|g1 z θ| * wt) ^ 2 + (|g2 z θ| * wt) ^ 2 + (|g3 z θ| * wt) ^ 2
              + (|g4 z θ| * wt) ^ 2 + (|g5 z θ| * wt) ^ 2) := hfive
        _ = 5 * (Work.Spaces.HkIntegrand α 0 g1 z θ + Work.Spaces.HkIntegrand α 0 g2 z θ
              + Work.Spaces.HkIntegrand α 0 g3 z θ + Work.Spaces.HkIntegrand α 0 g4 z θ
              + Work.Spaces.HkIntegrand α 0 g5 z θ) := by
            rw [HkIntegrand_zero_eq_abs, HkIntegrand_zero_eq_abs, HkIntegrand_zero_eq_abs,
              HkIntegrand_zero_eq_abs, HkIntegrand_zero_eq_abs]

/-! ## Integrating a pointwise five-term domination -/


/-! ## The assembly -/


end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.HonFirstMoment =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Two elementary facts about the angular profile and the slices -/

/-- `sinθcos²θ ≥ 0` on `Iθ`. -/
theorem sinCos2_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Elliptic.sinCos2 θ := by
  rw [Work.Elliptic.sinCos2]
  have h1 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  positivity

/-- The angular profile is continuous. -/
theorem continuous_sinCos2 : Continuous (fun θ : ℝ => Work.Elliptic.sinCos2 θ) := by
  rw [show (fun θ : ℝ => Work.Elliptic.sinCos2 θ)
      = fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2 from rfl]
  fun_prop


/-! ## The signed moment is an honest integral -/



/-! ## The main theorem -/


end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.honestBarLim =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false


end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.honestGSlice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Elementary facts about the weight `σ` -/


/-- `σ` is continuous on the open quadrant. -/
theorem continuousOn_sig_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, h0, h1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact sin_two_pos_of_mem_Ioo ⟨h0, h1⟩
  have hbase : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  exact hbase.rpow_const (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))

/-- `σ` is continuous on the open angular interval.

**Renamed from `continuousOn_sig_Ioo` (2026-10-04, branch-merge repair).**  `Honest/sliceBarSq2.lean`
declares a *different* lemma under that exact name, so any module whose import cone contained both
files was unimportable (`environment already contains 'Work.FTS.EllipticEst.Honest.continuousOn_sig_Ioo'`),
which split the elliptic library into two branches that several assemblies need together.  This
copy is used only by `aesm_sig_Iθ` below, and nothing outside this file refers to it; the external
references to the name (`ThetaU/Pieces/AeBarHkMem.lean`) resolve to `sliceBarSq2`'s version. -/
theorem continuousOn_sig_Ioo_open :
    ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hcont : Continuous fun θ : ℝ => ((1 : ℝ), θ) := by fun_prop
  have hmap : Set.MapsTo (fun θ : ℝ => ((1 : ℝ), θ)) (Set.Ioo 0 (Real.pi / 2))
      Work.FTS.EllipticEst.Q0 := fun θ hθ => ⟨by norm_num, hθ.1, hθ.2⟩
  have h := continuousOn_sig_Q0.comp hcont.continuousOn hmap
  simpa [Function.comp_def] using h

/-- `σ` is a.e. strongly measurable on `Iθ`. -/
theorem aesm_sig_Iθ :
    MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ)
      (volume.restrict Work.Spaces.Iθ) := by
  rw [restrict_Iθ_eq_Ioo]
  exact continuousOn_sig_Ioo_open.aestronglyMeasurable measurableSet_Ioo


/-! ## The angular slices of `Ψ` are bounded -/


/-! ## The one-dimensional Cauchy–Schwarz (Jensen) bound for interval integrals -/

/-- For a function continuous on `[a,a+1]`, the square of the integral is at most the integral of
the square: Jensen's inequality for the convex function `x ↦ x²` with respect to the probability
measure `vol.restrict (a,a+1]`. -/
theorem sq_integral_le_of_continuousOn {a : ℝ} {u : ℝ → ℝ}
    (hu : ContinuousOn u (Set.Icc a (a + 1))) :
    (∫ x in a..(a + 1), u x) ^ 2 ≤ ∫ x in a..(a + 1), (u x) ^ 2 := by
  haveI : MeasureTheory.IsProbabilityMeasure (volume.restrict (Set.Ioc a (a + 1))) := by
    refine ⟨?_⟩
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
    norm_num
  have huI : MeasureTheory.Integrable u (volume.restrict (Set.Ioc a (a + 1))) :=
    (hu.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hu2I : MeasureTheory.Integrable (fun x => (u x) ^ 2) (volume.restrict (Set.Ioc a (a + 1))) :=
    ((hu.pow 2).integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hj := ConvexOn.map_integral_le (μ := volume.restrict (Set.Ioc a (a + 1))) (s := Set.univ)
    (f := u) (g := fun x : ℝ => x ^ 2)
    (Even.convexOn_pow (𝕜 := ℝ) even_two) (continuousOn_id.pow 2) isClosed_univ
    (Filter.Eventually.of_forall (fun x => Set.mem_univ _)) huI hu2I
  rw [intervalIntegral.integral_of_le (le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 1)),
    intervalIntegral.integral_of_le (le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 1))]
  exact hj

/-! ## The box bound -/


/-! ## The second-order Taylor formula along `z` -/


/-! ## The main statement -/


end Work.FTS.EllipticEst.Honest
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.Fstar_DzIter_one_Psi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

/-- **The angular moment of `D_zΨ` vanishes for a datum of the weak class.**

This is the `Ψ`-half of `remov.Fstar_DzIter_one_eq_zero`: the moment condition needed to apply
the induction step `EllWeakPos_DzIter_one_shift` to the radially differentiated data
`(D_z F, D_z Ψ)`.

The proof is a *first-order* argument (no differentiation under the integral sign, hence no
`C¹`-up-to-the-boundary hypothesis): fix `z₀ > 0`, put
`B = ∫_θ ∂_zΨ(z₀,θ) sinθcos²θ dθ`, and for `h ∈ (0,z₀)` set
`G_h(θ) = (Ψ(z₀+h,θ) - Ψ(z₀,θ))/h - ∂_zΨ(z₀,θ)`.

* Because the two angular moments `F_*(Ψ)(z₀)`, `F_*(Ψ)(z₀+h)` vanish (a hypothesis) and
  `θ ↦ Ψ(z,θ) sinθcos²θ` is integrable (`Psi_slice_sinCos2_integrable`), linearity gives
  `∫_θ G_h(θ) sinθcos²θ dθ = -B`.
* On the other hand `G_h(θ) = h^{-1}∫_0^h (∂_zΨ(z₀+s,θ) - ∂_zΨ(z₀,θ)) ds`, so by the
  fundamental theorem of calculus along the `θ`-slice and Cauchy–Schwarz in `s`,
  `|G_h(θ)| ≤ (2/3)√h √(∫_0^h (∂_z²Ψ(z₀+s,θ))² ds)`, whence by Young's inequality and
  Tonelli `|B| ≤ K √h`, with `K` the weighted `ℋ^k`-energy of `z²∂_z²Ψ` divided by `z₀⁴` plus
  `π/2` (`DzIter_one_Psi_estimate`).

Letting `h → 0` gives `B = 0`, and `F_*(D_zΨ)(z₀) = z₀ B` because `D_z = z ∂_z` pulls out of the
angular integral. -/
theorem Fstar_DzIter_one_Psi {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z = 0 := by
  intro z₀ hz₀
  have hso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hcontσ : Continuous (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2) := by
    simp only [Work.Elliptic.sinCos2]; fun_prop
  have hsinCos2_nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Work.Elliptic.sinCos2 θ := by
    intro θ hθ
    rw [Work.Elliptic.sinCos2]
    have h1 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    nlinarith [sq_nonneg (Real.cos θ)]
  have hPsi : ∀ z, 0 < z → MeasureTheory.Integrable
      (fun θ : ℝ => Ψ z θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    have h1 : MeasureTheory.Integrable
        (fun θ : ℝ => |Ψ z θ| * Work.Elliptic.sinCos2 θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (Psi_slice_sinCos2_integrable hk h z hz).integrable
    refine h1.mono' ?_ ?_
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2)
        (hso.continuousOn.mul hcontσ.continuousOn) hz
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hsinCos2_nn θ hθ)]
  set B : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ with hB
  have hF : Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z₀ = z₀ * B := by
    rw [Work.Elliptic.Fstar, hB]
    rw [show (fun θ : ℝ => Work.Spaces.DzIter 1 Ψ z₀ θ * Work.Elliptic.sinCos2 θ)
        = fun θ : ℝ => z₀ * (Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ) from by
      funext θ
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz]
      ring]
    rw [MeasureTheory.integral_const_mul]
  by_cases hBint : MeasureTheory.Integrable
      (fun θ : ℝ => Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)
  · have hzero : B = 0 := by
      have hest := DzIter_one_Psi_estimate_sound hk h hPsi z₀ hz₀ hBint
      by_contra hne
      have hpos : 0 < |B| := abs_pos.mpr hne
      set K : ℝ := (∫ z in Work.Spaces.Iz,
              ∫ θ in Work.Spaces.Iθ,
                ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
                  * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
              / z₀ ^ 4
            + Real.pi / 2 with hKdef
      have hKnn : 0 ≤ K := by
        rw [hKdef]
        have h1 : 0 ≤ ∫ z in Work.Spaces.Iz,
              ∫ θ in Work.Spaces.Iθ,
                ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
                  * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 :=
          integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
        have h2 : 0 ≤ z₀ ^ 4 := by positivity
        have h3 : 0 ≤ Real.pi / 2 := by positivity
        exact add_nonneg (div_nonneg h1 h2) h3
      set h₁ : ℝ := min (z₀ / 2) ((|B| / (2 * (K + 1))) ^ 2) with hh₁
      have hh₁pos : 0 < h₁ := by
        rw [hh₁]
        exact lt_min (by linarith) (by positivity)
      have hh₁lt : h₁ < z₀ := by
        rw [hh₁]
        exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hb := hest h₁ ⟨hh₁pos, hh₁lt⟩
      have hK1 : 0 < K + 1 := by linarith
      have hsq : Real.sqrt h₁ ≤ |B| / (2 * (K + 1)) := by
        have hle : h₁ ≤ (|B| / (2 * (K + 1))) ^ 2 := by
          rw [hh₁]
          exact min_le_right _ _
        calc Real.sqrt h₁ ≤ Real.sqrt ((|B| / (2 * (K + 1))) ^ 2) := Real.sqrt_le_sqrt hle
          _ = |B| / (2 * (K + 1)) := by
              rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
      have hstep : K * Real.sqrt h₁ ≤ |B| / 2 := by
        have h1 : K * Real.sqrt h₁ ≤ K * (|B| / (2 * (K + 1))) :=
          mul_le_mul_of_nonneg_left hsq hKnn
        have h2 : K * (|B| / (2 * (K + 1))) ≤ |B| / 2 := by
          have hcoef : K / (2 * (K + 1)) ≤ 1 / 2 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
            linarith
          calc K * (|B| / (2 * (K + 1))) = (K / (2 * (K + 1))) * |B| := by ring
            _ ≤ (1 / 2) * |B| := mul_le_mul_of_nonneg_right hcoef (abs_nonneg B)
            _ = |B| / 2 := by ring
        linarith
      linarith [hb, hstep, hpos]
    rw [hF, hzero, mul_zero]
  · have hzero : B = 0 := by
      rw [hB]
      exact MeasureTheory.integral_undef hBint
    rw [hF, hzero, mul_zero]

end

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.SourceBound.diffEqAlphaNeg5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound


end Work.FTS.EllipticEst.remov.SourceBound
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The angular trace at `θ = π/4`

The level-six transport estimates need the *angular* trace of a weighted `D_z`-iterate at the
fixed angle `θ = π/4`.  Because `sin(2θ) = 1` there, the two angular weights
`sin(2θ)^{-η/2}` and `sin(2θ)^{-γ/2}` of the `ℋ⁶`-integrand are *bounded below* by `1` near
`π/4` (and above by an absolute constant), so — in contrast with the uniform-in-`θ`
Agmon/`SliceSupOpen` bounds, which lose a factor `1/α` — the trace estimate is *α-uniform*.

The route is the classical one-dimensional Morrey inequality on a fixed subinterval
`J = [π/8, 3π/8] ∋ π/4` on which `sin(2θ) ≥ 1/2`:
`h(π/4)² ≤ (2/|J|)∫_J h² + 2|J|∫_J (h')²`, applied to the angular slice
`h = fun θ => D_z^j g z θ`, followed by the pointwise slot comparisons
`w(z)²(D_z^j g)² ≤ HkIntegrand` and `w(z)²(∂_θD_z^j g)² ≤ 4·HkIntegrand`
(the latter through `∂_θ D_z^j g = mixed j 1 g / sin(2θ)`). -/

/-- **One-dimensional trace (Morrey) inequality.**  For `a < x₀ < b` and `h` of class
`C¹` on `[a,b]` (with `deriv h` continuous there), the value of `h` at the interior point
`x₀` is controlled by the `L²`-norms of `h` and of `deriv h` on `[a,b]`:
`h(x₀)² ≤ (2/(b-a))∫ h² + 2(b-a)∫ (h')²`. -/
theorem trace_morrey {h : ℝ → ℝ} {a x₀ b : ℝ} (hax : a < x₀) (hxb : x₀ < b)
    (hcont : ContinuousOn h (Set.Icc a b))
    (hdc : ContinuousOn (deriv h) (Set.Icc a b))
    (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt h (deriv h x) x) :
    (h x₀) ^ 2 ≤ (2 / (b - a)) * (∫ x in Set.Icc a b, (h x) ^ 2)
      + 2 * (b - a) * (∫ x in Set.Icc a b, (deriv h x) ^ 2) := by
  have hab : a < b := lt_trans hax hxb
  have hbma : 0 < b - a := by linarith
  have hInt1 : IntegrableOn (fun x => |deriv h x|) (Set.Icc a b) :=
    hdc.abs.integrableOn_compact isCompact_Icc
  have hInt0 : IntegrableOn (fun x => (h x) ^ 2) (Set.Icc a b) :=
    (hcont.pow 2).integrableOn_compact isCompact_Icc
  have hInt2 : IntegrableOn (fun x => (deriv h x) ^ 2) (Set.Icc a b) :=
    (hdc.pow 2).integrableOn_compact isCompact_Icc
  have hvol_ne : (volume : Measure ℝ) (Set.Icc a b) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  set S : ℝ := ∫ x in Set.Icc a b, |deriv h x| with hSdef
  -- the difference `h x₀ - h y` is bounded by the `L¹`-norm of `h'`
  have hdiff : ∀ y ∈ Set.Icc a b, (h x₀ - h y) ^ 2 ≤ S ^ 2 := by
    intro y hy
    have hyb : y ≤ b := hy.2
    have hay : a ≤ y := hy.1
    have hsub : Set.Ioc (min y x₀) (max y x₀) ⊆ Set.Icc a b := by
      intro x hx
      rw [Set.mem_Ioc] at hx
      have h1 : a ≤ min y x₀ := le_min hay hax.le
      have h2 : max y x₀ ≤ b := max_le hyb hxb.le
      exact ⟨le_of_lt (lt_of_le_of_lt h1 hx.1), le_trans hx.2 h2⟩
    have hmono : (∫ x in Set.Ioc (min y x₀) (max y x₀), |deriv h x|) ≤ S := by
      rw [hSdef]
      refine MeasureTheory.setIntegral_mono_set hInt1 ?_ ?_
      · exact Eventually.of_forall (fun x => abs_nonneg (deriv h x))
      · exact Eventually.of_forall (fun x hx => hsub hx)
    have key : |h x₀ - h y| ≤ ∫ x in Set.Ioc (min y x₀) (max y x₀), |deriv h x| := by
      rcases le_total y x₀ with hyx | hxy
      · -- `y ≤ x₀`: fundamental theorem of calculus on `[y,x₀]`
        have hFTC : ∫ x in y..x₀, deriv h x = h x₀ - h y := by
          refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hyx ?_ ?_ ?_
          · exact hcont.mono (Set.Icc_subset_Icc hay (le_of_lt hxb))
          · intro x hx
            exact hd x ⟨lt_of_le_of_lt hay hx.1, lt_of_lt_of_le hx.2 (le_of_lt hxb)⟩
          · refine ContinuousOn.intervalIntegrable (a := y) (b := x₀) ?_
            rw [Set.uIcc_of_le hyx]
            exact hdc.mono (Set.Icc_subset_Icc hay (le_of_lt hxb))
        have hset : Set.Ioc (min y x₀) (max y x₀) = Set.Ioc y x₀ := by
          rw [min_eq_left hyx, max_eq_right hyx]
        rw [hset, ← hFTC, intervalIntegral.integral_of_le hyx]
        exact MeasureTheory.abs_integral_le_integral_abs
      · -- `x₀ ≤ y`: the same on `[x₀,y]`
        have hFTC : ∫ x in x₀..y, deriv h x = h y - h x₀ := by
          refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hxy ?_ ?_ ?_
          · exact hcont.mono (Set.Icc_subset_Icc (le_of_lt hax) hyb)
          · intro x hx
            exact hd x ⟨lt_trans hax hx.1, lt_of_lt_of_le hx.2 hyb⟩
          · refine ContinuousOn.intervalIntegrable (a := x₀) (b := y) ?_
            rw [Set.uIcc_of_le hxy]
            exact hdc.mono (Set.Icc_subset_Icc (le_of_lt hax) hyb)
        have hset : Set.Ioc (min y x₀) (max y x₀) = Set.Ioc x₀ y := by
          rw [min_eq_right hxy, max_eq_left hxy]
        have hneg : h x₀ - h y = -(∫ x in x₀..y, deriv h x) := by rw [hFTC]; ring
        rw [hset, hneg, abs_neg, intervalIntegral.integral_of_le hxy]
        exact MeasureTheory.abs_integral_le_integral_abs
    have h2 : |h x₀ - h y| ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (le_trans key hmono) 2
    rwa [sq_abs] at h2
  -- pointwise: `h x₀² ≤ 2 h y² + 2 S²`
  have hpoint : ∀ y ∈ Set.Icc a b, (h x₀) ^ 2 ≤ 2 * (h y) ^ 2 + 2 * S ^ 2 := by
    intro y hy
    have h1 := hdiff y hy
    nlinarith [h1, sq_nonneg (h x₀ - 2 * h y)]
  have hIntRhs : IntegrableOn (fun y => 2 * (h y) ^ 2 + 2 * S ^ 2) (Set.Icc a b) :=
    (hInt0.const_mul 2).add (integrableOn_const (C := 2 * S ^ 2) hvol_ne)
  -- average the pointwise inequality over `y ∈ [a,b]`
  have hmono2 : (∫ y in Set.Icc a b, (h x₀) ^ 2)
      ≤ ∫ y in Set.Icc a b, (2 * (h y) ^ 2 + 2 * S ^ 2) :=
    MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall (fun y => sq_nonneg _)) hIntRhs
      (ae_restrict_of_forall_mem measurableSet_Icc hpoint)
  have hL : (∫ y in Set.Icc a b, (h x₀) ^ 2) = (b - a) * (h x₀) ^ 2 := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ b - a), smul_eq_mul]
  have hR : (∫ y in Set.Icc a b, (2 * (h y) ^ 2 + 2 * S ^ 2))
      = 2 * (∫ y in Set.Icc a b, (h y) ^ 2) + 2 * (b - a) * S ^ 2 := by
    rw [MeasureTheory.integral_add (hInt0.const_mul 2) (integrableOn_const (C := 2 * S ^ 2) hvol_ne),
      MeasureTheory.integral_const_mul, MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def,
      Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ b - a), smul_eq_mul]
    ring
  -- Cauchy–Schwarz: `S² ≤ (b-a) ∫ (h')²`
  have hCS : S ^ 2 ≤ (b - a) * (∫ x in Set.Icc a b, (deriv h x) ^ 2) := by
    have hmem1 : MemLp (fun _ : ℝ => (1:ℝ)) 2 (volume.restrict (Set.Icc a b)) := memLp_const 1
    have hmem0 : MemLp (deriv h) 2 (volume.restrict (Set.Icc a b)) :=
      (MeasureTheory.memLp_two_iff_integrable_sq
        (measurable_deriv h).aestronglyMeasurable).mpr hInt2
    have hmem2 : MemLp (fun x => |deriv h x|) 2 (volume.restrict (Set.Icc a b)) := by
      simpa using hmem0.norm
    have hcs := Work.Spaces.cs_integral hmem1 hmem2
    have h1 : (∫ x in Set.Icc a b, (1:ℝ) * |deriv h x|) = S := by
      rw [hSdef]
      exact MeasureTheory.integral_congr_ae (Eventually.of_forall (fun x => by simp))
    have h2 : (∫ x in Set.Icc a b, (1:ℝ) ^ 2) = b - a := by
      rw [one_pow, MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ b - a), smul_eq_mul, mul_one]
    have h3 : (∫ x in Set.Icc a b, |deriv h x| ^ 2)
        = ∫ x in Set.Icc a b, (deriv h x) ^ 2 :=
      MeasureTheory.integral_congr_ae (Eventually.of_forall (fun x => by simp [sq_abs]))
    rw [h1, h2, h3] at hcs
    exact hcs
  have hmain : (b - a) * (h x₀) ^ 2
      ≤ 2 * (∫ y in Set.Icc a b, (h y) ^ 2) + 2 * (b - a) * S ^ 2 := by
    rw [← hL, ← hR]
    exact hmono2
  have hfin : (b - a) * (h x₀) ^ 2
      ≤ (b - a) * ((2 / (b - a)) * (∫ x in Set.Icc a b, (h x) ^ 2)
          + 2 * (b - a) * (∫ x in Set.Icc a b, (deriv h x) ^ 2)) := by
    have hX : 2 * (b - a) * S ^ 2
        ≤ 2 * (b - a) * ((b - a) * (∫ x in Set.Icc a b, (deriv h x) ^ 2)) :=
      mul_le_mul_of_nonneg_left hCS (by linarith)
    calc (b - a) * (h x₀) ^ 2
        ≤ 2 * (∫ x in Set.Icc a b, (h x) ^ 2) + 2 * (b - a) * S ^ 2 := hmain
      _ ≤ 2 * (∫ x in Set.Icc a b, (h x) ^ 2)
            + 2 * (b - a) * ((b - a) * (∫ x in Set.Icc a b, (deriv h x) ^ 2)) := by linarith [hX]
      _ = (b - a) * ((2 / (b - a)) * (∫ x in Set.Icc a b, (h x) ^ 2)
          + 2 * (b - a) * (∫ x in Set.Icc a b, (deriv h x) ^ 2)) := by
        field_simp
  exact le_of_mul_le_mul_left hfin hbma

/-! ## The two pointwise slot comparisons -/

/-- The radial weight is nonnegative. -/
theorem w_nonneg_pi4 (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

/-- A weighted pure `D_z`-slot is dominated pointwise by the `ℋ^k`-integrand. -/
theorem wsq_dzIter_le_HkIntegrand_pi4 {α : ℝ} {g : ℝ → ℝ → ℝ} {j k : ℕ} (hjk : j ≤ k)
    {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter j g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have hsinθ : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hspos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hsinθ _
  have hsle : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one hsinθ.le (Real.sin_le_one _) (by norm_num [Work.Spaces.eta])
  have hL : Work.Spaces.w z ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
    rw [le_div_iff₀ hspos]
    nlinarith [w_nonneg_pi4 z, hsle]
  calc (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter j g z θ) ^ 2
      = (Work.Spaces.DzIter j g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 := by ring
    _ ≤ (Work.Spaces.DzIter j g z θ) ^ 2
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (w_nonneg_pi4 z) hL 2) (sq_nonneg _)
    _ = (Work.Spaces.DzIter j g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α k g z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α k g z θ j hjk

/-- A weighted mixed slot is dominated pointwise by the `ℋ^k`-integrand. -/
theorem wsq_mixed_le_HkIntegrand_pi4 {α : ℝ} (hα : 0 ≤ α) {g : ℝ → ℝ → ℝ} {i j k : ℕ}
    (hi : 1 ≤ i) (hij : i + j ≤ k) {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed j i g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have hsinθ : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsle1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hgam_nn : 0 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hspos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.gam α / 2) := Real.rpow_pos_of_pos hsinθ _
  have hsle : (Real.sin (2 * θ)) ^ (Work.Spaces.gam α / 2) ≤ 1 :=
    Real.rpow_le_one hsinθ.le hsle1 (by linarith)
  have hone : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := by
    rw [Real.rpow_neg hsinθ.le]
    exact (one_le_inv₀ hspos).mpr hsle
  have hL : Work.Spaces.w z ≤ Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := by
    simpa using mul_le_mul_of_nonneg_left hone (w_nonneg_pi4 z)
  calc (Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed j i g z θ) ^ 2
      = (Work.Spaces.mixed j i g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 := by ring
    _ ≤ (Work.Spaces.mixed j i g z θ) ^ 2
          * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (w_nonneg_pi4 z) hL 2) (sq_nonneg _)
    _ = (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 := by
        simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
        ring
    _ ≤ Work.Spaces.HkIntegrand α k g z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α k g z θ i j hi hij

/-- On `[π/8, 3π/8]` the angle satisfies `sin(2θ) ≥ 1/2` (used to convert the `θ`-derivative
of a `D_z`-iterate into the corresponding mixed slot). -/
theorem half_le_sin_two_pi4 {x : ℝ} (hx : x ∈ Set.Icc (Real.pi / 8) (3 * Real.pi / 8)) :
    (1 : ℝ) / 2 ≤ Real.sin (2 * x) := by
  have hxIθ : x ∈ Work.Spaces.Iθ :=
    ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
  have hmin : Real.pi / 8 ≤ min x (Real.pi / 2 - x) :=
    le_min (by linarith [hx.1]) (by linarith [hx.2])
  have h1 := Work.FTS.H2.min_le_sin x hxIθ
  nlinarith [h1, hmin, Real.pi_pos]


end
end Work.FTS.StrongPersist.N6Trans.SixRoute
end
