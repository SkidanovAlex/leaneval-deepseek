import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.Honest.I4UpperHonest
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.TT.ipMemUHtermFts
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SourceBound.weakSliceBounds
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.remov.wsSliceRight
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.T2Qaux.SupAux
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.LocDataExt.LocG5
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.LocDataExt.oneSubChi_jet_le5
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FzFacts
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Assembly6
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.H2.T1Q.SlotPtQ
import Submission.Work.H2.WPQ.hardy_slice_Aang
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.H2W.momentChainAe
import Submission.Work.SolutionDelivery.Scaling.Main
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.sup_mixed_le_H4
import Submission.Work.Stability.CutFactorFderivZero
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.aeGradTraceAe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `θ`-trace of `z ∂_z u` vanishes at both endpoints, a.e. in `z`

This module proves `Work.FTS.EllipticEst.AngAWeak.aeGradTraceAe`: for a datum
`AeData α u G` with the two *almost everywhere* honesties `hae` (a.e. `z > 0`: the slice
`θ ↦ (z ∂_θ∂_z u(z,θ))² σ(θ)` is integrable on `Iθ`) and `hint`
(`z ↦ w(z)² ∫_θ (z ∂_θ∂_z u(z,θ))² σ(θ)` is integrable on `Iz`), the slice
`θ ↦ z ∂_z u(z,θ)` tends to `0` at both endpoints `0⁺` and `(π/2)⁻` for almost every `z > 0`.

The argument is the one of
`Submission/Work/FTS/EllipticEst/H2W/SlotA/aeI1GradTraceLeft.lean` (the same statement under the
*global* honesty `HkMem α 0 (z ∂_θ∂_z u)`), carried out at both endpoints and with the exceptional
null set of `z` — where the slice energy of `z ∂_z u` need not be honest — threaded through the
`∀ᵐ z` statements.  The two halves are `aeGradTraceLeft` (below) and `aeGradTraceRight`.

The shared machinery (the slice energy `sliceE`, its local integrability from `hint`, the boundary
limits of `sliceBoundaryLimit`, the pointwise domination and the dominating function `boundU`) is
in `Submission.Work.FTS.EllipticEst.AngAWeak.GradTraceAux`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz




end Work.FTS.EllipticEst.AngAWeak
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.DiagEstEllT.FiniteFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.DiagEstEllT

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The open-quadrant smoothness of the datum -/



/-! ## The moment ladder, `L₁₂` and the primitive `J` -/







/-! ## The two Euler identities -/






/-! ## The vanishing of the `θ → 0⁺` trace -/


end Work.FTS.EllipticEst.Cores.DiagEstEllT
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.W5Clean.sliceStep5Integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false

/-! ## Part 0. Elementary facts about `Iθ`, the weights, and the region split -/

private lemma Iθ_eq_icc : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) := rfl

private lemma Iθ_measurable : MeasurableSet Work.Spaces.Iθ := by
  rw [Iθ_eq_icc]; exact measurableSet_Icc

private lemma Iθ_volume_lt_top : (volume : Measure ℝ) Work.Spaces.Iθ < ⊤ := by
  rw [Iθ_eq_icc, Real.volume_Icc]; exact ENNReal.ofReal_lt_top

/-- Almost every point of `Icc a b` lies in the open interval `Ioo a b`. -/
private lemma ae_mem_Ioo_of_Icc {a b : ℝ} :
    ∀ᵐ θ ∂(volume : Measure ℝ).restrict (Set.Icc a b), θ ∈ Set.Ioo a b := by
  rw [Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)) (a := a) (b := b)).symm]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- A function continuous on the open interval is a.e.-strongly-measurable for the
restriction to the closed interval. -/
private lemma aesm_of_continuousOn_Ioo {f : ℝ → ℝ} {a b : ℝ}
    (h : ContinuousOn f (Set.Ioo a b)) :
    AEStronglyMeasurable f ((volume : Measure ℝ).restrict (Set.Icc a b)) := by
  rw [Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)) (a := a) (b := b)).symm]
  exact h.aestronglyMeasurable measurableSet_Ioo

/-- `∂` commutes with `ContDiffOn` on an open set. -/
private lemma contDiffOn_deriv_of_le_w {f : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    {n m : WithTop ℕ∞} (h : ContDiffOn ℝ n f s) (hm : m + 1 ≤ n) :
    ContDiffOn ℝ m (deriv f) s := by
  intro x hx
  exact (Work.FTS.EllipticEst.remov.contDiffAt_deriv_of_le_w
    (h.contDiffAt (hs.mem_nhds hx)) hm).contDiffWithinAt

private lemma sin_two_nonneg_Iθ_prv {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := Work.FTS.EllipticEst.remov.sin_two_nonneg_R hθ

private lemma sEta_nonneg_Iθ' {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ := Work.FTS.EllipticEst.remov.sEta_nonneg_Iθ hθ

/-- `sin(2θ)^{2-γ} ≥ 0` on `Iθ`. -/
private lemma rpow_two_sub_gam_nonneg {γ θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
  Real.rpow_nonneg (sin_two_nonneg_Iθ_prv hθ) _

/-- `sin(2θ)^{2-γ} ≤ 1` on `Iθ` (because `2 - γ ≥ 0`). -/
private lemma rpow_two_sub_gam_le_one {γ θ : ℝ} (hγ2 : γ ≤ 3 / 2)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ 1 :=
  Real.rpow_le_one (sin_two_nonneg_Iθ_prv hθ) (Real.sin_le_one _) (by linarith)

/-- `sin(2θ)^{2-γ} ≤ sin(2θ)^{-η} = sEta θ` on `Iθ`. -/
private lemma rpow_two_sub_gam_le_sEta {γ θ : ℝ} (hγ2 : γ ≤ 3 / 2)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ Work.FTS.EllipticEst.sEta θ := by
  rcases eq_or_lt_of_le (sin_two_nonneg_Iθ_prv hθ) with hz | hpos
  · have h1 : Real.rpow (Real.sin (2 * θ)) (2 - γ) = 0 := by
      rw [← hz]; exact Real.zero_rpow (by linarith : (2 : ℝ) - γ ≠ 0)
    have h2 : Work.FTS.EllipticEst.sEta θ = 0 := by
      rw [Work.FTS.EllipticEst.sEta, ← hz]
      exact Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)
    rw [h1, h2]
  · refine Real.rpow_le_rpow_of_exponent_ge hpos (Real.sin_le_one _) ?_
    rw [Work.Spaces.eta]; linarith

/-- The explicit expression for `∂_θ g` coming from `Lzero1 u = g`. -/
private def gE (u : ℝ → ℝ) (θ : ℝ) : ℝ :=
  -(deriv (deriv (deriv u)) θ) + Real.tan θ * deriv (deriv u) θ
    + (2 * Real.tan θ ^ 2 - 4) * deriv u θ
    + (2 * Real.tan θ ^ 3 + 2 * Real.tan θ) * u θ

/-- **The comparison of the two weights** on `[π/2-1/8, π/2]`: with `δ = π/2 - θ`,
`sin 2θ = sin 2δ` and `δ ≤ sin 2δ ≤ 2δ` there. -/
private lemma sin_two_between_pi_half {θ : ℝ}
    (hθ : θ ∈ Set.Icc (Real.pi / 2 - 1 / 8) (Real.pi / 2)) :
    Real.pi / 2 - θ ≤ Real.sin (2 * θ) ∧ Real.sin (2 * θ) ≤ 2 * (Real.pi / 2 - θ) := by
  set δ : ℝ := Real.pi / 2 - θ with hδ
  have hδ0 : 0 ≤ δ := by simp only [hδ]; linarith [hθ.2]
  have hδ8 : δ ≤ 1 / 8 := by simp only [hδ]; linarith [hθ.1]
  have hsin : Real.sin (2 * θ) = Real.sin (2 * δ) := by
    rw [hδ]
    have : 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ := by ring
    rw [this, Real.sin_pi_sub]
  rw [hsin]
  have h2δ0 : 0 ≤ 2 * δ := by linarith
  have h2δπ : 2 * δ ≤ Real.pi / 2 := by linarith [hδ8, Real.pi_gt_three]
  refine ⟨?_, Real.sin_le h2δ0⟩
  have h1 : 2 / Real.pi * (2 * δ) ≤ Real.sin (2 * δ) := Real.mul_le_sin h2δ0 h2δπ
  have h2 : δ ≤ 2 / Real.pi * (2 * δ) := by
    have h4 : (1 : ℝ) ≤ 4 / Real.pi := by
      rw [le_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_four]
    have h5 : (1 : ℝ) * δ ≤ (4 / Real.pi) * δ := mul_le_mul_of_nonneg_right h4 hδ0
    calc δ = 1 * δ := by ring
      _ ≤ (4 / Real.pi) * δ := h5
      _ = 2 / Real.pi * (2 * δ) := by ring
  linarith

/-- On `[0, π/2-1/8]` we have `|tan θ| ≤ 8`. -/
private lemma abs_tan_le_eight {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2 - 1 / 8)) :
    |Real.tan θ| ≤ 8 := by
  set x : ℝ := Real.pi / 2 - θ with hx
  have hx1 : (0 : ℝ) < x := by simp only [hx]; linarith [hθ.2]
  have hx2 : x < Real.pi / 2 := by simp only [hx]; linarith [hθ.1]
  have htanpos : 0 < Real.tan x := Real.tan_pos_of_pos_of_lt_pi_div_two hx1 hx2
  have htanx : x ≤ Real.tan x := Real.le_tan hx1.le hx2
  have hx18 : (1 / 8 : ℝ) ≤ x := by simp only [hx]; linarith [hθ.2]
  have hkey : Real.tan θ = (Real.tan x)⁻¹ := by
    have h := Real.tan_pi_div_two_sub x
    rwa [show Real.pi / 2 - x = θ by simp only [hx]; ring] at h
  have hbound : (Real.tan x)⁻¹ ≤ 8 := by
    have h := (inv_le_inv₀ htanpos (by norm_num : (0 : ℝ) < 1 / 8)).mpr
      (by linarith [htanx, hx18])
    simpa using h
  rw [hkey, abs_of_nonneg (inv_nonneg.mpr htanpos.le)]
  exact hbound

/-! ## Part 1. The four conjuncts, one by one -/

/-- **Conjunct 1**: `(u/cos θ)² sin(2θ)^{2-γ}` is integrable on `Iθ`.  Pointwise,
`(u/cos θ)² ≤ 100 ∫ (u'')² sEta` (`div_cos_sq_le_M`) and the weight is at most `1`. -/
private lemma sliceStep5_integrable_V0 (γ : ℝ) (hγ2 : γ ≤ 3 / 2) {u : ℝ → ℝ}
    (hu2 : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (huc : ContinuousOn u (Set.Icc 0 (Real.pi / 2)))
    (hu0 : u 0 = 0) (hupi : u (Real.pi / 2) = 0)
    (h2 : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ := by
  set M : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
    Work.FTS.EllipticEst.sEta θ with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    exact MeasureTheory.setIntegral_nonneg Iθ_measurable
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_Iθ' hθ))
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
      ((volume : Measure ℝ).restrict Work.Spaces.Iθ) :=
    (MeasureTheory.AEStronglyMeasurable.div₀
        (huc.aestronglyMeasurable Iθ_measurable)
        (Real.continuous_cos.measurable.aestronglyMeasurable)).pow 2
      |>.mul (((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 2 - γ)).measurable.comp
        (Real.continuous_sin.measurable.comp
          (continuous_const.mul continuous_id).measurable)).aestronglyMeasurable)
  refine MeasureTheory.IntegrableOn.of_bound Iθ_volume_lt_top haesm (100 * M) ?_
  filter_upwards [Work.FTS.EllipticEst.remov.ae_mem_Ioo_Iθ_R] with θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have h1 : (u θ / Real.cos θ) ^ 2 ≤ 100 * M := by
    have h := Work.FTS.EllipticEst.remov.div_cos_sq_le_M u hu2 huc hu0 hupi h2 θ hθ
    rwa [← hM] at h
  have hw1 : 0 ≤ Real.rpow (Real.sin (2 * θ)) (2 - γ) := rpow_two_sub_gam_nonneg hθI
  have hwle : Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ 1 := rpow_two_sub_gam_le_one hγ2 hθI
  have hnn : 0 ≤ (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
    mul_nonneg (sq_nonneg _) hw1
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  calc (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
      ≤ (100 * M) * Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
        mul_le_mul_of_nonneg_right h1 hw1
    _ ≤ (100 * M) * 1 := mul_le_mul_of_nonneg_left hwle (by linarith)
    _ = 100 * M := by ring

/-- **Conjunct 2**: `(∂_θ(u/cos θ))² sin(2θ)^{4-γ}` is integrable on `Iθ`
(the integrability component of `slice5_vweight_le`). -/
private lemma sliceStep5_integrable_V1 (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2)
    {u : ℝ → ℝ}
    (hu2 : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (huc : ContinuousOn u (Set.Icc 0 (Real.pi / 2)))
    (hu0 : u 0 = 0) (hupi : u (Real.pi / 2) = 0)
    (h2 : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ)
    (h1 : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ)
    (h0 : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ := by
  obtain ⟨_C, _hC, hv⟩ := Work.FTS.EllipticEst.remov.slice5_vweight_le γ hγ1 hγ2
  exact (hv u hu2 huc hu0 hupi h2 h1 h0).2.1

/-- The `v`-form of the pointwise identity for `g`: `g = -u'' + sin θ · v' - 5 cos θ · v`
with `v = u / cos θ`. -/
private lemma g_eq_v_form {u g : ℝ → ℝ}
    (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      g θ = -(deriv (deriv u) θ) + Real.sin θ * deriv (fun t => u t / Real.cos t) θ
        - 5 * Real.cos θ * (u θ / Real.cos θ) := by
  intro θ hθ
  have hgp := Work.FTS.EllipticEst.remov.g_pointwise_ident u g (hu.of_le (by norm_num))
    hode θ hθ
  have hv := Work.FTS.EllipticEst.remov.slice5_v_rel_one u hu θ hθ
  have hcos : Real.cos θ ≠ 0 := (Work.FTS.EllipticEst.remov.cos_pos_of_mem_Ioo hθ).ne'
  rw [hgp, hv]
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  ring

/-- **Conjunct 3**: `(g)² sin(2θ)^{4-γ}` is integrable on `Iθ`.  Pointwise,
`g = -u'' + (sin θ v' - 5 cos θ v)`, hence `g² ψ ≤ 2 (u'')² sEta + 4 (v')² ψ + 100 u²`
(the first by `ψ ≤ sEta`, the third because `cos θ · v = u` and `ψ ≤ 1`). -/
private lemma sliceStep5_integrable_G0 (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2)
    {u g : ℝ → ℝ}
    (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ)
    (h2 : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ)
    (h0 : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ)
    (hv1 : MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ := by
  have hgid := g_eq_v_form hu hode
  have hdom : MeasureTheory.IntegrableOn (fun θ => 2 * ((deriv (deriv u) θ) ^ 2 *
        Work.FTS.EllipticEst.sEta θ)
      + 4 * ((deriv (fun t => u t / Real.cos t) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ))
      + 100 * (u θ) ^ 2) Work.Spaces.Iθ :=
    ((h2.const_mul 2).add (hv1.const_mul 4)).add (h0.const_mul 100)
  refine MeasureTheory.Integrable.mono hdom ?_ ?_
  · have hwcont : ContinuousOn (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (4 - γ))
        (Set.Ioo 0 (Real.pi / 2)) :=
      ((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 4 - γ)).comp
        (Real.continuous_sin.comp (continuous_const.mul continuous_id))).continuousOn
    have hψc : ContinuousOn (fun θ : ℝ => u θ / Real.cos θ) (Set.Ioo 0 (Real.pi / 2)) :=
      hu.continuousOn.div Real.continuous_cos.continuousOn
        (fun t ht => (Work.FTS.EllipticEst.remov.cos_pos_of_mem_Ioo ht).ne')
    have hψ2 : ContDiffOn ℝ 2 (fun θ : ℝ => u θ / Real.cos θ) (Set.Ioo 0 (Real.pi / 2)) :=
      (hu.of_le (by norm_num)).div Real.contDiff_cos.contDiffOn
        (fun t ht => (Work.FTS.EllipticEst.remov.cos_pos_of_mem_Ioo ht).ne')
    have hψ' : ContinuousOn (fun θ : ℝ => deriv (fun t => u t / Real.cos t) θ)
        (Set.Ioo 0 (Real.pi / 2)) :=
      (contDiffOn_deriv_of_le_w (m := 1) isOpen_Ioo hψ2 (by norm_num)).continuousOn
    have hu2c : ContinuousOn (fun θ : ℝ => deriv (deriv u) θ) (Set.Ioo 0 (Real.pi / 2)) := by
      have h3 : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)) := hu.of_le (by norm_num)
      have h2' : ContDiffOn ℝ 2 (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
        contDiffOn_deriv_of_le_w (m := 2) isOpen_Ioo h3 (by norm_num)
      exact (contDiffOn_deriv_of_le_w (m := 1) isOpen_Ioo h2' (by norm_num)).continuousOn
    have hbase : ContinuousOn (fun θ : ℝ => -(deriv (deriv u) θ)
          + Real.sin θ * deriv (fun t => u t / Real.cos t) θ
          - 5 * Real.cos θ * (u θ / Real.cos θ)) (Set.Ioo 0 (Real.pi / 2)) :=
      (hu2c.neg.add (Real.continuous_sin.continuousOn.mul hψ')).sub
        ((continuous_const.continuousOn.mul Real.continuous_cos.continuousOn).mul hψc)
    refine MeasureTheory.AEStronglyMeasurable.congr
      ((aesm_of_continuousOn_Ioo (hbase.pow 2)).mul (aesm_of_continuousOn_Ioo hwcont)) ?_
    filter_upwards [Work.FTS.EllipticEst.remov.ae_mem_Ioo_Iθ_R] with θ hθ
    show (-(deriv (deriv u) θ) + Real.sin θ * deriv (fun t => u t / Real.cos t) θ
        - 5 * Real.cos θ * (u θ / Real.cos θ)) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)
      = (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)
    rw [hgid θ hθ]
  · filter_upwards [Work.FTS.EllipticEst.remov.ae_mem_Ioo_Iθ_R] with θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hψnn : 0 ≤ Real.rpow (Real.sin (2 * θ)) (4 - γ) :=
      Work.FTS.EllipticEst.remov.sig4_nonneg_R γ hθI
    have hψle1 : Real.rpow (Real.sin (2 * θ)) (4 - γ) ≤ 1 :=
      Real.rpow_le_one (sin_two_nonneg_Iθ_prv hθI) (Real.sin_le_one _) (by linarith)
    have hψleEta : Real.rpow (Real.sin (2 * θ)) (4 - γ) ≤ Work.FTS.EllipticEst.sEta θ :=
      Work.FTS.EllipticEst.remov.sig4_le_sEta_R γ hγ1 hγ2 hθI
    have hS2 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
    have hCv : Real.cos θ * (u θ / Real.cos θ) = u θ :=
      Work.FTS.EllipticEst.remov.cos_mul_cbV hθ
    have hEta0 : 0 ≤ Work.FTS.EllipticEst.sEta θ := sEta_nonneg_Iθ' hθI
    set W : ℝ := Real.rpow (Real.sin (2 * θ)) (4 - γ) with hWdef
    have hWnn : 0 ≤ W := by rw [hWdef]; exact hψnn
    have hWleEta : W ≤ Work.FTS.EllipticEst.sEta θ := by rw [hWdef]; exact hψleEta
    have hWle1 : W ≤ 1 := by rw [hWdef]; exact hψle1
    have hA : (deriv (deriv u) θ) ^ 2 * W ≤ (deriv (deriv u) θ) ^ 2 *
        Work.FTS.EllipticEst.sEta θ :=
      mul_le_mul_of_nonneg_left hWleEta (sq_nonneg _)
    have hB : (Real.sin θ ^ 2 * (deriv (fun t => u t / Real.cos t) θ) ^ 2) * W
        ≤ (deriv (fun t => u t / Real.cos t) θ) ^ 2 * W := by
      have hc : 0 ≤ (deriv (fun t => u t / Real.cos t) θ) ^ 2 * W :=
        mul_nonneg (sq_nonneg _) hWnn
      have h := mul_le_mul_of_nonneg_right hS2 hc
      simpa [mul_assoc] using h
    have hC : (25 * (Real.cos θ * (u θ / Real.cos θ)) ^ 2) * W ≤ 25 * (u θ) ^ 2 := by
      rw [hCv]
      have h25 : 0 ≤ (25 : ℝ) * (u θ) ^ 2 := by positivity
      calc (25 * (u θ) ^ 2) * W ≤ (25 * (u θ) ^ 2) * 1 :=
            mul_le_mul_of_nonneg_left hWle1 h25
        _ = 25 * (u θ) ^ 2 := by ring
    have hsq : (g θ) ^ 2 ≤ 2 * (deriv (deriv u) θ) ^ 2
        + 2 * (Real.sin θ * deriv (fun t => u t / Real.cos t) θ
            - 5 * Real.cos θ * (u θ / Real.cos θ)) ^ 2 := by
      rw [hgid θ hθ]
      nlinarith [sq_nonneg (deriv (deriv u) θ
        + (Real.sin θ * deriv (fun t => u t / Real.cos t) θ
          - 5 * Real.cos θ * (u θ / Real.cos θ)))]
    have hsq2 : (Real.sin θ * deriv (fun t => u t / Real.cos t) θ
        - 5 * Real.cos θ * (u θ / Real.cos θ)) ^ 2
        ≤ 2 * (Real.sin θ ^ 2 * (deriv (fun t => u t / Real.cos t) θ) ^ 2)
          + 2 * (25 * (Real.cos θ * (u θ / Real.cos θ)) ^ 2) := by
      nlinarith [sq_nonneg (Real.sin θ * deriv (fun t => u t / Real.cos t) θ
        + 5 * Real.cos θ * (u θ / Real.cos θ))]
    have h1 : (g θ) ^ 2 * W ≤ (2 * (deriv (deriv u) θ) ^ 2
          + 2 * (Real.sin θ * deriv (fun t => u t / Real.cos t) θ
            - 5 * Real.cos θ * (u θ / Real.cos θ)) ^ 2) * W :=
      mul_le_mul_of_nonneg_right hsq hWnn
    have h2 : (2 * (deriv (deriv u) θ) ^ 2
          + 2 * (Real.sin θ * deriv (fun t => u t / Real.cos t) θ
            - 5 * Real.cos θ * (u θ / Real.cos θ)) ^ 2) * W
        ≤ 2 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + 4 * ((deriv (fun t => u t / Real.cos t) θ) ^ 2 * W)
          + 100 * (u θ) ^ 2 := by
      have hZ : (Real.sin θ * deriv (fun t => u t / Real.cos t) θ
            - 5 * Real.cos θ * (u θ / Real.cos θ)) ^ 2 * W
          ≤ (2 * (Real.sin θ ^ 2 * (deriv (fun t => u t / Real.cos t) θ) ^ 2)
            + 2 * (25 * (Real.cos θ * (u θ / Real.cos θ)) ^ 2)) * W :=
        mul_le_mul_of_nonneg_right hsq2 hWnn
      nlinarith [hA, hB, hC, hZ]
    have hfinal : (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)
        ≤ 2 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + 4 * ((deriv (fun t => u t / Real.cos t) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
          + 100 * (u θ) ^ 2 := by
      rw [← hWdef]
      linarith [h1, h2]
    have hnn : 0 ≤ (g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ) :=
      mul_nonneg (sq_nonneg _) hψnn
    have hnn2 : 0 ≤ 2 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + 4 * ((deriv (fun t => u t / Real.cos t) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
          + 100 * (u θ) ^ 2 :=
      add_nonneg (add_nonneg (mul_nonneg (by norm_num)
        (mul_nonneg (sq_nonneg _) hEta0))
        (mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) hψnn))) (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, Real.norm_eq_abs, abs_of_nonneg hnn2]
    exact hfinal

/-! ## Part 2. The fourth conjunct `(∂_θ g)² sin(2θ)^{2-γ}` -/

/-- `∂_θ g` equals the explicit `gE u` on `(0, π/2)`. -/
private lemma deriv_g_eq_gE {u g : ℝ → ℝ}
    (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), deriv g θ = gE u θ := by
  intro θ hθ
  have h := (sliceStep5gDerivIdents u g hu hode).2 θ hθ
  rw [h]
  rfl

/-- `Iθ` splits at `π/2 - 1/8`. -/
private lemma Icc_split_pi_half :
    Set.Icc (0 : ℝ) (Real.pi / 2 - 1 / 8) ∪ Set.Icc (Real.pi / 2 - 1 / 8) (Real.pi / 2)
      = Set.Icc (0 : ℝ) (Real.pi / 2) := by
  ext x
  simp only [Set.mem_union, Set.mem_Icc]
  constructor
  · rintro (h | h) <;> exact ⟨by linarith [h.1, Real.pi_gt_three], by linarith [h.2]⟩
  · intro h
    by_cases hx : x ≤ Real.pi / 2 - 1 / 8
    · exact Or.inl ⟨h.1, hx⟩
    · exact Or.inr ⟨(not_le.mp hx).le, h.2⟩

/-- **The pointwise bound on `[0, π/2-1/8]`.**  There `|tan θ| ≤ 8`, so
`(g')² ≤ 4 ((u''')² + 64 (u'')² + 132² (u')² + 1040² u²)`; multiplying by the weight and
using `sin(2θ)^{2-γ} ≤ sEta`, `sin(2θ)^{2-γ} ≤ 1` gives the claim. -/
private lemma regionA_pointwise (γ : ℝ) (hγ2 : γ ≤ 3 / 2) {u g : ℝ → ℝ}
    (hg' : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), deriv g θ = gE u θ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2 - 1 / 8)) :
    (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
      ≤ 4 * ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
          + 64 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + 132 ^ 2 * (deriv u θ) ^ 2
          + 1040 ^ 2 * (u θ) ^ 2) := by
  have hθI : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ.1, by linarith [hθ.2]⟩
  have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hWnn : 0 ≤ Real.rpow (Real.sin (2 * θ)) (2 - γ) := rpow_two_sub_gam_nonneg hθIθ
  have hW1 : Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ 1 := rpow_two_sub_gam_le_one hγ2 hθIθ
  have hWEta : Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ Work.FTS.EllipticEst.sEta θ :=
    rpow_two_sub_gam_le_sEta hγ2 hθIθ
  have hEta0 : 0 ≤ Work.FTS.EllipticEst.sEta θ := sEta_nonneg_Iθ' hθIθ
  have hT8 : |Real.tan θ| ≤ 8 := abs_tan_le_eight hθ
  have hT2 : Real.tan θ ^ 2 ≤ 64 := by
    have h : |Real.tan θ| ^ 2 ≤ (8 : ℝ) ^ 2 := by
      nlinarith [abs_nonneg (Real.tan θ), hT8]
    rwa [sq_abs, show (8 : ℝ) ^ 2 = 64 by norm_num] at h
  have hT4 : (2 * Real.tan θ ^ 2 - 4) ^ 2 ≤ 132 ^ 2 := by
    have h : |2 * Real.tan θ ^ 2 - 4| ≤ 132 := by
      refine abs_le.mpr ⟨by linarith [sq_nonneg (Real.tan θ)], by linarith⟩
    rw [← sq_abs (2 * Real.tan θ ^ 2 - 4)]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hT6 : (2 * Real.tan θ ^ 3 + 2 * Real.tan θ) ^ 2 ≤ 1040 ^ 2 := by
    have h : |2 * Real.tan θ ^ 3 + 2 * Real.tan θ| ≤ 1040 := by
      have h1 : |Real.tan θ ^ 3| ≤ 512 := by
        have h2 : |Real.tan θ| ^ 3 ≤ (8 : ℝ) ^ 3 :=
          pow_le_pow_left₀ (abs_nonneg _) hT8 3
        rw [abs_pow]
        have h3 : (8 : ℝ) ^ 3 = 512 := by norm_num
        linarith [h2, h3]
      calc |2 * Real.tan θ ^ 3 + 2 * Real.tan θ|
          ≤ |2 * Real.tan θ ^ 3| + |2 * Real.tan θ| := abs_add_le _ _
        _ = 2 * |Real.tan θ ^ 3| + 2 * |Real.tan θ| := by
            rw [abs_mul, abs_mul]; norm_num
        _ ≤ 2 * 512 + 2 * 8 := by linarith
        _ = 1040 := by norm_num
    rw [← sq_abs (2 * Real.tan θ ^ 3 + 2 * Real.tan θ)]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  -- the four-term square bound
  have hsq := Work.FTS.EllipticEst.remov.add_sq_le_four
    (-(deriv (deriv (deriv u)) θ)) (Real.tan θ * deriv (deriv u) θ)
    ((2 * Real.tan θ ^ 2 - 4) * deriv u θ)
    ((2 * Real.tan θ ^ 3 + 2 * Real.tan θ) * u θ)
  have hsq' : (-(deriv (deriv (deriv u)) θ) + Real.tan θ * deriv (deriv u) θ
      + (2 * Real.tan θ ^ 2 - 4) * deriv u θ
      + (2 * Real.tan θ ^ 3 + 2 * Real.tan θ) * u θ) ^ 2
      ≤ 4 * ((deriv (deriv (deriv u)) θ) ^ 2 + (Real.tan θ * deriv (deriv u) θ) ^ 2
        + ((2 * Real.tan θ ^ 2 - 4) * deriv u θ) ^ 2
        + ((2 * Real.tan θ ^ 3 + 2 * Real.tan θ) * u θ) ^ 2) := by
    simpa only [neg_sq] using hsq
  rw [hg' θ hθI]
  simp only [gE]
  have hterm1 : (deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
      ≤ (deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ) := le_rfl
  have hterm2 : (Real.tan θ * deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
      ≤ 64 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    have h1 : (Real.tan θ * deriv (deriv u) θ) ^ 2 ≤ 64 * (deriv (deriv u) θ) ^ 2 := by
      nlinarith [hT2, sq_nonneg (deriv (deriv u) θ)]
    calc (Real.tan θ * deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        ≤ (64 * (deriv (deriv u) θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
          mul_le_mul_of_nonneg_right h1 hWnn
      _ = 64 * ((deriv (deriv u) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)) := by ring
      _ ≤ 64 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hWEta (sq_nonneg _))
            (by norm_num)
  have hterm3 : ((2 * Real.tan θ ^ 2 - 4) * deriv u θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ 132 ^ 2 * (deriv u θ) ^ 2 := by
    have h1 : ((2 * Real.tan θ ^ 2 - 4) * deriv u θ) ^ 2
        ≤ 132 ^ 2 * (deriv u θ) ^ 2 := by
      nlinarith [hT4, sq_nonneg (deriv u θ)]
    calc ((2 * Real.tan θ ^ 2 - 4) * deriv u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        ≤ (132 ^ 2 * (deriv u θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
          mul_le_mul_of_nonneg_right h1 hWnn
      _ = 132 ^ 2 * ((deriv u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)) := by ring
      _ ≤ 132 ^ 2 * ((deriv u θ) ^ 2 * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW1 (sq_nonneg _))
            (by norm_num)
      _ = 132 ^ 2 * (deriv u θ) ^ 2 := by ring
  have hterm4 : ((2 * Real.tan θ ^ 3 + 2 * Real.tan θ) * u θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ 1040 ^ 2 * (u θ) ^ 2 := by
    have h1 : ((2 * Real.tan θ ^ 3 + 2 * Real.tan θ) * u θ) ^ 2
        ≤ 1040 ^ 2 * (u θ) ^ 2 := by
      nlinarith [hT6, sq_nonneg (u θ)]
    calc ((2 * Real.tan θ ^ 3 + 2 * Real.tan θ) * u θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 - γ)
        ≤ (1040 ^ 2 * (u θ) ^ 2) * Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
          mul_le_mul_of_nonneg_right h1 hWnn
      _ = 1040 ^ 2 * ((u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)) := by ring
      _ ≤ 1040 ^ 2 * ((u θ) ^ 2 * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW1 (sq_nonneg _))
            (by norm_num)
      _ = 1040 ^ 2 * (u θ) ^ 2 := by ring
  have hsum : (-(deriv (deriv (deriv u)) θ) + Real.tan θ * deriv (deriv u) θ
        + (2 * Real.tan θ ^ 2 - 4) * deriv u θ
        + (2 * Real.tan θ ^ 3 + 2 * Real.tan θ) * u θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)
      ≤ 4 * ((deriv (deriv (deriv u)) θ) ^ 2 + (Real.tan θ * deriv (deriv u) θ) ^ 2
        + ((2 * Real.tan θ ^ 2 - 4) * deriv u θ) ^ 2
        + ((2 * Real.tan θ ^ 3 + 2 * Real.tan θ) * u θ) ^ 2) *
        Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
    mul_le_mul_of_nonneg_right hsq' hWnn
  nlinarith [hsum, hterm1, hterm2, hterm3, hterm4, hWnn, hEta0]

/-- **Region A integrability**: on `[0, π/2-1/8]` the fourth integrand is dominated by
`4 ((u''')² sin(2θ)^{2-γ} + 64 (u'')² sEta + 132² (u')² + 1040² u²)`. -/
private lemma regionA_integrable (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {u g : ℝ → ℝ}
    (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hg' : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), deriv g θ = gE u θ)
    (h3 : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv u)) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ)
    (h2 : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ)
    (h1 : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ)
    (h0 : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => (deriv g θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) (Set.Icc 0 (Real.pi / 2 - 1 / 8)) := by
  have hsub : Set.Icc (0 : ℝ) (Real.pi / 2 - 1 / 8) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hIntA : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv u)) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) (Set.Icc 0 (Real.pi / 2 - 1 / 8)) :=
    h3.mono_set hsub
  have hIntB : MeasureTheory.IntegrableOn (fun θ => 64 * ((deriv (deriv u) θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ)) (Set.Icc 0 (Real.pi / 2 - 1 / 8)) :=
    (h2.mono_set hsub).const_mul 64
  have hIntC : MeasureTheory.IntegrableOn (fun θ => 132 ^ 2 * (deriv u θ) ^ 2)
      (Set.Icc 0 (Real.pi / 2 - 1 / 8)) :=
    (h1.mono_set hsub).const_mul (132 ^ 2)
  have hIntD : MeasureTheory.IntegrableOn (fun θ => 1040 ^ 2 * (u θ) ^ 2)
      (Set.Icc 0 (Real.pi / 2 - 1 / 8)) :=
    (h0.mono_set hsub).const_mul (1040 ^ 2)
  have hdom : MeasureTheory.IntegrableOn (fun θ => 4 *
      ((deriv (deriv (deriv u)) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        + 64 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        + 132 ^ 2 * (deriv u θ) ^ 2
        + 1040 ^ 2 * (u θ) ^ 2)) (Set.Icc 0 (Real.pi / 2 - 1 / 8)) :=
    (((hIntA.add hIntB).add hIntC).add hIntD).const_mul 4
  refine MeasureTheory.Integrable.mono hdom ?_ ?_
  · exact (((measurable_deriv g).pow_const 2).aestronglyMeasurable).mul
      (((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 2 - γ)).measurable.comp
        (Real.continuous_sin.measurable.comp
          (continuous_const.mul continuous_id).measurable)).aestronglyMeasurable)
  · filter_upwards [ae_mem_Ioo_of_Icc (a := (0 : ℝ)) (b := Real.pi / 2 - 1 / 8)]
      with θ hθ
    have hpt := regionA_pointwise γ hγ2 hg' hθ
    have hθIθ : θ ∈ Work.Spaces.Iθ :=
      ⟨le_of_lt hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    have hsin0 : 0 ≤ Real.sin (2 * θ) :=
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])).le
    have hnn : 0 ≤ (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin0 _)
    have hnn2 : 0 ≤ 4 * ((deriv (deriv (deriv u)) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 - γ)
        + 64 * ((deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        + 132 ^ 2 * (deriv u θ) ^ 2
        + 1040 ^ 2 * (u θ) ^ 2) := by
      refine mul_nonneg (by norm_num) (add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_)
      · exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin0 _)
      · exact mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) (sEta_nonneg_Iθ' hθIθ))
      · positivity
      · positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, Real.norm_eq_abs, abs_of_nonneg hnn2]
    exact hpt

/-- **Differentiability of `∂_θ g`** on the region near `π/2`, through the explicit
expression `gE u` (which is `C¹` there because `u ∈ C⁴`). -/
private lemma hasDerivAt_deriv_g {u g : ℝ → ℝ}
    (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hg' : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), deriv g θ = gE u θ) :
    ∀ θ ∈ Set.Ico (Real.pi / 2 - 1 / 8) (Real.pi / 2),
      HasDerivAt (deriv g) (deriv (deriv g) θ) θ := by
  intro θ hθ
  have hθI : θ ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [hθ.1, Real.pi_gt_three], hθ.2⟩
  have hcos : Real.cos θ ≠ 0 := (Work.FTS.EllipticEst.remov.cos_pos_of_mem_Ioo hθI).ne'
  have h4 : ContDiffAt ℝ 4 u θ := hu.contDiffAt (isOpen_Ioo.mem_nhds hθI)
  have hu3 : ContDiffAt ℝ 3 (deriv u) θ :=
    Work.FTS.EllipticEst.remov.contDiffAt_deriv_of_le_w (m := 3) h4 (by norm_num)
  have hu2 : ContDiffAt ℝ 2 (deriv (deriv u)) θ :=
    Work.FTS.EllipticEst.remov.contDiffAt_deriv_of_le_w (m := 2) hu3 (by norm_num)
  have hu1 : ContDiffAt ℝ 1 (deriv (deriv (deriv u))) θ :=
    Work.FTS.EllipticEst.remov.contDiffAt_deriv_of_le_w (m := 1) hu2 (by norm_num)
  have hA : DifferentiableAt ℝ (fun t => deriv (deriv (deriv u)) t) θ :=
    hu1.differentiableAt (by norm_num)
  have hB : DifferentiableAt ℝ (fun t => deriv (deriv u) t) θ :=
    hu2.differentiableAt (by norm_num)
  have hC : DifferentiableAt ℝ (fun t => deriv u t) θ :=
    hu3.differentiableAt (by norm_num)
  have hD : DifferentiableAt ℝ u θ := h4.differentiableAt (by norm_num)
  have hT : DifferentiableAt ℝ Real.tan θ := Real.differentiableAt_tan.mpr hcos
  have hdE : DifferentiableAt ℝ (gE u) θ := by
    show DifferentiableAt ℝ (fun t => -deriv (deriv (deriv u)) t
      + Real.tan t * deriv (deriv u) t + (2 * Real.tan t ^ 2 - 4) * deriv u t
      + (2 * Real.tan t ^ 3 + 2 * Real.tan t) * u t) θ
    exact (((hA.neg).add (hT.mul hB)).add ((((hT.pow 2).const_mul 2).sub
      (differentiableAt_const 4)).mul hC)).add
      ((((hT.pow 3).const_mul 2).add (hT.const_mul 2)).mul hD)
  have hEv : deriv g =ᶠ[𝓝 θ] gE u := by
    filter_upwards [isOpen_Ioo.mem_nhds hθI] with t ht
    exact hg' t ht
  exact ((hEv.differentiableAt_iff).mpr hdE).hasDerivAt

/-- Weighted AM–GM: `2|ab| d^{p+1} ≤ a² d^p + b² d^{p+2}` for `d > 0`. -/
private lemma amgm_weighted {p d a b : ℝ} (hd : 0 < d) :
    2 * (|a * b| * d ^ (p + 1)) ≤ a ^ 2 * d ^ p + b ^ 2 * d ^ (p + 2) := by
  have h1 : d ^ (p + 1) = d ^ (p / 2) * d ^ (p / 2 + 1) := by
    rw [← Real.rpow_add hd]; congr 1; ring
  have h2 : (|a| * d ^ (p / 2)) ^ 2 = a ^ 2 * d ^ p := by
    rw [mul_pow, sq_abs, sq, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hd)]
    congr 1; ring
  have h3 : (|b| * d ^ (p / 2 + 1)) ^ 2 = b ^ 2 * d ^ (p + 2) := by
    rw [mul_pow, sq_abs, sq, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hd)]
    congr 1; ring
  have h4 : 2 * (|a * b| * d ^ (p + 1))
      = 2 * (|a| * d ^ (p / 2)) * (|b| * d ^ (p / 2 + 1)) := by
    rw [h1, abs_mul]; ring
  have h5 : 2 * (|a| * d ^ (p / 2)) * (|b| * d ^ (p / 2 + 1))
      ≤ (|a| * d ^ (p / 2)) ^ 2 + (|b| * d ^ (p / 2 + 1)) ^ 2 := by
    nlinarith [sq_nonneg (|a| * d ^ (p / 2) - |b| * d ^ (p / 2 + 1))]
  rw [h2, h3, ← h4] at h5
  exact h5

/-- **Weighted Hardy inequality near `π/2`** (form used for conjunct 4).  For `α > 0`,
`f` continuous on `(π/2-ε, π/2)` with continuous derivative `f'` there and
`f'²(π/2-θ)^{α+2}` integrable,

  `∫_{π/2-ε}^{π/2} f²(π/2-θ)^α ≤ (1/α)(∫ f'²(π/2-θ)^{α+2} + ε^{α+1} f(π/2-ε)²)`.

The proof integrates `(f²(π/2-θ)^{α+1})' = 2ff'(π/2-θ)^{α+1} - (α+1)f²(π/2-θ)^α` over
`[c,t]` (`c = π/2-ε`, `t < π/2`), drops the nonnegative boundary term at `t` and uses
`2|ff'|(π/2-θ)^{α+1} ≤ f²(π/2-θ)^α + f'²(π/2-θ)^{α+2}`; the passage from the truncated
intervals to the whole one is done with the `AECover` machinery. -/
private lemma hardy_local {α : ℝ} (hα : 0 < α) {f f' : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hfcont : ContinuousOn f (Set.Ico (Real.pi / 2 - ε) (Real.pi / 2)))
    (hf'cont : ContinuousOn f' (Set.Ico (Real.pi / 2 - ε) (Real.pi / 2)))
    (hderiv : ∀ θ ∈ Set.Ico (Real.pi / 2 - ε) (Real.pi / 2), HasDerivAt f (f' θ) θ)
    (hint : MeasureTheory.IntegrableOn (fun θ => f' θ ^ 2 * (Real.pi / 2 - θ) ^ (α + 2))
      (Set.Icc (Real.pi / 2 - ε) (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun θ => f θ ^ 2 * (Real.pi / 2 - θ) ^ α)
        (Set.Icc (Real.pi / 2 - ε) (Real.pi / 2)) ∧
      (∫ θ in (Real.pi / 2 - ε)..(Real.pi / 2), f θ ^ 2 * (Real.pi / 2 - θ) ^ α)
        ≤ 1 / α * ((∫ θ in (Real.pi / 2 - ε)..(Real.pi / 2),
              f' θ ^ 2 * (Real.pi / 2 - θ) ^ (α + 2))
          + ε ^ (α + 1) * (f (Real.pi / 2 - ε)) ^ 2) := by
  set c : ℝ := Real.pi / 2 - ε with hcdef
  have hcle : c ≤ Real.pi / 2 := by simp only [hcdef]; linarith
  have hclt : c < Real.pi / 2 := by simp only [hcdef]; linarith
  have hcε : Real.pi / 2 - c = ε := by simp only [hcdef]; ring
  set u : ℝ → ℝ := fun θ => f θ ^ 2 * (Real.pi / 2 - θ) ^ α with hudef
  set B : ℝ := ∫ θ in c..Real.pi / 2, f' θ ^ 2 * (Real.pi / 2 - θ) ^ (α + 2) with hBdef
  set K : ℝ := 1 / α * (B + ε ^ (α + 1) * (f c) ^ 2) with hKdef
  have hwIoc : MeasureTheory.IntegrableOn
      (fun θ => f' θ ^ 2 * (Real.pi / 2 - θ) ^ (α + 2)) (Set.Ioc c (Real.pi / 2)) :=
    hint.mono_set (fun x hx => ⟨hx.1.le, hx.2⟩)
  -- ### the truncated bound
  have htrunc : ∀ t ∈ Set.Ico c (Real.pi / 2), ∫ θ in c..t, u θ ≤ K := by
    intro t ht
    have hct : c ≤ t := ht.1
    have htlt : t < Real.pi / 2 := ht.2
    have hUI : Set.uIcc c t = Set.Icc c t := Set.uIcc_of_le hct
    have mkInt : ∀ (g : ℝ → ℝ), ContinuousOn g (Set.Icc c t) →
        IntervalIntegrable g volume c t :=
      fun g hg => (hUI.symm ▸ hg).intervalIntegrable
    have hsub : Set.Icc c t ⊆ Set.Ico c (Real.pi / 2) := fun x hx =>
      ⟨hx.1, lt_of_le_of_lt hx.2 htlt⟩
    have hdt : ∀ θ ∈ Set.Icc c t, 0 < Real.pi / 2 - θ := fun θ hθ => by linarith [hθ.2, htlt]
    have hpow : ∀ β : ℝ, ContinuousOn (fun θ : ℝ => (Real.pi / 2 - θ) ^ β) (Set.Icc c t) := by
      intro β
      exact (continuous_const.sub continuous_id).continuousOn.rpow_const
        (fun x hx => Or.inl (ne_of_gt (hdt x hx)))
    have hucont : ContinuousOn u (Set.Icc c t) := by
      rw [hudef]
      exact ((hfcont.mono hsub).pow 2).mul (hpow α)
    have hH'cont : ContinuousOn (fun θ : ℝ => 2 * (f θ * f' θ) * (Real.pi / 2 - θ) ^ (α + 1)
        - (α + 1) * (f θ ^ 2 * (Real.pi / 2 - θ) ^ α)) (Set.Icc c t) :=
      ((((hfcont.mono hsub).mul (hf'cont.mono hsub)).const_mul 2).mul (hpow (α + 1))).sub
        ((((hfcont.mono hsub).pow 2).mul (hpow α)).const_mul (α + 1))
    have hHderiv : ∀ x ∈ Set.uIcc c t,
        HasDerivAt (fun θ : ℝ => f θ ^ 2 * (Real.pi / 2 - θ) ^ (α + 1))
          (2 * (f x * f' x) * (Real.pi / 2 - x) ^ (α + 1)
            - (α + 1) * (f x ^ 2 * (Real.pi / 2 - x) ^ α)) x := by
      intro x hx
      rw [Set.uIcc_of_le hct] at hx
      have hxlt : x < Real.pi / 2 := lt_of_le_of_lt hx.2 htlt
      have hxa : HasDerivAt f (f' x) x := hderiv x ⟨hx.1, hxlt⟩
      have hd : Real.pi / 2 - x ≠ 0 := by linarith
      have hd2 : HasDerivAt (fun θ : ℝ => Real.pi / 2 - θ) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub (Real.pi / 2)
      have hprod := (hxa.pow 2).mul (hd2.rpow_const (p := α + 1) (Or.inl hd))
      convert hprod using 1
      · simp only [Pi.pow_apply]; ring_nf
    have hFTC : ∫ θ in c..t, (2 * (f θ * f' θ) * (Real.pi / 2 - θ) ^ (α + 1)
        - (α + 1) * (f θ ^ 2 * (Real.pi / 2 - θ) ^ α))
        = f t ^ 2 * (Real.pi / 2 - t) ^ (α + 1) - f c ^ 2 * (Real.pi / 2 - c) ^ (α + 1) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hHderiv (mkInt _ hH'cont)
    have hInt_ff' : IntervalIntegrable
        (fun θ : ℝ => f θ * f' θ * (Real.pi / 2 - θ) ^ (α + 1)) volume c t :=
      mkInt _ (((hfcont.mono hsub).mul (hf'cont.mono hsub)).mul (hpow (α + 1)))
    have hInt_u : IntervalIntegrable u volume c t := mkInt _ hucont
    have hInt_w : IntervalIntegrable (fun θ : ℝ => f' θ ^ 2 * (Real.pi / 2 - θ) ^ (α + 2))
        volume c t := mkInt _ (((hf'cont.mono hsub).pow 2).mul (hpow (α + 2)))
    have hsplit : (α + 1) * (∫ θ in c..t, u θ)
        = 2 * (∫ θ in c..t, f θ * f' θ * (Real.pi / 2 - θ) ^ (α + 1))
          + f c ^ 2 * (Real.pi / 2 - c) ^ (α + 1)
          - f t ^ 2 * (Real.pi / 2 - t) ^ (α + 1) := by
      have hcongr : ∫ θ in c..t, (2 * (f θ * f' θ) * (Real.pi / 2 - θ) ^ (α + 1)
            - (α + 1) * (f θ ^ 2 * (Real.pi / 2 - θ) ^ α))
          = ∫ θ in c..t, (2 * (f θ * f' θ * (Real.pi / 2 - θ) ^ (α + 1))
            - (α + 1) * u θ) :=
        intervalIntegral.integral_congr fun θ _ => by rw [hudef]; ring
      rw [hcongr, intervalIntegral.integral_sub (hInt_ff'.const_mul 2)
          (hInt_u.const_mul (α + 1)),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hFTC
      linarith [hFTC]
    have hHt0 : 0 ≤ f t ^ 2 * (Real.pi / 2 - t) ^ (α + 1) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith) _)
    have hamgm : ∫ θ in c..t, |f θ * f' θ * (Real.pi / 2 - θ) ^ (α + 1)|
        ≤ (1 / 2) * ((∫ θ in c..t, u θ)
            + ∫ θ in c..t, f' θ ^ 2 * (Real.pi / 2 - θ) ^ (α + 2)) := by
      have h2 : IntervalIntegrable
          (fun θ : ℝ => (1 / 2) * (u θ + f' θ ^ 2 * (Real.pi / 2 - θ) ^ (α + 2))) volume c t :=
        ((hInt_u.add hInt_w).const_mul (1 / 2))
      have hpt : ∀ θ ∈ Set.Icc c t,
          |f θ * f' θ * (Real.pi / 2 - θ) ^ (α + 1)|
            ≤ (1 / 2) * (u θ + f' θ ^ 2 * (Real.pi / 2 - θ) ^ (α + 2)) := by
        intro θ hθ
        have hd0 : 0 < Real.pi / 2 - θ := hdt θ hθ
        have hagg := amgm_weighted (p := α) hd0 (a := f θ) (b := f' θ)
        have h3 : |f θ * f' θ * (Real.pi / 2 - θ) ^ (α + 1)|
            = |f θ * f' θ| * (Real.pi / 2 - θ) ^ (α + 1) := by
          rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hd0.le _)]
        rw [h3, hudef]
        linarith [hagg]
      have h1 : ∫ θ in c..t, |f θ * f' θ * (Real.pi / 2 - θ) ^ (α + 1)|
          ≤ ∫ θ in c..t, (1 / 2) * (u θ + f' θ ^ 2 * (Real.pi / 2 - θ) ^ (α + 2)) :=
        intervalIntegral.integral_mono_on hct
          (mkInt _ ((((hfcont.mono hsub).mul (hf'cont.mono hsub)).mul (hpow (α + 1))).abs))
          h2 hpt
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hInt_u hInt_w] at h1
      linarith [h1]
    have hmain : (α + 1) * (∫ θ in c..t, u θ)
        ≤ 2 * ((1 / 2) * ((∫ θ in c..t, u θ)
            + ∫ θ in c..t, f' θ ^ 2 * (Real.pi / 2 - θ) ^ (α + 2)))
          + f c ^ 2 * (Real.pi / 2 - c) ^ (α + 1) := by
      have habs : IntervalIntegrable
          (fun θ : ℝ => |f θ * f' θ * (Real.pi / 2 - θ) ^ (α + 1)|) volume c t :=
        mkInt _ ((((hfcont.mono hsub).mul (hf'cont.mono hsub)).mul (hpow (α + 1))).abs)
      have h1 : ∫ θ in c..t, f θ * f' θ * (Real.pi / 2 - θ) ^ (α + 1)
          ≤ ∫ θ in c..t, |f θ * f' θ * (Real.pi / 2 - θ) ^ (α + 1)| :=
        intervalIntegral.integral_mono_on hct hInt_ff' habs (fun θ _ => le_abs_self _)
      linarith [hsplit, h1, hamgm, hHt0]
    have hwle : ∫ θ in c..t, f' θ ^ 2 * (Real.pi / 2 - θ) ^ (α + 2) ≤ B := by
      rw [hBdef, intervalIntegral.integral_of_le hcle, intervalIntegral.integral_of_le hct]
      refine setIntegral_mono_set hwIoc ?_ ?_
      · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
        refine Eventually.of_forall fun θ hθ => ?_
        exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith [hθ.2]) _)
      · exact Eventually.of_forall fun θ hθ =>
          ⟨hθ.1, le_trans hθ.2 (le_of_lt htlt)⟩
    have hcd : f c ^ 2 * (Real.pi / 2 - c) ^ (α + 1) = ε ^ (α + 1) * f c ^ 2 := by
      rw [hcε]; ring
    have hAc : ∫ θ in c..t, u θ ≤ 1 / α * (B + ε ^ (α + 1) * f c ^ 2) := by
      have hAc' : ∫ θ in c..t, u θ
          ≤ 1 / α * (B + f c ^ 2 * (Real.pi / 2 - c) ^ (α + 1)) := by
        have hbal : 2 * ((1 / 2) * ((∫ θ in c..t, u θ)
              + ∫ θ in c..t, f' θ ^ 2 * (Real.pi / 2 - θ) ^ (α + 2)))
            + f c ^ 2 * (Real.pi / 2 - c) ^ (α + 1)
            ≤ 2 * ((1 / 2) * ((∫ θ in c..t, u θ) + B))
              + f c ^ 2 * (Real.pi / 2 - c) ^ (α + 1) := by
          linarith [hwle]
        have hfin : α * (∫ θ in c..t, u θ)
            ≤ B + f c ^ 2 * (Real.pi / 2 - c) ^ (α + 1) := by linarith [hmain, hbal]
        rw [one_div, le_inv_mul_iff₀ hα]
        linarith [hfin]
      rw [hcd] at hAc'
      exact hAc'
    rw [hKdef, hBdef]
    exact hAc
  -- ### the AECover argument
  have hδtend : Tendsto (fun n : ℕ => Real.pi / 2 - ε / ((n : ℝ) + 1)) atTop (𝓝 (Real.pi / 2)) := by
    have h1 : Tendsto (fun n : ℕ => ε / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds)
    simpa using (tendsto_const_nhds (x := Real.pi / 2)).sub h1
  have hcover : AECover (volume.restrict (Set.Ioc c (Real.pi / 2))) atTop
      (fun n : ℕ => Set.Ioc c (Real.pi / 2 - ε / ((n : ℝ) + 1))) :=
    aecover_Ioc_of_Ioc (μ := volume) (A := c) (B := Real.pi / 2) tendsto_const_nhds hδtend
  have hmem : ∀ n : ℕ, Real.pi / 2 - ε / ((n : ℝ) + 1) ∈ Set.Ico c (Real.pi / 2) := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hden : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have hpos : 0 < ε / ((n : ℝ) + 1) := div_pos hε hden
    have hle : ε / ((n : ℝ) + 1) ≤ ε := by
      rw [div_le_iff₀ hden]; nlinarith
    refine ⟨?_, ?_⟩
    · simp only [hcdef]; linarith
    · linarith
  have hfi : ∀ n : ℕ, MeasureTheory.IntegrableOn u
      (Set.Ioc c (Real.pi / 2 - ε / ((n : ℝ) + 1)))
      (volume.restrict (Set.Ioc c (Real.pi / 2))) := by
    intro n
    have hbn : Real.pi / 2 - ε / ((n : ℝ) + 1) < Real.pi / 2 := (hmem n).2
    have hsub : Set.Icc c (Real.pi / 2 - ε / ((n : ℝ) + 1)) ⊆ Set.Ico c (Real.pi / 2) :=
      fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hbn⟩
    have hcu : ContinuousOn u (Set.Icc c (Real.pi / 2 - ε / ((n : ℝ) + 1))) := by
      rw [hudef]
      exact ((hfcont.mono hsub).pow 2).mul
        ((continuous_const.sub continuous_id).continuousOn.rpow_const
          (fun _ _ => Or.inr hα.le))
    have hI : MeasureTheory.IntegrableOn u (Set.Ioc c (Real.pi / 2 - ε / ((n : ℝ) + 1))) volume :=
      (hcu.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    show Integrable u ((volume.restrict (Set.Ioc c (Real.pi / 2))).restrict
      (Set.Ioc c (Real.pi / 2 - ε / ((n : ℝ) + 1))))
    have hsub2 : Set.Ioc c (Real.pi / 2 - ε / ((n : ℝ) + 1)) ⊆ Set.Ioc c (Real.pi / 2) :=
      fun x hx => ⟨hx.1, le_of_lt (lt_of_le_of_lt hx.2 hbn)⟩
    rw [Measure.restrict_restrict_of_subset hsub2]
    exact hI
  have hnng : 0 ≤ᵐ[volume.restrict (Set.Ioc c (Real.pi / 2))] u := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun θ hθ => ?_
    rw [hudef, Pi.zero_apply]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith [hθ.2]) _)
  have hbounded : ∀ᶠ n : ℕ in atTop,
      (∫ x in Set.Ioc c (Real.pi / 2 - ε / ((n : ℝ) + 1)), u x
        ∂(volume.restrict (Set.Ioc c (Real.pi / 2)))) ≤ K := by
    filter_upwards with n
    have hbn : Real.pi / 2 - ε / ((n : ℝ) + 1) < Real.pi / 2 := (hmem n).2
    have hsub : Set.Ioc c (Real.pi / 2 - ε / ((n : ℝ) + 1)) ⊆ Set.Ioc c (Real.pi / 2) :=
      fun x hx => ⟨hx.1, le_of_lt (lt_of_le_of_lt hx.2 hbn)⟩
    rw [Measure.restrict_restrict_of_subset hsub]
    rw [← intervalIntegral.integral_of_le (hmem n).1]
    exact htrunc _ (hmem n)
  have hInt : Integrable u (volume.restrict (Set.Ioc c (Real.pi / 2))) :=
    hcover.integrable_of_integral_bounded_of_nonneg_ae K hfi hnng hbounded
  have hle : ∫ x, u x ∂(volume.restrict (Set.Ioc c (Real.pi / 2))) ≤ K :=
    le_of_tendsto (hcover.integral_tendsto_of_countably_generated hInt) hbounded
  -- ### conclusion
  rw [hKdef, hBdef] at hle
  refine ⟨?_, ?_⟩
  · have h1 : MeasureTheory.IntegrableOn u (Set.Ioc c (Real.pi / 2)) volume := hInt
    have h2 := MeasureTheory.IntegrableOn.congr_set_ae h1
      (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := c) (b := Real.pi / 2)).symm
    simpa only [hudef] using h2
  · rw [show c = Real.pi / 2 - ε from hcdef, intervalIntegral.integral_of_le hcle]
    exact hle

/-- **Region B integrability**: on `[π/2-1/8, π/2]` the fourth integrand is controlled by
the weighted Hardy inequality `hardy_local` applied to `∂_θ g`, together with
`sin 2θ ≤ 2 (π/2 - θ)` and `(π/2 - θ) ≤ sin 2θ`. -/
private lemma regionB_integrable (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {u g : ℝ → ℝ}
    (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ)
    (hg' : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), deriv g θ = gE u θ)
    (hB : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv g) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => (deriv g θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) (Set.Icc (Real.pi / 2 - 1 / 8) (Real.pi / 2)) := by
  have hμ : (2 : ℝ) - γ + 2 = 4 - γ := by ring
  -- integrability of `(g'')² (π/2-θ)^{4-γ}`, by comparison with `(g'')² sin(2θ)^{4-γ}`
  have hBregion : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv g) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ))
      (Set.Icc (Real.pi / 2 - 1 / 8) (Real.pi / 2)) :=
    hB.mono_set (fun x hx => ⟨by linarith [hx.1, Real.pi_gt_three], hx.2⟩)
  have hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv g) θ) ^ 2 * (Real.pi / 2 - θ) ^ ((2 - γ) + 2))
      (Set.Icc (Real.pi / 2 - 1 / 8) (Real.pi / 2)) := by
    rw [hμ]
    refine MeasureTheory.Integrable.mono hBregion ?_ ?_
    · exact (((measurable_deriv (deriv g)).pow_const 2).aestronglyMeasurable).mul
        (((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 4 - γ)).measurable.comp
          (continuous_const.sub continuous_id).measurable)).aestronglyMeasurable
    · filter_upwards [ae_mem_Ioo_of_Icc (a := Real.pi / 2 - 1 / 8) (b := Real.pi / 2)]
        with θ hθ
      obtain ⟨hge, _hle⟩ := sin_two_between_pi_half ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hδ0 : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
      have hpow : (Real.pi / 2 - θ) ^ (4 - γ) ≤ Real.rpow (Real.sin (2 * θ)) (4 - γ) :=
        Real.rpow_le_rpow hδ0 hge (by linarith)
      have h1 : 0 ≤ (deriv (deriv g) θ) ^ 2 * (Real.pi / 2 - θ) ^ (4 - γ) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hδ0 _)
      have h2 : 0 ≤ (deriv (deriv g) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_trans hδ0 hge) _)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1, abs_of_nonneg h2]
      exact mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
  have hHardy : MeasureTheory.IntegrableOn
      (fun θ => (deriv g θ) ^ 2 * (Real.pi / 2 - θ) ^ (2 - γ))
      (Set.Icc (Real.pi / 2 - 1 / 8) (Real.pi / 2)) := by
    have hα : 0 < (2 : ℝ) - γ := by linarith
    -- regularity of `g`, `∂g` on the region, through `Lzero1 u`
    have hLz : ContDiffOn ℝ 2 (Work.FTS.EllipticEst.Lzero1 u) (Set.Ioo 0 (Real.pi / 2)) :=
      Work.FTS.EllipticEst.remov.SliceTopAux.contDiffOnLzero1 2 hu
    have hLz1 : ContDiffOn ℝ 1 (deriv (Work.FTS.EllipticEst.Lzero1 u))
        (Set.Ioo 0 (Real.pi / 2)) := hLz.deriv_of_isOpen isOpen_Ioo (by norm_num)
    have hLz2 : ContDiffOn ℝ 0 (deriv (deriv (Work.FTS.EllipticEst.Lzero1 u)))
        (Set.Ioo 0 (Real.pi / 2)) := hLz1.deriv_of_isOpen isOpen_Ioo (by norm_num)
    have hsub : Set.Ico (Real.pi / 2 - 1 / 8) (Real.pi / 2) ⊆ Set.Ioo 0 (Real.pi / 2) :=
      fun x hx => ⟨by linarith [hx.1, Real.pi_gt_three], hx.2⟩
    have hev1 : ∀ x ∈ Set.Ico (Real.pi / 2 - 1 / 8) (Real.pi / 2),
        deriv g x = deriv (Work.FTS.EllipticEst.Lzero1 u) x := by
      intro x hx
      have hx' : x ∈ Set.Ioo 0 (Real.pi / 2) := hsub hx
      have hev : Work.FTS.EllipticEst.Lzero1 u =ᶠ[𝓝 x] g := by
        filter_upwards [isOpen_Ioo.mem_nhds hx'] with t ht
        exact hode t ht
      exact hev.deriv_eq.symm
    have hev2 : ∀ x ∈ Set.Ico (Real.pi / 2 - 1 / 8) (Real.pi / 2),
        deriv (deriv g) x = deriv (deriv (Work.FTS.EllipticEst.Lzero1 u)) x := by
      intro x hx
      have hx' : x ∈ Set.Ioo 0 (Real.pi / 2) := hsub hx
      have hev : Work.FTS.EllipticEst.Lzero1 u =ᶠ[𝓝 x] g := by
        filter_upwards [isOpen_Ioo.mem_nhds hx'] with t ht
        exact hode t ht
      have h1 : deriv (Work.FTS.EllipticEst.Lzero1 u) =ᶠ[𝓝 x] deriv g := hev.deriv
      exact h1.deriv_eq.symm
    have hfcont : ContinuousOn (deriv g) (Set.Ico (Real.pi / 2 - 1 / 8) (Real.pi / 2)) :=
      (hLz1.continuousOn.mono hsub).congr fun x hx => hev1 x hx
    have hf'cont : ContinuousOn (deriv (deriv g)) (Set.Ico (Real.pi / 2 - 1 / 8) (Real.pi / 2)) :=
      (hLz2.continuousOn.mono hsub).congr fun x hx => hev2 x hx
    have hderivB : ∀ θ ∈ Set.Ico (Real.pi / 2 - 1 / 8) (Real.pi / 2),
        HasDerivAt (fun θ => deriv g θ) (deriv (deriv g) θ) θ := hasDerivAt_deriv_g hu hg'
    exact (hardy_local (α := 2 - γ) (f := fun θ => deriv g θ)
      (f' := fun θ => deriv (deriv g) θ) (ε := 1 / 8) hα (by norm_num)
      hfcont hf'cont hderivB hint).1
  refine MeasureTheory.Integrable.mono (hHardy.const_mul 4) ?_ ?_
  · exact (((measurable_deriv g).pow_const 2).aestronglyMeasurable).mul
      (((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 2 - γ)).measurable.comp
        (Real.continuous_sin.measurable.comp
          (continuous_const.mul continuous_id).measurable)).aestronglyMeasurable)
  · filter_upwards [ae_mem_Ioo_of_Icc (a := Real.pi / 2 - 1 / 8) (b := Real.pi / 2)]
      with θ hθ
    obtain ⟨hge, hle⟩ := sin_two_between_pi_half ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hs0 : 0 ≤ Real.sin (2 * θ) := le_trans (by linarith [hθ.2]) hge
    have hδ0 : 0 ≤ Real.pi / 2 - θ := by linarith [hθ.2]
    have h1 : Real.rpow (Real.sin (2 * θ)) (2 - γ)
        ≤ Real.rpow (2 * (Real.pi / 2 - θ)) (2 - γ) :=
      Real.rpow_le_rpow hs0 hle (by linarith)
    have h2 : Real.rpow (2 * (Real.pi / 2 - θ)) (2 - γ)
        = 2 ^ (2 - γ) * (Real.pi / 2 - θ) ^ (2 - γ) :=
      Real.mul_rpow (by norm_num) hδ0
    have h3 : (2 : ℝ) ^ (2 - γ) ≤ 4 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by linarith : (2 : ℝ) - γ ≤ 2)
      rw [Real.rpow_two] at h
      norm_num at h
      exact h
    have hL : 0 ≤ (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _)
    have hR : 0 ≤ 4 * ((deriv g θ) ^ 2 * (Real.pi / 2 - θ) ^ (2 - γ)) :=
      mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hδ0 _))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hL, abs_of_nonneg hR]
    calc (deriv g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        ≤ (deriv g θ) ^ 2 * Real.rpow (2 * (Real.pi / 2 - θ)) (2 - γ) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = (deriv g θ) ^ 2 * (2 ^ (2 - γ) * (Real.pi / 2 - θ) ^ (2 - γ)) := by rw [h2]
      _ ≤ (deriv g θ) ^ 2 * (4 * (Real.pi / 2 - θ) ^ (2 - γ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          nlinarith [h3, Real.rpow_nonneg hδ0 (2 - γ)]
      _ = 4 * ((deriv g θ) ^ 2 * (Real.pi / 2 - θ) ^ (2 - γ)) := by ring

theorem sliceStep5Integrable (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) (u g : ℝ → ℝ)
    (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (huc : ContinuousOn u (Set.Icc 0 (Real.pi / 2)))
    (hu0 : u 0 = 0) (hupi : u (Real.pi / 2) = 0)
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ)
    (h4 : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv (deriv u))) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ)
    (h3 : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv u)) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ)
    (h2 : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ)
    (h1 : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ)
    (h0 : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ)
    (hB : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv g) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn (fun θ => (deriv g θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ := by
  have hu2 : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)) := hu.of_le (by norm_num)
  have hV0 := sliceStep5_integrable_V0 γ hγ2 hu2 huc hu0 hupi h2
  have hV1 := sliceStep5_integrable_V1 γ hγ1 hγ2 hu2 huc hu0 hupi h2 h1 h0
  have hG0 := sliceStep5_integrable_G0 γ hγ1 hγ2 hu hode h2 h0 hV1
  refine ⟨hV0, hV1, hG0, ?_⟩
  have hu2 : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)) := hu.of_le (by norm_num)
  have hg' := deriv_g_eq_gE hu hode
  have hA_int := regionA_integrable γ hγ1 hγ2 hu hg' h3 h2 h1 h0
  have hB_int := regionB_integrable γ hγ1 hγ2 hu hode hg' hB
  have hunion := hA_int.union hB_int
  have hset : Set.Icc (0 : ℝ) (Real.pi / 2 - 1 / 8) ∪ Set.Icc (Real.pi / 2 - 1 / 8) (Real.pi / 2)
      = Work.Spaces.Iθ := by
    rw [Iθ_eq_icc, Icc_split_pi_half]
  rwa [hset] at hunion

end Work.FTS.EllipticEst.H2W
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.ESW.U_le_of_1d =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `U_le_of_1d`: the two-dimensional assembly of the one-dimensional top-slot estimate

Target: `Work.FTS.EllipticEst.TT.ESW.U_le_of_1d`.  Given the one-dimensional estimate `OneD k`
(the paper's §"General `ℋ^k` case" reduced to a single angular slice), the two-dimensional
statement follows by applying `OneD k` to the slices `u = Ψ z ·` (with source
`g = Gsl α F Ψ z · = Lzero1 (Ψ z ·)`, `z > 0`) for almost every `z`, and integrating in `z`.

## The three ingredients

* `Work.FTS.EllipticEst.Cores.Pieces.TopSlotIntegrability` (proved) supplies, for a.e. `z ∈ Iz`,
  the continuity of the slice on the closed angular interval together with the angular
  integrability of the six slots occurring in the hypotheses of `OneD k`.
* the pointwise inequality for a.e. `z` is the conclusion of `OneD k` at `γ = gam α ∈ [1, 5/4]`,
  applied to the slices of `Ψ` with source `Gsl α F Ψ z ·`.
* the passage to the `z`-integral: every right-hand slot function is `z`-integrable — the plain
  angular slots are dominated, slot by slot, by the `ℋ^k`-integrand of the corresponding datum
  (`Work.FTS.EllipticEst.remov.selfdth.slot_pointwise_HkIntegrand` for the slots of `F`,
  `z²∂_z²Ψ` and `∂_θ²Ψ`, `Work.FTS.EllipticEst.Cores.Pieces.srcB_pointwise` for the slot of
  `D_zΨ`, and `Work.FTS.EllipticEst.Mine.SlicePoincare` for the two low-order slots).
  `MeasureTheory.integral_mono_of_nonneg` then gives the bound and the sum splits by
  `MeasureTheory.integral_add` and `Finset.integrable_sum`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT.ESW

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary helpers -/

/-- `∂_θ^{m+n} f = ∂_θ^m (∂_θ^n f)`. -/
theorem pthIter_add_fts (m n : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter (m + n) f = Work.Spaces.pthIter m (Work.Spaces.pthIter n f) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_add, Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]

/-- `∂_θ^n f z θ` is the `n`-th iterated derivative of the slice `θ ↦ f z θ`. -/
theorem pthIter_eq_iterDeriv_point (n : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter n f z θ = iteratedDeriv n (fun t => f z t) θ := by
  rw [Work.FTS.EllipticEst.Mine.pthIter_eq_iteratedDeriv]

/-- A constant multiple commutes with the iterated `∂_θ`. -/
theorem pthIter_const_mul_fts (c : ℝ) (m : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter m (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.pthIter m f z θ := by
  induction m with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]
      funext z θ
      simp only [Work.Spaces.pth]
      exact deriv_const_mul_field c

/-- `Work.Stability.smoothOrder` is the genuine smooth order `∞`. -/
theorem smoothOrder_ne_zero_fts : Work.Stability.smoothOrder ≠ 0 := by
  simp [Work.Stability.smoothOrder]

/-- On the open quadrant the iterated `∂_θ` is additive for `SmoothOpen` data. -/
theorem pthIter_add_on_Q0_fts {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) (n : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pthIter n (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.pthIter n f z θ + Work.Spaces.pthIter n g z θ := by
  have hsm : ∀ {h : ℝ → ℝ → ℝ}, Work.FTS.EllipticEst.SmoothOpen h → ∀ k : ℕ,
      Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter k h) := by
    intro h hh k
    induction k with
    | zero => exact hh
    | succ k ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth
  induction n with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
      intro z θ hz h1 h2
      have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨h1, h2⟩
      have heq : (fun θ' : ℝ => Work.Spaces.pthIter n (fun z θ => f z θ + g z θ) z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.pthIter n f z θ' + Work.Spaces.pthIter n g z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih z θ' hz hθ'.1 hθ'.2
      have hd1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.pthIter n f z θ') θ :=
        (((hsm hf n).curry_θ hz).differentiableOn smoothOrder_ne_zero_fts
          |>.differentiableAt (isOpen_Ioo.mem_nhds hθ))
      have hd2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.pthIter n g z θ') θ :=
        (((hsm hg n).curry_θ hz).differentiableOn smoothOrder_ne_zero_fts
          |>.differentiableAt (isOpen_Ioo.mem_nhds hθ))
      simp only [Work.Spaces.pthIter_succ, Work.Spaces.pth]
      exact heq.deriv_eq.trans (deriv_add hd1 hd2)

/-- The bounds `1 ≤ γ` and `γ ≤ 5/4` for `γ = gam α`, `0 < α ≤ 1/4`. -/
theorem gam_bounds_fts {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) :
    1 ≤ Work.Spaces.gam α ∧ Work.Spaces.gam α ≤ 5 / 4 := by
  constructor <;> simp only [Work.Spaces.gam] <;> linarith

/-- `sin(2θ) ≥ 0` on the closed angular interval. -/
theorem sin_two_nonneg_Iθ_fts {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩


/-- The angular weight `θ ↦ sin(2θ)^c` is continuous on the open quadrant. -/
theorem continuousOn_sin_rpow_Q0_fts (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Work.FTS.EllipticEst.Q0 := by
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  refine hsin.rpow_const (fun p hp => Or.inl (ne_of_gt ?_))
  obtain ⟨-, h0, h1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])

/-- On `(0, π/2)` the weight `sin(2θ)^e` is antitone in the exponent. -/
theorem sin_rpow_le_fts {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) {a b : ℝ}
    (hab : a ≤ b) : (Real.sin (2 * θ)) ^ b ≤ (Real.sin (2 * θ)) ^ a := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hsplit : (Real.sin (2 * θ)) ^ b
      = (Real.sin (2 * θ)) ^ a * (Real.sin (2 * θ)) ^ (b - a) := by
    rw [← Real.rpow_add hs, show a + (b - a) = b from by ring]
  have hle : (Real.sin (2 * θ)) ^ (b - a) ≤ 1 :=
    Real.rpow_le_one hs.le hs1 (by linarith)
  have hnn : 0 ≤ (Real.sin (2 * θ)) ^ a := Real.rpow_nonneg hs.le a
  rw [hsplit]
  calc (Real.sin (2 * θ)) ^ a * (Real.sin (2 * θ)) ^ (b - a)
      ≤ (Real.sin (2 * θ)) ^ a * 1 := mul_le_mul_of_nonneg_left hle hnn
    _ = (Real.sin (2 * θ)) ^ a := mul_one _

/-- The exponent arithmetic `2((j-2)) - γ = 2j - 4 - γ`. -/
theorem weight_sub_two (j : ℕ) (hj : 2 ≤ j) (γ θ : ℝ) :
    (Real.sin (2 * θ)) ^ (2 * ((j - 2 : ℕ) : ℝ) - γ)
      = (Real.sin (2 * θ)) ^ (2 * (j : ℝ) - 4 - γ) := by
  have hcast : (((j - 2 : ℕ)) : ℝ) = (j : ℝ) - 2 := by
    rw [Nat.cast_sub hj]; push_cast; ring
  rw [hcast]
  ring_nf

/-- Pulling the radial weight `(w z)²` inside the angular slot integral. -/
theorem wsq_mul_int_eq_fts (m : ℕ) (f : ℝ → ℝ → ℝ) (σ : ℝ → ℝ) (z : ℝ) :
    (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pthIter m f z θ) ^ 2 * σ θ)
      = ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter m f z θ) ^ 2 * σ θ) := by
  rw [← MeasureTheory.integral_const_mul]

/-- Nonnegativity of the slot integrand, a.e. on `Iθ`. -/
theorem ae_slot_nonneg_fts (m : ℕ) (f : ℝ → ℝ → ℝ) (α z : ℝ) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      0 ≤ (Work.Spaces.pthIter m f z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α) :=
  Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ =>
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
      (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos]))) _))

/-- Almost every `z ∈ Iz` is positive. -/
theorem ae_pos_Iz_fts :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), (0 : ℝ) < z := by
  rw [Work.Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici, MeasureTheory.ae_iff]
  have h1 : {x : ℝ | ¬ (x ∈ Set.Ici (0 : ℝ) → (0 : ℝ) < x)} = {0} := by
    ext x
    simp only [Set.mem_Ici, not_imp, not_lt, Set.mem_singleton_iff]
    constructor
    · intro h; linarith [h.1, h.2]
    · intro h; subst h; norm_num
  rw [h1]
  exact MeasureTheory.measure_singleton 0

/-- `θ ↦ ∂_θ^m g z θ` is measurable (no smoothness needed). -/
theorem measurable_pthIter_succ_fts (m : ℕ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    Measurable (fun θ => Work.Spaces.pthIter (m + 1) g z θ) := by
  have h : (fun θ => Work.Spaces.pthIter (m + 1) g z θ)
      = deriv (fun θ' => Work.Spaces.pthIter m g z θ') := by
    funext θ; rw [Work.Spaces.pthIter_succ]; rfl
  rw [h]
  exact measurable_deriv _

/-- `θ ↦ sin(2θ)^c` is measurable. -/
theorem measurable_sin_rpow_fts (c : ℝ) : Measurable fun θ : ℝ => (Real.sin (2 * θ)) ^ c :=
  (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const c

/-- A slot whose weight exponent is increased is still integrable on the slice. -/
theorem slot_theta_mono_fts {m : ℕ} (hm : 1 ≤ m) {g : ℝ → ℝ → ℝ} {z : ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (h : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter m g z θ) ^ 2 * (Real.sin (2 * θ)) ^ a)
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter m g z θ) ^ 2 * (Real.sin (2 * θ)) ^ b)
      Work.Spaces.Iθ := by
  have hmeas : Measurable (fun θ => Work.Spaces.pthIter m g z θ) := by
    have h := measurable_pthIter_succ_fts (m - 1) g z
    rwa [show m - 1 + 1 = m from by omega] at h
  refine MeasureTheory.Integrable.mono' h
    ((hmeas.pow_const 2).mul (measurable_sin_rpow_fts b)).aestronglyMeasurable ?_
  filter_upwards [Work.FTS.EllipticEst.remov.selfdth.ae_mem_Ioo_of_Iθ] with θ hθ
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
    (Real.rpow_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))) _))]
  exact mul_le_mul_of_nonneg_left (sin_rpow_le_fts hθ hab) (sq_nonneg _)

theorem three_sq_le_fts (a A D α σ : ℝ) (hσ : 0 ≤ σ) :
    (a + α ^ 2 * A + (α * (5 + α)) * D) ^ 2 * σ
      ≤ 3 * (a ^ 2 * σ) + 3 * (α ^ 2) ^ 2 * (A ^ 2 * σ)
        + 3 * (α * (5 + α)) ^ 2 * (D ^ 2 * σ) := by
  have h1 : (a + α ^ 2 * A + (α * (5 + α)) * D) ^ 2
      ≤ 3 * (a ^ 2 + (α ^ 2 * A) ^ 2 + ((α * (5 + α)) * D) ^ 2) := by
    nlinarith [sq_nonneg (a - α ^ 2 * A), sq_nonneg (α ^ 2 * A - (α * (5 + α)) * D),
      sq_nonneg (a - (α * (5 + α)) * D)]
  calc (a + α ^ 2 * A + (α * (5 + α)) * D) ^ 2 * σ
      ≤ (3 * (a ^ 2 + (α ^ 2 * A) ^ 2 + ((α * (5 + α)) * D) ^ 2)) * σ :=
        mul_le_mul_of_nonneg_right h1 hσ
    _ = 3 * (a ^ 2 * σ) + 3 * (α ^ 2) ^ 2 * (A ^ 2 * σ)
        + 3 * (α * (5 + α)) ^ 2 * (D ^ 2 * σ) := by ring

/-- **A plain angular slot is `z`-integrable as soon as it is dominated by the `ℋ^K`-integrand.**
The differentiated function `g` and the function `g'` whose `ℋ^K`-integrand dominates are allowed
to differ (the case `g = D_zΨ`, `g' = ∂_θ²(D_zΨ)`).  The domination is assumed a.e. in `θ` for
every `z ∈ Iz`; the `θ`-integral of the majorant is `z`-integrable by `HkMem`, and the slot
function is a.e. strongly measurable by `Work.FTS.EllipticEst.SrcBnd.SlotAESM`. -/
theorem slot_zInt {α : ℝ} {K m : ℕ} {g g' : ℝ → ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α K g')
    (hbound : ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter m g z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α))
        ≤ C * Work.Spaces.HkIntegrand α K g' z θ) :
    MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter m g z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α))) Work.Spaces.Iz := by
  have haesm : AEStronglyMeasurable (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter m g z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α)))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := (Work.FTS.EllipticEst.SrcBnd.SlotAESM (σ := fun θ : ℝ =>
      (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α)) m hg
      (continuousOn_sin_rpow_Q0_fts (2 * (m : ℝ) - Work.Spaces.gam α))).2
    refine h.congr (Filter.Eventually.of_forall (fun z => ?_))
    exact (wsq_mul_int_eq_fts m g
      (fun θ => (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α)) z).symm
  refine MeasureTheory.Integrable.mono' (hmem.2.const_mul C) haesm ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict
    (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with z hz
  have hnn : 0 ≤ (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter m g z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α)) :=
    mul_nonneg (sq_nonneg _) (MeasureTheory.integral_nonneg_of_ae (ae_slot_nonneg_fts m g α z))
  rw [Real.norm_of_nonneg hnn]
  have hinner : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
        ((Work.Spaces.pthIter m g z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α)))
      ≤ ∫ θ in Work.Spaces.Iθ, C * Work.Spaces.HkIntegrand α K g' z θ := by
    refine MeasureTheory.integral_mono_of_nonneg
      ((ae_slot_nonneg_fts m g α z).mono (fun θ hθ => mul_nonneg (sq_nonneg _) hθ))
      ((hmem.1 z hz).const_mul C) ?_
    filter_upwards [hbound z hz] with θ hθ
    exact hθ
  calc (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter m g z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α))
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
          ((Work.Spaces.pthIter m g z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α)) :=
        wsq_mul_int_eq_fts m g
          (fun θ => (Real.sin (2 * θ)) ^ (2 * (m : ℝ) - Work.Spaces.gam α)) z
    _ ≤ ∫ θ in Work.Spaces.Iθ, C * Work.Spaces.HkIntegrand α K g' z θ := hinner
    _ = C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α K g' z θ) :=
        MeasureTheory.integral_const_mul C _

/-- **The `u`-family slot**: for `j ∈ Icc 3 (k+1)` the `z`-integral of the plain angular slot of
`Ψ` at order `j` with weight `sin(2θ)^{2j-4-γ}` is honest. -/
theorem uSlot_zInt {α : ℝ} {k j : ℕ} (hk : 3 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hwk : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    (hj : j ∈ Finset.Icc 3 (k + 1)) :
    MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter j Ψ z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (j : ℝ) - 4 - Work.Spaces.gam α))) Work.Spaces.Iz := by
  have hBsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak hwk 0).2.2.2
  obtain ⟨C0, hC0pos, hC0⟩ :=
    Work.FTS.EllipticEst.remov.selfdth.slot_pointwise_HkIntegrand (j - 2) (by
      have := Finset.mem_Icc.mp hj; omega)
  have hbase := slot_zInt (α := α) (K := k) (m := j - 2) (g := Work.Spaces.pthIter 2 Ψ)
    (g' := Work.Spaces.pthIter 2 Ψ) (C := C0) hC0pos.le hBsm hwk.memB
    (fun z hz => hC0 α (Work.Spaces.pthIter 2 Ψ) k (by have := Finset.mem_Icc.mp hj; omega)
      hα (fun n => hBsm.forall n) z hz)
  have hfun : (fun z => (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pthIter (j - 2) (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * ((j - 2 : ℕ) : ℝ) - Work.Spaces.gam α)))
      = fun z => (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter j Ψ z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (j : ℝ) - 4 - Work.Spaces.gam α)) := by
    funext z
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
    have hj2 : 2 ≤ j := by have := Finset.mem_Icc.mp hj; omega
    have hpt : Work.Spaces.pthIter (j - 2) (Work.Spaces.pthIter 2 Ψ) z θ ^ 2
        * (Real.sin (2 * θ)) ^ (2 * ((j - 2 : ℕ) : ℝ) - Work.Spaces.gam α)
        = Work.Spaces.pthIter j Ψ z θ ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (j : ℝ) - 4 - Work.Spaces.gam α) := by
      rw [← pthIter_add_fts (j - 2) 2 Ψ, show j - 2 + 2 = j from by omega,
        weight_sub_two j hj2 (Work.Spaces.gam α) θ]
    exact hpt
  rwa [hfun] at hbase

/-- The `θ`-slot of `D_zΨ` at order `k` with the weight `sin(2θ)^{2k-γ}` is integrable on the
slice: it is the order-`(k-2)` slot of `∂_θ²(D_zΨ)` (a level-`(k-1)` datum), whose weight
`sin(2θ)^{2k-4-γ}` dominates `sin(2θ)^{2k-γ}`. -/
theorem dzSlot_theta_int {α : ℝ} {k : ℕ} (hk : 3 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hwk : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ =>
        (Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) Work.Spaces.Iθ := by
  have hk1 : 1 ≤ k := by omega
  have hΨsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hwk.smooth
  have hDzsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 1 Ψ) :=
    (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak hwk 1).2.1
  have hB2sm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) := hDzsm.pth.pth
  have hBsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak hwk 0).2.2.2
  have hDzmem : Work.Spaces.HkMem α (k - 1)
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) := by
    have h0 : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) :=
      Work.FTS.EllipticEst.AeMom.Repair.HkMem_Dz_shift (α := α) (k := k) hk1 hBsm hwk.memB
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) h0 ?_
    intro z hz θ hθ
    exact (Work.EllipticEst.H2W.pthIter2_DzIter_comm hΨsm 1
      (show ((z, θ) : ℝ × ℝ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) from ⟨hz, hθ⟩)).symm
  have hbase := Work.FTS.EllipticEst.Cores.Pieces.pthSlotInt_of_HkMem (α := α) hα (k := k - 1)
    (g := Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) (fun n => hB2sm.forall n) hDzmem
    hz (m := k - 2) (by omega) (by omega)
  have hrew : (fun θ =>
        (Work.Spaces.pthIter (k - 2) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * ((k - 2 : ℕ) : ℝ) - Work.Spaces.gam α))
      = fun θ => (Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - 4 - Work.Spaces.gam α) := by
    funext θ
    have hpt := weight_sub_two k (by omega) (Work.Spaces.gam α) θ
    have hpt2 : Work.Spaces.pthIter (k - 2) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) z θ
        = Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ := by
      rw [← pthIter_add_fts (k - 2) 2 (Work.Spaces.DzIter 1 Ψ),
        show k - 2 + 2 = k from by omega]
    rw [hpt2, hpt]
  rw [hrew] at hbase
  refine slot_theta_mono_fts (m := k) hk1 (by linarith : (2 : ℝ) * (k : ℝ) - 4
    - Work.Spaces.gam α ≤ 2 * (k : ℝ) - Work.Spaces.gam α) ?_
  exact hbase

/-- The pointwise expansion of `∂_θ^k(Gsl α F Ψ)` on the open quadrant. -/
theorem pthIter_Gsl_decomp {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hFsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hAsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (hDzsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 1 Ψ)) (k : ℕ) :
    ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pthIter k (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ
        = Work.Spaces.pthIter k F z θ
          + α ^ 2 * Work.Spaces.pthIter k
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
          + (α * (5 + α)) * Work.Spaces.pthIter k (Work.Spaces.Dz Ψ) z θ := by
  intro z θ hz hθ0 hθ1
  have h1 := pthIter_add_on_Q0_fts (f := F)
    (g := fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    hFsm (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α ^ 2) hAsm) k z θ hz hθ0 hθ1
  have h2 := pthIter_add_on_Q0_fts (f := fun z θ => F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
    (g := fun z θ => (α * (5 + α)) * Work.Spaces.Dz Ψ z θ)
    (Work.FTS.EllipticEst.smoothOpen_add hFsm
      (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α ^ 2) hAsm))
    (Work.FTS.EllipticEst.Cert.smoothOpen_const_mul_bsl (α * (5 + α)) hDzsm) k z θ hz hθ0 hθ1
  rw [pthIter_const_mul_fts] at h1
  rw [pthIter_const_mul_fts] at h2
  have hG : Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ
      = fun z θ => (F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        + (α * (5 + α)) * Work.Spaces.Dz Ψ z θ := by
    funext z θ
    simp only [Work.FTS.EllipticEst.TT.ESW.Gsl, Work.FTS.EllipticEst.TT.ESW.Asl,
      Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz]
  rw [hG, h2, h1]

/-- **The source slot**: the `z`-integral of the plain angular slot of `Gsl α F Ψ` at order `k`
with weight `sin(2θ)^{2k-γ}` is honest. -/
theorem sourceSlot_zInt {α : ℝ} {k : ℕ} (hk : 3 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hwk : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k
        (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))) Work.Spaces.Iz := by
  have hk1 : 1 ≤ k := by omega
  have hFsm : Work.FTS.EllipticEst.SmoothOpen F :=
    (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak hwk 0).1
  have hAsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak hwk 0).2.2.1
  have hDzsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DzIter 1 Ψ) :=
    (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak hwk 1).2.1
  have hB2sm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) := hDzsm.pth.pth
  have hGsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) :=
    Work.FTS.EllipticEst.Cores.Pieces.TL2.smoothOpen_Gsrc hwk
  obtain ⟨C0, hC0pos, hC0⟩ :=
    Work.FTS.EllipticEst.remov.selfdth.slot_pointwise_HkIntegrand k hk1
  have hzF : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k F z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))) Work.Spaces.Iz :=
    slot_zInt hC0pos.le hFsm hwk.memF
      (fun z hz => hC0 α F k le_rfl hα (fun n => hFsm.forall n) z hz)
  have hzA : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pthIter k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))) Work.Spaces.Iz :=
    slot_zInt hC0pos.le hAsm hwk.memA
      (fun z hz => hC0 α (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) k le_rfl hα
        (fun n => hAsm.forall n) z hz)
  obtain ⟨Cb, hCbpos, hCb⟩ := Work.FTS.EllipticEst.Cores.Pieces.srcB_pointwise k hk
  have hDzmem : Work.Spaces.HkMem α (k - 1)
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) := by
    have hΨsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
      Work.FTS.EllipticEst.smoothOpen_of_forall hwk.smooth
    have hBsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
      (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak hwk 0).2.2.2
    have h0 : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) :=
      Work.FTS.EllipticEst.AeMom.Repair.HkMem_Dz_shift (α := α) (k := k) hk1 hBsm hwk.memB
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) h0 ?_
    intro z hz θ hθ
    exact (Work.EllipticEst.H2W.pthIter2_DzIter_comm hΨsm 1
      (show ((z, θ) : ℝ × ℝ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) from ⟨hz, hθ⟩)).symm
  have hzD : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))) Work.Spaces.Iz :=
    slot_zInt hCbpos.le hDzsm hDzmem
      (fun z hz => hCb α (Work.Spaces.DzIter 1 Ψ) hα (fun n => hB2sm.forall n) z hz)
  refine MeasureTheory.Integrable.mono'
    (((hzF.const_mul 3).add (hzA.const_mul (3 * (α ^ 2) ^ 2))).add
      (hzD.const_mul (3 * (α * (5 + α)) ^ 2))) ?_ ?_
  · -- a.e. strong measurability of the source slot
    have h := (Work.FTS.EllipticEst.SrcBnd.SlotAESM (σ := fun θ : ℝ =>
      (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) k hGsm
      (continuousOn_sin_rpow_Q0_fts (2 * (k : ℝ) - Work.Spaces.gam α))).2
    refine h.congr (Filter.Eventually.of_forall (fun z => ?_))
    exact (wsq_mul_int_eq_fts k (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ)
      (fun θ => (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) z).symm
  · filter_upwards [MeasureTheory.self_mem_ae_restrict
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici), ae_pos_Iz_fts]
      with z hz hzpos
    have hnn : 0 ≤ (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k
          (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) :=
      mul_nonneg (sq_nonneg _)
        (MeasureTheory.integral_nonneg_of_ae (ae_slot_nonneg_fts k
          (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) α z))
    rw [Real.norm_of_nonneg hnn]
    -- the θ-slice comparison, `z > 0`
    have hFθ : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pthIter k F z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) Work.Spaces.Iθ :=
      Work.FTS.EllipticEst.Cores.Pieces.pthSlotInt_of_HkMem (α := α) hα (k := k) (g := F)
        (fun n => hFsm.forall n) hwk.memF hzpos (m := k) hk1 le_rfl
    have hAθ : MeasureTheory.IntegrableOn (fun θ =>
        (Work.Spaces.pthIter k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) Work.Spaces.Iθ :=
      Work.FTS.EllipticEst.Cores.Pieces.pthSlotInt_of_HkMem (α := α) hα (k := k)
        (g := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        (fun n => hAsm.forall n) hwk.memA hzpos (m := k) hk1 le_rfl
    have hDθ : MeasureTheory.IntegrableOn (fun θ =>
        (Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) Work.Spaces.Iθ :=
      dzSlot_theta_int hk hα hwk hzpos
    have hdec : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        (Work.Spaces.pthIter k (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)
        ≤ 3 * ((Work.Spaces.pthIter k F z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
          + 3 * (α ^ 2) ^ 2 * ((Work.Spaces.pthIter k
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
          + 3 * (α * (5 + α)) ^ 2 * ((Work.Spaces.pthIter k
              (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) := by
      refine Work.FTS.EllipticEst.remov.selfdth.ae_mem_Ioo_of_Iθ.mono (fun θ hθ => ?_)
      have h := pthIter_Gsl_decomp (α := α) hFsm hAsm hDzsm k z θ hzpos hθ.1 hθ.2
      have hs0 : 0 ≤ (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α) :=
        Real.rpow_nonneg (le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos]))) _
      rw [h]
      exact three_sq_le_fts (Work.Spaces.pthIter k F z θ)
        (Work.Spaces.pthIter k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)
        (Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ) α
        ((Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) hs0
    -- the integrand functions of the three summands, and the majorant
    set W : ℝ := (Work.Spaces.w z) ^ 2 with hW
    have hWnn : 0 ≤ W := by rw [hW]; exact sq_nonneg _
    have hFθ' : MeasureTheory.IntegrableOn (fun θ => W * ((Work.Spaces.pthIter k F z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))) Work.Spaces.Iθ :=
      hFθ.const_mul W
    have hAθ' : MeasureTheory.IntegrableOn (fun θ => W *
        ((Work.Spaces.pthIter k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))) Work.Spaces.Iθ :=
      hAθ.const_mul W
    have hDθ' : MeasureTheory.IntegrableOn (fun θ => W *
        ((Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))) Work.Spaces.Iθ :=
      hDθ.const_mul W
    set XF : ℝ → ℝ := fun θ => 3 * (W * ((Work.Spaces.pthIter k F z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))) with hXF
    set XA : ℝ → ℝ := fun θ => 3 * (α ^ 2) ^ 2 * (W *
      ((Work.Spaces.pthIter k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))) with hXA
    set XD : ℝ → ℝ := fun θ => 3 * (α * (5 + α)) ^ 2 * (W *
      ((Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))) with hXD
    have hXFint : MeasureTheory.IntegrableOn XF Work.Spaces.Iθ :=
      hXF ▸ (hFθ'.const_mul 3)
    have hXAint : MeasureTheory.IntegrableOn XA Work.Spaces.Iθ :=
      hXA ▸ (hAθ'.const_mul (3 * (α ^ 2) ^ 2))
    have hXDint : MeasureTheory.IntegrableOn XD Work.Spaces.Iθ :=
      hXD ▸ (hDθ'.const_mul (3 * (α * (5 + α)) ^ 2))
    have hpt' : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        W * ((Work.Spaces.pthIter k (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
          ≤ XF θ + XA θ + XD θ := by
      filter_upwards [hdec] with θ hθ
      have h1 := mul_le_mul_of_nonneg_left hθ hWnn
      rw [hXF, hXA, hXD]
      nlinarith [h1]
    have hinner : (∫ θ in Work.Spaces.Iθ, W *
          ((Work.Spaces.pthIter k (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)))
        ≤ ∫ θ in Work.Spaces.Iθ, XF θ + XA θ + XD θ :=
      MeasureTheory.integral_mono_of_nonneg
        ((ae_slot_nonneg_fts k (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) α z).mono
          (fun θ hθ => mul_nonneg hWnn hθ))
        ((hXFint.add hXAint).add hXDint) hpt'
    have hsplit : (∫ θ in Work.Spaces.Iθ, XF θ + XA θ + XD θ)
        = 3 * (W * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)))
          + 3 * (α ^ 2) ^ 2 * (W * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pthIter k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)))
          + 3 * (α * (5 + α)) ^ 2 * (W * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))) := by
      have e1 : (fun θ : ℝ => XF θ + XA θ + XD θ)
          = fun θ : ℝ => (fun θ' : ℝ => XF θ' + XA θ') θ + XD θ := rfl
      rw [e1, MeasureTheory.integral_add (f := fun θ' : ℝ => XF θ' + XA θ')
        (g := XD) (hXFint.add hXAint) hXDint]
      have e2 : (fun θ' : ℝ => XF θ' + XA θ')
          = fun θ' : ℝ => (fun θ'' : ℝ => XF θ'') θ' + (fun θ'' : ℝ => XA θ'') θ' := rfl
      rw [e2, MeasureTheory.integral_add (f := fun θ'' : ℝ => XF θ'')
        (g := fun θ'' : ℝ => XA θ'') hXFint hXAint]
      rw [hXF, hXA, hXD]
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have h1 : W * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k
          (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
        ≤ 3 * (W * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)))
          + 3 * (α ^ 2) ^ 2 * (W * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pthIter k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)))
          + 3 * (α * (5 + α)) ^ 2 * (W * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))) := by
      calc W * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k
            (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
          = ∫ θ in Work.Spaces.Iθ, W *
              ((Work.Spaces.pthIter k (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) := by
            rw [hW]
            exact wsq_mul_int_eq_fts k (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ)
              (fun θ => (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) z
        _ ≤ ∫ θ in Work.Spaces.Iθ, XF θ + XA θ + XD θ := hinner
        _ = 3 * (W * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k F z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)))
          + 3 * (α ^ 2) ^ 2 * (W * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pthIter k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)))
          + 3 * (α * (5 + α)) ^ 2 * (W * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pthIter k (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))) := hsplit
    rw [hW] at h1
    exact h1

/-- **The two low-order slots** `z ↦ w z² ∫_θ (∂_θΨ)²` and `z ↦ w z² ∫_θ Ψ²` are `z`-integrable,
by the slice Poincaré inequality and the honesty of the `η`-slot. -/
theorem lowSlot_zInt {α : ℝ} {k : ℕ} (hk : 3 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hwk : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)) Work.Spaces.Iz ∧
    MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) Work.Spaces.Iz := by
  have hk1 : 1 ≤ k := by omega
  obtain ⟨Kp, hKp, hSP⟩ := Work.FTS.EllipticEst.Mine.SlicePoincare
  have hmem0 : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ)) Work.Spaces.Iz :=
    Work.FTS.EllipticEst.TT.ESW.integrable_w_sq_thetaEnergy hwk
  have hΨsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hwk.smooth
  -- a.e. strong measurability of the two slot functions
  have haesm1 : AEStronglyMeasurable (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := (Work.FTS.EllipticEst.SrcBnd.SlotAESM (σ := fun _ : ℝ => (1 : ℝ)) 1 hΨsm
      continuousOn_const).2
    refine h.congr (Filter.Eventually.of_forall (fun z => ?_))
    show (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
        ((Work.Spaces.pthIter 1 Ψ z θ) ^ 2 * (1 : ℝ)))
      = (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
    rw [← wsq_mul_int_eq_fts 1 Ψ (fun _ => (1 : ℝ)) z]
    simp only [mul_one]
  have haesm2 : AEStronglyMeasurable (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := (Work.FTS.EllipticEst.SrcBnd.SlotAESM (σ := fun _ : ℝ => (1 : ℝ)) 0 hΨsm
      continuousOn_const).2
    refine h.congr (Filter.Eventually.of_forall (fun z => ?_))
    show (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
        ((Work.Spaces.pthIter 0 Ψ z θ) ^ 2 * (1 : ℝ)))
      = (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
    rw [← wsq_mul_int_eq_fts 0 Ψ (fun _ => (1 : ℝ)) z]
    simp only [Work.Spaces.pthIter_zero, mul_one]
  -- the `η`-slot Poincaré bound on the slices, a.e. in `z`
  have hbnd : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ‖(fun z => (Work.Spaces.w z) ^ 2 *
        ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
          + (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))) z‖
        ≤ (fun z => 2 * Kp * ((Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ))) z := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici), ae_pos_Iz_fts]
      with z hz hzpos
    have hlow := Work.FTS.EllipticEst.remov.weakSliceRegular k hk1 α F Ψ hα hα4 hwk z hzpos
    have hcont : ContinuousOn (fun θ => Ψ z θ) (Set.Icc 0 (Real.pi / 2)) := hlow.1
    have h2e : MeasureTheory.IntegrableOn (fun θ =>
        (deriv (deriv (fun θ' => Ψ z θ')) θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
      hlow.2.2.2.2.2.2
    have hC2 : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
      Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip hwk.smooth hzpos 2
    obtain ⟨-, -, hb1, hb2⟩ := hSP (fun θ => Ψ z θ) hC2 hcont (hwk.zero z) (hwk.pi_half z) h2e
    have hA0 : 0 ≤ (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2) :=
      MeasureTheory.integral_nonneg_of_ae (Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
        (fun θ _ => sq_nonneg (Work.Spaces.pthIter 1 Ψ z θ)))
    have hB0 : 0 ≤ (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2) :=
      MeasureTheory.integral_nonneg_of_ae (Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
        (fun θ _ => sq_nonneg (Ψ z θ)))
    have hR0 : 0 ≤ (∫ θ in Work.Spaces.Iθ, (deriv (deriv (fun θ' => Ψ z θ')) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) :=
      MeasureTheory.integral_nonneg_of_ae
        (Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
          (fun θ hθ => mul_nonneg (sq_nonneg _)
            (Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
              (by linarith [hθ.2, Real.pi_pos])) _)))
    have hgoal : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
        + (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
        ≤ 2 * Kp * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) := by
      have e1 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
          = ∫ θ in Work.Spaces.Iθ, (deriv (fun θ' => Ψ z θ') θ) ^ 2 := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with θ
        rfl
      have e2 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ)
          = ∫ θ in Work.Spaces.Iθ, (deriv (deriv (fun θ' => Ψ z θ')) θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with θ
        rfl
      rw [e1, e2]
      linarith [hb1, hb2, hR0]
    have hnn : 0 ≤ (Work.Spaces.w z) ^ 2 *
        ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
          + (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) :=
      mul_nonneg (sq_nonneg _) (add_nonneg hA0 hB0)
    rw [Real.norm_of_nonneg hnn]
    calc (Work.Spaces.w z) ^ 2 * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
          + (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
        ≤ (Work.Spaces.w z) ^ 2 * (2 * Kp * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) :=
          mul_le_mul_of_nonneg_left hgoal (sq_nonneg _)
      _ = 2 * Kp * ((Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by ring
  have haesm_sum : AEStronglyMeasurable (fun z => (Work.Spaces.w z) ^ 2 *
      ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
        + (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hcongr : (fun z => (Work.Spaces.w z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2))
          + (fun z => (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
        = fun z => (Work.Spaces.w z) ^ 2 *
            ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
              + (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) := by
      funext z; simp only [Pi.add_apply]; ring
    exact hcongr ▸ (haesm1.add haesm2)
  have hsum : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
      ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
        + (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))) Work.Spaces.Iz :=
    (hmem0.const_mul (2 * Kp)).mono' haesm_sum hbnd
  constructor
  · refine hsum.mono' haesm1 ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with z hz
    have hnn : 0 ≤ (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2) :=
      MeasureTheory.integral_nonneg_of_ae (Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
        (fun θ _ => sq_nonneg (Work.Spaces.pthIter 1 Ψ z θ)))
    have hbn : 0 ≤ (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2) :=
      MeasureTheory.integral_nonneg_of_ae (Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
        (fun θ _ => sq_nonneg (Ψ z θ)))
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hnn)]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hbn) (sq_nonneg _)
  · refine hsum.mono' haesm2 ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with z hz
    have hnn : 0 ≤ (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2) :=
      MeasureTheory.integral_nonneg_of_ae (Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
        (fun θ _ => sq_nonneg (Ψ z θ)))
    have hbn : 0 ≤ (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2) :=
      MeasureTheory.integral_nonneg_of_ae (Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
        (fun θ _ => sq_nonneg (Work.Spaces.pthIter 1 Ψ z θ)))
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hnn)]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hbn) (sq_nonneg _)

/-! ## The slot functions of the target's right-hand side -/

/-- The left-hand (top) slot `z ↦ w z² ∫_θ (∂_θ^{k+2}Ψ)² sin^{2k-γ}`. -/
abbrev Ul1d_L (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z =>
  (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter (k + 2) Ψ z θ) ^ 2
    * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))

/-- The source slot `z ↦ w z² ∫_θ (∂_θ^k G)² sin^{2k-γ}`. -/
abbrev Ul1d_E (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z =>
  (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k
      (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
    * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))

/-- The `u`-family slot at order `j`. -/
abbrev Ul1d_B (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (j : ℕ) : ℝ → ℝ := fun z =>
  (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter j Ψ z θ) ^ 2
    * (Real.sin (2 * θ)) ^ (2 * (j : ℝ) - 4 - Work.Spaces.gam α))

/-- The sum of the `u`-family slots. -/
abbrev Ul1d_U (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z =>
  ∑ j ∈ Finset.Icc 3 (k + 1), Ul1d_B α k F Ψ j z

/-- The `η`-slot `z ↦ w z² ∫_θ (∂_θ²Ψ)² sEta`. -/
abbrev Ul1d_D (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z =>
  (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
    * Work.FTS.EllipticEst.sEta θ)

/-- The low slot `z ↦ w z² ∫_θ (∂_θΨ)²`. -/
abbrev Ul1d_T (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z =>
  (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)

/-- The low slot `z ↦ w z² ∫_θ Ψ²`. -/
abbrev Ul1d_Z (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z =>
  (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)

/-- The angular source of the bundle is the one used in the statement. -/
theorem Gsrc_eq_Gsl (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) :
    Work.FTS.EllipticEst.Mine.Gsrc α F Ψ = Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ := by
  funext z θ
  simp only [Work.FTS.EllipticEst.Mine.Gsrc, Work.FTS.EllipticEst.TT.ESW.Gsl,
    Work.FTS.EllipticEst.TT.ESW.Asl, Work.Spaces.Dz]

/-- A weighted angular slot is nonnegative. -/
theorem wsq_slot_nonneg_fts (m : ℕ) (f : ℝ → ℝ → ℝ) {σ : ℝ → ℝ}
    (hσ : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ σ θ) (z : ℝ) :
    0 ≤ (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter m f z θ) ^ 2 * σ θ) :=
  mul_nonneg (sq_nonneg _) (MeasureTheory.integral_nonneg_of_ae
    (Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
      (fun θ hθ => mul_nonneg (sq_nonneg _) (hσ θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩))))

/-! ## The target -/

/-- **The two-dimensional assembly of the one-dimensional top-slot estimate.** -/
theorem U_le_of_1d (D : ℝ) (hD : 0 < D) :
    ∀ (k : ℕ), 3 ≤ k → Work.FTS.EllipticEst.TT.ESW.OneD k → ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      α ^ 2 * Work.Spaces.HkNorm α (k - 1) (Work.FTS.EllipticEst.TT.ESW.Asl Ψ)
          + Work.Spaces.HkNorm α (k - 1) (Work.FTS.EllipticEst.TT.ESW.Bsl Ψ)
        ≤ D * Work.Spaces.HkNorm α k F →
      α ^ 2 * Work.Spaces.HkNorm α (k - 1) (Work.FTS.EllipticEst.TT.ESW.Asl (Work.Spaces.DzIter 1 Ψ))
          + Work.Spaces.HkNorm α (k - 1) (Work.FTS.EllipticEst.TT.ESW.Bsl (Work.Spaces.DzIter 1 Ψ))
        ≤ D * Work.Spaces.HkNorm α k F →
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter (k + 2) Ψ z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
        ≤ C *
          ((∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
              ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
            + (∑ j ∈ Finset.Icc 3 (k + 1), ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
                ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter j Ψ z θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * (j : ℝ) - 4 - Work.Spaces.gam α))
            + (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
                ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
                  * Work.FTS.EllipticEst.sEta θ)
            + (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
                ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
            + (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
                ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) := by
  intro k hk hOneD
  obtain ⟨C1, hC1pos, h1d⟩ := hOneD
  refine ⟨max 1 C1, lt_max_iff.mpr (Or.inl one_pos), ?_⟩
  intro α F Ψ hα hα4 hwk hH1 hH2
  obtain ⟨hγ1, hγ54⟩ := gam_bounds_fts hα hα4
  have hΨsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hwk.smooth
  -- ## the a.e. slicewise inequality, from `OneD k` applied to the slices
  have hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      Ul1d_L α k F Ψ z ≤ max 1 C1 * (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z
        + Ul1d_D α k F Ψ z + Ul1d_T α k F Ψ z + Ul1d_Z α k F Ψ z) := by
    filter_upwards [Work.FTS.EllipticEst.Cores.Pieces.TopSlotIntegrability k hk D hD α F Ψ
      hα hα4 hwk hH1 hH2, ae_pos_Iz_fts] with z hz hzpos
    obtain ⟨hcont, hA, hB, hC, hD', hE, hF⟩ := hz
    have hsm : ContDiffOn ℝ (k + 2) (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
      Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip hwk.smooth hzpos (k + 2)
    have heq : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        (fun θ => Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ z θ) θ
          = Work.FTS.EllipticEst.Lzero1 (fun θ => Ψ z θ) θ :=
      fun θ hθ => (slice_source_eq hΨsm
        (fun z θ hz hθ0 hθ1 => hwk.eq z hz θ hθ0 hθ1) hzpos hθ).symm
    have hB0 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pthIter k
        (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) Work.Spaces.Iθ := by
      simpa only [Gsrc_eq_Gsl] using hB
    have hA' : MeasureTheory.IntegrableOn (fun θ =>
        (iteratedDeriv (k + 2) (fun θ => Ψ z θ) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) Work.Spaces.Iθ := by
      refine hA.congr (Filter.Eventually.of_forall (fun θ => ?_))
      simp only [pthIter_eq_iterDeriv_point]
    have hB' : MeasureTheory.IntegrableOn (fun θ =>
        (iteratedDeriv k (fun θ => Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ z θ) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) Work.Spaces.Iθ := by
      refine hB0.congr (Filter.Eventually.of_forall (fun θ => ?_))
      simp only [pthIter_eq_iterDeriv_point]
    have hC' : ∀ j ∈ Finset.Icc 3 (k + 1), MeasureTheory.IntegrableOn (fun θ =>
        (iteratedDeriv j (fun θ => Ψ z θ) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (j : ℝ) - 4 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
      intro j hj
      refine (hC j hj).congr (Filter.Eventually.of_forall (fun θ => ?_))
      simp only [pthIter_eq_iterDeriv_point]
    have hD'' : MeasureTheory.IntegrableOn (fun θ =>
        (deriv (deriv (fun θ => Ψ z θ)) θ) ^ 2
          * (Work.FTS.EllipticEst.sEta θ)) Work.Spaces.Iθ := by
      refine hD'.congr (Filter.Eventually.of_forall (fun θ => ?_))
      show (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        = (deriv (deriv (fun θ => Ψ z θ)) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      rw [show Work.Spaces.pthIter 2 Ψ z θ = deriv (deriv (fun θ => Ψ z θ)) θ from rfl]
    have hE' : MeasureTheory.IntegrableOn (fun θ => (deriv (fun θ => Ψ z θ) θ) ^ 2)
        Work.Spaces.Iθ := by
      refine hE.congr (Filter.Eventually.of_forall (fun θ => ?_))
      show (Work.Spaces.pthIter 1 Ψ z θ) ^ 2 = (deriv (fun θ => Ψ z θ) θ) ^ 2
      rw [show Work.Spaces.pthIter 1 Ψ z θ = deriv (fun θ => Ψ z θ) θ from rfl]
    have hone := h1d (Work.Spaces.gam α) (fun θ => Ψ z θ)
      (fun θ => Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ z θ) hγ1 hγ54 hsm hcont
      (hwk.zero z) (hwk.pi_half z) heq hA' hB' hC' hD'' hE' hF
    -- the conversion of the six slots back to the `pthIter` language
    have hAeq : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter (k + 2) Ψ z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
        = ∫ θ in Work.Spaces.Iθ, (iteratedDeriv (k + 2) (fun θ => Ψ z θ) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
      simp only [pthIter_eq_iterDeriv_point]
    have hBeq : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k
          (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
        = ∫ θ in Work.Spaces.Iθ, (iteratedDeriv k
            (fun θ => Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ z θ) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
      simp only [pthIter_eq_iterDeriv_point]
    have hsum' : (∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pthIter j Ψ z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (j : ℝ) - 4 - Work.Spaces.gam α))
        = ∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
            (iteratedDeriv j (fun θ => Ψ z θ) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (j : ℝ) - 4 - Work.Spaces.gam α) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
      simp only [pthIter_eq_iterDeriv_point]
    have hDeq : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ)
        = ∫ θ in Work.Spaces.Iθ, (deriv (deriv (fun θ => Ψ z θ)) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
      show (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        = (deriv (deriv (fun θ => Ψ z θ)) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      rw [show Work.Spaces.pthIter 2 Ψ z θ = deriv (deriv (fun θ => Ψ z θ)) θ from rfl]
    have hEeq : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
        = ∫ θ in Work.Spaces.Iθ, (deriv (fun θ => Ψ z θ) θ) ^ 2 := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
      show (Work.Spaces.pthIter 1 Ψ z θ) ^ 2 = (deriv (fun θ => Ψ z θ) θ) ^ 2
      rw [show Work.Spaces.pthIter 1 Ψ z θ = deriv (fun θ => Ψ z θ) θ from rfl]
    have hone' : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter (k + 2) Ψ z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
        ≤ C1 * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k
              (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
            + (∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pthIter j Ψ z θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * (j : ℝ) - 4 - Work.Spaces.gam α))
            + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)
            + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
            + (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)) := by
      rw [hAeq, hBeq, hsum', hDeq, hEeq]
      exact hone
    have hdist : (Work.Spaces.w z) ^ 2 * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k
              (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
            + (∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pthIter j Ψ z θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * (j : ℝ) - 4 - Work.Spaces.gam α))
            + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)
            + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
            + (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
        = Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z + Ul1d_D α k F Ψ z
            + Ul1d_T α k F Ψ z + Ul1d_Z α k F Ψ z := by
      simp only [Ul1d_E, Ul1d_U, Ul1d_B, Ul1d_D, Ul1d_T, Ul1d_Z, mul_add, Finset.mul_sum]
    have hnn : 0 ≤ Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z + Ul1d_D α k F Ψ z
        + Ul1d_T α k F Ψ z + Ul1d_Z α k F Ψ z := by
      have h1 : 0 ≤ Ul1d_E α k F Ψ z :=
        wsq_slot_nonneg_fts k (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ)
          (fun θ hθ => Real.rpow_nonneg (sin_two_nonneg_Iθ_fts hθ) _) z
      have h2 : 0 ≤ Ul1d_U α k F Ψ z :=
        Finset.sum_nonneg (fun j _ => wsq_slot_nonneg_fts j Ψ
          (fun θ hθ => Real.rpow_nonneg (sin_two_nonneg_Iθ_fts hθ) _) z)
      have h3 : 0 ≤ Ul1d_D α k F Ψ z :=
        wsq_slot_nonneg_fts 2 Ψ (fun θ hθ => Work.FTS.EllipticEst.Mine.sp_sEta_nonneg hθ) z
      have h4 : 0 ≤ Ul1d_T α k F Ψ z := by
        simpa only [Ul1d_T, mul_one] using
          wsq_slot_nonneg_fts 1 Ψ (fun θ _ => zero_le_one) z
      have h5 : 0 ≤ Ul1d_Z α k F Ψ z := by
        simpa only [Ul1d_Z, Work.Spaces.pthIter_zero, mul_one] using
          wsq_slot_nonneg_fts 0 Ψ (fun θ _ => zero_le_one) z
      linarith
    calc (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pthIter (k + 2) Ψ z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
        ≤ (Work.Spaces.w z) ^ 2 * (C1 * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k
                (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
              + (∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.pthIter j Ψ z θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * (j : ℝ) - 4 - Work.Spaces.gam α))
              + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
                  * Work.FTS.EllipticEst.sEta θ)
              + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
              + (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))) :=
          mul_le_mul_of_nonneg_left hone' (sq_nonneg (Work.Spaces.w z))
      _ = C1 * (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z + Ul1d_D α k F Ψ z
            + Ul1d_T α k F Ψ z + Ul1d_Z α k F Ψ z) := by
          rw [show (Work.Spaces.w z) ^ 2 * (C1 * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k
                  (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
                + (∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
                    (Work.Spaces.pthIter j Ψ z θ) ^ 2
                      * (Real.sin (2 * θ)) ^ (2 * (j : ℝ) - 4 - Work.Spaces.gam α))
                + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
                    * Work.FTS.EllipticEst.sEta θ)
                + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
                + (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)))
              = C1 * ((Work.Spaces.w z) ^ 2 * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k
                    (Work.FTS.EllipticEst.TT.ESW.Gsl α F Ψ) z θ) ^ 2
                      * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
                  + (∑ j ∈ Finset.Icc 3 (k + 1), ∫ θ in Work.Spaces.Iθ,
                      (Work.Spaces.pthIter j Ψ z θ) ^ 2
                        * (Real.sin (2 * θ)) ^ (2 * (j : ℝ) - 4 - Work.Spaces.gam α))
                  + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
                      * Work.FTS.EllipticEst.sEta θ)
                  + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
                  + (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))) from by ring]
          rw [hdist]
      _ ≤ max 1 C1 * (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z + Ul1d_D α k F Ψ z
            + Ul1d_T α k F Ψ z + Ul1d_Z α k F Ψ z) :=
          mul_le_mul_of_nonneg_right (le_max_right 1 C1) hnn
  -- ## integrability of the five slot functions and of the majorant
  have hEint : MeasureTheory.IntegrableOn (Ul1d_E α k F Ψ) Work.Spaces.Iz :=
    sourceSlot_zInt hk hα hwk
  have hBint : ∀ j ∈ Finset.Icc 3 (k + 1),
      MeasureTheory.IntegrableOn (Ul1d_B α k F Ψ j) Work.Spaces.Iz :=
    fun j hj => uSlot_zInt hk hα hwk hj
  have hUint : MeasureTheory.IntegrableOn (Ul1d_U α k F Ψ) Work.Spaces.Iz :=
    MeasureTheory.integrable_finsetSum (Finset.Icc 3 (k + 1)) hBint
  have hDint : MeasureTheory.IntegrableOn (Ul1d_D α k F Ψ) Work.Spaces.Iz :=
    Work.FTS.EllipticEst.TT.ESW.integrable_w_sq_thetaEnergy hwk
  have hTint : MeasureTheory.IntegrableOn (Ul1d_T α k F Ψ) Work.Spaces.Iz :=
    (lowSlot_zInt hk hα hα4 hwk).1
  have hZint : MeasureTheory.IntegrableOn (Ul1d_Z α k F Ψ) Work.Spaces.Iz :=
    (lowSlot_zInt hk hα hα4 hwk).2
  have hGint : MeasureTheory.IntegrableOn
      (fun z => max 1 C1 * (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z + Ul1d_D α k F Ψ z
        + Ul1d_T α k F Ψ z + Ul1d_Z α k F Ψ z)) Work.Spaces.Iz :=
    ((((hEint.add hUint).add hDint).add hTint).add hZint).const_mul (max 1 C1)
  -- ## the integral comparison
  have hLnn : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 ≤ Ul1d_L α k F Ψ z :=
    Filter.Eventually.of_forall (fun z => wsq_slot_nonneg_fts (k + 2) Ψ
      (fun θ hθ => Real.rpow_nonneg (sin_two_nonneg_Iθ_fts hθ) _) z)
  have hmono : (∫ z in Work.Spaces.Iz, Ul1d_L α k F Ψ z) ≤
      ∫ z in Work.Spaces.Iz, max 1 C1 * (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z
        + Ul1d_D α k F Ψ z + Ul1d_T α k F Ψ z + Ul1d_Z α k F Ψ z) :=
    MeasureTheory.integral_mono_of_nonneg hLnn hGint hae
  have hsplit1 : (∫ z in Work.Spaces.Iz, max 1 C1 *
        (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z + Ul1d_D α k F Ψ z
          + Ul1d_T α k F Ψ z + Ul1d_Z α k F Ψ z))
      = max 1 C1 * ∫ z in Work.Spaces.Iz, (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z
          + Ul1d_D α k F Ψ z + Ul1d_T α k F Ψ z + Ul1d_Z α k F Ψ z) :=
    MeasureTheory.integral_const_mul (max 1 C1) _
  have hsplit2 : (∫ z in Work.Spaces.Iz, (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z
          + Ul1d_D α k F Ψ z + Ul1d_T α k F Ψ z + Ul1d_Z α k F Ψ z))
      = (∫ z in Work.Spaces.Iz, Ul1d_E α k F Ψ z)
        + (∫ z in Work.Spaces.Iz, Ul1d_U α k F Ψ z)
        + (∫ z in Work.Spaces.Iz, Ul1d_D α k F Ψ z)
        + (∫ z in Work.Spaces.Iz, Ul1d_T α k F Ψ z)
        + (∫ z in Work.Spaces.Iz, Ul1d_Z α k F Ψ z) := by
    have e1 : (∫ z in Work.Spaces.Iz, (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z
            + Ul1d_D α k F Ψ z + Ul1d_T α k F Ψ z + Ul1d_Z α k F Ψ z))
        = (∫ z in Work.Spaces.Iz, (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z
            + Ul1d_D α k F Ψ z + Ul1d_T α k F Ψ z))
          + (∫ z in Work.Spaces.Iz, Ul1d_Z α k F Ψ z) :=
      MeasureTheory.integral_add
        (f := fun z => Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z + Ul1d_D α k F Ψ z
          + Ul1d_T α k F Ψ z)
        (g := fun z => Ul1d_Z α k F Ψ z)
        (((hEint.add hUint).add hDint).add hTint) hZint
    have e2 : (∫ z in Work.Spaces.Iz, (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z
            + Ul1d_D α k F Ψ z + Ul1d_T α k F Ψ z))
        = (∫ z in Work.Spaces.Iz, (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z
            + Ul1d_D α k F Ψ z))
          + (∫ z in Work.Spaces.Iz, Ul1d_T α k F Ψ z) :=
      MeasureTheory.integral_add
        (f := fun z => Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z + Ul1d_D α k F Ψ z)
        (g := fun z => Ul1d_T α k F Ψ z)
        ((hEint.add hUint).add hDint) hTint
    have e3 : (∫ z in Work.Spaces.Iz, (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z
            + Ul1d_D α k F Ψ z))
        = (∫ z in Work.Spaces.Iz, (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z))
          + (∫ z in Work.Spaces.Iz, Ul1d_D α k F Ψ z) :=
      MeasureTheory.integral_add
        (f := fun z => Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z)
        (g := fun z => Ul1d_D α k F Ψ z) (hEint.add hUint) hDint
    have e4 : (∫ z in Work.Spaces.Iz, (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z))
        = (∫ z in Work.Spaces.Iz, Ul1d_E α k F Ψ z)
          + (∫ z in Work.Spaces.Iz, Ul1d_U α k F Ψ z) :=
      MeasureTheory.integral_add
        (f := fun z => Ul1d_E α k F Ψ z) (g := fun z => Ul1d_U α k F Ψ z) hEint hUint
    rw [e1, e2, e3, e4]
  have hsplit3 : (∫ z in Work.Spaces.Iz, Ul1d_U α k F Ψ z)
      = ∑ j ∈ Finset.Icc 3 (k + 1), ∫ z in Work.Spaces.Iz, Ul1d_B α k F Ψ j z :=
    MeasureTheory.integral_finsetSum (Finset.Icc 3 (k + 1)) hBint
  have hfin : (∫ z in Work.Spaces.Iz, Ul1d_L α k F Ψ z) ≤ max 1 C1 *
      ((∫ z in Work.Spaces.Iz, Ul1d_E α k F Ψ z)
        + (∑ j ∈ Finset.Icc 3 (k + 1), ∫ z in Work.Spaces.Iz, Ul1d_B α k F Ψ j z)
        + (∫ z in Work.Spaces.Iz, Ul1d_D α k F Ψ z)
        + (∫ z in Work.Spaces.Iz, Ul1d_T α k F Ψ z)
        + (∫ z in Work.Spaces.Iz, Ul1d_Z α k F Ψ z)) := by
    calc (∫ z in Work.Spaces.Iz, Ul1d_L α k F Ψ z)
        ≤ ∫ z in Work.Spaces.Iz, max 1 C1 * (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z
            + Ul1d_D α k F Ψ z + Ul1d_T α k F Ψ z + Ul1d_Z α k F Ψ z) := hmono
      _ = max 1 C1 * ∫ z in Work.Spaces.Iz, (Ul1d_E α k F Ψ z + Ul1d_U α k F Ψ z
            + Ul1d_D α k F Ψ z + Ul1d_T α k F Ψ z + Ul1d_Z α k F Ψ z) := hsplit1
      _ = max 1 C1 * ((∫ z in Work.Spaces.Iz, Ul1d_E α k F Ψ z)
            + (∫ z in Work.Spaces.Iz, Ul1d_U α k F Ψ z)
            + (∫ z in Work.Spaces.Iz, Ul1d_D α k F Ψ z)
            + (∫ z in Work.Spaces.Iz, Ul1d_T α k F Ψ z)
            + (∫ z in Work.Spaces.Iz, Ul1d_Z α k F Ψ z)) := by rw [hsplit2]
      _ = max 1 C1 * ((∫ z in Work.Spaces.Iz, Ul1d_E α k F Ψ z)
            + (∑ j ∈ Finset.Icc 3 (k + 1), ∫ z in Work.Spaces.Iz, Ul1d_B α k F Ψ j z)
            + (∫ z in Work.Spaces.Iz, Ul1d_D α k F Ψ z)
            + (∫ z in Work.Spaces.Iz, Ul1d_T α k F Ψ z)
            + (∫ z in Work.Spaces.Iz, Ul1d_Z α k F Ψ z)) := by rw [hsplit3]
  simpa only [Ul1d_L, Ul1d_E, Ul1d_U, Ul1d_B, Ul1d_D, Ul1d_T, Ul1d_Z] using hfin

end Work.FTS.EllipticEst.TT.ESW
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.aeHtermOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Elementary facts about the angular weight -/


/-- At the two endpoints of `Iθ` the angular weight vanishes. -/
private lemma sEta_eq_zero_of_sin_eq_zero {θ : ℝ} (h : Real.sin (2 * θ) = 0) :
    Work.FTS.EllipticEst.sEta θ = 0 := by
  rw [Work.FTS.EllipticEst.sEta, h]
  exact Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)

/-! ## The derivatives of the slice of `U = z ∂_z u` -/

/-- The `θ`-derivative of `U = z∂_zu` is `z ∂_θ∂_zu`. -/
private lemma pth_grad_eq (u : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ
      = z * Work.Spaces.pth (Work.Spaces.pz u) z θ := by
  show deriv (fun θ' => Work.FTS.EllipticEst.H2W.Ae.grad u z θ') θ
      = z * deriv (fun θ' => Work.Spaces.pz u z θ') θ
  have h : (fun θ' => Work.FTS.EllipticEst.H2W.Ae.grad u z θ')
      = fun θ' => z * Work.Spaces.pz u z θ' := by
    funext θ'; rfl
  rw [h, deriv_const_mul_field]

/-- The second `θ`-derivative of `U = z∂_zu` is `z ∂_θ²∂_zu`. -/
private lemma pthIter_two_grad_eq (u : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ
      = z * Work.Spaces.pthIter 2 (Work.Spaces.pz u) z θ := by
  show deriv (fun θ' => Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ') θ
      = z * deriv (fun θ' => Work.Spaces.pth (Work.Spaces.pz u) z θ') θ
  have h : (fun θ' => Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ')
      = fun θ' => z * Work.Spaces.pth (Work.Spaces.pz u) z θ' := by
    funext θ'; exact pth_grad_eq u z θ'
  rw [h, deriv_const_mul_field]

/-- **Clairaut for the slice of `U = z∂_zu`**: on the open quadrant the second `θ`-derivative of
the slice equals `z ∂_z∂_θ²u`. -/
private lemma slice_second_deriv_eq (u : ℝ → ℝ → ℝ)
    (hS : Work.FTS.EllipticEst.SmoothOpen u) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (deriv (fun θ' => Work.FTS.EllipticEst.H2W.Ae.grad u z θ')) θ
      = z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ := by
  have h1 : deriv (deriv (fun θ' => Work.FTS.EllipticEst.H2W.Ae.grad u z θ')) θ
      = Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ := by
    show deriv (fun θ' => deriv (fun θ'' => Work.FTS.EllipticEst.H2W.Ae.grad u z θ'') θ') θ = _
    rw [show Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.H2W.Ae.grad u)
        = Work.Spaces.pth (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u)) from by
      rw [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]]
    rfl
  rw [h1, pthIter_two_grad_eq u z θ]
  have h3 : Work.Spaces.pthIter 2 (Work.Spaces.pz u) z θ
      = Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ :=
    Work.EllipticEst.RegQ.DzWeak.pthIter_two_pz_eqOn hS
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)
  rw [h3]

/-! ## The `θ`-integral of the `H^0`-integrand -/

/-- The `θ`-integral of the level-`0` `HkIntegrand` is the `w²`-weighted `σ`-mass. -/
private lemma integral_HkIntegrand_zero_eq (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
      = Work.FTS.EllipticEst.AngSecond.w2 z
        * ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  rw [show (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
      = ∫ θ in Work.Spaces.Iθ,
          (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ from
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun θ hθ => Work.FTS.EllipticEst.Endpt.HkIntegrand_zero_eq_sEta α g z hθ)]
  rw [show (fun θ : ℝ => (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      = fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.w2 z
          * ((g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) from by
    funext θ
    rw [Work.FTS.EllipticEst.AngSecond.w2]
    ring]
  rw [MeasureTheory.integral_const_mul]

/-- **The pairing integrand against the second `θ`-derivative of the slice.**  On `Iθ` the
product `U · ∂_θ²U` agrees with `f · f''` for the slice `f` of `U = z∂_zu` (at the endpoints both
integrands carry the vanishing weight `σ`), so the two `θ`-integrals agree. -/
private lemma pairing_integrand_eq (u : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen u)
    {z : ℝ} (hz : 0 < z) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.EllipticEst.H2W.Ae.grad u z θ
        * (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) z θ
        * Work.FTS.EllipticEst.AngSecond.sig θ
      = Work.FTS.EllipticEst.H2W.Ae.grad u z θ
        * deriv (deriv (fun θ' => Work.FTS.EllipticEst.H2W.Ae.grad u z θ')) θ
        * Work.FTS.EllipticEst.sEta θ := by
  by_cases hsin : Real.sin (2 * θ) = 0
  · have hz0 : Work.FTS.EllipticEst.sEta θ = 0 := sEta_eq_zero_of_sin_eq_zero hsin
    have hz1 : Work.FTS.EllipticEst.AngSecond.sig θ = 0 := hz0
    simp only [hz0, hz1, mul_zero]
  · have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := by
      refine ⟨?_, ?_⟩
      · rcases lt_or_ge 0 θ with h | h
        · exact h
        · exfalso
          have hθ0 : θ = 0 := le_antisymm h hθ.1
          rw [hθ0] at hsin
          rw [show (2 : ℝ) * 0 = 0 by norm_num, Real.sin_zero] at hsin
          exact hsin rfl
      · rcases lt_or_ge θ (Real.pi / 2) with h | h
        · exact h
        · exfalso
          have hθπ : θ = Real.pi / 2 := le_antisymm hθ.2 h
          rw [hθπ] at hsin
          rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi] at hsin
          exact hsin rfl
    have hmain : (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) z θ
        = deriv (deriv (fun θ' => Work.FTS.EllipticEst.H2W.Ae.grad u z θ')) θ :=
      (slice_second_deriv_eq u hS hz hθ').symm
    rw [hmain]
    rfl

private lemma integral_pairing_eq (u : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen u)
    {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.Ae.grad u z θ
        * (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) z θ
        * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ)
      = Work.FTS.EllipticEst.AngSecond.w2 z
        * ∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.H2W.Ae.grad u z θ
              * deriv (deriv (fun θ' => Work.FTS.EllipticEst.H2W.Ae.grad u z θ')) θ
              * Work.FTS.EllipticEst.sEta θ := by
  rw [show (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.Ae.grad u z θ
        * (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) z θ
        * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ)
      = ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AngSecond.w2 z
          * (Work.FTS.EllipticEst.H2W.Ae.grad u z θ
            * (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) z θ
            * Work.FTS.EllipticEst.AngSecond.sig θ) from
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    (fun θ hθ => pairing_integrand_eq u hS hz hθ)

/-! ## The mixed-derivative honesty -/

/-- `sEta` is nonnegative on `Iθ`. -/
private lemma sEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ :=
  Work.FTS.EllipticEst.thEta_nonneg hθ

/-- The two forms of the mixed slot agree as functions: `z ∂_θ∂_zu = ∂_θ(z∂_zu)`. -/
private lemma grad_pth_eq_Dz_pth (u : ℝ → ℝ → ℝ) (z θ : ℝ) :
    z * Work.Spaces.pth (Work.Spaces.pz u) z θ = Work.Spaces.pth (Work.Spaces.Dz u) z θ := by
  have hfun : (fun θ' => Work.Spaces.Dz u z θ') = fun θ' => z * Work.Spaces.pz u z θ' := by
    funext θ'; rfl
  show z * deriv (fun θ' => Work.Spaces.pz u z θ') θ = deriv (fun θ' => Work.Spaces.Dz u z θ') θ
  rw [hfun, deriv_const_mul_field]

/-- The second `θ`-derivative of the slice of `D_z u` is the mixed slot `z∂_z∂_θ²u`. -/
private lemma slice_second_deriv_eq_Dz (u : ℝ → ℝ → ℝ)
    (hS : Work.FTS.EllipticEst.SmoothOpen u) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (deriv (fun θ' => Work.Spaces.Dz u z θ')) θ
      = z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ := by
  have h1 : (fun θ' => Work.Spaces.Dz u z θ')
      = fun θ' => Work.FTS.EllipticEst.H2W.Ae.grad u z θ' := by
    funext θ'; rfl
  rw [h1]
  exact slice_second_deriv_eq u hS hz hθ

/-- The level-`0` `HkIntegrand` is the square of the weighted profile. -/
private lemma HkIntegrand_zero_pt (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp only [Work.Spaces.HkIntegrand]
  rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Work.Spaces.DzIter_zero]
  rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num

/-- **The mixed-derivative honesty.**  The `θ`-derivative of the slice of `U = z∂_zu` is the
mixed slot `z∂_z∂_θu = ∂_θ(z∂_zu)`; the slicewise Agmon inequality (`Mine.SliceAgmonWeighted`)
bounds its `σ`-energy by the two energies supplied by `HkMem α 0 U` and
`HkMem α 0 (z∂_z∂_θ²u)`, and that domination makes the global `z`-integral finite. -/
private lemma mixedHkMem_aux {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u))
    (hH : Work.Spaces.HkMem α 0
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)) :
    Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ) := by
  classical
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  obtain ⟨C, hCpos, hCagm⟩ := Work.FTS.EllipticEst.Mine.SliceAgmonWeighted
  -- (0) the second-derivative integrability of the slice of `D_z u`
  have hsecint : ∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv (fun θ' => Work.Spaces.Dz u z θ')) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    intro z hz
    have hbase : MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
      Work.FTS.EllipticEst.H2W.AeLeftClean.hkMemSliceSqSigma hH hz
    refine hbase.congr_fun (fun θ hθ => ?_) measurableSet_Icc
    by_cases hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2)
    · rw [slice_second_deriv_eq_Dz u hS hz hθ']
    · have hsin0 : Real.sin (2 * θ) = 0 := by
        have h1 : θ = 0 ∨ θ = Real.pi / 2 := by
          by_contra hcon
          push_neg at hcon
          exact hθ' ⟨lt_of_le_of_ne hθ.1 (Ne.symm hcon.1), lt_of_le_of_ne hθ.2 hcon.2⟩
        rcases h1 with h1 | h1
        · rw [h1, mul_zero, Real.sin_zero]
        · rw [h1, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      simp only [sEta_eq_zero_of_sin_eq_zero hsin0, mul_zero]
  -- (1) the slicewise integrability of the `σ`-energy of `∂_θ(z∂_zu) = z∂_z∂_θu`
  have hsliceDz : ∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pth (Work.Spaces.Dz u) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    intro z hz
    obtain ⟨M, hM0, hM⟩ := Work.FTS.EllipticEst.Honest.slice_bdd_of_sq_mul_sEta
      (u := fun θ => Work.Spaces.Dz u z θ)
      (Work.FTS.EllipticEst.remov.ws_contDiffOn_slice hS.Dz hz) (hsecint z hz)
    refine MeasureTheory.Integrable.mono'
      ((Work.FTS.EllipticEst.remov.ws_sEta_integrableOn.const_mul (M ^ 2))) ?_ ?_
    · exact ((Work.FTS.EllipticEst.remov.ws_aesm_slice (hS.Dz.pth) hz).pow 2).mul
        (Work.FTS.EllipticEst.remov.ws_sEta_integrableOn.aestronglyMeasurable)
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sEta_nonneg_Iθ hθ))]
      by_cases hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2)
      · have hb : |deriv (fun θ' => Work.Spaces.Dz u z θ') θ| ≤ M := (hM θ hθ').2
        have h2 : (deriv (fun θ' => Work.Spaces.Dz u z θ') θ) ^ 2 ≤ M ^ 2 := by
          rw [← sq_abs (deriv (fun θ' => Work.Spaces.Dz u z θ') θ)]
          exact pow_le_pow_left₀ (abs_nonneg _) hb 2
        have heq : Work.Spaces.pth (Work.Spaces.Dz u) z θ
            = deriv (fun θ' => Work.Spaces.Dz u z θ') θ := rfl
        rw [heq]
        exact mul_le_mul_of_nonneg_right h2 (sEta_nonneg_Iθ hθ)
      · have hsin0 : Real.sin (2 * θ) = 0 := by
          have h1 : θ = 0 ∨ θ = Real.pi / 2 := by
            by_contra hcon
            push_neg at hcon
            exact hθ' ⟨lt_of_le_of_ne hθ.1 (Ne.symm hcon.1), lt_of_le_of_ne hθ.2 hcon.2⟩
          rcases h1 with h1 | h1
          · rw [h1, mul_zero, Real.sin_zero]
          · rw [h1, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
        rw [sEta_eq_zero_of_sin_eq_zero hsin0]
        simp
  -- (2) the slicewise Agmon bound
  have hagm : ∀ z, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.Dz u) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ)
        ≤ C * ((∫ θ in Work.Spaces.Iθ,
              (z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)
            + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz u z θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)) := by
    intro z hz
    have hbase : MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.Dz u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ :=
      Work.FTS.EllipticEst.H2W.AeLeftClean.hkMemSliceSqSigma hU hz
    have hkey := hCagm (fun θ => Work.Spaces.Dz u z θ)
      (Work.FTS.EllipticEst.remov.ws_contDiffOn_slice hS.Dz hz) (hsecint z hz) hbase
    have h1 : (∫ θ in Work.Spaces.Iθ,
          (deriv (fun θ' => Work.Spaces.Dz u z θ') θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.Dz u) z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ := rfl
    have h2 : (∫ θ in Work.Spaces.Iθ,
          (deriv (deriv (fun θ' => Work.Spaces.Dz u z θ')) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ)
        = ∫ θ in Work.Spaces.Iθ,
            (z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      by_cases hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2)
      · rw [slice_second_deriv_eq_Dz u hS hz hθ']
      · have hsin0 : Real.sin (2 * θ) = 0 := by
          have h1' : θ = 0 ∨ θ = Real.pi / 2 := by
            by_contra hcon
            push_neg at hcon
            exact hθ' ⟨lt_of_le_of_ne hθ.1 (Ne.symm hcon.1), lt_of_le_of_ne hθ.2 hcon.2⟩
          rcases h1' with h1' | h1'
          · rw [h1', mul_zero, Real.sin_zero]
          · rw [h1', show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
        rw [sEta_eq_zero_of_sin_eq_zero hsin0]
        ring
    have hkey' : (∫ θ in Work.Spaces.Iθ,
          (deriv (fun θ' => Work.Spaces.Dz u z θ') θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ C * ((∫ θ in Work.Spaces.Iθ,
              (deriv (deriv (fun θ' => Work.Spaces.Dz u z θ')) θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)
            + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz u z θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)) := by
      simpa only [Work.FTS.EllipticEst.sEta] using hkey
    rw [h1, h2] at hkey'
    exact hkey'
  -- (3) continuity of the `HkIntegrand` of the mixed slot on the open quadrant
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0
      (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hVcont : ContinuousOn (fun p : ℝ × ℝ =>
        p.1 * Work.Spaces.pth (Work.Spaces.pz u) p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      (continuous_fst.continuousOn).mul ((hS.pz.pth).continuousOn)
    have hquot : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      have hsinpos : ∀ p : ℝ × ℝ, p ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) →
          (0 : ℝ) < Real.sin (2 * p.2) := by
        intro p hp
        obtain ⟨-, hp2⟩ := Set.mem_prod.mp hp
        exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hp2.1])
          (by linarith [hp2.2, Real.pi_pos])
      refine ContinuousOn.div ?_ ?_ ?_
      · show ContinuousOn (fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))
        exact ((continuous_fst.continuousOn.const_add 1).pow 2).div
          ((continuous_fst.continuousOn).pow 2)
          (fun p hp => pow_ne_zero 2 (ne_of_gt (Set.mem_Ioi.mp (Set.mem_prod.mp hp).1)))
      · have hsin2 : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
          (Real.continuous_sin.comp (continuous_const.mul
            (continuous_snd : Continuous (fun p : ℝ × ℝ => p.2)))).continuousOn
        exact hsin2.rpow_const (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
      · intro p hp
        exact ne_of_gt (Real.rpow_pos_of_pos (hsinpos p hp) _)
    have hmain : ContinuousOn (fun p : ℝ × ℝ =>
        ((fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ) p.1 p.2
          * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (hVcont.mul hquot).pow 2
    refine hmain.congr ?_
    intro p _
    exact HkIntegrand_zero_pt α (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ) p.1 p.2
  -- (4) assemble
  refine Work.FTS.EllipticEst.H2W.Radial.hkMem_of_ae_slice_bound
    (g := fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ)
    (Ψ := fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)
    (L := Work.Spaces.Dz u) (K := C) hCpos hcont ?_ ?_ hH ?_
  · intro z hz
    exact (hsliceDz z hz).congr_fun
      (fun θ _ => by
        show (Work.Spaces.pth (Work.Spaces.Dz u) z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
            = (z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ
        rw [← grad_pth_eq_Dz_pth u z θ]) measurableSet_Icc
  · intro z hz
    have h := hagm z hz
    have h' : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.Dz u) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ)
        = ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        (fun θ _ => by
          show (Work.Spaces.pth (Work.Spaces.Dz u) z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
              = (z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ
          rw [← grad_pth_eq_Dz_pth u z θ])
    rw [h'] at h
    exact h
  · exact hU

/-! ## The main theorem -/

theorem aeHtermOpen : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
    Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) →
    Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) →
    Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
        (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)
      ≤ - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * Work.Spaces.HkSq α 0
            (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u))
        + C * Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
            (Work.FTS.EllipticEst.H2W.Ae.grad u) := by
  classical
  refine ⟨2 * Work.Spaces.eta, by linarith [Work.Spaces.eta_pos], ?_⟩
  intro α u G hAe hU hH
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hAe.smooth
  -- (1) the mixed-derivative honesty and the honesty of the pairing
  have hV : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ) :=
    mixedHkMem_aux hAe hU hH
  have hW : Work.Spaces.HkMem α 0 (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u)) := by
    have hfe : (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ)
        = Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u) := by
      funext z θ; exact (pth_grad_eq u z θ).symm
    rw [← hfe]
    exact hV
  have hIP : Work.FTS.EllipticEst.AngSecond.IPMem (Work.FTS.EllipticEst.H2W.Ae.grad u)
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) :=
    ipMemUHtermFts α u G hAe hU hH
  -- (2) the traces of the slices of `U = z∂_zu` vanish a.e.
  have htr := AeI1.aeDzTraceHk α u G hAe hU hV
  -- (3) the three slice integrals
  set A : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u)) z θ
    with hA
  set B : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ with hB
  set D : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.H2W.Ae.grad u z θ
        * (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) z θ
        * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ with hD
  -- (4) integrability of the three
  have hIntA : MeasureTheory.IntegrableOn A Work.Spaces.Iz := by
    have h := hW.2
    simpa only [hA] using h
  have hIntB : MeasureTheory.IntegrableOn B Work.Spaces.Iz := by
    have h := hU.2
    simpa only [hB] using h
  have hIntD : MeasureTheory.IntegrableOn D Work.Spaces.Iz := by
    have h := hIP.2
    simpa only [hD] using h
  -- (5) the slicewise inequality, almost everywhere in `z`
  have haeslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      D z ≤ -((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * A z
        + (2 * Work.Spaces.eta) * B z := by
    refine (MeasureTheory.ae_restrict_congr_set (s := Set.Ioi (0 : ℝ)) (t := Set.Ici (0 : ℝ))
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))).mp ?_
    filter_upwards [htr, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z htz hzpos
    set f : ℝ → ℝ := fun θ => Work.FTS.EllipticEst.H2W.Ae.grad u z θ with hf
    have hfun : (fun θ => Work.Spaces.Dz u z θ) = f := by
      funext θ; rw [hf]; rfl
    have hfcd : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) := by
      have h := Work.FTS.EllipticEst.remov.ws_contDiffOn_slice hS.Dz hzpos
      rwa [hfun] at h
    have hfun2 : (fun θ => z * Work.Spaces.pz u z θ) = f := by
      funext θ; rw [hf]; rfl
    have ht0 : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have h := htz.1
      rwa [hfun2] at h
    have htπ : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have h := htz.2
      rwa [hfun2] at h
    have hderiv : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        deriv (deriv f) θ = z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ := by
      intro θ hθ
      have h := slice_second_deriv_eq u hS hzpos hθ
      rw [hf]
      exact h
    have h2 : MeasureTheory.IntegrableOn
        (fun θ => (deriv (deriv f) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ := by
      have hbase : MeasureTheory.IntegrableOn
          (fun θ => (z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
        Work.FTS.EllipticEst.H2W.AeLeftClean.hkMemSliceSqSigma hH hzpos
      refine hbase.congr_fun (fun θ hθ => ?_) measurableSet_Icc
      by_cases hsin : Real.sin (2 * θ) = 0
      · have hz0 : Work.FTS.EllipticEst.sEta θ = 0 := sEta_eq_zero_of_sin_eq_zero hsin
        have hz1 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) = 0 := by
          rw [hsin]
          exact Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)
        change (z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ
          = deriv (deriv f) θ ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))
        rw [hz0, hz1, mul_zero, mul_zero]
      · have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := by
          refine ⟨?_, ?_⟩
          · rcases lt_or_ge 0 θ with h | h
            · exact h
            · exfalso
              have hθ0 : θ = 0 := le_antisymm h hθ.1
              rw [hθ0] at hsin
              rw [show (2 : ℝ) * 0 = 0 by norm_num, Real.sin_zero] at hsin
              exact hsin rfl
          · rcases lt_or_ge θ (Real.pi / 2) with h | h
            · exact h
            · exfalso
              have hθπ : θ = Real.pi / 2 := le_antisymm hθ.2 h
              rw [hθπ] at hsin
              rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi] at hsin
              exact hsin rfl
        rw [hderiv θ hθ']
        rfl
    -- the bounds and the sharp one-dimensional inequality
    obtain ⟨M, hM0, hMb, hMd⟩ := sliceBoundsOfTraceFts hfcd ht0 htπ h2
    have hsharp := sliceSharpFts hfcd ⟨M, hM0, hMb, hMd⟩ h2
    have hsharp' : (∫ θ in Work.Spaces.Iθ,
          f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.sEta θ)
        ≤ -((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
            * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + (2 * Work.Spaces.eta)
            * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
      simpa only [Work.FTS.EllipticEst.sEta] using hsharp
    -- the three slice integrals in the `σ`-form
    have eD : D z = Work.FTS.EllipticEst.AngSecond.w2 z
        * (∫ θ in Work.Spaces.Iθ,
            f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.sEta θ) := by
      simp only [hD]
      rw [integral_pairing_eq u hS hzpos]
    have eA : A z = Work.FTS.EllipticEst.AngSecond.w2 z
        * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
      simp only [hA]
      rw [integral_HkIntegrand_zero_eq, hf]
      refine congrArg (fun t => Work.FTS.EllipticEst.AngSecond.w2 z * t) ?_
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        (fun θ _ => by simp only [Work.Spaces.pth])
    have eB : B z = Work.FTS.EllipticEst.AngSecond.w2 z
        * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
      simp only [hB]
      rw [integral_HkIntegrand_zero_eq, hf]
    rw [eD, eA, eB]
    calc Work.FTS.EllipticEst.AngSecond.w2 z
          * (∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.sEta θ)
        ≤ Work.FTS.EllipticEst.AngSecond.w2 z
            * (-((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
                * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
              + (2 * Work.Spaces.eta)
                * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) :=
          mul_le_mul_of_nonneg_left hsharp' (Work.FTS.EllipticEst.AngSecond.w2_nonneg z)
      _ = -((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
            * (Work.FTS.EllipticEst.AngSecond.w2 z
              * ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + (2 * Work.Spaces.eta) * (Work.FTS.EllipticEst.AngSecond.w2 z
              * ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
          ring
  -- (6) integrate in `z`
  have hIntR : MeasureTheory.IntegrableOn
      (fun z => -((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * A z
        + (2 * Work.Spaces.eta) * B z) Work.Spaces.Iz :=
    (hIntA.const_mul (-((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)))).add
      (hIntB.const_mul (2 * Work.Spaces.eta))
  have hmono : (∫ z in Work.Spaces.Iz, D z)
      ≤ ∫ z in Work.Spaces.Iz, (-((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * A z
          + (2 * Work.Spaces.eta) * B z) :=
    MeasureTheory.integral_mono_ae hIntD hIntR haeslice
  have hsplit : (∫ z in Work.Spaces.Iz, (-((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * A z
        + (2 * Work.Spaces.eta) * B z))
      = -((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * (∫ z in Work.Spaces.Iz, A z)
        + (2 * Work.Spaces.eta) * (∫ z in Work.Spaces.Iz, B z) := by
    rw [MeasureTheory.integral_add
        (hIntA.const_mul (-((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))))
        (hIntB.const_mul (2 * Work.Spaces.eta)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hAeq : (∫ z in Work.Spaces.Iz, A z)
      = Work.Spaces.HkSq α 0 (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u)) := by
    rw [Work.Spaces.HkSq, hA]
  have hBeq : (∫ z in Work.Spaces.Iz, B z)
      = Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) := by
    rw [Work.Spaces.HkSq, hB]
  have hIPeq : Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)
      = ∫ z in Work.Spaces.Iz, D z := by
    rw [Work.FTS.EllipticEst.AngSecond.IP, hD]
  calc Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
        (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)
      = ∫ z in Work.Spaces.Iz, D z := hIPeq
    _ ≤ ∫ z in Work.Spaces.Iz, (-((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * A z
          + (2 * Work.Spaces.eta) * B z) := hmono
    _ = -((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * (∫ z in Work.Spaces.Iz, A z)
          + (2 * Work.Spaces.eta) * (∫ z in Work.Spaces.Iz, B z) := hsplit
    _ = -((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
          * Work.Spaces.HkSq α 0 (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u))
        + (2 * Work.Spaces.eta)
          * Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
              (Work.FTS.EllipticEst.H2W.Ae.grad u) := by
        rw [hAeq, hBeq,
          Work.FTS.EllipticEst.Dispatch.HkSq_zero_eq_IP α (Work.FTS.EllipticEst.H2W.Ae.grad u)]

end Work.FTS.EllipticEst.TT
end
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow10aux.starH_smoothOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Row 10 (star half): `(z+1)/z · ℛ(Φ̃_*)` is `C^∞` on the open quadrant

This file proves `starH_smoothOpen`.  The statement is a *smoothness* statement only:

* `StarPkgo.smooth` gives `SmoothOpen Φs`, i.e. `C^∞` of `Φs` on the open quadrant
  `Q0 = (0,∞) × (0,π/2)`;
* `Θ_*(α) = Θ α (F_*)` is `sin(2θ)/(2(1+z))` there (`L₁₂(F_*) = 2α/(1+z)`), hence `C^∞`
  (`smoothOpen_Theta_Fstar`), so `Φ̃_* = Φ_s - Θ_*(α)` is `C^∞` on `Q0`;
* `ℛ` is a rational expression in `Ψ`, `∂_zΨ`, `∂_θΨ`, `sin θ`, `cos θ` divided by
  `cos θ ≠ 0` on `Q0`, and `∂_z`, `∂_θ` preserve interior `C^∞` (`contDiffOn_pz`,
  `contDiffOn_pth`), so `ℛ(Φ̃_*)` is `C^∞` on `Q0` (`smoothOpen_Rop`);
* the radial factor `(z+1)/z` is `C^∞` on `Q0` because `z > 0` there.

Nothing here needs the `z = 0`-smoothness (`SmoothQuad`, `z > -1`) that the primed
interface does not provide — which is why the proof does not go through the delivered
`SmoothQuad`-level lemma `row10aux.Rop_PhiTs_smoothQuad`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.NonlinRows.NRow10aux

set_option autoImplicit false

/-! ## Closure of `SmoothOpen` under the pointwise algebra

(`Work.FTS.EllipticEst` only exposes the `SmoothQuad`-level algebra; these are the
`Q0`-analogues, obtained by the same one-line `ContDiffOn` arguments.) -/

/-- `SmoothOpen` is closed under addition. -/
theorem smoothOpen_add {F G : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => F z θ + G z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => F z θ + G z θ)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z θ => F z θ + G z θ)
      = fun p : ℝ × ℝ => Function.uncurry F p + Function.uncurry G p := rfl
  rw [h]
  exact hF.add hG

/-- `SmoothOpen` is closed under subtraction. -/
theorem smoothOpen_sub {F G : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => F z θ - G z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => F z θ - G z θ)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z θ => F z θ - G z θ)
      = fun p : ℝ × ℝ => Function.uncurry F p - Function.uncurry G p := rfl
  rw [h]
  exact hF.sub hG

/-- `SmoothOpen` is closed under products. -/
theorem smoothOpen_mul {F G : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => F z θ * G z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => F z θ * G z θ)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z θ => F z θ * G z θ)
      = fun p : ℝ × ℝ => Function.uncurry F p * Function.uncurry G p := rfl
  rw [h]
  exact hF.mul hG

/-! ## The datum `Φ̃_* = Φ_s - Θ_*(α)` -/

/-- The `SmoothQuad`-smoothness of `Θ_*(α)` restricts to the open quadrant `Q0`. -/
theorem smoothOpen_Theta_Fstar {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Theta α (Work.Construction.Fstar α)) := by
  have hquad : Work.FTS.LocData.SmoothQuad
      (Work.Construction.Theta α (Work.Construction.Fstar α)) :=
    Work.FTS.Nonlinear.Pieces.RNP.row10aux.smoothQuad_Theta_Fstar hα hα1
  have hsub : Work.FTS.EllipticEst.Q0 ⊆ Work.Spaces.quadU := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ⟨Set.mem_Ioi.mpr (by linarith), Set.mem_Ioo.mpr ⟨hθ0, hθ1⟩⟩
  exact hquad.mono hsub

/-- `Φ̃_* = Φ_s - Θ_*(α)` is `C^∞` on the open quadrant as soon as `Φ_s` is. -/
theorem smoothOpen_PhiTs {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) := by
  have hΘ : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Theta α (Work.Construction.Fstar α)) :=
    smoothOpen_Theta_Fstar hα hα1
  have hsub := smoothOpen_sub hs.smooth hΘ
  show Work.FTS.EllipticEst.SmoothOpen
    (fun z θ => Φs z θ - Work.Construction.Theta α (Work.Construction.Fstar α) z θ)
  exact hsub

/-! ## `ℛ` preserves `C^∞` on the open quadrant -/

/-- **`ℛ(Ψ)` is `C^∞` on the open quadrant when `Ψ` is.**  The only point to check is the
division by `cos θ`, legitimate because `cos θ > 0` for `θ ∈ (0, π/2)`; the two derivatives
`∂_zΨ`, `∂_θΨ` are `C^∞` there by `contDiffOn_pz`/`contDiffOn_pth`.  This is the
`SmoothOpen`-analogue of `row10aux.smoothQuad_Rop`. -/
theorem smoothOpen_Rop {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Rop α Ψ) := by
  have hQ : IsOpen Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.isOpen_Q0
  have hpz : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pz Ψ)) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.LocData.contDiffOn_pz hQ hΨ
  have hpth : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pth Ψ)) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.LocData.contDiffOn_pth hQ hΨ
  have hsin : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin p.2) Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_sin.comp contDiff_snd).contDiffOn
  have hcos : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.cos p.2) Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_cos.comp contDiff_snd).contDiffOn
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => 2 * Real.sin p.2 * Function.uncurry Ψ p)
      Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_const.mul hsin).mul hΨ
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
        + Real.cos p.2 * Function.uncurry (Work.Spaces.pth Ψ) p)
      Work.FTS.EllipticEst.Q0 :=
    (h1.add h2).add h3
  have hne : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.cos p.2 ≠ 0 := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)
  refine (hnum.div hcos hne).congr ?_
  intro p _
  obtain ⟨z, θ⟩ := p
  rfl

/-! ## The radial factor and the target -/

/-- The radial factor `(z+1)/z` is `C^∞` on the open quadrant (its only singularity is at
`z = 0`, which is outside `Q0`). -/
theorem smoothOpen_zPlusOne_div_z :
    Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => (z + 1) / z) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z (_ : ℝ) => (z + 1) / z)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z (_ : ℝ) => (z + 1) / z)
      = fun p : ℝ × ℝ => (p.1 + 1) / p.1 := rfl
  rw [h]
  refine ContDiffOn.div (contDiffOn_fst.add contDiffOn_const) contDiffOn_fst ?_
  intro p hp
  exact ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1

theorem starH_smoothOpen :
    ∀ {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}, 0 < α → α ≤ 1 →
      Work.FTS.VocabO.StarPkgo α Cs Φs →
      Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) := by
  intro α Cs Φs hα hα1 hs
  have hΦ : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) :=
    smoothOpen_PhiTs hα hα1 hs
  have hR : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) :=
    smoothOpen_Rop hΦ
  exact smoothOpen_mul smoothOpen_zPlusOne_div_z hR

end Work.FTS.NonlinRows.NRow10aux
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row8 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP

set_option linter.unusedVariables false


end Work.FTS.Nonlinear.Pieces.RNP
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.Rl1.WAngEnergyLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.Rl1

set_option autoImplicit false

/-! ## The weighted angular energy of an `ℋ^k`-function

`∫_{z>0} w(z) ∫_θ f(z,θ)² dθ dz ≤ HkSq α k f` is a *one-term* consequence of the definition of
`HkSq`: the `i = 0` term of the `D_z`-part of `HkIntegrand α k f` is
`(f z θ · w z / sin(2θ)^{η/2})²`, and on the open quadrant the factor `w z / sin(2θ)^{η/2}` is
`≥ 1` (indeed `≥ w z ≥ 1`), so it dominates `w z · f z θ²`.  The two `L¹`-conjuncts follow from
the honest integrability of the `ℋ^k`-integrand slice (`HkMem`) by domination; the
`AEStronglyMeasurable` conjunct only needs the smoothness of `f`, through the joint
measurability of `(z,θ) ↦ f z θ²` on the open quadrant (`Spaces.aesm_of_continuousOn_Qd`).

Everything here rests on `[propext, Classical.choice, Quot.sound]`. -/

/-! ### Elementary facts about the radial weight -/

/-- On `z > 0` the radial weight `w z = ((1+z)/z)²` is `≥ 1`. -/
private lemma one_le_w_of_pos_prv {z : ℝ} (hz : 0 < z) : 1 ≤ Work.Spaces.w z := by
  have hz2 : (0 : ℝ) < z ^ 2 := pow_pos hz 2
  rw [Work.Spaces.w, one_le_div hz2]
  exact pow_le_pow_left₀ (le_of_lt hz) (by linarith) 2

/-- The radial weight is nonnegative everywhere (at `z = 0` Lean's totalised division
gives the value `0`, which is irrelevant). -/
private lemma w_nonneg_prv (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The open interval `(0,π/2)` and the closed `Iθ` carry the same restriction of Lebesgue
measure (they differ by the two null endpoints). -/
private lemma restrict_Ioo_eq_restrict_Iθ_prv :
    volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) = volume.restrict Work.Spaces.Iθ :=
  MeasureTheory.Measure.restrict_congr_set
    (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)

/-! ### The pointwise domination -/



/-! ### The target -/


end Work.FTS.Nonlinear.Pieces.Rl1
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgEngine =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary facts -/

/-- The `ℋ^k`-integrand is nonnegative. -/
lemma HkIntegrand_nonneg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ Work.Spaces.HkIntegrand α k f z θ := by
  rw [Work.Spaces.HkIntegrand]
  exact add_nonneg (Work.Spaces.hkZSum_nonneg α k f z θ)
    (Work.Spaces.hkMixedSum_nonneg α k f z θ)

/-- The `θ`-slice of a `SmoothQuad` function is a.e.-measurable on `Iθ`. -/
lemma slice_aem_of_smoothQuad {f : ℝ → ℝ → ℝ} (h : Work.FTS.LocData.SmoothQuad f)
    {z : ℝ} (hz : 0 < z) :
    AEMeasurable (fun θ : ℝ => f z θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hcd : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => f z θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Work.FTS.LocData.contDiffOn_slice_θ h (show (-1 : ℝ) < z by linarith)
  have h1 : AEMeasurable (fun θ : ℝ => f z θ)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hcd.continuousOn.aemeasurable measurableSet_Ioo
  rwa [← restrict_Iθ_eq_Ioo] at h1

/-- `√x ≤ 2` for `x ≤ 4`. -/
lemma sqrt_le_two {x : ℝ} (hx : x ≤ 4) : Real.sqrt x ≤ 2 := by
  have h := Real.sqrt_le_sqrt hx
  have h4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rwa [h4] at h

/-- `√(π/2) ≤ 2`. -/
lemma sqrt_pi_div_two_le_two : Real.sqrt (Real.pi / 2) ≤ 2 :=
  sqrt_le_two (by linarith [Real.pi_le_four])

/-- The angular volume in `ENNReal`: `∫⁻_θ 1 = ofReal (π/2)`. -/
lemma lintegral_one_Iθ : (∫⁻ _θ in Work.Spaces.Iθ, (1 : ENNReal)) = ENNReal.ofReal (Real.pi / 2) := by
  rw [MeasureTheory.setLIntegral_const, one_mul]
  rw [Work.Spaces.Iθ, Real.volume_Icc]
  norm_num

/-! ## The radial Hölder engine -/

/-- **The radial Hölder engine.**  If `A r ≤ ofReal (c·(r/(1+r)²)·√(J r))` a.e. on `r > 0`,
with `J` integrable and nonnegative, then

  `∫⁻_{r>0} A r ≤ ofReal (c · √(∫_{r>0} J r))`.

The proof is Cauchy–Schwarz for the two `L²`-functions `r ↦ c·r/(1+r)²` and `r ↦ √(J r)`,
using `∫_{r>0} (r/(1+r)²)² ≤ 1`. -/
theorem radial_of_sqrt {J : ℝ → ℝ} {A : ℝ → ENNReal} {c : ℝ}
    (hc : 0 ≤ c) (hJint : IntegrableOn J (Set.Ioi (0 : ℝ)))
    (hJnn : ∀ r, 0 ≤ J r)
    (hA : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      A r ≤ ENNReal.ofReal (c * (r / (1 + r) ^ 2) * Real.sqrt (J r))) :
    (∫⁻ r in Set.Ioi (0 : ℝ), A r)
      ≤ ENNReal.ofReal (c * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), J r)) := by
  have hcont : ContinuousOn (fun r : ℝ => c * (r / (1 + r) ^ 2)) (Set.Ioi (0 : ℝ)) := by
    refine continuousOn_const.mul (continuousOn_id.div ?_ ?_)
    · exact (continuousOn_const.add continuousOn_id).pow 2
    · intro r hr
      have hr0 : 0 < r := hr
      exact (pow_pos (by linarith : (0 : ℝ) < 1 + r) 2).ne'
  have hLae : AEMeasurable (fun r : ℝ => ENNReal.ofReal (c * (r / (1 + r) ^ 2)))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    (hcont.aemeasurable measurableSet_Ioi).ennreal_ofReal
  have hJae : AEMeasurable J (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    hJint.aestronglyMeasurable.aemeasurable
  have hMae : AEMeasurable (fun r : ℝ => ENNReal.ofReal (Real.sqrt (J r)))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := (hJae.sqrt).ennreal_ofReal
  have h22 : Real.HolderConjugate 2 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hhold := ENNReal.lintegral_mul_le_Lp_mul_Lq
    (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) (p := 2) (q := 2) h22 hLae hMae
  -- ### the monotonicity step, with the pointwise bound rewritten as a product
  have hmono : (∫⁻ r in Set.Ioi (0 : ℝ), A r)
      ≤ ∫⁻ r, ENNReal.ofReal (c * (r / (1 + r) ^ 2)) * ENNReal.ofReal (Real.sqrt (J r))
        ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine le_trans (lintegral_mono_ae hA) ?_
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    exact le_of_eq (ENNReal.ofReal_mul
      (mul_nonneg hc (div_nonneg hr0.le (by positivity))))
  -- ### the `L`-factor `r ↦ ofReal (c·r/(1+r)²)`
  have hc2int : Integrable (fun r : ℝ => (c * (r / (1 + r) ^ 2)) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h1 : Integrable (fun r : ℝ => (r / (1 + r) ^ 2) ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      Work.FTS.Nonlinear.Pieces.rl1Tools.integrableOn_G_sq
    refine (h1.const_mul (c ^ 2)).congr ?_
    filter_upwards with r
    ring
  have hInt0 : 0 ≤ ∫ r in Set.Ioi (0 : ℝ), (c * (r / (1 + r) ^ 2)) ^ 2 :=
    integral_nonneg fun r => sq_nonneg _
  have hLpt : (fun r : ℝ => (fun r : ℝ => ENNReal.ofReal (c * (r / (1 + r) ^ 2))) r ^ (2 : ℝ))
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))]
      fun r : ℝ => ENNReal.ofReal ((c * (r / (1 + r) ^ 2)) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    rw [ENNReal.ofReal_rpow_of_nonneg
      (mul_nonneg hc (div_nonneg hr0.le (by positivity))) (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.rpow_two]
  have hLeq : (∫⁻ r, (fun r : ℝ => ENNReal.ofReal (c * (r / (1 + r) ^ 2))) r ^ (2 : ℝ)
        ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
      = ENNReal.ofReal (∫ r in Set.Ioi (0 : ℝ), (c * (r / (1 + r) ^ 2)) ^ 2) := by
    rw [lintegral_congr_ae hLpt]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hc2int
      (Eventually.of_forall fun r => sq_nonneg _)).symm
  have hAle : Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (c * (r / (1 + r) ^ 2)) ^ 2) ≤ c := by
    have hval : (∫ r in Set.Ioi (0 : ℝ), (c * (r / (1 + r) ^ 2)) ^ 2)
        = c ^ 2 * ∫ r in Set.Ioi (0 : ℝ), (r / (1 + r) ^ 2) ^ 2 := by
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.integral_congr_ae (Eventually.of_forall fun r => by ring)
    rw [hval, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
    exact le_trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_one.mpr Work.FTS.Nonlinear.Pieces.rl1Tools.integral_G_sq_le_one) hc)
      (le_of_eq (mul_one c))
  have hLbound : (∫⁻ r, (fun r : ℝ => ENNReal.ofReal (c * (r / (1 + r) ^ 2))) r ^ (2 : ℝ)
        ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal c := by
    rw [hLeq, ENNReal.ofReal_rpow_of_nonneg hInt0 (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    exact ENNReal.ofReal_le_ofReal (by rwa [← Real.sqrt_eq_rpow])
  -- ### the `M`-factor `r ↦ ofReal (√(J r))`
  have hJint0 : 0 ≤ ∫ r in Set.Ioi (0 : ℝ), J r := integral_nonneg hJnn
  have hMpt : (fun r : ℝ => (fun r : ℝ => ENNReal.ofReal (Real.sqrt (J r))) r ^ (2 : ℝ))
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))]
      fun r : ℝ => ENNReal.ofReal (J r) := by
    filter_upwards with r
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.rpow_two, Real.sq_sqrt (hJnn r)]
  have hMeq : (∫⁻ r, (fun r : ℝ => ENNReal.ofReal (Real.sqrt (J r))) r ^ (2 : ℝ)
        ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
      = ENNReal.ofReal (∫ r in Set.Ioi (0 : ℝ), J r) := by
    rw [lintegral_congr_ae hMpt]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hJint
      (Eventually.of_forall hJnn)).symm
  have hMbound : (∫⁻ r, (fun r : ℝ => ENNReal.ofReal (Real.sqrt (J r))) r ^ (2 : ℝ)
        ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal (Real.sqrt (∫ r in Set.Ioi (0 : ℝ), J r)) := by
    rw [hMeq, ENNReal.ofReal_rpow_of_nonneg hJint0 (by norm_num : (0 : ℝ) ≤ 1 / 2),
      Real.sqrt_eq_rpow]
  refine le_trans (le_trans hmono hhold) ?_
  refine le_trans (mul_le_mul' hLbound hMbound) ?_
  exact le_of_eq (ENNReal.ofReal_mul hc).symm

/-! ## The slice of the `ℋ⁴`-integrand as a function of `r` -/

/-- `Jfun α g r` is the `θ`-slice of the `ℋ⁴`-integrand of `g`: the `r`-integrand of `HkSq`. -/
def Jfun (α : ℝ) (g : ℝ → ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ

/-- `HkSq α 4 g` is the integral of `Jfun α g` over `(0,∞)`. -/
lemma HkSq_eq_Ioi (α : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 4 g = ∫ r in Set.Ioi (0 : ℝ), Jfun α g r := by
  rw [Work.Spaces.HkSq, Work.Spaces.Iz, MeasureTheory.integral_Ici_eq_integral_Ioi]
  rfl

lemma Jfun_nonneg (α : ℝ) (g : ℝ → ℝ → ℝ) (r : ℝ) : 0 ≤ Jfun α g r :=
  integral_nonneg fun θ => HkIntegrand_nonneg α 4 g r θ

lemma Jfun_integrableOn {α : ℝ} {g : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 4 g) :
    IntegrableOn (Jfun α g) (Set.Ioi (0 : ℝ)) := by
  have h : IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 g z θ) (Set.Ici (0 : ℝ)) := hmem.2
  exact (h.mono_set (fun x hx => show (0 : ℝ) ≤ x from le_of_lt hx))

/-! ## The angular Cauchy–Schwarz step -/

/-- **The angular step.**  If the weighted square of `k` is dominated by the `ℋ⁴`-integrand of
`g` (`w(z)²·k(z,θ)² ≤ HkIntegrand α 4 g z θ` a.e.), then the angular lintegral of `|k|` is
bounded by `ofReal (2·√(Jfun α g r)/w r)`:
Cauchy–Schwarz in `θ` against `1`, using `∫_θ 1 = π/2 ≤ 4`. -/
lemma ang_le_of_slot {α : ℝ} {g k : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g)
    (hkaem : ∀ r : ℝ, 0 < r → AEMeasurable (fun θ : ℝ => k r θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hslot : ∀ r : ℝ, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.w r) ^ 2 * (k r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g r θ)
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|)
      ≤ ENNReal.ofReal (2 * Real.sqrt (Jfun α g r) / Work.Spaces.w r) := by
  have hw : 0 < Work.Spaces.w r := w_pos_of_pos hr
  have h22 : Real.HolderConjugate 2 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h1 : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |k r θ|)
      ≤ (∫⁻ θ in Work.Spaces.Iθ, (ENNReal.ofReal |k r θ|) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
        * (∫⁻ θ in Work.Spaces.Iθ, (1 : ENNReal) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (p := 2) (q := 2) h22 (f := fun θ : ℝ => ENNReal.ofReal |k r θ|)
      (g := fun _ : ℝ => (1 : ENNReal)) (hkaem r hr).abs.ennreal_ofReal aemeasurable_const
    simpa using h
  have hk2int : IntegrableOn (fun θ : ℝ => (k r θ) ^ 2) Work.Spaces.Iθ := by
    refine Integrable.mono' (g := fun θ : ℝ =>
      Work.Spaces.HkIntegrand α 4 g r θ / (Work.Spaces.w r) ^ 2) ?_ ?_ ?_
    · exact (hmem.1 r hr.le).div_const ((Work.Spaces.w r) ^ 2)
    · exact ((hkaem r hr).pow_const 2).aestronglyMeasurable
    · filter_upwards [hslot r hr] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hw2 : 0 < (Work.Spaces.w r) ^ 2 := pow_pos hw 2
      rw [le_div_iff₀ hw2]
      exact le_of_eq_of_le (by ring :
        (k r θ) ^ 2 * (Work.Spaces.w r) ^ 2 = (Work.Spaces.w r) ^ 2 * (k r θ) ^ 2) hθ
  have hUpt : (fun θ : ℝ => (ENNReal.ofReal |k r θ|) ^ (2 : ℝ))
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      fun θ : ℝ => ENNReal.ofReal ((k r θ) ^ 2) := by
    filter_upwards with θ
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.rpow_two, sq_abs]
  have hU : (∫⁻ θ in Work.Spaces.Iθ, (ENNReal.ofReal |k r θ|) ^ (2 : ℝ))
      = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (k r θ) ^ 2) := by
    rw [lintegral_congr_ae hUpt]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hk2int
      (Eventually.of_forall fun θ => sq_nonneg _)).symm
  have hV : (∫⁻ θ in Work.Spaces.Iθ, (1 : ENNReal) ^ (2 : ℝ)) = ENNReal.ofReal (Real.pi / 2) := by
    rw [show (fun θ : ℝ => (1 : ENNReal) ^ (2 : ℝ)) = fun _ : ℝ => (1 : ENNReal) from by
      funext θ; simp]
    exact lintegral_one_Iθ
  have hE0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (k r θ) ^ 2 := integral_nonneg fun θ => sq_nonneg _
  have hU2 : (∫⁻ θ in Work.Spaces.Iθ, (ENNReal.ofReal |k r θ|) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      = ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, (k r θ) ^ 2)) := by
    rw [hU, ENNReal.ofReal_rpow_of_nonneg hE0 (by norm_num : (0 : ℝ) ≤ 1 / 2),
      Real.sqrt_eq_rpow]
  have hV2 : (∫⁻ θ in Work.Spaces.Iθ, (1 : ENNReal) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal 2 := by
    rw [hV, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Real.sqrt_eq_rpow]
    exact sqrt_pi_div_two_le_two
  have hEbound : Real.sqrt (∫ θ in Work.Spaces.Iθ, (k r θ) ^ 2)
      ≤ Real.sqrt (Jfun α g r) / Work.Spaces.w r := by
    have h2 : (Work.Spaces.w r) ^ 2 * (∫ θ in Work.Spaces.Iθ, (k r θ) ^ 2) ≤ Jfun α g r := by
      rw [Jfun, ← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ =>
        mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hmem.1 r hr.le) ?_
      exact hslot r hr
    have h3 : Real.sqrt (Work.Spaces.w r ^ 2 * ∫ θ in Work.Spaces.Iθ, (k r θ) ^ 2)
        ≤ Real.sqrt (Jfun α g r) := Real.sqrt_le_sqrt h2
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hw.le] at h3
    rw [le_div_iff₀ hw, mul_comm]
    exact h3
  refine le_trans h1 ?_
  have hstep : ENNReal.ofReal (Real.sqrt (∫ θ in Work.Spaces.Iθ, (k r θ) ^ 2))
        * ENNReal.ofReal 2
      ≤ ENNReal.ofReal (2 * Real.sqrt (Jfun α g r) / Work.Spaces.w r) := by
    rw [mul_comm, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h3 : 2 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (k r θ) ^ 2)
        ≤ 2 * Real.sqrt (Jfun α g r) / Work.Spaces.w r := by
      have h4 := mul_le_mul_of_nonneg_left hEbound (by norm_num : (0 : ℝ) ≤ 2)
      rwa [show (2 : ℝ) * (Real.sqrt (Jfun α g r) / Work.Spaces.w r)
          = 2 * Real.sqrt (Jfun α g r) / Work.Spaces.w r from by ring] at h4
    exact h3
  exact le_trans (mul_le_mul' (le_of_eq hU2) hV2) hstep

/-- `w(z)²·(D_z g)² ≤ HkIntegrand α 4 g`: the `D_z¹`-slot of the `ℋ⁴`-integrand. -/
lemma w2_Dz_sq_le_HkIntegrand (α : ℝ) {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.w z) ^ 2 * (Work.Spaces.Dz g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hs := sin_two_pos hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hspos : 0 < Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hs _
  have hsle : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one hs.le hs1 (by norm_num [Work.Spaces.eta])
  have hw : 0 ≤ Work.Spaces.w z := w_nonneg z
  have h1 : Work.Spaces.w z ≤ Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := by
    rw [le_div_iff₀ hspos]
    nlinarith [hsle, hw]
  have hstep : (Work.Spaces.w z * |Work.Spaces.Dz g z θ|) ^ 2
      ≤ (Work.Spaces.Dz g z θ * (Work.Spaces.w z
          / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    have hle := mul_le_mul_of_nonneg_right h1 (abs_nonneg (Work.Spaces.Dz g z θ))
    rw [mul_comm (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))
      |Work.Spaces.Dz g z θ|] at hle
    have h5 : (|Work.Spaces.Dz g z θ| * (Work.Spaces.w z
        / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
        = (Work.Spaces.Dz g z θ * (Work.Spaces.w z
          / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs]
    rw [← h5]
    exact pow_le_pow_left₀ (mul_nonneg hw (abs_nonneg _)) hle 2
  have hdep : (Work.Spaces.w z) ^ 2 * (Work.Spaces.Dz g z θ) ^ 2
      = (Work.Spaces.w z * |Work.Spaces.Dz g z θ|) ^ 2 := by rw [mul_pow, sq_abs]
  rw [hdep]
  refine le_trans hstep ?_
  have hslot := Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ 1 (by norm_num)
  simpa [Work.Spaces.Dz, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using hslot

/-! ## The three basis bounds -/

/-- **The `rl¹`-norm of `g` itself.** -/
theorem envG {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g)
    (hmem : Work.Spaces.HkMem α 4 g) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |g r θ|))
      ≤ ENNReal.ofReal (2 * Work.Spaces.HkNorm α 4 g) := by
  have hslot : ∀ r : ℝ, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.w r) ^ 2 * (g r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g r θ := by
    intro r hr
    rw [restrict_Iθ_eq_Ioo]
    exact ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => w2_sq_le_HkIntegrand α hr hθ)
  have hA : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |g r θ|)
        ≤ ENNReal.ofReal (2 * (r / (1 + r) ^ 2) * Real.sqrt (Jfun α g r)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    refine le_trans (mul_le_mul' le_rfl (ang_le_of_slot hα hsm hmem
      (fun r hr => slice_aem_of_smoothQuad hsm hr) hslot hr0)) ?_
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hr0.le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have heq : r⁻¹ * (2 * Real.sqrt (Jfun α g r) / Work.Spaces.w r)
        = 2 * (r / (1 + r) ^ 2) * Real.sqrt (Jfun α g r) := by
      rw [Work.Spaces.w]
      field_simp
    rw [heq]
  have hmain := radial_of_sqrt (J := Jfun α g) (A := fun r : ℝ => ENNReal.ofReal r⁻¹ *
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |g r θ|)) (c := 2)
    (by norm_num) (Jfun_integrableOn hmem) (Jfun_nonneg α g) hA
  rw [← HkSq_eq_Ioi α g] at hmain
  simpa [Work.Spaces.HkNorm] using hmain

/-- **The `rl¹`-norm of `D_z g`.** -/
theorem envDz {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g)
    (hmem : Work.Spaces.HkMem α 4 g) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.Dz g r θ|))
      ≤ ENNReal.ofReal (2 * Work.Spaces.HkNorm α 4 g) := by
  have hsm2 : Work.FTS.LocData.SmoothQuad (Work.Spaces.Dz g) :=
    Work.FTS.LocData.contDiffOn_Dz Work.Spaces.isOpen_quadU hsm
  have hslot : ∀ r : ℝ, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.w r) ^ 2 * (Work.Spaces.Dz g r θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 g r θ := by
    intro r hr
    rw [restrict_Iθ_eq_Ioo]
    exact ae_restrict_of_forall_mem measurableSet_Ioo
      (fun θ hθ => w2_Dz_sq_le_HkIntegrand α hr hθ)
  have hA : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.Dz g r θ|)
        ≤ ENNReal.ofReal (2 * (r / (1 + r) ^ 2) * Real.sqrt (Jfun α g r)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    refine le_trans (mul_le_mul' le_rfl (ang_le_of_slot hα hsm hmem
      (fun r hr => slice_aem_of_smoothQuad hsm2 hr) hslot hr0)) ?_
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hr0.le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have heq : r⁻¹ * (2 * Real.sqrt (Jfun α g r) / Work.Spaces.w r)
        = 2 * (r / (1 + r) ^ 2) * Real.sqrt (Jfun α g r) := by
      rw [Work.Spaces.w]
      field_simp
    rw [heq]
  have hmain := radial_of_sqrt (J := Jfun α g) (A := fun r : ℝ => ENNReal.ofReal r⁻¹ *
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.Dz g r θ|)) (c := 2)
    (by norm_num) (Jfun_integrableOn hmem) (Jfun_nonneg α g) hA
  rw [← HkSq_eq_Ioi α g] at hmain
  simpa [Work.Spaces.HkNorm] using hmain


end Work.FTS.Nonlinear.Pieces.rl1Tools
end
end
