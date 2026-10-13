import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.SourceBound

/-- **The single-integration identity for `Lzero1`.**

For `u` of class `C²` on the open interval `(0, π/2)` and `0 < ε < b < π/2`,

  `tan b · u b = ∫_ε^b Lzero1 u + u'(b) - u'(ε) + tan ε · u ε + 6 ∫_ε^b u`.

Indeed `Lzero1 u = -u'' + ∂_θ(tan θ · u) - 6u`, so two applications of the fundamental
theorem of calculus (for `u'` and for `tan θ · u`) give the claim. -/
theorem tanuIdentity {u : ℝ → ℝ} (hsm : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    {ε b : ℝ} (hε : 0 < ε) (hεb : ε < b) (hb : b < Real.pi / 2) :
    Real.tan b * u b
      = (∫ θ in ε..b, Work.FTS.EllipticEst.Lzero1 u θ) + deriv u b - deriv u ε
        + Real.tan ε * u ε + 6 * (∫ θ in ε..b, u θ) := by
  have hU : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hsub : Set.Icc ε b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
    ⟨lt_of_lt_of_le hε hx.1, lt_of_le_of_lt hx.2 hb⟩
  have hcosU : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos x ≠ 0 := fun x hx =>
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩)
  -- regularity on the open interval
  have hu1U : ContDiffOn ℝ 1 u (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hsm.of_le (by norm_num)
  have hduU : ContDiffOn ℝ 1 (fun t => deriv u t) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hsm.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  have htanU : ContDiffOn ℝ 1 Real.tan (Set.Ioo (0 : ℝ) (Real.pi / 2)) := fun x hx =>
    ((Real.contDiffAt_tan (n := 1)).2 (hcosU x hx)).contDiffWithinAt
  have hprodU : ContDiffOn ℝ 1 (fun θ => Real.tan θ * u θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := htanU.mul hu1U
  -- the two fundamental-theorem-of-calculus applications
  have hFTCa : (∫ θ in ε..b, deriv (fun t => deriv u t) θ) = deriv u b - deriv u ε :=
    intervalIntegral.integral_deriv_of_contDiffOn_Icc (hduU.mono hsub) hεb.le
  have hFTCb : (∫ θ in ε..b, deriv (fun t => Real.tan t * u t) θ)
      = Real.tan b * u b - Real.tan ε * u ε :=
    intervalIntegral.integral_deriv_of_contDiffOn_Icc (hprodU.mono hsub) hεb.le
  -- integrability of the three pieces
  have hI1 : IntervalIntegrable (fun θ => deriv (fun t => deriv u t) θ) volume ε b := by
    have h0 : ContinuousOn (fun θ => deriv (fun t => deriv u t) θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      ((hduU.deriv_of_isOpen isOpen_Ioo (m := 0) (by norm_num)).continuousOn)
    exact (h0.mono hsub).intervalIntegrable_of_Icc hεb.le
  have hI2 : IntervalIntegrable (fun θ => deriv (fun t => Real.tan t * u t) θ) volume ε b :=
    ContinuousOn.intervalIntegrable_of_Icc hεb.le
      ((hprodU.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono hsub)
  have hI3 : IntervalIntegrable u volume ε b :=
    (hsm.continuousOn.mono hsub).intervalIntegrable_of_Icc hεb.le
  -- split the integral of `Lzero1`
  have hsplit : (∫ θ in ε..b, Work.FTS.EllipticEst.Lzero1 u θ)
      = -(∫ θ in ε..b, deriv (fun t => deriv u t) θ)
        + (∫ θ in ε..b, deriv (fun t => Real.tan t * u t) θ)
        - 6 * (∫ θ in ε..b, u θ) := by
    have hunfold : (∫ θ in ε..b, Work.FTS.EllipticEst.Lzero1 u θ)
        = ∫ θ in ε..b, (-(deriv (fun t => deriv u t) θ)
            + deriv (fun t => Real.tan t * u t) θ - 6 * u θ) := by
      simp only [Work.FTS.EllipticEst.Lzero1]
    have hA : IntervalIntegrable (fun θ => -(deriv (fun t => deriv u t) θ)
        + deriv (fun t => Real.tan t * u t) θ) volume ε b := hI1.neg.add hI2
    have hB : IntervalIntegrable (fun θ => 6 * u θ) volume ε b := hI3.const_mul 6
    have hA1 : IntervalIntegrable (fun θ => -(deriv (fun t => deriv u t) θ)) volume ε b :=
      hI1.neg
    rw [hunfold, intervalIntegral.integral_sub hA hB, intervalIntegral.integral_add hA1 hI2,
      intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
  rw [hsplit, hFTCa, hFTCb]
  ring

end Work.FTS.EllipticEst.remov.SourceBound
