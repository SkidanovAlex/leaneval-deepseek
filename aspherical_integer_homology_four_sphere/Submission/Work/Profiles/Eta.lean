/-
Copyright: area `Profiles` of the aspherical 4-manifold project.

# The smoothing bump `eta` and its normalisation constant

`eta` is a fixed nonnegative, even `C^∞` bump function supported in `[-1/4, 1/4]` with total
mass `1`; `mEta = ∫ e^{-t} eta t dt` is the constant by which the hyperbolic cusp constants
`C` and `D` are divided before smoothing.

The main numerical content is `two_mul_mEta_le : 2 * mEta ≤ Real.exp 2`, which is what makes
the smoothed model agree with the identity on `[0, 1/2]` for every `C ≥ 1`.
-/
import Submission.Work.Profiles.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open MeasureTheory Filter
open scoped Interval ContDiff Topology

namespace Work.Profiles

theorem eta_smooth : ContDiff ℝ ∞ eta :=
  ContDiffBump.contDiff_normed (f := baseBump) (μ := volume) (n := ⊤)

theorem eta_continuous : Continuous eta := ContDiffBump.continuous_normed baseBump

theorem eta_nonneg (t : ℝ) : 0 ≤ eta t := ContDiffBump.nonneg_normed baseBump t

theorem eta_even (t : ℝ) : eta (-t) = eta t := ContDiffBump.normed_neg baseBump t

theorem eta_hasCompactSupport : HasCompactSupport eta :=
  ContDiffBump.hasCompactSupport_normed (f := baseBump) (μ := volume)

theorem eta_integrable : Integrable eta volume := ContDiffBump.integrable_normed baseBump

theorem support_eta : Function.support eta = Metric.ball (0 : ℝ) (1/4) :=
  ContDiffBump.support_normed_eq baseBump

theorem integral_eta : ∫ t, eta t = 1 := ContDiffBump.integral_normed baseBump

theorem eta_eq_zero_of_quarter_le_abs (t : ℝ) (h : 1/4 ≤ |t|) : eta t = 0 := by
  by_contra hne
  have hmem : t ∈ Function.support eta := Function.mem_support.mpr hne
  rw [support_eta, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hmem
  linarith

theorem eta_pos_of_abs_lt {t : ℝ} (h : |t| < 1/4) : 0 < eta t := by
  have hmem : t ∈ Metric.ball (0 : ℝ) baseBump.rOut := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    exact h
  have hpos : 0 < baseBump t := ContDiffBump.pos_of_mem_ball baseBump hmem
  have hb : 0 < ∫ s, baseBump s := ContDiffBump.integral_pos baseBump
  have : eta t = baseBump t / ∫ s, baseBump s := rfl
  rw [this]
  exact div_pos hpos hb

theorem integral_eta_mul_id : ∫ t, t * eta t = 0 := by
  have hsym : ∫ t, ((-t : ℝ) * eta (-t)) = ∫ t, t * eta t :=
    integral_neg_eq_self (fun t : ℝ => t * eta t) volume
  have h1 : ∫ t, ((-t : ℝ) * eta (-t)) = ∫ t, -(t * eta t) := by
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    change (-t : ℝ) * eta (-t) = -(t * eta t)
    rw [eta_even t]; ring
  have h2 : ∫ t, -(t * eta t) = -(∫ t, t * eta t) := integral_neg _
  linarith

theorem exp_eta_continuous : Continuous fun t : ℝ => Real.exp (-t) * eta t :=
  (Real.continuous_exp.comp continuous_neg).mul eta_continuous

theorem exp_eta_integrable : Integrable (fun t : ℝ => Real.exp (-t) * eta t) volume :=
  Continuous.integrable_of_hasCompactSupport exp_eta_continuous eta_hasCompactSupport.mul_left

theorem support_exp_eta :
    Function.support (fun t : ℝ => Real.exp (-t) * eta t) = Metric.ball (0 : ℝ) (1/4) := by
  rw [Function.support_mul, show Function.support (fun t : ℝ => Real.exp (-t)) = Set.univ from ?_,
    Set.univ_inter, support_eta]
  ext t
  simp [Real.exp_ne_zero]

theorem mEta_pos : 0 < mEta := by
  rw [mEta]
  refine (integral_pos_iff_support_of_nonneg (fun t => ?_) exp_eta_integrable).mpr ?_
  · exact mul_nonneg (Real.exp_pos _).le (eta_nonneg t)
  · rw [support_exp_eta]
    exact Metric.measure_ball_pos volume (0 : ℝ) (by norm_num)

theorem mEta_le : mEta ≤ Real.exp (1/4) := by
  have hpt : ∀ t, Real.exp (-t) * eta t ≤ Real.exp (1/4) * eta t := by
    intro t
    rcases eq_or_lt_of_le (eta_nonneg t) with h | h
    · rw [← h, mul_zero, mul_zero]
    · have hmem : t ∈ Function.support eta := Function.mem_support.mpr h.ne'
      rw [support_eta, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hmem
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (le_trans (neg_le_abs t) hmem.le))
        (eta_nonneg t)
  have hint : Integrable (fun t : ℝ => Real.exp (1/4) * eta t) volume :=
    eta_integrable.const_mul (Real.exp (1/4))
  calc mEta = ∫ t, Real.exp (-t) * eta t := rfl
    _ ≤ ∫ t, Real.exp (1/4) * eta t := integral_mono exp_eta_integrable hint hpt
    _ = Real.exp (1/4) * ∫ t, eta t := integral_const_mul _ _
    _ = Real.exp (1/4) := by rw [integral_eta, mul_one]

theorem two_mul_exp_quarter_le_exp_two : 2 * Real.exp (1/4) ≤ Real.exp 2 := by
  have hb : (2 : ℝ) ≤ Real.exp (7/4) :=
    le_trans Real.exp_one_gt_two.le (Real.exp_le_exp.mpr (by norm_num))
  have h := mul_le_mul_of_nonneg_right hb (Real.exp_pos (1/4)).le
  rwa [← Real.exp_add, show (7 : ℝ)/4 + 1/4 = 2 from by norm_num] at h

theorem two_mul_mEta_le : 2 * mEta ≤ Real.exp 2 := by
  linarith [mEta_le, two_mul_exp_quarter_le_exp_two]

end Work.Profiles
