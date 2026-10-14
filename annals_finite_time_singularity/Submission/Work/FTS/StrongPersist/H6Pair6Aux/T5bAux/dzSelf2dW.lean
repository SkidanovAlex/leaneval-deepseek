import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.dzSelf2d
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.StabilityFar.Decay.KernelDefs
import Submission.Work.StabilityFar.Decay.hasDerivAt_biotSavart
import Submission.Work.StabilityFar.Decay.norm_kDerivCLM_sub_le
import Submission.Work.StabilityFar.Decay.timeDeriv_eq_zero_of_notMem_closedBall
-- ===== merged: Submission.Work.CoreResiduals.BiotSavart.norm_taylor_error_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Metric
open scoped ENNReal Topology

namespace Work.CoreResiduals.BiotSavart

open Work.StabilityFar.Decay (kf kDerivCLM crossL)

lemma setLIntegral_const_mul' {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) (r : ℝ≥0∞) (hr : r ≠ ∞) (f : α → ℝ≥0∞) :
    ∫⁻ a in s, r * f a ∂μ = r * ∫⁻ a in s, f a ∂μ := by
  rw [← lintegral_indicator hs (fun a => r * f a)]
  rw [show s.indicator (fun a => r * f a) = fun a => r * s.indicator f a from ?_]
  · rw [lintegral_const_mul' r _ hr, lintegral_indicator hs f]
  · funext a
    by_cases ha : a ∈ s
    · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha]
    · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha, mul_zero]

lemma setLIntegral_add' {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) {f g : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ a in s, f a + g a ∂μ = (∫⁻ a in s, f a ∂μ) + ∫⁻ a in s, g a ∂μ := by
  rw [← lintegral_indicator hs (fun a => f a + g a)]
  rw [show s.indicator (fun a => f a + g a) = fun a => s.indicator f a + s.indicator g a from ?_]
  · rw [lintegral_add_left (hf.indicator hs), lintegral_indicator hs f, lintegral_indicator hs g]
  · funext a
    by_cases ha : a ∈ s
    · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha, Set.indicator_of_mem ha]
    · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha, Set.indicator_of_notMem ha, add_zero]

lemma measurable_ofReal_rpow_norm (q : ℝ) (hq : 0 < q) :
    Measurable (fun y : Work.LWP.R3 => ENNReal.ofReal (‖y‖ ^ q)) := by
  apply ENNReal.measurable_ofReal.comp
  exact (Real.continuous_rpow_const (le_of_lt hq)).comp continuous_norm |>.measurable

lemma measurable_ofReal_rpow_norm_neg (q : ℝ) (hq : 0 < q) :
    Measurable (fun y : Work.LWP.R3 => ENNReal.ofReal (‖y‖ ^ (-q))) := by
  apply ENNReal.measurable_ofReal.comp
  have heq : (fun y : Work.LWP.R3 => (‖y‖:ℝ) ^ (-q)) = fun y : Work.LWP.R3 => ((‖y‖:ℝ) ^ q)⁻¹ := by
    funext y
    exact Real.rpow_neg (norm_nonneg y) q
  rw [heq]
  exact (Measurable.inv ((Real.continuous_rpow_const (le_of_lt hq)).comp continuous_norm).measurable)

lemma measurable_ofReal_shift_inv_sq (h : Work.LWP.R3) :
    Measurable (fun y : Work.LWP.R3 => ENNReal.ofReal (‖y + h‖ ^ (-2:ℝ))) := by
  apply ENNReal.measurable_ofReal.comp
  have heq : (fun y : Work.LWP.R3 => ‖y + h‖ ^ (-2:ℝ))
      = fun y : Work.LWP.R3 => ((‖y + h‖ : ℝ) ^ (2:ℕ))⁻¹ :=
    funext fun y => (inv_natPow_eq_rpow_neg (‖y+h‖) (norm_nonneg _) 2).symm
  rw [heq]
  fun_prop

theorem norm_taylor_error_le {ω : Work.LWP.R3 → Work.LWP.R3} {c C : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (hC : 0 ≤ C) (hhold : ∀ a b : Work.LWP.R3, ‖ω a - ω b‖ ≤ C * ‖a - b‖ ^ c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ρ : ℝ) (x h : Work.LWP.R3), h ≠ 0 →
      ∫ a in Metric.ball (0 : Work.LWP.R3) ρ,
          ‖Work.StabilityFar.Decay.crossL (ω a - ω x)
            (Work.StabilityFar.Decay.kf (x + h - a) - Work.StabilityFar.Decay.kf (x - a)
              - Work.StabilityFar.Decay.kDerivCLM (x - a) h)‖
        ≤ K * ‖h‖ ^ (1 + c) := by
  let K0 : ℝ := 12 * Real.pi * 2 ^ c + 4 * Real.pi * 2 ^ (c + 1) / (c + 1)
      + 16 * Real.pi * 2 ^ c / c + 4096 * Real.pi * 2 ^ (c - 1) / (1 - c)
  have hK0nn : 0 ≤ K0 := by
    have h2c : (0:ℝ) < 2 ^ c := Real.rpow_pos_of_pos (by norm_num) c
    have h2c1 : (0:ℝ) < 2 ^ (c+1) := Real.rpow_pos_of_pos (by norm_num) (c+1)
    have h2cm : (0:ℝ) < 2 ^ (c-1) := Real.rpow_pos_of_pos (by norm_num) (c-1)
    have h1c : (0:ℝ) < 1 - c := by linarith
    have hc1' : (0:ℝ) < c + 1 := by linarith
    simp only [K0]
    positivity
  refine ⟨C * K0, mul_nonneg hC hK0nn, ?_⟩
  intro ρ x h hh
  have hr : 0 < ‖h‖ := norm_pos_iff.mpr hh
  have hA : (∫ a in Metric.ball (0 : Work.LWP.R3) ρ,
        ‖crossL (ω a - ω x) (kf (x + h - a) - kf (x - a) - kDerivCLM (x - a) h)‖)
      = ∫ a in Metric.ball (0 : Work.LWP.R3) ρ,
        ‖crossL (ω a - ω x) (resid h (x - a))‖ := by
    apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
    intro a _
    simp only [resid_shift]
  rw [hA]
  have hmeas : AEStronglyMeasurable (fun a : Work.LWP.R3 =>
      ‖crossL (ω a - ω x) (resid h (x - a))‖) volume :=
    taylor_integrand_measurable hc hC hhold x h
  have hpt : ∀ a : Work.LWP.R3,
      ‖crossL (ω a - ω x) (resid h (x - a))‖ ≤ C * (‖x - a‖ ^ c * ‖resid h (x - a)‖) := by
    intro a
    have h1 : ‖crossL (ω a - ω x) (resid h (x - a))‖
        ≤ ‖ω a - ω x‖ * ‖resid h (x - a)‖ := by
      calc ‖crossL (ω a - ω x) (resid h (x - a))‖
          ≤ ‖crossL (ω a - ω x)‖ * ‖resid h (x - a)‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖ω a - ω x‖ * ‖resid h (x - a)‖ := by
            gcongr
            exact Work.StabilityFar.Decay.norm_crossL_le _
    calc ‖crossL (ω a - ω x) (resid h (x - a))‖
        ≤ ‖ω a - ω x‖ * ‖resid h (x - a)‖ := h1
      _ ≤ (C * ‖x - a‖ ^ c) * ‖resid h (x - a)‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            simpa [norm_sub_rev] using hhold a x
      _ = C * (‖x - a‖ ^ c * ‖resid h (x - a)‖) := by ring
  have hptS : ∀ y ∈ Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖),
      ENNReal.ofReal (‖y‖ ^ c * ‖resid h y‖)
        ≤ ENNReal.ofReal (‖y‖ ^ c * ‖y + h‖ ^ (-2:ℝ)) + ENNReal.ofReal (‖y‖ ^ (c - 2))
          + ENNReal.ofReal (4 * ‖h‖ * ‖y‖ ^ (c - 3)) := by
    intro y _
    have h1 := norm_resid_mul_rpow_le hc h y
    refine le_trans (ENNReal.ofReal_le_ofReal h1) ?_
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity)]
  have hm1 : Measurable (fun y : Work.LWP.R3 => ENNReal.ofReal (‖y‖ ^ c * ‖y + h‖ ^ (-2:ℝ))) := by
    rw [show (fun y : Work.LWP.R3 => ENNReal.ofReal (‖y‖ ^ c * ‖y + h‖ ^ (-2:ℝ)))
        = fun y : Work.LWP.R3 => ENNReal.ofReal (‖y‖ ^ c) * ENNReal.ofReal (‖y + h‖ ^ (-2:ℝ)) from
          funext fun y => ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg y) c)]
    exact (measurable_ofReal_rpow_norm c hc).mul (measurable_ofReal_shift_inv_sq h)
  have hm2 : Measurable (fun y : Work.LWP.R3 => ENNReal.ofReal (‖y‖ ^ (c - 2))) := by
    rw [show (fun y : Work.LWP.R3 => ENNReal.ofReal (‖y‖ ^ (c - 2)))
        = fun y : Work.LWP.R3 => ENNReal.ofReal (‖y‖ ^ (-(2 - c))) from
          funext fun y => by rw [show c - 2 = -(2 - c) by ring]]
    exact measurable_ofReal_rpow_norm_neg (2 - c) (by linarith)
  have hm3 : Measurable (fun y : Work.LWP.R3 => ENNReal.ofReal (‖y‖ ^ (c - 3))) := by
    rw [show (fun y : Work.LWP.R3 => ENNReal.ofReal (‖y‖ ^ (c - 3)))
        = fun y : Work.LWP.R3 => ENNReal.ofReal (‖y‖ ^ (-(3 - c))) from
          funext fun y => by rw [show c - 3 = -(3 - c) by ring]]
    exact measurable_ofReal_rpow_norm_neg (3 - c) (by linarith)
  have hT1 : ∫⁻ y in Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖), ENNReal.ofReal (‖y‖ ^ c * ‖y + h‖ ^ (-2:ℝ))
      ≤ ENNReal.ofReal ((2 * ‖h‖) ^ c * (12 * Real.pi * ‖h‖)) := by
    have hpt1 : ∀ y ∈ Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖),
        ENNReal.ofReal (‖y‖ ^ c * ‖y + h‖ ^ (-2:ℝ))
          ≤ ENNReal.ofReal ((2 * ‖h‖) ^ c) * ENNReal.ofReal (‖y + h‖ ^ (-2:ℝ)) := by
      intro y hy
      have hy2 : ‖y‖ < 2 * ‖h‖ := by
        rw [Metric.mem_ball, dist_eq_norm] at hy; simpa [sub_zero] using hy
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg y) c)]
      exact mul_le_mul_left
        (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg y) (le_of_lt hy2) (le_of_lt hc)))
        (ENNReal.ofReal (‖y + h‖ ^ (-2:ℝ)))
    calc ∫⁻ y in Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖), ENNReal.ofReal (‖y‖ ^ c * ‖y + h‖ ^ (-2:ℝ))
        ≤ ∫⁻ y in Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖),
            ENNReal.ofReal ((2 * ‖h‖) ^ c) * ENNReal.ofReal (‖y + h‖ ^ (-2:ℝ)) :=
          setLIntegral_mono' Metric.isOpen_ball.measurableSet hpt1
      _ = ENNReal.ofReal ((2 * ‖h‖) ^ c) *
            ∫⁻ y in Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖), ENNReal.ofReal (‖y + h‖ ^ (-2:ℝ)) :=
          setLIntegral_const_mul' Metric.isOpen_ball.measurableSet _ ENNReal.ofReal_ne_top _
      _ ≤ ENNReal.ofReal ((2 * ‖h‖) ^ c) * ENNReal.ofReal (12 * Real.pi * ‖h‖) :=
          mul_le_mul_right (lintegral_ball_shift_inv_sq h) _
      _ = ENNReal.ofReal ((2 * ‖h‖) ^ c * (12 * Real.pi * ‖h‖)) :=
          (ENNReal.ofReal_mul (by positivity)).symm
  have hT2 : ∫⁻ y in Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖), ENNReal.ofReal (‖y‖ ^ (c - 2))
      ≤ ENNReal.ofReal (4 * Real.pi * (2 * ‖h‖) ^ (c + 1) / (c + 1)) := by
    rw [lintegral_ball_norm_rpow (c - 2) (by linarith) (2 * ‖h‖) (by linarith)]
    rw [show c - 2 + 3 = c + 1 by ring]
  have hT3 : ∫⁻ y in Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖), ENNReal.ofReal (4 * ‖h‖ * ‖y‖ ^ (c - 3))
      ≤ ENNReal.ofReal (4 * ‖h‖ * (4 * Real.pi * (2 * ‖h‖) ^ c / c)) := by
    rw [show (fun y : Work.LWP.R3 => ENNReal.ofReal (4 * ‖h‖ * ‖y‖ ^ (c - 3)))
        = fun y : Work.LWP.R3 => ENNReal.ofReal (4 * ‖h‖) * ENNReal.ofReal (‖y‖ ^ (c - 3)) from
          funext fun y => ENNReal.ofReal_mul (by positivity)]
    rw [setLIntegral_const_mul' Metric.isOpen_ball.measurableSet _ ENNReal.ofReal_ne_top
          (fun y : Work.LWP.R3 => ENNReal.ofReal (‖y‖ ^ (c - 3)))]
    rw [show (∫⁻ y in Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖), ENNReal.ofReal (‖y‖ ^ (c - 3)))
          = ENNReal.ofReal (4 * Real.pi * (2 * ‖h‖) ^ c / c) from by
        rw [lintegral_ball_norm_rpow (c - 3) (by linarith) (2 * ‖h‖) (by linarith)]
        rw [show c - 3 + 3 = c by ring]]
    exact le_of_eq (ENNReal.ofReal_mul (by positivity)).symm
  have hS : ∫⁻ y in Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖), ENNReal.ofReal (‖y‖ ^ c * ‖resid h y‖)
      ≤ ENNReal.ofReal ((2 * ‖h‖) ^ c * (12 * Real.pi * ‖h‖) + 4 * Real.pi * (2 * ‖h‖) ^ (c + 1) / (c + 1)
          + 4 * ‖h‖ * (4 * Real.pi * (2 * ‖h‖) ^ c / c)) := by
    have hsplit : ∫⁻ y in Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖),
          (ENNReal.ofReal (‖y‖ ^ c * ‖y + h‖ ^ (-2:ℝ)) + ENNReal.ofReal (‖y‖ ^ (c - 2))
            + ENNReal.ofReal (4 * ‖h‖ * ‖y‖ ^ (c - 3)))
        = ((∫⁻ y in Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖), ENNReal.ofReal (‖y‖ ^ c * ‖y + h‖ ^ (-2:ℝ)))
          + (∫⁻ y in Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖), ENNReal.ofReal (‖y‖ ^ (c - 2))))
          + (∫⁻ y in Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖), ENNReal.ofReal (4 * ‖h‖ * ‖y‖ ^ (c - 3))) := by
      rw [setLIntegral_add' Metric.isOpen_ball.measurableSet (f := fun y : Work.LWP.R3 =>
            ENNReal.ofReal (‖y‖ ^ c * ‖y + h‖ ^ (-2:ℝ)) + ENNReal.ofReal (‖y‖ ^ (c - 2)))
            (hm1.add hm2)]
      rw [setLIntegral_add' Metric.isOpen_ball.measurableSet (f := fun y : Work.LWP.R3 =>
            ENNReal.ofReal (‖y‖ ^ c * ‖y + h‖ ^ (-2:ℝ))) hm1]
    have hAS : ENNReal.ofReal ((2 * ‖h‖) ^ c * (12 * Real.pi * ‖h‖)
          + 4 * Real.pi * (2 * ‖h‖) ^ (c + 1) / (c + 1)
          + 4 * ‖h‖ * (4 * Real.pi * (2 * ‖h‖) ^ c / c))
        = ((ENNReal.ofReal ((2 * ‖h‖) ^ c * (12 * Real.pi * ‖h‖))
          + ENNReal.ofReal (4 * Real.pi * (2 * ‖h‖) ^ (c + 1) / (c + 1)))
          + ENNReal.ofReal (4 * ‖h‖ * (4 * Real.pi * (2 * ‖h‖) ^ c / c))) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
    calc ∫⁻ y in Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖), ENNReal.ofReal (‖y‖ ^ c * ‖resid h y‖)
        ≤ ∫⁻ y in Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖),
            (ENNReal.ofReal (‖y‖ ^ c * ‖y + h‖ ^ (-2:ℝ)) + ENNReal.ofReal (‖y‖ ^ (c - 2))
              + ENNReal.ofReal (4 * ‖h‖ * ‖y‖ ^ (c - 3))) :=
          setLIntegral_mono' Metric.isOpen_ball.measurableSet hptS
      _ = ((∫⁻ y in Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖), ENNReal.ofReal (‖y‖ ^ c * ‖y + h‖ ^ (-2:ℝ)))
            + (∫⁻ y in Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖), ENNReal.ofReal (‖y‖ ^ (c - 2))))
            + (∫⁻ y in Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖), ENNReal.ofReal (4 * ‖h‖ * ‖y‖ ^ (c - 3))) := hsplit
      _ ≤ ENNReal.ofReal ((2 * ‖h‖) ^ c * (12 * Real.pi * ‖h‖) + 4 * Real.pi * (2 * ‖h‖) ^ (c + 1) / (c + 1)
            + 4 * ‖h‖ * (4 * Real.pi * (2 * ‖h‖) ^ c / c)) :=
          le_trans (add_le_add (add_le_add hT1 hT2) hT3) (le_of_eq hAS.symm)
  have hptL : ∀ y ∈ (Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖))ᶜ,
      ENNReal.ofReal (‖y‖ ^ c * ‖resid h y‖)
        ≤ ENNReal.ofReal (1024 * ‖h‖ ^ (2:ℕ)) * ENNReal.ofReal (‖y‖ ^ (c - 4)) := by
    intro y hy
    simp only [Set.mem_compl_iff, Metric.mem_ball, not_lt, dist_eq_norm, sub_zero] at hy
    have h1 := norm_resid_mul_rpow_le_far (c := c) h y hy
    calc ENNReal.ofReal (‖y‖ ^ c * ‖resid h y‖)
        ≤ ENNReal.ofReal (1024 * ‖h‖ ^ (2:ℕ) * ‖y‖ ^ (c - 4)) := ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal (1024 * ‖h‖ ^ (2:ℕ)) * ENNReal.ofReal (‖y‖ ^ (c - 4)) :=
          ENNReal.ofReal_mul (by positivity)
  have hL : ∫⁻ y in (Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖))ᶜ, ENNReal.ofReal (‖y‖ ^ c * ‖resid h y‖)
      ≤ ENNReal.ofReal (1024 * ‖h‖ ^ (2:ℕ) * (4 * Real.pi * (2 * ‖h‖) ^ (c - 1) / (1 - c))) := by
    calc ∫⁻ y in (Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖))ᶜ, ENNReal.ofReal (‖y‖ ^ c * ‖resid h y‖)
        ≤ ∫⁻ y in (Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖))ᶜ,
            ENNReal.ofReal (1024 * ‖h‖ ^ (2:ℕ)) * ENNReal.ofReal (‖y‖ ^ (c - 4)) :=
          setLIntegral_mono' (Metric.isOpen_ball.measurableSet.compl) hptL
      _ = ENNReal.ofReal (1024 * ‖h‖ ^ (2:ℕ)) *
            ∫⁻ y in (Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖))ᶜ, ENNReal.ofReal (‖y‖ ^ (c - 4)) :=
          setLIntegral_const_mul' (Metric.isOpen_ball.measurableSet.compl) _ ENNReal.ofReal_ne_top _
      _ = ENNReal.ofReal (1024 * ‖h‖ ^ (2:ℕ)) * ENNReal.ofReal (4 * Real.pi * (2 * ‖h‖) ^ (c - 1) / (1 - c)) := by
          rw [lintegral_exterior_norm_rpow (c - 4) (by linarith) (2 * ‖h‖) (by linarith)]
          rw [show c - 4 + 3 = c - 1 by ring, show -((c:ℝ) - 1) = 1 - c by ring]
      _ = ENNReal.ofReal (1024 * ‖h‖ ^ (2:ℕ) * (4 * Real.pi * (2 * ‖h‖) ^ (c - 1) / (1 - c))) :=
          (ENNReal.ofReal_mul (by positivity)).symm
  have hmain : ∫⁻ y, ENNReal.ofReal (‖y‖ ^ c * ‖resid h y‖)
      ≤ ENNReal.ofReal ((2 * ‖h‖) ^ c * (12 * Real.pi * ‖h‖) + 4 * Real.pi * (2 * ‖h‖) ^ (c + 1) / (c + 1)
          + 4 * ‖h‖ * (4 * Real.pi * (2 * ‖h‖) ^ c / c)
          + 1024 * ‖h‖ ^ (2:ℕ) * (4 * Real.pi * (2 * ‖h‖) ^ (c - 1) / (1 - c))) := by
    refine le_trans (le_of_eq ((lintegral_add_compl (μ := volume)
      (A := Metric.ball (0 : Work.LWP.R3) (2 * ‖h‖)) _ Metric.isOpen_ball.measurableSet).symm)) ?_
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    exact add_le_add hS hL
  have hmain2 : ∫⁻ y, ENNReal.ofReal (‖y‖ ^ c * ‖resid h y‖) ≤ ENNReal.ofReal (K0 * ‖h‖ ^ (1 + c)) :=
    le_trans hmain (ENNReal.ofReal_le_ofReal (by
      simpa only [K0] using taylor_bound_arith hc hc1 ‖h‖ hr))
  have hlin_ofReal : ∫⁻ a in Metric.ball (0 : Work.LWP.R3) ρ,
        ENNReal.ofReal (‖crossL (ω a - ω x) (resid h (x - a))‖)
      ≤ ENNReal.ofReal ((C * K0) * ‖h‖ ^ (1 + c)) := by
    have hstep1 : ∫⁻ a in Metric.ball (0 : Work.LWP.R3) ρ,
          ENNReal.ofReal (‖crossL (ω a - ω x) (resid h (x - a))‖)
        ≤ ∫⁻ a in Metric.ball (0 : Work.LWP.R3) ρ,
          ENNReal.ofReal (C * (‖x - a‖ ^ c * ‖resid h (x - a)‖)) :=
      setLIntegral_mono' Metric.isOpen_ball.measurableSet (fun a _ => ENNReal.ofReal_le_ofReal (hpt a))
    have hstep2 : ∫⁻ a in Metric.ball (0 : Work.LWP.R3) ρ,
          ENNReal.ofReal (C * (‖x - a‖ ^ c * ‖resid h (x - a)‖))
        = ENNReal.ofReal C * ∫⁻ a in Metric.ball (0 : Work.LWP.R3) ρ,
          ENNReal.ofReal (‖x - a‖ ^ c * ‖resid h (x - a)‖) := by
      rw [show (fun a : Work.LWP.R3 => ENNReal.ofReal (C * (‖x - a‖ ^ c * ‖resid h (x - a)‖)))
          = fun a : Work.LWP.R3 => ENNReal.ofReal C * ENNReal.ofReal (‖x - a‖ ^ c * ‖resid h (x - a)‖) from
            funext fun a => ENNReal.ofReal_mul hC]
      exact setLIntegral_const_mul' Metric.isOpen_ball.measurableSet _ ENNReal.ofReal_ne_top _
    have hsub : ∫⁻ a in Metric.ball (0 : Work.LWP.R3) ρ, ENNReal.ofReal (‖x - a‖ ^ c * ‖resid h (x - a)‖)
        = ∫⁻ y in Metric.ball x ρ, ENNReal.ofReal (‖y‖ ^ c * ‖resid h y‖) := by
      have hpoint : ∀ a : Work.LWP.R3,
          (Metric.ball x ρ).indicator (fun y => ENNReal.ofReal (‖y‖ ^ c * ‖resid h y‖)) (x - a)
            = (Metric.ball (0:Work.LWP.R3) ρ).indicator
                (fun a => ENNReal.ofReal (‖x - a‖ ^ c * ‖resid h (x - a)‖)) a := by
        intro a
        by_cases ha : a ∈ Metric.ball (0:Work.LWP.R3) ρ
        · have hxa : x - a ∈ Metric.ball x ρ := by
            simp only [Metric.mem_ball, dist_eq_norm] at ha ⊢
            rw [show x - a - x = -a by abel, norm_neg]
            simpa using ha
          rw [Set.indicator_of_mem hxa, Set.indicator_of_mem ha]
        · have hxa : x - a ∉ Metric.ball x ρ := by
            simp only [Metric.mem_ball, dist_eq_norm] at ha ⊢
            rw [show x - a - x = -a by abel, norm_neg]
            simpa using ha
          rw [Set.indicator_of_notMem hxa, Set.indicator_of_notMem ha]
      calc ∫⁻ a in Metric.ball (0:Work.LWP.R3) ρ, ENNReal.ofReal (‖x - a‖ ^ c * ‖resid h (x - a)‖)
          = ∫⁻ a, (Metric.ball (0:Work.LWP.R3) ρ).indicator
                (fun a => ENNReal.ofReal (‖x - a‖ ^ c * ‖resid h (x - a)‖)) a :=
              (lintegral_indicator Metric.isOpen_ball.measurableSet _).symm
        _ = ∫⁻ a, (Metric.ball x ρ).indicator (fun y => ENNReal.ofReal (‖y‖ ^ c * ‖resid h y‖)) (x - a) := by
              apply lintegral_congr; intro a; exact (hpoint a).symm
        _ = ∫⁻ y, (Metric.ball x ρ).indicator (fun y => ENNReal.ofReal (‖y‖ ^ c * ‖resid h y‖)) y :=
              lintegral_sub_left_eq_self _ x
        _ = ∫⁻ y in Metric.ball x ρ, ENNReal.ofReal (‖y‖ ^ c * ‖resid h y‖) :=
              lintegral_indicator Metric.isOpen_ball.measurableSet _
    calc ∫⁻ a in Metric.ball (0 : Work.LWP.R3) ρ, ENNReal.ofReal (‖crossL (ω a - ω x) (resid h (x - a))‖)
        ≤ ∫⁻ a in Metric.ball (0 : Work.LWP.R3) ρ,
            ENNReal.ofReal (C * (‖x - a‖ ^ c * ‖resid h (x - a)‖)) := hstep1
      _ = ENNReal.ofReal C * ∫⁻ a in Metric.ball (0 : Work.LWP.R3) ρ,
            ENNReal.ofReal (‖x - a‖ ^ c * ‖resid h (x - a)‖) := hstep2
      _ = ENNReal.ofReal C * ∫⁻ y in Metric.ball x ρ, ENNReal.ofReal (‖y‖ ^ c * ‖resid h y‖) := by rw [hsub]
      _ ≤ ENNReal.ofReal C * ∫⁻ y, ENNReal.ofReal (‖y‖ ^ c * ‖resid h y‖) :=
            mul_le_mul_right (setLIntegral_le_lintegral _ _) _
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (K0 * ‖h‖ ^ (1 + c)) := mul_le_mul_right hmain2 _
      _ = ENNReal.ofReal (C * (K0 * ‖h‖ ^ (1 + c))) := (ENNReal.ofReal_mul hC).symm
      _ = ENNReal.ofReal ((C * K0) * ‖h‖ ^ (1 + c)) := by congr 1; ring
  refine le_trans (le_of_eq (setIntegral_eq_lintegral_of_nonneg Metric.isOpen_ball.measurableSet hmeas
    (fun a => norm_nonneg _))) ?_
  refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin_ofReal) ?_
  exact le_of_eq (ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg hC hK0nn)
    (Real.rpow_nonneg (norm_nonneg h) _)))

end Work.CoreResiduals.BiotSavart
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.dzSelf2dW =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T5bAux

/-!
## The weighted two-dimensional radial self-pairing bound `dzSelf2dW`

This is the `ψ`-weighted (and unsigned) form of `Work.FTS.StrongPersist.H6Pair6Aux.dzSelf2d`:
from the one-dimensional bound `h1d` (with the weight `ψ` and the constant `D`) for every
admissible slice `Y`, we deduce the two-dimensional bound with an arbitrary (not necessarily
positive, not even a.e. non-zero) angular weight `θw`:

`|∫_z ∫_θ w(z)² θw(θ) ψ(z) ((z ∂_z V)(z,θ)) V(z,θ)| ≤ D ∫_z ∫_θ w(z)² |θw(θ)| V(z,θ)²`.

The route is the one of `dzSelf2d`: apply `h1d` to the slices `Y = V(·,θ)` for a.e. `θ`,
multiply by `|θw θ|` and integrate in `θ`, using Fubini to pass between the two orders.  Two
points differ from `dzSelf2d`:

* no positivity of `θw` is assumed, so the slicewise inequality is only needed where
  `θw θ ≠ 0`; on the remaining (possibly non-null) set the whole inner integrand vanishes
  identically because of the factor `θw θ`, and the desired inequality reduces to `0 ≤ 0`;
* the slice integrability that `hF`/`hD2` supply by Fubini is only available after dividing
  by `|θw θ|`, which is why the case split above is needed.

The cross term is *given* as product-integrable (`hcross`), so no a.e.-measurability argument
is required here (unlike in `dzSelf2d`, where it had to be manufactured).
-/

theorem dzSelf2dW {θw : ℝ → ℝ} {ψ : ℝ → ℝ} {V : ℝ → ℝ → ℝ} {D : ℝ}
    (hD0 : 0 ≤ D)
    (h1d : ∀ (Y : ℝ → ℝ), ContDiffOn ℝ 1 Y (Set.Ioi 0) →
      MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (Y z) ^ 2) (Set.Ioi 0) →
      MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (z * deriv Y z) ^ 2)
        (Set.Ioi 0) →
      |∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * ψ z * ((z * deriv Y z) * Y z)|
        ≤ D * ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * (Y z) ^ 2)
    (hθwm : AEMeasurable θw (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hV : ∀ θ ∈ Set.Ioo 0 (π / 2), ContDiffOn ℝ 1 (fun z => V z θ) (Set.Ioi 0))
    (hVae : AEMeasurable (Function.uncurry V)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hF : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * |θw p.2| * (V p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hD2 : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * |θw p.2|
        * (p.1 * Work.Spaces.pz V p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hcross : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * θw p.2 * ψ p.1
        * ((p.1 * Work.Spaces.pz V p.1 p.2) * V p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * θw θ * ψ z * ((z * Work.Spaces.pz V z θ) * V z θ)|
      ≤ D * ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * |θw θ| * (V z θ) ^ 2 := by
  have hΛz : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) :=
    Measure.restrict_congr_set Work.FTS.StrongPersist.H6Pair6Aux.dzSelf2d_Iz_ae
  have hΛθ : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
    Measure.restrict_congr_set Work.FTS.StrongPersist.H6Pair6Aux.dzSelf2d_Ith_ae
  have haeθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
    have h := MeasureTheory.ae_restrict_mem (μ := (MeasureTheory.volume : Measure ℝ))
      (s := Set.Ioo (0 : ℝ) (π / 2)) measurableSet_Ioo
    rwa [← hΛθ] at h
  -- slice integrability for a.e. `θ`, available where `θw θ ≠ 0`
  have hsliceF : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θw θ ≠ 0 → MeasureTheory.IntegrableOn
        (fun z => (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2) (Set.Ioi 0) := by
    have h1 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        MeasureTheory.Integrable
          (fun z => (Work.Spaces.w z) ^ 2 * |θw θ| * (V z θ) ^ 2)
          (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      MeasureTheory.Integrable.prod_left_ae hF
    filter_upwards [h1] with θ hθ hne
    have h2 : MeasureTheory.Integrable
        (fun z => |θw θ| * ((Work.Spaces.w z) ^ 2 * (V z θ) ^ 2))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      simpa only [mul_comm, mul_left_comm, mul_assoc] using hθ
    have h3 : MeasureTheory.Integrable
        (fun z => (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (abs_ne_zero.mpr hne))
        (fun z => (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2)).mp h2
    rw [hΛz] at h3
    exact h3
  have hsliceD : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θw θ ≠ 0 → MeasureTheory.IntegrableOn
        (fun z => (Work.Spaces.w z) ^ 2 * (z * Work.Spaces.pz V z θ) ^ 2) (Set.Ioi 0) := by
    have h1 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        MeasureTheory.Integrable
          (fun z => (Work.Spaces.w z) ^ 2 * |θw θ| * (z * Work.Spaces.pz V z θ) ^ 2)
          (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      MeasureTheory.Integrable.prod_left_ae hD2
    filter_upwards [h1] with θ hθ hne
    have h2 : MeasureTheory.Integrable
        (fun z => |θw θ| * ((Work.Spaces.w z) ^ 2 * (z * Work.Spaces.pz V z θ) ^ 2))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      simpa only [mul_comm, mul_left_comm, mul_assoc] using hθ
    have h3 : MeasureTheory.Integrable
        (fun z => (Work.Spaces.w z) ^ 2 * (z * Work.Spaces.pz V z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (abs_ne_zero.mpr hne))
        (fun z => (Work.Spaces.w z) ^ 2 * (z * Work.Spaces.pz V z θ) ^ 2)).mp h2
    rw [hΛz] at h3
    exact h3
  -- the a.e.-`θ` slicewise 1-D bound
  have hkey : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |∫ z in Work.Spaces.Iz,
          (Work.Spaces.w z) ^ 2 * θw θ * ψ z * ((z * Work.Spaces.pz V z θ) * V z θ)|
        ≤ D * (|θw θ| * ∫ z in Set.Ioi (0 : ℝ),
            (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2) := by
    filter_upwards [haeθ, hsliceF, hsliceD] with θ hmem hsf hsd
    by_cases hne : θw θ = 0
    · have hzero : (∫ z in Work.Spaces.Iz,
          (Work.Spaces.w z) ^ 2 * θw θ * ψ z * ((z * Work.Spaces.pz V z θ) * V z θ)) = 0 := by
        have hfun : (fun z => (Work.Spaces.w z) ^ 2 * θw θ * ψ z
              * ((z * Work.Spaces.pz V z θ) * V z θ)) = fun _ => (0 : ℝ) := by
          funext z
          rw [hne]
          ring
        rw [hfun]
        simp
      rw [hzero, abs_zero]
      simp [hne]
    · have h1 := h1d (fun z => V z θ) (hV θ hmem) (hsf hne) (hsd hne)
      have hL : (∫ z in Work.Spaces.Iz,
            (Work.Spaces.w z) ^ 2 * θw θ * ψ z * ((z * Work.Spaces.pz V z θ) * V z θ))
          = θw θ * (∫ z in Set.Ioi (0 : ℝ),
              (Work.Spaces.w z) ^ 2 * ψ z
                * ((z * Work.Spaces.pz V z θ) * V z θ)) := by
        rw [setIntegral_congr_set Work.FTS.StrongPersist.H6Pair6Aux.dzSelf2d_Iz_ae]
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun z => ?_)
        ring
      rw [hL, abs_mul]
      calc |θw θ| * |∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * ψ z
              * ((z * Work.Spaces.pz V z θ) * V z θ)|
          ≤ |θw θ| * (D * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2) :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg (θw θ))
        _ = D * (|θw θ| * ∫ z in Set.Ioi (0 : ℝ),
              (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2) := by ring
  -- integrability of the upper bound `θ ↦ D * |θw θ| * ∫_z w²V²`
  have hψint : MeasureTheory.Integrable
      (fun θ => |θw θ| * ∫ z in Set.Ioi (0 : ℝ), (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h := MeasureTheory.Integrable.integral_prod_right hF
    have hfun : (fun θ => ∫ z, (Work.Spaces.w z) ^ 2 * |θw θ| * (V z θ) ^ 2
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
        = fun θ => |θw θ| * ∫ z in Set.Ioi (0 : ℝ),
            (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2 := by
      funext θ
      rw [show (fun z => (Work.Spaces.w z) ^ 2 * |θw θ| * (V z θ) ^ 2)
          = fun z => |θw θ| * ((Work.Spaces.w z) ^ 2 * (V z θ) ^ 2) from by
            funext z; ring]
      rw [MeasureTheory.integral_const_mul]
      rw [setIntegral_congr_set Work.FTS.StrongPersist.H6Pair6Aux.dzSelf2d_Iz_ae]
    rwa [hfun] at h
  have hRHSint : MeasureTheory.Integrable
      (fun θ => D * (|θw θ| * ∫ z in Set.Ioi (0 : ℝ),
        (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hψint.const_mul D
  have hLHSint : MeasureTheory.Integrable
      (fun θ => |∫ z in Work.Spaces.Iz,
        (Work.Spaces.w z) ^ 2 * θw θ * ψ z * ((z * Work.Spaces.pz V z θ) * V z θ)|)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h := MeasureTheory.Integrable.integral_prod_right hcross
    exact h.abs
  -- Fubini and the comparison
  have hswap : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * θw θ * ψ z * ((z * Work.Spaces.pz V z θ) * V z θ))
      = ∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
        (Work.Spaces.w z) ^ 2 * θw θ * ψ z * ((z * Work.Spaces.pz V z θ) * V z θ) :=
    MeasureTheory.integral_integral_swap hcross
  calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * θw θ * ψ z * ((z * Work.Spaces.pz V z θ) * V z θ)|
      = |∫ θ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
          (Work.Spaces.w z) ^ 2 * θw θ * ψ z * ((z * Work.Spaces.pz V z θ) * V z θ)| := by
        rw [hswap]
    _ ≤ ∫ θ in Work.Spaces.Iθ, |∫ z in Work.Spaces.Iz,
          (Work.Spaces.w z) ^ 2 * θw θ * ψ z * ((z * Work.Spaces.pz V z θ) * V z θ)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ θ in Work.Spaces.Iθ, D * (|θw θ| * ∫ z in Set.Ioi (0 : ℝ),
          (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2) :=
        integral_mono_ae hLHSint hRHSint hkey
    _ = D * ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * |θw θ| * (V z θ) ^ 2 := by
        rw [MeasureTheory.integral_const_mul]
        congr 1
        rw [show (fun θ => |θw θ| * ∫ z in Set.Ioi (0 : ℝ),
              (Work.Spaces.w z) ^ 2 * (V z θ) ^ 2)
            = fun θ => ∫ z in Work.Spaces.Iz,
              (Work.Spaces.w z) ^ 2 * |θw θ| * (V z θ) ^ 2 from by
              funext θ
              rw [show (fun z => (Work.Spaces.w z) ^ 2 * |θw θ| * (V z θ) ^ 2)
                  = fun z => |θw θ| * ((Work.Spaces.w z) ^ 2 * (V z θ) ^ 2) from by
                    funext z; ring]
              rw [MeasureTheory.integral_const_mul]
              rw [setIntegral_congr_set Work.FTS.StrongPersist.H6Pair6Aux.dzSelf2d_Iz_ae]]
        rw [← MeasureTheory.integral_integral_swap hF]

end Work.FTS.StrongPersist.H6Pair6Aux.T5bAux
end
