import Mathlib
import Submission.Work.Asymptotics.contourLeftDefs
import Submission.Work.Asymptotics.MiddleRange.Basic
import Submission.Work.Asymptotics.straightPartSet
import Submission.Work.Asymptotics.divisor_lower_of_compact
import Submission.Work.Asymptotics.Instances
import Submission.Work.Asymptotics.Holomorphy
import Submission.Work.Asymptotics.Basic
import Submission.Work.Asymptotics.Divisor
import Submission.Work.Asymptotics.divisor_lower_compact
import Submission.Work.Asymptotics.growthPrefactor_lower_atTop
import Submission.Work.Asymptotics.growthPrefactor_lower_atZero
import Submission.Work.Asymptotics.differentiableAt_Kfun_tau
import Submission.Work.Asymptotics.Eisenstein_atZero
import Submission.Work.Asymptotics.norm_Eisenstein_imagAxis_atZero
import Submission.Work.Asymptotics.norm_theta_imagAxis_atZero
import Submission.Work.Asymptotics.norm_L_imagAxis_atZero
import Submission.Work.Asymptotics.aestronglyMeasurable_contourIntegrand_clean
import Submission.Work.Asymptotics.norm_Kaxis_Kfun8_le_near_zero
import Submission.Work.Asymptotics.DeltaFun_imagAxis_atTop
import Submission.Work.Asymptotics.jInvariantFun_imagAxis_atTop
import Submission.Work.Asymptotics.DeltaFun_imagAxis_atZero
import Submission.Work.Asymptotics.MFix.KAux
import Submission.Work.Asymptotics.MFix.KPlusSlash
import Submission.Work.Asymptotics.MFix.KMinusSlashBall
import Submission.Work.Asymptotics.MFix.KXiDefs
import Submission.Work.Asymptotics.MFix.Xi8Eq
import Submission.Work.Asymptotics.MFix.Xi24Eq
import Submission.Work.Asymptotics.KMinusCuspBallLimit
import Submission.Work.Asymptotics.cuspAtomLimits
import Submission.Work.Asymptotics.KMinusCuspBallDefs
import Submission.Work.Asymptotics.MFix.KMinusCuspBall
import Submission.Work.Asymptotics.MFix.MdiffEta
import Submission.Work.Residues.ThetaDecay

noncomputable section

open MeasureTheory Filter Topology UpperHalfPlane
open ModularForm ModularGroup
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

set_option maxHeartbeats 4000000

namespace MR

/-! ## Axis helpers (vendored from `Work.Asymptotics.KernelBoundAux`) -/

lemma imagAxis_coe (t : ℝ) (ht : 0 < t) :
    ((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I := rfl

lemma norm_imagAxis (t : ℝ) (ht : 0 < t) :
    ‖((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ)‖ = t := by
  show ‖((t : ℂ) * Complex.I)‖ = t
  rw [norm_mul, Complex.norm_I, mul_one]
  have h : ‖((t : ℂ))‖ = |t| := RCLike.norm_ofReal t
  rw [h, abs_of_pos ht]

lemma scale_imagAxis (t : ℝ) (ht : 0 < t) :
    Work.Kernels.scale (Work.Kernels.imagAxis t ht) = 1 + t⁻¹ + t := by
  have h1 : (Work.Kernels.imagAxis t ht).im = t := by
    show ((t : ℂ) * Complex.I).im = t
    simp
  have h2 : ‖((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ)‖ = t := norm_imagAxis t ht
  simp only [Work.Kernels.scale, h1, h2]

lemma norm_sub_ge_half' {v w : ℂ} {c A t : ℝ} (hc : 0 < c) (ht : 0 < t)
    (hw : c * Real.exp (2 * Real.pi * t) ≤ ‖w‖) (hv : ‖v‖ ≤ A)
    (hA : 2 * A ≤ c * Real.exp (2 * Real.pi * t)) :
    c / 2 * Real.exp (2 * Real.pi * t) ≤ ‖v - w‖ := by
  have h := norm_sub_norm_le w v
  rw [norm_sub_rev] at h
  have h2 : c / 2 * Real.exp (2 * Real.pi * t) ≤ c * Real.exp (2 * Real.pi * t) - A := by
    nlinarith [hA]
  linarith


/-! ## The retained-axis contour carries no pole: the slash bounds without `hclean` -/

theorem KMinus_slash_cusp_ball_nc (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ₀ : UpperHalfPlane} {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ z : UpperHalfPlane), dist τ τ₀ ≤ R → 1 ≤ z.im →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z →
      ‖(z : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2)) * Work.Kernels.KMinus ℓ d τ (ModularGroup.S • z)‖ ≤
        C * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) * Real.exp (-(Real.pi * z.im)) /
          ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ :=
  Work.Asymptotics.MFix.slash_cusp_ball_of ℓ d hd hR (Work.Asymptotics.MFix.KMinusCuspBallBound ℓ d hd hR) (Work.Asymptotics.KMinusCuspBallLimit ℓ d hd)
    (Work.Asymptotics.MFix.mdiff_eta ℓ d)

theorem KPlus_slash_cusp_ball_nc (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ₀ : UpperHalfPlane} {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ z : UpperHalfPlane), dist τ τ₀ ≤ R → 1 ≤ z.im →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z →
      ‖(z : ℂ) ^ (-((2 : ℤ) - (d : ℤ) / 2)) * Work.Kernels.KPlus d τ (ModularGroup.S • z)‖ ≤
        C * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) * Real.exp (-(Real.pi * z.im)) /
          ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
  rcases hd with rfl | rfl
  · obtain ⟨C, hC, hX⟩ := Work.Asymptotics.MFix.Xi8_bound τ₀ R
    have hpi : (Real.pi : ℂ) ^ (-2 : ℤ) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)
    have hcne : (36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I ≠ 0 := by exact mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero
    refine ⟨max (C / ‖(36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
      fun τ z hτ hz hne => ?_⟩
    have hJne : Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z ≠ 0 := sub_ne_zero.mpr hne
    have hDz : Work.Kernels.DeltaFun z
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) ≠ 0 :=
      mul_ne_zero (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z) hJne
    have hcD : (36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I * (Work.Kernels.DeltaFun z
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)) ≠ 0 :=
      mul_ne_zero hcne hDz
    have hkey := Work.Asymptotics.MFix.Xi8_eq τ z hne
    have hXi : (z : ℂ) ^ 2 * Work.Kernels.KPlus 8 τ (ModularGroup.S • z)
        = Work.Asymptotics.MFix.Xi8 τ z / ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I * (Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z))) := by
      rw [eq_div_iff hcD]
      rw [mul_comm ((z : ℂ) ^ 2 * Work.Kernels.KPlus 8 τ (ModularGroup.S • z))
        ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I * (Work.Kernels.DeltaFun z
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)))]
      exact hkey
    have hzpow : (z : ℂ) ^ (-((2 : ℤ) - ((8 : ℕ) : ℤ) / 2)) = (z : ℂ) ^ 2 := by
      rw [show -((2 : ℤ) - ((8 : ℕ) : ℤ) / 2) = (2 : ℤ) by norm_num, _root_.zpow_ofNat]
    rw [hzpow, hXi, norm_div, norm_mul]
    have hq := hX τ z hτ hz
    have hqn : ‖Work.Kernels.qParamFun z‖ = Real.exp (-(2 * Real.pi * z.im)) := Work.Asymptotics.MFix.norm_qParamFun z
    have hqle : Real.exp (-(2 * Real.pi * z.im))
        ≤ (1 + ‖(z : ℂ)‖) ^ 2 * Real.exp (-(Real.pi * z.im)) := by
      have h1 : Real.exp (-(2 * Real.pi * z.im)) ≤ Real.exp (-(Real.pi * z.im)) := by
        rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, z.im_pos]
      have h3 : (1 : ℝ) ≤ 1 + ‖(z : ℂ)‖ := by
        have h := norm_nonneg (z : ℂ); linarith
      have h2 : (1 : ℝ) ≤ (1 + ‖(z : ℂ)‖) ^ 2 := by
        calc (1 : ℝ) = 1 * 1 := by ring
          _ ≤ (1 + ‖(z : ℂ)‖) * (1 + ‖(z : ℂ)‖) :=
              mul_le_mul h3 h3 (by norm_num) (by positivity)
          _ = (1 + ‖(z : ℂ)‖) ^ 2 := by ring
      nlinarith [Real.exp_pos (-(Real.pi * z.im)), h1, h2]
    have hDn0 : (0 : ℝ) ≤ C / ‖(36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖ := div_nonneg hC.le (norm_nonneg _)
    have hXn0 : (0 : ℝ) ≤ (1 + ‖(z : ℂ)‖) ^ 2 * Real.exp (-(Real.pi * z.im))
        / ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ :=
      div_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) (norm_nonneg _)
    calc ‖Work.Asymptotics.MFix.Xi8 τ z‖ / (‖(36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖ * ‖Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖)
        ≤ C * ‖Work.Kernels.qParamFun z‖ / (‖(36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖ * ‖Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖) :=
          div_le_div_of_nonneg_right hq (by positivity)
      _ = C / ‖(36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖ * (‖Work.Kernels.qParamFun z‖
            / ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖) := by ring
      _ ≤ C / ‖(36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖ * ((1 + ‖(z : ℂ)‖) ^ 2 * Real.exp (-(Real.pi * z.im))
            / ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖) := by
          apply mul_le_mul_of_nonneg_left _ hDn0
          rw [hqn]
          exact div_le_div_of_nonneg_right hqle (norm_nonneg _)
      _ ≤ max (C / ‖(36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖) 1 * ((1 + ‖(z : ℂ)‖) ^ 2 * Real.exp (-(Real.pi * z.im))
            / ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hXn0
      _ = max (C / ‖(36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖) 1 * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) * Real.exp (-(Real.pi * z.im))
            / ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by ring
  · obtain ⟨C, hC, hX⟩ := Work.Asymptotics.MFix.Xi24_bound τ₀ R
    have hpi : (Real.pi : ℂ) ^ (-2 : ℤ) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)
    have hcne : (36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I ≠ 0 := by exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by simp [Work.Kernels.c1728])) hpi) Complex.I_ne_zero
    refine ⟨max (C / ‖(36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
      fun τ z hτ hz hne => ?_⟩
    have hJne : Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z ≠ 0 := sub_ne_zero.mpr hne
    have hDz : Work.Kernels.DeltaFun z
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) ≠ 0 :=
      mul_ne_zero (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z) hJne
    have hcD : (36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I * (Work.Kernels.DeltaFun z
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)) ≠ 0 :=
      mul_ne_zero hcne hDz
    have hkey := Work.Asymptotics.MFix.Xi24_eq τ z hne
    have hXi : (z : ℂ) ^ 10 * Work.Kernels.KPlus 24 τ (ModularGroup.S • z)
        = Work.Asymptotics.MFix.Xi24 τ z / ((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I * (Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z))) := by
      rw [eq_div_iff hcD]
      rw [mul_comm ((z : ℂ) ^ 10 * Work.Kernels.KPlus 24 τ (ModularGroup.S • z))
        ((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I * (Work.Kernels.DeltaFun z
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)))]
      exact hkey
    have hzpow : (z : ℂ) ^ (-((2 : ℤ) - ((24 : ℕ) : ℤ) / 2)) = (z : ℂ) ^ 10 := by
      rw [show -((2 : ℤ) - ((24 : ℕ) : ℤ) / 2) = (10 : ℤ) by norm_num, _root_.zpow_ofNat]
    rw [hzpow, hXi, norm_div, norm_mul]
    have hq := hX τ z hτ hz
    have hqn : ‖Work.Kernels.qParamFun z‖ = Real.exp (-(2 * Real.pi * z.im)) := Work.Asymptotics.MFix.norm_qParamFun z
    have hqle : Real.exp (-(2 * Real.pi * z.im))
        ≤ (1 + ‖(z : ℂ)‖) ^ 2 * Real.exp (-(Real.pi * z.im)) := by
      have h1 : Real.exp (-(2 * Real.pi * z.im)) ≤ Real.exp (-(Real.pi * z.im)) := by
        rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, z.im_pos]
      have h3 : (1 : ℝ) ≤ 1 + ‖(z : ℂ)‖ := by
        have h := norm_nonneg (z : ℂ); linarith
      have h2 : (1 : ℝ) ≤ (1 + ‖(z : ℂ)‖) ^ 2 := by
        calc (1 : ℝ) = 1 * 1 := by ring
          _ ≤ (1 + ‖(z : ℂ)‖) * (1 + ‖(z : ℂ)‖) :=
              mul_le_mul h3 h3 (by norm_num) (by positivity)
          _ = (1 + ‖(z : ℂ)‖) ^ 2 := by ring
      nlinarith [Real.exp_pos (-(Real.pi * z.im)), h1, h2]
    have hDn0 : (0 : ℝ) ≤ C / ‖(36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖ := div_nonneg hC.le (norm_nonneg _)
    have hXn0 : (0 : ℝ) ≤ (1 + ‖(z : ℂ)‖) ^ 2 * Real.exp (-(Real.pi * z.im))
        / ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ :=
      div_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) (norm_nonneg _)
    calc ‖Work.Asymptotics.MFix.Xi24 τ z‖ / (‖(36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖ * ‖Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖)
        ≤ C * ‖Work.Kernels.qParamFun z‖ / (‖(36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖ * ‖Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖) :=
          div_le_div_of_nonneg_right hq (by positivity)
      _ = C / ‖(36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖ * (‖Work.Kernels.qParamFun z‖
            / ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖) := by ring
      _ ≤ C / ‖(36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖ * ((1 + ‖(z : ℂ)‖) ^ 2 * Real.exp (-(Real.pi * z.im))
            / ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖) := by
          apply mul_le_mul_of_nonneg_left _ hDn0
          rw [hqn]
          exact div_le_div_of_nonneg_right hqle (norm_nonneg _)
      _ ≤ max (C / ‖(36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖) 1 * ((1 + ‖(z : ℂ)‖) ^ 2 * Real.exp (-(Real.pi * z.im))
            / ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hXn0
      _ = max (C / ‖(36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I‖) 1 * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) * Real.exp (-(Real.pi * z.im))
            / ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by ring


/-! ## The cusp-`0` exponential decay (vendored from `Work.Asymptotics.norm_Kaxis_le_exp_neg_inv_of_ne`) -/

lemma divisor_iinv_lower (τ₀ : UpperHalfPlane) (R : ℝ) :
    ∃ T : ℝ, 0 < T ∧ ∀ (t : ℝ) (ht : 0 < t), t ≤ T → ∀ τ : UpperHalfPlane, dist τ τ₀ ≤ R →
      (1 : ℝ) / 2 ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)) *
        (Work.Kernels.jInvariantFun τ -
          Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)))‖ := by
  obtain ⟨Ce, hCe, hE4dec⟩ := Work.Residues.E4Fun_decay
  obtain ⟨Cd, hCd, hDdec⟩ := Work.Residues.DeltaFun_decay
  have hc : IsCompact (Metric.closedBall τ₀ R) := isCompact_closedBall τ₀ R
  have hE4' : Continuous (fun τ : UpperHalfPlane => Work.Kernels.E4Fun τ) :=
    (ModularForm.holo' ModularForm.E₄).continuous
  have hjcont : ContinuousOn (fun τ : UpperHalfPlane => Work.Kernels.jInvariantFun τ)
      (Metric.closedBall τ₀ R) :=
    ((hE4'.pow 3).div ((CuspForm.holo' CuspForm.discriminant).continuous)
      (fun τ => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)).continuousOn
  obtain ⟨Mj, hMj⟩ := hc.exists_bound_of_continuousOn hjcont
  have hM0 : 0 ≤ max Mj 0 := le_max_right _ _
  set M : ℝ := max Mj 0 with hMdef
  have hMb : ∀ τ : UpperHalfPlane, dist τ τ₀ ≤ R → ‖Work.Kernels.jInvariantFun τ‖ ≤ M :=
    fun τ hτ => le_trans (hMj τ hτ) (le_max_left _ _)
  set A : ℝ := Cd * M + 1 with hAdef
  have hA1 : 1 ≤ A := by rw [hAdef]; have := mul_nonneg hCd.le hM0; linarith
  set B : ℝ := Ce * 10 + 1 with hBdef
  have hB1 : 1 ≤ B := by rw [hBdef]; have := mul_nonneg hCe.le (by norm_num : (0:ℝ) ≤ 10); linarith
  set K : ℝ := max (8 * A) (8 * B) with hKdef
  have hK1 : 1 < K := by
    rw [hKdef]
    have h1 : (8:ℝ) ≤ 8 * A := by nlinarith
    exact lt_of_lt_of_le (by norm_num) (le_trans h1 (le_max_left _ _))
  have hK0 : 0 < K := lt_trans one_pos hK1
  have h80 : (8:ℝ) * A ≤ K := by rw [hKdef]; exact le_max_left _ _
  have h8B : (8:ℝ) * B ≤ K := by rw [hKdef]; exact le_max_right _ _
  have hlogK : 0 < Real.log K := Real.log_pos hK1
  refine ⟨min 1 (2 * Real.pi / Real.log K), lt_min one_pos (div_pos (by positivity) hlogK), ?_⟩
  intro t ht htT τ hτ
  have ht1 : t ≤ 1 := le_trans htT (min_le_left _ _)
  have htK : t ≤ 2 * Real.pi / Real.log K := le_trans htT (min_le_right _ _)
  have hinv0 : 0 < t⁻¹ := inv_pos.mpr ht
  set w : UpperHalfPlane := Work.Kernels.imagAxis t⁻¹ hinv0 with hwdef
  have hwim : w.im = t⁻¹ := by simp [hwdef, Work.Kernels.imagAxis]
  have hw1 : 1 ≤ w.im := by
    rw [hwim, le_inv_comm₀ one_pos ht]
    simpa using ht1
  have hexpK : Real.exp (-(2 * Real.pi * w.im)) ≤ 1 / K := by
    rw [hwim, show -(2 * Real.pi * t⁻¹) = -(2 * Real.pi / t) by rw [div_eq_mul_inv]]
    have h1 : -(2 * Real.pi / t) ≤ -(Real.log K) := by
      rw [neg_le_neg_iff]
      have h2 : t * Real.log K ≤ 2 * Real.pi := (le_div_iff₀ hlogK).mp htK
      rw [le_div_iff₀ ht]; linarith
    calc Real.exp (-(2 * Real.pi / t)) ≤ Real.exp (-(Real.log K)) := Real.exp_le_exp.mpr h1
      _ = 1 / K := by rw [Real.exp_neg, Real.exp_log hK0, one_div]
  have hDz : ‖Work.Kernels.DeltaFun w‖ ≤ Cd / K := by
    have h := hDdec w hw1
    have h2 : Cd * Real.exp (-(2 * Real.pi * w.im)) ≤ Cd / K := by
      rw [← mul_one_div]; exact mul_le_mul_of_nonneg_left hexpK hCd.le
    linarith
  have hE4z : ‖Work.Kernels.E4Fun w - 1‖ ≤ Ce / K := by
    have h := hE4dec w hw1
    have h2 : Ce * Real.exp (-(2 * Real.pi * w.im)) ≤ Ce / K := by
      rw [← mul_one_div]; exact mul_le_mul_of_nonneg_left hexpK hCe.le
    linarith
  have hE4zsmall : ‖Work.Kernels.E4Fun w - 1‖ ≤ 1 / 2 := by
    have h1 : Ce / K ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (lt_trans one_pos hK1) (by norm_num : (0:ℝ) < 2)]
      have h2 : (2:ℝ) * Ce ≤ 8 * B := by rw [hBdef]; nlinarith
      nlinarith [h2, h8B]
    linarith [hE4z, h1]
  have hDjz : Work.Kernels.DeltaFun w * Work.Kernels.jInvariantFun w = Work.Kernels.E4Fun w ^ 3 :=
    Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun w
  have hE4cube : ‖Work.Kernels.E4Fun w ^ 3 - 1‖ ≤ 1 / 4 := by
    have hfac : Work.Kernels.E4Fun w ^ 3 - 1
        = (Work.Kernels.E4Fun w - 1) * (Work.Kernels.E4Fun w ^ 2 + Work.Kernels.E4Fun w + 1) := by
      ring
    have hnorm : ‖Work.Kernels.E4Fun w‖ ≤ 2 := by
      have h := norm_sub_norm_le (Work.Kernels.E4Fun w) (1 : ℂ)
      rw [norm_one] at h
      have h2 := abs_le.mp (abs_norm_sub_norm_le (Work.Kernels.E4Fun w) (1:ℂ))
      nlinarith [hE4zsmall, norm_nonneg (Work.Kernels.E4Fun w), h2.1, h2.2, h]
    have hb : ‖Work.Kernels.E4Fun w ^ 2 + Work.Kernels.E4Fun w + 1‖ ≤ 10 := by
      calc ‖Work.Kernels.E4Fun w ^ 2 + Work.Kernels.E4Fun w + 1‖
          ≤ ‖Work.Kernels.E4Fun w ^ 2‖ + ‖Work.Kernels.E4Fun w‖ + ‖(1:ℂ)‖ := by
            exact le_trans (norm_add_le _ _) (add_le_add (norm_add_le _ _) le_rfl)
        _ = ‖Work.Kernels.E4Fun w‖^2 + ‖Work.Kernels.E4Fun w‖ + 1 := by
            rw [norm_pow, norm_one]
        _ ≤ 10 := by nlinarith [hnorm, norm_nonneg (Work.Kernels.E4Fun w)]
    calc ‖Work.Kernels.E4Fun w ^ 3 - 1‖
        = ‖(Work.Kernels.E4Fun w - 1) * (Work.Kernels.E4Fun w ^ 2 + Work.Kernels.E4Fun w + 1)‖ := by
          rw [hfac]
      _ ≤ ‖Work.Kernels.E4Fun w - 1‖ * 10 := by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ ≤ (Ce / K) * 10 := by linarith [hE4z, norm_nonneg (Work.Kernels.E4Fun w - 1)]
      _ ≤ 1 / 4 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (lt_trans one_pos hK1) (by norm_num : (0:ℝ) < 4)]
          have h2 : (4:ℝ) * (Ce * 10) ≤ 8 * B := by rw [hBdef]; nlinarith
          linarith [h2, h8B]
  have hnum : Work.Kernels.DeltaFun w * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun w)
      = Work.Kernels.DeltaFun w * Work.Kernels.jInvariantFun τ - Work.Kernels.E4Fun w ^ 3 := by
    rw [mul_sub, hDjz]
  have hMj : ‖Work.Kernels.jInvariantFun τ‖ ≤ M := hMb τ hτ
  have hDsmall : ‖Work.Kernels.DeltaFun w‖ * M ≤ 1 / 4 := by
    have h1 : Cd / K * M ≤ 1 / 8 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (lt_trans one_pos hK1) (by norm_num : (0:ℝ) < 8)]
      have h2 : (8:ℝ) * (Cd * M) ≤ 8 * A := by rw [hAdef]; nlinarith
      nlinarith [h2, h80]
    have h3 : ‖Work.Kernels.DeltaFun w‖ * M ≤ Cd / K * M :=
      mul_le_mul_of_nonneg_right hDz hM0
    linarith
  have hDsmall' : ‖Work.Kernels.DeltaFun w * Work.Kernels.jInvariantFun τ‖ ≤ 1 / 4 := by
    rw [norm_mul]
    exact le_trans (mul_le_mul_of_nonneg_left hMj (norm_nonneg _)) hDsmall
  have hge : (1:ℝ) / 2 ≤ ‖Work.Kernels.E4Fun w ^ 3 - Work.Kernels.DeltaFun w * Work.Kernels.jInvariantFun τ‖ := by
    have h1 := norm_sub_norm_le (Work.Kernels.E4Fun w ^ 3)
      (Work.Kernels.DeltaFun w * Work.Kernels.jInvariantFun τ)
    have h2 : (3:ℝ) / 4 ≤ ‖Work.Kernels.E4Fun w ^ 3‖ := by
      have h3 := norm_sub_norm_le (1:ℂ) (Work.Kernels.E4Fun w ^ 3)
      rw [norm_one] at h3
      have h3' : ‖(1:ℂ) - Work.Kernels.E4Fun w ^ 3‖ ≤ 1 / 4 := by
        rw [norm_sub_rev]; exact hE4cube
      linarith [h3, h3']
    linarith [h1, h2, hDsmall']
  rw [hnum, norm_sub_rev]
  exact hge

theorem norm_Kaxis_le_exp_neg_inv_of_ne (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {τ₀ : UpperHalfPlane} {R : ℝ} (hR : 0 < R) :
    ∃ C c T : ℝ, 0 < C ∧ 0 < c ∧ 0 < T ∧
      ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t), dist τ τ₀ ≤ R → t ≤ T →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) →
          ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C * Real.exp (-(c / t)) := by

  obtain ⟨C1, hC1pos, hC1⟩ := KPlus_slash_cusp_ball_nc d hd (τ₀ := τ₀) (R := R) hR
  obtain ⟨C2, hC2pos, hC2⟩ := KMinus_slash_cusp_ball_nc ℓ d hd (τ₀ := τ₀) (R := R) hR
  obtain ⟨T0, hT0, hlow⟩ := divisor_iinv_lower τ₀ R
  have hCf : 0 < 4 * (C1 + C2) + 1 := by positivity
  refine ⟨4 * (C1 + C2) + 1, Real.pi / 2, min 1 T0, hCf, by positivity,
    lt_min one_pos hT0, ?_⟩
  intro τ t ht hτ htT hne
  have ht1 : t ≤ 1 := le_trans htT (min_le_left _ _)
  have htT0 : t ≤ T0 := le_trans htT (min_le_right _ _)
  have hinv0 : 0 < t⁻¹ := inv_pos.mpr ht
  set w : UpperHalfPlane := Work.Kernels.imagAxis t⁻¹ hinv0 with hwdef
  have hwim : w.im = t⁻¹ := by simp [hwdef, Work.Kernels.imagAxis]
  have hw1 : 1 ≤ w.im := by
    rw [hwim, inv_eq_one_div]
    exact (one_le_div₀ ht).mpr ht1
  have hwn : ‖(w : ℂ)‖ = t⁻¹ := by
    have h1 : (w : ℂ) = (((t⁻¹ : ℝ)) : ℂ) * Complex.I := by rw [hwdef]; rfl
    rw [h1, Complex.norm_def, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_I,
      mul_one, ← sq, Real.sqrt_sq_eq_abs, abs_of_nonneg hinv0.le]
  have hSw : ModularGroup.S • w = Work.Kernels.imagAxis t ht := by
    rw [hwdef, Work.Asymptotics.imagAxis_smul_S]
    apply UpperHalfPlane.ext
    simp only [Work.Kernels.imagAxis, UpperHalfPlane.coe_mk, inv_inv]
  have hclean' : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun w := by
    intro h
    have h2 : Work.Kernels.jInvariantFun τ = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
      rw [← hSw, Work.Kernels.KernelFacts.jInvariantFun_S_smul]
      exact h
    exact hne h2
  have hDne : Work.Kernels.DeltaFun w * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun w) ≠ 0 :=
    mul_ne_zero (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero w) (sub_ne_zero.mpr hclean')
  have hDl0 : 0 < ‖Work.Kernels.DeltaFun w * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun w)‖ :=
    norm_pos_iff.mpr hDne
  have hden := hlow t ht htT0 τ hτ
  have hA : (1 + t⁻¹) ^ 2 ≤ 4 * t ^ (((2:ℤ) - (d:ℤ)/2)) := by
    have h1 : 1 ≤ t⁻¹ := (one_le_inv₀ ht).mpr ht1
    have h2 : (1 + t⁻¹) ^ 2 ≤ 4 * (t⁻¹) ^ 2 := by
      have h := pow_le_pow_left₀ (show (0:ℝ) ≤ 1 + t⁻¹ by positivity)
        (show 1 + t⁻¹ ≤ 2 * t⁻¹ by linarith [h1]) 2
      nlinarith [h]
    have h3 : 4 * (t⁻¹) ^ 2 ≤ 4 * t ^ (((2:ℤ) - (d:ℤ)/2)) := by
      have hp : (t⁻¹)^2 = t ^ (-2:ℤ) := by rw [inv_pow]; rfl
      rcases hd with h8 | h24
      · subst h8
        rw [hp]
        norm_num
      · subst h24
        have h10 : ((2:ℤ) - ((24:ℕ):ℤ)/2) = -10 := by norm_num
        rw [hp, h10]
        have e2 : t ^ (-2:ℤ) = (t ^ (2:ℕ))⁻¹ := by simp
        have e10 : t ^ (-10:ℤ) = (t ^ (10:ℕ))⁻¹ := by simp
        rw [e2, e10]
        exact mul_le_mul_of_nonneg_left
          ((inv_le_inv₀ (pow_pos ht 2) (pow_pos ht 10)).mpr
            (pow_le_pow_of_le_one ht.le ht1 (by norm_num : 2 ≤ 10))) (by norm_num : (0:ℝ) ≤ 4)
    linarith [h2, h3]
  have hbnd : ∀ (C : ℝ) (K : ℂ), 0 ≤ C →
      ‖(w : ℂ) ^ (-((2:ℤ) - (d:ℤ)/2)) * K‖ ≤
        C * (1 + t⁻¹) ^ 2 * Real.exp (-(Real.pi / t)) /
          ‖Work.Kernels.DeltaFun w * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun w)‖ →
      ‖K‖ ≤ 8 * C * Real.exp (-(Real.pi / t)) := by
    intro C K hC0 hK
    have hk0 : 0 < t ^ (((2:ℤ) - (d:ℤ)/2)) := zpow_pos ht _
    have hfac : ‖(w : ℂ) ^ (-((2:ℤ) - (d:ℤ)/2)) * K‖
        = t ^ (((2:ℤ) - (d:ℤ)/2)) * ‖K‖ := by
      have h1 : ‖(w : ℂ) ^ (-((2:ℤ) - (d:ℤ)/2))‖ = t ^ (((2:ℤ) - (d:ℤ)/2)) := by
        rw [norm_zpow, hwn, _root_.inv_zpow, zpow_neg, inv_inv]
      rw [norm_mul, h1]
    rw [hfac] at hK
    have hkey : C * (1 + t⁻¹) ^ 2 * Real.exp (-(Real.pi / t))
          / ‖Work.Kernels.DeltaFun w * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun w)‖
        ≤ t ^ (((2:ℤ) - (d:ℤ)/2)) * (8 * C * Real.exp (-(Real.pi / t))) := by
      rw [div_le_iff₀ hDl0]
      have hDl1 : 1 ≤ 2 * ‖Work.Kernels.DeltaFun w
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun w)‖ := by
        linarith [hden, hDl0]
      have htk0' : 0 < t ^ (((2:ℤ) - (d:ℤ)/2)) := zpow_pos ht _
      nlinarith [hA, hDl1, hC0, hDl0, htk0', Real.exp_pos (-(Real.pi / t)),
        mul_le_mul_of_nonneg_left hA (by positivity : (0:ℝ) ≤ C * Real.exp (-(Real.pi / t))),
        mul_le_mul_of_nonneg_left hDl1 (by positivity : (0:ℝ) ≤
          4 * C * Real.exp (-(Real.pi / t)) * t ^ (((2:ℤ) - (d:ℤ)/2)))]
    calc ‖K‖ = t ^ (((2:ℤ) - (d:ℤ)/2)) * ‖K‖ / t ^ (((2:ℤ) - (d:ℤ)/2)) := by
          rw [mul_div_cancel_left₀ _ (ne_of_gt hk0)]
      _ ≤ (t ^ (((2:ℤ) - (d:ℤ)/2)) * (8 * C * Real.exp (-(Real.pi / t))))
            / t ^ (((2:ℤ) - (d:ℤ)/2)) := div_le_div_of_nonneg_right (le_trans hK hkey) hk0.le
      _ = 8 * C * Real.exp (-(Real.pi / t)) := by rw [mul_div_cancel_left₀ _ (ne_of_gt hk0)]
  have hK1 : ‖Work.Kernels.KPlus d τ (Work.Kernels.imagAxis t ht)‖
      ≤ 8 * C1 * Real.exp (-(Real.pi / t)) := by
    refine hbnd C1 _ hC1pos.le ?_
    have hb := hC1 τ w hτ hw1 hclean'
    rw [hSw] at hb
    simp only [hwim, hwn] at hb
    rw [show Real.exp (-(Real.pi * t⁻¹)) = Real.exp (-(Real.pi / t)) by rw [div_eq_mul_inv]] at hb
    exact hb
  have hK2 : ‖Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht)‖
      ≤ 8 * C2 * Real.exp (-(Real.pi / t)) := by
    refine hbnd C2 _ hC2pos.le ?_
    have hb := hC2 τ w hτ hw1 hclean'
    rw [hSw] at hb
    simp only [hwim, hwn] at hb
    rw [show Real.exp (-(Real.pi * t⁻¹)) = Real.exp (-(Real.pi / t)) by rw [div_eq_mul_inv]] at hb
    exact hb
  have hKaxis : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
      = Work.Kernels.Kfun ℓ d τ (Work.Kernels.imagAxis t ht) := by
    rw [Work.Kernels.Kaxis, dif_pos ht]
  rw [hKaxis, Work.Kernels.Kfun]
  have hrexp : Real.exp (-(Real.pi / t)) ≤ Real.exp (-(Real.pi / 2 / t)) := by
    rw [Real.exp_le_exp, neg_le_neg_iff]
    rw [div_le_div_iff₀ ht ht]
    nlinarith [Real.pi_pos]
  calc ‖(Work.Kernels.KPlus d τ (Work.Kernels.imagAxis t ht)
        + Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht)) / 2‖
      ≤ (‖Work.Kernels.KPlus d τ (Work.Kernels.imagAxis t ht)‖
          + ‖Work.Kernels.KMinus ℓ d τ (Work.Kernels.imagAxis t ht)‖) / 2 := by
        rw [norm_div]
        norm_num
        exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
    _ ≤ (8 * C1 * Real.exp (-(Real.pi / t))
          + 8 * C2 * Real.exp (-(Real.pi / t))) / 2 :=
        div_le_div_of_nonneg_right (add_le_add hK1 hK2) (by norm_num)
    _ = (4 * (C1 + C2)) * Real.exp (-(Real.pi / t)) := by ring
    _ ≤ (4 * (C1 + C2) + 1) * Real.exp (-(Real.pi / 2 / t)) := by
        have h4 : 4 * (C1 + C2) ≤ 4 * (C1 + C2) + 1 := by linarith
        have hp : 0 < Real.exp (-(Real.pi / t)) := Real.exp_pos _
        calc (4 * (C1 + C2)) * Real.exp (-(Real.pi / t))
            ≤ (4 * (C1 + C2) + 1) * Real.exp (-(Real.pi / t)) :=
              mul_le_mul_of_nonneg_right h4 hp.le
          _ ≤ (4 * (C1 + C2) + 1) * Real.exp (-(Real.pi / 2 / t)) :=
              mul_le_mul_of_nonneg_left hrexp (by positivity)


/-! ## Mathlib-level helpers used by the dominator -/

/-- For every constant `M` there is `T > 0` with `M ≤ exp (2 π t)` for all `t ≥ T`. -/
lemma exists_const_le_exp_two_pi_mul (M : ℝ) :
    ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, T ≤ t → M ≤ Real.exp (2 * Real.pi * t) := by
  by_cases hM : M ≤ 1
  · exact ⟨1, one_pos, fun t ht => le_trans hM (Real.one_le_exp (by nlinarith [Real.pi_pos, ht]))⟩
  · push_neg at hM
    refine ⟨max 1 (Real.log M / (2 * Real.pi)), lt_of_lt_of_le one_pos (le_max_left _ _),
      fun t ht => ?_⟩
    have hlog : Real.log M ≤ 2 * Real.pi * t := by
      have h1 : Real.log M / (2 * Real.pi) ≤ t := le_trans (le_max_right _ _) ht
      have h2 : 0 < 2 * Real.pi := by positivity
      have h3 : Real.log M ≤ t * (2 * Real.pi) := (div_le_iff₀ h2).mp h1
      linarith
    calc M = Real.exp (Real.log M) := (Real.exp_log (lt_trans zero_lt_one hM)).symm
      _ ≤ Real.exp (2 * Real.pi * t) := Real.exp_le_exp.mpr hlog

/-- `t ↦ A (1+t)^n e^{-bt}` is integrable on `(0,∞)` for `b > 0`. -/
lemma integrableOn_add_one_pow_mul_exp_neg (A b : ℝ) (n : ℕ) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => A * (1 + t) ^ n * Real.exp (-(b * t))) (Set.Ioi (0 : ℝ)) := by
  have hleft : IntegrableOn (fun t : ℝ => A * (1 + t) ^ n * Real.exp (-(b * t)))
      (Set.Ioc (0 : ℝ) 1) := by
    refine IntegrableOn.of_bound (by simp) ?_ (|A| * 2 ^ n + 1) ?_
    · apply Measurable.aestronglyMeasurable
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := ht.1
      have ht1 : t ≤ 1 := ht.2
      have h1 : (1 + t) ^ n ≤ 2 ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      have he : Real.exp (-(b * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      have h2n : (0 : ℝ) ≤ 2 ^ n := pow_nonneg (by norm_num) n
      have hAn : (0 : ℝ) ≤ |A| * 2 ^ n := mul_nonneg (abs_nonneg A) h2n
      have htn : (0 : ℝ) ≤ (1 + t) ^ n := pow_nonneg (by linarith) n
      calc ‖A * (1 + t) ^ n * Real.exp (-(b * t))‖
          = |A| * (1 + t) ^ n * Real.exp (-(b * t)) := by
            rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg htn,
              abs_of_nonneg (Real.exp_nonneg _)]
        _ ≤ |A| * 2 ^ n * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 (abs_nonneg A)) he (Real.exp_nonneg _) hAn
        _ ≤ |A| * 2 ^ n + 1 := by linarith
  have hright : IntegrableOn (fun t : ℝ => A * (1 + t) ^ n * Real.exp (-(b * t)))
      (Set.Ici (1 : ℝ)) := by
    have hmaj : IntegrableOn (fun t : ℝ => (|A| * 2 ^ n) * (t ^ (n : ℝ) * Real.exp (-(b * t))))
        (Set.Ici (1 : ℝ)) := by
      have hn1 : (-1 : ℝ) < (n : ℝ) := by
        have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have h0 : IntegrableOn (fun t : ℝ => t ^ (n : ℝ) * Real.exp (-(b * t)))
          (Set.Ioi (0 : ℝ)) := by
        simpa using
          integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (n : ℝ)) (b := b) hn1 one_pos hb
      exact IntegrableOn.mono_set (h0.const_mul (|A| * 2 ^ n))
        (Set.Ici_subset_Ioi.mpr (by norm_num : (0 : ℝ) < 1))
    refine Integrable.mono' hmaj ?_ ?_
    · apply Measurable.aestronglyMeasurable
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      have ht1 : 1 ≤ t := ht
      have ht0 : 0 < t := lt_of_lt_of_le one_pos ht1
      have hpow : (1 + t) ^ n ≤ (2 * t) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      rw [mul_pow] at hpow
      have hn0 : (0 : ℝ) ≤ t ^ n := pow_nonneg ht0.le n
      have h2n : (0 : ℝ) ≤ 2 ^ n := pow_nonneg (by norm_num) n
      have h1t : (0 : ℝ) ≤ (1 + t) ^ n := pow_nonneg (by linarith) n
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg h1t, abs_of_nonneg (Real.exp_nonneg _)]
      calc |A| * (1 + t) ^ n * Real.exp (-(b * t))
          ≤ |A| * (2 ^ n * t ^ n) * Real.exp (-(b * t)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (abs_nonneg A))
              (Real.exp_nonneg _)
        _ = (|A| * 2 ^ n) * (t ^ n * Real.exp (-(b * t))) := by ring
        _ = (|A| * 2 ^ n) * (t ^ (n : ℝ) * Real.exp (-(b * t))) := by
            rw [Real.rpow_natCast]
  have hset : Set.Ioc (0 : ℝ) 1 ∪ Set.Ici (1 : ℝ) = Set.Ioi (0 : ℝ) := by
    ext t
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ici, Set.mem_Ioi]
    constructor
    · rintro (⟨h1, _⟩ | h2)
      · exact h1
      · exact lt_of_lt_of_le zero_lt_one h2
    · intro h1
      by_cases h2 : t ≤ 1
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr (le_of_lt (lt_of_not_ge h2))
  rw [← hset]
  exact hleft.union hright


/-! ## The dominator -/

theorem exists_bound_straightPart_of_clean (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {r t₀ A₁ A₂ : ℝ} (hr : r ≠ 0) (hrange : d = 8 ∨ 2 < r ^ 2)
    {x : UpperHalfPlane} {ρ : ℝ} (hρ : 0 < ρ)
    (hclean : ∀ (t : ℝ) (ht : 0 < t), t ∈ straightPartSet t₀ A₁ A₂ →
      ∀ τ : UpperHalfPlane, dist τ x ≤ ρ →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    ∃ bound : ℝ → ℝ, IntegrableOn bound (Set.Ioi (0 : ℝ)) ∧
      (∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ bound t) ∧
      ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t), dist τ x ≤ ρ →
        t ∈ straightPartSet t₀ A₁ A₂ →
          ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ * Real.exp (-(Real.pi * r ^ 2 * t))
            ≤ bound t := by
  classical
  -- ## The exponent `Δ(it)^e` of the divisor and the residual Gaussian rate `b`
  set Ee : ℕ := if d = 8 then 1 else 2 with hEedef
  set ex' : ℕ := if d = 8 then 0 else 1 with hex'def
  have hEe_eq : Ee = ex' + 1 := by
    rcases hd with h | h <;> simp [hEedef, hex'def, h]
  have hEe_cast : (Ee : ℝ) = (ex' : ℝ) + 1 := by
    rw [hEe_eq]; push_cast; ring
  -- ## Constants
  obtain ⟨Cn, cn, Tn, hCnp, hcnp, hTnp, hnear⟩ :=
    norm_Kaxis_le_exp_neg_inv_of_ne ℓ d hd hρ
  obtain ⟨S₀, hS₀0, hS₀b⟩ := Work.Asymptotics.MFix.bound_on_ball_real (τ₀ := x) (R := ρ) continuous_scale
  set S : ℝ := max S₀ 1 with hSdef
  have hS1 : 1 ≤ S := le_max_right _ _
  have hS : ∀ τ : UpperHalfPlane, dist τ x ≤ ρ → Work.Kernels.scale τ ≤ S :=
    fun τ hτ => le_trans (hS₀b τ hτ) (le_max_left _ _)
  obtain ⟨α, N, M, hα, hN, hM, hcont⟩ := contour_bound_Kfun ℓ d hd
  obtain ⟨cΔt, CΔt, TΔt, hcΔt, hCΔt, hTΔt, hΔt⟩ := DeltaFun_imagAxis_atTop
  obtain ⟨cj', Tj', hcj', hTj', hj'⟩ := jInvariantFun_imagAxis_atTop
  obtain ⟨δ', Aj, hδ'p, hAj0, hδ'le, hAj⟩ := Work.Asymptotics.MFix.exists_delta_Aj (τ₀ := x) (R := ρ) hρ
  obtain ⟨Texp, hTexp, hTexpb⟩ := exists_const_le_exp_two_pi_mul (2 * Aj / cj')
  set Lt : ℝ := max (max 1 Tn) (max TΔt (max Tj' Texp)) with hLtdef
  have hLt1 : 1 ≤ Lt := le_trans (le_max_left 1 Tn) (le_max_left _ _)
  have hLtTn : Tn ≤ Lt := le_trans (le_max_right 1 Tn) (le_max_left _ _)
  have hLtTΔt : TΔt ≤ Lt := le_trans (le_max_left TΔt _) (le_max_right _ _)
  have hLtTj' : Tj' ≤ Lt :=
    le_trans (le_max_left Tj' Texp) (le_trans (le_max_right TΔt _) (le_max_right _ _))
  have hLtTexp : Texp ≤ Lt :=
    le_trans (le_max_right Tj' Texp) (le_trans (le_max_right TΔt _) (le_max_right _ _))
  set b : ℝ := Real.pi * (r ^ 2 - 2 * (ex' : ℝ)) with hbdef
  have hbpos : 0 < b := by
    rw [hbdef]
    rcases hd with h8 | h24
    · have hex0 : ex' = 0 := by rw [h8] at hex'def; simpa using hex'def
      have h2ex : (2 : ℝ) * (ex' : ℝ) = 0 := by rw [hex0]; norm_num
      rw [h2ex]
      simpa using mul_pos Real.pi_pos (sq_pos_of_ne_zero hr)
    · have hr2 : 2 < r ^ 2 := by
        rcases hrange with h | h
        · exact absurd (h.symm.trans h24) (by norm_num)
        · exact h
      have hex1 : ex' = 1 := by
        rw [h24] at hex'def
        rw [if_neg (by norm_num : ¬((24 : ℕ) = 8))] at hex'def
        exact hex'def
      have h2ex : (2 : ℝ) * (ex' : ℝ) = 2 := by rw [hex1]; norm_num
      rw [h2ex]
      exact mul_pos Real.pi_pos (by linarith)
  -- ## The compact middle range
  set Kmid : Set ℝ :=
    Set.Icc Tn Lt \ (Set.Ioo (t₀ - A₁) (t₀ + A₁) ∪ Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂))
    with hKmidden
  have hKmid_c : IsCompact Kmid := by
    rw [hKmidden]
    refine (isCompact_Icc (a := Tn) (b := Lt)).of_isClosed_subset ?_ Set.diff_subset
    rw [Set.sdiff_eq]
    exact isClosed_Icc.inter (IsOpen.isClosed_compl (isOpen_Ioo.union isOpen_Ioo))
  have hKmid_pos : ∀ t ∈ Kmid, 0 < t := by
    intro t ht
    rw [hKmidden, Set.mem_sdiff, Set.mem_Icc] at ht
    linarith [hTnp, ht.1.1]
  have hKmid_sub : ∀ t ∈ Kmid, t ∈ straightPartSet t₀ A₁ A₂ := by
    intro t ht
    rw [hKmidden, Set.mem_sdiff, Set.mem_Icc, Set.mem_union] at ht
    rw [mem_straightPartSet]
    exact ⟨by linarith [hTnp, ht.1.1], fun h => ht.2 (Or.inl h), fun h => ht.2 (Or.inr h)⟩
  obtain ⟨cmid, hcmidp, hcmid⟩ :=
    divisor_lower_of_compact (d := d) (τ₀ := x) (R := ρ) hρ hKmid_c hKmid_pos
      (fun t ht htK τ hdist => hclean t ht (hKmid_sub t htK) τ hdist)
  have hs0 : 0 ≤ 1 + Tn⁻¹ + Lt := by positivity
  have hS0N : 0 ≤ S ^ N := Real.rpow_nonneg (le_trans zero_le_one hS1) N
  set Cmid : ℝ := α * S ^ N * (1 + Tn⁻¹ + Lt) ^ M / cmid with hCmddef
  have hnum0 : (0 : ℝ) ≤ α * S ^ N * (1 + Tn⁻¹ + Lt) ^ M :=
    mul_nonneg (mul_nonneg hα hS0N) (Real.rpow_nonneg hs0 M)
  have hCmid0 : 0 ≤ Cmid := by rw [hCmddef]; exact div_nonneg hnum0 hcmidp.le
  set Ktop : ℝ := α * S ^ N / (δ' * cΔt ^ Ee * (cj' / 2)) with hKtopdef
  have hKtop0 : 0 ≤ Ktop := by
    rw [hKtopdef]
    exact div_nonneg (mul_nonneg hα hS0N)
      (le_of_lt (mul_pos (mul_pos hδ'p (pow_pos hcΔt Ee)) (div_pos hcj' (by norm_num))))
  -- ## The bound on the far range
  have htop : ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t), dist τ x ≤ ρ → Lt ≤ t →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
        ≤ Ktop * (1 + t⁻¹ + t) ^ M * Real.exp (2 * Real.pi * (ex' : ℝ) * t) := by
    intro τ t ht hdist htLt
    have htTΔt : TΔt ≤ t := le_trans hLtTΔt htLt
    have htTj : Tj' ≤ t := le_trans hLtTj' htLt
    have htTexp : Texp ≤ t := le_trans hLtTexp htLt
    have h1 : δ' ≤ ‖Work.Kernels.DeltaFun τ‖ := hδ'le τ hdist
    have h2 : cΔt * Real.exp (-(2 * Real.pi * t)) ≤
        ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ := (hΔt t ht htTΔt).1
    have hjz : cj' * Real.exp (2 * Real.pi * t) ≤
        ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ := hj' t ht htTj
    have hjτ : ‖Work.Kernels.jInvariantFun τ‖ ≤ Aj := hAj τ hdist
    have hexp : 2 * Aj ≤ cj' * Real.exp (2 * Real.pi * t) := by
      have h := hTexpb t htTexp
      rw [div_le_iff₀ hcj'] at h
      linarith
    have h3 : cj' / 2 * Real.exp (2 * Real.pi * t) ≤
        ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ :=
      norm_sub_ge_half' hcj' ht hjz hjτ hexp
    -- the divisor is bounded below by the cusp asymptotics
    have hgplb : δ' * (cΔt * Real.exp (-(2 * Real.pi * t))) ^ Ee
          * (cj' / 2 * Real.exp (2 * Real.pi * t))
        ≤ ‖Work.Kernels.growthPrefactor d τ (Work.Kernels.imagAxis t ht)‖ := by
      rw [show Work.Kernels.growthPrefactor d τ (Work.Kernels.imagAxis t ht)
          = Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht) ^ Ee
            * (Work.Kernels.jInvariantFun τ
                - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) from by
        simp only [Work.Kernels.growthPrefactor, hEedef]]
      rw [norm_mul, norm_mul, norm_pow]
      have h2' : (cΔt * Real.exp (-(2 * Real.pi * t))) ^ Ee
          ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ^ Ee :=
        pow_le_pow_left₀ (mul_nonneg hcΔt.le (Real.exp_nonneg _)) h2 Ee
      calc δ' * (cΔt * Real.exp (-(2 * Real.pi * t))) ^ Ee
              * (cj' / 2 * Real.exp (2 * Real.pi * t))
          ≤ ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ^ Ee
              * (cj' / 2 * Real.exp (2 * Real.pi * t)) := by
            refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (div_nonneg hcj'.le (by norm_num))
              (Real.exp_nonneg _))
            exact mul_le_mul h1 h2' (pow_nonneg (mul_nonneg hcΔt.le (Real.exp_nonneg _)) Ee)
              (norm_nonneg _)
        _ ≤ ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ^ Ee
              * ‖Work.Kernels.jInvariantFun τ
                  - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ :=
            mul_le_mul_of_nonneg_left h3
              (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) Ee))
    -- the identity relating the two forms of the divisor lower bound
    have hLid : δ' * (cΔt * Real.exp (-(2 * Real.pi * t))) ^ Ee
          * (cj' / 2 * Real.exp (2 * Real.pi * t))
        = δ' * cΔt ^ Ee * (cj' / 2) * Real.exp (-(2 * Real.pi * (ex' : ℝ) * t)) := by
      have hexpid : Real.exp (-(2 * Real.pi * t)) ^ Ee * Real.exp (2 * Real.pi * t)
          = Real.exp (-(2 * Real.pi * (ex' : ℝ) * t)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        rw [hEe_cast]; ring
      calc δ' * (cΔt * Real.exp (-(2 * Real.pi * t))) ^ Ee
              * (cj' / 2 * Real.exp (2 * Real.pi * t))
          = δ' * cΔt ^ Ee * (cj' / 2)
              * (Real.exp (-(2 * Real.pi * t)) ^ Ee * Real.exp (2 * Real.pi * t)) := by
            rw [mul_pow]; ring
        _ = δ' * cΔt ^ Ee * (cj' / 2) * Real.exp (-(2 * Real.pi * (ex' : ℝ) * t)) := by
            rw [hexpid]
    have hnum : α * Work.Kernels.scale τ ^ N * Work.Kernels.scale (Work.Kernels.imagAxis t ht) ^ M
        ≤ α * S ^ N * (1 + t⁻¹ + t) ^ M := by
      rw [scale_imagAxis t ht]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Work.Kernels.scale_pos τ).le (hS τ hdist) hN) hα)
        (Real.rpow_nonneg (by positivity) M)
    have hkey : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
          * (δ' * cΔt ^ Ee * (cj' / 2) * Real.exp (-(2 * Real.pi * (ex' : ℝ) * t)))
        ≤ α * S ^ N * (1 + t⁻¹ + t) ^ M := by
      calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
            * (δ' * cΔt ^ Ee * (cj' / 2) * Real.exp (-(2 * Real.pi * (ex' : ℝ) * t)))
          = ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
              * (δ' * (cΔt * Real.exp (-(2 * Real.pi * t))) ^ Ee
                  * (cj' / 2 * Real.exp (2 * Real.pi * t))) := by rw [hLid]
        _ ≤ ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
              * ‖Work.Kernels.growthPrefactor d τ (Work.Kernels.imagAxis t ht)‖ :=
            mul_le_mul_of_nonneg_left hgplb (norm_nonneg _)
        _ ≤ α * Work.Kernels.scale τ ^ N * Work.Kernels.scale (Work.Kernels.imagAxis t ht) ^ M := hcont τ t ht
        _ ≤ α * S ^ N * (1 + t⁻¹ + t) ^ M := hnum
    -- divide by the constant `D = δ' cΔt^Ee cj'/2`
    have hDpos : 0 < δ' * cΔt ^ Ee * (cj' / 2) :=
      mul_pos (mul_pos hδ'p (pow_pos hcΔt Ee)) (div_pos hcj' (by norm_num))
    have hkey2 : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ * (δ' * cΔt ^ Ee * (cj' / 2))
        ≤ α * S ^ N * (1 + t⁻¹ + t) ^ M * Real.exp (2 * Real.pi * (ex' : ℝ) * t) := by
      have h1 : (‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
            * (δ' * cΔt ^ Ee * (cj' / 2)))
            * Real.exp (-(2 * Real.pi * (ex' : ℝ) * t))
          ≤ α * S ^ N * (1 + t⁻¹ + t) ^ M := by
        rw [mul_assoc]
        exact hkey
      have h2 := (le_div_iff₀ (Real.exp_pos (-(2 * Real.pi * (ex' : ℝ) * t)))).mpr h1
      have h3 : α * S ^ N * (1 + t⁻¹ + t) ^ M / Real.exp (-(2 * Real.pi * (ex' : ℝ) * t))
          = α * S ^ N * (1 + t⁻¹ + t) ^ M * Real.exp (2 * Real.pi * (ex' : ℝ) * t) := by
        rw [div_eq_mul_inv, Real.exp_neg, inv_inv]
      rwa [h3] at h2
    have h4 : α * S ^ N * (1 + t⁻¹ + t) ^ M * Real.exp (2 * Real.pi * (ex' : ℝ) * t)
          / (δ' * cΔt ^ Ee * (cj' / 2))
        = Ktop * (1 + t⁻¹ + t) ^ M * Real.exp (2 * Real.pi * (ex' : ℝ) * t) := by
      rw [hKtopdef, div_eq_mul_inv, div_eq_mul_inv]
      ring
    have h5 := (le_div_iff₀ hDpos).mpr hkey2
    rwa [h4] at h5
  -- ## The bound on the middle range
  have hmid : ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t), dist τ x ≤ ρ →
      t ∈ straightPartSet t₀ A₁ A₂ → Tn < t → t ≤ Lt →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ Cmid := by
    intro τ t ht hdist htE htn htle
    have hmem : t ∈ Kmid := by
      rw [hKmidden, Set.mem_sdiff, Set.mem_Icc, Set.mem_union]
      exact ⟨⟨le_of_lt htn, htle⟩, fun h => h.elim (mem_straightPartSet.mp htE).2.1
        (mem_straightPartSet.mp htE).2.2⟩
    have hgplb := hcmid τ t ht hdist hmem
    have hgppos : 0 < ‖Work.Kernels.growthPrefactor d τ (Work.Kernels.imagAxis t ht)‖ :=
      lt_of_lt_of_le hcmidp hgplb
    have hdiv : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
        ≤ α * Work.Kernels.scale τ ^ N * Work.Kernels.scale (Work.Kernels.imagAxis t ht) ^ M
          / ‖Work.Kernels.growthPrefactor d τ (Work.Kernels.imagAxis t ht)‖ :=
      (le_div_iff₀ hgppos).mpr (hcont τ t ht)
    have hnum : α * Work.Kernels.scale τ ^ N * Work.Kernels.scale (Work.Kernels.imagAxis t ht) ^ M
        ≤ α * S ^ N * (1 + Tn⁻¹ + Lt) ^ M := by
      rw [scale_imagAxis t ht]
      have hs2 : 1 + t⁻¹ + t ≤ 1 + Tn⁻¹ + Lt := by
        have hm1 : t⁻¹ ≤ Tn⁻¹ := (inv_le_inv₀ (lt_trans hTnp htn) hTnp).mpr htn.le
        linarith
      refine mul_le_mul
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Work.Kernels.scale_pos τ).le (hS τ hdist) hN) hα)
        (Real.rpow_le_rpow (add_nonneg (add_nonneg zero_le_one (inv_nonneg.mpr ht.le)) ht.le)
          hs2 hM)
        (Real.rpow_nonneg (add_nonneg (add_nonneg zero_le_one (inv_nonneg.mpr ht.le)) ht.le) M)
        (mul_nonneg hα hS0N)
    calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
        ≤ α * Work.Kernels.scale τ ^ N * Work.Kernels.scale (Work.Kernels.imagAxis t ht) ^ M
          / ‖Work.Kernels.growthPrefactor d τ (Work.Kernels.imagAxis t ht)‖ := hdiv
      _ ≤ α * S ^ N * (1 + Tn⁻¹ + Lt) ^ M / cmid :=
          div_le_div₀ hnum0 hnum hcmidp hgplb
      _ = Cmid := by rw [hCmddef]
  -- ## The dominator
  obtain ⟨n, hnM⟩ : ∃ n : ℕ, M ≤ (n : ℝ) := ⟨Nat.ceil M, Nat.le_ceil M⟩
  set A : ℝ := max (Cmid * Real.exp (b * Lt) / (1 + Tn) ^ n) (max (Ktop * 2 ^ M) 1) with hAdef
  have hTn0 : (1 : ℝ) ≤ 1 + Tn := by linarith [hTnp]
  have hA_mid : Cmid ≤ A * (1 + Tn) ^ n * Real.exp (-(b * Lt)) := by
    have hA_lb : Cmid * Real.exp (b * Lt) / (1 + Tn) ^ n ≤ A := le_max_left _ _
    have hpos : 0 < (1 + Tn) ^ n := pow_pos (by linarith [hTnp]) n
    have hne1 : (1 + Tn) ^ n ≠ 0 := ne_of_gt hpos
    have hne2 : Real.exp (b * Lt) ≠ 0 := Real.exp_ne_zero _
    have hstep : Cmid = Cmid * Real.exp (b * Lt) / (1 + Tn) ^ n * (1 + Tn) ^ n
        / Real.exp (b * Lt) := by
      field_simp
    rw [hstep]
    calc Cmid * Real.exp (b * Lt) / (1 + Tn) ^ n * (1 + Tn) ^ n / Real.exp (b * Lt)
        ≤ A * (1 + Tn) ^ n / Real.exp (b * Lt) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hA_lb hpos.le) (Real.exp_pos _).le
      _ = A * (1 + Tn) ^ n * Real.exp (-(b * Lt)) := by
          rw [Real.exp_neg, div_eq_mul_inv]
  have hA_top : Ktop * 2 ^ M ≤ A := le_trans (le_max_left _ _) (le_max_right _ _)
  have hA1 : 1 ≤ A := le_trans (le_max_right _ _) (le_max_right _ _)
  have hA0 : 0 ≤ A := le_trans zero_le_one hA1
  refine ⟨fun t => Cn * Real.exp Tn * Real.exp (-(cn / t)) * Real.exp (-t)
      + A * (1 + t) ^ n * Real.exp (-(b * t)), ?_, ?_, ?_⟩
  · -- integrability
    have hbd0 : IntegrableOn (fun t : ℝ => Cn * Real.exp Tn * (1 + t) ^ (0:ℕ)
        * Real.exp (-(1 * t))) (Set.Ioi (0 : ℝ)) :=
      integrableOn_add_one_pow_mul_exp_neg (Cn * Real.exp Tn) 1 0 one_pos
    have hbd : IntegrableOn (fun t : ℝ => Cn * Real.exp Tn * Real.exp (-t)) (Set.Ioi (0 : ℝ)) := by
      simpa using hbd0
    have h1 : IntegrableOn (fun t : ℝ => Cn * Real.exp Tn * Real.exp (-(cn / t)) * Real.exp (-t))
        (Set.Ioi (0 : ℝ)) := by
      refine Integrable.mono' hbd ?_ ?_
      · exact (by fun_prop : Measurable (fun t : ℝ =>
          Cn * Real.exp Tn * Real.exp (-(cn / t)) * Real.exp (-t))).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.exp_nonneg _),
          abs_of_nonneg (Real.exp_nonneg _), abs_of_nonneg (Real.exp_nonneg _),
          abs_of_nonneg hCnp.le]
        have hone : Real.exp (-(cn / t)) ≤ 1 :=
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg hcnp.le ht.le))
        exact mul_le_mul_of_nonneg_right
          (mul_le_of_le_one_right (mul_nonneg hCnp.le (Real.exp_nonneg _)) hone)
          (Real.exp_nonneg _)
    have h2 : IntegrableOn (fun t : ℝ => A * (1 + t) ^ n * Real.exp (-(b * t)))
        (Set.Ioi (0 : ℝ)) :=
      integrableOn_add_one_pow_mul_exp_neg A b n hbpos
    exact h1.add h2
  · -- nonnegativity
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    exact add_nonneg (by positivity) (by positivity)
  · -- domination
    intro τ t ht hdist htE
    have hJ : Work.Kernels.jInvariantFun τ
        ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := hclean t ht htE τ hdist
    have hexp1 : Real.exp (-(Real.pi * r ^ 2 * t)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr
        (mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg r)) ht.le))
    by_cases htn : t ≤ Tn
    · -- near the cusp `0`
      have hle := hnear τ t ht hdist htn hJ
      have hb1 : Cn * Real.exp (-(cn / t)) ≤ Cn * Real.exp Tn * Real.exp (-(cn / t))
          * Real.exp (-t) := by
        have h1 : 1 ≤ Real.exp Tn * Real.exp (-t) := by
          rw [← Real.exp_add]
          exact Real.one_le_exp (by linarith [hTnp])
        calc Cn * Real.exp (-(cn / t)) = Cn * Real.exp (-(cn / t)) * 1 := by ring
          _ ≤ Cn * Real.exp (-(cn / t)) * (Real.exp Tn * Real.exp (-t)) :=
              mul_le_mul_of_nonneg_left h1 (mul_nonneg hCnp.le (Real.exp_nonneg _))
          _ = Cn * Real.exp Tn * Real.exp (-(cn / t)) * Real.exp (-t) := by ring
      calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ * Real.exp (-(Real.pi * r ^ 2 * t))
          ≤ (Cn * Real.exp (-(cn / t))) * 1 :=
            mul_le_mul hle hexp1 (Real.exp_nonneg _) (mul_nonneg hCnp.le (Real.exp_nonneg _))
        _ = Cn * Real.exp (-(cn / t)) := by ring
        _ ≤ Cn * Real.exp Tn * Real.exp (-(cn / t)) * Real.exp (-t) := hb1
        _ ≤ Cn * Real.exp Tn * Real.exp (-(cn / t)) * Real.exp (-t)
              + A * (1 + t) ^ n * Real.exp (-(b * t)) :=
            le_add_of_nonneg_right (mul_nonneg (mul_nonneg hA0 (pow_nonneg (by linarith [ht]) n))
              (Real.exp_nonneg _))
    · push_neg at htn
      by_cases htLt : t ≤ Lt
      · -- the compact middle range
        have hle := hmid τ t ht hdist htE htn htLt
        have h1 : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
            * Real.exp (-(Real.pi * r ^ 2 * t)) ≤ Cmid := by
          calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖
                * Real.exp (-(Real.pi * r ^ 2 * t))
              ≤ Cmid * 1 := mul_le_mul hle hexp1 (Real.exp_nonneg _) hCmid0
            _ = Cmid := by ring
        have h2 : Cmid ≤ A * (1 + t) ^ n * Real.exp (-(b * t)) := by
          refine le_trans hA_mid ?_
          have hpt : (1 + Tn) ^ n ≤ (1 + t) ^ n :=
            pow_le_pow_left₀ (by linarith [hTnp]) (by linarith) n
          have hpe : Real.exp (-(b * Lt)) ≤ Real.exp (-(b * t)) :=
            Real.exp_le_exp.mpr (by nlinarith [hbpos, htLt])
          calc A * (1 + Tn) ^ n * Real.exp (-(b * Lt))
              = A * ((1 + Tn) ^ n * Real.exp (-(b * Lt))) := by ring
            _ ≤ A * ((1 + t) ^ n * Real.exp (-(b * t))) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul hpt hpe (Real.exp_nonneg _) (pow_nonneg (by linarith [hTnp]) n)) hA0
            _ = A * (1 + t) ^ n * Real.exp (-(b * t)) := by ring
        refine le_trans (le_trans h1 h2) ?_
        exact le_add_of_nonneg_left (by positivity)
      · -- the far range
        push_neg at htLt
        have hle := htop τ t ht hdist htLt.le
        have hexpid : Real.exp (2 * Real.pi * (ex' : ℝ) * t) * Real.exp (-(Real.pi * r ^ 2 * t))
            = Real.exp (-(b * t)) := by
          rw [← Real.exp_add, hbdef]
          congr 1
          ring
        have hsm : (1 + t⁻¹ + t) ^ M ≤ 2 ^ M * (1 + t) ^ n := by
          have ht1 : 1 ≤ t := le_trans hLt1 htLt.le
          have hle2 : 1 + t⁻¹ + t ≤ 2 * (1 + t) := by
            have hinv : t⁻¹ ≤ 1 := by
              rw [inv_le_one₀ (by linarith)]
              exact ht1
            linarith
          have hbase : (0 : ℝ) ≤ 1 + t⁻¹ + t := by positivity
          calc (1 + t⁻¹ + t) ^ M ≤ (2 * (1 + t)) ^ M :=
                Real.rpow_le_rpow hbase hle2 hM
            _ = 2 ^ M * (1 + t) ^ M := Real.mul_rpow (by norm_num) (by linarith)
            _ ≤ 2 ^ M * (1 + t) ^ n := by
                refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) M)
                rw [show (1 + t) ^ n = (1 + t) ^ ((n : ℕ) : ℝ) by rw [Real.rpow_natCast]]
                exact Real.rpow_le_rpow_of_exponent_le (by linarith) hnM
        have h3 : Ktop * (1 + t⁻¹ + t) ^ M * Real.exp (-(b * t))
            ≤ A * (1 + t) ^ n * Real.exp (-(b * t)) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
          calc Ktop * (1 + t⁻¹ + t) ^ M ≤ Ktop * (2 ^ M * (1 + t) ^ n) :=
                mul_le_mul_of_nonneg_left hsm hKtop0
            _ = Ktop * 2 ^ M * (1 + t) ^ n := by ring
            _ ≤ A * (1 + t) ^ n := mul_le_mul_of_nonneg_right hA_top (pow_nonneg (by linarith) n)
        calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ * Real.exp (-(Real.pi * r ^ 2 * t))
            ≤ (Ktop * (1 + t⁻¹ + t) ^ M * Real.exp (2 * Real.pi * (ex' : ℝ) * t))
                * Real.exp (-(Real.pi * r ^ 2 * t)) :=
              mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _)
          _ = Ktop * (1 + t⁻¹ + t) ^ M
                * (Real.exp (2 * Real.pi * (ex' : ℝ) * t) * Real.exp (-(Real.pi * r ^ 2 * t))) := by
              ring
          _ = Ktop * (1 + t⁻¹ + t) ^ M * Real.exp (-(b * t)) := by rw [hexpid]
          _ ≤ A * (1 + t) ^ n * Real.exp (-(b * t)) := h3
          _ ≤ Cn * Real.exp Tn * Real.exp (-(cn / t)) * Real.exp (-t)
                + A * (1 + t) ^ n * Real.exp (-(b * t)) :=
              le_add_of_nonneg_left (by positivity)

end MR

/-- **The dominator of the retained-axis contour integral (import-compatible copy).**  For `τ` in a
closed ball `B(x,ρ)` on which the retained contour `straightPartSet t₀ A₁ A₂` carries no pole of
`z ↦ K^{(d)}(τ,z)`, there is an integrable function `bound` on `(0,∞)` dominating
`‖K^{(d)}(τ,it)‖·e^{-πr²t}`.

This is a verbatim copy of the *proved* `Work.Asymptotics.exists_bound_straightPart_of_clean`
(module `Submission.Work.Asymptotics.straightPart_dominator`), restated in a module whose import
closure contains at most one of the four modules declaring `Work.Asymptotics.continuous_scale`
(`KernelBoundAux`, `MiddleRange.Basic`, `KaxisMid.Basic`, `PropagateBounds.Estimate`) — the copy
must be usable together with the dimension-`24` cusp-expansion files, whose closures contain
`MiddleRange.Basic`.  The proved original cannot be imported together with `MiddleRange.Basic`,
because it imports `Work.Asymptotics.norm_Kaxis_le_exp_neg_inv_of_ne` and
`Work.Asymptotics.mdifferentiableAt_kernelTransform_of_clean`, which import `KernelBoundAux`.

Suggested route (mechanical): copy `KMinusCuspBallBound` and
`mdifferentiableAt_kernelTransform_of_clean` to new modules, replacing their
`import Submission.Work.Asymptotics.KernelBoundAux` by an import of
`Submission.Work.Asymptotics.MiddleRange.Basic` (which also declares `continuous_scale`, so the
proof text is unchanged there) plus *differently named* local copies of the other few lemmas they
use from `KernelBoundAux` (`bound_on_ball`, `bound_on_ball_real`, `exists_delta_Aj`), renaming the
uses accordingly; then copy `KMinus_slash_cusp_ball`, `slash_cusp_ball_noclean`,
`norm_Kaxis_le_exp_neg_inv_of_ne` and `straightPart_dominator` with their imports redirected to the
new modules; finally rename the dominator.  All statements are unchanged, so the copies are
verbatim apart from the import lines and the renamed local helpers.  (Do NOT import the original
`straightPart_dominator` or `KernelBoundAux`.) -/
theorem exists_bound_straightPart_of_clean_MR (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {r t₀ A₁ A₂ : ℝ} (hr : r ≠ 0) (hrange : d = 8 ∨ 2 < r ^ 2)
    {x : UpperHalfPlane} {ρ : ℝ} (hρ : 0 < ρ)
    (hclean : ∀ (t : ℝ) (ht : 0 < t), t ∈ Work.Asymptotics.straightPartSet t₀ A₁ A₂ →
      ∀ τ : UpperHalfPlane, dist τ x ≤ ρ →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    ∃ bound : ℝ → ℝ, MeasureTheory.IntegrableOn bound (Set.Ioi (0 : ℝ)) ∧
      (∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ bound t) ∧
      ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t), dist τ x ≤ ρ →
        t ∈ Work.Asymptotics.straightPartSet t₀ A₁ A₂ →
          ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ * Real.exp (-(Real.pi * r ^ 2 * t))
            ≤ bound t :=
  MR.exists_bound_straightPart_of_clean ℓ d hd hr hrange hρ hclean

end Work.Asymptotics
