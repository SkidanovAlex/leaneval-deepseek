import Mathlib
import Submission.Commons.Analysis.Complex.contour_shift_residue
import Submission.Commons.Analysis.Integral.gam0_contour_integral_le

namespace Commons.Analysis.Complex

open MeasureTheory
open scoped Topology

noncomputable section

/-- A dominating constant for `(gam β t ^ 2)⁻¹ * gamDot β t`. -/
def curveConst (β : ℝ) : ℝ :=
  2 * (β / (2 * (Real.log 2) ^ 2) + 1) * (1 + 1 / (min (β / Real.log 3) 1) ^ 2)

lemma curveConst_pos {β : ℝ} (hβ : 0 < β) : 0 < curveConst β := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [curveConst]
  refine mul_pos (mul_pos two_pos ?_) ?_
  · have h : 0 < β / (2 * (Real.log 2) ^ 2) := div_pos hβ (mul_pos two_pos (pow_pos hlog2 2))
    linarith
  · have h2 : 0 < min (β / Real.log 3) 1 := lt_min (div_pos hβ hlog3) one_pos
    have : 0 < 1 / (min (β / Real.log 3) 1) ^ 2 := one_div_pos.mpr (pow_pos h2 2)
    linarith

/-- Lower bound for `‖gam β t‖`, uniform in `t`. -/
lemma min_div_log_three_one_le_norm_gam {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    min (β / Real.log 3) 1 ≤ ‖gam β t‖ := by
  by_cases h : |t| ≤ 1
  · have hpos : (0:ℝ) < |t| + 2 := by have := abs_nonneg t; linarith
    have hlt : Real.log (|t| + 2) ≤ Real.log 3 := Real.log_le_log hpos (by linarith)
    have h1lt : (1:ℝ) < |t| + 2 := by have := abs_nonneg t; linarith
    have hphi : β / Real.log 3 ≤ β / Real.log (|t| + 2) :=
      div_le_div_of_nonneg_left hβ.le (Real.log_pos h1lt) hlt
    exact le_trans (min_le_left _ _)
      (le_trans hphi (Commons.Analysis.Integral.gam_norm_ge_phi hβ t))
  · have h1 : 1 < |t| := not_le.mp h
    exact le_trans (min_le_right _ _)
      (le_trans h1.le (Commons.Analysis.Integral.gam_norm_ge_abs β t))

/-- Pointwise bound for the integrand `(gam β t ^ 2)⁻¹ * gamDot β t`. -/
lemma inv_sq_mul_gamDot_norm_le {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    ‖(gam β t ^ 2)⁻¹ * gamDot β t‖ ≤ curveConst β * (1 + t ^ 2)⁻¹ := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hepos : 0 < min (β / Real.log 3) 1 := lt_min (div_pos hβ hlog3) one_pos
  have he2 : 0 < (min (β / Real.log 3) 1) ^ 2 := pow_pos hepos 2
  have hde : 0 < t ^ 2 + (min (β / Real.log 3) 1) ^ 2 := by
    have := sq_nonneg t; linarith
  have hd1 : 0 < 1 + t ^ 2 := by positivity
  have hge_t : t ^ 2 ≤ ‖gam β t‖ ^ 2 := by
    have h := Commons.Analysis.Integral.gam_norm_ge_abs β t
    have h2 := pow_le_pow_left₀ (abs_nonneg t) h 2
    rwa [sq_abs] at h2
  have hge_e : (min (β / Real.log 3) 1) ^ 2 ≤ ‖gam β t‖ ^ 2 :=
    pow_le_pow_left₀ hepos.le (min_div_log_three_one_le_norm_gam hβ t) 2
  have hsum : (t ^ 2 + (min (β / Real.log 3) 1) ^ 2) / 2 ≤ ‖gam β t‖ ^ 2 := by linarith
  have hpos_sum : 0 < (t ^ 2 + (min (β / Real.log 3) 1) ^ 2) / 2 := by positivity
  have hinv : (‖gam β t‖ ^ 2)⁻¹ ≤ 2 / (t ^ 2 + (min (β / Real.log 3) 1) ^ 2) := by
    have h1 := inv_anti₀ hpos_sum hsum
    have h2 : ((t ^ 2 + (min (β / Real.log 3) 1) ^ 2) / 2)⁻¹
        = 2 / (t ^ 2 + (min (β / Real.log 3) 1) ^ 2) := by
      rw [inv_div]
    rwa [h2] at h1
  have hB : ‖gamDot β t‖ ≤ β / (2 * (Real.log 2) ^ 2) + 1 :=
    Commons.Analysis.Integral.gamDot_norm_le hβ t
  have hnn : 0 ≤ 2 / (t ^ 2 + (min (β / Real.log 3) 1) ^ 2) := by positivity
  have hnorm : ‖(gam β t ^ 2)⁻¹ * gamDot β t‖
      = (‖gam β t‖ ^ 2)⁻¹ * ‖gamDot β t‖ := by
    rw [norm_mul, norm_inv, norm_pow]
  have hstep : ‖(gam β t ^ 2)⁻¹ * gamDot β t‖
      ≤ (2 / (t ^ 2 + (min (β / Real.log 3) 1) ^ 2)) * (β / (2 * (Real.log 2) ^ 2) + 1) := by
    rw [hnorm]
    exact mul_le_mul hinv hB (norm_nonneg _) hnn
  refine le_trans hstep ?_
  have hB0pos : 0 < β / (2 * (Real.log 2) ^ 2) + 1 := by
    have : 0 < β / (2 * (Real.log 2) ^ 2) := div_pos hβ (mul_pos two_pos (pow_pos hlog2 2))
    linarith
  have hcore : 1 / (t ^ 2 + (min (β / Real.log 3) 1) ^ 2) ≤ (1 + 1 / (min (β / Real.log 3) 1) ^ 2) / (1 + t ^ 2) := by
    rw [div_le_div_iff₀ hde hd1]
    rw [one_mul]
    have hexp : (1 + 1 / (min (β / Real.log 3) 1) ^ 2) * (t ^ 2 + (min (β / Real.log 3) 1) ^ 2)
        = (1 + t ^ 2) + ((min (β / Real.log 3) 1) ^ 2 + t ^ 2 / (min (β / Real.log 3) 1) ^ 2) := by
      field_simp
      ring
    rw [hexp]
    have : 0 ≤ (min (β / Real.log 3) 1) ^ 2 + t ^ 2 / (min (β / Real.log 3) 1) ^ 2 :=
      add_nonneg (le_of_lt he2) (div_nonneg (sq_nonneg t) (le_of_lt he2))
    linarith
  rw [curveConst]
  calc (2 / (t ^ 2 + (min (β / Real.log 3) 1) ^ 2)) * (β / (2 * (Real.log 2) ^ 2) + 1)
      = (2 * (β / (2 * (Real.log 2) ^ 2) + 1)) * (1 / (t ^ 2 + (min (β / Real.log 3) 1) ^ 2)) := by
        ring
    _ ≤ (2 * (β / (2 * (Real.log 2) ^ 2) + 1))
          * ((1 + 1 / (min (β / Real.log 3) 1) ^ 2) / (1 + t ^ 2)) :=
        mul_le_mul_of_nonneg_left hcore (by positivity)
    _ = 2 * (β / (2 * (Real.log 2) ^ 2) + 1) * (1 + 1 / (min (β / Real.log 3) 1) ^ 2)
          * (1 + t ^ 2)⁻¹ := by
        rw [div_eq_mul_inv]; ring

/-- The core integrability result, stated with `gam`/`gamDot`. -/
lemma gam_inv_sq_mul_deriv_integrable {β : ℝ} (hβ : 0 < β) :
    Integrable (fun t : ℝ => (gam β t ^ 2)⁻¹ * deriv (gam β) t) volume := by
  have hcont : Continuous (fun t : ℝ => (gam β t ^ 2)⁻¹) :=
    ((gam_continuous β).pow 2).inv₀ (fun t => pow_ne_zero 2 (gam_ne_zero hβ t))
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (gam β t ^ 2)⁻¹ * deriv (gam β) t) volume :=
    AEStronglyMeasurable.mul hcont.aestronglyMeasurable (aestronglyMeasurable_deriv (gam β) volume)
  have hdom : Integrable (fun t : ℝ => curveConst β * (1 + t ^ 2)⁻¹) volume :=
    integrable_inv_one_add_sq.const_mul (curveConst β)
  have hbound : ∀ᵐ t ∂volume,
      ‖(gam β t ^ 2)⁻¹ * deriv (gam β) t‖ ≤ curveConst β * (1 + t ^ 2)⁻¹ := by
    filter_upwards [ae_ne_zero] with t ht
    rw [(hasDerivAt_gam (β := β) ht).deriv]
    exact inv_sq_mul_gamDot_norm_le hβ t
  exact Integrable.mono' hdom hmeas hbound

theorem curve_inv_sq_integrable {β : ℝ} (hβ : 0 < β) :
    MeasureTheory.Integrable (fun t : ℝ =>
      (((( -(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ 2)⁻¹
        * deriv (fun s : ℝ => ((( -(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t) := by
  change Integrable (fun t : ℝ => (gam β t ^ 2)⁻¹ * deriv (gam β) t) volume
  exact gam_inv_sq_mul_deriv_integrable hβ

end

end Commons.Analysis.Complex
