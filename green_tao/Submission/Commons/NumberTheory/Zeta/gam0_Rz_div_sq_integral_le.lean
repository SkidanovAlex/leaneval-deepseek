import Mathlib
import Submission.Commons.Analysis.Complex.contour_shift_residue
import Submission.Commons.Analysis.Complex.curve_inv_sq_integrable
import Submission.Commons.Analysis.Complex.norm_cpow_gam_eq

namespace Commons.NumberTheory.Zeta

open MeasureTheory
open scoped Topology

/-- `gam β 0` lies in the standard region (used to derive `0 ≤ B`). -/
lemma gam_zero_mem_region {β : ℝ} (hβ : 0 < β) :
    -(β / Real.log (|(Commons.Analysis.Complex.gam β 0).im| + 2))
        ≤ (Commons.Analysis.Complex.gam β 0).re
      ∧ (Commons.Analysis.Complex.gam β 0).re ≤ 1 := by
  constructor
  · rw [Commons.Analysis.Complex.gam_im, Commons.Analysis.Complex.gam_re]
  · rw [Commons.Analysis.Complex.gam_re]
    have h := Commons.Analysis.Complex.phi_neg hβ 0
    have h2 : -(β / Real.log (|(0:ℝ)| + 2)) < 0 := by
      simpa [Commons.Analysis.Complex.phi] using h
    linarith

/-- Every point of the curve `gam β` lies in the region where `F` is bounded by `B`. -/
lemma gam_mem_region {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    -(β / Real.log (|(Commons.Analysis.Complex.gam β t).im| + 2))
        ≤ (Commons.Analysis.Complex.gam β t).re
      ∧ (Commons.Analysis.Complex.gam β t).re ≤ 1 := by
  constructor
  · rw [Commons.Analysis.Complex.gam_im, Commons.Analysis.Complex.gam_re]
  · rw [Commons.Analysis.Complex.gam_re]
    have h := Commons.Analysis.Complex.phi_lt_c hβ zero_lt_one t
    have h2 : -(β / Real.log (|t| + 2)) < 1 := by
      simpa [Commons.Analysis.Complex.phi] using h
    linarith

/-- On the curve, `‖(R : ℂ) ^ (gam β t)‖ ≤ 1` for `R ≥ 1`. -/
lemma norm_cpow_gam_le_one {β R : ℝ} (hβ : 0 < β) (hR : 1 ≤ R) (t : ℝ) :
    ‖(R : ℂ) ^ (Commons.Analysis.Complex.gam β t)‖ ≤ 1 := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  rw [Commons.Analysis.Complex.norm_cpow_gam_eq hRpos t, Real.exp_le_one_iff]
  refine div_nonpos_of_nonpos_of_nonneg ?_ ?_
  · exact neg_nonpos.mpr (mul_nonneg hβ.le (Real.log_nonneg hR))
  · exact (Real.log_pos (by have := abs_nonneg t; linarith)).le

/-- Splitting the norm of the integrand into a product of norms. -/
lemma norm_div_sq_mul (F : ℂ → ℂ) (R : ℝ) (β t : ℝ) :
    ‖F (Commons.Analysis.Complex.gam β t) * (R : ℂ) ^ (Commons.Analysis.Complex.gam β t)
        / (Commons.Analysis.Complex.gam β t) ^ 2 * Commons.Analysis.Complex.gamDot β t‖
      = ‖F (Commons.Analysis.Complex.gam β t)‖
        * ‖(R : ℂ) ^ (Commons.Analysis.Complex.gam β t)‖
        * ‖((Commons.Analysis.Complex.gam β t) ^ 2)⁻¹ * Commons.Analysis.Complex.gamDot β t‖ := by
  simp only [div_eq_mul_inv, norm_mul, norm_inv, norm_pow]
  ring

/-- Pointwise bound for the integrand. -/
lemma norm_integrand_le {β R B : ℝ} (hβ : 0 < β) (hR : 1 ≤ R) (hB0 : 0 ≤ B)
    (F : ℂ → ℂ)
    (hb : ∀ z : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 → ‖F z‖ ≤ B)
    (t : ℝ) :
    ‖F (Commons.Analysis.Complex.gam β t) * (R : ℂ) ^ (Commons.Analysis.Complex.gam β t)
        / (Commons.Analysis.Complex.gam β t) ^ 2 * Commons.Analysis.Complex.gamDot β t‖
      ≤ B * (Commons.Analysis.Complex.curveConst β * (1 + t ^ 2)⁻¹) := by
  have hF : ‖F (Commons.Analysis.Complex.gam β t)‖ ≤ B :=
    hb _ (gam_mem_region hβ t).1 (gam_mem_region hβ t).2
  have hpow : ‖(R : ℂ) ^ (Commons.Analysis.Complex.gam β t)‖ ≤ 1 :=
    norm_cpow_gam_le_one hβ hR t
  have hdot := Commons.Analysis.Complex.inv_sq_mul_gamDot_norm_le hβ t
  rw [norm_div_sq_mul]
  calc ‖F (Commons.Analysis.Complex.gam β t)‖
        * ‖(R : ℂ) ^ (Commons.Analysis.Complex.gam β t)‖
        * ‖((Commons.Analysis.Complex.gam β t) ^ 2)⁻¹ * Commons.Analysis.Complex.gamDot β t‖
      ≤ B * 1 * (Commons.Analysis.Complex.curveConst β * (1 + t ^ 2)⁻¹) :=
        mul_le_mul (mul_le_mul hF hpow (norm_nonneg _) hB0) hdot (norm_nonneg _)
          (by positivity)
    _ = B * (Commons.Analysis.Complex.curveConst β * (1 + t ^ 2)⁻¹) := by ring

theorem gam0_Rz_div_sq_integral_le {β : ℝ} (hβ : 0 < β) (F : ℂ → ℂ) (B : ℝ)
    (hb : ∀ z : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 → ‖F z‖ ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
      ‖∫ t : ℝ, F (Commons.Analysis.Complex.gam β t) * (R : ℂ) ^ (Commons.Analysis.Complex.gam β t)
          / (Commons.Analysis.Complex.gam β t) ^ 2 * Commons.Analysis.Complex.gamDot β t‖ ≤ C * B := by
  have hB0 : 0 ≤ B :=
    le_trans (norm_nonneg _) (hb _ (gam_zero_mem_region hβ).1 (gam_zero_mem_region hβ).2)
  refine ⟨max 1 (Commons.Analysis.Complex.curveConst β * ∫ t : ℝ, (1 + t ^ 2)⁻¹),
    lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro R hR
  have hg : Integrable (fun t : ℝ => B * (Commons.Analysis.Complex.curveConst β * (1 + t ^ 2)⁻¹))
      volume := by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      (integrable_inv_one_add_sq.const_mul (Commons.Analysis.Complex.curveConst β)).const_mul B
  have hbd : ∀ᵐ t ∂volume,
      ‖F (Commons.Analysis.Complex.gam β t) * (R : ℂ) ^ (Commons.Analysis.Complex.gam β t)
          / (Commons.Analysis.Complex.gam β t) ^ 2 * Commons.Analysis.Complex.gamDot β t‖
        ≤ B * (Commons.Analysis.Complex.curveConst β * (1 + t ^ 2)⁻¹) :=
    Filter.Eventually.of_forall (norm_integrand_le hβ hR hB0 F hb)
  have h := MeasureTheory.norm_integral_le_of_norm_le hg hbd
  have hInt : (∫ t : ℝ, B * (Commons.Analysis.Complex.curveConst β * (1 + t ^ 2)⁻¹))
      = B * (Commons.Analysis.Complex.curveConst β * ∫ t : ℝ, (1 + t ^ 2)⁻¹) := by
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [hInt] at h
  calc ‖∫ t : ℝ, F (Commons.Analysis.Complex.gam β t) * (R : ℂ) ^ (Commons.Analysis.Complex.gam β t)
        / (Commons.Analysis.Complex.gam β t) ^ 2 * Commons.Analysis.Complex.gamDot β t‖
      ≤ B * (Commons.Analysis.Complex.curveConst β * ∫ t : ℝ, (1 + t ^ 2)⁻¹) := h
    _ = (Commons.Analysis.Complex.curveConst β * ∫ t : ℝ, (1 + t ^ 2)⁻¹) * B := by ring
    _ ≤ max 1 (Commons.Analysis.Complex.curveConst β * ∫ t : ℝ, (1 + t ^ 2)⁻¹) * B :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hB0

end Commons.NumberTheory.Zeta
