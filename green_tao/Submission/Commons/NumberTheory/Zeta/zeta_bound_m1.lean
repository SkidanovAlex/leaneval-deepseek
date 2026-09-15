import Mathlib
import Submission.Commons.Analysis.Complex.contour_shift_residue
import Submission.Commons.Analysis.Complex.contour_shift_residue_multi
import Submission.Commons.Analysis.Complex.curve_inv_sq_integrable
import Submission.Commons.Analysis.Integral.uScaleHalf_integrable
import Submission.Commons.NumberTheory.Zeta.zeta_region_inv_analytic_bound_ne
import Submission.Commons.NumberTheory.Zeta.norm_riemannZeta_le_const_of_one_lt_re
import Submission.Commons.NumberTheory.Zeta.gam0_Rz_div_sq_integral_le
import Submission.Commons.NumberTheory.Zeta.gam0_zeta_quartic_integral_le
import Submission.Commons.NumberTheory.Zeta.gam0_zeta_quartic_integrable
import Submission.Commons.NumberTheory.Zeta.greenTao_shift_Gamma1_to_Gamma2
import Submission.Commons.NumberTheory.Zeta.greenTao_single_pole_shift_Gamma2
import Submission.Commons.NumberTheory.Zeta.greenTao_Gamma2_double_pole
import Submission.Commons.NumberTheory.Zeta.greenTao_two_pole_shift_v4
import Submission.Commons.NumberTheory.Zeta.zeta_one_add_add_bound_curve_sqrt_curve
import Submission.Commons.NumberTheory.Zeta.greenTao_kernel_integrable_eta_sigma_cont
import Submission.Commons.NumberTheory.Zeta.greenTao_kernel_integrable_gam_sigma_cont
import Submission.Commons.NumberTheory.Zeta.greenTao_kernel_integrable_gam_gam_cont

/-!
# Green–Tao Appendix Lemma A.3 (the `m = 1` case of Lemma 10.4)
-/
set_option maxHeartbeats 16000000

open Complex MeasureTheory intervalIntegral Filter Set
open scoped Topology Interval

namespace Commons.NumberTheory.Zeta

open MeasureTheory

noncomputable section

/-- The Green-Tao integrand `f z w · ζ(1+z+w)/(ζ(1+z)ζ(1+w)) · R^{z+w}/(z²w²)`. -/
def zetaM1Kernel (R : ℝ) (f : ℂ → ℂ → ℂ) (z z' : ℂ) : ℂ :=
  f z z' * (riemannZeta (1 + z + z') / (riemannZeta (1 + z) * riemannZeta (1 + z'))) *
    (R : ℂ) ^ (z + z') / (z ^ 2 * z' ^ 2)

/-- The vertical line `Γ₁ = {Re = 1/log R}`. -/
def zetaM1Eta (R : ℝ) (t : ℝ) : ℂ := ((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I

/-- The vertical line `Γ₂ = {Re = 1}`. -/
def zetaM1Sigma (t : ℝ) : ℂ := (1 : ℂ) + (t : ℂ) * Complex.I

@[simp] lemma zetaM1Eta_re (R : ℝ) (t : ℝ) : (zetaM1Eta R t).re = 1 / Real.log R := by
  simp [zetaM1Eta]
@[simp] lemma zetaM1Eta_im (R : ℝ) (t : ℝ) : (zetaM1Eta R t).im = t := by
  simp [zetaM1Eta]
@[simp] lemma zetaM1Sigma_re (t : ℝ) : (zetaM1Sigma t).re = 1 := by
  simp [zetaM1Sigma]
@[simp] lemma zetaM1Sigma_im (t : ℝ) : (zetaM1Sigma t).im = t := by
  simp [zetaM1Sigma]

lemma zetaM1Eta_continuous (R : ℝ) : Continuous (zetaM1Eta R) := by
  unfold zetaM1Eta; fun_prop
lemma zetaM1Sigma_continuous : Continuous (zetaM1Sigma) := by
  unfold zetaM1Sigma; fun_prop

/-! ## Elementary numeric facts -/

lemma log_three_pos : (0:ℝ) < Real.log 3 := Real.log_pos (by norm_num)

lemma one_div_log_le_one {R : ℝ} (hR : 3 ≤ R) : 1 / Real.log R ≤ 1 := by
  have h3 : (1:ℝ) < Real.log 3 := by
    rw [← Real.log_exp 1]; exact Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
  have hl : Real.log 3 ≤ Real.log R := Real.log_le_log (by norm_num) hR
  have hpos : 0 < Real.log R := Real.log_pos (by linarith)
  rw [div_le_one hpos]; linarith

lemma one_div_log_pos {R : ℝ} (hR : 3 ≤ R) : 0 < 1 / Real.log R := by
  have : 0 < Real.log R := Real.log_pos (by linarith)
  positivity

lemma rpow_neg_beta_div_log_le_one {R : ℝ} (hR : 1 ≤ R) {c : ℝ} (hc : c ≤ 0) :
    R ^ c ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hR hc

lemma norm_pi_complex : ‖(Real.pi : ℂ)‖ = Real.pi := by
  have hsq : ‖(Real.pi : ℂ)‖ ^ 2 = Real.pi ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
  nlinarith [norm_nonneg (Real.pi : ℂ), Real.pi_pos]

lemma norm_two_pi_complex : ‖(2 : ℂ) * (Real.pi : ℂ)‖ = 2 * Real.pi := by
  rw [norm_mul, Complex.norm_ofNat, norm_pi_complex]

/-- The dominating weight `(|t|+3)^{1/2}(log(|t|+2)+1)/(1+t^2)` for the `Γ₀ × Γ₀` estimate. -/
def uScale (t : ℝ) : ℝ := (|t| + 3) ^ ((1:ℝ)/2) * (Real.log (|t| + 2) + 1) / (1 + t ^ 2)

lemma uScale_eq (t : ℝ) :
    uScale t = (|t| + 3) ^ ((1:ℝ)/2) * (Real.log (|t| + 2) + 1) / (1 + t ^ 2) := rfl

lemma uScale_nonneg (t : ℝ) : 0 ≤ uScale t := by
  rw [uScale_eq]
  have h1 : (0:ℝ) ≤ (|t| + 3) ^ ((1:ℝ)/2) := Real.rpow_nonneg (by linarith [abs_nonneg t]) _
  have h2 : (0:ℝ) ≤ Real.log (|t| + 2) + 1 := by
    have := Real.log_nonneg (show (1:ℝ) ≤ |t| + 2 by linarith [abs_nonneg t]); linarith
  exact div_nonneg (mul_nonneg h1 h2) (by positivity)

/-! ## The kernel as a product, and its pointwise bound -/

lemma zetaM1Kernel_eq (R : ℝ) (f : ℂ → ℂ → ℂ) (z z' : ℂ) :
    zetaM1Kernel R f z z' = f z z'
      * (riemannZeta (1 + z + z') * (riemannZeta (1 + z))⁻¹ * (riemannZeta (1 + z'))⁻¹)
      * (R : ℂ) ^ (z + z') * (z ^ 2)⁻¹ * (z' ^ 2)⁻¹ := by
  unfold zetaM1Kernel
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

/-- Pointwise norm bound for the kernel, in factored form. -/
lemma norm_zetaM1Kernel_le {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ → ℂ} {B C₂ : ℝ}
    (hB : 0 ≤ B) (hC2 : 0 ≤ C₂) {z z' : ℂ}
    (hf : ‖f z z'‖ ≤ B) (hnum : ‖riemannZeta (1 + z + z')‖ ≤ C₂) :
    ‖zetaM1Kernel R f z z'‖
      ≤ B * C₂ * ‖(riemannZeta (1 + z))⁻¹‖ * ‖(riemannZeta (1 + z'))⁻¹‖
        * ‖(R : ℂ) ^ (z + z')‖ * ‖(z ^ 2)⁻¹‖ * ‖(z' ^ 2)⁻¹‖ := by
  rw [zetaM1Kernel_eq, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul]
  have hstep1 : ‖riemannZeta (1 + z + z')‖ * ‖(riemannZeta (1 + z))⁻¹‖
      ≤ C₂ * ‖(riemannZeta (1 + z))⁻¹‖ :=
    mul_le_mul_of_nonneg_right hnum (by positivity)
  have hstep2 : ‖riemannZeta (1 + z + z')‖ * ‖(riemannZeta (1 + z))⁻¹‖
        * ‖(riemannZeta (1 + z'))⁻¹‖
      ≤ C₂ * ‖(riemannZeta (1 + z))⁻¹‖ * ‖(riemannZeta (1 + z'))⁻¹‖ :=
    mul_le_mul_of_nonneg_right hstep1 (by positivity)
  have hstep : ‖f z z'‖ * (‖riemannZeta (1 + z + z')‖ * ‖(riemannZeta (1 + z))⁻¹‖
        * ‖(riemannZeta (1 + z'))⁻¹‖)
      ≤ B * (C₂ * ‖(riemannZeta (1 + z))⁻¹‖ * ‖(riemannZeta (1 + z'))⁻¹‖) :=
    mul_le_mul hf hstep2 (by positivity) hB
  calc ‖f z z'‖ * (‖riemannZeta (1 + z + z')‖ * ‖(riemannZeta (1 + z))⁻¹‖
          * ‖(riemannZeta (1 + z'))⁻¹‖) * ‖(R : ℂ) ^ (z + z')‖ * ‖(z ^ 2)⁻¹‖ * ‖(z' ^ 2)⁻¹‖
      ≤ B * (C₂ * ‖(riemannZeta (1 + z))⁻¹‖ * ‖(riemannZeta (1 + z'))⁻¹‖)
          * ‖(R : ℂ) ^ (z + z')‖ * ‖(z ^ 2)⁻¹‖ * ‖(z' ^ 2)⁻¹‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hstep (by positivity))
            (by positivity)) (by positivity)
    _ = B * C₂ * ‖(riemannZeta (1 + z))⁻¹‖ * ‖(riemannZeta (1 + z'))⁻¹‖
        * ‖(R : ℂ) ^ (z + z')‖ * ‖(z ^ 2)⁻¹‖ * ‖(z' ^ 2)⁻¹‖ := by ring

lemma norm_cpow_eq_of_pos {R : ℝ} (hR : 0 < R) (z : ℂ) :
    ‖(R : ℂ) ^ z‖ = R ^ z.re := Complex.norm_cpow_eq_rpow_re_of_pos hR z

/-! ## Norms of the quadratic denominators -/

lemma normSq_zetaM1Eta (R : ℝ) (t : ℝ) :
    ‖zetaM1Eta R t‖ ^ 2 = (1 / Real.log R) ^ 2 + t ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [zetaM1Eta]
  ring

lemma normSq_zetaM1Sigma (t : ℝ) : ‖zetaM1Sigma t‖ ^ 2 = 1 + t ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [zetaM1Sigma]
  ring

lemma norm_inv_sq_zetaM1Eta {R : ℝ} (hR : 3 ≤ R) (t : ℝ) :
    ‖(zetaM1Eta R t ^ 2)⁻¹‖ ≤ (Real.log R) ^ 2 * (1 + t ^ 2)⁻¹ := by
  have hL : 1 < Real.log R := by
    have h3 : (1:ℝ) < Real.log 3 := by
      rw [← Real.log_exp 1]; exact Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
    exact lt_of_lt_of_le h3 (Real.log_le_log (by norm_num) hR)
  have hLpos : 0 < Real.log R := by linarith
  have hLs : (1 / Real.log R) ^ 2 + t ^ 2
      = (1 + (Real.log R) ^ 2 * t ^ 2) / (Real.log R) ^ 2 := by
    field_simp
  have hmono : 1 + t ^ 2 ≤ 1 + (Real.log R) ^ 2 * t ^ 2 := by
    have hL2 : (1:ℝ) ≤ (Real.log R) ^ 2 := by nlinarith [hL]
    have := mul_le_mul_of_nonneg_left hL2 (sq_nonneg t)
    linarith
  rw [norm_inv, norm_pow, normSq_zetaM1Eta, hLs, inv_div]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hmono

lemma norm_inv_sq_zetaM1Sigma (t : ℝ) :
    ‖(zetaM1Sigma t ^ 2)⁻¹‖ = (1 + t ^ 2)⁻¹ := by
  rw [norm_inv, norm_pow, normSq_zetaM1Sigma]

/-- A constant dominating `‖(gam β t ^ 2)⁻¹‖`. -/
def gamInvSqConst (β : ℝ) : ℝ := 2 * (1 + 1 / (min (β / Real.log 3) 1) ^ 2)

lemma gamInvSqConst_pos {β : ℝ} (hβ : 0 < β) : 0 < gamInvSqConst β := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h : 0 < min (β / Real.log 3) 1 := lt_min (div_pos hβ h3) one_pos
  unfold gamInvSqConst
  positivity

lemma norm_inv_sq_gam_le {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    ‖(Commons.Analysis.Complex.gam β t ^ 2)⁻¹‖ ≤ gamInvSqConst β * (1 + t ^ 2)⁻¹ := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hepos : 0 < min (β / Real.log 3) 1 := lt_min (div_pos hβ h3) one_pos
  have hinv : (‖Commons.Analysis.Complex.gam β t‖ ^ 2)⁻¹
      ≤ 2 / (t ^ 2 + (min (β / Real.log 3) 1) ^ 2) := by
    have hge_t : t ^ 2 ≤ ‖Commons.Analysis.Complex.gam β t‖ ^ 2 := by
      have h := Commons.Analysis.Integral.gam_norm_ge_abs β t
      have h2 := pow_le_pow_left₀ (abs_nonneg t) h 2
      rwa [sq_abs] at h2
    have hge_e : (min (β / Real.log 3) 1) ^ 2 ≤ ‖Commons.Analysis.Complex.gam β t‖ ^ 2 :=
      pow_le_pow_left₀ hepos.le
        (Commons.Analysis.Complex.min_div_log_three_one_le_norm_gam hβ t) 2
    have hsum : (t ^ 2 + (min (β / Real.log 3) 1) ^ 2) / 2 ≤ ‖Commons.Analysis.Complex.gam β t‖ ^ 2 := by
      linarith
    have hpos_sum : 0 < (t ^ 2 + (min (β / Real.log 3) 1) ^ 2) / 2 := by positivity
    have h1 := inv_anti₀ hpos_sum hsum
    have h2 : ((t ^ 2 + (min (β / Real.log 3) 1) ^ 2) / 2)⁻¹
        = 2 / (t ^ 2 + (min (β / Real.log 3) 1) ^ 2) := by rw [inv_div]
    rwa [h2] at h1
  rw [norm_inv, norm_pow]
  refine le_trans hinv ?_
  have hde : 0 < t ^ 2 + (min (β / Real.log 3) 1) ^ 2 := by positivity
  have hd1 : 0 < 1 + t ^ 2 := by positivity
  have hcore : 1 / (t ^ 2 + (min (β / Real.log 3) 1) ^ 2)
      ≤ (1 + 1 / (min (β / Real.log 3) 1) ^ 2) / (1 + t ^ 2) := by
    rw [div_le_div_iff₀ hde hd1, one_mul]
    have he2 : 0 < (min (β / Real.log 3) 1) ^ 2 := pow_pos hepos 2
    have hexp : (1 + 1 / (min (β / Real.log 3) 1) ^ 2) * (t ^ 2 + (min (β / Real.log 3) 1) ^ 2)
        = (1 + t ^ 2) + ((min (β / Real.log 3) 1) ^ 2 + t ^ 2 / (min (β / Real.log 3) 1) ^ 2) := by
      field_simp
      ring
    rw [hexp]
    have : 0 ≤ (min (β / Real.log 3) 1) ^ 2 + t ^ 2 / (min (β / Real.log 3) 1) ^ 2 :=
      add_nonneg (le_of_lt he2) (div_nonneg (sq_nonneg t) (le_of_lt he2))
    linarith
  calc 2 / (t ^ 2 + (min (β / Real.log 3) 1) ^ 2)
      = 2 * (1 / (t ^ 2 + (min (β / Real.log 3) 1) ^ 2)) := by ring
    _ ≤ 2 * ((1 + 1 / (min (β / Real.log 3) 1) ^ 2) / (1 + t ^ 2)) :=
        mul_le_mul_of_nonneg_left hcore (by norm_num)
    _ = gamInvSqConst β * (1 + t ^ 2)⁻¹ := by
        rw [gamInvSqConst, div_eq_mul_inv]; ring

end


/-- Constant dominating `‖gamDot β t‖` (from `Commons.Analysis.Integral.gamDot_norm_le`). -/
noncomputable def gamDotConst (β : ℝ) : ℝ := β / (2 * (Real.log 2) ^ 2) + 1

/-- Pointwise bound for the `Γ₀ × Γ₀` Green-Tao integrand. -/
lemma gamma_gamma_pointwise {β R : ℝ} (hβ : 0 < β) (hR : 1 ≤ R) (f : ℂ → ℂ → ℂ)
    (B C₁ Cn : ℝ) (hB : 0 ≤ B) (hC1 : 0 < C₁) (hCn : 0 < Cn)
    (hinvb : ∀ z : ℂ, z ≠ 0 → -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2) + 1))
    (hbound : ∀ z z' : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
        -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 → ‖f z z'‖ ≤ B)
    (hnum : ∀ t t' : ℝ, ‖riemannZeta (1 + Commons.Analysis.Complex.gam β t
        + Commons.Analysis.Complex.gam β t')‖ ≤ Cn * (|t| + |t'| + 3) ^ ((1:ℝ)/2))
    (t t' : ℝ) :
    ‖zetaM1Kernel R f (Commons.Analysis.Complex.gam β t) (Commons.Analysis.Complex.gam β t')
        * Commons.Analysis.Complex.gamDot β t'‖
      * ‖Commons.Analysis.Complex.gamDot β t‖
      ≤ (B * Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β ^ 2)
        * (uScale t * uScale t') := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hgam_re : ∀ s : ℝ, (Commons.Analysis.Complex.gam β s).re
      = -(β / Real.log (|s| + 2)) := fun s => by
    simp [Commons.Analysis.Complex.gam, Commons.Analysis.Complex.phi]
  have hgam_im : ∀ s : ℝ, (Commons.Analysis.Complex.gam β s).im = s := fun s => by
    simp [Commons.Analysis.Complex.gam]
  have hreg : ∀ s : ℝ, -(β / Real.log (|(Commons.Analysis.Complex.gam β s).im| + 2))
      ≤ (Commons.Analysis.Complex.gam β s).re := fun s => by rw [hgam_re, hgam_im]
  have hle : ∀ s : ℝ, (Commons.Analysis.Complex.gam β s).re ≤ 1 := by
    intro s
    rw [hgam_re]
    have hpos : 0 < Real.log (|s| + 2) := Real.log_pos (by linarith [abs_nonneg s])
    have h2 : 0 ≤ β / Real.log (|s| + 2) := div_nonneg hβ.le hpos.le
    linarith
  have hb : ‖f (Commons.Analysis.Complex.gam β t) (Commons.Analysis.Complex.gam β t')‖ ≤ B :=
    hbound _ _ (hreg t) (hle t) (hreg t') (hle t')
  have hnum' := hnum t t'
  have hzt : ‖(riemannZeta (1 + Commons.Analysis.Complex.gam β t))⁻¹‖
      ≤ C₁ * (Real.log (|t| + 2) + 1) := by
    have h := hinvb _ (Commons.Analysis.Complex.gam_ne_zero hβ t) (hreg t) (hle t)
    rwa [hgam_im] at h
  have hzt' : ‖(riemannZeta (1 + Commons.Analysis.Complex.gam β t'))⁻¹‖
      ≤ C₁ * (Real.log (|t'| + 2) + 1) := by
    have h := hinvb _ (Commons.Analysis.Complex.gam_ne_zero hβ t') (hreg t') (hle t')
    rwa [hgam_im] at h
  have hRt : ‖(R : ℂ) ^ (Commons.Analysis.Complex.gam β t
      + Commons.Analysis.Complex.gam β t')‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hRpos, Complex.add_re, hgam_re, hgam_re]
    refine Real.rpow_le_one_of_one_le_of_nonpos hR (by
      have h1 : 0 ≤ β / Real.log (|t| + 2) := div_nonneg hβ.le
        (Real.log_nonneg (by linarith [abs_nonneg t]))
      have h2 : 0 ≤ β / Real.log (|t'| + 2) := div_nonneg hβ.le
        (Real.log_nonneg (by linarith [abs_nonneg t']))
      linarith)
  have hmu : ‖(Commons.Analysis.Complex.gam β t ^ 2)⁻¹‖
      * ‖Commons.Analysis.Complex.gamDot β t‖
      ≤ Commons.Analysis.Complex.curveConst β * (1 + t ^ 2)⁻¹ := by
    rw [← norm_mul]
    exact Commons.Analysis.Complex.inv_sq_mul_gamDot_norm_le hβ t
  have hmu' : ‖(Commons.Analysis.Complex.gam β t' ^ 2)⁻¹‖
      * ‖Commons.Analysis.Complex.gamDot β t'‖
      ≤ Commons.Analysis.Complex.curveConst β * (1 + t' ^ 2)⁻¹ := by
    rw [← norm_mul]
    exact Commons.Analysis.Complex.inv_sq_mul_gamDot_norm_le hβ t'
  have hK := norm_zetaM1Kernel_le (R := R) hRpos (f := f) (B := B)
    (C₂ := Cn * (|t| + |t'| + 3) ^ ((1:ℝ)/2)) hB (by positivity) hb hnum'
  have hbroot : (|t| + |t'| + 3) ^ ((1:ℝ)/2)
      ≤ (|t| + 3) ^ ((1:ℝ)/2) * (|t'| + 3) ^ ((1:ℝ)/2) := by
    have h1 : (|t| + |t'| + 3) ≤ (|t| + 3) * (|t'| + 3) := by
      nlinarith [abs_nonneg t, abs_nonneg t']
    calc (|t| + |t'| + 3) ^ ((1:ℝ)/2)
        ≤ ((|t| + 3) * (|t'| + 3)) ^ ((1:ℝ)/2) :=
          Real.rpow_le_rpow (by positivity) h1 (by norm_num)
      _ = (|t| + 3) ^ ((1:ℝ)/2) * (|t'| + 3) ^ ((1:ℝ)/2) :=
          Real.mul_rpow (by linarith [abs_nonneg t]) (by linarith [abs_nonneg t'])
  have huS : uScale t * uScale t'
      = (|t| + 3) ^ ((1:ℝ)/2) * (|t'| + 3) ^ ((1:ℝ)/2)
        * ((Real.log (|t| + 2) + 1) * (Real.log (|t'| + 2) + 1) * ((1 + t ^ 2)⁻¹ * (1 + t' ^ 2)⁻¹)) := by
    rw [uScale_eq, uScale_eq]; ring
  have hLt : 0 ≤ Real.log (|t| + 2) + 1 := by
    have := Real.log_nonneg (show (1:ℝ) ≤ |t| + 2 by linarith [abs_nonneg t]); linarith
  have hLt' : 0 ≤ Real.log (|t'| + 2) + 1 := by
    have := Real.log_nonneg (show (1:ℝ) ≤ |t'| + 2 by linarith [abs_nonneg t']); linarith
  have hAt : 0 ≤ (1 + t ^ 2)⁻¹ := by positivity
  have hAt' : 0 ≤ (1 + t' ^ 2)⁻¹ := by positivity
  have hcc : 0 ≤ Commons.Analysis.Complex.curveConst β := (Commons.Analysis.Complex.curveConst_pos hβ).le
  have hK2 : ‖zetaM1Kernel R f (Commons.Analysis.Complex.gam β t)
        (Commons.Analysis.Complex.gam β t')‖
      ≤ B * (Cn * (|t| + |t'| + 3) ^ ((1:ℝ)/2))
        * ‖(riemannZeta (1 + Commons.Analysis.Complex.gam β t))⁻¹‖
        * ‖(riemannZeta (1 + Commons.Analysis.Complex.gam β t'))⁻¹‖ * 1
        * ‖(Commons.Analysis.Complex.gam β t ^ 2)⁻¹‖
        * ‖(Commons.Analysis.Complex.gam β t' ^ 2)⁻¹‖ := by
    refine le_trans hK ?_
    rw [show B * (Cn * (|t| + |t'| + 3) ^ ((1:ℝ)/2))
          * ‖(riemannZeta (1 + Commons.Analysis.Complex.gam β t))⁻¹‖
          * ‖(riemannZeta (1 + Commons.Analysis.Complex.gam β t'))⁻¹‖
          * ‖(R : ℂ) ^ (Commons.Analysis.Complex.gam β t + Commons.Analysis.Complex.gam β t')‖
          * ‖(Commons.Analysis.Complex.gam β t ^ 2)⁻¹‖
          * ‖(Commons.Analysis.Complex.gam β t' ^ 2)⁻¹‖
        = (B * (Cn * (|t| + |t'| + 3) ^ ((1:ℝ)/2))
            * ‖(riemannZeta (1 + Commons.Analysis.Complex.gam β t))⁻¹‖
            * ‖(riemannZeta (1 + Commons.Analysis.Complex.gam β t'))⁻¹‖)
          * ‖(R : ℂ) ^ (Commons.Analysis.Complex.gam β t + Commons.Analysis.Complex.gam β t')‖
          * (‖(Commons.Analysis.Complex.gam β t ^ 2)⁻¹‖
            * ‖(Commons.Analysis.Complex.gam β t' ^ 2)⁻¹‖) by ring,
        show B * (Cn * (|t| + |t'| + 3) ^ ((1:ℝ)/2))
          * ‖(riemannZeta (1 + Commons.Analysis.Complex.gam β t))⁻¹‖
          * ‖(riemannZeta (1 + Commons.Analysis.Complex.gam β t'))⁻¹‖ * 1
          * ‖(Commons.Analysis.Complex.gam β t ^ 2)⁻¹‖
          * ‖(Commons.Analysis.Complex.gam β t' ^ 2)⁻¹‖
        = (B * (Cn * (|t| + |t'| + 3) ^ ((1:ℝ)/2))
            * ‖(riemannZeta (1 + Commons.Analysis.Complex.gam β t))⁻¹‖
            * ‖(riemannZeta (1 + Commons.Analysis.Complex.gam β t'))⁻¹‖)
          * 1
          * (‖(Commons.Analysis.Complex.gam β t ^ 2)⁻¹‖
            * ‖(Commons.Analysis.Complex.gam β t' ^ 2)⁻¹‖) by ring]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRt (by positivity)) (by positivity)
  rw [norm_mul]
  refine le_trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hK2 (norm_nonneg _)) (norm_nonneg _)) ?_
  rw [show (B * (Cn * (|t| + |t'| + 3) ^ ((1:ℝ)/2))
        * ‖(riemannZeta (1 + Commons.Analysis.Complex.gam β t))⁻¹‖
        * ‖(riemannZeta (1 + Commons.Analysis.Complex.gam β t'))⁻¹‖ * 1
        * ‖(Commons.Analysis.Complex.gam β t ^ 2)⁻¹‖
        * ‖(Commons.Analysis.Complex.gam β t' ^ 2)⁻¹‖)
        * ‖Commons.Analysis.Complex.gamDot β t'‖ * ‖Commons.Analysis.Complex.gamDot β t‖
      = (B * (Cn * (|t| + |t'| + 3) ^ ((1:ℝ)/2))
          * ‖(riemannZeta (1 + Commons.Analysis.Complex.gam β t))⁻¹‖
          * ‖(riemannZeta (1 + Commons.Analysis.Complex.gam β t'))⁻¹‖ * 1)
        * ((‖(Commons.Analysis.Complex.gam β t ^ 2)⁻¹‖
              * ‖Commons.Analysis.Complex.gamDot β t‖)
            * (‖(Commons.Analysis.Complex.gam β t' ^ 2)⁻¹‖
              * ‖Commons.Analysis.Complex.gamDot β t'‖)) by ring]
  refine le_trans (mul_le_mul_of_nonneg_left
    (mul_le_mul hmu hmu' (by positivity) (by positivity)) (by positivity)) ?_
  rw [show (B * (Cn * (|t| + |t'| + 3) ^ ((1:ℝ)/2))
        * ‖(riemannZeta (1 + Commons.Analysis.Complex.gam β t))⁻¹‖
        * ‖(riemannZeta (1 + Commons.Analysis.Complex.gam β t'))⁻¹‖ * 1)
        * ((Commons.Analysis.Complex.curveConst β * (1 + t ^ 2)⁻¹)
          * (Commons.Analysis.Complex.curveConst β * (1 + t' ^ 2)⁻¹))
      = (B * (Cn * (|t| + |t'| + 3) ^ ((1:ℝ)/2)) * 1)
        * (‖(riemannZeta (1 + Commons.Analysis.Complex.gam β t))⁻¹‖
          * ‖(riemannZeta (1 + Commons.Analysis.Complex.gam β t'))⁻¹‖)
        * ((Commons.Analysis.Complex.curveConst β * (1 + t ^ 2)⁻¹)
          * (Commons.Analysis.Complex.curveConst β * (1 + t' ^ 2)⁻¹)) by ring]
  refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (mul_le_mul hzt hzt' (by positivity) (by positivity)) (by positivity)) (by positivity)) ?_
  rw [show (B * (Cn * (|t| + |t'| + 3) ^ ((1:ℝ)/2)) * 1)
        * ((C₁ * (Real.log (|t| + 2) + 1)) * (C₁ * (Real.log (|t'| + 2) + 1)))
        * ((Commons.Analysis.Complex.curveConst β * (1 + t ^ 2)⁻¹)
          * (Commons.Analysis.Complex.curveConst β * (1 + t' ^ 2)⁻¹))
      = (B * Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β ^ 2)
        * ((|t| + |t'| + 3) ^ ((1:ℝ)/2)
          * ((Real.log (|t| + 2) + 1) * (Real.log (|t'| + 2) + 1)
            * ((1 + t ^ 2)⁻¹ * (1 + t' ^ 2)⁻¹))) by ring]
  rw [huS]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbroot (by positivity)) (by positivity)
section Main

open Commons.Analysis.Complex

/-- Main theorem (Green-Tao Lemma A.3, `m = 1`). -/
theorem zeta_bound_m1 :
    ∃ β δ C : ℝ, 0 < β ∧ β ≤ 1 / 10 ∧ 0 < δ ∧ 0 < C ∧
      ∀ R : ℝ, 3 ≤ R → ∀ f : ℂ → ℂ → ℂ, ∀ B : ℝ,
      (∀ z z' : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
          -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 →
        DifferentiableAt ℂ (fun u : ℂ => f u z') z) →
      (∀ z z' : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
          -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 →
        DifferentiableAt ℂ (fun u : ℂ => f z u) z') →
      Continuous (Function.uncurry f) →
      (∀ z z' : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
          -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 → ‖f z z'‖ ≤ B) →
      ‖(fun g1 : ℝ → ℂ =>
          (2 * (Real.pi : ℂ) * Complex.I)⁻¹ ^ 2 *
            ∫ t : ℝ, ∫ t' : ℝ,
              f (g1 t) (g1 t') *
                (riemannZeta (1 + g1 t + g1 t') / (riemannZeta (1 + g1 t) * riemannZeta (1 + g1 t'))) *
                (R : ℂ) ^ (g1 t + g1 t') / ((g1 t) ^ 2 * (g1 t') ^ 2) * Complex.I * Complex.I)
        (fun t => ((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        - (f 0 0 * Real.log R + deriv (fun w : ℂ => f 0 w) 0)‖
        ≤ C * (B + 1) + C * Real.exp (-(δ * Real.sqrt (Real.log R))) := by
  obtain ⟨β₀, hβ₀pos, hβ₀10, C₁, hC₁pos, hreg⟩ := zeta_region_inv_analytic_bound_ne
  obtain ⟨Cn, hCnpos, hCn⟩ := zeta_one_add_add_bound_curve_sqrt_curve (β := β₀) hβ₀pos hβ₀10
  obtain ⟨Cs, hCspos, hCs⟩ := norm_riemannZeta_le_const_of_one_lt_re (σ := 3/2) (by norm_num)
  have hinv : ∀ z : ℂ, z ≠ 0 → -(β₀ / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
      DifferentiableAt ℂ (fun u : ℂ => (riemannZeta (1 + u))⁻¹) z :=
    fun z hz h1 h2 => (hreg z hz h1 h2).2.1
  have hinvb : ∀ z : ℂ, z ≠ 0 → -(β₀ / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
      ‖(riemannZeta (1 + z))⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2) + 1) :=
    fun z hz h1 h2 => (hreg z hz h1 h2).2.2
  obtain ⟨Ku, hKupos, hUint, hUle⟩ := Commons.Analysis.Integral.uScaleHalf_integrable
  obtain ⟨Cq, hCqpos, hQle⟩ := gam0_zeta_quartic_integral_le (β := β₀) hβ₀pos hβ₀10 C₁ hC₁pos hinvb
  have hcc : 0 < Commons.Analysis.Complex.curveConst β₀ :=
    Commons.Analysis.Complex.curveConst_pos hβ₀pos
  set K1 : ℝ := Commons.Analysis.Complex.curveConst β₀ * (∫ t : ℝ, (1 + t ^ 2)⁻¹) with hK1def
  set K2 : ℝ := Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β₀ ^ 2 * Ku ^ 2 with hK2def
  change ∃ β δ C : ℝ, 0 < β ∧ β ≤ 1 / 10 ∧ 0 < δ ∧ 0 < C ∧
      ∀ R : ℝ, 3 ≤ R → ∀ f : ℂ → ℂ → ℂ, ∀ B : ℝ,
      (∀ z z' : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
          -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 →
        DifferentiableAt ℂ (fun u : ℂ => f u z') z) →
      (∀ z z' : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
          -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 →
        DifferentiableAt ℂ (fun u : ℂ => f z u) z') →
      Continuous (Function.uncurry f) →
      (∀ z z' : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ 1 →
          -(β / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 → ‖f z z'‖ ≤ B) →
      ‖(fun g1 : ℝ → ℂ =>
          (2 * (Real.pi : ℂ) * Complex.I)⁻¹ ^ 2 *
            ∫ t : ℝ, ∫ t' : ℝ,
              f (g1 t) (g1 t') *
                (riemannZeta (1 + g1 t + g1 t') / (riemannZeta (1 + g1 t) * riemannZeta (1 + g1 t'))) *
                (R : ℂ) ^ (g1 t + g1 t') / ((g1 t) ^ 2 * (g1 t') ^ 2) * Complex.I * Complex.I)
        (fun t => ((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        - (f 0 0 * Real.log R + deriv (fun w : ℂ => f 0 w) 0)‖
        ≤ C * (B + 1) + C * Real.exp (-(δ * Real.sqrt (Real.log R)))
  refine ⟨β₀, 1, max 1 ((2 * Real.pi)⁻¹ * (K1 + K1 + Cq) + (4 * Real.pi ^ 2)⁻¹ * K2),
    hβ₀pos, hβ₀10, one_pos, lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro R hR f B hd1 hd2 hcont hbound
  set Cbig : ℝ := max 1 ((2 * Real.pi)⁻¹
    * (K1 + K1 + Cq) + (4 * Real.pi ^ 2)⁻¹ * K2) with hCbigdef
  have hCbigpos : 0 < Cbig := by
    rw [hCbigdef]; exact lt_of_lt_of_le one_pos (le_max_left _ _)
  set M : ℂ := (2 * (Real.pi : ℂ) * Complex.I)⁻¹ with hMdef
  have hRpos : 0 < R := by linarith
  have hRone : (1:ℝ) ≤ R := by linarith
  have hlogRpos : 0 < Real.log R := Real.log_pos (by linarith)
  have hpiI : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero
    exact_mod_cast Real.pi_ne_zero
  have hMM : M * (2 * (Real.pi : ℂ) * Complex.I) = 1 := by
    rw [hMdef]; exact inv_mul_cancel₀ hpiI
  have hM2 : M ^ 2 * (2 * (Real.pi : ℂ) * Complex.I) ^ 2 = 1 := by
    rw [← mul_pow, hMM]; simp
  have hM21 : M ^ 2 * (2 * (Real.pi : ℂ) * Complex.I) = M := by
    rw [sq, mul_assoc, hMM, mul_one]
  have hnormM : ‖M‖ = (2 * Real.pi)⁻¹ := by
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    have hp : ‖(Real.pi : ℂ)‖ = Real.pi := by
      have hsq : ‖(Real.pi : ℂ)‖ ^ 2 = Real.pi ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
      nlinarith [norm_nonneg (Real.pi : ℂ), Real.pi_pos]
    rw [hMdef, norm_inv, norm_mul, norm_mul, h2, hp, Complex.norm_I, mul_one]
  have hnormM2 : ‖M ^ 2‖ = (4 * Real.pi ^ 2)⁻¹ := by
    rw [norm_pow, hnormM, inv_pow]
    congr 1
    ring
  -- region membership of 0
  have hzero_reg : -(β₀ / Real.log (|(0:ℂ).im| + 2)) ≤ (0:ℂ).re := by
    simp only [Complex.zero_im, abs_zero, Complex.zero_re, zero_add]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have : 0 ≤ β₀ / Real.log 2 := div_nonneg hβ₀pos.le hlog2.le
    linarith
  have hzero_le : (0:ℂ).re ≤ 1 := by simp
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hbound 0 0 hzero_reg hzero_le hzero_reg hzero_le)
  -- basic region facts for `gam`
  have hgam_re : ∀ s : ℝ, (Commons.Analysis.Complex.gam β₀ s).re
      = -(β₀ / Real.log (|s| + 2)) := by
    intro s; simp [Commons.Analysis.Complex.gam, Commons.Analysis.Complex.phi]
  have hgam_im : ∀ s : ℝ, (Commons.Analysis.Complex.gam β₀ s).im = s := by
    intro s; simp [Commons.Analysis.Complex.gam]
  have hbeta_div_le : ∀ s : ℝ, β₀ / Real.log (|s| + 2) ≤ 1 / 2 := by
    intro s
    have hpos : 0 < Real.log (|s| + 2) := Real.log_pos (by linarith [abs_nonneg s])
    rw [div_le_iff₀ hpos]
    have hlog2' : (0.69:ℝ) < Real.log (|s| + 2) := by
      have h1 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      have h2 : Real.log 2 ≤ Real.log (|s| + 2) :=
        Real.log_le_log (by norm_num) (by linarith [abs_nonneg s])
      linarith
    nlinarith [hβ₀10, hlog2']
  have hgam_reg : ∀ t : ℝ, -(β₀ / Real.log (|(Commons.Analysis.Complex.gam β₀ t).im| + 2))
      ≤ (Commons.Analysis.Complex.gam β₀ t).re := by
    intro t; rw [hgam_re, hgam_im]
  have hgam_reg' : ∀ t : ℝ, (Commons.Analysis.Complex.gam β₀ t).re
      ≤ -(β₀ / Real.log (|(Commons.Analysis.Complex.gam β₀ t).im| + 2)) := by
    intro t; rw [hgam_re, hgam_im]
  have hgam_le : ∀ t : ℝ, (Commons.Analysis.Complex.gam β₀ t).re ≤ 1 := by
    intro t
    rw [hgam_re, neg_le]
    exact le_trans (by norm_num : (-1:ℝ) ≤ 0)
      (div_nonneg hβ₀pos.le (Real.log_pos (by linarith [abs_nonneg t])).le)
  have hgam_le_neg_one : ∀ t : ℝ, -1 ≤ (Commons.Analysis.Complex.gam β₀ t).re := by
    intro t
    rw [hgam_re]
    exact neg_le_neg (le_trans (hbeta_div_le t) (by norm_num))
  -- numerator bounds
  have hnum_eta_sigma : ∀ t t' : ℝ,
      ‖riemannZeta (1 + zetaM1Eta R t + zetaM1Sigma t')‖ ≤ Cs := by
    intro t t'
    refine hCs _ ?_
    simp only [Complex.add_re, Complex.one_re, zetaM1Eta_re, zetaM1Sigma_re]
    have h := one_div_log_pos hR
    linarith
  have hnum_gam_sigma : ∀ t t' : ℝ,
      ‖riemannZeta (1 + Commons.Analysis.Complex.gam β₀ t + zetaM1Sigma t')‖ ≤ Cs := by
    intro t t'
    refine hCs _ ?_
    rw [show (1 + Commons.Analysis.Complex.gam β₀ t + zetaM1Sigma t').re
        = 2 - β₀ / Real.log (|t| + 2) by
      simp only [Complex.add_re, Complex.one_re, zetaM1Sigma_re, hgam_re]; ring]
    linarith [hbeta_div_le t]
  have hgam_lo : ∀ s : ℝ, -(β₀ / Real.log 2) ≤ (Commons.Analysis.Complex.gam β₀ s).re := by
    intro s
    rw [hgam_re]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hle : β₀ / Real.log (|s| + 2) ≤ β₀ / Real.log 2 :=
      div_le_div_of_nonneg_left hβ₀pos.le hlog2
        (Real.log_le_log (by norm_num) (by linarith [abs_nonneg s]))
    linarith
  have hnum_gam_gam : ∀ t t' : ℝ,
      ‖riemannZeta (1 + Commons.Analysis.Complex.gam β₀ t + Commons.Analysis.Complex.gam β₀ t')‖
        ≤ Cn * (|t| + |t'| + 3) ^ ((1:ℝ)/2) := by
    intro t t'
    have h := hCn (Commons.Analysis.Complex.gam β₀ t) (Commons.Analysis.Complex.gam β₀ t')
      (hgam_lo t) (hgam_reg' t) (hgam_lo t') (hgam_reg' t')
    simpa [hgam_im] using h
  have hd0 : ∀ z' : ℂ, -(β₀ / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 →
      DifferentiableAt ℂ (fun u : ℂ => f 0 u) z' :=
    fun z' h1 h2 => hd2 0 z' hzero_reg hzero_le h1 h2
  have hb0 : ∀ z' : ℂ, -(β₀ / Real.log (|z'.im| + 2)) ≤ z'.re → z'.re ≤ 1 → ‖f 0 z'‖ ≤ B :=
    fun z' h1 h2 => hbound 0 z' hzero_reg hzero_le h1 h2
  -- the initial unfolding
  have hE : (fun g1 : ℝ → ℂ =>
          (2 * (Real.pi : ℂ) * Complex.I)⁻¹ ^ 2 *
            ∫ t : ℝ, ∫ t' : ℝ,
              f (g1 t) (g1 t') *
                (riemannZeta (1 + g1 t + g1 t') / (riemannZeta (1 + g1 t) * riemannZeta (1 + g1 t'))) *
                (R : ℂ) ^ (g1 t + g1 t') / ((g1 t) ^ 2 * (g1 t') ^ 2) * Complex.I * Complex.I)
        (fun t => ((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      = M ^ 2 * ∫ t : ℝ,
          (∫ t' : ℝ, zetaM1Kernel R f (zetaM1Eta R t) (zetaM1Eta R t') * Complex.I) * Complex.I := by
    simp only [zetaM1Kernel, zetaM1Eta, hMdef]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards with t
    simp only [MeasureTheory.integral_mul_const]
  -- STEP 1: shift the second variable from Γ₁ to Γ₂ (pointwise in t)
  have hstep1 : M ^ 2 * ∫ t : ℝ,
        (∫ t' : ℝ, zetaM1Kernel R f (zetaM1Eta R t) (zetaM1Eta R t') * Complex.I) * Complex.I
      = M ^ 2 * ∫ t : ℝ,
        (∫ t' : ℝ, zetaM1Kernel R f (zetaM1Eta R t) (zetaM1Sigma t') * Complex.I) * Complex.I := by
    congr 1
    refine integral_congr_ae ?_
    filter_upwards with t
    congr 1
    refine greenTao_shift_Gamma1_to_Gamma2 (β := β₀) hβ₀pos hβ₀10 hR f B C₁ hC₁pos hinv hinvb
      hd2 hcont hbound (z := zetaM1Eta R t) (by simp) ?_
    rw [zetaM1Eta_re, zetaM1Eta_im, neg_le]
    exact le_trans (neg_nonpos.mpr (le_of_lt (one_div_log_pos hR)))
      (div_nonneg hβ₀pos.le (Real.log_nonneg (by linarith [abs_nonneg t])))
  -- FUBINI 1
  have hInt1 : MeasureTheory.Integrable (Function.uncurry (fun t t' : ℝ =>
      zetaM1Kernel R f (zetaM1Eta R t) (zetaM1Sigma t')))
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    greenTao_kernel_integrable_eta_sigma_cont hβ₀pos hβ₀10 hR f B C₁ Cs hC₁pos hCspos hcont hinvb hbound hnum_eta_sigma
  have hInt1b : MeasureTheory.Integrable (Function.uncurry (fun t t' : ℝ =>
      (zetaM1Kernel R f (zetaM1Eta R t) (zetaM1Sigma t') * Complex.I) * Complex.I))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    refine hInt1.neg.congr ?_
    filter_upwards with p
    obtain ⟨a, b⟩ := p
    simp only [Function.uncurry_apply_pair, Pi.neg_apply]
    rw [show (zetaM1Kernel R f (zetaM1Eta R a) (zetaM1Sigma b) * Complex.I) * Complex.I
        = -(zetaM1Kernel R f (zetaM1Eta R a) (zetaM1Sigma b)) by
          rw [mul_assoc, Complex.I_mul_I]; ring]
  have hstep2 : M ^ 2 * ∫ t : ℝ,
        (∫ t' : ℝ, zetaM1Kernel R f (zetaM1Eta R t) (zetaM1Sigma t') * Complex.I) * Complex.I
      = M ^ 2 * ∫ t' : ℝ,
        (∫ t : ℝ, zetaM1Kernel R f (zetaM1Eta R t) (zetaM1Sigma t') * Complex.I) * Complex.I := by
    have hL : (∫ t : ℝ,
          (∫ t' : ℝ, zetaM1Kernel R f (zetaM1Eta R t) (zetaM1Sigma t') * Complex.I) * Complex.I)
        = ∫ t : ℝ, ∫ t' : ℝ,
            (zetaM1Kernel R f (zetaM1Eta R t) (zetaM1Sigma t') * Complex.I) * Complex.I := by
      refine integral_congr_ae ?_
      filter_upwards with t
      simp only [MeasureTheory.integral_mul_const]
    have hR' : (∫ t' : ℝ,
          (∫ t : ℝ, zetaM1Kernel R f (zetaM1Eta R t) (zetaM1Sigma t') * Complex.I) * Complex.I)
        = ∫ t' : ℝ, ∫ t : ℝ,
            (zetaM1Kernel R f (zetaM1Eta R t) (zetaM1Sigma t') * Complex.I) * Complex.I := by
      refine integral_congr_ae ?_
      filter_upwards with t'
      simp only [MeasureTheory.integral_mul_const]
    rw [hL, hR', MeasureTheory.integral_integral_swap hInt1b]
  -- STEP 2: shift the first variable from Γ₁ to Γ₀ (pointwise in t')
  have hstep3 : M ^ 2 * ∫ t' : ℝ,
        (∫ t : ℝ, zetaM1Kernel R f (zetaM1Eta R t) (zetaM1Sigma t') * Complex.I) * Complex.I
      = M ^ 2 * ∫ t' : ℝ, ((∫ t : ℝ,
            zetaM1Kernel R f (Commons.Analysis.Complex.gam β₀ t) (zetaM1Sigma t')
              * Commons.Analysis.Complex.gamDot β₀ t)
          + 2 * (Real.pi : ℂ) * Complex.I *
            (f 0 (zetaM1Sigma t') * (R : ℂ) ^ (zetaM1Sigma t') / (zetaM1Sigma t') ^ 2))
          * Complex.I := by
    congr 1
    refine integral_congr_ae ?_
    filter_upwards with t'
    congr 1
    exact greenTao_single_pole_shift_Gamma2 (β := β₀) hβ₀pos hβ₀10 hR f B C₁ hC₁pos hinv hinvb
      hd1 hcont hbound t'
  -- integrability of the two pieces of the split
  have hIntA : MeasureTheory.Integrable (fun t' : ℝ =>
      (∫ t : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β₀ t) (zetaM1Sigma t')
        * Commons.Analysis.Complex.gamDot β₀ t) * Complex.I) MeasureTheory.volume := by
    have hjoin : MeasureTheory.Integrable (Function.uncurry (fun t t' : ℝ =>
        zetaM1Kernel R f (Commons.Analysis.Complex.gam β₀ t) (zetaM1Sigma t')
          * Commons.Analysis.Complex.gamDot β₀ t)) (MeasureTheory.volume.prod MeasureTheory.volume) :=
      greenTao_kernel_integrable_gam_sigma_cont hβ₀pos hβ₀10 hR f B C₁ Cs hC₁pos hCspos hcont hinvb hbound hnum_gam_sigma
    exact (hjoin.integral_prod_right).mul_const Complex.I
  have hRne : (R : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hRpos)
  have hIntB : MeasureTheory.Integrable (fun t' : ℝ =>
      (2 * (Real.pi : ℂ) * Complex.I *
        (f 0 (zetaM1Sigma t') * (R : ℂ) ^ (zetaM1Sigma t') / (zetaM1Sigma t') ^ 2))
        * Complex.I) MeasureTheory.volume := by
    have hcont1 : Continuous (fun t' : ℝ =>
        2 * (Real.pi : ℂ) * Complex.I *
          (f 0 (zetaM1Sigma t') * (R : ℂ) ^ (zetaM1Sigma t') / (zetaM1Sigma t') ^ 2)
          * Complex.I) := by
      refine Continuous.mul (Continuous.mul continuous_const ?_) continuous_const
      refine Continuous.div (Continuous.mul ?_ ?_) (zetaM1Sigma_continuous.pow 2) ?_
      · exact hcont.comp (Continuous.prodMk continuous_const zetaM1Sigma_continuous)
      · exact zetaM1Sigma_continuous.const_cpow (Or.inl hRne)
      · intro t' h
        have hz : zetaM1Sigma t' ≠ 0 := by
          intro hz
          have h1 := congrArg Complex.re hz
          simpa [zetaM1Sigma] using h1
        exact pow_ne_zero 2 hz h
    refine Integrable.mono' ((show MeasureTheory.Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹)
        MeasureTheory.volume from integrable_inv_one_add_sq).const_mul (2 * Real.pi * B * R))
      hcont1.aestronglyMeasurable ?_
    filter_upwards with t'
    have hre : -(β₀ / Real.log (|(zetaM1Sigma t').im| + 2)) ≤ (zetaM1Sigma t').re := by
      rw [zetaM1Sigma_re, zetaM1Sigma_im, neg_le]
      exact le_trans (neg_nonpos.mpr zero_le_one)
        (div_nonneg hβ₀pos.le (Real.log_nonneg (by linarith [abs_nonneg t'])))
    have hle : (zetaM1Sigma t').re ≤ 1 := by rw [zetaM1Sigma_re]
    have hb : ‖f 0 (zetaM1Sigma t')‖ ≤ B := hb0 (zetaM1Sigma t') hre hle
    have hR2 : ‖(R : ℂ) ^ (zetaM1Sigma t')‖ ≤ R := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hRpos, zetaM1Sigma_re]
      exact le_of_eq (Real.rpow_one R)
    have hprod : ‖f 0 (zetaM1Sigma t') * (R : ℂ) ^ (zetaM1Sigma t')‖ ≤ B * R := by
      rw [norm_mul]; exact mul_le_mul hb hR2 (norm_nonneg _) hB0
    have hden : ‖(zetaM1Sigma t') ^ 2‖ = 1 + t' ^ 2 := by
      rw [norm_pow, normSq_zetaM1Sigma]
    have hsplit : ‖2 * (Real.pi : ℂ) * Complex.I *
          (f 0 (zetaM1Sigma t') * (R : ℂ) ^ (zetaM1Sigma t') / (zetaM1Sigma t') ^ 2)
          * Complex.I‖
        = ‖(2 : ℂ) * (Real.pi : ℂ)‖ * ‖f 0 (zetaM1Sigma t') * (R : ℂ) ^ (zetaM1Sigma t')‖
            / ‖(zetaM1Sigma t') ^ 2‖ := by
      rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_div, Complex.norm_I, mul_one, mul_one]
      ring
    have hstep : ‖(2 : ℂ) * (Real.pi : ℂ)‖ * ‖f 0 (zetaM1Sigma t') * (R : ℂ) ^ (zetaM1Sigma t')‖
          / ‖(zetaM1Sigma t') ^ 2‖ ≤ (2 * Real.pi * B * R) * (1 + t' ^ 2)⁻¹ := by
      rw [norm_two_pi_complex, hden, div_eq_mul_inv]
      have h2 : (0:ℝ) ≤ (1 + t' ^ 2)⁻¹ := by positivity
      have h3 : (0:ℝ) ≤ 2 * Real.pi := by positivity
      have h4 : (0:ℝ) ≤ B * R := mul_nonneg hB0 (by linarith)
      calc (2 * Real.pi) * ‖f 0 (zetaM1Sigma t') * (R : ℂ) ^ (zetaM1Sigma t')‖ * (1 + t' ^ 2)⁻¹
          ≤ (2 * Real.pi) * (B * R) * (1 + t' ^ 2)⁻¹ := by
            apply mul_le_mul_of_nonneg_right _ h2
            exact mul_le_mul_of_nonneg_left hprod h3
        _ = (2 * Real.pi * B * R) * (1 + t' ^ 2)⁻¹ := by ring
    exact le_trans (le_of_eq hsplit) hstep
  have hstep4 : M ^ 2 * ∫ t' : ℝ, ((∫ t : ℝ,
            zetaM1Kernel R f (Commons.Analysis.Complex.gam β₀ t) (zetaM1Sigma t')
              * Commons.Analysis.Complex.gamDot β₀ t)
          + 2 * (Real.pi : ℂ) * Complex.I *
            (f 0 (zetaM1Sigma t') * (R : ℂ) ^ (zetaM1Sigma t') / (zetaM1Sigma t') ^ 2))
          * Complex.I
      = M ^ 2 * ((∫ t' : ℝ, (∫ t : ℝ,
            zetaM1Kernel R f (Commons.Analysis.Complex.gam β₀ t) (zetaM1Sigma t')
              * Commons.Analysis.Complex.gamDot β₀ t) * Complex.I)
          + ∫ t' : ℝ, (2 * (Real.pi : ℂ) * Complex.I *
              (f 0 (zetaM1Sigma t') * (R : ℂ) ^ (zetaM1Sigma t') / (zetaM1Sigma t') ^ 2))
              * Complex.I) := by
    congr 1
    rw [show (∫ t' : ℝ, ((∫ t : ℝ,
              zetaM1Kernel R f (Commons.Analysis.Complex.gam β₀ t) (zetaM1Sigma t')
                * Commons.Analysis.Complex.gamDot β₀ t)
            + 2 * (Real.pi : ℂ) * Complex.I *
              (f 0 (zetaM1Sigma t') * (R : ℂ) ^ (zetaM1Sigma t') / (zetaM1Sigma t') ^ 2))
            * Complex.I)
        = ∫ t' : ℝ, ((∫ t : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β₀ t)
              (zetaM1Sigma t') * Commons.Analysis.Complex.gamDot β₀ t) * Complex.I
            + (2 * (Real.pi : ℂ) * Complex.I *
              (f 0 (zetaM1Sigma t') * (R : ℂ) ^ (zetaM1Sigma t') / (zetaM1Sigma t') ^ 2))
              * Complex.I) from by
          refine integral_congr_ae ?_
          filter_upwards with t'
          ring]
    rw [MeasureTheory.integral_add hIntA hIntB]
  -- the double pole at z' = 0
  have hpart2 : (∫ t' : ℝ, (2 * (Real.pi : ℂ) * Complex.I *
        (f 0 (zetaM1Sigma t') * (R : ℂ) ^ (zetaM1Sigma t') / (zetaM1Sigma t') ^ 2)) * Complex.I)
      = 2 * (Real.pi : ℂ) * Complex.I *
        (2 * (Real.pi : ℂ) * Complex.I *
            deriv (fun w : ℂ => f 0 w * (R : ℂ) ^ w) 0
          + (∫ t : ℝ, (f 0 (Commons.Analysis.Complex.gam β₀ t)
              * (R : ℂ) ^ (Commons.Analysis.Complex.gam β₀ t))
              / (Commons.Analysis.Complex.gam β₀ t) ^ 2
              * Commons.Analysis.Complex.gamDot β₀ t)) := by
    rw [show (∫ t' : ℝ, (2 * (Real.pi : ℂ) * Complex.I *
          (f 0 (zetaM1Sigma t') * (R : ℂ) ^ (zetaM1Sigma t') / (zetaM1Sigma t') ^ 2)) * Complex.I)
        = ∫ t' : ℝ, 2 * (Real.pi : ℂ) * Complex.I *
            ((f 0 (zetaM1Sigma t') * (R : ℂ) ^ (zetaM1Sigma t') / (zetaM1Sigma t') ^ 2)
              * Complex.I) from by
          refine integral_congr_ae ?_
          filter_upwards with t'
          ring]
    rw [MeasureTheory.integral_const_mul]
    simp only [zetaM1Sigma]
    rw [greenTao_Gamma2_double_pole (β := β₀) hβ₀pos hR f B hd0 hb0]
  -- integrability on the Γ₀ side
  have hdot : AEStronglyMeasurable (fun t : ℝ => Commons.Analysis.Complex.gamDot β₀ t)
      MeasureTheory.volume :=
    (aestronglyMeasurable_deriv (Commons.Analysis.Complex.gam β₀) MeasureTheory.volume).congr
      (by filter_upwards [Commons.Analysis.Complex.ae_ne_zero] with t ht
          rw [(Commons.Analysis.Complex.hasDerivAt_gam (β := β₀) ht).deriv])
  have hgam_cont : Continuous (fun t : ℝ => (Commons.Analysis.Complex.gam β₀ t) ^ 2) :=
    (Commons.Analysis.Complex.gam_continuous β₀).pow 2
  have hIntC : MeasureTheory.Integrable (fun t : ℝ =>
      (f (Commons.Analysis.Complex.gam β₀ t) 0 * (R : ℂ) ^ (Commons.Analysis.Complex.gam β₀ t)
        / (Commons.Analysis.Complex.gam β₀ t) ^ 2) * Commons.Analysis.Complex.gamDot β₀ t)
      MeasureTheory.volume := by
    have hcont1 : Continuous (fun t : ℝ =>
        f (Commons.Analysis.Complex.gam β₀ t) 0 * (R : ℂ) ^ (Commons.Analysis.Complex.gam β₀ t)
          / (Commons.Analysis.Complex.gam β₀ t) ^ 2) := by
      refine Continuous.div (Continuous.mul ?_ ?_) hgam_cont ?_
      · exact hcont.comp (Continuous.prodMk (Commons.Analysis.Complex.gam_continuous β₀) continuous_const)
      · exact (Commons.Analysis.Complex.gam_continuous β₀).const_cpow (Or.inl hRne)
      · intro t; exact pow_ne_zero 2 (Commons.Analysis.Complex.gam_ne_zero hβ₀pos t)
    refine Integrable.mono' ((show MeasureTheory.Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹)
        MeasureTheory.volume from integrable_inv_one_add_sq).const_mul
        (B * Commons.Analysis.Complex.curveConst β₀))
      (hcont1.aestronglyMeasurable.mul hdot) ?_
    filter_upwards with t
    have hb : ‖f (Commons.Analysis.Complex.gam β₀ t) 0‖ ≤ B :=
      hbound _ _ (hgam_reg t) (hgam_le t) hzero_reg hzero_le
    have hR2 : ‖(R : ℂ) ^ (Commons.Analysis.Complex.gam β₀ t)‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hRpos, hgam_re]
      exact Real.rpow_le_one_of_one_le_of_nonpos hRone
        (neg_nonpos.mpr (div_nonneg hβ₀pos.le (Real.log_nonneg (by linarith [abs_nonneg t]))))
    have hmu := Commons.Analysis.Complex.inv_sq_mul_gamDot_norm_le hβ₀pos t
    rw [show (f (Commons.Analysis.Complex.gam β₀ t) 0
            * (R : ℂ) ^ (Commons.Analysis.Complex.gam β₀ t) / (Commons.Analysis.Complex.gam β₀ t) ^ 2)
            * Commons.Analysis.Complex.gamDot β₀ t
        = (f (Commons.Analysis.Complex.gam β₀ t) 0 * (R : ℂ) ^ (Commons.Analysis.Complex.gam β₀ t))
            * (((Commons.Analysis.Complex.gam β₀ t) ^ 2)⁻¹ * Commons.Analysis.Complex.gamDot β₀ t) by ring,
      norm_mul, norm_mul]
    calc ‖f (Commons.Analysis.Complex.gam β₀ t) 0‖
          * ‖(R : ℂ) ^ (Commons.Analysis.Complex.gam β₀ t)‖
          * ‖((Commons.Analysis.Complex.gam β₀ t) ^ 2)⁻¹ * Commons.Analysis.Complex.gamDot β₀ t‖
        ≤ (B * 1) * (Commons.Analysis.Complex.curveConst β₀ * (1 + t ^ 2)⁻¹) :=
          mul_le_mul (mul_le_mul hb hR2 (norm_nonneg _) hB0) hmu (norm_nonneg _) (by positivity)
      _ = (B * Commons.Analysis.Complex.curveConst β₀) * (1 + t ^ 2)⁻¹ := by ring
  have hneggam : Continuous (fun t : ℝ => -(Commons.Analysis.Complex.gam β₀ t)) :=
    (Commons.Analysis.Complex.gam_continuous β₀).neg
  have hgam_ne1 : ∀ t : ℝ, 1 + Commons.Analysis.Complex.gam β₀ t ≠ 1 := by
    intro t h
    have h0 : Commons.Analysis.Complex.gam β₀ t = 0 := by
      have := congrArg (fun w : ℂ => w - 1) h; simpa using this
    exact Commons.Analysis.Complex.gam_ne_zero hβ₀pos t h0
  have hgam_ne1' : ∀ t : ℝ, 1 - Commons.Analysis.Complex.gam β₀ t ≠ 1 := by
    intro t h
    have h0 : Commons.Analysis.Complex.gam β₀ t = 0 := by
      have := congrArg (fun w : ℂ => 1 - w) h; simpa using this
    exact Commons.Analysis.Complex.gam_ne_zero hβ₀pos t h0
  have hcontζ1 : Continuous (fun t : ℝ => riemannZeta (1 + Commons.Analysis.Complex.gam β₀ t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact ContinuousAt.comp (x := t)
      ((differentiableAt_riemannZeta (hgam_ne1 t)).continuousAt)
      (((continuous_const : Continuous fun _ : ℝ => (1:ℂ)).add
        (Commons.Analysis.Complex.gam_continuous β₀)).continuousAt)
  have hcontζ2 : Continuous (fun t : ℝ => riemannZeta (1 - Commons.Analysis.Complex.gam β₀ t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact ContinuousAt.comp (x := t)
      ((differentiableAt_riemannZeta (hgam_ne1' t)).continuousAt)
      (((continuous_const : Continuous fun _ : ℝ => (1:ℂ)).sub
        (Commons.Analysis.Complex.gam_continuous β₀)).continuousAt)
  have hzene1 : ∀ t : ℝ, riemannZeta (1 + Commons.Analysis.Complex.gam β₀ t) ≠ 0 :=
    fun t => (hreg (Commons.Analysis.Complex.gam β₀ t)
      (Commons.Analysis.Complex.gam_ne_zero hβ₀pos t) (hgam_reg t) (hgam_le t)).1
  have hreg_neg : ∀ t : ℝ, -(β₀ / Real.log (|(-(Commons.Analysis.Complex.gam β₀ t)).im| + 2))
      ≤ (-(Commons.Analysis.Complex.gam β₀ t)).re := by
    intro t
    have him : (-(Commons.Analysis.Complex.gam β₀ t)).im = -t := by rw [Complex.neg_im, hgam_im]
    have hre : (-(Commons.Analysis.Complex.gam β₀ t)).re = β₀ / Real.log (|t| + 2) := by
      rw [Complex.neg_re, hgam_re]; ring
    rw [him, abs_neg, hre]
    exact neg_le_self (div_nonneg hβ₀pos.le (Real.log_nonneg (by linarith [abs_nonneg t])))
  have hneg_le : ∀ t : ℝ, (-(Commons.Analysis.Complex.gam β₀ t)).re ≤ 1 := by
    intro t
    rw [Complex.neg_re, hgam_re, neg_neg]
    exact le_trans (hbeta_div_le t) (by norm_num)
  have hzene2 : ∀ t : ℝ, riemannZeta (1 - Commons.Analysis.Complex.gam β₀ t) ≠ 0 := by
    intro t
    have := hreg (-(Commons.Analysis.Complex.gam β₀ t))
      (by intro h; exact Commons.Analysis.Complex.gam_ne_zero hβ₀pos t (neg_eq_zero.mp h))
      (hreg_neg t) (hneg_le t)
    simpa [sub_eq_add_neg] using this.1
  have hIntD : MeasureTheory.Integrable (fun t : ℝ =>
      (f (Commons.Analysis.Complex.gam β₀ t) (-(Commons.Analysis.Complex.gam β₀ t))
        / (riemannZeta (1 + Commons.Analysis.Complex.gam β₀ t)
            * riemannZeta (1 - Commons.Analysis.Complex.gam β₀ t)
            * (Commons.Analysis.Complex.gam β₀ t) ^ 4))
        * Commons.Analysis.Complex.gamDot β₀ t) MeasureTheory.volume := by
    have hQint := gam0_zeta_quartic_integrable (β := β₀) hβ₀pos hβ₀10 C₁ hC₁pos hinvb
    have hcont1 : Continuous (fun t : ℝ =>
        f (Commons.Analysis.Complex.gam β₀ t) (-(Commons.Analysis.Complex.gam β₀ t))
          / (riemannZeta (1 + Commons.Analysis.Complex.gam β₀ t)
              * riemannZeta (1 - Commons.Analysis.Complex.gam β₀ t)
              * (Commons.Analysis.Complex.gam β₀ t) ^ 4)) := by
      refine Continuous.div ?_ ?_ ?_
      · exact hcont.comp (Continuous.prodMk (Commons.Analysis.Complex.gam_continuous β₀) hneggam)
      · exact Continuous.mul (Continuous.mul hcontζ1 hcontζ2)
          ((Commons.Analysis.Complex.gam_continuous β₀).pow 4)
      · intro t
        exact mul_ne_zero (mul_ne_zero (hzene1 t) (hzene2 t))
          (pow_ne_zero 4 (Commons.Analysis.Complex.gam_ne_zero hβ₀pos t))
    refine Integrable.mono' (hQint.const_mul B) (hcont1.aestronglyMeasurable.mul hdot) ?_
    filter_upwards with t
    have hb : ‖f (Commons.Analysis.Complex.gam β₀ t) (-(Commons.Analysis.Complex.gam β₀ t))‖ ≤ B :=
      hbound _ _ (hgam_reg t) (hgam_le t) (hreg_neg t) (hneg_le t)
    have hden : ‖riemannZeta (1 + Commons.Analysis.Complex.gam β₀ t)
          * riemannZeta (1 - Commons.Analysis.Complex.gam β₀ t)
          * (Commons.Analysis.Complex.gam β₀ t) ^ 4‖
        = ‖riemannZeta (1 + Commons.Analysis.Complex.gam β₀ t)‖
          * ‖riemannZeta (1 - Commons.Analysis.Complex.gam β₀ t)‖
          * ‖Commons.Analysis.Complex.gam β₀ t‖ ^ 4 := by
      rw [norm_mul, norm_mul, norm_pow]
    rw [show (f (Commons.Analysis.Complex.gam β₀ t) (-(Commons.Analysis.Complex.gam β₀ t))
            / (riemannZeta (1 + Commons.Analysis.Complex.gam β₀ t)
                * riemannZeta (1 - Commons.Analysis.Complex.gam β₀ t)
                * (Commons.Analysis.Complex.gam β₀ t) ^ 4))
            * Commons.Analysis.Complex.gamDot β₀ t
        = (f (Commons.Analysis.Complex.gam β₀ t) (-(Commons.Analysis.Complex.gam β₀ t)))
            * (Commons.Analysis.Complex.gamDot β₀ t
              / (riemannZeta (1 + Commons.Analysis.Complex.gam β₀ t)
                  * riemannZeta (1 - Commons.Analysis.Complex.gam β₀ t)
                  * (Commons.Analysis.Complex.gam β₀ t) ^ 4)) by ring,
      norm_mul, norm_div, hden]
    exact mul_le_mul hb le_rfl (by positivity) hB0
  have hIntA2 : MeasureTheory.Integrable (fun t : ℝ =>
      (∫ t' : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β₀ t)
          (Commons.Analysis.Complex.gam β₀ t') * Commons.Analysis.Complex.gamDot β₀ t')
        * Commons.Analysis.Complex.gamDot β₀ t) MeasureTheory.volume := by
    have hjoin : MeasureTheory.Integrable (Function.uncurry (fun t t' : ℝ =>
        zetaM1Kernel R f (Commons.Analysis.Complex.gam β₀ t) (Commons.Analysis.Complex.gam β₀ t')
          * Commons.Analysis.Complex.gamDot β₀ t' * Commons.Analysis.Complex.gamDot β₀ t))
        (MeasureTheory.volume.prod MeasureTheory.volume) := by
      refine (greenTao_kernel_integrable_gam_gam_cont hβ₀pos hβ₀10 hR f B C₁ Cn hC₁pos hCnpos hcont hinvb hbound
        hnum_gam_gam).congr ?_
      filter_upwards with p
      obtain ⟨a, b⟩ := p
      simp only [Function.uncurry_apply_pair, zetaM1Kernel_eq]
      ring
    refine (hjoin.integral_prod_left).congr ?_
    filter_upwards with t
    simp only [Function.uncurry_apply_pair]
    exact (MeasureTheory.integral_mul_const (Commons.Analysis.Complex.gamDot β₀ t)
      (fun t' : ℝ => zetaM1Kernel R f (Commons.Analysis.Complex.gam β₀ t)
        (Commons.Analysis.Complex.gam β₀ t') * Commons.Analysis.Complex.gamDot β₀ t'))
  have hIntB2 : MeasureTheory.Integrable (fun t : ℝ =>
      (2 * (Real.pi : ℂ) * Complex.I *
        (f (Commons.Analysis.Complex.gam β₀ t) 0 * (R : ℂ) ^ (Commons.Analysis.Complex.gam β₀ t)
          / (Commons.Analysis.Complex.gam β₀ t) ^ 2
          + f (Commons.Analysis.Complex.gam β₀ t) (-(Commons.Analysis.Complex.gam β₀ t))
            / (riemannZeta (1 + Commons.Analysis.Complex.gam β₀ t)
                * riemannZeta (1 - Commons.Analysis.Complex.gam β₀ t)
                * (Commons.Analysis.Complex.gam β₀ t) ^ 4)))
        * Commons.Analysis.Complex.gamDot β₀ t) MeasureTheory.volume := by
    refine ((hIntC.add hIntD).const_mul (2 * (Real.pi : ℂ) * Complex.I)).congr ?_
    filter_upwards with t
    simp only [Pi.add_apply]
    ring
  -- FUBINI 2 and STEP 3 (two poles)
  have hIntGamSigma := greenTao_kernel_integrable_gam_sigma_cont hβ₀pos hβ₀10 hR f B C₁ Cs hC₁pos hCspos hcont hinvb hbound
    hnum_gam_sigma
  have hIntD3 : MeasureTheory.Integrable (Function.uncurry (fun x y : ℝ =>
      zetaM1Kernel R f (Commons.Analysis.Complex.gam β₀ y) (zetaM1Sigma x)
        * Commons.Analysis.Complex.gamDot β₀ y))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    refine (hIntGamSigma.swap).congr ?_
    filter_upwards with p
    obtain ⟨a, b⟩ := p
    simp only [Function.comp_apply, Prod.swap_prod_mk, Function.uncurry_apply_pair, zetaM1Kernel,
      zetaM1Sigma]
  have hpart1 : (∫ t' : ℝ, (∫ t : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β₀ t)
          (zetaM1Sigma t') * Commons.Analysis.Complex.gamDot β₀ t) * Complex.I)
      = (∫ t : ℝ, (∫ t' : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β₀ t)
            (Commons.Analysis.Complex.gam β₀ t') * Commons.Analysis.Complex.gamDot β₀ t')
          * Commons.Analysis.Complex.gamDot β₀ t)
        + 2 * (Real.pi : ℂ) * Complex.I *
          ((∫ t : ℝ, (f (Commons.Analysis.Complex.gam β₀ t) 0
              * (R : ℂ) ^ (Commons.Analysis.Complex.gam β₀ t)
              / (Commons.Analysis.Complex.gam β₀ t) ^ 2)
              * Commons.Analysis.Complex.gamDot β₀ t)
            + (∫ t : ℝ, (f (Commons.Analysis.Complex.gam β₀ t)
                (-(Commons.Analysis.Complex.gam β₀ t))
              / (riemannZeta (1 + Commons.Analysis.Complex.gam β₀ t)
                  * riemannZeta (1 - Commons.Analysis.Complex.gam β₀ t)
                  * (Commons.Analysis.Complex.gam β₀ t) ^ 4))
              * Commons.Analysis.Complex.gamDot β₀ t)) := by
    rw [MeasureTheory.integral_mul_const]
    have hswap := MeasureTheory.integral_integral_swap (μ := MeasureTheory.volume)
      (ν := MeasureTheory.volume)
      (f := fun x y : ℝ => zetaM1Kernel R f (Commons.Analysis.Complex.gam β₀ y)
        (zetaM1Sigma x) * Commons.Analysis.Complex.gamDot β₀ y) hIntD3
    rw [hswap]
    rw [← MeasureTheory.integral_mul_const]
    rw [show (∫ t : ℝ, (∫ t' : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β₀ t)
            (zetaM1Sigma t') * Commons.Analysis.Complex.gamDot β₀ t) * Complex.I)
        = ∫ t : ℝ, (∫ t' : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β₀ t)
            (zetaM1Sigma t') * Complex.I) * Commons.Analysis.Complex.gamDot β₀ t from by
          refine integral_congr_ae ?_
          filter_upwards with t
          rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_mul_const]
          ring]
    have h2 : (∫ t : ℝ, (∫ t' : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β₀ t)
            (zetaM1Sigma t') * Complex.I) * Commons.Analysis.Complex.gamDot β₀ t)
        = ∫ t : ℝ, ((∫ t' : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β₀ t)
              (Commons.Analysis.Complex.gam β₀ t') * Commons.Analysis.Complex.gamDot β₀ t')
            + 2 * (Real.pi : ℂ) * Complex.I *
              (f (Commons.Analysis.Complex.gam β₀ t) 0
                  * (R : ℂ) ^ (Commons.Analysis.Complex.gam β₀ t)
                  / (Commons.Analysis.Complex.gam β₀ t) ^ 2
                + f (Commons.Analysis.Complex.gam β₀ t) (-(Commons.Analysis.Complex.gam β₀ t))
                  / (riemannZeta (1 + Commons.Analysis.Complex.gam β₀ t)
                      * riemannZeta (1 - Commons.Analysis.Complex.gam β₀ t)
                      * (Commons.Analysis.Complex.gam β₀ t) ^ 4)))
            * Commons.Analysis.Complex.gamDot β₀ t := by
      refine integral_congr_ae ?_
      filter_upwards with t
      congr 1
      exact greenTao_two_pole_shift_v4 (β := β₀) hβ₀pos hβ₀10 hR f B C₁ Cs Cn hC₁pos hCspos hCnpos
        hinv hinvb hd2 hcont hbound t
        (fun t' => le_trans (hnum_gam_sigma t t') (le_mul_of_one_le_right hCspos.le
          (Real.one_le_rpow (by linarith [abs_nonneg t, abs_nonneg t']) (by norm_num))))
        (fun t' => hnum_gam_gam t t')
    rw [h2]
    rw [show (∫ t : ℝ, ((∫ t' : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β₀ t)
              (Commons.Analysis.Complex.gam β₀ t') * Commons.Analysis.Complex.gamDot β₀ t')
            + 2 * (Real.pi : ℂ) * Complex.I *
              (f (Commons.Analysis.Complex.gam β₀ t) 0
                  * (R : ℂ) ^ (Commons.Analysis.Complex.gam β₀ t)
                  / (Commons.Analysis.Complex.gam β₀ t) ^ 2
                + f (Commons.Analysis.Complex.gam β₀ t) (-(Commons.Analysis.Complex.gam β₀ t))
                  / (riemannZeta (1 + Commons.Analysis.Complex.gam β₀ t)
                      * riemannZeta (1 - Commons.Analysis.Complex.gam β₀ t)
                      * (Commons.Analysis.Complex.gam β₀ t) ^ 4)))
            * Commons.Analysis.Complex.gamDot β₀ t)
        = ∫ t : ℝ, ((∫ t' : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β₀ t)
              (Commons.Analysis.Complex.gam β₀ t') * Commons.Analysis.Complex.gamDot β₀ t')
              * Commons.Analysis.Complex.gamDot β₀ t
            + (2 * (Real.pi : ℂ) * Complex.I *
              (f (Commons.Analysis.Complex.gam β₀ t) 0
                  * (R : ℂ) ^ (Commons.Analysis.Complex.gam β₀ t)
                  / (Commons.Analysis.Complex.gam β₀ t) ^ 2
                + f (Commons.Analysis.Complex.gam β₀ t) (-(Commons.Analysis.Complex.gam β₀ t))
                  / (riemannZeta (1 + Commons.Analysis.Complex.gam β₀ t)
                      * riemannZeta (1 - Commons.Analysis.Complex.gam β₀ t)
                      * (Commons.Analysis.Complex.gam β₀ t) ^ 4)))
              * Commons.Analysis.Complex.gamDot β₀ t) from by
          refine integral_congr_ae ?_
          filter_upwards with t
          ring]
    rw [MeasureTheory.integral_add hIntA2 hIntB2]
    rw [show (∫ t : ℝ, (2 * (Real.pi : ℂ) * Complex.I *
              (f (Commons.Analysis.Complex.gam β₀ t) 0
                  * (R : ℂ) ^ (Commons.Analysis.Complex.gam β₀ t)
                  / (Commons.Analysis.Complex.gam β₀ t) ^ 2
                + f (Commons.Analysis.Complex.gam β₀ t) (-(Commons.Analysis.Complex.gam β₀ t))
                  / (riemannZeta (1 + Commons.Analysis.Complex.gam β₀ t)
                      * riemannZeta (1 - Commons.Analysis.Complex.gam β₀ t)
                      * (Commons.Analysis.Complex.gam β₀ t) ^ 4)))
              * Commons.Analysis.Complex.gamDot β₀ t)
        = ∫ t : ℝ, 2 * (Real.pi : ℂ) * Complex.I *
            ((f (Commons.Analysis.Complex.gam β₀ t) 0
                * (R : ℂ) ^ (Commons.Analysis.Complex.gam β₀ t)
                / (Commons.Analysis.Complex.gam β₀ t) ^ 2
              + f (Commons.Analysis.Complex.gam β₀ t) (-(Commons.Analysis.Complex.gam β₀ t))
                / (riemannZeta (1 + Commons.Analysis.Complex.gam β₀ t)
                    * riemannZeta (1 - Commons.Analysis.Complex.gam β₀ t)
                    * (Commons.Analysis.Complex.gam β₀ t) ^ 4))
              * Commons.Analysis.Complex.gamDot β₀ t) from by
          refine integral_congr_ae ?_
          filter_upwards with t
          ring]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [show (∫ t : ℝ, (f (Commons.Analysis.Complex.gam β₀ t) 0
            * (R : ℂ) ^ (Commons.Analysis.Complex.gam β₀ t)
            / (Commons.Analysis.Complex.gam β₀ t) ^ 2
          + f (Commons.Analysis.Complex.gam β₀ t) (-(Commons.Analysis.Complex.gam β₀ t))
            / (riemannZeta (1 + Commons.Analysis.Complex.gam β₀ t)
                * riemannZeta (1 - Commons.Analysis.Complex.gam β₀ t)
                * (Commons.Analysis.Complex.gam β₀ t) ^ 4))
          * Commons.Analysis.Complex.gamDot β₀ t)
        = ∫ t : ℝ, ((f (Commons.Analysis.Complex.gam β₀ t) 0
            * (R : ℂ) ^ (Commons.Analysis.Complex.gam β₀ t)
            / (Commons.Analysis.Complex.gam β₀ t) ^ 2)
            * Commons.Analysis.Complex.gamDot β₀ t
          + (f (Commons.Analysis.Complex.gam β₀ t) (-(Commons.Analysis.Complex.gam β₀ t))
            / (riemannZeta (1 + Commons.Analysis.Complex.gam β₀ t)
                * riemannZeta (1 - Commons.Analysis.Complex.gam β₀ t)
                * (Commons.Analysis.Complex.gam β₀ t) ^ 4))
            * Commons.Analysis.Complex.gamDot β₀ t) from by
          refine integral_congr_ae ?_
          filter_upwards with t
          ring]
    rw [MeasureTheory.integral_add hIntC hIntD]
  -- the four Γ₀ error terms
  set W1 : ℂ := ∫ t : ℝ, (f 0 (Commons.Analysis.Complex.gam β₀ t)
      * (R : ℂ) ^ (Commons.Analysis.Complex.gam β₀ t))
      / (Commons.Analysis.Complex.gam β₀ t) ^ 2
      * Commons.Analysis.Complex.gamDot β₀ t with hW1
  set W2 : ℂ := ∫ t : ℝ, (∫ t' : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β₀ t)
      (Commons.Analysis.Complex.gam β₀ t') * Commons.Analysis.Complex.gamDot β₀ t')
      * Commons.Analysis.Complex.gamDot β₀ t with hW2
  set W3 : ℂ := ∫ t : ℝ, (f (Commons.Analysis.Complex.gam β₀ t) 0
      * (R : ℂ) ^ (Commons.Analysis.Complex.gam β₀ t)
      / (Commons.Analysis.Complex.gam β₀ t) ^ 2)
      * Commons.Analysis.Complex.gamDot β₀ t with hW3
  set W4 : ℂ := ∫ t : ℝ, (f (Commons.Analysis.Complex.gam β₀ t)
      (-(Commons.Analysis.Complex.gam β₀ t))
      / (riemannZeta (1 + Commons.Analysis.Complex.gam β₀ t)
          * riemannZeta (1 - Commons.Analysis.Complex.gam β₀ t)
          * (Commons.Analysis.Complex.gam β₀ t) ^ 4))
      * Commons.Analysis.Complex.gamDot β₀ t with hW4
  have hW1b : ‖W1‖ ≤ K1 * B := by
    rw [hW1]
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
    have hg : MeasureTheory.Integrable (fun t : ℝ =>
        B * (Commons.Analysis.Complex.curveConst β₀ * (1 + t ^ 2)⁻¹)) MeasureTheory.volume :=
      ((show MeasureTheory.Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹) MeasureTheory.volume
        from integrable_inv_one_add_sq).const_mul
        (Commons.Analysis.Complex.curveConst β₀)).const_mul B
    refine le_trans (MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hg
      (Filter.Eventually.of_forall (fun t => ?_))) ?_
    · exact norm_integrand_le hβ₀pos hRone hB0 (fun z => f 0 z) (fun z h1 h2 => hb0 z h1 h2) t
    · have hI1 : (∫ t : ℝ, B * (Commons.Analysis.Complex.curveConst β₀ * (1 + t ^ 2)⁻¹))
          = B * (∫ t : ℝ, Commons.Analysis.Complex.curveConst β₀ * (1 + t ^ 2)⁻¹) :=
        MeasureTheory.integral_const_mul _ _
      have hI2 : (∫ t : ℝ, Commons.Analysis.Complex.curveConst β₀ * (1 + t ^ 2)⁻¹)
          = Commons.Analysis.Complex.curveConst β₀ * (∫ t : ℝ, (1 + t ^ 2)⁻¹) :=
        MeasureTheory.integral_const_mul _ _
      rw [hI1, hI2, hK1def]
      exact le_of_eq (by ring)
  have hW3b : ‖W3‖ ≤ K1 * B := by
    rw [hW3]
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
    have hg : MeasureTheory.Integrable (fun t : ℝ =>
        B * (Commons.Analysis.Complex.curveConst β₀ * (1 + t ^ 2)⁻¹)) MeasureTheory.volume :=
      ((show MeasureTheory.Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹) MeasureTheory.volume
        from integrable_inv_one_add_sq).const_mul
        (Commons.Analysis.Complex.curveConst β₀)).const_mul B
    refine le_trans (MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hg
      (Filter.Eventually.of_forall (fun t => ?_))) ?_
    · exact norm_integrand_le hβ₀pos hRone hB0 (fun z => f z 0)
        (fun z h1 h2 => hbound z 0 h1 h2 hzero_reg hzero_le) t
    · have hI1 : (∫ t : ℝ, B * (Commons.Analysis.Complex.curveConst β₀ * (1 + t ^ 2)⁻¹))
          = B * (∫ t : ℝ, Commons.Analysis.Complex.curveConst β₀ * (1 + t ^ 2)⁻¹) :=
        MeasureTheory.integral_const_mul _ _
      have hI2 : (∫ t : ℝ, Commons.Analysis.Complex.curveConst β₀ * (1 + t ^ 2)⁻¹)
          = Commons.Analysis.Complex.curveConst β₀ * (∫ t : ℝ, (1 + t ^ 2)⁻¹) :=
        MeasureTheory.integral_const_mul _ _
      rw [hI1, hI2, hK1def]
      exact le_of_eq (by ring)
  have hW4b : ‖W4‖ ≤ Cq * B := by
    rw [hW4]
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
    have hQint := gam0_zeta_quartic_integrable (β := β₀) hβ₀pos hβ₀10 C₁ hC₁pos hinvb
    have hpt : ∀ t : ℝ, ‖(f (Commons.Analysis.Complex.gam β₀ t)
          (-(Commons.Analysis.Complex.gam β₀ t))
          / (riemannZeta (1 + Commons.Analysis.Complex.gam β₀ t)
              * riemannZeta (1 - Commons.Analysis.Complex.gam β₀ t)
              * (Commons.Analysis.Complex.gam β₀ t) ^ 4))
          * Commons.Analysis.Complex.gamDot β₀ t‖
        ≤ B * (‖Commons.Analysis.Complex.gamDot β₀ t‖
            / (‖riemannZeta (1 + Commons.Analysis.Complex.gam β₀ t)‖
                * ‖riemannZeta (1 - Commons.Analysis.Complex.gam β₀ t)‖
                * ‖Commons.Analysis.Complex.gam β₀ t‖ ^ 4)) := by
      intro t
      have hb : ‖f (Commons.Analysis.Complex.gam β₀ t)
          (-(Commons.Analysis.Complex.gam β₀ t))‖ ≤ B :=
        hbound _ _ (hgam_reg t) (hgam_le t) (hreg_neg t) (hneg_le t)
      have hden : ‖riemannZeta (1 + Commons.Analysis.Complex.gam β₀ t)
              * riemannZeta (1 - Commons.Analysis.Complex.gam β₀ t)
              * (Commons.Analysis.Complex.gam β₀ t) ^ 4‖
          = ‖riemannZeta (1 + Commons.Analysis.Complex.gam β₀ t)‖
            * ‖riemannZeta (1 - Commons.Analysis.Complex.gam β₀ t)‖
            * ‖Commons.Analysis.Complex.gam β₀ t‖ ^ 4 := by
        rw [norm_mul, norm_mul, norm_pow]
      rw [show (f (Commons.Analysis.Complex.gam β₀ t) (-(Commons.Analysis.Complex.gam β₀ t))
            / (riemannZeta (1 + Commons.Analysis.Complex.gam β₀ t)
                * riemannZeta (1 - Commons.Analysis.Complex.gam β₀ t)
                * (Commons.Analysis.Complex.gam β₀ t) ^ 4))
            * Commons.Analysis.Complex.gamDot β₀ t
          = f (Commons.Analysis.Complex.gam β₀ t) (-(Commons.Analysis.Complex.gam β₀ t))
            * (Commons.Analysis.Complex.gamDot β₀ t
              / (riemannZeta (1 + Commons.Analysis.Complex.gam β₀ t)
                  * riemannZeta (1 - Commons.Analysis.Complex.gam β₀ t)
                  * (Commons.Analysis.Complex.gam β₀ t) ^ 4)) by ring,
        norm_mul, norm_div, hden]
      exact mul_le_mul hb le_rfl (by positivity) hB0
    refine le_trans (MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun t => norm_nonneg _))
      (hQint.const_mul B) (Filter.Eventually.of_forall hpt)) ?_
    rw [MeasureTheory.integral_const_mul, mul_comm Cq B]
    exact mul_le_mul_of_nonneg_left hQle hB0
  have hW2b : ‖W2‖ ≤ K2 * B := by
    rw [hW2]
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
    set Kg : ℝ := B * Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β₀ ^ 2 with hKg
    have hpt : ∀ t : ℝ, ‖(∫ t' : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β₀ t)
          (Commons.Analysis.Complex.gam β₀ t') * Commons.Analysis.Complex.gamDot β₀ t')
          * Commons.Analysis.Complex.gamDot β₀ t‖
        ≤ (Kg * (∫ s : ℝ, uScale s)) * uScale t := by
      intro t
      have hpt' : ∀ t' : ℝ, ‖zetaM1Kernel R f (Commons.Analysis.Complex.gam β₀ t)
            (Commons.Analysis.Complex.gam β₀ t')
            * Commons.Analysis.Complex.gamDot β₀ t'‖
            * ‖Commons.Analysis.Complex.gamDot β₀ t‖ ≤ (Kg * uScale t) * uScale t' := by
        intro t'
        have h := gamma_gamma_pointwise hβ₀pos hRone f B C₁ Cn hB0 hC₁pos hCnpos hinvb hbound
          hnum_gam_gam t t'
        rw [hKg]
        calc ‖zetaM1Kernel R f (Commons.Analysis.Complex.gam β₀ t)
              (Commons.Analysis.Complex.gam β₀ t')
              * Commons.Analysis.Complex.gamDot β₀ t'‖
              * ‖Commons.Analysis.Complex.gamDot β₀ t‖
            ≤ (B * Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β₀ ^ 2)
              * (uScale t * uScale t') := h
          _ = (B * Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β₀ ^ 2 * uScale t)
              * uScale t' := by ring
      have hInt : MeasureTheory.Integrable (fun t' : ℝ => (Kg * uScale t) * uScale t')
          MeasureTheory.volume := hUint.const_mul _
      calc ‖(∫ t' : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β₀ t)
              (Commons.Analysis.Complex.gam β₀ t')
              * Commons.Analysis.Complex.gamDot β₀ t')
            * Commons.Analysis.Complex.gamDot β₀ t‖
          = ‖∫ t' : ℝ, zetaM1Kernel R f (Commons.Analysis.Complex.gam β₀ t)
              (Commons.Analysis.Complex.gam β₀ t')
              * Commons.Analysis.Complex.gamDot β₀ t'‖
            * ‖Commons.Analysis.Complex.gamDot β₀ t‖ := norm_mul _ _
        _ ≤ (∫ t' : ℝ, ‖zetaM1Kernel R f (Commons.Analysis.Complex.gam β₀ t)
              (Commons.Analysis.Complex.gam β₀ t')
              * Commons.Analysis.Complex.gamDot β₀ t'‖)
            * ‖Commons.Analysis.Complex.gamDot β₀ t‖ :=
            mul_le_mul_of_nonneg_right (MeasureTheory.norm_integral_le_integral_norm _) (norm_nonneg _)
        _ = ∫ t' : ℝ, ‖zetaM1Kernel R f (Commons.Analysis.Complex.gam β₀ t)
              (Commons.Analysis.Complex.gam β₀ t')
              * Commons.Analysis.Complex.gamDot β₀ t'‖
            * ‖Commons.Analysis.Complex.gamDot β₀ t‖ :=
            (MeasureTheory.integral_mul_const _ _).symm
        _ ≤ ∫ t' : ℝ, (Kg * uScale t) * uScale t' :=
            MeasureTheory.integral_mono_of_nonneg
              (Filter.Eventually.of_forall (fun t' => by positivity)) hInt
              (Filter.Eventually.of_forall hpt')
        _ = (Kg * uScale t) * (∫ s : ℝ, uScale s) :=
            MeasureTheory.integral_const_mul _ _
        _ = (Kg * (∫ s : ℝ, uScale s)) * uScale t := by ring
    have hdom : MeasureTheory.Integrable (fun t : ℝ => (Kg * (∫ s : ℝ, uScale s)) * uScale t)
        MeasureTheory.volume := hUint.const_mul _
    refine le_trans (MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hdom
      (Filter.Eventually.of_forall hpt)) ?_
    rw [show (∫ t : ℝ, (Kg * (∫ s : ℝ, uScale s)) * uScale t)
        = (Kg * (∫ s : ℝ, uScale s)) * (∫ s : ℝ, uScale s) from
          MeasureTheory.integral_const_mul _ _]
    have hu0 : 0 ≤ ∫ s : ℝ, uScale s := MeasureTheory.integral_nonneg (fun s => uScale_nonneg s)
    have hsq : (∫ s : ℝ, uScale s) * (∫ s : ℝ, uScale s) ≤ Ku * Ku :=
      mul_le_mul hUle hUle hu0 hKupos.le
    rw [hKg, hK2def]
    calc ((B * Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β₀ ^ 2)
            * (∫ s : ℝ, uScale s)) * (∫ s : ℝ, uScale s)
        = B * Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β₀ ^ 2
          * ((∫ s : ℝ, uScale s) * (∫ s : ℝ, uScale s)) := by ring
      _ ≤ B * Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β₀ ^ 2 * (Ku * Ku) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = Cn * C₁ * C₁ * Commons.Analysis.Complex.curveConst β₀ ^ 2 * Ku ^ 2 * B := by ring
  have hH : deriv (fun w : ℂ => f 0 w * (R : ℂ) ^ w) 0
      = f 0 0 * Real.log R + deriv (fun w : ℂ => f 0 w) 0 := by
    have hd : DifferentiableAt ℂ (fun w : ℂ => f 0 w) 0 := hd0 0 hzero_reg hzero_le
    have hRw : HasDerivAt (fun w : ℂ => (R : ℂ) ^ w) (Real.log R) 0 := by
      have h := (Complex.hasStrictDerivAt_const_cpow (x := (R:ℂ)) (y := 0)
        (Or.inl hRne)).hasDerivAt
      have h2 : (R : ℂ) ^ (0:ℂ) * Complex.log (R : ℂ) = (Real.log R : ℂ) := by
        rw [Complex.cpow_zero, one_mul]
        exact (Complex.ofReal_log (le_of_lt hRpos)).symm
      rwa [h2] at h
    have hmul : deriv (fun w : ℂ => f 0 w * (R : ℂ) ^ w) 0
        = deriv (fun w : ℂ => f 0 w) 0 + f 0 0 * (Real.log R) := by
      have h := (hd.hasDerivAt.mul hRw).deriv
      have h2 : deriv (fun w : ℂ => f 0 w * (R : ℂ) ^ w) 0
          = deriv (fun w : ℂ => f 0 w) 0 * (R : ℂ) ^ (0:ℂ) + f 0 0 * (Real.log R) := h
      rw [Complex.cpow_zero, mul_one] at h2
      exact h2
    rw [hmul]
    ring
  have hres : (fun g1 : ℝ → ℂ =>
          (2 * (Real.pi : ℂ) * Complex.I)⁻¹ ^ 2 *
            ∫ t : ℝ, ∫ t' : ℝ,
              f (g1 t) (g1 t') *
                (riemannZeta (1 + g1 t + g1 t') / (riemannZeta (1 + g1 t) * riemannZeta (1 + g1 t'))) *
                (R : ℂ) ^ (g1 t + g1 t') / ((g1 t) ^ 2 * (g1 t') ^ 2) * Complex.I * Complex.I)
        (fun t => ((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      - (f 0 0 * Real.log R + deriv (fun w : ℂ => f 0 w) 0)
      = M * W1 + M ^ 2 * W2 + M * (W3 + W4) := by
    have hchain : (fun g1 : ℝ → ℂ =>
          (2 * (Real.pi : ℂ) * Complex.I)⁻¹ ^ 2 *
            ∫ t : ℝ, ∫ t' : ℝ,
              f (g1 t) (g1 t') *
                (riemannZeta (1 + g1 t + g1 t') / (riemannZeta (1 + g1 t) * riemannZeta (1 + g1 t'))) *
                (R : ℂ) ^ (g1 t + g1 t') / ((g1 t) ^ 2 * (g1 t') ^ 2) * Complex.I * Complex.I)
        (fun t => ((1 / Real.log R : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        = M ^ 2 * ((W2 + 2 * (Real.pi : ℂ) * Complex.I * (W3 + W4))
            + 2 * (Real.pi : ℂ) * Complex.I *
              (2 * (Real.pi : ℂ) * Complex.I
                  * (f 0 0 * Real.log R + deriv (fun w : ℂ => f 0 w) 0) + W1)) := by
      rw [hE, hstep1, hstep2, hstep3, hstep4, hpart1, hpart2, hH]
    rw [hchain, mul_add, mul_add]
    have hA : M ^ 2 * (2 * (Real.pi : ℂ) * Complex.I * (W3 + W4)) = M * (W3 + W4) := by
      rw [show M ^ 2 * (2 * (Real.pi : ℂ) * Complex.I * (W3 + W4))
          = (M * (2 * (Real.pi : ℂ) * Complex.I)) * (M * (W3 + W4)) by ring, hMM, one_mul]
    have hB : M ^ 2 * (2 * (Real.pi : ℂ) * Complex.I *
        (2 * (Real.pi : ℂ) * Complex.I
            * (f 0 0 * Real.log R + deriv (fun w : ℂ => f 0 w) 0) + W1))
        = (f 0 0 * Real.log R + deriv (fun w : ℂ => f 0 w) 0) + M * W1 := by
      rw [show M ^ 2 * (2 * (Real.pi : ℂ) * Complex.I *
            (2 * (Real.pi : ℂ) * Complex.I
                * (f 0 0 * Real.log R + deriv (fun w : ℂ => f 0 w) 0) + W1))
          = (M * (2 * (Real.pi : ℂ) * Complex.I))
            * (M * (2 * (Real.pi : ℂ) * Complex.I
                * (f 0 0 * Real.log R + deriv (fun w : ℂ => f 0 w) 0) + W1)) by ring,
        hMM, one_mul, mul_add]
      rw [show M * (2 * (Real.pi : ℂ) * Complex.I
            * (f 0 0 * Real.log R + deriv (fun w : ℂ => f 0 w) 0))
          = (M * (2 * (Real.pi : ℂ) * Complex.I))
            * (f 0 0 * Real.log R + deriv (fun w : ℂ => f 0 w) 0) by ring, hMM, one_mul]
    rw [hA, hB]
    ring
  rw [hres]
  have hnorm : ‖M‖ = (2 * Real.pi)⁻¹ := hnormM
  calc ‖M * W1 + M ^ 2 * W2 + M * (W3 + W4)‖
      ≤ ‖M * W1‖ + ‖M ^ 2 * W2‖ + ‖M * (W3 + W4)‖ := by
        have h1 := norm_add_le (M * W1 + M ^ 2 * W2) (M * (W3 + W4))
        have h2 := norm_add_le (M * W1) (M ^ 2 * W2)
        linarith
    _ = ‖M‖ * ‖W1‖ + ‖M ^ 2‖ * ‖W2‖ + ‖M‖ * ‖W3 + W4‖ := by
        rw [norm_mul, norm_mul, norm_mul]
    _ ≤ (2 * Real.pi)⁻¹ * (K1 * B) + (4 * Real.pi ^ 2)⁻¹ * (K2 * B)
        + (2 * Real.pi)⁻¹ * (K1 * B + Cq * B) := by
        rw [hnormM, hnormM2]
        have h34 : ‖W3 + W4‖ ≤ K1 * B + Cq * B := by
          have h := norm_add_le W3 W4
          linarith [hW3b, hW4b, h]
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hW1b (by positivity))
          (mul_le_mul_of_nonneg_left hW2b (by positivity)))
          (mul_le_mul_of_nonneg_left h34 (by positivity))
    _ = ((2 * Real.pi)⁻¹ * (K1 + K1 + Cq) + (4 * Real.pi ^ 2)⁻¹ * K2) * B := by ring
    _ ≤ Cbig * B := by
        rw [hCbigdef]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) hB0
    _ ≤ Cbig * (B + 1) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hCbigpos.le
    _ ≤ Cbig * (B + 1) + Cbig * Real.exp (-(1 * Real.sqrt (Real.log R))) := by
        have h : 0 ≤ Cbig * Real.exp (-(1 * Real.sqrt (Real.log R))) := by positivity
        linarith

end Main

end Commons.NumberTheory.Zeta
