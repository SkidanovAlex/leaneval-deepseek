import Mathlib
import Submission.Work.TMC7Core.Fourier.log_root_aux
import Submission.Work.TMC7Core.Fourier.log_root_core

namespace Work.TMC7Core.Fourier

open MeasureTheory intervalIntegral

/-- `‖exp (2πix)‖ = 1`. -/
private lemma exp_norm_one (x : ℝ) : ‖Complex.exp (2 * Real.pi * Complex.I * x)‖ = 1 := by
  rw [Complex.norm_exp]; simp

/-- `‖e^{2πix} - α‖ = ‖1 - \bar α e^{2πix}‖`. -/
private lemma norm_sub_eq (α : ℂ) (x : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * x) - α‖
      = ‖1 - (starRingEnd ℂ) α * Complex.exp (2 * Real.pi * Complex.I * x)‖ := by
  set E : ℂ := Complex.exp (2 * Real.pi * Complex.I * x) with hE
  have hEconj : E * (starRingEnd ℂ) E = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [show ‖E‖ = 1 by rw [hE]; exact exp_norm_one x]
    norm_num
  have hsplit : E - α = E * (starRingEnd ℂ) (1 - (starRingEnd ℂ) α * E) := by
    rw [map_sub, map_one, map_mul, starRingEnd_self_apply, mul_sub, mul_one]
    rw [← mul_assoc, mul_comm E α, mul_assoc, hEconj, mul_one]
  rw [hsplit, norm_mul, show ‖E‖ = 1 by rw [hE]; exact exp_norm_one x, one_mul,
    Complex.norm_conj]

/-- `‖z^k / (2k)‖ ≤ 1/(2k)` for `‖z‖ < 1`, `0 < k`. -/
private lemma norm_zpow_div_le (z : ℂ) (hz : ‖z‖ < 1) (k : ℤ) (hk : 0 < k) :
    ‖z ^ k / (2 * (k : ℂ))‖ ≤ 1 / (2 * (k : ℝ)) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [norm_div]
  have hden : ‖(2 : ℂ) * (k : ℂ)‖ = 2 * (k : ℝ) := by
    rw [norm_mul, Complex.norm_intCast, abs_of_pos hkpos]
    norm_num
  rw [hden]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [show z ^ k = z ^ (k.toNat : ℕ) by
    conv_lhs => rw [← Int.toNat_of_nonneg (le_of_lt hk)]
    rw [zpow_natCast]]
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg z) (le_of_lt hz)

/-- `log ‖e^{2πix} - α‖ = log‖α‖ + log‖1 - (1/α) e^{2πix}‖` when `‖α‖ > 1`. -/
private lemma log_eq_gt (α : ℂ) (hα : 1 < ‖α‖) (x : ℝ) :
    Real.log ‖Complex.exp (2 * Real.pi * Complex.I * x) - α‖
      = Real.log ‖α‖ + Real.log ‖1 - (1/α) * Complex.exp (2 * Real.pi * Complex.I * x)‖ := by
  have hαpos : 0 < ‖α‖ := lt_trans zero_lt_one hα
  have hα0 : α ≠ 0 := norm_pos_iff.mp hαpos
  have hw : ‖(1/α) * Complex.exp (2 * Real.pi * Complex.I * x)‖ = 1 / ‖α‖ := by
    rw [Complex.norm_mul, exp_norm_one, mul_one, norm_div, norm_one]
  have hne : ‖1 - (1/α) * Complex.exp (2 * Real.pi * Complex.I * x)‖ ≠ 0 := by
    intro h
    have hineq := norm_sub_norm_le (1 : ℂ) ((1/α) * Complex.exp (2 * Real.pi * Complex.I * x))
    rw [norm_one, hw, h] at hineq
    have : 1 / ‖α‖ < 1 := (div_lt_one hαpos).mpr hα
    linarith
  have hfac : Complex.exp (2 * Real.pi * Complex.I * x) - α
      = -α * (1 - (1/α) * Complex.exp (2 * Real.pi * Complex.I * x)) := by
    field_simp; ring
  rw [hfac, norm_mul, norm_neg, Real.log_mul (norm_ne_zero_iff.mpr hα0) hne]

/-- Positive integer frequency case of the target bound. -/
private lemma log_root_fourier_pos (α : ℂ) (hα : ‖α‖ ≠ 1) (k : ℤ) (hk : 0 < k) :
    ‖∫ x in (0 : ℝ)..1, ((Real.log ‖Complex.exp (2 * Real.pi * Complex.I * x) - α‖ : ℝ) : ℂ) *
        Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x))‖ ≤ 1 / (2 * |(k : ℝ)|) := by
  have hkabs : |(k : ℝ)| = (k : ℝ) := abs_of_pos (by exact_mod_cast hk)
  rcases lt_or_gt_of_ne hα with hlt | hgt
  · -- ‖α‖ < 1
    have hza : ‖(starRingEnd ℂ) α‖ < 1 := by simpa using hlt
    have hle : (∫ x in (0 : ℝ)..1, ((Real.log ‖Complex.exp (2 * Real.pi * Complex.I * x) - α‖ : ℝ) : ℂ) *
          Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x)))
        = -(starRingEnd ℂ) α ^ k / (2 * (k : ℂ)) := by
      rw [show (∫ x in (0 : ℝ)..1, ((Real.log ‖Complex.exp (2 * Real.pi * Complex.I * x) - α‖ : ℝ) : ℂ) *
            Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x)))
          = ∫ x in (0 : ℝ)..1, ((Real.log ‖1 - (starRingEnd ℂ) α * Complex.exp (2 * Real.pi * Complex.I * x)‖ : ℝ) : ℂ) *
            Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x)) by
          apply intervalIntegral.integral_congr; intro x _
          dsimp only
          rw [norm_sub_eq α x]]
      exact log_norm_one_sub_mul_exp_fourierCoeff_int (starRingEnd ℂ α) hza k hk
    rw [hle, hkabs,
      show (-((starRingEnd ℂ) α ^ k)) / (2 * (k : ℂ))
          = -(((starRingEnd ℂ) α ^ k) / (2 * (k : ℂ))) by ring,
      norm_neg]
    exact norm_zpow_div_le ((starRingEnd ℂ) α) hza k hk
  · -- 1 < ‖α‖
    have hαpos : 0 < ‖α‖ := lt_trans zero_lt_one hgt
    have hza : ‖(1/α)‖ < 1 := by
      rw [norm_div, norm_one]
      exact (div_lt_one hαpos).mpr hgt
    have hWc : Continuous (fun x : ℝ => 1 - (1/α) * Complex.exp (2 * Real.pi * Complex.I * x)) := by
      fun_prop
    have hWmem : ∀ x : ℝ, (1 - (1/α) * Complex.exp (2 * Real.pi * Complex.I * x)) ∈ Complex.slitPlane := by
      intro x
      rw [Complex.mem_slitPlane_iff]; left
      rw [Complex.sub_re, Complex.one_re]
      have hw : ‖(1/α) * Complex.exp (2 * Real.pi * Complex.I * x)‖ = 1 / ‖α‖ := by
        rw [Complex.norm_mul, exp_norm_one, mul_one, norm_div, norm_one]
      have hle : ((1/α) * Complex.exp (2 * Real.pi * Complex.I * x)).re
          ≤ ‖(1/α) * Complex.exp (2 * Real.pi * Complex.I * x)‖ := Complex.re_le_norm _
      rw [hw] at hle
      have : 1 / ‖α‖ < 1 := (div_lt_one hαpos).mpr hgt
      linarith
    have hPc : Continuous (fun x : ℝ => Complex.log (1 - (1/α) * Complex.exp (2 * Real.pi * Complex.I * x))) :=
      hWc.clog hWmem
    have hDc : Continuous (fun x : ℝ => Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x))) := by
      fun_prop
    have hGcont : Continuous (fun x : ℝ => ((Real.log ‖1 - (1/α) * Complex.exp (2 * Real.pi * Complex.I * x)‖ : ℝ) : ℂ) *
        Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x))) := by
      rw [show (fun x : ℝ => ((Real.log ‖1 - (1/α) * Complex.exp (2 * Real.pi * Complex.I * x)‖ : ℝ) : ℂ) *
            Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x)))
          = (fun x : ℝ => ((Complex.log (1 - (1/α) * Complex.exp (2 * Real.pi * Complex.I * x))).re : ℂ) *
            Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x))) by
        funext x; rw [Complex.log_re]]
      exact ((Complex.continuous_ofReal.comp (Complex.continuous_re.comp hPc)).mul hDc)
    have hDint : IntervalIntegrable (fun x : ℝ => (↑(Real.log ‖α‖) : ℂ) *
        Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x))) volume 0 1 :=
      (continuous_const.mul hDc).intervalIntegrable 0 1
    have hGint : IntervalIntegrable (fun x : ℝ => ((Real.log ‖1 - (1/α) * Complex.exp (2 * Real.pi * Complex.I * x)‖ : ℝ) : ℂ) *
        Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x))) volume 0 1 :=
      hGcont.intervalIntegrable 0 1
    have hkey : (∫ x in (0 : ℝ)..1, ((Real.log ‖Complex.exp (2 * Real.pi * Complex.I * x) - α‖ : ℝ) : ℂ) *
          Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x)))
        = (↑(Real.log ‖α‖) : ℂ) * (∫ x in (0 : ℝ)..1, Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x)))
          + ∫ x in (0 : ℝ)..1, ((Real.log ‖1 - (1/α) * Complex.exp (2 * Real.pi * Complex.I * x)‖ : ℝ) : ℂ) *
              Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x)) := by
      rw [show (∫ x in (0 : ℝ)..1, ((Real.log ‖Complex.exp (2 * Real.pi * Complex.I * x) - α‖ : ℝ) : ℂ) *
            Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x)))
          = ∫ x in (0 : ℝ)..1, ((↑(Real.log ‖α‖) : ℂ) *
              Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x))
              + ((Real.log ‖1 - (1/α) * Complex.exp (2 * Real.pi * Complex.I * x)‖ : ℝ) : ℂ) *
              Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x))) by
          apply intervalIntegral.integral_congr; intro x _
          dsimp only
          rw [log_eq_gt α hgt x, Complex.ofReal_add, add_mul]]
      rw [intervalIntegral.integral_add hDint hGint, intervalIntegral.integral_const_mul]
    rw [hkey, integral_exp_neg_two_pi_I_int k, if_neg (ne_of_gt hk), mul_zero, zero_add,
      log_norm_one_sub_mul_exp_fourierCoeff_int (1/α) hza k hk, hkabs,
      show (-(((1/α) ^ k))) / (2 * (k : ℂ)) = -(((1/α) ^ k) / (2 * (k : ℂ))) by ring,
      norm_neg]
    exact norm_zpow_div_le (1/α) hza k hk

/-- The coefficient at frequency `k` is the conjugate of the coefficient at `-k`. -/
private lemma coeff_conj (α : ℂ) (k : ℤ) :
    (∫ x in (0 : ℝ)..1, ((Real.log ‖Complex.exp (2 * Real.pi * Complex.I * x) - α‖ : ℝ) : ℂ) *
        Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x)))
      = (starRingEnd ℂ) (∫ x in (0 : ℝ)..1, ((Real.log ‖Complex.exp (2 * Real.pi * Complex.I * x) - α‖ : ℝ) : ℂ) *
        Complex.exp (-(2 * Real.pi * Complex.I * (((-k) : ℤ) : ℝ) * x))) := by
  rw [intervalIntegral_conj]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 1
  rw [show -(2 * Real.pi * Complex.I * (((-k) : ℤ) : ℝ) * x)
        = Complex.I * ((2 * Real.pi * (k : ℝ) * x : ℝ) : ℂ) by push_cast; ring]
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- **Avila-Jitomirskaya, `log_root_fourier`.** -/
theorem log_root_fourier (α : ℂ) (hα : ‖α‖ ≠ 1) (k : ℤ) (hk : k ≠ 0) :
    ‖∫ x in (0 : ℝ)..1, ((Real.log ‖Complex.exp (2 * Real.pi * Complex.I * x) - α‖ : ℝ) : ℂ) *
        Complex.exp (-(2 * Real.pi * Complex.I * ((k : ℤ) : ℝ) * x))‖ ≤ 1 / (2 * |((k : ℤ) : ℝ)|) := by
  rcases lt_or_gt_of_ne hk with hkn | hkp
  · have hpos : 0 < -k := by omega
    have h := log_root_fourier_pos α hα (-k) hpos
    rw [coeff_conj α k, Complex.norm_conj]
    convert h using 1
    rw [show ((((-k) : ℤ)) : ℝ) = -(k : ℝ) by push_cast; ring, abs_neg]
  · exact log_root_fourier_pos α hα k hkp

end Work.TMC7Core.Fourier
