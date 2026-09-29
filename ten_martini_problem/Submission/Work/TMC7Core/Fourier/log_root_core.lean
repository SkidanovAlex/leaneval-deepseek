import Mathlib
import Submission.Work.TMC7Core.Fourier.log_root_aux

namespace Work.TMC7Core.Fourier

open MeasureTheory intervalIntegral

/-- `∑ ‖z‖ⁿ/n` converges for `‖z‖ < 1`. -/
private lemma summable_norm_pow_div (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖z‖ ^ n / (n : ℝ)) := by
  have h := (Complex.hasSum_taylorSeries_neg_log hz).summable
  refine h.norm.congr (fun n => ?_)
  rw [norm_div, norm_pow, norm_natCast]

/-- `HasSum` of a function supported at a single point. -/
private lemma hasSum_ite_eq (c : ℕ) (v : ℂ) :
    HasSum (fun n : ℕ => if n = c then v else 0) v := by
  have h := hasSum_single (f := fun n : ℕ => if n = c then v else 0) c
    (fun n hn => by rw [if_neg hn])
  simpa using h

/-- The integral of `log (1 - z e^{2πix}) · e^{-2πimx}` term by term. -/
private lemma hasSum_integral_log_mul_exp (z : ℂ) (hz : ‖z‖ < 1) (m : ℤ) :
    HasSum (fun n : ℕ => ∫ x in (0 : ℝ)..1,
        (-(z ^ n / (n : ℂ)) * Complex.exp (2 * Real.pi * Complex.I * (n : ℝ) * x)) *
          Complex.exp (-(2 * Real.pi * Complex.I * (m : ℝ) * x)))
      (∫ x in (0 : ℝ)..1,
        Complex.log (1 - z * Complex.exp (2 * Real.pi * Complex.I * x)) *
          Complex.exp (-(2 * Real.pi * Complex.I * (m : ℝ) * x))) := by
  have hsum := summable_norm_pow_div z hz
  have hcont : ∀ n : ℕ, Continuous (fun x : ℝ =>
      (-(z ^ n / (n : ℂ)) * Complex.exp (2 * Real.pi * Complex.I * (n : ℝ) * x)) *
        Complex.exp (-(2 * Real.pi * Complex.I * (m : ℝ) * x))) := by
    intro n; fun_prop
  have hnorm : ∀ (n : ℕ) (x : ℝ),
      ‖(-(z ^ n / (n : ℂ)) * Complex.exp (2 * Real.pi * Complex.I * (n : ℝ) * x)) *
        Complex.exp (-(2 * Real.pi * Complex.I * (m : ℝ) * x))‖ = ‖z‖ ^ n / (n : ℝ) := by
    intro n x
    have h1 : ‖Complex.exp (2 * Real.pi * Complex.I * (n : ℝ) * x)‖ = 1 := by
      rw [Complex.norm_exp]; simp
    have h2 : ‖Complex.exp (-(2 * Real.pi * Complex.I * (m : ℝ) * x))‖ = 1 := by
      rw [Complex.norm_exp]; simp
    rw [norm_mul, h2, mul_one, norm_mul, norm_neg, norm_div, norm_pow, h1, mul_one,
      norm_natCast]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := 0) (b := 1)
    (ι := ℕ)
    (F := fun n x => (-(z ^ n / (n : ℂ)) * Complex.exp (2 * Real.pi * Complex.I * (n : ℝ) * x)) *
        Complex.exp (-(2 * Real.pi * Complex.I * (m : ℝ) * x)))
    (f := fun x => Complex.log (1 - z * Complex.exp (2 * Real.pi * Complex.I * x)) *
        Complex.exp (-(2 * Real.pi * Complex.I * (m : ℝ) * x)))
    (bound := fun n x => ‖z‖ ^ n / (n : ℝ)) ?_ ?_ ?_ ?_ ?_
  · intro n; exact (hcont n).aestronglyMeasurable
  · intro n; filter_upwards with t _ using le_of_eq (hnorm n t)
  · filter_upwards with t _ using hsum
  · exact intervalIntegrable_const
  · filter_upwards with t _ using (log_one_sub_mul_exp_hasSum z hz t).mul_right _

/-- Computation of one term of the above series. -/
private lemma integral_log_term (z : ℂ) (m : ℤ) (n : ℕ) :
    ∫ x in (0 : ℝ)..1,
        (-(z ^ n / (n : ℂ)) * Complex.exp (2 * Real.pi * Complex.I * (n : ℝ) * x)) *
          Complex.exp (-(2 * Real.pi * Complex.I * (m : ℝ) * x))
      = -(z ^ n / (n : ℂ)) * (if (n : ℤ) - m = 0 then 1 else 0) := by
  rw [show (∫ x in (0 : ℝ)..1,
        (-(z ^ n / (n : ℂ)) * Complex.exp (2 * Real.pi * Complex.I * (n : ℝ) * x)) *
          Complex.exp (-(2 * Real.pi * Complex.I * (m : ℝ) * x)))
      = ∫ x in (0 : ℝ)..1, (-(z ^ n / (n : ℂ))) *
          (Complex.exp (2 * Real.pi * Complex.I * (n : ℝ) * x) *
            Complex.exp (-(2 * Real.pi * Complex.I * (m : ℝ) * x))) by
        apply intervalIntegral.integral_congr; intro x _; ring]
  rw [intervalIntegral.integral_const_mul]
  congr 1
  rw [show (∫ x in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * (n : ℝ) * x) *
          Complex.exp (-(2 * Real.pi * Complex.I * (m : ℝ) * x)))
      = ∫ x in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * (((n : ℤ) - m : ℤ) : ℝ) * x) by
        apply intervalIntegral.integral_congr; intro x _
        change Complex.exp (2 * Real.pi * Complex.I * (n : ℝ) * x) *
            Complex.exp (-(2 * Real.pi * Complex.I * (m : ℝ) * x))
          = Complex.exp (2 * Real.pi * Complex.I * (((n : ℤ) - m : ℤ) : ℝ) * x)
        rw [← Complex.exp_add]; congr 1; push_cast; ring]
  rw [integral_exp_two_pi_I_int ((n : ℤ) - m)]

/-- Exact value of `∫₀¹ log (1 - z e^{2πix}) e^{-2πimx} dx` for `‖z‖ < 1`. -/
private lemma integral_log_mul_exp_eq (z : ℂ) (hz : ‖z‖ < 1) (m : ℤ) :
    ∫ x in (0 : ℝ)..1, Complex.log (1 - z * Complex.exp (2 * Real.pi * Complex.I * x)) *
        Complex.exp (-(2 * Real.pi * Complex.I * (m : ℝ) * x))
      = if 0 ≤ m then -(z ^ m.toNat) / ((m.toNat : ℕ) : ℂ) else 0 := by
  have hH := hasSum_integral_log_mul_exp z hz m
  have hcongr : HasSum (fun n : ℕ => -(z ^ n / (n : ℂ)) * (if (n : ℤ) - m = 0 then 1 else 0))
      (∫ x in (0 : ℝ)..1, Complex.log (1 - z * Complex.exp (2 * Real.pi * Complex.I * x)) *
        Complex.exp (-(2 * Real.pi * Complex.I * (m : ℝ) * x))) :=
    hH.congr_fun (fun n => (integral_log_term z m n).symm)
  by_cases hm : (0:ℤ) ≤ m
  · rw [if_pos hm]
    have hsingle : HasSum (fun n : ℕ => -(z ^ n / (n : ℂ)) * (if (n : ℤ) - m = 0 then 1 else 0))
        (-(z ^ m.toNat) / ((m.toNat : ℕ) : ℂ)) := by
      have h0 : (fun n : ℕ => -(z ^ n / (n : ℂ)) * (if (n : ℤ) - m = 0 then 1 else 0))
          = (fun n : ℕ => if n = m.toNat then -(z ^ m.toNat) / ((m.toNat : ℕ) : ℂ) else 0) := by
        funext n
        by_cases hn : n = m.toNat
        · subst hn
          have hz0 : ((m.toNat : ℕ) : ℤ) - m = 0 := by rw [Int.toNat_of_nonneg hm]; ring
          rw [if_pos hz0, mul_one, if_pos rfl, neg_div]
        · rw [if_neg hn]
          have hne : (n : ℤ) - m ≠ 0 := by
            intro h
            apply hn
            have h' : (n : ℤ) = m := by omega
            have h2 : (n : ℤ) = (m.toNat : ℤ) := by rw [Int.toNat_of_nonneg hm]; exact h'
            exact_mod_cast h2
          rw [if_neg hne, mul_zero]
      rw [h0]; exact hasSum_ite_eq m.toNat _
    exact HasSum.unique hcongr hsingle
  · rw [if_neg hm]
    refine HasSum.unique hcongr ?_
    rw [show (fun n : ℕ => -(z ^ n / (n : ℂ)) * (if (n : ℤ) - m = 0 then 1 else 0))
        = (fun _ : ℕ => (0 : ℂ)) by
      funext n
      have hne : (n : ℤ) - m ≠ 0 := by omega
      rw [if_neg hne, mul_zero]]
    exact hasSum_zero

end Work.TMC7Core.Fourier

namespace Work.TMC7Core.Fourier

open MeasureTheory intervalIntegral

/-- Conjugation commutes with the interval integral. -/
lemma intervalIntegral_conj (f : ℝ → ℂ) :
    (starRingEnd ℂ) (∫ x in (0 : ℝ)..1, f x) = ∫ x in (0 : ℝ)..1, (starRingEnd ℂ) (f x) := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact (integral_conj (f := f)).symm

/-- **Master Fourier coefficient.** For `‖z‖ < 1` and `k ≥ 1`,
`∫₀¹ log‖1 - z e^{2πix}‖ e^{-2πikx} dx = -z^k/(2k)`. -/
theorem log_norm_one_sub_mul_exp_fourierCoeff (z : ℂ) (hz : ‖z‖ < 1) (k : ℕ) (hk : 1 ≤ k) :
    ∫ x in (0 : ℝ)..1, ((Real.log ‖1 - z * Complex.exp (2 * Real.pi * Complex.I * x)‖ : ℝ) : ℂ) *
        Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x)) = -(z ^ k) / (2 * (k : ℂ)) := by
  have hWcont : Continuous (fun x : ℝ => 1 - z * Complex.exp (2 * Real.pi * Complex.I * x)) := by
    fun_prop
  have hWmem : ∀ x : ℝ, (1 - z * Complex.exp (2 * Real.pi * Complex.I * x)) ∈ Complex.slitPlane := by
    intro x
    rw [Complex.mem_slitPlane_iff]
    left
    rw [Complex.sub_re, Complex.one_re]
    have hEx : ‖Complex.exp (2 * Real.pi * Complex.I * x)‖ = 1 := by rw [Complex.norm_exp]; simp
    have hle : (z * Complex.exp (2 * Real.pi * Complex.I * x)).re
        ≤ ‖z * Complex.exp (2 * Real.pi * Complex.I * x)‖ := Complex.re_le_norm _
    rw [Complex.norm_mul, hEx, mul_one] at hle
    linarith
  have hPcont : Continuous (fun x : ℝ => Complex.log (1 - z * Complex.exp (2 * Real.pi * Complex.I * x))) :=
    hWcont.clog hWmem
  have hEcont : Continuous (fun x : ℝ => Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x))) := by
    fun_prop
  have hFint : IntervalIntegrable (fun x : ℝ => Complex.log (1 - z * Complex.exp (2 * Real.pi * Complex.I * x)) *
      Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x))) volume 0 1 :=
    (hPcont.mul hEcont).intervalIntegrable 0 1
  have hGint : IntervalIntegrable (fun x : ℝ =>
      (starRingEnd ℂ) (Complex.log (1 - z * Complex.exp (2 * Real.pi * Complex.I * x))) *
      Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x))) volume 0 1 :=
    ((Complex.continuous_conj.comp hPcont).mul hEcont).intervalIntegrable 0 1
  have hI : ∫ x in (0:ℝ)..1, Complex.log (1 - z * Complex.exp (2 * Real.pi * Complex.I * x)) *
      Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x)) = -(z ^ k) / (k : ℂ) := by
    have h := integral_log_mul_exp_eq z hz (k : ℤ)
    rw [if_pos (by exact_mod_cast Nat.zero_le k), Int.toNat_natCast] at h
    simpa only [Int.cast_natCast] using h
  have hI' : ∫ x in (0:ℝ)..1, Complex.log (1 - z * Complex.exp (2 * Real.pi * Complex.I * x)) *
      Complex.exp (2 * Real.pi * Complex.I * (k : ℝ) * x) = 0 := by
    have h := integral_log_mul_exp_eq z hz (-(k : ℤ))
    rw [if_neg (by omega : ¬ ((0:ℤ) ≤ -(k:ℤ)))] at h
    rw [← h]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    rw [show -(2 * Real.pi * Complex.I * (((-(k:ℤ)) : ℤ) : ℝ) * x)
          = 2 * Real.pi * Complex.I * (k : ℝ) * x by push_cast; ring]
  have hJ : ∫ x in (0:ℝ)..1, (starRingEnd ℂ) (Complex.log (1 - z * Complex.exp (2 * Real.pi * Complex.I * x))) *
      Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x)) = 0 := by
    have h1 := intervalIntegral_conj (f := fun x : ℝ =>
      (starRingEnd ℂ) (Complex.log (1 - z * Complex.exp (2 * Real.pi * Complex.I * x))) *
        Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x)))
    have h2 : (∫ x in (0:ℝ)..1, (starRingEnd ℂ) ((starRingEnd ℂ) (Complex.log (1 - z * Complex.exp (2 * Real.pi * Complex.I * x))) *
        Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x))))
        = ∫ x in (0:ℝ)..1, Complex.log (1 - z * Complex.exp (2 * Real.pi * Complex.I * x)) *
            Complex.exp (2 * Real.pi * Complex.I * (k : ℝ) * x) := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [map_mul, starRingEnd_self_apply,
        show (starRingEnd ℂ) (Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x)))
            = Complex.exp (2 * Real.pi * Complex.I * (k : ℝ) * x) by
          rw [← Complex.exp_conj]
          congr 1
          have hzw : (starRingEnd ℂ) (2 * Real.pi * Complex.I * (k : ℝ) * x)
              = -(2 * Real.pi * Complex.I * (k : ℝ) * x) := by
            rw [show 2 * Real.pi * Complex.I * (k : ℝ) * x
                = Complex.I * ((2 * Real.pi * (k : ℝ) * x : ℝ) : ℂ) by push_cast; ring]
            rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
          rw [map_neg, hzw]; ring]
    rw [h2] at h1
    exact (starRingEnd ℂ).injective (by rw [h1, hI', map_zero])
  have hpt : ∀ x : ℝ, ((Real.log ‖1 - z * Complex.exp (2 * Real.pi * Complex.I * x)‖ : ℝ) : ℂ) *
        Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x))
      = (1/2) * ((Complex.log (1 - z * Complex.exp (2 * Real.pi * Complex.I * x)) *
            Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x)))
          + ((starRingEnd ℂ) (Complex.log (1 - z * Complex.exp (2 * Real.pi * Complex.I * x))) *
            Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x)))) := by
    intro x
    rw [← Complex.log_re, Complex.re_eq_add_conj]
    ring
  rw [show (∫ x in (0:ℝ)..1, ((Real.log ‖1 - z * Complex.exp (2 * Real.pi * Complex.I * x)‖ : ℝ) : ℂ) *
        Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x)))
      = ∫ x in (0:ℝ)..1, (1/2) * ((Complex.log (1 - z * Complex.exp (2 * Real.pi * Complex.I * x)) *
            Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x)))
          + ((starRingEnd ℂ) (Complex.log (1 - z * Complex.exp (2 * Real.pi * Complex.I * x))) *
            Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x)))) by
      apply intervalIntegral.integral_congr; intro x _; exact hpt x]
  have hk0 : (k : ℂ) ≠ 0 := by
    have : k ≠ 0 := by omega
    exact_mod_cast this
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hFint hGint, hI, hJ, add_zero]
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
  ring

end Work.TMC7Core.Fourier

namespace Work.TMC7Core.Fourier

/-- **Master Fourier coefficient, integer frequency.** Version of
`log_norm_one_sub_mul_exp_fourierCoeff` for a positive integer frequency. -/
theorem log_norm_one_sub_mul_exp_fourierCoeff_int (z : ℂ) (hz : ‖z‖ < 1) (k : ℤ) (hk : 0 < k) :
    ∫ x in (0 : ℝ)..1, ((Real.log ‖1 - z * Complex.exp (2 * Real.pi * Complex.I * x)‖ : ℝ) : ℂ) *
        Complex.exp (-(2 * Real.pi * Complex.I * (k : ℝ) * x)) = -(z ^ k) / (2 * (k : ℂ)) := by
  have hknn : 0 ≤ k := le_of_lt hk
  have h := log_norm_one_sub_mul_exp_fourierCoeff z hz k.toNat (by omega)
  have h1 : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hknn)
  have h2 : ((k.toNat : ℕ) : ℂ) = (k : ℂ) := by
    exact_mod_cast (Int.toNat_of_nonneg hknn)
  have h3 : z ^ (k.toNat : ℕ) = z ^ k := by
    conv_rhs => rw [← Int.toNat_of_nonneg hknn]
    rw [zpow_natCast]
  rw [h1, h2, h3] at h
  exact h

/-- `∫₀¹ exp (-(2πi m x)) dx = 1` if `m = 0` and `0` otherwise. -/
lemma integral_exp_neg_two_pi_I_int (m : ℤ) :
    ∫ x in (0 : ℝ)..1, Complex.exp (-(2 * Real.pi * Complex.I * (m : ℝ) * x))
      = if m = 0 then 1 else 0 := by
  rw [show (fun x : ℝ => Complex.exp (-(2 * Real.pi * Complex.I * (m : ℝ) * x)))
      = fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * (((-m) : ℤ) : ℝ) * x) by
    funext x; congr 1; push_cast; ring]
  rw [integral_exp_two_pi_I_int (-m)]
  by_cases h : m = 0
  · subst h; simp
  · rw [if_neg h, if_neg (by omega)]

end Work.TMC7Core.Fourier
