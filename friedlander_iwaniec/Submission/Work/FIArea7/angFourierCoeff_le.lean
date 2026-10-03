import Mathlib
import Submission.Work.FIArea7.AngFourier
import Submission.Work.FIArea7.integral_mul_cexp_eq
import Submission.Work.FIArea7.vanishing_and_support
import Submission.Work.FIArea7.norm_integral_le_of_support

namespace Work.FIArea7

open MeasureTheory intervalIntegral

noncomputable section

/-- The Fourier kernel `x ↦ e^{-iℓx}`. -/
noncomputable def cexp (ℓ : ℤ) : ℝ → ℂ :=
  fun x => Complex.exp (-(Complex.I * (ℓ : ℂ) * (x : ℂ)))

lemma cexp_norm (ℓ : ℤ) (x : ℝ) : ‖cexp ℓ x‖ = 1 := by
  simp [cexp, Complex.norm_exp]

/-- An interval integral over a period equals the integral over the whole line for a function
vanishing outside `(0, 2π)`. -/
lemma intervalIntegral_eq_integral_of_vanishing {F : ℝ → ℂ}
    (h0 : ∀ x, x < 0 → F x = 0) (h2 : ∀ x, 2 * Real.pi < x → F x = 0) :
    ∫ x in (0 : ℝ)..(2 * Real.pi), F x = ∫ x, F x := by
  rw [intervalIntegral.integral_of_le (by positivity),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Set.Icc 0 (2 * Real.pi))
    (fun x hx => by
      simp only [Set.mem_Icc, not_and_or, not_le] at hx
      rcases hx with h | h
      · exact h0 x h
      · exact h2 x h))

/-- **Part of *FI* (16.26)**: the Fourier coefficients of the angular mollifier. -/
theorem angFourierCoeff_le (C : ℝ) (hC : 0 < C) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ (w : ℝ → ℂ) (θ : ℝ) (ℓ : ℤ),
        0 < θ → θ ≤ 1 →
        ContDiff ℝ 2 w →
        (∀ α, ‖w α‖ ≤ 1) →
        (∀ α, w α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ) →
        (∀ j : ℕ, j ≤ 2 → ∀ α : ℝ, ‖iteratedDeriv j w α‖ ≤ (C * θ ^ (-(j : ℝ)))) →
        ‖Work.FIArea7.angFourierCoeff w ℓ‖ ≤ C' * θ / (1 + θ ^ 2 * (ℓ : ℝ) ^ 2) := by
  refine ⟨max 2 (4 * C), by positivity, ?_⟩
  intro w θ ℓ hθ hθ1 hw hbdd hsupp hder
  obtain ⟨hw0, hwA, hd0, hdA, hd20, hd2A, hcsw, hcsd⟩ := vanishing_and_support w θ hsupp
  have hAle : 2 * Real.pi * θ ≤ 2 * Real.pi := by nlinarith [Real.pi_pos]
  have hc0 : (∫ x in (0 : ℝ)..(2 * Real.pi), w x * cexp ℓ x) = ∫ x, w x * cexp ℓ x :=
    intervalIntegral_eq_integral_of_vanishing
      (fun x hx => by rw [hw0 x hx, zero_mul])
      (fun x hx => by rw [hwA x (lt_of_le_of_lt hAle hx), zero_mul])
  have hcoeff : angFourierCoeff w ℓ = (1 / (2 * (Real.pi : ℂ))) * ∫ x, w x * cexp ℓ x := by
    rw [show angFourierCoeff w ℓ
        = (1 / (2 * (Real.pi : ℂ))) * ∫ x in (0:ℝ)..(2*Real.pi), w x * cexp ℓ x from rfl, hc0]
  have hnormc : ‖(1 / (2 * (Real.pi : ℂ)))‖ = (2 * Real.pi)⁻¹ := by
    have h1 : (1 / (2 * (Real.pi : ℂ))) = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) := by
      rw [one_div,
        show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by
          rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul],
        ← Complex.ofReal_inv]
    rw [h1, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0:ℝ) < (2*Real.pi)⁻¹)]
  have hb0 : ∫ x, ‖w x * cexp ℓ x‖ ≤ (2 * Real.pi * θ) * 1 := by
    refine norm_integral_le_of_support (f := fun x => w x * cexp ℓ x)
      (A := 2 * Real.pi * θ) (B := 1) (by positivity) (by norm_num) ?_ ?_ ?_
    · intro x; rw [norm_mul, cexp_norm ℓ x, mul_one]; exact hbdd x
    · intro x hx; rw [hw0 x hx, zero_mul]
    · intro x hx; rw [hwA x hx, zero_mul]
  have hb1 : ∫ x, ‖deriv w x * cexp ℓ x‖ ≤ (2 * Real.pi * θ) * (C * θ ^ (-(1:ℝ))) := by
    refine norm_integral_le_of_support (f := fun x => deriv w x * cexp ℓ x)
      (A := 2 * Real.pi * θ) (B := C * θ ^ (-(1:ℝ))) (by positivity) (by positivity) ?_ ?_ ?_
    · intro x
      rw [norm_mul, cexp_norm ℓ x, mul_one]
      simpa [iteratedDeriv_one] using hder 1 (by norm_num) x
    · intro x hx; rw [hd0 x hx, zero_mul]
    · intro x hx; rw [hdA x hx, zero_mul]
  have hb2 : ∫ x, ‖iteratedDeriv 2 w x * cexp ℓ x‖ ≤ (2 * Real.pi * θ) * (C * θ ^ (-(2:ℝ))) := by
    refine norm_integral_le_of_support (f := fun x => iteratedDeriv 2 w x * cexp ℓ x)
      (A := 2 * Real.pi * θ) (B := C * θ ^ (-(2:ℝ))) (by positivity) (by positivity) ?_ ?_ ?_
    · intro x; rw [norm_mul, cexp_norm ℓ x, mul_one]; exact hder 2 (by norm_num) x
    · intro x hx; rw [hd20 x hx, zero_mul]
    · intro x hx; rw [hd2A x hx, zero_mul]
  have hY0 : ‖∫ x, w x * cexp ℓ x‖ ≤ 2 * Real.pi * θ := by
    calc ‖∫ x, w x * cexp ℓ x‖ ≤ ∫ x, ‖w x * cexp ℓ x‖ := norm_integral_le_integral_norm _
      _ ≤ (2 * Real.pi * θ) * 1 := hb0
      _ = 2 * Real.pi * θ := by ring
  have hI2 : ‖∫ x, iteratedDeriv 2 w x * cexp ℓ x‖
      ≤ (2 * Real.pi * θ) * (C * θ ^ (-(2:ℝ))) := by
    calc ‖∫ x, iteratedDeriv 2 w x * cexp ℓ x‖
        ≤ ∫ x, ‖iteratedDeriv 2 w x * cexp ℓ x‖ := norm_integral_le_integral_norm _
      _ ≤ _ := hb2
  by_cases hcase : θ * |(ℓ : ℝ)| ≤ 1
  · have h2 : θ ^ 2 * (ℓ : ℝ) ^ 2 ≤ 1 := by
      have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ θ * |(ℓ:ℝ)|) hcase 2
      rwa [one_pow, mul_pow, sq_abs] at h
    have hfin : θ ≤ max 2 (4 * C) * θ / (1 + θ ^ 2 * (ℓ : ℝ) ^ 2) := by
      have h1 : (1 : ℝ) + θ ^ 2 * (ℓ : ℝ) ^ 2 ≤ max 2 (4 * C) := by
        have := le_max_left (2:ℝ) (4 * C); linarith
      rw [le_div_iff₀ (by positivity)]
      nlinarith [hθ, h1, sq_nonneg θ, sq_nonneg ((ℓ:ℝ))]
    calc ‖angFourierCoeff w ℓ‖ = (2 * Real.pi)⁻¹ * ‖∫ x, w x * cexp ℓ x‖ := by
          rw [hcoeff, norm_mul, hnormc]
      _ ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * θ) :=
          mul_le_mul_of_nonneg_left hY0 (by positivity)
      _ = θ := by field_simp
      _ ≤ max 2 (4 * C) * θ / (1 + θ ^ 2 * (ℓ : ℝ) ^ 2) := hfin
  · have hcase' : 1 < θ * |(ℓ : ℝ)| := not_le.mp hcase
    have hℓ0 : (ℓ : ℝ) ≠ 0 := by
      intro h
      rw [h] at hcase'
      norm_num at hcase'
    have hℓne : (ℓ : ℂ) ≠ 0 := by
      intro h
      exact hℓ0 (by exact_mod_cast h)
    have hge : 1 ≤ θ ^ 2 * (ℓ : ℝ) ^ 2 := by
      have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) (le_of_lt hcase') 2
      rwa [one_pow, mul_pow, sq_abs] at h
    have h2eq : iteratedDeriv 2 w = deriv (deriv w) := by
      have h := iteratedDeriv_succ (n := 1) (f := w)
      simpa [iteratedDeriv_one] using h
    have hdiffw : Differentiable ℝ w := hw.differentiable (by norm_num)
    have hdcontw : Continuous (deriv w) := hw.continuous_deriv (by norm_num)
    have hdiffd : Differentiable ℝ (deriv w) := by
      simpa [iteratedDeriv_one] using ContDiff.differentiable_iteratedDeriv' 1 hw
    have hdcontd : Continuous (deriv (deriv w)) := by
      simpa [h2eq] using ContDiff.continuous_iteratedDeriv' 2 hw
    have hIBP1 : ∫ x, w x * cexp ℓ x
        = (Complex.I * (ℓ : ℂ))⁻¹ * ∫ x, deriv w x * cexp ℓ x := by
      simpa [cexp] using integral_mul_cexp_eq w ℓ hdiffw hdcontw hcsw hℓne
    have hIBP2 : ∫ x, deriv w x * cexp ℓ x
        = (Complex.I * (ℓ : ℂ))⁻¹ * ∫ x, deriv (deriv w) x * cexp ℓ x := by
      simpa [cexp] using integral_mul_cexp_eq (deriv w) ℓ hdiffd hdcontd hcsd hℓne
    have hIBP2' : ∫ x, deriv w x * cexp ℓ x
        = (Complex.I * (ℓ : ℂ))⁻¹ * ∫ x, iteratedDeriv 2 w x * cexp ℓ x := by
      rw [← h2eq] at hIBP2
      exact hIBP2
    have hnorminv : ‖(Complex.I * (ℓ : ℂ))⁻¹‖ = (|(ℓ : ℝ)|)⁻¹ := by
      rw [norm_inv, norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast]
    have hY3 : ‖∫ x, w x * cexp ℓ x‖
        ≤ (|(ℓ : ℝ)|)⁻¹ * ((|(ℓ : ℝ)|)⁻¹ * ((2 * Real.pi * θ) * (C * θ ^ (-(2:ℝ))))) := by
      rw [hIBP1, hIBP2', norm_mul, norm_mul, hnorminv]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hI2 (by positivity))
        (by positivity)
    have hth2 : θ ^ (-(2:ℝ)) = (θ ^ 2)⁻¹ := by
      have hpow : θ ^ (2:ℝ) = θ ^ 2 := by
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      rw [Real.rpow_neg (le_of_lt hθ), hpow]
    have habs : |(ℓ:ℝ)|⁻¹ * |(ℓ:ℝ)|⁻¹ = ((ℓ:ℝ)^2)⁻¹ := by
      rw [← mul_inv_rev]
      congr 1
      rw [← sq, sq_abs]
    have hY3' : ‖∫ x, w x * cexp ℓ x‖ ≤ 2 * Real.pi * C / (θ * (ℓ:ℝ)^2) := by
      refine hY3.trans (le_of_eq ?_)
      rw [hth2, ← mul_assoc, habs]
      field_simp
    have hkey : C * (1 + θ^2 * (ℓ:ℝ)^2) ≤ max 2 (4*C) * (θ^2 * (ℓ:ℝ)^2) := by
      have h1 : (1:ℝ) + θ^2 * (ℓ:ℝ)^2 ≤ 2 * (θ^2 * (ℓ:ℝ)^2) := by linarith
      have h4 : (4*C) ≤ max 2 (4*C) := le_max_right _ _
      nlinarith [h1, h4, hC, sq_nonneg θ, sq_nonneg ((ℓ:ℝ))]
    have hfin : C / (θ * (ℓ:ℝ)^2) ≤ max 2 (4*C) * θ / (1 + θ^2 * (ℓ:ℝ)^2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hkey]
    calc ‖angFourierCoeff w ℓ‖ = (2 * Real.pi)⁻¹ * ‖∫ x, w x * cexp ℓ x‖ := by
          rw [hcoeff, norm_mul, hnormc]
      _ ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * C / (θ * (ℓ:ℝ)^2)) :=
          mul_le_mul_of_nonneg_left hY3' (by positivity)
      _ = C / (θ * (ℓ:ℝ)^2) := by field_simp
      _ ≤ max 2 (4 * C) * θ / (1 + θ ^ 2 * (ℓ : ℝ) ^ 2) := hfin

end

end Work.FIArea7
