import Mathlib

namespace Work.BourgainPlan.IonescuWainger

/-- For real `s`, `‖exp (I * s) - 1 - I * s‖ ≤ 2 ‖s‖`: the second-order remainder of the
exponential on the imaginary axis. -/
private lemma norm_exp_I_mul_sub_one_sub_le (s : ℝ) :
    ‖Complex.exp (Complex.I * (s : ℂ)) - 1 - Complex.I * (s : ℂ)‖ ≤ 2 * ‖s‖ := by
  calc ‖Complex.exp (Complex.I * (s : ℂ)) - 1 - Complex.I * (s : ℂ)‖
      ≤ ‖Complex.exp (Complex.I * (s : ℂ)) - 1‖ + ‖Complex.I * (s : ℂ)‖ := norm_sub_le _ _
    _ ≤ ‖s‖ + ‖s‖ := by
        gcongr
        · exact Real.norm_exp_I_mul_ofReal_sub_one_le
        · rw [norm_mul, Complex.norm_I, one_mul]; simp
    _ = 2 * ‖s‖ := by ring

theorem norm_fourier_diffQuot_sub_le (t : ℝ) (n : ℤ) :
    ‖((t : ℂ)⁻¹ * (fourier n (t : AddCircle (1 : ℝ)) - 1)) - (2 : ℂ) * Real.pi * Complex.I * (n : ℂ)‖
      ≤ (4 : ℝ) * Real.pi * ‖(n : ℂ)‖ := by
  have hfact : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
  have hfourier : fourier n (t : AddCircle (1 : ℝ))
      = Complex.exp (Complex.I * ((2 * Real.pi * (n : ℝ) * t : ℝ) : ℂ)) := by
    rw [fourier_coe_apply]
    push_cast
    ring_nf
  rw [hfourier, Complex.norm_intCast n]
  rcases eq_or_ne t 0 with rfl | ht
  · simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_self, mul_zero, zero_sub,
      norm_neg]
    have h2 : ‖(2 : ℂ) * Real.pi * Complex.I * (n : ℂ)‖ = 2 * Real.pi * |(n : ℝ)| := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_intCast]
      simp [Real.pi_pos.le]
    rw [h2]
    nlinarith [Real.pi_pos, abs_nonneg (n : ℝ)]
  · have hIt : Complex.I * ((2 * Real.pi * (n : ℝ) * t : ℝ) : ℂ)
        = (2 * Real.pi * Complex.I * (n : ℂ)) * (t : ℂ) := by
      push_cast; ring
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    have hsplit : (t : ℂ)⁻¹ * (Complex.exp (Complex.I * ((2 * Real.pi * (n : ℝ) * t : ℝ) : ℂ)) - 1)
          - 2 * Real.pi * Complex.I * (n : ℂ)
        = (t : ℂ)⁻¹ * (Complex.exp (Complex.I * ((2 * Real.pi * (n : ℝ) * t : ℝ) : ℂ)) - 1
            - Complex.I * ((2 * Real.pi * (n : ℝ) * t : ℝ) : ℂ)) := by
      rw [hIt]
      field_simp
    rw [hsplit, norm_mul]
    have hnorm_inv : ‖((t : ℂ))⁻¹‖ = |t|⁻¹ := by rw [norm_inv]; simp
    have hnorm_S : ‖(2 * Real.pi * (n : ℝ) * t : ℝ)‖ = 2 * Real.pi * |(n : ℝ)| * |t| := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
      simp [Real.pi_pos.le]
    have hmain : ‖Complex.exp (Complex.I * ((2 * Real.pi * (n : ℝ) * t : ℝ) : ℂ)) - 1
          - Complex.I * ((2 * Real.pi * (n : ℝ) * t : ℝ) : ℂ)‖
        ≤ 2 * (2 * Real.pi * |(n : ℝ)| * |t|) := by
      have h := norm_exp_I_mul_sub_one_sub_le (2 * Real.pi * (n : ℝ) * t)
      rwa [hnorm_S] at h
    rw [hnorm_inv]
    calc |t|⁻¹ * ‖Complex.exp (Complex.I * ((2 * Real.pi * (n : ℝ) * t : ℝ) : ℂ)) - 1
            - Complex.I * ((2 * Real.pi * (n : ℝ) * t : ℝ) : ℂ)‖
        ≤ |t|⁻¹ * (2 * (2 * Real.pi * |(n : ℝ)| * |t|)) :=
          mul_le_mul_of_nonneg_left hmain (by positivity)
      _ = 4 * Real.pi * |(n : ℝ)| := by
          have htabs : |t| ≠ 0 := abs_ne_zero.mpr ht
          have hcancel : |t|⁻¹ * |t| = 1 := inv_mul_cancel₀ htabs
          calc |t|⁻¹ * (2 * (2 * Real.pi * |(n : ℝ)| * |t|))
              = (2 * (2 * Real.pi * |(n : ℝ)|)) * (|t|⁻¹ * |t|) := by ring
            _ = 4 * Real.pi * |(n : ℝ)| := by rw [hcancel, mul_one]; ring

end Work.BourgainPlan.IonescuWainger
