import Mathlib

open MeasureTheory

namespace Work.Asymptotics

/-- **Window integral bound.**  For `B ≥ 1`, `λ ≥ 0` and `m ≤ l`, on the window `[1,B]` the
polynomial factor `(1+t)^M t^m` is dominated by `(1+B)^{M+l+1}` and the Gaussian factor
`e^{-πλt}` by `e^{-πλ}`; integrating over the window of length `B - 1 ≤ 1 + B` gives the stated
estimate. -/
theorem windowIntegral_bound (M : ℝ) (hM : 0 ≤ M) (B : ℝ) (hB : 1 ≤ B) (l : ℕ) {lam : ℝ}
    (hlam : 0 ≤ lam) {m : ℕ} (hm : m ≤ l) :
    ∫ t in Set.Icc (1 : ℝ) B, (1 + t) ^ M * t ^ m * Real.exp (-(Real.pi * lam * t))
      ≤ (1 + B) ^ (M + l + 1) * Real.exp (-(Real.pi * lam)) := by
  have hB1 : (0 : ℝ) < 1 + B := by linarith
  set C : ℝ := (1 + B) ^ (M + l) * Real.exp (-(Real.pi * lam)) with hC
  have hCnonneg : 0 ≤ C := by
    rw [hC]; positivity
  -- Pointwise bound of the integrand on the window.
  have hpoint : ∀ t ∈ Set.Icc (1 : ℝ) B,
      (1 + t) ^ M * t ^ m * Real.exp (-(Real.pi * lam * t)) ≤ C := by
    intro t ht
    obtain ⟨ht1, htB⟩ := ht
    have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht1
    have h1t : (0 : ℝ) ≤ 1 + t := by linarith
    have hpoly : (1 + t) ^ M * t ^ m ≤ (1 + B) ^ (M + l) := by
      have hb : (1 + t) ^ M ≤ (1 + B) ^ M := Real.rpow_le_rpow h1t (by linarith) hM
      have htm : t ^ m ≤ (1 + B) ^ l := by
        have h2 : t ^ m ≤ (1 + B) ^ m := pow_le_pow_left₀ ht0 (by linarith) m
        have h3 : (1 + B) ^ m ≤ (1 + B) ^ l := pow_le_pow_right₀ (by linarith) hm
        linarith
      have := mul_le_mul hb htm (pow_nonneg ht0 m)
        (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + B) M)
      rwa [← Real.rpow_natCast (1 + B) l, ← Real.rpow_add hB1 M (l : ℝ)] at this
    have hexp : Real.exp (-(Real.pi * lam * t)) ≤ Real.exp (-(Real.pi * lam)) := by
      apply Real.exp_le_exp.mpr
      have hpl : (0 : ℝ) ≤ Real.pi * lam := mul_nonneg Real.pi_pos.le hlam
      have : Real.pi * lam ≤ Real.pi * lam * t := by
        have := mul_le_mul_of_nonneg_left ht1 hpl
        simpa using this
      linarith
    exact mul_le_mul hpoly hexp (Real.exp_pos _).le
      (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + B) (M + l))
  -- Integrability of the integrand on the (finite-measure) window.
  have hint_f : IntegrableOn (fun t : ℝ => (1 + t) ^ M * t ^ m * Real.exp (-(Real.pi * lam * t)))
      (Set.Icc (1 : ℝ) B) volume := by
    apply Measure.integrableOn_of_bounded
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    · measurability
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact hpoint t ht
      · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith [ht.1] : (0 : ℝ) ≤ 1 + t) M)
          (pow_nonneg (by linarith [ht.1] : (0 : ℝ) ≤ t) m)) (Real.exp_pos _).le
  have hint_C : IntegrableOn (fun _ : ℝ => C) (Set.Icc (1 : ℝ) B) volume := by
    apply Measure.integrableOn_of_bounded (M := C)
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    · measurability
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg hCnonneg]
  calc
    ∫ t in Set.Icc (1 : ℝ) B, (1 + t) ^ M * t ^ m * Real.exp (-(Real.pi * lam * t))
        ≤ ∫ t in Set.Icc (1 : ℝ) B, C :=
          setIntegral_mono_on hint_f hint_C measurableSet_Icc hpoint
    _ = C * volume.real (Set.Icc (1 : ℝ) B) := by
          rw [setIntegral_const, smul_eq_mul, mul_comm]
    _ = C * (B - 1) := by rw [Real.volume_real_Icc_of_le hB]
    _ ≤ C * (1 + B) := by
          apply mul_le_mul_of_nonneg_left _ hCnonneg
          linarith
    _ = (1 + B) ^ (M + l + 1) * Real.exp (-(Real.pi * lam)) := by
          rw [hC, Real.rpow_add hB1 (M + l) 1, Real.rpow_one]
          ring

end Work.Asymptotics
