import Mathlib

namespace Work.Drive

/-- The squared modulus of the map `D ↦ √2 · (D/|D|) · √(1 - |D|²/2)` is `2 - |D|²`
(when `|D|² ≤ 2`). -/
lemma dcOf_normSq {D : ℂ} (hD : D ≠ 0) (hn : Complex.normSq D ≤ 2) :
    Complex.normSq ((Real.sqrt 2 : ℂ) * (D / ((Real.sqrt (Complex.normSq D) : ℝ) : ℂ)) *
      ((Real.sqrt (1 - Complex.normSq D / 2) : ℝ) : ℂ)) = 2 - Complex.normSq D := by
  have hpos : 0 < Complex.normSq D := Complex.normSq_pos.mpr hD
  have hn' : (0 : ℝ) ≤ 1 - Complex.normSq D / 2 := by linarith
  rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_div,
    Complex.normSq_ofReal, Complex.normSq_ofReal]
  rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.mul_self_sqrt hpos.le,
    Real.mul_self_sqrt hn']
  have hne : Complex.normSq D ≠ 0 := hpos.ne'
  field_simp

theorem dcOf_inj {D₁ D₂ : ℂ} (h₁ : D₁ ≠ 0) (h₂ : D₂ ≠ 0) (hn₁ : Complex.normSq D₁ < 2) (hn₂ : Complex.normSq D₂ < 2) (h : (Real.sqrt 2 : ℂ) * (D₁ / ((Real.sqrt (Complex.normSq D₁) : ℝ) : ℂ)) * ((Real.sqrt (1 - Complex.normSq D₁ / 2) : ℝ) : ℂ) = (Real.sqrt 2 : ℂ) * (D₂ / ((Real.sqrt (Complex.normSq D₂) : ℝ) : ℂ)) * ((Real.sqrt (1 - Complex.normSq D₂ / 2) : ℝ) : ℂ)) : D₁ = D₂ := by
  -- the squared moduli of the images agree, so `|D₁|² = |D₂|²`
  have hn : Complex.normSq D₁ = Complex.normSq D₂ := by
    have hc := congrArg Complex.normSq h
    rw [dcOf_normSq h₁ hn₁.le, dcOf_normSq h₂ hn₂.le] at hc
    linarith
  -- hence the two real scaling factors coincide
  have hsq : ((Real.sqrt (Complex.normSq D₁) : ℝ) : ℂ) =
      ((Real.sqrt (Complex.normSq D₂) : ℝ) : ℂ) := by rw [hn]
  have hsr : ((Real.sqrt (1 - Complex.normSq D₁ / 2) : ℝ) : ℂ) =
      ((Real.sqrt (1 - Complex.normSq D₂ / 2) : ℝ) : ℂ) := by rw [hn]
  -- the factors being cancelled are nonzero
  have hs₁ : ((Real.sqrt (1 - Complex.normSq D₁ / 2) : ℝ) : ℂ) ≠ 0 := by
    simp only [Complex.ofReal_ne_zero, ne_eq]
    exact (Real.sqrt_pos.mpr (by linarith : (0 : ℝ) < 1 - Complex.normSq D₁ / 2)).ne'
  have hsqrt : (Real.sqrt 2 : ℂ) ≠ 0 := by
    simp only [Complex.ofReal_ne_zero, ne_eq]
    exact (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hA : ((Real.sqrt (Complex.normSq D₁) : ℝ) : ℂ) ≠ 0 := by
    simp only [Complex.ofReal_ne_zero, ne_eq]
    exact (Real.sqrt_pos.mpr (Complex.normSq_pos.mpr h₁)).ne'
  -- cancel the two nonzero scalars from `h`
  rw [← hsr] at h
  have hcancel : (Real.sqrt 2 : ℂ) * (D₁ / ((Real.sqrt (Complex.normSq D₁) : ℝ) : ℂ)) =
      (Real.sqrt 2 : ℂ) * (D₂ / ((Real.sqrt (Complex.normSq D₂) : ℝ) : ℂ)) :=
    mul_right_cancel₀ hs₁ h
  have huv : D₁ / ((Real.sqrt (Complex.normSq D₁) : ℝ) : ℂ) =
      D₂ / ((Real.sqrt (Complex.normSq D₂) : ℝ) : ℂ) := mul_left_cancel₀ hsqrt hcancel
  rw [← hsq] at huv
  calc D₁ = (D₁ / ((Real.sqrt (Complex.normSq D₁) : ℝ) : ℂ)) *
        ((Real.sqrt (Complex.normSq D₁) : ℝ) : ℂ) := (div_mul_cancel₀ _ hA).symm
    _ = (D₂ / ((Real.sqrt (Complex.normSq D₁) : ℝ) : ℂ)) *
        ((Real.sqrt (Complex.normSq D₁) : ℝ) : ℂ) := by rw [huv]
    _ = D₂ := div_mul_cancel₀ _ hA

end Work.Drive
