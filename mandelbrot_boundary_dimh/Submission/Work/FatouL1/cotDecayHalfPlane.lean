import Mathlib
import Submission.Work.FatouL1.cothDecay

namespace Work.FatouL1

/-- `cot z = i · coth (i z)`, written with `z * i` inside `cosh`/`sinh`. -/
private lemma cot_eq_I_mul_cosh_div_sinh (z : ℂ) :
    Complex.cot z =
      Complex.I * (Complex.cosh (z * Complex.I) / Complex.sinh (z * Complex.I)) := by
  have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hcos : Complex.cos z = Complex.cosh (z * Complex.I) := by
    have h := Complex.cos_mul_I (z * Complex.I)
    rw [show (z * Complex.I) * Complex.I = -z by rw [mul_assoc, hII]; ring] at h
    rw [Complex.cos_neg] at h
    exact h
  have hsin : Complex.sin z = -(Complex.sinh (z * Complex.I)) * Complex.I := by
    have h := Complex.sin_mul_I (z * Complex.I)
    rw [show (z * Complex.I) * Complex.I = -z by rw [mul_assoc, hII]; ring] at h
    rw [Complex.sin_neg] at h
    linear_combination -h
  rw [Complex.cot_eq_cos_div_sin, hcos, hsin]
  field_simp
  rw [Complex.I_sq]; ring

theorem cotDecayHalfPlane :
    (∀ τ : ℂ, 1 / 2 ≤ τ.im →
      ‖Complex.cot (Real.pi * τ) + Complex.I‖ ≤ 4 * Real.exp (-2 * Real.pi * τ.im)) ∧
    (∀ τ : ℂ, τ.im ≤ -(1 / 2) →
      ‖Complex.cot (Real.pi * τ) - Complex.I‖ ≤ 4 * Real.exp (2 * Real.pi * τ.im)) := by
  have hre : ∀ τ : ℂ, (Complex.I * τ).re = -τ.im := by
    intro τ
    rw [Complex.mul_re]
    simp
  constructor
  · -- upper half-plane: reduce to `coth (π s) + 1` at `s = i τ`, `Re s ≤ -1/2`
    intro τ hτ
    set s := Complex.I * τ with hs
    have hsr : s.re = -τ.im := by rw [hs, hre τ]
    have hs2 : s.re ≤ -(1 / 2) := by rw [hsr]; linarith
    have hcd := cothDecay.2 s hs2
    have harg : (Real.pi * τ) * Complex.I = Real.pi * s := by rw [hs]; ring
    have hcot : Complex.cot (Real.pi * τ) =
        Complex.I * (Complex.cosh (Real.pi * s) / Complex.sinh (Real.pi * s)) := by
      rw [cot_eq_I_mul_cosh_div_sinh, harg]
    calc ‖Complex.cot (Real.pi * τ) + Complex.I‖
        = ‖Complex.I * ((Complex.cosh (Real.pi * s) / Complex.sinh (Real.pi * s)) + 1)‖ := by
          rw [hcot]; ring_nf
      _ = ‖(Complex.cosh (Real.pi * s) / Complex.sinh (Real.pi * s)) + 1‖ := by
          rw [norm_mul, Complex.norm_I, one_mul]
      _ ≤ 4 * Real.exp (2 * Real.pi * s.re) := hcd
      _ = 4 * Real.exp (-2 * Real.pi * τ.im) := by rw [hsr]; ring_nf
  · -- lower half-plane: reduce to `coth (π s) - 1` at `s = i τ`, `Re s ≥ 1/2`
    intro τ hτ
    set s := Complex.I * τ with hs
    have hsr : s.re = -τ.im := by rw [hs, hre τ]
    have hs2 : 1 / 2 ≤ s.re := by rw [hsr]; linarith
    have hcd := cothDecay.1 s hs2
    have harg : (Real.pi * τ) * Complex.I = Real.pi * s := by rw [hs]; ring
    have hcot : Complex.cot (Real.pi * τ) =
        Complex.I * (Complex.cosh (Real.pi * s) / Complex.sinh (Real.pi * s)) := by
      rw [cot_eq_I_mul_cosh_div_sinh, harg]
    calc ‖Complex.cot (Real.pi * τ) - Complex.I‖
        = ‖Complex.I * ((Complex.cosh (Real.pi * s) / Complex.sinh (Real.pi * s)) - 1)‖ := by
          rw [hcot]; ring_nf
      _ = ‖(Complex.cosh (Real.pi * s) / Complex.sinh (Real.pi * s)) - 1‖ := by
          rw [norm_mul, Complex.norm_I, one_mul]
      _ ≤ 4 * Real.exp (-2 * Real.pi * s.re) := hcd
      _ = 4 * Real.exp (2 * Real.pi * τ.im) := by rw [hsr]; ring_nf

end Work.FatouL1
