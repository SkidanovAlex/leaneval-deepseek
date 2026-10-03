import Mathlib

namespace Work.FatouL1

/-- The zeros of `sinh (π ·)` are exactly the integral multiples of `I`:
`sinh (π s) = 0 ↔ ∃ n : ℤ, s = n I`. -/
theorem sinhPiZero : ∀ s : ℂ, (Complex.sinh (Real.pi * s) = 0 ↔ ∃ n : ℤ, s = (n : ℂ) * Complex.I) := by
  intro s
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  constructor
  · intro h
    -- `sinh w = 0` forces `exp w = exp (-w)`, hence `exp (w - (-w)) = 1`
    have h1 : Complex.exp ((Real.pi : ℂ) * s) = Complex.exp (-((Real.pi : ℂ) * s)) := by
      have h2 := Complex.two_sinh ((Real.pi : ℂ) * s)
      rw [h, mul_zero] at h2
      exact sub_eq_zero.mp h2.symm
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h1
    refine ⟨n, ?_⟩
    -- `hn : π s = -(π s) + n (2πI)` gives `2 (π s) = n (2πI)`
    have hw : (2 : ℂ) * ((Real.pi : ℂ) * s) = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      linear_combination (norm := ring) hn
    have h3 : (2 : ℂ) * ((Real.pi : ℂ) * s) =
        (2 : ℂ) * ((Real.pi : ℂ) * ((n : ℂ) * Complex.I)) := by
      rw [hw]; ring
    exact mul_left_cancel₀ hpi (mul_left_cancel₀ htwo h3)
  · rintro ⟨n, rfl⟩
    -- `π (n I) = (π n) I` and `sinh (x I) = sin x · I`, with `sin (π n) = 0`
    have hcoef : (Real.pi : ℂ) * (n : ℂ) = ((Real.pi * (n : ℝ) : ℝ) : ℂ) := by
      push_cast; ring
    have hsin : Real.sin (Real.pi * (n : ℝ)) = 0 := by
      rw [mul_comm]; exact Real.sin_int_mul_pi n
    rw [show (Real.pi : ℂ) * ((n : ℂ) * Complex.I) = ((Real.pi : ℂ) * (n : ℂ)) * Complex.I by ring]
    rw [Complex.sinh_mul_I, hcoef, ← Complex.ofReal_sin, hsin]
    simp

end Work.FatouL1
