import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Commons.Analysis.Fourier

open scoped BigOperators

/-- Splitting the exponential `exp (2πi ∑ᵢ (xᵢ + i yᵢ) aᵢ)` into a complex phase
`exp (2πi ∑ᵢ xᵢ aᵢ)` times the real exponential `exp (-(2π) ∑ᵢ yᵢ aᵢ)`. -/
theorem cexp_sum_add_I_mul_eq (d : ℕ) (x y a : EuclideanSpace ℝ (Fin d)) :
    Complex.exp (2 * Real.pi * Complex.I * (∑ i : Fin d, ((x i : ℂ) + (y i : ℂ) * Complex.I) * (a i : ℂ)))
      = Complex.exp (2 * Real.pi * Complex.I * (∑ i : Fin d, (x i : ℂ) * (a i : ℂ)))
        * (Real.exp (-(2 * Real.pi) * ∑ i : Fin d, y i * a i) : ℂ) := by
  have hterm : ∀ i : Fin d, ((x i : ℂ) + (y i : ℂ) * Complex.I) * (a i : ℂ)
      = (x i : ℂ) * (a i : ℂ) + Complex.I * ((y i : ℂ) * (a i : ℂ)) := fun i => by ring
  have h2 : (∑ i : Fin d, (y i : ℂ) * (a i : ℂ)) = ((∑ i : Fin d, y i * a i : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    simp [Complex.ofReal_mul]
  have hsplit : (∑ i : Fin d, ((x i : ℂ) + (y i : ℂ) * Complex.I) * (a i : ℂ))
      = (∑ i : Fin d, (x i : ℂ) * (a i : ℂ))
        + Complex.I * ((∑ i : Fin d, y i * a i : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, ← Finset.mul_sum, h2]
  have harg : 2 * Real.pi * Complex.I
        * ((∑ i : Fin d, (x i : ℂ) * (a i : ℂ)) + Complex.I * ((∑ i : Fin d, y i * a i : ℝ) : ℂ))
      = 2 * Real.pi * Complex.I * (∑ i : Fin d, (x i : ℂ) * (a i : ℂ))
        + ((↑(-(2 * Real.pi) * ∑ i : Fin d, y i * a i)) : ℂ) := by
    calc 2 * Real.pi * Complex.I
          * ((∑ i : Fin d, (x i : ℂ) * (a i : ℂ)) + Complex.I * ((∑ i : Fin d, y i * a i : ℝ) : ℂ))
        = 2 * Real.pi * Complex.I * (∑ i : Fin d, (x i : ℂ) * (a i : ℂ))
          + (2 * Real.pi : ℂ) * ((∑ i : Fin d, y i * a i : ℝ) : ℂ) * (Complex.I * Complex.I) := by
            ring
      _ = 2 * Real.pi * Complex.I * (∑ i : Fin d, (x i : ℂ) * (a i : ℂ))
          + ((↑(-(2 * Real.pi) * ∑ i : Fin d, y i * a i)) : ℂ) := by
            rw [Complex.I_mul_I]; push_cast; ring
  rw [hsplit, harg, Complex.exp_add, ← Complex.ofReal_exp]

end Commons.Analysis.Fourier