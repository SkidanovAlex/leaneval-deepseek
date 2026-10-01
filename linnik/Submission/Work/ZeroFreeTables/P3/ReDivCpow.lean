import Mathlib

namespace Work.ZeroFreeTables.P3

/-- Real part of `c / n ^ (σ + ΔI)` for a positive natural `n`:
`Re (c / n ^ (σ + iΔ)) = n ^ (-σ) * Re (c * exp (-i Δ log n))`.

The point is that `n ^ (σ + iΔ) = n ^ σ * exp (i Δ log n)` for `n > 0`, so taking the
inverse contributes the factor `n ^ (-σ)` and the phase `exp (-i Δ log n)`. -/
theorem ReDivCpow {n : ℕ} (hn : 1 ≤ n) (σ Δ : ℝ) (c : ℂ) :
    (c / (n : ℂ) ^ ((σ : ℂ) + (Δ : ℂ) * Complex.I)).re
      = (n : ℝ) ^ (-σ) * (c * Complex.exp ((((-(Δ * Real.log n)) : ℝ) : ℂ) * Complex.I)).re := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  -- `n ^ (σ + iΔ) = n ^ σ * exp (i Δ log n)`
  have hcpow : (n : ℂ) ^ ((σ : ℂ) + (Δ : ℂ) * Complex.I)
      = ((((n : ℝ) ^ σ : ℝ) : ℂ) * Complex.exp ((((Δ * Real.log n) : ℝ) : ℂ) * Complex.I)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (show n ≠ 0 by omega))]
    rw [← Complex.ofReal_natCast]
    rw [← Complex.ofReal_log (le_of_lt hnpos)]
    rw [show (Real.log (n : ℝ) : ℂ) * ((σ : ℂ) + (Δ : ℂ) * Complex.I)
        = ((Real.log (n : ℝ) * σ : ℝ) : ℂ)
            + (((Real.log (n : ℝ) * Δ : ℝ)) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_add, ← Complex.ofReal_exp]
    rw [← Real.rpow_def_of_pos hnpos σ]
    rw [show Real.log (n : ℝ) * Δ = Δ * Real.log (n : ℝ) by ring]
  -- inversion of the real factor `n ^ σ`
  have hA : ((((n : ℝ) ^ σ : ℝ) : ℂ))⁻¹ = ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ) := by
    rw [← Complex.ofReal_inv, ← Real.rpow_neg (le_of_lt hnpos) σ]
  -- inversion of the phase factor `exp (i Δ log n)`
  have hE : (Complex.exp ((((Δ * Real.log n) : ℝ) : ℂ) * Complex.I))⁻¹
      = Complex.exp ((((-(Δ * Real.log n)) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_neg]
    congr 1
    push_cast
    ring
  -- the complex identity
  have key : c / (n : ℂ) ^ ((σ : ℂ) + (Δ : ℂ) * Complex.I)
      = ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)
          * (c * Complex.exp ((((-(Δ * Real.log n)) : ℝ) : ℂ) * Complex.I)) := by
    rw [hcpow, div_eq_mul_inv, mul_inv, hA, hE]
    ring
  rw [key]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

end Work.ZeroFreeTables.P3
