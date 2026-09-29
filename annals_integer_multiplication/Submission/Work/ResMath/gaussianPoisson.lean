import Mathlib
import Submission.Work.ResMath.defs

/-!
# Gaussian Poisson summation (paper §4.1, Thm 4.2 proof, step (a))

For `B > 0` and `x : ℝ`,

`∑' q : ℤ, exp (-π * B * (x - q) ^ 2) = (√B)⁻¹ * ∑' m : ℤ, exp (-π * m ^ 2 / B) * exp (2π i m x)`

(the Poisson summation formula for a Gaussian, in the form used in Harvey–van der Hoeven,
*Integer multiplication in time* `O(n log n)`, Annals 193 (2021), proof of Theorem 4.2).

The proof is a direct application of Mathlib's
`Complex.tsum_exp_neg_quadratic` (Jacobi's theta transformation formula) with `a = B⁻¹` and
`b = I * x`, followed by elementary rewrites of the summands.
-/

namespace Work.ResMath

private lemma gaussianPoisson_aux (B x : ℝ) (hB : 0 < B) :
    (∑' n : ℤ, (Real.exp (-Real.pi * B * (x - (n : ℝ)) ^ 2) : ℂ))
      = ((Real.sqrt B)⁻¹ : ℂ) * ∑' n : ℤ, (Real.exp (-Real.pi * (n : ℝ) ^ 2 / B) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ)) := by
  have hmain := Complex.tsum_exp_neg_quadratic (a := ((B⁻¹ : ℝ) : ℂ))
    (b := Complex.I * (x : ℂ)) (by rw [Complex.ofReal_re]; exact inv_pos.mpr hB)
  -- Pointwise identification of the `cexp` sum on the left with the sum in the statement.
  have h1 : ∀ n : ℤ, Complex.exp (-↑Real.pi * ((B⁻¹ : ℝ) : ℂ) * (n : ℂ) ^ 2
        + 2 * ↑Real.pi * (Complex.I * (x : ℂ)) * (n : ℂ))
      = (Real.exp (-Real.pi * (n : ℝ) ^ 2 / B) : ℂ)
          * Complex.exp (2 * ↑Real.pi * Complex.I * (n : ℂ) * (x : ℂ)) := by
    intro n
    have h : -↑Real.pi * ((B⁻¹ : ℝ) : ℂ) * (n : ℂ) ^ 2
          + 2 * ↑Real.pi * (Complex.I * (x : ℂ)) * (n : ℂ)
        = ((-Real.pi * (n : ℝ) ^ 2 / B : ℝ) : ℂ)
          + 2 * ↑Real.pi * Complex.I * (n : ℂ) * (x : ℂ) := by
      push_cast
      ring
    rw [h, Complex.exp_add, Complex.ofReal_exp]
  -- Pointwise identification of the `cexp` sum on the right with the Gaussian sum.
  have h2 : ∀ n : ℤ, Complex.exp (-↑Real.pi / ((B⁻¹ : ℝ) : ℂ)
        * ((n : ℂ) + Complex.I * (Complex.I * (x : ℂ))) ^ 2)
      = (Real.exp (-Real.pi * B * (x - (n : ℝ)) ^ 2) : ℂ) := by
    intro n
    have hI : Complex.I * (Complex.I * ((x : ℝ) : ℂ)) = -(x : ℂ) := by
      rw [← mul_assoc, Complex.I_mul_I]; ring
    have h : -↑Real.pi / ((B⁻¹ : ℝ) : ℂ) * ((n : ℂ) + Complex.I * (Complex.I * (x : ℂ))) ^ 2
        = ((-Real.pi * B * (x - (n : ℝ)) ^ 2 : ℝ) : ℂ) := by
      rw [hI]
      push_cast
      have hBne : ((B : ℝ) : ℂ) ≠ 0 := by simp [ne_of_gt hB]
      field_simp
      ring
    rw [h, Complex.ofReal_exp]
  simp_rw [h1, h2] at hmain
  -- The prefactor `1 / (B⁻¹)^(1/2)` equals `√B`.
  have hc : 1 / (((B⁻¹ : ℝ)) : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt B : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
    rw [← Complex.ofReal_cpow (inv_nonneg.mpr hB.le) (1 / 2 : ℝ)]
    rw [← Real.sqrt_eq_rpow, Real.sqrt_inv]
    rw [Complex.ofReal_inv, one_div, inv_inv]
  rw [hc] at hmain
  have hsq : ((Real.sqrt B : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_zero, Ne, Complex.ofReal_inj]
    exact Real.sqrt_ne_zero'.mpr hB
  rw [hmain, ← mul_assoc, inv_mul_cancel₀ hsq, one_mul]

theorem gaussianPoisson (B x : ℝ) (hB : 0 < B) :
    (∑' (q : ℤ), (Real.exp (-Real.pi * B * (x - q) ^ 2) : ℂ)) =
      ((Real.sqrt B)⁻¹ : ℂ) *
        ∑' (m : ℤ), (Real.exp (-Real.pi * (m : ℝ) ^ 2 / B) : ℂ) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (x : ℂ)) := by
  exact gaussianPoisson_aux B x hB

end Work.ResMath
