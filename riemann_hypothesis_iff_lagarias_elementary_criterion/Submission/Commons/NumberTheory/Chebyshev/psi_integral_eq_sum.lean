import Mathlib
import Submission.Commons.NumberTheory.Zeta.chebyshevPsi_mfold_explicit

namespace Commons.NumberTheory.Chebyshev

open MeasureTheory intervalIntegral

/-- `x * (1 - n/x) = x - n`, cast to `ℂ`, for `x ≠ 0`. -/
lemma psi_integral_eq_sum_aux_mul {x : ℝ} (hx : x ≠ 0) (n : ℕ) :
    (x : ℂ) * (1 - (n : ℂ) / (x : ℂ)) = ((x - (n : ℝ) : ℝ) : ℂ) := by
  have hx' : (x : ℂ) ≠ 0 := by simpa using hx
  have h : (x : ℂ) * (1 - (n : ℂ) / (x : ℂ)) = (x : ℂ) - (n : ℂ) := by
    field_simp
  rw [h]
  push_cast
  ring

theorem psi_integral_eq_sum (x : ℝ) (hx : 0 ≤ x) :
    (∫ t in (0 : ℝ)..x, (Chebyshev.psi t : ℂ))
      = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (((x - (n : ℝ)) : ℝ) : ℂ) := by
  rcases eq_or_lt_of_le hx with hx0 | hxpos
  · subst hx0; simp
  have hxne : (x : ℂ) ≠ 0 := by simpa using (ne_of_gt hxpos)
  -- the `m = 1` case of the shared `m`-fold identity
  have hkey : ((1 : ℂ) / (x : ℂ)) * (∫ t in (0 : ℝ)..x, (Chebyshev.psi t : ℂ))
      = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℂ) / (x : ℂ)) := by
    simpa using
      (Commons.NumberTheory.Zeta.psi_mfold_sum_eq_integral 1 le_rfl hxpos).symm
  have hI : (∫ t in (0 : ℝ)..x, (Chebyshev.psi t : ℂ))
      = (x : ℂ) * ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℂ) / (x : ℂ)) := by
    rw [← hkey, div_eq_inv_mul, mul_one, ← mul_assoc, mul_inv_cancel₀ hxne, one_mul]
  have hS : (x : ℂ) * ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℂ) / (x : ℂ))
      = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (((x - (n : ℝ)) : ℝ) : ℂ) := by
    rw [Finset.mul_sum]
    rw [show Finset.Ioc 0 ⌊x⌋₊ = Finset.Icc 1 ⌊x⌋₊ from by
      ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega]
    apply Finset.sum_congr rfl
    intro n _
    calc (x : ℂ) * (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (1 - (n : ℂ) / (x : ℂ)))
        = ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * ((x : ℂ) * (1 - (n : ℂ) / (x : ℂ))) := by
          ring
      _ = ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (((x - (n : ℝ)) : ℝ) : ℂ) := by
          rw [psi_integral_eq_sum_aux_mul (ne_of_gt hxpos) n]
  rw [hI, hS]

end Commons.NumberTheory.Chebyshev
