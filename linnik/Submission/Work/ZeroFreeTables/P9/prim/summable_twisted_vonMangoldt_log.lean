import Mathlib
import Submission.Work.ZeroFreeTables.P3.SummableVonMangoldtLogPow

namespace Work.ZeroFreeTables.P9.prim

open ArithmeticFunction

/-- **Absolute convergence of the twisted von Mangoldt series.**
For `1 < re s`, every Dirichlet character `χ` mod `N` and every `j : ℕ` the series
`∑_n Λ(n) χ(n) n^{-s} (-log n)^j` converges absolutely.

Since `Λ(n) ≤ log n`, `‖χ(n)‖ ≤ 1` and `‖n^{-s}‖ = n^{-re s}`, the `n`-th summand is
dominated in norm by `Λ(n) (log n)^j / n^{re s}`, whose summability is the
`j`-instance of `SummableVonMangoldtLogPow`. -/
theorem summable_twisted_vonMangoldt_log {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) (j : ℕ) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod N) : ℂ) * (n : ℂ) ^ (-s) * (-(Real.log n : ℂ)) ^ j) := by
  have hsum : Summable (fun n : ℕ =>
      ArithmeticFunction.vonMangoldt n * (Real.log (n : ℝ)) ^ j / (n : ℝ) ^ (s.re)) :=
    Work.ZeroFreeTables.P3.SummableVonMangoldtLogPow hs j
  refine Summable.of_norm_bounded hsum ?_
  intro n
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    have hΛ0 : ArithmeticFunction.vonMangoldt 0 = 0 := by
      have h := ArithmeticFunction.vonMangoldt_le_log (n := 0)
      simp only [Nat.cast_zero, Real.log_zero] at h
      exact le_antisymm h ArithmeticFunction.vonMangoldt_nonneg
    simp [hΛ0]
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    have hA : ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ = ArithmeticFunction.vonMangoldt n :=
      Complex.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg
    have hχ : ‖(χ (n : ZMod N) : ℂ)‖ ≤ 1 := χ.norm_le_one _
    have hC : ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
      rw [show (n : ℂ) = ((n : ℝ) : ℂ) from (Complex.ofReal_natCast n).symm]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hnpos (-s), Complex.neg_re]
    have hD : ‖(-(Real.log (n : ℝ) : ℂ)) ^ j‖ = (Real.log (n : ℝ)) ^ j := by
      rw [norm_pow, norm_neg, Complex.norm_of_nonneg hlog_nonneg]
    rw [norm_mul, norm_mul, norm_mul, hA, hC, hD]
    calc ArithmeticFunction.vonMangoldt n * ‖(χ (n : ZMod N) : ℂ)‖ * (n : ℝ) ^ (-s.re)
            * (Real.log (n : ℝ)) ^ j
        ≤ ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-s.re) * (Real.log (n : ℝ)) ^ j := by
          apply mul_le_mul_of_nonneg_right
          · apply mul_le_mul_of_nonneg_right
            · simpa using
                mul_le_mul_of_nonneg_left hχ ArithmeticFunction.vonMangoldt_nonneg
            · exact le_of_lt (Real.rpow_pos_of_pos hnpos (-s.re))
          · exact pow_nonneg hlog_nonneg j
      _ = ArithmeticFunction.vonMangoldt n * (Real.log (n : ℝ)) ^ j / (n : ℝ) ^ (s.re) := by
          rw [Real.rpow_neg hnpos.le, div_eq_mul_inv]
          ring

end Work.ZeroFreeTables.P9.prim
