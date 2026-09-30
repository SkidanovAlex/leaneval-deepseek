import Mathlib.NumberTheory.LSeries.Dirichlet

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.Zeta

/-! The Dirichlet series of the von Mangoldt function `Λ` converges absolutely for `σ > 1`.

The key input from Mathlib is `ArithmeticFunction.LSeriesSummable_vonMangoldt`, which states
that the complex L-series of `Λ` converges absolutely whenever `1 < s.re`.  Taking
`s = σ : ℂ`, the norm of the `n`-th term is exactly `Λ n / n ^ σ`, so the real-valued
series converges. -/

open scoped BigOperators

theorem summable_vonMangoldt_div_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ) := by
  let v : ℕ → ℂ := fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
  -- absolute convergence of the complex L-series of Λ at `σ : ℂ`
  have hL := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ)) (by simpa using hσ)
  -- the series of norms converges
  have hsum : Summable (fun n : ℕ => ‖LSeries.term v (σ : ℂ) n‖) := by
    simpa [v] using (summable_norm_iff.mpr hL)
  -- and its terms are exactly `Λ n / n ^ σ`
  have hterm : ∀ n : ℕ, ‖LSeries.term v (σ : ℂ) n‖ =
      (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ := by
    intro n
    rw [LSeries.norm_term_eq]
    by_cases hn : n = 0
    · rw [if_pos hn]
      simp only [hn, Nat.cast_zero]
      have hz : (0 : ℝ) ^ σ = 0 := Real.zero_rpow (by linarith)
      simp [hz]
    · rw [if_neg hn]
      simp only [Complex.ofReal_re]
      have hnorm : ‖v n‖ = (ArithmeticFunction.vonMangoldt n : ℝ) := by
        dsimp [v]
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg)
      rw [hnorm]
  exact (summable_congr hterm).mp hsum

end Commons.NumberTheory.Zeta