import Mathlib
import Submission.Commons.NumberTheory.Zeta.summable_vonMangoldt_div_rpow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.Zeta

open scoped BigOperators

/-! For `σ > 1` and `x > 0`, the weighted von Mangoldt series
`∑ Λ(n) · (x / n) ^ σ` converges absolutely (all terms are nonnegative).

This is the elementary (real) version of the convergence of the Dirichlet series
of `Λ`, obtained from `summable_vonMangoldt_div_rpow` by extracting the constant
factor `x ^ σ` from the `n`-th term. -/

theorem summable_vonMangoldt_mul_rpow {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * ((x / (n : ℝ)) ^ σ)) := by
  -- the unweighted series `Λ n / n ^ σ` is summable for σ > 1
  have hg : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ) :=
    summable_vonMangoldt_div_rpow hσ
  -- pointwise identity: `Λ n * (x / n) ^ σ = x ^ σ * (Λ n / n ^ σ)`
  have hEq : ∀ n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * ((x / (n : ℝ)) ^ σ) =
      x ^ σ * ((ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ) := by
    intro n
    by_cases hn : n = 0
    · subst n
      have hΛ0 : (ArithmeticFunction.vonMangoldt 0 : ℝ) = 0 := by simp
      simp [hΛ0]
    · have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
      have hdiv : (x / (n : ℝ)) ^ σ = x ^ σ / (n : ℝ) ^ σ :=
        Real.div_rpow (le_of_lt hx) (le_of_lt hnpos) σ
      rw [hdiv]
      have hnσ : (n : ℝ) ^ σ ≠ 0 := (Real.rpow_pos_of_pos hnpos σ).ne'
      field_simp [hnσ]
  -- multiplying a summable series by the constant `x ^ σ` keeps it summable
  have hsum : Summable (fun n : ℕ => x ^ σ * ((ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ)) :=
    Summable.mul_left (x ^ σ) hg
  exact (summable_congr hEq).mpr hsum

end Commons.NumberTheory.Zeta
