import Mathlib.NumberTheory.Chebyshev

namespace Commons.NumberTheory.ArithmeticFunction

open scoped BigOperators

/-- Second moment of the von Mangoldt function: there is `C > 0` with
`Σ_{n ≤ x} Λ(n)² ≤ C x log(2x+2)` for every `x`. -/
theorem sum_vonMangoldt_sq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ,
      ∑ n ∈ Finset.Icc 1 x, (ArithmeticFunction.vonMangoldt n) ^ 2
        ≤ C * (x : ℝ) * Real.log (2 * (x : ℝ) + 2) := by
  refine ⟨Real.log 4 + 4, ?_, fun x => ?_⟩
  · have : 0 < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  · rcases Nat.eq_zero_or_pos x with hx | hx
    · subst hx
      simp
    · have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
      have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
      have hlogx_nonneg : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg hx1
      have hCpos : 0 < Real.log 4 + 4 := by
        have : 0 < Real.log 4 := Real.log_pos (by norm_num)
        linarith
      have key : ∀ n ∈ Finset.Icc 1 x,
          (ArithmeticFunction.vonMangoldt n) ^ 2
            ≤ ArithmeticFunction.vonMangoldt n * Real.log (x : ℝ) := by
        intro n hn
        rw [Finset.mem_Icc] at hn
        obtain ⟨hn1, hnx⟩ := hn
        have hnn : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
        have hle : ArithmeticFunction.vonMangoldt n ≤ Real.log (x : ℝ) := by
          have h1 : ArithmeticFunction.vonMangoldt n ≤ Real.log (n : ℝ) :=
            ArithmeticFunction.vonMangoldt_le_log
          have h2 : Real.log (n : ℝ) ≤ Real.log (x : ℝ) := by
            apply Real.log_le_log
            · exact_mod_cast hn1
            · exact_mod_cast hnx
          linarith
        calc (ArithmeticFunction.vonMangoldt n) ^ 2
            = ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt n := by ring
          _ ≤ ArithmeticFunction.vonMangoldt n * Real.log (x : ℝ) :=
              mul_le_mul_of_nonneg_left hle hnn
      have hS : ∑ n ∈ Finset.Icc 1 x, (ArithmeticFunction.vonMangoldt n) ^ 2
          ≤ (∑ n ∈ Finset.Icc 1 x, ArithmeticFunction.vonMangoldt n) * Real.log (x : ℝ) := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum key
      have hpsi_eq : Chebyshev.psi (x : ℝ)
          = ∑ n ∈ Finset.Icc 1 x, ArithmeticFunction.vonMangoldt n := by
        rw [Chebyshev.psi]
        simp only [Nat.floor_natCast]
        congr 1
      have hpsi_le : Chebyshev.psi (x : ℝ) ≤ (Real.log 4 + 4) * (x : ℝ) :=
        Chebyshev.psi_le_const_mul_self (le_of_lt hxpos)
      calc ∑ n ∈ Finset.Icc 1 x, (ArithmeticFunction.vonMangoldt n) ^ 2
          ≤ (∑ n ∈ Finset.Icc 1 x, ArithmeticFunction.vonMangoldt n) * Real.log (x : ℝ) := hS
        _ = Chebyshev.psi (x : ℝ) * Real.log (x : ℝ) := by rw [hpsi_eq]
        _ ≤ (Real.log 4 + 4) * (x : ℝ) * Real.log (x : ℝ) :=
            mul_le_mul_of_nonneg_right hpsi_le hlogx_nonneg
        _ ≤ (Real.log 4 + 4) * (x : ℝ) * Real.log (2 * (x : ℝ) + 2) := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg (le_of_lt hCpos) (le_of_lt hxpos))
            apply Real.log_le_log hxpos
            linarith

end Commons.NumberTheory.ArithmeticFunction