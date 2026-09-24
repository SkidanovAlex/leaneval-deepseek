import Mathlib
import Submission.Commons.NumberTheory.Zeta.psi_sub_id_powLog_real

open Filter Finset
open scoped BigOperators

namespace Commons.NumberTheory.PrimeNumberTheorem

/-!
# `ψ(x) − x` is bounded by any power of `1/log x`

The target theorem: for every `A > 0`, eventually (in the natural `x`)

`|∑_{n ≤ x} Λ(n) − x| ≤ x / (log x)^A`,

i.e. the Chebyshev–von-Mangoldt function `ψ(x) := ∑_{n ≤ x} Λ(n)` satisfies
`ψ(x) = x + O_A(x / (log x)^A)` for every positive `A`.

This is the classical Prime Number Theorem with error term (de la Vallée
Poussin: `ψ(x) − x ≪ x·exp(−c√(log x))`, which beats every power of `log x`).
The analytic input is provided (in `Chebyshev.psi` form over real `x`) by
`Commons.NumberTheory.Zeta.psi_sub_id_powLog_real`; this file supplies the
purely arithmetic/order-theoretic glue turning that real-`x` bound into the
eventual statement over the explicit natural-`x` partial sums above.
-/

/-- `Finset.range (x+1) = {0, 1, …, x}`. -/
private lemma range_eq_Icc_zero (x : ℕ) :
    (Finset.range (x + 1) : Finset ℕ) = Finset.Icc 0 x := by
  ext n
  simp only [mem_range, mem_Icc]
  omega

/-- `{0, …, x} = {0} ∪ {1, …, x}`. -/
private lemma Icc_zero_eq_insert (x : ℕ) :
    Finset.Icc 0 x = insert 0 (Finset.Icc 1 x) := by
  ext n
  simp only [mem_insert, mem_Icc]
  omega

/-- For a natural `x`, Mathlib's `Chebyshev.psi (x : ℝ) = ∑_{n ≤ x} Λ n` equals
the explicit sum over `Finset.range (x+1)` appearing in the target statement
(`Λ 0 = Λ 1 = 0`, and the ranges `{0,…,x}` and `{1,…,x}` differ only by `0`). -/
private lemma psi_nat_eq_sum_range (x : ℕ) :
    Chebyshev.psi (x : ℝ) =
      ∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n := by
  let f : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n
  have hfl : ⌊(x : ℝ)⌋₊ = x := Nat.floor_natCast x
  have hIoc : (Finset.Ioc 0 x : Finset ℕ) = Finset.Icc 1 x := by
    ext n
    simp only [mem_Ioc, mem_Icc]
    omega
  calc
    Chebyshev.psi (x : ℝ) = ∑ n ∈ Finset.Ioc 0 x, f n := by
      unfold Chebyshev.psi
      simp [hfl, f]
    _ = ∑ n ∈ Finset.Icc 1 x, f n := by rw [hIoc]
    _ = ∑ n ∈ Finset.range (x + 1), f n := by
      rw [range_eq_Icc_zero x]
      rw [Icc_zero_eq_insert x]
      rw [Finset.sum_insert (by simp : (0 : ℕ) ∉ Finset.Icc 1 x)]
      have hf0 : f 0 = 0 := by simp [f]
      rw [hf0]
      simp
    _ = ∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n := by simp [f]

/-- Reduce the eventual bound over naturals to the real-`x` bound on `Chebyshev.psi`. -/
private theorem psi_sub_id_powLog_of_real
    (hreal : ∀ A : ℝ, 0 < A → ∃ x₀ : ℝ,
      ∀ x : ℝ, x₀ ≤ x → |Chebyshev.psi x - x| ≤ x / (Real.log x) ^ A) :
    ∀ A : ℝ, 0 < A → ∀ᶠ x : ℕ in Filter.atTop,
      |(∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n) - (x : ℝ)|
        ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
  intro A hA
  rcases hreal A hA with ⟨x₀, hx₀⟩
  let y : ℝ := max x₀ 2
  rcases exists_nat_ge y with ⟨N, hN⟩
  rw [Filter.eventually_atTop]
  refine ⟨N, ?_⟩
  intro n hn
  have hyge : y ≤ (n : ℝ) := le_trans hN (by exact_mod_cast hn)
  have hx₀n : x₀ ≤ (n : ℝ) := le_trans (le_max_left x₀ 2) hyge
  have hb := hx₀ (n : ℝ) hx₀n
  simpa [psi_nat_eq_sum_range n] using hb

theorem psi_sub_id_powLog :
    ∀ A : ℝ, 0 < A →
    ∀ᶠ x : ℕ in Filter.atTop,
      |(∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n) - (x : ℝ)|
        ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A :=
  psi_sub_id_powLog_of_real Commons.NumberTheory.Zeta.psi_sub_id_powLog_real

end Commons.NumberTheory.PrimeNumberTheorem
