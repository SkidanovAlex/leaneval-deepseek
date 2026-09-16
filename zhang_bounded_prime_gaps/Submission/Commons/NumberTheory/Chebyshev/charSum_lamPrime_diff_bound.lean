import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

open scoped ArithmeticFunction
open Finset
open Real

noncomputable section

namespace Commons.NumberTheory.Chebyshev

/-! Helpers are kept in a nested namespace so that this module does not redeclare
top-level constants of `Commons.NumberTheory.Chebyshev` that may live in other
commmons modules. -/

namespace CharSumLamPrime

/-- `ψ x - θ x` equals the sum of `Λ` over the non-primes up to `x`
    (i.e. over the prime powers with exponent `≥ 2`). -/
lemma psi_sub_theta_eq_sum_nonprime (x : ℝ) :
    Chebyshev.psi x - Chebyshev.theta x =
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with ¬ n.Prime, ArithmeticFunction.vonMangoldt n) := by
  have hpsi : Chebyshev.psi x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n := rfl
  have htheta : Chebyshev.theta x =
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with n.Prime, Real.log (n : ℝ) := rfl
  have hprime : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with n.Prime, ArithmeticFunction.vonMangoldt n)
      = (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with n.Prime, Real.log (n : ℝ)) := by
    apply Finset.sum_congr rfl
    intro n hn
    exact ArithmeticFunction.vonMangoldt_apply_prime (by simpa using (Finset.mem_filter.mp hn).2)
  calc
    Chebyshev.psi x - Chebyshev.theta x
        = (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n)
            - (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with n.Prime, Real.log (n : ℝ)) := by rw [hpsi, htheta]
    _ = ((∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with n.Prime, ArithmeticFunction.vonMangoldt n) +
          (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with ¬ n.Prime, ArithmeticFunction.vonMangoldt n))
            - (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with n.Prime, Real.log (n : ℝ)) := by
          rw [Finset.sum_filter_add_sum_filter_not]
    _ = (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with ¬ n.Prime, ArithmeticFunction.vonMangoldt n) := by
          rw [hprime]; ring

/-- Finset identity: the `(a, b]` band equals `(0, b]` minus `(0, a]`. -/
lemma Ioc_band_eq_sdiff {a b : ℕ} (_hab : a ≤ b) :
    Finset.Ioc a b = (Finset.Ioc 0 b) \ (Finset.Ioc 0 a) := by
  ext n
  simp only [Finset.mem_sdiff, Finset.mem_Ioc]
  omega

/-- Plain sums over the `(a, b]` band equal the difference of the `(0, b]` and `(0, a]` sums. -/
lemma sum_Ioc_band_eq_sub {a b : ℕ} (hab : a ≤ b) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.Ioc a b, f n) =
      (∑ n ∈ Finset.Ioc 0 b, f n) - (∑ n ∈ Finset.Ioc 0 a, f n) := by
  have hsubset : Finset.Ioc 0 a ⊆ Finset.Ioc 0 b := by
    intro n hn
    exact Finset.mem_Ioc.mpr
      ⟨(Finset.mem_Ioc.mp hn).1, le_trans (Finset.mem_Ioc.mp hn).2 hab⟩
  have hsd := Finset.sum_sdiff (s₁ := Finset.Ioc 0 a) (s₂ := Finset.Ioc 0 b) (f := f) hsubset
  rw [← Ioc_band_eq_sdiff hab] at hsd
  calc
    (∑ n ∈ Finset.Ioc a b, f n)
        = ((∑ n ∈ Finset.Ioc a b, f n) + (∑ n ∈ Finset.Ioc 0 a, f n)) -
            (∑ n ∈ Finset.Ioc 0 a, f n) := by ring
    _ = (∑ n ∈ Finset.Ioc 0 b, f n) - (∑ n ∈ Finset.Ioc 0 a, f n) := by rw [hsd]

/-- Filtered sum over the `(a, b]` band = difference of the filtered `(0, b]` and `(0, a]` sums. -/
lemma sum_filter_Ioc_band_eq_sub {a b : ℕ} (hab : a ≤ b) (p : ℕ → Prop) [DecidablePred p]
    (f : ℕ → ℝ) :
    (∑ n ∈ Finset.Ioc a b with p n, f n) =
      (∑ n ∈ Finset.Ioc 0 b with p n, f n) - (∑ n ∈ Finset.Ioc 0 a with p n, f n) := by
  simp only [sum_filter]
  exact sum_Ioc_band_eq_sub hab (fun n => if p n then f n else 0)

/-- The `(a, b]` band difference of `ψ - θ` equals the `Λ`-sum over non-primes in `(a, b]`. -/
lemma psi_sub_theta_band {a b : ℕ} (hab : a ≤ b) :
    (Chebyshev.psi (b : ℝ) - Chebyshev.theta (b : ℝ)) -
      (Chebyshev.psi (a : ℝ) - Chebyshev.theta (a : ℝ)) =
      (∑ n ∈ Finset.Ioc a b with ¬ n.Prime, ArithmeticFunction.vonMangoldt n) := by
  rw [psi_sub_theta_eq_sum_nonprime (b : ℝ), psi_sub_theta_eq_sum_nonprime (a : ℝ)]
  simp only [Nat.floor_natCast]
  rw [← sum_filter_Ioc_band_eq_sub hab (fun n => ¬ n.Prime)
    (fun n => ArithmeticFunction.vonMangoldt n)]

/-- Summing `χ·Λ` over `(a,b]` and subtracting the sum of `χ·log` over the primes in `(a,b]`
    leaves only the non-prime (prime-power) terms. -/
lemma charSum_sub_primeLog_eq_nonprime (a b : ℕ) (χ : ℕ → ℝ) :
    (∑ n ∈ Finset.Ioc a b, χ n * ArithmeticFunction.vonMangoldt n) -
      (∑ p ∈ Finset.Ioc a b with p.Prime, χ p * Real.log (p : ℝ)) =
      (∑ n ∈ Finset.Ioc a b with ¬ n.Prime, χ n * ArithmeticFunction.vonMangoldt n) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Ioc a b) (fun n : ℕ => n.Prime)
    (fun n : ℕ => χ n * ArithmeticFunction.vonMangoldt n)
  have hprime : (∑ n ∈ Finset.Ioc a b with n.Prime, χ n * ArithmeticFunction.vonMangoldt n)
      = (∑ p ∈ Finset.Ioc a b with p.Prime, χ p * Real.log (p : ℝ)) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by simpa using (Finset.mem_filter.mp hn).2)]
  calc
    (∑ n ∈ Finset.Ioc a b, χ n * ArithmeticFunction.vonMangoldt n) -
        (∑ p ∈ Finset.Ioc a b with p.Prime, χ p * Real.log (p : ℝ))
        = ((∑ n ∈ Finset.Ioc a b with n.Prime, χ n * ArithmeticFunction.vonMangoldt n) +
            (∑ n ∈ Finset.Ioc a b with ¬ n.Prime, χ n * ArithmeticFunction.vonMangoldt n))
              - (∑ p ∈ Finset.Ioc a b with p.Prime, χ p * Real.log (p : ℝ)) := by
          rw [hsplit]
    _ = (∑ n ∈ Finset.Ioc a b with ¬ n.Prime, χ n * ArithmeticFunction.vonMangoldt n) := by
          rw [hprime]; ring

/-- The `(ψ − θ)(b) − (ψ − θ)(a)` band difference is nonnegative. -/
lemma psi_sub_theta_band_nonneg {a b : ℕ} (hab : a ≤ b) :
    0 ≤ (Chebyshev.psi (b : ℝ) - Chebyshev.theta (b : ℝ)) -
      (Chebyshev.psi (a : ℝ) - Chebyshev.theta (a : ℝ)) := by
  rw [psi_sub_theta_band hab]
  apply Finset.sum_nonneg
  intro n hn
  exact ArithmeticFunction.vonMangoldt_nonneg (n := n)

/-- Bound for `|χ| ≤ 1`: the absolute value of the `Λ`-sum minus prime-log-sum over `(a,b]`
    is ≤ the band difference of `ψ − θ`. -/
lemma charSum_sub_primeLog_bound {a b : ℕ} (hab : a ≤ b) (χ : ℕ → ℝ)
    (hχ : ∀ n, |χ n| ≤ 1) :
    |(∑ n ∈ Finset.Ioc a b, χ n * ArithmeticFunction.vonMangoldt n) -
      (∑ p ∈ Finset.Ioc a b with p.Prime, χ p * Real.log (p : ℝ))|
      ≤ (Chebyshev.psi (b : ℝ) - Chebyshev.theta (b : ℝ)) -
        (Chebyshev.psi (a : ℝ) - Chebyshev.theta (a : ℝ)) := by
  rw [charSum_sub_primeLog_eq_nonprime a b χ]
  calc
    |∑ n ∈ Finset.Ioc a b with ¬ n.Prime, χ n * ArithmeticFunction.vonMangoldt n|
        ≤ ∑ n ∈ Finset.Ioc a b with ¬ n.Prime, |χ n * ArithmeticFunction.vonMangoldt n| :=
          abs_sum_le_sum_abs _ _
    _ = ∑ n ∈ Finset.Ioc a b with ¬ n.Prime, |χ n| * ArithmeticFunction.vonMangoldt n := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [abs_mul, abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))]
    _ ≤ ∑ n ∈ Finset.Ioc a b with ¬ n.Prime, ArithmeticFunction.vonMangoldt n := by
          apply Finset.sum_le_sum
          intro n hn
          exact mul_le_of_le_one_left (ArithmeticFunction.vonMangoldt_nonneg (n := n)) (hχ n)
    _ = (Chebyshev.psi (b : ℝ) - Chebyshev.theta (b : ℝ)) -
        (Chebyshev.psi (a : ℝ) - Chebyshev.theta (a : ℝ)) := by
          rw [psi_sub_theta_band hab]

end CharSumLamPrime

open CharSumLamPrime

/--
The absolute value of the difference between the character-weighted von Mangoldt sum and the
character-weighted prime-log sum over the band `(a, b]` is bounded by the band difference of
`ψ − θ`.
-/
theorem charSum_lamPrime_diff_bound {a b : ℕ} (hab : a ≤ b) (χ : ℕ → ℝ)
    (hχ : ∀ n, |χ n| ≤ 1) :
    |(∑ n ∈ Finset.Ioc a b, χ n * ArithmeticFunction.vonMangoldt n) -
      (∑ p ∈ Finset.Ioc a b with p.Prime, χ p * Real.log (p : ℝ))|
      ≤ (Chebyshev.psi (b : ℝ) - Chebyshev.theta (b : ℝ)) -
        (Chebyshev.psi (a : ℝ) - Chebyshev.theta (a : ℝ)) := by
  exact charSum_sub_primeLog_bound hab χ hχ

end Commons.NumberTheory.Chebyshev
