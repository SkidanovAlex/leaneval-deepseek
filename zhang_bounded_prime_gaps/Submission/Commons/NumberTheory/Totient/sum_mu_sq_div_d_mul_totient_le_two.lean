import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.NormNum.BigOperators
import Submission.Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors

open scoped BigOperators
open Finset

namespace Commons.NumberTheory.Totient

noncomputable section

/-- The summand `μ(d)² / (d · φ(d))` of the statement, as a real number. -/
private def term (d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2 / ((d : ℝ) * (Nat.totient d : ℝ))

/-- The tail factor `1/(p(p-1))` for a prime `p`. -/
private def x (p : ℕ) : ℝ := 1 / ((p : ℝ) * ((p : ℝ) - 1))

private lemma term_eq (d : ℕ) :
    term d = ((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2 / ((d : ℝ) * (Nat.totient d : ℝ)) :=
  rfl

private lemma term_one : term 1 = 1 := by
  simp [term]

private lemma term_nonneg (d : ℕ) : 0 ≤ term d := by
  unfold term
  exact div_nonneg (by positivity) (by positivity)

private lemma term_mul_of_coprime (a b : ℕ) (h : Nat.Coprime a b) :
    term (a * b) = term a * term b := by
  have hmu : ArithmeticFunction.moebius (a * b)
      = ArithmeticFunction.moebius a * ArithmeticFunction.moebius b :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (Nat.coprime_iff_gcd_eq_one.mp h)
  have hφ : Nat.totient (a * b) = Nat.totient a * Nat.totient b := Nat.totient_mul h
  unfold term
  rw [hmu, hφ]
  push_cast
  rw [mul_pow]
  ring_nf

private lemma term_prime_pow (p k : ℕ) (hp : Nat.Prime p) (hk : 2 ≤ k) : term (p ^ k) = 0 := by
  unfold term
  have hmu : ArithmeticFunction.moebius (p ^ k) = 0 := by
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
    simp [show k ≠ 1 by omega]
  rw [hmu]
  simp

private lemma term_prime (p : ℕ) (hp : Nat.Prime p) : term p = x p := by
  unfold term x
  rw [ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp]
  rw [Nat.cast_sub hp.one_le]
  norm_num

/-- For a prime `p`, `x p ≥ 0`. -/
private lemma x_nonneg_of_prime {p : ℕ} (hp : Nat.Prime p) : 0 ≤ x p := by
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  unfold x
  exact div_nonneg (by norm_num) (by nlinarith)

private lemma one_add_x_nonneg_of_prime {p : ℕ} (hp : Nat.Prime p) : 0 ≤ 1 + x p := by
  have := x_nonneg_of_prime hp
  linarith

private lemma one_le_one_add_x_of_prime {p : ℕ} (hp : Nat.Prime p) : 1 ≤ 1 + x p := by
  have := x_nonneg_of_prime hp
  linarith

/-- Prime factor set of `N!` is the set of primes `≤ N`. -/
private lemma primeFactors_factorial (N : ℕ) :
    (N.factorial).primeFactors = (Finset.Icc 1 N).filter Nat.Prime := by
  ext p
  rw [Nat.mem_primeFactors, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hp, hdvd, _⟩
    exact ⟨⟨hp.one_le, hp.dvd_factorial.mp hdvd⟩, hp⟩
  · rintro ⟨⟨h1, hle⟩, hp⟩
    exact ⟨hp, hp.dvd_factorial.mpr hle, Nat.factorial_ne_zero N⟩

/-- Product form of the union bound: `∏(1 + xᵢ) ≤ 1/(1 - ∑ xᵢ)` for `xᵢ ≥ 0`
with `∑ xᵢ < 1`. -/
private lemma prod_one_add_le_inv_one_sub_sum (s : Finset ℕ) (x : ℕ → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (h : ∑ i ∈ s, x i < 1) :
    ∏ i ∈ s, (1 + x i) ≤ 1 / (1 - ∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hxa : 0 ≤ x a := hx a (Finset.mem_insert_self a t)
    have hxt : ∀ i ∈ t, 0 ≤ x i := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hS : 0 ≤ ∑ i ∈ t, x i := Finset.sum_nonneg hxt
    have hh : x a + ∑ i ∈ t, x i < 1 := by simpa [Finset.sum_insert ha] using h
    have hsumt : ∑ i ∈ t, x i < 1 := by linarith
    have ih' := ih hxt hsumt
    have hden1 : 0 < 1 - ∑ i ∈ t, x i := by linarith
    have hden2 : 0 < 1 - (x a + ∑ i ∈ t, x i) := by linarith
    calc (1 + x a) * ∏ i ∈ t, (1 + x i)
        ≤ (1 + x a) * (1 / (1 - ∑ i ∈ t, x i)) :=
          mul_le_mul_of_nonneg_left ih' (by linarith)
      _ ≤ 1 / (1 - (x a + ∑ i ∈ t, x i)) := by
          rw [mul_one_div, div_le_div_iff₀ hden1 hden2]
          nlinarith [mul_nonneg hxa hxa, mul_nonneg hxa hS]

/-- `1/(n(n-1)) = 1/(n-1) - 1/n` for `n ≥ 2`. -/
private lemma inv_mul_pred (n : ℕ) (hn : 2 ≤ n) :
    (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) = 1 / ((n : ℝ) - 1) - 1 / (n : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  field_simp
  ring

/-- Telescoping bound: `∑_{102 ≤ n ≤ M} 1/(n(n-1)) ≤ 1/101`. -/
private lemma sum_Icc_102_inv_mul_pred_le (M : ℕ) :
    (∑ n ∈ Finset.Icc 102 M, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤ 1 / 101 := by
  have key : ∀ k : ℕ,
      (∑ n ∈ Finset.Icc 102 (102 + k), (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
        = 1 / 101 - 1 / ((102 + k : ℕ) : ℝ) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      simp only [Nat.add_succ]
      rw [Finset.sum_Icc_succ_top (a := 102) (b := 102 + k) (by omega)]
      rw [ih]
      have hterm : (1 : ℝ)
            / ((((102 + k + 1 : ℕ)) : ℝ) * ((((102 + k + 1 : ℕ)) : ℝ) - 1))
          = 1 / ((102 + k : ℕ) : ℝ) - 1 / ((102 + k + 1 : ℕ) : ℝ) := by
        have hm : (((102 + k + 1 : ℕ)) : ℝ) - 1 = ((102 + k : ℕ) : ℝ) := by
          push_cast; ring
        rw [inv_mul_pred (102 + k + 1) (by omega), hm]
      rw [hterm]
      ring
  by_cases hM : 102 ≤ M
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hM
    rw [key k]
    have hpos : (0 : ℝ) < 1 / ((102 + k : ℕ) : ℝ) := by positivity
    linarith
  · push Not at hM
    rw [Finset.Icc_eq_empty_of_lt hM]
    norm_num

/-- The product over the primes `≤ 101` is below `2/(101/100)`. -/
private lemma prod_primes_101 :
    (∏ p ∈ (Finset.Icc 1 101).filter Nat.Prime, (1 + x p)) * (101 / 100) < 2 := by
  have heq : (Finset.Icc 1 101).filter Nat.Prime =
      ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79,
        83, 89, 97, 101} : Finset ℕ) := by decide
  rw [heq]
  norm_num [x]

/-- `∏_{p prime ≤ N} (1 + 1/(p(p-1))) ≤ 2`. -/
private lemma prod_primes_le_two (N : ℕ) :
    (∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 + x p)) ≤ 2 := by
  set A : Finset ℕ := (Finset.Icc 1 N).filter Nat.Prime with hA
  -- factor 1: primes `≤ 101`, bounded by the explicit product.
  have hsub1 : A.filter (fun p => p ≤ 101) ⊆ (Finset.Icc 1 101).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, hA, Finset.mem_Icc] at hp ⊢
    obtain ⟨⟨⟨h1, _⟩, hpp⟩, hle⟩ := hp
    exact ⟨⟨h1, hle⟩, hpp⟩
  have hf1 : (∏ p ∈ A.filter (fun p => p ≤ 101), (1 + x p))
      ≤ ∏ p ∈ (Finset.Icc 1 101).filter Nat.Prime, (1 + x p) := by
    apply Finset.prod_le_prod_of_subset_of_one_le₀ hsub1
    · intro p hp
      exact one_add_x_nonneg_of_prime (by
        simp only [Finset.mem_filter, hA, Finset.mem_Icc] at hp
        exact hp.1.2)
    · intro p hp _
      exact one_le_one_add_x_of_prime (Finset.mem_filter.mp hp).2
  -- factor 2: primes `> 101`.
  set B : Finset ℕ := A.filter (fun p => ¬ p ≤ 101) with hB
  have hBprime : ∀ p ∈ B, Nat.Prime p := by
    intro p hp
    simp only [hB, Finset.mem_filter, hA, Finset.mem_Icc] at hp
    exact hp.1.2
  have hBx : ∀ p ∈ B, 0 ≤ x p := fun p hp => x_nonneg_of_prime (hBprime p hp)
  have hBsum : ∑ p ∈ B, x p ≤ 1 / 101 := by
    have hsubB : B ⊆ Finset.Icc 102 N := by
      intro p hp
      simp only [hB, Finset.mem_filter, hA, Finset.mem_Icc] at hp
      obtain ⟨⟨⟨_, hN⟩, _⟩, hgt⟩ := hp
      exact Finset.mem_Icc.mpr ⟨by omega, hN⟩
    have hstep : ∑ p ∈ B, x p ≤ ∑ n ∈ Finset.Icc 102 N, x n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubB (fun n hn _ => by
        have hn102 : 102 ≤ n := (Finset.mem_Icc.mp hn).1
        have h2 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
        unfold x
        exact div_nonneg (by norm_num) (by nlinarith))
    exact le_trans hstep (sum_Icc_102_inv_mul_pred_le N)
  have hBlt : ∑ p ∈ B, x p < 1 := by linarith
  have hf2 : ∏ p ∈ B, (1 + x p) ≤ 101 / 100 := by
    have hprod := prod_one_add_le_inv_one_sub_sum B x hBx hBlt
    have hden : (1 : ℝ) - 1 / 101 ≤ 1 - ∑ p ∈ B, x p := by linarith
    have hpos : (0 : ℝ) < 1 - 1 / 101 := by norm_num
    have hle := one_div_le_one_div_of_le hpos hden
    calc ∏ p ∈ B, (1 + x p) ≤ 1 / (1 - ∑ p ∈ B, x p) := hprod
      _ ≤ 1 / (1 - 1 / 101) := hle
      _ = 101 / 100 := by norm_num
  -- combine
  have hC := prod_primes_101
  have hf1nn : 0 ≤ ∏ p ∈ A.filter (fun p => p ≤ 101), (1 + x p) :=
    Finset.prod_nonneg (fun p hp => one_add_x_nonneg_of_prime (by
      simp only [Finset.mem_filter, hA, Finset.mem_Icc] at hp
      exact hp.1.2))
  have hCnn : 0 ≤ ∏ p ∈ (Finset.Icc 1 101).filter Nat.Prime, (1 + x p) :=
    Finset.prod_nonneg (fun p hp => one_add_x_nonneg_of_prime (Finset.mem_filter.mp hp).2)
  have hf2nn : 0 ≤ ∏ p ∈ A.filter (fun p => ¬ p ≤ 101), (1 + x p) :=
    Finset.prod_nonneg (fun p hp => one_add_x_nonneg_of_prime (by
      simp only [Finset.mem_filter, hA, Finset.mem_Icc] at hp
      exact hp.1.2))
  rw [← Finset.prod_filter_mul_prod_filter_not A (fun p => p ≤ 101) (fun p => 1 + x p)]
  calc (∏ p ∈ A.filter (fun p => p ≤ 101), (1 + x p))
        * ∏ p ∈ A.filter (fun p => ¬ p ≤ 101), (1 + x p)
      ≤ (∏ p ∈ (Finset.Icc 1 101).filter Nat.Prime, (1 + x p)) * (101 / 100) :=
        mul_le_mul hf1 hf2 hf2nn hCnn
    _ ≤ 2 := le_of_lt hC

theorem sum_mu_sq_div_d_mul_totient_le_two (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2 / ((d : ℝ) * (Nat.totient d : ℝ)))
      ≤ 2 := by
  change (∑ d ∈ Finset.Icc 1 N, term d) ≤ 2
  calc (∑ d ∈ Finset.Icc 1 N, term d)
      ≤ ∑ d ∈ (N.factorial).divisors, term d := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro d hd
          have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
          have hdN : d ≤ N := (Finset.mem_Icc.mp hd).2
          rw [Nat.mem_divisors]
          exact ⟨Nat.dvd_factorial (by omega) hdN, Nat.factorial_ne_zero N⟩
        · intro d _ _
          exact term_nonneg d
    _ = ∏ p ∈ (N.factorial).primeFactors, (1 + term p) :=
        (Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors term (N.factorial)
          (Nat.factorial_ne_zero N) term_one term_mul_of_coprime term_prime_pow).symm
    _ = ∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 + x p) := by
        rw [primeFactors_factorial N]
        apply Finset.prod_congr rfl
        intro p hp
        rw [term_prime p (Finset.mem_filter.mp hp).2]
    _ ≤ 2 := prod_primes_le_two N

end

end Commons.NumberTheory.Totient