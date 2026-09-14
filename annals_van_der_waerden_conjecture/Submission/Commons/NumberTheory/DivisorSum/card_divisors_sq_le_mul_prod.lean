import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.IntervalCases

namespace Commons.NumberTheory.DivisorSum

private lemma odd_key (p : ℕ) (hp : 3 ≤ p) :
    ∀ a : ℕ, 1 ≤ a → (a + 1)^2 * p ≤ 4 * p^a := by
  intro a ha
  induction a, ha using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h1 : (n + 2)^2 ≤ 3 * (n + 1)^2 := by nlinarith
    have h2 : 3 * (4 * p^n) ≤ 4 * p^(n+1) := by
      have hp' : 12 ≤ 4 * p := by omega
      calc 3 * (4 * p^n) = 12 * p^n := by ring
        _ ≤ (4*p) * p^n := Nat.mul_le_mul_right _ hp'
        _ = 4 * p^(n+1) := by rw [pow_succ]; ring
    calc (n + 1 + 1)^2 * p
        = (n + 2)^2 * p := by ring
      _ ≤ (3 * (n + 1)^2) * p := Nat.mul_le_mul_right _ h1
      _ = 3 * ((n + 1)^2 * p) := by ring
      _ ≤ 3 * (4 * p^n) := Nat.mul_le_mul_left _ ih
      _ ≤ 4 * p ^ (n+1) := h2

private lemma two_key : ∀ a : ℕ, 1 ≤ a → 4 * (a + 1)^2 ≤ 9 * 2^a := by
  intro a ha
  induction a, ha using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rcases lt_or_ge n 2 with h | h
    · interval_cases n
      norm_num
    · have h1 : 4 * (n + 2)^2 ≤ 2 * (4 * (n + 1)^2) := by nlinarith
      have h2 : 2 * (4 * (n + 1)^2) ≤ 2 * (9 * 2^n) := Nat.mul_le_mul_left 2 ih
      have h3 : 2 * (9 * 2^n) = 9 * 2^(n+1) := by rw [pow_succ]; ring
      calc 4 * (n + 1 + 1)^2 = 4 * (n + 2)^2 := by ring
        _ ≤ 2 * (4 * (n + 1)^2) := h1
        _ ≤ 2 * (9 * 2^n) := h2
        _ = 9 * 2^(n+1) := h3

theorem card_divisors_sq_le_mul_prod (n : ℕ) (hn : n ≠ 0) :
    ((Nat.divisors n).card : ℝ) ^ 2
      ≤ (n : ℝ) * ∏ q ∈ n.primeFactors, (if q = 2 then (9 : ℝ) / 4 else 4 / (q : ℝ)) := by
  have hcard : ((n.divisors.card : ℕ) : ℝ)
      = ∏ q ∈ n.primeFactors, ((n.factorization q + 1 : ℕ) : ℝ) := by
    rw [Nat.card_divisors hn, Nat.cast_prod]
  have hpow : (n : ℝ) = ∏ q ∈ n.primeFactors, (q : ℝ) ^ n.factorization q := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
    rw [Nat.cast_prod]
    simp only [Nat.cast_pow]
  rw [hcard, ← Finset.prod_pow]
  calc ∏ q ∈ n.primeFactors, ((n.factorization q + 1 : ℕ) : ℝ) ^ 2
      ≤ ∏ q ∈ n.primeFactors,
          ((q : ℝ) ^ n.factorization q * (if q = 2 then (9 : ℝ) / 4 else 4 / (q : ℝ))) := by
        refine Finset.prod_le_prod (fun q _ => sq_nonneg _) (fun q hq => ?_)
        rw [Nat.mem_primeFactors] at hq
        obtain ⟨hqp, hqdvd, -⟩ := hq
        have ha : 1 ≤ n.factorization q := (hqp.dvd_iff_one_le_factorization hn).mp hqdvd
        by_cases hq2 : q = 2
        · subst hq2
          simp only [if_true]
          have hk := two_key (n.factorization 2) ha
          have hkR : (4 : ℝ) * ((n.factorization 2 + 1 : ℕ) : ℝ) ^ 2
              ≤ 9 * (2 : ℝ) ^ (n.factorization 2) := by
            exact_mod_cast hk
          nlinarith [hkR]
        · rw [if_neg hq2]
          have hq2le : 2 ≤ q := hqp.two_le
          have hq3 : 3 ≤ q := by omega
          have hk := odd_key q hq3 (n.factorization q) ha
          have hkR : ((n.factorization q + 1 : ℕ) : ℝ) ^ 2 * (q : ℝ)
              ≤ 4 * (q : ℝ) ^ (n.factorization q) := by
            exact_mod_cast hk
          have hqpos : (0 : ℝ) < q := by exact_mod_cast hqp.pos
          have hmul : (q : ℝ) ^ (n.factorization q) * (4 / (q : ℝ))
              = 4 * (q : ℝ) ^ (n.factorization q) / (q : ℝ) := by ring
          rw [hmul, le_div_iff₀ hqpos]
          exact hkR
    _ = (∏ q ∈ n.primeFactors, (q : ℝ) ^ n.factorization q)
          * ∏ q ∈ n.primeFactors, (if q = 2 then (9 : ℝ) / 4 else 4 / (q : ℝ)) :=
        Finset.prod_mul_distrib
    _ = (n : ℝ) * ∏ q ∈ n.primeFactors, (if q = 2 then (9 : ℝ) / 4 else 4 / (q : ℝ)) := by
        rw [hpow]

end Commons.NumberTheory.DivisorSum