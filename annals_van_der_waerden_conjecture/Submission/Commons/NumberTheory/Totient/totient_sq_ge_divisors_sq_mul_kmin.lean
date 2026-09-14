import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Submission.Commons.NumberTheory.Totient.totient_eq_prod_primeFactors

open scoped BigOperators

namespace Commons.NumberTheory.Totient

/-- For `q ≥ 3` and every `m`, `(m+2)^2 ≤ 4 q^m`.  (The `q = 2` analogue fails at
`m = 1`, which is exactly why the prime `2` needs its own constant below.) -/
theorem sq_add_two_le_four_mul_pow (q m : ℕ) (hq : 3 ≤ q) :
    ((m : ℝ) + 2)^2 ≤ 4 * (q:ℝ)^m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      have hq3 : (3:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
      have hm : (0:ℝ) ≤ (m:ℝ) := by positivity
      have h1 : ((m:ℝ)+3)^2 ≤ 3*((m:ℝ)+2)^2 := by nlinarith [sq_nonneg ((m:ℝ)+2), hm]
      have h2 : 3*((m:ℝ)+2)^2 ≤ (q:ℝ)*((m:ℝ)+2)^2 :=
        mul_le_mul_of_nonneg_right hq3 (sq_nonneg _)
      calc (((m+1 : ℕ) : ℝ) + 2)^2 = ((m:ℝ)+3)^2 := by push_cast; ring
        _ ≤ (q:ℝ)*((m:ℝ)+2)^2 := le_trans h1 h2
        _ ≤ (q:ℝ)*(4*(q:ℝ)^m) := by
              apply mul_le_mul_of_nonneg_left ih; linarith
        _ = 4*(q:ℝ)^(m+1) := by rw [pow_succ]; ring

/-- `(b+3)^2 ≤ 9·2^b` for every `b`. -/
theorem sq_add_three_le_nine_mul_two_pow (b : ℕ) :
    ((b : ℝ) + 3)^2 ≤ 9 * (2:ℝ)^b := by
  induction b with
  | zero => norm_num
  | succ b ih =>
      have hb : (0:ℝ) ≤ (b:ℝ) := by positivity
      have hstep : ((b:ℝ) + 4)^2 ≤ 2*((b:ℝ)+3)^2 := by
        nlinarith [sq_nonneg ((b:ℝ)+3), hb]
      calc (((b+1 : ℕ) : ℝ) + 3)^2 = ((b:ℝ)+4)^2 := by push_cast; ring
        _ ≤ 2*((b:ℝ)+3)^2 := hstep
        _ ≤ 2*(9*(2:ℝ)^b) := by
              apply mul_le_mul_of_nonneg_left ih; norm_num
        _ = 9*(2:ℝ)^(b+1) := by rw [pow_succ]; ring

/-- For `a ≥ 1`, `4(a+1)^2 ≤ 9·2^a`. -/
theorem four_mul_sq_le_nine_mul_two_pow (a : ℕ) (ha : 1 ≤ a) :
    4*((a:ℝ)+1)^2 ≤ 9*(2:ℝ)^a := by
  rcases eq_or_lt_of_le ha with h | h
  · subst h; norm_num
  · obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
    have hb := sq_add_three_le_nine_mul_two_pow b
    calc 4*(((b+2 : ℕ) : ℝ)+1)^2 = 4*((b:ℝ)+3)^2 := by push_cast; ring
      _ ≤ 4*(9*(2:ℝ)^b) := by
            apply mul_le_mul_of_nonneg_left hb; norm_num
      _ = 9*(2:ℝ)^(b+2) := by
            rw [pow_succ, pow_succ]; ring

/-- The per-prime-power inequality for the prime `2`: for `a ≥ 1`,
`(a+1)^2 · 2^a · (1/9) ≤ (2^(a-1))^2`. -/
theorem term_le_two (a : ℕ) (ha : 1 ≤ a) :
    ((a : ℝ) + 1)^2 * (2 : ℝ)^a * ((1 : ℝ)/9)
      ≤ ((2 : ℝ)^(a - 1) * ((2 : ℝ) - 1))^2 := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a-1, by omega⟩
  have h4 := four_mul_sq_le_nine_mul_two_pow (b+1) (by omega)
  have hz : (0:ℝ) < (2:ℝ)^b := by positivity
  have hzrel : (2:ℝ)^(b+1) = 2*(2:ℝ)^b := by rw [pow_succ]; ring
  have hrhs : ((2:ℝ)^((b+1)-1) * ((2:ℝ) - 1))^2 = ((2:ℝ)^b)^2 := by
    rw [Nat.add_sub_cancel]; norm_num
  rw [hrhs]
  nlinarith [h4, hzrel, hz]

/-- The per-prime-power inequality for an odd prime `p`: for `a ≥ 1`,
`(a+1)^2 · p^a · (p-1)^2/(4p) ≤ (p^(a-1)·(p-1))^2`. -/
theorem term_le_odd_prime (p a : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) (ha : 1 ≤ a) :
    ((a : ℝ) + 1)^2 * (p : ℝ)^a * (((p : ℝ) - 1)^2 / (4 * (p : ℝ)))
      ≤ ((p : ℝ)^(a - 1) * ((p : ℝ) - 1))^2 := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a-1, by omega⟩
  have hq : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp3
  have hp0 : (0:ℝ) < (p:ℝ) := by linarith
  have hbound : ((b:ℝ)+2)^2 ≤ 4*(p:ℝ)^b := sq_add_two_le_four_mul_pow p b hp3
  have hpb : (0:ℝ) < (p:ℝ)^b := by positivity
  have hpm : (0:ℝ) < (p:ℝ) - 1 := by linarith
  have hsq : (0:ℝ) < ((p:ℝ)-1)^2 := by positivity
  have hpow : (p:ℝ)^(b+1) = (p:ℝ)^b * (p:ℝ) := by rw [pow_succ]
  rw [hpow]
  rw [show (((b+1:ℕ):ℝ) + 1) = (b:ℝ)+2 by push_cast; ring]
  rw [show ((b+1)-1) = b by omega]
  have hL : ((b:ℝ)+2)^2 * ((p:ℝ)^b * (p:ℝ)) * (((p:ℝ)-1)^2/(4*(p:ℝ)))
      = ((b:ℝ)+2)^2 * (p:ℝ)^b * ((p:ℝ)-1)^2 / 4 := by
    field_simp [hp0.ne']
  rw [hL]
  nlinarith [hbound, hpb, hsq, mul_nonneg hpb.le hsq.le]

/-- **Main lemma.**  For every nonzero `n`,
`(τ(n))^2 · n · ∏_{q | n} c(q) ≤ φ(n)^2`, where `c(2) = 1/9` and
`c(q) = (q-1)^2/(4q)` for odd primes `q`.  This is the `k`-minimal
(rational-density) shape of the lower bound for `φ(n)^2/(n·τ(n)^2)`.

The proof is termwise: writing `n = ∏_{q ∈ primeFactors n} q^{a_q}`, Euler's
product formula gives `φ(n) = ∏_q q^{a_q-1}(q-1)` and `τ(n) = ∏_q (a_q+1)`;
the factors multiply out, and each prime-power factor is bounded by
`sq_add_two_le_four_mul_pow` (odd `q`) resp. `four_mul_sq_le_nine_mul_two_pow`
(`q = 2`). -/
theorem totient_sq_ge_divisors_sq_mul_kmin (n : ℕ) (hn : n ≠ 0) :
    ((Nat.divisors n).card : ℝ)^2 * (n : ℝ) *
        (∏ q ∈ n.primeFactors, (if q = 2 then (1 : ℝ)/9 else (((q : ℝ) - 1)^2 / (4 * (q : ℝ)))))
      ≤ ((Nat.totient n : ℝ))^2 := by
  classical
  have hA : ((Nat.divisors n).card : ℝ)
      = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
    rw [Nat.card_divisors hn]
    push_cast
    rfl
  have hN : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p) := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
    push_cast
    rfl
  have hΦ : (n.totient : ℝ)
      = ∏ p ∈ n.primeFactors,
          ((p : ℝ) ^ (n.factorization p - 1) * ((p : ℝ) - 1)) := by
    rw [totient_eq_prod_primeFactors n hn, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro p hp
    have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_le
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp1, Nat.cast_one]
  rw [hA, hN, hΦ, ← Finset.prod_pow, ← Finset.prod_pow]
  have hL : (∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) ^ 2) *
        (∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p)) *
        (∏ q ∈ n.primeFactors, (if q = 2 then (1 : ℝ)/9 else (((q : ℝ) - 1)^2 / (4 * (q : ℝ)))))
      = ∏ p ∈ n.primeFactors,
          (((n.factorization p : ℝ) + 1) ^ 2 * (p : ℝ) ^ (n.factorization p) *
            (if p = 2 then (1 : ℝ)/9 else (((p : ℝ) - 1)^2 / (4 * (p : ℝ))))) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  rw [hL]
  apply Finset.prod_le_prod
  · intro p hp
    rcases eq_or_ne p 2 with h2 | h2
    · subst h2
      rw [if_pos rfl]
      positivity
    · rw [if_neg h2]
      have hp1 : (0:ℝ) < (p:ℝ) := by
        have := (Nat.prime_of_mem_primeFactors hp).two_le
        exact_mod_cast (by omega : 0 < p)
      positivity
  · intro p hp
    obtain ⟨hpprime, hpdvd, _⟩ := Nat.mem_primeFactors.mp hp
    have ha : 1 ≤ n.factorization p := hpprime.factorization_pos_of_dvd hn hpdvd
    rcases eq_or_ne p 2 with h2 | h2
    · subst h2
      rw [if_pos rfl]
      have := term_le_two (n.factorization 2) ha
      simpa using this
    · rw [if_neg h2]
      have := term_le_odd_prime p (n.factorization p) hpprime h2 ha
      simpa using this

end Commons.NumberTheory.Totient