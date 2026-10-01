import Mathlib

/-!
# A divisor-sum identity for the square of the divisor-counting function

We prove, for every natural number `n`,

  `#(n.divisors) ^ 2 = ∑ d ∈ n.divisors, 2 ^ ω(d) * #((n / d).divisors)`,

where `ω d = d.primeFactors.card` is the number of distinct prime factors of `d`.

Both sides, viewed as functions of `n`, are multiplicative: the left-hand side is the
pointwise square of the divisor-counting function `σ 0`, and the right-hand side is the
Dirichlet convolution of `d ↦ 2 ^ ω(d)` with `σ 0`.  Since `σ 0` is also multiplicative,
it suffices to check the identity on the prime powers `n = p ^ i`; there it reduces to the
elementary triangular sum `(i + 1) + 2 * ∑_{j = 1}^{i} j = (i + 1) ^ 2`.
-/

namespace Work.ZeroDensity.Montgomery

open ArithmeticFunction

/-- `n ↦ 2 ^ ω(n)`, where `ω(n)` is the number of distinct prime factors of `n`, viewed as an
arithmetic function with values in `ℝ` (with the value `0` forced at `n = 0`). -/
noncomputable def cardDivisorsSq_twoPowOmegaArith : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else (2 : ℝ) ^ n.primeFactors.card, by simp⟩

theorem cardDivisorsSq_twoPowOmegaArith_apply (n : ℕ) :
    cardDivisorsSq_twoPowOmegaArith n =
      if n = 0 then 0 else (2 : ℝ) ^ n.primeFactors.card := rfl

/-- The divisor-counting function `σ 0`, with values in `ℝ`. -/
noncomputable abbrev cardDivisorsSq_sigmaZeroArith : ArithmeticFunction ℝ :=
  (ArithmeticFunction.sigma 0 : ArithmeticFunction ℕ)

theorem cardDivisorsSq_sigmaZeroArith_apply (n : ℕ) :
    cardDivisorsSq_sigmaZeroArith n = ((n.divisors.card : ℕ) : ℝ) := by
  simp [cardDivisorsSq_sigmaZeroArith, ArithmeticFunction.sigma_zero_apply]

/-- The pointwise square of the divisor-counting function, with values in `ℝ`. -/
noncomputable def cardDivisorsSq_sigmaZeroArithSq : ArithmeticFunction ℝ :=
  ⟨fun n => cardDivisorsSq_sigmaZeroArith n ^ 2, by simp⟩

theorem cardDivisorsSq_sigmaZeroArithSq_apply (n : ℕ) :
    cardDivisorsSq_sigmaZeroArithSq n = cardDivisorsSq_sigmaZeroArith n ^ 2 := rfl

theorem cardDivisorsSq_twoPowOmegaArith_isMultiplicative :
    cardDivisorsSq_twoPowOmegaArith.IsMultiplicative := by
  refine IsMultiplicative.iff_ne_zero.2 ⟨?_, ?_⟩
  · rw [cardDivisorsSq_twoPowOmegaArith_apply, if_neg one_ne_zero, Nat.primeFactors_one,
      Finset.card_empty, pow_zero]
  · intro m n hm hn hcop
    rw [cardDivisorsSq_twoPowOmegaArith_apply, cardDivisorsSq_twoPowOmegaArith_apply,
      cardDivisorsSq_twoPowOmegaArith_apply, if_neg (mul_ne_zero hm hn), if_neg hm, if_neg hn]
    rw [Nat.primeFactors_mul hm hn, Finset.card_union_of_disjoint hcop.disjoint_primeFactors,
      pow_add]

theorem cardDivisorsSq_sigmaZeroArith_isMultiplicative :
    cardDivisorsSq_sigmaZeroArith.IsMultiplicative := by
  have h := (ArithmeticFunction.isMultiplicative_sigma (k := 0)).natCast (R := ℝ)
  simpa [cardDivisorsSq_sigmaZeroArith] using h

theorem cardDivisorsSq_sigmaZeroArithSq_isMultiplicative :
    cardDivisorsSq_sigmaZeroArithSq.IsMultiplicative := by
  refine IsMultiplicative.iff_ne_zero.2 ⟨?_, ?_⟩
  · rw [cardDivisorsSq_sigmaZeroArithSq_apply, cardDivisorsSq_sigmaZeroArith_apply,
      Nat.divisors_one, Finset.card_singleton, Nat.cast_one, one_pow]
  · intro m n _ _ hcop
    rw [cardDivisorsSq_sigmaZeroArithSq_apply, cardDivisorsSq_sigmaZeroArithSq_apply,
      cardDivisorsSq_sigmaZeroArithSq_apply,
      cardDivisorsSq_sigmaZeroArith_isMultiplicative.map_mul_of_coprime hcop, mul_pow]

/-- The number of divisors of a prime power. -/
theorem cardDivisorsSq_card_divisors_prime_pow (p k : ℕ) (hp : p.Prime) :
    (p ^ k).divisors.card = k + 1 := by
  rw [← ArithmeticFunction.sigma_zero_apply,
    ArithmeticFunction.sigma_zero_apply_prime_pow hp]

/-- The real triangular sum: `2 * ∑_{k < n} k = n (n - 1)`. -/
theorem cardDivisorsSq_two_mul_sum_range (n : ℕ) :
    2 * (∑ k ∈ Finset.range n, ((k : ℕ) : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

/-- The prime-power case of the divisor-sum identity, in closed form. -/
theorem cardDivisorsSq_sum_range (p i : ℕ) (hp : p.Prime) :
    (∑ x ∈ Finset.range (i + 1),
        (2 : ℝ) ^ ((p ^ x).primeFactors.card) * (((i - x) + 1 : ℕ) : ℝ))
      = ((i + 1 : ℕ) : ℝ) ^ 2 := by
  have hc : ∀ x : ℕ,
      (2 : ℝ) ^ ((p ^ x).primeFactors.card) = if x = 0 then 1 else 2 := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · rw [if_neg hx, Nat.primeFactors_prime_pow hx hp]
      simp
  simp only [hc]
  rw [Finset.sum_range_succ']
  have h0 : (if 0 = 0 then (1 : ℝ) else 2) * ((i - 0 + 1 : ℕ) : ℝ) = ((i + 1 : ℕ) : ℝ) := by
    simp
  have hk : ∀ k ∈ Finset.range i,
      (if k + 1 = 0 then (1 : ℝ) else 2) * ((i - (k + 1) + 1 : ℕ) : ℝ)
        = 2 * ((i - k : ℕ) : ℝ) := by
    intro k hk
    have hk' : k < i := Finset.mem_range.mp hk
    have hsub : i - (k + 1) + 1 = i - k := by omega
    rw [if_neg (Nat.succ_ne_zero k), hsub]
  rw [Finset.sum_congr rfl hk, h0]
  rw [← Finset.mul_sum]
  have hS2 : (∑ k ∈ Finset.range i, ((i - k : ℕ) : ℝ))
      = (∑ k ∈ Finset.range i, ((k : ℕ) : ℝ)) + (i : ℝ) := by
    have h1 : ∀ k ∈ Finset.range i,
        ((i - k : ℕ) : ℝ) = ((i - 1 - k : ℕ) : ℝ) + 1 := by
      intro k hk
      have hk' : k < i := Finset.mem_range.mp hk
      have hik : i - k = (i - 1 - k) + 1 := by omega
      rw [hik, Nat.cast_add, Nat.cast_one]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
    rw [Finset.sum_range_reflect (fun j => ((j : ℕ) : ℝ))]
    simp [Finset.sum_const, Finset.card_range]
  rw [hS2, mul_add, cardDivisorsSq_two_mul_sum_range i]
  push_cast
  ring

theorem cardDivisorsSq_eq_sum (n : ℕ) :
    ((n.divisors.card : ℝ)) ^ 2
      = ∑ d ∈ n.divisors, (2 : ℝ) ^ (d.primeFactors.card) * ((n / d).divisors.card : ℝ) := by
  have hkey : ∀ p i : ℕ, Nat.Prime p →
      (cardDivisorsSq_twoPowOmegaArith * cardDivisorsSq_sigmaZeroArith) (p ^ i)
        = cardDivisorsSq_sigmaZeroArithSq (p ^ i) := by
    intro p i hp
    rw [cardDivisorsSq_sigmaZeroArithSq_apply, cardDivisorsSq_sigmaZeroArith_apply,
      cardDivisorsSq_card_divisors_prime_pow p i hp]
    rw [ArithmeticFunction.mul_apply]
    rw [Nat.sum_divisorsAntidiagonal (f := fun a b =>
      cardDivisorsSq_twoPowOmegaArith a * cardDivisorsSq_sigmaZeroArith b)]
    rw [Nat.divisors_prime_pow hp i]
    simp only [Finset.sum_map, Function.Embedding.coeFn_mk]
    rw [← cardDivisorsSq_sum_range p i hp]
    apply Finset.sum_congr rfl
    intro x hx
    have hx' : x ≤ i := by simpa using hx
    rw [cardDivisorsSq_twoPowOmegaArith_apply, cardDivisorsSq_sigmaZeroArith_apply,
      if_neg (pow_ne_zero x hp.ne_zero), Nat.pow_div hx' hp.pos,
      cardDivisorsSq_card_divisors_prime_pow p (i - x) hp]
  have hEq : cardDivisorsSq_twoPowOmegaArith * cardDivisorsSq_sigmaZeroArith
      = cardDivisorsSq_sigmaZeroArithSq :=
    (IsMultiplicative.eq_iff_eq_on_prime_powers _ (cardDivisorsSq_twoPowOmegaArith_isMultiplicative.mul
      cardDivisorsSq_sigmaZeroArith_isMultiplicative) _
        cardDivisorsSq_sigmaZeroArithSq_isMultiplicative).2 hkey
  rw [show ((n.divisors.card : ℝ)) ^ 2 = cardDivisorsSq_sigmaZeroArithSq n from by
    rw [cardDivisorsSq_sigmaZeroArithSq_apply, cardDivisorsSq_sigmaZeroArith_apply]]
  rw [← hEq, ArithmeticFunction.mul_apply]
  rw [Nat.sum_divisorsAntidiagonal (f := fun a b =>
    cardDivisorsSq_twoPowOmegaArith a * cardDivisorsSq_sigmaZeroArith b)]
  apply Finset.sum_congr rfl
  intro d hd
  rw [cardDivisorsSq_twoPowOmegaArith_apply, cardDivisorsSq_sigmaZeroArith_apply,
    if_neg (Nat.pos_of_mem_divisors hd).ne']

end Work.ZeroDensity.Montgomery
