import Mathlib

namespace Work.FIArea3

/-- If `n ≥ 1` has no prime factor `≤ P` (with `P ≥ 2`), then the number `τ(n)` of
divisors of `n` satisfies `log τ(n) ≤ log 2 · log n / log P`.

Indeed every prime factor of `n` is `> P`, so writing `n = ∏ p ^ a_p` over the
primes `p | n` and `Ω = ∑ a_p`, we have `n ≥ P ^ Ω` and `τ(n) = ∏ (a_p + 1) ≤ ∏ 2 ^ a_p = 2 ^ Ω`. -/
lemma tau_le_log_pz_rough {n P : ℕ} (hn : 1 ≤ n) (hP : 2 ≤ P)
    (hrough : ∀ p : ℕ, p.Prime → p ≤ P → ¬ p ∣ n) :
    Real.log ((n.divisors.card : ℕ) : ℝ) ≤ Real.log 2 * Real.log (n : ℝ) / Real.log (P : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  have hP0 : 0 < P := by omega
  have hlogP : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast hP : (1:ℝ) < (P:ℝ))
  -- `Ω` is the total number of prime factors of `n`, counted with multiplicity.
  set Ω : ℕ := ∑ p ∈ n.primeFactors, n.factorization p with hΩ
  -- `n` is the product of `p ^ a_p` over the primes `p | n`.
  have hprod : ∏ p ∈ n.primeFactors, p ^ (n.factorization p) = n := by
    rw [← Nat.support_factorization]
    exact Nat.prod_factorization_pow_eq_self hn0
  -- `τ(n) = ∏ (a_p + 1) ≤ ∏ 2 ^ a_p = 2 ^ Ω`.
  have hcard : n.divisors.card ≤ 2 ^ Ω := by
    rw [Nat.card_divisors hn0, hΩ, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod₀ (fun p _ => Nat.zero_le _)
      (fun p _ => Nat.succ_le_of_lt Nat.lt_two_pow_self)
  -- `n = ∏ p ^ a_p ≥ ∏ P ^ a_p = P ^ Ω`, since every `p | n` is `> P`.
  have hPn : P ^ Ω ≤ n := by
    rw [hΩ, ← Finset.prod_pow_eq_pow_sum]
    calc ∏ p ∈ n.primeFactors, P ^ (n.factorization p)
        ≤ ∏ p ∈ n.primeFactors, p ^ (n.factorization p) := by
          refine Finset.prod_le_prod₀ (fun p _ => Nat.zero_le _) (fun p hp => ?_)
          have hpP : P ≤ p := by
            by_contra h
            exact hrough p (Nat.prime_of_mem_primeFactors hp) (le_of_lt (not_le.mp h))
              (Nat.dvd_of_mem_primeFactors hp)
          exact Nat.pow_le_pow_left hpP _
      _ = n := hprod
  have hτpos : 0 < ((n.divisors.card : ℕ) : ℝ) := by
    have : 0 < n.divisors.card := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn0⟩
    exact_mod_cast this
  have hcardR : ((n.divisors.card : ℕ) : ℝ) ≤ (2:ℝ) ^ Ω := by exact_mod_cast hcard
  have h1 : Real.log ((n.divisors.card : ℕ) : ℝ) ≤ (Ω:ℝ) * Real.log 2 := by
    calc Real.log ((n.divisors.card : ℕ) : ℝ) ≤ Real.log ((2:ℝ)^Ω) :=
          Real.log_le_log hτpos hcardR
      _ = (Ω:ℝ) * Real.log 2 := Real.log_pow 2 Ω
  have h2 : (Ω:ℝ) * Real.log 2 ≤ Real.log 2 * Real.log (n:ℝ) / Real.log (P:ℝ) := by
    have hPnR : ((P:ℝ) ^ Ω) ≤ (n:ℝ) := by exact_mod_cast hPn
    have hle : (Ω:ℝ) * Real.log (P:ℝ) ≤ Real.log (n:ℝ) := by
      have h := Real.log_le_log (pow_pos (by exact_mod_cast hP0) Ω) hPnR
      rwa [Real.log_pow] at h
    have hΩle : (Ω:ℝ) ≤ Real.log (n:ℝ) / Real.log (P:ℝ) := (le_div_iff₀ hlogP).mpr hle
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    calc (Ω:ℝ) * Real.log 2 ≤ (Real.log (n:ℝ) / Real.log (P:ℝ)) * Real.log 2 :=
          mul_le_mul_of_nonneg_right hΩle hlog2
      _ = Real.log 2 * Real.log (n:ℝ) / Real.log (P:ℝ) := by ring
  exact le_trans h1 h2

end Work.FIArea3
