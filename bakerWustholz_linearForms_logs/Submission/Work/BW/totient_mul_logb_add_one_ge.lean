import Mathlib
import Submission.Work.BW.prod_one_sub_inv_prime_ge
import Submission.Work.BW.primeFactors_card_le_logb

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-! Elementary bound `k ≤ φ(k)·(log₂ k + 1)` for `k ≥ 1`.

Route (no Chebyshev/Mertens needed).  From `Nat.totient_eq_mul_prod_factors` (over ℚ) one has
`k/φ(k) = ∏_{p ∈ k.primeFactors} p/(p-1)`, i.e. `φ(k)/k = ∏_{p ∈ k.primeFactors} (1 - 1/p)`.
Key sub-fact: for any finset `s` of primes, `∏_{p∈s} (1 - 1/p) ≥ 1/(|s|+1)` (lemma
`prod_one_sub_inv_prime_ge`).  Finally `ω := k.primeFactors.card ≤ Real.logb 2 k` (lemma
`primeFactors_card_le_logb`) because `∏_{p ∈ k.primeFactors} p` divides `k` and is `≥ 2^ω`.
Then `φ(k)·(log₂ k + 1) ≥ k·(log₂ k + 1)/(ω+1) ≥ k·(ω+1)/(ω+1) = k`.  Edge case `k = 1`

is covered uniformly. -/
theorem totient_mul_logb_add_one_ge (k : ℕ) (hk : 0 < k) :
    (k : ℝ) ≤ (Nat.totient k : ℝ) * (Real.logb 2 (k : ℝ) + 1) := by
  -- Euler's product formula, pushed from ℚ to ℝ.
  have hφ : (Nat.totient k : ℝ) = (k : ℝ) * ∏ p ∈ k.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have h := Nat.totient_eq_mul_prod_factors k
    have h' := congrArg (fun q : ℚ => (q : ℝ)) h
    simp only [Rat.cast_mul, Rat.cast_prod, Rat.cast_sub, Rat.cast_one, Rat.cast_inv,
      Rat.cast_natCast] at h'
    exact h'
  -- the key product lower bound for the prime factors of `k`
  have hP : 1 / ((k.primeFactors.card : ℝ) + 1)
      ≤ ∏ p ∈ k.primeFactors, (1 - (p : ℝ)⁻¹) :=
    prod_one_sub_inv_prime_ge k.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
  -- ω(k) ≤ log₂ k
  have hL : (k.primeFactors.card : ℝ) ≤ Real.logb 2 (k : ℝ) := primeFactors_card_le_logb k hk
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hc : (0 : ℝ) < (k.primeFactors.card : ℝ) + 1 := by positivity
  have hL1 : (k.primeFactors.card : ℝ) + 1 ≤ Real.logb 2 (k : ℝ) + 1 := by linarith
  have hposL : (0 : ℝ) < Real.logb 2 (k : ℝ) + 1 := by linarith
  have h1 : (1 : ℝ) ≤ (Real.logb 2 (k : ℝ) + 1) / ((k.primeFactors.card : ℝ) + 1) := by
    rw [le_div_iff₀ hc]; linarith
  have h2 : (Real.logb 2 (k : ℝ) + 1) / ((k.primeFactors.card : ℝ) + 1)
      ≤ (∏ p ∈ k.primeFactors, (1 - (p : ℝ)⁻¹)) * (Real.logb 2 (k : ℝ) + 1) := by
    have h := mul_le_mul_of_nonneg_right hP (le_of_lt hposL)
    simpa [div_eq_inv_mul] using h
  have key : (1 : ℝ) ≤ (∏ p ∈ k.primeFactors, (1 - (p : ℝ)⁻¹)) * (Real.logb 2 (k : ℝ) + 1) :=
    le_trans h1 h2
  rw [hφ]
  nlinarith [key, hkR]

end Work.BW
