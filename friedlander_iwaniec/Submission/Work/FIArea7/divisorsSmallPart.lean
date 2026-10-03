import Mathlib

namespace Work.FIArea7

/-- Among the prime factors of `n` that are `< B` (there are at most `B` of them), each
contributes a factor `factorization n p + 1` that is bounded by `log n / log 2 + 1`.
Hence the whole product is at most `(log n / log 2 + 1) ^ B`. -/
theorem divisorsSmallPart (B n : ℕ) :
    (∏ p ∈ n.primeFactors.filter (fun p => p < B), ((n.factorization p + 1 : ℕ) : ℝ))
      ≤ (Real.log (n : ℝ) / Real.log 2 + 1) ^ B := by
  classical
  have h2pos : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  -- Each individual factor is bounded by `log n / log 2 + 1`.
  have hfac : ∀ p ∈ n.primeFactors.filter (fun p => p < B),
      ((n.factorization p + 1 : ℕ) : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 + 1 := by
    intro p hpS
    have hp : p ∈ n.primeFactors := (Finset.mem_filter.mp hpS).1
    have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hn0 : n ≠ 0 := (Nat.mem_primeFactors.mp hp).2.2
    set a := n.factorization p with ha
    -- `p ^ a` divides `n`.
    have hdvd : p ^ a ∣ n := by
      rw [← Nat.factorization_le_iff_dvd (pow_ne_zero a hpprime.ne_zero) hn0]
      rw [hpprime.factorization_pow]
      exact Finsupp.single_le_iff.mpr le_rfl
    obtain ⟨m, hm⟩ := hdvd
    have hm0 : m ≠ 0 := by intro h; rw [h, mul_zero] at hm; exact hn0 hm
    -- hence `2 ^ a ≤ p ^ a ≤ n`.
    have hle : 2 ^ a ≤ n := by
      have h2p : 2 ≤ p := hpprime.two_le
      have h1 : 2 ^ a ≤ p ^ a := Nat.pow_le_pow_left h2p a
      have h2 : p ^ a * 1 ≤ p ^ a * m := Nat.mul_le_mul_left _ (Nat.one_le_iff_ne_zero.mpr hm0)
      calc 2 ^ a ≤ p ^ a := h1
        _ = p ^ a * 1 := (mul_one _).symm
        _ ≤ p ^ a * m := h2
        _ = n := hm.symm
    -- taking logarithms: `a * log 2 ≤ log n`.
    have hlog : (a : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
      have hcast : ((2 : ℕ) ^ a : ℝ) ≤ (n : ℝ) := by exact_mod_cast hle
      have hpos : (0 : ℝ) < ((2 : ℕ) ^ a : ℝ) := by positivity
      have hli := Real.log_le_log hpos hcast
      rw [Real.log_pow] at hli
      simpa using hli
    have hdiv : (a : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
      rw [le_div_iff₀ h2pos]; exact hlog
    calc ((n.factorization p + 1 : ℕ) : ℝ) = (a : ℝ) + 1 := by rw [← ha]; push_cast; ring
      _ ≤ Real.log (n : ℝ) / Real.log 2 + 1 := by linarith
  -- There are at most `B` primes `< B`.
  have hcard : (n.primeFactors.filter (fun p => p < B)).card ≤ B := by
    have hsub : n.primeFactors.filter (fun p => p < B) ⊆ Finset.range B := by
      intro p hpS
      have := (Finset.mem_filter.mp hpS).2
      simpa using this
    calc (n.primeFactors.filter (fun p => p < B)).card ≤ (Finset.range B).card :=
          Finset.card_le_card hsub
      _ = B := Finset.card_range B
  have hbase : (1 : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 + 1 := by
    have : (0 : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 :=
      div_nonneg (Real.log_natCast_nonneg n) (le_of_lt h2pos)
    linarith
  have hstep : (∏ p ∈ n.primeFactors.filter (fun p => p < B), ((n.factorization p + 1 : ℕ) : ℝ))
      ≤ (Real.log (n : ℝ) / Real.log 2 + 1) ^ (n.primeFactors.filter (fun p => p < B)).card := by
    have := Finset.prod_le_prod₀ (s := n.primeFactors.filter (fun p => p < B))
      (f := fun p => ((n.factorization p + 1 : ℕ) : ℝ))
      (g := fun _ => Real.log (n : ℝ) / Real.log 2 + 1)
      (fun i _ => by positivity) (fun i hi => hfac i hi)
    simpa [Finset.prod_const] using this
  calc (∏ p ∈ n.primeFactors.filter (fun p => p < B), ((n.factorization p + 1 : ℕ) : ℝ))
      ≤ (Real.log (n : ℝ) / Real.log 2 + 1) ^ (n.primeFactors.filter (fun p => p < B)).card :=
        hstep
    _ ≤ (Real.log (n : ℝ) / Real.log 2 + 1) ^ B := pow_le_pow_right₀ hbase hcard

end Work.FIArea7
