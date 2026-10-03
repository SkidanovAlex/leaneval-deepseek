import Mathlib

namespace Work.FIArea7

theorem divisorsLargePart (q n : ℕ) (hn : n ≠ 0) :
    (∏ p ∈ n.primeFactors.filter (fun p => 2 ^ q ≤ p), ((n.factorization p + 1 : ℕ) : ℝ)) ^ q
      ≤ (n : ℝ) := by
  -- We show the stronger natural-number statement, then cast to `ℝ`.
  set s := n.primeFactors.filter (fun p => 2 ^ q ≤ p) with hs
  -- For each prime `p ∣ n` with `2 ^ q ≤ p`, we have `(v_p(n) + 1) ^ q ≤ p ^ v_p(n)`.
  have hterm : ∀ p ∈ s, (n.factorization p + 1) ^ q ≤ p ^ (n.factorization p) := by
    intro p hp
    rw [hs, Finset.mem_filter] at hp
    obtain ⟨hpPF, hp2⟩ := hp
    calc (n.factorization p + 1) ^ q
        ≤ (2 ^ n.factorization p) ^ q :=
          Nat.pow_le_pow_left (Nat.succ_le_of_lt Nat.lt_two_pow_self) q
      _ = 2 ^ (n.factorization p * q) := (pow_mul 2 _ _).symm
      _ = 2 ^ (q * n.factorization p) := by rw [Nat.mul_comm]
      _ = (2 ^ q) ^ n.factorization p := pow_mul 2 q _
      _ ≤ p ^ n.factorization p := Nat.pow_le_pow_left hp2 _
  -- Multiply over the selected primes and compare with the full factorisation of `n`.
  have hnat : ∏ p ∈ s, (n.factorization p + 1) ^ q ≤ n := by
    calc ∏ p ∈ s, (n.factorization p + 1) ^ q
        ≤ ∏ p ∈ s, p ^ n.factorization p := Finset.prod_le_prod' hterm
      _ ≤ ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
            apply Finset.prod_le_prod_of_subset_of_one_le'
            · rw [hs]; exact Finset.filter_subset _ _
            · intro i hi _
              exact one_le_pow₀ (le_of_lt (Nat.Prime.one_lt (Nat.mem_primeFactors.mp hi).1))
      _ = n := by
            rw [← Nat.support_factorization n, ← Finsupp.prod]
            exact Nat.prod_factorization_pow_eq_self hn
  -- Translate the real-valued product into the cast of its natural-number version.
  have hcast : (∏ p ∈ s, ((n.factorization p + 1 : ℕ) : ℝ)) ^ q
      = ((∏ p ∈ s, (n.factorization p + 1) ^ q : ℕ) : ℝ) := by
    rw [← Finset.prod_pow, Nat.cast_prod]
    exact Finset.prod_congr rfl (fun p _ => (Nat.cast_pow _ _).symm)
  rw [hcast]
  exact_mod_cast hnat

end Work.FIArea7
