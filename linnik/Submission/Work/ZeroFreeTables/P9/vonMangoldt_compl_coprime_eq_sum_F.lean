import Mathlib

namespace Work.ZeroFreeTables.P9

theorem vonMangoldt_compl_coprime_eq_sum_F {q : ℕ} (hq : q ≠ 0) {σ : ℝ} (j : ℕ) (n : ℕ) : (if Nat.Coprime n q then (0:ℝ) else 1) * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j = ∑ p ∈ q.primeFactors, (if IsPrimePow n ∧ n.minFac = p then (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j else (0:ℝ)) := by
  by_cases hpp : IsPrimePow n
  · set X : ℝ := (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j with hX
    have hlhs : (if Nat.Coprime n q then (0:ℝ) else 1) * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j
        = (if Nat.Coprime n q then (0:ℝ) else 1) * X := by
      rw [hX]; ring
    rw [hlhs]
    have hsum1 : (∑ p ∈ q.primeFactors, (if IsPrimePow n ∧ n.minFac = p then X else (0:ℝ)))
        = ∑ p ∈ q.primeFactors, (if n.minFac = p then X else (0:ℝ)) := by
      refine Finset.sum_congr rfl (fun p hp => ?_)
      simp only [hpp, true_and]
    have hsum2 : (∑ p ∈ q.primeFactors, (if n.minFac = p then X else (0:ℝ)))
        = if n.minFac ∈ q.primeFactors then X else (0:ℝ) :=
      Finset.sum_ite_eq q.primeFactors n.minFac (fun _ => X)
    rw [hsum1, hsum2]
    have hminfac_prime : Nat.Prime n.minFac := Nat.minFac_prime_iff.mpr hpp.ne_one
    have hmem : n.minFac ∈ q.primeFactors ↔ n.minFac ∣ q := by
      rw [Nat.mem_primeFactors]
      exact ⟨fun h => h.2.1, fun h => ⟨hminfac_prime, h, hq⟩⟩
    have hcop : Nat.Coprime n q ↔ Nat.Coprime n.minFac q := by
      constructor
      · intro h; exact Nat.Coprime.coprime_dvd_left (Nat.minFac_dvd n) h
      · intro h
        have h2 : Nat.Coprime (n.minFac ^ n.factorization n.minFac) q :=
          Nat.Coprime.pow_left (n.factorization n.minFac) h
        rwa [IsPrimePow.minFac_pow_factorization_eq hpp] at h2
    have hdvd : (n.minFac ∣ q) ↔ ¬ Nat.Coprime n.minFac q := by
      rw [Nat.Prime.coprime_iff_not_dvd hminfac_prime, not_not]
    have hkey : (if Nat.Coprime n q then (0:ℝ) else 1)
        = (if n.minFac ∈ q.primeFactors then (1:ℝ) else 0) := by
      by_cases hC : Nat.Coprime n q
      · rw [if_pos hC, if_neg (by rw [hmem, hdvd]; exact fun h => h (hcop.mp hC))]
      · rw [if_neg hC, if_pos (by rw [hmem, hdvd]; exact fun h => hC (hcop.mpr h))]
    rw [hkey]
    by_cases hm : n.minFac ∈ q.primeFactors <;> simp [hm]
  · have h0 : (ArithmeticFunction.vonMangoldt n : ℝ) = 0 := by
      rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]
    rw [h0]
    simp only [hpp, false_and, ↓reduceIte, mul_zero, zero_mul, Finset.sum_const_zero]

end Work.ZeroFreeTables.P9
