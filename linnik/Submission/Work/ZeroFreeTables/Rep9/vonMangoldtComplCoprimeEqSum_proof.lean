/-
# ZeroFreeTables/Rep9/vonMangoldtComplCoprimeEqSum_proof

Pointwise splitting of the non-coprime von Mangoldt tail over the prime divisors of `q`.
-/
import Mathlib

open ArithmeticFunction
open scoped BigOperators

namespace Work.ZeroFreeTables.Rep9

theorem vonMangoldtComplCoprimeEqSum_proof {q : ℕ} (hq : q ≠ 0) {σ : ℝ} (j : ℕ) (n : ℕ) :
    (if Nat.Coprime n q then (0:ℝ) else 1) * (ArithmeticFunction.vonMangoldt n : ℝ)
        * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j
      = ∑ p ∈ q.primeFactors,
          (if IsPrimePow n ∧ n.minFac = p then (ArithmeticFunction.vonMangoldt n : ℝ)
            * (n : ℝ) ^ (-σ) * (Real.log (n : ℝ)) ^ j else (0:ℝ)) := by
  set A : ℝ := (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)
    * (Real.log (n : ℝ)) ^ j with hA
  by_cases hpp : IsPrimePow n
  · have hn0 : n ≠ 0 := hpp.ne_zero
    have hp0prime : (n.minFac).Prime := Nat.minFac_prime hpp.ne_one
    have hpos : 0 < n.factorization n.minFac :=
      hp0prime.factorization_pos_of_dvd hn0 (Nat.minFac_dvd n)
    have hpow : n = n.minFac ^ (n.factorization n.minFac) :=
      (IsPrimePow.minFac_pow_factorization_eq hpp).symm
    have hcop : Nat.Coprime n q ↔ Nat.Coprime n.minFac q := by
      conv_lhs => rw [hpow]
      exact Nat.coprime_pow_left_iff hpos n.minFac q
    have hmem : n.minFac ∈ q.primeFactors ↔ ¬ Nat.Coprime n q := by
      rw [Nat.mem_primeFactors, hcop, hp0prime.coprime_iff_not_dvd]
      exact ⟨fun h hh => hh h.2.1, fun h => ⟨hp0prime, not_not.mp h, hq⟩⟩
    have hsum : ∑ p ∈ q.primeFactors, (if IsPrimePow n ∧ n.minFac = p then A else (0:ℝ))
        = if n.minFac ∈ q.primeFactors then A else 0 := by
      by_cases hm : n.minFac ∈ q.primeFactors
      · rw [if_pos hm]
        rw [Finset.sum_eq_single n.minFac ?_ ?_]
        · rw [if_pos ⟨hpp, rfl⟩]
        · intro b _ hne
          rw [if_neg]
          intro hcon
          exact hne hcon.2.symm
        · intro hnot
          exact absurd hm hnot
      · rw [if_neg hm]
        refine Finset.sum_eq_zero ?_
        intro b hb
        rw [if_neg]
        intro hcon
        exact hm (hcon.2.symm ▸ hb)
    have hif : (if Nat.Coprime n q then (0:ℝ) else 1)
        = if n.minFac ∈ q.primeFactors then (1:ℝ) else 0 := by
      by_cases hc : Nat.Coprime n q
      · rw [if_pos hc, if_neg (fun hm => (hmem.mp hm) hc)]
      · rw [if_neg hc, if_pos (hmem.mpr hc)]
    rw [hsum, hif]
    by_cases hm : n.minFac ∈ q.primeFactors
    · rw [if_pos hm, if_pos hm, one_mul]
    · rw [if_neg hm, if_neg hm]; ring
  · have hΛ : (ArithmeticFunction.vonMangoldt n : ℝ) = 0 :=
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp
    have hsum0 : (∑ p ∈ q.primeFactors,
        (if IsPrimePow n ∧ n.minFac = p then (0:ℝ) * (n : ℝ) ^ (-σ)
          * (Real.log (n : ℝ)) ^ j else (0:ℝ))) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro p _
      have hnot : ¬ (IsPrimePow n ∧ n.minFac = p) := fun h => hpp h.1
      rw [if_neg hnot]
    rw [hA, hΛ, hsum0]
    ring

end Work.ZeroFreeTables.Rep9
