import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Nat

namespace Commons.NumberTheory.FriedlanderIwaniec

theorem squarefree_sqKernel_of_cubefree {d : ℕ} (hd : ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ d) :
    Squarefree ((Nat.primeFactors d).prod (fun p : ℕ => p ^ (d.factorization p / 2))) := by
  have hBsq : Squarefree ((Nat.primeFactors d).prod (fun p : ℕ => p)) := by
    refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
    · intro a ha b hb hab
      exact Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (Nat.mem_primeFactors.mp ha).1 (Nat.mem_primeFactors.mp hb).1).mpr hab)
    · intro a ha
      exact (Nat.mem_primeFactors.mp ha).1.prime.squarefree
  refine Squarefree.squarefree_of_dvd ?_ hBsq
  refine Finset.prod_dvd_prod_of_dvd _ _ ?_
  intro p hp
  obtain ⟨hpprime, hpdiv, hdne⟩ := Nat.mem_primeFactors.mp hp
  have h3 : ¬ (3 ≤ d.factorization p) :=
    fun h => hd p hpprime ((hpprime.pow_dvd_iff_le_factorization hdne).mpr h)
  have he : d.factorization p / 2 ≤ 1 := by omega
  calc p ^ (d.factorization p / 2) ∣ p ^ 1 :=
        (Nat.pow_dvd_pow_iff_le_right hpprime.one_lt).mpr he
    _ = p := pow_one p

end Commons.NumberTheory.FriedlanderIwaniec
