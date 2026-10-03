import Mathlib
import Submission.Work.FIArea1.L51Count

namespace Work.FIArea1

open Finset

/-- Multiplicativity of `Nc` over a finite set of pairwise coprimes, in the form needed for the
prime-factor decomposition of the modulus. -/
lemma Nc_prod_of_prime : ∀ (s : Finset ℕ) (e : ℕ → ℕ) (a b : ℕ),
    (∀ p ∈ s, p.Prime) →
    Nc (∏ p ∈ s, p ^ e p) a b = ∏ p ∈ s, Nc (p ^ e p) a b := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro e a b _
      simp only [Finset.prod_empty]
      rw [Nc_eq_Ncount_of_ne 1 (by norm_num) a b]
      exact Ncount_one a b
  | insert p t hp ih =>
      intro e a b hprime
      have hpprime : p.Prime := hprime p (Finset.mem_insert_self p t)
      have htprime : ∀ x ∈ t, x.Prime := fun x hx => hprime x (Finset.mem_insert_of_mem hx)
      have hcop : Nat.Coprime (p ^ e p) (∏ x ∈ t, x ^ e x) :=
        Nat.Coprime.prod_right fun x hx =>
          Nat.Coprime.pow (e p) (e x)
            ((Nat.coprime_primes hpprime (htprime x hx)).mpr fun h => hp (h ▸ hx))
      have h1 : p ^ e p ≠ 0 := pow_ne_zero _ hpprime.ne_zero
      have h2 : (∏ x ∈ t, x ^ e x) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun x hx => pow_ne_zero _ (htprime x hx).ne_zero
      rw [Finset.prod_insert hp, Finset.prod_insert hp,
        Nc_mul (p ^ e p) (∏ x ∈ t, x ^ e x) a b h1 h2 hcop,
        ih e a b htprime]

theorem l51_Nc_prod (d a b : ℕ) (hd : d ≠ 0) :
    Work.FIArea1.Nc d a b =
      ∏ p ∈ d.primeFactors, Work.FIArea1.Nc (p ^ d.factorization p) a b := by
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hd]
  exact Nc_prod_of_prime d.primeFactors d.factorization a b
    fun p hp => Nat.prime_of_mem_primeFactors hp

end Work.FIArea1
