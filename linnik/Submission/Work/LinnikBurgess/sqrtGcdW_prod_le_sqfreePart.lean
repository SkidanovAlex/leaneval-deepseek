import Mathlib
import Submission.Work.LinnikBurgess.singleton_ssa_defs

/-!
# `∏_{p ∈ lowPrimeSet q} sqrtGcdW p i v ≤ sqrtGcdW (sqfreePart q) i v`

The weight `sqrtGcdW m i v = ∏_{l ≠ i} √(gcd (m, |v_i - v_l|))` is multiplicative in `m`
along a product of pairwise coprime moduli: for `S` a finset of pairwise coprime naturals,
`∏_{p ∈ S} √(gcd (p, n)) = √(gcd (∏_{p ∈ S} p, n))`.  Applying this to the set
`lowPrimeSet q` of primes of exponent exactly `1` in `q`, whose product is `sqfreePart q`,
gives the identity (hence the inequality) below.

The proof is a small missing chapter of Mathlib: the number-theoretic core is
`Nat.gcd (∏_{p ∈ S} p) n = ∏_{p ∈ S} Nat.gcd p n` for pairwise coprime `S`
(`gcd_prod_eq_prod_gcd`), lifted to the reals through `Real.sqrt_prod`.
-/

open scoped BigOperators
open Classical

namespace Work.LinnikBurgess

/-- `sqfreePart q` is literally the product of the primes in `lowPrimeSet q`. -/
lemma sqfreePart_eq_prod_lowPrimeSet (q : ℕ) :
    sqfreePart q = ∏ p ∈ lowPrimeSet q, p := rfl

/-- Every element of `lowPrimeSet q` is prime. -/
lemma prime_of_mem_lowPrimeSet {q p : ℕ} (hp : p ∈ lowPrimeSet q) : Nat.Prime p := by
  simp only [lowPrimeSet, Finset.mem_filter] at hp
  exact Nat.prime_of_mem_primeFactors hp.1

/-- For a finset `S` of pairwise coprime values of `f`, the gcd of the product is the product
of the gcds. -/
lemma gcd_prod_eq_prod_gcd (S : Finset ℕ) (f : ℕ → ℕ) (n : ℕ)
    (h : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.Coprime (f a) (f b)) :
    Nat.gcd (∏ a ∈ S, f a) n = ∏ a ∈ S, Nat.gcd (f a) n := by
  induction S using Finset.induction with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hcop : Nat.Coprime (f a) (∏ b ∈ T, f b) := by
      apply Nat.Coprime.prod_right
      intro b hb
      exact h a (Finset.mem_insert_self a T) b (Finset.mem_insert_of_mem hb)
        (fun hEq => ha (hEq.symm ▸ hb))
    rw [Nat.gcd_comm (f a * ∏ b ∈ T, f b) n, Nat.Coprime.gcd_mul n hcop,
        Nat.gcd_comm n (f a), Nat.gcd_comm n (∏ b ∈ T, f b)]
    rw [ih (fun a' ha' b' hb' hne =>
      h a' (Finset.mem_insert_of_mem ha') b' (Finset.mem_insert_of_mem hb') hne)]

/-- The real form: the product of the square roots of the individual gcds is the square root of
the gcd with the product, for a finset of primes. -/
lemma prod_sqrt_gcd_eq_sqrt_gcd_prod (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p) (n : ℕ) :
    (∏ p ∈ S, Real.sqrt ((Nat.gcd p n : ℕ) : ℝ))
      = Real.sqrt ((Nat.gcd (∏ p ∈ S, p) n : ℕ) : ℝ) := by
  rw [← Real.sqrt_prod S (x := fun p => ((Nat.gcd p n : ℕ) : ℝ)) (fun p _ => by positivity)]
  congr 1
  have hcop : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.Coprime a b :=
    fun a ha b hb hne => (Nat.coprime_primes (hprime a ha) (hprime b hb)).mpr hne
  have hnat := gcd_prod_eq_prod_gcd S id n hcop
  simp only [id_eq] at hnat
  exact_mod_cast hnat.symm

theorem sqrtGcdW_prod_le_sqfreePart (q : ℕ) (i : Fin 6) (v : Fin 6 → ℕ) :
    (∏ p ∈ lowPrimeSet q, sqrtGcdW p i v) ≤ sqrtGcdW (sqfreePart q) i v := by
  rw [sqfreePart_eq_prod_lowPrimeSet]
  have key : (∏ p ∈ lowPrimeSet q, sqrtGcdW p i v)
      = ∏ l ∈ Finset.univ.erase i,
          Real.sqrt ((Nat.gcd (∏ p ∈ lowPrimeSet q, p)
            ((v i : ℤ) - (v l : ℤ)).natAbs : ℕ) : ℝ) := by
    simp only [sqrtGcdW]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl (fun l hl => ?_)
    exact prod_sqrt_gcd_eq_sqrt_gcd_prod (lowPrimeSet q)
      (fun p hp => prime_of_mem_lowPrimeSet hp) _
  rw [key]
  simp only [sqrtGcdW]
  exact le_refl _

end Work.LinnikBurgess
