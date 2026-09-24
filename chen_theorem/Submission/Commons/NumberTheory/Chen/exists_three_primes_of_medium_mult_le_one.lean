import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Submission.Commons.Data.Nat.factorization_prod_prime_pow_apply

open scoped ArithmeticFunction.Omega BigOperators
open Finset

namespace Commons.NumberTheory.Chen

/-- `Ω n = cardFactors n` is the sum of the exponents in the prime factorisation of `n`. -/
lemma cardFactors_eq_sum_primeFactors (n : ℕ) :
    ArithmeticFunction.cardFactors n = ∑ p ∈ n.primeFactors, n.factorization p := by
  rw [ArithmeticFunction.cardFactors_eq_sum_factorization]
  rw [Finsupp.sum, Nat.support_factorization]

/-- `n` is the product of its prime factors raised to their exponents. -/
lemma factorization_prod_eq_self (n : ℕ) (hn : n ≠ 0) :
    n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
  have h := Nat.prod_factorization_pow_eq_self hn
  simp only [Finsupp.prod, Nat.support_factorization] at h
  exact h.symm

theorem exists_three_primes_of_medium_mult_le_one {n z y : ℕ}
    (h3 : 3 ≤ ArithmeticFunction.cardFactors n)
    (hrough : ∀ p ∈ n.primeFactors, z ≤ p)
    (hmed : ((Finset.Icc z (y - 1)).filter (fun q : ℕ => q.Prime)).sum
      (fun q => n.factorization q) ≤ 1)
    (hny : n < y ^ 3) :
    ∃ q p₂ p₃ : ℕ, q.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ z ≤ q ∧ q < y ∧ y ≤ p₂ ∧ p₂ ≤ p₃ ∧
      n = q * p₂ * p₃ := by
  classical
  set Sm : Finset ℕ := (Finset.Icc z (y - 1)).filter (fun q : ℕ => q.Prime) with hSm
  have hmed' : Sm.sum (fun r => n.factorization r) ≤ 1 := hmed
  have hn0 : n ≠ 0 := by
    intro h
    rw [h] at h3
    simp at h3
  have hΩn : ArithmeticFunction.cardFactors n = ∑ p ∈ n.primeFactors, n.factorization p :=
    cardFactors_eq_sum_primeFactors n
  have hnprod : n = ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
    factorization_prod_eq_self n hn0
  rcases eq_or_ne y 0 with hy0 | hy0
  · exact absurd (by simpa [hy0] using hny) (Nat.not_lt_zero n)
  have hy1 : 1 ≤ y := Nat.one_le_iff_ne_zero.mpr hy0
  -- Step 1: there is a prime factor of `n` below `y`
  have hex : ∃ q ∈ n.primeFactors, q < y := by
    by_contra hcon
    push_neg at hcon
    have hle : y ^ ArithmeticFunction.cardFactors n ≤ n := by
      calc y ^ ArithmeticFunction.cardFactors n
          = ∏ p ∈ n.primeFactors, y ^ n.factorization p := by
            rw [hΩn, Finset.prod_pow_eq_pow_sum]
        _ ≤ ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
            apply Finset.prod_le_prod₀
            · intro p hp; exact Nat.zero_le _
            · intro p hp; exact Nat.pow_le_pow_left (hcon p hp) _
        _ = n := hnprod.symm
    have h3le : y ^ 3 ≤ y ^ ArithmeticFunction.cardFactors n :=
      Nat.pow_le_pow_right (by omega) h3
    omega
  obtain ⟨q, hqm, hqy⟩ := hex
  have hqprime : q.Prime := (Nat.mem_primeFactors.mp hqm).1
  have hqdvd : q ∣ n := (Nat.mem_primeFactors.mp hqm).2.1
  have hqz : z ≤ q := hrough q hqm
  have hqle : q ≤ y - 1 := Nat.le_sub_one_of_lt hqy
  have hqSm : q ∈ Sm := by
    rw [hSm, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hqz, hqle⟩, hqprime⟩
  have hfq1 : 1 ≤ n.factorization q := (hqprime.dvd_iff_one_le_factorization hn0).mp hqdvd
  have hsum_ge : n.factorization q ≤ Sm.sum (fun r => n.factorization r) :=
    Finset.single_le_sum (fun r _ => Nat.zero_le _) hqSm
  have hfq : n.factorization q = 1 := le_antisymm (le_trans hsum_ge hmed') hfq1
  have hrest0 : (Sm.erase q).sum (fun r => n.factorization r) = 0 := by
    have hsplit := Finset.sum_erase_add Sm (fun r => n.factorization r) hqSm
    rw [hfq] at hsplit
    omega
  have hzeroSm : ∀ r ∈ Sm.erase q, n.factorization r = 0 := by
    intro r hr
    have := Finset.single_le_sum (f := fun x => n.factorization x) (fun x _ => Nat.zero_le _) hr
    omega
  -- Step 2: every prime factor of `n` different from `q` is at least `y`
  have hlarge : ∀ r ∈ n.primeFactors, r ≠ q → y ≤ r := by
    intro r hr hrne
    by_contra hcon
    push_neg at hcon
    have hrp : r.Prime := (Nat.mem_primeFactors.mp hr).1
    have hrz : z ≤ r := hrough r hr
    have hrle : r ≤ y - 1 := Nat.le_sub_one_of_lt hcon
    have hrSm : r ∈ Sm := by
      rw [hSm, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hrz, hrle⟩, hrp⟩
    have hmem : r ∈ Sm.erase q := Finset.mem_erase.mpr ⟨hrne, hrSm⟩
    have hz := hzeroSm r hmem
    have hpos : 1 ≤ n.factorization r :=
      (hrp.dvd_iff_one_le_factorization hn0).mp (Nat.mem_primeFactors.mp hr).2.1
    omega
  -- the "large" part of `n`
  set L : Finset ℕ := n.primeFactors.erase q with hL
  have hLsub : ∀ p ∈ L, p ∈ n.primeFactors := by
    intro p hp; rw [hL] at hp; exact Finset.mem_of_mem_erase hp
  have hLne : ∀ p ∈ L, p ≠ q := by
    intro p hp; rw [hL] at hp; exact (Finset.mem_erase.mp hp).1
  have hLprime : ∀ p ∈ L, p.Prime := fun p hp => (Nat.mem_primeFactors.mp (hLsub p hp)).1
  set m : ℕ := ∏ p ∈ L, p ^ n.factorization p with hm
  have hm0 : m ≠ 0 := by
    rw [hm]
    exact ne_of_gt (Finset.prod_pos (fun p hp => pow_pos (hLprime p hp).pos _))
  have hqmL : q ∉ L := by
    rw [hL]; simp
  have hmfact : ∀ t, m.factorization t = if t ∈ L then n.factorization t else 0 := by
    intro t
    rw [hm]
    exact Commons.Data.Nat.factorization_prod_prime_pow_apply L n.factorization hLprime t
  have hn_eq : n = q * m := by
    have h := Finset.mul_prod_erase n.primeFactors (fun p : ℕ => p ^ n.factorization p) hqm
    rw [← hL, ← hm] at h
    rw [← hnprod, hfq, pow_one] at h
    exact h.symm
  have hsumL : ∑ p ∈ L, n.factorization p = ArithmeticFunction.cardFactors n - 1 := by
    have h := Finset.sum_erase_add n.primeFactors (fun p => n.factorization p) hqm
    rw [← hL, hfq, ← hΩn] at h
    omega
  have hmΩ : ArithmeticFunction.cardFactors m = ArithmeticFunction.cardFactors n - 1 := by
    have h := ArithmeticFunction.cardFactors_mul (m := q) (n := m) hqprime.ne_zero hm0
    rw [← hn_eq, ArithmeticFunction.cardFactors_apply_prime hqprime] at h
    omega
  have hmΩ2 : 2 ≤ ArithmeticFunction.cardFactors m := by omega
  have hm1 : m ≠ 1 := by
    intro h
    have hc1 : ArithmeticFunction.cardFactors 1 = 0 := by simp
    rw [h, hc1] at hmΩ2
    omega
  -- Step 3: `m ≥ y ^ Ω m`, forcing `Ω m = 2`
  have hm_ge : y ^ ArithmeticFunction.cardFactors m ≤ m := by
    have hkey : ArithmeticFunction.cardFactors m = ∑ p ∈ L, n.factorization p := by
      rw [hmΩ, hsumL]
    calc y ^ ArithmeticFunction.cardFactors m
        = ∏ p ∈ L, y ^ n.factorization p := by
          rw [hkey, Finset.prod_pow_eq_pow_sum]
      _ ≤ ∏ p ∈ L, p ^ n.factorization p := by
          apply Finset.prod_le_prod₀
          · intro p hp; exact Nat.zero_le _
          · intro p hp
            exact Nat.pow_le_pow_left (hlarge p (hLsub p hp) (hLne p hp)) _
      _ = m := hm.symm
  have hmΩ_le : ArithmeticFunction.cardFactors m ≤ 2 := by
    by_contra hcon
    push_neg at hcon
    have hm3 : y ^ 3 ≤ m :=
      le_trans (Nat.pow_le_pow_right (by omega) (by omega : 3 ≤ ArithmeticFunction.cardFactors m)) hm_ge
    have hq1 : 1 ≤ q := hqprime.one_le
    have : y ^ 3 ≤ n := by
      rw [hn_eq]
      calc y ^ 3 ≤ m := hm3
        _ = 1 * m := (one_mul m).symm
        _ ≤ q * m := Nat.mul_le_mul_right m hq1
    omega
  have hmΩeq : ArithmeticFunction.cardFactors m = 2 := le_antisymm hmΩ_le hmΩ2
  -- Step 4: prime factors of `m` are all `≥ y`
  have hlarge_m : ∀ r ∈ m.primeFactors, y ≤ r := by
    intro r hr
    have hrprime : r.Prime := (Nat.mem_primeFactors.mp hr).1
    have hrdvdm : r ∣ m := (Nat.mem_primeFactors.mp hr).2.1
    have hrdvdn : r ∣ n := by rw [hn_eq]; exact dvd_mul_of_dvd_right hrdvdm q
    have hrne : r ≠ q := by
      intro heq
      have h1 : 1 ≤ m.factorization q :=
        (hqprime.dvd_iff_one_le_factorization hm0).mp (heq ▸ hrdvdm)
      have h2 : m.factorization q = 0 := by rw [hmfact q]; simp [hqmL]
      omega
    exact hlarge r (Nat.mem_primeFactors.mpr ⟨hrprime, hrdvdn, hn0⟩) hrne
  -- Step 5: split `m` into two primes
  have hp2prim : Nat.Prime m.minFac := Nat.minFac_prime hm1
  have hp2dvd : m.minFac ∣ m := Nat.minFac_dvd m
  have hp2ne0 : m.minFac ≠ 0 := hp2prim.ne_zero
  have hquotne0 : m / m.minFac ≠ 0 := by
    intro hh
    have : m = 0 := by rw [← Nat.mul_div_cancel' hp2dvd, hh, mul_zero]
    exact hm0 this
  have hΩquot : ArithmeticFunction.cardFactors (m / m.minFac) = 1 := by
    have h := ArithmeticFunction.cardFactors_mul hp2ne0 hquotne0
    rw [Nat.mul_div_cancel' hp2dvd, ArithmeticFunction.cardFactors_apply_prime hp2prim] at h
    omega
  have hp3prim : Nat.Prime (m / m.minFac) :=
    (ArithmeticFunction.cardFactors_eq_one_iff_prime).mp hΩquot
  have hp3dvd : m / m.minFac ∣ m := by
    refine ⟨m.minFac, ?_⟩
    rw [mul_comm, Nat.mul_div_cancel' hp2dvd]
  refine ⟨q, m.minFac, m / m.minFac, hqprime, hp2prim, hp3prim, hqz, hqy, ?_, ?_, ?_⟩
  · exact hlarge_m m.minFac (Nat.mem_primeFactors.mpr ⟨hp2prim, hp2dvd, hm0⟩)
  · exact Nat.minFac_le_of_dvd hp3prim.two_le hp3dvd
  · rw [hn_eq, mul_assoc]
    congr 1
    exact (Nat.mul_div_cancel' hp2dvd).symm

end Commons.NumberTheory.Chen