import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Submission.Commons.NumberTheory.Nat.coprime_iff_forall_primeFactors_not_dvd
import Submission.Commons.NumberTheory.Nat.prod_pm1_pm2_eq_divisor_sum
import Submission.Commons.NumberTheory.Nat.prime_dvd_finset_prod

namespace Commons.NumberTheory.Moebius

open scoped ArithmeticFunction.Moebius
open scoped BigOperators
open Finset

/-- For a squarefree `m`, the product over the distinct prime factors of `m` of
`1 - w p` equals the Möbius-weighted divisor sum: `∑_{d | m} μ(d) · ∏_{p | d} w p`.
(Non-squarefree divisors never occur since `m` is squarefree.) -/
lemma moebius_expand_squarefree (m : ℕ) (hm : Squarefree m) (w : ℕ → ℚ) :
    (∏ p ∈ m.primeFactors, (1 - w p)) =
      ∑ d ∈ m.divisors, (((ArithmeticFunction.moebius d : ℤ) : ℚ) *
        (∏ p ∈ d.primeFactors, w p)) := by
  classical
  let F : ArithmeticFunction ℚ := ArithmeticFunction.prodPrimeFactors w
  have hmult : F.IsMultiplicative := ArithmeticFunction.IsMultiplicative.prodPrimeFactors w
  have hmne : m ≠ 0 := hm.ne_zero
  have hthm := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
    (f := F) hmult (n := m) hm
  have hFp (p : ℕ) (hp : p ∈ m.primeFactors) : F p = w p := by
    have hpP : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    rw [show F p = (ArithmeticFunction.prodPrimeFactors (fun p : ℕ => w p)) p by rfl]
    rw [ArithmeticFunction.prodPrimeFactors_apply hpP.ne_zero]
    rw [Nat.Prime.primeFactors hpP]
    simp
  have hFd (d : ℕ) (hd : d ∈ m.divisors) :
      F d = ∏ p ∈ d.primeFactors, w p := by
    have hdne : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
    rw [show F d = (ArithmeticFunction.prodPrimeFactors (fun p : ℕ => w p)) d by rfl]
    rw [ArithmeticFunction.prodPrimeFactors_apply hdne]
  calc
    (∏ p ∈ m.primeFactors, (1 - w p))
        = ∏ p ∈ m.primeFactors, (1 - F p) := by
          refine Finset.prod_congr rfl ?_
          intro p hp
          simp [hFp p hp]
    _ = ∑ d ∈ m.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℚ) * F d := by
          simpa using hthm
    _ = ∑ d ∈ m.divisors, (((ArithmeticFunction.moebius d : ℤ) : ℚ) *
          (∏ p ∈ d.primeFactors, w p)) := by
          refine Finset.sum_congr rfl ?_
          intro d hd
          rw [hFd d hd]

/-- Dropping the factors of `∏_{p | ℓ} (1 − α p · [p ∤ c])` whose prime divides `c`
(the factors are `1` there) leaves the product over the primes not dividing `c`. -/
private lemma prod_primeFactors_filter (ℓ c : ℕ) (α : ℕ → ℚ) :
    (∏ p ∈ ℓ.primeFactors, (1 - α p * (if p ∣ c then 0 else 1))) =
      ∏ p ∈ ℓ.primeFactors.filter (fun p => ¬ p ∣ c), (1 - α p) := by
  classical
  set S : Finset ℕ := ℓ.primeFactors.filter (fun p => ¬ p ∣ c) with hSdef
  have hSsub : S ⊆ ℓ.primeFactors := by
    rw [hSdef]
    exact Finset.filter_subset _ _
  have hcongr : (∏ p ∈ S, (1 - α p * (if p ∣ c then 0 else 1))) = ∏ p ∈ S, (1 - α p) := by
    refine Finset.prod_congr rfl ?_
    intro p hp
    have hpndc : ¬ p ∣ c := by
      rw [hSdef] at hp
      exact (Finset.mem_filter.mp hp).2
    simp [hpndc]
  have hout (p : ℕ) (hpPF : p ∈ ℓ.primeFactors) (hpS : p ∉ S) :
      (1 - α p * (if p ∣ c then 0 else 1)) = 1 := by
    have hpc : p ∣ c := by
      by_contra hc
      exact hpS (by
        rw [hSdef]
        exact Finset.mem_filter.mpr ⟨hpPF, hc⟩)
    simp [hpc]
  calc
    (∏ p ∈ ℓ.primeFactors, (1 - α p * (if p ∣ c then 0 else 1)))
        = ∏ p ∈ S, (1 - α p * (if p ∣ c then 0 else 1)) := by
          exact (Finset.prod_subset hSsub hout).symm
    _ = ∏ p ∈ S, (1 - α p) := hcongr

/-- Pointwise expansion: for each fixed `c`, the product over the prime factors of
`ℓ` of `1 − α p · [p ∤ c]` equals the Möbius sum over the divisors `d | ℓ` that are
coprime to `c`. -/
private lemma pointwise_expand (ℓ c : ℕ) (hℓ : ℓ ≠ 0) (α : ℕ → ℚ) :
    (∏ p ∈ ℓ.primeFactors, (1 - α p * (if p ∣ c then 0 else 1))) =
      ∑ d ∈ ℓ.divisors,
        (((ArithmeticFunction.moebius d : ℤ) : ℚ) * (∏ p ∈ d.primeFactors, α p)) *
          (if Nat.Coprime c d then (1 : ℚ) else 0) := by
  classical
  let g : ℕ → ℚ := fun d => (((ArithmeticFunction.moebius d : ℤ) : ℚ) *
    (∏ p ∈ d.primeFactors, α p))
  set S : Finset ℕ := ℓ.primeFactors.filter (fun p => ¬ p ∣ c) with hSdef
  set m : ℕ := ∏ p ∈ S, p with hmdef
  have hSsub : S ⊆ ℓ.primeFactors := by
    rw [hSdef]
    exact Finset.filter_subset _ _
  have hSprime : ∀ p ∈ S, Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors (hSsub hp)
  have hPFm : m.primeFactors = S := by
    rw [hmdef]
    exact Nat.primeFactors_prod hSprime
  have hsqm : Squarefree m := by
    rw [hmdef]
    exact Commons.NumberTheory.Nat.squarefree_prod_of_prime hSprime
  have hmne : m ≠ 0 := hsqm.ne_zero
  have hmdvd : m ∣ ℓ := by
    rw [hmdef]
    calc
      (∏ p ∈ S, p) ∣ ∏ p ∈ ℓ.primeFactors, p :=
        Finset.prod_dvd_prod_of_subset S ℓ.primeFactors (fun p : ℕ => p) hSsub
      _ ∣ ℓ := Nat.prod_primeFactors_dvd ℓ
  have hcopd (d : ℕ) (hd : d ∈ m.divisors) : Nat.Coprime c d := by
    have hdm : d ∣ m := Nat.dvd_of_mem_divisors hd
    have hdne : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
    rw [Commons.NumberTheory.Nat.coprime_iff_forall_primeFactors_not_dvd (q := d) (x := c) hdne]
    intro p hp
    have hpP : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ d := (Nat.mem_primeFactors.mp hp).2.1
    have hpm : p ∣ m := dvd_trans hpd hdm
    have hpS : p ∈ S := by
      rw [← hPFm]
      exact Nat.mem_primeFactors.mpr ⟨hpP, hpm, hmne⟩
    rw [hSdef] at hpS
    exact (Finset.mem_filter.mp hpS).2
  have hmdiv_sub_U : m.divisors ⊆ (ℓ.divisors.filter (fun d : ℕ => Nat.Coprime c d)) := by
    intro d hd
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨dvd_trans (Nat.dvd_of_mem_divisors hd) hmdvd, hℓ⟩, hcopd d hd⟩
  have hnotsquarefree (d : ℕ) (hdU : d ∈ ℓ.divisors.filter (fun d : ℕ => Nat.Coprime c d))
      (hdnm : d ∉ m.divisors) : ¬ Squarefree d := by
    intro hsq
    have hdℓ : d ∣ ℓ := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hdU).1
    have hcop : Nat.Coprime c d := (Finset.mem_filter.mp hdU).2
    have hPFdS : d.primeFactors ⊆ S := by
      intro p hp
      have hpP : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
      have hpd : p ∣ d := (Nat.mem_primeFactors.mp hp).2.1
      have hpℓ : p ∣ ℓ := dvd_trans hpd hdℓ
      have hpPF : p ∈ ℓ.primeFactors := Nat.mem_primeFactors.mpr ⟨hpP, hpℓ, hℓ⟩
      have hpndc : ¬ p ∣ c := by
        by_contra hpc
        have hpg : p ∣ c.gcd d := Nat.dvd_gcd hpc hpd
        have hg : c.gcd d = 1 := (Nat.coprime_iff_gcd_eq_one.mp hcop)
        exact hpP.not_dvd_one (by simpa [hg] using hpg)
      rw [hSdef]
      exact Finset.mem_filter.mpr ⟨hpPF, hpndc⟩
    have hdvdm : d ∣ ∏ p ∈ S, p := by
      calc
        d = ∏ p ∈ d.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hsq).symm
        _ ∣ ∏ p ∈ S, p := Finset.prod_dvd_prod_of_subset d.primeFactors S (fun p : ℕ => p) hPFdS
    have hdnm' : d ∣ m := by
      rw [hmdef]
      exact hdvdm
    exact hdnm (Nat.mem_divisors.mpr ⟨hdnm', hmne⟩)
  have hgood_zero (d : ℕ) (hdU : d ∈ ℓ.divisors.filter (fun d : ℕ => Nat.Coprime c d))
      (hdnm : d ∉ m.divisors) : g d = 0 := by
    have hnsq : ¬ Squarefree d := hnotsquarefree d hdU hdnm
    have hμ : ArithmeticFunction.moebius d = 0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq
    simp [g, hμ]
  have hsum1 : (∑ d ∈ ℓ.divisors.filter (fun d : ℕ => Nat.Coprime c d), g d) = ∑ d ∈ m.divisors, g d := by
    calc
      (∑ d ∈ ℓ.divisors.filter (fun d : ℕ => Nat.Coprime c d), g d)
          = ∑ d ∈ (ℓ.divisors.filter (fun d : ℕ => Nat.Coprime c d)) \ m.divisors, g d
              + ∑ d ∈ m.divisors, g d := (Finset.sum_sdiff hmdiv_sub_U).symm
      _ = ∑ d ∈ m.divisors, g d := by
          have hzero : ∑ d ∈ (ℓ.divisors.filter (fun d : ℕ => Nat.Coprime c d)) \ m.divisors, g d = 0 := by
            apply Finset.sum_eq_zero
            intro d hd
            exact hgood_zero d (Finset.mem_sdiff.mp hd).1 (Finset.mem_sdiff.mp hd).2
          rw [hzero, zero_add]
  have hsum2 : (∑ d ∈ ℓ.divisors.filter (fun d : ℕ => Nat.Coprime c d), g d) =
      ∑ d ∈ ℓ.divisors, g d * (if Nat.Coprime c d then (1 : ℚ) else 0) := by
    calc
      (∑ d ∈ ℓ.divisors.filter (fun d : ℕ => Nat.Coprime c d), g d)
          = ∑ d ∈ ℓ.divisors, if Nat.Coprime c d then g d else 0 := by
            rw [Finset.sum_filter (p := fun d : ℕ => Nat.Coprime c d) (s := ℓ.divisors) (f := g)]
      _ = ∑ d ∈ ℓ.divisors, g d * (if Nat.Coprime c d then (1 : ℚ) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro d hd
            by_cases hcop : Nat.Coprime c d <;> simp [hcop]
  have hfinal : (∑ d ∈ m.divisors, g d) =
      ∑ d ∈ ℓ.divisors,
        (((ArithmeticFunction.moebius d : ℤ) : ℚ) * (∏ p ∈ d.primeFactors, α p)) *
          (if Nat.Coprime c d then (1 : ℚ) else 0) := by
    calc
      (∑ d ∈ m.divisors, g d) = ∑ d ∈ ℓ.divisors.filter (fun d : ℕ => Nat.Coprime c d), g d := hsum1.symm
      _ = ∑ d ∈ ℓ.divisors,
            (((ArithmeticFunction.moebius d : ℤ) : ℚ) * (∏ p ∈ d.primeFactors, α p)) *
              (if Nat.Coprime c d then (1 : ℚ) else 0) := by
            simpa [g] using hsum2
  have hprod := prod_primeFactors_filter ℓ c α
  rw [← hSdef] at hprod
  calc
    (∏ p ∈ ℓ.primeFactors, (1 - α p * (if p ∣ c then 0 else 1)))
        = ∏ p ∈ S, (1 - α p) := hprod
    _ = ∏ p ∈ m.primeFactors, (1 - α p) := by
          rw [hPFm]
    _ = ∑ d ∈ m.divisors, g d := moebius_expand_squarefree m hsqm α
    _ = ∑ d ∈ ℓ.divisors,
          (((ArithmeticFunction.moebius d : ℤ) : ℚ) * (∏ p ∈ d.primeFactors, α p)) *
            (if Nat.Coprime c d then (1 : ℚ) else 0) := hfinal

/-- Inclusion–exclusion expansion of a product of one-minus-indicator factors over
the prime factors of `ℓ`: `∏_{p | ℓ} (1 − α p · 1_{p ∤ c})` expands over the
divisors `d | ℓ` with Möbius coefficient `μ d · ∏_{p|d} α p` and the count of
`c ∈ A` coprime to `d`.  (Non-squarefree divisors contribute `μ d = 0`.) -/
theorem sum_prod_not_dvd (ℓ : ℕ) (hℓ : ℓ ≠ 0) (A : Finset ℕ) (α : ℕ → ℚ) :
    (∑ c ∈ A, ∏ p ∈ ℓ.primeFactors, (1 - α p * (if p ∣ c then 0 else 1))) =
      ∑ d ∈ ℓ.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℚ) *
        (∏ p ∈ d.primeFactors, α p) *
          ((∑ c ∈ A.filter (fun c : ℕ => Nat.Coprime c d), 1 : ℕ) : ℚ) := by
  classical
  calc
    (∑ c ∈ A, ∏ p ∈ ℓ.primeFactors, (1 - α p * (if p ∣ c then 0 else 1)))
        = ∑ c ∈ A, ∑ d ∈ ℓ.divisors,
            (((ArithmeticFunction.moebius d : ℤ) : ℚ) * (∏ p ∈ d.primeFactors, α p)) *
              (if Nat.Coprime c d then (1 : ℚ) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro c _
            exact pointwise_expand ℓ c hℓ α
    _ = ∑ d ∈ ℓ.divisors, ∑ c ∈ A,
            (((ArithmeticFunction.moebius d : ℤ) : ℚ) * (∏ p ∈ d.primeFactors, α p)) *
              (if Nat.Coprime c d then (1 : ℚ) else 0) := by
            rw [Finset.sum_comm]
    _ = ∑ d ∈ ℓ.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℚ) *
          (∏ p ∈ d.primeFactors, α p) *
            ((∑ c ∈ A.filter (fun c : ℕ => Nat.Coprime c d), 1 : ℕ) : ℚ) := by
          refine Finset.sum_congr rfl ?_
          intro d hd
          have hinner : (∑ c ∈ A,
                (((ArithmeticFunction.moebius d : ℤ) : ℚ) * (∏ p ∈ d.primeFactors, α p)) *
                  (if Nat.Coprime c d then (1 : ℚ) else 0)) =
              (((ArithmeticFunction.moebius d : ℤ) : ℚ) * (∏ p ∈ d.primeFactors, α p)) *
                ((∑ c ∈ A.filter (fun c : ℕ => Nat.Coprime c d), 1 : ℕ) : ℚ) := by
            calc
              (∑ c ∈ A,
                  (((ArithmeticFunction.moebius d : ℤ) : ℚ) * (∏ p ∈ d.primeFactors, α p)) *
                    (if Nat.Coprime c d then (1 : ℚ) else 0))
                  = (((ArithmeticFunction.moebius d : ℤ) : ℚ) * (∏ p ∈ d.primeFactors, α p)) *
                      (∑ c ∈ A, if Nat.Coprime c d then (1 : ℚ) else 0) := by
                      exact (Finset.mul_sum (s := A)
                        (f := fun c : ℕ => if Nat.Coprime c d then (1 : ℚ) else 0)
                        (a := (((ArithmeticFunction.moebius d : ℤ) : ℚ) * (∏ p ∈ d.primeFactors, α p)))).symm
                  _ = (((ArithmeticFunction.moebius d : ℤ) : ℚ) * (∏ p ∈ d.primeFactors, α p)) *
                      ((∑ c ∈ A.filter (fun c : ℕ => Nat.Coprime c d), 1 : ℕ) : ℚ) := by
                      congr 1
                      rw [Finset.sum_boole]
                      simp
          exact hinner

end Commons.NumberTheory.Moebius
