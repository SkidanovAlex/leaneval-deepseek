import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Real.Basic
import Submission.Commons.NumberTheory.Moebius.sum_moebius_divisors

namespace Commons.NumberTheory.Moebius

open scoped BigOperators

theorem sum_moebius_primeFactors_ge (z : ℝ) (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors.filter (fun d => ∀ p : ℕ, p ∈ d.primeFactors → z ≤ (p : ℝ)),
        (ArithmeticFunction.moebius d : ℝ))
      = if (∀ p : ℕ, p ∈ n.primeFactors → (p : ℝ) < z) then 1 else 0 := by
  classical
  -- `S` = the primes of `n` that are `≥ z`; we will sum over those divisors all of
  -- whose prime factors lie in `S`.
  set S : Finset ℕ := n.primeFactors.filter (fun p => z ≤ (p : ℝ)) with hSdef
  set m : ℕ := ∏ p ∈ S, p with hmdef
  have hSsub : S ⊆ n.primeFactors := Finset.filter_subset _ _
  have hSprime : ∀ p ∈ S, Nat.Prime p := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors (hSsub hp)
  have hPFm : m.primeFactors = S := by
    rw [hmdef]
    exact Nat.primeFactors_prod hSprime
  have hmdvd : m ∣ n := by
    rw [hmdef]
    exact (Finset.prod_dvd_prod_of_subset S n.primeFactors (fun p : ℕ => p) hSsub).trans
      (Nat.prod_primeFactors_dvd n)
  have hmne : m ≠ 0 := by
    rw [hmdef]
    exact Finset.prod_ne_zero_iff.mpr (fun p hp => (hSprime p hp).ne_zero)
  -- Every divisor of `m` lies in the filtered divisor set.
  have hmd_subset : m.divisors ⊆
      n.divisors.filter (fun d => ∀ p : ℕ, p ∈ d.primeFactors → z ≤ (p : ℝ)) := by
    intro d hd
    have hdm : d ∣ m := Nat.dvd_of_mem_divisors hd
    rw [Finset.mem_filter]
    refine ⟨Nat.mem_divisors.mpr ⟨dvd_trans hdm hmdvd, hn⟩, ?_⟩
    intro p hp
    have hpS : p ∈ S := hPFm ▸ Nat.primeFactors_mono hdm hmne hp
    exact (Finset.mem_filter.mp hpS).2
  -- Every divisor of `n` in the filter but not a divisor of `m` is non-squarefree.
  have hnsq : ∀ d ∈ n.divisors.filter
      (fun d => ∀ p : ℕ, p ∈ d.primeFactors → z ≤ (p : ℝ)),
      d ∉ m.divisors → ¬ Squarefree d := by
    intro d hdF hdnm hsq
    have hddvdn : d ∣ n := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hdF).1
    have hpF : ∀ p : ℕ, p ∈ d.primeFactors → z ≤ (p : ℝ) := (Finset.mem_filter.mp hdF).2
    have hPFdS : d.primeFactors ⊆ S := by
      intro p hp
      have hpP : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
      have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
      have hpn : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hpP, hpd.trans hddvdn, hn⟩
      rw [hSdef]
      exact Finset.mem_filter.mpr ⟨hpn, hpF p hp⟩
    have hdvdm : d ∣ m := by
      rw [show d = ∏ p ∈ d.primeFactors, p from (Nat.prod_primeFactors_of_squarefree hsq).symm,
        hmdef]
      exact Finset.prod_dvd_prod_of_subset d.primeFactors S (fun p : ℕ => p) hPFdS
    exact hdnm (Nat.mem_divisors.mpr ⟨hdvdm, hmne⟩)
  have hsum_eq : (∑ d ∈ n.divisors.filter
        (fun d => ∀ p : ℕ, p ∈ d.primeFactors → z ≤ (p : ℝ)),
        (ArithmeticFunction.moebius d : ℝ))
      = ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℝ) := by
    refine (Finset.sum_subset hmd_subset ?_).symm
    intro d hdF hdnm
    have hμ : ArithmeticFunction.moebius d = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree (hnsq d hdF hdnm)
    simp [hμ]
  have hsum_m : (∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℝ))
      = if m = 1 then 1 else 0 := by
    have hZ := Commons.NumberTheory.Moebius.sum_moebius_divisors m
    have hcast : (∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℝ))
        = ((∑ d ∈ m.divisors, ArithmeticFunction.moebius d : ℤ) : ℝ) := by
      push_cast
      rfl
    rw [hcast, hZ]
    split_ifs <;> simp
  have hm_eq_one_iff : m = 1 ↔ S = ∅ := by
    constructor
    · intro hm1
      by_contra hSne
      obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hSne
      have hpdvd : p ∣ m := by
        rw [hmdef]
        exact Finset.dvd_prod_of_mem (f := fun p : ℕ => p) hp
      rw [hm1] at hpdvd
      exact (hSprime p hp).not_dvd_one hpdvd
    · intro hS
      rw [hmdef, hS]
      simp
  have hS_empty_iff : (∀ p : ℕ, p ∈ n.primeFactors → (p : ℝ) < z) ↔ S = ∅ := by
    constructor
    · intro h
      rw [hSdef, Finset.eq_empty_iff_forall_notMem]
      intro p hp
      obtain ⟨hpn, hzp⟩ := Finset.mem_filter.mp hp
      exact absurd (h p hpn) (not_lt.mpr hzp)
    · intro h p hp
      by_contra hlt
      have hzp : z ≤ (p : ℝ) := not_lt.mp hlt
      have hpS : p ∈ S := by
        rw [hSdef]
        exact Finset.mem_filter.mpr ⟨hp, hzp⟩
      rw [h] at hpS
      exact Finset.notMem_empty p hpS
  rw [hsum_eq, hsum_m]
  exact if_congr (hm_eq_one_iff.trans hS_empty_iff.symm) rfl rfl

end Commons.NumberTheory.Moebius