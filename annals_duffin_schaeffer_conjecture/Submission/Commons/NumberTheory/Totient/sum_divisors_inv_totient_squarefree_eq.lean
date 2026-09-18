import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors
import Submission.Commons.NumberTheory.Totient.totient_eq_prod_primeFactors

open scoped BigOperators
open Finset

noncomputable section

namespace Commons.NumberTheory.Totient

/-- Auxiliary function: `1/φ(d)` when `d` is squarefree and `0` otherwise. -/
private def invTotientOnSquarefree (d : ℕ) : ℝ :=
  if Squarefree d then (Nat.totient d : ℝ)⁻¹ else 0

private lemma invTotientOnSquarefree_one : invTotientOnSquarefree 1 = 1 := by
  simp [invTotientOnSquarefree]

private lemma squarefree_of_prime {p : ℕ} (hp : Nat.Prime p) : Squarefree p :=
  (Nat.prime_iff.mp hp).squarefree

private lemma invTotientOnSquarefree_prime_pow (p k : ℕ) (hp : Nat.Prime p) (hk : 2 ≤ k) :
    invTotientOnSquarefree (p ^ k) = 0 := by
  rw [invTotientOnSquarefree]
  have hns : ¬ Squarefree (p ^ k) := by
    intro hsq
    have hu : IsUnit p := hsq p (by simpa [pow_two] using (pow_dvd_pow p hk))
    exact hp.ne_one (Nat.isUnit_iff.mp hu)
  simp [hns]

private lemma invTotientOnSquarefree_mul (a b : ℕ) (hab : Nat.Coprime a b) :
    invTotientOnSquarefree (a * b) = invTotientOnSquarefree a * invTotientOnSquarefree b := by
  by_cases hab_sq : Squarefree (a * b)
  · have hsq : Squarefree a ∧ Squarefree b := (Nat.squarefree_mul hab).mp hab_sq
    have hφ : Nat.totient (a * b) = Nat.totient a * Nat.totient b := Nat.totient_mul hab
    calc
      invTotientOnSquarefree (a * b)
          = ((Nat.totient (a * b) : ℝ))⁻¹ := by simp [invTotientOnSquarefree, hab_sq]
      _ = ((Nat.totient a * Nat.totient b : ℕ) : ℝ)⁻¹ := by rw [hφ]
      _ = ((Nat.totient a : ℝ) * (Nat.totient b : ℝ))⁻¹ := by norm_num
      _ = (Nat.totient a : ℝ)⁻¹ * (Nat.totient b : ℝ)⁻¹ := mul_inv _ _
      _ = invTotientOnSquarefree a * invTotientOnSquarefree b := by
            simp [invTotientOnSquarefree, hsq.1, hsq.2]
  · have hns' : ¬ (Squarefree a ∧ Squarefree b) := fun h =>
        hab_sq ((Nat.squarefree_mul hab).mpr h)
    rcases not_and_or.mp hns' with hna | hnb
    · simp [invTotientOnSquarefree, hab_sq, hna]
    · simp [invTotientOnSquarefree, hab_sq, hnb]

private lemma totient_prod_primeFactors_squarefree (n : ℕ) (hn : n ≠ 0) (hsq : Squarefree n) :
    Nat.totient n = ∏ p ∈ n.primeFactors, Nat.totient p := by
  calc
    Nat.totient n
        = ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p - 1) :=
          Commons.NumberTheory.Totient.totient_eq_prod_primeFactors n hn
    _ = ∏ p ∈ n.primeFactors, Nat.totient p := by
          apply Finset.prod_congr rfl
          intro p hp
          have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
          have hfac : n.factorization p = 1 :=
            Nat.factorization_eq_one_of_squarefree hsq hpp (Nat.mem_primeFactors.mp hp).2.1
          have hφp : Nat.totient p = p - 1 := Nat.totient_prime hpp
          simp [hfac, hφp]

private lemma n_prod_primeFactors_squarefree (n : ℕ) (hsq : Squarefree n) :
    ∏ p ∈ n.primeFactors, (p : ℝ) = (n : ℝ) := by
  rw [← Nat.cast_prod (fun p : ℕ => p) n.primeFactors]
  rw [Nat.prod_primeFactors_of_squarefree hsq]

private lemma one_add_inv_totient_prime (p : ℕ) (hp : Nat.Prime p) :
    1 + (Nat.totient p : ℝ)⁻¹ = (p : ℝ) / (Nat.totient p : ℝ) := by
  have hp1 : 1 ≤ p := hp.one_le
  have hφ_ne : (Nat.totient p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hp.pos).ne'
  have hφp1 : Nat.totient p + 1 = p := by
    rw [Nat.totient_prime hp]
    exact Nat.sub_add_cancel hp1
  have hcast : (Nat.totient p : ℝ) + 1 = (p : ℝ) := by exact_mod_cast hφp1
  have hp_eq : (p : ℝ) = (Nat.totient p : ℝ) + 1 := hcast.symm
  rw [hp_eq, div_eq_mul_inv, add_mul, mul_inv_cancel₀ hφ_ne, one_mul]

private lemma prod_inv_one_add_squarefree (n : ℕ) (hn : n ≠ 0) (hsq : Squarefree n) :
    (∏ p ∈ n.primeFactors, (1 + (Nat.totient p : ℝ)⁻¹)) = (n : ℝ) / (Nat.totient n : ℝ) := by
  have hn_prod : ∏ p ∈ n.primeFactors, (p : ℝ) = (n : ℝ) := n_prod_primeFactors_squarefree n hsq
  have hφn_nat : Nat.totient n = ∏ p ∈ n.primeFactors, Nat.totient p :=
    totient_prod_primeFactors_squarefree n hn hsq
  have hφn_prod : ∏ p ∈ n.primeFactors, (Nat.totient p : ℝ) = (Nat.totient n : ℝ) := by
    rw [← Nat.cast_prod (fun p : ℕ => Nat.totient p) n.primeFactors]
    rw [hφn_nat]
  calc
    (∏ p ∈ n.primeFactors, (1 + (Nat.totient p : ℝ)⁻¹))
        = ∏ p ∈ n.primeFactors, ((p : ℝ) / (Nat.totient p : ℝ)) := by
          apply Finset.prod_congr rfl
          intro p hp
          exact one_add_inv_totient_prime p (Nat.prime_of_mem_primeFactors hp)
    _ = (∏ p ∈ n.primeFactors, (p : ℝ)) / (∏ p ∈ n.primeFactors, (Nat.totient p : ℝ)) := by
          rw [Finset.prod_div_distrib]
    _ = (n : ℝ) / (Nat.totient n : ℝ) := by rw [hn_prod, hφn_prod]

/-! For a nonzero squarefree natural `n`, the sum of `1/φ(d)` over all divisors `d | n` equals `n/φ(n)`.  This is the Euler-product identity `∏_{p|n}(1 + 1/(p-1)) = ∏_{p|n} p/(p-1) = n/φ(n)` (squarefree: `φ(n) = ∏(p-1)`).  Needed as the "full (untruncated) Selberg sum" in the fundamental-lemma-of-sieve main-term estimates. -/
theorem sum_divisors_inv_totient_squarefree_eq (n : ℕ) (hn : n ≠ 0) (hsq : Squarefree n) :
    (∑ d ∈ Nat.divisors n, (1 / (Nat.totient d : ℝ))) = (n : ℝ) / (Nat.totient n : ℝ) := by
  classical
  have hprod_sum :
      (∏ p ∈ n.primeFactors, (1 + invTotientOnSquarefree p)) =
        ∑ d ∈ n.divisors, invTotientOnSquarefree d := by
    exact Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors
      invTotientOnSquarefree n hn invTotientOnSquarefree_one invTotientOnSquarefree_mul
      invTotientOnSquarefree_prime_pow
  have hsum_d : (∑ d ∈ n.divisors, (1 / (Nat.totient d : ℝ))) =
      ∑ d ∈ n.divisors, invTotientOnSquarefree d := by
    apply Finset.sum_congr rfl
    intro d hd
    have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hsqd : Squarefree d := hsq.squarefree_of_dvd hdvd
    simp [invTotientOnSquarefree, hsqd]
  have hprod_p : (∏ p ∈ n.primeFactors, (1 + invTotientOnSquarefree p)) =
      ∏ p ∈ n.primeFactors, (1 + (Nat.totient p : ℝ)⁻¹) := by
    apply Finset.prod_congr rfl
    intro p hp
    have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hsp : Squarefree p := squarefree_of_prime hpp
    congr 1
    simp [invTotientOnSquarefree, hsp]
  calc
    (∑ d ∈ Nat.divisors n, (1 / (Nat.totient d : ℝ)))
        = ∑ d ∈ n.divisors, invTotientOnSquarefree d := hsum_d
    _ = ∏ p ∈ n.primeFactors, (1 + invTotientOnSquarefree p) := hprod_sum.symm
    _ = ∏ p ∈ n.primeFactors, (1 + (Nat.totient p : ℝ)⁻¹) := hprod_p
    _ = (n : ℝ) / (Nat.totient n : ℝ) := prod_inv_one_add_squarefree n hn hsq

end Commons.NumberTheory.Totient

end