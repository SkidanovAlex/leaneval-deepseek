/-
  Companion paper, §9: the pointwise evaluation of `g([ν²,d])` for squarefree `d`.

  This file contains the elementary number-theoretic input of the identity (9.9), namely

      `g([ν²,d]) = g(ν²) · ∏_{p | d} (if p ∣ ν then 1 else g p)`

  for a multiplicative `g`.  The core is the `Nat.lcm` identity

      `Nat.lcm (ν^2) d = ν^2 · ∏_{p ∈ d.primeFactors, p ∤ ν} p`.

  The assembly of (9.9) itself is in `Submission.ASP.S9o`.
-/
import Mathlib
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Totient
import Submission.Commons.NumberTheory.Nat.prod_pm1_pm2_eq_divisor_sum
import Submission.Commons.NumberTheory.Nat.prod_dvd_iff_all_dvd

set_option maxHeartbeats 800000

namespace Submission.ASP

open Finset

noncomputable section

/-! ### Elementary `Nat.lcm` identities for squarefree `d` -/

/-- For squarefree `d` and prime `p`, `Nat.gcd ν p` is `p` if `p ∣ ν` and `1` otherwise. -/
private lemma gcd_eq_ite (ν p : ℕ) (hp : p.Prime) :
    Nat.gcd ν p = if p ∣ ν then p else 1 := by
  by_cases h : p ∣ ν
  · rw [if_pos h, Nat.gcd_eq_right h]
  · rw [if_neg h]
    exact Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr h)

/-- For squarefree `d` and prime `p`, `d ∣ ν^2 * M` where `M` is any multiple of the primes
`p | d` with `p ∤ ν`. -/
private lemma sqfree_dvd_mul_of (d M ν : ℕ) (hd : Squarefree d)
    (hM : ∀ p ∈ d.primeFactors, ¬ p ∣ ν → p ∣ M) : d ∣ ν ^ 2 * M := by
  rw [← Nat.prod_primeFactors_of_squarefree hd]
  refine (Commons.NumberTheory.Nat.prod_dvd_iff_all_dvd (Finset.Subset.refl _)).mpr ?_
  intro p hp
  by_cases h : p ∣ ν
  · exact dvd_mul_of_dvd_left (h.trans (dvd_pow_self ν (by norm_num : 2 ≠ 0))) M
  · exact dvd_mul_of_dvd_right (hM p hp h) _

/-- **The `lcm` identity**: for squarefree `d`, `Nat.lcm (ν^2) d = ν^2 · ∏_{p | d, p ∤ ν} p`. -/
lemma lcm_sq_eq_mul_filter (d ν : ℕ) (hd : Squarefree d) :
    Nat.lcm (ν ^ 2) d
      = ν ^ 2 * ∏ p ∈ d.primeFactors.filter (fun p => ¬ p ∣ ν), p := by
  set M := ∏ p ∈ d.primeFactors.filter (fun p => ¬ p ∣ ν), p
  have hMle : M ∣ d := by
    refine (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)).trans ?_
    rw [Nat.prod_primeFactors_of_squarefree hd]
  have hcop : Nat.Coprime (ν ^ 2) M := by
    refine Nat.Coprime.pow_left _ (Nat.Coprime.prod_right fun p hp => ?_)
    exact (Nat.coprime_comm.mp ((Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).coprime_iff_not_dvd.mpr
      (Finset.mem_filter.mp hp).2))
  refine Nat.dvd_antisymm ?_ ?_
  · rw [Nat.lcm_dvd_iff]
    refine ⟨dvd_mul_right _ _, sqfree_dvd_mul_of d M ν hd ?_⟩
    intro p hp hpν
    exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨hp, hpν⟩)
  · exact hcop.mul_dvd_of_dvd_of_dvd (Nat.dvd_lcm_left _ _) (hMle.trans (Nat.dvd_lcm_right _ _))

/-! ### The pointwise evaluation of `g([ν²,d])` -/

/-- `g` of a product of distinct primes is the product of the `g`'s. -/
private lemma g_prod_primes (g : ℕ → ℝ) (hmul : ∀ a b : ℕ, Nat.Coprime a b → g (a * b) = g a * g b)
    (h1 : g 1 = 1) {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    g (∏ p ∈ s, p) = ∏ p ∈ s, g p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [h1]
  | insert a s ha ih =>
      have hpr : a.Prime := hs a (Finset.mem_insert_self a s)
      have hsp : ∀ p ∈ s, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
      have hcop : Nat.Coprime a (∏ p ∈ s, p) :=
        Nat.Coprime.prod_right fun p hp => hpr.coprime_iff_not_dvd.mpr fun h =>
          ha ((((hsp p hp).dvd_iff_eq (ne_of_gt hpr.one_lt)).mp h) ▸ hp)
      rw [Finset.prod_insert ha, Finset.prod_insert ha, hmul a _ hcop, ih hsp]

/-- **Pointwise evaluation**: for squarefree `d` and multiplicative `g`,
`g([ν²,d]) = g(ν²) · ∏_{p | d} (if p ∣ ν then 1 else g p)`. -/
theorem g_lcm_eq (g : ℕ → ℝ) (hmul : ∀ a b : ℕ, Nat.Coprime a b → g (a * b) = g a * g b)
    (h1 : g 1 = 1) {d : ℕ} (hd : Squarefree d) (ν : ℕ) :
    g (Nat.lcm (ν ^ 2) d) = g (ν ^ 2) * ∏ p ∈ d.primeFactors, (if p ∣ ν then 1 else g p) := by
  classical
  set M := ∏ p ∈ d.primeFactors.filter (fun p => ¬ p ∣ ν), p
  have hcop : Nat.Coprime (ν ^ 2) M := by
    refine Nat.Coprime.pow_left _ (Nat.Coprime.prod_right fun p hp => ?_)
    exact (Nat.coprime_comm.mp ((Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).coprime_iff_not_dvd.mpr
      (Finset.mem_filter.mp hp).2))
  have hgM : g M = ∏ p ∈ d.primeFactors.filter (fun p => ¬ p ∣ ν), g p :=
    g_prod_primes g hmul h1 fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  rw [lcm_sq_eq_mul_filter d ν hd, hmul _ _ hcop, hgM]
  congr 1
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl fun p hp => ?_
  by_cases h : p ∣ ν <;> simp [h]

end

end Submission.ASP
