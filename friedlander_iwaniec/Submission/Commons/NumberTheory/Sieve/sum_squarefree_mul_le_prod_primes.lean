import Mathlib
import Submission.Commons.NumberTheory.ArithmeticFunction.g_eq_prod_primeFactors
import Submission.Commons.Data.Nat.prod_primeFactors_eq_self_of_squarefree
import Submission.Commons.Data.Nat.squarefree_prod_primes

namespace Commons.NumberTheory.Sieve

open Finset

theorem sum_squarefree_mul_le_prod_primes {f : ℕ → ℝ} (h1 : f 1 = 1) (hnn : ∀ n : ℕ, 0 ≤ f n)
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) (N : ℕ) :
    (∑ d ∈ (Finset.Icc 1 N).filter Squarefree, f d)
      ≤ ∏ p ∈ (Finset.Icc 2 N).filter Nat.Prime, (1 + f p) := by
  classical
  set P : Finset ℕ := (Finset.Icc 2 N).filter Nat.Prime with hP
  set A : Finset ℕ := (Finset.Icc 1 N).filter Squarefree with hA
  have hA_mem : ∀ d : ℕ, d ∈ A ↔ d ∈ Finset.Icc 1 N ∧ Squarefree d := by
    intro d; rw [hA, Finset.mem_filter]
  have hP_mem : ∀ p : ℕ, p ∈ P ↔ p ∈ Finset.Icc 2 N ∧ Nat.Prime p := by
    intro p; rw [hP, Finset.mem_filter]
  -- Expand the Euler product as a sum over subsets of primes.
  have hprod : ∏ p ∈ P, (1 + f p) = ∑ S ∈ P.powerset, ∏ p ∈ S, f p := by
    have hcongr : (∏ p ∈ P, (1 + f p)) = ∏ p ∈ P, (f p + (fun _ => (1 : ℝ)) p) := by
      apply Finset.prod_congr rfl
      intro p hp
      ring
    rw [hcongr, Finset.prod_add]
    simp
  have hfac : ∀ d : ℕ, Squarefree d → f d = ∏ p ∈ d.primeFactors, f p :=
    fun d hd => Commons.NumberTheory.ArithmeticFunction.g_eq_prod_primeFactors f hmul h1 hd
  -- The map d ↦ primeFactors d is injective on squarefree d.
  have hinj : Set.InjOn (fun d : ℕ => d.primeFactors) (A : Set ℕ) := by
    intro a ha b hb hab
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ((hA_mem a).mp ha).1).1
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp ((hA_mem b).mp hb).1).1
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    have hsa : Squarefree a := ((hA_mem a).mp ha).2
    have hsb : Squarefree b := ((hA_mem b).mp hb).2
    have hab' : a.primeFactors = b.primeFactors := hab
    rw [show a = ∏ p ∈ a.primeFactors, p from
        (Commons.Data.Nat.prod_primeFactors_eq_self_of_squarefree a ha0 hsa).symm,
      show b = ∏ p ∈ b.primeFactors, p from
        (Commons.Data.Nat.prod_primeFactors_eq_self_of_squarefree b hb0 hsb).symm, hab']
  -- The image lies in powerset of P.
  have hsub : A.image (fun d : ℕ => d.primeFactors) ⊆ P.powerset := by
    intro S hS
    rw [Finset.mem_powerset]
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hS
    intro p hp
    rw [hP_mem, Finset.mem_Icc]
    have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ d := (Nat.mem_primeFactors.mp hp).2.1
    have hdle : d ≤ N := (Finset.mem_Icc.mp ((hA_mem d).mp hd).1).2
    have hd0 : 0 < d := by
      have := (Finset.mem_Icc.mp ((hA_mem d).mp hd).1).1
      omega
    exact ⟨⟨hpp.two_le, le_trans (Nat.le_of_dvd hd0 hpd) hdle⟩, hpp⟩
  have h1' : ∑ S ∈ A.image (fun d : ℕ => d.primeFactors), ∏ p ∈ S, f p
      = ∑ d ∈ A, ∏ p ∈ d.primeFactors, f p :=
    Finset.sum_image hinj
  have h2' : ∑ d ∈ A, ∏ p ∈ d.primeFactors, f p = ∑ d ∈ A, f d := by
    apply Finset.sum_congr rfl
    intro d hd
    exact (hfac d ((hA_mem d).mp hd).2).symm
  have hL : ∑ d ∈ A, f d = ∑ S ∈ A.image (fun d : ℕ => d.primeFactors), ∏ p ∈ S, f p :=
    (h1'.trans h2').symm
  have hcmp : ∑ S ∈ A.image (fun d : ℕ => d.primeFactors), ∏ p ∈ S, f p
      ≤ ∑ S ∈ P.powerset, ∏ p ∈ S, f p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun S _ _ => Finset.prod_nonneg (fun p _ => hnn p))
  have hprod' : (∑ S ∈ P.powerset, ∏ p ∈ S, f p) = ∏ p ∈ P, (1 + f p) := hprod.symm
  calc ∑ d ∈ A, f d
      = ∑ S ∈ A.image (fun d : ℕ => d.primeFactors), ∏ p ∈ S, f p := hL
    _ ≤ ∑ S ∈ P.powerset, ∏ p ∈ S, f p := hcmp
    _ ≤ ∏ p ∈ P, (1 + f p) := le_of_eq hprod'

end Commons.NumberTheory.Sieve
