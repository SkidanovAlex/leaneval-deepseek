import Mathlib

namespace Work.ChenPlan.H1

open Finset

/-- Expansion of an Euler product over a finite set as the sum over all its subsets: this is the
`f = 1`, `g = c` case of `Finset.prod_add`, proved directly by induction on the finite set. -/
private lemma prod_one_add_eq_sum_powerset (T : Finset ℕ) (c : ℕ → ℝ) :
    ∏ p ∈ T, (1 + c p) = ∑ S ∈ T.powerset, ∏ p ∈ S, c p := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ih, Finset.sum_powerset_insert ha, add_mul, one_mul]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro S hS
    have haS : a ∉ S := fun h => ha (Finset.mem_powerset.mp hS h)
    rw [Finset.prod_insert haS]

/-- Euler-product domination for the divisors of a squarefree number: the sum over the divisors
`d ≤ N` of `P` of the product of `c` over `d.primeFactors` is at most the Euler product over the
primes `p ≤ N` dividing `P`.

Useful ingredients: `Nat.prod_primeFactors_of_squarefree` (`∏ p ∈ n.primeFactors, p = n` for
squarefree `n`), injectivity of `n ↦ n.primeFactors` on squarefree numbers, and
`Finset.prod_add` (expanding `∏ p ∈ T, (1 + c p)` as a sum over subsets of `T`). -/
theorem sum_divisors_primeFactors_prod_le (P N : ℕ) (c : ℕ → ℝ)
    (hP : Squarefree P) (hc : ∀ p, 0 ≤ c p) :
    (∑ d ∈ P.divisors.filter (fun d : ℕ => d ≤ N), ∏ p ∈ d.primeFactors, c p)
      ≤ ∏ p ∈ P.primeFactors.filter (fun p : ℕ => p ≤ N), (1 + c p) := by
  classical
  rw [prod_one_add_eq_sum_powerset]
  have hne : P ≠ 0 := hP.ne_zero
  have hinj : Set.InjOn (fun d : ℕ => d.primeFactors)
      ↑(P.divisors.filter (fun d : ℕ => d ≤ N)) := by
    intro d hd e he hde
    have hd' : d ∈ P.divisors.filter (fun d : ℕ => d ≤ N) := hd
    have he' : e ∈ P.divisors.filter (fun d : ℕ => d ≤ N) := he
    have hde' : d.primeFactors = e.primeFactors := hde
    have hdvd : d ∣ P := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd').1
    have hedvd : e ∣ P := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp he').1
    rw [← Nat.prod_primeFactors_of_squarefree (hP.squarefree_of_dvd hdvd), hde',
      Nat.prod_primeFactors_of_squarefree (hP.squarefree_of_dvd hedvd)]
  have hsum : (∑ d ∈ P.divisors.filter (fun d : ℕ => d ≤ N), ∏ p ∈ d.primeFactors, c p)
      = ∑ S ∈ (P.divisors.filter (fun d : ℕ => d ≤ N)).image (fun d : ℕ => d.primeFactors),
          ∏ p ∈ S, c p := by
    rw [Finset.sum_image hinj]
  rw [hsum]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro S hS
    rcases Finset.mem_image.mp hS with ⟨d, hd, hfd⟩
    rw [← hfd, Finset.mem_powerset]
    have hd' : d ∈ P.divisors.filter (fun d : ℕ => d ≤ N) := hd
    obtain ⟨hddiv, hdle⟩ := Finset.mem_filter.mp hd'
    intro p hp
    rw [Finset.mem_filter]
    obtain ⟨hpp, hpdvd, hdne⟩ := Nat.mem_primeFactors.mp hp
    exact ⟨Nat.mem_primeFactors.mpr ⟨hpp, hpdvd.trans (Nat.dvd_of_mem_divisors hddiv), hne⟩,
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hdne) hpdvd).trans hdle⟩
  · intro S _ _
    exact Finset.prod_nonneg (fun p _ => hc p)

end Work.ChenPlan.H1
