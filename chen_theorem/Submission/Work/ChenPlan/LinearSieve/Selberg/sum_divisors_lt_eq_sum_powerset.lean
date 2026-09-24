import Mathlib

/-!
# Divisors of a squarefree `P` vs. subsets of `P.primeFactors`

For `P` squarefree, the divisors of `P` are exactly the products `∏ p ∈ S, p` over subsets
`S ⊆ P.primeFactors`, and for such a divisor `d` one has `d.primeFactors = S`. Hence summing a
function `F` of `d.primeFactors` over the divisors `d < ξ` of `P` is the same as summing `F S`
over the subsets `S ⊆ P.primeFactors` with `∏ p ∈ S, p < ξ`.
-/

open Finset

namespace Work.ChenPlan.LinearSieve.Selberg

theorem sum_divisors_lt_eq_sum_powerset (P : ℕ) (hsq : Squarefree P) (ξ : ℝ) (F : Finset ℕ → ℝ) :
    (∑ d ∈ P.divisors.filter (fun d : ℕ => (d : ℝ) < ξ), F d.primeFactors)
      = ∑ S ∈ P.primeFactors.powerset.filter (fun S => ((∏ p ∈ S, p : ℕ) : ℝ) < ξ), F S := by
  have hP0 : P ≠ 0 := hsq.ne_zero
  refine Finset.sum_bij (fun d _ => d.primeFactors) ?_ ?_ ?_ ?_
  · -- `d ↦ d.primeFactors` maps the filtered divisors into the filtered powerset
    intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdvd, -⟩, hlt⟩ := hd
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
    · exact Nat.primeFactors_mono hdvd hP0
    · rw [Nat.prod_primeFactors_of_squarefree (hsq.squarefree_of_dvd hdvd)]
      exact hlt
  · -- injectivity on the divisors of a squarefree number
    intro a ha b hb hab
    have hda : a ∣ P := (Nat.mem_divisors.mp (Finset.mem_filter.mp ha).1).1
    have hdb : b ∣ P := (Nat.mem_divisors.mp (Finset.mem_filter.mp hb).1).1
    rw [← Nat.prod_primeFactors_of_squarefree (hsq.squarefree_of_dvd hda),
        ← Nat.prod_primeFactors_of_squarefree (hsq.squarefree_of_dvd hdb), hab]
  · -- surjectivity: the inverse map is `S ↦ ∏ p ∈ S, p`
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨hsub, hlt⟩ := hS
    refine ⟨∏ p ∈ S, p, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_, hP0⟩, ?_⟩
      · calc ∏ p ∈ S, p ∣ ∏ p ∈ P.primeFactors, p := Finset.prod_dvd_prod_of_subset _ _ _ hsub
          _ = P := Nat.prod_primeFactors_of_squarefree hsq
      · simpa using hlt
    · exact Nat.primeFactors_prod (fun p hp => (Nat.mem_primeFactors.mp (hsub hp)).1)
  · intro a ha
    rfl

end Work.ChenPlan.LinearSieve.Selberg
