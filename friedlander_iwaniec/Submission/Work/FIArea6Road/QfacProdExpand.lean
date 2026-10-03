import Mathlib

namespace Work.FIArea6Road

/-- The sum over squarefree `c ≤ M` of `∏_{p | c} g p` is bounded by the full Euler product
`∏_{p ≤ M} (1 + g p)`, by expanding the product and discarding terms. -/
theorem QfacProdExpand (M : ℕ) (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p) :
    (∑ c ∈ (Finset.Icc 1 M).filter Squarefree, ∏ p ∈ c.primeFactors, g p)
      ≤ ∏ p ∈ Nat.primesBelow (M + 1), (1 + g p) := by
  classical
  rw [Finset.prod_one_add]
  set S : Finset ℕ := (Finset.Icc 1 M).filter Squarefree with hS
  have hinj : Set.InjOn Nat.primeFactors (↑S : Set ℕ) := by
    intro a ha b hb hab
    have haS : a ∈ S := Finset.mem_coe.mp ha
    have hbS : b ∈ S := Finset.mem_coe.mp hb
    rw [hS] at haS hbS
    have hsa : Squarefree a := (Finset.mem_filter.mp haS).2
    have hsb : Squarefree b := (Finset.mem_filter.mp hbS).2
    have h : (∏ p ∈ a.primeFactors, p) = (∏ p ∈ b.primeFactors, p) := by rw [hab]
    rwa [Nat.prod_primeFactors_of_squarefree hsa,
      Nat.prod_primeFactors_of_squarefree hsb] at h
  have hL : (∑ c ∈ S, ∏ p ∈ c.primeFactors, g p)
      = ∑ t ∈ S.image Nat.primeFactors, ∏ p ∈ t, g p :=
    (Finset.sum_image (s := S) (g := Nat.primeFactors)
      (f := fun t : Finset ℕ => ∏ p ∈ t, g p) hinj).symm
  rw [hL]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro t ht
    rw [hS, Finset.mem_image] at ht
    obtain ⟨c, hc, rfl⟩ := ht
    rw [Finset.mem_powerset]
    intro p hp
    have hcIcc : c ∈ Finset.Icc 1 M := (Finset.mem_filter.mp hc).1
    rw [Finset.mem_Icc] at hcIcc
    rw [Nat.mem_primesBelow]
    exact ⟨by have h := Nat.le_of_mem_primeFactors hp; omega,
      Nat.prime_of_mem_primeFactors hp⟩
  · intro t _ _
    exact Finset.prod_nonneg fun p _ => hg p

end Work.FIArea6Road
