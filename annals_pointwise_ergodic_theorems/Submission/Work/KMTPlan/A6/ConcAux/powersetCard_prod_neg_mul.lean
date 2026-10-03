import Mathlib

namespace Work.KMTPlan.A6.ConcAux

open Finset

/-- For every subset `t` of `(range (d+1)).erase i` of cardinality `d - l`, the product
`∏_{a ∈ t} (x₀ - (x₀ + b*a))` equals `(-1)^{d-l} * b^{d-l} * ∏_{a ∈ t} a`; summing over all such
subsets and pushing the integer cast through the sum/product gives the stated identity. -/
theorem powersetCard_prod_neg_mul (d l i : ℕ) (x₀ b : ℤ) :
    ∑ t ∈ Finset.powersetCard (d - l) ((Finset.range (d + 1)).erase i),
        ∏ a ∈ t, ((x₀ : ℚ) - ((x₀ : ℚ) + (b : ℚ) * (a : ℚ)))
      = (-1 : ℚ) ^ (d - l) * (b : ℚ) ^ (d - l)
          * ((∑ t ∈ Finset.powersetCard (d - l) ((Finset.range (d + 1)).erase i),
                ∏ a ∈ t, (a : ℤ) : ℤ) : ℚ) := by
  set s := Finset.powersetCard (d - l) ((Finset.range (d + 1)).erase i) with hs
  have hcast : ((∑ t ∈ s, ∏ a ∈ t, (a : ℤ) : ℤ) : ℚ) = ∑ t ∈ s, ∏ a ∈ t, (a : ℚ) := by
    push_cast
    rfl
  have hmain : ∑ t ∈ s, ∏ a ∈ t, ((x₀ : ℚ) - ((x₀ : ℚ) + (b : ℚ) * (a : ℚ)))
      = (-1 : ℚ) ^ (d - l) * (b : ℚ) ^ (d - l) * ∑ t ∈ s, ∏ a ∈ t, (a : ℚ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro t ht
    have hcard : t.card = d - l := (Finset.mem_powersetCard.mp (by rw [hs] at ht; exact ht)).2
    rw [show ∏ a ∈ t, ((x₀ : ℚ) - ((x₀ : ℚ) + (b : ℚ) * (a : ℚ)))
          = ∏ a ∈ t, (-((b : ℚ) * (a : ℚ))) from
        Finset.prod_congr rfl fun a _ => by ring]
    rw [Finset.prod_neg, Finset.prod_mul_distrib, Finset.prod_const, hcard]
    ring
  rw [hmain, hcast]

end Work.KMTPlan.A6.ConcAux
