import Mathlib

namespace Work.Peluse.TransferUp

/-- Fibrewise summation: a sum over the product `A × A` of a function of the difference
`p.2 - p.1`, where all differences lie in `B`, is the `B`-sum of the fibre cardinalities times
the value `Ψ` at the fibre label. -/
theorem sum_prod_fiberwise {A B : Finset ℤ}
    (hAB : ∀ p ∈ A.product A, p.2 - p.1 ∈ B) (Ψ : ℤ → ℂ) :
    (∑ p ∈ A.product A, Ψ (p.2 - p.1))
      = ∑ m ∈ B, (((A.product A).filter (fun p : ℤ × ℤ => p.2 - p.1 = m)).card : ℂ) * Ψ m := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to hAB (fun p : ℤ × ℤ => Ψ (p.2 - p.1))]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.mp hp).2]),
    Finset.sum_const, nsmul_eq_mul]

end Work.Peluse.TransferUp
