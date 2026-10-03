import Mathlib
import Submission.Work.Peluse.MajorArc.Defs

namespace Work.Peluse.MajorArc

open scoped BigOperators

/-- Reindexing the double sum `∑_{y ∈ [1,M]} ∑_{u ∈ [-N,N]}` into
`∑_{u ∈ [-N,N]} ∑_{y ∈ [-M,M]}` with the weight `eeH M P β` (which vanishes off `[1,M]`),
for the weight `ee (β P y)` on the `y`-variable. -/
theorem reindexToTriple (N M : ℕ) (P : Polynomial ℤ) (f₀ f₁ : ℤ → ℂ) (β : ℝ) :
    (∑ y ∈ Finset.Icc (1 : ℤ) (M : ℤ), Work.Peluse.ee (β * ((P.eval y : ℤ) : ℝ)) *
        ∑ u ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          (f₀ u * Work.Peluse.ee (β * (u : ℝ))) * f₁ (u + y))
      = ∑ u ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ∑ y ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          (f₀ u * Work.Peluse.ee (β * (u : ℝ))) * Work.Peluse.eeH M P β y * f₁ (u + y) := by
  -- `[1,M] ⊆ [-M,M]`, and `eeH` vanishes off `[1,M]`, so the `y`-range may be widened.
  have hsub : Finset.Icc (1 : ℤ) (M : ℤ) ⊆ Finset.Icc (-(M : ℤ)) (M : ℤ) := by
    intro y hy
    simp only [Finset.mem_Icc] at hy ⊢
    omega
  have hinner : ∀ u : ℤ,
      (∑ y ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          (f₀ u * Work.Peluse.ee (β * (u : ℝ))) * Work.Peluse.eeH M P β y * f₁ (u + y))
        = ∑ y ∈ Finset.Icc (1 : ℤ) (M : ℤ),
          (f₀ u * Work.Peluse.ee (β * (u : ℝ))) *
            Work.Peluse.ee (β * ((P.eval y : ℤ) : ℝ)) * f₁ (u + y) := by
    intro u
    rw [← Finset.sum_subset hsub (fun y _ hyR => by
      rw [Work.Peluse.eeH_apply_of_not_mem hyR]; ring)]
    exact Finset.sum_congr rfl (fun y hy => by rw [Work.Peluse.eeH_apply_of_mem hy])
  -- Replace the inner `y`-sum on the right-hand side by the sum over `[1,M]`.
  rw [Finset.sum_congr rfl (fun u _ => hinner u)]
  -- Interchange the two sums, then rearrange the (commutative) product.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun u _ => by ring)

end Work.Peluse.MajorArc
