import Mathlib
import Submission.Work.GM.S3.Base

namespace Work.GM.S3

/-- The iterated sum over `m₁,m₂,m₃ ∈ Finset.Icc (-K) K` with the "all three nonzero"
indicator (the truncated sum of GM (7.1)) equals the sum of `Iterm N W` over the filtered product
Finset of `ℤ × (ℤ × ℤ)`.  Route: `Finset.sum_filter` and `Finset.sum_product` twice, e.g.
`rw [Finset.sum_filter, Finset.sum_product]` and then `Finset.sum_product` again on the inner sum. -/
theorem finite_part_reindex (N : ℕ) (W : Finset ℝ) (K : ℤ) :
    (∑ m₁ ∈ Finset.Icc (-K) K, ∑ m₂ ∈ Finset.Icc (-K) K, ∑ m₃ ∈ Finset.Icc (-K) K,
        (if m₁ ≠ 0 ∧ m₂ ≠ 0 ∧ m₃ ≠ 0 then Submission.GM.Iterm N W (m₁, m₂, m₃) else 0))
      = ∑ m ∈ ((Finset.Icc (-K) K ×ˢ (Finset.Icc (-K) K ×ˢ Finset.Icc (-K) K)).filter
          (fun m : ℤ × ℤ × ℤ => m.1 ≠ 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 ≠ 0)),
        Submission.GM.Iterm N W m := by
  -- Turn the filtered sum on the right into a sum over the full product with an indicator.
  rw [Finset.sum_filter]
  -- Peel off the outer coordinate of the product `Icc ×ˢ (Icc ×ˢ Icc)`.
  rw [Finset.sum_product (Finset.Icc (-K) K) (Finset.Icc (-K) K ×ˢ Finset.Icc (-K) K)
        (fun m : ℤ × ℤ × ℤ =>
          if m.1 ≠ 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 ≠ 0 then Submission.GM.Iterm N W m else 0)]
  -- The remaining equality is between the two nested sums over the last two coordinates;
  -- the two sides are syntactically different but definitionally equal (`Prod` projections).
  apply Finset.sum_congr rfl
  intro x _
  exact (Finset.sum_product (Finset.Icc (-K) K) (Finset.Icc (-K) K)
    (fun y : ℤ × ℤ =>
      if (x, y).1 ≠ 0 ∧ (x, y).2.1 ≠ 0 ∧ (x, y).2.2 ≠ 0 then Submission.GM.Iterm N W (x, y) else 0)).symm

end Work.GM.S3
