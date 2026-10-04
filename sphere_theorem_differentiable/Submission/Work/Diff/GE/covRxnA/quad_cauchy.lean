import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Cauchy–Schwarz for a weighted array of squared sums (`quad_cauchy`)

For a finite index `κ` with weights `f : κ → ℝ` and an array
`F : κ → ι₁ → ι₂ → ι₃ → ι₄ → ℝ`,

`∑_{i j k l} (∑_m f m * F m i j k l)^2 ≤ (∑_m f m^2) * (∑_m ∑_{i j k l} (F m i j k l)^2)`.

This is the "little ℓ²" Cauchy–Schwarz inequality applied to the vector `f` against each
of the fibre vectors `(F · i j k l)`, summed over the four indices `i j k l`.

The proof is elementary: apply `Finset.sum_mul_sq_le_sq_mul_sq` to each quadruple
`(i, j, k, l)` and sum the resulting inequalities over `i j k l`; the right-hand side is a
constant `∑_m f m^2` times a sum which, after the (harmless) interchange of the `m`-sum with
the four index sums, is exactly the right-hand side of the claim.
-/

open Finset

namespace Work.Diff.GE.covRxnA

/-- Merge two nested sums as a sum over the product index type. -/
private lemma sum_curry {α β γ : Type*} [Fintype α] [Fintype β] [AddCommMonoid γ]
    (f : α → β → γ) : (∑ a, ∑ b, f a b) = ∑ p : α × β, f p.1 p.2 :=
  (Fintype.sum_prod_type (f := fun p : α × β => f p.1 p.2)).symm

/-- Merge four nested sums as a sum over the iterated product index type. -/
private lemma sum_curry4 {α β γ δ ε : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [AddCommMonoid ε] (f : α → β → γ → δ → ε) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ r : ((α × β) × γ) × δ,
      f r.1.1.1 r.1.1.2 r.1.2 r.2 := by
  rw [sum_curry, sum_curry, sum_curry]

theorem quad_cauchy
    {ι₁ ι₂ ι₃ ι₄ κ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃] [Fintype ι₄] [Fintype κ]
    (f : κ → ℝ) (F : κ → ι₁ → ι₂ → ι₃ → ι₄ → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, (∑ m, f m * F m i j k l) ^ 2
      ≤ (∑ m, f m ^ 2) * (∑ m, ∑ i, ∑ j, ∑ k, ∑ l, (F m i j k l) ^ 2) := by
  -- Cauchy–Schwarz on each fibre, then sum over the four indices.
  have h1 : ∑ i, ∑ j, ∑ k, ∑ l, (∑ m, f m * F m i j k l) ^ 2
      ≤ ∑ i, ∑ j, ∑ k, ∑ l, (∑ m, f m ^ 2) * (∑ m, (F m i j k l) ^ 2) := by
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    apply Finset.sum_le_sum; intro k _
    apply Finset.sum_le_sum; intro l _
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f (fun m => F m i j k l)
  -- The right-hand side is the constant `∑ m, f m ^ 2` times a single sum.
  have h2 : ∑ i, ∑ j, ∑ k, ∑ l, (∑ m, f m ^ 2) * (∑ m, (F m i j k l) ^ 2)
      = (∑ m, f m ^ 2) * (∑ m, ∑ i, ∑ j, ∑ k, ∑ l, (F m i j k l) ^ 2) := by
    rw [sum_curry4 (fun i j k l => (∑ m, f m ^ 2) * (∑ m, (F m i j k l) ^ 2))]
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun m _ => (sum_curry4 (fun i j k l => (F m i j k l) ^ 2)).symm)
  exact h1.trans (le_of_eq h2)

end Work.Diff.GE.covRxnA
