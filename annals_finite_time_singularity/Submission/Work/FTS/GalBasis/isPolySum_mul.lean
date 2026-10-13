import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.ContinuousMap.Algebra
import Submission.Work.FTS.GalBasis.PolySumDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis

open scoped BigOperators

/-- A finite sum of two-variable monomials is closed under pointwise product: the product of
two monomial sums is the sum over the product index of the products of the monomials, the
exponents adding and the coefficients multiplying. -/
theorem isPolySum_mul {s : Set (ℝ × ℝ)} {g₁ g₂ : C(s, ℝ)}
    (h₁ : Work.FTS.GalBasis.IsPolySum g₁) (h₂ : Work.FTS.GalBasis.IsPolySum g₂) :
    Work.FTS.GalBasis.IsPolySum (g₁ * g₂) := by
  obtain ⟨ι, hι, a₁, b₁, c₁, hc₁⟩ := h₁
  obtain ⟨κ, hκ, a₂, b₂, c₂, hc₂⟩ := h₂
  refine ⟨ι × κ, inferInstance, fun p => a₁ p.1 + a₂ p.2, fun p => b₁ p.1 + b₂ p.2,
    fun p => c₁ p.1 * c₂ p.2, ?_⟩
  intro x
  rw [ContinuousMap.mul_apply, hc₁ x, hc₂ x, Finset.sum_mul_sum]
  rw [← Finset.sum_product', Finset.univ_product_univ]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [pow_add, pow_add]
  ring

end Work.FTS.GalBasis
