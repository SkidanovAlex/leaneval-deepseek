import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.EltDeg

namespace Work.ORHughesFree.NaturalExtension

/-- The inverse of `ofAdd v` followed by `ofAdd w` is `ofAdd (w - v)`: rewriting the group
operation of `Multiplicative ℤ` in terms of the additive one. -/
private theorem ofAdd_inv_mul (v w : ℤ) :
    (Multiplicative.ofAdd v)⁻¹ * Multiplicative.ofAdd w = Multiplicative.ofAdd (w - v) := by
  rw [← ofAdd_neg, ← ofAdd_add]
  congr 1
  ring

/-- Convolution formula for the coefficients of a product in `U[t^{±1};τ]`, restricted to the
range `[-L, K]` which contains all the degrees occurring in `f` (by `hL`, `hK`).

Writing `f = ∑_v f_v t^v` and `g = ∑_u g_u t^u`, the coefficient of `t^w` in `f * g` is
`∑_v f_v · (t^v • g_{w-v})`; the sum over `v` only involves the degrees in which `f` is
non-zero, and these all lie in `[-L, K]` by `support_subset_Icc_image`. -/
theorem coeffElt_mul {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (f g : SkewL U) (w : ℤ) {L K : ℕ} (hL : lowDeg f ≤ L) (hK : upDeg f ≤ K) :
    coeffElt (f * g) w =
      ∑ v ∈ Finset.Icc (-(L : ℤ)) (K : ℤ),
        coeffElt f v * ((Multiplicative.ofAdd v) • coeffElt g (w - v)) := by
  classical
  -- Expand the product as a `Finsupp.sum` over the support of `f`.
  rw [coeffElt, SkewMonoidAlgebra.coeff_mul_left]
  -- The support of `f` is contained in the image of `[-L, K]` under `ofAdd`.
  rw [Finsupp.sum_of_support_subset f.coeff (support_subset_Icc_image f hL hK)
      (fun a b => b * a • g.coeff (a⁻¹ * Multiplicative.ofAdd w)) (by intro i hi; simp)]
  -- Reindex the sum along the bijection `ofAdd` between `[-L, K]` and `ofAdd '' [-L, K]`.
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl fun v _ => ?_
    simp only [coeffElt]
    rw [ofAdd_inv_mul]
  · intro a _ b _ hab
    exact Multiplicative.ofAdd.injective hab

end Work.ORHughesFree.NaturalExtension
