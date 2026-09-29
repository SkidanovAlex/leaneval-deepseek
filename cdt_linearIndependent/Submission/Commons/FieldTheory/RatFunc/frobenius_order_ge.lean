import Mathlib
import Submission.Commons.FieldTheory.RatFunc.ordAtT_def
import Submission.Commons.FieldTheory.RatFunc.ordAtT_mul
import Submission.Commons.FieldTheory.RatFunc.ordAtT_algebraMap
import Submission.Commons.FieldTheory.RatFunc.le_ordAtT_finset_sum
import Submission.Commons.Algebra.Polynomial.dnum_def

namespace Commons.FieldTheory.RatFunc

open Classical
open Commons.Algebra.Polynomial
open Commons.FieldTheory.RatFunc

/-- The product rule for `ordAtT` as an inequality, valid also when one of the factors
vanishes: the order of a product is at least the sum of the orders. -/
theorem ordAtT_mul_ge {K : Type*} [Field K] (α : K) (x y : RatFunc K) :
    ordAtT α x + ordAtT α y ≤ ordAtT α (x * y) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [zero_mul]
    rw [show ordAtT α (0 : RatFunc K) = ⊤ from by simp [ordAtT]]
    simp
  rcases eq_or_ne y 0 with rfl | hy
  · rw [mul_zero]
    rw [show ordAtT α (0 : RatFunc K) = ⊤ from by simp [ordAtT]]
    simp
  · rw [ordAtT_mul α hx hy]

/-- **The one-sided Frobenius bound.**  If every polynomial coefficient `A j` has order at least
`c j` at `α` and the `e j`-th derivative of `f` has order at least `N − e j`, then the operator
`∑_j A_j · (d/dx)^{e j}` applied to `f` has order at least `M`, where `M ≤ c j + (N − e j)` for
all `j`. -/
theorem frobenius_order_ge {K : Type*} [Field K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative)
    {α : K} {f : RatFunc K} {N M : ℤ}
    {ι : Type*} (s : Finset ι) (A : ι → Polynomial K) (e : ι → ℕ) (c : ι → ℤ)
    (hA : ∀ j ∈ s, (c j : WithTop ℤ) ≤ ordAtT α (algebraMap (Polynomial K) (RatFunc K) (A j)))
    (hder : ∀ j ∈ s,
      (((N - (e j) : ℤ)) : WithTop ℤ) ≤ ordAtT α (((D : RatFunc K → RatFunc K)^[e j] f)))
    (hM : ∀ j ∈ s, M ≤ c j + (N - (e j))) :
    (M : WithTop ℤ) ≤ ordAtT α
      (∑ j ∈ s, algebraMap (Polynomial K) (RatFunc K) (A j)
        * ((D : RatFunc K → RatFunc K)^[e j] f)) := by
  apply le_ordAtT_finset_sum
  intro j hj
  calc (M : WithTop ℤ) ≤ ((c j + (N - (e j)) : ℤ) : WithTop ℤ) := by exact_mod_cast hM j hj
    _ = (c j : WithTop ℤ) + ((N - (e j) : ℤ) : WithTop ℤ) := by push_cast; rfl
    _ ≤ ordAtT α (algebraMap (Polynomial K) (RatFunc K) (A j))
          + ordAtT α (((D : RatFunc K → RatFunc K)^[e j] f)) :=
        add_le_add (hA j hj) (hder j hj)
    _ ≤ ordAtT α (algebraMap (Polynomial K) (RatFunc K) (A j)
          * ((D : RatFunc K → RatFunc K)^[e j] f)) := ordAtT_mul_ge α _ _

end Commons.FieldTheory.RatFunc
