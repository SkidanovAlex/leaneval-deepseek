import Mathlib
import Submission.Work.SG.SellingDefs

/-! ### The quadratic form of a Weyl sum `∑ B ∈ S, Bᵀ * B`

`qf` is a linear functional of its matrix argument, so the quadratic form of a finite sum of
matrices is the sum of the quadratic forms; and `qf (Bᵀ * B) v` is the squared length of
`B.mulVec v`.  Together these give the announced identity
`qf (∑ B ∈ S, Bᵀ * B) v = ∑ B ∈ S, ∑ i, (B.mulVec v i)^2`, hence nonnegativity (and strict
positivity when `1 ∈ S` and `v ≠ 0`). -/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

open scoped Matrix

/-- `qf Q v` is the dot product of `v` with `Q.mulVec v`. -/
theorem qf_eq_dotProduct (Q : IMat) (v : IVec) : qf Q v = v ⬝ᵥ (Q.mulVec v) := by
  simp [qf, bf, dotProduct, Matrix.mulVec]

/-- The quadratic form of the identity matrix is the sum of the squares of the components. -/
theorem qf_one (v : IVec) : qf (1 : IMat) v = ∑ i, (v i)^2 := by
  rw [qf_eq_dotProduct, Matrix.one_mulVec]
  simp [dotProduct, sq]

/-- The quadratic form is additive in its matrix argument: it distributes over finite sums. -/
theorem qf_finset_sum (S : Finset IMat) (f : IMat → IMat) (v : IVec) :
    qf (∑ B ∈ S, f B) v = ∑ B ∈ S, qf (f B) v := by
  simp only [qf_eq_dotProduct]
  rw [Matrix.sum_mulVec, dotProduct_sum]

/-- The quadratic form of `Bᵀ * B` is the sum of the squares of the components of `B.mulVec v`. -/
theorem qf_transpose_mul (B : IMat) (v : IVec) :
    qf (B.transpose * B) v = ∑ i, (B.mulVec v i)^2 := by
  have h := qf_conj (1 : IMat) B v
  rw [Matrix.mul_one] at h
  rw [h, qf_one]

/-- The quadratic form `qf` of the Weyl sum `∑ B ∈ S, Bᵀ * B` is the sum over `B ∈ S` of the
squared components of `B.mulVec v`; in particular it is `≥ 0`, and `> 0` when `v ≠ 0` and
`1 ∈ S`.  Useful helpers: `qf` is additive in its matrix argument
(`qf (∑ B ∈ S, f B) v = ∑ B ∈ S, qf (f B) v`), `qf (Wᵀ * Q * W) y = qf Q (W.mulVec y)` is already
proved as `Work.SG.qf_conj`, and `qf (1 : IMat) v = ∑ i, (v i)^2`. -/
theorem qf_sum_transpose_mul_eq (S : Finset IMat) (v : IVec) :
    qf (∑ B ∈ S, B.transpose * B) v = ∑ B ∈ S, ∑ i, (B.mulVec v i)^2 := by
  rw [qf_finset_sum]
  exact Finset.sum_congr rfl fun B _ => qf_transpose_mul B v

end Work.SG
