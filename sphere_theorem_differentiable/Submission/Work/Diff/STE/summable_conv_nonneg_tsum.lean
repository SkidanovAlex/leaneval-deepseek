import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE

/-- Convolution of two summable nonnegative real-valued functions over an additive commutative
group: the convolution is everywhere summable, its total sum exists, and it equals the product
of the two total sums.

Proof sketch: the family `p ↦ a p.1 * b p.2` is summable on `α × α` with sum
`(∑' a) * (∑' b)` (`Summable.mul_of_nonneg`, `Summable.tsum_mul_tsum`).  Pulling it back along
the bijection `(k, m) ↦ (k - m, m)` of `α × α` identifies it with `(k, m) ↦ a (k - m) * b m`,
whose iterated summation is the convolution.  Finally `summable_prod_of_nonneg` converts
summability of the pulled-back family into the pointwise summability and the summability of the
convolution, and `Summable.tsum_prod` identifies the double sum with the iterated one. -/
theorem summable_conv_nonneg_tsum {α : Type*} [AddCommGroup α] (a b : α → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (ha' : Summable a) (hb' : Summable b) :
    (∀ k, Summable fun m => a (k - m) * b m) ∧
    Summable (fun k => ∑' m, a (k - m) * b m) ∧
      (∑' k, ∑' m, a (k - m) * b m) = (∑' i, a i) * (∑' i, b i) := by
  let e : α × α ≃ α × α :=
    { toFun := fun p => (p.1 - p.2, p.2)
      invFun := fun q => (q.1 + q.2, q.2)
      left_inv := by rintro ⟨k, m⟩; simp
      right_inv := by rintro ⟨i, m⟩; simp }
  have hbase : Summable fun q : α × α => a q.1 * b q.2 :=
    Summable.mul_of_nonneg ha' hb' ha hb
  have hG : Summable fun p : α × α => a (p.1 - p.2) * b p.2 := by
    have := (Equiv.summable_iff e).mpr hbase
    simpa [e, Function.comp_def] using this
  obtain ⟨hinner, houter⟩ := (summable_prod_of_nonneg
    (f := fun p : α × α => a (p.1 - p.2) * b p.2)
    (fun p => mul_nonneg (ha _) (hb _))).mp hG
  refine ⟨hinner, houter, ?_⟩
  have h1 : (∑' k, ∑' m, a (k - m) * b m) = ∑' p : α × α, a (p.1 - p.2) * b p.2 :=
    (Summable.tsum_prod hG).symm
  have h2 : (∑' p : α × α, a (p.1 - p.2) * b p.2) = ∑' q : α × α, a q.1 * b q.2 := by
    simpa [e] using Equiv.tsum_eq e (fun q : α × α => a q.1 * b q.2)
  have h3 : (∑' q : α × α, a q.1 * b q.2) = (∑' i, a i) * (∑' i, b i) :=
    (Summable.tsum_mul_tsum ha' hb' hbase).symm
  exact h1.trans (h2.trans h3)

end Work.Diff.STE
