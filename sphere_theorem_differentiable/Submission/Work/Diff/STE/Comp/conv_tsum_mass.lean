import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Comp

/-- Discrete Tonelli + translation invariance for a convolution of nonnegative summable
families on `ι → ℤ`: the convolution `k ↦ ∑' l, a l * b (k - l)` is summable and its total mass
factors as `(∑ a) * (∑ b)`.

This is `Work.Diff.STE.summable_translate_conv` with `b ^ 2` replaced by `b` (that square is never
used in the proof), so the proof is a verbatim copy of that one: the product family `(i,j) ↦ a i * b j`
is summable with total `(∑ a) * (∑ b)` (`summable_prod_of_nonneg`, `tsum_prod`, `tsum_mul_left`), and
it is reindexed along the bijection `(i,j) ↦ (i+j, i)` of `(ι → ℤ) × (ι → ℤ)`, whose inverse is
`(k,l) ↦ (l, k-l)`, giving `∑'_{(k,l)}, a l * b (k-l)`; Tonelli then splits it. -/
theorem conv_tsum_mass {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : (ι → ℤ) → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (ha' : Summable a) (hb' : Summable b) :
    Summable (fun k : ι → ℤ => ∑' l : ι → ℤ, a l * b (k - l)) ∧
      (∑' k : ι → ℤ, ∑' l : ι → ℤ, a l * b (k - l)) = (∑' k : ι → ℤ, a k) * (∑' k, b k) := by
  -- Step 1: the product-index family `(i,j) ↦ a i * b j` is summable with total `(∑ a) * (∑ b)`.
  have hprod : Summable fun p : (ι → ℤ) × (ι → ℤ) => a p.1 * b p.2 :=
    Summable.mul_of_nonneg ha' hb' ha hb
  have hprod_tsum : (∑' p : (ι → ℤ) × (ι → ℤ), a p.1 * b p.2)
      = (∑' i, a i) * (∑' i, b i) :=
    (Summable.tsum_mul_tsum ha' hb' hprod).symm
  -- Step 2: reindex along `(k,l) ↦ (l, k-l)`, whose inverse is `(l,j) ↦ (l+j, l)`, so that
  -- `a i * b j` becomes `a l * b (k-l)` with `i = l`, `j = k - l`.
  let e : (ι → ℤ) × (ι → ℤ) ≃ (ι → ℤ) × (ι → ℤ) :=
    { toFun := fun p => (p.2, p.1 - p.2)
      invFun := fun p => (p.2 + p.1, p.1)
      left_inv := by rintro ⟨k, l⟩; simp
      right_inv := by rintro ⟨l, j⟩; simp }
  have hg : Summable (fun p : (ι → ℤ) × (ι → ℤ) => a p.2 * b (p.1 - p.2)) := by
    have h := (Equiv.summable_iff e).2 hprod
    simpa [e, Function.comp_def] using h
  have key : (∑' p : (ι → ℤ) × (ι → ℤ), a p.2 * b (p.1 - p.2))
      = (∑' p : (ι → ℤ) × (ι → ℤ), a p.1 * b p.2) := by
    simpa [e] using (Equiv.tsum_eq e (fun p : (ι → ℤ) × (ι → ℤ) => a p.1 * b p.2))
  -- Step 3: Tonelli splits the summable double sum; the outer sum is the convolution.
  refine ⟨?_, ?_⟩
  · exact ((summable_prod_of_nonneg (f := fun p : (ι → ℤ) × (ι → ℤ) => a p.2 * b (p.1 - p.2))
      (fun p => mul_nonneg (ha p.2) (hb (p.1 - p.2)))).1 hg).2
  · rw [← hg.tsum_prod, key, hprod_tsum]

end Work.Diff.STE.Comp
