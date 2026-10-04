import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Summability and evaluation of a discrete convolution

For nonnegative `a`, `b : α → ℝ` on an additive group `α`, with `∑ a` and `∑ b²` finite,
the convolution `k ↦ ∑' l, a l * b (k - l)²` is summable and its total sum factors as
`(∑ a) * (∑ b²)`.

The proof is the discrete Tonelli/Fubini theorem for nonnegative terms:
`∑'_{(k,l)} a l * b (k-l)²` is identified, via the bijection `(k,l) ↦ (l, k-l)`, with
`∑'_{(l,j)} a l * b j² = (∑ a) * (∑ b²)`, and then split as an iterated sum.
-/

namespace Work.Diff.STE

open scoped BigOperators

set_option linter.unusedVariables false

theorem summable_translate_conv {α : Type*} [AddGroup α] (a b : α → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (ha' : Summable a) (hb' : Summable fun i => b i ^ 2) :
    Summable (fun k => ∑' l, a l * b (k - l) ^ 2) ∧
      (∑' k, ∑' l, a l * b (k - l) ^ 2) = (∑' i, a i) * (∑' i, b i ^ 2) := by
  have hb2nn : ∀ p : α × α, 0 ≤ a p.1 * b p.2 ^ 2 :=
    fun p => mul_nonneg (ha p.1) (sq_nonneg (b p.2))
  -- Step 1: the product-index function `(i,j) ↦ a i * b j²` is summable, with the expected sum.
  have hprod : Summable (fun p : α × α => a p.1 * b p.2 ^ 2) := by
    rw [summable_prod_of_nonneg hb2nn]
    refine ⟨fun x => hb'.mul_left (a x), ?_⟩
    have h1 : (fun x => ∑' y : α, a x * b y ^ 2) = fun x => a x * (∑' y : α, b y ^ 2) := by
      funext x
      exact tsum_mul_left
    rw [h1]
    exact ha'.mul_right _
  have hprod_tsum : (∑' p : α × α, a p.1 * b p.2 ^ 2) = (∑' i, a i) * (∑' i, b i ^ 2) := by
    rw [hprod.tsum_prod]
    have h1 : ∀ x : α, (∑' y : α, a x * b y ^ 2) = a x * (∑' y : α, b y ^ 2) :=
      fun x => tsum_mul_left
    simp_rw [h1]
    rw [tsum_mul_right]
  -- Step 2: reindex `(i,j) ↦ (i+j, i)`, i.e. inverse to `(k,l) ↦ (l, k-l)`, so that
  -- `a i * b j²` becomes `a l * b (k-l)²` with `i = l`, `j = k - l`.
  let e : α × α ≃ α × α :=
    { toFun := fun p => (p.2, p.1 - p.2)
      invFun := fun p => (p.2 + p.1, p.1)
      left_inv := by rintro ⟨k, l⟩; simp
      right_inv := by rintro ⟨l, j⟩; simp }
  have hg' : Summable ((fun p : α × α => a p.1 * b p.2 ^ 2) ∘ e) :=
    (Equiv.summable_iff e).2 hprod
  have hg : Summable (fun p : α × α => a p.2 * b (p.1 - p.2) ^ 2) := by
    simpa [e, Function.comp_def] using hg'
  have key : (∑' p : α × α, a p.2 * b (p.1 - p.2) ^ 2)
      = (∑' p : α × α, a p.1 * b p.2 ^ 2) := by
    simpa [e] using (Equiv.tsum_eq e (fun p : α × α => a p.1 * b p.2 ^ 2))
  -- Step 3: Tonelli splits the (summable) double sum, and gives the summability of the
  -- iterated sum along the first coordinate.
  refine ⟨?_, ?_⟩
  · exact ((summable_prod_of_nonneg (f := fun p : α × α => a p.2 * b (p.1 - p.2) ^ 2)
      (fun p => mul_nonneg (ha p.2) (sq_nonneg (b (p.1 - p.2))))).1 hg).2
  · rw [← hg.tsum_prod, key, hprod_tsum]

end Work.Diff.STE
