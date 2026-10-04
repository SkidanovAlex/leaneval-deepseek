import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.norm_conv_le
import Submission.Work.Diff.STE.summable_translate_conv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Summability of the norm of a discrete convolution

If `c` and `d` are absolutely summable families of complex numbers indexed by the lattice
`ι → ℤ`, then so is the convolution `k ↦ ∑' l, c l * d (k - l)` (`Work.Diff.STE.conv`).

The point is the elementary `ℓ¹ * ℓ¹ ⊆ ℓ¹` estimate: the convolution of two absolutely
summable families of *nonnegative reals* is summable, which is proved here by Tonelli
(`summable_prod_of_nonneg`) together with the reindexing `(k,l) ↦ (l, k - l)` of `α × α`
(an involutive-inverse pair on an additive group).  The result for complex coefficients
follows by comparing `‖conv c d k‖` with the nonnegative convolution of the norms
(`Work.Diff.STE.norm_conv_le`).
-/

namespace Work.Diff.STE

open scoped BigOperators

/-- The convolution `k ↦ ∑' l, a l * b (k - l)` of two summable nonnegative real families
on an additive group is summable. -/
private lemma summable_conv_of_nonneg {α : Type*} [AddGroup α] (a b : α → ℝ)
    (ha : Summable a) (hb : Summable b) (ha0 : ∀ i, 0 ≤ a i) (hb0 : ∀ i, 0 ≤ b i) :
    Summable fun k => ∑' l, a l * b (k - l) := by
  -- The product family `(i,j) ↦ a i * b j` is summable (Tonelli on a product of nonnegative
  -- summable families).
  have hnn : 0 ≤ fun p : α × α => a p.1 * b p.2 :=
    fun p => mul_nonneg (ha0 p.1) (hb0 p.2)
  have hprod : Summable fun p : α × α => a p.1 * b p.2 := by
    rw [summable_prod_of_nonneg hnn]
    refine ⟨fun x => hb.mul_left (a x), ?_⟩
    have hsplit : (fun x : α => ∑' y : α, a x * b y) = fun x => a x * (∑' y : α, b y) :=
      funext fun x => tsum_mul_left
    rw [hsplit]
    exact ha.mul_right _
  -- Reindex `(i,j) ↦ (i + j, i)`, inverse to `(k,l) ↦ (l, k - l)`, which turns
  -- `a i * b j` into `a l * b (k - l)`.
  let e : α × α ≃ α × α :=
    { toFun := fun p => (p.2, p.1 - p.2)
      invFun := fun q => (q.2 + q.1, q.1)
      left_inv := by rintro ⟨k, l⟩; simp
      right_inv := by rintro ⟨i, j⟩; simp }
  have hg' : Summable ((fun p : α × α => a p.1 * b p.2) ∘ e) := (Equiv.summable_iff e).2 hprod
  have hg : Summable fun p : α × α => a p.2 * b (p.1 - p.2) := by
    simpa [e, Function.comp_def] using hg'
  have hgnn : 0 ≤ fun p : α × α => a p.2 * b (p.1 - p.2) :=
    fun p => mul_nonneg (ha0 p.2) (hb0 (p.1 - p.2))
  -- Tonelli then yields the summability of the iterated sum over the second coordinate.
  exact ((summable_prod_of_nonneg hgnn).1 hg).2

theorem summable_conv_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c d : (ι → ℤ) → ℂ) (hc : Summable (fun k : ι → ℤ => ‖c k‖))
    (hd : Summable (fun k : ι → ℤ => ‖d k‖)) :
    Summable (fun k : ι → ℤ => ‖Work.Diff.STE.conv c d k‖) := by
  -- Summability of the norms is stronger than the `ℓ²` hypothesis of `norm_conv_le`:
  -- `‖d k‖ ≤ ∑' j, ‖d j‖`, hence `‖d k‖ ^ 2 ≤ (∑' j, ‖d j‖) * ‖d k‖`.
  have hd2 : Summable fun k : ι → ℤ => ‖d k‖ ^ 2 := by
    have hbdd : ∀ k : ι → ℤ, ‖d k‖ ≤ ∑' j : ι → ℤ, ‖d j‖ :=
      fun k => hd.le_tsum k (fun j _ => norm_nonneg _)
    have hsq : Summable fun k : ι → ℤ => ‖d k‖ * ‖d k‖ :=
      Summable.of_nonneg_of_le (fun k => mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (fun k => mul_le_mul_of_nonneg_right (hbdd k) (norm_nonneg _))
        (hd.mul_left (∑' j : ι → ℤ, ‖d j‖))
    simpa [sq] using hsq
  -- The absolute convolution dominates `‖conv c d k‖` pointwise and is summable.
  have hconv : Summable fun k : ι → ℤ => ∑' l : ι → ℤ, ‖c l‖ * ‖d (k - l)‖ :=
    summable_conv_of_nonneg (fun l : ι → ℤ => ‖c l‖) (fun l : ι → ℤ => ‖d l‖) hc hd
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  exact Summable.of_nonneg_of_le (fun k => norm_nonneg _)
    (fun k => norm_conv_le c d hc hd2 k) hconv

end Work.Diff.STE
