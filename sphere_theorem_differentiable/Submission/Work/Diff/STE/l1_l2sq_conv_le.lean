import Mathlib
import Submission.Work.Diff.STE.tsum_mul_sq_le
import Submission.Work.Diff.STE.summable_translate_conv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Young's inequality `ℓ¹ ∗ ℓ² ⊆ ℓ²` for nonnegative families on `ℤ^ι`

For nonnegative families `A`, `B` on the lattice `ι → ℤ` with `∑ A` and `∑ B²` finite,
the convolution `k ↦ ∑' l, A l * B (k - l)` is square summable and

  `∑' k, (∑' l, A l * B (k - l))² ≤ (∑' A)² * (∑' B²)`.

Proof (the classical one): the weighted Cauchy–Schwarz inequality
(`Work.Diff.STE.tsum_mul_sq_le`, applied to the weight `A` and the values `l ↦ B (k - l)`)
gives, pointwise in `k`,
`(∑' l, A l * B (k - l))² ≤ (∑' A) * (∑' l, A l * B (k - l)²)`,
and the total mass of the second factor is computed by discrete Tonelli
(`Work.Diff.STE.summable_translate_conv`):
`∑' k, ∑' l, A l * B (k - l)² = (∑' A) * (∑' B²)`.
-/

namespace Work.Diff.STE

open scoped BigOperators

theorem l1_l2sq_conv_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : (ι → ℤ) → ℝ)
    (hA0 : ∀ k, 0 ≤ A k) (hB0 : ∀ k, 0 ≤ B k)
    (hA1 : Summable (fun k : ι → ℤ => A k)) (hB2 : Summable (fun k : ι → ℤ => B k ^ 2)) :
    Summable (fun k : ι → ℤ => (∑' l : ι → ℤ, A l * B (k - l)) ^ 2) ∧
      (∑' k : ι → ℤ, (∑' l : ι → ℤ, A l * B (k - l)) ^ 2)
        ≤ (∑' k : ι → ℤ, A k) ^ 2 * (∑' k : ι → ℤ, B k ^ 2) := by
  -- `B²` is bounded by its total mass (the terms are nonnegative).
  have hbdd : ∀ m : ι → ℤ, B m ^ 2 ≤ ∑' j : ι → ℤ, B j ^ 2 := fun m =>
    hB2.le_tsum m (fun j _ => sq_nonneg (B j))
  -- Hence `l ↦ A l * B (k - l)²` is summable for each `k`, dominated by `A l * ∑' B²`.
  have hQl : ∀ k : ι → ℤ, Summable fun l : ι → ℤ => A l * B (k - l) ^ 2 := fun k =>
    Summable.of_nonneg_of_le (fun l => mul_nonneg (hA0 l) (sq_nonneg _))
      (fun l => mul_le_mul_of_nonneg_left (hbdd (k - l)) (hA0 l)) (hA1.mul_right _)
  -- Weighted Cauchy–Schwarz, pointwise in `k`.
  have hkey : ∀ k : ι → ℤ, (∑' l : ι → ℤ, A l * B (k - l)) ^ 2
      ≤ (∑' m : ι → ℤ, A m) * (∑' l : ι → ℤ, A l * B (k - l) ^ 2) := fun k =>
    tsum_mul_sq_le A (fun l : ι → ℤ => B (k - l)) hA0 (fun l => hB0 (k - l)) hA1 (hQl k)
  -- Discrete Tonelli: the total mass of `k ↦ ∑' l, A l * B (k - l)²` factors.
  have hconv := summable_translate_conv (α := ι → ℤ) A B hA0 hB0 hA1 hB2
  have hmain : Summable (fun k : ι → ℤ => (∑' l : ι → ℤ, A l * B (k - l)) ^ 2) :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _) hkey (hconv.1.mul_left _)
  refine ⟨hmain, ?_⟩
  calc (∑' k : ι → ℤ, (∑' l : ι → ℤ, A l * B (k - l)) ^ 2)
      ≤ ∑' k : ι → ℤ, (∑' m : ι → ℤ, A m) * (∑' l : ι → ℤ, A l * B (k - l) ^ 2) :=
        Summable.tsum_le_tsum hkey hmain (hconv.1.mul_left _)
    _ = (∑' m : ι → ℤ, A m) * (∑' k : ι → ℤ, ∑' l : ι → ℤ, A l * B (k - l) ^ 2) :=
        Summable.tsum_mul_left _ hconv.1
    _ = (∑' m : ι → ℤ, A m) * ((∑' m : ι → ℤ, A m) * (∑' m : ι → ℤ, B m ^ 2)) := by
        rw [hconv.2]
    _ = (∑' m : ι → ℤ, A m) ^ 2 * (∑' m : ι → ℤ, B m ^ 2) := by ring

end Work.Diff.STE
