import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.wt_pow_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Summability of `l ↦ a l · φ (m - l) · c (m - l)`

Let `a` be a coefficient family on the lattice `ℤ^ι` with summable weighted `ℓ¹`-norm
`∑_k ⟨k⟩^N ‖a k‖` for every `N` (`⟨k⟩² = wt k = 1 + Σ_i k_i²`), let `c` be a family with summable
square norm `∑_k ‖c k‖²`, and let `φ` have at most polynomial growth of order `M`,
`‖φ k‖ ≤ Cf · ⟨k⟩^M`.  Then for every shift `m` the "convolution-type" family

  `l ↦ a l · (φ (m - l) · c (m - l))`

is summable.

The mathematics is the elementary (and sharp) fact `ℓ¹ · ℓ² ⊆ ℓ¹`: the slowly varying inequality
for the weight, `⟨m - l⟩ ≤ 2 ⟨m⟩ ⟨l⟩`, moves the polynomial weight of `φ (m - l)` onto `l`, so that
`‖a l · φ (m - l) · c (m - l)‖ ≤ C · (⟨l⟩^M ‖a l‖) · ‖c (m - l)‖`
with `C = max Cf 0 · (2 ⟨m⟩)^M`, and the product of a nonnegative `ℓ¹`-family (`l ↦ ⟨l⟩^M ‖a l‖`,
provided by `ha M`) with a nonnegative `ℓ²`-family (`l ↦ ‖c (m - l)‖`, a shift of `c`) is summable
(the `ℓ¹` factor is bounded, and `g h ≤ g + g h²`).
-/

namespace Work.Diff.STE.B3.SymCalcStep1

open scoped BigOperators

/-- `h ≤ 1 + h ^ 2` for `h ≥ 0`. -/
private lemma le_one_add_sq {h : ℝ} : h ≤ 1 + h ^ 2 := by
  nlinarith [sq_nonneg (h - 1)]

/-- **`ℓ¹ · ℓ² ⊆ ℓ¹` (pointwise product).**  The product of a nonnegative summable family with a
nonnegative family of summable square is summable. -/
private theorem summable_mul_of_l1_l2 {α : Type*} (g h : α → ℝ)
    (hg0 : ∀ l, 0 ≤ g l) (hh0 : ∀ l, 0 ≤ h l)
    (hg : Summable g) (hh2 : Summable (fun l => h l ^ 2)) :
    Summable (fun l => g l * h l) := by
  -- a nonnegative summable family is bounded by its total mass
  have hle : ∀ l, g l ≤ ∑' l, g l := fun l => hg.le_tsum l (fun j _ => hg0 j)
  have hgh2 : Summable (fun l => g l * h l ^ 2) :=
    Summable.of_nonneg_of_le (fun l => mul_nonneg (hg0 l) (sq_nonneg (h l)))
      (fun l => mul_le_mul_of_nonneg_right (hle l) (sq_nonneg (h l)))
      (hh2.mul_left (∑' l, g l))
  refine Summable.of_nonneg_of_le (fun l => mul_nonneg (hg0 l) (hh0 l)) (fun l => ?_)
    (hg.add hgh2)
  have h1 : h l ≤ 1 + h l ^ 2 := le_one_add_sq
  calc g l * h l ≤ g l * (1 + h l ^ 2) := mul_le_mul_of_nonneg_left h1 (hg0 l)
    _ = g l + g l * h l ^ 2 := by ring

private lemma wt_neg' {ι : Type*} [Fintype ι] (l : ι → ℤ) :
    Work.Diff.STE.wt (-l) = Work.Diff.STE.wt l := by
  simp only [Work.Diff.STE.wt, Pi.neg_apply, Int.cast_neg, neg_sq]

/-- The slowly varying inequality in the form needed here:
`⟨m - l⟩ ≤ 2 ⟨m⟩ ⟨l⟩`. -/
private lemma wt_shift_le' {ι : Type*} [Fintype ι] (m l : ι → ℤ) :
    Work.Diff.STE.wt (m - l) ≤ 2 * Work.Diff.STE.wt m * Work.Diff.STE.wt l := by
  have h := Work.Diff.STE.wt_le_two_mul (m - l) m
  have heq : (m - l) - m = -l := by ext i; simp
  rw [heq, wt_neg'] at h
  linarith [h]

theorem conv_summable_of_moment_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a c φ : (ι → ℤ) → ℂ)
    (ha : ∀ N : ℕ, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖a k‖))
    (hc : Summable (fun k : ι → ℤ => ‖c k‖ ^ 2))
    (Cf : ℝ) (M : ℕ) (hφ : ∀ k : ι → ℤ, ‖φ k‖ ≤ Cf * (Work.Diff.STE.wt k) ^ M)
    (m : ι → ℤ) :
    Summable (fun l : ι → ℤ => a l * (φ (m - l) * c (m - l))) := by
  classical
  set C : ℝ := max Cf 0 * (2 * Work.Diff.STE.wt m) ^ M with hC
  have hwtm : 0 < Work.Diff.STE.wt m := Work.Diff.STE.wt_pos m
  have hCnn : 0 ≤ C := by
    rw [hC]
    exact mul_nonneg (le_max_right _ _) (pow_nonneg (by linarith) M)
  -- `l ↦ ‖c (m - l)‖` has summable square: it is `c` reindexed by the involution `l ↦ m - l`
  have hh2 : Summable (fun l : ι → ℤ => ‖c (m - l)‖ ^ 2) := by
    let σ : (ι → ℤ) ≃ (ι → ℤ) :=
      { toFun := fun l => m - l
        invFun := fun l => m - l
        left_inv := by intro l; simp
        right_inv := by intro l; simp }
    have hσ := (Equiv.summable_iff σ).2 hc
    simpa [Function.comp_def, σ] using hσ
  -- the dominating family is the product of an `ℓ¹` and an `ℓ²` family
  have hgh : Summable
      (fun l : ι → ℤ => ((Work.Diff.STE.wt l) ^ M * ‖a l‖) * ‖c (m - l)‖) :=
    summable_mul_of_l1_l2 (fun l : ι → ℤ => (Work.Diff.STE.wt l) ^ M * ‖a l‖)
      (fun l : ι → ℤ => ‖c (m - l)‖)
      (fun l => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos l)) M) (norm_nonneg _))
      (fun l => norm_nonneg _) (ha M) hh2
  refine Summable.of_norm_bounded (hgh.mul_left C) (fun l => ?_)
  -- the moment bound on `φ`, with the weight of `m - l` moved to `l`
  have hφl : ‖φ (m - l)‖ ≤ C * (Work.Diff.STE.wt l) ^ M := by
    have hshift := wt_shift_le' m l
    have h1 : (Work.Diff.STE.wt (m - l)) ^ M
        ≤ (2 * Work.Diff.STE.wt m) ^ M * (Work.Diff.STE.wt l) ^ M := by
      calc (Work.Diff.STE.wt (m - l)) ^ M
          ≤ (2 * Work.Diff.STE.wt m * Work.Diff.STE.wt l) ^ M :=
            pow_le_pow_left₀ (le_of_lt (Work.Diff.STE.wt_pos (m - l))) hshift M
        _ = (2 * Work.Diff.STE.wt m) ^ M * (Work.Diff.STE.wt l) ^ M := by rw [mul_pow]
    calc ‖φ (m - l)‖ ≤ Cf * (Work.Diff.STE.wt (m - l)) ^ M := hφ (m - l)
      _ ≤ max Cf 0 * (Work.Diff.STE.wt (m - l)) ^ M :=
          mul_le_mul_of_nonneg_right (le_max_left Cf 0)
            (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos (m - l))) M)
      _ ≤ max Cf 0 * ((2 * Work.Diff.STE.wt m) ^ M * (Work.Diff.STE.wt l) ^ M) :=
          mul_le_mul_of_nonneg_left h1 (le_max_right Cf 0)
      _ = C * (Work.Diff.STE.wt l) ^ M := by rw [hC]; ring
  simp only [norm_mul]
  calc ‖a l‖ * (‖φ (m - l)‖ * ‖c (m - l)‖)
      ≤ ‖a l‖ * ((C * (Work.Diff.STE.wt l) ^ M) * ‖c (m - l)‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hφl (norm_nonneg _)) (norm_nonneg _)
    _ = C * (((Work.Diff.STE.wt l) ^ M * ‖a l‖) * ‖c (m - l)‖) := by ring

end Work.Diff.STE.B3.SymCalcStep1
