import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.tsum_mul_sq_le
import Submission.Work.Diff.STE.summable_translate_conv
import Submission.Work.Diff.STE.norm_conv_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Young's inequality `ℓ¹ ∗ ℓ² ⊆ ℓ²` for coefficient families on `ℤ^ι`

This is the Fourier-side ingredient of Layer A of the short-time-existence development: the
convolution `conv c d` (the coefficient family of a pointwise product) of a family with summable
`ℓ¹`-norm `‖c‖₁ = ∑' ‖c‖` and a family with summable `ℓ²`-norm squared `∑' ‖d‖²` again has
summable squared norm, bounded by `‖c‖₁² · ∑' ‖d‖²`.
-/

namespace Work.Diff.STE

open scoped BigOperators

theorem conv_l2_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c d : (ι → ℤ) → ℂ) (hc : Summable fun k : ι → ℤ => ‖c k‖)
    (hd : Summable fun k : ι → ℤ => ‖d k‖ ^ 2) :
    Summable (fun k : ι → ℤ => ‖Work.Diff.STE.conv c d k‖ ^ 2) ∧
      ∑' k : ι → ℤ, ‖Work.Diff.STE.conv c d k‖ ^ 2
        ≤ (∑' k : ι → ℤ, ‖c k‖) ^ 2 * ∑' k : ι → ℤ, ‖d k‖ ^ 2 := by
  -- `d` is bounded, because a single term is dominated by the sum of the (nonnegative) series.
  have hbdd : ∀ m : ι → ℤ, ‖d m‖ ^ 2 ≤ ∑' j : ι → ℤ, ‖d j‖ ^ 2 := fun m =>
    hd.le_tsum m fun j _ => sq_nonneg ‖d j‖
  -- the inner families `l ↦ ‖c l‖ * ‖d (k - l)‖ ^ 2` are summable (dominated by `‖c‖ * B`)
  have hQl : ∀ k : ι → ℤ, Summable fun l : ι → ℤ => ‖c l‖ * ‖d (k - l)‖ ^ 2 := by
    intro k
    refine Summable.of_nonneg_of_le (fun l => mul_nonneg (norm_nonneg _) (sq_nonneg _))
      (fun l => mul_le_mul_of_nonneg_left (hbdd (k - l)) (norm_nonneg _))
      (hc.mul_right (∑' j : ι → ℤ, ‖d j‖ ^ 2))
  -- weighted Cauchy--Schwarz, pointwise in `k`
  have hkey : ∀ k : ι → ℤ, (∑' l : ι → ℤ, ‖c l‖ * ‖d (k - l)‖) ^ 2
      ≤ (∑' m : ι → ℤ, ‖c m‖) * (∑' l : ι → ℤ, ‖c l‖ * ‖d (k - l)‖ ^ 2) := fun k =>
    tsum_mul_sq_le (fun l : ι → ℤ => ‖c l‖) (fun l : ι → ℤ => ‖d (k - l)‖)
      (fun l => norm_nonneg _) (fun l => norm_nonneg _) hc (hQl k)
  -- Tonelli + translation invariance: the total mass of `k ↦ ∑' l, ‖c l‖ * ‖d (k - l)‖ ^ 2`
  have hconv := summable_translate_conv (α := ι → ℤ) (fun l : ι → ℤ => ‖c l‖)
    (fun l : ι → ℤ => ‖d l‖) (fun l => norm_nonneg _) (fun l => norm_nonneg _) hc hd
  -- the squared majorant of `conv c d` is summable, by comparison with `‖c‖₁ * Q`
  have hP2summ : Summable fun k : ι → ℤ => (∑' l : ι → ℤ, ‖c l‖ * ‖d (k - l)‖) ^ 2 :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => hkey k) (hconv.1.mul_left _)
  have hP2bound : (∑' k : ι → ℤ, (∑' l : ι → ℤ, ‖c l‖ * ‖d (k - l)‖) ^ 2)
      ≤ (∑' k : ι → ℤ, ‖c k‖) ^ 2 * ∑' k : ι → ℤ, ‖d k‖ ^ 2 := by
    have h1 : (∑' k : ι → ℤ, (∑' l : ι → ℤ, ‖c l‖ * ‖d (k - l)‖) ^ 2)
        ≤ ∑' k : ι → ℤ,
            (∑' m : ι → ℤ, ‖c m‖) * (∑' l : ι → ℤ, ‖c l‖ * ‖d (k - l)‖ ^ 2) :=
      Summable.tsum_le_tsum (fun k => hkey k) hP2summ (hconv.1.mul_left _)
    have h2 : (∑' k : ι → ℤ,
          (∑' m : ι → ℤ, ‖c m‖) * (∑' l : ι → ℤ, ‖c l‖ * ‖d (k - l)‖ ^ 2))
        = (∑' m : ι → ℤ, ‖c m‖) * (∑' k : ι → ℤ, ∑' l : ι → ℤ, ‖c l‖ * ‖d (k - l)‖ ^ 2) :=
      Summable.tsum_mul_left _ hconv.1
    refine h1.trans (le_of_eq ?_)
    rw [h2, hconv.2, pow_two, mul_assoc]
  -- triangle inequality for the convolution, then compare termwise
  have hpoint : ∀ k : ι → ℤ, ‖conv c d k‖ ^ 2
      ≤ (∑' l : ι → ℤ, ‖c l‖ * ‖d (k - l)‖) ^ 2 := fun k =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_conv_le c d hc hd k) 2
  have hsumm : Summable fun k : ι → ℤ => ‖conv c d k‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _) hpoint hP2summ
  exact ⟨hsumm, (Summable.tsum_le_tsum hpoint hsumm hP2summ).trans hP2bound⟩

end Work.Diff.STE
