import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The triangle inequality for the coefficient convolution

The convolution `conv c d k = ∑' l, c l * d (k - l)` (`Work.Diff.STE.conv`) is estimated in
absolute value by the convolution of the absolute values,
`‖conv c d k‖ ≤ ∑' l, ‖c l‖ * ‖d (k - l)‖`.

The point of the hypotheses is that the right hand side really is a summable family (and hence
the `tsum` is finite): `c` is in `ℓ¹` and `d` is in `ℓ²`, so `d` is bounded, and
`∑' l, ‖c l‖ * ‖d (k - l)‖ ≤ (sup ‖d‖) · ∑' l, ‖c l‖`.
-/

namespace Work.Diff.STE

open scoped BigOperators

theorem norm_conv_le {ι : Type*} [Fintype ι] [DecidableEq ι] (c d : (ι → ℤ) → ℂ)
    (hc : Summable fun k : ι → ℤ => ‖c k‖) (hd : Summable fun k : ι → ℤ => ‖d k‖ ^ 2)
    (k : ι → ℤ) :
    ‖Work.Diff.STE.conv c d k‖ ≤ ∑' l : ι → ℤ, ‖c l‖ * ‖d (k - l)‖ := by
  -- `d` is bounded, since a single term of a nonnegative series is at most the whole series.
  have hbdd : ∀ m : ι → ℤ, ‖d m‖ ≤ Real.sqrt (∑' j : ι → ℤ, ‖d j‖ ^ 2) := fun m =>
    Real.le_sqrt_of_sq_le (hd.le_tsum m fun j _ => sq_nonneg ‖d j‖)
  -- hence `l ↦ ‖c l‖ * ‖d (k - l)‖` is dominated by `l ↦ ‖c l‖ * √(∑' ‖d‖²)`, which is summable.
  have hsumm : Summable fun l : ι → ℤ => ‖c l‖ * ‖d (k - l)‖ :=
    Summable.of_nonneg_of_le (fun l => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun l => mul_le_mul_of_nonneg_left (hbdd (k - l)) (norm_nonneg _))
      (hc.mul_right (Real.sqrt (∑' j : ι → ℤ, ‖d j‖ ^ 2)))
  rw [conv]
  calc ‖∑' l : ι → ℤ, c l * d (k - l)‖
      ≤ ∑' l : ι → ℤ, ‖c l * d (k - l)‖ :=
        norm_tsum_le_tsum_norm (by simpa only [norm_mul] using hsumm)
    _ = ∑' l : ι → ℤ, ‖c l‖ * ‖d (k - l)‖ :=
        tsum_congr fun l => norm_mul _ _

end Work.Diff.STE
