import Mathlib
import Submission.Work.KMTAreas.A7.ModelOps

namespace Work.A7.ModelApproxCore_aux

/-- The `ℓ¹` bound for the linear convolution operator: if the kernel `κ` is summable and `u` is
bounded by `Cu`, then `‖(κ * u)(a)‖ ≤ ‖κ‖_{ℓ¹} · max Cu 0` for every `a : ℤ`. -/
theorem norm_convOp_le {κ u : ℤ → ℂ} {Cu : ℝ}
    (hκ : Summable fun j : ℤ => ‖κ j‖) (hu : ∀ y, ‖u y‖ ≤ Cu) (a : ℤ) :
    ‖Work.KMTAreas.A7.convOp κ u a‖ ≤ (∑' j : ℤ, ‖κ j‖) * max Cu 0 := by
  -- `hu` at `y = 0` forces `Cu ≥ 0`, so `max Cu 0 = Cu`.
  have hCu : 0 ≤ Cu := le_trans (norm_nonneg _) (hu 0)
  rw [max_eq_left hCu]
  have hsum2 : Summable fun j : ℤ => ‖κ j‖ * Cu := hκ.mul_right Cu
  have hpt : ∀ j : ℤ, ‖κ j * u (a - j)‖ ≤ ‖κ j‖ * Cu := fun j => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hu (a - j)) (norm_nonneg _)
  have hf0 : Summable fun j : ℤ => κ j * u (a - j) :=
    Summable.of_norm_bounded hsum2 hpt
  have hf : Summable fun j : ℤ => ‖κ j * u (a - j)‖ := hf0.norm
  calc ‖Work.KMTAreas.A7.convOp κ u a‖
      = ‖∑' j : ℤ, κ j * u (a - j)‖ := rfl
    _ ≤ ∑' j : ℤ, ‖κ j * u (a - j)‖ := norm_tsum_le_tsum_norm hf
    _ ≤ ∑' j : ℤ, ‖κ j‖ * Cu := Summable.tsum_le_tsum hpt hf hsum2
    _ = (∑' j : ℤ, ‖κ j‖) * Cu := tsum_mul_right

end Work.A7.ModelApproxCore_aux
