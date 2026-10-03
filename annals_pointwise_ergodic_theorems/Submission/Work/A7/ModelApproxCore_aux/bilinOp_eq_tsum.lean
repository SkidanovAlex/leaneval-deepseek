import Mathlib
import Submission.Work.KMTAreas.A7.ModelOps

namespace Work.A7.ModelApproxCore_aux

/-- The bilinear convolution operator of `ModelOps`, written as one sum over `ℤ × ℤ`.

`bilinOp K u v x = ∑'_a ∑'_b K a b * u (x - a) * v (x - b)` unfolds definitionally into
the iterated sum; the content of the lemma is that the iterated sum may be replaced by the
sum over the product `ℤ × ℤ`, which holds because the kernel is summable (`hK`) and `u`, `v`
are bounded, so the product family is absolutely summable. -/
theorem bilinOp_eq_tsum {K : ℤ → ℤ → ℂ} {u v : ℤ → ℂ} {Cu Cv : ℝ}
    (hK : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖) (hu : ∀ y, ‖u y‖ ≤ Cu)
    (hv : ∀ y, ‖v y‖ ≤ Cv) (x : ℤ) :
    Work.KMTAreas.A7.bilinOp K u v x
      = ∑' p : ℤ × ℤ, K p.1 p.2 * u (x - p.1) * v (x - p.2) := by
  have hCu : 0 ≤ Cu := le_trans (norm_nonneg _) (hu 0)
  have hCv : 0 ≤ Cv := le_trans (norm_nonneg _) (hv 0)
  -- absolute summability of the product family, by comparison with `‖K‖ * (Cu * Cv)`
  have hFsum : Summable (fun p : ℤ × ℤ => K p.1 p.2 * u (x - p.1) * v (x - p.2)) := by
    refine Summable.of_norm_bounded (hK.mul_right (Cu * Cv)) (fun p => ?_)
    rw [norm_mul, norm_mul]
    have h1 : ‖K p.1 p.2‖ * ‖u (x - p.1)‖ ≤ ‖K p.1 p.2‖ * Cu :=
      mul_le_mul_of_nonneg_left (hu _) (norm_nonneg _)
    have h2 : ‖K p.1 p.2‖ * ‖u (x - p.1)‖ * ‖v (x - p.2)‖ ≤ ‖K p.1 p.2‖ * Cu * Cv :=
      mul_le_mul h1 (hv _) (norm_nonneg _) (mul_nonneg (norm_nonneg _) hCu)
    calc ‖K p.1 p.2‖ * ‖u (x - p.1)‖ * ‖v (x - p.2)‖
        ≤ ‖K p.1 p.2‖ * Cu * Cv := h2
      _ = ‖K p.1 p.2‖ * (Cu * Cv) := by ring
  -- Fubini for the absolutely summable product family
  rw [Work.KMTAreas.A7.bilinOp]
  exact (hFsum.tsum_prod).symm

end Work.A7.ModelApproxCore_aux
