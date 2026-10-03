import Mathlib

namespace Work.Repel.R3Level0

open Metric Set

/-- **A Cauchy-estimate comparison of derivatives.**

If `f` and `g` are holomorphic on a neighbourhood `U` of `closedBall c (2r)` and agree up to `δ`
there, while `‖deriv g‖` does not drop below `2/3 ‖deriv g c‖` on `ball c r`, and
`δ ≤ r ‖deriv g c‖ / 8`, then `‖deriv f‖ ≥ ‖deriv g c‖ / 2` on `ball c r`.

The proof is Cauchy's estimate applied to `f - g` on the ball of radius `r` around a point `z`;
then `‖deriv f z - deriv g z‖ ≤ δ/r ≤ ‖deriv g c‖/8`, so
`‖deriv f z‖ ≥ ‖deriv g z‖ - ‖deriv f z - deriv g z‖ ≥ (2/3 - 1/8)‖deriv g c‖ > ‖deriv g c‖/2`. -/
theorem deriv_lower_of_close {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) {c : ℂ} {r δ : ℝ}
    (hr : 0 < r) (hsub : Metric.closedBall c (2 * r) ⊆ U)
    (hclose : ∀ z ∈ Metric.closedBall c (2 * r), ‖f z - g z‖ ≤ δ)
    (hglow : ∀ z ∈ Metric.ball c r, ‖deriv g c‖ * 2 / 3 ≤ ‖deriv g z‖)
    (hδ : δ ≤ r * ‖deriv g c‖ / 8) :
    ∀ z ∈ Metric.ball c r, ‖deriv g c‖ / 2 ≤ ‖deriv f z‖ := by
  intro z hz
  -- `z` is within `r` of `c`, so the ball of radius `r` about `z` sits inside `closedBall c (2r)`.
  have hzc_lt : dist z c < r := by simpa [Metric.mem_ball] using hz
  have hmem2 : ∀ w ∈ Metric.closedBall z r, w ∈ Metric.closedBall c (2 * r) := by
    intro w hw
    rw [Metric.mem_closedBall] at hw ⊢
    calc dist w c ≤ dist w z + dist z c := dist_triangle w z c
      _ ≤ r + r := by linarith
      _ = 2 * r := by ring
  have hmem : ∀ w ∈ Metric.closedBall z r, w ∈ U := fun w hw => hsub (hmem2 w hw)
  -- Cauchy's estimate for `f - g` on the ball `ball z r`.
  have hdiff : DifferentiableOn ℂ (f - g) U := hf.sub hg
  have hdc : DiffContOnCl ℂ (f - g) (Metric.ball z r) := hdiff.diffContOnCl_ball hmem
  have hC : ∀ w ∈ Metric.sphere z r, ‖(f - g) w‖ ≤ δ := fun w hw =>
    hclose w (hmem2 w (Metric.sphere_subset_closedBall hw))
  have hcauchy : ‖deriv (f - g) z‖ ≤ δ / r :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdc hC
  -- Differentiability at `z` identifies `deriv (f - g)` with `deriv f - deriv g`.
  have hzU : z ∈ U := by
    apply hsub
    rw [Metric.mem_closedBall]
    linarith [le_of_lt hzc_lt, hr]
  have hdf : DifferentiableAt ℂ f z := hf.differentiableAt (hU.mem_nhds hzU)
  have hdg : DifferentiableAt ℂ g z := hg.differentiableAt (hU.mem_nhds hzU)
  have hderiv : deriv (f - g) z = deriv f z - deriv g z := deriv_sub hdf hdg
  have hdist : ‖deriv f z - deriv g z‖ ≤ δ / r := by rw [← hderiv]; exact hcauchy
  have hδr : δ / r ≤ ‖deriv g c‖ / 8 := by
    rw [div_le_iff₀ hr]; linarith [hδ]
  have hlow : ‖deriv g c‖ * 2 / 3 ≤ ‖deriv g z‖ := hglow z hz
  have h1 : ‖deriv g z‖ ≤ ‖deriv f z‖ + ‖deriv f z - deriv g z‖ := by
    calc ‖deriv g z‖ = ‖deriv f z - (deriv f z - deriv g z)‖ := by ring_nf
      _ ≤ ‖deriv f z‖ + ‖deriv f z - deriv g z‖ := norm_sub_le _ _
  have hgc : 0 ≤ ‖deriv g c‖ := norm_nonneg _
  linarith

end Work.Repel.R3Level0
