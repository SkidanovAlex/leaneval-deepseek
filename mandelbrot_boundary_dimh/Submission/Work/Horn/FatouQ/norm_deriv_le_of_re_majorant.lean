import Mathlib

namespace Work.Horn.FatouQ

/-- **Cauchy estimate on a right half-plane with a decreasing majorant.**

If `h` is holomorphic on `{Re z > N}` and `‖h z‖ ≤ V (Re z)` there, where `V` is non-increasing
and non-negative on `[N, ∞)`, then at every point `w` with `Re w > N + 1` the derivative is
bounded by `V (Re w - 1)`.

This is Cauchy's estimate on the circle of radius `1` about `w`: that circle lies in the
half-plane (its points `z` satisfy `Re z ≥ Re w - 1 > N`), so `‖h‖ ≤ V (Re z) ≤ V (Re w - 1)`
on it, and `‖h'(w)‖ ≤ (sup ‖h‖) / 1`. -/
theorem norm_deriv_le_of_re_majorant {h : ℂ → ℂ} {N : ℝ} {V : ℝ → ℝ}
    (hdiff : DifferentiableOn ℂ h {w : ℂ | N < w.re})
    (hVanti : ∀ x y : ℝ, N ≤ x → x ≤ y → V y ≤ V x)
    (hVnn : ∀ x : ℝ, N ≤ x → 0 ≤ V x)
    (hbound : ∀ w : ℂ, N < w.re → ‖h w‖ ≤ V w.re)
    {w : ℂ} (hw : N + 1 < w.re) : ‖deriv h w‖ ≤ V (w.re - 1) := by
  have hNle : N ≤ w.re - 1 := by linarith
  have _hVnn := hVnn (w.re - 1) hNle
  -- The closed unit ball about `w` lies in the half-plane `{Re z > N}`.
  have hclosed : Metric.closedBall w 1 ⊆ {z : ℂ | N < z.re} := by
    intro z hz
    have h2 : ‖z - w‖ ≤ 1 := by
      rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hz
    have h3 : w.re - z.re ≤ 1 := by
      have h4 : |(z - w).re| ≤ ‖z - w‖ := Complex.abs_re_le_norm _
      rw [Complex.sub_re] at h4
      have h5 : -(z.re - w.re) ≤ |z.re - w.re| := neg_le_abs _
      linarith
    show N < z.re
    linarith
  -- On the unit circle about `w`, `‖h‖ ≤ V (Re w - 1)`.
  have hsphere : ∀ z ∈ Metric.sphere w 1, ‖h z‖ ≤ V (w.re - 1) := by
    intro z hz
    have hNz : N < z.re := hclosed (Metric.sphere_subset_closedBall hz)
    have hre : w.re - 1 ≤ z.re := by
      have h2 : ‖z - w‖ = 1 := by
        rw [← dist_eq_norm]; exact Metric.mem_sphere.mp hz
      have h4 : |(z - w).re| ≤ ‖z - w‖ := Complex.abs_re_le_norm _
      rw [Complex.sub_re, h2] at h4
      have h5 : -(1:ℝ) ≤ z.re - w.re := (abs_le.mp h4).1
      linarith
    exact le_trans (hbound z hNz) (hVanti (w.re - 1) z.re hNle hre)
  -- Cauchy's estimate on the circle of radius `1`.
  have hmain := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := h) (c := w) (R := 1)
    (C := V (w.re - 1)) one_pos ((hdiff.mono hclosed).diffContOnCl_ball subset_rfl) hsphere
  simpa using hmain

end Work.Horn.FatouQ
