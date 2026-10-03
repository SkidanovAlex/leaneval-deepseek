import Mathlib

/-!
# `Work.Pert.Ksub2.norm_sub_le_of_deriv_close_far`

Far-field Lipschitz estimate: if `f : ℂ → ℂ` is complex differentiable on the exterior
`{‖w‖ ≥ R}` and its derivative is `1` up to an error `C / ‖w‖²`, then on any disc of radius
`‖z‖/2` centred at a point `z` with `‖z‖ ≥ 2R` (so that the whole disc and every chord in it
avoid the inner disc of radius `R`), `f` is Lipschitz with constant `1 + 4 C / ‖z‖²`.

The proof is the convex mean value inequality (`Convex.norm_image_sub_le_of_norm_deriv_le`)
applied to `f - id` on the closed ball `closedBall z (‖z‖/2)`: on that ball `‖w‖ ≥ ‖z‖/2`,
hence `‖deriv (f - id) w‖ = ‖deriv f w - 1‖ ≤ C / ‖w‖² ≤ 4 C / ‖z‖²`.
-/

namespace Work.Pert.Ksub2

theorem norm_sub_le_of_deriv_close_far {f : ℂ → ℂ} {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (hdiff : ∀ w : ℂ, R ≤ ‖w‖ → DifferentiableAt ℂ f w)
    (hder : ∀ w : ℂ, R ≤ ‖w‖ → ‖deriv f w - 1‖ ≤ C / ‖w‖ ^ 2) :
    ∀ z : ℂ, 2 * R ≤ ‖z‖ → ∀ x y : ℂ, ‖x - z‖ ≤ ‖z‖ / 2 → ‖y - z‖ ≤ ‖z‖ / 2 →
      ‖f x - f y‖ ≤ (1 + 4 * C / ‖z‖ ^ 2) * ‖x - y‖ := by
  intro z hz x y hx hy
  have hzpos : 0 < ‖z‖ := by linarith
  set r : ℝ := ‖z‖ / 2 with hrdef
  have hrpos : 0 < r := by rw [hrdef]; linarith
  have hRr : R ≤ r := by rw [hrdef]; linarith
  set s : Set ℂ := Metric.closedBall z r with hsdef
  have hconv : Convex ℝ s := by rw [hsdef]; exact convex_closedBall z r
  have hxs : x ∈ s := by rw [hsdef, Metric.mem_closedBall, dist_eq_norm, hrdef]; exact hx
  have hys : y ∈ s := by rw [hsdef, Metric.mem_closedBall, dist_eq_norm, hrdef]; exact hy
  -- Every point of the ball has norm at least `r = ‖z‖/2 ≥ R`.
  have hnorm_ge : ∀ w ∈ s, r ≤ ‖w‖ := by
    intro w hw
    rw [hrdef]
    rw [hsdef, Metric.mem_closedBall, dist_eq_norm] at hw
    have h1 : ‖z‖ - ‖w‖ ≤ ‖z - w‖ := norm_sub_norm_le z w
    have h2 : ‖z - w‖ = ‖w - z‖ := norm_sub_rev z w
    rw [h2] at h1
    linarith
  -- `f - id` is differentiable on the ball.
  have hgdiff : ∀ w ∈ s, DifferentiableAt ℂ (f - id) w := by
    intro w hw
    exact (hdiff w (le_trans hRr (hnorm_ge w hw))).sub differentiableAt_id
  -- and its derivative is bounded by `4 C / ‖z‖²` there.
  have hgbound : ∀ w ∈ s, ‖deriv (f - id) w‖ ≤ 4 * C / ‖z‖ ^ 2 := by
    intro w hw
    have hwR : R ≤ ‖w‖ := le_trans hRr (hnorm_ge w hw)
    have hwge : r ≤ ‖w‖ := hnorm_ge w hw
    have hd : deriv (f - id) w = deriv f w - 1 := by
      rw [deriv_sub (hdiff w hwR) differentiableAt_id, deriv_id]
    rw [hd]
    have h1 : C / ‖w‖ ^ 2 ≤ C / r ^ 2 := by
      refine div_le_div_of_nonneg_left hC (by positivity) ?_
      exact pow_le_pow_left₀ hrpos.le hwge 2
    have h2 : C / r ^ 2 = 4 * C / ‖z‖ ^ 2 := by
      rw [hrdef]
      field_simp
      ring
    calc ‖deriv f w - 1‖ ≤ C / ‖w‖ ^ 2 := hder w hwR
      _ ≤ C / r ^ 2 := h1
      _ = 4 * C / ‖z‖ ^ 2 := h2
  -- Convex mean value inequality.
  have hmvt : ‖(f - id : ℂ → ℂ) y - (f - id : ℂ → ℂ) x‖ ≤ (4 * C / ‖z‖ ^ 2) * ‖y - x‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le hgdiff hgbound hconv hxs hys
  -- Assemble.
  have hkey : ‖f x - f y‖
      ≤ ‖x - y‖ + ‖(f - id : ℂ → ℂ) y - (f - id : ℂ → ℂ) x‖ := by
    have hsplit : f x - f y
        = (x - y) + ((f - id : ℂ → ℂ) x - (f - id : ℂ → ℂ) y) := by
      simp only [Pi.sub_apply, id_eq]; ring
    rw [hsplit]
    calc ‖(x - y) + ((f - id : ℂ → ℂ) x - (f - id : ℂ → ℂ) y)‖
        ≤ ‖x - y‖ + ‖(f - id : ℂ → ℂ) x - (f - id : ℂ → ℂ) y‖ := norm_add_le _ _
      _ = ‖x - y‖ + ‖(f - id : ℂ → ℂ) y - (f - id : ℂ → ℂ) x‖ :=
        by rw [norm_sub_rev ((f - id : ℂ → ℂ) x) ((f - id : ℂ → ℂ) y)]
  calc ‖f x - f y‖ ≤ ‖x - y‖ + ‖(f - id : ℂ → ℂ) y - (f - id : ℂ → ℂ) x‖ := hkey
    _ ≤ ‖x - y‖ + (4 * C / ‖z‖ ^ 2) * ‖y - x‖ := add_le_add le_rfl hmvt
    _ = (1 + 4 * C / ‖z‖ ^ 2) * ‖x - y‖ := by rw [norm_sub_rev y x]; ring

end Work.Pert.Ksub2
