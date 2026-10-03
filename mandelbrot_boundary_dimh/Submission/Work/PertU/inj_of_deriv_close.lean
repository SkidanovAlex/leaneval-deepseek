import Mathlib

/-!
# Injectivity from derivatives close to `1` (mean value inequality)

If `f : ℂ → ℂ` is holomorphic on a convex set `C` with `‖deriv f z - 1‖ ≤ 1/2` for every
`z ∈ C`, then `f` is injective on `C`.

The proof applies the mean value inequality to `g z = f z - z`: since `deriv g z = deriv f z - 1`
is bounded by `1/2` on `C`, the map `g` is `1/2`-Lipschitz on `C`. If `f x = f y` then
`g x - g y = -(x - y)`, so `‖x - y‖ ≤ ‖x - y‖ / 2`, hence `x = y`.
-/

namespace Work.PertU

theorem inj_of_deriv_close {f : ℂ → ℂ} {C : Set ℂ} (hC : Convex ℝ C)
    (hd : ∀ z ∈ C, DifferentiableAt ℂ f z) (hb : ∀ z ∈ C, ‖deriv f z - 1‖ ≤ 1 / 2) :
    Set.InjOn f C := by
  intro x hx y hy hxy
  -- The mean value inequality applies to `g z = f z - z`, whose derivative is `deriv f z - 1`.
  have hgdiff : ∀ z ∈ C, DifferentiableAt ℂ (fun w : ℂ => f w - w) z :=
    fun z hz => (hd z hz).sub differentiableAt_id
  have hbound : ∀ z ∈ C, ‖deriv (fun w : ℂ => f w - w) z‖ ≤ 1 / 2 := by
    intro z hz
    have h1 : deriv (fun w : ℂ => f w - w) z = deriv f z - 1 := by
      rw [show (fun w : ℂ => f w - w) = f - id from rfl,
        deriv_sub (hd z hz) differentiableAt_id, deriv_id]
    rw [h1]
    exact hb z hz
  -- `‖g x - g y‖ ≤ 1/2 * ‖x - y‖`
  have h := hC.norm_image_sub_le_of_norm_deriv_le hgdiff hbound hy hx
  rw [hxy] at h
  rw [show f y - x - (f y - y) = y - x by ring] at h
  rw [norm_sub_rev y x] at h
  -- `f x = f y` yields `‖x - y‖ ≤ 1/2 * ‖x - y‖`, so `x = y`.
  have hzero : ‖x - y‖ = 0 := by
    have := norm_nonneg (x - y)
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

end Work.PertU
