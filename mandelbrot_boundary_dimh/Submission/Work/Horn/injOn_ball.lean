import Mathlib
import Submission.Work.Horn.flower_defs

/-!
# Injectivity of a germ whose derivative is close to `1`

`Work.Horn.Flower.Bounds` records, among other things, that `‖deriv f z - 1‖ ≤ 1/2` on the disc
`Metric.ball 0 ρ`.  On a convex set such a bound on `deriv f - 1` forces `f` to be injective: the
map `g = f - id` has `‖deriv g‖ ≤ 1/2`, so the mean value inequality gives
`‖g y - g x‖ ≤ ‖y - x‖/2`, whence
`‖x - y‖ ≤ ‖f x - f y‖ + ‖g x - g y‖ ≤ ‖f x - f y‖ + ‖x - y‖/2`,
i.e. `‖f x - f y‖ ≥ ‖x - y‖/2 > 0` for `x ≠ y`.

This is the `injOn` half of the "the germ is univalent on the disc" statement used to build the
flower of a parabolic germ.
-/

namespace Work.Horn

open Set Metric

noncomputable section

/-- A differentiable-compatible bound `‖deriv f z - 1‖ ≤ 1/2` on a ball makes `f` injective there.
(The hypothesis also forces `f` to be differentiable at every point of the ball, since `deriv`
vanishes at a point where `f` is not differentiable.) -/
theorem injOn_ball_of_norm_deriv_sub_one_le {f : ℂ → ℂ} {ρ : ℝ}
    (hderiv : ∀ z ∈ Metric.ball (0 : ℂ) ρ, ‖deriv f z - 1‖ ≤ 1 / 2) :
    Set.InjOn f (Metric.ball (0 : ℂ) ρ) := by
  intro x hx y hy hxy
  -- the hypothesis rules out non-differentiability, where `deriv` is `0`
  have hdiff : ∀ z ∈ Metric.ball (0 : ℂ) ρ, DifferentiableAt ℂ f z := by
    intro z hz
    by_contra h
    have hzero : deriv f z = 0 := deriv_zero_of_not_differentiableAt h
    have h1 := hderiv z hz
    rw [hzero] at h1
    norm_num at h1
  -- `g = f - id` has derivative bounded by `1/2` on the convex ball
  set g : ℂ → ℂ := fun z => f z - z with hg
  have hgd : ∀ z ∈ Metric.ball (0 : ℂ) ρ, DifferentiableAt ℂ g z := by
    intro z hz
    have h1 : DifferentiableAt ℂ f z := hdiff z hz
    have h2 : DifferentiableAt ℂ (fun w : ℂ => w) z := differentiableAt_id
    rw [hg]
    exact h1.sub h2
  have hgderiv : ∀ z ∈ Metric.ball (0 : ℂ) ρ, deriv g z = deriv f z - 1 := by
    intro z hz
    have h1 : HasDerivAt f (deriv f z) z := (hdiff z hz).hasDerivAt
    have h2 : HasDerivAt (fun w : ℂ => w) 1 z := hasDerivAt_id z
    have h3 : HasDerivAt g (deriv f z - 1) z := by
      rw [hg]
      exact h1.sub h2
    exact h3.deriv
  have hgbound : ∀ z ∈ Metric.ball (0 : ℂ) ρ, ‖deriv g z‖ ≤ 1 / 2 := by
    intro z hz
    rw [hgderiv z hz]
    exact hderiv z hz
  have hmvt :=
    Convex.norm_image_sub_le_of_norm_deriv_le hgd hgbound (convex_ball (0 : ℂ) ρ) hx hy
  -- `x - y = (f x - f y) - (g x - g y)`, so `‖x - y‖ ≤ ‖f x - f y‖ + ‖g x - g y‖`
  have key : ‖x - y‖ ≤ (1 / 2) * ‖x - y‖ := by
    have h1 : ‖x - y‖ ≤ ‖f x - f y‖ + ‖g x - g y‖ := by
      have hxy' : x - y = (f x - f y) - (g x - g y) := by
        rw [hg]; ring
      calc ‖x - y‖ = ‖(f x - f y) - (g x - g y)‖ := by rw [hxy']
        _ ≤ ‖f x - f y‖ + ‖g x - g y‖ := norm_sub_le _ _
    rw [hxy, sub_self, norm_zero, zero_add] at h1
    have h2 : ‖g x - g y‖ ≤ (1 / 2) * ‖x - y‖ := by
      rw [norm_sub_rev (g x) (g y), norm_sub_rev x y]
      exact hmvt
    linarith
  have hzero : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

theorem injOn_ball {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ} {ρ : ℝ}
    (hb : Work.Horn.Flower.Bounds f D q a ρ) : Set.InjOn f (Metric.ball (0 : ℂ) ρ) :=
  injOn_ball_of_norm_deriv_sub_one_le fun z hz => hb.hderiv z hz

end

end Work.Horn
