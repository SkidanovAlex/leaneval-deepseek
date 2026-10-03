import Mathlib

-- `hdiff` in the main theorem below is not needed: the pointwise bound on `deriv` already forces
-- differentiability on `Q` (see the first step of the proof), but the statement is the one requested.
set_option linter.unusedVariables false

namespace Work.Pert.pert2v2

/-- Quantitative version of the mean value inequality used below: for `Φ : ℂ → ℂ` differentiable at
`v`, the operator norm of the Fréchet derivative of `Φ - id` at `v` equals the modulus of
`deriv Φ v - 1`.

Both sides are computed by transporting along the isometry `c ↦ ContinuousLinearMap.toSpanSingleton ℂ c`
(the defining identity `fderiv ℂ f = toSpanSingleton ℂ (deriv f)`, i.e.
`norm_deriv_eq_norm_fderiv`). -/
private lemma norm_fderiv_sub_one (Φ : ℂ → ℂ) {v : ℂ} (h : DifferentiableAt ℂ Φ v) :
    ‖fderiv ℂ Φ v - (1 : ℂ →L[ℂ] ℂ)‖ = ‖deriv Φ v - 1‖ := by
  have h1 : fderiv ℂ (Φ - id) v = fderiv ℂ Φ v - 1 := by
    rw [fderiv_sub h differentiableAt_id, fderiv_id]
    rfl
  have h2 : deriv (Φ - id) v = deriv Φ v - 1 := by
    rw [deriv_sub h differentiableAt_id]
    simp
  rw [← h1, ← h2, norm_deriv_eq_norm_fderiv]

/-- **The mean value inequality for a map whose derivative is close to `1`.**

If `Q` is convex, `Φ` is complex differentiable on `Q` and `‖deriv Φ v - 1‖ ≤ 1/2` for every
`v ∈ Q`, then `Φ` is `2`-antilipschitz on `Q`, i.e. `‖z - z'‖ ≤ 2‖Φ z - Φ z'‖` for all
`z, z' ∈ Q`.

Proof: the bound on `deriv` forces `deriv Φ v ≠ 0` at every `v ∈ Q`, hence (junk value of `deriv`
at points where `Φ` is not differentiable) `Φ` is actually differentiable at every point of `Q`;
then the convex mean value inequality applied to `Φ` with the comparison map `1` gives
`‖Φ z' - Φ z - (z' - z)‖ ≤ (1/2)‖z' - z‖`, and the triangle inequality yields
`‖z - z'‖ ≤ (1/2)‖z - z'‖ + ‖Φ z - Φ z'‖`. -/
theorem norm_sub_le_two_mul_of_deriv_sub_one {Φ : ℂ → ℂ} {Q : Set ℂ}
    (hconv : ∀ z ∈ Q, ∀ z' ∈ Q, ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      ((1 - t) • z + t • z') ∈ Q)
    (hdiff : DifferentiableOn ℂ Φ Q)
    (hder : ∀ v ∈ Q, ‖deriv Φ v - 1‖ ≤ 1 / 2)
    {z z' : ℂ} (hz : z ∈ Q) (hz' : z' ∈ Q) :
    ‖z - z'‖ ≤ 2 * ‖Φ z - Φ z'‖ := by
  -- `Q` is convex over `ℝ`
  have hconvex : Convex ℝ Q := by
    intro x hx y hy a b ha hb hab
    have hb1 : b ≤ 1 := by linarith
    have h := hconv x hx y hy b ⟨hb, hb1⟩
    rw [show a = 1 - b by linarith]
    exact h
  -- the derivative bound forces differentiability everywhere on `Q`
  have hdiffAt : ∀ v ∈ Q, DifferentiableAt ℂ Φ v := by
    intro v hv
    by_contra h
    have h0 : deriv Φ v = 0 := deriv_zero_of_not_differentiableAt h
    have hv' := hder v hv
    rw [h0] at hv'
    norm_num at hv'
  -- the bound on `fderiv Φ - 1`
  have hbound : ∀ v ∈ Q, ‖fderiv ℂ Φ v - (1 : ℂ →L[ℂ] ℂ)‖ ≤ 1 / 2 := by
    intro v hv
    rw [norm_fderiv_sub_one Φ (hdiffAt v hv)]
    exact hder v hv
  -- convex mean value inequality for `Φ` compared with the identity map
  have hMVT := hconvex.norm_image_sub_le_of_norm_fderiv_le' hdiffAt hbound hz hz'
  simp only [one_apply_eq_self] at hMVT
  have key : ‖z' - z - (Φ z' - Φ z)‖ ≤ 1 / 2 * ‖z' - z‖ := by
    rwa [norm_sub_rev (Φ z' - Φ z) (z' - z)] at hMVT
  -- triangle inequality and algebra
  have h1 : ‖z' - z‖ ≤ ‖z' - z - (Φ z' - Φ z)‖ + ‖Φ z' - Φ z‖ := by
    calc ‖z' - z‖ = ‖(z' - z - (Φ z' - Φ z)) + (Φ z' - Φ z)‖ := by
          congr 1
          ring
      _ ≤ _ := norm_add_le _ _
  have h2 : ‖z' - z‖ ≤ 1 / 2 * ‖z' - z‖ + ‖Φ z' - Φ z‖ := by linarith
  have h3 : (1 / 2 : ℝ) * ‖z' - z‖ ≤ ‖Φ z' - Φ z‖ := by linarith
  have h4 : ‖z' - z‖ ≤ 2 * ‖Φ z' - Φ z‖ := by linarith
  rw [norm_sub_rev z z', norm_sub_rev (Φ z) (Φ z')]
  exact h4

end Work.Pert.pert2v2
