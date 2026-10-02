import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FBif

/-- **The quadratic coefficient of a simple parabolic point is not orthogonal to the multiplier.**

Let `lam, A₂, s : ℂ` with `‖lam‖ = 1` and `s ^ 2 = lam` (so `s` is a unit complex number and
`lam = s ^ 2`).  If `lam * star A₂ + A₂ * (star lam) ^ 2 ≠ 0` -- the second derivative at the
parabolic point of the holomorphic second return map `z ↦ z + K z² + …`, where
`K = lam * star A₂ + A₂ * (star lam) ^ 2` -- then `(A₂ / (lam * s)).re ≠ 0`.

Indeed one has the exact identity
`lam * star A₂ + A₂ * (star lam) ^ 2 = 2 * star s * ((A₂ / (lam * s)).re : ℂ)`, so the hypothesis
says precisely `Re (A₂ / (lam * s)) ≠ 0`; note `‖s‖ = 1` follows from `‖lam‖ = 1` and `s ^ 2 = lam`. -/
theorem quadratic_coeff_re_ne_zero {lam A₂ s : ℂ} (hlam : ‖lam‖ = 1) (hs : s ^ 2 = lam)
    (hK : lam * star A₂ + A₂ * (star lam) ^ 2 ≠ 0) : (A₂ / (lam * s)).re ≠ 0 := by
  -- `‖lam‖ = 1` gives `lam * star lam = 1`.
  have hlam_normSq : Complex.normSq lam = 1 := by
    rw [Complex.normSq_eq_norm_sq, hlam]; norm_num
  have hlam_mul : lam * star lam = 1 := by
    rw [Complex.star_def, Complex.mul_conj, hlam_normSq]; norm_num
  have hlam_ne : lam ≠ 0 := by
    intro h; rw [h, zero_mul] at hlam_mul; exact zero_ne_one hlam_mul
  -- `s ^ 2 = lam` together with `‖lam‖ = 1` gives `Complex.normSq s = 1`, hence `s * star s = 1`.
  have hnorm_sq_s : (Complex.normSq s)^2 = 1 := by
    have h1 : Complex.normSq (s^2) = Complex.normSq lam := by rw [hs]
    have h2 : Complex.normSq (s^2) = (Complex.normSq s)^2 := by
      rw [pow_two, map_mul, pow_two]
    rw [← h2, h1, hlam_normSq]
  have hnormSq_s : Complex.normSq s = 1 := by
    have hnn : 0 ≤ Complex.normSq s := Complex.normSq_nonneg s
    nlinarith
  have hs_mul : s * star s = 1 := by
    rw [Complex.star_def, Complex.mul_conj, hnormSq_s]; norm_num
  have hs_ne : s ≠ 0 := by
    intro h; rw [h] at hs_mul; norm_num at hs_mul
  -- Write `A₂ = lam * s * u` with `u = A₂ / (lam * s)`; the goal is `u.re ≠ 0`.
  set u : ℂ := A₂ / (lam * s) with hu
  have hA : lam * s * u = A₂ := by
    rw [hu]; exact mul_div_cancel₀ A₂ (mul_ne_zero hlam_ne hs_ne)
  have hs_inv : star s = s⁻¹ := eq_inv_of_mul_eq_one_right hs_mul
  have hlam_inv : star lam = lam⁻¹ := eq_inv_of_mul_eq_one_right hlam_mul
  -- `u + star u = 2 * Re u`.
  have h_star_u : star u = 2 * (u.re : ℂ) - u := by
    have h' : u + star u = 2 * (u.re : ℂ) := by
      rw [Complex.star_def, Complex.add_conj]; norm_num
    rw [eq_sub_iff_add_eq, add_comm]; exact h'
  -- The exact identity `K = 2 * star s * Re u`.
  have key : lam * star A₂ + A₂ * (star lam)^2 = 2 * star s * (u.re : ℂ) := by
    rw [← hA]
    simp only [star_mul]
    rw [hs_inv, hlam_inv, ← hs, h_star_u]
    field_simp
    ring
  rw [key] at hK
  intro h
  exact hK (by simp [h])

end Work.FBif
