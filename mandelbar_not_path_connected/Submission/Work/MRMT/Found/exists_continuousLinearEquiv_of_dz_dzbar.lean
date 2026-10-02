import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

/-- The real-linear map `w ↦ a * w + b * star w` is invertible as soon as `‖b‖ < ‖a‖`,
i.e. its "Jacobian determinant" `‖a‖ ^ 2 - ‖b‖ ^ 2` is nonzero. -/
theorem exists_continuousLinearEquiv_of_dz_dzbar {a b : ℂ} (h : ‖b‖ < ‖a‖) (L : ℂ →L[ℝ] ℂ)
    (hL : ∀ w : ℂ, L w = a * w + b * star w) : ∃ e : ℂ ≃L[ℝ] ℂ, (e : ℂ →L[ℝ] ℂ) = L := by
  -- `L` is injective: from `a * w + b * star w = 0` we get `‖a‖ * ‖w‖ = ‖b‖ * ‖w‖`.
  have hsub : ∀ w : ℂ, L w = 0 → w = 0 := by
    intro w hw
    have h0 : a * w + b * star w = 0 := by rw [← hL w, hw]
    have h1 : a * w = -(b * star w) := eq_neg_of_add_eq_zero_left h0
    have h2 : ‖a‖ * ‖w‖ = ‖b‖ * ‖w‖ := by
      rw [← norm_mul, h1, norm_neg, norm_mul, norm_star]
    have hlt : (0 : ℝ) < ‖a‖ - ‖b‖ := sub_pos.mpr h
    have h3 : ‖w‖ = 0 := by nlinarith [norm_nonneg w, hlt, h2]
    exact norm_eq_zero.mp h3
  have hinj : Function.Injective L := by
    intro x y hxy
    have hz : L (x - y) = 0 := by simp [map_sub, hxy]
    have hz' : x - y = 0 := hsub (x - y) hz
    simpa using sub_eq_zero.mp hz'
  -- On the finite-dimensional space `ℂ / ℝ`, injective implies surjective.
  have hker : (L : ℂ →ₗ[ℝ] ℂ).ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have hsurj : (L : ℂ →ₗ[ℝ] ℂ).range = ⊤ :=
    LinearMap.range_eq_top.mpr (LinearMap.surjective_of_injective hinj)
  exact ⟨ContinuousLinearEquiv.ofBijective L hker hsurj,
    ContinuousLinearEquiv.coe_ofBijective L hker hsurj⟩

end Work.MRMT.Found
