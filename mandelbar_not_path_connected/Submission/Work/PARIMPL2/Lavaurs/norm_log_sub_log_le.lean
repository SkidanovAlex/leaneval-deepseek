import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Lavaurs

/-- **`Complex.log` is Lipschitz on the right half-plane** `{Re z ≥ c}` (`c > 0`), with constant
`1/c`: the derivative is `1/z` and `‖1/z‖ ≤ 1/c` there, `{Re z ≥ c}` is convex, and it avoids the
branch cut. -/
theorem norm_log_sub_log_le {c : ℝ} (hc : 0 < c) {z w : ℂ} (hz : c ≤ z.re) (hw : c ≤ w.re) :
    ‖Complex.log z - Complex.log w‖ ≤ ‖z - w‖ / c := by
  -- The right half-plane `{u | c ≤ u.re}` is convex (preimage of `Ici c` under `re`).
  have hs : Convex ℝ {u : ℂ | c ≤ u.re} := by
    have := (convex_Ici c).linear_preimage (Complex.reCLM : ℂ →ₗ[ℝ] ℝ)
    simpa [Set.preimage, Complex.reCLM_apply, Set.mem_Ici] using this
  -- `Complex.log` is differentiable on this set, with derivative `1/u = u⁻¹`.
  have hdiff : ∀ x ∈ {u : ℂ | c ≤ u.re},
      HasFDerivWithinAt Complex.log (ContinuousLinearMap.toSpanSingleton ℂ x⁻¹)
        {u : ℂ | c ≤ u.re} x := by
    intro x hx
    have hxpos : 0 < x.re := lt_of_lt_of_le hc hx
    have hslit : x ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; exact Or.inl hxpos
    exact (Complex.hasDerivAt_log hslit).hasFDerivAt.hasFDerivWithinAt
  -- The derivative is bounded by `1/c = c⁻¹` on the half-plane.
  have hbound : ∀ x ∈ {u : ℂ | c ≤ u.re},
      ‖ContinuousLinearMap.toSpanSingleton ℂ x⁻¹‖ ≤ c⁻¹ := by
    intro x hx
    rw [ContinuousLinearMap.norm_toSpanSingleton, norm_inv]
    have hc_le : c ≤ ‖x‖ := le_trans hx (Complex.re_le_norm x)
    exact (inv_le_inv₀ (lt_of_lt_of_le hc hc_le) hc).mpr hc_le
  have hmain := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hdiff hbound hs hw hz
  rwa [div_eq_inv_mul]

end Work.PARIMPL2.Lavaurs
