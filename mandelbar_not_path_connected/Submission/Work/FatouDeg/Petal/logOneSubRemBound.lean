import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouDeg.Petal

/-- For `‖w‖ ≤ 1/2`, `log (1 - w)` agrees with `-w - w^2/2` up to `O(‖w‖^3)`.

This is a corollary of Mathlib's `Complex.norm_log_sub_logTaylor_le`, which bounds
`log (1 + z)` minus its Taylor polynomial at `z = 0` by `‖z‖^(n+1) * (1 - ‖z‖)⁻¹ / (n+1)`. -/
theorem logOneSubRemBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, ‖w‖ ≤ 1 / 2 →
    ‖Complex.log (1 - w) + w + w ^ 2 / 2‖ ≤ C * ‖w‖ ^ 3 := by
  refine ⟨2 / 3, by norm_num, ?_⟩
  intro w hw
  have hz : ‖(-w : ℂ)‖ < 1 := by
    rw [norm_neg]
    linarith
  have h := Complex.norm_log_sub_logTaylor_le 2 hz
  norm_num at h
  have hlt : (1 - ‖w‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith [norm_nonneg w] : (0 : ℝ) < 1 - ‖w‖) (by norm_num)]
    linarith
  calc
    ‖Complex.log (1 - w) + w + w ^ 2 / 2‖
        = ‖Complex.log (1 + (-w)) - Complex.logTaylor 3 (-w)‖ := by
            have htay : Complex.logTaylor 3 (-w) = -w - w ^ 2 / 2 := by
              unfold Complex.logTaylor
              simp only [Finset.sum_range_succ, Finset.sum_range_zero]
              norm_num
              ring
            rw [htay]
            ring_nf
    _ ≤ ‖(-w : ℂ)‖ ^ 3 * (1 - ‖(-w : ℂ)‖)⁻¹ / 3 := by
            simpa using h
    _ = ‖w‖ ^ 3 * (1 - ‖w‖)⁻¹ / 3 := by rw [norm_neg]
    _ ≤ ‖w‖ ^ 3 * 2 / 3 := by
            have hnn : 0 ≤ ‖w‖ ^ 3 := by positivity
            nlinarith
    _ = 2 / 3 * ‖w‖ ^ 3 := by ring

end Work.FatouDeg.Petal
