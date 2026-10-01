import Mathlib

namespace Work.ZeroFreeTables.Table4

/-- For any positive constant `c`, the quartic polynomial in `Real.log x` is eventually
dominated by `c * x`.  This is the classical statement that `log` grows slower than any
positive power of `x`. -/
theorem loglogPow4_le_mul {c : ℝ} (hc : 0 < c) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → (Real.log x + 2) ^ 4 ≤ c * x := by
  -- `Real.log x + 2 → ∞` as `x → ∞`.
  have hφ : Filter.Tendsto (fun x : ℝ => Real.log x + 2) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 2 Real.tendsto_log_atTop
  -- `u ^ 4 = o(exp u)` at `+∞`, hence eventually `u ^ 4 ≤ (c / exp 2) * exp u`.
  have hbound : ∀ᶠ u in Filter.atTop, u ^ 4 ≤ (c / Real.exp 2) * Real.exp u := by
    have h := (Real.isLittleO_pow_exp_atTop (n := 4)).def (div_pos hc (Real.exp_pos 2))
    filter_upwards [h] with u hu
    rwa [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.exp_pos u).le] at hu
  -- Pull this back along `x ↦ log x + 2`.
  have hbound' : ∀ᶠ x in Filter.atTop,
      (Real.log x + 2) ^ 4 ≤ (c / Real.exp 2) * Real.exp (Real.log x + 2) :=
    hφ.eventually hbound
  have hpos : ∀ᶠ x : ℝ in Filter.atTop, 0 < x := Filter.eventually_gt_atTop 0
  have hmain : ∀ᶠ x in Filter.atTop, (Real.log x + 2) ^ 4 ≤ c * x := by
    filter_upwards [hbound', hpos] with x hx hxpos
    -- for `x > 0`, `exp (log x + 2) = x * exp 2`, so the bound becomes `c * x`.
    have he : Real.exp (Real.log x + 2) = x * Real.exp 2 := by
      rw [Real.exp_add, Real.exp_log hxpos]
    rw [he] at hx
    calc (Real.log x + 2) ^ 4 ≤ (c / Real.exp 2) * (x * Real.exp 2) := hx
      _ = c * x := by
        rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_right₀ _ (Real.exp_ne_zero 2)]
  rw [Filter.eventually_atTop] at hmain
  obtain ⟨X, hX⟩ := hmain
  exact ⟨X, fun x hx => hX x hx⟩

end Work.ZeroFreeTables.Table4
