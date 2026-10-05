import Mathlib

namespace Work.RPB1a

theorem interval_step_bound (u : ℝ → ℂ) (hu : Differentiable ℝ u) (hcu : Continuous (deriv u))
    {m t h : ℝ} (hmt : m ≤ ‖deriv u t‖)
    (hclose : ∀ y ∈ Set.uIcc t (t + h), ‖deriv u y - deriv u t‖ ≤ m / 2) :
    (m / 2) * |h| ≤ ‖u (t + h) - u t‖ := by
  -- Fundamental theorem of calculus: `u (t+h) - u t` is the integral of `deriv u`.
  have hFTC : ∫ y in t..t+h, deriv u y = u (t + h) - u t := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx; exact (hu x).hasDerivAt
    · exact hcu.intervalIntegrable t (t + h)
  have hIntu : IntervalIntegrable (deriv u) MeasureTheory.volume t (t + h) :=
    hcu.intervalIntegrable t (t + h)
  -- Subtract the linearisation `h • deriv u t` from the chord; what remains is the
  -- integral of the deviation of `deriv u` from `deriv u t` over the interval.
  have hdecomp : u (t + h) - u t - h • deriv u t
      = ∫ y in t..t+h, (deriv u y - deriv u t) := by
    rw [← hFTC]
    rw [intervalIntegral.integral_sub hIntu intervalIntegrable_const]
    rw [intervalIntegral.integral_const]
    rw [add_sub_cancel_left]
  -- Hence the deviation is bounded in norm by `(m / 2) * |h|`.
  have hb : ‖u (t + h) - u t - h • deriv u t‖ ≤ (m / 2) * |h| := by
    rw [hdecomp]
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun y => deriv u y - deriv u t) (a := t) (b := t + h) (C := m / 2)
      (fun x hx => hclose x (Set.uIoc_subset_uIcc hx))
    simpa [add_sub_cancel_left] using this
  -- The linearisation itself has norm at least `m * |h|`.
  have hA : m * |h| ≤ ‖h • deriv u t‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc m * |h| ≤ ‖deriv u t‖ * |h| := mul_le_mul_of_nonneg_right hmt (abs_nonneg h)
      _ = |h| * ‖deriv u t‖ := by ring
  -- Reverse triangle inequality produces the lower bound on the chord.
  have hrev : ‖h • deriv u t‖ - ‖u (t + h) - u t‖ ≤ (m / 2) * |h| := by
    have h1 := norm_sub_norm_le (h • deriv u t) (u (t + h) - u t)
    rw [norm_sub_rev (h • deriv u t) (u (t + h) - u t)] at h1
    linarith
  nlinarith [hA, hrev]

end Work.RPB1a
