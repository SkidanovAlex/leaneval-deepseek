import Mathlib
import Submission.Work.Smooth.Jordan.JordanIndex

namespace Work.Smooth.Jordan

open Set MeasureTheory
open scoped Topology

/-!
# The index vanishes at infinity

For a `C¹` closed plane curve `c` the winding integral around a point `x` is
`(2πi)⁻¹ ∮ dz/(z - x)`; its absolute value is bounded by `(2π)⁻¹ · 2π · sup ‖γ'‖ / (‖x‖ - sup ‖γ‖)`,
which tends to `0` as `‖x‖ → ∞`.  Since the index of a point off the trace is an integer
(`Work.Smooth.Jordan.wind_mem_int`) and has modulus `< 1` for `‖x‖` large, it must be zero there.

* `ind_vanishes_at_infinity` — the index of a smooth closed curve vanishes outside a large disc.
-/

/-- **The index of a smooth closed plane curve vanishes outside a large disc.**  The trace of the
curve is compact, so `x` is off the trace once `‖x‖` is large; on that region the winding integral
is bounded by `(2π)⁻¹ · (2π) · C/(‖x‖ - M) < 1`, and being an integer it is zero. -/
theorem ind_vanishes_at_infinity (c : SmoothPlaneCurve) : ∃ R : ℝ, ∀ x : ℂ, R < ‖x‖ → ind c x = 0 := by
  -- Bounds for the curve and for its derivative on one period `[0, 2π]`.
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * Real.pi)).exists_bound_of_continuousOn
    c.cont.continuousOn
  obtain ⟨M₁, hM₁⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * Real.pi)).exists_bound_of_continuousOn
    c.continuous_deriv.continuousOn
  refine ⟨max M 0 + max M₁ 0 + 1, fun x hx => ?_⟩
  -- The point `x` is far outside the (bounded) trace of the curve.
  have hxnt : x ∉ c.trace := by
    intro hxmem
    rw [PlaneCurve.trace_eq_image_Icc] at hxmem
    obtain ⟨t, ht, rfl⟩ := hxmem
    have h1 : ‖c.γ t‖ ≤ max M 0 := le_trans (hM t ht) (le_max_left _ _)
    have h2 : (0 : ℝ) ≤ max M₁ 0 := le_max_right _ _
    linarith
  -- Pointwise bound for the winding integrand.
  have hint : ∀ t ∈ Set.uIoc (0 : ℝ) (2 * Real.pi),
      ‖windingIntegrand c x t‖ ≤ max M₁ 0 / (max M₁ 0 + 1) := by
    intro t ht
    rw [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)] at ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := ⟨le_of_lt ht.1, ht.2⟩
    have hd : ‖deriv c.γ t‖ ≤ max M₁ 0 := le_trans (hM₁ t htIcc) (le_max_left _ _)
    have hden : max M₁ 0 + 1 ≤ ‖c.γ t - x‖ := by
      have h1 : ‖x‖ - ‖c.γ t‖ ≤ ‖c.γ t - x‖ := by
        rw [norm_sub_rev]
        exact le_trans (le_abs_self _) (abs_norm_sub_norm_le x (c.γ t))
      have h2 : ‖c.γ t‖ ≤ max M 0 := le_trans (hM t htIcc) (le_max_left _ _)
      linarith
    rw [windingIntegrand_apply, norm_div]
    exact div_le_div₀ (le_max_right M₁ 0) hd (by positivity) hden
  -- Bound on the primitive at the full period.
  have hP : ‖windingPrimitive c x (2 * Real.pi)‖
      ≤ (max M₁ 0 / (max M₁ 0 + 1)) * (2 * Real.pi) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 2 * Real.pi)
      (C := max M₁ 0 / (max M₁ 0 + 1)) (f := windingIntegrand c x) hint
    have h' : ‖windingPrimitive c x (2 * Real.pi)‖
        ≤ (max M₁ 0 / (max M₁ 0 + 1)) * |2 * Real.pi - 0| := h
    rwa [sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h'
  -- Therefore the winding integral has modulus `< 1`.
  have hwind : ‖wind c x‖ ≤ max M₁ 0 / (max M₁ 0 + 1) := by
    have hnorm : ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ = (2 * Real.pi)⁻¹ := by
      rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, mul_one]
      simp
      try positivity
    rw [wind_def]
    calc ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ * windingPrimitive c x (2 * Real.pi)‖
        = ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ * ‖windingPrimitive c x (2 * Real.pi)‖ :=
          norm_mul _ _
      _ ≤ (2 * Real.pi)⁻¹ * ((max M₁ 0 / (max M₁ 0 + 1)) * (2 * Real.pi)) := by
          rw [hnorm]
          exact mul_le_mul le_rfl hP (norm_nonneg _) (by positivity)
      _ = max M₁ 0 / (max M₁ 0 + 1) := by
          rw [mul_comm (max M₁ 0 / (max M₁ 0 + 1)) (2 * Real.pi), ← mul_assoc,
            inv_mul_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0), one_mul]
  have hlt : ‖wind c x‖ < 1 := by
    have h1 : max M₁ 0 / (max M₁ 0 + 1) < 1 := by
      rw [div_lt_one (by positivity : (0 : ℝ) < max M₁ 0 + 1)]
      linarith [le_max_right M₁ (0 : ℝ)]
    linarith
  -- The winding integral is an integer of modulus `< 1`, hence zero.
  obtain ⟨k, hk⟩ := wind_mem_int c hxnt
  have hk0 : k = 0 := by
    have hA : |(k : ℝ)| < 1 := by
      rw [← Complex.norm_intCast, ← hk]
      exact hlt
    have hB : |k| < 1 := by
      have h3 : ((|k| : ℤ) : ℝ) < 1 := by
        rw [Int.cast_abs]
        exact hA
      exact_mod_cast h3
    exact Int.abs_lt_one_iff.mp hB
  have hres : (ind c x : ℂ) = 0 := by
    rw [ind_spec c ⟨k, hk⟩, hk, hk0]
    norm_num
  exact Int.cast_eq_zero.mp hres

end Work.Smooth.Jordan
