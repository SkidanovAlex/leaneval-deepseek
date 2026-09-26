import Mathlib

open MeasureTheory

set_option linter.unusedVariables false

namespace Work.Asymptotics.HalfFunnel

/-- The recursion step of `spike_model_integral`: knowing a uniform bound for the integral with
`(u+iε)⁻¹ u^m`, produce one for `(u+iε)⁻¹ u^{m+1}`.  Pointwise
`u^{m+1}/(u+iε) = u^m - iε · u^m/(u+iε)`, so the integral equals
`∫ e^{-a(y+u)} u^m du - iε ∫ e^{-a(y+u)}(u+iε)⁻¹ u^m du`; the first factor is bounded by
`2ρ^{m+1}` since `|e^{-a(y+u)}| ≤ 1` and `|u| ≤ ρ` on `[-ρ,ρ]`, and `|ε| ≤ 1/4`. -/
theorem spike_model_integral_succ (m : ℕ) {y ρ : ℝ} (hy : 0 < y) (hρ : 0 < ρ) (hρy : ρ < y)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ (a ε : ℝ), 0 < a → ε ≠ 0 → |ε| ≤ 1 / 4 →
      ‖∫ u in (-ρ)..ρ, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) *
          ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((u : ℂ) ^ m)‖ ≤ C) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (a ε : ℝ), 0 < a → ε ≠ 0 → |ε| ≤ 1 / 4 →
      ‖∫ u in (-ρ)..ρ, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) *
          ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((u : ℂ) ^ (m + 1))‖ ≤ C' := by
  refine ⟨2 * ρ ^ (m + 1) + (1 / 4) * C, by positivity, ?_⟩
  intro a ε ha hε hεb
  -- The pole is off the real axis, so `u + iε` never vanishes for real `u`.
  have hne : ∀ u : ℝ, ((u : ℂ) + (ε : ℂ) * Complex.I) ≠ 0 := by
    intro u h
    have := congrArg Complex.im h
    simp at this
    exact hε this
  -- Pointwise algebra: `u^{m+1}/(u+iε) = u^m - iε·u^m/(u+iε)`.
  have hpt : ∀ u : ℝ,
      Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((u : ℂ) ^ (m + 1))
      = Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((u : ℂ) ^ m)
        - (ε : ℂ) * Complex.I * (Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((u : ℂ) ^ m)) := by
    intro u
    have hu := hne u
    have hmain : ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((u : ℂ) ^ (m + 1))
        = (u : ℂ) ^ m - (ε : ℂ) * Complex.I * (((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((u : ℂ) ^ m)) := by
      have key : ((u : ℂ) + (ε : ℂ) * Complex.I) * ((u : ℂ) ^ m) = (u : ℂ) ^ (m + 1) + (ε : ℂ) * Complex.I * ((u : ℂ) ^ m) := by
        rw [pow_succ]; ring
      have h2 : ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((u : ℂ) ^ (m + 1)) + (ε : ℂ) * Complex.I * (((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((u : ℂ) ^ m))
          = ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * (((u : ℂ) + (ε : ℂ) * Complex.I) * ((u : ℂ) ^ m)) := by
        rw [key]; ring
      rw [eq_sub_iff_add_eq, h2, ← mul_assoc, inv_mul_cancel₀ hu, one_mul]
    rw [mul_assoc, hmain]; ring
  -- Split the integral accordingly.
  have hcongr : (∫ u in (-ρ)..ρ, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((u : ℂ) ^ (m + 1)))
      = ∫ u in (-ρ)..ρ, (Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((u : ℂ) ^ m)
          - (ε : ℂ) * Complex.I * (Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((u : ℂ) ^ m))) := by
    apply intervalIntegral.integral_congr
    intro u _
    exact hpt u
  have hcont1 : Continuous fun u : ℝ => Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((u : ℂ) ^ m) := by fun_prop
  have hcont2 : Continuous fun u : ℝ => Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((u : ℂ) ^ m) := by
    have hP : Continuous fun u : ℝ => ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ := Continuous.inv₀ (by fun_prop) hne
    exact ((by fun_prop : Continuous fun u : ℝ => Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ)))).mul hP).mul (by fun_prop)
  have hf : IntervalIntegrable (fun u : ℝ => Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((u : ℂ) ^ m)) volume (-ρ) ρ :=
    hcont1.intervalIntegrable _ _
  have hg0 : IntervalIntegrable (fun u : ℝ => Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((u : ℂ) ^ m)) volume (-ρ) ρ :=
    hcont2.intervalIntegrable _ _
  have hg : IntervalIntegrable (fun u : ℝ => (ε : ℂ) * Complex.I * (Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((u : ℂ) ^ m))) volume (-ρ) ρ :=
    hg0.const_mul _
  -- The polynomial part: `‖∫ e^{-a(y+u)} u^m du‖ ≤ 2ρ^{m+1}`.
  have hbound1 : ‖∫ u in (-ρ)..ρ, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((u : ℂ) ^ m)‖ ≤ 2 * ρ ^ (m + 1) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -ρ) (b := ρ) (C := ρ ^ m)
      (f := fun u : ℝ => Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((u : ℂ) ^ m)) ?_
    · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ ρ - -ρ)] at h
      calc ‖∫ u in (-ρ)..ρ, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((u : ℂ) ^ m)‖
          ≤ ρ ^ m * (ρ - -ρ) := h
        _ = 2 * ρ ^ (m + 1) := by rw [pow_succ]; ring
    · intro u hu
      rw [Set.uIoc_of_le (by linarith : -ρ ≤ ρ)] at hu
      have huI : -ρ ≤ u ∧ u ≤ ρ := ⟨le_of_lt hu.1, hu.2⟩
      have hnormE : ‖Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ)))‖ ≤ 1 := by
        rw [Complex.norm_exp]
        have hre : (-(a : ℂ) * ((y : ℂ) + (u : ℂ))).re = -(a * (y + u)) := by simp
        rw [hre]
        have hyu : 0 < y + u := by linarith [hy, huI.1, hρy]
        have : 0 < a * (y + u) := mul_pos ha hyu
        exact Real.exp_le_one_iff.mpr (by linarith)
      have hnormP : ‖(u : ℂ) ^ m‖ ≤ ρ ^ m := by
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg u) (abs_le.mpr huI) m
      calc ‖Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((u : ℂ) ^ m)‖
          = ‖Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ)))‖ * ‖(u : ℂ) ^ m‖ := norm_mul _ _
        _ ≤ 1 * ρ ^ m := mul_le_mul hnormE hnormP (norm_nonneg _) (by norm_num)
        _ = ρ ^ m := one_mul _
  -- The recurrence term: `‖iε · ∫ e^{-a(y+u)}(u+iε)⁻¹u^m du‖ ≤ (1/4)·C`.
  have hbound2 : ‖(ε : ℂ) * Complex.I * (∫ u in (-ρ)..ρ, Complex.exp (-(a : ℂ) * ((y : ℂ) + (u : ℂ))) * ((u : ℂ) + (ε : ℂ) * Complex.I)⁻¹ * ((u : ℂ) ^ m))‖ ≤ (1 / 4) * C := by
    have hI : ‖(ε : ℂ) * Complex.I‖ = |ε| := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [norm_mul, hI]
    exact mul_le_mul hεb (hbound a ε ha hε hεb) (norm_nonneg _) (by norm_num)
  rw [hcongr, intervalIntegral.integral_sub hf hg, intervalIntegral.integral_const_mul]
  exact (norm_sub_le _ _).trans (add_le_add hbound1 hbound2)

end Work.Asymptotics.HalfFunnel
