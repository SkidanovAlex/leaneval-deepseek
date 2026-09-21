import Mathlib

namespace Work.Analysis.Calculus

open MeasureTheory

/-- Change of variables `τ = sin θ ^ 2` in the singular integral
`∫_0^1 g τ / sqrt (τ (1 - τ)) dτ`: substituting `τ = sin θ ^ 2`, so that
`dτ = 2 sin θ cos θ dθ` and `sqrt (τ (1 - τ)) = sin θ cos θ`, turns the integral
into `∫_0^{π/2} 2 g (sin θ ^ 2) dθ`.

The statement holds for an arbitrary (not necessarily integrable) `g`: both sides
are `0` when the relevant function is not integrable, and the substitution
`intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg` (for nonnegative
derivative) is available without integrability hypotheses. -/
theorem integral_div_sqrt_eq_integral_sin_sq (g : ℝ → ℝ) :
    (∫ τ in (0 : ℝ)..1, g τ / Real.sqrt (τ * (1 - τ)))
      = ∫ θ in (0 : ℝ)..(Real.pi / 2), 2 * g (Real.sin θ ^ 2) := by
  -- Pointwise identity on the open interval, where `sin θ * cos θ ≠ 0`.
  have hpoint : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      g (Real.sin θ ^ 2) / Real.sqrt (Real.sin θ ^ 2 * (1 - Real.sin θ ^ 2)) *
          (2 * Real.sin θ * Real.cos θ) = 2 * g (Real.sin θ ^ 2) := by
    intro θ hθ
    have hsin : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ.1 (lt_trans hθ.2 (by linarith [Real.pi_pos]))
    have hcos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
    have hs1 : (1 : ℝ) - Real.sin θ ^ 2 = Real.cos θ ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq θ]
    have hs2 : Real.sin θ ^ 2 * (1 - Real.sin θ ^ 2) = (Real.sin θ * Real.cos θ) ^ 2 := by
      rw [hs1]; ring
    have hsqrt : Real.sqrt (Real.sin θ ^ 2 * (1 - Real.sin θ ^ 2)) = Real.sin θ * Real.cos θ := by
      rw [hs2, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
    rw [hsqrt]
    have hne : Real.sin θ * Real.cos θ ≠ 0 := by positivity
    field_simp
  -- `deriv (sin θ ^ 2) = 2 sin θ cos θ`, and this derivative is nonnegative on `(0, π/2)`.
  have hderiv : ∀ x ∈ Set.Ioo (min (0 : ℝ) (Real.pi / 2)) (max (0 : ℝ) (Real.pi / 2)),
      HasDerivAt (fun θ : ℝ => Real.sin θ ^ 2) (2 * Real.sin x * Real.cos x) x := by
    intro x _
    have h : HasDerivAt (Real.sin ^ 2) (2 * Real.sin x * Real.cos x) x := by
      simpa using (Real.hasDerivAt_sin x).pow 2
    exact h
  have hnonneg : ∀ x ∈ Set.Ioo (min (0 : ℝ) (Real.pi / 2)) (max (0 : ℝ) (Real.pi / 2)),
      0 ≤ 2 * Real.sin x * Real.cos x := by
    intro x hx
    rw [min_eq_left (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2),
      max_eq_right (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)] at hx
    have hsin : 0 ≤ Real.sin x :=
      le_of_lt (Real.sin_pos_of_pos_of_lt_pi hx.1 (lt_trans hx.2 (by linarith [Real.pi_pos])))
    have hcos : 0 ≤ Real.cos x :=
      le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2]⟩)
    positivity
  -- Change of variables: `∫_0^{π/2} (h ∘ sin²) · (sin²)' = ∫_0^1 h`.
  have hkey := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (a := (0 : ℝ)) (b := Real.pi / 2)
      (f := fun θ : ℝ => Real.sin θ ^ 2)
      (f' := fun θ : ℝ => 2 * Real.sin θ * Real.cos θ)
      (g := fun τ => g τ / Real.sqrt (τ * (1 - τ)))
      (by fun_prop) hderiv hnonneg
  have hkey' : (∫ x in (0 : ℝ)..(Real.pi / 2), g (Real.sin x ^ 2) /
        Real.sqrt (Real.sin x ^ 2 * (1 - Real.sin x ^ 2)) * (2 * Real.sin x * Real.cos x))
      = ∫ u in (0 : ℝ)..1, g u / Real.sqrt (u * (1 - u)) := by
    simpa [Function.comp_apply] using hkey
  -- The two integrands agree almost everywhere: they can differ only at `θ = π/2`.
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.uIoc (0 : ℝ) (Real.pi / 2) →
      g (Real.sin x ^ 2) / Real.sqrt (Real.sin x ^ 2 * (1 - Real.sin x ^ 2)) *
          (2 * Real.sin x * Real.cos x) = 2 * g (Real.sin x ^ 2) := by
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_singleton (Real.pi / 2))
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    rw [Classical.not_imp] at hx
    obtain ⟨hxmem, hxne⟩ := hx
    rw [Set.uIoc_of_le (le_of_lt (by positivity : (0 : ℝ) < Real.pi / 2)), Set.mem_Ioc] at hxmem
    by_contra hne
    exact hxne (hpoint x ⟨hxmem.1, lt_of_le_of_ne hxmem.2 hne⟩)
  rw [← hkey']
  exact intervalIntegral.integral_congr_ae hae

end Work.Analysis.Calculus
