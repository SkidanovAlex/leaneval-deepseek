import Mathlib

namespace Work.LinnikAreas.Density4

/-- Auxiliary: `T ↦ T ^ A * exp (-(π/2) * T)` tends to `0` at `+∞`. -/
private lemma tendsto_rpow_mul_exp_neg_half_pi (A : ℝ) :
    Filter.Tendsto (fun T : ℝ => T ^ A * Real.exp (-(Real.pi / 2) * T))
      Filter.atTop (nhds 0) := by
  simpa [neg_mul] using
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero A (Real.pi / 2) (by positivity)

/-- The uniform bound on the vertical edge integral tends to `0`. -/
private lemma tendsto_edge_bound (C : ℝ) {a b : ℝ} (A : ℝ) :
    Filter.Tendsto
      (fun T : ℝ => (C * Real.exp (-(Real.pi / 2) * T) * T ^ A) * |b - a|)
      Filter.atTop (nhds 0) := by
  have h1 := tendsto_rpow_mul_exp_neg_half_pi A
  have h2 : Filter.Tendsto
      (fun T : ℝ => (C * |b - a|) * (T ^ A * Real.exp (-(Real.pi / 2) * T)))
      Filter.atTop (nhds ((C * |b - a|) * 0)) :=
    tendsto_const_nhds.mul h1
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards with T
  ring

theorem rect_edge_tendsto_zero (F : ℂ → ℂ) (a b A C : ℝ) (hab : a ≤ b) (hC : 0 < C)
    (hF : ∀ x ∈ Set.Icc a b, ∀ T : ℝ, 1 ≤ T → ‖F ((x : ℂ) + (T : ℂ) * Complex.I)‖
      ≤ C * Real.exp (-(Real.pi / 2) * T) * T ^ A) :
    Filter.Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x : ℂ) + (T : ℂ) * Complex.I))
      Filter.atTop (nhds 0) := by
  have _ := hC
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero'
    (f := fun T : ℝ => ‖∫ x : ℝ in a..b, F ((x : ℂ) + (T : ℂ) * Complex.I)‖)
    (g := fun T : ℝ => (C * Real.exp (-(Real.pi / 2) * T) * T ^ A) * |b - a|)
    (Filter.Eventually.of_forall fun T => norm_nonneg _) ?_ (tendsto_edge_bound C A)
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with T hT
  calc ‖∫ x : ℝ in a..b, F ((x : ℂ) + (T : ℂ) * Complex.I)‖
      ≤ (C * Real.exp (-(Real.pi / 2) * T) * T ^ A) * |b - a| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro x hx
        rw [Set.uIoc_of_le hab] at hx
        exact hF x ⟨le_of_lt hx.1, hx.2⟩ T hT

end Work.LinnikAreas.Density4
