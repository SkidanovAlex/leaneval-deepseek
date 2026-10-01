import Mathlib

open MeasureTheory Filter

namespace Work.ZeroDensity.Ingham

/-- For `x` in the unordered interval from `p` to `q`, `|x| ≤ |p| + |q|`. -/
lemma abs_le_abs_add_abs_of_mem_uIoc {p q x : ℝ} (hx : x ∈ Set.uIoc p q) :
    |x| ≤ |p| + |q| := by
  rcases (Set.mem_uIoc.mp hx) with ⟨hp, hq⟩ | ⟨hq, hp⟩
  · calc |x| ≤ max |p| |q| := abs_le_max_abs_abs (le_of_lt hp) hq
      _ ≤ |p| + |q| := max_le (le_add_of_nonneg_right (abs_nonneg q))
          (le_add_of_nonneg_left (abs_nonneg p))
  · calc |x| ≤ max |q| |p| := abs_le_max_abs_abs (le_of_lt hq) hp
      _ ≤ |p| + |q| := max_le (le_add_of_nonneg_left (abs_nonneg p))
          (le_add_of_nonneg_right (abs_nonneg q))

theorem horizontalPoleDecaySub (a u : ℂ) (p q : ℝ) :
    Filter.Tendsto (fun R : ℝ => ∫ x in p..q, a / ((x : ℂ) - R * Complex.I - u)) Filter.atTop (nhds 0) := by
  have key : ∀ᶠ R : ℝ in Filter.atTop,
      ‖∫ x in p..q, a / ((x : ℂ) - R * Complex.I - u)‖ ≤ (2 * ‖a‖ * |q - p|) / R := by
    filter_upwards [eventually_ge_atTop (2 * (|p| + |q| + ‖u‖ + 1))] with R hR
    have hRpos : 0 < R := by linarith [abs_nonneg p, abs_nonneg q, norm_nonneg u]
    have hpt : ∀ x ∈ Set.uIoc p q, ‖a / ((x : ℂ) - R * Complex.I - u)‖ ≤ 2 * ‖a‖ / R := by
      intro x hx
      have hxabs : |x| ≤ |p| + |q| := abs_le_abs_add_abs_of_mem_uIoc hx
      have hxu : ‖(x : ℂ) - u‖ ≤ |p| + |q| + ‖u‖ := by
        calc ‖(x : ℂ) - u‖ ≤ ‖(x : ℂ)‖ + ‖u‖ := norm_sub_le _ _
          _ = |x| + ‖u‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
          _ ≤ |p| + |q| + ‖u‖ := by linarith
      have hz : R / 2 ≤ ‖(x : ℂ) - R * Complex.I - u‖ := by
        have h1 : ‖(x : ℂ) - R * Complex.I - u‖ = ‖R * Complex.I - ((x : ℂ) - u)‖ := by
          rw [show (x : ℂ) - R * Complex.I - u = -(R * Complex.I - ((x : ℂ) - u)) by ring,
            norm_neg]
        rw [h1]
        have h2 : ‖R * Complex.I‖ - ‖(x : ℂ) - u‖ ≤ ‖R * Complex.I - ((x : ℂ) - u)‖ :=
          norm_sub_norm_le _ _
        have h3 : ‖R * Complex.I‖ = R := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (le_of_lt hRpos)]
        linarith
      rw [norm_div]
      have hle := div_le_div_of_nonneg_left (norm_nonneg a) (by linarith : (0:ℝ) < R / 2) hz
      calc ‖a‖ / ‖(x : ℂ) - R * Complex.I - u‖ ≤ ‖a‖ / (R / 2) := hle
        _ = 2 * ‖a‖ / R := by field_simp
    calc ‖∫ x in p..q, a / ((x : ℂ) - R * Complex.I - u)‖
        ≤ (2 * ‖a‖ / R) * |q - p| := intervalIntegral.norm_integral_le_of_norm_le_const hpt
      _ = (2 * ‖a‖ * |q - p|) / R := by ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (0:ℝ)) Filter.atTop (nhds 0))
    (Filter.Tendsto.const_div_atTop tendsto_id (2 * ‖a‖ * |q - p|))
    (Eventually.of_forall fun R => norm_nonneg _) key

end Work.ZeroDensity.Ingham
