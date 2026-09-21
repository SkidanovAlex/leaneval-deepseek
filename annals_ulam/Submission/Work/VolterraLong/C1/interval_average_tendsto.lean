import Mathlib

namespace Work.VolterraLong.C1

open MeasureTheory

/-- If `f u σ → f s s` uniformly for `σ` between `s` and `u` as `u → s` along `l`, and `f u` is
interval integrable on `s..u`, then the average `(u - s)⁻¹ • ∫_s^u f u σ dσ` converges to
`f s s` along `l`. -/
theorem interval_average_tendsto {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → ℝ → E} {s : ℝ} {l : Filter ℝ} (hl : l ≤ nhdsWithin s {s}ᶜ)
    (hf : ∀ ε > 0, ∀ᶠ u in l, ∀ σ ∈ Set.uIcc s u, dist (f u σ) (f s s) < ε)
    (hint : ∀ᶠ u in l, IntervalIntegrable (fun σ => f u σ) volume s u) :
    Filter.Tendsto (fun u => (u - s)⁻¹ • (∫ σ in s..u, f u σ)) l (nhds (f s s)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have hcompl : {s}ᶜ ∈ l := hl self_mem_nhdsWithin
  filter_upwards [hf (ε / 2) hε2, hint, hcompl] with u hfu hintu hu
  have hus : u ≠ s := by simpa using hu
  have hsub : u - s ≠ 0 := sub_ne_zero.mpr hus
  have habs : |u - s| ≠ 0 := abs_ne_zero.mpr hsub
  have hg_int : IntervalIntegrable (fun σ : ℝ => f u σ - f s s) volume s u :=
    hintu.sub intervalIntegrable_const
  have hsplit : (∫ σ in s..u, f u σ)
      = (∫ σ in s..u, (fun σ : ℝ => f u σ - f s s) σ) + (u - s) • f s s := by
    rw [← intervalIntegral.integral_const (a := s) (b := u) (f s s),
      ← intervalIntegral.integral_add hg_int intervalIntegrable_const]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp
  rw [hsplit, smul_add, smul_smul, inv_mul_cancel₀ hsub, one_smul, dist_eq_norm,
    add_sub_cancel_right]
  have hbound : ‖∫ σ in s..u, (fun σ : ℝ => f u σ - f s s) σ‖ ≤ (ε / 2) * |u - s| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => by
      have hx' : x ∈ Set.uIcc s u := Set.uIoc_subset_uIcc hx
      have h := hfu x hx'
      rw [dist_eq_norm] at h
      exact le_of_lt h)
  calc ‖(u - s)⁻¹ • (∫ σ in s..u, (fun σ : ℝ => f u σ - f s s) σ)‖
      = |u - s|⁻¹ * ‖∫ σ in s..u, (fun σ : ℝ => f u σ - f s s) σ‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv]
    _ ≤ |u - s|⁻¹ * ((ε / 2) * |u - s|) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = ε / 2 := by
        rw [← mul_assoc, mul_comm (|u - s|⁻¹) (ε / 2), mul_assoc,
          inv_mul_cancel₀ habs, mul_one]
    _ < ε := by linarith

end Work.VolterraLong.C1
