import Mathlib
import Submission.Work.Analysis.integrable_inv_norm_mul

/-!
# Integrability of `z ↦ ‖z - p‖⁻¹ * ‖z - q‖⁻¹ * v z` (two distinct singularities)

For `p ≠ q` and a continuous compactly supported `v : ℂ → ℝ` the function
`z ↦ ‖z - p‖⁻¹ * ‖z - q‖⁻¹ * v z` is integrable for the Lebesgue measure on `ℂ`.

The two logarithmic singularities are handled by the elementary inequality
`‖z - p‖⁻¹ * ‖z - q‖⁻¹ ≤ ‖p - q‖⁻¹ * (‖z - p‖⁻¹ + ‖z - q‖⁻¹)`, whose only content is
`‖p - q‖ ≤ ‖z - p‖ + ‖z - q‖`, i.e. the triangle inequality.  This bounds the two-pole function
by a constant times a sum of two one-pole functions, each of which is integrable by
`integrable_inv_norm_mul_of_hasCompactSupport`.
-/

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace Work.Analysis

/-- The pointwise domination of the two-pole kernel by two one-pole kernels:
`‖z - p‖⁻¹ ‖z - q‖⁻¹ ≤ ‖p - q‖⁻¹ (‖z - p‖⁻¹ + ‖z - q‖⁻¹)` for `p ≠ q`. -/
theorem inv_norm_mul_inv_norm_le {p q z : ℂ} (hpq : p ≠ q) :
    (‖z - p‖)⁻¹ * (‖z - q‖)⁻¹
      ≤ (‖p - q‖)⁻¹ * ((‖z - p‖)⁻¹ + (‖z - q‖)⁻¹) := by
  have hd : (0 : ℝ) < ‖p - q‖ := by
    rw [norm_pos_iff]; exact sub_ne_zero.mpr hpq
  have hab : ‖p - q‖ ≤ ‖z - p‖ + ‖z - q‖ := by
    have h : p - q = (p - z) + (z - q) := by ring
    rw [h]
    calc ‖(p - z) + (z - q)‖ ≤ ‖p - z‖ + ‖z - q‖ := norm_add_le _ _
      _ = ‖z - p‖ + ‖z - q‖ := by rw [norm_sub_rev]
  by_cases ha0 : ‖z - p‖ = 0
  · rw [ha0]; simp [inv_zero, zero_mul]; positivity
  by_cases hb0 : ‖z - q‖ = 0
  · rw [hb0]; simp [inv_zero, mul_zero]; positivity
  have ha' : 0 < ‖z - p‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm ha0)
  have hb' : 0 < ‖z - q‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hb0)
  have h : (‖z - p‖)⁻¹ * (‖z - q‖)⁻¹ * (‖z - p‖ * ‖z - q‖ * ‖p - q‖) ≤
      (‖p - q‖)⁻¹ * ((‖z - p‖)⁻¹ + (‖z - q‖)⁻¹) * (‖z - p‖ * ‖z - q‖ * ‖p - q‖) := by
    have e1 : (‖z - p‖)⁻¹ * (‖z - q‖)⁻¹ * (‖z - p‖ * ‖z - q‖ * ‖p - q‖)
        = ‖p - q‖ := by field_simp
    have e2 : (‖p - q‖)⁻¹ * ((‖z - p‖)⁻¹ + (‖z - q‖)⁻¹) * (‖z - p‖ * ‖z - q‖ * ‖p - q‖)
        = ‖z - p‖ + ‖z - q‖ := by field_simp; ring
    rw [e1, e2]; exact hab
  exact le_of_mul_le_mul_right h (by positivity)

/-- Integrability of `z ↦ ‖z - p‖⁻¹ * ‖z - q‖⁻¹ * v z` for `p ≠ q` and continuous compactly
supported `v`, the two-pole companion of `integrable_inv_norm_mul_of_hasCompactSupport`. -/
theorem integrable_inv_norm_mul_two {p q : ℂ} (hpq : p ≠ q) (v : ℂ → ℝ)
    (hv : Continuous v) (hc : HasCompactSupport v) :
    MeasureTheory.Integrable (fun z : ℂ => (‖z - p‖)⁻¹ * (‖z - q‖)⁻¹ * v z)
      MeasureTheory.volume := by
  have h1 : Integrable (fun z : ℂ => (‖z - p‖)⁻¹ * ‖v z‖) :=
    integrable_inv_norm_mul_of_hasCompactSupport p (fun z => ‖v z‖) hv.norm hc.norm
  have h2 : Integrable (fun z : ℂ => (‖z - q‖)⁻¹ * ‖v z‖) :=
    integrable_inv_norm_mul_of_hasCompactSupport q (fun z => ‖v z‖) hv.norm hc.norm
  have hg : Integrable (fun z : ℂ =>
      (‖p - q‖)⁻¹ * ((‖z - p‖)⁻¹ * ‖v z‖ + (‖z - q‖)⁻¹ * ‖v z‖)) volume :=
    (h1.add h2).const_mul _
  refine hg.mono' ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    exact ((measurable_norm.comp (measurable_id.sub measurable_const)).inv.mul
      (measurable_norm.comp (measurable_id.sub measurable_const)).inv).mul hv.measurable
  · filter_upwards with z
    have key := inv_norm_mul_inv_norm_le (p := p) (q := q) (z := z) hpq
    calc ‖(‖z - p‖)⁻¹ * (‖z - q‖)⁻¹ * v z‖
        = (‖z - p‖)⁻¹ * (‖z - q‖)⁻¹ * ‖v z‖ := by
          rw [norm_mul, norm_mul, norm_inv, norm_inv, norm_norm, norm_norm]
      _ = ((‖z - p‖)⁻¹ * (‖z - q‖)⁻¹) * ‖v z‖ := by ring
      _ ≤ ((‖p - q‖)⁻¹ * ((‖z - p‖)⁻¹ + (‖z - q‖)⁻¹)) * ‖v z‖ :=
          mul_le_mul_of_nonneg_right key (norm_nonneg _)
      _ = (‖p - q‖)⁻¹ * ((‖z - p‖)⁻¹ * ‖v z‖ + (‖z - q‖)⁻¹ * ‖v z‖) := by ring

end Work.Analysis
