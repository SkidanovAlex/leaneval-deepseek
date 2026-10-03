import Mathlib

namespace Work.Pert

open MeasureTheory

/-- Pushforward of Lebesgue measure on `ℝ` under the affine map `y ↦ a * y + c`
with `a > 0`: it is `a⁻¹` times Lebesgue measure. -/
private theorem map_mul_add_volume {a c : ℝ} (ha : 0 < a) :
    Measure.map (fun y : ℝ => a * y + c) volume = ENNReal.ofReal a⁻¹ • (volume : Measure ℝ) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hg : Measurable (fun u : ℝ => u + c) := by fun_prop
  have hf : Measurable (fun y : ℝ => a • y) := by fun_prop
  have hcomp : (fun y : ℝ => a * y + c) = (fun u : ℝ => u + c) ∘ (fun y : ℝ => a • y) := by
    funext y; simp [smul_eq_mul]
  rw [hcomp, ← Measure.map_map hg hf]
  rw [Measure.map_addHaar_smul volume ha0]
  have hfin : Module.finrank ℝ ℝ = 1 := by simp
  rw [hfin]
  have habs : ENNReal.ofReal |(a ^ (1 : ℕ))⁻¹| = ENNReal.ofReal a⁻¹ := by
    rw [pow_one, abs_inv, abs_of_pos ha]
  rw [habs]
  rw [Measure.map_smul]
  · rw [MeasureTheory.map_add_right_eq_self volume c]
  · exact hg.aemeasurable

theorem lintegral_comp_mul_add {a c : ℝ} (ha : 0 < a) (F : ℝ → ENNReal) (hF : Measurable F) :
    ∫⁻ y : ℝ, F (a * y + c) = ENNReal.ofReal a⁻¹ * ∫⁻ u : ℝ, F u := by
  have hT : Measurable (fun y : ℝ => a * y + c) := by fun_prop
  rw [← MeasureTheory.lintegral_map hF hT]
  rw [map_mul_add_volume ha, MeasureTheory.lintegral_smul_measure, smul_eq_mul]

end Work.Pert
