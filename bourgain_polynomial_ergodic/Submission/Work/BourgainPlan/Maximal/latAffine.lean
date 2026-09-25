import Mathlib

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BourgainPlan.Maximal

theorem lintegral_comp_affine (g : ℝ → ENNReal) (hg : Measurable g) {Q : ℝ} (hQ : 0 < Q)
    (m : ℝ) : ∫⁻ y, g (Q * y + m) = ENNReal.ofReal Q⁻¹ * ∫⁻ y, g y := by
  have hmul : Measurable (fun y : ℝ => Q * y) := measurable_const_mul Q
  have hshift : Measurable (fun z : ℝ => g (z + m)) := hg.comp (measurable_id.add_const m)
  rw [show (fun y : ℝ => g (Q * y + m))
      = (fun z : ℝ => g (z + m)) ∘ (fun y : ℝ => Q * y) from rfl]
  rw [MeasureTheory.lintegral_comp (μ := volume) hshift hmul]
  rw [Real.map_volume_mul_left hQ.ne']
  rw [MeasureTheory.lintegral_smul_measure]
  rw [abs_of_pos (inv_pos.mpr hQ), MeasureTheory.lintegral_add_right_eq_self g m, smul_eq_mul]

theorem integrable_comp_affine {H : ℝ → ℂ} (hH : MeasureTheory.Integrable H) {Q : ℝ} (hQ : 0 < Q)
    (m : ℝ) : MeasureTheory.Integrable (fun y : ℝ => H (Q * y + m)) := by
  have hshift : MeasureTheory.Integrable (fun z : ℝ => H (z + m)) :=
    (hH.comp_add_left m).congr (Filter.Eventually.of_forall fun z => by simp [add_comm])
  exact hshift.comp_mul_left' hQ.ne'

end Work.BourgainPlan.Maximal
