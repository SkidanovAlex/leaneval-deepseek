import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Sys

theorem intervalIntegrable_if_zero_add {S : ℝ} (hS : 0 < S) {F A B : ℝ → ℝ}
    (hF : IntervalIntegrable F MeasureTheory.volume 0 S)
    (hA : ContinuousOn A (Set.Icc 0 S)) (hB : ContinuousOn B (Set.Icc 0 S)) :
    IntervalIntegrable (fun τ => (if τ = 0 then 0 else F τ) + A τ + B τ)
      MeasureTheory.volume 0 S := by
  have hSle : (0 : ℝ) ≤ S := le_of_lt hS
  -- The modified function agrees with `F` on the (open) interval of integration.
  have hF0 :
      IntervalIntegrable (fun τ => if τ = 0 then 0 else F τ) MeasureTheory.volume 0 S := by
    refine hF.congr_uIoo ?_
    intro τ hτ
    rw [Set.uIoo_of_le hSle] at hτ
    simp only
    rw [ite_eq_right (ne_of_gt hτ.1)]
  -- `A + B` is continuous on `[0, S]`, hence interval integrable.
  have hAB : IntervalIntegrable (A + B) MeasureTheory.volume 0 S :=
    (hA.add hB).intervalIntegrable_of_Icc hSle
  have h := hF0.add hAB
  simpa [Pi.add_apply, add_assoc] using h

end Work.FTS_RegExport.RXT.Sys
