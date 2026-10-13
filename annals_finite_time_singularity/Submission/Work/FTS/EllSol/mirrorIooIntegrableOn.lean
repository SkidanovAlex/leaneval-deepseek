import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol

theorem mirrorIooIntegrableOn (F : ℝ → ℝ) :
    MeasureTheory.IntegrableOn F (Set.Ioo (Real.pi / 4) (Real.pi / 2)) ↔
      MeasureTheory.IntegrableOn (fun φ : ℝ => F (Real.pi / 2 - φ)) (Set.Ioo 0 (Real.pi / 4)) := by
  -- `IntegrableOn` on an open interval is `IntervalIntegrable` on its endpoints
  have h₁ := intervalIntegrable_iff_integrableOn_Ioo_of_le (f := F) (μ := MeasureTheory.volume)
      (a := Real.pi / 4) (b := Real.pi / 2) (by linarith [Real.pi_pos])
  have h₂ := intervalIntegrable_iff_integrableOn_Ioo_of_le
      (f := fun φ : ℝ => F (Real.pi / 2 - φ))
      (μ := MeasureTheory.volume) (a := 0) (b := Real.pi / 4) (by linarith [Real.pi_pos])
  -- the reflection `x ↦ π/2 - x` swaps the two intervals
  have h₃ : IntervalIntegrable (fun x => F (Real.pi / 2 - x)) MeasureTheory.volume (Real.pi / 4) 0 ↔
      IntervalIntegrable F MeasureTheory.volume (Real.pi / 4) (Real.pi / 2) := by
    have h := IntervalIntegrable.comp_sub_left_iff (f := F)
      (a := Real.pi / 4) (b := Real.pi / 2) (Real.pi / 2)
    rw [show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 from by ring,
        show Real.pi / 2 - Real.pi / 2 = 0 from by ring] at h
    exact h
  rw [← h₁, ← h₂, ← h₃]
  exact IntervalIntegrable.symm_iff

end Work.FTS.EllSol
