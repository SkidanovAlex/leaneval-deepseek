import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.FTS.StrongEps.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.L12JepsAux

/-- The map `p ↦ (a - p.1, c - p.2)` on `ℝ × ℝ` is `p ↦ (a, c) - p`, a reflection of the
additive group, hence (quasi-)measure preserving for the Lebesgue measure. -/
theorem quasiMeasurePreserving_sub {a c : ℝ} :
    MeasureTheory.Measure.QuasiMeasurePreserving
      (fun p : ℝ × ℝ => (a - p.1, c - p.2))
      (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) MeasureTheory.volume :=
  (MeasureTheory.Measure.measurePreserving_sub_left
    (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) (a, c)).quasiMeasurePreserving

theorem ae_eq_comp_sub {P Q : ℝ × ℝ → ℝ} (h : P =ᵐ[MeasureTheory.volume] Q) (a c : ℝ) :
    (fun p : ℝ × ℝ => P (a - p.1, c - p.2)) =ᵐ[MeasureTheory.volume]
      (fun p : ℝ × ℝ => Q (a - p.1, c - p.2)) :=
  quasiMeasurePreserving_sub (a := a) (c := c) |>.ae_eq_comp h

end Work.FTS.StrongEps.EpsE4Thr.L12JepsAux
