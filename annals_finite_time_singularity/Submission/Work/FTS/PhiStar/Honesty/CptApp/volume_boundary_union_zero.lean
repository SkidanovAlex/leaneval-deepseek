import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptApp

theorem volume_boundary_union_zero :
    (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
      ({p : ℝ × ℝ | p.1 = 0} ∪ {p : ℝ × ℝ | p.2 = 0}
        ∪ {p : ℝ × ℝ | p.2 = Real.pi / 2}) = 0 := by
  rw [MeasureTheory.Measure.volume_eq_prod]
  have h1 : {p : ℝ × ℝ | p.1 = 0} = ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
    ext p; simp
  have h2 : {p : ℝ × ℝ | p.2 = 0} = (Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ) := by
    ext p; simp
  have h3 : {p : ℝ × ℝ | p.2 = Real.pi / 2} =
      (Set.univ : Set ℝ) ×ˢ ({Real.pi / 2} : Set ℝ) := by
    ext p; simp
  rw [h1, h2, h3]
  refine MeasureTheory.measure_union_null (MeasureTheory.measure_union_null ?_ ?_) ?_
  · rw [MeasureTheory.Measure.prod_prod]; simp
  · rw [MeasureTheory.Measure.prod_prod]; simp
  · rw [MeasureTheory.Measure.prod_prod]; simp

end Work.FTS.PhiStar.Honesty.CptApp
