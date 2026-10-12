import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBox.LatticeModel.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBox.LatticeModel

open MeasureTheory Set
open scoped Real

/-- On `(0,∞)` the radial integrand `r² · 1_{r≤A}(r) · (c + c²/(2r²))` agrees with the
step function `1_{(0,A]}(r) · (c r² + c²/2)`. -/
private lemma radial_ball_bound_eqOn (c A : ℝ) :
    EqOn ((Set.Ioc (0 : ℝ) A).indicator (fun r : ℝ => c * r ^ 2 + c ^ 2 / 2))
      (fun r : ℝ => r ^ 2 * (Set.Iic A).indicator (fun s : ℝ => c + c ^ 2 / (2 * s ^ 2)) r)
      (Set.Ioi (0 : ℝ)) := by
  intro r hr
  simp only []
  rcases le_or_gt r A with hle | hlt
  · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hr, hle⟩),
        Set.indicator_of_mem (Set.mem_Iic.mpr hle)]
    have hr0 : r ≠ 0 := ne_of_gt hr
    field_simp
  · rw [Set.indicator_of_notMem (fun h => absurd h.2 (not_le.mpr hlt)),
        Set.indicator_of_notMem (fun h => absurd (Set.mem_Iic.mp h) (not_le.mpr hlt))]
    ring

lemma integrableOn_radial_ball_bound (c A : ℝ) :
    MeasureTheory.IntegrableOn (fun r : ℝ => r ^ 2 * (Set.Iic A).indicator (fun s : ℝ => c + c ^ 2 / (2 * s ^ 2)) r)
      (Set.Ioi (0 : ℝ)) := by
  -- The step function `1_{(0,A]}(r) · (c r² + c²/2)` is integrable on the whole halfline:
  -- it is the indicator of the interval `(0,A]` of a continuous function.
  have hbase : IntegrableOn (fun r : ℝ => c * r ^ 2 + c ^ 2 / 2) (Set.Ioc (0 : ℝ) A) volume :=
    (by fun_prop : Continuous fun r : ℝ => c * r ^ 2 + c ^ 2 / 2).integrableOn_Ioc
  have hind : IntegrableOn
      ((Set.Ioc (0 : ℝ) A).indicator (fun r : ℝ => c * r ^ 2 + c ^ 2 / 2))
      (Set.Ioi (0 : ℝ)) volume := by
    rw [integrableOn_indicator_iff measurableSet_Ioc,
      Set.inter_eq_left.mpr (fun x hx => hx.1)]
    exact hbase
  exact hind.congr_fun (radial_ball_bound_eqOn c A) measurableSet_Ioi

end Work.BoseBox.LatticeModel
