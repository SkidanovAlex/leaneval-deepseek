import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

theorem integral_alpha_div_mul_rpow {α : ℝ} (hα : 0 < α) {a z : ℝ} (ha : 0 < a)
    (haz : a ≤ z) :
    ∫ r in a..z, ((5 + α) / (α * r)) * (r / a) ^ ((5 + α) / α)
      = (z / a) ^ ((5 + α) / α) - 1 := by
  set c : ℝ := (5 + α) / α with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have step : ∀ x ∈ Set.uIcc a z,
      HasDerivAt (fun r => (r / a) ^ c) (((5 + α) / (α * x)) * (x / a) ^ c) x := by
    intro x hx
    rw [Set.uIcc_of_le haz] at hx
    have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
    have hxa : 0 < x / a := div_pos hxpos ha
    have hd : HasDerivAt (fun r : ℝ => (r / a) ^ c) (((5 + α) / (α * x)) * (x / a) ^ c) x := by
      have h1 : HasDerivAt (fun r : ℝ => r / a) (1 / a) x := by
        simpa using (hasDerivAt_id x).div_const a
      have h2 : HasDerivAt (fun y : ℝ => y ^ c) (c * (x / a) ^ (c - 1)) (x / a) := by
        simpa using Real.hasDerivAt_rpow_const (x := x / a) (p := c) (Or.inl (ne_of_gt hxa))
      have heq : c * (x / a) ^ (c - 1) * (1 / a) = ((5 + α) / (α * x)) * (x / a) ^ c := by
        have hrw : (x / a) ^ c = (x / a) ^ (c - 1) * (x / a) := by
          conv_lhs => rw [← sub_add_cancel c 1]
          rw [Real.rpow_add hxa, Real.rpow_one]
        rw [hrw]
        set S : ℝ := (x / a) ^ (c - 1) with hS
        rw [hc]
        field_simp
      convert h2.comp x h1 using 1
      · funext r; rfl
      · exact heq.symm
    exact hd
  have hint : IntervalIntegrable
      (fun r : ℝ => ((5 + α) / (α * r)) * (r / a) ^ c) MeasureTheory.volume a z := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le haz]
    have hf : ContinuousOn (fun r : ℝ => (r / a) ^ c) (Set.Icc a z) :=
      ContinuousOn.rpow_const (continuousOn_id.div_const a) (fun x _ => Or.inr (le_of_lt hcpos))
    exact (continuousOn_const.div (continuousOn_const.mul continuousOn_id) (fun x hx =>
        mul_ne_zero (ne_of_gt hα) (ne_of_gt (lt_of_lt_of_le ha hx.1)))).mul hf
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun r => (r / a) ^ c) step hint
  simpa [div_self (ne_of_gt ha)] using h

end Work.FTS.ClassC
