import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Submission.Work.ConstructionInstance.GCompDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- For `0 < s ≤ 1` the map `t ↦ t^s` is concave on `[0,∞)`, hence for `0 < a ≤ b`
the difference `b^s - a^s` is bounded by the tangent value at `a`:
`s * a^(s-1) * (b - a)`. -/
theorem rpow_sub_le_mul {s a b : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (ha : 0 < a) (hab : a ≤ b) :
    b ^ s - a ^ s ≤ s * a ^ (s - 1) * (b - a) := by
  rcases eq_or_lt_of_le hab with hEq | hlt
  · simp [hEq]
  · have hconc : ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun t : ℝ => t ^ s) :=
      Real.concaveOn_rpow (le_of_lt hs) hs1
    have ha' : a ∈ Set.Ici (0 : ℝ) := le_of_lt ha
    have hb' : b ∈ Set.Ici (0 : ℝ) := le_trans (le_of_lt ha) hab
    have hdiff : DifferentiableAt ℝ (fun t : ℝ => t ^ s) a :=
      (Real.hasDerivAt_rpow_const (x := a) (p := s) (Or.inl (ne_of_gt ha))).differentiableAt
    have hslope := hconc.slope_le_deriv ha' hb' hlt hdiff
    rw [Real.deriv_rpow_const a s] at hslope
    rw [slope_def_field] at hslope
    rw [div_le_iff₀ (sub_pos.mpr hlt)] at hslope
    exact hslope

end Work.ConstructionInstance
