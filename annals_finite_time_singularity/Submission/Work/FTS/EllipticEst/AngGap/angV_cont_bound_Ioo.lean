import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.AngGap.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.EllipticEst.AngGap

theorem angV_cont_bound_Ioo (h : ℝ → ℝ) (C : ℝ) (hC : 0 < C)
    (hg : ∀ θ ∈ Set.Ioo 0 (π / 2), HasDerivAt (Work.FTS.EllipticEst.AngGap.angG h)
        (h θ * Real.sin (2 * θ)) θ)
    (hCg : ∀ θ ∈ Set.Icc 0 (π / 2),
        |Work.FTS.EllipticEst.AngGap.angG h θ| ≤ C * (Real.sin (2 * θ)) ^ 3) :
    ContinuousOn (Work.FTS.EllipticEst.AngGap.angV h) (Set.Ioo 0 (π / 2)) ∧
    ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Work.FTS.EllipticEst.AngGap.angV h θ| ≤ C * (Real.sin (2 * θ)) ^ 2 := by
  constructor
  · -- `angG h` is differentiable (hence continuous) on the open interval, `sin (2·)` too,
    -- and the denominator does not vanish there.
    have hcontSin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (π / 2)) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    have hcontG : ContinuousOn (angG h) (Set.Ioo 0 (π / 2)) :=
      fun θ hθ => (hg θ hθ).continuousAt.continuousWithinAt
    have hq := hcontG.div hcontSin (fun θ hθ => ne_of_gt (sin_two_pos hθ))
    have hfun : (angG h / fun θ : ℝ => Real.sin (2 * θ)) = angV h := by
      funext θ; simp only [Pi.div_apply, angV]
    rwa [hfun] at hq
  · intro θ hθ
    have hs : 0 < Real.sin (2 * θ) := sin_two_pos hθ
    have hsne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hs
    have h1 := div_le_div_of_nonneg_right (hCg θ (Set.Ioo_subset_Icc_self hθ)) hs.le
    have h2 : C * (Real.sin (2 * θ)) ^ 3 / Real.sin (2 * θ) = C * (Real.sin (2 * θ)) ^ 2 := by
      field_simp
    rw [angV, abs_div, abs_of_pos hs]
    linarith [h1, h2]

end Work.FTS.EllipticEst.AngGap
