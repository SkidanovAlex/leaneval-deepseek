import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Elliptic.HardyTwoDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

theorem tendsto_abs_sin_two_mul (K : ℝ) :
    Filter.Tendsto (fun θ : ℝ => |Real.sin (2 * θ)| * K)
      (nhdsWithin (0 : ℝ) (Set.Icc 0 (Real.pi / 2))) (nhds (0 : ℝ)) := by
  have h : Continuous fun θ : ℝ => |Real.sin (2 * θ)| := by fun_prop
  have ht : Filter.Tendsto (fun θ : ℝ => |Real.sin (2 * θ)|)
      (nhdsWithin (0 : ℝ) (Set.Icc 0 (Real.pi / 2))) (nhds 0) := by
    have h1 := (h.tendsto 0).mono_left
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Icc 0 (Real.pi / 2)))
    simpa using h1
  simpa using ht.mul_const K

end Work.Elliptic
