import Mathlib
import Submission.Work.RPB1a.Defs

namespace Work.RPB1a

open Complex Set Metric
open scoped ContDiff Real
open Work.RPB1a

/-- `IsLoopFamily` is stable under the affine image `z ↦ a * z + b` of the plane with `a ≠ 0`.
The four fields are transported as follows: joint smoothness is preserved because
`z ↦ a * z + b` is smooth (`ContDiff.const_smul`, `ContDiff.add`), periodicity is immediate,
injectivity mod `2π` follows by cancelling `a` (`mul_left_cancel₀`) after cancelling the
translation, and the non-vanishing of the `t`-derivative follows from
`deriv (fun t => a * c s t + b) t = a * deriv (c s) t` (`deriv_add_const`, `deriv_const_mul`)
together with `a ≠ 0`. -/
theorem loopFamily_affine {c : ℝ → ℝ → ℂ} (hc : IsLoopFamily c) (a b : ℂ) (ha : a ≠ 0) :
    IsLoopFamily (fun s t => a * c s t + b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hc.1.const_smul a).add contDiff_const
  · intro s t
    simp only [hc.2.1 s t]
  · intro s hs t t' h
    exact hc.2.2.1 s hs t t' (mul_left_cancel₀ ha (add_right_cancel h))
  · intro s hs t
    have hcomp : ContDiff ℝ ∞ (fun t : ℝ => (s, t)) := by fun_prop
    have hct : ContDiff ℝ ∞ (fun t : ℝ => c s t) := hc.1.comp hcomp
    have hd : DifferentiableAt ℝ (c s) t := (hct.differentiable (by simp)).differentiableAt
    rw [deriv_add_const, deriv_const_mul a hd]
    exact mul_ne_zero ha (hc.2.2.2 s hs t)

end Work.RPB1a
