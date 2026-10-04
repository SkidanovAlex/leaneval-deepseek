import Mathlib
import Submission.Work.Diff.Dim2.Lib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set Filter

/-- The two components of `circPt` determine the angle: if `circPt a = circPt b` then
`Real.cos a = Real.cos b` and `Real.sin a = Real.sin b`. -/
lemma circPt_components_eq {a b : ℝ} (hab : circPt a = circPt b) :
    Real.cos a = Real.cos b ∧ Real.sin a = Real.sin b := by
  constructor
  · have h := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) hab
    simpa [circPt_zero] using h
  · have h := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) hab
    simpa [circPt_one] using h

/-- `circPt` is the unit circle parametrisation `t ↦ exp (i t)`: an equality `circPt a = circPt b`
is an equality of the corresponding points of `Circle`. -/
lemma circPt_eq_circle_exp {a b : ℝ} (hab : circPt a = circPt b) :
    Circle.exp a = Circle.exp b := by
  obtain ⟨hcos, hsin⟩ := circPt_components_eq hab
  apply Subtype.ext
  rw [Circle.coe_exp, Circle.coe_exp, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I,
    hcos, hsin]

/-- **`circPt` is injective on the half-open interval `[0, 2π)`**: every point of the unit circle
has a unique angle in `[0, 2π)`. -/
theorem circPt_injOn :
    Set.InjOn (Work.Diff.Dim2.circPt) (Set.Ico 0 (2 * Real.pi)) := by
  intro a ha b hb hab
  exact Circle.exp_injOn_Ico (by linarith [Real.pi_pos] : (2 * Real.pi) - 0 ≤ 2 * Real.pi)
    ha hb (circPt_eq_circle_exp hab)

end Work.Diff.Dim2
