import Mathlib
import Submission.Work.Motion.pertSetup

namespace Work.Motion

open Work.Motion.Pert

/-- `Fmap τ m q` is the map `w ↦ TcIter m (q.1, τ q.2 + w) - TcIter m (q.1, τ q.2)`;
it is holomorphic in `w` (indeed a polynomial, since `TcIter m` is a polynomial
in its second variable and no hypothesis on `τ` is needed: `τ q.2` is a constant). -/
theorem differentiableAt_Fmap (τ : ℂ → ℂ) (m : ℕ) (q : ℂ × ℂ) (w : ℂ) :
    DifferentiableAt ℂ (Work.Motion.Pert.Fmap τ m q) w := by
  have h : Work.Motion.Pert.Fmap τ m q
      = fun w => TcIter m (q.1, τ q.2 + w) - TcIter m (q.1, τ q.2) := rfl
  rw [h]
  exact ((differentiable_TcIter m).differentiableAt.comp w
    ((differentiableAt_const q.1).prodMk
      ((differentiableAt_const (τ q.2)).add differentiableAt_id))).sub_const _

end Work.Motion
