import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Spaces.DthIter_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.VopTransfer

/-- Helper: `Lop` sends `C^∞` functions (in the sense of `∀ k, ContDiff ℝ k`) to
`C^∞` functions.  The derivative lowers the order by one and the multiplication by
`sin (2θ)` restores it. -/
theorem contDiff_Lop (u : ℝ → ℝ) (hu : ∀ k : ℕ, ContDiff ℝ k u) :
    ∀ k : ℕ, ContDiff ℝ k (Work.Spaces.Lop u) := by
  intro k
  change ContDiff ℝ k ((fun θ : ℝ => Real.sin (2 * θ)) * deriv u)
  have hd : ContDiff ℝ k (deriv u) :=
    -- `ContDiff.deriv'` lowers the order by one
    ContDiff.deriv' (𝕜 := ℝ) (f := u) (n := (k : WithTop ℕ∞)) (hu (k + 1))
  have hsin : ContDiff ℝ k (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
  exact hsin.mul hd

theorem contDiff_Lop_iterate (u : ℝ → ℝ) (hu : ∀ k : ℕ, ContDiff ℝ k u) (r : ℕ) :
    ∀ k : ℕ, ContDiff ℝ k (Work.Spaces.Lop^[r] u) := by
  induction r with
  | zero => simpa using hu
  | succ r ih =>
      rw [Function.iterate_succ_apply']
      exact contDiff_Lop _ ih

end Work.FTS_EllLimOK.VopTransfer
