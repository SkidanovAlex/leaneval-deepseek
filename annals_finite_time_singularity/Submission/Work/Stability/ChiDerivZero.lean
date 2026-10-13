import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Stability

/-- The derivative of an even function at `0` vanishes: if `f (-x) = f x` for all `x`, then
`deriv f 0 = 0`.  (Mathlib's `deriv_comp_neg` computes the derivative of `x ↦ f (-x)` as
`x ↦ -deriv f (-x)`; at `x = 0` the two functions agree by evenness.) -/
theorem deriv_zero_of_even {f : ℝ → ℝ} (hf : ∀ x, f (-x) = f x) : deriv f 0 = 0 := by
  have h := deriv_comp_neg (f := f) (x := 0)
  rw [show (fun x : ℝ => f (-x)) = f from funext hf] at h
  simp only [neg_zero] at h
  linarith

/-- `chi` (the `C^∞` bump of the cut-off: `= 1` on `[-1,1]`, `= 0` off `(-2,2)`) is even,
hence its derivative at `0` vanishes. -/
theorem ChiDerivZero : deriv chi 0 = 0 :=
  deriv_zero_of_even chi_neg

end Work.Stability
