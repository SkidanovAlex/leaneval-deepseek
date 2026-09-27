import Mathlib
import Submission.Work.PL.Approx.Defs

/-!
# Continuity of the one-dimensional cutoff `seg`

`seg a b u = clamp 0 1 ((b - |u|) / (b - a))` is a composition of continuous functions
(`|·|`, subtraction by a constant, division by the constant `b - a`, and the clamp
`max 0 ∘ min 1`), hence continuous.  Note that no hypothesis `a < b` is needed: for
`a = b` the quotient is still a continuous function of `u` (division by the constant
`b - a = 0` is multiplication by `0⁻¹ = 0`), and `clamp` is everywhere continuous.
-/

namespace Work.PL.Approx.Seg

open Work.PL.Approx

/-- The one-dimensional cutoff `seg a b` is continuous, for all `a b : ℝ`. -/
lemma continuous_seg (a b : ℝ) : Continuous (fun u : ℝ => seg a b u) := by
  unfold seg clamp
  fun_prop

end Work.PL.Approx.Seg
