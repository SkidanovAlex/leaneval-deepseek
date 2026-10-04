import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The entire function `cosSqrt s = cos (√s)` as a power series

`cosSqrt s = ∑' n, (-1)^n s^n / (2n)!` is the entire function whose value at `s ≥ 0` is
`Real.cos (Real.sqrt s)` (equivalently: `cosSqrt (x^2) = Real.cos x` for all real `x`).  It is the
"even half" of the cosine series, and its whole point is that it is `C^∞` at `0`, where
`s ↦ Real.cos (Real.sqrt s)` is only one-sided smooth.

This module only fixes the definition, so that lemmas about it can be stated in other modules.
-/

namespace Work.Diff.C

open scoped BigOperators

/-- The entire function with `cosSqrt (x^2) = Real.cos x`. -/
noncomputable def cosSqrt (s : ℝ) : ℝ :=
  ∑' n : ℕ, (-1) ^ n * s ^ n / ((Nat.factorial (2 * n) : ℕ) : ℝ)

end Work.Diff.C
