/-
# `FIArea2/R6/Area6eBDefs.lean` — the nonnegative majorisation `majG` of the round-6 majorant

`Work.FIArea2.R6.majF Pa f hf` is the compactly supported `C⁴` interpolant of the round-6
majorant sequence `f` (`Pack6.lean`, from `IsMajorant6`).  It is **not** nonnegative: the
`IsMajorant6` clauses constrain the interpolant only through `F(n) = f n` and the derivative
bounds `|F^{(j)}| ≤ cMaj j·M^{-j}`, which allow dips of size `O(M^{-1})` between two consecutive
integers.  The (7.10) input `Work.FIArea2.R6.FintProp` of the round-6 area-2 assembly, on the
other hand, is stated for functions with `0 ≤ F`, so it cannot be applied to `majF` directly.

This module supplies the standard repair

  `majG u = √(majF u ^ 2 + δ^2) - δ`,  `δ = Pa.M⁻¹`,

which is `C¹`, nonnegative, compactly supported in `[M/64, 64M]` (it vanishes exactly where
`majF` does), has the same derivative constant `Cder6·M⁻¹` (the factor `|majF|/√(majF²+δ²) ≤ 1`),
is pointwise within `O(M⁻¹)` of `majF` (i.e. `majG` is `max(majF,0)` up to `O(M⁻¹)`), and whose
trace at the integers is `n ↦ √(f n ^ 2 + δ^2) - δ` — a function that vanishes exactly at the
integers where `f` vanishes, so that the support clause of `FintProp` is inherited from
`IsMajorant6`.
-/
import Mathlib
import Submission.Work.FIArea2.R6.Pack6
import Submission.Work.FIArea2.R6.ExactMain

set_option autoImplicit false

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The nonnegative majorisation of the round-6 majorant**: `√(majF² + δ²) - δ` with
`δ = M⁻¹`.  It equals `max(majF, 0)` up to `O(δ)`, is nonnegative, has the same support and the
same derivative constant as `majF`, and its trace vanishes exactly where `f` does. -/
def majG (Pa : Work.FITop.Params) (f : ℤ → ℝ) (hf : Work.FITop4.IsMajorant6 Pa f) : ℝ → ℝ :=
  fun u => Real.sqrt (majF Pa f hf u ^ 2 + (Pa.M)⁻¹ ^ 2) - (Pa.M)⁻¹

end

end Work.FIArea2.R6
