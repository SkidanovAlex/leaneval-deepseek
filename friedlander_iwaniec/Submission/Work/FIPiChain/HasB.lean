/-
# `Submission.Work.FIPiChain.HasB`

The chain modules of this chapter are **verbatim copies** of `Submission/Work/FIChain/*` with the
*pinned* scale `Bstar = 2^31 + 2` replaced by a *free* parameter `Bc ≥ 2` (the sieve-range exponent
of the corrected family `sc x B`, `Yc x B`, `zc x B`).

Rather than thread that parameter as an explicit argument through every copied declaration (which
would force an edit at every one of the several hundred call sites), the parameter is carried by a
**typeclass instance**:

  `class HasBc where val : ℝ; ge_two : 2 ≤ val`

A copied declaration whose statement mentions the scale acquires `[HasBc]` as an *instance-implicit*
argument automatically (Lean's section-variable mechanism), and every call site inside the chapter
receives it by instance synthesis from the enclosing declaration's own instance.  The pin is
recovered by instantiating with `HasBc.of Work.FIChain.Bstar (by norm_num)` and every admissible
exponent by `HasBc.of B hB`.
-/
import Mathlib

set_option autoImplicit false

/-- A free version of the FIChain scale parameter: a real number `val ≥ 2`.  Carried as a
typeclass so that the copied chain modules (which were written against the global constant
`Work.FIChain.Bstar`) need no call-site edits. -/
class HasBc where
  /-- The sieve-range exponent `B ≥ 2` of the corrected family. -/
  val : ℝ
  /-- The admissibility condition used throughout the chain. -/
  ge_two : 2 ≤ val

namespace HasBc

/-- An instance from an admissible exponent. -/
@[reducible] def of (B : ℝ) (hB : 2 ≤ B) : HasBc := ⟨B, hB⟩

/-- `0 < val`. -/
theorem val_pos (self : HasBc) : 0 < self.val :=
  lt_of_lt_of_le (by norm_num) (HasBc.ge_two (self := self))

end HasBc
