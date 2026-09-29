import Submission.Work.IntLib.SqrtGcd.Defs

/-!
# Binary gcd: pure layer

`oddPart n` is `n` with all factors of `2` removed; `gcdStep u v` is one iteration of the binary
gcd (both arguments odd and distinct): the *larger* of `u`, `v` is replaced by the odd part of the
difference.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib
namespace SG

open HvdH Work.Layout

/-- `n` with all factors of `2` removed. -/
def oddPart (n : ℕ) : ℕ :=
  if n % 2 = 0 ∧ 0 < n then oddPart (n / 2) else n
termination_by n
decreasing_by omega

/-- One binary-gcd step (for odd, distinct arguments): replace the larger one by `oddPart` of the
difference. -/
def gcdStep (u v : ℕ) : ℕ × ℕ :=
  if v ≤ u then (oddPart (u - v), v) else (u, oddPart (v - u))

end SG
end Work.IntLib
