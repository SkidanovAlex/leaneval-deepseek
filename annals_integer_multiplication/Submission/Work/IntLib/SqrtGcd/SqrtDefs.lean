import Submission.Work.IntLib.SqrtGcd.Defs

/-!
# Integer square root: pure layer

The restoring (bit-pair) square root.  `s` is the value of the prefix of the radicand read so far,
`r` the current root and `rem = s - r ^ 2`; `bhi`, `blo` are the next two bits of the radicand
(`bhi` the more significant one).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.IntLib
namespace SG

open HvdH Work.Layout

/-- One restoring square-root step: returns the new `(s, r, rem)`. -/
def sqrtStep (s r rem : ℕ) (bhi blo : Bool) : ℕ × ℕ × ℕ :=
  let p := 2 * bhi.toNat + blo.toNat
  let s' := 4 * s + p
  let t := 4 * r + 1
  if t ≤ 4 * rem + p then (s', 2 * r + 1, 4 * rem + p - t) else (s', 2 * r, 4 * rem + p)

end SG
end Work.IntLib
