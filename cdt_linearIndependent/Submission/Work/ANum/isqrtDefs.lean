import Mathlib

/-! # Area ANum — a kernel-reducible integer square root

**Why this module exists.**  The certificate of Theorem A evaluates interval enclosures of the
contour map `psiA` inside the *kernel* (via `decide`/`rfl` on the computable definitions).  The
`Iv.sqrt`/`CD.sqrt` operations of the interval library use `Nat.sqrt`, and Lean's `Nat.sqrt` is
`Nat.sqrt.iter` (a well-founded Newton iteration) — the kernel's reduction gets **stuck** on
`Nat.sqrt n` for a literal `n` (measured: `example : Nat.sqrt 1152921504606846976 = 1073741824 := by
decide` fails with "reduction got stuck").  Hence no certificate definition depending on `Nat.sqrt`
can be evaluated by the kernel, and the whole `Submission/Work/ANum` certificate architecture is
dead unless `Nat.sqrt` is replaced by a *structurally recursive* (hence kernel-reducible)
integer square root.

`isqAux` below is the base-4 digit-pair recursion (`r = ⌊√(n/4)⌋`, then `2r` or `2r+1`), which is
structural on its *fuel* argument, so the kernel reduces it in `fuel` steps.  `isqrt` wraps it for
`n < 4^64 = 2^128` (the regime of the certificate: every mantissa `I.lo * SC` occurring there is
below `2^128`, since the interval values stay below `10^30`) and falls back to `Nat.sqrt` outside,
so that `isqrt n = Nat.sqrt n` holds for **every** `n` (no side condition needed anywhere). -/

namespace Work.ANum

/-- Base-4 digit-pair integer square root, driven by an explicit fuel.

`isqAux k n = ⌊√n⌋` whenever `n < 4^k` (proved in the sibling module `isqrt_eq_sqrt`); for larger `n`
it is some lower bound.  The recursion is structural on `k`, so the kernel can evaluate it. -/
def isqAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | (k + 1), n =>
      if n < 4 then (if n < 2 then n else 1)
      else
        let r := isqAux k (n / 4)
        if (2 * r + 1) * (2 * r + 1) ≤ n then 2 * r + 1 else 2 * r

/-- `⌊√n⌋`, computed by the kernel-reducible `isqAux` in the range `n < 2^128` and by `Nat.sqrt`
outside it.  By construction `isqrt n = Nat.sqrt n` for all `n`. -/
def isqrt (n : ℕ) : ℕ :=
  if n < 340282366920938463463374607431768211456 then isqAux 64 n else Nat.sqrt n

/-- The `isqrt` of a literal below `2^128` is the digit-pair recursion (definitional). -/
theorem isqrt_of_lt {n : ℕ} (h : n < 340282366920938463463374607431768211456) :
    isqrt n = isqAux 64 n := if_pos h

end Work.ANum
