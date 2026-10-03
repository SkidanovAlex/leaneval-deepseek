/-
# The squarefree kernel of a natural number

`sqPart m` is the largest `t` with `t ^ 2 ∣ m` and `sqfreeKernel m = m / (sqPart m)^2` is the
squarefree kernel of `m`: the product of the primes occurring in `m` to an odd power.  Writing
`m = sqfreeKernel m * (sqPart m)^2`, the Jacobi-symbol character `(·|m)` agrees with the
squarefree-modulus character `(·|sqfreeKernel m)` on all integers coprime to `m` — this is the
reduction used in `Submission/Work/FIArea4/polya_vinogradov.lean` to pass from a general modulus
to a *primitive* Jacobi character.

Only the definitions live here; the properties are proved in the delegated files
`Submission/Work/FIArea4/sqfree_kernel.lean` and
`Submission/Work/FIArea4/jacobiSym_sqfreeKernel_of_coprime.lean`.
-/
import Mathlib

namespace Work.FIArea4

noncomputable section

/-- `sqPart m` is the largest `t` whose square divides `m`. -/
def sqPart (m : ℕ) : ℕ := Nat.findGreatest (fun t => t ^ 2 ∣ m) (Nat.sqrt m)

/-- The squarefree kernel of `m`: `m` divided by its largest square divisor. -/
def sqfreeKernel (m : ℕ) : ℕ := m / (sqPart m) ^ 2

end

end Work.FIArea4
