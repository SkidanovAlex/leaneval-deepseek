import Mathlib
import Submission.Work.FIArea7.FIsymbols
import Submission.Work.FIArea4.sqfree_kernel

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The squarefree kernel of the odd part of `n`: `Kern n = sqfreeKernel (oddPart n)`. -/
def Kern (n : ℕ) : ℕ := Work.FIArea4.sqfreeKernel (Work.FIPlan.oddPart n)

/-- The number of `(a, b, s)` with `a ^ 2 + b ^ 2 = s ^ 2`, `1 ≤ s ≤ N`. -/
def R2 (N : ℕ) : ℕ :=
  ((((Finset.Icc (-(N : ℤ)) (N : ℤ)) ×ˢ (Finset.Icc (-(N : ℤ)) (N : ℤ))) ×ˢ
      (Finset.Icc 1 N)).filter
    (fun q => q.1.1 ^ 2 + q.1.2 ^ 2 = (q.2 : ℤ) ^ 2)).card

/-- The number of `w` in the box `gBox R` whose kernel is `d`. -/
def aCount (R : ℤ) (d : ℕ) : ℕ :=
  ((Work.FIPlan.gBox R).filter (fun w => Kern (Work.FIPlan.gnorm w) = d)).card

/-- The set of admissible kernels: squarefree numbers `≤ N₀²` all of whose prime factors are `≡ 1`
modulo `4`, where `N₀ = (2R+1).toNat`. -/
def Sset (R : ℤ) : Finset ℕ :=
  (Finset.range (((2 * R + 1).toNat) ^ 2 + 1)).filter
    (fun d => d ≠ 0 ∧ Squarefree d ∧ (∀ p ∈ d.primeFactors, p % 4 = 1))

end

end Work.FIArea7
