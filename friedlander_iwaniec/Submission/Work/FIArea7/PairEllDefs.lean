import Mathlib
import Submission.Work.FIArea7.Classical172Defs

/-!
# `Work.FIArea7.PairEllDefs`

The two summands of *FI* (25.4): the pair `(c, ℓ)` summand `pairTerm`, and the summand of the
hyperbola (Type II) form `pairTermH` used by the `PairEllAux` machinery (`hyperbolaBlockLeGen`,
`hyperbolaStarEps`, `smoothStarEps`).

`pairTermH` is exactly the summand of `Work.FIArea7.PairEllAux.smoothStarEps` with the parameter
`c₀` kept, so that the two can be identified definitionally.
-/

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The summand of *FI* (25.4) for the pair `(c, ℓ)`: `α_c β_ℓ P(cℓ) λ(cℓ)` on coprime pairs. -/
def pairTerm (chi : GaussianInt → ℂ) (k : ℤ) (al be : ℕ → ℂ) (P : ℝ → ℝ) (c ℓ : ℕ) : ℂ :=
  if Nat.Coprime c ℓ then al c * be ℓ * ((P ((c : ℝ) * (ℓ : ℝ)) : ℝ) : ℂ)
    * quadEigen (grossenChar chi k) (c * ℓ) else 0

/-- The summand of the hyperbola (Type II) form of (25.4): the restriction `m n ≤ U` is imposed and
the weight is read as `P (c₀ (m n))`.  This is the summand of
`Work.FIArea7.PairEllAux.smoothStarEps`. -/
def pairTermH (chi : GaussianInt → ℂ) (k : ℤ) (α β : ℕ → ℂ) (P : ℝ → ℝ) (c0 U : ℕ)
    (m n : ℕ) : ℂ :=
  if m * n ≤ U then (if Nat.Coprime m n then α m * β n
    * ((P ((c0 : ℝ) * ((m * n : ℕ) : ℝ)) : ℝ) : ℂ)
    * quadEigen (grossenChar chi k) (c0 * (m * n)) else 0) else 0

end

end Work.FIArea7
