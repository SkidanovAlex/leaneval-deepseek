import Mathlib
import Submission.Work.HilbertSymbol.Basic
import Submission.Work.HilbertSymbol.epsZ_mul
import Submission.Work.HilbertSymbol.omegaZ_mul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-!
# `(a, b²)_2 = 1`

We show that the `2`-adic Hilbert symbol of `Submission.Work.HilbertSymbol.Basic` is trivial on
squares in the second argument.  The proof only needs the multiplicativity of the characters
`epsZ` and `omegaZ` (files `epsZ_mul` and `omegaZ_mul`) together with the multiplicativity of
`unitPart` and of the `2`-adic valuation.

Writing `S` for the `ZMod 2`-valued exponent appearing in the definition of `hilbertSymbolTwo`,
we have

* `v₂(b²) = 2 v₂(b)`, hence `v₂(b²) ≡ 0 (mod 2)`,
* `unitPart 2 (b²) = (unitPart 2 b)²`, hence `epsZ (unitPart 2 (b²)) = 2 · epsZ (unitPart 2 b) = 0`
  and likewise for `omegaZ`.

Thus `S = 0`, and `signOf 0 = 1`.
-/

theorem hilbertSymbolTwo_sq_right (a b : ℚˣ) : hilbertSymbolTwo a (b ^ 2) = 1 := by
  have hsq : unitPart 2 (b ^ 2) = unitPart 2 b ^ 2 := by
    rw [sq, unitPart_mul, sq]
  have hval : (padicVal 2 (b ^ 2) : ZMod 2) = 0 := by
    rw [sq, padicVal_mul]
    push_cast
    exact CharTwo.add_self_eq_zero _
  have heps : epsZ (unitPart 2 (b ^ 2)) = 0 := by
    rw [hsq, sq, epsZ_mul]
    exact CharTwo.add_self_eq_zero _
  have homega : omegaZ (unitPart 2 (b ^ 2)) = 0 := by
    rw [hsq, sq, omegaZ_mul]
    exact CharTwo.add_self_eq_zero _
  rw [hilbertSymbolTwo, hval, heps, homega]
  simp

end Work.HilbertSymbol
