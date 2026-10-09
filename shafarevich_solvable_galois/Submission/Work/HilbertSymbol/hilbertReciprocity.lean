/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hilbert reciprocity over `ℚ`

The product of the Hilbert symbols `(a,b)_v` over all places `v` of `ℚ` equals `1`
(Hilbert's product formula / the reciprocity law for the Hilbert symbol over `ℚ`).

The reduction is the classical one:

* every nonzero rational is a nonzero integer times a square (`exists_intUnit_mul_sq`),
  so by bilinearity of the place product (`placeProduct_mul_left`, `placeProduct_mul_right`)
  and triviality on squares (`placeProduct_sq_left`, `placeProduct_sq_right`) it suffices to
  treat the case of two nonzero *integers*;
* for two nonzero integers the statement is `placeProduct_intUnit`, proved from the product
  formula for pairs of primes (quadratic reciprocity plus the supplementary laws) by strong
  induction on the absolute value.
-/
import Mathlib
import Submission.Work.HilbertSymbol.Places
import Submission.Work.HilbertSymbol.Symbol
import Submission.Work.HilbertSymbol.placeProduct_mul_left
import Submission.Work.HilbertSymbol.placeProduct_mul_right
import Submission.Work.HilbertSymbol.placeProduct_sq_left
import Submission.Work.HilbertSymbol.placeProduct_sq_right
import Submission.Work.HilbertSymbol.placeProduct_intUnit
import Submission.Work.HilbertSymbol.exists_intUnit_mul_sq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped Classical

namespace Work.HilbertSymbol

/-- A square factor can be removed from either argument of the place product. -/
theorem placeProduct_mul_sq (x y c d : ℚˣ) :
    placeProduct (x * c ^ 2) (y * d ^ 2) = placeProduct x y := by
  rw [placeProduct_mul_left, placeProduct_mul_right, placeProduct_mul_right]
  simp [placeProduct_sq_left, placeProduct_sq_right]

/-- **Hilbert reciprocity over `ℚ`.**  The product of the Hilbert symbols `(a,b)_v` over all
places `v` of `ℚ` equals `1`. -/
theorem hilbertReciprocity (a b : ℚˣ) : placeProduct a b = 1 := by
  obtain ⟨A, hA, c, rfl⟩ := exists_intUnit_mul_sq a
  obtain ⟨B, hB, d, rfl⟩ := exists_intUnit_mul_sq b
  rw [placeProduct_mul_sq (intUnit A hA) (intUnit B hB) c d,
    placeProduct_intUnit A B hA hB]

end Work.HilbertSymbol
