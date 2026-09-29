import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# The norm of an integral element of a finite field extension of `ℚ` is an integer

Let `L/ℚ` be a finite field extension.  If `δ : L` is integral over `ℤ`
(an algebraic integer), then its field-theoretic norm `Algebra.norm ℚ δ`
lies in `ℤ`.

## Proof

1. `Algebra.isIntegral_norm` shows that in the tower `ℤ → ℚ → L` the norm
   `Algebra.norm ℚ δ` is integral over `ℤ` (it is a product of conjugates
   of `δ`).
2. An element of `ℚ` integral over `ℤ` is an integer: this is the rational
   root theorem, packaged as `UniqueFactorizationMonoid.integer_of_integral`
   (applied to the UFD `ℤ` and its fraction field `ℚ`).
-/

namespace Commons.FieldTheory.Norm

/-- The norm of an algebraic integer in a finite extension of `ℚ` is an integer. -/
lemma norm_isInt {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    {δ : L} (hδint : IsIntegral ℤ δ) :
    ∃ d : ℤ, (d : ℚ) = Algebra.norm ℚ δ := by
  classical
  -- The norm of an element integral over `ℤ` is itself integral over `ℤ`
  -- (viewing `L` as a `ℤ`-algebra through the tower `ℤ → ℚ → L`).
  have hI : IsIntegral ℤ (Algebra.norm ℚ δ) :=
    Algebra.isIntegral_norm (K := ℚ) (R := ℤ) hδint
  -- Integral elements of the fraction field `ℚ` of the UFD `ℤ` are exactly
  -- the images of `ℤ` (rational root theorem).
  exact (UniqueFactorizationMonoid.integer_of_integral (A := ℤ) (K := ℚ) hI)

end Commons.FieldTheory.Norm