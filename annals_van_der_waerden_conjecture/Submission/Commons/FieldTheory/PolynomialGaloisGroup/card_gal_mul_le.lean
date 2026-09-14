import Mathlib.FieldTheory.PolynomialGaloisGroup

open Polynomial
set_option autoImplicit false

namespace Commons.FieldTheory.PolynomialGaloisGroup

/-- The Galois group of a product embeds into the product of the Galois groups,
so its cardinality is bounded by the product of the cardinalities. -/
theorem card_gal_mul_le {F : Type*} [Field F] (q r : F[X]) :
    Nat.card (q * r).Gal ≤ Nat.card q.Gal * Nat.card r.Gal := by
  calc
    Nat.card (q * r).Gal ≤ Nat.card (q.Gal × r.Gal) := by
      exact Nat.card_le_card_of_injective (Polynomial.Gal.restrictProd q r)
        (Polynomial.Gal.restrictProd_injective q r)
    _ = Nat.card q.Gal * Nat.card r.Gal := by
      simp

end Commons.FieldTheory.PolynomialGaloisGroup