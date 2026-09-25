import Mathlib
import Submission.Work.QuadraticFields.QuadField

namespace Work.QuadraticFields

/-- The quadratic field `ℚ(√a)` attached to a rational number `a` which is not a square in `ℚ`
has degree `2` over `ℚ`. This is because `sqrtVal a` is a root of the irreducible polynomial
`X ^ 2 - a`, so that its minimal polynomial has degree `2`, and `ℚ(√a) = ℚ⟮sqrtVal a⟯`. -/
theorem quadField_finrank (a : ℚ) (ha : ∀ r : ℚ, r ^ 2 ≠ a) :
    Module.finrank ℚ ↥(quadField a) = 2 := by
  -- `sqrtVal a` is integral over `ℚ`: it satisfies the monic equation `X ^ 2 - a`.
  have hint : IsIntegral ℚ (sqrtVal a) := by
    apply IsIntegral.of_pow (R := ℚ) (B := AlgebraicClosure ℚ) (n := 2) (by norm_num)
    rw [sqrtVal_sq]
    exact isIntegral_algebraMap
  -- `X ^ 2 - a` is irreducible over `ℚ` because `a` is not a square in `ℚ`.
  have hIrr : Irreducible (Polynomial.X ^ 2 - Polynomial.C a : Polynomial ℚ) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two ha
  -- `sqrtVal a` is a root of `X ^ 2 - a`.
  have hroot : (Polynomial.aeval (sqrtVal a)) (Polynomial.X ^ 2 - Polynomial.C a : Polynomial ℚ)
      = 0 := by
    simp [sqrtVal_sq]
  -- hence `X ^ 2 - a` is its minimal polynomial.
  have hmin : minpoly ℚ (sqrtVal a) = Polynomial.X ^ 2 - Polynomial.C a :=
    (minpoly.eq_of_irreducible_of_monic hIrr hroot
      (Polynomial.monic_X_pow_sub_C a (by norm_num))).symm
  rw [quadField, IntermediateField.adjoin.finrank hint, hmin,
    Polynomial.natDegree_X_pow_sub_C]

end Work.QuadraticFields
