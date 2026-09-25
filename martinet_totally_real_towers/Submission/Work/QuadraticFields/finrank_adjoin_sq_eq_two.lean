import Mathlib
import Submission.Work.QuadraticFields.MultiquadraticInside

/-!
# The degree of `ℚ(x)` for `x ^ 2 = a`, `a` a non-square in `ℚ`

Let `M` be a field equipped with a `ℚ`-algebra structure, let `a : ℚ` and `x : M` with
`x ^ 2 = a` (more precisely `x ^ 2 = algebraMap ℚ M a`).  If `a` is not a square in `ℚ`, then
`x` generates a quadratic extension:  `[ℚ(x) : ℚ] = 2`.

This is the abstract-field version of `Work.QuadraticFields.quadField_finrank` (which treats the
special case `M = AlgebraicClosure ℚ`): the element `x` is integral over `ℚ` with
`minpoly ℚ x = X ^ 2 - C a`, and `X ^ 2 - C a` is irreducible over `ℚ` because `a` is not a
square, so `IntermediateField.adjoin.finrank` gives the degree `2`.

Note that the hypothesis `∀ r : ℚ, r ^ 2 ≠ a` forces `a ≠ 0`, hence also `x ≠ 0`.
-/

namespace Work.QuadraticFields

/-- If `x ^ 2 = a` for a rational number `a` which is not a square in `ℚ`, then the subextension
`ℚ(x)` is quadratic over `ℚ`. -/
theorem finrank_adjoin_sq_eq_two {M : Type*} [Field M] [Algebra ℚ M] (a : ℚ) (x : M)
    (hx : x ^ 2 = algebraMap ℚ M a) (ha : ∀ r : ℚ, r ^ 2 ≠ a) :
    Module.finrank ℚ ↥(IntermediateField.adjoin ℚ ({x} : Set M)) = 2 := by
  -- `x` is integral over `ℚ`: it satisfies the monic equation `X ^ 2 - a`.
  have hint : IsIntegral ℚ x := by
    apply IsIntegral.of_pow (R := ℚ) (B := M) (n := 2) (by norm_num)
    rw [hx]
    exact isIntegral_algebraMap
  -- `X ^ 2 - a` is irreducible over `ℚ` because `a` is not a square in `ℚ`.
  have hIrr : Irreducible (Polynomial.X ^ 2 - Polynomial.C a : Polynomial ℚ) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two ha
  -- `x` is a root of `X ^ 2 - a`.
  have hroot : (Polynomial.aeval x) (Polynomial.X ^ 2 - Polynomial.C a : Polynomial ℚ) = 0 := by
    simp [hx]
  -- hence `X ^ 2 - a` is its minimal polynomial.
  have hmin : minpoly ℚ x = Polynomial.X ^ 2 - Polynomial.C a :=
    (minpoly.eq_of_irreducible_of_monic hIrr hroot
      (Polynomial.monic_X_pow_sub_C a (by norm_num))).symm
  rw [IntermediateField.adjoin.finrank hint, hmin, Polynomial.natDegree_X_pow_sub_C]

end Work.QuadraticFields
