import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.FieldTheory.Discriminant.discr_powerBasis_eq_discr

namespace Commons.FieldTheory.Discriminant

open Polynomial in
/-- **Discriminant of the standard quadratic algebra**: for the field
`S = AdjoinRoot (X^2 + C b * X + C c)` over `ℚ`, the discriminant of the power basis
`{1, gen}` is `b^2 - 4*c`.

Proof: `Commons.FieldTheory.Discriminant.discr_powerBasis_eq_discr` reduces this to
`Polynomial.discr (minpoly ℚ pb.gen)`; `AdjoinRoot.minpoly_powerBasis_gen_of_monic` (using
`Polynomial.monic_X_pow_add`-style monicity of `X^2 + C b * X + C c`) identifies that
minimal polynomial with `X^2 + C b * X + C c`; then compute with
`Polynomial.discr_of_degree_eq_two`. -/
theorem discr_powerBasis_quadratic (b c : ℚ)
    [Fact (Irreducible (X ^ 2 + C b * X + C c : ℚ[X]))]
    (hf : (X ^ 2 + C b * X + C c : ℚ[X]) ≠ 0) :
    Algebra.discr ℚ (AdjoinRoot.powerBasis hf).basis = b ^ 2 - 4 * c := by
  -- Reduce the discriminant of the power basis to the discriminant of the minimal polynomial
  -- of the generator.  Separability is automatic over `ℚ`.
  rw [← Commons.FieldTheory.Discriminant.discr_powerBasis_eq_discr
        (F := ℚ) (S := AdjoinRoot (X ^ 2 + C b * X + C c : ℚ[X]))
        (pb := AdjoinRoot.powerBasis hf)]
  -- The minimal polynomial of the generator is `X ^ 2 + C b * X + C c`.
  have hmon : (X ^ 2 + C b * X + C c : ℚ[X]).Monic := by
    have h : (X ^ 2 + C b * X + C c : ℚ[X]) = X ^ 2 + (C b * X + C c) := by ring
    rw [h]; apply monic_X_pow_add; compute_degree!
  rw [AdjoinRoot.minpoly_powerBasis_gen_of_monic hmon hf]
  -- Now compute the discriminant of the quadratic polynomial.
  rw [Polynomial.discr_of_degree_eq_two
        (by compute_degree! : (X ^ 2 + C b * X + C c : ℚ[X]).degree = 2)]
  simp [coeff_add, coeff_X_pow, coeff_X, coeff_C]

end Commons.FieldTheory.Discriminant