import Mathlib.NumberTheory.NumberField.Basic
import Submission.Commons.FieldTheory.Discriminant.discr_powerBasis_quadratic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.FieldTheory.Discriminant

open Polynomial in
/-- **Discriminant of the power basis of `ℚ(√a)`**: for `S = AdjoinRoot (X^2 - C a)` over `ℚ`,
the discriminant of the power basis `{1, gen}` is `4 * a`.

This is `Commons.FieldTheory.Discriminant.discr_powerBasis_quadratic` with `b = 0`, `c = -a`
(the identity `X ^ 2 + C 0 * X + C (-a) = X ^ 2 - C a` and `0 ^ 2 - 4 * (-a) = 4 * a` are
`ring` identities; either apply that result after rewriting, or redo its proof directly with
`Commons.FieldTheory.Discriminant.discr_powerBasis_eq_discr`,
`AdjoinRoot.minpoly_powerBasis_gen_of_monic` and the resultant formula). -/
theorem discr_powerBasis_X_sq_sub_C (a : ℚ)
    [Fact (Irreducible (X ^ 2 - C a : ℚ[X]))]
    (hf : (X ^ 2 - C a : ℚ[X]) ≠ 0) :
    Algebra.discr ℚ (AdjoinRoot.powerBasis hf).basis = 4 * a := by
  rw [← Commons.FieldTheory.Discriminant.discr_powerBasis_eq_discr
        (F := ℚ) (S := AdjoinRoot (X ^ 2 - C a : ℚ[X]))
        (pb := AdjoinRoot.powerBasis hf)]
  have hmon : (X ^ 2 - C a : ℚ[X]).Monic := monic_X_pow_sub_C a (by norm_num)
  rw [AdjoinRoot.minpoly_powerBasis_gen_of_monic hmon hf]
  rw [Polynomial.discr_of_degree_eq_two
        (by compute_degree! : (X ^ 2 - C a : ℚ[X]).degree = 2)]
  simp [coeff_X_pow, coeff_C]

end Commons.FieldTheory.Discriminant