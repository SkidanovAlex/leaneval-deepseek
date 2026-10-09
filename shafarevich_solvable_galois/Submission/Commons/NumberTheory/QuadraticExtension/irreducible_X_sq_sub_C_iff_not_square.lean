import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Tactic.NormNum.Prime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.QuadraticExtension

theorem irreducible_X_sq_sub_C_iff_not_square
    {K : Type*} [Field K] [CharZero K] {a : K} (ha : a ≠ 0) :
    Irreducible (Polynomial.X ^ 2 - Polynomial.C a) ↔ ∀ b : K, b ^ 2 ≠ a := by
  have _ : a ≠ 0 := ha
  simpa using (X_pow_sub_C_irreducible_iff_of_prime (K := K) (p := 2) (by norm_num) (a := a))

end Commons.NumberTheory.QuadraticExtension