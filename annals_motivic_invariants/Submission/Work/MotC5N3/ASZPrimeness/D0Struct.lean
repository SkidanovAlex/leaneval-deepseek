import Mathlib
import Submission.Work.MotAS.ASZGC.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC5N3.ASZPrimeness

theorem D0Struct (K : Type) [Field K] [CharP K 5] (a b g : K) :
    Work.MotAS.ASZGC.D0 a b g =
      MvPolynomial.C (g * (a + 2 * b) ^ 6) * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) * MvPolynomial.X 1
        + MvPolynomial.C (2 * b ^ 6 + a * b ^ 5 + a ^ 5 * b + 3 * a ^ 6)
        + MvPolynomial.C (4 * b ^ 6 + 3 * a * b ^ 5 + 2 * a ^ 5 * b + 4 * a ^ 6) * MvPolynomial.X 0
        + MvPolynomial.C (a * b ^ 5 + 2 * a ^ 2 * b ^ 4 + 4 * a ^ 3 * b ^ 3 + 3 * a ^ 4 * b ^ 2 + a ^ 5 * b)
            * (MvPolynomial.X 0) ^ 2 := by
  -- In characteristic 5 the Frobenius identity gives `(a + 2b)^6 = a^6 + 2a^5 b + 2ab^5 + 4b^6`.
  have hchar : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h6 : (a + 2 * b) ^ 6 = a ^ 6 + 2 * a ^ 5 * b + 2 * a * b ^ 5 + 4 * b ^ 6 := by
    have h : (a + 2 * b) ^ 6
        = a ^ 6 + 2 * a ^ 5 * b + 2 * a * b ^ 5 + 4 * b ^ 6
          + 5 * (2 * a ^ 5 * b + 12 * a ^ 4 * b ^ 2 + 32 * a ^ 3 * b ^ 3
              + 48 * a ^ 2 * b ^ 4 + 38 * a * b ^ 5 + 12 * b ^ 6) := by ring
    rw [h, hchar]; ring
  rw [h6]
  unfold Work.MotAS.ASZGC.D0
  simp only [MvPolynomial.C_eq_algebraMap, map_mul, map_add, map_pow, map_ofNat]
  ring_nf

end Work.MotC5N3.ASZPrimeness
