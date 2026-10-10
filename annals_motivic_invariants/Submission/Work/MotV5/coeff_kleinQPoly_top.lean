import Mathlib
import Submission.Work.MotV5.WtDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The top coefficient of the Klein polynomial

`kleinQPoly a b P = -ab P(T)² + a² P(T+2)P(T+3) - b² P(T+1)P(T+4)` is a sum of three products
each of which has degree `2 • P.natDegree`.  At the top index `2 * P.natDegree` every one of the
three products contributes exactly `(P.coeff P.natDegree)²`, whence the top coefficient of the
Klein polynomial is `(a² - ab - b²) · (P.coeff P.natDegree)²`.

The two auxiliary lemmas below isolate the two ingredients: the top coefficient of `P * P`, and
the top coefficient of `P(T+k) * P(T+l)` for arbitrary constants `k l` (note that
`P(T+k) = P.taylor k`, and `Polynomial.natDegree_taylor`/`coeff_taylor_natDegree` hold over an
arbitrary semiring, so no `NoZeroDivisors` assumption is needed).  Both are consequences of
`Polynomial.coeff_mul_add_eq_of_natDegree_le`.
-/

set_option autoImplicit false

namespace Work.MotV5

open Polynomial

/-- The top coefficient of `P * P` (equivalently of `P ^ 2`). -/
theorem coeff_sq_top {F : Type*} [CommRing F] (P : Polynomial F) :
    (P ^ 2).coeff (2 * P.natDegree) = (P.coeff P.natDegree) ^ 2 := by
  have h : 2 * P.natDegree = P.natDegree + P.natDegree := by ring
  rw [pow_two, h, coeff_mul_add_eq_of_natDegree_le le_rfl le_rfl, sq]

/-- The top coefficient of `P(T+k) * P(T+l)` is `(P.coeff P.natDegree)²` for arbitrary
constants `k`, `l`. -/
theorem coeff_comp_mul_top {F : Type*} [CommRing F] (k l : F) (P : Polynomial F) :
    (P.comp (X + C k) * P.comp (X + C l)).coeff (2 * P.natDegree)
      = (P.coeff P.natDegree) ^ 2 := by
  rw [← taylor_apply k P, ← taylor_apply l P]
  have h : 2 * P.natDegree = (taylor k P).natDegree + (taylor l P).natDegree := by
    rw [natDegree_taylor, natDegree_taylor]; ring
  rw [h, coeff_mul_add_eq_of_natDegree_le le_rfl le_rfl, natDegree_taylor, natDegree_taylor,
    coeff_taylor_natDegree, coeff_taylor_natDegree, sq, ← coeff_natDegree]

theorem coeff_kleinQPoly_top {F : Type*} [CommRing F] [CharP F 5] (a b : F)
    {P : Polynomial F} (hP : P ≠ 0) (hdeg : P.natDegree ≤ 4) :
    (kleinQPoly a b P).coeff (2 * P.natDegree)
      = (a ^ 2 - a * b - b ^ 2) * (P.coeff P.natDegree) ^ 2 := by
  have h1 := coeff_sq_top P
  have h2 := coeff_comp_mul_top (2 : F) (3 : F) P
  have h3 := coeff_comp_mul_top (1 : F) (4 : F) P
  have hK : kleinQPoly a b P
      = C (-(a * b)) * P ^ 2
        + C (a ^ 2) * (P.comp (X + C 2) * P.comp (X + C 3))
        - C (b ^ 2) * (P.comp (X + C 1) * P.comp (X + C 4)) := by
    simp only [kleinQPoly, C_neg]
    first | refl_ring1 | ring
  rw [hK, coeff_sub, coeff_add, coeff_C_mul, coeff_C_mul, coeff_C_mul, h1, h2, h3]
  first | refl_ring1 | ring

end Work.MotV5
