import Mathlib
import Submission.CDT.ElimOperator

/-!
# From the paper's system to the eliminated operator

The paper's system for `b0,b1,b2,b3` is
```
b3' + b2 - (c3/c4) b3 = 0,   b2' + b1 - (c2/c4) b3 = 0,
b1' + b0 - (c1/c4) b3 = 0,   b0'      - (c0/c4) b3 = R
```
(where `R = a0 + a_{-1}/y + a_{-2}/y^2`).  Here we show that such a quadruple
satisfies the *eliminated* equation

`∑_{j=0}^{4} Q_j b3^{(j)} = R`,  `Q_4 = -1`,  `Q_j = 2 P_j / D1^(4-j)` (`j ≤ 3`),

and its cleared form

`∑_{j} A_j b3^{(j)} = D1^4 · R`,  `A_j = 2 P_j D1^j` (`j ≤ 3`),  `A_4 = -D1^4`.
-/

open Classical

noncomputable section

namespace Submission.CDT

open Polynomial

namespace ElimOp

open Submission.CDT.Elim14

/-- **The system implies the eliminated operator equation.** -/
theorem elim_from_system (b0 b1 b2 b3 R : RF)
    (h1 : dRat b3 + b2 - Ww * b3 = 0)
    (h2 : dRat b2 + b1 - Vv * b3 = 0)
    (h3 : dRat b1 + b0 - Uu * b3 = 0)
    (h4 : dRat b0 - Zz * b3 = R) :
    dRat (Uu * b3) - dRat (dRat (Vv * b3)) + dRat (dRat (dRat (Ww * b3)))
        - dRat (dRat (dRat (dRat b3))) - Zz * b3 = R := by
  have e2 : b2 = Ww * b3 - dRat b3 := by linear_combination h1
  have e1 : b1 = Vv * b3 - dRat b2 := by linear_combination h2
  have e0 : b0 = Uu * b3 - dRat b1 := by linear_combination h3
  have eR : dRat b0 = Zz * b3 + R := by linear_combination h4
  have key : dRat (Uu * b3) - dRat (dRat (Vv * b3)) + dRat (dRat (dRat (Ww * b3)))
      - dRat (dRat (dRat (dRat b3))) = dRat b0 := by
    rw [e0, e1, e2]
    simp only [dRat_sub]
    ring
  rw [key, eR]
  ring

/-- **The eliminated equation** `∑_j Q_j b3^{(j)} = R`. -/
theorem elim_equation (b0 b1 b2 b3 R : RF)
    (h1 : dRat b3 + b2 - Ww * b3 = 0)
    (h2 : dRat b2 + b1 - Vv * b3 = 0)
    (h3 : dRat b1 + b0 - Uu * b3 = 0)
    (h4 : dRat b0 - Zz * b3 = R) :
    (am (2 * P0) / am (D1 ^ 4)) * b3 + (am (2 * P1) / am (D1 ^ 3)) * dRat b3
        + (am (2 * P2) / am (D1 ^ 2)) * dRat (dRat b3)
        + (am (2 * P3) / am D1) * dRat (dRat (dRat b3))
        - dRat (dRat (dRat (dRat b3))) = R := by
  rw [← elim_operator b3]
  exact elim_from_system b0 b1 b2 b3 R h1 h2 h3 h4

/-- The cleared form of the eliminated equation, with polynomial coefficients. -/
theorem elim_equation_cleared (b0 b1 b2 b3 R : RF)
    (h1 : dRat b3 + b2 - Ww * b3 = 0)
    (h2 : dRat b2 + b1 - Vv * b3 = 0)
    (h3 : dRat b1 + b0 - Uu * b3 = 0)
    (h4 : dRat b0 - Zz * b3 = R) :
    am (2 * P0) * b3 + am (2 * P1 * D1) * dRat b3
        + am (2 * P2 * D1 ^ 2) * dRat (dRat b3)
        + am (2 * P3 * D1 ^ 3) * dRat (dRat (dRat b3))
        - am (D1 ^ 4) * dRat (dRat (dRat (dRat b3)))
      = am (D1 ^ 4) * R := by
  have h := elim_equation b0 b1 b2 b3 R h1 h2 h3 h4
  have hD : (am D1 : RF) ≠ 0 := RatFunc.algebraMap_ne_zero D1_ne_zero
  have key : am (D1 ^ 4) * ((am (2 * P0) / am (D1 ^ 4)) * b3
        + (am (2 * P1) / am (D1 ^ 3)) * dRat b3
        + (am (2 * P2) / am (D1 ^ 2)) * dRat (dRat b3)
        + (am (2 * P3) / am D1) * dRat (dRat (dRat b3))
        - dRat (dRat (dRat (dRat b3))))
      = am (2 * P0) * b3 + am (2 * P1 * D1) * dRat b3 + am (2 * P2 * D1 ^ 2) * dRat (dRat b3)
        + am (2 * P3 * D1 ^ 3) * dRat (dRat (dRat b3))
        - am (D1 ^ 4) * dRat (dRat (dRat (dRat b3))) := by
    rw [mul_sub, mul_add, mul_add, mul_add]
    simp only [map_mul, map_pow]
    field_simp <;> ring
  have h2 := congrArg (fun x : RF => am (D1 ^ 4) * x) h
  rw [key] at h2
  exact h2

end ElimOp

end Submission.CDT
