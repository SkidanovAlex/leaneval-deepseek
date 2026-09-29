import Mathlib
import Submission.CDT.EliminationData
import Submission.CDT.RatFuncDeriv

/-!
# The eliminated operator of CDT Lemma `14functions`

The second half of the paper's Lemma `14functions` eliminates `b0,b1,b2` from the
system
```
b3' + b2 - (c3/c4) b3 = 0,   b2' + b1 - (c2/c4) b3 = 0,
b1' + b0 - (c1/c4) b3 = 0,   b0'      - (c0/c4) b3 = R
```
and obtains `∑_{j=0}^4 Q_j b3^{(j)} = R` with `Q_4 = -1` and
`Q_j = 2 P_j / D1^(4-j)` for `j ≤ 3`.

Concretely: if `b3` satisfies the system, then
`D[(c1/c4) b3] - D^2[(c2/c4) b3] + D^3[(c3/c4) b3] - (c0/c4) b3 - b3'''' = R`.

This module proves the corresponding operator identity for an arbitrary `f`:

`D[u f] - D^2[v f] + D^3[w f] - D^4 f - z f
   = (2P0/D1^4) f + (2P1/D1^3) f' + (2P2/D1^2) f'' + (2P3/D1) f''' - f''''`

(with `u = c1/c4`, `v = c2/c4`, `w = c3/c4`, `z = c0/c4`).  The proof expands the
derivatives by Leibniz, clears denominators and reduces to the four polynomial
identities of `Submission.CDT.Elim14`.

Everything is fully proved (no `sorry`, no extra axioms).
-/

open Classical

noncomputable section

namespace Submission.CDT

open Polynomial

namespace ElimOp

open Submission.CDT.Elim14

abbrev RF : Type := RatFunc ℚ
abbrev am (p : Polynomial ℚ) : RF := algebraMap (Polynomial ℚ) (RatFunc ℚ) p

macro "dunwrap" : tactic => `(tactic|
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_X, Polynomial.derivative_C, Polynomial.derivative_natCast,
    Polynomial.derivative_intCast, Polynomial.derivative_one, Polynomial.derivative_zero,
    mul_one, mul_zero, Polynomial.C_eq_natCast, Polynomial.C_eq_intCast])

lemma c4_ne_zero : c4 ≠ 0 := by
  intro h
  have := congrArg (fun p : Polynomial ℚ => Polynomial.eval 1 p) h
  simp [c4, y] at this
  norm_num at this

lemma D1_ne_zero : D1 ≠ 0 := by
  intro h
  have := congrArg (fun p : Polynomial ℚ => Polynomial.eval 1 p) h
  simp [D1, y] at this
  norm_num at this

lemma c1_derivative : c1.derivative = c1d := by unfold c1 c1d y; dunwrap; ring
lemma c2_derivative : c2.derivative = c2d := by unfold c2 c2d y; dunwrap; ring
lemma c2d_derivative : c2d.derivative = c2dd := by unfold c2d c2dd y; dunwrap; ring
lemma c3_derivative : c3.derivative = c3d := by unfold c3 c3d y; dunwrap; ring
lemma c3d_derivative : c3d.derivative = c3dd := by unfold c3d c3dd y; dunwrap; ring
lemma c3dd_derivative : c3dd.derivative = c3ddd := by unfold c3dd c3ddd y; dunwrap; ring
lemma c4_derivative : c4.derivative = c4d := by unfold c4 c4d y; dunwrap; ring
lemma c4d_derivative : c4d.derivative = c4dd := by unfold c4d c4dd y; dunwrap; ring
lemma c4dd_derivative : c4dd.derivative = c4ddd := by unfold c4dd c4ddd y; dunwrap; ring

/-- Derivative of `am p / am q`. -/
lemma dRat_am_div (p q : Polynomial ℚ) :
    dRat (am p / am q) = am (p.derivative * q - p * q.derivative) / am (q ^ 2) := by
  rw [dRat_div, ← map_pow]

/-- Derivative of `am p / am (q^2)`. -/
lemma dRat_am_div_sq (p q : Polynomial ℚ) :
    dRat (am p / am (q ^ 2))
      = am (p.derivative * q ^ 2 - p * (2 * q * q.derivative)) / am (q ^ 4) := by
  rw [dRat_div, Polynomial.derivative_pow, ← map_pow]
  simp only [Polynomial.C_eq_natCast, Nat.reduceSub, pow_one]
  congr 1
  ring

def Uu : RF := am c1 / am c4
def Vv : RF := am c2 / am c4
def Ww : RF := am c3 / am c4
def Zz : RF := am c0 / am c4

lemma dRat_Ww : dRat Ww = am (c3d * c4 - c3 * c4d) / am (c4 ^ 2) := by
  rw [show Ww = am c3 / am c4 from rfl, dRat_am_div, c3_derivative, c4_derivative]
lemma dRat_Vv : dRat Vv = am (c2d * c4 - c2 * c4d) / am (c4 ^ 2) := by
  rw [show Vv = am c2 / am c4 from rfl, dRat_am_div, c2_derivative, c4_derivative]
lemma dRat_Uu : dRat Uu = am (c1d * c4 - c1 * c4d) / am (c4 ^ 2) := by
  rw [show Uu = am c1 / am c4 from rfl, dRat_am_div, c1_derivative, c4_derivative]

abbrev P1Nu : Polynomial ℚ := (c3d * c4 - c3 * c4d).derivative * c4 ^ 2
  - (c3d * c4 - c3 * c4d) * (2 * c4 * c4.derivative)

lemma dRat2_Ww : dRat (dRat Ww) = am P1Nu / am (c4 ^ 4) := by
  show dRat (dRat Ww) = _
  rw [dRat_Ww, dRat_am_div_sq]

abbrev P1Nv : Polynomial ℚ := (c2d * c4 - c2 * c4d).derivative * c4 ^ 2
  - (c2d * c4 - c2 * c4d) * (2 * c4 * c4.derivative)

lemma dRat2_Vv : dRat (dRat Vv) = am P1Nv / am (c4 ^ 4) := by
  show dRat (dRat Vv) = _
  rw [dRat_Vv, dRat_am_div_sq]

abbrev P2Nu : Polynomial ℚ := P1Nu.derivative * c4 ^ 4 - P1Nu * (c4 ^ 4).derivative

lemma dRat3_Ww : dRat (dRat (dRat Ww)) = am P2Nu / am ((c4 ^ 4) ^ 2) := by
  show dRat (dRat (dRat Ww)) = _
  rw [dRat2_Ww, dRat_am_div]

macro "toPoly" : tactic => `(tactic| (
  first
    | rw [show (2 : RF) = am (2 : Polynomial ℚ) from (map_ofNat _ 2).symm]
    | skip
  first
    | rw [show (3 : RF) = am (3 : Polynomial ℚ) from (map_ofNat _ 3).symm]
    | skip
  first
    | rw [show (4 : RF) = am (4 : Polynomial ℚ) from (map_ofNat _ 4).symm]
    | skip
  simp only [← map_mul, ← map_pow, ← map_sub, ← map_add, ← map_neg]))

/-! ## The four coefficient identities -/

lemma coeff_three : Ww = am (2 * P3) / am D1 := by
  have h4 : am c4 ≠ 0 := RatFunc.algebraMap_ne_zero c4_ne_zero
  have hD : am D1 ≠ 0 := RatFunc.algebraMap_ne_zero D1_ne_zero
  rw [show Ww = am c3 / am c4 from rfl, div_eq_div_iff h4 hD]
  simp only [← map_mul]
  refine congrArg (algebraMap (Polynomial ℚ) (RatFunc ℚ)) ?_
  linear_combination (-1) * coeff_ident_three

lemma coeff_two : 3 * dRat Ww - Vv = am (2 * P2) / am (D1 ^ 2) := by
  have h4 : am c4 ≠ 0 := RatFunc.algebraMap_ne_zero c4_ne_zero
  have hD : am D1 ≠ 0 := RatFunc.algebraMap_ne_zero D1_ne_zero
  rw [show Ww = am c3 / am c4 from rfl, show Vv = am c2 / am c4 from rfl, dRat_div,
    c3_derivative, c4_derivative]
  simp only [map_mul, map_sub, map_pow]
  field_simp
  ring_nf
  toPoly
  refine congrArg (algebraMap (Polynomial ℚ) (RatFunc ℚ)) ?_
  linear_combination (coeff_ident_two)

lemma coeff_one : 3 * dRat (dRat Ww) - 2 * dRat Vv + Uu = am (2 * P1) / am (D1 ^ 3) := by
  have h4 : am c4 ≠ 0 := RatFunc.algebraMap_ne_zero c4_ne_zero
  have hD : am D1 ≠ 0 := RatFunc.algebraMap_ne_zero D1_ne_zero
  rw [dRat2_Ww, dRat_Vv, show Uu = am c1 / am c4 from rfl]
  simp only [P1Nu, P1Nv, Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_pow,
    c1_derivative, c2_derivative, c2d_derivative, c3_derivative, c3d_derivative,
    c4_derivative, c4d_derivative, Nat.reduceSub, pow_one, map_mul, map_sub, map_add, map_pow]
  field_simp
  ring_nf
  toPoly
  refine congrArg (algebraMap (Polynomial ℚ) (RatFunc ℚ)) ?_
  linear_combination (coeff_ident_one)

lemma coeff_zero : dRat (dRat (dRat Ww)) - dRat (dRat Vv) + dRat Uu - Zz
    = am (2 * P0) / am (D1 ^ 4) := by
  have h4 : am c4 ≠ 0 := RatFunc.algebraMap_ne_zero c4_ne_zero
  have hD : am D1 ≠ 0 := RatFunc.algebraMap_ne_zero D1_ne_zero
  rw [dRat3_Ww, dRat2_Vv, dRat_Uu, show Zz = am c0 / am c4 from rfl]
  simp only [P2Nu, P1Nu, P1Nv, Polynomial.derivative_sub, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_add, Polynomial.derivative_X,
    Polynomial.derivative_C, Polynomial.derivative_natCast, Polynomial.derivative_intCast,
    Polynomial.derivative_one, Polynomial.derivative_zero, Polynomial.derivative_ofNat,
    c2_derivative, c2d_derivative, c3_derivative, c3d_derivative,
    c3dd_derivative, c4_derivative, c4d_derivative, c4dd_derivative, Nat.reduceSub, pow_one,
    mul_one, mul_zero,
    Polynomial.C_eq_natCast, Polynomial.C_eq_intCast, map_mul, map_sub, map_add, map_pow]
  field_simp
  ring_nf
  toPoly
  refine congrArg (algebraMap (Polynomial ℚ) (RatFunc ℚ)) ?_
  trace_state
  linear_combination (coeff_ident_zero)

/-! ## Leibniz rules and the operator identity -/

lemma dRat_natCast (n : ℕ) : dRat ((n : ℕ) : RF) = 0 := by
  rw [← map_natCast (algebraMap (Polynomial ℚ) (RatFunc ℚ)) n, dRat_algebraMap,
    Polynomial.derivative_natCast, map_zero]

lemma dRat_two : dRat (2 : RF) = 0 := by
  rw [show (2 : RF) = am (2 : Polynomial ℚ) from (map_ofNat _ 2).symm, dRat_algebraMap,
    Polynomial.derivative_ofNat, map_zero]

lemma dRat_mul_two (u f : RF) :
    dRat (dRat (u * f)) = dRat (dRat u) * f + 2 * dRat u * dRat f + u * dRat (dRat f) := by
  rw [dRat_mul, dRat_add, dRat_mul, dRat_mul]
  ring

lemma dRat_mul_three (u f : RF) :
    dRat (dRat (dRat (u * f)))
      = dRat (dRat (dRat u)) * f + 3 * dRat (dRat u) * dRat f + 3 * dRat u * dRat (dRat f)
        + u * dRat (dRat (dRat f)) := by
  rw [dRat_mul_two]
  simp only [dRat_add, dRat_mul, dRat_two, mul_zero, zero_mul, mul_one, add_zero]
  ring

/-- **The eliminated operator identity.**  The operator produced by the paper's
system for `b3` equals `∑_j (2 P_j / D1^{4-j}) b3^{(j)}`. -/
theorem elim_operator (f : RF) :
    dRat (Uu * f) - dRat (dRat (Vv * f)) + dRat (dRat (dRat (Ww * f)))
        - dRat (dRat (dRat (dRat f))) - Zz * f
      = (am (2 * P0) / am (D1 ^ 4)) * f
        + (am (2 * P1) / am (D1 ^ 3)) * dRat f
        + (am (2 * P2) / am (D1 ^ 2)) * dRat (dRat f)
        + (am (2 * P3) / am D1) * dRat (dRat (dRat f))
        - dRat (dRat (dRat (dRat f))) := by
  rw [dRat_mul, dRat_mul_two, dRat_mul_three, ← coeff_three, ← coeff_two, ← coeff_one,
    ← coeff_zero]
  ring

end ElimOp
end Submission.CDT
