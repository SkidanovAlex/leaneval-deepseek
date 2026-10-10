/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Submission.Work.MotK.KleinData
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# I5: the second partials of the secant quintic lie in the ideal of the curve

`kleinSecDD_{ij}` is `∂_i ∂_j s` (an explicit cubic form), and `kleinSecDD_{ij}_eq` exhibits it
as an explicit combination `∑_k c_k p_k` with `c_k` linear in the coordinates (the shape forced
by the `ℤ/5`-grading).  Geometrically: the secant surface is singular of multiplicity `≥ 3`
along `C`, i.e. `mult_C(Sec C) ≥ 3` (audit node K1, identity I5).  The certificates were
computed by `cas/s07_cert.py`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Work.MotK

variable {R : Type*} [CommRing R]

/-- `∂_0 ∂_0 s`. -/
def kleinSecDD_00 (a b : R) (x : Fin 5 → R) : R :=
  -18*a^(4:ℕ)*b^(6:ℕ)*x 0*x 1*x 4 + 18*a^(6:ℕ)*b^(4:ℕ)*x 0*x 2*x 3 + 2*a^(2:ℕ)*b^(8:ℕ)*(x 1)^(2:ℕ)*x 3 + 2*a^(2:ℕ)*b^(8:ℕ)*x 2*(x 4)^(2:ℕ) - 2*a^(8:ℕ)*b^(2:ℕ)*(x 3)^(2:ℕ)*x 4 - 2*a^(8:ℕ)*b^(2:ℕ)*x 1*(x 2)^(2:ℕ) - 20*a^(5:ℕ)*b^(5:ℕ)*(x 0)^(3:ℕ) - 4*a^(3:ℕ)*b^(7:ℕ)*(x 3)^(2:ℕ)*x 4 - 4*a^(3:ℕ)*b^(7:ℕ)*x 1*(x 2)^(2:ℕ) - 4*a^(7:ℕ)*b^(3:ℕ)*(x 1)^(2:ℕ)*x 3 - 4*a^(7:ℕ)*b^(3:ℕ)*x 2*(x 4)^(2:ℕ) + 6*a*b^(9:ℕ)*x 0*x 2*x 3 + 6*a^(9:ℕ)*b*x 0*x 1*x 4

/-- `∂_0 ∂_1 s`. -/
def kleinSecDD_01 (a b : R) (x : Fin 5 → R) : R :=
  16*a^(5:ℕ)*b^(5:ℕ)*x 2*x 3*x 4 - 2*a^(8:ℕ)*b^(2:ℕ)*x 0*(x 2)^(2:ℕ) - 2*a^(8:ℕ)*b^(2:ℕ)*x 1*(x 4)^(2:ℕ) + 3*a^(6:ℕ)*b^(4:ℕ)*(x 3)^(3:ℕ) + 3*a^(9:ℕ)*b*(x 0)^(2:ℕ)*x 4 + 3*a^(9:ℕ)*b*(x 1)^(2:ℕ)*x 2 + 4*a^(2:ℕ)*b^(8:ℕ)*x 0*x 1*x 3 - 4*a^(3:ℕ)*b^(7:ℕ)*x 0*(x 2)^(2:ℕ) - 4*a^(3:ℕ)*b^(7:ℕ)*x 1*(x 4)^(2:ℕ) - 8*a^(7:ℕ)*b^(3:ℕ)*x 0*x 1*x 3 - 9*a^(4:ℕ)*b^(6:ℕ)*(x 0)^(2:ℕ)*x 4 - 9*a^(4:ℕ)*b^(6:ℕ)*(x 1)^(2:ℕ)*x 2 + a*b^(9:ℕ)*(x 3)^(3:ℕ) - a^(10:ℕ)*x 2*x 3*x 4 + b^(10:ℕ)*x 2*x 3*x 4

/-- `∂_0 ∂_2 s`. -/
def kleinSecDD_02 (a b : R) (x : Fin 5 → R) : R :=
  16*a^(5:ℕ)*b^(5:ℕ)*x 1*x 3*x 4 + 2*a^(2:ℕ)*b^(8:ℕ)*x 0*(x 4)^(2:ℕ) + 2*a^(2:ℕ)*b^(8:ℕ)*x 2*(x 3)^(2:ℕ) + 3*a*b^(9:ℕ)*(x 0)^(2:ℕ)*x 3 + 3*a*b^(9:ℕ)*(x 2)^(2:ℕ)*x 4 - 3*a^(4:ℕ)*b^(6:ℕ)*(x 1)^(3:ℕ) - 4*a^(7:ℕ)*b^(3:ℕ)*x 0*(x 4)^(2:ℕ) - 4*a^(7:ℕ)*b^(3:ℕ)*x 2*(x 3)^(2:ℕ) - 4*a^(8:ℕ)*b^(2:ℕ)*x 0*x 1*x 2 - 8*a^(3:ℕ)*b^(7:ℕ)*x 0*x 1*x 2 + 9*a^(6:ℕ)*b^(4:ℕ)*(x 0)^(2:ℕ)*x 3 + 9*a^(6:ℕ)*b^(4:ℕ)*(x 2)^(2:ℕ)*x 4 - a^(10:ℕ)*x 1*x 3*x 4 + a^(9:ℕ)*b*(x 1)^(3:ℕ) + b^(10:ℕ)*x 1*x 3*x 4

/-- `∂_0 ∂_3 s`. -/
def kleinSecDD_03 (a b : R) (x : Fin 5 → R) : R :=
  16*a^(5:ℕ)*b^(5:ℕ)*x 1*x 2*x 4 + 2*a^(2:ℕ)*b^(8:ℕ)*(x 2)^(2:ℕ)*x 3 + 2*a^(2:ℕ)*b^(8:ℕ)*x 0*(x 1)^(2:ℕ) + 3*a*b^(9:ℕ)*(x 0)^(2:ℕ)*x 2 + 3*a*b^(9:ℕ)*x 1*(x 3)^(2:ℕ) - 3*a^(4:ℕ)*b^(6:ℕ)*(x 4)^(3:ℕ) - 4*a^(7:ℕ)*b^(3:ℕ)*(x 2)^(2:ℕ)*x 3 - 4*a^(7:ℕ)*b^(3:ℕ)*x 0*(x 1)^(2:ℕ) - 4*a^(8:ℕ)*b^(2:ℕ)*x 0*x 3*x 4 - 8*a^(3:ℕ)*b^(7:ℕ)*x 0*x 3*x 4 + 9*a^(6:ℕ)*b^(4:ℕ)*(x 0)^(2:ℕ)*x 2 + 9*a^(6:ℕ)*b^(4:ℕ)*x 1*(x 3)^(2:ℕ) - a^(10:ℕ)*x 1*x 2*x 4 + a^(9:ℕ)*b*(x 4)^(3:ℕ) + b^(10:ℕ)*x 1*x 2*x 4

/-- `∂_0 ∂_4 s`. -/
def kleinSecDD_04 (a b : R) (x : Fin 5 → R) : R :=
  16*a^(5:ℕ)*b^(5:ℕ)*x 1*x 2*x 3 - 2*a^(8:ℕ)*b^(2:ℕ)*(x 1)^(2:ℕ)*x 4 - 2*a^(8:ℕ)*b^(2:ℕ)*x 0*(x 3)^(2:ℕ) + 3*a^(6:ℕ)*b^(4:ℕ)*(x 2)^(3:ℕ) + 3*a^(9:ℕ)*b*(x 0)^(2:ℕ)*x 1 + 3*a^(9:ℕ)*b*x 3*(x 4)^(2:ℕ) + 4*a^(2:ℕ)*b^(8:ℕ)*x 0*x 2*x 4 - 4*a^(3:ℕ)*b^(7:ℕ)*(x 1)^(2:ℕ)*x 4 - 4*a^(3:ℕ)*b^(7:ℕ)*x 0*(x 3)^(2:ℕ) - 8*a^(7:ℕ)*b^(3:ℕ)*x 0*x 2*x 4 - 9*a^(4:ℕ)*b^(6:ℕ)*(x 0)^(2:ℕ)*x 1 - 9*a^(4:ℕ)*b^(6:ℕ)*x 3*(x 4)^(2:ℕ) + a*b^(9:ℕ)*(x 2)^(3:ℕ) - a^(10:ℕ)*x 1*x 2*x 3 + b^(10:ℕ)*x 1*x 2*x 3

/-- `∂_1 ∂_1 s`. -/
def kleinSecDD_11 (a b : R) (x : Fin 5 → R) : R :=
  -18*a^(4:ℕ)*b^(6:ℕ)*x 0*x 1*x 2 + 18*a^(6:ℕ)*b^(4:ℕ)*x 1*x 3*x 4 + 2*a^(2:ℕ)*b^(8:ℕ)*(x 0)^(2:ℕ)*x 3 + 2*a^(2:ℕ)*b^(8:ℕ)*(x 2)^(2:ℕ)*x 4 - 2*a^(8:ℕ)*b^(2:ℕ)*x 0*(x 4)^(2:ℕ) - 2*a^(8:ℕ)*b^(2:ℕ)*x 2*(x 3)^(2:ℕ) - 20*a^(5:ℕ)*b^(5:ℕ)*(x 1)^(3:ℕ) - 4*a^(3:ℕ)*b^(7:ℕ)*x 0*(x 4)^(2:ℕ) - 4*a^(3:ℕ)*b^(7:ℕ)*x 2*(x 3)^(2:ℕ) - 4*a^(7:ℕ)*b^(3:ℕ)*(x 0)^(2:ℕ)*x 3 - 4*a^(7:ℕ)*b^(3:ℕ)*(x 2)^(2:ℕ)*x 4 + 6*a*b^(9:ℕ)*x 1*x 3*x 4 + 6*a^(9:ℕ)*b*x 0*x 1*x 2

/-- `∂_1 ∂_2 s`. -/
def kleinSecDD_12 (a b : R) (x : Fin 5 → R) : R :=
  16*a^(5:ℕ)*b^(5:ℕ)*x 0*x 3*x 4 - 2*a^(8:ℕ)*b^(2:ℕ)*(x 0)^(2:ℕ)*x 2 - 2*a^(8:ℕ)*b^(2:ℕ)*x 1*(x 3)^(2:ℕ) + 3*a^(6:ℕ)*b^(4:ℕ)*(x 4)^(3:ℕ) + 3*a^(9:ℕ)*b*(x 2)^(2:ℕ)*x 3 + 3*a^(9:ℕ)*b*x 0*(x 1)^(2:ℕ) + 4*a^(2:ℕ)*b^(8:ℕ)*x 1*x 2*x 4 - 4*a^(3:ℕ)*b^(7:ℕ)*(x 0)^(2:ℕ)*x 2 - 4*a^(3:ℕ)*b^(7:ℕ)*x 1*(x 3)^(2:ℕ) - 8*a^(7:ℕ)*b^(3:ℕ)*x 1*x 2*x 4 - 9*a^(4:ℕ)*b^(6:ℕ)*(x 2)^(2:ℕ)*x 3 - 9*a^(4:ℕ)*b^(6:ℕ)*x 0*(x 1)^(2:ℕ) + a*b^(9:ℕ)*(x 4)^(3:ℕ) - a^(10:ℕ)*x 0*x 3*x 4 + b^(10:ℕ)*x 0*x 3*x 4

/-- `∂_1 ∂_3 s`. -/
def kleinSecDD_13 (a b : R) (x : Fin 5 → R) : R :=
  16*a^(5:ℕ)*b^(5:ℕ)*x 0*x 2*x 4 + 2*a^(2:ℕ)*b^(8:ℕ)*(x 0)^(2:ℕ)*x 1 + 2*a^(2:ℕ)*b^(8:ℕ)*x 3*(x 4)^(2:ℕ) + 3*a*b^(9:ℕ)*(x 1)^(2:ℕ)*x 4 + 3*a*b^(9:ℕ)*x 0*(x 3)^(2:ℕ) - 3*a^(4:ℕ)*b^(6:ℕ)*(x 2)^(3:ℕ) - 4*a^(7:ℕ)*b^(3:ℕ)*(x 0)^(2:ℕ)*x 1 - 4*a^(7:ℕ)*b^(3:ℕ)*x 3*(x 4)^(2:ℕ) - 4*a^(8:ℕ)*b^(2:ℕ)*x 1*x 2*x 3 - 8*a^(3:ℕ)*b^(7:ℕ)*x 1*x 2*x 3 + 9*a^(6:ℕ)*b^(4:ℕ)*(x 1)^(2:ℕ)*x 4 + 9*a^(6:ℕ)*b^(4:ℕ)*x 0*(x 3)^(2:ℕ) - a^(10:ℕ)*x 0*x 2*x 4 + a^(9:ℕ)*b*(x 2)^(3:ℕ) + b^(10:ℕ)*x 0*x 2*x 4

/-- `∂_1 ∂_4 s`. -/
def kleinSecDD_14 (a b : R) (x : Fin 5 → R) : R :=
  16*a^(5:ℕ)*b^(5:ℕ)*x 0*x 2*x 3 + 2*a^(2:ℕ)*b^(8:ℕ)*(x 3)^(2:ℕ)*x 4 + 2*a^(2:ℕ)*b^(8:ℕ)*x 1*(x 2)^(2:ℕ) + 3*a*b^(9:ℕ)*(x 1)^(2:ℕ)*x 3 + 3*a*b^(9:ℕ)*x 2*(x 4)^(2:ℕ) - 3*a^(4:ℕ)*b^(6:ℕ)*(x 0)^(3:ℕ) - 4*a^(7:ℕ)*b^(3:ℕ)*(x 3)^(2:ℕ)*x 4 - 4*a^(7:ℕ)*b^(3:ℕ)*x 1*(x 2)^(2:ℕ) - 4*a^(8:ℕ)*b^(2:ℕ)*x 0*x 1*x 4 - 8*a^(3:ℕ)*b^(7:ℕ)*x 0*x 1*x 4 + 9*a^(6:ℕ)*b^(4:ℕ)*(x 1)^(2:ℕ)*x 3 + 9*a^(6:ℕ)*b^(4:ℕ)*x 2*(x 4)^(2:ℕ) - a^(10:ℕ)*x 0*x 2*x 3 + a^(9:ℕ)*b*(x 0)^(3:ℕ) + b^(10:ℕ)*x 0*x 2*x 3

/-- `∂_2 ∂_2 s`. -/
def kleinSecDD_22 (a b : R) (x : Fin 5 → R) : R :=
  -18*a^(4:ℕ)*b^(6:ℕ)*x 1*x 2*x 3 + 18*a^(6:ℕ)*b^(4:ℕ)*x 0*x 2*x 4 + 2*a^(2:ℕ)*b^(8:ℕ)*(x 1)^(2:ℕ)*x 4 + 2*a^(2:ℕ)*b^(8:ℕ)*x 0*(x 3)^(2:ℕ) - 2*a^(8:ℕ)*b^(2:ℕ)*(x 0)^(2:ℕ)*x 1 - 2*a^(8:ℕ)*b^(2:ℕ)*x 3*(x 4)^(2:ℕ) - 20*a^(5:ℕ)*b^(5:ℕ)*(x 2)^(3:ℕ) - 4*a^(3:ℕ)*b^(7:ℕ)*(x 0)^(2:ℕ)*x 1 - 4*a^(3:ℕ)*b^(7:ℕ)*x 3*(x 4)^(2:ℕ) - 4*a^(7:ℕ)*b^(3:ℕ)*(x 1)^(2:ℕ)*x 4 - 4*a^(7:ℕ)*b^(3:ℕ)*x 0*(x 3)^(2:ℕ) + 6*a*b^(9:ℕ)*x 0*x 2*x 4 + 6*a^(9:ℕ)*b*x 1*x 2*x 3

/-- `∂_2 ∂_3 s`. -/
def kleinSecDD_23 (a b : R) (x : Fin 5 → R) : R :=
  16*a^(5:ℕ)*b^(5:ℕ)*x 0*x 1*x 4 - 2*a^(8:ℕ)*b^(2:ℕ)*(x 1)^(2:ℕ)*x 3 - 2*a^(8:ℕ)*b^(2:ℕ)*x 2*(x 4)^(2:ℕ) + 3*a^(6:ℕ)*b^(4:ℕ)*(x 0)^(3:ℕ) + 3*a^(9:ℕ)*b*(x 3)^(2:ℕ)*x 4 + 3*a^(9:ℕ)*b*x 1*(x 2)^(2:ℕ) + 4*a^(2:ℕ)*b^(8:ℕ)*x 0*x 2*x 3 - 4*a^(3:ℕ)*b^(7:ℕ)*(x 1)^(2:ℕ)*x 3 - 4*a^(3:ℕ)*b^(7:ℕ)*x 2*(x 4)^(2:ℕ) - 8*a^(7:ℕ)*b^(3:ℕ)*x 0*x 2*x 3 - 9*a^(4:ℕ)*b^(6:ℕ)*(x 3)^(2:ℕ)*x 4 - 9*a^(4:ℕ)*b^(6:ℕ)*x 1*(x 2)^(2:ℕ) + a*b^(9:ℕ)*(x 0)^(3:ℕ) - a^(10:ℕ)*x 0*x 1*x 4 + b^(10:ℕ)*x 0*x 1*x 4

/-- `∂_2 ∂_4 s`. -/
def kleinSecDD_24 (a b : R) (x : Fin 5 → R) : R :=
  16*a^(5:ℕ)*b^(5:ℕ)*x 0*x 1*x 3 + 2*a^(2:ℕ)*b^(8:ℕ)*(x 0)^(2:ℕ)*x 4 + 2*a^(2:ℕ)*b^(8:ℕ)*(x 1)^(2:ℕ)*x 2 + 3*a*b^(9:ℕ)*x 0*(x 2)^(2:ℕ) + 3*a*b^(9:ℕ)*x 1*(x 4)^(2:ℕ) - 3*a^(4:ℕ)*b^(6:ℕ)*(x 3)^(3:ℕ) - 4*a^(7:ℕ)*b^(3:ℕ)*(x 0)^(2:ℕ)*x 4 - 4*a^(7:ℕ)*b^(3:ℕ)*(x 1)^(2:ℕ)*x 2 - 4*a^(8:ℕ)*b^(2:ℕ)*x 2*x 3*x 4 - 8*a^(3:ℕ)*b^(7:ℕ)*x 2*x 3*x 4 + 9*a^(6:ℕ)*b^(4:ℕ)*x 0*(x 2)^(2:ℕ) + 9*a^(6:ℕ)*b^(4:ℕ)*x 1*(x 4)^(2:ℕ) - a^(10:ℕ)*x 0*x 1*x 3 + a^(9:ℕ)*b*(x 3)^(3:ℕ) + b^(10:ℕ)*x 0*x 1*x 3

/-- `∂_3 ∂_3 s`. -/
def kleinSecDD_33 (a b : R) (x : Fin 5 → R) : R :=
  -18*a^(4:ℕ)*b^(6:ℕ)*x 2*x 3*x 4 + 18*a^(6:ℕ)*b^(4:ℕ)*x 0*x 1*x 3 + 2*a^(2:ℕ)*b^(8:ℕ)*x 0*(x 2)^(2:ℕ) + 2*a^(2:ℕ)*b^(8:ℕ)*x 1*(x 4)^(2:ℕ) - 2*a^(8:ℕ)*b^(2:ℕ)*(x 0)^(2:ℕ)*x 4 - 2*a^(8:ℕ)*b^(2:ℕ)*(x 1)^(2:ℕ)*x 2 - 20*a^(5:ℕ)*b^(5:ℕ)*(x 3)^(3:ℕ) - 4*a^(3:ℕ)*b^(7:ℕ)*(x 0)^(2:ℕ)*x 4 - 4*a^(3:ℕ)*b^(7:ℕ)*(x 1)^(2:ℕ)*x 2 - 4*a^(7:ℕ)*b^(3:ℕ)*x 0*(x 2)^(2:ℕ) - 4*a^(7:ℕ)*b^(3:ℕ)*x 1*(x 4)^(2:ℕ) + 6*a*b^(9:ℕ)*x 0*x 1*x 3 + 6*a^(9:ℕ)*b*x 2*x 3*x 4

/-- `∂_3 ∂_4 s`. -/
def kleinSecDD_34 (a b : R) (x : Fin 5 → R) : R :=
  16*a^(5:ℕ)*b^(5:ℕ)*x 0*x 1*x 2 - 2*a^(8:ℕ)*b^(2:ℕ)*(x 0)^(2:ℕ)*x 3 - 2*a^(8:ℕ)*b^(2:ℕ)*(x 2)^(2:ℕ)*x 4 + 3*a^(6:ℕ)*b^(4:ℕ)*(x 1)^(3:ℕ) + 3*a^(9:ℕ)*b*x 0*(x 4)^(2:ℕ) + 3*a^(9:ℕ)*b*x 2*(x 3)^(2:ℕ) + 4*a^(2:ℕ)*b^(8:ℕ)*x 1*x 3*x 4 - 4*a^(3:ℕ)*b^(7:ℕ)*(x 0)^(2:ℕ)*x 3 - 4*a^(3:ℕ)*b^(7:ℕ)*(x 2)^(2:ℕ)*x 4 - 8*a^(7:ℕ)*b^(3:ℕ)*x 1*x 3*x 4 - 9*a^(4:ℕ)*b^(6:ℕ)*x 0*(x 4)^(2:ℕ) - 9*a^(4:ℕ)*b^(6:ℕ)*x 2*(x 3)^(2:ℕ) + a*b^(9:ℕ)*(x 1)^(3:ℕ) - a^(10:ℕ)*x 0*x 1*x 2 + b^(10:ℕ)*x 0*x 1*x 2

/-- `∂_4 ∂_4 s`. -/
def kleinSecDD_44 (a b : R) (x : Fin 5 → R) : R :=
  -18*a^(4:ℕ)*b^(6:ℕ)*x 0*x 3*x 4 + 18*a^(6:ℕ)*b^(4:ℕ)*x 1*x 2*x 4 + 2*a^(2:ℕ)*b^(8:ℕ)*(x 0)^(2:ℕ)*x 2 + 2*a^(2:ℕ)*b^(8:ℕ)*x 1*(x 3)^(2:ℕ) - 2*a^(8:ℕ)*b^(2:ℕ)*(x 2)^(2:ℕ)*x 3 - 2*a^(8:ℕ)*b^(2:ℕ)*x 0*(x 1)^(2:ℕ) - 20*a^(5:ℕ)*b^(5:ℕ)*(x 4)^(3:ℕ) - 4*a^(3:ℕ)*b^(7:ℕ)*(x 2)^(2:ℕ)*x 3 - 4*a^(3:ℕ)*b^(7:ℕ)*x 0*(x 1)^(2:ℕ) - 4*a^(7:ℕ)*b^(3:ℕ)*(x 0)^(2:ℕ)*x 2 - 4*a^(7:ℕ)*b^(3:ℕ)*x 1*(x 3)^(2:ℕ) + 6*a*b^(9:ℕ)*x 1*x 2*x 4 + 6*a^(9:ℕ)*b*x 0*x 3*x 4

theorem kleinSecDD_00_eq (a b : R) (x : Fin 5 → R) :
    kleinSecDD_00 a b x = (20*a^(4:ℕ)*b^(4:ℕ)*x 0) * kleinP0 a b x + (2*a^(2:ℕ)*b^(6:ℕ)*x 1 + 6*a^(7:ℕ)*b*x 1) * kleinP1 a b x + (-2*a*b^(7:ℕ)*x 2 + 4*a^(6:ℕ)*b^(2:ℕ)*x 2) * kleinP2 a b x + (-2*a^(6:ℕ)*b^(2:ℕ)*x 3 - 4*a*b^(7:ℕ)*x 3) * kleinP3 a b x + (-0) * kleinP4 a b x := by
  simp only [kleinSecDD_00, kleinP0, kleinP1, kleinP2, kleinP3, kleinP4]
  first | refl_ring1 | ring

theorem kleinSecDD_01_eq (a b : R) (x : Fin 5 → R) :
    kleinSecDD_01 a b x = (13*a^(3:ℕ)*b^(5:ℕ)*x 4 - a^(8:ℕ)*x 4) * kleinP0 a b x + (2*a^(7:ℕ)*b*x 0 + 4*a^(2:ℕ)*b^(6:ℕ)*x 0) * kleinP1 a b x + (3*a^(7:ℕ)*b*x 1 - 9*a^(2:ℕ)*b^(6:ℕ)*x 1) * kleinP2 a b x + (-0) * kleinP3 a b x + (-3*a^(5:ℕ)*b^(3:ℕ)*x 3 - b^(8:ℕ)*x 3) * kleinP4 a b x := by
  simp only [kleinSecDD_01, kleinP0, kleinP1, kleinP2, kleinP3, kleinP4]
  first | refl_ring1 | ring

theorem kleinSecDD_02_eq (a b : R) (x : Fin 5 → R) :
    kleinSecDD_02 a b x = (2*b^(8:ℕ)*x 3 - 4*a^(5:ℕ)*b^(3:ℕ)*x 3) * kleinP0 a b x + (-3*b^(8:ℕ)*x 4 - 9*a^(5:ℕ)*b^(3:ℕ)*x 4) * kleinP1 a b x + (-5*a*b^(7:ℕ)*x 0 - 5*a^(6:ℕ)*b^(2:ℕ)*x 0) * kleinP2 a b x + (3*a^(3:ℕ)*b^(5:ℕ)*x 1 - a^(8:ℕ)*x 1) * kleinP3 a b x + (-0) * kleinP4 a b x := by
  simp only [kleinSecDD_02, kleinP0, kleinP1, kleinP2, kleinP3, kleinP4]
  first | refl_ring1 | ring

theorem kleinSecDD_03_eq (a b : R) (x : Fin 5 → R) :
    kleinSecDD_03 a b x = (-13*a^(5:ℕ)*b^(3:ℕ)*x 2 - b^(8:ℕ)*x 2) * kleinP0 a b x + (-3*a*b^(7:ℕ)*x 3 - 9*a^(6:ℕ)*b^(2:ℕ)*x 3) * kleinP1 a b x + (3*a^(3:ℕ)*b^(5:ℕ)*x 4 - a^(8:ℕ)*x 4) * kleinP2 a b x + (-2*a*b^(7:ℕ)*x 0 + 4*a^(6:ℕ)*b^(2:ℕ)*x 0) * kleinP3 a b x + (-0) * kleinP4 a b x := by
  simp only [kleinSecDD_03, kleinP0, kleinP1, kleinP2, kleinP3, kleinP4]
  first | refl_ring1 | ring

theorem kleinSecDD_04_eq (a b : R) (x : Fin 5 → R) :
    kleinSecDD_04 a b x = (-3*a^(8:ℕ)*x 1 + 9*a^(3:ℕ)*b^(5:ℕ)*x 1) * kleinP0 a b x + (-3*a^(5:ℕ)*b^(3:ℕ)*x 2 - b^(8:ℕ)*x 2) * kleinP1 a b x + (2*a^(8:ℕ)*x 3 + 4*a^(3:ℕ)*b^(5:ℕ)*x 3) * kleinP2 a b x + (-5*a^(2:ℕ)*b^(6:ℕ)*x 4 + 5*a^(7:ℕ)*b*x 4) * kleinP3 a b x + (-0) * kleinP4 a b x := by
  simp only [kleinSecDD_04, kleinP0, kleinP1, kleinP2, kleinP3, kleinP4]
  first | refl_ring1 | ring

theorem kleinSecDD_11_eq (a b : R) (x : Fin 5 → R) :
    kleinSecDD_11 a b x = (-2*a^(6:ℕ)*b^(2:ℕ)*x 3 - 4*a*b^(7:ℕ)*x 3) * kleinP0 a b x + (-2*a*b^(7:ℕ)*x 4 + 4*a^(6:ℕ)*b^(2:ℕ)*x 4) * kleinP1 a b x + (2*a^(2:ℕ)*b^(6:ℕ)*x 0 + 6*a^(7:ℕ)*b*x 0) * kleinP2 a b x + (20*a^(4:ℕ)*b^(4:ℕ)*x 1) * kleinP3 a b x + (-0) * kleinP4 a b x := by
  simp only [kleinSecDD_11, kleinP0, kleinP1, kleinP2, kleinP3, kleinP4]
  first | refl_ring1 | ring

theorem kleinSecDD_12_eq (a b : R) (x : Fin 5 → R) :
    kleinSecDD_12 a b x = (-5*a^(2:ℕ)*b^(6:ℕ)*x 2 + 5*a^(7:ℕ)*b*x 2) * kleinP0 a b x + (2*a^(8:ℕ)*x 3 + 4*a^(3:ℕ)*b^(5:ℕ)*x 3) * kleinP1 a b x + (-3*a^(5:ℕ)*b^(3:ℕ)*x 4 - b^(8:ℕ)*x 4) * kleinP2 a b x + (-3*a^(8:ℕ)*x 0 + 9*a^(3:ℕ)*b^(5:ℕ)*x 0) * kleinP3 a b x + (-0) * kleinP4 a b x := by
  simp only [kleinSecDD_12, kleinP0, kleinP1, kleinP2, kleinP3, kleinP4]
  first | refl_ring1 | ring

theorem kleinSecDD_13_eq (a b : R) (x : Fin 5 → R) :
    kleinSecDD_13 a b x = (-2*a*b^(7:ℕ)*x 1 + 4*a^(6:ℕ)*b^(2:ℕ)*x 1) * kleinP0 a b x + (3*a^(3:ℕ)*b^(5:ℕ)*x 2 - a^(8:ℕ)*x 2) * kleinP1 a b x + (-3*a*b^(7:ℕ)*x 3 - 9*a^(6:ℕ)*b^(2:ℕ)*x 3) * kleinP2 a b x + (-13*a^(5:ℕ)*b^(3:ℕ)*x 4 - b^(8:ℕ)*x 4) * kleinP3 a b x + (-0) * kleinP4 a b x := by
  simp only [kleinSecDD_13, kleinP0, kleinP1, kleinP2, kleinP3, kleinP4]
  first | refl_ring1 | ring

theorem kleinSecDD_14_eq (a b : R) (x : Fin 5 → R) :
    kleinSecDD_14 a b x = (3*a^(3:ℕ)*b^(5:ℕ)*x 0 - a^(8:ℕ)*x 0) * kleinP0 a b x + (-5*a*b^(7:ℕ)*x 1 - 5*a^(6:ℕ)*b^(2:ℕ)*x 1) * kleinP1 a b x + (-3*b^(8:ℕ)*x 2 - 9*a^(5:ℕ)*b^(3:ℕ)*x 2) * kleinP2 a b x + (2*b^(8:ℕ)*x 3 - 4*a^(5:ℕ)*b^(3:ℕ)*x 3) * kleinP3 a b x + (-0) * kleinP4 a b x := by
  simp only [kleinSecDD_14, kleinP0, kleinP1, kleinP2, kleinP3, kleinP4]
  first | refl_ring1 | ring

theorem kleinSecDD_22_eq (a b : R) (x : Fin 5 → R) :
    kleinSecDD_22 a b x = (2*a^(7:ℕ)*b*x 1 + 4*a^(2:ℕ)*b^(6:ℕ)*x 1) * kleinP0 a b x + (20*a^(4:ℕ)*b^(4:ℕ)*x 2) * kleinP1 a b x + (-2*a^(2:ℕ)*b^(6:ℕ)*x 3 + 4*a^(7:ℕ)*b*x 3) * kleinP2 a b x + (2*a^(6:ℕ)*b^(2:ℕ)*x 4 - 6*a*b^(7:ℕ)*x 4) * kleinP3 a b x + (-0) * kleinP4 a b x := by
  simp only [kleinSecDD_22, kleinP0, kleinP1, kleinP2, kleinP3, kleinP4]
  first | refl_ring1 | ring

theorem kleinSecDD_23_eq (a b : R) (x : Fin 5 → R) :
    kleinSecDD_23 a b x = (-3*a^(5:ℕ)*b^(3:ℕ)*x 0 - b^(8:ℕ)*x 0) * kleinP0 a b x + (13*a^(3:ℕ)*b^(5:ℕ)*x 1 - a^(8:ℕ)*x 1) * kleinP1 a b x + (2*a^(7:ℕ)*b*x 2 + 4*a^(2:ℕ)*b^(6:ℕ)*x 2) * kleinP2 a b x + (3*a^(7:ℕ)*b*x 3 - 9*a^(2:ℕ)*b^(6:ℕ)*x 3) * kleinP3 a b x + (-0) * kleinP4 a b x := by
  simp only [kleinSecDD_23, kleinP0, kleinP1, kleinP2, kleinP3, kleinP4]
  first | refl_ring1 | ring

theorem kleinSecDD_24_eq (a b : R) (x : Fin 5 → R) :
    kleinSecDD_24 a b x = (-5*a*b^(7:ℕ)*x 4 - 5*a^(6:ℕ)*b^(2:ℕ)*x 4) * kleinP0 a b x + (-3*b^(8:ℕ)*x 0 - 9*a^(5:ℕ)*b^(3:ℕ)*x 0) * kleinP1 a b x + (2*b^(8:ℕ)*x 1 - 4*a^(5:ℕ)*b^(3:ℕ)*x 1) * kleinP2 a b x + (-0) * kleinP3 a b x + (3*a^(3:ℕ)*b^(5:ℕ)*x 3 - a^(8:ℕ)*x 3) * kleinP4 a b x := by
  simp only [kleinSecDD_24, kleinP0, kleinP1, kleinP2, kleinP3, kleinP4]
  first | refl_ring1 | ring

theorem kleinSecDD_33_eq (a b : R) (x : Fin 5 → R) :
    kleinSecDD_33 a b x = (2*a^(2:ℕ)*b^(6:ℕ)*x 4 + 6*a^(7:ℕ)*b*x 4) * kleinP0 a b x + (-2*a*b^(7:ℕ)*x 0 + 4*a^(6:ℕ)*b^(2:ℕ)*x 0) * kleinP1 a b x + (-2*a^(6:ℕ)*b^(2:ℕ)*x 1 - 4*a*b^(7:ℕ)*x 1) * kleinP2 a b x + (-0) * kleinP3 a b x + (20*a^(4:ℕ)*b^(4:ℕ)*x 3) * kleinP4 a b x := by
  simp only [kleinSecDD_33, kleinP0, kleinP1, kleinP2, kleinP3, kleinP4]
  first | refl_ring1 | ring

theorem kleinSecDD_34_eq (a b : R) (x : Fin 5 → R) :
    kleinSecDD_34 a b x = (3*a^(7:ℕ)*b*x 3 - 9*a^(2:ℕ)*b^(6:ℕ)*x 3) * kleinP0 a b x + (2*a^(7:ℕ)*b*x 4 + 4*a^(2:ℕ)*b^(6:ℕ)*x 4) * kleinP1 a b x + (13*a^(3:ℕ)*b^(5:ℕ)*x 0 - a^(8:ℕ)*x 0) * kleinP2 a b x + (-3*a^(5:ℕ)*b^(3:ℕ)*x 1 - b^(8:ℕ)*x 1) * kleinP3 a b x + (-0) * kleinP4 a b x := by
  simp only [kleinSecDD_34, kleinP0, kleinP1, kleinP2, kleinP3, kleinP4]
  first | refl_ring1 | ring

theorem kleinSecDD_44_eq (a b : R) (x : Fin 5 → R) :
    kleinSecDD_44 a b x = (2*a^(6:ℕ)*b^(2:ℕ)*x 2 - 6*a*b^(7:ℕ)*x 2) * kleinP0 a b x + (-2*a^(2:ℕ)*b^(6:ℕ)*x 3 + 4*a^(7:ℕ)*b*x 3) * kleinP1 a b x + (20*a^(4:ℕ)*b^(4:ℕ)*x 4) * kleinP2 a b x + (2*a^(7:ℕ)*b*x 0 + 4*a^(2:ℕ)*b^(6:ℕ)*x 0) * kleinP3 a b x + (-0) * kleinP4 a b x := by
  simp only [kleinSecDD_44, kleinP0, kleinP1, kleinP2, kleinP3, kleinP4]
  first | refl_ring1 | ring

end Work.MotK

