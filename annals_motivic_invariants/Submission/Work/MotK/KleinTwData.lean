/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Submission.Work.MotK.KleinData

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The T-twist (Kummer coordinate) data of the Klein model

Let `w` be a fifth root of `h` (`h = w^5`) and substitute `x_i = w^i y_i` in the Klein data.
Every polynomial of the model is homogeneous for the `ℤ/5`-grading `deg x_i = i`; the `p_k`,
`s`, `s'` have index degrees `-k`, `0`, `0`, and the `R_k` degree `-k`, so the substitution
produces a `w`-power times a polynomial in `(h, y)`:

* `kleinTwP a b h y k`  : `kleinP a b (fun i => w^i y i) k = w^(4*k) * kleinTwP a b (w^5) y k`
  (identical to `kleinTw` of `Work.MotV` / `MOTIVIC_S45_STATEMENTS.lean.txt` §0, verified);
* `kleinTwS a b h y`     : `kleinSec a b (fun i => w^i y i) = kleinTwS a b (w^5) y`;
* `kleinTwSDual a b h y` : `kleinSecDual a b (fun i => w^i y i) = kleinTwSDual a b (w^5) y`;
* `kleinTwR a b h y k`   : `kleinR a b (fun i => w^(4*i) y i) k = w^k * kleinTwR a b (w^5) y k`
  (note the *inverse* twist `z_j = w^(4j) z_j` here: it is the convention under which the
  twisted quadro-cubic identity I1' `kleinTwR_k (kleinTwP) = kleinTwS * y_k` holds; both are
  verified in `cas/s08_twist.py`, `cas/s09_twfix.py`).

These are the data over `K = 𝕜(t)` for the twisted Crauder--Katz link (audit node **K2_T**,
`MOTIVIC_S45_LEAD.md` §6), the T-twist analogue of the split identities of `KleinIdents`.
Computed by `cas/s08_twist.py`; the twisted identity I1'
`kleinTwR_k (kleinTwP) = kleinTwS * y_k` was verified there.

Index arithmetic: `4*k` is in `Fin 5` (`w^5 = h`), matching `kleinTw_subst`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace Work.MotK

variable {R : Type*} [CommRing R]

/-- The twisted Pfaffian `p_0` (the `kleinTw` of `Work.MotV`). -/
def kleinTwP0 (a b h : R) (y : Fin 5 → R) : R :=
  -a*b*(y 0)^(2:ℕ) + a^(2:ℕ)*h*y 2*y 3 - b^(2:ℕ)*h*y 1*y 4

/-- The twisted Pfaffian `p_1` (the `kleinTw` of `Work.MotV`). -/
def kleinTwP1 (a b h : R) (y : Fin 5 → R) : R :=
  -a*b*(y 2)^(2:ℕ) + a^(2:ℕ)*y 0*y 4 - b^(2:ℕ)*y 1*y 3

/-- The twisted Pfaffian `p_2` (the `kleinTw` of `Work.MotV`). -/
def kleinTwP2 (a b h : R) (y : Fin 5 → R) : R :=
  -a*b*h*(y 4)^(2:ℕ) + a^(2:ℕ)*y 1*y 2 - b^(2:ℕ)*y 0*y 3

/-- The twisted Pfaffian `p_3` (the `kleinTw` of `Work.MotV`). -/
def kleinTwP3 (a b h : R) (y : Fin 5 → R) : R :=
  -a*b*(y 1)^(2:ℕ) + a^(2:ℕ)*h*y 3*y 4 - b^(2:ℕ)*y 0*y 2

/-- The twisted Pfaffian `p_4` (the `kleinTw` of `Work.MotV`). -/
def kleinTwP4 (a b h : R) (y : Fin 5 → R) : R :=
  -a*b*h*(y 3)^(2:ℕ) + a^(2:ℕ)*y 0*y 1 - b^(2:ℕ)*h*y 2*y 4

/-- The five twisted Pfaffians. -/
def kleinTwP (a b h : R) (y : Fin 5 → R) : Fin 5 → R :=
  ![kleinTwP0 a b h y, kleinTwP1 a b h y, kleinTwP2 a b h y, kleinTwP3 a b h y, kleinTwP4 a b h y]

/-- The twisted secant quintic `s`. -/
def kleinTwS (a b h : R) (y : Fin 5 → R) : R :=
  16*a^(5:ℕ)*b^(5:ℕ)*h^(2:ℕ)*y 0*y 1*y 2*y 3*y 4 - 2*a^(3:ℕ)*b^(7:ℕ)*h*(y 0)^(2:ℕ)*y 1*(y 2)^(2:ℕ) - 2*a^(3:ℕ)*b^(7:ℕ)*h^(2:ℕ)*(y 0)^(2:ℕ)*(y 3)^(2:ℕ)*y 4 - 2*a^(3:ℕ)*b^(7:ℕ)*h^(2:ℕ)*(y 1)^(2:ℕ)*y 2*(y 3)^(2:ℕ) - 2*a^(3:ℕ)*b^(7:ℕ)*h^(2:ℕ)*y 0*(y 1)^(2:ℕ)*(y 4)^(2:ℕ) - 2*a^(3:ℕ)*b^(7:ℕ)*h^(3:ℕ)*(y 2)^(2:ℕ)*y 3*(y 4)^(2:ℕ) - 2*a^(7:ℕ)*b^(3:ℕ)*h*(y 0)^(2:ℕ)*(y 1)^(2:ℕ)*y 3 - 2*a^(7:ℕ)*b^(3:ℕ)*h^(2:ℕ)*(y 0)^(2:ℕ)*y 2*(y 4)^(2:ℕ) - 2*a^(7:ℕ)*b^(3:ℕ)*h^(2:ℕ)*(y 1)^(2:ℕ)*(y 2)^(2:ℕ)*y 4 - 2*a^(7:ℕ)*b^(3:ℕ)*h^(2:ℕ)*y 0*(y 2)^(2:ℕ)*(y 3)^(2:ℕ) - 2*a^(7:ℕ)*b^(3:ℕ)*h^(3:ℕ)*y 1*(y 3)^(2:ℕ)*(y 4)^(2:ℕ) - 3*a^(4:ℕ)*b^(6:ℕ)*h*(y 0)^(3:ℕ)*y 1*y 4 - 3*a^(4:ℕ)*b^(6:ℕ)*h*y 0*(y 1)^(3:ℕ)*y 2 - 3*a^(4:ℕ)*b^(6:ℕ)*h^(2:ℕ)*y 1*(y 2)^(3:ℕ)*y 3 - 3*a^(4:ℕ)*b^(6:ℕ)*h^(3:ℕ)*y 0*y 3*(y 4)^(3:ℕ) - 3*a^(4:ℕ)*b^(6:ℕ)*h^(3:ℕ)*y 2*(y 3)^(3:ℕ)*y 4 + 3*a^(6:ℕ)*b^(4:ℕ)*h*(y 0)^(3:ℕ)*y 2*y 3 + 3*a^(6:ℕ)*b^(4:ℕ)*h^(2:ℕ)*(y 1)^(3:ℕ)*y 3*y 4 + 3*a^(6:ℕ)*b^(4:ℕ)*h^(2:ℕ)*y 0*(y 2)^(3:ℕ)*y 4 + 3*a^(6:ℕ)*b^(4:ℕ)*h^(2:ℕ)*y 0*y 1*(y 3)^(3:ℕ) + 3*a^(6:ℕ)*b^(4:ℕ)*h^(3:ℕ)*y 1*y 2*(y 4)^(3:ℕ) + a*b^(9:ℕ)*h*(y 0)^(3:ℕ)*y 2*y 3 + a*b^(9:ℕ)*h^(2:ℕ)*(y 1)^(3:ℕ)*y 3*y 4 + a*b^(9:ℕ)*h^(2:ℕ)*y 0*(y 2)^(3:ℕ)*y 4 + a*b^(9:ℕ)*h^(2:ℕ)*y 0*y 1*(y 3)^(3:ℕ) + a*b^(9:ℕ)*h^(3:ℕ)*y 1*y 2*(y 4)^(3:ℕ) - a^(10:ℕ)*h^(2:ℕ)*y 0*y 1*y 2*y 3*y 4 + a^(2:ℕ)*b^(8:ℕ)*h*(y 0)^(2:ℕ)*(y 1)^(2:ℕ)*y 3 + a^(2:ℕ)*b^(8:ℕ)*h^(2:ℕ)*(y 0)^(2:ℕ)*y 2*(y 4)^(2:ℕ) + a^(2:ℕ)*b^(8:ℕ)*h^(2:ℕ)*(y 1)^(2:ℕ)*(y 2)^(2:ℕ)*y 4 + a^(2:ℕ)*b^(8:ℕ)*h^(2:ℕ)*y 0*(y 2)^(2:ℕ)*(y 3)^(2:ℕ) + a^(2:ℕ)*b^(8:ℕ)*h^(3:ℕ)*y 1*(y 3)^(2:ℕ)*(y 4)^(2:ℕ) - a^(5:ℕ)*b^(5:ℕ)*(y 0)^(5:ℕ) - a^(5:ℕ)*b^(5:ℕ)*h*(y 1)^(5:ℕ) - a^(5:ℕ)*b^(5:ℕ)*h^(2:ℕ)*(y 2)^(5:ℕ) - a^(5:ℕ)*b^(5:ℕ)*h^(3:ℕ)*(y 3)^(5:ℕ) - a^(5:ℕ)*b^(5:ℕ)*h^(4:ℕ)*(y 4)^(5:ℕ) - a^(8:ℕ)*b^(2:ℕ)*h*(y 0)^(2:ℕ)*y 1*(y 2)^(2:ℕ) - a^(8:ℕ)*b^(2:ℕ)*h^(2:ℕ)*(y 0)^(2:ℕ)*(y 3)^(2:ℕ)*y 4 - a^(8:ℕ)*b^(2:ℕ)*h^(2:ℕ)*(y 1)^(2:ℕ)*y 2*(y 3)^(2:ℕ) - a^(8:ℕ)*b^(2:ℕ)*h^(2:ℕ)*y 0*(y 1)^(2:ℕ)*(y 4)^(2:ℕ) - a^(8:ℕ)*b^(2:ℕ)*h^(3:ℕ)*(y 2)^(2:ℕ)*y 3*(y 4)^(2:ℕ) + a^(9:ℕ)*b*h*(y 0)^(3:ℕ)*y 1*y 4 + a^(9:ℕ)*b*h*y 0*(y 1)^(3:ℕ)*y 2 + a^(9:ℕ)*b*h^(2:ℕ)*y 1*(y 2)^(3:ℕ)*y 3 + a^(9:ℕ)*b*h^(3:ℕ)*y 0*y 3*(y 4)^(3:ℕ) + a^(9:ℕ)*b*h^(3:ℕ)*y 2*(y 3)^(3:ℕ)*y 4 + b^(10:ℕ)*h^(2:ℕ)*y 0*y 1*y 2*y 3*y 4

/-- The twisted dual secant quintic `s'`. -/
def kleinTwSDual (a b h : R) (y : Fin 5 → R) : R :=
  2*a^(3:ℕ)*b^(7:ℕ)*h*(y 0)^(3:ℕ)*y 2*y 3 + 2*a^(3:ℕ)*b^(7:ℕ)*h^(2:ℕ)*(y 1)^(3:ℕ)*y 3*y 4 + 2*a^(3:ℕ)*b^(7:ℕ)*h^(2:ℕ)*y 0*(y 2)^(3:ℕ)*y 4 + 2*a^(3:ℕ)*b^(7:ℕ)*h^(2:ℕ)*y 0*y 1*(y 3)^(3:ℕ) + 2*a^(3:ℕ)*b^(7:ℕ)*h^(3:ℕ)*y 1*y 2*(y 4)^(3:ℕ) + 2*a^(7:ℕ)*b^(3:ℕ)*h*(y 0)^(3:ℕ)*y 1*y 4 + 2*a^(7:ℕ)*b^(3:ℕ)*h*y 0*(y 1)^(3:ℕ)*y 2 + 2*a^(7:ℕ)*b^(3:ℕ)*h^(2:ℕ)*y 1*(y 2)^(3:ℕ)*y 3 + 2*a^(7:ℕ)*b^(3:ℕ)*h^(3:ℕ)*y 0*y 3*(y 4)^(3:ℕ) + 2*a^(7:ℕ)*b^(3:ℕ)*h^(3:ℕ)*y 2*(y 3)^(3:ℕ)*y 4 + 3*a^(4:ℕ)*b^(6:ℕ)*h*(y 0)^(2:ℕ)*y 1*(y 2)^(2:ℕ) + 3*a^(4:ℕ)*b^(6:ℕ)*h^(2:ℕ)*(y 0)^(2:ℕ)*(y 3)^(2:ℕ)*y 4 + 3*a^(4:ℕ)*b^(6:ℕ)*h^(2:ℕ)*(y 1)^(2:ℕ)*y 2*(y 3)^(2:ℕ) + 3*a^(4:ℕ)*b^(6:ℕ)*h^(2:ℕ)*y 0*(y 1)^(2:ℕ)*(y 4)^(2:ℕ) + 3*a^(4:ℕ)*b^(6:ℕ)*h^(3:ℕ)*(y 2)^(2:ℕ)*y 3*(y 4)^(2:ℕ) - 3*a^(6:ℕ)*b^(4:ℕ)*h*(y 0)^(2:ℕ)*(y 1)^(2:ℕ)*y 3 - 3*a^(6:ℕ)*b^(4:ℕ)*h^(2:ℕ)*(y 0)^(2:ℕ)*y 2*(y 4)^(2:ℕ) - 3*a^(6:ℕ)*b^(4:ℕ)*h^(2:ℕ)*(y 1)^(2:ℕ)*(y 2)^(2:ℕ)*y 4 - 3*a^(6:ℕ)*b^(4:ℕ)*h^(2:ℕ)*y 0*(y 2)^(2:ℕ)*(y 3)^(2:ℕ) - 3*a^(6:ℕ)*b^(4:ℕ)*h^(3:ℕ)*y 1*(y 3)^(2:ℕ)*(y 4)^(2:ℕ) - 6*a^(5:ℕ)*b^(5:ℕ)*h^(2:ℕ)*y 0*y 1*y 2*y 3*y 4 - a*b^(9:ℕ)*h*(y 0)^(2:ℕ)*(y 1)^(2:ℕ)*y 3 - a*b^(9:ℕ)*h^(2:ℕ)*(y 0)^(2:ℕ)*y 2*(y 4)^(2:ℕ) - a*b^(9:ℕ)*h^(2:ℕ)*(y 1)^(2:ℕ)*(y 2)^(2:ℕ)*y 4 - a*b^(9:ℕ)*h^(2:ℕ)*y 0*(y 2)^(2:ℕ)*(y 3)^(2:ℕ) - a*b^(9:ℕ)*h^(3:ℕ)*y 1*(y 3)^(2:ℕ)*(y 4)^(2:ℕ) + a^(10:ℕ)*h^(2:ℕ)*y 0*y 1*y 2*y 3*y 4 - a^(2:ℕ)*b^(8:ℕ)*h*(y 0)^(3:ℕ)*y 1*y 4 - a^(2:ℕ)*b^(8:ℕ)*h*y 0*(y 1)^(3:ℕ)*y 2 - a^(2:ℕ)*b^(8:ℕ)*h^(2:ℕ)*y 1*(y 2)^(3:ℕ)*y 3 - a^(2:ℕ)*b^(8:ℕ)*h^(3:ℕ)*y 0*y 3*(y 4)^(3:ℕ) - a^(2:ℕ)*b^(8:ℕ)*h^(3:ℕ)*y 2*(y 3)^(3:ℕ)*y 4 - a^(5:ℕ)*b^(5:ℕ)*(y 0)^(5:ℕ) - a^(5:ℕ)*b^(5:ℕ)*h*(y 1)^(5:ℕ) - a^(5:ℕ)*b^(5:ℕ)*h^(2:ℕ)*(y 2)^(5:ℕ) - a^(5:ℕ)*b^(5:ℕ)*h^(3:ℕ)*(y 3)^(5:ℕ) - a^(5:ℕ)*b^(5:ℕ)*h^(4:ℕ)*(y 4)^(5:ℕ) + a^(8:ℕ)*b^(2:ℕ)*h*(y 0)^(3:ℕ)*y 2*y 3 + a^(8:ℕ)*b^(2:ℕ)*h^(2:ℕ)*(y 1)^(3:ℕ)*y 3*y 4 + a^(8:ℕ)*b^(2:ℕ)*h^(2:ℕ)*y 0*(y 2)^(3:ℕ)*y 4 + a^(8:ℕ)*b^(2:ℕ)*h^(2:ℕ)*y 0*y 1*(y 3)^(3:ℕ) + a^(8:ℕ)*b^(2:ℕ)*h^(3:ℕ)*y 1*y 2*(y 4)^(3:ℕ) - a^(9:ℕ)*b*h*(y 0)^(2:ℕ)*y 1*(y 2)^(2:ℕ) - a^(9:ℕ)*b*h^(2:ℕ)*(y 0)^(2:ℕ)*(y 3)^(2:ℕ)*y 4 - a^(9:ℕ)*b*h^(2:ℕ)*(y 1)^(2:ℕ)*y 2*(y 3)^(2:ℕ) - a^(9:ℕ)*b*h^(2:ℕ)*y 0*(y 1)^(2:ℕ)*(y 4)^(2:ℕ) - a^(9:ℕ)*b*h^(3:ℕ)*(y 2)^(2:ℕ)*y 3*(y 4)^(2:ℕ) - b^(10:ℕ)*h^(2:ℕ)*y 0*y 1*y 2*y 3*y 4

/-- The twisted inverse map `R_0`. -/
def kleinTwR0 (a b h : R) (y : Fin 5 → R) : R :=
  -a*b^(3:ℕ)*h*(y 3)^(2:ℕ)*y 4 - a*b^(3:ℕ)*h^(2:ℕ)*y 1*(y 2)^(2:ℕ) + a^(2:ℕ)*b^(2:ℕ)*(y 0)^(3:ℕ) + a^(3:ℕ)*b*h*y 2*(y 4)^(2:ℕ) + a^(3:ℕ)*b*h^(2:ℕ)*(y 1)^(2:ℕ)*y 3 - a^(4:ℕ)*h*y 0*y 1*y 4 - b^(4:ℕ)*h*y 0*y 2*y 3

/-- The twisted inverse map `R_1`. -/
def kleinTwR1 (a b h : R) (y : Fin 5 → R) : R :=
  -a*b^(3:ℕ)*(y 0)^(2:ℕ)*y 4 - a*b^(3:ℕ)*h^(2:ℕ)*(y 1)^(2:ℕ)*y 2 + a^(2:ℕ)*b^(2:ℕ)*h*(y 3)^(3:ℕ) + a^(3:ℕ)*b*h*y 0*(y 2)^(2:ℕ) + a^(3:ℕ)*b*h*y 1*(y 4)^(2:ℕ) - a^(4:ℕ)*h*y 2*y 3*y 4 - b^(4:ℕ)*h*y 0*y 1*y 3

/-- The twisted inverse map `R_2`. -/
def kleinTwR2 (a b h : R) (y : Fin 5 → R) : R :=
  -a*b^(3:ℕ)*h*y 2*(y 3)^(2:ℕ) - a*b^(3:ℕ)*y 0*(y 4)^(2:ℕ) + a^(2:ℕ)*b^(2:ℕ)*h^(2:ℕ)*(y 1)^(3:ℕ) + a^(3:ℕ)*b*(y 0)^(2:ℕ)*y 3 + a^(3:ℕ)*b*h*(y 2)^(2:ℕ)*y 4 - a^(4:ℕ)*h*y 0*y 1*y 2 - b^(4:ℕ)*h*y 1*y 3*y 4

/-- The twisted inverse map `R_3`. -/
def kleinTwR3 (a b h : R) (y : Fin 5 → R) : R :=
  -a*b^(3:ℕ)*h*(y 2)^(2:ℕ)*y 3 - a*b^(3:ℕ)*h*y 0*(y 1)^(2:ℕ) + a^(2:ℕ)*b^(2:ℕ)*(y 4)^(3:ℕ) + a^(3:ℕ)*b*(y 0)^(2:ℕ)*y 2 + a^(3:ℕ)*b*h*y 1*(y 3)^(2:ℕ) - a^(4:ℕ)*y 0*y 3*y 4 - b^(4:ℕ)*h*y 1*y 2*y 4

/-- The twisted inverse map `R_4`. -/
def kleinTwR4 (a b h : R) (y : Fin 5 → R) : R :=
  -a*b^(3:ℕ)*(y 0)^(2:ℕ)*y 1 - a*b^(3:ℕ)*y 3*(y 4)^(2:ℕ) + a^(2:ℕ)*b^(2:ℕ)*h*(y 2)^(3:ℕ) + a^(3:ℕ)*b*h*(y 1)^(2:ℕ)*y 4 + a^(3:ℕ)*b*y 0*(y 3)^(2:ℕ) - a^(4:ℕ)*h*y 1*y 2*y 3 - b^(4:ℕ)*y 0*y 2*y 4

/-- The five twisted cubics of the inverse map. -/
def kleinTwR (a b h : R) (y : Fin 5 → R) : Fin 5 → R :=
  ![kleinTwR0 a b h y, kleinTwR1 a b h y, kleinTwR2 a b h y, kleinTwR3 a b h y, kleinTwR4 a b h y]

end Work.MotK

