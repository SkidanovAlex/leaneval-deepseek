/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Klein--Fisher (Pfaffian) model of the elliptic normal quintic

Data layer of the area `Submission/Work/MotK`; its target is the explicit Crauder--Katz
quadro-cubic link of

* H.-Y. Lin, E. Shinder, *Motivic invariants of birational maps*, Ann. of Math. **199** (2024),

in the form designed in `MOTIVIC_AUDIT_LEAD.md` (audit nodes **K0**/**K1**) and in
`MOTIVIC_S45_LEAD.md` (T-twist).

## Conventions

* `kleinP a b x` is the 5-tuple of Pfaffians `p_0, …, p_4` of the skew matrix
  `M_{i j} = c_{j - i} x_{i + j}`, `c = (0, a, b, -b, -a)` (indices mod 5).  Its vanishing
  locus `C = V(p_0, …, p_4) ⊂ ℙ⁴` is the elliptic normal quintic `E_{a,b}`, and
  `kleinP` is the *birational* quadro-cubic Cremona map `ℙ⁴ ⇢ ℙ⁴` given by the net of
  quadrics through `C` (`C` is the scheme-theoretic intersection of those quadrics).
  Components: `kleinP0 … kleinP4`, with the `rfl` lemmas `kleinP_zero … kleinP_four`.
* `kleinQ a b x = ∑ k, p_k` is the shift-invariant quadric `Q ⊃ C`; `kleinShift` is the
  cyclic shift `x_i ↦ x_{i + 1}` (the Galois action of the S-twist).
* `kleinR a b z` is the inverse quadro-cubic map (5 cubic forms), `kleinSec a b x` (`s`)
  the *secant quintic* of `C`: `R_i (p(x)) = s(x) x_i` (node **K1**, I1);
  `kleinSecDual a b z` (`s'`): `p_i (R(z)) = s'(z) z_i` (I2).
* Secondary identities: I3 `s'(p(x)) = s(x)^2`, I4 `s(R(z)) = s'(z)^3`,
  I5 (`∂_i∂_j s ∈ (p_0, …, p_4)`, i.e. `mult_C(Sec C) ≥ 3`), `q_y`, `b_y` (stereographic
  parametrisation of `Q`) and `M · p = 0`.  See `KleinIdents.lean`.
* `kleinTw`/`twMon` in `Work.MotV` are the T-twist (Kummer coordinate) forms of the same
  Pfaffians: `kleinP a b (fun i => w^i y_i) k = w^{4k} kleinTw a b (w^5) y k` (proved in
  `Work.MotV`, `MOTIVIC_S45_STATEMENTS.lean.txt` §0).

All polynomials were computed with the CAS scripts in `Submission/Work/MotK/cas/`
(sympy over `ℤ[a,b]`, verified symbolically in `a, b`).

Everything is stated for a general commutative ring `R`, with `a b : R` and the coordinates
`x : Fin 5 → R` as *atoms*: the identities are polynomial identities with integer
coefficients, hence hold in every commutative ring and specialise by instantiating `R`
(to `𝕜`, to `𝕜[y]`, to `L ⊗ 𝕜[y]`, …).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotK

variable {R : Type*} [CommRing R]

/-- The Pfaffian quadric `p_0`. -/
def kleinP0 (a b : R) (x : Fin 5 → R) : R :=
  -a*b*(x 0)^(2:ℕ) + a^(2:ℕ)*x 2*x 3 - b^(2:ℕ)*x 1*x 4

/-- The Pfaffian quadric `p_1`. -/
def kleinP1 (a b : R) (x : Fin 5 → R) : R :=
  -a*b*(x 2)^(2:ℕ) + a^(2:ℕ)*x 0*x 4 - b^(2:ℕ)*x 1*x 3

/-- The Pfaffian quadric `p_2`. -/
def kleinP2 (a b : R) (x : Fin 5 → R) : R :=
  -a*b*(x 4)^(2:ℕ) + a^(2:ℕ)*x 1*x 2 - b^(2:ℕ)*x 0*x 3

/-- The Pfaffian quadric `p_3`. -/
def kleinP3 (a b : R) (x : Fin 5 → R) : R :=
  -a*b*(x 1)^(2:ℕ) + a^(2:ℕ)*x 3*x 4 - b^(2:ℕ)*x 0*x 2

/-- The Pfaffian quadric `p_4`. -/
def kleinP4 (a b : R) (x : Fin 5 → R) : R :=
  -a*b*(x 3)^(2:ℕ) + a^(2:ℕ)*x 0*x 1 - b^(2:ℕ)*x 2*x 4

/-- The five Pfaffian quadrics `p_0, …, p_4`. -/
def kleinP (a b : R) (x : Fin 5 → R) : Fin 5 → R :=
  ![kleinP0 a b x, kleinP1 a b x, kleinP2 a b x, kleinP3 a b x, kleinP4 a b x]

theorem kleinP_zero (a b : R) (x : Fin 5 → R) : kleinP a b x 0 = kleinP0 a b x := rfl
theorem kleinP_one (a b : R) (x : Fin 5 → R) : kleinP a b x 1 = kleinP1 a b x := rfl
theorem kleinP_two (a b : R) (x : Fin 5 → R) : kleinP a b x 2 = kleinP2 a b x := rfl
theorem kleinP_three (a b : R) (x : Fin 5 → R) : kleinP a b x 3 = kleinP3 a b x := rfl
theorem kleinP_four (a b : R) (x : Fin 5 → R) : kleinP a b x 4 = kleinP4 a b x := rfl

theorem kleinP_zero' (a b : R) (x : Fin 5 → R) (h : 0 < 5) :
    kleinP a b x ⟨0, h⟩ = kleinP0 a b x := rfl
theorem kleinP_one' (a b : R) (x : Fin 5 → R) (h : 1 < 5) :
    kleinP a b x ⟨1, h⟩ = kleinP1 a b x := rfl
theorem kleinP_two' (a b : R) (x : Fin 5 → R) (h : 2 < 5) :
    kleinP a b x ⟨2, h⟩ = kleinP2 a b x := rfl
theorem kleinP_three' (a b : R) (x : Fin 5 → R) (h : 3 < 5) :
    kleinP a b x ⟨3, h⟩ = kleinP3 a b x := rfl
theorem kleinP_four' (a b : R) (x : Fin 5 → R) (h : 4 < 5) :
    kleinP a b x ⟨4, h⟩ = kleinP4 a b x := rfl

/-- The shift-invariant quadric `q = ∑ k, p_k`. -/
def kleinQ (a b : R) (x : Fin 5 → R) : R :=
  kleinP0 a b x + kleinP1 a b x + kleinP2 a b x + kleinP3 a b x + kleinP4 a b x

theorem kleinQ_eq_sum (a b : R) (x : Fin 5 → R) :
    kleinQ a b x = ∑ k, kleinP a b x k := by
  simp only [kleinQ, kleinP, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  first | refl_ring1 | ring

/-- Row `0` of the matrix `M_{i j} = c_{j - i} x_{i + j}`. -/
def kleinM0 (a b : R) (x : Fin 5 → R) : Fin 5 → R :=
  ![0, a*(x 1), b*(x 2), -b*(x 3), -a*(x 4)]

/-- Row `1` of the matrix `M_{i j} = c_{j - i} x_{i + j}`. -/
def kleinM1 (a b : R) (x : Fin 5 → R) : Fin 5 → R :=
  ![-a*(x 1), 0, a*(x 3), b*(x 4), -b*(x 0)]

/-- Row `2` of the matrix `M_{i j} = c_{j - i} x_{i + j}`. -/
def kleinM2 (a b : R) (x : Fin 5 → R) : Fin 5 → R :=
  ![-b*(x 2), -a*(x 3), 0, a*(x 0), b*(x 1)]

/-- Row `3` of the matrix `M_{i j} = c_{j - i} x_{i + j}`. -/
def kleinM3 (a b : R) (x : Fin 5 → R) : Fin 5 → R :=
  ![b*(x 3), -b*(x 4), -a*(x 0), 0, a*(x 2)]

/-- Row `4` of the matrix `M_{i j} = c_{j - i} x_{i + j}`. -/
def kleinM4 (a b : R) (x : Fin 5 → R) : Fin 5 → R :=
  ![a*(x 4), b*(x 0), -b*(x 1), -a*(x 2), 0]

/-- The skew matrix `M_{i j} = c_{j - i} x_{i + j}`, `c = (0, a, b, -b, -a)`:
`kleinP` is its vector of Pfaffians, and `M · p = 0`. -/
def kleinM (a b : R) (x : Fin 5 → R) : Fin 5 → Fin 5 → R :=
  ![kleinM0 a b x, kleinM1 a b x, kleinM2 a b x, kleinM3 a b x, kleinM4 a b x]

theorem kleinM_zero (a b : R) (x : Fin 5 → R) :
    kleinM a b x 0 = kleinM0 a b x := rfl
theorem kleinM_one (a b : R) (x : Fin 5 → R) :
    kleinM a b x 1 = kleinM1 a b x := rfl
theorem kleinM_two (a b : R) (x : Fin 5 → R) :
    kleinM a b x 2 = kleinM2 a b x := rfl
theorem kleinM_three (a b : R) (x : Fin 5 → R) :
    kleinM a b x 3 = kleinM3 a b x := rfl
theorem kleinM_four (a b : R) (x : Fin 5 → R) :
    kleinM a b x 4 = kleinM4 a b x := rfl

theorem kleinM_zero' (a b : R) (x : Fin 5 → R) (h : 0 < 5) :
    kleinM a b x ⟨0, h⟩ = kleinM0 a b x := rfl
theorem kleinM_one' (a b : R) (x : Fin 5 → R) (h : 1 < 5) :
    kleinM a b x ⟨1, h⟩ = kleinM1 a b x := rfl
theorem kleinM_two' (a b : R) (x : Fin 5 → R) (h : 2 < 5) :
    kleinM a b x ⟨2, h⟩ = kleinM2 a b x := rfl
theorem kleinM_three' (a b : R) (x : Fin 5 → R) (h : 3 < 5) :
    kleinM a b x ⟨3, h⟩ = kleinM3 a b x := rfl
theorem kleinM_four' (a b : R) (x : Fin 5 → R) (h : 4 < 5) :
    kleinM a b x ⟨4, h⟩ = kleinM4 a b x := rfl

/-- The cyclic shift `x_i ↦ x_{i + 1}`. -/
def kleinShift (x : Fin 5 → R) : Fin 5 → R := ![x 1, x 2, x 3, x 4, x 0]

theorem kleinShift_zero (x : Fin 5 → R) : kleinShift x 0 = x 1 := rfl
theorem kleinShift_one (x : Fin 5 → R) : kleinShift x 1 = x 2 := rfl
theorem kleinShift_two (x : Fin 5 → R) : kleinShift x 2 = x 3 := rfl
theorem kleinShift_three (x : Fin 5 → R) : kleinShift x 3 = x 4 := rfl
theorem kleinShift_four (x : Fin 5 → R) : kleinShift x 4 = x 0 := rfl

theorem kleinShift_zero' (x : Fin 5 → R) (h : 0 < 5) :
    kleinShift x ⟨0, h⟩ = x 1 := rfl
theorem kleinShift_one' (x : Fin 5 → R) (h : 1 < 5) :
    kleinShift x ⟨1, h⟩ = x 2 := rfl
theorem kleinShift_two' (x : Fin 5 → R) (h : 2 < 5) :
    kleinShift x ⟨2, h⟩ = x 3 := rfl
theorem kleinShift_three' (x : Fin 5 → R) (h : 3 < 5) :
    kleinShift x ⟨3, h⟩ = x 4 := rfl
theorem kleinShift_four' (x : Fin 5 → R) (h : 4 < 5) :
    kleinShift x ⟨4, h⟩ = x 0 := rfl

/-- The cubic form `R_0` (component of the inverse quadro-cubic map). -/
def kleinR0 (a b : R) (z : Fin 5 → R) : R :=
  -a*b^(3:ℕ)*(z 3)^(2:ℕ)*z 4 - a*b^(3:ℕ)*z 1*(z 2)^(2:ℕ) + a^(2:ℕ)*b^(2:ℕ)*(z 0)^(3:ℕ) + a^(3:ℕ)*b*(z 1)^(2:ℕ)*z 3 + a^(3:ℕ)*b*z 2*(z 4)^(2:ℕ) - a^(4:ℕ)*z 0*z 1*z 4 - b^(4:ℕ)*z 0*z 2*z 3

/-- The cubic form `R_1` (component of the inverse quadro-cubic map). -/
def kleinR1 (a b : R) (z : Fin 5 → R) : R :=
  -a*b^(3:ℕ)*(z 0)^(2:ℕ)*z 4 - a*b^(3:ℕ)*(z 1)^(2:ℕ)*z 2 + a^(2:ℕ)*b^(2:ℕ)*(z 3)^(3:ℕ) + a^(3:ℕ)*b*z 0*(z 2)^(2:ℕ) + a^(3:ℕ)*b*z 1*(z 4)^(2:ℕ) - a^(4:ℕ)*z 2*z 3*z 4 - b^(4:ℕ)*z 0*z 1*z 3

/-- The cubic form `R_2` (component of the inverse quadro-cubic map). -/
def kleinR2 (a b : R) (z : Fin 5 → R) : R :=
  -a*b^(3:ℕ)*z 0*(z 4)^(2:ℕ) - a*b^(3:ℕ)*z 2*(z 3)^(2:ℕ) + a^(2:ℕ)*b^(2:ℕ)*(z 1)^(3:ℕ) + a^(3:ℕ)*b*(z 0)^(2:ℕ)*z 3 + a^(3:ℕ)*b*(z 2)^(2:ℕ)*z 4 - a^(4:ℕ)*z 0*z 1*z 2 - b^(4:ℕ)*z 1*z 3*z 4

/-- The cubic form `R_3` (component of the inverse quadro-cubic map). -/
def kleinR3 (a b : R) (z : Fin 5 → R) : R :=
  -a*b^(3:ℕ)*(z 2)^(2:ℕ)*z 3 - a*b^(3:ℕ)*z 0*(z 1)^(2:ℕ) + a^(2:ℕ)*b^(2:ℕ)*(z 4)^(3:ℕ) + a^(3:ℕ)*b*(z 0)^(2:ℕ)*z 2 + a^(3:ℕ)*b*z 1*(z 3)^(2:ℕ) - a^(4:ℕ)*z 0*z 3*z 4 - b^(4:ℕ)*z 1*z 2*z 4

/-- The cubic form `R_4` (component of the inverse quadro-cubic map). -/
def kleinR4 (a b : R) (z : Fin 5 → R) : R :=
  -a*b^(3:ℕ)*(z 0)^(2:ℕ)*z 1 - a*b^(3:ℕ)*z 3*(z 4)^(2:ℕ) + a^(2:ℕ)*b^(2:ℕ)*(z 2)^(3:ℕ) + a^(3:ℕ)*b*(z 1)^(2:ℕ)*z 4 + a^(3:ℕ)*b*z 0*(z 3)^(2:ℕ) - a^(4:ℕ)*z 1*z 2*z 3 - b^(4:ℕ)*z 0*z 2*z 4

/-- The inverse quadro-cubic map `R` (five cubic forms). -/
def kleinR (a b : R) (z : Fin 5 → R) : Fin 5 → R :=
  ![kleinR0 a b z, kleinR1 a b z, kleinR2 a b z, kleinR3 a b z, kleinR4 a b z]

theorem kleinR_zero (a b : R) (z : Fin 5 → R) : kleinR a b z 0 = kleinR0 a b z := rfl
theorem kleinR_one (a b : R) (z : Fin 5 → R) : kleinR a b z 1 = kleinR1 a b z := rfl
theorem kleinR_two (a b : R) (z : Fin 5 → R) : kleinR a b z 2 = kleinR2 a b z := rfl
theorem kleinR_three (a b : R) (z : Fin 5 → R) : kleinR a b z 3 = kleinR3 a b z := rfl
theorem kleinR_four (a b : R) (z : Fin 5 → R) : kleinR a b z 4 = kleinR4 a b z := rfl

theorem kleinR_zero' (a b : R) (z : Fin 5 → R) (h : 0 < 5) :
    kleinR a b z ⟨0, h⟩ = kleinR0 a b z := rfl
theorem kleinR_one' (a b : R) (z : Fin 5 → R) (h : 1 < 5) :
    kleinR a b z ⟨1, h⟩ = kleinR1 a b z := rfl
theorem kleinR_two' (a b : R) (z : Fin 5 → R) (h : 2 < 5) :
    kleinR a b z ⟨2, h⟩ = kleinR2 a b z := rfl
theorem kleinR_three' (a b : R) (z : Fin 5 → R) (h : 3 < 5) :
    kleinR a b z ⟨3, h⟩ = kleinR3 a b z := rfl
theorem kleinR_four' (a b : R) (z : Fin 5 → R) (h : 4 < 5) :
    kleinR a b z ⟨4, h⟩ = kleinR4 a b z := rfl

/-- The secant quintic `s` of `C` (the equation of `Sym² C ⊂ ℙ⁴`). -/
def kleinSec (a b : R) (x : Fin 5 → R) : R :=
  16*a^(5:ℕ)*b^(5:ℕ)*x 0*x 1*x 2*x 3*x 4 - 2*a^(3:ℕ)*b^(7:ℕ)*(x 0)^(2:ℕ)*(x 3)^(2:ℕ)*x 4 - 2*a^(3:ℕ)*b^(7:ℕ)*(x 0)^(2:ℕ)*x 1*(x 2)^(2:ℕ) - 2*a^(3:ℕ)*b^(7:ℕ)*(x 1)^(2:ℕ)*x 2*(x 3)^(2:ℕ) - 2*a^(3:ℕ)*b^(7:ℕ)*(x 2)^(2:ℕ)*x 3*(x 4)^(2:ℕ) - 2*a^(3:ℕ)*b^(7:ℕ)*x 0*(x 1)^(2:ℕ)*(x 4)^(2:ℕ) - 2*a^(7:ℕ)*b^(3:ℕ)*(x 0)^(2:ℕ)*(x 1)^(2:ℕ)*x 3 - 2*a^(7:ℕ)*b^(3:ℕ)*(x 0)^(2:ℕ)*x 2*(x 4)^(2:ℕ) - 2*a^(7:ℕ)*b^(3:ℕ)*(x 1)^(2:ℕ)*(x 2)^(2:ℕ)*x 4 - 2*a^(7:ℕ)*b^(3:ℕ)*x 0*(x 2)^(2:ℕ)*(x 3)^(2:ℕ) - 2*a^(7:ℕ)*b^(3:ℕ)*x 1*(x 3)^(2:ℕ)*(x 4)^(2:ℕ) - 3*a^(4:ℕ)*b^(6:ℕ)*(x 0)^(3:ℕ)*x 1*x 4 - 3*a^(4:ℕ)*b^(6:ℕ)*x 0*(x 1)^(3:ℕ)*x 2 - 3*a^(4:ℕ)*b^(6:ℕ)*x 0*x 3*(x 4)^(3:ℕ) - 3*a^(4:ℕ)*b^(6:ℕ)*x 1*(x 2)^(3:ℕ)*x 3 - 3*a^(4:ℕ)*b^(6:ℕ)*x 2*(x 3)^(3:ℕ)*x 4 + 3*a^(6:ℕ)*b^(4:ℕ)*(x 0)^(3:ℕ)*x 2*x 3 + 3*a^(6:ℕ)*b^(4:ℕ)*(x 1)^(3:ℕ)*x 3*x 4 + 3*a^(6:ℕ)*b^(4:ℕ)*x 0*(x 2)^(3:ℕ)*x 4 + 3*a^(6:ℕ)*b^(4:ℕ)*x 0*x 1*(x 3)^(3:ℕ) + 3*a^(6:ℕ)*b^(4:ℕ)*x 1*x 2*(x 4)^(3:ℕ) + a*b^(9:ℕ)*(x 0)^(3:ℕ)*x 2*x 3 + a*b^(9:ℕ)*(x 1)^(3:ℕ)*x 3*x 4 + a*b^(9:ℕ)*x 0*(x 2)^(3:ℕ)*x 4 + a*b^(9:ℕ)*x 0*x 1*(x 3)^(3:ℕ) + a*b^(9:ℕ)*x 1*x 2*(x 4)^(3:ℕ) - a^(10:ℕ)*x 0*x 1*x 2*x 3*x 4 + a^(2:ℕ)*b^(8:ℕ)*(x 0)^(2:ℕ)*(x 1)^(2:ℕ)*x 3 + a^(2:ℕ)*b^(8:ℕ)*(x 0)^(2:ℕ)*x 2*(x 4)^(2:ℕ) + a^(2:ℕ)*b^(8:ℕ)*(x 1)^(2:ℕ)*(x 2)^(2:ℕ)*x 4 + a^(2:ℕ)*b^(8:ℕ)*x 0*(x 2)^(2:ℕ)*(x 3)^(2:ℕ) + a^(2:ℕ)*b^(8:ℕ)*x 1*(x 3)^(2:ℕ)*(x 4)^(2:ℕ) - a^(5:ℕ)*b^(5:ℕ)*(x 0)^(5:ℕ) - a^(5:ℕ)*b^(5:ℕ)*(x 1)^(5:ℕ) - a^(5:ℕ)*b^(5:ℕ)*(x 2)^(5:ℕ) - a^(5:ℕ)*b^(5:ℕ)*(x 3)^(5:ℕ) - a^(5:ℕ)*b^(5:ℕ)*(x 4)^(5:ℕ) - a^(8:ℕ)*b^(2:ℕ)*(x 0)^(2:ℕ)*(x 3)^(2:ℕ)*x 4 - a^(8:ℕ)*b^(2:ℕ)*(x 0)^(2:ℕ)*x 1*(x 2)^(2:ℕ) - a^(8:ℕ)*b^(2:ℕ)*(x 1)^(2:ℕ)*x 2*(x 3)^(2:ℕ) - a^(8:ℕ)*b^(2:ℕ)*(x 2)^(2:ℕ)*x 3*(x 4)^(2:ℕ) - a^(8:ℕ)*b^(2:ℕ)*x 0*(x 1)^(2:ℕ)*(x 4)^(2:ℕ) + a^(9:ℕ)*b*(x 0)^(3:ℕ)*x 1*x 4 + a^(9:ℕ)*b*x 0*(x 1)^(3:ℕ)*x 2 + a^(9:ℕ)*b*x 0*x 3*(x 4)^(3:ℕ) + a^(9:ℕ)*b*x 1*(x 2)^(3:ℕ)*x 3 + a^(9:ℕ)*b*x 2*(x 3)^(3:ℕ)*x 4 + b^(10:ℕ)*x 0*x 1*x 2*x 3*x 4

/-- The dual secant quintic `s'` on the target side. -/
def kleinSecDual (a b : R) (z : Fin 5 → R) : R :=
  2*a^(3:ℕ)*b^(7:ℕ)*(z 0)^(3:ℕ)*z 2*z 3 + 2*a^(3:ℕ)*b^(7:ℕ)*(z 1)^(3:ℕ)*z 3*z 4 + 2*a^(3:ℕ)*b^(7:ℕ)*z 0*(z 2)^(3:ℕ)*z 4 + 2*a^(3:ℕ)*b^(7:ℕ)*z 0*z 1*(z 3)^(3:ℕ) + 2*a^(3:ℕ)*b^(7:ℕ)*z 1*z 2*(z 4)^(3:ℕ) + 2*a^(7:ℕ)*b^(3:ℕ)*(z 0)^(3:ℕ)*z 1*z 4 + 2*a^(7:ℕ)*b^(3:ℕ)*z 0*(z 1)^(3:ℕ)*z 2 + 2*a^(7:ℕ)*b^(3:ℕ)*z 0*z 3*(z 4)^(3:ℕ) + 2*a^(7:ℕ)*b^(3:ℕ)*z 1*(z 2)^(3:ℕ)*z 3 + 2*a^(7:ℕ)*b^(3:ℕ)*z 2*(z 3)^(3:ℕ)*z 4 + 3*a^(4:ℕ)*b^(6:ℕ)*(z 0)^(2:ℕ)*(z 3)^(2:ℕ)*z 4 + 3*a^(4:ℕ)*b^(6:ℕ)*(z 0)^(2:ℕ)*z 1*(z 2)^(2:ℕ) + 3*a^(4:ℕ)*b^(6:ℕ)*(z 1)^(2:ℕ)*z 2*(z 3)^(2:ℕ) + 3*a^(4:ℕ)*b^(6:ℕ)*(z 2)^(2:ℕ)*z 3*(z 4)^(2:ℕ) + 3*a^(4:ℕ)*b^(6:ℕ)*z 0*(z 1)^(2:ℕ)*(z 4)^(2:ℕ) - 3*a^(6:ℕ)*b^(4:ℕ)*(z 0)^(2:ℕ)*(z 1)^(2:ℕ)*z 3 - 3*a^(6:ℕ)*b^(4:ℕ)*(z 0)^(2:ℕ)*z 2*(z 4)^(2:ℕ) - 3*a^(6:ℕ)*b^(4:ℕ)*(z 1)^(2:ℕ)*(z 2)^(2:ℕ)*z 4 - 3*a^(6:ℕ)*b^(4:ℕ)*z 0*(z 2)^(2:ℕ)*(z 3)^(2:ℕ) - 3*a^(6:ℕ)*b^(4:ℕ)*z 1*(z 3)^(2:ℕ)*(z 4)^(2:ℕ) - 6*a^(5:ℕ)*b^(5:ℕ)*z 0*z 1*z 2*z 3*z 4 - a*b^(9:ℕ)*(z 0)^(2:ℕ)*(z 1)^(2:ℕ)*z 3 - a*b^(9:ℕ)*(z 0)^(2:ℕ)*z 2*(z 4)^(2:ℕ) - a*b^(9:ℕ)*(z 1)^(2:ℕ)*(z 2)^(2:ℕ)*z 4 - a*b^(9:ℕ)*z 0*(z 2)^(2:ℕ)*(z 3)^(2:ℕ) - a*b^(9:ℕ)*z 1*(z 3)^(2:ℕ)*(z 4)^(2:ℕ) + a^(10:ℕ)*z 0*z 1*z 2*z 3*z 4 - a^(2:ℕ)*b^(8:ℕ)*(z 0)^(3:ℕ)*z 1*z 4 - a^(2:ℕ)*b^(8:ℕ)*z 0*(z 1)^(3:ℕ)*z 2 - a^(2:ℕ)*b^(8:ℕ)*z 0*z 3*(z 4)^(3:ℕ) - a^(2:ℕ)*b^(8:ℕ)*z 1*(z 2)^(3:ℕ)*z 3 - a^(2:ℕ)*b^(8:ℕ)*z 2*(z 3)^(3:ℕ)*z 4 - a^(5:ℕ)*b^(5:ℕ)*(z 0)^(5:ℕ) - a^(5:ℕ)*b^(5:ℕ)*(z 1)^(5:ℕ) - a^(5:ℕ)*b^(5:ℕ)*(z 2)^(5:ℕ) - a^(5:ℕ)*b^(5:ℕ)*(z 3)^(5:ℕ) - a^(5:ℕ)*b^(5:ℕ)*(z 4)^(5:ℕ) + a^(8:ℕ)*b^(2:ℕ)*(z 0)^(3:ℕ)*z 2*z 3 + a^(8:ℕ)*b^(2:ℕ)*(z 1)^(3:ℕ)*z 3*z 4 + a^(8:ℕ)*b^(2:ℕ)*z 0*(z 2)^(3:ℕ)*z 4 + a^(8:ℕ)*b^(2:ℕ)*z 0*z 1*(z 3)^(3:ℕ) + a^(8:ℕ)*b^(2:ℕ)*z 1*z 2*(z 4)^(3:ℕ) - a^(9:ℕ)*b*(z 0)^(2:ℕ)*(z 3)^(2:ℕ)*z 4 - a^(9:ℕ)*b*(z 0)^(2:ℕ)*z 1*(z 2)^(2:ℕ) - a^(9:ℕ)*b*(z 1)^(2:ℕ)*z 2*(z 3)^(2:ℕ) - a^(9:ℕ)*b*(z 2)^(2:ℕ)*z 3*(z 4)^(2:ℕ) - a^(9:ℕ)*b*z 0*(z 1)^(2:ℕ)*(z 4)^(2:ℕ) - b^(10:ℕ)*z 0*z 1*z 2*z 3*z 4

/-- The polar bilinear form of `q`: `b(u, v) = q(u + v) - q(u) - q(v)`. -/
def kleinBilin (a b : R) (u v : Fin 5 → R) : R :=
  kleinQ a b (u + v) - kleinQ a b u - kleinQ a b v

/-- Inverse stereographic projection from `p ∈ Q`: `y(v) = q(v) · p - b(p, v) · v`. -/
def kleinStereo (a b : R) (p v : Fin 5 → R) : Fin 5 → R :=
  fun i => kleinQ a b v * p i - kleinBilin a b p v * v i

end Work.MotK

