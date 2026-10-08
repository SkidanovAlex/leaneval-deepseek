/-
# The matrix model of the Bender–Suzuki group of case c

Peterfalvi II, Ch. VI §3 identifies `Q = S₁ = {(x,y)}` with the group of upper
unitriangular matrices over `E = GF(q²)` fixing the anti-diagonal Hermitian form
`J = !![0,0,1; 0,1,0; 1,0,0]`:

`(x,y) ↦ A(x,y) = !![1, x, y; 0, 1, σ x; 0, 0, 1]`,

where `σ` is the `q`-power Frobenius.  This file sets up the matrices; the
computation of the multiplicativity, of the Hermitian condition, of the determinant
and of the conjugation by the Weyl element `J` are stated for the fleet.

Main objects:

* `Work.PSU3.hermMat` — the anti-diagonal form `J`;
* `Work.PSU3.hermConj` — the Hermitian transpose `A^H`, `(A^H)_{ij} = σ(A_{ji})`;
* `Work.PSU3.matOfXY x y` — the unitriangular matrix `A(x,y)`;
* `Work.PSU3.matFun p` — the same for `p : SZ E`;
* `Work.PSU3.weylMat` — the Weyl involution `t = J`.
-/
import Submission.Work.PSU3.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.PSU3

open Matrix

variable {E : Type*} [Field E] [FrobeniusInvolution E]

/-- The anti-diagonal Hermitian form `J = !![0,0,1; 0,1,0; 1,0,0]`.  It is also the
matrix of the Weyl involution `t` of `PSU(3,q)` (`Work.PSU3.weylMat`). -/
def hermMat : Matrix (Fin 3) (Fin 3) E := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

/-- The Hermitian transpose `A^H`, defined by `(A^H)_{ij} = σ(A_{ji})`. -/
def hermConj (A : Matrix (Fin 3) (Fin 3) E) : Matrix (Fin 3) (Fin 3) E :=
  A.transpose.map σE

/-- The unitriangular matrix `A(x,y) = !![1,x,y; 0,1,σx; 0,0,1]` attached to the pair
`(x,y)`. -/
def matOfXY (x y : E) : Matrix (Fin 3) (Fin 3) E := !![1, x, y; 0, 1, σE x; 0, 0, 1]

/-- The unitriangular matrix of an element of the group `SZ`. -/
def matFun (p : SZ E) : Matrix (Fin 3) (Fin 3) E := matOfXY p.x p.y

/-- The Weyl involution `t`, equal to the anti-diagonal matrix `J`. -/
abbrev weylMat : Matrix (Fin 3) (Fin 3) E := hermMat

/-- The upper unitriangular-ish matrix occurring in the factorisation of the Weyl
conjugate of `A(x,y)` (see `Work.PSU3.weylConj_matOfXY`):
`!![(σ y)⁻¹, x/y, 1; 0, σ y / y, σ x; 0, 0, y]`. -/
def weylFactor (x y : E) : Matrix (Fin 3) (Fin 3) E :=
  !![(σE y)⁻¹, x / y, 1; 0, σE y / y, σE x; 0, 0, y]

@[simp] lemma matOfXY_apply_00 (x y : E) : matOfXY x y 0 0 = 1 := rfl

@[simp] lemma matOfXY_apply_01 (x y : E) : matOfXY x y 0 1 = x := rfl

@[simp] lemma matOfXY_apply_02 (x y : E) : matOfXY x y 0 2 = y := rfl

@[simp] lemma matOfXY_apply_10 (x y : E) : matOfXY x y 1 0 = 0 := rfl

@[simp] lemma matOfXY_apply_11 (x y : E) : matOfXY x y 1 1 = 1 := rfl

@[simp] lemma matOfXY_apply_12 (x y : E) : matOfXY x y 1 2 = σE x := rfl

@[simp] lemma matOfXY_apply_20 (x y : E) : matOfXY x y 2 0 = 0 := rfl

@[simp] lemma matOfXY_apply_21 (x y : E) : matOfXY x y 2 1 = 0 := rfl

@[simp] lemma matOfXY_apply_22 (x y : E) : matOfXY x y 2 2 = 1 := rfl

@[simp] lemma matFun_apply (p : SZ E) : matFun p = matOfXY p.x p.y := rfl

@[simp] lemma hermMat_apply_02 : hermMat (E := E) 0 2 = 1 := rfl

@[simp] lemma hermMat_apply_11 : hermMat (E := E) 1 1 = 1 := rfl

@[simp] lemma hermMat_apply_20 : hermMat (E := E) 2 0 = 1 := rfl

@[simp] lemma weylMat_eq : weylMat (E := E) = hermMat := rfl

@[simp] lemma weylFactor_apply_00 (x y : E) : weylFactor x y 0 0 = (σE y)⁻¹ := rfl

@[simp] lemma weylFactor_apply_01 (x y : E) : weylFactor x y 0 1 = x / y := rfl

@[simp] lemma weylFactor_apply_02 (x y : E) : weylFactor x y 0 2 = 1 := rfl

@[simp] lemma weylFactor_apply_10 (x y : E) : weylFactor x y 1 0 = 0 := rfl

@[simp] lemma weylFactor_apply_11 (x y : E) : weylFactor x y 1 1 = σE y / y := rfl

@[simp] lemma weylFactor_apply_12 (x y : E) : weylFactor x y 1 2 = σE x := rfl

@[simp] lemma weylFactor_apply_20 (x y : E) : weylFactor x y 2 0 = 0 := rfl

@[simp] lemma weylFactor_apply_21 (x y : E) : weylFactor x y 2 1 = 0 := rfl

@[simp] lemma weylFactor_apply_22 (x y : E) : weylFactor x y 2 2 = y := rfl

end Work.PSU3
