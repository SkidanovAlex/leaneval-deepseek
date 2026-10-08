/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The area `Work/PSL2`: explicit elements of `SL(2,F)` and `PSL(2,F)`

This file sets up the vocabulary used throughout `Submission/Work/PSL2/`.

Written conventions (all `F` is a field):
* `diag a`       is `⟨⟨a,0⟩,⟨0,a⁻¹⟩⟩ ∈ SL(2,F)`;  `diagHom : Fˣ →* SL(2,F)`.
* `unipotent b`  is `⟨⟨1,b⟩,⟨0,1⟩⟩`;              `unipotentHom : Multiplicative F →* SL(2,F)`.
* `unipotent' b` is `⟨⟨1,0⟩,⟨b,1⟩⟩` (lower);      `unipotent'Hom : Multiplicative F →* SL(2,F)`.
* `weyl`         is `⟨⟨0,1⟩,⟨-1,0⟩⟩`.
* `pslMap : SL(2,F) →* PSL(2,F)` is the quotient map (modulo the centre);
  `pslDiag a`, `pslUnipotent b`, `pslUnipotent' b`, `pslWeyl` are the images.
* `ptOf t = [t:1]` (`t = x₀/x₁`), `ptInf = [1:0]`, `ptZero = [0:1]` are points of `ℙ F (Fin 2 → F)`.

The `[simp]` lemmas `coe_diag`, `coe_unipotent`, `coe_unipotent'`, `coe_weyl` state the
matrix entries; combined with `Matrix.SpecialLinearGroup.coe_mul` and
`Matrix.mul_fin_two` they reduce any identity between these elements to `Fin 2` cases.
A typical proof is

```
  apply Subtype.ext
  change ((lhs : SL(2,F)) : Matrix (Fin 2) (Fin 2) F) = ((rhs : SL(2,F)) : Matrix (Fin 2) (Fin 2) F)
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_diag, coe_unipotent, Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp
```

(the explicit `change` matters: it pins the coercion to `Matrix n n F` and avoids a
`Subtype`-transparency issue).
-/
import Mathlib

open scoped MatrixGroups
open Matrix

namespace Work.PSL2

variable (F : Type*) [Field F]

/-! ## Elementary matrices -/

/-- The diagonal matrix `diag(a, a⁻¹)` as an element of `SL(2,F)`. -/
def diag (a : Fˣ) : SL(2, F) :=
  ⟨!![↑a, 0; 0, ↑(a⁻¹)], by rw [Matrix.det_fin_two_of]; simp⟩

/-- The upper unitriangular matrix `[[1,b],[0,1]]` as an element of `SL(2,F)`. -/
def unipotent (b : F) : SL(2, F) :=
  ⟨!![1, b; 0, 1], by rw [Matrix.det_fin_two_of]; simp⟩

/-- The lower unitriangular matrix `[[1,0],[b,1]]` as an element of `SL(2,F)`. -/
def unipotent' (b : F) : SL(2, F) :=
  ⟨!![1, 0; b, 1], by rw [Matrix.det_fin_two_of]; simp⟩

/-- The Weyl element `[[0,1],[-1,0]]` as an element of `SL(2,F)`. -/
def weyl : SL(2, F) :=
  ⟨!![0, 1; -1, 0], by rw [Matrix.det_fin_two_of]; simp⟩

@[simp]
theorem coe_diag (a : Fˣ) :
    ((diag F a : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![↑a, 0; 0, ↑(a⁻¹)] := rfl

@[simp]
theorem coe_unipotent (b : F) :
    ((unipotent F b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, b; 0, 1] := rfl

@[simp]
theorem coe_unipotent' (b : F) :
    ((unipotent' F b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; b, 1] := rfl

@[simp]
theorem coe_weyl :
    ((weyl F : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl

/-- The diagonal torus as a monoid homomorphism `Fˣ →* SL(2,F)`. -/
def diagHom : Fˣ →* SL(2, F) where
  toFun := diag F
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_diag, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]
  map_mul' a b := by
    apply Subtype.ext
    change ((diag F (a * b) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      ((diag F a * diag F b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
    simp only [coe_diag, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_fin_two,
      Units.val_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_comm]

/-- The upper unitriangular group as a monoid homomorphism `Multiplicative F →* SL(2,F)`. -/
def unipotentHom : Multiplicative F →* SL(2, F) where
  toFun b := unipotent F (Multiplicative.toAdd b)
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_unipotent, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]
  map_mul' b c := by
    apply Subtype.ext
    change ((unipotent F (Multiplicative.toAdd (b * c)) : SL(2, F)) :
        Matrix (Fin 2) (Fin 2) F) =
      ((unipotent F (Multiplicative.toAdd b) * unipotent F (Multiplicative.toAdd c) :
        SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
    simp only [toAdd_mul, coe_unipotent, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [add_comm]

/-- The lower unitriangular group as a monoid homomorphism `Multiplicative F →* SL(2,F)`. -/
def unipotent'Hom : Multiplicative F →* SL(2, F) where
  toFun b := unipotent' F (Multiplicative.toAdd b)
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_unipotent', Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]
  map_mul' b c := by
    apply Subtype.ext
    change ((unipotent' F (Multiplicative.toAdd (b * c)) : SL(2, F)) :
        Matrix (Fin 2) (Fin 2) F) =
      ((unipotent' F (Multiplicative.toAdd b) * unipotent' F (Multiplicative.toAdd c) :
        SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
    simp only [toAdd_mul, coe_unipotent', Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-! ## The projective special linear group -/

/-- The quotient map `SL(2,F) → PSL(2,F)`. -/
def pslMap : SL(2, F) →* PSL(2, F) :=
  QuotientGroup.mk' (Subgroup.center (SL(2, F)))

/-- The image of the diagonal torus in `PSL(2,F)`, as a monoid homomorphism. -/
def pslDiagHom : Fˣ →* PSL(2, F) := (pslMap F).comp (diagHom F)

/-- The image of the upper unipotent group in `PSL(2,F)`, as a monoid homomorphism. -/
def pslUnipotentHom : Multiplicative F →* PSL(2, F) := (pslMap F).comp (unipotentHom F)

/-- The image of the lower unipotent group in `PSL(2,F)`, as a monoid homomorphism. -/
def pslUnipotent'Hom : Multiplicative F →* PSL(2, F) := (pslMap F).comp (unipotent'Hom F)

/-- The image of the diagonal torus in `PSL(2,F)`. -/
def pslDiag (a : Fˣ) : PSL(2, F) := pslDiagHom F a

/-- The image of the upper unipotent group in `PSL(2,F)`. -/
def pslUnipotent (b : F) : PSL(2, F) := pslUnipotentHom F (Multiplicative.ofAdd b)

/-- The image of the lower unipotent group in `PSL(2,F)`. -/
def pslUnipotent' (b : F) : PSL(2, F) := pslUnipotent'Hom F (Multiplicative.ofAdd b)

/-- The image of the Weyl element in `PSL(2,F)`. -/
def pslWeyl : PSL(2, F) := pslMap F (weyl F)

/-- The diagonal torus of `SL(2,F)`. -/
def torus : Subgroup (SL(2, F)) := (diagHom F).range

/-- The upper unipotent subgroup of `SL(2,F)`. -/
def unipotentSubgroup : Subgroup (SL(2, F)) := (unipotentHom F).range

@[simp]
theorem pslDiag_apply (a : Fˣ) : pslDiag F a = pslMap F (diag F a) := rfl

@[simp]
theorem pslUnipotent_apply (b : F) :
    pslUnipotent F b = pslMap F (unipotent F b) := rfl

@[simp]
theorem pslUnipotent'_apply (b : F) :
    pslUnipotent' F b = pslMap F (unipotent' F b) := rfl

/-! ## The projective line

We use the affine coordinate `t = x₀/x₁` on `ℙ F (Fin 2 → F)`: the point `ptOf t` is `[t:1]`,
and `ptInf` is `[1:0]`.  With this convention the elementary matrices act by

* `pslUnipotent b : t ↦ t + b`,
* `pslDiag a      : t ↦ a² t`,
* `pslWeyl        : t ↦ -1/t`.
-/

open scoped LinearAlgebra.Projectivization

/-- The point `[t:1]` of the projective line, in the affine coordinate `t = x₀/x₁`. -/
def ptOf (t : F) : ℙ F (Fin 2 → F) :=
  Projectivization.mk F ![t, 1] (by simp [Fin.forall_fin_two])

/-- The point `[1:0]`, the point at infinity for the coordinate `x₀/x₁`. -/
def ptInf : ℙ F (Fin 2 → F) :=
  Projectivization.mk F ![1, 0] (by simp [Fin.forall_fin_two])

/-- The point `[0:1]`, the origin for the coordinate `x₀/x₁`. -/
def ptZero : ℙ F (Fin 2 → F) := ptOf F 0

@[simp]
theorem ptOf_zero : ptOf F 0 = ptZero F := rfl

end Work.PSL2
