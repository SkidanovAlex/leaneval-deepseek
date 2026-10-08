/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AREA L2F, `PGL2CommutatorTorus`: the matrix vocabulary

This file fixes the vocabulary used by `Submission/Work/L2F/Props/PGL2CommutatorTorus.lean`
(the `L2F`-area statement `Work.L2F.PGL2CommutatorTorusProp`, Bender's commutator–torus fact
used in Gorenstein–Walter Theorem 2.6 step 2).

Everything concerns the two groups

* `SL(2,F) = Matrix.SpecialLinearGroup (Fin 2) F`,
* `PGL(2,F) = Matrix.ProjGenLinGroup (Fin 2) F`  (the quotient of `GL(2,F)` by its centre),

together with the natural map `Matrix.SpecialLinearGroup.toPGL : SL(2,F) →* PGL(2,F)`
(the composite of `toGL` and the quotient map) whose range is `L₂(F) ⊆ PGL₂(F)`.

For `S ∈ GL(2,F)` we introduce

* `negOneGL F`     : the central element `-1` of `GL(2,F)`;
* `negGL F S`      : `(-1) * S`, i.e. the matrix `-S`, as an element of `GL(2,F)`;
* `cmtK0 F S`      : the centralizer of `S` in `SL(2,F)`
  (`= {x ∈ SL(2,F) | x S x⁻¹ = S}`), the "rotation subgroup" of the torus;
* `cmtK1 F S`      : the set `{x ∈ SL(2,F) | x S x⁻¹ = -S}`, the "reflection coset";
* `cmtK F S`       : `{x ∈ SL(2,F) | x S x⁻¹ = ±S}`; its image in `PGL(2,F)` is `C_{L₂(F)}(S)`.

The main theorem of the area identifies `C_L(s)` with `(cmtK F S).map toPGL` and the commutator
`[⟨t⟩, C_L(s)]` with `(cmtK0 F S).map toPGL`, hence the cyclic order-`m` structure.
-/
import Mathlib
import Submission.Work.L2F.Defs

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Props

variable (F : Type*) [Field F]

/-- The image `L₂(F)` of `SL(2,F)` in `PGL(2,F)`, as a subgroup. -/
def SLsub : Subgroup (PGL(2, F)) :=
  (Matrix.SpecialLinearGroup.toPGL : SL(2, F) →* PGL(2, F)).range

@[simp]
theorem mem_SLsub {g : PGL(2, F)} :
    g ∈ SLsub F ↔ ∃ x : SL(2, F), Matrix.SpecialLinearGroup.toPGL x = g := Iff.rfl

@[simp]
theorem toPGL_mem_SLsub (x : SL(2, F)) : Matrix.SpecialLinearGroup.toPGL x ∈ SLsub F :=
  ⟨x, rfl⟩

/-! ## The central element `-1` and the "sign" `-S` -/

/-- The matrix `-1` as an element of `GL(2,F)`. -/
def negOneGL : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (-(1 : Matrix (Fin 2) (Fin 2) F))
    (by
      have h : (-(1 : Matrix (Fin 2) (Fin 2) F)).det = 1 := by
        rw [Matrix.det_neg, Fintype.card_fin, Matrix.det_one]
        ring
      rw [h]
      exact one_ne_zero)

@[simp]
theorem negOneGL_apply : (negOneGL F : Matrix (Fin 2) (Fin 2) F) = -1 := rfl

@[simp]
theorem negOneGL_mul_self : negOneGL F * negOneGL F = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul, negOneGL_apply, Matrix.neg_mul, Matrix.one_mul,
    neg_neg, Matrix.GeneralLinearGroup.coe_one]

theorem negOneGL_mul_comm (A : GL (Fin 2) F) : negOneGL F * A = A * negOneGL F := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, negOneGL_apply,
    Matrix.neg_mul, Matrix.one_mul, Matrix.mul_neg, Matrix.mul_one]

/-- Conjugating `negOneGL F * S` conjugates `S`. -/
theorem negOneGL_conj (A S : GL (Fin 2) F) :
    A * (negOneGL F * S) * A⁻¹ = negOneGL F * (A * S * A⁻¹) := by
  rw [← mul_assoc A (negOneGL F) S, ← negOneGL_mul_comm F A]
  group

/-- `-S` as an element of `GL(2,F)`; this is `(-1) * S`. -/
abbrev negGL (S : GL (Fin 2) F) : GL (Fin 2) F := negOneGL F * S

@[simp]
theorem negGL_apply (S : GL (Fin 2) F) :
    (negGL F S : Matrix (Fin 2) (Fin 2) F) = -(S : Matrix (Fin 2) (Fin 2) F) := by
  rw [negGL, Matrix.GeneralLinearGroup.coe_mul, negOneGL_apply, Matrix.neg_mul, Matrix.one_mul]

@[simp]
theorem negGL_negGL (S : GL (Fin 2) F) : negGL F (negGL F S) = S := by
  rw [negGL, negGL, ← mul_assoc, negOneGL_mul_self, one_mul]

@[simp]
theorem conj_negGL (x : SL(2, F)) (S : GL (Fin 2) F) :
    Matrix.SpecialLinearGroup.toGL x * negGL F S * (Matrix.SpecialLinearGroup.toGL x)⁻¹ =
      negGL F (Matrix.SpecialLinearGroup.toGL x * S * (Matrix.SpecialLinearGroup.toGL x)⁻¹) :=
  negOneGL_conj F (Matrix.SpecialLinearGroup.toGL x) S

/-- Conjugation is multiplicative: conjugating by `x * y` is conjugating by `y` then by `x`. -/
theorem conj_mul_eq (x y : SL(2, F)) (S : GL (Fin 2) F) :
    Matrix.SpecialLinearGroup.toGL (x * y) * S * (Matrix.SpecialLinearGroup.toGL (x * y))⁻¹ =
      Matrix.SpecialLinearGroup.toGL x *
        (Matrix.SpecialLinearGroup.toGL y * S * (Matrix.SpecialLinearGroup.toGL y)⁻¹) *
          (Matrix.SpecialLinearGroup.toGL x)⁻¹ := by
  rw [map_mul, _root_.mul_inv_rev]
  group

/-- Conjugation by `x⁻¹` fixes `S` when conjugation by `x` does. -/
theorem conj_inv_of_eq (x : SL(2, F)) (S : GL (Fin 2) F)
    (h : Matrix.SpecialLinearGroup.toGL x * S * (Matrix.SpecialLinearGroup.toGL x)⁻¹ = S) :
    Matrix.SpecialLinearGroup.toGL x⁻¹ * S * (Matrix.SpecialLinearGroup.toGL x⁻¹)⁻¹ = S := by
  rw [map_inv]
  have h' : (Matrix.SpecialLinearGroup.toGL x)⁻¹ *
      (Matrix.SpecialLinearGroup.toGL x * S * (Matrix.SpecialLinearGroup.toGL x)⁻¹) *
        ((Matrix.SpecialLinearGroup.toGL x)⁻¹)⁻¹ = S := by group
  rw [h] at h'
  exact h'

/-- Conjugation by `x⁻¹` sends `S` to `-S` when conjugation by `x` does. -/
theorem conj_inv_of_eq_neg (x : SL(2, F)) (S : GL (Fin 2) F)
    (h : Matrix.SpecialLinearGroup.toGL x * S * (Matrix.SpecialLinearGroup.toGL x)⁻¹ =
      negGL F S) :
    Matrix.SpecialLinearGroup.toGL x⁻¹ * S * (Matrix.SpecialLinearGroup.toGL x⁻¹)⁻¹ =
      negGL F S := by
  rw [map_inv]
  have e : (Matrix.SpecialLinearGroup.toGL x)⁻¹ *
      (Matrix.SpecialLinearGroup.toGL x * S * (Matrix.SpecialLinearGroup.toGL x)⁻¹) *
        ((Matrix.SpecialLinearGroup.toGL x)⁻¹)⁻¹ = S := by group
  rw [h] at e
  rw [negOneGL_conj] at e
  have e2 := congrArg (fun t : GL (Fin 2) F => negOneGL F * t) e
  rw [← mul_assoc, negOneGL_mul_self, one_mul] at e2
  exact e2

/-! ## The subgroups `cmtK0 ≤ cmtK` of `SL(2,F)` -/

/-- The centralizer of `S` in `SL(2,F)`. -/
def cmtK0 (S : GL (Fin 2) F) : Subgroup (SL(2, F)) where
  carrier := {x | Matrix.SpecialLinearGroup.toGL x * S * (Matrix.SpecialLinearGroup.toGL x)⁻¹ = S}
  mul_mem' := by
    intro x y hx hy
    change Matrix.SpecialLinearGroup.toGL (x * y) * S *
      (Matrix.SpecialLinearGroup.toGL (x * y))⁻¹ = S
    rw [conj_mul_eq, hy, hx]
  one_mem' := by
    change Matrix.SpecialLinearGroup.toGL (1 : SL(2, F)) * S *
      (Matrix.SpecialLinearGroup.toGL (1 : SL(2, F)))⁻¹ = S
    rw [map_one, one_mul, inv_one, mul_one]
  inv_mem' := by
    intro x hx
    change Matrix.SpecialLinearGroup.toGL x⁻¹ * S * (Matrix.SpecialLinearGroup.toGL x⁻¹)⁻¹ = S
    exact conj_inv_of_eq F x S hx

@[simp]
theorem mem_cmtK0_iff (S : GL (Fin 2) F) (x : SL(2, F)) :
    x ∈ cmtK0 F S ↔
      Matrix.SpecialLinearGroup.toGL x * S * (Matrix.SpecialLinearGroup.toGL x)⁻¹ = S :=
  Iff.rfl

/-- Membership in `cmtK0 F S` is commutation with `S`. -/
theorem mem_cmtK0_iff_comm (S : GL (Fin 2) F) (x : SL(2, F)) :
    x ∈ cmtK0 F S ↔
      Matrix.SpecialLinearGroup.toGL x * S = S * Matrix.SpecialLinearGroup.toGL x := by
  rw [mem_cmtK0_iff]
  constructor
  · intro h
    calc Matrix.SpecialLinearGroup.toGL x * S
        = (Matrix.SpecialLinearGroup.toGL x * S * (Matrix.SpecialLinearGroup.toGL x)⁻¹) *
            Matrix.SpecialLinearGroup.toGL x := by group
      _ = S * Matrix.SpecialLinearGroup.toGL x := by rw [h]
  · intro h
    rw [h]
    group

/-- The set `{x ∈ SL(2,F) | x S x⁻¹ = -S}`. -/
def cmtK1 (S : GL (Fin 2) F) : Set (SL(2, F)) :=
  {x | Matrix.SpecialLinearGroup.toGL x * S * (Matrix.SpecialLinearGroup.toGL x)⁻¹ = negGL F S}

@[simp]
theorem mem_cmtK1_iff (S : GL (Fin 2) F) (x : SL(2, F)) :
    x ∈ cmtK1 F S ↔
      Matrix.SpecialLinearGroup.toGL x * S * (Matrix.SpecialLinearGroup.toGL x)⁻¹ = negGL F S :=
  Iff.rfl

/-- Membership in `cmtK1 F S`, commutation form. -/
theorem mem_cmtK1_iff_comm (S : GL (Fin 2) F) (x : SL(2, F)) :
    x ∈ cmtK1 F S ↔
      Matrix.SpecialLinearGroup.toGL x * S = negGL F S * Matrix.SpecialLinearGroup.toGL x := by
  rw [mem_cmtK1_iff]
  constructor
  · intro h
    calc Matrix.SpecialLinearGroup.toGL x * S
        = (Matrix.SpecialLinearGroup.toGL x * S * (Matrix.SpecialLinearGroup.toGL x)⁻¹) *
            Matrix.SpecialLinearGroup.toGL x := by group
      _ = negGL F S * Matrix.SpecialLinearGroup.toGL x := by rw [h]
  · intro h
    rw [h]
    group

/-- `{x ∈ SL(2,F) | x S x⁻¹ = ±S}` as a subgroup. -/
def cmtK (S : GL (Fin 2) F) : Subgroup (SL(2, F)) where
  carrier := {x | Matrix.SpecialLinearGroup.toGL x * S * (Matrix.SpecialLinearGroup.toGL x)⁻¹ = S ∨
    Matrix.SpecialLinearGroup.toGL x * S * (Matrix.SpecialLinearGroup.toGL x)⁻¹ = negGL F S}
  mul_mem' := by
    intro x y hx hy
    change Matrix.SpecialLinearGroup.toGL (x * y) * S *
      (Matrix.SpecialLinearGroup.toGL (x * y))⁻¹ = S ∨
      Matrix.SpecialLinearGroup.toGL (x * y) * S *
        (Matrix.SpecialLinearGroup.toGL (x * y))⁻¹ = negGL F S
    rw [conj_mul_eq]
    rcases hy with hy | hy
    · rcases hx with hx | hx
      · exact Or.inl (by rw [hy, hx])
      · exact Or.inr (by rw [hy, hx])
    · rw [hy]
      rcases hx with hx | hx
      · exact Or.inr (by rw [negOneGL_conj, hx])
      · exact Or.inl (by rw [negOneGL_conj, hx, ← mul_assoc, negOneGL_mul_self, one_mul])
  one_mem' := by
    change Matrix.SpecialLinearGroup.toGL (1 : SL(2, F)) * S *
      (Matrix.SpecialLinearGroup.toGL (1 : SL(2, F)))⁻¹ = S ∨ _
    left
    rw [map_one, one_mul, inv_one, mul_one]
  inv_mem' := by
    intro x hx
    change Matrix.SpecialLinearGroup.toGL x⁻¹ * S * (Matrix.SpecialLinearGroup.toGL x⁻¹)⁻¹ = S ∨
      Matrix.SpecialLinearGroup.toGL x⁻¹ * S * (Matrix.SpecialLinearGroup.toGL x⁻¹)⁻¹ =
        negGL F S
    rcases hx with hx | hx
    · exact Or.inl (conj_inv_of_eq F x S hx)
    · exact Or.inr (conj_inv_of_eq_neg F x S hx)

@[simp]
theorem mem_cmtK_iff (S : GL (Fin 2) F) (x : SL(2, F)) :
    x ∈ cmtK F S ↔ Matrix.SpecialLinearGroup.toGL x * S *
        (Matrix.SpecialLinearGroup.toGL x)⁻¹ = S ∨
      Matrix.SpecialLinearGroup.toGL x * S * (Matrix.SpecialLinearGroup.toGL x)⁻¹ =
        negGL F S := Iff.rfl

theorem cmtK0_le_cmtK (S : GL (Fin 2) F) : cmtK0 F S ≤ cmtK F S := fun _ hx => Or.inl hx

theorem cmtK1_subset_cmtK (S : GL (Fin 2) F) : cmtK1 F S ⊆ cmtK F S := fun _ hx => Or.inr hx

end Work.L2F.Props
