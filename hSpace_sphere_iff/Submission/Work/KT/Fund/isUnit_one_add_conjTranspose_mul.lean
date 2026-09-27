import Mathlib

/-!
# `1 + Aᴴ A` is a unit over `C(Y, ℂ)`

For a matrix `A` with entries in the ring of continuous complex functions on a topological
space `Y`, the matrix `1 + Aᴴ * A` is invertible.

The proof is pointwise.  In a commutative ring a square matrix is a unit iff its determinant is,
and a continuous complex function is a unit of `C(Y, ℂ)` precisely when it never vanishes.  So it
suffices to know that the complex matrix `1 + Bᴴ * B` is invertible for every `B`; it is in fact
positive definite, since `xᴴ(1 + BᴴB)x = xᴴx + (Bx)ᴴ(Bx) > 0` for `x ≠ 0`.
-/

open scoped ComplexOrder

namespace Work.KT.Fund

/-- Evaluating the determinant of a matrix of continuous functions at a point equals the
determinant of the pointwise evaluation of the matrix. -/
lemma det_map_eval {X : Type} [TopologicalSpace X] (n : ℕ)
    (M : Matrix (Fin n) (Fin n) C(X, ℂ)) (x : X) :
    (M.map ((ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom)).det = M.det x := by
  rw [← RingHom.mapMatrix_apply]
  exact ((ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom.map_det M).symm

/-- A matrix over `C(X, ℂ)` is a unit as soon as all of its pointwise evaluations are.
(No compactness of `X` is needed: the inverse of a nowhere vanishing continuous `ℂ`-valued
function is continuous because `ℂ` is complete.) -/
lemma isUnit_map_of_isUnit_pointwise {X : Type} [TopologicalSpace X] (n : ℕ)
    (M : Matrix (Fin n) (Fin n) C(X, ℂ))
    (h : ∀ x, IsUnit ((ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom.mapMatrix M)) :
    IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det, ContinuousMap.isUnit_iff_forall_ne_zero]
  intro x
  have hx := h x
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, RingHom.mapMatrix_apply] at hx
  rwa [det_map_eval] at hx

/-- Over `ℂ`, the matrix `1 + Bᴴ * B` is positive definite, hence invertible. -/
lemma isUnit_one_add_conjTranspose_mul_complex {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) :
    IsUnit (1 + B.conjTranspose * B) := by
  have h : (1 + B.conjTranspose * B).PosDef :=
    (Matrix.PosDef.one (n := Fin n)).add_posSemidef
      (Matrix.posSemidef_conjTranspose_mul_self B)
  exact h.isUnit

theorem isUnit_one_add_conjTranspose_mul {Y : Type} [TopologicalSpace Y] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) C(Y, ℂ)) :
    IsUnit (1 + A.conjTranspose * A) := by
  apply isUnit_map_of_isUnit_pointwise n
  intro y
  set ev : C(Y, ℂ) →+* ℂ := (ContinuousMap.evalAlgHom ℂ ℂ y).toRingHom with hev
  have hsem : Function.Semiconj ev star star := fun a => ContinuousMap.star_apply a y
  have hconj : ev.mapMatrix A.conjTranspose = (ev.mapMatrix A).conjTranspose := by
    rw [RingHom.mapMatrix_apply, Matrix.conjTranspose_map ev hsem, RingHom.mapMatrix_apply]
  have hmap : ev.mapMatrix (1 + A.conjTranspose * A) =
      1 + (ev.mapMatrix A).conjTranspose * ev.mapMatrix A := by
    rw [map_add, map_mul, map_one, hconj]
  rw [hmap]
  exact isUnit_one_add_conjTranspose_mul_complex (ev.mapMatrix A)

end Work.KT.Fund
