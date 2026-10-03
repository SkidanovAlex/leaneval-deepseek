/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Matrices over a skew Laurent polynomial ring

For a ring `R` carrying an action of `Multiplicative ℤ` (thought of as the twist `τ` of the skew
Laurent polynomial ring `R[t^{±1}; τ] = SkewMonoidAlgebra R (Multiplicative ℤ)`), the skew monoid
algebra of `M_k(R)` over `Multiplicative ℤ` is isomorphic to `M_k(R[t^{±1}; τ])`:

  `skewMatrixRingEquiv` : `M_k(R)[t^{±1}; τ] ≃+* M_k(R[t^{±1}; τ])`

The isomorphism is the "obvious" one: an element `∑_m A_m · t^m` of `M_k(R)[t^{±1}; τ]`
(with each `A_m` a `k × k` matrix over `R`) is sent to the matrix whose `(i,j)` entry is
`∑_m (A_m)_{ij} t^m`.  It is multiplicative because the twist `m • A` on the coefficient ring is
entrywise, so `∑_{m + n = l} A_m · (m • B_n)` is mapped to `∑_{m+n=l} A_m B_n`, which is exactly the
product of the two matrices in `M_k(R[t^{±1}; τ])`.

The map is constructed from the universal property of the skew monoid algebra
(`SkewMonoidAlgebra.liftNC`): the coefficient ring `M_k(R)` maps in by `A ↦ A.map (single 1)`
(entrywise `t^0`), and `t^m` maps to the diagonal matrix with `t^m` on the diagonal.

Note that in the Mathlib version this is built on, `MulSemiringAction (Multiplicative ℤ)
(Matrix (Fin k) (Fin k) R)` is *not* available as an instance (only the pointwise `(Distrib)SMul`
is), so the two sides can only be compared as non-unital rings: the universal property used is the
one for `NonUnitalRingHom` (`SkewMonoidAlgebra.liftNC_mul`), and the isomorphism is produced by
`RingEquiv.ofBijective`.
-/
import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.Defs
import Submission.Work.ORHughesFree.NaturalExtension.coeffSupportFinite

set_option autoImplicit false

universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix

variable (R : Type u) [Ring R] [MulSemiringAction (Multiplicative ℤ) R] (k : ℕ)

/-! ### The two maps defining the isomorphism -/

/-- The ring hom `A ↦ A.map (single 1)` embedding `M_k(R)` into `M_k(R[t^{±1}; τ])` entrywise. -/
noncomputable def skewMatrixMapSingle :
    Matrix (Fin k) (Fin k) R →+* Matrix (Fin k) (Fin k) (SkewMonoidAlgebra R (Multiplicative ℤ)) where
  toFun A := A.map (SkewMonoidAlgebra.single 1)
  map_one' := by
    rw [Matrix.map_one (SkewMonoidAlgebra.single 1) (by simp) (by simp)]
  map_mul' A B := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.map_apply, Matrix.mul_apply]
    simp only [SkewMonoidAlgebra.single_mul_single, one_smul, mul_one, mul_one]
    exact _root_.map_sum (SkewMonoidAlgebra.singleAddHom (1 : Multiplicative ℤ))
      (fun l => A i l * B l j) Finset.univ
  map_zero' := by
    rw [Matrix.map_zero (SkewMonoidAlgebra.single 1) (by simp)]
  map_add' A B := by
    apply Matrix.ext
    intro i j
    simp [Matrix.map_apply, Matrix.add_apply]

/-- `skewMatrixMapSingle` is the entrywise map `A ↦ (i j ↦ single 1 (A i j))`. -/
theorem skewMatrixMapSingle_apply (A : Matrix (Fin k) (Fin k) R) :
    skewMatrixMapSingle R k A = A.map (SkewMonoidAlgebra.single 1) := rfl

/-- The monoid hom `m ↦ diagonal (single m 1)`, the image of `t^m` under the isomorphism. -/
noncomputable def skewMatrixDiag :
    Multiplicative ℤ →* Matrix (Fin k) (Fin k) (SkewMonoidAlgebra R (Multiplicative ℤ)) where
  toFun m := Matrix.diagonal (fun _ : Fin k => SkewMonoidAlgebra.single m 1)
  map_one' := by
    simp [Matrix.diagonal_one]
  map_mul' a b := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    simp [SkewMonoidAlgebra.single_mul_single]

theorem skewMatrixDiag_apply (m : Multiplicative ℤ) :
    skewMatrixDiag R k m = Matrix.diagonal (fun _ : Fin k => SkewMonoidAlgebra.single m 1) := rfl

/-- The compatibility between the two maps, ensuring that the resulting map out of the skew monoid
algebra is multiplicative: the action of `m` on a matrix is entrywise, and
`single 1 x * single m 1 = single m (m • x)`. -/
theorem skewMatrixMapSingle_smul_mul (A : Matrix (Fin k) (Fin k) R) (m : Multiplicative ℤ) :
    skewMatrixMapSingle R k (m • A) * skewMatrixDiag R k m
      = skewMatrixDiag R k m * skewMatrixMapSingle R k A := by
  rw [skewMatrixDiag_apply, skewMatrixMapSingle_apply, skewMatrixMapSingle_apply]
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.map_apply, Matrix.smul_apply]
  rw [SkewMonoidAlgebra.single_mul_single, SkewMonoidAlgebra.single_mul_single]
  simp

/-- The underlying additive map of the isomorphism, obtained from the universal property
(`SkewMonoidAlgebra.liftNC`) of the skew monoid algebra. -/
noncomputable def skewMatrixToFun :
    SkewMonoidAlgebra (Matrix (Fin k) (Fin k) R) (Multiplicative ℤ) →+
      Matrix (Fin k) (Fin k) (SkewMonoidAlgebra R (Multiplicative ℤ)) :=
  SkewMonoidAlgebra.liftNC (skewMatrixMapSingle R k) (skewMatrixDiag R k)

/-- The map `M_k(R)[t^{±1}; τ] → M_k(R[t^{±1}; τ])` sending `∑_m A_m t^m` to the matrix with
entries `(i,j) ↦ ∑_m (A_m)_{ij} t^m`. -/
noncomputable def skewMatrixToHom :
    SkewMonoidAlgebra (Matrix (Fin k) (Fin k) R) (Multiplicative ℤ) →ₙ+*
      Matrix (Fin k) (Fin k) (SkewMonoidAlgebra R (Multiplicative ℤ)) where
  toFun := skewMatrixToFun R k
  map_zero' := (skewMatrixToFun R k).map_zero'
  map_add' := fun a b => (skewMatrixToFun R k).map_add' a b
  map_mul' a b := SkewMonoidAlgebra.liftNC_mul (skewMatrixMapSingle R k) (skewMatrixDiag R k) a b
    (fun {x y} _ => skewMatrixMapSingle_smul_mul R k (b.coeff x) y)

theorem skewMatrixToHom_apply
    (x : SkewMonoidAlgebra (Matrix (Fin k) (Fin k) R) (Multiplicative ℤ)) :
    skewMatrixToHom R k x = skewMatrixToFun R k x := rfl

/-- The value of the isomorphism on a "monomial" `A · t^m`. -/
theorem skewMatrixToHom_single (m : Multiplicative ℤ) (A : Matrix (Fin k) (Fin k) R) :
    skewMatrixToHom R k (SkewMonoidAlgebra.single m A)
      = A.map (SkewMonoidAlgebra.single m) := by
  rw [skewMatrixToHom_apply, skewMatrixToFun, SkewMonoidAlgebra.liftNC_single]
  show skewMatrixMapSingle R k A * skewMatrixDiag R k m = A.map (SkewMonoidAlgebra.single m)
  rw [skewMatrixMapSingle_apply, skewMatrixDiag_apply]
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_diagonal, Matrix.map_apply]
  simp [SkewMonoidAlgebra.single_mul_single]

/-! ### The coefficient formula -/

/-- The `(i,j)` entry of the image of `x` has `m`-th coefficient the `(i,j)` entry of the `m`-th
coefficient matrix of `x`.  This is the key computation: it says `skewMatrixToHom` is exactly the
"entrywise" identification of the two sides. -/
theorem skewMatrixToHom_coeff :
    ∀ x : SkewMonoidAlgebra (Matrix (Fin k) (Fin k) R) (Multiplicative ℤ),
      ∀ (i j : Fin k) (m : Multiplicative ℤ),
        (skewMatrixToHom R k x i j).coeff m = (x.coeff m) i j := by
  intro x
  refine SkewMonoidAlgebra.induction_on x ?_ ?_ ?_
  · intro i j m
    simp
  · intro a b i j m
    rw [skewMatrixToHom_single]
    simp only [Matrix.map_apply]
    by_cases h : a = m <;> simp [h]
  · intro f g hf hg i j m
    simp [hf, hg]

/-! ### Injectivity and surjectivity -/

theorem skewMatrixToHom_injective : Function.Injective (skewMatrixToHom R k) := by
  intro x y hxy
  apply SkewMonoidAlgebra.ext
  intro m
  apply Matrix.ext
  intro i j
  have h2 := congrArg (fun z => (z i j).coeff m) hxy
  simpa [skewMatrixToHom_coeff R k] using h2

/-- A preimage of `Y` under `skewMatrixToHom`: the element of `M_k(R)[t^{±1}; τ]` whose `m`-th
coefficient matrix is `(i j ↦ (Y i j).coeff m)`. -/
noncomputable def skewMatrixOfFun
    (Y : Matrix (Fin k) (Fin k) (SkewMonoidAlgebra R (Multiplicative ℤ))) :
    SkewMonoidAlgebra (Matrix (Fin k) (Fin k) R) (Multiplicative ℤ) :=
  SkewMonoidAlgebra.ofCoeff (Finsupp.ofSupportFinite
    (fun m : Multiplicative ℤ => Matrix.of (fun i j : Fin k => (Y i j).coeff m))
    (coeffSupportFinite R k Y))

theorem skewMatrixToHom_surjective : Function.Surjective (skewMatrixToHom R k) := by
  intro Y
  refine ⟨skewMatrixOfFun R k Y, ?_⟩
  apply Matrix.ext
  intro i j
  apply SkewMonoidAlgebra.ext
  intro m
  rw [skewMatrixToHom_coeff R k]
  rfl

/-! ### The isomorphism -/

theorem skewMatrixRingEquiv (R : Type u) [Ring R] [MulSemiringAction (Multiplicative ℤ) R] (k : ℕ) : Nonempty (SkewMonoidAlgebra (Matrix (Fin k) (Fin k) R) (Multiplicative ℤ) ≃+* Matrix (Fin k) (Fin k) (SkewMonoidAlgebra R (Multiplicative ℤ))) := by
  exact ⟨RingEquiv.ofBijective (skewMatrixToHom R k)
    ⟨skewMatrixToHom_injective R k, skewMatrixToHom_surjective R k⟩⟩

end Work.ORHughesFree.NaturalExtension
