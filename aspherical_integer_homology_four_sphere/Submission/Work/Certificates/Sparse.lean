/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Certificates/`: sparse integer vectors and sparse operators

This file fixes the *data format* of every linear-algebra certificate in this area.

A **sparse vector** in `ℤ^{n}` is a list of `(index, coefficient)` pairs, i.e. the formal sum
`∑ p ∈ v, p.2 • e_{p.1}`.  Its semantics is the function `SVec.toFun v : Fin n → ℤ` obtained by
summing the coefficients with a given index (repeated indices add up).  `SVec.norm` is the
normal form (indices strictly increasing, coefficients nonzero) and `SVec.eqb` compares normal
forms, so equality of sparse vectors can be *decided* at linear cost.

A **sparse operator** `A : SOp n m` is the data of the images `A.img j : SVec n` of the basis
vectors of `ℤ^{m}`; `A.toMatrix : Matrix (Fin n) (Fin m) ℤ` is its matrix in the standard bases
(so `toMatrix A` is the map `ℤ^{m} → ℤ^{n}`).  All operations used by the checkers -- `apply`,
`mul`, `add`, `neg`, `sub`, `smul`, `eqb` -- run on the sparse data, in time linear in its size;
the `toMatrix` API is used only to *state* (and prove) the soundness theorems.
-/

import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Certificates

/-- A sparse vector in `ℤ^{n}`: a list of `(index, coefficient)` pairs, to be read as the formal
sum `∑ p ∈ v, p.2 • e_{p.1}`. -/
abbrev SVec (n : ℕ) : Type := List (Fin n × ℤ)

namespace SVec

variable {n : ℕ}

/-- The element of `Fin n → ℤ` represented by a sparse vector: the sum of the coefficients
labelled by `i` (repeated indices are added up). -/
def toFun (v : SVec n) : Fin n → ℤ :=
  fun i => (v.map (fun p => if p.1 = i then p.2 else 0)).sum

/-- Insert `p` into a sparse vector whose indices are strictly increasing, combining equal
indices and dropping zero coefficients. -/
def insert (p : Fin n × ℤ) : SVec n → SVec n
  | [] => if p.2 = 0 then [] else [p]
  | q :: qs =>
      if p.1 < q.1 then (if p.2 = 0 then q :: qs else p :: q :: qs)
      else if p.1 = q.1 then
        (if p.2 + q.2 = 0 then qs else (q.1, p.2 + q.2) :: qs)
      else q :: insert p qs

/-- Normal form of a sparse vector: indices strictly increasing and coefficients nonzero. -/
def norm (v : SVec n) : SVec n := v.foldr insert []

/-- Sparse equality test: compare normal forms. -/
def eqb (a b : SVec n) : Bool := decide (a.norm = b.norm)

/-- Negation of a sparse vector (coefficientwise). -/
def neg (v : SVec n) : SVec n := v.map fun p => (p.1, -p.2)

/-- Difference of sparse vectors. -/
def sub (a b : SVec n) : SVec n := a ++ b.neg

end SVec

/-- A sparse operator `ℤ^{m} → ℤ^{n}`, given by the images of the basis vectors. -/
structure SOp (n m : ℕ) where
  /-- `img j` is the image of the `j`-th basis vector of `ℤ^{m}`. -/
  img : Fin m → SVec n

namespace SOp

variable {n m l : ℕ}

/-- The matrix of a sparse operator in the standard bases; its `j`-th column is the image of
the `j`-th basis vector.  Thus `toMatrix A : Matrix (Fin n) (Fin m) ℤ` is the matrix of the map
`ℤ^{m} → ℤ^{n}`. -/
def toMatrix (A : SOp n m) : Matrix (Fin n) (Fin m) ℤ := fun i j => (A.img j).toFun i

/-- The linear map of a sparse operator. -/
def toLin (A : SOp n m) : (Fin m → ℤ) →ₗ[ℤ] (Fin n → ℤ) := Matrix.toLin' A.toMatrix

/-- A sparse operator from a list of images of basis vectors, in order; positions beyond the
end of the list give zero. -/
def ofList (l : List (SVec n)) : SOp n m := ⟨fun j => l.getD j.1 []⟩

@[ext]
theorem ext {A B : SOp n m} (h : ∀ j, A.img j = B.img j) : A = B := by
  cases A; cases B; congr 1; exact funext h

/-- Sparse application of an operator to a sparse vector. -/
def apply (A : SOp n m) (v : SVec m) : SVec n :=
  (v.map fun p => (A.img p.1).map fun q => (q.1, q.2 * p.2)).flatten

/-- Sparse composition: `(A.mul B).img j = A (B e_j)`. -/
def mul (A : SOp n m) (B : SOp m l) : SOp n l := ⟨fun j => A.apply (B.img j)⟩

/-- The identity operator. -/
def id (n : ℕ) : SOp n n := ⟨fun j => [(j, 1)]⟩

/-- The zero operator. -/
def zero (n m : ℕ) : SOp n m := ⟨fun _ => []⟩

/-- Sum of operators. -/
def add (A B : SOp n m) : SOp n m := ⟨fun j => A.img j ++ B.img j⟩

/-- Negation of an operator. -/
def neg (A : SOp n m) : SOp n m := ⟨fun j => (A.img j).map fun q => (q.1, -q.2)⟩

/-- Difference of operators. -/
def sub (A B : SOp n m) : SOp n m := A.add B.neg

/-- Scalar multiple of an operator. -/
def smul (c : ℤ) (A : SOp n m) : SOp n m := ⟨fun j => (A.img j).map fun q => (q.1, q.2 * c)⟩

/-- Componentwise normal form. -/
def norm (A : SOp n m) : SOp n m := ⟨fun j => (A.img j).norm⟩

/-- Sparse equality test for operators. -/
def eqb (A B : SOp n m) : Bool := (List.finRange m).all (fun j => (A.img j).eqb (B.img j))

/-- The matrix of the zero operator is the zero matrix. -/
theorem toMatrix_zero (n m : ℕ) : (zero n m).toMatrix = 0 := by
  ext i j
  simp [SOp.toMatrix, SOp.zero, SVec.toFun]

end SOp

end Work.Certificates
