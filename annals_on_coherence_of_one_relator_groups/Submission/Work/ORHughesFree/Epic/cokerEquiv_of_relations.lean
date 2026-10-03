/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The cokernels of related matrices are isomorphic

Let `A : m × n`, `B : m' × n'`, `P : n' × n` and `G : n × n'` be matrices over a ring `R`.
Suppose there are matrices making the four relations

* `B * P = W * A`,  * `G * P = 1 + Z * A`,  * `A * G = X * B`,  * `P * G = 1 + Z' * B`

hold.  Then right multiplication by `P` and by `G` induce mutually inverse linear maps between
the cokernels `cokerMat A = R^n / R^m A` and `cokerMat B = R^{n'} / R^{m'} B`:

* `B * P = W * A` says exactly that the row space of `B` is carried into the row space of `A`
  by `P`, so that `v ↦ v ᵥ* P` descends to `cokerMat B → cokerMat A`;
* `G * P = 1 + Z * A` says that on `cokerMat A` the composite `P` then `G` is the identity,
  since `1 + Z * A` differs from the identity by an element of the row space of `A` (and
  symmetrically for the other composite with `P * G = 1 + Z' * B`).

Consequently `cokerMat A ≃ₗ[R] cokerMat B`.  This is the converse of the construction in
`Epic/fpDim_eq_of_presentation.lean`, where such a pair `P`, `G` is produced from a given
linear equivalence of the cokernels.
-/
import Mathlib
import Submission.Work.ORHughesFree.Epic.rk_blkM_defs

set_option autoImplicit false

namespace Work.ORHughesFree.Epic

open Matrix

/-! ## Elementary identities for the row map of a matrix

These are the analogues, for the concrete row map `rowMulLin` of `DimTheory`, of the
corresponding statements used elsewhere in the project; they are reproduced here so that this
file only depends on the definitions and not on any other development. -/

private theorem rowMulLin_mul' {R : Type*} [Ring R] {a b c : ℕ}
    (M : Matrix (Fin a) (Fin b) R) (N : Matrix (Fin b) (Fin c) R) :
    rowMulLin (M * N) = (rowMulLin N).comp (rowMulLin M) := by
  refine LinearMap.ext fun v => ?_
  refine funext fun j => ?_
  show (∑ i, v i * (∑ k, M i k * N k j)) = ∑ k, (∑ i, v i * M i k) * N k j
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_assoc]

private theorem rowMulLin_add' {R : Type*} [Ring R] {a b : ℕ}
    (M N : Matrix (Fin a) (Fin b) R) :
    rowMulLin (M + N) = rowMulLin M + rowMulLin N := by
  refine LinearMap.ext fun v => ?_
  refine funext fun j => ?_
  show (∑ i, v i * (M + N) i j) = (∑ i, v i * M i j) + (∑ i, v i * N i j)
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]

private theorem rowMulLin_one' {R : Type*} [Ring R] (a : ℕ) :
    rowMulLin (1 : Matrix (Fin a) (Fin a) R) = LinearMap.id := by
  refine LinearMap.ext fun v => ?_
  refine funext fun j => ?_
  show (∑ i, v i * (1 : Matrix (Fin a) (Fin a) R) i j) = v j
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [Matrix.one_apply_ne hij, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- `1 + Z * A` acts on a vector of length `n` as `v ↦ v + (v ᵥ* Z) ᵥ* A`. -/
private theorem rowMulLin_one_add' {R : Type*} [Ring R] {n m : ℕ}
    (Z : Matrix (Fin n) (Fin m) R) (A : Matrix (Fin m) (Fin n) R) :
    rowMulLin ((1 : Matrix (Fin n) (Fin n) R) + Z * A)
      = LinearMap.id + (rowMulLin A).comp (rowMulLin Z) := by
  rw [rowMulLin_add', rowMulLin_one', rowMulLin_mul']

theorem cokerEquiv_of_relations {R : Type*} [Ring R] {m n m' n' : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin m') (Fin n') R)
    (P : Matrix (Fin n') (Fin n) R) (G : Matrix (Fin n) (Fin n') R)
    (h1 : ∃ W : Matrix (Fin m') (Fin m) R, B * P = W * A)
    (h2 : ∃ Z : Matrix (Fin n) (Fin m) R, G * P = 1 + Z * A)
    (h3 : ∃ X : Matrix (Fin m) (Fin m') R, A * G = X * B)
    (h4 : ∃ Z' : Matrix (Fin n') (Fin m') R, P * G = 1 + Z' * B) :
    Nonempty (Work.ORHughesFree.Epic.cokerMat A ≃ₗ[R] Work.ORHughesFree.Epic.cokerMat B) := by
  obtain ⟨W, hW⟩ := h1
  obtain ⟨Z, hZ⟩ := h2
  obtain ⟨X, hX⟩ := h3
  obtain ⟨Z', hZ'⟩ := h4
  -- `B * P = W * A` puts the row space of `B` into the preimage of that of `A` under `P`
  have hleP : LinearMap.range (rowMulLin B)
      ≤ (LinearMap.range (rowMulLin A)).comap (rowMulLin P) := by
    intro v hv
    rw [Submodule.mem_comap]
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hv
    refine LinearMap.mem_range.mpr ⟨rowMulLin W u, ?_⟩
    have key : (rowMulLin P).comp (rowMulLin B) = (rowMulLin A).comp (rowMulLin W) := by
      rw [← rowMulLin_mul', ← rowMulLin_mul', hW]
    simpa only [LinearMap.comp_apply] using (LinearMap.congr_fun key u).symm
  -- `A * G = X * B` puts the row space of `A` into the preimage of that of `B` under `G`
  have hleG : LinearMap.range (rowMulLin A)
      ≤ (LinearMap.range (rowMulLin B)).comap (rowMulLin G) := by
    intro v hv
    rw [Submodule.mem_comap]
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hv
    refine LinearMap.mem_range.mpr ⟨rowMulLin X u, ?_⟩
    have key : (rowMulLin G).comp (rowMulLin A) = (rowMulLin B).comp (rowMulLin X) := by
      rw [← rowMulLin_mul', ← rowMulLin_mul', hX]
    simpa only [LinearMap.comp_apply] using (LinearMap.congr_fun key u).symm
  set φ : cokerMat B →ₗ[R] cokerMat A :=
    (LinearMap.range (rowMulLin B)).mapQ (LinearMap.range (rowMulLin A)) (rowMulLin P) hleP
    with hφ
  set ψ : cokerMat A →ₗ[R] cokerMat B :=
    (LinearMap.range (rowMulLin A)).mapQ (LinearMap.range (rowMulLin B)) (rowMulLin G) hleG
    with hψ
  -- `G * P = 1 + Z * A` makes `φ ∘ ψ` the identity on `cokerMat A`
  have hleft : Function.LeftInverse φ ψ := by
    intro x
    rw [hφ, hψ]
    refine Submodule.Quotient.induction_on (LinearMap.range (rowMulLin A)) x fun v => ?_
    rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq]
    have hv : rowMulLin P (rowMulLin G v)
        = rowMulLin ((1 : Matrix (Fin n) (Fin n) R) + Z * A) v := by
      rw [← LinearMap.comp_apply, ← rowMulLin_mul', hZ]
    rw [hv, rowMulLin_one_add']
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply]
    exact LinearMap.mem_range.mpr ⟨rowMulLin Z v, by rw [add_sub_cancel_left]⟩
  -- `P * G = 1 + Z' * B` makes `ψ ∘ φ` the identity on `cokerMat B`
  have hright : Function.LeftInverse ψ φ := by
    intro x
    rw [hφ, hψ]
    refine Submodule.Quotient.induction_on (LinearMap.range (rowMulLin B)) x fun v => ?_
    rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq]
    have hv : rowMulLin G (rowMulLin P v)
        = rowMulLin ((1 : Matrix (Fin n') (Fin n') R) + Z' * B) v := by
      rw [← LinearMap.comp_apply, ← rowMulLin_mul', hZ']
    rw [hv, rowMulLin_one_add']
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply]
    exact LinearMap.mem_range.mpr ⟨rowMulLin Z' v, by rw [add_sub_cancel_left]⟩
  exact ⟨(LinearEquiv.ofBijective φ ⟨hright.injective, hleft.surjective⟩).symm⟩

end Work.ORHughesFree.Epic
