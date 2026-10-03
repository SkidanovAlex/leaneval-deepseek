/-
# `rdim` is invariant under a linear map admitting a left inverse

For a ring `R` with a Sylvester rank function `rk`, a submodule `K ≤ R^n` and a linear map
`φ : R^n → R^N` admitting a left inverse `ψ` (`ψ ∘ φ = id`), the row-wise dimension `rdim`
(see `DualityDefs.lean`) satisfies `rdim rk (K.map φ) = rdim rk K`.

The proof identifies the two defining sets of `rdim`.  Writing `M = toMatrixRight' φ` and
`M' = toMatrixRight' ψ` for the matrices of `φ` and `ψ` (so that `φ x = x ᵥ* M`, and the
hypothesis `ψ ∘ φ = id` becomes `M * M' = 1`):

* the rows of `B * M` are `φ` applied to the rows of `B`, so multiplying matrices whose rows
  lie in `K` on the right by `M` produces exactly the matrices whose rows lie in `K.map φ`;
* by `SylvesterRank.rk_eq_of_mul_right_inverse`, multiplying a matrix on the right by `M`
  (which has the right inverse `M'`) does not change its rank.

Hence a real number occurs in the defining set of `rdim rk (K.map φ)` iff it occurs in the
defining set of `rdim rk K`, and the two suprema agree.  In particular no instance of
`VonNeumannRegularRing R` is needed.
-/
import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.NaturalExtension.DualityAPI

set_option autoImplicit false

universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix Work.ORHughesFree

/-- The rows of `B * M`, where `M = toMatrixRight' φ` is the matrix of a linear map
`φ : R^n → R^N`, are the images under `φ` of the rows of `B`. -/
theorem row_mul_toMatrixRight' {R : Type u} [Ring R] {m n N : ℕ}
    (B : Matrix (Fin m) (Fin n) R) (φ : (Fin n → R) →ₗ[R] (Fin N → R)) :
    (fun i : Fin m => Matrix.row (B * LinearMap.toMatrixRight' φ) i) =
      fun i : Fin m => φ (Matrix.row B i) := by
  have hφM : Matrix.toLinearMapRight' (LinearMap.toMatrixRight' φ) = φ :=
    LinearEquiv.apply_symm_apply Matrix.toLinearMapRight' φ
  funext i j
  rw [← hφM, Matrix.toLinearMapRight'_apply]
  simp [Matrix.mul_apply, Matrix.vecMul_apply, Matrix.row, dotProduct]

/-- Multiplying a matrix on the right by the matrix `M = toMatrixRight' φ` of a linear map with a
left inverse does not change its Sylvester rank. -/
theorem rk_mul_toMatrixRight' {R : Type u} [Ring R] (rk : SylvesterRank R) {m n N : ℕ}
    {φ : (Fin n → R) →ₗ[R] (Fin N → R)} {ψ : (Fin N → R) →ₗ[R] (Fin n → R)}
    (h : ψ ∘ₗ φ = LinearMap.id) (B : Matrix (Fin m) (Fin n) R) :
    rk.rk m N (B * LinearMap.toMatrixRight' φ) = rk.rk m n B := by
  have hMM' : LinearMap.toMatrixRight' φ * LinearMap.toMatrixRight' ψ = 1 := by
    have hcomp := LinearMap.toMatrixRight'_comp φ ψ
    rw [h, LinearMap.toMatrixRight'_id] at hcomp
    exact hcomp.symm
  exact SylvesterRank.rk_eq_of_mul_right_inverse rk B _ _ hMM'

theorem rdim_map_of_leftInverse {R : Type u} [Ring R] (rk : SylvesterRank R) {n N : ℕ}
    {φ : (Fin n → R) →ₗ[R] (Fin N → R)} {ψ : (Fin N → R) →ₗ[R] (Fin n → R)}
    (h : ψ ∘ₗ φ = LinearMap.id) (K : Submodule R (Fin n → R)) :
    rdim rk (K.map φ) = rdim rk K := by
  classical
  have hset : {x : ℝ | ∃ (m : ℕ) (A : Matrix (Fin m) (Fin N) R),
        (∀ i, (fun j => A i j) ∈ K.map φ) ∧ x = rk.rk m N A} =
      {x : ℝ | ∃ (m : ℕ) (A : Matrix (Fin m) (Fin n) R),
        (∀ i, (fun j => A i j) ∈ K) ∧ x = rk.rk m n A} := by
    ext x
    constructor
    · -- every matrix with rows in `K.map φ` is `B * M` for a matrix `B` with rows in `K`
      rintro ⟨m, A, hA, rfl⟩
      have hb : ∀ i : Fin m, ∃ b ∈ K, φ b = Matrix.row A i :=
        fun i => Submodule.mem_map.mp (hA i)
      choose b hbK hbφ using hb
      refine ⟨m, Matrix.of fun i j => b i j, fun i => hbK i, ?_⟩
      have hAeq : A = Matrix.of (fun i j => b i j) * LinearMap.toMatrixRight' φ := by
        ext i j
        have h2 : (Matrix.of (fun i j => b i j) * LinearMap.toMatrixRight' φ) i j
            = φ (b i) j :=
          congrFun (congrFun (row_mul_toMatrixRight' (Matrix.of fun i j => b i j) φ) i) j
        rw [h2]
        exact (congrFun (hbφ i) j).symm
      rw [hAeq, rk_mul_toMatrixRight' rk h (Matrix.of fun i j => b i j)]
    · -- conversely, `B * M` has rows in `K.map φ` whenever `B` has rows in `K`
      rintro ⟨m, B, hB, rfl⟩
      refine ⟨m, B * LinearMap.toMatrixRight' φ, fun i => ?_,
        (rk_mul_toMatrixRight' rk h B).symm⟩
      show Matrix.row (B * LinearMap.toMatrixRight' φ) i ∈ K.map φ
      rw [congrFun (row_mul_toMatrixRight' B φ) i]
      exact Submodule.mem_map.mpr ⟨Matrix.row B i, hB i, rfl⟩
  unfold rdim
  rw [hset]

end Work.ORHughesFree.NaturalExtension
