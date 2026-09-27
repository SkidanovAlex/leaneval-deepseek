import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.Fund.kbi_kron_A_mul_B

/-!
# `p ⊗ E₀₀ ≅ p` for an idempotent matrix `p`

For an idempotent square matrix `p` over an arbitrary (not necessarily commutative) ring `R`, the
Kronecker product of `p` with the rank-one projection `E₀₀ = diag(1,0)` on `R²` is Murray–von
Neumann equivalent to `p`: tensoring a finitely generated projective module with the free module
`R` changes nothing.

The witnesses are, with indices transported across `finProdFinEquiv : Fin n × Fin 2 ≃ Fin (n*2)`,

* `A : Matrix (Fin n) (Fin (n * 2)) R`, `A j (k, k') = if k' = 0 then p j k else 0`
  (the inclusion `p R^n ↪ p R^n ⊗ R²` onto the `E₀₀` summand),
* `B : Matrix (Fin (n * 2)) (Fin n) R`, `B (k, k') j = if k' = 0 then p k j else 0`
  (the projection `p R^n ⊗ R² ↠ p R^n` along `E₀₀`).

The two identities are `A * B = p * p = p` (multiplied out over the middle index `Fin n × Fin 2`)
and `B * A = p ⊗ E₀₀` (multiplied out over the middle index `Fin n`, using `p * p = p`).  Both
computations avoid any commutation of `R`, so the result holds in a non-commutative ring; this is
why the proof does not go through the general Murray–von Neumann calculus of `KronMat`, which
needs commutativity.
-/

namespace Work.KT.Fund

open Matrix

/-- The inclusion `p Rⁿ ↪ p Rⁿ ⊗ R²` onto the `E₀₀` summand, as a `n × (n*2)` matrix. -/
def kbi_kron_E00_A {R : Type} [Ring R] (n : ℕ) (P : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin (n * 2)) R :=
  Matrix.reindex (Equiv.refl (Fin n)) finProdFinEquiv
    (Matrix.of fun (j : Fin n) (x : Fin n × Fin 2) => if x.2 = 0 then P j x.1 else 0)

/-- The projection `p Rⁿ ⊗ R² ↠ p Rⁿ` off the `E₀₀` summand, as a `(n*2) × n` matrix. -/
def kbi_kron_E00_B {R : Type} [Ring R] (n : ℕ) (P : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n * 2)) (Fin n) R :=
  Matrix.reindex finProdFinEquiv (Equiv.refl (Fin n))
    (Matrix.of fun (x : Fin n × Fin 2) (j : Fin n) => if x.2 = 0 then P x.1 j else 0)

/-- `B * A = P ⊗ E₀₀`, computed on the product index set `Fin n × Fin 2` over the middle index
`Fin n` (so no commutation of `R` is needed). -/
theorem kbi_kron_E00_B_mul_A {R : Type} [Ring R] {n : ℕ} (P : Matrix (Fin n) (Fin n) R)
    (hP : P * P = P) :
    (Matrix.of fun (x : Fin n × Fin 2) (j : Fin n) => if x.2 = 0 then P x.1 j else 0) *
      (Matrix.of fun (j : Fin n) (x : Fin n × Fin 2) => if x.2 = 0 then P j x.1 else 0) =
    Matrix.kroneckerMap (· * ·) P (Matrix.of fun i j : Fin 2 => if i = 0 ∧ j = 0 then (1 : R) else 0) := by
  ext i j
  rw [Matrix.mul_apply, Matrix.kroneckerMap_apply]
  by_cases hi : i.2 = 0 <;> by_cases hj : j.2 = 0 <;>
    simp [hi, hj, ← Matrix.mul_apply, hP]

/-- The same identity for the reindexed witnesses: `B * A = p ⊗ E₀₀`. -/
theorem kbi_kron_E00_B_mul_A_reindexed {R : Type} [Ring R] {n : ℕ}
    (P : Matrix (Fin n) (Fin n) R) (hP : P * P = P) :
    kbi_kron_E00_B n P * kbi_kron_E00_A n P =
    Matrix.reindex finProdFinEquiv finProdFinEquiv
      (Matrix.kroneckerMap (· * ·) P (Matrix.of fun i j : Fin 2 => if i = 0 ∧ j = 0 then (1 : R) else 0)) := by
  show (Matrix.reindex finProdFinEquiv (Equiv.refl (Fin n))
        (Matrix.of fun (x : Fin n × Fin 2) (j : Fin n) => if x.2 = 0 then P x.1 j else 0)) *
      (Matrix.reindex (Equiv.refl (Fin n)) finProdFinEquiv
        (Matrix.of fun (j : Fin n) (x : Fin n × Fin 2) => if x.2 = 0 then P j x.1 else 0)) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.kroneckerMap (· * ·) P (Matrix.of fun i j : Fin 2 => if i = 0 ∧ j = 0 then (1 : R) else 0))
  rw [reindexMul, kbi_kron_E00_B_mul_A P hP]

/-- The identity `A * B = p * p = p` for the reindexed witnesses. -/
theorem kbi_kron_E00_A_mul_B_reindexed {R : Type} [Ring R] {n : ℕ}
    (P : Matrix (Fin n) (Fin n) R) (hP : P * P = P) :
    kbi_kron_E00_A n P * kbi_kron_E00_B n P = P := by
  show (Matrix.reindex (Equiv.refl (Fin n)) finProdFinEquiv
        (Matrix.of fun (j : Fin n) (x : Fin n × Fin 2) => if x.2 = 0 then P j x.1 else 0)) *
      (Matrix.reindex finProdFinEquiv (Equiv.refl (Fin n))
        (Matrix.of fun (x : Fin n × Fin 2) (j : Fin n) => if x.2 = 0 then P x.1 j else 0)) = P
  rw [reindexMul, kbi_kron_A_mul_B P, hP, Matrix.reindex_refl_refl]

theorem kbi_kron_E00 {R : Type} [Ring R] (p : Work.KT.Mat R) (hp : p.IsIdem) :
    Work.KT.Mat.MvN (p.kron ⟨2, (Matrix.of fun i j : Fin 2 => if i = 0 ∧ j = 0 then (1 : R) else 0)⟩) p := by
  exact ⟨kbi_kron_E00_A p.1 p.2, kbi_kron_E00_B p.1 p.2,
    kbi_kron_E00_B_mul_A_reindexed p.2 hp, kbi_kron_E00_A_mul_B_reindexed p.2 hp⟩

end Work.KT.Fund
