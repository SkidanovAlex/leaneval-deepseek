import Submission.ZagierHoffmanProof.ABPVanishing
import Submission.ZagierHoffmanProof.EntireTwist

/-!
# The key identity of the ABP criterion

For a matrix `Θ` of power series with `Θ * Φ = det Φ • 1` and a vector `ψ` satisfying the twisted
functional equation `ψ = Φ^{(1)} • ψ^{(1)}`, the `M`-fold product
`keyProd Θ M = Θ^{(M)} · Θ^{(M-1)} · ⋯ · Θ^{(1)}` satisfies the **key identity**

  `(keyProd Θ M) • ψ = (∏_{k=1}^{M} (det Φ)^{(k)}) • ψ^{(M)}`.
-/

set_option autoImplicit false
open Polynomial Matrix
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] {q : ℕ} [FrobPow K q]

/-- The Frobenius twist is additive on finite sums. -/
lemma frobTwist_sum {ι : Type*} (k : ℕ) (s : Finset ι) (f : ι → PowerSeries K) :
    frobTwist (R := K) (p := q) k (∑ i ∈ s, f i)
      = ∑ i ∈ s, frobTwist (R := K) (p := q) k (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, frobTwist_add, ih]

/-- The Frobenius twist of a matrix of power series (entrywise). -/
noncomputable def frobTwistMat {m n : Type*} (k : ℕ) (A : Matrix m n (PowerSeries K)) :
    Matrix m n (PowerSeries K) :=
  A.map (frobTwist (R := K) (p := q) k)

/-- The Frobenius twist of a vector of power series. -/
noncomputable def frobTwistVec {n : Type*} (k : ℕ) (v : n → PowerSeries K) : n → PowerSeries K :=
  fun i => frobTwist (R := K) (p := q) k (v i)

lemma frobTwistVec_apply {n : Type*} (k : ℕ) (v : n → PowerSeries K) (i : n) :
    frobTwistVec (q := q) k v i = frobTwist (R := K) (p := q) k (v i) := rfl

lemma frobTwistMat_apply {m n : Type*} (k : ℕ) (A : Matrix m n (PowerSeries K))
    (i : m) (j : n) :
    frobTwistMat (q := q) k A i j = frobTwist (R := K) (p := q) k (A i j) := rfl

/-- The twist commutes with the matrix-vector product. -/
lemma frobTwistMat_mulVec {m n : Type*} [Fintype n] (k : ℕ)
    (A : Matrix m n (PowerSeries K)) (v : n → PowerSeries K) :
    (frobTwistMat (q := q) k A).mulVec (frobTwistVec (q := q) k v)
      = frobTwistVec (q := q) k (A.mulVec v) := by
  funext i
  show (∑ j, frobTwist (R := K) (p := q) k (A i j) * frobTwist (R := K) (p := q) k (v j))
    = frobTwist (R := K) (p := q) k (∑ j, A i j * v j)
  rw [frobTwist_sum]
  exact Finset.sum_congr rfl fun j _ =>
    (frobTwist_mul (R := K) (p := q) k (A i j) (v j)).symm

lemma frobTwistMat_mul {l m n : Type*} [Fintype m] (k : ℕ)
    (A : Matrix l m (PowerSeries K)) (B : Matrix m n (PowerSeries K)) :
    frobTwistMat (q := q) k (A * B)
      = frobTwistMat (q := q) k A * frobTwistMat (q := q) k B := by
  funext i j
  show frobTwist (R := K) (p := q) k (∑ b, A i b * B b j)
    = ∑ b, frobTwist (R := K) (p := q) k (A i b) * frobTwist (R := K) (p := q) k (B b j)
  rw [frobTwist_sum]
  exact Finset.sum_congr rfl fun b _ =>
    frobTwist_mul (R := K) (p := q) k (A i b) (B b j)

lemma frobTwistMat_one {n : Type*} [DecidableEq n] (k : ℕ) :
    frobTwistMat (q := q) k (1 : Matrix n n (PowerSeries K)) = 1 := by
  ext i j
  simp only [frobTwistMat_apply, Matrix.one_apply]
  by_cases h : i = j
  · simp [h, frobTwist_one]
  · simp [h, frobTwist_zero]

lemma frobTwistMat_smul_one {n : Type*} [DecidableEq n] (k : ℕ) (c : PowerSeries K) :
    frobTwistMat (q := q) k (c • (1 : Matrix n n (PowerSeries K)))
      = (frobTwist (R := K) (p := q) k c) • 1 := by
  ext i j
  simp only [frobTwistMat_apply, Matrix.smul_apply, Matrix.one_apply]
  by_cases h : i = j
  · simp [h, smul_eq_mul]
  · simp [h, smul_eq_mul]

lemma frobTwistMat_det {n : Type*} [Fintype n] [DecidableEq n] (k : ℕ)
    (A : Matrix n n (PowerSeries K)) :
    (frobTwistMat (q := q) k A).det = frobTwist (R := K) (p := q) k A.det :=
  ((frobTwistHom (R := K) (p := q) k).map_det A).symm

lemma frobTwistMat_comp {m n : Type*} (k l : ℕ) (A : Matrix m n (PowerSeries K)) :
    frobTwistMat (q := q) k (frobTwistMat (q := q) l A)
      = frobTwistMat (q := q) (k + l) A := by
  funext i j
  show frobTwist (R := K) (p := q) k (frobTwist (R := K) (p := q) l (A i j))
    = frobTwist (R := K) (p := q) (k + l) (A i j)
  rw [frobTwist_comp]

lemma frobTwistVec_comp {n : Type*} (k l : ℕ) (v : n → PowerSeries K) :
    frobTwistVec (q := q) k (frobTwistVec (q := q) l v)
      = frobTwistVec (q := q) (k + l) v := by
  funext i
  show frobTwist (R := K) (p := q) k (frobTwist (R := K) (p := q) l (v i))
    = frobTwist (R := K) (p := q) (k + l) (v i)
  rw [frobTwist_comp]

lemma frobTwistVec_zero_eq {n : Type*} (v : n → PowerSeries K) :
    frobTwistVec (q := q) 0 v = v := by
  funext i
  show frobTwist (R := K) (p := q) 0 (v i) = v i
  ext k
  rw [frobTwist_coeff, pow_zero, pow_one]

/-- The `M`-fold product `Θ^{(M)} · Θ^{(M-1)} · ⋯ · Θ^{(1)}`. -/
noncomputable def keyProd {ℓ : ℕ} (Θ : Matrix (Fin ℓ) (Fin ℓ) (PowerSeries K)) :
    ℕ → Matrix (Fin ℓ) (Fin ℓ) (PowerSeries K)
  | 0 => 1
  | (M + 1) => frobTwistMat (q := q) (M + 1) Θ * keyProd Θ M

lemma keyProd_zero {ℓ : ℕ} (Θ : Matrix (Fin ℓ) (Fin ℓ) (PowerSeries K)) :
    keyProd (q := q) Θ 0 = 1 := rfl

lemma keyProd_succ {ℓ : ℕ} (Θ : Matrix (Fin ℓ) (Fin ℓ) (PowerSeries K)) (M : ℕ) :
    keyProd (q := q) Θ (M + 1)
      = frobTwistMat (q := q) (M + 1) Θ * keyProd (q := q) Θ M := rfl

/-- The twisted functional equation `ψ = Φ^{(1)} • ψ^{(1)}` implies its `k`-fold twist. -/
lemma frobTwistVec_functional {ℓ : ℕ} {Φ : Matrix (Fin ℓ) (Fin ℓ) (PowerSeries K)}
    {ψ : Fin ℓ → PowerSeries K}
    (hfe : ψ = (frobTwistMat (q := q) 1 Φ).mulVec (frobTwistVec (q := q) 1 ψ)) (k : ℕ) :
    frobTwistVec (q := q) k ψ
      = (frobTwistMat (q := q) (k + 1) Φ).mulVec (frobTwistVec (q := q) (k + 1) ψ) := by
  have h := congrArg (frobTwistVec (q := q) k) hfe
  rw [← frobTwistMat_mulVec, frobTwistMat_comp, frobTwistVec_comp] at h
  exact h

/-- ★★★ **The key identity of the ABP criterion.** -/
theorem key_identity {ℓ : ℕ} {Φ Θ : Matrix (Fin ℓ) (Fin ℓ) (PowerSeries K)}
    (hadj : Θ * Φ = Φ.det • 1)
    {ψ : Fin ℓ → PowerSeries K}
    (hfe : ψ = (frobTwistMat (q := q) 1 Φ).mulVec (frobTwistVec (q := q) 1 ψ)) (M : ℕ) :
    (keyProd (q := q) Θ M).mulVec ψ
      = (∏ k ∈ Finset.Icc 1 M, frobTwist (R := K) (p := q) k Φ.det)
        • frobTwistVec (q := q) M ψ := by
  induction M with
  | zero =>
      rw [keyProd_zero, Matrix.one_mulVec, frobTwistVec_zero_eq]
      simp
  | succ M ih =>
      rw [keyProd_succ, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul,
        frobTwistVec_functional hfe M, Matrix.mulVec_mulVec, ← frobTwistMat_mul, hadj,
        frobTwistMat_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul]
      congr 1
      exact (Finset.prod_Icc_succ_top (a := 1) (by omega : 1 ≤ M + 1)
        (fun k => frobTwist (R := K) (p := q) k Φ.det)).symm

end ZagierHoffmanPositiveChar
