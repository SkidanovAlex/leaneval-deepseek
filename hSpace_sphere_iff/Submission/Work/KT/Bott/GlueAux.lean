import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.cls_eq_stable_mvN
import Submission.Work.KT.k0_rep
import Submission.Work.KT.K0map.map_comp

/-!
# `Work.KT.Bott.GlueAux` — matrix bookkeeping for the Mayer–Vietoris injectivity of `K₀`

Infrastructure shared by `Work.KT.Bott.k0_mv_inj` and the glueing lemma
`Work.KT.Bott.mvN_glue`:

* `blk t A` — the block matrix `diag(A, 1_t)` (rectangular `A` allowed);
* `blk_mul`, `blk_map`, `blk_one` — `blk` is multiplicative, intertwines entrywise images and
  sends identities to identities;
* `Mat.map_one'`, `Mat.map_sum'` — `Mat.map` on identities and block sums;
* `mat_ext_of_maps`, `mat_lift` — the cartesian square: a square matrix over `P` is determined by
  its two images, and a compatible pair of matrices over `P₁`, `P₂` has a common preimage;
* `k0map_cls` — `K₀(φ)` on the class of an idempotent matrix.
-/

namespace Work.KT.Bott

open Matrix

noncomputable section

/-! ## Elementary `Matrix.map` lemmas -/

lemma matrix_map_zero {R S : Type} [Ring R] [Ring S] {m n : Type} (φ : R →+* S) :
    (0 : Matrix m n R).map φ = 0 := by
  ext i j; simp [Matrix.map_apply]

lemma matrix_map_one {R S : Type} [Ring R] [Ring S] {n : Type} [Fintype n] [DecidableEq n]
    (φ : R →+* S) : (1 : Matrix n n R).map φ = 1 := by
  ext i j
  rw [Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases h : i = j <;> simp [h]

lemma matrix_reindex_one {R : Type} [Ring R] {ι ι' : Type} [Fintype ι] [Fintype ι']
    [DecidableEq ι] [DecidableEq ι'] (e : ι ≃ ι') :
    Matrix.reindex e e (1 : Matrix ι ι R) = 1 := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply, e.symm.injective.eq_iff]

lemma matrix_map_map {R S T : Type} [Ring R] [Ring S] [Ring T] {m n : Type}
    (φ : R →+* S) (ψ : S →+* T) (M : Matrix m n R) :
    (M.map φ).map ψ = M.map (ψ.comp φ) := by
  ext i j; simp [Matrix.map_apply]

/-- The entrywise image of an identity matrix. -/
lemma Mat.map_one' {R S : Type} [Ring R] [Ring S] (φ : R →+* S) (n : ℕ) :
    (Mat.one R n).map φ = Mat.one S n := by
  simp [Mat.one, Mat.map]

/-- `Mat.map` commutes with the block sum. -/
lemma Mat.map_sum' {R S : Type} [Ring R] [Ring S] (φ : R →+* S) (p q : Mat R) :
    (p.sum q).map φ = (p.map φ).sum (q.map φ) := by
  obtain ⟨n, M⟩ := p
  obtain ⟨k, N⟩ := q
  show (⟨n + k, (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks M 0 0 N)).map φ⟩ : Mat S) =
    (⟨n + k, Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (M.map φ) 0 0 (N.map φ))⟩ : Mat S)
  rw [Matrix.reindex_apply, Matrix.reindex_apply, ← Matrix.submatrix_map, Matrix.fromBlocks_map]
  simp only [matrix_map_zero]

/-! ## Block matrices `diag(A, 1_t)` -/

/-- The block matrix `diag(A, 1_t)`, of size `N + t` by `M + t`. -/
def blk {R : Type} [Ring R] {N M : ℕ} (t : ℕ) (A : Matrix (Fin N) (Fin M) R) :
    Matrix (Fin (N + t)) (Fin (M + t)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin t) (Fin t) R))

/-- `blk` of a `Mat` is its block sum with an identity block. -/
lemma blk_mat_sum {R : Type} [Ring R] (p : Mat R) (k : ℕ) :
    blk k p.2 = (p.sum (Mat.one R k)).2 := rfl

lemma blk_mul {R : Type} [Ring R] {N M L : ℕ} (t : ℕ) (A : Matrix (Fin N) (Fin M) R)
    (B : Matrix (Fin M) (Fin L) R) : blk t A * blk t B = blk t (A * B) := by
  unfold blk
  rw [Work.KT.reindexMul, Matrix.fromBlocks_multiply]
  simp

lemma blk_map {R S : Type} [Ring R] [Ring S] {N M : ℕ} (φ : R →+* S) (t : ℕ)
    (A : Matrix (Fin N) (Fin M) R) : (blk t A).map φ = blk t (A.map φ) := by
  unfold blk
  rw [Matrix.reindex_apply, Matrix.reindex_apply, ← Matrix.submatrix_map, Matrix.fromBlocks_map]
  simp only [matrix_map_zero, matrix_map_one]

/-- Explicit factorization data from a Murray–von Neumann equivalence `M ⊕ 1_a ~ 1_{N+a}`:
rectangular matrices `A`, `B` of the stated sizes with `B * A = blk a M` and `A * B = 1`. -/
lemma exists_factor_of_mvN {R : Type} [Ring R] {m : ℕ} (M : Matrix (Fin m) (Fin m) R)
    (N a : ℕ) (h : Mat.MvN (⟨m + a, blk a M⟩ : Mat R) (Mat.one R (N + a))) :
    ∃ (A : Matrix (Fin (N + a)) (Fin (m + a)) R) (B : Matrix (Fin (m + a)) (Fin (N + a)) R),
      B * A = blk a M ∧ A * B = 1 := h

lemma blk_one {R : Type} [Ring R] {N : ℕ} (t : ℕ) :
    blk t (1 : Matrix (Fin N) (Fin N) R) = 1 := by
  unfold blk
  rw [Matrix.fromBlocks_one, matrix_reindex_one]

/-! ## The cartesian square -/

/-- Cartesianity: a matrix over `P` is determined by its two images. -/
lemma mat_ext_of_maps {P P₁ P₂ Q : Type} [Ring P] [Ring P₁] [Ring P₂] [Ring Q]
    (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hcomm : σ₁.comp ρ₁ = σ₂.comp ρ₂)
    (hpb : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂)
    {m : ℕ} {A B : Matrix (Fin m) (Fin m) P}
    (h1 : A.map ρ₁ = B.map ρ₁) (h2 : A.map ρ₂ = B.map ρ₂) : A = B := by
  ext i j
  have h1' : ρ₁ (B i j) = ρ₁ (A i j) := by
    have h := congrFun (congrFun h1 i) j
    rw [Matrix.map_apply, Matrix.map_apply] at h
    exact h.symm
  have h2' : ρ₂ (B i j) = ρ₂ (A i j) := by
    have h := congrFun (congrFun h2 i) j
    rw [Matrix.map_apply, Matrix.map_apply] at h
    exact h.symm
  have hq : σ₁ (ρ₁ (A i j)) = σ₂ (ρ₂ (A i j)) := by
    have h := congrArg (fun (f : P →+* Q) => f (A i j)) hcomm
    simpa using h
  exact (hpb (ρ₁ (A i j)) (ρ₂ (A i j)) hq).unique ⟨rfl, rfl⟩ ⟨h1', h2'⟩

/-- A pair of matrices with entrywise matching images in `Q` is the pair of images of a matrix
over `P`. -/
lemma mat_lift {P P₁ P₂ Q : Type} [Ring P] [Ring P₁] [Ring P₂] [Ring Q]
    (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hpb : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂)
    {m l : ℕ} (N₁ : Matrix (Fin m) (Fin l) P₁) (N₂ : Matrix (Fin m) (Fin l) P₂)
    (h : ∀ i j, σ₁ (N₁ i j) = σ₂ (N₂ i j)) :
    ∃ Ê : Matrix (Fin m) (Fin l) P, Ê.map ρ₁ = N₁ ∧ Ê.map ρ₂ = N₂ := by
  refine ⟨fun i j => (hpb (N₁ i j) (N₂ i j) (h i j)).choose, ?_, ?_⟩
  · ext i j
    show ρ₁ ((hpb (N₁ i j) (N₂ i j) (h i j)).choose) = N₁ i j
    exact ((hpb (N₁ i j) (N₂ i j) (h i j)).choose_spec).1.1
  · ext i j
    show ρ₂ ((hpb (N₁ i j) (N₂ i j) (h i j)).choose) = N₂ i j
    exact ((hpb (N₁ i j) (N₂ i j) (h i j)).choose_spec).1.2

/-- A pair of matrices whose images in `Q` agree (as matrices) is the pair of images of a matrix
over `P`. -/
lemma mat_lift' {P P₁ P₂ Q : Type} [Ring P] [Ring P₁] [Ring P₂] [Ring Q]
    (ρ₁ : P →+* P₁) (ρ₂ : P →+* P₂) (σ₁ : P₁ →+* Q) (σ₂ : P₂ →+* Q)
    (hpb : ∀ x₁ x₂, σ₁ x₁ = σ₂ x₂ → ∃! x, ρ₁ x = x₁ ∧ ρ₂ x = x₂)
    {m l : ℕ} (N₁ : Matrix (Fin m) (Fin l) P₁) (N₂ : Matrix (Fin m) (Fin l) P₂)
    (h : N₁.map σ₁ = N₂.map σ₂) :
    ∃ Ê : Matrix (Fin m) (Fin l) P, Ê.map ρ₁ = N₁ ∧ Ê.map ρ₂ = N₂ := by
  refine mat_lift ρ₁ ρ₂ σ₁ σ₂ hpb N₁ N₂ (fun i j => ?_)
  have hh := congrFun (congrFun h i) j
  rwa [Matrix.map_apply, Matrix.map_apply] at hh

/-! ## `K₀` on generators -/

/-- `K₀(φ)` on the class of an idempotent matrix. -/
lemma k0map_cls {R S : Type} [Ring R] [Ring S] (φ : R →+* S) {p : Mat R} (hp : p.IsIdem) :
    K0.map φ (cls p) = cls (p.map φ) := by
  rw [Work.KT.K0map.map_cls, mapCls, if_pos hp]

end

end Work.KT.Bott
