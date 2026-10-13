/-
  WilE9G / Lagrange — **the abstract block model of the Jacobian** `lagJac` / `lagJacTrue`.

  The two matrices `lagJac` and `lagJacTrue` of the Lagrange construction are indexed by
  `Fin ((1+m) + (S.j+1))` and are written, in their definitions, by splitting that index first into
  `Fin (1+m)` and `Fin (S.j+1)` and then splitting the second piece into `Fin S.j` and `Fin 1`
  (the multiplier `μ₀`).  This file fixes the corresponding **abstract block model**: a matrix
  `cM A W g mu mu0` on the index type `(Fin r ⊕ Fin j) ⊕ Fin 1` whose blocks are

  * `(L, yt)`: `A`,
  * `(L, μ_b)`: `- W i b`, `(L, μ₀)`: `g i`,
  * `(h_a, yt_k)`: `W k a`, `(h_a, μ_b)`: `0`, `(h_a, μ₀)`: `0`,
  * `(N, yt_k)`: `0`, `(N, μ_b)`: `2 μ b`, `(N, μ₀)`: `2 μ₀`.

  The pure linear algebra of the abstract model is proved in `lagJacTrue_det.lean`; the
  identification of `lagJac`/`lagJacTrue` with the model (via `lagA1`, `lagA2`, `lagW`, `lagG`
  and the index equivalence `cMEquiv`) is stated here for the delegated transfer lemmas.
-/
import Mathlib
import Submission.Work.WilE9G.Lagrange.Stratum
import Submission.Work.WilE3.API.eaD_commute

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE9G.Lagrange
open Matrix
open WilkiesDesign WilkiesDesign.E Work.WilE9G

/-! ## The abstract block matrix -/

/-- The core `(L,h) × (yt,μ)` block `[[A, -W],[Wᵀ,0]]` of the Lagrange Jacobian: the `(L, μ_b)`
entry is `- W i b` and the `(h_a, yt_k)` entry is `W k a`. -/
def cM0 {r j : ℕ} (A : Matrix (Fin r) (Fin r) ℝ) (W : Matrix (Fin r) (Fin j) ℝ) :
    Matrix (Fin r ⊕ Fin j) (Fin r ⊕ Fin j) ℝ :=
  Matrix.fromBlocks A (-W) Wᵀ 0

/-- The index equivalence between the index `Fin (r + (j+1))` of `lagJac` and the fully split
index `(Fin r ⊕ Fin j) ⊕ Fin 1` of the abstract block model `cM`.  It sends `i < r` to
`Sum.inl (Sum.inl i)`, `r ≤ i < r + j` to `Sum.inl (Sum.inr _)` and `i = r + j` to `Sum.inr 0`. -/
def cMEquiv (r j : ℕ) : Fin (r + (j + 1)) ≃ (Fin r ⊕ Fin j) ⊕ Fin 1 :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl (Fin r)) finSumFinEquiv.symm)).trans
    (Equiv.sumAssoc (Fin r) (Fin j) (Fin 1)).symm

/-- **The abstract block model of the Lagrange Jacobian**: rows and columns indexed by
`(Fin r ⊕ Fin j) ⊕ Fin 1` (the `L`-rows/`yt`-columns, the `h`-rows/`μ`-columns and the
`N`-row/`μ₀`-column). -/
def cM {r j : ℕ} (A : Matrix (Fin r) (Fin r) ℝ) (W : Matrix (Fin r) (Fin j) ℝ) (g : Fin r → ℝ)
    (mu : Fin j → ℝ) (mu0 : ℝ) :
    Matrix ((Fin r ⊕ Fin j) ⊕ Fin 1) ((Fin r ⊕ Fin j) ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks (cM0 A W)
    (Matrix.of fun x (_ : Fin 1) => Sum.elim g (fun _ => 0) x)
    (Matrix.of fun (_ : Fin 1) y => Sum.elim (fun _ => 0) (fun b => 2 * mu b) y)
    (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => 2 * mu0)

@[simp] theorem cM_apply_inl_inl_inl_inl {r j : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (W : Matrix (Fin r) (Fin j) ℝ) (g : Fin r → ℝ) (mu : Fin j → ℝ) (mu0 : ℝ)
    (i k : Fin r) :
    cM A W g mu mu0 (Sum.inl (Sum.inl i)) (Sum.inl (Sum.inl k)) = A i k := by
  simp [cM, cM0]

@[simp] theorem cM_apply_inl_inl_inl_inr {r j : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (W : Matrix (Fin r) (Fin j) ℝ) (g : Fin r → ℝ) (mu : Fin j → ℝ) (mu0 : ℝ)
    (i : Fin r) (b : Fin j) :
    cM A W g mu mu0 (Sum.inl (Sum.inl i)) (Sum.inl (Sum.inr b)) = - W i b := by
  simp [cM, cM0]

@[simp] theorem cM_apply_inl_inl_inr {r j : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (W : Matrix (Fin r) (Fin j) ℝ) (g : Fin r → ℝ) (mu : Fin j → ℝ) (mu0 : ℝ)
    (i : Fin r) (u : Fin 1) :
    cM A W g mu mu0 (Sum.inl (Sum.inl i)) (Sum.inr u) = g i := by
  simp [cM, cM0]

@[simp] theorem cM_apply_inl_inr_inl_inl {r j : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (W : Matrix (Fin r) (Fin j) ℝ) (g : Fin r → ℝ) (mu : Fin j → ℝ) (mu0 : ℝ)
    (a : Fin j) (k : Fin r) :
    cM A W g mu mu0 (Sum.inl (Sum.inr a)) (Sum.inl (Sum.inl k)) = W k a := by
  simp [cM, cM0]

@[simp] theorem cM_apply_inl_inr_inl_inr {r j : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (W : Matrix (Fin r) (Fin j) ℝ) (g : Fin r → ℝ) (mu : Fin j → ℝ) (mu0 : ℝ)
    (a b : Fin j) :
    cM A W g mu mu0 (Sum.inl (Sum.inr a)) (Sum.inl (Sum.inr b)) = 0 := by
  simp [cM, cM0]

@[simp] theorem cM_apply_inl_inr_inr {r j : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (W : Matrix (Fin r) (Fin j) ℝ) (g : Fin r → ℝ) (mu : Fin j → ℝ) (mu0 : ℝ)
    (a : Fin j) (u : Fin 1) :
    cM A W g mu mu0 (Sum.inl (Sum.inr a)) (Sum.inr u) = 0 := by
  simp [cM, cM0]

@[simp] theorem cM_apply_inr_inl_inl {r j : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (W : Matrix (Fin r) (Fin j) ℝ) (g : Fin r → ℝ) (mu : Fin j → ℝ) (mu0 : ℝ)
    (u : Fin 1) (k : Fin r) :
    cM A W g mu mu0 (Sum.inr u) (Sum.inl (Sum.inl k)) = 0 := by
  simp [cM, cM0]

@[simp] theorem cM_apply_inr_inl_inr {r j : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (W : Matrix (Fin r) (Fin j) ℝ) (g : Fin r → ℝ) (mu : Fin j → ℝ) (mu0 : ℝ)
    (u : Fin 1) (b : Fin j) :
    cM A W g mu mu0 (Sum.inr u) (Sum.inl (Sum.inr b)) = 2 * mu b := by
  simp [cM, cM0]

@[simp] theorem cM_apply_inr_inr {r j : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (W : Matrix (Fin r) (Fin j) ℝ) (g : Fin r → ℝ) (mu : Fin j → ℝ) (mu0 : ℝ)
    (u u' : Fin 1) :
    cM A W g mu mu0 (Sum.inr u) (Sum.inr u') = 2 * mu0 := by
  simp [cM, cM0]

/-! ## The data of the two Jacobians -/

/-- The `(L,yt)` block of `lagJac`: entry `(i,k)` is
`μ₀ (∂_k∂_i Φ + (∂_i Φ) c_k) - ∑_a μ_a ∂_k∂_i h_a` at `z`. -/
def lagA1 {n m : ℕ} (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (c : Fin (1 + m) → ℝ) (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ) :
    Matrix (Fin (1 + m)) (Fin (1 + m)) ℝ :=
  Matrix.of fun i k =>
    mu0 * (eaEval S.X.c (eaD S.X.c (Fin.natAdd n k) (eaD S.X.c (Fin.natAdd n i) Phi)) z
        + eaEval S.X.c (eaD S.X.c (Fin.natAdd n i) Phi) z * c k)
      - ∑ a' : Fin S.j, mu a' * eaEval S.X.c
          (eaD S.X.c (Fin.natAdd n k) (eaD S.X.c (Fin.natAdd n i) (S.h a'))) z

/-- The `(L,yt)` block of `lagJacTrue`: entry `(i,k)` is
`μ₀ (∂_k∂_i Φ + (∂_k Φ) c_i) - ∑_a μ_a ∂_k∂_i h_a` at `z`.  It is the transpose of `lagA1`. -/
def lagA2 {n m : ℕ} (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (c : Fin (1 + m) → ℝ) (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ) :
    Matrix (Fin (1 + m)) (Fin (1 + m)) ℝ :=
  Matrix.of fun i k =>
    mu0 * (eaEval S.X.c (eaD S.X.c (Fin.natAdd n k) (eaD S.X.c (Fin.natAdd n i) Phi)) z
        + eaEval S.X.c (eaD S.X.c (Fin.natAdd n k) Phi) z * c i)
      - ∑ a' : Fin S.j, mu a' * eaEval S.X.c
          (eaD S.X.c (Fin.natAdd n k) (eaD S.X.c (Fin.natAdd n i) (S.h a'))) z

/-- The matrix `W` of the paper: `W i b = ∂_i h_b(z)`. -/
def lagW {n m : ℕ} (S : AmbStratum (n + (1 + m))) (z : Fin (n + (1 + m)) → ℝ) :
    Matrix (Fin (1 + m)) (Fin S.j) ℝ :=
  Matrix.of fun i b => eaEval S.X.c (eaD S.X.c (Fin.natAdd n i) (S.h b)) z

/-- The vector `g i = ∂_i Φ(z) + Φ(z) c_i`. -/
def lagG {n m : ℕ} (S : AmbStratum (n + (1 + m))) (Phi : EAPoly (n + (1 + m)) S.X.r)
    (c : Fin (1 + m) → ℝ) (z : Fin (n + (1 + m)) → ℝ) : Fin (1 + m) → ℝ :=
  fun i => eaEval S.X.c (eaD S.X.c (Fin.natAdd n i) Phi) z + eaEval S.X.c Phi z * c i

end Work.WilE9G.Lagrange
