import Mathlib
import Submission.Work.KT.EG.kappa_linearise_defs
import Submission.Work.KT.EG.kappa_linearise_b
import Submission.Work.KT.EG.kappa_linearise_c
import Submission.Work.KT.Fund.kappa_homotopic

/-!
# `Work.KT.EG.kappa_linearise_d` — the units and the homotopy of the linearisation

The companion matrix `A`, the column-operation matrix `R` and the row-elimination matrix `L` are
assembled into units; `L · A · R = B` then produces the homotopy from `A` to `B` through units,
which is the input of `Work.KT.Fund.kappa_homotopic`.
-/

namespace Work.KT.EG

open Matrix

noncomputable section

variable (X : Type) [TopologicalSpace X]

/-! ## 1. The units at the circle level -/

/-- The column-operation unit: `Rmat` with inverse `1 - z • shMat`. -/
def uRmat (X : Type) [TopologicalSpace X] (N m : ℕ) :
    (Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ))ˣ :=
  Units.mk (Rmat X N) (1 - zc X • shC X N m)
    (Rmat_mul_one_sub_zc_shC X N m) (one_sub_zc_shC_mul_Rmat X N m)

@[simp] lemma uRmat_val (X : Type) [TopologicalSpace X] (N m : ℕ) :
    ((uRmat X N m : (Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ))ˣ) :
      Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ)) = Rmat X N := rfl

@[simp] lemma uRmat_inv_val (X : Type) [TopologicalSpace X] (N m : ℕ) :
    (((uRmat X N m)⁻¹ : (Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ))ˣ) :
      Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ)) = 1 - zc X • shC X N m := rfl

/-- The inverse of `Lmat`. -/
def uRowInv {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) :
    Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ) :=
  (Matrix.fromBlocks (1 : Matrix (Fin N × Fin m) (Fin N × Fin m) C(X × Sph ℂ, ℂ)) 0
    (RowM X N q) (1 : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ)) :
      Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ))

lemma Lmat_mul_uRowInv {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) :
    Lmat X N q * uRowInv X N q = 1 := by
  have hL : Lmat X N q
      = (Matrix.fromBlocks (1 : Matrix (Fin N × Fin m) (Fin N × Fin m) C(X × Sph ℂ, ℂ)) 0
          (-(RowM X N q)) (1 : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ)) :
          Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ)) := rfl
  have hR : uRowInv X N q
      = (Matrix.fromBlocks (1 : Matrix (Fin N × Fin m) (Fin N × Fin m) C(X × Sph ℂ, ℂ)) 0
          (RowM X N q) (1 : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ)) :
          Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ)) := rfl
  rw [hL, hR, Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
    Matrix.neg_mul, neg_add_cancel, neg_zero, Matrix.fromBlocks_one]

lemma uRowInv_mul_Lmat {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) :
    uRowInv X N q * Lmat X N q = 1 := by
  have hL : Lmat X N q
      = (Matrix.fromBlocks (1 : Matrix (Fin N × Fin m) (Fin N × Fin m) C(X × Sph ℂ, ℂ)) 0
          (-(RowM X N q)) (1 : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ)) :
          Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ)) := rfl
  have hR : uRowInv X N q
      = (Matrix.fromBlocks (1 : Matrix (Fin N × Fin m) (Fin N × Fin m) C(X × Sph ℂ, ℂ)) 0
          (RowM X N q) (1 : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ)) :
          Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ)) := rfl
  rw [hL, hR, Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
    Matrix.mul_neg, add_neg_cancel, neg_zero, Matrix.fromBlocks_one]

/-- The row-elimination unit: `Lmat` with inverse `fromBlocks 1 0 RowM 1`. -/
def uLmat {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) :
    (Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ))ˣ :=
  Units.mk (Lmat X N q) (uRowInv X N q) (Lmat_mul_uRowInv X N q) (uRowInv_mul_Lmat X N q)

@[simp] lemma uLmat_val {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ))) :
    ((uLmat X N q : (Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ))ˣ) :
      Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ)) = Lmat X N q := rfl

/-- The target unit: `Bmat = fromBlocks 1 0 0 q(z)`. -/
def uBmat {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ)))
    (u : (Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))ˣ)
    (hu : (u : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ)) = q.map (polyMapA X)) :
    (Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ))ˣ :=
  Units.mk (Bmat X N q) (Matrix.fromBlocks (1 : Matrix (Fin N × Fin m) (Fin N × Fin m)
      C(X × Sph ℂ, ℂ)) 0 0 ((u⁻¹ : (Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))ˣ) :
        Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ)))
    (by
      have hB : Bmat X N q
          = (Matrix.fromBlocks (1 : Matrix (Fin N × Fin m) (Fin N × Fin m) C(X × Sph ℂ, ℂ))
              0 0 (q.map (polyMapA X)) : Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ)) := rfl
      rw [hB, Matrix.fromBlocks_multiply]
      simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, zero_add,
        add_zero]
      rw [← hu, Units.mul_inv, Matrix.fromBlocks_one])
    (by
      have hB : Bmat X N q
          = (Matrix.fromBlocks (1 : Matrix (Fin N × Fin m) (Fin N × Fin m) C(X × Sph ℂ, ℂ))
              0 0 (q.map (polyMapA X)) : Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ)) := rfl
      rw [hB, Matrix.fromBlocks_multiply]
      simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, zero_add,
        add_zero]
      rw [← hu, Units.inv_mul, Matrix.fromBlocks_one])

@[simp] lemma uBmat_val {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ)))
    (u : (Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))ˣ)
    (hu : (u : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ)) = q.map (polyMapA X)) :
    ((uBmat X N q u hu : (Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ))ˣ) :
      Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ)) = Bmat X N q := rfl

/-- The companion-matrix unit, obtained from `L · A · R = B`. -/
def uAmat {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ)))
    (u : (Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))ˣ)
    (hu : (u : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ)) = q.map (polyMapA X)) :
    (Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ))ˣ :=
  (uLmat X N q)⁻¹ * uBmat X N q u hu * (uRmat X N m)⁻¹

/-- The matrix identity `A = L⁻¹ · B · R⁻¹` behind `uAmat`. -/
theorem Amat_eq {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ)))
    (u : (Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))ˣ)
    (hu : (u : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ)) = q.map (polyMapA X))
    (hN : ∀ i j, (q i j).natDegree ≤ N) :
    Amat X N q = uRowInv X N q * Bmat X N q * (1 - zc X • shC X N m) := by
  have h := Lmat_mul_Amat_Rmat X m N q hN
  calc Amat X N q
      = (uRowInv X N q * Lmat X N q) * Amat X N q
          * (Rmat X N * (1 - zc X • shC X N m)) := by
        rw [uRowInv_mul_Lmat X N q, Rmat_mul_one_sub_zc_shC X N m, one_mul, mul_one]
    _ = uRowInv X N q * (Lmat X N q * (Amat X N q * Rmat X N))
          * (1 - zc X • shC X N m) := by
        noncomm_ring
    _ = uRowInv X N q * Bmat X N q * (1 - zc X • shC X N m) := by
        rw [h]

theorem uAmat_val {m : ℕ} (N : ℕ) (q : Matrix (Fin m) (Fin m) (Polynomial C(X, ℂ)))
    (u : (Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ))ˣ)
    (hu : (u : Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ)) = q.map (polyMapA X))
    (hN : ∀ i j, (q i j).natDegree ≤ N) :
    ((uAmat X N q u hu : (Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ))ˣ) :
      Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ)) = Amat X N q := by
  have hA := Amat_eq X N q u hu hN
  rw [uAmat, Units.val_mul, Units.val_mul]
  have hLm : (((uLmat X N q)⁻¹ : (Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ))ˣ) :
      Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ)) = uRowInv X N q := rfl
  have hRm : (((uRmat X N m)⁻¹ : (Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ))ˣ) :
      Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ)) = 1 - zc X • shC X N m := rfl
  have hBm : ((uBmat X N q u hu : (Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ))ˣ) :
      Matrix (BIdx N m) (BIdx N m) C(X × Sph ℂ, ℂ)) = Bmat X N q := rfl
  rw [hLm, hBm, hRm]
  exact hA.symm

end

end Work.KT.EG
