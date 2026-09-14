import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.det_mono_posSemidef_sub

open Matrix
open scoped BigOperators

set_option autoImplicit false

namespace Commons.LinearAlgebra.Matrix

/-- For an injective `e : α ↪ β` and a nonnegative function `g`, the sum of `g` over the image
of `e` (equivalently the sum `∑ a, g (e a)`) is at most the full sum `∑ b, g b`. -/
private lemma sum_le_sum_comp {α β : Type*} [Fintype α] [Fintype β] (e : α ↪ β)
    (g : β → ℝ) (hg : ∀ b, 0 ≤ g b) :
    (∑ a : α, g (e a)) ≤ ∑ b : β, g b := by
  classical
  let s : Finset β := Finset.map e (Finset.univ : Finset α)
  calc
    (∑ a : α, g (e a)) = ∑ b ∈ s, g b := by
        rw [Finset.sum_map]
    _ ≤ ∑ b : β, g b := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (s := s) (t := Finset.univ)
          (by intro b hb; simp [s] at hb ⊢) (by intro b hb hb2; exact hg b)

/-- Adjoint identity for the real dot product: `x ⬝ Mᵀ y = (M x) ⬝ y`. -/
private lemma dot_x_transpose_mulVec {n r : ℕ} (M : Matrix (Fin n) (Fin r) ℝ)
    (x : Fin r → ℝ) (y : Fin n → ℝ) :
    x ⬝ᵥ (M.transpose *ᵥ y) = (M *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.dotProduct_transpose_mulVec]
  rw [dotProduct_comm]

/-- Keeping only the rows indexed by the image of `e` can only decrease the Gram matrix
`Mᵀ * M` in the Loewner (positive semidefinite) order. -/
private lemma psd_self_mul_sub_submatrix {n r : ℕ} (M : Matrix (Fin n) (Fin r) ℝ)
    (e : Fin r ↪ Fin n) :
    ((M.transpose * M) - ((M.submatrix (fun i : Fin r => e i) (fun j : Fin r => j)).transpose *
        (M.submatrix (fun i : Fin r => e i) (fun j : Fin r => j)))).PosSemidef := by
  classical
  let B : Matrix (Fin r) (Fin r) ℝ := M.submatrix (fun i : Fin r => e i) (fun j : Fin r => j)
  have h1 : (M.transpose * M).IsHermitian := by
    rw [Matrix.IsHermitian]
    simp [Matrix.conjTranspose_eq_transpose_of_trivial]
  have h2 : (B.transpose * B).IsHermitian := by
    rw [Matrix.IsHermitian]
    simp [Matrix.conjTranspose_eq_transpose_of_trivial]
  have hherm : ((M.transpose * M) - (B.transpose * B)).IsHermitian := h1.sub h2
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm ?quad
  · intro x
    have hstar : star x = x := by
      funext i
      simp
    rw [hstar]
    let f : Fin n → ℝ := M *ᵥ x
    have hfB : B *ᵥ x = fun l => f (e l) := by
      funext l
      simp [f, B, Matrix.mulVec]
    have hsplit : x ⬝ᵥ (((M.transpose * M) - (B.transpose * B)) *ᵥ x)
        = x ⬝ᵥ ((M.transpose * M) *ᵥ x) - x ⬝ᵥ ((B.transpose * B) *ᵥ x) := by
      rw [Matrix.sub_mulVec]
      rw [dotProduct_sub]
    rw [hsplit]
    have hMself : x ⬝ᵥ ((M.transpose * M) *ᵥ x) = f ⬝ᵥ f := by
      rw [← Matrix.mulVec_mulVec]
      rw [dot_x_transpose_mulVec]
    have hBself : x ⬝ᵥ ((B.transpose * B) *ᵥ x) = (B *ᵥ x) ⬝ᵥ (B *ᵥ x) := by
      rw [← Matrix.mulVec_mulVec]
      rw [dot_x_transpose_mulVec]
    rw [hMself, hBself, hfB]
    have hnonneg : (∑ l : Fin r, f (e l) * f (e l)) ≤ (∑ i : Fin n, f i * f i) :=
      sum_le_sum_comp e (fun b => f b * f b) (fun b => mul_self_nonneg (f b))
    rw [dotProduct]
    rw [dotProduct]
    exact sub_nonneg.mpr hnonneg

/-- The determinant of the Gram matrix `Mᵀ * M` of an `n × r` real matrix `M` is at least the
square of the determinant of the `r × r` submatrix obtained by keeping the rows indexed by `e`. -/
private theorem det_self_mul_ge_submatrix_det_sq {n r : ℕ} (M : Matrix (Fin n) (Fin r) ℝ)
    (e : Fin r ↪ Fin n) :
    ((M.submatrix (fun i : Fin r => e i) (fun j : Fin r => j)).det) ^ 2 ≤
      (M.transpose * M).det := by
  classical
  let B : Matrix (Fin r) (Fin r) ℝ := M.submatrix (fun i : Fin r => e i) (fun j : Fin r => j)
  have hAB : (B.transpose * B).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_conjTranspose_mul_self (R := ℝ) (A := B))
  have hdiff : ((M.transpose * M) - (B.transpose * B)).PosSemidef := psd_self_mul_sub_submatrix M e
  have hdetle : (B.transpose * B).det ≤ (M.transpose * M).det := by
    exact Commons.LinearAlgebra.Matrix.det_mono_posSemidef_sub
      (A := B.transpose * B) (B := M.transpose * M) hAB hdiff
  have hBB : (B.transpose * B).det = (B.det) ^ 2 := by
    rw [Matrix.det_mul, Matrix.det_transpose]
    ring
  rw [← hBB]
  exact hdetle

theorem gram_det_ge_submatrix_det_sq {n r : ℕ} (A : Matrix (Fin n) (Fin r) ℤ)
    (e : Fin r ↪ Fin n) :
    (((A.map (fun z : ℤ => (z : ℝ))).transpose *
        (A.map (fun z : ℤ => (z : ℝ)))).det) ≥
      (((A.submatrix (fun i : Fin r => e i) (fun j : Fin r => j)).map
        (fun z : ℤ => (z : ℝ))).det) ^ 2 := by
  classical
  let M : Matrix (Fin n) (Fin r) ℝ := A.map (fun z : ℤ => (z : ℝ))
  let B : Matrix (Fin r) (Fin r) ℝ := M.submatrix (fun i : Fin r => e i) (fun j : Fin r => j)
  have hB : B = (A.submatrix (fun i : Fin r => e i) (fun j : Fin r => j)).map
      (fun z : ℤ => (z : ℝ)) := by
    dsimp [B, M]
    rw [Matrix.submatrix_map]
  change (M.transpose * M).det ≥
      ((A.submatrix (fun i : Fin r => e i) (fun j : Fin r => j)).map
        (fun z : ℤ => (z : ℝ))).det ^ 2
  rw [← hB]
  exact det_self_mul_ge_submatrix_det_sq M e

end Commons.LinearAlgebra.Matrix
