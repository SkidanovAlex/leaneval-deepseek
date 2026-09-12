import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef

open Matrix
open scoped BigOperators

namespace Commons.LinearAlgebra.Matrix

lemma det_one_add_eq_sum_principal {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) :
    (1 + M).det = ∑ s : Finset n, (M.submatrix (Subtype.val : s → n) Subtype.val).det := by
  classical
  calc
    (1 + M).det = detRowAlternating ((fun i => M i) + (fun i => (1 : Matrix n n R) i)) := by
      congr 1
      ext i j
      simp [add_comm]
    _ = ∑ s : Finset n, detRowAlternating (s.piecewise (fun i => M i) (fun i => (1 : Matrix n n R) i)) := by
      rw [detRowAlternating.map_add_univ]
    _ = ∑ s : Finset n, (M.submatrix (Subtype.val : s → n) Subtype.val).det := by
      apply Finset.sum_congr rfl
      intro s hs
      have h1 : s.piecewise (fun i => M i) (fun i => (1 : Matrix n n R) i) =
          s.piecewise M.row (row (1 : Matrix n n R)) := by
        funext i j
        unfold Finset.piecewise
        by_cases hi : i ∈ s <;> simp [hi, Matrix.row]
      calc
        detRowAlternating (s.piecewise (fun i => M i) (fun i => (1 : Matrix n n R) i))
            = detRowAlternating (s.piecewise M.row (row (1 : Matrix n n R))) := by rw [h1]
        _ = (M.submatrix (Subtype.val : s → n) Subtype.val).det := by
              rw [← Matrix.det_piecewise_one_eq_submatrix_det M s]
              rfl

lemma det_principal_submatrix_posSemidef_nonneg {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosSemidef) (s : Finset (Fin n)) :
    0 ≤ (X.submatrix (Subtype.val : s → Fin n) Subtype.val).det := by
  classical
  exact (hX.submatrix (Subtype.val : s → Fin n)).det_nonneg

lemma det_diagonal_add_posSemidef {n : ℕ} {α : Fin n → ℝ} {X : Matrix (Fin n) (Fin n) ℝ}
    (hα : ∀ i, 0 ≤ α i) (hX : X.PosSemidef) :
    (Matrix.diagonal α).det ≤ (Matrix.diagonal α + X).det := by
  classical
  by_cases hdet : (Matrix.diagonal α).det ≠ 0
  · have hprodne : (∏ i : Fin n, α i) ≠ 0 := by simpa [Matrix.det_diagonal] using hdet
    have hαne : ∀ i, α i ≠ 0 := by
      intro i hi
      exact hprodne (Finset.prod_eq_zero (Finset.mem_univ i) hi)
    have hpos : ∀ i, 0 < α i := by
      intro i
      exact lt_of_le_of_ne (hα i) (Ne.symm (hαne i))
    let d : Fin n → ℝ := fun i => (α i)⁻¹
    let M : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal d * X
    have hD : Matrix.diagonal α * Matrix.diagonal d = 1 := by
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases h : i = j
      · subst h
        simp [d, hαne i]
      · simp [h, d]
    have hDM : Matrix.diagonal α * M = X := by
      dsimp [M]
      rw [← Matrix.mul_assoc, hD, Matrix.one_mul]
    have hfactor : Matrix.diagonal α * (1 + M) = Matrix.diagonal α + X := by
      rw [Matrix.mul_add, Matrix.mul_one, hDM]
    have hdetfactor : (Matrix.diagonal α + X).det = (Matrix.diagonal α).det * (1 + M).det := by
      rw [← hfactor]
      rw [Matrix.det_mul]
    have hM_s_nonneg : ∀ s : Finset (Fin n),
        0 ≤ (M.submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n)).det := by
      intro s
      have hMsub : M.submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n) =
          Matrix.diagonal (fun i : {x : Fin n // x ∈ s} => d (i : Fin n)) *
            (X.submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n)) := by
        ext i j
        simp [M, d, Matrix.diagonal_mul]
      rw [hMsub, Matrix.det_mul, Matrix.det_diagonal]
      refine mul_nonneg (Finset.prod_nonneg (fun i _ => ?_))
        (det_principal_submatrix_posSemidef_nonneg hX s)
      exact inv_nonneg.mpr (le_of_lt (hpos (i : Fin n)))
    have hge1 : 1 ≤ (1 + M).det := by
      rw [det_one_add_eq_sum_principal M]
      have hEmpty : ((M.submatrix (Subtype.val : (∅ : Finset (Fin n)) → Fin n)
          (Subtype.val : (∅ : Finset (Fin n)) → Fin n))).det = 1 := by
        simp
      calc
        1 = (M.submatrix (Subtype.val : (∅ : Finset (Fin n)) → Fin n)
            (Subtype.val : (∅ : Finset (Fin n)) → Fin n)).det := hEmpty.symm
        _ ≤ ∑ s : Finset (Fin n), (M.submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n)).det := by
              exact Finset.single_le_sum (s := Finset.univ)
                (f := fun s : Finset (Fin n) => (M.submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n)).det)
                (by intro s _; exact hM_s_nonneg s)
                (Finset.mem_univ (∅ : Finset (Fin n)))
    have hdetA_nonneg : 0 ≤ (Matrix.diagonal α).det := by
      rw [Matrix.det_diagonal]
      exact Finset.prod_nonneg (fun i _ => hα i)
    rw [hdetfactor]
    simpa using mul_le_mul_of_nonneg_left hge1 hdetA_nonneg
  · have hz : (Matrix.diagonal α).det = 0 := not_not.mp hdet
    have hD : (Matrix.diagonal α).PosSemidef := Matrix.PosSemidef.diagonal hα
    have hsum : (Matrix.diagonal α + X).PosSemidef := hD.add hX
    have hnn : 0 ≤ (Matrix.diagonal α + X).det := hsum.det_nonneg
    rw [hz]
    exact hnn

lemma det_conj_unitary_real {n : ℕ} {V X : Matrix (Fin n) (Fin n) ℝ} (hV : V * star V = 1) :
    (V * X * star V).det = X.det := by
  classical
  have hdetV : V.det * (star V).det = 1 := by
    rw [← Matrix.det_mul, hV, Matrix.det_one]
  calc
    (V * X * star V).det = V.det * (X.det * (star V).det) := by
      rw [Matrix.det_mul, Matrix.det_mul]
      ac_rfl
    _ = X.det := by
      have h : V.det * (X.det * (star V).det) = X.det * (V.det * (star V).det) := by ring
      rw [h, hdetV, mul_one]

lemma spectral_decomp {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
        Matrix.diagonal (fun i => hA.eigenvalues i) *
        star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) := by
  classical
  simpa using hA.spectral_theorem

theorem det_mono_posSemidef_sub {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (hsub : (B - A).PosSemidef) : A.det ≤ B.det := by
  classical
  let C : Matrix (Fin n) (Fin n) ℝ := B - A
  let V : Matrix (Fin n) (Fin n) ℝ := (hA.isHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  let α : Fin n → ℝ := hA.isHermitian.eigenvalues
  have hB : B = A + C := by
    dsimp [C]
    abel
  have hVstarV : V * star V = 1 := by
    dsimp [V]
    exact Matrix.mem_unitaryGroup_iff.mp hA.isHermitian.eigenvectorUnitary.property
  have hspec : A = V * Matrix.diagonal α * star V := by
    dsimp [V, α]
    exact spectral_decomp hA.isHermitian
  let X : Matrix (Fin n) (Fin n) ℝ := star V * C * V
  have hCid : C = V * X * star V := by
    dsimp [X]
    simp [Matrix.mul_assoc, hVstarV]
    rw [← Matrix.mul_assoc, hVstarV, one_mul]
  have hAC : A + C = V * (Matrix.diagonal α + X) * star V := by
    calc
      A + C = V * Matrix.diagonal α * star V + C := by rw [hspec]
      _ = V * Matrix.diagonal α * star V + V * X * star V := by rw [hCid]
      _ = V * (Matrix.diagonal α + X) * star V := by
            calc
              V * Matrix.diagonal α * star V + V * X * star V
                  = (V * Matrix.diagonal α + V * X) * star V := by rw [Matrix.add_mul]
              _ = V * (Matrix.diagonal α + X) * star V := by rw [Matrix.mul_add]
  have hAdet : A.det = (Matrix.diagonal α).det := by
    rw [hspec]
    exact det_conj_unitary_real hVstarV
  have hACdet : (A + C).det = (Matrix.diagonal α + X).det := by
    rw [hAC]
    exact det_conj_unitary_real hVstarV
  have hXpsd : X.PosSemidef := by
    dsimp [X]
    simpa [Matrix.star_eq_conjTranspose] using
      (hsub.conjTranspose_mul_mul_same (B := (V : Matrix (Fin n) (Fin n) ℝ)))
  have hα0 : ∀ i, 0 ≤ α i := by
    intro i
    exact hA.eigenvalues_nonneg i
  have hdiag : (Matrix.diagonal α).det ≤ (Matrix.diagonal α + X).det :=
    det_diagonal_add_posSemidef hα0 hXpsd
  rw [hB, hAdet, hACdet]
  exact hdiag

end Commons.LinearAlgebra.Matrix