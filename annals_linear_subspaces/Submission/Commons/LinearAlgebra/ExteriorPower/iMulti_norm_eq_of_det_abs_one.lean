import Mathlib.Analysis.InnerProductSpace.ExteriorPower

open scoped BigOperators
open Matrix

namespace Commons.LinearAlgebra.ExteriorPower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Expansion of the inner product of two ℝ-linear combinations in terms of the inner
products of the basis vectors. -/
lemma sum_smul_inner_wedge {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (u : ι → E) :
    inner ℝ (∑ i ∈ s, a i • u i) (∑ j ∈ s, b j • u j) =
      ∑ i ∈ s, ∑ j ∈ s, a i * b j * inner ℝ (u i) (u j) := by
  rw [sum_inner]
  simp_rw [inner_sum, real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The `r c`-entry of the product `Aᵀ * G * A`. -/
lemma mul_mul_apply_gram {ι : Type*} [Fintype ι] (A G : Matrix ι ι ℝ) (r c : ι) :
    (Aᵀ * G * A) r c = ∑ p ∈ (Finset.univ : Finset ι), ∑ q ∈ (Finset.univ : Finset ι),
      A p r * G p q * A q c := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Gram matrix of the transformed family `w j = ∑ i, A i j • u i`. -/
lemma gram_w_eq {k : ℕ} (u : Fin k → E) (A : Matrix (Fin k) (Fin k) ℝ)
    (w : Fin k → E) (hw : ∀ j : Fin k, w j = (Finset.univ : Finset (Fin k)).sum
      (fun i : Fin k => A i j • u i)) :
    Matrix.gram ℝ w = Aᵀ * Matrix.gram ℝ u * A := by
  ext r c
  rw [Matrix.gram_apply, hw r, hw c]
  rw [sum_smul_inner_wedge (Finset.univ : Finset (Fin k)) (fun p : Fin k => A p r)
    (fun q : Fin k => A q c) u]
  rw [mul_mul_apply_gram]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  simp [Matrix.gram_apply]
  ring

theorem iMulti_norm_eq_of_det_abs_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {k : ℕ} (u : Fin k → E) (A : Matrix (Fin k) (Fin k) ℝ)
    (w : Fin k → E) (hw : ∀ j : Fin k,
      w j = (Finset.univ : Finset (Fin k)).sum (fun i : Fin k => A i j • u i))
    (hdet : |A.det| = 1) :
    ‖exteriorPower.ιMulti ℝ k w‖ = ‖exteriorPower.ιMulti ℝ k u‖ := by
  have hsq : ‖exteriorPower.ιMulti ℝ k w‖ ^ 2 = ‖exteriorPower.ιMulti ℝ k u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    rw [exteriorPower.inner_ιMulti_self, exteriorPower.inner_ιMulti_self]
    have hgram : Matrix.gram ℝ w = Aᵀ * Matrix.gram ℝ u * A :=
      gram_w_eq (E := E) (k := k) u A w hw
    rw [hgram]
    calc
      (Aᵀ * Matrix.gram ℝ u * A).det = A.det * (Matrix.gram ℝ u).det * A.det := by
        simp [Matrix.det_mul, Matrix.det_transpose]
      _ = (Matrix.gram ℝ u).det := by
        rcases eq_or_eq_neg_of_abs_eq hdet with hd | hd
        · rw [hd]
          ring
        · rw [hd]
          ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · have ha : 0 ≤ ‖exteriorPower.ιMulti ℝ k w‖ := norm_nonneg _
    have hb : 0 ≤ ‖exteriorPower.ιMulti ℝ k u‖ := norm_nonneg _
    have haw : ‖exteriorPower.ιMulti ℝ k w‖ = 0 := by nlinarith
    have hbu : ‖exteriorPower.ιMulti ℝ k u‖ = 0 := by nlinarith
    rw [haw, hbu]

end Commons.LinearAlgebra.ExteriorPower