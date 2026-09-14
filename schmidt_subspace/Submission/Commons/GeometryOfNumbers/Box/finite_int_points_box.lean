import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Matrix.Adjugate

namespace Commons.GeometryOfNumbers.Box

open scoped BigOperators
open Matrix

theorem finite_int_points_box {N : ℕ} (L : Fin N → Fin N → ℂ) (hdet : (Matrix.of L).det ≠ 0)
    (M : Fin N → ℝ) :
    {y : Fin N → ℤ | ∀ i, ‖∑ k, L i k * (y k : ℂ)‖ ≤ M i}.Finite := by
  let A : Matrix (Fin N) (Fin N) ℂ := Matrix.of L
  have hAdet : A.det ≠ 0 := by simpa [A] using hdet
  have hdpos : 0 < ‖A.det‖ := norm_pos_iff.mpr hAdet
  set B : Fin N → ℝ := fun k => (∑ i, ‖A.adjugate k i‖ * max (M i) 0) / ‖A.det‖ with hBdef
  have key : ∀ (y : Fin N → ℤ), (∀ i, ‖∑ k, L i k * (y k : ℂ)‖ ≤ M i) →
      ∀ k, ‖((y k : ℤ) : ℂ)‖ ≤ B k := by
    intro y hy k
    set v : Fin N → ℂ := fun k => (y k : ℂ) with hvdef
    have hvi : ∀ i, (A *ᵥ v) i = ∑ k, L i k * (y k : ℂ) := by
      intro i
      rw [hvdef]
      rfl
    have hz : ∀ i, ‖(A *ᵥ v) i‖ ≤ max (M i) 0 := fun i =>
      le_trans (by rw [hvi i]; exact hy i) (le_max_left _ _)
    have hmul : A.det * v k = ∑ i, A.adjugate k i * (A *ᵥ v) i := by
      have h1 : A.adjugate *ᵥ (A *ᵥ v) = A.det • v := by
        rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
      have h := congr_fun h1 k
      rw [show (A.adjugate *ᵥ (A *ᵥ v)) k = ∑ i, A.adjugate k i * (A *ᵥ v) i from rfl] at h
      rw [show (A.det • v) k = A.det * v k from rfl] at h
      exact h.symm
    have hbound : ‖A.det‖ * ‖v k‖ ≤ ∑ i, ‖A.adjugate k i‖ * max (M i) 0 := by
      calc ‖A.det‖ * ‖v k‖ = ‖A.det * v k‖ := (norm_mul _ _).symm
        _ = ‖∑ i, A.adjugate k i * (A *ᵥ v) i‖ := by rw [hmul]
        _ ≤ ∑ i, ‖A.adjugate k i * (A *ᵥ v) i‖ := norm_sum_le _ _
        _ = ∑ i, ‖A.adjugate k i‖ * ‖(A *ᵥ v) i‖ := by
              apply Finset.sum_congr rfl; intro i _; rw [norm_mul]
        _ ≤ ∑ i, ‖A.adjugate k i‖ * max (M i) 0 := by
              apply Finset.sum_le_sum; intro i _
              exact mul_le_mul_of_nonneg_left (hz i) (norm_nonneg _)
    have hsum : ∑ i, ‖A.adjugate k i‖ * max (M i) 0 = B k * ‖A.det‖ := by
      rw [hBdef]
      exact (div_mul_cancel₀ _ hdpos.ne').symm
    rw [hvdef] at hbound
    have h2 : ‖((y k : ℤ) : ℂ)‖ * ‖A.det‖ ≤ B k * ‖A.det‖ := by
      rw [hsum] at hbound
      simpa [mul_comm] using hbound
    exact le_of_mul_le_mul_right h2 hdpos
  refine (Set.Finite.pi (fun k => Set.finite_Icc (-(⌈B k⌉) : ℤ) (⌈B k⌉))).subset ?_
  intro y hy
  rw [Set.mem_univ_pi]
  intro k
  rw [Set.mem_Icc]
  have hk : ‖((y k : ℤ) : ℂ)‖ ≤ B k := key y hy k
  have hnorm : ‖((y k : ℤ) : ℂ)‖ = |((y k : ℤ) : ℝ)| := by
    rw [← Complex.ofReal_intCast]
    exact RCLike.norm_ofReal _
  have habs : |((y k : ℤ) : ℝ)| ≤ B k := by rw [← hnorm]; exact hk
  have h1 : ((y k : ℤ) : ℝ) ≤ ((⌈B k⌉ : ℤ) : ℝ) :=
    le_trans (le_abs_self _) (le_trans habs (Int.le_ceil _))
  have h3 : -(((y k : ℤ)) : ℝ) ≤ ((⌈B k⌉ : ℤ) : ℝ) :=
    le_trans (neg_le_abs _) (le_trans habs (Int.le_ceil _))
  have h2 : (((-(⌈B k⌉) : ℤ)) : ℝ) ≤ ((y k : ℤ) : ℝ) := by
    push_cast
    linarith
  exact ⟨Int.cast_le.mp h2, Int.cast_le.mp h1⟩

end Commons.GeometryOfNumbers.Box