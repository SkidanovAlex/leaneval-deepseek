import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

open Matrix

namespace Commons.LinearAlgebra.Matrix

theorem starVec_dotProduct_eq_zero {K : Type*} [Field K] {N : ℕ} (G : Matrix (Fin (N+1)) (Fin N) K)
    (j : Fin N) :
    ∑ i : Fin (N+1), ((-1 : K) ^ (i : ℕ) * (G.submatrix (Fin.succAbove i) id).det) * G i j = 0 := by
  set B : Matrix (Fin (N+1)) (Fin (N+1)) K :=
    fun i k => G i (if h : (k : ℕ) < N then ⟨k, h⟩ else j) with hB
  have hsub : ∀ i, B.submatrix (Fin.succAbove i) Fin.castSucc = G.submatrix (Fin.succAbove i) id := by
    intro i; ext a b
    change G (i.succAbove a)
        (if h : ((Fin.castSucc b : Fin (N+1)) : ℕ) < N then ⟨(Fin.castSucc b : ℕ), h⟩ else j)
      = G (i.succAbove a) b
    rw [show (Fin.castSucc b : ℕ) = (b : ℕ) from rfl, dif_pos b.isLt]
  have hlast : ∀ i, B i (Fin.last N) = G i j := by
    intro i; simp [hB]
  have hdet : B.det = 0 := by
    apply Matrix.det_zero_of_column_eq (i := Fin.castSucc j) (j := Fin.last N)
    · intro h
      have h2 := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_last] at h2
      omega
    · intro k; simp [hB]
  rw [Matrix.det_succ_column B (Fin.last N), Fin.succAbove_last] at hdet
  simp only [hlast, hsub] at hdet
  have key : (-1 : K)^N *
        (∑ i : Fin (N+1), (-1 : K)^(i:ℕ) * (G.submatrix (Fin.succAbove i) id).det * G i j)
      = ∑ i : Fin (N+1), (-1 : K)^((i:ℕ) + N) * G i j * (G.submatrix (Fin.succAbove i) id).det := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_add]
    ring
  have hS : (-1 : K)^N *
        (∑ i : Fin (N+1), (-1 : K)^(i:ℕ) * (G.submatrix (Fin.succAbove i) id).det * G i j) = 0 := by
    rw [key]; exact hdet
  have hne : (-1 : K)^N ≠ 0 := pow_ne_zero _ (by norm_num)
  exact (mul_eq_zero.mp hS).resolve_left hne

end Commons.LinearAlgebra.Matrix