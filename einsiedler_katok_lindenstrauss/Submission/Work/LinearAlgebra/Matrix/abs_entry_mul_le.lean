import Mathlib

namespace Work.LinearAlgebra.Matrix

theorem abs_entry_mul_le {A B M : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ∀ i j, |A i j| ≤ 2) (hB : ∀ i j, |B i j| ≤ 11) (i j : Fin 3) :
    |(A * M * B) i j| ≤ 22 * ∑ a : Fin 3, ∑ b : Fin 3, |M a b| := by
  have hAM : ∀ l : Fin 3, |(A * M) i l| ≤ 2 * ∑ k : Fin 3, |M k l| := by
    intro l
    rw [Matrix.mul_apply]
    calc |∑ k : Fin 3, A i k * M k l|
        ≤ ∑ k : Fin 3, |A i k * M k l| :=
            Finset.abs_sum_le_sum_abs (fun k : Fin 3 => A i k * M k l) Finset.univ
      _ = ∑ k : Fin 3, |A i k| * |M k l| := by simp only [abs_mul]
      _ ≤ ∑ k : Fin 3, 2 * |M k l| :=
            Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (hA i k) (abs_nonneg _))
      _ = 2 * ∑ k : Fin 3, |M k l| := by rw [Finset.mul_sum]
  have hmul : (A * M * B) i j = ∑ l : Fin 3, (A * M) i l * B l j := Matrix.mul_apply
  rw [hmul]
  have hsum : (∑ l : Fin 3, ∑ k : Fin 3, |M k l|) = ∑ a : Fin 3, ∑ b : Fin 3, |M a b| := by
    rw [show (∑ l : Fin 3, ∑ k : Fin 3, |M k l|) = ∑ k : Fin 3, ∑ l : Fin 3, |M k l|
          from Finset.sum_comm]
  calc |∑ l : Fin 3, (A * M) i l * B l j|
      ≤ ∑ l : Fin 3, |(A * M) i l * B l j| :=
          Finset.abs_sum_le_sum_abs (fun l : Fin 3 => (A * M) i l * B l j) Finset.univ
    _ = ∑ l : Fin 3, |(A * M) i l| * |B l j| := by simp only [abs_mul]
    _ ≤ ∑ l : Fin 3, (2 * ∑ k : Fin 3, |M k l|) * 11 :=
          Finset.sum_le_sum (fun l _ =>
            mul_le_mul (hAM l) (hB l j) (abs_nonneg _)
              (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun k _ => abs_nonneg _))))
    _ = ∑ l : Fin 3, 22 * ∑ k : Fin 3, |M k l| := by
          apply Finset.sum_congr rfl
          intro l _
          ring
    _ = 22 * ∑ l : Fin 3, ∑ k : Fin 3, |M k l| := by rw [Finset.mul_sum]
    _ = 22 * ∑ a : Fin 3, ∑ b : Fin 3, |M a b| := by rw [hsum]

end Work.LinearAlgebra.Matrix
