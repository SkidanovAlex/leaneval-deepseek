import Mathlib

namespace Work.EKLC6Core

/-- Product bound: if `|a| ≤ M` and `|b| ≤ M` with `0 ≤ M`, then `|a * b| ≤ M * M`. -/
lemma abs_mul_le_of_abs_le (a b M : ℝ) (hM : 0 ≤ M) (ha : |a| ≤ M) (hb : |b| ≤ M) :
    |a * b| ≤ M * M := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg b) hM

/-- Bound on a difference of two products of entries each bounded by `M`. -/
lemma abs_two_prod_sub_le_of_abs_le {a b c d M : ℝ} (hM : 0 ≤ M) (ha : |a| ≤ M)
    (hb : |b| ≤ M) (hc : |c| ≤ M) (hd : |d| ≤ M) : |a * b - c * d| ≤ 2 * M ^ 2 := by
  have h1 : |a * b| ≤ M * M := abs_mul_le_of_abs_le a b M hM ha hb
  have h2 : |c * d| ≤ M * M := abs_mul_le_of_abs_le c d M hM hc hd
  calc |a * b - c * d| = |a * b + -(c * d)| := by rw [sub_eq_add_neg]
    _ ≤ |a * b| + |-(c * d)| := abs_add_le _ _
    _ = |a * b| + |c * d| := by rw [abs_neg]
    _ ≤ M * M + M * M := add_le_add h1 h2
    _ = 2 * M ^ 2 := by ring

/-- Signed variant: bound on `|-(a * b) + c * d|`. -/
lemma abs_neg_prod_add_le_of_abs_le {a b c d M : ℝ} (hM : 0 ≤ M) (ha : |a| ≤ M)
    (hb : |b| ≤ M) (hc : |c| ≤ M) (hd : |d| ≤ M) : |-(a * b) + c * d| ≤ 2 * M ^ 2 := by
  have h : -(a * b) + c * d = c * d - a * b := by ring
  rw [h, abs_sub_comm]
  exact abs_two_prod_sub_le_of_abs_le hM ha hb hc hd

theorem adjugate_entry_bound_abs (A : Matrix (Fin 3) (Fin 3) ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hA : ∀ i j, |A i j| ≤ M) : ∀ i j, |A.adjugate i j| ≤ 2 * M ^ 2 := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    (simp only [Matrix.adjugate_apply, Matrix.det_fin_three]
     simp only [Matrix.updateRow_apply, Fin.isValue]
     simp
     first
      | exact abs_two_prod_sub_le_of_abs_le hM (hA _ _) (hA _ _) (hA _ _) (hA _ _)
      | exact abs_neg_prod_add_le_of_abs_le hM (hA _ _) (hA _ _) (hA _ _) (hA _ _))

end Work.EKLC6Core
