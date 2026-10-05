import Mathlib

namespace Work.RPB.B1a

theorem abs_mul_sub_le_of {σ M x q q' : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h1 : |q - σ * x| ≤ M * x ^ 2) (h2 : |q' - σ| ≤ M * |x|) :
    |q * q' - x| ≤ 2 * M * x ^ 2 + M ^ 2 * |x| ^ 3 := by
  have hσ2 : σ * σ = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hσabs : |σ| = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  set a := q - σ * x with ha
  set b := q' - σ with hb
  have hq : q = σ * x + a := by rw [ha]; ring
  have hq' : q' = σ + b := by rw [hb]; ring
  have key : q * q' - x = σ * (x * b) + σ * a + a * b := by
    rw [hq, hq']
    linear_combination x * hσ2
  rw [key]
  have ha_nn : 0 ≤ M * x ^ 2 := le_trans (abs_nonneg a) h1
  have t1 : |σ * (x * b)| ≤ M * x ^ 2 := by
    rw [abs_mul, hσabs, one_mul, abs_mul]
    calc |x| * |b| ≤ |x| * (M * |x|) := mul_le_mul_of_nonneg_left h2 (abs_nonneg x)
      _ = M * |x| ^ 2 := by ring
      _ = M * x ^ 2 := by rw [sq_abs]
  have t2 : |σ * a| ≤ M * x ^ 2 := by
    rw [abs_mul, hσabs, one_mul]; exact h1
  have t3 : |a * b| ≤ M ^ 2 * |x| ^ 3 := by
    rw [abs_mul]
    calc |a| * |b| ≤ (M * x ^ 2) * (M * |x|) := mul_le_mul h1 h2 (abs_nonneg b) ha_nn
      _ = M ^ 2 * |x| ^ 3 := by rw [← sq_abs]; ring
  calc |σ * (x * b) + σ * a + a * b|
      ≤ |σ * (x * b) + σ * a| + |a * b| := abs_add_le _ _
    _ ≤ (|σ * (x * b)| + |σ * a|) + |a * b| :=
          add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (M * x ^ 2 + M * x ^ 2) + M ^ 2 * |x| ^ 3 :=
          add_le_add (add_le_add t1 t2) t3
    _ = 2 * M * x ^ 2 + M ^ 2 * |x| ^ 3 := by ring

end Work.RPB.B1a
