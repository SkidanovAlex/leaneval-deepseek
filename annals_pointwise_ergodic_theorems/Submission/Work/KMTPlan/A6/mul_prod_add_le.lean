import Mathlib

namespace Work.KMTPlan.A6

/-- Elementary ENNReal inequality: the bilinear cross terms are dominated by the
product of the sums.  Both `A * B + A * Vb = A * (B + Vb)` and `B * Va` are at
most `(A + Va) * (B + Vb)`. -/
theorem mul_prod_add_le {A Va B Vb : ENNReal} :
    A * B + (B * Va + A * Vb) ≤ 2 * ((A + Va) * (B + Vb)) := by
  have hA : A ≤ A + Va := le_add_right le_rfl
  have hB : B ≤ B + Vb := le_add_right le_rfl
  have h1 : A * (B + Vb) ≤ (A + Va) * (B + Vb) := by
    apply mul_le_mul_of_nonneg_right hA
    exact zero_le
  have h2 : B * Va ≤ (A + Va) * (B + Vb) := by
    calc B * Va ≤ (B + Vb) * Va := by
          apply mul_le_mul_of_nonneg_right hB
          exact zero_le
      _ = Va * (B + Vb) := by ring
      _ ≤ (A + Va) * (B + Vb) := by
          apply mul_le_mul_of_nonneg_right (le_add_left le_rfl)
          exact zero_le
  calc A * B + (B * Va + A * Vb) = A * (B + Vb) + B * Va := by ring
    _ ≤ (A + Va) * (B + Vb) + (A + Va) * (B + Vb) := add_le_add h1 h2
    _ = 2 * ((A + Va) * (B + Vb)) := by ring

end Work.KMTPlan.A6
