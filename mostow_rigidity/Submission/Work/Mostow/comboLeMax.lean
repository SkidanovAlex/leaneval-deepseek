import Mathlib

namespace Work.Mostow

theorem comboLeMax {Mp Mq a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1)
    (hMp : 0 ≤ Mp) (hMq : 0 ≤ Mq) : a * Mp + b * Mq ≤ max Mp Mq := by
  have hmax : 0 ≤ max Mp Mq := le_trans hMp (le_max_left Mp Mq)
  have h1 : a * Mp ≤ a * max Mp Mq := mul_le_mul_of_nonneg_left (le_max_left Mp Mq) ha
  have h2 : b * Mq ≤ b * max Mp Mq := mul_le_mul_of_nonneg_left (le_max_right Mp Mq) hb
  have h3 : (a + b) * max Mp Mq ≤ 1 * max Mp Mq :=
    mul_le_mul_of_nonneg_right hab hmax
  have h4 : a * max Mp Mq + b * max Mp Mq = (a + b) * max Mp Mq := by ring
  linarith [h1, h2, h3, h4]

end Work.Mostow
