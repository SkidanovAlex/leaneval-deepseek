import Mathlib

namespace Work.KMTAreas.A4

/-- For `a, b ≥ 0` and `s ≥ 0`, `(a + b)^s ≤ 2^s * (a^s + b^s)`.
Indeed `a + b ≤ 2 * max a b`, and `max a b` is `a` or `b`, so
`(max a b)^s ≤ a^s + b^s`. -/
lemma addRpowLeTwoRpowMul {a b s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 ≤ s) :
    (a + b) ^ s ≤ (2 : ℝ) ^ s * (a ^ s + b ^ s) := by
  have hab : 0 ≤ a + b := add_nonneg ha hb
  have hmax0 : 0 ≤ max a b := le_trans ha (le_max_left a b)
  calc (a + b) ^ s ≤ (2 * max a b) ^ s :=
        Real.rpow_le_rpow hab (by linarith [le_max_left a b, le_max_right a b]) hs
    _ = 2 ^ s * (max a b) ^ s := Real.mul_rpow (by norm_num) hmax0
    _ ≤ 2 ^ s * (a ^ s + b ^ s) := by
        have h2s : 0 ≤ (2 : ℝ) ^ s := Real.rpow_nonneg (by norm_num) s
        have hmax : (max a b) ^ s ≤ a ^ s + b ^ s := by
          rcases max_cases a b with ⟨h, _⟩ | ⟨h, _⟩
          · rw [h]; exact le_add_of_nonneg_right (Real.rpow_nonneg hb s)
          · rw [h]; exact le_add_of_nonneg_left (Real.rpow_nonneg ha s)
        exact mul_le_mul_of_nonneg_left hmax h2s

end Work.KMTAreas.A4
