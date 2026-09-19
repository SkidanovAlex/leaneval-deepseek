import Mathlib

namespace Commons.Data.Int

/-- Every integer is the difference of its positive and negative parts. -/
lemma int_eq_pos_sub_neg (a : ℤ) : a = max a 0 - max (-a) 0 := by
  rcases le_total 0 a with h | h
  · rw [max_eq_left h, max_eq_right (by linarith : -a ≤ 0)]
    ring
  · rw [max_eq_right h, max_eq_left (by linarith : 0 ≤ -a)]
    ring

/-- Casting `max x 0` from `ℕ` back to `ℤ` is the identity. -/
lemma int_toNat_max_eq (x : ℤ) : ((max x 0).toNat : ℤ) = max x 0 :=
  Int.toNat_of_nonneg (le_max_right x 0)

theorem mul_eq_pos_neg_parts (a b : ℤ) :
    a * b = (((max a 0).toNat * (max b 0).toNat : ℕ) : ℤ)
      - (((max a 0).toNat * (max (-b) 0).toNat : ℕ) : ℤ)
      - (((max (-a) 0).toNat * (max b 0).toNat : ℕ) : ℤ)
      + (((max (-a) 0).toNat * (max (-b) 0).toNat : ℕ) : ℤ) := by
  have h1 : ((max a 0).toNat : ℤ) = max a 0 := int_toNat_max_eq a
  have h2 : ((max (-a) 0).toNat : ℤ) = max (-a) 0 := int_toNat_max_eq (-a)
  have h3 : ((max b 0).toNat : ℤ) = max b 0 := int_toNat_max_eq b
  have h4 : ((max (-b) 0).toNat : ℤ) = max (-b) 0 := int_toNat_max_eq (-b)
  conv_lhs => rw [int_eq_pos_sub_neg a, int_eq_pos_sub_neg b]
  push_cast
  rw [h1, h2, h3, h4]
  ring

end Commons.Data.Int
