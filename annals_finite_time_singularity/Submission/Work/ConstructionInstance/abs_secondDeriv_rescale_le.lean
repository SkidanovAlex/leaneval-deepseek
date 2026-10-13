import Mathlib.Algebra.Order.Star.Real

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- `| -( a + b - c ) | = | a + b - c |` style triangle bound used below. -/
private theorem abs_add_sub_le (a b c : ℝ) :
    |a + b - c| ≤ |a| + |b| + |c| := by
  have e : a + b - c = (a + b) + (-c) := by ring
  rw [e]
  calc |(a + b) + (-c)| ≤ |a + b| + |(-c)| := abs_add_le _ _
    _ = |a + b| + |c| := by rw [abs_neg]
    _ ≤ (|a| + |b|) + |c| := by
          have := abs_add_le a b
          linarith
    _ = |a| + |b| + |c| := by ring

theorem abs_secondDeriv_rescale_le {B1 B2 K K₂ L G dd l l₂ m : ℝ}
    (hm : 0 < m) (hmL : m ≤ L) (hK : 0 ≤ K) (hK₂ : 0 ≤ K₂)
    (hG : |G| ≤ B1) (hdd : |dd| ≤ B2) (hl : |l| ≤ K) (hl₂ : |l₂| ≤ K₂) :
    |-(l₂ * G / L ^ 2 + l * (-(l / L) * dd) / L ^ 2 - 2 * l ^ 2 * G / L ^ 3)|
      ≤ K₂ * B1 / m ^ 2 + K ^ 2 * B2 / m ^ 3 + 2 * K ^ 2 * B1 / m ^ 3 := by
  have hL : 0 < L := lt_of_lt_of_le hm hmL
  have hB1 : 0 ≤ B1 := le_trans (abs_nonneg G) hG
  have hB2 : 0 ≤ B2 := le_trans (abs_nonneg dd) hdd
  have hm2 : (0:ℝ) < m ^ 2 := by positivity
  have hm3 : (0:ℝ) < m ^ 3 := by positivity
  have hL2 : (0:ℝ) < L ^ 2 := by positivity
  have hL3 : (0:ℝ) < L ^ 3 := by positivity
  have hmL2 : m ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hm.le hmL 2
  have hmL3 : m ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ hm.le hmL 3
  have hlK : l ^ 2 ≤ K ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg hK]; exact hl
  -- bound of the first term
  have hA : |l₂ * G / L ^ 2| ≤ K₂ * B1 / m ^ 2 := by
    rw [abs_div, abs_of_pos hL2, abs_mul]
    have h1 : |l₂| * |G| ≤ K₂ * B1 := mul_le_mul hl₂ hG (abs_nonneg G) hK₂
    calc |l₂| * |G| / L ^ 2 ≤ K₂ * B1 / L ^ 2 :=
          div_le_div_of_nonneg_right h1 hL2.le
      _ ≤ K₂ * B1 / m ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) hm2 hmL2
  -- bound of the second term
  have hB : |l * (-(l / L) * dd) / L ^ 2| ≤ K ^ 2 * B2 / m ^ 3 := by
    have heq : l * (-(l / L) * dd) / L ^ 2 = -(l ^ 2 * dd / L ^ 3) := by
      field_simp
    rw [heq, abs_neg, abs_div, abs_of_pos hL3, abs_mul,
        abs_of_nonneg (sq_nonneg l)]
    have h1 : l ^ 2 * |dd| ≤ K ^ 2 * B2 :=
      mul_le_mul hlK hdd (abs_nonneg dd) (sq_nonneg K)
    calc l ^ 2 * |dd| / L ^ 3 ≤ K ^ 2 * B2 / L ^ 3 :=
          div_le_div_of_nonneg_right h1 hL3.le
      _ ≤ K ^ 2 * B2 / m ^ 3 :=
          div_le_div_of_nonneg_left (by positivity) hm3 hmL3
  -- bound of the third term
  have hC : |2 * l ^ 2 * G / L ^ 3| ≤ 2 * K ^ 2 * B1 / m ^ 3 := by
    rw [abs_div, abs_of_pos hL3, abs_mul, abs_mul,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg (sq_nonneg l)]
    have h1 : l ^ 2 * |G| ≤ K ^ 2 * B1 :=
      mul_le_mul hlK hG (abs_nonneg G) (sq_nonneg K)
    have h2 : 2 * (l ^ 2 * |G|) ≤ 2 * (K ^ 2 * B1) :=
      mul_le_mul_of_nonneg_left h1 (by norm_num)
    calc 2 * l ^ 2 * |G| / L ^ 3 = 2 * (l ^ 2 * |G|) / L ^ 3 := by ring
      _ ≤ 2 * (K ^ 2 * B1) / L ^ 3 := div_le_div_of_nonneg_right h2 hL3.le
      _ = 2 * K ^ 2 * B1 / L ^ 3 := by ring
      _ ≤ 2 * K ^ 2 * B1 / m ^ 3 :=
          div_le_div_of_nonneg_left (by positivity) hm3 hmL3
  rw [abs_neg]
  have htri := abs_add_sub_le (l₂ * G / L ^ 2) (l * (-(l / L) * dd) / L ^ 2)
      (2 * l ^ 2 * G / L ^ 3)
  linarith [htri, hA, hB, hC]

end Work.ConstructionInstance
