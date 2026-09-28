import Mathlib

namespace Work.HP.GradCount

/-- The integers in an affine interval of real length `2L/a` number at most `2L/a + 2`. -/
theorem ncard_int_interval (a T L : ℝ) (ha : 0 < a) (hL : 0 ≤ L) :
    (({z : ℤ | |(z : ℝ) * a + T| ≤ L} : Set ℤ).ncard : ℝ) ≤ 2 * L / a + 2 := by
  set lo : ℤ := ⌈(-L - T) / a⌉ with hlo
  set hi : ℤ := ⌊(L - T) / a⌋ with hhi
  have hsub : {z : ℤ | |(z : ℝ) * a + T| ≤ L} ⊆ Set.Icc lo hi := by
    intro z hz
    have hz' : |(z : ℝ) * a + T| ≤ L := hz
    obtain ⟨h1, h2⟩ := abs_le.mp hz'
    simp only [Set.mem_Icc, hlo, hhi]
    constructor
    · rw [Int.ceil_le, div_le_iff₀ ha]
      linarith
    · rw [Int.le_floor, le_div_iff₀ ha]
      linarith
  have hcard := Set.ncard_le_ncard hsub
  have hIcc : (Set.Icc lo hi).ncard = (hi + 1 - lo).toNat := by
    rw [Set.ncard_Icc, Int.card_Icc]
  rw [hIcc] at hcard
  have hhi' : (hi : ℝ) ≤ (L - T) / a := by rw [hhi]; exact Int.floor_le _
  have hlo' : (-L - T) / a ≤ (lo : ℝ) := by rw [hlo]; exact Int.le_ceil _
  have hbound : (((hi + 1 - lo).toNat : ℝ)) ≤ 2 * L / a + 2 := by
    rcases lt_or_ge (hi + 1 - lo) 0 with h | h
    · rw [Int.toNat_of_nonpos (le_of_lt h)]
      have : (0 : ℝ) ≤ 2 * L / a := by positivity
      linarith
    · have h1 : ((hi + 1 - lo).toNat : ℝ) = (hi : ℝ) + 1 - (lo : ℝ) := by
        exact_mod_cast (Int.toNat_of_nonneg h : ((hi + 1 - lo).toNat : ℤ) = hi + 1 - lo)
      rw [h1]
      have hE : (L - T) / a + 1 - (-L - T) / a = 2 * L / a + 1 := by
        field_simp
        ring
      linarith
  calc (({z : ℤ | |(z : ℝ) * a + T| ≤ L} : Set ℤ).ncard : ℝ)
      ≤ ((hi + 1 - lo).toNat : ℝ) := by exact_mod_cast hcard
    _ ≤ 2 * L / a + 2 := hbound

end Work.HP.GradCount
