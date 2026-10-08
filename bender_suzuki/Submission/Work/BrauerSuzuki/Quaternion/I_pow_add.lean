import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Quaternion

/-- For an integer exponent, `I ^ i` only depends on `i` modulo `4`.  Here we
reduce to a natural-number power `I ^ ((i % 4).toNat)`, since `I ^ 4 = 1`. -/
private lemma I_zpow_eq (i : ℤ) : (Complex.I : ℂ) ^ i = Complex.I ^ (i % 4).toNat := by
  conv_lhs => rw [show i = 4 * (i / 4) + i % 4 from (Int.mul_ediv_add_emod i 4).symm]
  rw [zpow_add₀ Complex.I_ne_zero, zpow_mul]
  have : (Complex.I : ℂ) ^ (4 : ℤ) = 1 := by norm_num
  rw [this, one_zpow, one_mul]
  have hnn : 0 ≤ i % 4 := Int.emod_nonneg i (by norm_num)
  conv_lhs => rw [show (i % 4) = ↑(i % 4).toNat from (Int.toNat_of_nonneg hnn).symm]
  rw [zpow_natCast]

/-- If `i` is even but not divisible by `4`, then `i % 4 = 2`. -/
private lemma emod4_eq_two_of (i : ℤ) (h2 : i % 2 = 0) (h4 : i % 4 ≠ 0) : i % 4 = 2 := by
  have hlt : i % 4 < 4 := Int.emod_lt_of_pos i (by norm_num)
  have hnn : 0 ≤ i % 4 := Int.emod_nonneg i (by norm_num)
  have hev : (i % 4) % 2 = 0 := by
    rw [Int.emod_emod_of_dvd i (by norm_num : (2 : ℤ) ∣ 4)]
    exact h2
  omega

private lemma conj_one (i : ℤ) (h4 : (4 : ℤ) ∣ i) : Complex.I ^ i + Complex.I ^ (-i) = 2 := by
  have hmod : i % 4 = 0 := (Int.dvd_iff_emod_eq_zero).mp h4
  have hmod' : (-i) % 4 = 0 := (Int.dvd_iff_emod_eq_zero).mp (dvd_neg.mpr h4)
  rw [I_zpow_eq i, I_zpow_eq (-i), hmod, hmod']
  norm_num

private lemma conj_two (i : ℤ) (h2 : (2 : ℤ) ∣ i) (h4 : ¬ (4 : ℤ) ∣ i) :
    Complex.I ^ i + Complex.I ^ (-i) = -2 := by
  have hmod2 : i % 2 = 0 := (Int.dvd_iff_emod_eq_zero).mp h2
  have hmod4 : i % 4 ≠ 0 := fun h => h4 ((Int.dvd_iff_emod_eq_zero).mpr h)
  have hmod2' : (-i) % 2 = 0 := (Int.dvd_iff_emod_eq_zero).mp ((dvd_neg).mpr h2)
  have hmod4' : (-i) % 4 ≠ 0 := fun h => h4 (dvd_neg.mp ((Int.dvd_iff_emod_eq_zero).mpr h))
  have hi4 : i % 4 = 2 := emod4_eq_two_of i hmod2 hmod4
  have hneg4 : (-i) % 4 = 2 := emod4_eq_two_of (-i) hmod2' hmod4'
  rw [I_zpow_eq i, I_zpow_eq (-i), hi4, hneg4]
  norm_num

private lemma conj_three (i : ℤ) (h2 : ¬ (2 : ℤ) ∣ i) :
    Complex.I ^ i + Complex.I ^ (-i) = 0 := by
  have hodd : Odd i := by
    rw [← Int.not_even_iff_odd]
    intro he
    exact h2 (even_iff_two_dvd.mp he)
  have hsq : (Complex.I ^ i) * (Complex.I ^ i) = -1 := by
    rw [← zpow_add₀ Complex.I_ne_zero]
    have h2i : i + i = 2 * i := by ring
    rw [h2i, zpow_mul]
    have hI2 : (Complex.I : ℂ) ^ (2 : ℤ) = -1 := by norm_num
    rw [hI2]
    exact Odd.neg_one_zpow hodd
  have hinv : Complex.I ^ (-i) = -(Complex.I ^ i) := by
    rw [zpow_neg, inv_eq_of_mul_eq_one_right]
    rw [mul_neg, hsq]
    ring
  rw [hinv]
  ring

theorem I_pow_add (i : ℤ) :
    (((4 : ℤ) ∣ i → Complex.I ^ i + Complex.I ^ (-i) = 2)) ∧
    (((2 : ℤ) ∣ i → ¬ (4 : ℤ) ∣ i → Complex.I ^ i + Complex.I ^ (-i) = -2)) ∧
    ((¬ (2 : ℤ) ∣ i → Complex.I ^ i + Complex.I ^ (-i) = 0)) := by
  exact ⟨conj_one i, fun h2 h4 => conj_two i h2 h4, conj_three i⟩

end Work.BrauerSuzuki.Quaternion
