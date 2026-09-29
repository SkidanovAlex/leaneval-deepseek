import Mathlib
import Submission.Work.Fx.scaleCommon

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Fx

lemma mul_succ_le_two_pow {m n k : ℕ} (hm : m ≤ 2 ^ k) : m * (n + 1) ≤ 2 ^ (n + k) := by
  have h1 : n + 1 ≤ 2 ^ n := Nat.succ_le_of_lt Nat.lt_two_pow_self
  calc m * (n + 1) ≤ 2 ^ k * (n + 1) := Nat.mul_le_mul_right _ hm
    _ ≤ 2 ^ k * 2 ^ n := Nat.mul_le_mul_left _ h1
    _ = 2 ^ (k + n) := by rw [← Nat.pow_add]
    _ = 2 ^ (n + k) := by rw [Nat.add_comm]

lemma natCast_two_pow (n : ℕ) : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by
  push_cast
  ring

lemma pi_div_log_two_lt_five : Real.pi / Real.log 2 < 5 := by
  have hlog : (0:ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  rw [div_lt_iff₀ hlog]
  nlinarith [Real.pi_lt_d6, Real.log_two_gt_d9]

lemma int_natAbs_cast {a : ℤ} (ha : 0 ≤ a) : ((a.natAbs : ℕ) : ℝ) = (a : ℝ) := by
  have h1 : ((a.natAbs : ℤ) : ℝ) = ((a : ℤ) : ℝ) := by rw [Int.natAbs_of_nonneg ha]
  have h2 : ((a.natAbs : ℕ) : ℝ) = ((a.natAbs : ℤ) : ℝ) := by norm_num
  rw [h2]; exact h1

theorem expNegXtau (p j k : ℕ) (u L X : ℤ) (τ : ℕ)
    (hp : 100 ≤ p) (hk : 1 ≤ k) (hj : j < k * (p + 2))
    (hu : |(u : ℝ) - 2 ^ (2 * p + 60) * Real.pi| ≤ 1)
    (hL : |(L : ℝ) - 2 ^ (2 * p + 60) * Real.log 2| ≤ 1)
    (hX : X = Int.tdiv (u * j) k) (hτ : τ = (Int.tdiv X L).toNat) :
    0 ≤ X ∧
    |(X : ℝ) - 2 ^ (2 * p + 60) * (Real.pi * j / k)| ≤ ((p + 3 : ℕ) : ℝ) ∧
    X.natAbs.size ≤ 3 * p + 80 ∧
    |(τ : ℝ) - (Real.pi * j / k) / Real.log 2| ≤ 2 ∧
    τ ≤ 6 * (p + 2) ∧ τ.size ≤ 7 * p + 10 ∧
    u.natAbs.size ≤ 2 * p + 70 ∧ L.natAbs.size ≤ 2 * p + 70 := by
  set B : ℝ := (2:ℝ)^(2*p+60) with hB
  set q : ℝ := Real.pi * (j:ℝ) / (k:ℝ) with hq
  have hlog : (0:ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hloglt1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hBpos : 0 < B := by rw [hB]; exact pow_pos (by norm_num) _
  have hBge6 : (6:ℝ) ≤ B := by
    rw [hB]
    have h1 : (2:ℝ)^3 ≤ (2:ℝ)^(2*p+60) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (6:ℝ) ≤ (2:ℝ)^3 := by norm_num
    linarith
  have hkpos : (0:ℤ) < (k:ℤ) := by exact_mod_cast (show 0 < k by omega)
  have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hq_nonneg : 0 ≤ q := by
    rw [hq]; exact div_nonneg (mul_nonneg (le_of_lt Real.pi_pos) (Nat.cast_nonneg j)) (le_of_lt hkR)
  have hjk_lt : (j:ℝ)/(k:ℝ) < ((p+2:ℕ):ℝ) := by
    rw [div_lt_iff₀ hkR]
    have h := (Nat.cast_lt (α := ℝ)).mpr hj
    push_cast at h ⊢
    linarith
  -- ======================= u =======================
  have hu_lo : B * Real.pi - 1 ≤ (u:ℝ) := by linarith [(abs_le.mp hu).1]
  have hu_hi : (u:ℝ) ≤ B * Real.pi + 1 := by linarith [(abs_le.mp hu).2]
  have hu_posR : (0:ℝ) < (u:ℝ) := by nlinarith [hu_lo, hBge6, Real.pi_gt_three]
  have hu_pos : (0:ℤ) < u := by exact_mod_cast hu_posR
  have hUcast : ((u.natAbs : ℕ) : ℝ) = (u:ℝ) := int_natAbs_cast (le_of_lt hu_pos)
  have hu_lt : (u:ℝ) < (2:ℝ)^(2*p+63) := by
    have h1 : B * Real.pi < (2:ℝ)^(2*p+62) := by
      have h4 : (2:ℝ)^(2*p+62) = B * 4 := by
        rw [hB, show 2*p+62 = (2*p+60)+2 by ring, pow_add]; norm_num
      have h5 : B * Real.pi < B * 4 := mul_lt_mul_of_pos_left Real.pi_lt_four hBpos
      linarith
    have h2 : (2:ℝ)^(2*p+62) + 1 ≤ (2:ℝ)^(2*p+63) := by
      have hx : (1:ℝ) ≤ (2:ℝ)^(2*p+62) := one_le_pow₀ (by norm_num)
      have hpw : (2:ℝ)^(2*p+63) = 2 * (2:ℝ)^(2*p+62) := by
        rw [show 2*p+63 = (2*p+62)+1 by ring, pow_succ]; ring
      linarith
    linarith [hu_hi, h1, h2]
  have hUnatAbs : u.natAbs < 2^(2*p+63) := by
    have hcast : ((2^(2*p+63) : ℕ) : ℝ) = (2:ℝ)^(2*p+63) := natCast_two_pow _
    have h2 : ((u.natAbs : ℕ) : ℝ) < ((2^(2*p+63) : ℕ) : ℝ) := by rw [hUcast, hcast]; exact hu_lt
    exact Nat.cast_lt.mp h2
  have hu_size : u.natAbs.size ≤ 2*p+70 := by
    rw [Nat.size_le]
    exact lt_of_lt_of_le hUnatAbs (Nat.pow_le_pow_right (by norm_num) (by omega))
  -- ======================= L =======================
  have hL_lo : B * Real.log 2 - 1 ≤ (L:ℝ) := by linarith [(abs_le.mp hL).1]
  have hL_hi : (L:ℝ) ≤ B * Real.log 2 + 1 := by linarith [(abs_le.mp hL).2]
  have hL_posR : (0:ℝ) < (L:ℝ) := by nlinarith [hL_lo, hBge6, Real.log_two_gt_d9]
  have hL_pos : (0:ℤ) < L := by exact_mod_cast hL_posR
  have hLcast : ((L.natAbs : ℕ) : ℝ) = (L:ℝ) := int_natAbs_cast (le_of_lt hL_pos)
  have hL_half : B / 2 ≤ (L:ℝ) := by
    have hkey : (1:ℝ) ≤ B * (Real.log 2 - 1/2) := by
      have h1 : (0:ℝ) ≤ Real.log 2 - 1/2 := by linarith [Real.log_two_gt_d9]
      have h2 := mul_le_mul_of_nonneg_right hBge6 h1
      nlinarith [Real.log_two_gt_d9]
    nlinarith [hL_lo, hkey]
  have hBhalf : B / 2 = (2:ℝ)^(2*p+59) := by
    rw [hB, show 2*p+60 = (2*p+59)+1 by ring, pow_succ]; ring
  have hLge : (2:ℝ)^(2*p+59) ≤ (L:ℝ) := by rw [← hBhalf]; exact hL_half
  have hL_lt : (L:ℝ) < (2:ℝ)^(2*p+61) := by
    have h1 : B * Real.log 2 < B := mul_lt_of_lt_one_right hBpos hloglt1
    have h4 : (2:ℝ)^(2*p+61) = B * 2 := by
      rw [hB, show 2*p+61 = (2*p+60)+1 by ring, pow_add]; norm_num
    have h2 : B + 1 ≤ B * 2 := by nlinarith [hBge6]
    linarith [hL_hi, h1, h2, h4]
  have hLnatAbs : L.natAbs < 2^(2*p+61) := by
    have hcast : ((2^(2*p+61) : ℕ) : ℝ) = (2:ℝ)^(2*p+61) := natCast_two_pow _
    have h2 : ((L.natAbs : ℕ) : ℝ) < ((2^(2*p+61) : ℕ) : ℝ) := by rw [hLcast, hcast]; exact hL_lt
    exact Nat.cast_lt.mp h2
  have hL_size : L.natAbs.size ≤ 2*p+70 := by
    rw [Nat.size_le]
    exact lt_of_lt_of_le hLnatAbs (Nat.pow_le_pow_right (by norm_num) (by omega))
  -- ======================= X =======================
  have hX0 : 0 ≤ X := by
    rw [hX]
    exact Int.tdiv_nonneg (mul_nonneg (le_of_lt hu_pos) (Int.natCast_nonneg j)) (le_of_lt hkpos)
  have hXnatAbs : X.natAbs = u.natAbs * j / k := by
    rw [hX, Int.natAbs_tdiv, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
    rfl
  have hu_natAbs_pos : 0 < u.natAbs := Int.natAbs_pos.mpr (ne_of_gt hu_pos)
  have hXnatAbs_lt : X.natAbs < u.natAbs * (p+2) := by
    rw [hXnatAbs, Nat.div_lt_iff_lt_mul (show 0 < k by omega)]
    have h := Nat.mul_lt_mul_of_pos_left hj hu_natAbs_pos
    calc u.natAbs * j < u.natAbs * (k * (p+2)) := h
      _ = (u.natAbs * (p+2)) * k := by ring
  have hXsize : X.natAbs.size ≤ 3*p+80 := by
    rw [Nat.size_le]
    have h1 : u.natAbs * (p+2) < 2^(2*p+63) * (p+2) :=
      Nat.mul_lt_mul_of_pos_right hUnatAbs (show 0 < p+2 by omega)
    have h2 : 2^(2*p+63) * (p+2) ≤ 2^(3*p+64) := by
      have h := mul_succ_le_two_pow (m := 2^(2*p+63)) (n := p+1) (k := 2*p+63) (le_refl _)
      simpa [show (p+1)+1 = p+2 by ring, show p+1+(2*p+63) = 3*p+64 by ring] using h
    have h3 : 2^(3*p+64) ≤ 2^(3*p+80) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact lt_of_lt_of_le (lt_trans hXnatAbs_lt h1) (le_trans h2 h3)
  have hXe : |(X:ℝ) - B * q| ≤ ((p+3:ℕ):ℝ) := by
    have h1 : |(X:ℝ) - (u:ℝ)*(j:ℝ)/(k:ℝ)| < 1 := by
      have h := tdiv_sub_div_lt_one (u*j) hkpos
      rw [← hX] at h
      push_cast at h
      simpa using h
    have h2 : |(u:ℝ)*(j:ℝ)/(k:ℝ) - B*q| ≤ (j:ℝ)/(k:ℝ) := by
      rw [hq]
      have hkey : (u:ℝ)*(j:ℝ)/(k:ℝ) - B * (Real.pi * (j:ℝ)/(k:ℝ))
          = ((u:ℝ) - B*Real.pi) * ((j:ℝ)/(k:ℝ)) := by
        ring
      rw [hkey, abs_mul, abs_of_nonneg (div_nonneg (Nat.cast_nonneg j) (le_of_lt hkR))]
      calc |(u:ℝ) - B*Real.pi| * ((j:ℝ)/(k:ℝ)) ≤ 1 * ((j:ℝ)/(k:ℝ)) :=
            mul_le_mul_of_nonneg_right hu (div_nonneg (Nat.cast_nonneg j) (le_of_lt hkR))
        _ = (j:ℝ)/(k:ℝ) := one_mul _
    have h4 : (1:ℝ) + (j:ℝ)/(k:ℝ) < ((p+3:ℕ):ℝ) := by
      have := hjk_lt
      push_cast at this ⊢
      linarith
    calc |(X:ℝ) - B*q| ≤ |(X:ℝ) - (u:ℝ)*(j:ℝ)/(k:ℝ)| + |(u:ℝ)*(j:ℝ)/(k:ℝ) - B*q| := abs_sub_le _ _ _
      _ ≤ 1 + (j:ℝ)/(k:ℝ) := add_le_add (le_of_lt h1) h2
      _ ≤ ((p+3:ℕ):ℝ) := le_of_lt h4
  -- ======================= τ =======================
  have h12 : 24*p+52 ≤ 2^(2*p+59) := by
    have h1 : 26*(p+2) ≤ 2^(p+6) := by
      have h := mul_succ_le_two_pow (m := 26) (n := p+1) (k := 5) (by norm_num)
      simpa [show (p+1)+1 = p+2 by ring, show (p+1)+5 = p+6 by ring] using h
    have h2 : 24*p+52 ≤ 26*(p+2) := by nlinarith
    have h3 : 2^(p+6) ≤ 2^(2*p+59) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact le_trans h2 (le_trans h1 h3)
  have h12R : (24*(p:ℝ)+52) ≤ (2:ℝ)^(2*p+59) := by
    have h := (Nat.cast_le (α := ℝ)).mpr h12
    rw [natCast_two_pow] at h
    push_cast at h
    exact h
  have hr_nonneg : 0 ≤ q / Real.log 2 := div_nonneg hq_nonneg (le_of_lt hlog)
  have hr_lt : q / Real.log 2 < 5 * ((p:ℝ)+2) := by
    have hπ : Real.pi / Real.log 2 < 5 := pi_div_log_two_lt_five
    have hkey : q / Real.log 2 = (Real.pi / Real.log 2) * ((j:ℝ)/(k:ℝ)) := by
      rw [hq]; ring
    rw [hkey]
    have hjk : (j:ℝ)/(k:ℝ) < (p:ℝ)+2 := by
      have := hjk_lt; push_cast at this; exact this
    calc (Real.pi / Real.log 2) * ((j:ℝ)/(k:ℝ))
        < (Real.pi / Real.log 2) * ((p:ℝ)+2) := mul_lt_mul_of_pos_left hjk (div_pos Real.pi_pos hlog)
      _ < 5 * ((p:ℝ)+2) := mul_lt_mul_of_pos_right hπ (by have hp0 : (0:ℝ) ≤ (p:ℝ) := Nat.cast_nonneg p; linarith)
  have hτabs : |(τ:ℝ) - q/Real.log 2| ≤ 2 := by
    have htd_pos : 0 ≤ Int.tdiv X L := Int.tdiv_nonneg hX0 (le_of_lt hL_pos)
    have hτ_cast : (τ:ℝ) = ((Int.tdiv X L : ℤ) : ℝ) := by
      rw [hτ]
      have h2 := congrArg (fun z : ℤ => (z:ℝ)) (Int.toNat_of_nonneg htd_pos)
      push_cast at h2
      exact h2
    have h1 : |(τ:ℝ) - (X:ℝ)/L| < 1 := by
      have h := tdiv_sub_div_lt_one X hL_pos
      rw [hτ_cast]; exact h
    have h2 : |(X:ℝ)/L - q/Real.log 2| ≤ 1/2 := by
      have hLne : (L:ℝ) ≠ 0 := ne_of_gt hL_posR
      have hkey : (X:ℝ)/L - q/Real.log 2 = ((X:ℝ) - (q/Real.log 2)*L)/L := by
        rw [sub_div, mul_div_cancel_right₀ _ hLne]
      rw [hkey, abs_div, abs_of_pos hL_posR]
      have hrB : (q/Real.log 2) * (B*Real.log 2) = B*q := by
        rw [div_mul_eq_mul_div]
        have h1 : q * (B*Real.log 2) = (q*B) * Real.log 2 := by ring
        rw [h1, mul_div_cancel_right₀ _ (ne_of_gt hlog)]
        ring
      have hsplit : (X:ℝ) - (q/Real.log 2)*L
          = ((X:ℝ) - B*q) - (q/Real.log 2)*((L:ℝ) - B*Real.log 2) := by
        have hms : (q/Real.log 2)*((L:ℝ) - B*Real.log 2) = (q/Real.log 2)*L - B*q := by
          rw [mul_sub, hrB]
        rw [hms]; ring
      have hb1 : |(X:ℝ) - B*q| ≤ (p:ℝ)+3 := by
        have := hXe; push_cast at this; exact this
      have hb2 : |(q/Real.log 2)*((L:ℝ) - B*Real.log 2)| ≤ (q/Real.log 2)*1 := by
        rw [abs_mul, abs_of_nonneg hr_nonneg]
        exact mul_le_mul_of_nonneg_left hL hr_nonneg
      have hnum : |(X:ℝ) - (q/Real.log 2)*L| ≤ 12*(p:ℝ)+26 := by
        rw [hsplit]
        calc |((X:ℝ) - B*q) - (q/Real.log 2)*((L:ℝ) - B*Real.log 2)|
            ≤ |(X:ℝ) - B*q| + |(q/Real.log 2)*((L:ℝ) - B*Real.log 2)| := by
              simpa using abs_sub_le ((X:ℝ) - B*q) 0 ((q/Real.log 2)*((L:ℝ) - B*Real.log 2))
          _ ≤ ((p:ℝ)+3) + (q/Real.log 2)*1 := add_le_add hb1 hb2
          _ ≤ 12*(p:ℝ)+26 := by linarith [hr_lt]
      rw [div_le_iff₀ hL_posR]
      linarith [hnum, hLge, h12R]
    calc |(τ:ℝ) - q/Real.log 2| ≤ |(τ:ℝ) - (X:ℝ)/L| + |(X:ℝ)/L - q/Real.log 2| := abs_sub_le _ _ _
      _ ≤ 1 + 1/2 := add_le_add (le_of_lt h1) h2
      _ ≤ 2 := by norm_num
  have hτ_le : τ ≤ 6*(p+2) := by
    have h1 := (abs_le.mp hτabs).2
    have hlt : (τ:ℝ) < ((6*(p+2) : ℕ) : ℝ) := by
      have hcast : ((6*(p+2) : ℕ) : ℝ) = 6*((p:ℝ)+2) := by push_cast; ring
      rw [hcast]
      have h2 : (2:ℝ) ≤ (p:ℝ)+2 := by have hp0 : (0:ℝ) ≤ (p:ℝ) := Nat.cast_nonneg p; linarith
      linarith [h1, hr_lt, h2]
    exact le_of_lt ((Nat.cast_lt (α := ℝ)).mp hlt)
  have hτ_size : τ.size ≤ 7*p+10 := by
    have h1 : τ.size ≤ τ := Nat.size_le.mpr Nat.lt_two_pow_self
    omega
  exact ⟨hX0, hXe, hXsize, hτabs, hτ_le, hτ_size, hu_size, hL_size⟩

end Work.Fx
