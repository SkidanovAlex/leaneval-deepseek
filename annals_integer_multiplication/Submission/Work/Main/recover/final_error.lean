import Mathlib
import Submission.Work.Main.defs

namespace Work.Main.recover

/-- `2^(k*b) = (2^b)^k` for the real power of two. -/
lemma two_pow_mul (b k : ℕ) : (2:ℝ)^(k*b) = ((2:ℝ)^b)^k := by
  rw [mul_comm k b, pow_mul]

/-- The combination of powers that appears in the final error estimate:
`2^(2b) · (2^(6b))⁻¹ · 2^(b-5) · 2^(3b) = 1/32`. -/
lemma powid (b : ℕ) (hb : 5 ≤ b) :
    (2:ℝ)^(2*b) * ((2:ℝ)^(6*b))⁻¹ * (2:ℝ)^(b-5) * (2:ℝ)^(3*b) = 1/32 := by
  have hxb : (2:ℝ)^b = (2:ℝ)^(b-5) * 32 := by
    have hpow : (2:ℝ)^(b-5) * 32 = (2:ℝ)^(b-5) * (2:ℝ)^5 := by norm_num
    rw [hpow, ← pow_add]
    congr 1
    omega
  rw [two_pow_mul b 2, two_pow_mul b 6, two_pow_mul b 3, hxb]
  field_simp

theorem final_error {S T n b p γ : ℕ} (hS : S ≤ T) (hTb : T * b ≤ 10 * n) (hn : n ≤ 2 ^ b)
    (hp : 6 * b ≤ p) (hγ : γ + 13 ≤ b) (hb : 12 ≤ b) :
    (2 : ℝ) ^ (2 * b) * (S : ℝ) * ((2 : ℝ) ^ p)⁻¹ *
      ((2 : ℝ) ^ (γ + 8) * (T : ℝ) ^ 2 * (Nat.log 2 T : ℝ)) < 1 / 4 := by
  have hb5 : 5 ≤ b := by omega
  have h10 : 10 < b := by omega
  have hbR : (12:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb
  have hbpos : (0:ℝ) < (b:ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hS' : (S:ℝ) ≤ (T:ℝ) := by exact_mod_cast hS
  have hTb2 : T * b ≤ 10 * 2 ^ b := le_trans hTb (Nat.mul_le_mul_left 10 hn)
  have hTreal : (T:ℝ) ≤ 10 * (2:ℝ)^b / (b:ℝ) := by
    rw [le_div_iff₀ hbpos]
    exact_mod_cast hTb2
  have hTlt : T < 2^b := by
    have hlt : T * b < b * 2^b :=
      lt_of_le_of_lt hTb2 (Nat.mul_lt_mul_of_pos_right h10 (by positivity))
    rw [mul_comm T b] at hlt
    exact Nat.lt_of_mul_lt_mul_left hlt
  have hlog : Nat.log 2 T ≤ b := by
    rcases Nat.eq_zero_or_pos T with hT0 | hTp
    · rw [hT0]; simp
    · rw [← Nat.lt_succ_iff, Nat.log_lt_iff_lt_pow (by norm_num) (Nat.pos_iff_ne_zero.mp hTp)]
      calc T < 2^b := hTlt
        _ < 2^(b+1) := Nat.pow_lt_pow_succ (by norm_num)
  have hp' : (2:ℝ)^(6*b) ≤ (2:ℝ)^p := pow_le_pow_right₀ (by norm_num) hp
  have hinv : ((2:ℝ)^p)⁻¹ ≤ ((2:ℝ)^(6*b))⁻¹ := inv_anti₀ (by positivity) hp'
  have hgam : (2:ℝ)^(γ+8) ≤ (2:ℝ)^(b-5) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hlogR : (Nat.log 2 T : ℝ) ≤ (b:ℝ) := by exact_mod_cast hlog
  have hstep1 : (2:ℝ)^(2*b) * (S:ℝ) * ((2:ℝ)^p)⁻¹ * ((2:ℝ)^(γ+8) * (T:ℝ)^2 * (Nat.log 2 T:ℝ))
      ≤ (2:ℝ)^(2*b) * (T:ℝ) * ((2:ℝ)^(6*b))⁻¹ * ((2:ℝ)^(b-5) * (T:ℝ)^2 * (b:ℝ)) := by
    gcongr
  have hstep2 : (2:ℝ)^(2*b) * (T:ℝ) * ((2:ℝ)^(6*b))⁻¹ * ((2:ℝ)^(b-5) * (T:ℝ)^2 * (b:ℝ))
      ≤ 125/(4*(b:ℝ)^2) := by
    have hT3 : (T:ℝ)^3 ≤ (10 * (2:ℝ)^b / (b:ℝ))^3 := pow_le_pow_left₀ (by positivity) hTreal 3
    have hpowid := powid b hb5
    calc (2:ℝ)^(2*b) * (T:ℝ) * ((2:ℝ)^(6*b))⁻¹ * ((2:ℝ)^(b-5) * (T:ℝ)^2 * (b:ℝ))
        = ((2:ℝ)^(2*b) * ((2:ℝ)^(6*b))⁻¹ * (2:ℝ)^(b-5)) * (T:ℝ)^3 * (b:ℝ) := by ring
      _ ≤ ((2:ℝ)^(2*b) * ((2:ℝ)^(6*b))⁻¹ * (2:ℝ)^(b-5)) * (10*(2:ℝ)^b/(b:ℝ))^3 * (b:ℝ) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT3 (by positivity))
            (by positivity)
      _ = 125/(4*(b:ℝ)^2) := by
          have hp3 : (10*(2:ℝ)^b/(b:ℝ))^3 = 1000 * (2:ℝ)^(3*b) / (b:ℝ)^3 := by
            rw [div_pow, mul_pow, ← two_pow_mul b 3]; norm_num
          rw [hp3]
          rw [show (2:ℝ)^(2*b) * ((2:ℝ)^(6*b))⁻¹ * (2:ℝ)^(b-5)
                  * (1000 * (2:ℝ)^(3*b) / (b:ℝ)^3) * (b:ℝ)
                = ((2:ℝ)^(2*b) * ((2:ℝ)^(6*b))⁻¹ * (2:ℝ)^(b-5) * (2:ℝ)^(3*b))
                    * (1000/(b:ℝ)^3) * (b:ℝ) by ring]
          rw [hpowid]
          field_simp
          ring
  have hstep3 : (125:ℝ)/(4*(b:ℝ)^2) < 1/4 := by
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < 4*(b:ℝ)^2)]
    nlinarith [hbR]
  exact lt_of_le_of_lt (le_trans hstep1 hstep2) hstep3

end Work.Main.recover
