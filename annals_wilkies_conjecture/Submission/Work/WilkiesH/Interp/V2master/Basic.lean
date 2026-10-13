import Mathlib
import Submission.Work.WilkiesH.Interp.V2Params

set_option maxHeartbeats 4000000

namespace Work.WilkiesH.Interp.V2master

open Work.WilkiesH.Interp

/-- `rhoN μ g H` is the natural number whose `(μ+1)`-st power is `bV μ g H`. -/
noncomputable def rhoN (μ g H : ℕ) : ℕ :=
  (μ+2)^(40*(μ+1)) * (g+1)^(100*(μ+1)^2) * (lgNat H)^(100*(μ+1)^2)

/-- `bV μ g H = (rhoN μ g H)^(μ+1)`. -/
lemma bV_eq_rhoN (μ g H : ℕ) : bV μ g H = rhoN μ g H ^ (μ+1) := by
  have h1 : (40*(μ+1))*(μ+1) = 40*(μ+1)^2 := by ring
  have h2 : (100*(μ+1)^2)*(μ+1) = 100*(μ+1)^3 := by ring
  simp only [bV, EE, AA, BB, rhoN]
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, h1, h2]

lemma one_le_rhoN (μ g H : ℕ) : 1 ≤ rhoN μ g H := by
  simp only [rhoN]
  have h1 : 1 ≤ (μ+2)^(40*(μ+1)) := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ (g+1)^(100*(μ+1)^2) := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ (lgNat H)^(100*(μ+1)^2) := Nat.one_le_pow _ _ (lgNat_pos H)
  calc 1 = 1*1*1 := by ring
    _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3

lemma log_KK_gt_one (μ : ℕ) : 1 < Real.log ((KK μ : ℕ) : ℝ) := by
  have h4nat : 4 ≤ KK μ := by simp [KK]
  have h4 : (4:ℝ) ≤ ((KK μ : ℕ) : ℝ) := by exact_mod_cast h4nat
  have hlog4 : Real.log (4:ℝ) = 2 * Real.log 2 := by
    have h : (4:ℝ) = 2^2 := by norm_num
    rw [h, Real.log_pow]; norm_num
  have hmono : Real.log (4:ℝ) ≤ Real.log ((KK μ : ℕ) : ℝ) := Real.log_le_log (by norm_num) h4
  linarith [Real.log_two_gt_d9, hmono, hlog4]

end Work.WilkiesH.Interp.V2master
