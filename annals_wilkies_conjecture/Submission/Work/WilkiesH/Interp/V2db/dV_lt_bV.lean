import Mathlib
import Submission.Work.WilkiesH.Interp.V2Params

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.WilkiesH.Interp.V2db

open Work.WilkiesH.Interp

/-- Real-analytic step of the estimate.

If the integer inequality `16^(μ+1) · (μ+1)! · (8g+9) < b` holds (and `b ≥ 2`), then the
right-hand side of the `dV_upper` bound for `dV μ g b` is strictly smaller than `b`:
`8 · ((μ+1)!(8g+9))^(1/(μ+1)) · (b+2)^(μ/(μ+1)) < b`.

Indeed, `(b+2)^(μ/(μ+1)) ≤ 2 b^(μ/(μ+1))`, so the left side is `≤ 16 · C · b^(μ/(μ+1))`
with `C = ((μ+1)!(8g+9))^(1/(μ+1))`, and `16 · C · b^(μ/(μ+1)) < b` is equivalent (raising
to the power `μ+1`) to `16^(μ+1)(μ+1)!(8g+9) < b`. -/
lemma rpow_bound (μ g b : ℕ) (hb2 : 2 ≤ b)
    (hN : 16 ^ (μ + 1) * (μ + 1).factorial * (8 * g + 9) < b) :
    8 * ((((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9)) ^ (1 / ((μ : ℝ) + 1)) *
      ((b : ℝ) + 2) ^ ((μ : ℝ) / ((μ : ℝ) + 1)) < (b : ℝ) := by
  set p : ℝ := (μ : ℝ) + 1 with hpdef
  set D : ℝ := (((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9) with hDdef
  have hp : 0 < p := by rw [hpdef]; positivity
  have hpne : p ≠ 0 := ne_of_gt hp
  have hDnn : 0 ≤ D := by rw [hDdef]; positivity
  have hbr2 : (2:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb2
  have hbrpos : 0 < (b:ℝ) := by linarith
  have hmup_nonneg : 0 ≤ (μ:ℝ)/p := by positivity
  have hmup_le_one : (μ:ℝ)/p ≤ 1 := by
    rw [div_le_one hp]; rw [hpdef]; linarith
  -- Step 1: `(b+2)^(μ/(μ+1)) ≤ 2 b^(μ/(μ+1))`.
  have hbase : ((b:ℝ) + 2) ^ ((μ:ℝ)/p) ≤ 2 * (b:ℝ) ^ ((μ:ℝ)/p) := by
    have hle : (b:ℝ) + 2 ≤ 2 * (b:ℝ) := by linarith
    have h1 : ((b:ℝ)+2) ^ ((μ:ℝ)/p) ≤ (2*(b:ℝ)) ^ ((μ:ℝ)/p) :=
      Real.rpow_le_rpow (by linarith) hle hmup_nonneg
    rw [Real.mul_rpow (by norm_num) (le_of_lt hbrpos)] at h1
    have h2 : (2:ℝ) ^ ((μ:ℝ)/p) ≤ 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hmup_le_one
      rwa [Real.rpow_one] at h
    calc ((b:ℝ)+2) ^ ((μ:ℝ)/p) ≤ 2 ^ ((μ:ℝ)/p) * (b:ℝ)^((μ:ℝ)/p) := h1
      _ ≤ 2 * (b:ℝ)^((μ:ℝ)/p) :=
          mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (le_of_lt hbrpos) _)
  -- Step 2: `16 · C · b^(μ/(μ+1)) < b`.
  have h16p : ((16:ℝ)) ^ p = ((16 ^ (μ+1) : ℕ) : ℝ) := by
    rw [hpdef, show (μ:ℝ)+1 = ((μ+1:ℕ):ℝ) by push_cast; ring, Real.rpow_natCast]
    exact (Nat.cast_pow (α := ℝ) 16 (μ+1)).symm
  have hDp : (D ^ (1/p)) ^ p = D := by
    rw [← Real.rpow_mul hDnn]
    have : 1/p * p = 1 := by rw [one_div, inv_mul_cancel₀ hpne]
    rw [this, Real.rpow_one]
  have hbr1p : ((b:ℝ)^(1/p)) ^ p = (b:ℝ) := by
    rw [← Real.rpow_mul (le_of_lt hbrpos)]
    have : 1/p * p = 1 := by rw [one_div, inv_mul_cancel₀ hpne]
    rw [this, Real.rpow_one]
  have h16D : (16 * D ^ (1/p)) ^ p = ((16 ^ (μ+1) * (μ+1).factorial * (8*g+9) : ℕ) : ℝ) := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hDnn _), h16p, hDp, hDdef]
    push_cast
    ring
  have hlt : 16 * D ^ (1/p) < (b:ℝ)^(1/p) := by
    rw [← Real.rpow_lt_rpow_iff (x := 16 * D^(1/p)) (y := (b:ℝ)^(1/p)) (z := p)
        (by positivity) (Real.rpow_nonneg (le_of_lt hbrpos) _) hp]
    rw [h16D, hbr1p]
    exact_mod_cast hN
  have hkey : 16 * D ^ (1/p) * (b:ℝ)^((μ:ℝ)/p) < (b:ℝ) := by
    have hbr_mup_pos : 0 < (b:ℝ)^((μ:ℝ)/p) := Real.rpow_pos_of_pos hbrpos _
    have h1 : 16 * D ^ (1/p) * (b:ℝ)^((μ:ℝ)/p) < (b:ℝ)^(1/p) * (b:ℝ)^((μ:ℝ)/p) :=
      mul_lt_mul_of_pos_right hlt hbr_mup_pos
    rw [← Real.rpow_add hbrpos] at h1
    have hsum : 1/p + (μ:ℝ)/p = 1 := by
      have : ((μ:ℝ)+1) ≠ 0 := by positivity
      rw [← add_div, hpdef]; field_simp; ring
    rw [hsum, Real.rpow_one] at h1
    exact h1
  calc 8 * D ^ (1/p) * ((b:ℝ)+2)^((μ:ℝ)/p)
      ≤ 8 * D ^ (1/p) * (2 * (b:ℝ)^((μ:ℝ)/p)) :=
          mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = 16 * D ^ (1/p) * (b:ℝ)^((μ:ℝ)/p) := by ring
    _ < (b:ℝ) := hkey

/-- `16^(μ+1) · (μ+1)! · 9 < EE μ = (μ+2)^(40(μ+1)^2)`. -/
lemma T_lt_EE (μ : ℕ) : 16 ^ (μ + 1) * (μ + 1).factorial * 9 < EE μ := by
  rcases Nat.eq_zero_or_pos μ with h | h
  · subst h; norm_num [EE]
  · have h1 : 16 ^ (μ+1) ≤ (μ+2)^(4*(μ+1)) := by
      calc 16 ^ (μ+1) = (2^4)^(μ+1) := by norm_num
        _ = 2^(4*(μ+1)) := by rw [← pow_mul]
        _ ≤ (μ+2)^(4*(μ+1)) := Nat.pow_le_pow_left (by omega) _
    have h2 : (μ+1).factorial ≤ (μ+2)^(μ+1) := by
      calc (μ+1).factorial ≤ (μ+1)^(μ+1) := Nat.factorial_le_pow _
        _ ≤ (μ+2)^(μ+1) := Nat.pow_le_pow_left (by omega) _
    have h3 : 9 ≤ (μ+2)^2 := by
      calc (9:ℕ) = 3^2 := by norm_num
        _ ≤ (μ+2)^2 := Nat.pow_le_pow_left (by omega) 2
    have hb : (1:ℕ) < μ + 2 := by omega
    calc 16 ^ (μ+1) * (μ+1).factorial * 9
        ≤ (μ+2)^(4*(μ+1)) * (μ+2)^(μ+1) * (μ+2)^2 :=
            Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
      _ = (μ+2)^(4*(μ+1) + (μ+1) + 2) := by rw [← pow_add, ← pow_add]
      _ < (μ+2)^(40*(μ+1)^2) := by
            apply Nat.pow_lt_pow_right hb
            nlinarith
      _ = EE μ := by rw [EE]

/-- `16^(μ+1) · (μ+1)! · (8g+9) < bV μ g H`. -/
lemma N_lt_bV (μ g H : ℕ) :
    16 ^ (μ + 1) * (μ + 1).factorial * (8 * g + 9) < bV μ g H := by
  have hT : 16 ^ (μ + 1) * (μ + 1).factorial * 9 < EE μ := T_lt_EE μ
  have hAA : 1 ≤ AA μ := by
    rw [AA]
    exact Nat.succ_le_of_lt (Nat.mul_pos (by norm_num) (Nat.pow_pos (by omega)))
  have h89 : 8 * g + 9 ≤ 9 * (g+1)^(AA μ) := by
    have hp1 : (g+1)^1 ≤ (g+1)^(AA μ) := Nat.pow_le_pow_right (by omega) hAA
    calc 8*g+9 ≤ 9*(g+1)^1 := by simp only [pow_one]; omega
      _ ≤ 9*(g+1)^(AA μ) := Nat.mul_le_mul_left 9 hp1
  have hl : 1 ≤ (lgNat H)^(BB μ) := Nat.one_le_pow _ _ (lgNat_pos H)
  calc 16^(μ+1)*(μ+1).factorial*(8*g+9)
      ≤ 16^(μ+1)*(μ+1).factorial*(9*(g+1)^(AA μ)) := Nat.mul_le_mul_left _ h89
    _ = (16^(μ+1)*(μ+1).factorial*9) * (g+1)^(AA μ) := by ring
    _ < EE μ * (g+1)^(AA μ) :=
        Nat.mul_lt_mul_of_pos_right hT (Nat.pow_pos (by omega))
    _ ≤ EE μ * (g+1)^(AA μ) * (lgNat H)^(BB μ) :=
        le_mul_of_one_le_right (Nat.zero_le _) hl
    _ = bV μ g H := rfl

-- `d = dV μ g (bV μ g H)` is much smaller than `b = bV μ g H`: `d + 1 ≤ b`.
-- From `hd`, `d ≤ 8 ((μ+1)!(8g+9))^(1/(μ+1)) (b+2)^(μ/(μ+1))`, and
-- `b = EE μ (g+1)^A Lg^B ≥ EE μ = (μ+2)^(40(μ+1)^2)` with `A = B = 100(μ+1)^3`, so that
-- `b^(1/(μ+1)) ≥ (μ+2)^(40(μ+1))` dominates `8 ((μ+1)!(8g+9))^(1/(μ+1)) 2`.
theorem dV_lt_bV (μ g H : ℕ) (hH : 1 ≤ H)
    (hd : ((Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H) : ℕ) : ℝ) ≤
      8 * ((((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9)) ^ (1 / ((μ : ℝ) + 1)) *
        (((Work.WilkiesH.Interp.bV μ g H : ℕ) : ℝ) + 2) ^ ((μ : ℝ) / ((μ : ℝ) + 1))) :
    Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H) + 1 ≤
      Work.WilkiesH.Interp.bV μ g H := by
  have hb2 : 2 ≤ Work.WilkiesH.Interp.bV μ g H := by
    have hEE : 2 ≤ EE μ := by
      have h1 : 1 ≤ 40 * (μ + 1) ^ 2 := by
        have : 0 < 40 * (μ + 1) ^ 2 := Nat.mul_pos (by norm_num) (Nat.pow_pos (by omega))
        omega
      rw [EE]
      calc (2:ℕ) = 2^1 := by norm_num
        _ ≤ 2^(40*(μ+1)^2) := Nat.pow_le_pow_right (by norm_num) h1
        _ ≤ (μ+2)^(40*(μ+1)^2) := Nat.pow_le_pow_left (by omega) _
    have hEEle : EE μ ≤ bV μ g H := by
      rw [bV]
      have h1 : 1 ≤ (g+1)^(AA μ) := Nat.one_le_pow _ _ (by omega)
      have h2 : 1 ≤ (lgNat H)^(BB μ) := Nat.one_le_pow _ _ (lgNat_pos H)
      calc EE μ = EE μ * 1 * 1 := by ring
        _ ≤ EE μ * (g+1)^(AA μ) * (lgNat H)^(BB μ) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
    exact le_trans hEE hEEle
  have hN := N_lt_bV μ g H
  have hbound := rpow_bound μ g (Work.WilkiesH.Interp.bV μ g H) hb2 hN
  have hltR : ((Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H) : ℕ) : ℝ) <
      ((Work.WilkiesH.Interp.bV μ g H : ℕ) : ℝ) := lt_of_le_of_lt hd hbound
  have hltN : Work.WilkiesH.Interp.dV μ g (Work.WilkiesH.Interp.bV μ g H) <
      Work.WilkiesH.Interp.bV μ g H := Nat.cast_lt.mp hltR
  omega

end Work.WilkiesH.Interp.V2db
