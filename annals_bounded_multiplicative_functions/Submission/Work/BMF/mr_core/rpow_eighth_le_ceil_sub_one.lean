import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_core

/-- Elementary inequality: for `t ≥ 16` one has `t ≤ t^8 - 1`.
Indeed `t^8 = t·t^7 ≥ 2t`, and `2t - 1 ≥ t` since `t ≥ 1`. -/
private lemma self_le_pow_eight_sub_one (t : ℝ) (ht : 16 ≤ t) : t ≤ t ^ 8 - 1 := by
  have h2 : (2 : ℝ) ≤ t ^ 7 := by
    calc (2 : ℝ) ≤ (16 : ℝ) ^ 7 := by norm_num
      _ ≤ t ^ 7 := pow_le_pow_left₀ (by norm_num) ht 7
  have h3 : (2 : ℝ) * t ≤ t ^ 8 := by
    have hsplit : t ^ 8 = t ^ 7 * t := by ring
    nlinarith only [hsplit, h2, ht]
  nlinarith only [h3, ht]

theorem rpow_eighth_le_ceil_sub_one (Y : ℝ) (hY : (16 : ℝ) ^ 8 ≤ Y) :
    Y ^ (1 / 8 : ℝ) ≤ ((⌈Y⌉₊ - 1 : ℕ) : ℝ) := by
  have hYpos : (0 : ℝ) < Y := by
    have : (0 : ℝ) < (16 : ℝ) ^ 8 := by norm_num
    linarith
  -- switch to the real exponent `8`
  have hY' : ((16 : ℝ) ^ (8 : ℝ)) ≤ Y := by
    have h : ((16 : ℝ) ^ (8 : ℝ)) = (16 : ℝ) ^ 8 := by norm_num
    rw [h]; exact hY
  have h16eq : ((16 : ℝ) ^ (8 : ℝ)) ^ (1 / 8 : ℝ) = 16 := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (16 : ℝ))]
    norm_num
  -- `16 ≤ Y^{1/8}`
  have ht_ge : (16 : ℝ) ≤ Y ^ (1 / 8 : ℝ) := by
    have h := Real.rpow_le_rpow (x := (16 : ℝ) ^ (8 : ℝ)) (y := Y) (z := (1 / 8 : ℝ))
      (by positivity) hY' (by norm_num)
    rwa [h16eq] at h
  -- `(Y^{1/8})^8 = Y`
  have htpow : (Y ^ (1 / 8 : ℝ)) ^ (8 : ℝ) = Y := by
    rw [← Real.rpow_mul (le_of_lt hYpos) (1 / 8) 8]
    norm_num
  have ht8 : (Y ^ (1 / 8 : ℝ)) ^ 8 = Y := by
    have h : (Y ^ (1 / 8 : ℝ)) ^ (8 : ℝ) = (Y ^ (1 / 8 : ℝ)) ^ 8 := by norm_num
    rw [← h]; exact htpow
  have key : Y ^ (1 / 8 : ℝ) ≤ (Y ^ (1 / 8 : ℝ)) ^ 8 - 1 :=
    self_le_pow_eight_sub_one (Y ^ (1 / 8 : ℝ)) ht_ge
  have hYsub : Y ^ (1 / 8 : ℝ) ≤ Y - 1 := by
    rw [ht8] at key; exact key
  -- `Y - 1 ≤ ⌈Y⌉₊ - 1`
  have h1 : 1 ≤ ⌈Y⌉₊ := Nat.one_le_ceil_iff.mpr hYpos
  have hceil : Y ≤ ((⌈Y⌉₊ : ℕ) : ℝ) := Nat.le_ceil Y
  have hcast : ((⌈Y⌉₊ - 1 : ℕ) : ℝ) = ((⌈Y⌉₊ : ℕ) : ℝ) - 1 := by
    rw [Nat.cast_sub h1]; norm_num
  have hfin : Y ^ (1 / 8 : ℝ) ≤ ((⌈Y⌉₊ : ℕ) : ℝ) - 1 := by
    linarith only [hYsub, hceil]
  rw [hcast]
  exact hfin

end Work.BMF.mr_core
