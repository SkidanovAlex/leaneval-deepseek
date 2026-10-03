import Mathlib

namespace Work.FIArea2.Count

/-- Counting-factor bookkeeping for *FI* §9 (9.5): with `thr = √(ϑ Nr)`, `0 < ϑ ≤ 1`, `Nr ≥ 1`,
`0 ≤ R`, `2R+1 ≤ 8√Nr`, and a coordinate `s₂` off the axis-avoidance threshold
(`thr < |s₂|`), the count factor `1 + (s₁,s₂)·(2R+1)/|s₂|` of the linear-diophantine counting
bound is at most `9 ϑ^{-1/2}·(s₁,s₂)`:

`(2R+1)/|s₂| < 8√Nr/√(ϑNr) = 8ϑ^{-1/2}` since `|s₂| > thr = √ϑ·√Nr`, and the additive `1` is
absorbed because `√ϑ ≤ 1 ≤ (s₁,s₂)`. -/
theorem factor_le_nine (R s1 s2 : ℤ) (thr Nr ϑ : ℝ)
    (hϑ0 : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hNr : 1 ≤ Nr) (hR : 0 ≤ R)
    (hthr : thr = Real.sqrt (ϑ * Nr)) (hbox : 2 * (R : ℝ) + 1 ≤ 8 * Real.sqrt Nr)
    (hs2 : thr < |(s2 : ℝ)|) :
    1 + ((Nat.gcd s1.natAbs s2.natAbs : ℕ) : ℝ) * (((2 * R + 1).natAbs : ℕ) : ℝ)
          / ((s2.natAbs : ℕ) : ℝ)
      ≤ 9 * ϑ ^ (-(1 : ℝ) / 2) * ((Nat.gcd s1.natAbs s2.natAbs : ℕ) : ℝ) := by
  set g : ℕ := Nat.gcd s1.natAbs s2.natAbs with hg
  set D : ℕ := (2 * R + 1).natAbs with hD
  have hϑ0' : (0 : ℝ) ≤ ϑ := le_of_lt hϑ0
  have hNr0 : (0 : ℝ) < Nr := by linarith
  have hsqrtϑ_pos : 0 < Real.sqrt ϑ := Real.sqrt_pos_of_pos hϑ0
  have hsqrtϑ_le_one : Real.sqrt ϑ ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hϑ1
  -- the threshold is positive, hence so is `|s₂|`
  have hthr_pos : 0 < thr := by
    rw [hthr]; exact Real.sqrt_pos_of_pos (mul_pos hϑ0 hNr0)
  have hs2abs_pos : 0 < |(s2 : ℝ)| := lt_trans hthr_pos hs2
  have hs2_ne : s2 ≠ 0 := by
    intro h; rw [h] at hs2abs_pos; simp at hs2abs_pos
  have hs2nat_pos : 0 < s2.natAbs := Int.natAbs_pos.mpr hs2_ne
  -- `g = (s₁,s₂) ≥ 1`
  have hg_pos : 0 < g := by rw [hg]; exact Nat.gcd_pos_of_pos_right _ hs2nat_pos
  have hg_ge_one : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg_pos
  have hsqrtϑ_le_g : Real.sqrt ϑ ≤ (g : ℝ) := le_trans hsqrtϑ_le_one hg_ge_one
  -- `D = 2R+1` as a real, and the box hypothesis
  have hDcast : (D : ℝ) = 2 * (R : ℝ) + 1 := by
    rw [hD, Nat.cast_natAbs, Int.cast_abs]
    have h2R : (0 : ℤ) ≤ 2 * R + 1 := by omega
    rw [abs_of_nonneg]
    · push_cast; ring
    · exact_mod_cast h2R
  have hD_le : (D : ℝ) ≤ 8 * Real.sqrt Nr := by rw [hDcast]; exact hbox
  -- `√Nr = thr / √ϑ`
  have hthr_mul : thr = Real.sqrt ϑ * Real.sqrt Nr := by
    rw [hthr, Real.sqrt_mul hϑ0']
  have hsqrtNr_eq : Real.sqrt Nr = thr / Real.sqrt ϑ := by
    rw [hthr_mul]
    exact (mul_div_cancel_left₀ _ (ne_of_gt hsqrtϑ_pos)).symm
  have hD_le' : (D : ℝ) ≤ 8 * thr / Real.sqrt ϑ := by
    have h := hD_le
    rw [hsqrtNr_eq] at h
    calc (D : ℝ) ≤ 8 * (thr / Real.sqrt ϑ) := h
      _ = 8 * thr / Real.sqrt ϑ := by ring
  -- the quotient `D/|s₂|` is `< 8/√ϑ`
  have h8thr_pos : 0 < 8 * thr / Real.sqrt ϑ :=
    div_pos (by linarith [hthr_pos]) hsqrtϑ_pos
  have hquot1 : (D : ℝ) / |(s2 : ℝ)| ≤ (8 * thr / Real.sqrt ϑ) / |(s2 : ℝ)| :=
    div_le_div_of_nonneg_right hD_le' (le_of_lt hs2abs_pos)
  have hquot2 : (8 * thr / Real.sqrt ϑ) / |(s2 : ℝ)| < (8 * thr / Real.sqrt ϑ) / thr :=
    div_lt_div_of_pos_left h8thr_pos hthr_pos hs2
  have hquot3 : (8 * thr / Real.sqrt ϑ) / thr = 8 / Real.sqrt ϑ := by
    field_simp
  have hs2cast : ((s2.natAbs : ℕ) : ℝ) = |(s2 : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hDM : (D : ℝ) / ((s2.natAbs : ℕ) : ℝ) < 8 / Real.sqrt ϑ := by
    rw [hs2cast]
    exact lt_of_le_of_lt hquot1 (hquot2.trans_eq hquot3)
  -- multiply by `g ≥ 0`
  have hstep : (g : ℝ) * (D : ℝ) / ((s2.natAbs : ℕ) : ℝ) ≤ 8 * ((g : ℝ) / Real.sqrt ϑ) := by
    rw [mul_div_assoc]
    calc (g : ℝ) * ((D : ℝ) / ((s2.natAbs : ℕ) : ℝ))
        ≤ (g : ℝ) * (8 / Real.sqrt ϑ) :=
          mul_le_mul_of_nonneg_left (le_of_lt hDM) (by positivity)
      _ = 8 * ((g : ℝ) / Real.sqrt ϑ) := by ring
  -- the additive `1` is absorbed by `√ϑ ≤ g`
  have hgdiv : 1 ≤ (g : ℝ) / Real.sqrt ϑ := by
    rw [le_div_iff₀ hsqrtϑ_pos]
    simpa using hsqrtϑ_le_g
  have hfinal : 1 + 8 * ((g : ℝ) / Real.sqrt ϑ) ≤ 9 * ((g : ℝ) / Real.sqrt ϑ) := by
    linarith
  have hrpow : ϑ ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt ϑ := by
    rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring, Real.rpow_neg hϑ0',
      ← Real.sqrt_eq_rpow, one_div]
  calc 1 + (g : ℝ) * (D : ℝ) / ((s2.natAbs : ℕ) : ℝ)
      ≤ 1 + 8 * ((g : ℝ) / Real.sqrt ϑ) := by linarith
    _ ≤ 9 * ((g : ℝ) / Real.sqrt ϑ) := hfinal
    _ = 9 * ϑ ^ (-(1 : ℝ) / 2) * (g : ℝ) := by rw [hrpow]; ring

end Work.FIArea2.Count
