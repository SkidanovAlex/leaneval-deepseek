import Mathlib
import Submission.Work.Analysis.EndVar.Defs

namespace Work.KMTAreas.A7

/-- With `ρ ≤ 1/(8C₀)` and `M ≤ C₀ · Nat.log 2 (R+2)`, the scale count `scaleCount 1 ρ M = ⌊2^{2ρM}⌋` is at most `(R+2)^{1/4}`.  Route: `2ρM ≤ 2ρC₀·L ≤ L/4 ≤ (1/4) log₂(R+2)` with `L = Nat.log 2 (R+2) ≤ Real.logb 2 (R+2)`, so `⌊2^{2ρM}⌋ ≤ 2^{2ρM} ≤ 2^{(1/4)log₂(R+2)} = (R+2)^{1/4}`. -/
theorem scaleCount_le_rpow (ρ : ℝ) (C₀ M R : ℕ) (hC₀ : 1 ≤ C₀) (hρ : 0 < ρ)
    (hρ₀ : ρ ≤ 1 / (8 * (C₀ : ℝ))) (hMR : M ≤ C₀ * Nat.log 2 (R + 2)) :
    (Work.Analysis.EndVar.scaleCount 1 ρ M : ℝ) ≤ ((R : ℝ) + 2) ^ ((1 : ℝ) / 4) := by
  set L : ℕ := Nat.log 2 (R + 2) with hL
  have hC₀pos : (0 : ℝ) < (C₀ : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hC₀)
  have hxpos : (0 : ℝ) < (2 : ℝ) ^ (2 * ρ * (M : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  -- the floor is dominated by its argument
  have hsc : (Work.Analysis.EndVar.scaleCount 1 ρ M : ℝ) ≤ (2 : ℝ) ^ (2 * ρ * (M : ℝ)) := by
    unfold Work.Analysis.EndVar.scaleCount
    simpa only [Int.floor_toNat, Nat.cast_one, one_mul]
      using Nat.floor_le (show (0 : ℝ) ≤ 1 * 2 ^ (2 * ρ * (M : ℝ)) by positivity)
  -- `2ρC₀ ≤ 1/4`
  have hρC : 2 * ρ * (C₀ : ℝ) ≤ 1 / 4 := by
    have h8 : (0 : ℝ) < 8 * (C₀ : ℝ) := by positivity
    have h1 : ρ * (8 * (C₀ : ℝ)) ≤ 1 := (le_div_iff₀ h8).mp hρ₀
    nlinarith
  -- `M ≤ C₀ L` in `ℝ`
  have hML : (M : ℝ) ≤ (C₀ : ℝ) * (L : ℝ) := by
    exact_mod_cast hMR
  -- the exponent bound
  have hexp : 2 * ρ * (M : ℝ) ≤ (1 / 4) * (L : ℝ) := by
    have h1 : 2 * ρ * (M : ℝ) ≤ 2 * ρ * ((C₀ : ℝ) * (L : ℝ)) := by
      apply mul_le_mul_of_nonneg_left hML
      nlinarith
    have h2 : 2 * ρ * ((C₀ : ℝ) * (L : ℝ)) = (2 * ρ * (C₀ : ℝ)) * (L : ℝ) := by ring
    have h3 : (2 * ρ * (C₀ : ℝ)) * (L : ℝ) ≤ (1 / 4) * (L : ℝ) :=
      mul_le_mul_of_nonneg_right hρC (Nat.cast_nonneg L)
    linarith
  -- `L ≤ log₂ (R+2)`
  have hLlogb : ((L : ℕ) : ℝ) ≤ Real.logb 2 ((R : ℝ) + 2) := by
    rw [hL]
    simpa using Real.natLog_le_logb (R + 2) 2
  have hRpos : 0 < ((R : ℝ) + 2) := by positivity
  calc (Work.Analysis.EndVar.scaleCount 1 ρ M : ℝ)
      ≤ (2 : ℝ) ^ (2 * ρ * (M : ℝ)) := hsc
    _ ≤ (2 : ℝ) ^ ((1 / 4) * (L : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ ≤ (2 : ℝ) ^ ((1 / 4) * Real.logb 2 ((R : ℝ) + 2)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [hLlogb])
    _ = (((R : ℝ) + 2) ^ ((1 : ℝ) / 4)) := by
        rw [mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        rw [Real.rpow_logb (by norm_num) (by norm_num) hRpos]

end Work.KMTAreas.A7
