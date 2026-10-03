import Mathlib
import Submission.Work.KMTAreas.A7.Large.Defs

namespace Work.KMTPlan.A6

/-- The scale count `u = ⌊2^{2ρL}⌋` can be made small by choosing the separation constants: if
`ρ C₀ ≤ 1/4` and the height `m` is bounded by `L ≤ C₀ q`, then `uScale ρ m ≤ 2^{q/2}`.

Indeed `2ρm ≤ 2ρL ≤ 2ρC₀ q ≤ q/2`, and `⌊2^{2ρm}⌋ ≤ 2^{2ρm} ≤ 2^{q/2}`. -/
theorem uScaleHalfPow (ρ : ℝ) (hρ : 0 < ρ) (C₀ q L m : ℕ)
    (hρC : ρ * (C₀ : ℝ) ≤ 1 / 4) (hmL : m ≤ L) (hLq : L ≤ C₀ * q) :
    (Work.KMTAreas.A7.uScale ρ m : ℝ) ≤ (2 : ℝ) ^ ((q : ℝ) / 2) := by
  have hmL' : (m : ℝ) ≤ (L : ℝ) := by exact_mod_cast hmL
  have hLq' : (L : ℝ) ≤ (C₀ : ℝ) * (q : ℝ) := by exact_mod_cast hLq
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hexp : 2 * ρ * (m : ℝ) ≤ (q : ℝ) / 2 := by
    have h1 : 2 * ρ * (m : ℝ) ≤ 2 * ρ * (L : ℝ) := by nlinarith
    have h2 : 2 * ρ * (L : ℝ) ≤ 2 * ρ * ((C₀ : ℝ) * (q : ℝ)) := by nlinarith
    have h3 : 2 * ρ * ((C₀ : ℝ) * (q : ℝ)) ≤ (q : ℝ) / 2 := by
      have h4 : 2 * (ρ * (C₀ : ℝ)) * (q : ℝ) ≤ 2 * (1 / 4) * (q : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith [hρC]) hq0
      linarith
    linarith
  calc (Work.KMTAreas.A7.uScale ρ m : ℝ)
      = ((Nat.floor ((2 : ℝ) ^ (2 * ρ * (m : ℝ))) : ℕ) : ℝ) := by
        simp only [Work.KMTAreas.A7.uScale, Work.Analysis.EndVar.scaleCount,
          Int.floor_toNat, Nat.cast_one, one_mul]
    _ ≤ (2 : ℝ) ^ (2 * ρ * (m : ℝ)) := Nat.floor_le (Real.rpow_nonneg (by norm_num) _)
    _ ≤ (2 : ℝ) ^ ((q : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

end Work.KMTPlan.A6
