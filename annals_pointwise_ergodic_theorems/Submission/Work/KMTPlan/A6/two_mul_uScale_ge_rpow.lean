import Mathlib
import Submission.Work.KMTPlan.A6.LowSmallSymDefs

namespace Work.KMTPlan.A6

/-- The number of available scales `uScale ρ L = ⌊2^{2ρL}⌋` is comparable to `2^{2ρL}` from
below: `2^{2ρL} ≤ 2 uScale ρ L` for `ρ ≥ 0`.  Elementary: `⌊x⌋ ≥ x - 1 ≥ x/2` when `x ≥ 2`,
and `⌊x⌋ ≥ 1 > x/2` when `1 ≤ x < 2` (here `x = 2^{2ρL} ≥ 1`). -/
theorem two_mul_uScale_ge_rpow (ρ : ℝ) (hρ : 0 ≤ ρ) (L : ℕ) :
    (2 : ℝ) ^ (2 * ρ * (L : ℝ)) ≤ 2 * (Work.KMTAreas.A7.uScale ρ L : ℝ) := by
  set x : ℝ := (2 : ℝ) ^ (2 * ρ * (L : ℝ)) with hx
  have hx1 : 1 ≤ x := by
    rw [hx]
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have hfl : (1 : ℤ) ≤ ⌊x⌋ := by
    rw [Int.le_floor]
    push_cast
    exact hx1
  have hfl0 : (0 : ℤ) ≤ ⌊x⌋ := le_trans (by norm_num) hfl
  have hcast : (Work.KMTAreas.A7.uScale ρ L : ℝ) = (⌊x⌋ : ℝ) := by
    rw [Work.KMTAreas.A7.uScale, Work.Analysis.EndVar.scaleCount, ← hx]
    simp only [Nat.cast_one, one_mul]
    exact_mod_cast Int.toNat_of_nonneg hfl0
  have hkey : x ≤ 2 * (⌊x⌋ : ℝ) := by
    by_cases h2 : (2 : ℝ) ≤ x
    · have h : x - 1 < (⌊x⌋ : ℝ) := by
        have := Int.lt_floor_add_one x
        linarith
      linarith
    · have h : (1 : ℝ) ≤ (⌊x⌋ : ℝ) := by exact_mod_cast hfl
      linarith
  rw [hx, hcast]
  exact hkey

end Work.KMTPlan.A6
