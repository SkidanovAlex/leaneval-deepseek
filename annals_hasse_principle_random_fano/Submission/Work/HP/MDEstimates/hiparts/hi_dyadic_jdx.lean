import Mathlib
import Submission.Work.HP.MDEstimates.hiparts.HiCellDefs

/-!
# The `λ₁`-cutoff `2^{⌊logb 2 l⌋}` sandwiches `l` and stays inside the index range

`hiM (hiJdx l) = 2^{⌊logb 2 l⌋}` is the dyadic cutoff attached to a `λ₁`-value `l ≥ 1`:
it satisfies `hiM (hiJdx l) ≤ l < 2 * hiM (hiJdx l)`, so the intervals
`[2^j, 2^{j+1})` tile `[1, ∞)`, and since `l ≤ A` its index does not exceed
`hiJ A = ⌈logb 2 A⌉₊` (the largest index occurring in the cell decomposition).
-/

namespace Work.HP.MDEstimates.hiparts

theorem hi_dyadic_jdx (A l : ℝ) (hA : 1 ≤ A) (hl0 : 1 ≤ l) (hlA : l ≤ A) :
    hiM (hiJdx l) ≤ l ∧ l < 2 * hiM (hiJdx l) ∧ hiJdx l ≤ hiJ A := by
  have hl : 0 < l := lt_of_lt_of_le one_pos hl0
  have h2 : (1 : ℝ) < 2 := by norm_num
  -- `logb 2 l ≥ 0` because `l ≥ 1`
  have hlog : 0 ≤ Real.logb 2 l := by
    have h := Real.logb_le_logb_of_le h2 zero_lt_one hl0
    rwa [Real.logb_one] at h
  -- `⌊logb 2 l⌋ ≤ logb 2 l`
  have hfloor : ((hiJdx l : ℕ) : ℝ) ≤ Real.logb 2 l := by
    simpa [hiJdx] using Nat.floor_le hlog
  -- `logb 2 l < ⌊logb 2 l⌋ + 1`
  have hceil : Real.logb 2 l < ((hiJdx l : ℕ) : ℝ) + 1 := by
    simpa [hiJdx] using Nat.lt_floor_add_one (Real.logb 2 l)
  refine ⟨?_, ?_, ?_⟩
  · have h := (Real.rpow_le_rpow_left_iff h2).mpr hfloor
    rw [Real.rpow_logb (by norm_num) (by norm_num) hl] at h
    simpa [hiM, Real.rpow_natCast] using h
  · have h := (Real.rpow_lt_rpow_left_iff h2).mpr hceil
    rw [Real.rpow_logb (by norm_num) (by norm_num) hl] at h
    have hrw : (2 : ℝ) ^ (((hiJdx l : ℕ) : ℝ) + 1) = 2 * hiM (hiJdx l) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_one, Real.rpow_natCast, hiM]
      ring
    rwa [hrw] at h
  · have h := Real.logb_le_logb_of_le h2 hl hlA
    exact le_trans (Nat.floor_mono h) (Nat.floor_le_ceil _)

end Work.HP.MDEstimates.hiparts
