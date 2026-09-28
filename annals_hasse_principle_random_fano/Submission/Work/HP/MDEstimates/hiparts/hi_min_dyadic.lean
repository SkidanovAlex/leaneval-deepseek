import Mathlib
import Submission.Work.HP.MDEstimates.hiparts.HiCellDefs

namespace Work.HP.MDEstimates.hiparts

/-- The dyadic `𝔡₃`-cutoff of the cell of `d` is at most `d`: the cell bottom
`hiDelta A (hiIdx A d) = A^{1/20} · 2^{⌊logb 2 (d/A^{1/20})⌋₊}` never exceeds `d`. -/
lemma hiDelta_hiIdx_le (A d : ℝ) (hA : 0 < A) (hd : A ^ ((1 : ℝ) / 20) ≤ d) :
    hiDelta A (hiIdx A d) ≤ d := by
  have hA20 : 0 < A ^ ((1 : ℝ) / 20) := Real.rpow_pos_of_pos hA _
  set t : ℝ := d / A ^ ((1 : ℝ) / 20) with ht_def
  have ht1 : 1 ≤ t := by
    rw [ht_def]; exact (one_le_div hA20).mpr hd
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht1
  have hlog : 0 ≤ Real.logb 2 t := Real.logb_nonneg one_lt_two ht1
  have hfloor : ((⌊Real.logb 2 t⌋₊ : ℕ) : ℝ) ≤ Real.logb 2 t := Nat.floor_le hlog
  have hpow : (2 : ℝ) ^ (⌊Real.logb 2 t⌋₊) ≤ (2 : ℝ) ^ Real.logb 2 t := by
    rw [← Real.rpow_natCast]
    exact (Real.rpow_le_rpow_left_iff one_lt_two).mpr hfloor
  have hlogb : (2 : ℝ) ^ Real.logb 2 t = t := Real.rpow_logb (by norm_num) (by norm_num) ht0
  have hpowle : (2 : ℝ) ^ (⌊Real.logb 2 t⌋₊) ≤ t := hpow.trans_eq hlogb
  have hidx : hiIdx A d = ⌊Real.logb 2 t⌋₊ := by rw [hiIdx, ← ht_def]
  have hAt : A ^ ((1 : ℝ) / 20) * t = d := by
    rw [ht_def]; field_simp
  rw [hiDelta, hidx]
  calc A ^ ((1 : ℝ) / 20) * (2 : ℝ) ^ (⌊Real.logb 2 t⌋₊)
      ≤ A ^ ((1 : ℝ) / 20) * t := mul_le_mul_of_nonneg_left hpowle hA20.le
    _ = d := hAt

/-- The dyadic `λ₁`-cutoff of the cell of `l` is at most `l`: `hiM (hiJdx l) = 2^{⌊logb 2 l⌋₊} ≤ l`
for `l ≥ 1`. -/
lemma hiM_hiJdx_le (l : ℝ) (hl : 1 ≤ l) : hiM (hiJdx l) ≤ l := by
  have hl0 : 0 < l := lt_of_lt_of_le one_pos hl
  have hlog : 0 ≤ Real.logb 2 l := Real.logb_nonneg one_lt_two hl
  have hfloor : ((⌊Real.logb 2 l⌋₊ : ℕ) : ℝ) ≤ Real.logb 2 l := Nat.floor_le hlog
  have hpow : (2 : ℝ) ^ (⌊Real.logb 2 l⌋₊) ≤ (2 : ℝ) ^ Real.logb 2 l := by
    rw [← Real.rpow_natCast]
    exact (Real.rpow_le_rpow_left_iff one_lt_two).mpr hfloor
  have hlogb : (2 : ℝ) ^ Real.logb 2 l = l := Real.rpow_logb (by norm_num) (by norm_num) hl0
  simpa [hiM, hiJdx] using hpow.trans_eq hlogb

/-- The `R0`-minimum at the dyadic cell cutoffs `(hiDelta A (hiIdx A d), hiM (hiJdx l))` is at
least the minimum at `(d, l)`, since these cutoffs are dominated by `d` and `l` and `hiMin` is
antitone. -/
theorem hi_min_dyadic (A B d l : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hd : A ^ ((1 : ℝ) / 20) ≤ d) (hl : 1 ≤ l) :
    hiMin A B d l ≤ hiMin A B (hiDelta A (hiIdx A d)) (hiM (hiJdx l)) := by
  have hdelta_le : hiDelta A (hiIdx A d) ≤ d := hiDelta_hiIdx_le A d hA hd
  have hM_le : hiM (hiJdx l) ≤ l := hiM_hiJdx_le l hl
  have hdelta_pos : 0 < hiDelta A (hiIdx A d) := by
    rw [hiDelta]; positivity
  have hM_pos : 0 < hiM (hiJdx l) := by
    rw [hiM]; positivity
  exact hiMin_anti A B (hiDelta A (hiIdx A d)) (hiM (hiJdx l)) d l hA.le hB.le
    hdelta_pos hdelta_le hM_pos hM_le

end Work.HP.MDEstimates.hiparts
