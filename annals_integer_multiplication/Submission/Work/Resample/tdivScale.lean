import Mathlib
import Submission.Work.Resample.auDefs
import Submission.Work.Fx.expStepErr

namespace Work.Resample

/-- Truncating `A` at precision `auPrec p - p` and then scaling by `2^{-p}` differs from `A/2^{auPrec p}`
by at most `2^{-p}`: the discarded remainder is `< 2^{auPrec p - p}`. -/
theorem tdivScale (p : ℕ) (A : ℤ) :
    |(((Int.tdiv A ((2 : ℤ) ^ (Work.Resample.auPrec p - p)) : ℤ)) : ℝ) / (2 : ℝ) ^ p
        - (A : ℝ) / (2 : ℝ) ^ Work.Resample.auPrec p| ≤ 1 / (2 : ℝ) ^ p := by
  set d : ℤ := (2 : ℤ) ^ (auPrec p - p) with hd
  set q : ℤ := Int.tdiv A d with hq
  set r : ℤ := Int.tmod A d with hr
  have hdpos : 0 < d := by rw [hd]; positivity
  have hpp : p ≤ auPrec p := by simp only [auPrec]; omega
  have hA : A = q * d + r := by
    rw [hq, hr, hd]
    exact (Int.tdiv_mul_add_tmod A _).symm
  have hdcast : ((d : ℤ) : ℝ) = (2 : ℝ) ^ (auPrec p - p) := by
    rw [hd]; push_cast; ring
  have hpow : (2 : ℝ) ^ auPrec p = (2 : ℝ) ^ (auPrec p - p) * (2 : ℝ) ^ p := by
    rw [← pow_add, Nat.sub_add_cancel hpp]
  have hkey : (q : ℝ) / (2 : ℝ) ^ p - (A : ℝ) / (2 : ℝ) ^ auPrec p
      = -((r : ℝ)) / ((2 : ℝ) ^ (auPrec p - p) * (2 : ℝ) ^ p) := by
    rw [hA, hpow]
    push_cast
    rw [hdcast]
    field_simp
    ring
  rw [hkey]
  rw [abs_div, abs_neg,
    abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ (auPrec p - p) * (2 : ℝ) ^ p)]
  have hrle : |((r : ℝ))| ≤ (2 : ℝ) ^ (auPrec p - p) := by
    have h1 : -d < r := by
      rw [hr]
      exact Int.lt_tmod_of_pos A (b := d) hdpos
    have h2 : r < d := by
      rw [hr]
      exact Int.tmod_lt_of_pos A hdpos
    have h3 : |((r : ℝ))| < (2 : ℝ) ^ (auPrec p - p) := by
      have h4 : |((r : ℝ))| < (d : ℝ) := by
        rw [abs_lt]
        exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
      rwa [hdcast] at h4
    exact le_of_lt h3
  calc |((r : ℝ))| / ((2 : ℝ) ^ (auPrec p - p) * (2 : ℝ) ^ p)
      ≤ (2 : ℝ) ^ (auPrec p - p)
          / ((2 : ℝ) ^ (auPrec p - p) * (2 : ℝ) ^ p) :=
        div_le_div_of_nonneg_right hrle (by positivity)
    _ = 1 / (2 : ℝ) ^ p := by field_simp

end Work.Resample
