import Mathlib
import Submission.Work.Resample.auDefs
import Submission.Work.Resample.auWtErr

namespace Work.Resample

-- Size bounds for the computed weights: since |auWt p α t (auNsq ..)| ≤ 2^p * auWi + 2 and
-- auWi = (1/(2α)) exp(...) ≤ 1/(2α) ≤ 1/4, the weights have |auWt| ≤ 2^p and hence isz ≤ p + 3.
-- `hwt` is the per-weight accuracy bound; it is Work.Resample.auWtErr in
-- Submission/Work/Resample/auWtErr.lean (which needs the π bound Resample/auPiApp as input).
theorem auWtSz (p α s t : ℕ) (hs : 2 ≤ s) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p) (ht : 0 < t)
    (hwt : ∀ (k i : ℕ), |(Work.Resample.auWt p α t (Work.Resample.auNsq p α s t k i) : ℝ) -
      (2 : ℝ) ^ p * Work.Resample.auWi p α s t k i| ≤ 2) :
    ∀ k i : ℕ, (Work.Resample.auWt p α t (Work.Resample.auNsq p α s t k i)).natAbs ≤ 2 ^ p ∧
      HvdH.isz (Work.Resample.auWt p α t (Work.Resample.auNsq p α s t k i)) ≤ p + 3 := by
  intro k i
  have hαR : (2 : ℝ) ≤ (α : ℝ) := by exact_mod_cast hα
  -- the exponent is ≤ 0, so the exponential factor is ≤ 1
  have hexp_le : Real.exp (-(Real.pi * (auNsq p α s t k i : ℝ) /
      ((α : ℝ) ^ 2 * (t : ℝ) ^ 2))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    apply neg_nonpos.mpr
    apply div_nonneg
    · exact mul_nonneg Real.pi_pos.le (by exact_mod_cast auNsq_nonneg p α s t k i)
    · positivity
  -- hence auWi ≤ 1/(2α) ≤ 1/4
  have hWi : auWi p α s t k i ≤ 1 / 4 := by
    rw [auWi]
    have h2a : (0 : ℝ) ≤ 1 / (2 * (α : ℝ)) := by positivity
    have hle : (1 : ℝ) / (2 * (α : ℝ)) ≤ 1 / 4 := by
      apply one_div_le_one_div_of_le (by norm_num) (by linarith)
    calc (1 / (2 * (α : ℝ))) * Real.exp (-(Real.pi * (auNsq p α s t k i : ℝ) /
            ((α : ℝ) ^ 2 * (t : ℝ) ^ 2)))
        ≤ (1 / (2 * (α : ℝ))) * 1 := mul_le_mul_of_nonneg_left hexp_le h2a
      _ ≤ 1 / 4 := by rw [mul_one]; exact hle
  have hWi0 : 0 ≤ auWi p α s t k i := by
    rw [auWi]; positivity
  have hpow4 : (4 : ℝ) ≤ (2 : ℝ) ^ p := by
    calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (2 : ℝ) ^ p := pow_le_pow_right₀ (by norm_num) (by omega : 2 ≤ p)
  have hbound : (2 : ℝ) ^ p * (1 / 4) + 2 ≤ (2 : ℝ) ^ p := by nlinarith
  have hba := hwt k i
  have hprod : (2 : ℝ) ^ p * auWi p α s t k i ≤ (2 : ℝ) ^ p * (1 / 4) :=
    mul_le_mul_of_nonneg_left hWi (by positivity)
  have hWt_le : ((auWt p α t (auNsq p α s t k i) : ℤ) : ℝ) ≤ (2 : ℝ) ^ p := by
    have h1 := (abs_le.mp hba).2
    linarith
  have hWt_ge : -((2 : ℝ) ^ p) ≤ ((auWt p α t (auNsq p α s t k i) : ℤ) : ℝ) := by
    have h1 := (abs_le.mp hba).1
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ p * auWi p α s t k i := mul_nonneg (by positivity) hWi0
    linarith
  have hAbs : |((auWt p α t (auNsq p α s t k i) : ℤ) : ℝ)| ≤ (2 : ℝ) ^ p :=
    abs_le.mpr ⟨hWt_ge, hWt_le⟩
  have hnatAbsR : ((auWt p α t (auNsq p α s t k i)).natAbs : ℝ) ≤ ((2 : ℕ) ^ p : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
    push_cast
    exact hAbs
  have hnatAbs : (auWt p α t (auNsq p α s t k i)).natAbs ≤ 2 ^ p := by exact_mod_cast hnatAbsR
  refine ⟨hnatAbs, ?_⟩
  rw [HvdH.isz]
  have hsize : (auWt p α t (auNsq p α s t k i)).natAbs.size ≤ p + 1 := by
    rw [Nat.size_le]
    calc (auWt p α t (auNsq p α s t k i)).natAbs ≤ 2 ^ p := hnatAbs
      _ < 2 ^ (p + 1) := Nat.pow_lt_pow_right one_lt_two (Nat.lt_succ_self p)
  omega

end Work.Resample
