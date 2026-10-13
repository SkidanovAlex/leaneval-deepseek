import Mathlib
import Submission.Work.WilG3.Defs

namespace Work.WilG3

-- Scale-counting fact for the chart family of `Submission/Work/WilG3/Defs.lean`: after
-- `geoK r ε = ⌈(r+2)(-log ε)⌉ + 2` geometric scales the family has descended from the midpoint
-- `1/2` past `ε`, i.e. `geoRho r ^ (geoK r ε) / 2 ≤ ε` (equivalently `geoRho r ^ (geoK r ε) ≤ 2ε`).
-- Proof idea: `-log ρ ≥ 1/(r+2)` (`Real.log_le_sub_one_of_pos`), so
-- `log (ρ^K) = K log ρ ≤ -K/(r+2) ≤ log ε - 2/(r+2) < log(2ε)`; conclude with
-- `Real.log_le_log_iff`, `Real.log_pow`, `Real.log_mul`.  Only `0 < ε < 1` is used.
theorem GeoKReaches (r : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    geoRho r ^ (geoK r ε) / 2 ≤ ε := by
  have hρpos : 0 < geoRho r := geoRho_pos r
  have hdpos : 0 < (r : ℝ) + 2 := by positivity
  -- `log ρ ≤ ρ - 1 = -1/(r+2)`
  have hlogρ : Real.log (geoRho r) ≤ -(((r : ℝ) + 2)⁻¹) := by
    have h := Real.log_le_sub_one_of_pos hρpos
    have he : geoRho r - 1 = -(((r : ℝ) + 2)⁻¹) := by simp [geoRho]
    linarith
  set K := geoK r ε with hK
  -- `K ≥ (r+2)(-log ε) + 2`
  have hKcast : (K : ℝ) = ((Nat.ceil (((r : ℝ) + 2) * (-Real.log ε)) : ℕ) : ℝ) + 2 := by
    rw [hK, geoK]; push_cast; ring
  have hKge : ((r : ℝ) + 2) * (-Real.log ε) + 2 ≤ (K : ℝ) := by
    rw [hKcast]
    have := Nat.le_ceil (((r : ℝ) + 2) * (-Real.log ε))
    linarith
  -- hence `K/(r+2) ≥ -log ε + 2/(r+2)`
  have hdiv : -Real.log ε + 2 / ((r : ℝ) + 2) ≤ (K : ℝ) / ((r : ℝ) + 2) := by
    rw [← sub_nonneg]
    have h1 : (K : ℝ) / ((r : ℝ) + 2) - (-Real.log ε + 2 / ((r : ℝ) + 2))
        = ((K : ℝ) - ((r : ℝ) + 2) * (-Real.log ε) - 2) / ((r : ℝ) + 2) := by
      field_simp
      ring
    rw [h1]
    exact div_nonneg (by linarith) (le_of_lt hdpos)
  have hstep : -((K : ℝ) / ((r : ℝ) + 2)) ≤ Real.log ε - 2 / ((r : ℝ) + 2) := by
    have := neg_le_neg hdiv
    linarith
  -- so `log (ρ^K) = K log ρ ≤ log (2ε)`
  have hmain : (K : ℝ) * Real.log (geoRho r) ≤ Real.log (2 * ε) := by
    have h1 : (K : ℝ) * Real.log (geoRho r) ≤ (K : ℝ) * (-(((r : ℝ) + 2)⁻¹)) :=
      mul_le_mul_of_nonneg_left hlogρ (Nat.cast_nonneg K)
    have h2 : (K : ℝ) * (-(((r : ℝ) + 2)⁻¹)) = -((K : ℝ) / ((r : ℝ) + 2)) := by
      field_simp
    have h3 : Real.log (2 * ε) = Real.log 2 + Real.log ε :=
      Real.log_mul (by norm_num) (ne_of_gt hε)
    have h4 : -(2 / ((r : ℝ) + 2)) ≤ Real.log 2 := by
      have hp : 0 < 2 / ((r : ℝ) + 2) := by positivity
      have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      linarith
    rw [h2] at h1
    rw [h3]
    linarith
  have hpowpos : 0 < geoRho r ^ K := geoRho_pow_pos r K
  have h2ε : 0 < 2 * ε := by linarith
  have hle : geoRho r ^ K ≤ 2 * ε := by
    refine (Real.log_le_log_iff hpowpos h2ε).mp ?_
    rw [Real.log_pow]
    exact hmain
  linarith

end Work.WilG3
