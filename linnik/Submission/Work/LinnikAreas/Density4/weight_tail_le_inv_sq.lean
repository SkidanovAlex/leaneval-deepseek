import Mathlib

namespace Work.LinnikAreas.Density4

/-- The tail weight `(log (2 + 2^m)) ^ (-A)` (with `A ≥ 2`) is bounded by `4 / m ^ 2`.
Indeed `log (2 + 2^m) ≥ m · log 2`, and `(m · log 2) ^ A ≥ (m · log 2) ^ 2 ≥ m ^ 2 / 4`
because `log 2 ≥ 1/2` and `m ≥ 2`. -/
lemma weight_tail_le_inv_sq (A : ℝ) (hA : 2 ≤ A) (m : ℕ) (hm : 2 ≤ m) :
    (Real.log (2 + (2 : ℝ) ^ m)) ^ (-A) ≤ 4 / (m : ℝ) ^ 2 := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2half : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  -- the comparison base `m · log 2`
  have hbase : 0 < (m : ℝ) * Real.log 2 := mul_pos hmpos hlog2pos
  have hbase1 : 1 ≤ (m : ℝ) * Real.log 2 := by
    have h := mul_le_mul hmR hlog2half (by norm_num) (le_of_lt hmpos)
    linarith
  -- `log (2 + 2^m) ≥ log (2^m) = m · log 2`
  have hloglb : (m : ℝ) * Real.log 2 ≤ Real.log (2 + (2 : ℝ) ^ m) := by
    have hpos2m : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
    have hle2m : (2 : ℝ) ^ m ≤ 2 + (2 : ℝ) ^ m := by linarith
    have h := Real.log_le_log hpos2m hle2m
    rwa [Real.log_pow] at h
  -- step 1: `x ↦ x ^ (-A)` is antitone on positive reals
  have hstep1 : (Real.log (2 + (2 : ℝ) ^ m)) ^ (-A) ≤ ((m : ℝ) * Real.log 2) ^ (-A) :=
    Real.rpow_le_rpow_of_nonpos hbase hloglb (by linarith)
  -- step 2: `(m · log 2) ^ A ≥ (m · log 2) ^ 2 ≥ m ^ 2 / 4`
  have htwo : ((m : ℝ) * Real.log 2) ^ (2 : ℝ) = ((m : ℝ) * Real.log 2) ^ 2 :=
    Real.rpow_ofNat _ 2
  have hpow : ((m : ℝ) * Real.log 2) ^ 2 ≤ ((m : ℝ) * Real.log 2) ^ A := by
    have h2 : ((m : ℝ) * Real.log 2) ^ (2 : ℝ) ≤ ((m : ℝ) * Real.log 2) ^ A :=
      Real.rpow_le_rpow_of_exponent_le hbase1 hA
    exact htwo ▸ h2
  have hsqpos : (0 : ℝ) < ((m : ℝ) * Real.log 2) ^ 2 := by positivity
  have hb2 : (m : ℝ) ^ 2 / 4 ≤ ((m : ℝ) * Real.log 2) ^ 2 := by
    have hlog2sq : (1 : ℝ) / 4 ≤ (Real.log 2) ^ 2 := by nlinarith
    calc (m : ℝ) ^ 2 / 4 = (m : ℝ) ^ 2 * (1 / 4 : ℝ) := by ring
      _ ≤ (m : ℝ) ^ 2 * (Real.log 2) ^ 2 := by
            apply mul_le_mul_of_nonneg_left hlog2sq (by positivity)
      _ = ((m : ℝ) * Real.log 2) ^ 2 := by ring
  have hm2pos : (0 : ℝ) < (m : ℝ) ^ 2 / 4 := by positivity
  have h1 : 1 / ((m : ℝ) * Real.log 2) ^ A ≤ 1 / ((m : ℝ) * Real.log 2) ^ 2 :=
    one_div_le_one_div_of_le hsqpos hpow
  have h2 : 1 / ((m : ℝ) * Real.log 2) ^ 2 ≤ 4 / (m : ℝ) ^ 2 := by
    have h3 : 1 / ((m : ℝ) * Real.log 2) ^ 2 ≤ 1 / ((m : ℝ) ^ 2 / 4) :=
      one_div_le_one_div_of_le hm2pos hb2
    have h4 : 1 / ((m : ℝ) ^ 2 / 4) = 4 / (m : ℝ) ^ 2 := one_div_div _ _
    linarith [h3, h4.le, h4.ge]
  have hstep2 : ((m : ℝ) * Real.log 2) ^ (-A) ≤ 4 / (m : ℝ) ^ 2 := by
    rw [Real.rpow_neg (le_of_lt hbase), ← one_div]
    exact le_trans h1 h2
  exact le_trans hstep1 hstep2

end Work.LinnikAreas.Density4
